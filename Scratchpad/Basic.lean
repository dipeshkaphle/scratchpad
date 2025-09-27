import Auto
import Lean

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 4
set_option auto.smt.solver.name "cvc5"
-- Syntax for our custom proof macro with timing
@[incremental]
syntax "prove" ":" term "by" tacticSeq : command

-- Command elaborator with timing
open Lean Elab Command in
@[incremental]
elab "prove" ":" prop:term "by" tactics:tacticSeq : command => do
  let startTime ← IO.monoMsNow
  elabCommand (← `(example : $prop := by $tactics))
  let endTime ← IO.monoMsNow
  let elapsed := endTime - startTime
  logInfo m!"Proof elaborated in {elapsed}ms"

-- Timing tactic that measures and logs execution time
open Lean Elab Tactic Meta in
elab "time_tactic" tac:tacticSeq : tactic => do
  let startTime ← IO.monoMsNow
  evalTactic tac
  let endTime ← IO.monoMsNow
  let elapsed := endTime - startTime
  logInfo m!"Tactic executed in {elapsed}ms"

-- Export hello for Main.lean
def hello : String := "world"

@[reducible]
def isMax (mx: Int) (arr: Array Int) := 
    forall ( i : Nat), ( h: i < arr.size ) -> mx >= (arr[i]'h)

def maxElem (arr: Array Int) : Int := 
  let mx := arr[0]!
  arr.foldl (fun a b => if a > b then a else b) mx
  

prove: ∀ (arr1 arr2 arr3 arr4: Array Int), 
    (h1: arr1.size > 0) -> 
    (h2: arr2.size > 0) -> 
    (h3: arr3.size > 0) -> 
    (h4: arr4.size > 0) -> 
    isMax (maxElem arr1) arr1
    ∧ isMax (maxElem arr2) arr2
    ∧ isMax (maxElem arr3) arr3
    ∧ isMax (maxElem arr4) arr4
    ∧ isMax (maxElem arr2) arr2
    ∧ isMax (maxElem arr4) arr4
    ∧ isMax (maxElem arr2) arr2
    ∧ isMax (maxElem arr2) arr2
    ∧ isMax (maxElem arr2) arr2
    ∧ isMax (maxElem arr1) arr1
    ∧ isMax (maxElem arr2) arr2
    ∧ isMax (maxElem arr3) arr3
    ∧ isMax (maxElem arr4) arr4
    ∧ isMax (maxElem arr2) arr2
    ∧ isMax (maxElem arr4) arr4
    ∧ isMax (maxElem arr2) arr2
    ∧ isMax (maxElem arr2) arr2
    by
  intro arr1 arr2 arr3 arr4 h1 h2 h3 h4
  time_tactic (repeat' (apply And.intro <;> try (unfold isMax; intro i h; unfold maxElem ; try auto [*] )))
  · time_tactic (skip)
    simp_all
    simp_all
  · skip
  · simp_all
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry



example: ∀ (arr1 arr2 arr3 arr4: Array Int), 
    (h1: arr1.size > 0) -> 
    (h2: arr2.size > 0) -> 
    (h3: arr3.size > 0) -> 
    (h4: arr4.size > 0) -> 
    isMax (maxElem arr1) arr1
    ∧ isMax (maxElem arr2) arr2
    ∧ isMax (maxElem arr3) arr3
    ∧ isMax (maxElem arr4) arr4
    ∧ isMax (maxElem arr2) arr2
    ∧ isMax (maxElem arr4) arr4
    ∧ isMax (maxElem arr2) arr2
    ∧ isMax (maxElem arr2) arr2
    ∧ isMax (maxElem arr2) arr2
    ∧ isMax (maxElem arr1) arr1
    ∧ isMax (maxElem arr2) arr2
    ∧ isMax (maxElem arr3) arr3
    ∧ isMax (maxElem arr4) arr4
    ∧ isMax (maxElem arr2) arr2
    ∧ isMax (maxElem arr4) arr4
    ∧ isMax (maxElem arr2) arr2
    ∧ isMax (maxElem arr2) arr2
    := by
  intro arr1 arr2 arr3 arr4 h1 h2 h3 h4
  time_tactic (repeat' (apply And.intro <;> try (unfold isMax; intro i h; unfold maxElem ; try auto [*] )))
  · simp_all
    simp_all
  · skip
  · simp_all
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry

