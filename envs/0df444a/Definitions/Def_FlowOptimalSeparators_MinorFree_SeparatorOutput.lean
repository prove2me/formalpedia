-- Prove2me | Definitions.Def_FlowOptimalSeparators_MinorFree_SeparatorOutput
-- name    : FlowOptimalSeparators_MinorFree_SeparatorOutput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T00:06:19.399167+00:00
-- url     : https://prove2.me/theorems/ad63b7a4-2e22-4695-b1dc-a5369cf290ae
-- title:
--   Actual separator output masks and polynomial index-word ranges
-- statement:
--   A returned vertex set is a bit mask in output memory: the first cell is $n$, followed by $n$ zero-or-one cells. The separator output condition asserts balance and
--   $$|S|\le C_{\rm size}\,h\ln h\sqrt n.$$
--   A separate index-range predicate bounds every natural register and memory value during every execution by a fixed polynomial range. Real registers support exact scalar arithmetic, including rational connector loads. These are properties to prove about actual executions, with no separator or cost supplied in the input.
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 3, 17, Theorem 2, output and machine convention

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_Graph
import Definitions.Def_FlowOptimalSeparators_MinorFree_RandomRAM

set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree

/-- A vertex mask in natural output memory: cell 0 is n, cells 1..n are its bits. -/
noncomputable def outputSet (n : ℕ)
    (s : VehicleRoutingSurvey.Routing.ArithmeticState) : Finset (Fin n) :=
  by classical exact Finset.univ.filter (fun v => s.nm (v.val + 1) = 1)

def IsVertexMask (n : ℕ) (s : VehicleRoutingSurvey.Routing.ArithmeticState) : Prop :=
  s.nm 0 = n ∧ ∀ v : Fin n, s.nm (v.val + 1) ≤ 1

/-- A polynomial word range for index registers and natural memory throughout every run.
Real registers hold exact scalar arithmetic, including the connector's rational loads. -/
def IndexRange (P : Program) (ns : List ℕ) (rs : List ℝ) (B : ℕ) : Prop :=
  ∀ ω t i, (ramRun P ns rs ω t).scalar.nr i ≤ B ∧
    (ramRun P ns rs ω t).scalar.nm i ≤ B

noncomputable def SeparatorOutput {n : ℕ} (G : Graph n) (h : ℕ) (Csize : ℝ)
    (s : VehicleRoutingSurvey.Routing.ArithmeticState) : Prop :=
  IsVertexMask n s ∧ Balanced G (outputSet n s) ∧
    ((outputSet n s).card : ℝ) ≤ Csize * h * Real.log h * Real.sqrt n

end FlowOptimalSeparators.MinorFree


