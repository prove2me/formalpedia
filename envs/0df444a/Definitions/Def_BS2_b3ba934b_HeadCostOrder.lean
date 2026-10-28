-- Prove2me | Definitions.Def_BS2_b3ba934b_HeadCostOrder
-- name    : BS2_b3ba934b_HeadCostOrder
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:02:07.490015+00:00
-- url     : https://prove2.me/theorems/53d2f948-0569-49b4-a03c-4836acaaf080
-- title:
--   Sensitivity separation: HeadCostOrder (complete source module)
-- statement:
--   Complete Lean source module `HeadCostOrder` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/HeadCostOrder.lean; original SHA-256 09c1e532953458de00beb8d6fedfcf69c5e5eb272eec49bb4631b724ce08c876; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Numeric order needed for nonnegative histogram differences. -/
import Definitions.Def_BS2_b3ba934b_Q2RawExpressions
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace ThreeBoundHeadCostOrder
open ThreeBoundNumeric ThreeBoundFullProfile

theorem eval_min {n : ℕ} (v : Profile n) (a b : Expr n) :
    (min a b).eval v = min (a.eval v) (b.eval v) := rfl
theorem eval_max {n : ℕ} (v : Profile n) (a b : Expr n) :
    (max a b).eval v = max (a.eval v) (b.eval v) := rfl
theorem eval_add {n : ℕ} (v : Profile n) (a b : Expr n) :
    (a+b).eval v = a.eval v+b.eval v := rfl
theorem eval_scale {n : ℕ} (v : Profile n) (k : ℕ) (a : Expr n) :
    (k*a).eval v = k*a.eval v := rfl

theorem headCost_zero_le {n : ℕ} (a c : Entry) (v : Profile n)
    (kind : Fin 8) (hits : Fin 3) :
    (headCost n a c kind.val 0).eval v ≤ (headCost n a c kind.val hits.val).eval v := by
  fin_cases kind <;> fin_cases hits <;> dsimp [headCost] <;>
    (try split_ifs) <;> (try simp only [eval_min,eval_max,eval_add,eval_scale,Expr.eval]) <;> omega

theorem headCost_one_le_two {n : ℕ} (a c : Entry) (v : Profile n) (kind : Fin 8) :
    (headCost n a c kind.val 1).eval v ≤ (headCost n a c kind.val 2).eval v := by
  fin_cases kind <;> dsimp [headCost] <;> (try split_ifs) <;>
    (try simp only [eval_min,eval_max,eval_add,eval_scale,Expr.eval]) <;> omega

end ThreeBoundHeadCostOrder

#print axioms ThreeBoundHeadCostOrder.headCost_zero_le
#print axioms ThreeBoundHeadCostOrder.headCost_one_le_two


