-- Prove2me | Definitions.Def_BS2_b3ba934b_NumericOrderBounds
-- name    : BS2_b3ba934b_NumericOrderBounds
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:33:55.256817+00:00
-- url     : https://prove2.me/theorems/881311fa-b8b5-43d5-819e-08417e98998b
-- title:
--   Sensitivity separation: NumericOrderBounds (complete source module)
-- statement:
--   Complete Lean source module `NumericOrderBounds` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/NumericOrderBounds.lean; original SHA-256 959ba9457344bdfcda5394295387f79e65ac2526376772a4033a375c53ffa9bb; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_NumericAdmissibility
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundNumericOrder
open ThreeBoundNumeric ThreeBoundFullProfile

theorem a_antitone_right {n : ℕ} (v : Profile n) (hv : Ordered v)
    (i j k : Fin n) (hij : i ≤ j) (hjk : j ≤ k) : v (.a i k) ≤ v (.a i j) := by
  have aux : ∀ d : ℕ, ∀ k : Fin n, k.val = d →
      ∀ j : Fin n, i ≤ j → j ≤ k → v (.a i k) ≤ v (.a i j) := by
    intro d
    induction d with
    | zero =>
      intro k hk j hij hjk
      have he : k = j := Fin.ext (by omega)
      subst k
      exact le_rfl
    | succ d ih =>
      intro k hk j hij hjk
      by_cases he : k = j
      · subst k; exact le_rfl
      have hjk' : j < k := lt_of_le_of_ne hjk (Ne.symm he)
      have hik : i < k := lt_of_le_of_lt hij hjk'
      have hp : (prev k).val = d := by simp only [prev,Fin.val_mk]; omega
      have hjp : j ≤ prev k := by change j.val ≤ k.val-1; omega
      exact (hv i k hik).2.1.trans (ih (prev k) hp j hij hjp)
  exact aux k.val k rfl j hij hjk

theorem aExpr_antitone_right {n : ℕ} (v : Profile n) (hv : Ordered v)
    (i j k : Fin n) (hij : i ≤ j) (hjk : j ≤ k) :
    (aExpr n i.val k.val).eval v ≤ (aExpr n i.val j.val).eval v := by
  simpa only [aExpr,dif_pos i.isLt,dif_pos j.isLt,dif_pos k.isLt,Expr.eval]
    using a_antitone_right v hv i j k hij hjk

end ThreeBoundNumericOrder

#print axioms ThreeBoundNumericOrder.aExpr_antitone_right


