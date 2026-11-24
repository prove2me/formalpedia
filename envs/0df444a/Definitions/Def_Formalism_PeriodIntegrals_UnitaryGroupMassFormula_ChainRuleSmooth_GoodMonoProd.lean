-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_GoodMonoProd
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_GoodMonoProd
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T16:18:35.287342+00:00
-- url     : https://prove2.me/theorems/ee5be1e2-4d51-437d-9b2a-5a76eb877552
-- title:
--   Good Mono Prod
-- statement:
--   Definitions and structural lemmas for Good Mono Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/GoodMonoProd.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Theorems.Thm_CCRuleCW_apO_cons
import Theorems.Thm_CCRuleCW_apO_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CCRuleCW.apO_cons
attribute [local simp] CCRuleCW.apO_nil


set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
namespace CCRuleCW
open Formalism.FourierDecayAlt
section sup
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
def dirL (o : Bool × B.Mat k r) : B.Mat k r →L[ℝ] B.Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := dir o
      map_add' := fun a b => by
        rcases o with ⟨_ | _, X⟩
        · exact Matrix.add_mul a b X
        · show -(X * (a + b)) = -(X * a) + -(X * b)
          rw [Matrix.mul_add, neg_add]
      map_smul' := fun c a => by
        rcases o with ⟨_ | _, X⟩
        · exact Matrix.smul_mul c a X
        · show -(X * (c • a)) = c • -(X * a)
          rw [Matrix.mul_smul, smul_neg] }
def coordL (p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) : B.Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => g p.1 p.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
def ccoordL (p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) : B.Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => conj (g p.1 p.2)
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp [Matrix.smul_apply, Complex.real_smul] }
def xv (g : B.Mat k r) : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → ℂ :=
  Sum.elim (fun p => g p.1 p.2) (fun p => conj (g p.1 p.2))
end sup
end CCRuleCW


