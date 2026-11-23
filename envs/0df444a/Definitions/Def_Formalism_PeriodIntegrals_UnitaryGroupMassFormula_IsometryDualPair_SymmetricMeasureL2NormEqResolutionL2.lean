-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDualPair_SymmetricMeasureL2NormEqResolutionL2
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDualPair_SymmetricMeasureL2NormEqResolutionL2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:42.612967+00:00
-- url     : https://prove2.me/theorems/fa460257-6e8e-475f-be7f-858733b560fd
-- title:
--   Symmetric Measure L2 Norm Eq Resolution L2
-- statement:
--   Definitions and structural lemmas for Symmetric Measure L2 Norm Eq Resolution L2, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDualPair/SymmetricMeasureL2NormEqResolutionL2.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDualPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
namespace PI.IsoDualPair.UnitaryGroupMassFormula
open PI.IsoDualPair
instance finite_colChoice {Lt : Type} [Finite Lt] (N : ℕ) (nu : Lt → YoungDiagram) :
    Finite (ColChoice N nu) := by
  unfold ColChoice
  have : ∀ a, Finite (Fin a ↪o Fin N) := fun a =>
    Finite.of_injective (fun e : Fin a ↪o Fin N => (e : Fin a → Fin N))
      (fun e f h => DFunLike.coe_injective h)
  infer_instance
noncomputable instance fintype_colChoice {Lt : Type} [Finite Lt] (N : ℕ) (nu : Lt → YoungDiagram) :
    Fintype (ColChoice N nu) := Fintype.ofFinite _
variable {Lt : Type} [Fintype Lt] {N : ℕ} {nu : Lt → YoungDiagram}
lemma prC_eq (φ ψ : LaC N nu) : prC φ ψ = ∑ J, φ J * ψ J := finsum_eq_sum_of_fintype _
def pairL : Vnu N nu →ₗ[ℂ] Module.Dual ℂ (Vnu N nu) :=
  LinearMap.mk₂ ℂ (fun φ ψ : Vnu N nu => prC (φ : LaC N nu) ψ)
    (fun a b c => by
      simp only [Submodule.coe_add, prC_eq, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun J _ => by ring)
    (fun r a b => by
      simp only [Submodule.coe_smul, prC_eq, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun J _ => by ring)
    (fun a b c => by
      simp only [Submodule.coe_add, prC_eq, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun J _ => by ring)
    (fun r a b => by
      simp only [Submodule.coe_smul, prC_eq, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun J _ => by ring)
end PI.IsoDualPair.UnitaryGroupMassFormula


