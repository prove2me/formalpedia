-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:41:50.968635+00:00
-- url     : https://prove2.me/theorems/d27def30-2cb0-4ab8-877a-2ab097cdaaaf
-- title:
--   Norm Units Of Calculation
-- statement:
--   Definitions and structural lemmas for Norm Units Of Calculation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EmbeddingTraceSumAlt/NormUnitsOfCalculation.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.S
open scoped TensorProduct
namespace PI.ScPsiExists.UnitaryGroupMassFormula
section Tau
variable {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
theorem add_star_mem (hfix : ∀ a : E, star a = a ↔ a ∈ (algebraMap F E).range) (x : E) :
    ∃ a : F, algebraMap F E a = x + star x :=
  RingHom.mem_range.1 ((hfix (x + star x)).1 (by rw [star_add, star_star, add_comm]))
def tauFun (hfix : ∀ a : E, star a = a ↔ a ∈ (algebraMap F E).range) (x : E) : F :=
  (add_star_mem hfix x).choose
theorem tauFun_spec (hfix : ∀ a : E, star a = a ↔ a ∈ (algebraMap F E).range) (x : E) :
    algebraMap F E (tauFun hfix x) = x + star x :=
  (add_star_mem hfix x).choose_spec
def tau (hfix : ∀ a : E, star a = a ↔ a ∈ (algebraMap F E).range) : E →ₗ[F] F where
  toFun := tauFun hfix
  map_add' x y := (algebraMap F E).injective (by
    rw [map_add, tauFun_spec, tauFun_spec, tauFun_spec, star_add]; ring)
  map_smul' a x := (algebraMap F E).injective (by
    rw [RingHom.id_apply, smul_eq_mul, map_mul, tauFun_spec, tauFun_spec, Algebra.smul_def,
      star_mul, (hfix (algebraMap F E a)).2 ⟨a, rfl⟩]
    ring)
end Tau
section Tens
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def tT (τ : E →ₗ[F] F) : E ⊗[F] Af F →ₗ[F] Af F :=
  (TensorProduct.lid F (Af F)).toLinearMap ∘ₗ TensorProduct.map τ LinearMap.id
end Tens
def sHom (I : AutInst) : I.E →+ ℝ :=
  AddMonoidHom.mk' (fun x => ∑ v, 2 * (I.φ v x).re) (by
    intro x y
    simp only [map_add, Complex.add_re, mul_add, Finset.sum_add_distrib])
end PI.ScPsiExists.UnitaryGroupMassFormula


