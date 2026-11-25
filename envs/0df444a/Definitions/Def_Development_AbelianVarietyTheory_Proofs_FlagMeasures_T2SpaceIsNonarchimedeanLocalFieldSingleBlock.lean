-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:17:55.214798+00:00
-- url     : https://prove2.me/theorems/92314189-4ba0-40f4-816e-40d5c4a5108d
-- title:
--   T2 Space Is Nonarchimedean Local Field Single Block
-- statement:
--   Definitions and structural lemmas for T2 Space Is Nonarchimedean Local Field Single Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
namespace GlobalTheory.ResidueCharacterDense
theorem norm_le_one_of_isIntegral {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω] {x : Ω}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨f, hf, hx⟩ := hx
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ] at hx
  have h1 : f.coeff f.natDegree = 1 := hf
  rw [h1, map_one, one_mul] at hx
  have h2 : x ^ f.natDegree = - ∑ i ∈ Finset.range f.natDegree, algebraMap ℤ Ω (f.coeff i) * x ^ i := by
    linear_combination hx
  have h3 : ‖∑ i ∈ Finset.range f.natDegree, algebraMap ℤ Ω (f.coeff i) * x ^ i‖ ≤ ‖x‖ ^ f.natDegree / ‖x‖ := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul, norm_pow, le_div_iff₀ (by linarith)]
    have h4 : ‖algebraMap ℤ Ω (f.coeff i)‖ ≤ 1 := by
      simpa using IsUltrametricDist.norm_intCast_le_one Ω (f.coeff i)
    have h5 : ‖x‖ ^ (i + 1) ≤ ‖x‖ ^ f.natDegree :=
      pow_le_pow_right₀ h.le (Finset.mem_range.mp hi)
    calc _ ≤ 1 * ‖x‖ ^ i * ‖x‖ := by gcongr
      _ = ‖x‖ ^ (i + 1) := by ring
      _ ≤ _ := h5
  rw [← norm_neg, ← h2, norm_pow, le_div_iff₀ (by linarith)] at h3
  have : 0 < ‖x‖ ^ f.natDegree := by positivity
  nlinarith
def smallIdeal {F Ω : Type} [Field F] [NormedField Ω] [IsUltrametricDist Ω] (σ : F →+* Ω) :
    Ideal (𝓞 F) where
  carrier := {x | ‖σ x‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
    have h1 : ‖σ c‖ ≤ 1 :=
      norm_le_one_of_isIntegral ((RingOfIntegers.isIntegral_coe c).map σ.toIntAlgHom)
    calc _ ≤ 1 * ‖σ x‖ := by gcongr
      _ < 1 := by simpa using hx
section Local
variable {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [NumberField F]
  (p : HeightOneSpectrum (𝓞 F)) {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [T2Space K] [CharZero K] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K] [ContinuousSMul ℚ_[l] K]
  (ι : F →+* K) (U : Set K)
end Local
open Formalism.MainNotions.S.Loc
end GlobalTheory.ResidueCharacterDense


