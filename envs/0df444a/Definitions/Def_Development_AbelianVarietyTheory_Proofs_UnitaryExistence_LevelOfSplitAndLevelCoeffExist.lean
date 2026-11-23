-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelOfSplitAndLevelCoeffExist
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelOfSplitAndLevelCoeffExist
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:32.794123+00:00
-- url     : https://prove2.me/theorems/0d2f6125-e712-4d12-98b0-e91f013f97d0
-- title:
--   Level Of Split And Level Coeff Exist
-- statement:
--   Definitions and structural lemmas for Level Of Split And Level Coeff Exist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LevelOfSplitAndLevelCoeffExist.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Theorems.Thm_GlobalTheory_HostModel_coe_rt_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.LevelExist
open GlobalTheory.HostModel
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem bar_mem_adjoin (H : Host E) {a : 𝓞 E} (ha : a ∈ Algebra.adjoin ℤ {H.w0}) :
    H.bar a ∈ Algebra.adjoin ℤ {H.w0} := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx, cmHost_bar_halfIntegerGenerator]
    exact sub_mem (one_mem _) (Algebra.self_mem_adjoin_singleton ℤ _)
  | algebraMap r =>
    rw [eq_intCast, map_intCast]
    exact intCast_mem _ r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
theorem map_bar_span_bar (H : Host E) (al : 𝓞 E) :
    (Ideal.span {H.bar al}).map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {al} := by
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  exact bar_bar H al
def levelOfSplit (H : Host E) (al : 𝓞 E) (M A : ℕ) (hal : al ∈ Algebra.adjoin ℤ {H.w0})
    (hM : al * H.bar al = (M : 𝓞 E)) (hc : IsCoprime al (H.bar al)) (h3 : 3 ≤ M) (ho : Odd M)
    (hA : 0 < A) : Level H where
  M := M
  three_le := h3
  odd := ho
  Mb := Ideal.span {H.bar al}
  fromK := by
    apply le_antisymm
    · apply Ideal.span_mono
      rintro a rfl
      exact ⟨Ideal.mem_span_singleton_self _, bar_mem_adjoin H hal⟩
    · exact Ideal.span_le.mpr fun a ha => ha.1
  prod := by
    rw [map_bar_span_bar, Ideal.span_singleton_mul_span_singleton, mul_comm, hM]
  coprime := by
    rw [map_bar_span_bar, ← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
    exact hc.symm
  A := A
  A_pos := hA
theorem M'_pos {H : Host E} (l : Level H) : 0 < l.M' :=
  Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
theorem zeta_eq_pow_of_dvd {a n : ℕ} (hn : 0 < n) (h : a ∣ n) : ∃ k : ℕ, zeta a = zeta n ^ k := by
  obtain ⟨k, rfl⟩ := h
  have ha : (a : ℂ) ≠ 0 := by
    have : a ≠ 0 := by rintro rfl; simp at hn
    exact_mod_cast this
  have hk : (k : ℂ) ≠ 0 := by
    have : k ≠ 0 := by rintro rfl; simp at hn
    exact_mod_cast this
  refine ⟨k, ?_⟩
  unfold zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp
theorem isIntegral_zeta {n : ℕ} (hn : 0 < n) : IsIntegral ℚ (zeta n) :=
  ((Complex.isPrimitiveRoot_exp n hn.ne').isIntegral hn).tower_top
theorem hostRootValue_eq_or_neg_embedding (H : Host E) (τ : E →+* ℂ) : H.rt0 = τ (H.rt : E) ∨ H.rt0 = -τ (H.rt : E) := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [H.sqrt_neg_disc_sq, ← map_pow, coe_rt_sq]
  simp
def minCoeff {H : Host E} (l : Level H) : Coeff l :=
  have hconj : ∀ (τ : E →+* ℂ) (a : E), τ a ∈
      IntermediateField.normalClosure ℚ E ℂ ⊔ IntermediateField.adjoin ℚ {zeta l.M'} := fun τ a =>
    (le_sup_left : IntermediateField.normalClosure ℚ E ℂ ≤ _)
      (AlgHom.fieldRange_le_normalClosure τ.toRatAlgHom ⟨a, rfl⟩)
  have hz : zeta l.M' ∈
      IntermediateField.normalClosure ℚ E ℂ ⊔ IntermediateField.adjoin ℚ {zeta l.M'} :=
    (le_sup_right : IntermediateField.adjoin ℚ {zeta l.M'} ≤ _)
      (IntermediateField.mem_adjoin_simple_self ℚ _)
  { F := IntermediateField.normalClosure ℚ E ℂ ⊔ IntermediateField.adjoin ℚ {zeta l.M'}
    fin := by
      haveI := IntermediateField.adjoin.finiteDimensional (isIntegral_zeta (M'_pos l))
      infer_instance
    conj := hconj
    zeta_mem := hz
    le := by
      unfold KA
      rw [IntermediateField.adjoin_le_iff]
      rintro x (rfl | rfl)
      · obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
        rcases hostRootValue_eq_or_neg_embedding H τ with h | h <;> rw [h]
        · exact hconj τ _
        · exact neg_mem (hconj τ _)
      · obtain ⟨k, hk⟩ := zeta_eq_pow_of_dvd (M'_pos l) (Nat.dvd_lcm_right l.M l.A)
        rw [hk]
        exact pow_mem hz k }
instance instNonemptyCoeff {H : Host E} (l : Level H) : Nonempty (Coeff l) := ⟨minCoeff l⟩
end GlobalTheory.LevelExist
namespace GlobalTheory
end GlobalTheory


