-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapesBis
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapesBis
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T10:56:23.438233+00:00
-- url     : https://prove2.me/theorems/52e5070c-9f4b-5fe3-94c7-9e86015b697c
-- title:
--   Discriminant Norm Shapes Bis
-- statement:
--   Definitions and structural lemmas for Discriminant Norm Shapes Bis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscriminantNormShapesBis.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapes
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_mem_pow_vF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_notMem_pow_vF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero


set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
namespace Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.HermitianLattices.Ext.L3.localValuationFiltration Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
def LiftOnto : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → ∀ Y : udPre K 𝔭 k a,
      ∃ X ∈ skSet K 𝔭 k a, ∃ Z : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), X - Y.1 = Z * diagQ K 𝔭 k a
theorem mul_not_mem_pow_add_succ {F : Type} [Field F] [NumberField F] {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {x y : 𝓞 F} {a b : ℕ} (hx : x ∈ 𝔭 ^ a) (hx' : x ∉ 𝔭 ^ (a + 1))
    (hy : y ∈ 𝔭 ^ b) (hy' : y ∉ 𝔭 ^ (b + 1)) : x * y ∉ 𝔭 ^ (a + b + 1) := by
  have hp0 : 𝔭 ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have hpr : Prime 𝔭 := Ideal.prime_of_isPrime hp0 h𝔭.isPrime
  intro hxy
  rw [← Ideal.dvd_span_singleton] at hx hx' hy hy' hxy
  obtain ⟨I, hI⟩ := hx
  obtain ⟨J, hJ⟩ := hy
  have hI' : ¬ 𝔭 ∣ I := fun h => hx' (by rw [hI, pow_succ]; exact mul_dvd_mul_left _ h)
  have hJ' : ¬ 𝔭 ∣ J := fun h => hy' (by rw [hJ, pow_succ]; exact mul_dvd_mul_left _ h)
  rw [← Ideal.span_singleton_mul_span_singleton, hI, hJ] at hxy
  have h : 𝔭 ^ (a + b) * 𝔭 ∣ 𝔭 ^ (a + b) * (I * J) := by
    rw [← pow_succ]
    convert hxy using 1
    rw [pow_add]
    ring
  rcases hpr.dvd_or_dvd ((mul_dvd_mul_iff_left (pow_ne_zero _ hp0)).mp h) with h | h
  exacts [hI' h, hJ' h]
theorem prod_notMem {F : Type} [Field F] [NumberField F] {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {ι : Type} (s : Finset ι) (f : ι → 𝓞 F) (hf : ∀ i, f i ≠ 0) :
    ∏ i ∈ s, f i ∉ 𝔭 ^ (∑ i ∈ s, vF 𝔭 (f i) + 1) := by
  classical

  have key : ∀ t : Finset ι, ∏ i ∈ t, f i ∈ 𝔭 ^ (∑ i ∈ t, vF 𝔭 (f i)) ∧
      ∏ i ∈ t, f i ∉ 𝔭 ^ (∑ i ∈ t, vF 𝔭 (f i) + 1) := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · refine ⟨by simp, ?_⟩
      simp only [Finset.prod_empty, Finset.sum_empty, zero_add, pow_one]
      exact (Ideal.ne_top_iff_one 𝔭).mp h𝔭.ne_top
    · intro j t hj ih
      rw [Finset.prod_insert hj, Finset.sum_insert hj]
      refine ⟨?_, mul_not_mem_pow_add_succ h𝔭 (mem_pow_vF h𝔭 (hf j)) (notMem_pow_vF h𝔭 (hf j)) ih.1 ih.2⟩
      rw [pow_add]
      exact Ideal.mul_mem_mul (mem_pow_vF h𝔭 (hf j)) ih.1
  exact (key s).2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
theorem mem_extP_of_mul_mem_pow_succ {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A : 𝓞 F} {e : ℕ}
    (hA : A ∈ 𝔭 ^ e) (hA' : A ∉ 𝔭 ^ (e + 1)) {w : 𝓞 K}
    (hw : ι A * w ∈ extP K 𝔭 ^ (e + 1)) : w ∈ extP K 𝔭 := by
  have hp0 : 𝔭 ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have hJdef : extP K 𝔭 = 𝔭.map ι := rfl
  rw [← Ideal.dvd_span_singleton] at hA hA'
  obtain ⟨I, hI⟩ := hA

  have hI' : I ⊔ 𝔭 = ⊤ := by
    by_contra h
    apply hA'
    rw [hI, pow_succ]
    apply mul_dvd_mul_left
    rw [Ideal.dvd_iff_le]
    exact le_sup_left.trans (h𝔭.eq_of_le h le_sup_right).ge
  have hJ0 : extP K 𝔭 ≠ ⊥ := by
    intro h
    apply hp0
    rw [hJdef] at h
    exact (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))).mp h
  have hspan : Ideal.span {ι A} = extP K 𝔭 ^ e * I.map ι := by
    rw [hJdef, ← Ideal.map_pow, ← Ideal.map_mul, ← hI, Ideal.map_span, Set.image_singleton]
  have hcop : I.map ι ⊔ extP K 𝔭 = ⊤ := by
    rw [hJdef, ← Ideal.map_sup, hI', Ideal.map_top]
  rw [← Ideal.dvd_span_singleton, ← Ideal.span_singleton_mul_span_singleton, hspan, pow_succ,
    mul_assoc] at hw
  have h1 := (mul_dvd_mul_iff_left (pow_ne_zero e hJ0)).mp hw
  rw [Ideal.dvd_iff_le] at h1
  rw [← Ideal.dvd_span_singleton, Ideal.dvd_iff_le]
  calc Ideal.span {w} = (I.map ι ⊔ extP K 𝔭) * Ideal.span {w} := by rw [hcop, Ideal.top_mul]
    _ = I.map ι * Ideal.span {w} ⊔ extP K 𝔭 * Ideal.span {w} := Ideal.sup_mul _ _ _
    _ ≤ extP K 𝔭 := sup_le h1 (Ideal.mul_le_inf.trans inf_le_left)
theorem isUnit_det {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : Fin m → 𝓞 F} (ha : ∀ i, a i ≠ 0)
    {k : ℕ} (hk : vJof 𝔭 a + 1 ≤ k) {X : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hX : X ∈ skSet K 𝔭 k a) : IsUnit X.det := by
  classical
  have hX0 : Xᴴ * diagQ K 𝔭 k a * X = diagQ K 𝔭 k a := hX
  have hA0 : ∏ i, a i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  have hdet : (diagQ K 𝔭 k a).det = Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι (∏ i, a i)) := by
    unfold diagQ
    rw [Matrix.det_diagonal]
    simp only [map_prod]
  have hd := congrArg Matrix.det hX0
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdet] at hd

  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (1 - star X.det * X.det)
  have hAw : ι (∏ i, a i) * w ∈ extP K 𝔭 ^ k := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hw]
    linear_combination -hd
  have he : vF 𝔭 (∏ i, a i) ≤ vJof 𝔭 a := by
    by_contra h
    have h2 : ∑ i, vF 𝔭 (a i) + 1 ≤ vF 𝔭 (∏ i, a i) := by
      unfold vJof at h
      omega
    exact prod_notMem h𝔭 Finset.univ a ha (Ideal.pow_le_pow_right h2 (mem_pow_vF h𝔭 hA0))
  have hwJ : w ∈ extP K 𝔭 := mem_extP_of_mul_mem_pow_succ h𝔭 (mem_pow_vF h𝔭 hA0) (notMem_pow_vF h𝔭 hA0)
    (Ideal.pow_le_pow_right (by omega) hAw)
  have hnil : IsNilpotent (1 - star X.det * X.det) := by
    refine ⟨k, ?_⟩
    rw [← hw, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hwJ k
  have h1 : IsUnit (star X.det * X.det) := by
    have h := hnil.isUnit_one_sub
    rwa [sub_sub_cancel] at h
  exact isUnit_of_mul_isUnit_right h1
theorem mul_mem_skSet {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : Fin m → 𝓞 F}
    {X X' : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)} (hX : X ∈ skSet K 𝔭 k a)
    (hX' : X' ∈ skSet K 𝔭 k a) : X * X' ∈ skSet K 𝔭 k a := by
  have h1 : Xᴴ * diagQ K 𝔭 k a * X = diagQ K 𝔭 k a := hX
  have h2 : X'ᴴ * diagQ K 𝔭 k a * X' = diagQ K 𝔭 k a := hX'
  show (X * X')ᴴ * diagQ K 𝔭 k a * (X * X') = diagQ K 𝔭 k a
  rw [conjTranspose_mul, show X'ᴴ * Xᴴ * diagQ K 𝔭 k a * (X * X') = X'ᴴ * (Xᴴ * diagQ K 𝔭 k a * X) * X' by
    simp only [Matrix.mul_assoc], h1, h2]
def toPre {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : Fin m → 𝓞 F} (ha : ∀ i, a i ≠ 0)
    {k : ℕ} (hk : vJof 𝔭 a + 1 ≤ k) (X : skSet K 𝔭 k a) : udPre K 𝔭 k a :=
  ⟨X.1, ⟨(X.1⁻¹)ᴴ, by
    have hu := isUnit_det h𝔭 ha hk X.2
    have hX0 : X.1ᴴ * diagQ K 𝔭 k a * X.1 = diagQ K 𝔭 k a := X.2
    calc (X.1⁻¹)ᴴ * diagQ K 𝔭 k a = (X.1⁻¹)ᴴ * (X.1ᴴ * diagQ K 𝔭 k a * X.1) := by rw [hX0]
      _ = (X.1 * X.1⁻¹)ᴴ * diagQ K 𝔭 k a * X.1 := by
          rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [mul_nonsing_inv _ hu, conjTranspose_one, Matrix.one_mul]⟩,
    ⟨0, by
      have hX0 : X.1ᴴ * diagQ K 𝔭 k a * X.1 = diagQ K 𝔭 k a := X.2
      rw [hX0, sub_self, Matrix.mul_zero, Matrix.zero_mul]⟩⟩
def cls {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : Fin m → 𝓞 F} (ha : ∀ i, a i ≠ 0)
    {k : ℕ} (hk : vJof 𝔭 a + 1 ≤ k) (X : skSet K 𝔭 k a) : udQ K 𝔭 k a :=
  Quotient.mk (udSetoid K 𝔭 k a) (toPre h𝔭 ha hk X)
end Formalism.L2.SG.Pf.discriminantNormShapes


