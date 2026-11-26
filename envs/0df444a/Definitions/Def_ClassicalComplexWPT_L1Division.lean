-- Prove2me | Definitions.Def_ClassicalComplexWPT_L1Division
-- name    : ClassicalComplexWPT_L1Division
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:00:11.990453+00:00
-- url     : https://prove2.me/theorems/3e17dd69-ba96-4796-a20b-6c3055a96f5b
-- title:
--   L1 Division
-- statement:
--   Definitions and structural lemmas for L1 Division, from BochaoKong (BochaoKong/classical-complex-wpt; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Classical complex-analytic Weierstrass preparation theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_norm_convolutionRight_le
import Theorems.Thm_ClassicalComplexWPT_norm_highShiftCLM_le
attribute [local simp] ClassicalComplexWPT.monomial_zero


set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
namespace ClassicalComplexWPT
section ProductAntidiagonal
variable {A B : Type*}
def prodAntidiagonalEquiv : ((A × A) × (B × B)) ≃ ((A × B) × (A × B)) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv := by rintro ⟨⟨a₁,a₂⟩,⟨b₁,b₂⟩⟩; rfl
  right_inv := by rintro ⟨⟨a₁,b₁⟩,⟨a₂,b₂⟩⟩; rfl
noncomputable instance prodHasAntidiagonal [AddCommMonoid A] [AddCommMonoid B]
    [Finset.HasAntidiagonal A] [Finset.HasAntidiagonal B] :
    Finset.HasAntidiagonal (A × B) where
  antidiagonal n := (Finset.antidiagonal n.1 ×ˢ Finset.antidiagonal n.2).map
    (prodAntidiagonalEquiv (A := A) (B := B)).toEmbedding
  mem_antidiagonal := by
    classical
    rintro ⟨a,b⟩ ⟨⟨a₁,b₁⟩,⟨a₂,b₂⟩⟩
    simp [prodAntidiagonalEquiv, Prod.ext_iff]
end ProductAntidiagonal
namespace L1Coeff
variable {I J : Type*}
noncomputable def embedFun (e : I ↪ J) (f : L1Coeff I) (j : J) : ℂ := by
  classical
  exact if h : ∃ i, e i = j then f h.choose else 0
@[simp] lemma embedFun_apply_self (e : I ↪ J) (f : L1Coeff I) (i : I) :
    embedFun e f (e i) = f i := by
  classical
  let h : ∃ k, e k = e i := ⟨i, rfl⟩
  rw [embedFun, dif_pos h]
  have hk : e h.choose = e i := h.choose_spec
  rw [e.injective hk]
lemma embedFun_apply_of_not_mem (e : I ↪ J) (f : L1Coeff I) (j : J)
    (hj : j ∉ Set.range e) : embedFun e f j = 0 := by
  classical
  rw [embedFun, dif_neg]
  simpa only [Set.mem_range] using hj
def embed (e : I ↪ J) (f : L1Coeff I) : L1Coeff J :=
  ⟨embedFun e f, by
    classical
    apply memℓp_gen
    apply (Function.Injective.summable_iff e.injective (fun j hj ↦ ?_)).mp
    · simpa [Function.comp_def] using L1Coeff.summable_norm f
    · simp [embedFun_apply_of_not_mem e f j hj]⟩
@[simp] lemma embed_apply_self (e : I ↪ J) (f : L1Coeff I) (i : I) :
    embed e f (e i) = f i := embedFun_apply_self e f i
end L1Coeff
section WShift
variable {A : Type*}
def lowIndex (d : ℕ) : A × ℕ ↪ A × ℕ where
  toFun x := (x.1, x.2 + d)
  inj' := by
    rintro ⟨a,n⟩ ⟨b,m⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨h.1, Nat.add_right_cancel h.2⟩
def lowShift (d : ℕ) (f : L1Coeff (A × ℕ)) : L1Coeff (A × ℕ) :=
  L1Coeff.embed (lowIndex (A := A) d) f
@[simp] lemma lowShift_apply_add (d : ℕ) (f : L1Coeff (A × ℕ)) (a : A) (n : ℕ) :
    lowShift d f (a, n + d) = f (a,n) := by
  exact L1Coeff.embed_apply_self (lowIndex (A := A) d) f (a,n)
@[simp] lemma highShift_lowShift (d : ℕ) (f : L1Coeff (A × ℕ)) :
    highShift d (lowShift d f) = f := by
  apply lp.ext
  funext x
  rcases x with ⟨a,n⟩
  simp
@[simp] lemma highShift_lowCut (d : ℕ) (f : L1Coeff (A × ℕ)) :
    highShift d (lowCut d f) = 0 := by
  apply lp.ext
  funext x
  rcases x with ⟨a,n⟩
  rw [highShift_apply]
  rw [lowCut_apply_of_le d f a (by omega)]
  rfl
end WShift
section Division
variable {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]
lemma convolution_comm (f g : L1Coeff A) : convolution f g = convolution g f := by
  apply lp.ext
  funext n
  rw [convolution_apply, convolution_apply]
  refine Finset.sum_bij (fun kl _ ↦ kl.swap) ?_ ?_ ?_ ?_
  · intro kl hkl
    simpa [add_comm] using hkl
  · intro kl₁ h₁ kl₂ h₂ h
    exact Prod.swap_injective h
  · intro kl hkl
    exact ⟨kl.swap, by simpa [add_comm] using hkl, by simp⟩
  · intro kl hkl
    simp [mul_comm]
lemma convolution_add_right (f g₁ g₂ : L1Coeff A) :
    convolution f (g₁ + g₂) = convolution f g₁ + convolution f g₂ := by
  rw [convolution_comm f, convolution_add_left, convolution_comm g₁, convolution_comm g₂]
lemma convolution_smul_right (c : ℂ) (f g : L1Coeff A) :
    convolution f (c • g) = c • convolution f g := by
  rw [convolution_comm f, convolution_smul_left, convolution_comm g]
def convolutionRightMap :
    L1Coeff A →L[ℂ] (L1Coeff A →L[ℂ] L1Coeff A) :=
  ({
    toFun := convolutionRight
    map_add' := by
      intro p₁ p₂
      apply ContinuousLinearMap.ext
      intro q
      exact convolution_add_right q p₁ p₂
    map_smul' := by
      intro c p
      apply ContinuousLinearMap.ext
      intro q
      exact convolution_smul_right c q p
    } : L1Coeff A →ₗ[ℂ]
      (L1Coeff A →L[ℂ] L1Coeff A)).mkContinuous 1 (by
        intro p
        simpa using norm_convolutionRight_le p)
@[simp] lemma convolutionRightMap_apply (p : L1Coeff A) :
    convolutionRightMap p = convolutionRight p := rfl
def divisionPerturbation (d : ℕ) (p : L1Coeff (A × ℕ)) :
    L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ) :=
  highShiftCLM d ∘L convolutionRight p
@[simp] lemma divisionPerturbation_apply (d : ℕ) (p q : L1Coeff (A × ℕ)) :
    divisionPerturbation d p q = highShift d (convolution q p) := rfl
theorem norm_divisionPerturbation_le (d : ℕ) (p : L1Coeff (A × ℕ)) :
    ‖divisionPerturbation d p‖ ≤ ‖p‖ := by
  calc
    ‖divisionPerturbation d p‖ ≤ ‖highShiftCLM (A := A) d‖ * ‖convolutionRight p‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖p‖ := mul_le_mul (norm_highShiftCLM_le d) (norm_convolutionRight_le p)
      (norm_nonneg _) zero_le_one
    _ = ‖p‖ := one_mul _
def divisionPerturbationMap (d : ℕ) :
    L1Coeff (A × ℕ) →L[ℂ] (L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ)) :=
  ({
    toFun := divisionPerturbation d
    map_add' := by
      intro p₁ p₂
      apply ContinuousLinearMap.ext
      intro q
      change highShift d (convolution q (p₁ + p₂)) =
        highShift d (convolution q p₁) + highShift d (convolution q p₂)
      rw [convolution_add_right, highShift_add]
    map_smul' := by
      intro c p
      apply ContinuousLinearMap.ext
      intro q
      change highShift d (convolution q (c • p)) = c • highShift d (convolution q p)
      rw [convolution_smul_right, highShift_smul]
    } : L1Coeff (A × ℕ) →ₗ[ℂ]
      (L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ))).mkContinuous 1 (by
        intro p
        simpa using norm_divisionPerturbation_le (A := A) d p)
@[simp] lemma divisionPerturbationMap_apply (d : ℕ) (p : L1Coeff (A × ℕ)) :
    divisionPerturbationMap d p = divisionPerturbation d p := rfl
lemma norm_neg_divisionPerturbation_lt_one (d : ℕ) (p : L1Coeff (A × ℕ))
    (hp : ‖p‖ < 1) : ‖-(divisionPerturbation d p)‖ < 1 := by
  rw [norm_neg]
  exact lt_of_le_of_lt (norm_divisionPerturbation_le d p) hp
noncomputable def divisionInverse (d : ℕ) (p : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1) :
    L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ) :=
  ↑((Units.oneSub (-(divisionPerturbation d p))
    (norm_neg_divisionPerturbation_lt_one d p hp))⁻¹)
noncomputable def divisionQuotient (d : ℕ) (p : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1)
    (f : L1Coeff (A × ℕ)) : L1Coeff (A × ℕ) :=
  divisionInverse d p hp (highShift d f)
noncomputable def divisionQuotientGlobal (d : ℕ)
    (pf : L1Coeff (A × ℕ) × L1Coeff (A × ℕ)) : L1Coeff (A × ℕ) :=
  Ring.inverse (1 + divisionPerturbation d pf.1) (highShift d pf.2)
def divisionOperatorInput (d : ℕ) :
    (L1Coeff (A × ℕ) × L1Coeff (A × ℕ)) →L[ℂ]
      (L1Coeff (A × ℕ) →L[ℂ] L1Coeff (A × ℕ)) :=
  divisionPerturbationMap d ∘L
    ContinuousLinearMap.fst ℂ (L1Coeff (A × ℕ)) (L1Coeff (A × ℕ))
def divisionRhsInput (d : ℕ) :
    (L1Coeff (A × ℕ) × L1Coeff (A × ℕ)) →L[ℂ] L1Coeff (A × ℕ) :=
  highShiftCLM d ∘L
    ContinuousLinearMap.snd ℂ (L1Coeff (A × ℕ)) (L1Coeff (A × ℕ))
@[simp] lemma divisionOperatorInput_apply (d : ℕ)
    (pf : L1Coeff (A × ℕ) × L1Coeff (A × ℕ)) :
    divisionOperatorInput d pf = divisionPerturbation d pf.1 := rfl
omit [AddCommMonoid A] [Finset.HasAntidiagonal A] in
@[simp] lemma divisionRhsInput_apply (d : ℕ)
    (pf : L1Coeff (A × ℕ) × L1Coeff (A × ℕ)) :
    divisionRhsInput d pf = highShift d pf.2 := rfl
noncomputable def divisionRemainder (d : ℕ) (p : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1)
    (f : L1Coeff (A × ℕ)) : L1Coeff (A × ℕ) :=
  lowCut d (f - convolution (divisionQuotient d p hp f) p)
@[simp] theorem highShift_divisionRemainder (d : ℕ) (p : L1Coeff (A × ℕ))
    (hp : ‖p‖ < 1) (f : L1Coeff (A × ℕ)) :
    highShift d (divisionRemainder d p hp f) = 0 := by
  exact highShift_lowCut d _
end Division
section NatDivision
def seqHighShift (d : ℕ) (f : L1Coeff ℕ) : L1Coeff ℕ :=
  ⟨fun n ↦ f (n + d), by
    apply memℓp_gen
    simpa [Function.comp_def] using
      (L1Coeff.summable_norm f).comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)⟩
@[simp] lemma seqHighShift_apply (d : ℕ) (f : L1Coeff ℕ) (n : ℕ) :
    seqHighShift d f n = f (n + d) := rfl
theorem norm_seqHighShift_le (d : ℕ) (f : L1Coeff ℕ) : ‖seqHighShift d f‖ ≤ ‖f‖ := by
  rw [L1Coeff.norm_eq_tsum_norm, L1Coeff.norm_eq_tsum_norm]
  apply (L1Coeff.summable_norm (seqHighShift d f)).tsum_le_tsum_of_inj (fun n ↦ n + d)
    (fun _ _ h ↦ Nat.add_right_cancel h)
  · intro n hn
    exact norm_nonneg _
  · intro n
    exact le_rfl
  · exact L1Coeff.summable_norm f
lemma seqHighShift_add (d : ℕ) (f g : L1Coeff ℕ) :
    seqHighShift d (f + g) = seqHighShift d f + seqHighShift d g := by
  apply lp.ext
  funext n
  rfl
lemma seqHighShift_smul (d : ℕ) (c : ℂ) (f : L1Coeff ℕ) :
    seqHighShift d (c • f) = c • seqHighShift d f := by
  apply lp.ext
  funext n
  rfl
def seqHighShiftCLM (d : ℕ) : L1Coeff ℕ →L[ℂ] L1Coeff ℕ :=
  ({
    toFun := seqHighShift d
    map_add' := seqHighShift_add d
    map_smul' := seqHighShift_smul d
    } : L1Coeff ℕ →ₗ[ℂ] L1Coeff ℕ).mkContinuous 1 (by
      intro f
      simpa using norm_seqHighShift_le d f)
def seqLowIndex (d : ℕ) : ℕ ↪ ℕ where
  toFun n := n + d
  inj' := fun _ _ h ↦ Nat.add_right_cancel h
def seqLowShift (d : ℕ) (f : L1Coeff ℕ) : L1Coeff ℕ :=
  L1Coeff.embed (seqLowIndex d) f
@[simp] lemma seqLowShift_apply_add (d : ℕ) (f : L1Coeff ℕ) (n : ℕ) :
    seqLowShift d f (n + d) = f n := L1Coeff.embed_apply_self (seqLowIndex d) f n
def seqLowCut (d : ℕ) (f : L1Coeff ℕ) : L1Coeff ℕ :=
  ⟨fun n ↦ if n < d then f n else 0, by
    apply memℓp_gen
    simpa using (L1Coeff.summable_norm f).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (fun n ↦ by split_ifs <;> simp)⟩
@[simp] lemma seqLowCut_apply_of_lt (d : ℕ) (f : L1Coeff ℕ) {n : ℕ} (hn : n < d) :
    seqLowCut d f n = f n := by simp [seqLowCut, hn]
@[simp] lemma seqLowCut_apply_of_le (d : ℕ) (f : L1Coeff ℕ) {n : ℕ} (hn : d ≤ n) :
    seqLowCut d f n = 0 := by simp [seqLowCut, Nat.not_lt.mpr hn]
theorem norm_seqLowCut_le (d : ℕ) (f : L1Coeff ℕ) : ‖seqLowCut d f‖ ≤ ‖f‖ := by
  rw [L1Coeff.norm_eq_tsum_norm, L1Coeff.norm_eq_tsum_norm]
  apply (L1Coeff.summable_norm (seqLowCut d f)).tsum_le_tsum
  · intro n
    change ‖if n < d then f n else 0‖ ≤ ‖f n‖
    split_ifs <;> simp
  · exact L1Coeff.summable_norm f
lemma seqLowCut_add (d : ℕ) (f g : L1Coeff ℕ) :
    seqLowCut d (f + g) = seqLowCut d f + seqLowCut d g := by
  apply lp.ext
  funext n
  simp only [seqLowCut, lp.coeFn_add, Pi.add_apply]
  split_ifs <;> simp
lemma seqLowCut_smul (d : ℕ) (c : ℂ) (f : L1Coeff ℕ) :
    seqLowCut d (c • f) = c • seqLowCut d f := by
  apply lp.ext
  funext n
  simp only [seqLowCut, lp.coeFn_smul, Pi.smul_apply]
  split_ifs <;> simp
def seqLowCutCLM (d : ℕ) : L1Coeff ℕ →L[ℂ] L1Coeff ℕ :=
  ({
    toFun := seqLowCut d
    map_add' := seqLowCut_add d
    map_smul' := seqLowCut_smul d
    } : L1Coeff ℕ →ₗ[ℂ] L1Coeff ℕ).mkContinuous 1 (by
      intro f
      simpa using norm_seqLowCut_le d f)
@[simp] theorem seqHighShift_seqLowShift (d : ℕ) (f : L1Coeff ℕ) :
    seqHighShift d (seqLowShift d f) = f := by
  apply lp.ext
  funext n
  simp
@[simp] theorem seqHighShift_seqLowCut (d : ℕ) (f : L1Coeff ℕ) :
    seqHighShift d (seqLowCut d f) = 0 := by
  apply lp.ext
  funext n
  rw [seqHighShift_apply, seqLowCut_apply_of_le d f (by omega)]
  rfl
def seqDivisionPerturbation (d : ℕ) (p : L1Coeff ℕ) : L1Coeff ℕ →L[ℂ] L1Coeff ℕ :=
  seqHighShiftCLM d ∘L convolutionRight p
@[simp] lemma seqDivisionPerturbation_apply (d : ℕ) (p q : L1Coeff ℕ) :
    seqDivisionPerturbation d p q = seqHighShift d (convolution q p) := rfl
theorem norm_seqDivisionPerturbation_le (d : ℕ) (p : L1Coeff ℕ) :
    ‖seqDivisionPerturbation d p‖ ≤ ‖p‖ := by
  calc
    ‖seqDivisionPerturbation d p‖ ≤ ‖seqHighShiftCLM d‖ * ‖convolutionRight p‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖p‖ := by
      apply mul_le_mul
      · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro f
        change ‖seqHighShift d f‖ ≤ 1 * ‖f‖
        simpa using norm_seqHighShift_le d f
      · exact norm_convolutionRight_le p
      · exact norm_nonneg _
      · exact zero_le_one
    _ = ‖p‖ := one_mul _
def seqDivisionPerturbationMap (d : ℕ) :
    L1Coeff ℕ →L[ℂ] (L1Coeff ℕ →L[ℂ] L1Coeff ℕ) :=
  ({
    toFun := seqDivisionPerturbation d
    map_add' := by
      intro p₁ p₂
      apply ContinuousLinearMap.ext
      intro q
      change seqHighShift d (convolution q (p₁ + p₂)) =
        seqHighShift d (convolution q p₁) + seqHighShift d (convolution q p₂)
      rw [convolution_add_right, seqHighShift_add]
    map_smul' := by
      intro c p
      apply ContinuousLinearMap.ext
      intro q
      change seqHighShift d (convolution q (c • p)) = c • seqHighShift d (convolution q p)
      rw [convolution_smul_right, seqHighShift_smul]
    } : L1Coeff ℕ →ₗ[ℂ] (L1Coeff ℕ →L[ℂ] L1Coeff ℕ)).mkContinuous 1 (by
      intro p
      simpa using norm_seqDivisionPerturbation_le d p)
lemma norm_neg_seqDivisionPerturbation_lt_one (d : ℕ) (p : L1Coeff ℕ)
    (hp : ‖p‖ < 1) : ‖-(seqDivisionPerturbation d p)‖ < 1 := by
  rw [norm_neg]
  exact lt_of_le_of_lt (norm_seqDivisionPerturbation_le d p) hp
noncomputable def seqDivisionInverse (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1) :
    L1Coeff ℕ →L[ℂ] L1Coeff ℕ :=
  ↑((Units.oneSub (-(seqDivisionPerturbation d p))
    (norm_neg_seqDivisionPerturbation_lt_one d p hp))⁻¹)
noncomputable def seqDivisionQuotient (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (f : L1Coeff ℕ) : L1Coeff ℕ :=
  seqDivisionInverse d p hp (seqHighShift d f)
noncomputable def seqDivisionRemainder (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (f : L1Coeff ℕ) : L1Coeff ℕ :=
  seqLowCut d (f - convolution (seqDivisionQuotient d p hp f) p)
def seqDivisionOperatorInput (d : ℕ) :
    (L1Coeff ℕ × L1Coeff ℕ) →L[ℂ] (L1Coeff ℕ →L[ℂ] L1Coeff ℕ) :=
  seqDivisionPerturbationMap d ∘L
    ContinuousLinearMap.fst ℂ (L1Coeff ℕ) (L1Coeff ℕ)
def seqDivisionRhsInput (d : ℕ) :
    (L1Coeff ℕ × L1Coeff ℕ) →L[ℂ] L1Coeff ℕ :=
  seqHighShiftCLM d ∘L ContinuousLinearMap.snd ℂ (L1Coeff ℕ) (L1Coeff ℕ)
noncomputable def seqDivisionQuotientGlobal (d : ℕ) (pf : L1Coeff ℕ × L1Coeff ℕ) :
    L1Coeff ℕ :=
  Ring.inverse (1 + seqDivisionOperatorInput d pf) (seqDivisionRhsInput d pf)
noncomputable def seqDivisionRemainderGlobal (d : ℕ) (pf : L1Coeff ℕ × L1Coeff ℕ) :
    L1Coeff ℕ :=
  seqLowCut d (pf.2 - convolution (seqDivisionQuotientGlobal d pf) pf.1)
end NatDivision
end ClassicalComplexWPT


