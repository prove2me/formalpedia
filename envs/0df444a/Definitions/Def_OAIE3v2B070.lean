-- Prove2me | Definitions.Def_OAIE3v2B070
-- name    : OAIE3v2B070
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:16:19.868217+00:00
-- url     : https://prove2.me/theorems/da9de09c-ed56-41e7-af6d-41d4d80d0c5f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 71 of 311
-- statement:
--   Definitions bundle 71 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B010`, `OAIE3v2B038`, `OAIE3v2B039`, `OAIE3v2B041`, `OAIE3v2B042`, `OAIE3v2B043` of this split.
--
--   Modules: `Estimates/AllocatedFiberCap.lean`, `Estimates/CoefficientFiberOrthogonality.lean`, `Estimates/DenseProductApproximation.lean`, `Estimates/EmptyLayerDetectionGeometry.lean`, `Estimates/MultiaffineBias.lean`, `Estimates/MultiaffineExpansion.lean`, `Estimates/PairedDiagonalApproximation.lean`, `Estimates/PartialComplexScaledQuadrature.lean`, `Estimates/PrincipalCoefficientMarginal.lean`, `Estimates/ProductDifferenceBias.lean`, `Estimates/RationalRowReduction.lean`, `Fourier/AllocatedMaskedCoefficientFourier.lean`, `Fourier/BoxDifferenceCharacter.lean`, `Fourier/CoefficientResidualCharacter.lean`, `Geometry/BoxCornerMean.lean`, `Geometry/BoxDifferenceHom.lean`, `Geometry/IntervalBoxDifference.lean`, `Geometry/MixedRealCoordinates.lean`, `Lattices/AffineCoefficientSubspace.lean`, `Lattices/NearIntegerMultiples.lean`, `Lattices/SelectedResidueApproximation.lean`, `Lattices/SmoothResidueWindowMass.lean`, `Linear/AllocatedJointAmbientKernel.lean`, `Linear/CanonicalAmbientKernel.lean`, `Polynomial/AffinePhaseBias.lean`, `Polynomial/MultiaffinePhaseDifference.lean`, `Polynomial/PhasePreservingCauchySchwarz.lean`, `Polynomial/PolynomialRationalApproximationMono.lean`, `Polynomial/SitePhaseCauchySchwarz.lean`, `Probability/DenseProductDensity.lean`, `Probability/MixedDensityInterpolation.lean`, `Probability/ShiftedSmoothProductLaw.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B038
import Definitions.Def_OAIE3v2B039
import Definitions.Def_OAIE3v2B041
import Definitions.Def_OAIE3v2B042
import Definitions.Def_OAIE3v2B043

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalRowReduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem RationalHeightLE.sub {q r : ℚ} {H K : ℕ}
    (hq : RationalHeightLE q H) (hr : RationalHeightLE r K) :
    RationalHeightLE (q - r) (2 * H * K) := by
  simpa only [sub_eq_add_neg] using hq.add hr.neg

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J : Type*} [Fintype J]

noncomputable def rectangularWeightSum (f : (J → ℝ) → ℝ) (a S : J → ℝ) (R : ℝ) : ℝ :=
  ∑ k ∈ rectangularWeightIndices a S R, rectangularWeight f a S k

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem rectangularWeightIndices_card_le {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 1 ≤ S i) {R : ℝ} (hR : 0 ≤ R) :
    ((rectangularWeightIndices a S R).card : ℝ) ≤
      (2 * R + 1) ^ Fintype.card I * ∏ i, S i := by
  have hi (i : I) : ((sampledWeightIndices (a i) (S i) R).card : ℝ) ≤ (2 * R + 1) * S i := by
    apply (sampledWeightIndices_card_le _ _ _ (zero_le_one.trans (hS i)) hR).trans
    nlinarith [hS i]
  calc
    ((rectangularWeightIndices a S R).card : ℝ) =
        ∏ i, ((sampledWeightIndices (a i) (S i) R).card : ℝ) := by
      simp [rectangularWeightIndices]
    _ ≤ ∏ i, ((2 * R + 1) * S i) :=
      Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hi i)
    _ = _ := by simp [Finset.prod_mul_distrib]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem rectangularWeight_translation_pointwise {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (a S : I → ℝ) (v k : I → ℤ) :
    |rectangularWeight f a S (k - v) - rectangularWeight f a S k| ≤
      L * ‖rectangularLatticePoint 0 S v‖ := by
  have h := hf.norm_sub_le (rectangularLatticePoint a S (k - v)) (rectangularLatticePoint a S k)
  rw [rectangularLatticePoint_sub_displacement, norm_neg] at h
  exact h

theorem rectangularWeight_translation_l1 {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (a S : I → ℝ) (hS : ∀ i, 1 ≤ S i) {R : ℝ} (hR : 0 ≤ R)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (v : I → ℤ) :
    (∑' k, |rectangularWeight f a S (k - v) - rectangularWeight f a S k|) ≤
      2 * ((2 * R + 1) ^ Fintype.card I * ∏ i, S i) *
        (L * ‖rectangularLatticePoint 0 S v‖) := by
  have h := finiteSupport_translation_l1_bound (rectangularWeight f a S)
    (rectangularWeightIndices a S R)
    (rectangularWeight_zero_off_indices f a S (fun i => zero_lt_one.trans_le (hS i)) hsupport)
    v (mul_nonneg L.coe_nonneg (norm_nonneg _)) (rectangularWeight_translation_pointwise f hf a S v)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (rectangularWeightIndices_card_le a S hS hR) (by norm_num))
    (mul_nonneg L.coe_nonneg (norm_nonneg _)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffinePhaseBias
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace CircleFourier

theorem geometricCharacterMean_eq (N : ℕ) (x : Circle) :
    geometricCharacterMean N x = geometricCharacterSum N x / N := by
  rw [geometricCharacterMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin,
    geometricCharacterSum_eq_sum_fin]

theorem norm_geometricCharacterMean_le_one (N : ℕ) (hN : 0 < N) (x : Circle) :
    ‖geometricCharacterMean N x‖ ≤ 1 := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  calc
    ‖geometricCharacterMean N x‖ ≤ 𝔼 n : Fin N, ‖character ((n : ℕ) • x)‖ := RCLike.norm_expect_le (K := ℂ)
    _ = 1 := by simp

theorem integerDistance_le_of_geometric_mean {N : ℕ} (hN : 0 < N) (x : Circle)
    {δ : ℝ} (hδ : 0 < δ) (hbias : δ ≤ ‖geometricCharacterMean N x‖) :
    integerDistance x ≤ 1 / (2 * N * δ) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hnorm : ‖geometricCharacterMean N x‖ = ‖geometricCharacterSum N x‖ / N := by
    rw [geometricCharacterMean_eq, norm_div]
    simp
  have hprod := two_mul_integerDistance_mul_norm_geometricCharacterSum_le_one N x
  have hsmall : (N : ℝ) * δ ≤ ‖geometricCharacterSum N x‖ := by
    rw [hnorm, le_div_iff₀ hN'] at hbias
    simpa only [mul_comm] using hbias
  have h := (mul_le_mul_of_nonneg_left hsmall
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (integerDistance_nonneg x))).trans hprod
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * N * δ)).mpr
  nlinarith only [h]

end CircleFourier
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NearIntegerMultiples
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem nearIntegerDensity_of_geometric_mean {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) {M : ℕ} (hM : 0 < M) {a : ℝ} (ha : 0 < a)
    (hbias : a ≤ 𝔼 x, ‖geometricCharacterMean M (f x : CircleFourier.Circle)‖) :
    a/2 ≤ nearIntegerDensity f (1/((M : ℝ)*a)) := by
  obtain ⟨S, hS, hgood⟩ := exists_dense_level_set
    (fun x => ‖geometricCharacterMean M (f x : CircleFourier.Circle)‖) ha.le
    (fun x => norm_geometricCharacterMean_le_one M hM _) hbias
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  apply ((le_div_iff₀ hX).mpr hS).trans
  apply card_div_le_nearIntegerDensity _ _ S
  intro x hx
  have hnear := integerDistance_le_of_geometric_mean hM (f x : CircleFourier.Circle)
    (by linarith : 0 < a/2) (hgood x hx)
  refine ⟨round (f x), ?_⟩
  rw [← integerDistance_coe]
  apply hnear.trans_eq
  congr 1
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProductApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem dense_product_approximation (e B : ℕ) (hB : 1 ≤ B)
    {X : Fin e → Type*} [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (v : ∀ i, X i → ℤ) (hv : ∀ i, Function.Injective (v i)) (N : Fin e → ℕ)
    (hN : ∀ i, denseProductBudget e B ≤ N i)
    (hcard : ∀ i, N i ≤ Fintype.card (X i))
    (hbound : ∀ i x, |v i x| ≤ (N i : ℤ))
    {θ ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/(denseProductBudget e B : ℝ))
    (hdensity : 1/(B : ℝ) ≤
      nearIntegerDensity (fun x : ∀ i, X i => θ * ∏ i, (v i (x i) : ℝ)) ε) :
    ∃ q : ℕ, 0 < q ∧ q ≤ denseProductBudget e B ∧
      NearInteger ((denseProductBudget e B : ℝ)*ε / ∏ i, (N i : ℝ)) ((q : ℝ)*θ) := by
  induction e generalizing B θ ε with
  | zero =>
    have hBp : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hB)
    have hd : 0 < nearIntegerDensity (fun _ : ∀ i, X i => θ) ε := by
      simpa only [Fin.prod_univ_zero, mul_one] using
        (lt_of_lt_of_le (one_div_pos.mpr hBp) hdensity)
    refine ⟨1, by omega, le_rfl, ?_⟩
    simpa only [denseProductBudget, Nat.cast_one, one_mul, Fin.prod_univ_zero, div_one]
      using nearInteger_of_pos_density_const hd
  | succ e ih =>
    let C := denseProductBudget e (16*B^2)
    let K := denseProductBudget (e+1) B
    obtain ⟨h8, hCK, h256, h384, h8C⟩ := denseProductBudget_step_bounds e B hB
    have hB' : 1 ≤ 16*B^2 := by nlinarith
    have hCp : (0 : ℝ) < C := by exact_mod_cast denseProductBudget_pos e (16*B^2) hB'
    have hKp : (0 : ℝ) < K := by exact_mod_cast denseProductBudget_pos (e+1) B hB
    have hNp : ∀ i, (0 : ℝ) < N i := by
      intro i
      exact_mod_cast (lt_of_lt_of_le (denseProductBudget_pos (e+1) B hB) (hN i))
    have hN1 : (1 : ℝ) ≤ N 0 := by
      exact_mod_cast (lt_of_lt_of_le (denseProductBudget_pos (e+1) B hB) (hN 0))
    have hcoef : 384*(B : ℝ)^2*C ≤ K := by exact_mod_cast h384
    have hsmall' : ε ≤ 1/(256*(B : ℝ)^2) := by
      apply hsmall.trans
      apply one_div_le_one_div_of_le
      · have hBp : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hB)
        positivity
      · exact_mod_cast h256
    obtain ⟨q₀, hq₀, hq₀B, hd⟩ := dense_product_fiber (v 0) (hv 0)
      (fun y : ∀ i : Fin e, X i.succ => θ * ∏ i, (v i.succ (y i) : ℝ)) B (N 0) hB
      (h8.trans (hN 0)) (hcard 0) (hbound 0) hε hsmall'
      (by rwa [nearIntegerDensity_product_cons] at hdensity)
    let δ := 384*(B : ℝ)^2*ε/N 0
    have hδ : 0 ≤ δ := by dsimp [δ]; positivity
    have hδsmall : δ ≤ 1/(denseProductBudget e (16*B^2) : ℝ) :=
      dense_product_step_tolerance hCp hN1 hKp hcoef hε hsmall
    have hd' : 1/((16*B^2 : ℕ) : ℝ) ≤ nearIntegerDensity
        (fun y : ∀ i : Fin e, X i.succ => ((q₀ : ℝ)*θ) * ∏ i, (v i.succ (y i) : ℝ)) δ := by
      simpa only [δ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using hd
    obtain ⟨q₁, hq₁, hq₁C, hnear⟩ := ih (16*B^2) hB'
      (fun i => v i.succ) (fun i => hv i.succ) (fun i => N i.succ)
      (fun i => hCK.trans (hN i.succ)) (fun i => hcard i.succ)
      (fun i => hbound i.succ) hδ hδsmall hd'
    refine ⟨q₁*q₀, Nat.mul_pos hq₁ hq₀, ?_, ?_⟩
    · calc
        q₁*q₀ ≤ C*(8*B) := Nat.mul_le_mul hq₁C hq₀B
        _ = 8*B*C := by ring
        _ ≤ K := h8C
    · have hP : 0 < ∏ i : Fin e, (N i.succ : ℝ) :=
        Finset.prod_pos (fun i _ => hNp i.succ)
      have herror := dense_product_error_composition (hNp 0) hP hcoef hε
      have hresult := nearInteger_mono hnear herror
      simpa only [Nat.cast_mul, Fin.prod_univ_succ, mul_assoc] using hresult

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PhasePreservingCauchySchwarz
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_family_cauchy_schwarz_re {H Ω : Type*} [Fintype H] [Fintype Ω]
    [Nonempty Ω] (B : Ω → ℂ) (v : H → Ω → ℂ) {M : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) :
    ‖𝔼 x, B x * (𝔼 h, v h x)‖ ^ 2 ≤
      M ^ 2 * (𝔼 h, 𝔼 k, 𝔼 x, v h x * star (v k x)).re := by
  have hcs := norm_expect_mul_star_sq_le B (fun x => star (𝔼 h, v h x))
  simp only [star_star, norm_star] at hcs
  have hBM : (𝔼 x, ‖B x‖ ^ 2) ≤ M ^ 2 :=
    (Finset.expect_le_expect (fun x _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hB x) 2)).trans_eq (Fintype.expect_const _)
  rw [← mean_square_family_eq_cross_re]
  exact hcs.trans (mul_le_mul_of_nonneg_right hBM
    (Finset.expect_nonneg (fun x _ => sq_nonneg _)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxDifferenceHom
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem iterated_box_cauchy_schwarz (n : ℕ) {X : Fin n → Type*}
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    {Z : Type*} [Fintype Z] [Nonempty Z] (F : (∀ i, X i) → Z → ℂ) :
    ‖𝔼 x, 𝔼 z, F x z‖^(2^n) ≤
      𝔼 u, 𝔼 v, ‖𝔼 z, iteratedBoxDifference n F u v z‖ := by
  induction n with
  | zero => simp only [pow_zero, pow_one, expect_empty_tuple, iteratedBoxDifference, le_refl]
  | succ n ih =>
    let G := fun a b (x : ∀ i : Fin n, X i.succ) z =>
      F (Fin.cons a x) z * star (F (Fin.cons b x) z)
    have hcs : ‖𝔼 x, 𝔼 z, F x z‖^2 ≤
        𝔼 a : X 0, 𝔼 b : X 0, ‖𝔼 x : ∀ i : Fin n, X i.succ, 𝔼 z, G a b x z‖ := by
      rw [expect_dependent_fin_cons]
      have h := norm_mean_first_difference
        (fun (a : X 0) (p : (∀ i : Fin n, X i.succ) × Z) => F (Fin.cons a p.1) p.2)
      simpa only [expect_prod_split] using h
    calc
      _ = (‖𝔼 x, 𝔼 z, F x z‖^2)^(2^n) := by rw [← pow_mul, pow_succ]; congr 1; omega
      _ ≤ (𝔼 a : X 0, 𝔼 b : X 0,
          ‖𝔼 x : ∀ i : Fin n, X i.succ, 𝔼 z, G a b x z‖)^(2^n) :=
        pow_le_pow_left₀ (sq_nonneg _) hcs _
      _ ≤ 𝔼 a : X 0, 𝔼 b : X 0,
          ‖𝔼 x : ∀ i : Fin n, X i.succ, 𝔼 z, G a b x z‖^(2^n) :=
        expect_double_pow_two_pow_le n _ (fun _ _ => norm_nonneg _)
      _ ≤ 𝔼 a : X 0, 𝔼 b : X 0, 𝔼 u : ∀ i : Fin n, X i.succ,
          𝔼 v : ∀ i : Fin n, X i.succ, ‖𝔼 z, iteratedBoxDifference n (G a b) u v z‖ := by
        apply Finset.expect_le_expect
        intro a _
        apply Finset.expect_le_expect
        intro b _
        exact ih (G a b)
      _ = _ := by
        rw [expect_two_dependent_fin_cons]
        rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalCoefficientMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

variable {σ R W Z : Type*} [CommRing R] [AddCommGroup W] [Module R W]
  [AddCommGroup Z] [Module R Z]

theorem siteEvaluation_tmul {ι : Type*} (x : ι → σ → R) (P : MvPolynomial σ R) (w : W) :
    siteEvaluation x (P ⊗ₜ[R] w) = fun i => MvPolynomial.eval (x i) P • w := rfl

theorem curried_nonfactor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → σ → R) (Λ : VectorPolynomial σ R W →ₗ[R] R) (h : ℕ)
    (hn : ¬ ∃ M : (ι → W) →ₗ[R] R, ∀ p, Homogeneous h p → Λ p = M (siteEvaluation x p)) :
    ¬ ∃ L : (ι → R) →ₗ[R] (W →ₗ[R] R),
      ∀ P, P.IsHomogeneous h → TensorProduct.curry Λ P = L (fun i => MvPolynomial.eval (x i) P) := by
  rintro ⟨L, hL⟩
  apply hn
  refine ⟨siteFunctional L, ?_⟩
  intro p hp
  apply eq_of_homogeneous_tmul Λ ((siteFunctional L).comp (siteEvaluation x)) h _ hp
  intro P hP w
  have he := congrArg (fun F : W →ₗ[R] R => F w) (hL P hP)
  rw [TensorProduct.curry_apply] at he
  change Λ (P ⊗ₜ[R] w) = siteFunctional L (siteEvaluation x (P ⊗ₜ[R] w))
  rw [siteEvaluation_tmul, siteFunctional_tmul]
  exact he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {I R S W : Type*} [CommRing R] [CommRing S] [AddCommGroup W] [Module R W]

theorem coefficients_homogeneousPart (h : ℕ) (p : VectorPolynomial I R W) (d : I →₀ ℕ) :
    coefficients (homogeneousPart h p) d = if d.degree = h then coefficients p d else 0 := by
  classical
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul P w =>
    rw [homogeneousPart_tmul, coefficients_tmul, MvPolynomial.coeff_homogeneousComponent,
      coefficients_tmul]
    split <;> simp_all
  | add p q hp hq =>
    simp only [map_add, Finsupp.add_apply, hp, hq]
    split <;> simp

theorem homogeneousPart_homogeneous (h : ℕ) (p : VectorPolynomial I R W) :
    Homogeneous h (homogeneousPart h p) := by
  intro d hd
  simp only [coefficients_homogeneousPart, if_neg hd]

theorem sub_homogeneousPart_degreeLE {n : ℕ} {p : VectorPolynomial I R W}
    (hp : DegreeLE (1 : I → ℕ) (n + 1) p) :
    DegreeLE (1 : I → ℕ) n (p - homogeneousPart (n + 1) p) := by
  intro d hd
  have hd' : n < d.degree := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
  simp only [map_sub, Finsupp.sub_apply, coefficients_homogeneousPart]
  by_cases he : d.degree = n + 1
  · simp only [if_pos he, sub_self]
  · have hh : n + 1 < Finsupp.weight (1 : I → ℕ) d := by
      have hh' : n + 1 < d.degree := by omega
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hh'
    simp only [if_neg he, hp d hh, sub_zero]

theorem coordinate_homogeneousPart (f : W →+ S) (h : ℕ) (p : VectorPolynomial I R W) :
    coordinate f (homogeneousPart h p) = MvPolynomial.homogeneousComponent h (coordinate f p) := by
  classical
  ext d
  simp only [coeff_coordinate, coefficients_homogeneousPart, MvPolynomial.coeff_homogeneousComponent]
  split <;> simp

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BoxDifferenceCharacter
namespace OAI

section

namespace Erdos3

open CircleFourier

theorem iteratedBoxDifference_character (n : ℕ) {X : Fin n → Type*} {Z : Type*}
    (F : (∀ i, X i) → Z → ℝ) (u v : ∀ i, X i) (z : Z) :
    iteratedBoxDifference n (fun x t => character (F x t : CircleFourier.Circle)) u v z =
      character ((additiveBoxDifference n F u v z : ℝ) : CircleFourier.Circle) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iteratedBoxDifference, additiveBoxDifference, ← character_real_sub]
    exact ih _ (Fin.tail u) (Fin.tail v)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxCornerMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem missesBoxCoordinate_head {n : ℕ} {X : Type*}
    {U : (Fin (n + 1) → X) → ℂ} (hU : MissesBoxCoordinate U 0)
    (a b : X) (x : Fin n → X) : U (Fin.cons a x) = U (Fin.cons b x) := by
  simpa only [Fin.update_cons_zero] using hU (Fin.cons b x) a

noncomputable def boxTailPhase {n : ℕ} {X : Type*}
    (F : (Fin (n + 1) → X) → ℂ) (a b : X) (x : Fin n → X) : ℂ :=
  F (Fin.cons a x) * star (F (Fin.cons b x))

noncomputable def boxTailTests {n : ℕ} {X : Type*}
    (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ) (a b : X)
    (i : Fin n) (x : Fin n → X) : ℂ :=
  U i.succ (Fin.cons a x) * star (U i.succ (Fin.cons b x))

theorem boxTailTests_misses {n : ℕ} {X : Type*}
    (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ)
    (hU : ∀ i, MissesBoxCoordinate (U i) i) (a b : X) (i : Fin n) :
    MissesBoxCoordinate (boxTailTests U a b i) i := by
  intro x c
  simp only [boxTailTests, Fin.cons_update]
  rw [hU i.succ (Fin.cons a x) c, hU i.succ (Fin.cons b x) c]

theorem boxTailTests_norm {n : ℕ} {X : Type*}
    (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ)
    (hU : ∀ i x, ‖U i x‖ ≤ 1) (a b : X) (i : Fin n) (x : Fin n → X) :
    ‖boxTailTests U a b i x‖ ≤ 1 := by
  rw [boxTailTests, norm_mul, norm_star]
  exact (mul_le_mul (hU _ _) (hU _ _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

noncomputable def boxPhaseMoment {X : Type*} [Fintype X] (n : ℕ)
    (F : (Fin n → X) → ℂ) : ℂ :=
  𝔼 u, 𝔼 v, iteratedBoxDifference n (fun x (_ : Unit) => F x) u v ()

theorem boxPhaseMoment_zero {X : Type*} [Fintype X] (F : (Fin 0 → X) → ℂ) :
    boxPhaseMoment 0 F = F (fun i => Fin.elim0 i) := by
  simp only [boxPhaseMoment, iteratedBoxDifference, Fintype.expect_const]

theorem boxPhaseMoment_succ {X : Type*} [Fintype X] (n : ℕ)
    (F : (Fin (n + 1) → X) → ℂ) :
    boxPhaseMoment (n + 1) F = 𝔼 a, 𝔼 b, boxPhaseMoment n (boxTailPhase F a b) := by
  rw [boxPhaseMoment, expect_two_dependent_fin_cons]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def boxTailAmplitude {n : ℕ} {X : Type*}
    (F : (Fin (n + 1) → X) → ℂ) (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ)
    (a : X) (x : Fin n → X) : ℂ :=
  F (Fin.cons a x) * ∏ i : Fin n, U i.succ (Fin.cons a x)

theorem boxTailAmplitude_cross {n : ℕ} {X : Type*}
    (F : (Fin (n + 1) → X) → ℂ) (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ)
    (a b : X) (x : Fin n → X) :
    boxTailAmplitude F U a x * star (boxTailAmplitude F U b x) =
      boxTailPhase F a b x * ∏ i, boxTailTests U a b i x := by
  simp only [boxTailAmplitude, boxTailPhase, boxTailTests, star_mul, star_prod,
    Finset.prod_mul_distrib]
  ring

theorem boxTestCorrelation_head {n : ℕ} {X : Type*} [Fintype X]
    (F : (Fin (n + 1) → X) → ℂ) (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ)
    (hU : MissesBoxCoordinate (U 0) 0) (base : X) :
    boxTestCorrelation F U =
      𝔼 x : Fin n → X, U 0 (Fin.cons base x) * (𝔼 a, boxTailAmplitude F U a x) := by
  rw [boxTestCorrelation, expect_dependent_fin_cons, Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro x _
  rw [Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro a _
  rw [Fin.prod_univ_succ, missesBoxCoordinate_head hU a base x]
  unfold boxTailAmplitude
  ring

theorem boxTestCorrelation_square_le {n : ℕ} {X : Type*} [Fintype X] [Nonempty X]
    (F : (Fin (n + 1) → X) → ℂ) (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ)
    (hU : ∀ x, ‖U 0 x‖ ≤ 1) (hmiss : MissesBoxCoordinate (U 0) 0) :
    ‖boxTestCorrelation F U‖ ^ 2 ≤
      (𝔼 a, 𝔼 b, boxTestCorrelation (boxTailPhase F a b) (boxTailTests U a b)).re := by
  let base : X := Classical.choice inferInstance
  have h := finite_family_cauchy_schwarz_re
    (fun x : Fin n → X => U 0 (Fin.cons base x)) (boxTailAmplitude F U)
    (fun x => hU (Fin.cons base x))
  rw [← boxTestCorrelation_head F U hmiss base] at h
  simp only [one_pow, one_mul] at h
  simp_rw [boxTailAmplitude_cross] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem boxTest_cauchySchwarz {X : Type*} [Fintype X] [Nonempty X] (n : ℕ) :
    ∀ (F : (Fin (n + 1) → X) → ℂ) (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ),
      (∀ i x, ‖U i x‖ ≤ 1) → (∀ i, MissesBoxCoordinate (U i) i) →
      ‖boxTestCorrelation F U‖ ^ (2 ^ (n + 1)) ≤ (boxPhaseMoment (n + 1) F).re := by
  induction n with
  | zero =>
    intro F U hU hmiss
    simpa only [Nat.zero_add, pow_one, boxPhaseMoment_succ,
      boxPhaseMoment_zero, boxTestCorrelation_zero] using
      boxTestCorrelation_square_le F U (hU 0) (hmiss 0)
  | succ n ih =>
    intro F U hU hmiss
    have hr : (𝔼 a, 𝔼 b, boxTestCorrelation (boxTailPhase F a b) (boxTailTests U a b)).re ≤
        𝔼 a, 𝔼 b, ‖boxTestCorrelation (boxTailPhase F a b) (boxTailTests U a b)‖ := by
      simp only [expect_re]
      apply Finset.expect_le_expect
      intro a _
      apply Finset.expect_le_expect
      intro b _
      exact Complex.re_le_norm _
    have hcs := (boxTestCorrelation_square_le F U (hU 0) (hmiss 0)).trans hr
    calc
      _ = (‖boxTestCorrelation F U‖ ^ 2) ^ (2 ^ (n + 1)) := by
        rw [← pow_mul, pow_succ]
        congr 1
        omega
      _ ≤ (𝔼 a, 𝔼 b, ‖boxTestCorrelation (boxTailPhase F a b) (boxTailTests U a b)‖) ^
          (2 ^ (n + 1)) := pow_le_pow_left₀ (sq_nonneg _) hcs _
      _ ≤ 𝔼 a, 𝔼 b, ‖boxTestCorrelation (boxTailPhase F a b) (boxTailTests U a b)‖ ^
          (2 ^ (n + 1)) := expect_double_pow_two_pow_le (n + 1) _ (fun _ _ => norm_nonneg _)
      _ ≤ 𝔼 a, 𝔼 b, (boxPhaseMoment (n + 1) (boxTailPhase F a b)).re := by
        apply Finset.expect_le_expect
        intro a _
        apply Finset.expect_le_expect
        intro b _
        exact ih _ _ (boxTailTests_norm U hU a b) (boxTailTests_misses U hmiss a b)
      _ = _ := by rw [boxPhaseMoment_succ]; simp only [expect_re]

theorem boxTest_cauchySchwarz_of_pos {X : Type*} [Fintype X] [Nonempty X] {h : ℕ}
    (hh : 0 < h) (F : (Fin h → X) → ℂ) (U : Fin h → (Fin h → X) → ℂ)
    (hU : ∀ i x, ‖U i x‖ ≤ 1) (hmiss : ∀ i, MissesBoxCoordinate (U i) i) :
    ‖boxTestCorrelation F U‖ ^ (2 ^ h) ≤ (boxPhaseMoment h F).re := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hh)
  exact boxTest_cauchySchwarz n F U hU hmiss

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem assigned_site_cauchySchwarz {h : ℕ} {S X : Type*}
    [Fintype S] [Fintype X] [Nonempty X] (hh : 0 < h)
    (F : (Fin h → X) → ℂ) (assignment : S → Fin h)
    (U : S → (Fin h → X) → ℂ) (hU : ∀ s x, ‖U s x‖ ≤ 1)
    (hmiss : ∀ s, MissesBoxCoordinate (U s) (assignment s)) :
    ‖𝔼 x, F x * ∏ s, U s x‖ ^ (2 ^ h) ≤ (boxPhaseMoment h F).re := by
  have hc := boxTest_cauchySchwarz_of_pos hh F (assignedBoxTest assignment U)
    (assignedBoxTest_norm assignment U hU) (assignedBoxTest_misses assignment U hmiss)
  simpa only [boxTestCorrelation, assignedBoxTest_prod] using hc

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SitePhaseCauchySchwarz
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem boxPhaseMoment_character {X : Type*} [Fintype X] (h : ℕ)
    (P : (Fin h → X) → ℝ) :
    boxPhaseMoment h (fun x => character (P x : CircleFourier.Circle)) =
      𝔼 u, 𝔼 v, character
        ((additiveBoxDifference h (fun x (_ : Unit) => P x) u v () : ℝ) : CircleFourier.Circle) := by
  unfold boxPhaseMoment
  simp_rw [iteratedBoxDifference_character]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DenseProductDensity
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem dense_product_approximation_density (e : ℕ)
    {X : Fin e → Type*} [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (v : ∀ i, X i → ℤ) (hv : ∀ i, Function.Injective (v i)) (N : Fin e → ℕ)
    {η θ ε : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hN : ∀ i, denseProductDensityBudget e η ≤ N i)
    (hcard : ∀ i, N i ≤ Fintype.card (X i))
    (hbound : ∀ i x, |v i x| ≤ (N i : ℤ))
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1/denseProductDensityBudget e η)
    (hdensity : η ≤ nearIntegerDensity
      (fun x : ∀ i, X i => θ * ∏ i, (v i (x i) : ℝ)) ε) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ denseProductDensityBudget e η ∧
      NearInteger (denseProductDensityBudget e η*ε / ∏ i, (N i : ℝ)) ((q : ℝ)*θ) := by
  obtain ⟨hB, hBη, _⟩ := reciprocal_density_ceil hη hη1
  have hKB := denseProductBudget_ceil_le e hη hη1
  have hKN : ∀ i, denseProductBudget e ⌈1/η⌉₊ ≤ N i := by
    intro i
    exact_mod_cast hKB.trans (hN i)
  have hKp : (0 : ℝ) < denseProductBudget e ⌈1/η⌉₊ := by
    exact_mod_cast denseProductBudget_pos e ⌈1/η⌉₊ hB
  have hsmall' : ε ≤ 1/(denseProductBudget e ⌈1/η⌉₊ : ℝ) :=
    hsmall.trans (one_div_le_one_div_of_le hKp hKB)
  obtain ⟨q, hq, hqK, hnear⟩ := dense_product_approximation e ⌈1/η⌉₊ hB
    v hv N hKN hcard hbound hε hsmall' (hBη.trans hdensity)
  refine ⟨q, hq, (Nat.cast_le.mpr hqK).trans hKB, nearInteger_mono hnear ?_⟩
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKB hε)
    (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (N i)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.IntervalBoxDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem dense_product_signed_box (e : ℕ) (N : Fin e → ℕ)
    {η θ ε : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hN : ∀ i, denseProductDensityBudget e η ≤ N i)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1/denseProductDensityBudget e η)
    (hdensity : η ≤ nearIntegerDensity
      (fun x : ∀ i, SymmetricIntegerInterval (N i) => θ * ∏ i, ((x i : ℤ) : ℝ)) ε) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ denseProductDensityBudget e η ∧
      NearInteger (denseProductDensityBudget e η*ε / ∏ i, (N i : ℝ)) ((q : ℝ)*θ) := by
  apply dense_product_approximation_density e (X := fun i => SymmetricIntegerInterval (N i))
    (fun _ x => (x : ℤ))
    (fun _ => Subtype.val_injective) N hη hη1 hN
  · intro i
    rw [symmetricIntegerInterval_card]
    omega
  · exact fun i => symmetricIntegerInterval_abs_le (N i)
  · exact hε
  · exact hsmall
  · exact hdensity

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem intervalBox_card_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) (hN : ∀ i, 0 < N i) :
    (1 : ℝ)/3^Fintype.card ι ≤
      (Fintype.card (∀ i, Fin (N i)) : ℝ) /
        Fintype.card (∀ i, SymmetricIntegerInterval (N i)) := by
  have hden : (0 : ℝ) < Fintype.card (∀ i, SymmetricIntegerInterval (N i)) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_div_iff₀ (by positivity) hden).mpr
  simp only [Fintype.card_pi, Fintype.card_fin, symmetricIntegerInterval_card,
    Nat.cast_prod, one_mul]
  calc
    (∏ i, ((2*N i+1 : ℕ) : ℝ)) ≤ ∏ i, (N i : ℝ)*3 := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        have hi : (1 : ℝ) ≤ N i := by exact_mod_cast hN i
        push_cast
        linarith
    _ = (∏ i, (N i : ℝ))*3^Fintype.card ι := by
      rw [Finset.prod_mul_distrib]
      simp

theorem nearIntegerDensity_interval_differences {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) (hN : ∀ i, 0 < N i)
    (a : (∀ i, SymmetricIntegerInterval (N i)) → ℝ) (ε : ℝ)
    {η : ℝ} (hη : 0 ≤ η)
    (hdensity : η ≤ 𝔼 y : ∀ i, Fin (N i),
      nearIntegerDensity (fun x => a (intervalBoxDifference N y x)) ε) :
    η/3^Fintype.card ι ≤ nearIntegerDensity a ε := by
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hN i⟩⟩
  have hd := nearIntegerDensity_fiber_injections a ε (intervalBoxDifference N)
    (intervalBoxDifference_injective N) hdensity
  have hr := mul_le_mul_of_nonneg_left (intervalBox_card_ratio N hN) hη
  apply (le_trans ?_ hd)
  simpa only [← mul_div_assoc, mul_one] using hr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductDifferenceBias
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem product_difference_bias_approximation (e : ℕ) (N : Fin e → ℕ) (M : ℕ)
    (hM : 0 < M) {a θ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hN : ∀ i, denseProductDensityBudget e (a/(2*3^e)) ≤ N i)
    (hMlarge : denseProductDensityBudget e (a/(2*3^e)) ≤ (M : ℝ)*a)
    (hbias : a ≤ 𝔼 y : (∀ i : Fin e, Fin (N i)), 𝔼 x : (∀ i : Fin e, Fin (N i)),
      ‖geometricCharacterMean M
        ((θ * (∏ i : Fin e, (((x i).val : ℝ)-((y i).val : ℝ))) : ℝ) : CircleFourier.Circle)‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ denseProductDensityBudget e (a/(2*3^e)) ∧
      NearInteger
        (denseProductDensityBudget e (a/(2*3^e))/((M : ℝ)*a*∏ i, (N i : ℝ)))
        ((q : ℝ)*θ) := by
  let η := a/(2*3^e)
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    have hp : (1 : ℝ) ≤ 3^e := one_le_pow₀ (by norm_num)
    apply (div_le_one (by positivity : (0 : ℝ) < 2*3^e)).mpr
    linarith
  have hNp : ∀ i, 0 < N i := by
    intro i
    have h := (denseProductDensityBudget_pos e hη).trans_le (hN i)
    exact_mod_cast h
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hNp i⟩⟩
  let f := fun (y x : ∀ i, Fin (N i)) =>
    θ * (∏ i : Fin e, (((x i).val : ℝ)-((y i).val : ℝ)))
  have hsplit : (𝔼 p : (∀ i, Fin (N i)) × (∀ i, Fin (N i)),
      ‖geometricCharacterMean M (f p.1 p.2 : CircleFourier.Circle)‖) =
      𝔼 y, 𝔼 x, ‖geometricCharacterMean M (f y x : CircleFourier.Circle)‖ := by
    simpa using (Finset.expect_product' Finset.univ Finset.univ
      (fun y x => ‖geometricCharacterMean M (f y x : CircleFourier.Circle)‖))
  have hpair := nearIntegerDensity_of_geometric_mean
    (fun p : (∀ i, Fin (N i)) × (∀ i, Fin (N i)) => f p.1 p.2) hM ha
    (hbias.trans_eq hsplit.symm)
  rw [nearIntegerDensity_product f] at hpair
  have hdiff : a/2/3^e ≤ nearIntegerDensity
      (fun x : ∀ i, SymmetricIntegerInterval (N i) => θ * ∏ i, ((x i : ℤ) : ℝ))
      (1/((M : ℝ)*a)) := by
    simpa only [Fintype.card_fin] using nearIntegerDensity_interval_differences N hNp
      (fun x => θ * ∏ i, ((x i : ℤ) : ℝ)) (1/((M : ℝ)*a)) (by positivity : 0 ≤ a/2)
      (by simpa only [f, intervalBoxDifference, intervalDifference, Int.cast_sub,
        Int.cast_natCast] using hpair)
  have hsmall : 1/((M : ℝ)*a) ≤ 1/denseProductDensityBudget e η :=
    one_div_le_one_div_of_le (denseProductDensityBudget_pos e hη) hMlarge
  obtain ⟨q, hq, hqB, hnear⟩ := dense_product_signed_box e N hη hη1 hN
    (by positivity : 0 ≤ 1/((M : ℝ)*a)) hsmall
    (by simpa only [η, div_div] using hdiff)
  refine ⟨q, hq, hqB, ?_⟩
  convert hnear using 1
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultiaffineExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem multiaffineExpansion_box_difference {R Z : Type*} [CommRing R]
    (n : ℕ) {X : Fin n → Type*} (c : Finset (Fin n) → Z → R)
    (f : ∀ i, X i → R) (u v : ∀ i, X i) (z : Z) :
    additiveBoxDifference n
      (fun x t => multiaffineExpansion (fun S => c S t) (fun i => f i (x i))) u v z =
      c Finset.univ z * ∏ i, (f i (u i)-f i (v i)) := by
  unfold multiaffineExpansion
  rw [additiveBoxDifference_sum]
  have hprod (S : Finset (Fin n)) :
      additiveBoxDifference n (fun x t => c S t * ∏ i, if i ∈ S then f i (x i) else 1) u v z =
        c S z * ∏ i, ((if i ∈ S then f i (u i) else 1)-(if i ∈ S then f i (v i) else 1)) :=
    additiveBoxDifference_product n (c S) (fun i x => if i ∈ S then f i x else 1) u v z
  simp_rw [hprod]
  rw [Finset.sum_eq_single (Finset.univ : Finset (Fin n))]
  · simp
  · intro S _ hS
    have hmissing : ∃ i, i ∉ S := by
      by_contra h
      apply hS
      apply Finset.eq_univ_of_forall
      intro i
      by_contra hi
      exact h ⟨i,hi⟩
    obtain ⟨i,hi⟩ := hmissing
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    · exact mul_zero _
    · simp only [hi, ite_false, sub_self]
  · simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MultiaffinePhaseDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem norm_affine_fin_phase_mean (M : ℕ) (a b : ℝ) :
    ‖𝔼 t : Fin M, character ((a*(t.val : ℝ)+b : ℝ) : CircleFourier.Circle)‖ =
      ‖geometricCharacterMean M (a : CircleFourier.Circle)‖ := by
  have he (t : Fin M) :
      character ((a*(t.val : ℝ)+b : ℝ) : CircleFourier.Circle) =
        character (b : CircleFourier.Circle) * character (t.val • (a : CircleFourier.Circle)) := by
    have hr : a*(t.val : ℝ)+b = b+t.val • a := by simp only [nsmul_eq_mul]; ring
    rw [hr, AddCircle.coe_add, AddCircle.coe_nsmul, character_add]
  simp_rw [he]
  rw [← Finset.mul_expect, norm_mul, norm_character, one_mul]
  rfl

theorem multiaffine_phase_difference_mean {n : ℕ} (N : Fin n → ℕ) (M : ℕ)
    (a b : Finset (Fin n) → ℝ) (u : Fin n → ℝ) (w : ℝ)
    (x y : ∀ i, Fin (N i)) :
    ‖𝔼 t : Fin M, iteratedBoxDifference n (multiaffineIntervalPhase a b u w) x y t‖ =
      ‖geometricCharacterMean M
        ((a Finset.univ * ∏ i, (((x i).val : ℝ)-((y i).val : ℝ)) : ℝ) : CircleFourier.Circle)‖ := by
  unfold multiaffineIntervalPhase
  simp_rw [iteratedBoxDifference_character,
    multiaffineExpansion_box_difference n
      (fun S (t : Fin M) => a S*(w+(t.val : ℝ))+b S)
      (fun i (j : Fin (N i)) => u i+(j.val : ℝ)), add_sub_add_left_eq_sub]
  let D := ∏ i, (((x i).val : ℝ)-((y i).val : ℝ))
  change ‖𝔼 t : Fin M,
    character (((a Finset.univ*(w+(t.val : ℝ))+b Finset.univ)*D : ℝ) : CircleFourier.Circle)‖ =
      ‖geometricCharacterMean M (a Finset.univ*D : CircleFourier.Circle)‖
  have he (t : Fin M) : (a Finset.univ*(w+(t.val : ℝ))+b Finset.univ)*D =
      (a Finset.univ*D)*(t.val : ℝ)+(a Finset.univ*w+b Finset.univ)*D := by ring
  simp_rw [he]
  exact norm_affine_fin_phase_mean M _ _

theorem multiaffine_phase_box_bias {n : ℕ} (N : Fin n → ℕ) (hN : ∀ i, 0 < N i)
    (M : ℕ) (hM : 0 < M) (a b : Finset (Fin n) → ℝ) (u : Fin n → ℝ) (w : ℝ)
    {ζ : ℝ} (hζ : 0 ≤ ζ)
    (hbias : ζ ≤ ‖𝔼 x : ∀ i, Fin (N i), 𝔼 t : Fin M, multiaffineIntervalPhase a b u w x t‖) :
    ζ^(2^n) ≤ 𝔼 y : (∀ i, Fin (N i)), 𝔼 x : (∀ i, Fin (N i)),
      ‖geometricCharacterMean M
        ((a Finset.univ * ∏ i, (((x i).val : ℝ)-((y i).val : ℝ)) : ℝ) : CircleFourier.Circle)‖ := by
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hN i⟩⟩
  let : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  have h := (pow_le_pow_left₀ hζ hbias (2^n)).trans
    (iterated_box_cauchy_schwarz n (multiaffineIntervalPhase a b u w))
  simp_rw [multiaffine_phase_difference_mean] at h
  rwa [Finset.expect_comm] at h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultiaffineBias
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem multiaffine_bias_approximation {n : ℕ} (N : Fin n → ℕ) (M : ℕ)
    (a b : Finset (Fin n) → ℝ) (u : Fin n → ℝ) (w : ℝ)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hN : ∀ i, multiaffineBiasBudget n ζ ≤ N i)
    (hM : multiaffineBiasBudget n ζ ≤ M)
    (hbias : ζ ≤ ‖𝔼 x : ∀ i, Fin (N i), 𝔼 t : Fin M,
      multiaffineIntervalPhase a b u w x t‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ multiaffineBiasBudget n ζ ∧
      ∃ m : ℤ, |a Finset.univ-(m : ℝ)/q| ≤
        multiaffineBiasBudget n ζ / ((M : ℝ)*∏ i, (N i : ℝ)) := by
  have hQ := multiaffineBiasBudget_pos n hζ
  have hNp : ∀ i, 0 < N i := fun i => by exact_mod_cast hQ.trans_le (hN i)
  have hMp : 0 < M := by exact_mod_cast hQ.trans_le hM
  have hp : 0 < ζ^(2^n) := pow_pos hζ _
  have hp1 : ζ^(2^n) ≤ 1 := pow_le_one₀ hζ.le hζ1
  obtain ⟨hLQ,hQmul⟩ := multiaffineBiasBudget_bounds n hζ hζ1
  have hMlarge : denseProductDensityBudget n (ζ^(2^n)/(2*3^n)) ≤ (M : ℝ)*ζ^(2^n) := by
    rw [← hQmul]
    exact mul_le_mul_of_nonneg_right hM hp.le
  obtain ⟨q,hq,hqL,hnear⟩ := product_difference_bias_approximation n N M hMp hp hp1
    (fun i => hLQ.trans (hN i)) hMlarge
    (multiaffine_phase_box_bias N hNp M hMp a b u w hζ.le hbias)
  refine ⟨q,hq,hqL.trans hLQ,nearInteger_rational_approximation hq ?_⟩
  convert hnear using 1
  unfold multiaffineBiasBudget
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedSmoothProductLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem shiftedSmoothProductPMF_toReal_sum {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) :
    (∑' x, (shiftedSmoothProductPMF a S hS hZ x).toReal) = 1 := by
  simp only [shiftedSmoothProductPMF_toReal, tsum_div_const]
  exact div_self hZ.ne'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PairedDiagonalApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem tensorDiagonalPolynomial_coeff_bound {I : Type*} [Fintype I] {h : ℕ}
    (θ : (Fin h → I) → ℝ) (T : I → ℝ) (hT : ∀ i, 0 < T i)
    {B : ℝ} (hB : 0 ≤ B) (hθ : ∀ j, |θ j| ≤ B / ∏ i, T (j i))
    (α : I →₀ ℕ) :
    |(tensorDiagonalPolynomial θ).coeff α| ≤
      (Fintype.card I : ℝ) ^ h * B / monomialScale T α := by
  rw [tensorDiagonalPolynomial_eq_sum_monomial]
  simp only [MvPolynomial.coeff_sum]
  have hj (j : Fin h → I) :
      |(MvPolynomial.monomial (productBlockExponent j) (θ j)).coeff α| ≤
        B / monomialScale T α := by
    by_cases he : productBlockExponent j = α
    · simpa [he, ← monomialScale_productBlockExponent j T] using hθ j
    · simp only [MvPolynomial.coeff_monomial, he, ite_false, abs_zero]
      exact div_nonneg hB (monomialScale_pos T hT α).le
  calc
    |∑ j : Fin h → I, (MvPolynomial.monomial (productBlockExponent j) (θ j)).coeff α| ≤
        ∑ j : Fin h → I, |(MvPolynomial.monomial (productBlockExponent j) (θ j)).coeff α| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin h → I, B / monomialScale T α := Finset.sum_le_sum (fun j _ => hj j)
    _ = _ := by simp [mul_div_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem tensorDiagonalPolynomial_rational_split {I : Type*} [Fintype I] {h : ℕ}
    (θ : (Fin h → I) → ℝ) (m : (Fin h → I) → ℤ) (D : ℕ) :
    tensorDiagonalPolynomial θ = tensorDiagonalPolynomial (fun j => θ j - (m j : ℝ) / D) +
      MvPolynomial.C (1 / (D : ℝ)) *
        MvPolynomial.map (Int.castRingHom ℝ) (tensorDiagonalPolynomial m) := by
  rw [tensorDiagonalPolynomial_map, ← tensorDiagonalPolynomial_mul, ← tensorDiagonalPolynomial_add]
  congr 1
  funext j
  simp only [Int.coe_castRingHom, div_eq_mul_inv]
  ring

theorem tensorDiagonalPolynomial_approximation {I : Type*} [Fintype I] {h : ℕ}
    (θ : (Fin h → I) → ℝ) (m : (Fin h → I) → ℤ) (D : ℕ)
    (T : I → ℝ) (hT : ∀ i, 0 < T i) {B : ℝ} (hB : 0 ≤ B)
    (hθ : ∀ j, |θ j - (m j : ℝ) / D| ≤ B / ∏ i, T (j i)) :
    ∃ E : MvPolynomial I ℝ, ∃ Q : MvPolynomial I ℤ,
      tensorDiagonalPolynomial θ = E + MvPolynomial.C (1 / (D : ℝ)) *
        MvPolynomial.map (Int.castRingHom ℝ) Q ∧
      ∀ α, |E.coeff α| ≤ (Fintype.card I : ℝ) ^ h * B / monomialScale T α := by
  exact ⟨tensorDiagonalPolynomial (fun j => θ j - (m j : ℝ) / D),
    tensorDiagonalPolynomial m, tensorDiagonalPolynomial_rational_split θ m D,
    tensorDiagonalPolynomial_coeff_bound _ T hT hB hθ⟩

theorem integerPolynomialQuotient_coeff {I : Type*} (D : ℕ) (Q : MvPolynomial I ℤ)
    (α : I →₀ ℕ) :
    (MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Q).coeff α =
      ((Q.coeff α : ℤ) : ℝ) / D := by
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  simp only [Int.coe_castRingHom, div_eq_mul_inv]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialRationalApproximationMono
namespace OAI

section

namespace Erdos3

theorem polynomialRationalApproximation_of_decomposition {I : Type*}
    (T : I → ℝ) (R : ℝ) (P E : MvPolynomial I ℝ) (Q : MvPolynomial I ℤ)
    (D : ℕ) (hD : 0 < D) (hDR : (D : ℝ) ≤ R)
    (hP : P = E + MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Q)
    (hE : ∀ α, |E.coeff α| ≤ R / monomialScale T α) :
    PolynomialRationalApproximation T R P := by
  refine ⟨D, hD, hDR, Q, ?_⟩
  intro α
  rw [hP, MvPolynomial.coeff_add,
    integerPolynomialQuotient_coeff, add_sub_cancel_right]
  exact hE α

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientSubspace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem dehomogenize_rowPolynomial {K : Type*} [Fintype K] (a : Option K → ℝ) :
    MvPolynomial.aeval dehomogenizingSubstitution (rowPolynomial a) =
      MvPolynomial.C (a none) + rowPolynomial (fun k => a (some k)) := by
  simp [rowPolynomial, dehomogenizingSubstitution, Fintype.sum_option]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open CircleFourier _root_.MvPolynomial
open scoped BigOperators Classical

def FiniteSitePhaseRemoval {h : ℕ} {S K X V : Type*}
    [Fintype S] [Fintype K] [Fintype X] [AddCommGroup V]
    (site : S → K → ℤ) (rows : Fin h → K → ℤ) : Prop :=
  ∀ (base : K → V) (shift : X → V) (phase : (K → V) → ℝ) (test : S → V → ℂ),
    (∀ s v, ‖test s v‖ ≤ 1) →
    ‖𝔼 x, character (phase (rowShiftedTuple base rows shift x) : CircleFourier.Circle) *
      ∏ s, test s (integerSiteValue (site s) (rowShiftedTuple base rows shift x))‖ ^ (2 ^ h) ≤
      ‖𝔼 u, 𝔼 v, character ((additiveBoxDifference h
        (fun x (_ : Unit) => phase (rowShiftedTuple base rows shift x)) u v () : ℝ) : CircleFourier.Circle)‖

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def residueSmoothIndexPMF {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) : PMF (K × I → ℤ) :=
  shiftedSmoothProductPMF (residueProfileCenter residue modulus) (residueProfileWidth modulus V)
    (residueProfileWidth_pos modulus V hmodulus hV) hZ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MixedDensityInterpolation
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {I Z : Type*} [Fintype I] [Fintype Z]

noncomputable def mixedDensityInterpolation (c w : I → ℝ) (f : Z → ℝ → ℝ)
    (x : (I → ℝ) × (Z → ℝ)) : ℝ :=
  affineProductProfile c w x.1 * ∏ j, f j (x.2 j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedRealCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

noncomputable def mixedRealCoordinates :
    EuclideanSpace ℝ D →ₗ[ℝ] ((I → ℝ) × (Fin n → ℝ)) :=
  ((orthonormalChart o).symm.toLinearMap.prodMap LinearMap.id).comp
    (normalizedOrthogonalChart W b).toLinearMap

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EmptyLayerDetectionGeometry
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

noncomputable def mixedAmbientInterpolation (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    (v : D → ℝ) : ℝ :=
  mixedDensityCovolumeRatio W b * mixedDensityInterpolation c w f
    (mixedRealCoordinates W b o ((EuclideanSpace.equiv D ℝ).symm v))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothResidueWindowMass
namespace OAI

section

namespace Erdos3

noncomputable def selectedResidueDensityMass {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (D : (K × I → ℤ) → ℝ) : ℝ :=
  finiteDensityMass (selectedResidueSmoothWeight modulus G V) D

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CanonicalAmbientKernel
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

noncomputable def canonicalAmbientKernel (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    (v : D → ℝ) : ℝ :=
  smallBoxCutoff v * mixedAmbientInterpolation W b o c w f v

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedJointAmbientKernel
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (f : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℝ → ℝ)

noncomputable def coefficientJointAmbientKernel (v : CoefficientAmbientIndex K J → ℝ) : ℝ :=
  ∏ s : CoefficientSlot K m,
    canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
      (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => f s.1 i s.2)
      (fun i => v ⟨s,i⟩)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

noncomputable def allocatedCoefficientJointAmbientKernel
    (x : CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ℝ) : ℝ :=
  coefficientJointAmbientKernel U b o (allocatedLayerCenters B U b S)
    (allocatedLayerWidths B U b S) (allocatedLayerIntegerInterpolation B U b S) x

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedMaskedCoefficientFourier
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedMaskedCoefficientDensity (q : ℕ)
    (mask : (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ZMod q) → ℝ)
    (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U) : ℝ :=
  maskedIntegerTorusKernel q mask (allocatedCoefficientJointAmbientKernel B U b S o)
    (coefficientAmbientTorus U x)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFiberCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def coefficientFiberMap {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (y : CoefficientTorus (K := Empty) U) (x : CoefficientTorus (K := K) U) :
    CoefficientTorus (K := K) U :=
  constantCoefficientTorusMap U y +
    (x - constantCoefficientTorusMap U (coefficientEvaluationTorus U t x))

theorem coefficientFiberMap_retraction {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (x : CoefficientTorus (K := K) U) :
    coefficientFiberMap U t (coefficientEvaluationTorus U t x) x = x := by
  dsimp only [coefficientFiberMap]
  abel

theorem coefficientFiberMap_continuous {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (y : CoefficientTorus (K := Empty) U) : Continuous (coefficientFiberMap U t y) :=
  continuous_const.add (continuous_id.sub ((constantCoefficientTorusMap_continuous U).comp
    (coefficientEvaluationTorus_continuous U t)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

noncomputable def coefficientFiberAverage {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure (CoefficientTorus (K := K) U)) (t : K → ℤ)
    (F : CoefficientTorus (K := K) U → E) (y : CoefficientTorus (K := Empty) U) : E :=
  ∫ x, F (coefficientFiberMap U t y x) ∂μ

theorem coefficientFiberAverage_bound {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure μ] (t : K → ℤ)
    (F : CoefficientTorus (K := K) U → E) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B)
    (y : CoefficientTorus (K := Empty) U) : ‖coefficientFiberAverage U μ t F y‖ ≤ B := by
  have h := norm_integral_le_of_norm_le (integrable_const B (μ := μ))
    (ae_of_all μ (fun x => hB (coefficientFiberMap U t y x)))
  simpa only [coefficientFiberAverage, integral_const, probReal_univ, one_smul] using h

theorem coefficientFiberAverage_approx {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure μ] (t : K → ℤ)
    (F G : CoefficientTorus (K := K) U → E) {ε : ℝ} (hε : ∀ x, ‖F x - G x‖ ≤ ε)
    (y : CoefficientTorus (K := Empty) U)
    (hF : Integrable (fun x => F (coefficientFiberMap U t y x)) μ)
    (hG : Integrable (fun x => G (coefficientFiberMap U t y x)) μ) :
    ‖coefficientFiberAverage U μ t F y - coefficientFiberAverage U μ t G y‖ ≤ ε := by
  simp only [coefficientFiberAverage]
  rw [← integral_sub hF hG]
  exact coefficientFiberAverage_bound U μ t (fun x => F x - G x) hε y

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CoefficientResidualCharacter
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def coefficientResidualFunctional {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) : CoefficientArray (K := K) U →ₗ[ℝ] ℝ :=
  (coefficientArrayFunctional U frequency).comp (coefficientResidualArray U t)

theorem coefficientResidualFunctional_integral {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    ∃ n : ℤ, coefficientResidualFunctional U t frequency x = n :=
  coefficientArrayFunctional_integral U frequency _
    (coefficientResidualArray_preserves_lattice U t x hx)

theorem coefficientTorusCharacter_fiber {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (y : CoefficientTorus (K := Empty) U) (x : CoefficientTorus (K := K) U) :
    coefficientTorusCharacter U frequency (coefficientFiberMap U t y x) =
      coefficientTorusCharacter U frequency (constantCoefficientTorusMap U y) *
        quotientLinearCharacter (coefficientIntegerLattice U) (coefficientResidualFunctional U t frequency)
          (coefficientResidualFunctional_integral U t frequency) x := by
  unfold coefficientFiberMap
  change quotientLinearCharacter _ _ _ (_ + _) = _
  rw [quotientLinearCharacter_add]
  congr 1
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [coefficientEvaluationTorus_mk, constantCoefficientTorusMap_mk, ← map_sub]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientFiberOrthogonality
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

theorem coefficientTorusCharacter_fiberAverage {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [MeasurableAdd₂ (CoefficientTorus (K := K) U)]
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (y : CoefficientTorus (K := Empty) U) :
    coefficientFiberAverage U μ t (coefficientTorusCharacter U frequency) y =
      if coefficientResidualFunctional U t frequency = 0 then
        coefficientTorusCharacter U frequency (constantCoefficientTorusMap U y) else 0 := by
  unfold coefficientFiberAverage
  simp_rw [coefficientTorusCharacter_fiber]
  rw [integral_const_mul, quotientLinearCharacter_integral]
  split_ifs <;> simp

theorem coefficientTorusCharacter_fiberAverage_evaluation {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [MeasurableAdd₂ (CoefficientTorus (K := K) U)]
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (x : CoefficientTorus (K := K) U) :
    coefficientFiberAverage U μ t (coefficientTorusCharacter U frequency) (coefficientEvaluationTorus U t x) =
      if coefficientResidualFunctional U t frequency = 0 then coefficientTorusCharacter U frequency x else 0 := by
  rw [coefficientTorusCharacter_fiberAverage]
  by_cases h : coefficientResidualFunctional U t frequency = 0
  · rw [if_pos h, if_pos h]
    have he := coefficientTorusCharacter_fiber U t frequency (coefficientEvaluationTorus U t x) x
    simpa only [coefficientFiberMap_retraction, h, quotientLinearCharacter_zero, mul_one] using he.symm
  · simp only [if_neg h]

end Erdos3.VectorPolynomial

end

end OAI
end


