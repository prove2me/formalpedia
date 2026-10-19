-- Prove2me | Definitions.Def_OAIE3v2B090
-- name    : OAIE3v2B090
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:23:24.222046+00:00
-- url     : https://prove2.me/theorems/baaff95a-8915-4695-81df-8783dda404a0
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 91 of 311
-- statement:
--   Definitions bundle 91 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B068`, `OAIE3v2B069`, `OAIE3v2B070`, `OAIE3v2B071`, `OAIE3v2B072` of this split.
--
--   Modules: `Estimates/AllocatedEnormousProfiles.lean`, `Estimates/AllocatedFiberCap.lean`, `Estimates/BoundedAmbientModeWitness.lean`, `Estimates/CoefficientModeLowerTerms.lean`, `Estimates/DehomogenizedExponent.lean`, `Estimates/DilationPairFiltration.lean`, `Estimates/LieFiniteProduct.lean`, `Estimates/MultidegreeDilationPair.lean`, `Estimates/PairedDiagonalApproximation.lean`, `Estimates/PartialComplexScaledQuadrature.lean`, `Estimates/PrincipalCoefficientMarginal.lean`, `Estimates/RowShiftTopSymbol.lean`, `Estimates/ShiftedSmoothProductAmplitudeTransfer.lean`, `Estimates/SquarefreePermutationFiltration.lean`, `Estimates/SquarefreeSplitCount.lean`, `Estimates/StrideProductBounds.lean`, `Estimates/VectorHomogenization.lean`, `Estimates/WeightedAxisScaling.lean`, `FixedDensity/GeneratorCells.lean`, `Fourier/BohrTorusApproximation.lean`, `Fourier/QuarticBohrProgression.lean`, `Geometry/ShiftedBoxSites.lean`, `Geometry/SupportedLieQuotient.lean`, `Geometry/TopSupportSubstitution.lean`, `Lattices/AffineCoefficientSubspace.lean`, `Lattices/AffineTopCoefficient.lean`, `Lattices/RelativeSliceAffineThreeFactorLaw.lean`, `Lattices/SelectedResidueApproximation.lean`, `Linear/HomogeneousLieSpan.lean`, `Linear/MarkedLieSpan.lean`, `Nilpotent/BCHConjugationLinear.lean`, `Nilpotent/BCHLatticeImageGap.lean`, `Nilpotent/RealPolynomialBCH.lean`, `Polynomial/AdaptedPolynomialSubstitution.lean`, `Polynomial/AffineShiftPolynomial.lean`, `Polynomial/CRTPolynomialChargeBound.lean`, `Polynomial/DegreeRankSunflower.lean`, `Polynomial/MarkedPolynomialGenerators.lean`, `Polynomial/PolynomialSiteRemoval.lean`, `Polynomial/SitePhaseCauchySchwarz.lean`, `Probability/ShiftedSmoothProductLaw.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B068
import Definitions.Def_OAIE3v2B069
import Definitions.Def_OAIE3v2B070
import Definitions.Def_OAIE3v2B071
import Definitions.Def_OAIE3v2B072

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J : Type*} [Fintype J]

theorem rectangularWeightSum_eq_tsum (f : (J → ℝ) → ℝ) (a S : J → ℝ)
    (hS : ∀ j, 0 < S j) {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    rectangularWeightSum f a S R = ∑' k : J → ℤ, f (rectangularLatticePoint a S k) :=
  (hasSum_sum_of_ne_finset_zero (rectangularWeight_zero_off_indices f a S hS hsupport)).tsum_eq.symm

theorem rectangularWeightHistogram_integral (f : (J → ℝ) → ℝ) (a S : J → ℝ)
    (hS : ∀ j, 0 < S j) (R : ℝ) :
    (∫ x, rectangularWeightHistogram f a S R x) = rectangularWeightSum f a S R / (∏ j, S j) :=
  finiteRectangularHistogram_integral _ _ a S hS

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J : Type*} [Fintype J]

theorem rectangularWeightSum_error (f : (J → ℝ) → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L f) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1 / S j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    |rectangularWeightSum f a S R / (∏ j, S j) - ∫ x, f x| ≤
      (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  rw [← rectangularWeightHistogram_integral f a S hS R,
    ← integral_sub (rectangularWeightHistogram_integrable f a S R)
      (compactBox_integrable f hLip.continuous R hsupport)]
  exact (norm_integral_le_integral_norm _).trans
    (rectangularWeightHistogram_l1_error f hLip a S hS hR hδ hδ1 hmesh hsupport)

theorem rectangularLattice_quadrature (f : (J → ℝ) → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L f) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1 / S j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    |(∑' k : J → ℤ, f (rectangularLatticePoint a S k)) / (∏ j, S j) - ∫ x, f x| ≤
      (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  rw [← rectangularWeightSum_eq_tsum f a S hS hsupport]
  exact rectangularWeightSum_error f hLip a S hS hR hδ hδ1 hmesh hsupport

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem normalized_rectangular_translation_test_le {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (a S : I → ℝ) (hS : ∀ i, 1 ≤ S i) {R : ℝ} (hR : 0 ≤ R)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) {Z : ℝ}
    (hmass : (∏ i, S i) / 2 ≤ Z) (φ : (I → ℤ) → ℂ) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (v : I → ℤ) :
    ‖(∑' x, ((rectangularWeight f a S x / Z : ℝ) : ℂ) * φ (x + v)) -
      ∑' x, ((rectangularWeight f a S x / Z : ℝ) : ℂ) * φ x‖ ≤
        4 * (2 * R + 1) ^ Fintype.card I * (L * ‖rectangularLatticePoint 0 S v‖) := by
  have hprod : 0 < ∏ i, S i := Finset.prod_pos (fun i _ => zero_lt_one.trans_le (hS i))
  have hZ : 0 < Z := (div_pos hprod (by norm_num)).trans_le hmass
  have hratio : (∏ i, S i) / Z ≤ 2 := (div_le_iff₀ hZ).mpr (by linarith)
  apply (normalized_finite_translation_test_le (rectangularWeight f a S)
    (rectangularWeightIndices a S R)
    (rectangularWeight_zero_off_indices f a S (fun i => zero_lt_one.trans_le (hS i)) hsupport)
    φ hφ v hZ).trans
  apply (div_le_div_of_nonneg_right (rectangularWeight_translation_l1 f hf a S hS hR hsupport v) hZ.le).trans
  calc
    (2 * ((2 * R + 1) ^ Fintype.card I * ∏ i, S i) *
        (L * ‖rectangularLatticePoint 0 S v‖)) / Z =
      (2 * (2 * R + 1) ^ Fintype.card I) * ((∏ i, S i) / Z) *
        (L * ‖rectangularLatticePoint 0 S v‖) := by ring
    _ ≤ (2 * (2 * R + 1) ^ Fintype.card I) * 2 *
        (L * ‖rectangularLatticePoint 0 S v‖) := by
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (by positivity)) (by positivity)
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalCoefficientMarginal
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped TensorProduct Classical

theorem exists_integral_vector_mode_witness {α K W : Type*} [Fintype α] [DecidableEq α]
    [AddCommGroup W] [Module ℝ W]
    (root : K → ℤ) (difference : α → K → ℤ) (selection : α → K)
    (hdet : (integerDifferencePivot difference selection).det ≠ 0)
    {H D : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (Λ : VectorPolynomial (Option K) ℝ W →ₗ[ℝ] ℝ) (h : ℕ)
    (hnonfactor : ¬ ∃ M : (Finset α → W) →ₗ[ℝ] ℝ,
      ∀ p, VectorPolynomial.Homogeneous h p → Λ p = M (VectorPolynomial.siteEvaluation
        (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ forms : List (MvPolynomial (Option K) ℤ), forms.length = h ∧
      (∀ P ∈ forms, P.IsHomogeneous 1 ∧
        realPolynomialMass (map (Int.castRingHom ℝ) P) ≤ integerCubeWitnessBound (Fintype.card α) H D) ∧
      (∀ s : Finset α, ∃ P ∈ forms, eval (affineSite root difference s) P = 0) ∧
      ∃ w : W, Λ ((map (Int.castRingHom ℝ) forms.prod) ⊗ₜ[ℝ] w) ≠ 0 := by
  have hn := VectorPolynomial.curried_nonfactor
    (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) Λ h hnonfactor
  obtain ⟨forms, hlen, hforms, hz, hΛ⟩ := exists_bounded_integer_vanishing_product
    root difference selection hdet hH hD hroot hdiff (TensorProduct.curry Λ) h hn
  refine ⟨forms, hlen, hforms, hz, ?_⟩
  by_contra hnone
  apply hΛ
  ext w
  change Λ ((map (Int.castRingHom ℝ) forms.prod) ⊗ₜ[ℝ] w) = 0
  by_contra hw
  exact hnone ⟨w, hw⟩

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeSplitCount
namespace OAI

section

namespace Erdos3

variable {ι σ : Type*} [Fintype ι]

noncomputable def SquarefreeIndex.ofFinset (S : Finset ι) : SquarefreeIndex ι := by
  classical
  exact ⟨Finsupp.equivFunOnFinite.symm (fun i => if i ∈ S then 1 else 0),
    fun i => by
      change (if i ∈ S then 1 else 0) ≤ 1
      split_ifs <;> omega⟩

theorem SquarefreeIndex.ofFinset_apply [DecidableEq ι] (S : Finset ι) (i : ι) :
    (ofFinset S).val i = if i ∈ S then 1 else 0 := by
  classical
  simp [ofFinset]

theorem SquarefreeIndex.support_ofFinset (S : Finset ι) : (ofFinset S).val.support = S := by
  classical
  ext i
  simp only [Finsupp.mem_support_iff, ofFinset_apply]
  split_ifs <;> simp_all

theorem SquarefreeIndex.ofFinset_support (a : SquarefreeIndex ι) : ofFinset a.val.support = a := by
  classical
  apply Subtype.ext
  ext i
  rw [ofFinset_apply]
  have hi := a.property i
  split_ifs with h
  · have := Finsupp.mem_support_iff.mp h
    omega
  · exact (Finsupp.notMem_support_iff.mp h).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def fullShiftExponent (n : ℕ) : Fin n →₀ ℕ :=
  (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val

theorem fullShiftExponent_apply (n : ℕ) (i : Fin n) : fullShiftExponent n i = 1 := by
  simp only [fullShiftExponent, SquarefreeIndex.ofFinset_apply, Finset.mem_univ, ite_true]

theorem fullShiftExponent_sum (n : ℕ) : (fullShiftExponent n).sum (fun _ e => e) = n := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp only [fullShiftExponent_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]

theorem exponent_eq_full_or_missing {n : ℕ} (d : Fin n →₀ ℕ)
    (hd : d.sum (fun _ e => e) ≤ n) : d = fullShiftExponent n ∨ ∃ i, d i = 0 := by
  by_cases hz : ∃ i, d i = 0
  · exact Or.inr hz
  left
  have hpos (i : Fin n) : 1 ≤ d i := by
    have hn : d i ≠ 0 := fun hi => hz ⟨i, hi⟩
    omega
  have hsum : (∑ i, d i) ≤ n := by
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hd
  ext i
  rw [fullShiftExponent_apply]
  by_contra hi
  have hstrict : (1 : ℕ) < d i := by have := hpos i; omega
  have hlt := Finset.sum_lt_sum (s := Finset.univ) (fun j _ => hpos j)
    ⟨i, Finset.mem_univ i, hstrict⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hlt
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StrideProductBounds
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem full_mixed_difference_of_totalDegree {R : Type*} [CommRing R] {n : ℕ}
    (P : MvPolynomial (Fin n) R) (hP : P.totalDegree ≤ n) (u v : Fin n → R) :
    additiveBoxDifference n (fun x (_ : Unit) => eval x P) u v () =
      P.coeff (fullShiftExponent n) * ∏ i, (u i - v i) := by
  have he : (fun x (_ : Unit) => eval x P) =
      (fun x (_ : Unit) => ∑ d ∈ P.support, P.coeff d * ∏ i, x i ^ d i) := by
    funext x _
    conv_lhs => rw [P.as_sum]
    simp only [map_sum, eval_monomial, Finsupp.prod_pow]
  rw [he, additiveBoxDifference_sum]
  have hm (d : Fin n →₀ ℕ) :
      additiveBoxDifference n (fun x (_ : Unit) => P.coeff d * ∏ i, x i ^ d i) u v () =
        P.coeff d * ∏ i, (u i ^ d i - v i ^ d i) :=
    additiveBoxDifference_product n (fun _ : Unit => P.coeff d) (fun i x => x ^ d i) u v ()
  simp_rw [hm]
  rw [Finset.sum_eq_single (fullShiftExponent n)]
  · simp only [fullShiftExponent_apply, pow_one]
  · intro d hd hne
    obtain ⟨i, hi⟩ := (exponent_eq_full_or_missing d ((le_totalDegree hd).trans hP)).resolve_left hne
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [hi, pow_zero, sub_self]), mul_zero]
  · intro hnot
    rw [notMem_support_iff.mp hnot, zero_mul]

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

theorem assigned_phase_cauchySchwarz {h : ℕ} {S X : Type*}
    [Fintype S] [Fintype X] [Nonempty X] (hh : 0 < h)
    (P : (Fin h → X) → ℝ) (assignment : S → Fin h)
    (U : S → (Fin h → X) → ℂ) (hU : ∀ s x, ‖U s x‖ ≤ 1)
    (hmiss : ∀ s, MissesBoxCoordinate (U s) (assignment s)) :
    ‖𝔼 x, character (P x : CircleFourier.Circle) * ∏ s, U s x‖ ^ (2 ^ h) ≤
      ‖𝔼 u, 𝔼 v, character
        ((additiveBoxDifference h (fun x (_ : Unit) => P x) u v () : ℝ) : CircleFourier.Circle)‖ := by
  have hc := assigned_site_cauchySchwarz hh
    (fun x => character (P x : CircleFourier.Circle)) assignment U hU hmiss
  rw [boxPhaseMoment_character] at hc
  exact hc.trans (Complex.re_le_norm _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ShiftedBoxSites
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem shifted_site_phase_cauchySchwarz {h : ℕ} {S X V : Type*}
    [Fintype S] [Fintype X] [Nonempty X] [AddCommGroup V] (hh : 0 < h)
    (base : S → V) (coefficient : S → Fin h → ℤ) (shift : X → V)
    (hzero : ∀ s, ∃ i, coefficient s i = 0) (P : (Fin h → X) → ℝ)
    (test : S → V → ℂ) (htest : ∀ s v, ‖test s v‖ ≤ 1) :
    ‖𝔼 x, character (P x : CircleFourier.Circle) *
      ∏ s, test s (shiftedBoxSite (base s) (coefficient s) shift x)‖ ^ (2 ^ h) ≤
      ‖𝔼 u, 𝔼 v, character
        ((additiveBoxDifference h (fun x (_ : Unit) => P x) u v () : ℝ) : CircleFourier.Circle)‖ := by
  let assignment : S → Fin h := fun s => (hzero s).choose
  apply assigned_phase_cauchySchwarz hh P assignment
    (fun s x => test s (shiftedBoxSite (base s) (coefficient s) shift x))
    (fun s x => htest s _)
  intro s x a
  exact congrArg (test s)
    (shiftedBoxSite_update (base s) (coefficient s) shift (hzero s).choose_spec x a)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TopSupportSubstitution
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem weightedSupportLT_aeval {σ τ R : Type*} [CommRing R]
    (w : σ → ℕ) (v : τ → ℕ) (f : σ → MvPolynomial τ R)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    {P : MvPolynomial σ R} {d : ℕ} (hP : P ∈ weightedSupportLT w d) :
    aeval f P ∈ weightedSupportLT v d := by
  rw [← P.support_sum_monomial_coeff, map_sum]
  apply (weightedSupportLT v d).sum_mem
  intro a ha b hb
  have hap : Finsupp.weight w a < d := hP ha
  exact (weightedSupportLE_aeval_monomial w v f hf a _ hb).trans_lt hap

theorem polynomialTranslate_sub_mem_weightedSupportLT {σ R : Type*} [CommRing R]
    (base : σ → R) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    {P : MvPolynomial σ R} {d : ℕ} (hP : P ∈ weightedSupportLE w d) :
    polynomialTranslate base P - P ∈ weightedSupportLT w d := by
  have hexp : P = ∑ a ∈ P.support, P.coeff a • monomial a (1 : R) := by
    simpa only [smul_monomial, smul_eq_mul, mul_one] using P.as_sum
  have he := congrArg (fun Q => polynomialTranslate base Q - Q) hexp
  simp only [map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub] at he
  rw [he]
  apply (weightedSupportLT w d).sum_mem
  intro a ha
  apply (weightedSupportLT w d).smul_mem
  intro b hb
  have hap : Finsupp.weight w a ≤ d := hP ha
  exact ((polynomialTranslate_monomial_bounds base w hw a).2 hb).trans_le hap

theorem fullShiftExponent_weight (n : ℕ) :
    Finsupp.weight (1 : Fin n → ℕ) (fullShiftExponent n) = n := by
  simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using
    fullShiftExponent_sum n

theorem full_coefficient_zero_of_lower_support {R : Type*} [CommRing R] {n : ℕ}
    {P : MvPolynomial (Fin n) R} (hP : P ∈ weightedSupportLT (1 : Fin n → ℕ) n) :
    P.coeff (fullShiftExponent n) = 0 := by
  by_contra hn
  have hlt : Finsupp.weight (1 : Fin n → ℕ) (fullShiftExponent n) < n :=
    hP (mem_support_iff.mpr hn)
  rw [fullShiftExponent_weight] at hlt
  exact (lt_irrefl n) hlt

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffineShiftPolynomial
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem affineShift_full_difference {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ)
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n) (u v : Fin n → ℝ) :
    additiveBoxDifference n
      (fun t (_ : Unit) => eval (fun i => base i + ∑ j, direction j i * t j) P) u v () =
      (affineShiftPullback base direction P).coeff (fullShiftExponent n) * ∏ i, (u i - v i) := by
  simpa only [affineShiftPullback_eval] using full_mixed_difference_of_totalDegree
    (affineShiftPullback base direction P) (affineShiftPullback_degree base direction P hP) u v

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineTopCoefficient
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem affineShiftPullback_translate {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ) (P : MvPolynomial I ℝ) :
    affineShiftPullback (fun _ => 0) direction (polynomialTranslate base P) =
      affineShiftPullback base direction P := by
  have he : (affineShiftPullback (fun _ => 0) direction).comp (polynomialTranslate base) =
      affineShiftPullback base direction := by
    apply algHom_ext
    intro i
    simp [AlgHom.comp_apply, polynomialTranslate_X, affineShiftPullback,
      affineShiftCoordinate, add_comm]
  exact AlgHom.congr_fun he P

theorem affineShift_full_coefficient_base {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ)
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n) :
    (affineShiftPullback base direction P).coeff (fullShiftExponent n) =
      (affineShiftPullback (fun _ => 0) direction P).coeff (fullShiftExponent n) := by
  have hc (i : I) : affineShiftCoordinate (fun _ => 0) direction i ∈
      weightedSupportLE (1 : Fin n → ℕ) ((1 : I → ℕ) i) :=
    (mem_weightedSupportLE_one_iff _ 1).mpr (affineShiftCoordinate_degree _ _ _)
  have hp := (mem_weightedSupportLE_one_iff P n).mpr hP
  have ht := polynomialTranslate_sub_mem_weightedSupportLT base (1 : I → ℕ)
    (fun _ => by simp) hp
  have hl := weightedSupportLT_aeval (1 : I → ℕ) (1 : Fin n → ℕ)
    (affineShiftCoordinate (fun _ => 0) direction) hc ht
  have hz := full_coefficient_zero_of_lower_support hl
  change (affineShiftPullback (fun _ => 0) direction (polynomialTranslate base P - P)).coeff
    (fullShiftExponent n) = 0 at hz
  rw [map_sub, coeff_sub, affineShiftPullback_translate] at hz
  exact sub_eq_zero.mp hz

theorem sub_topComponent_mem_lowerSupport {I R : Type*} [CommRing R] {n : ℕ}
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ n) :
    P - homogeneousComponent n P ∈ weightedSupportLT (1 : I → ℕ) n := by
  intro a ha
  change Finsupp.weight (1 : I → ℕ) a < n
  have hne : (P - homogeneousComponent n P).coeff a ≠ 0 := mem_support_iff.mp ha
  simp only [coeff_sub, coeff_homogeneousComponent] at hne
  by_cases hd : a.degree = n
  · simp only [hd, ite_true, sub_self, ne_eq, not_true_eq_false] at hne
  · have haP : P.coeff a ≠ 0 := by
      intro hz
      simp only [hz, hd, ite_false, sub_self, ne_eq, not_true_eq_false] at hne
    have hle : Finsupp.weight (1 : I → ℕ) a ≤ n :=
      (mem_weightedSupportLE_one_iff P n).mpr hP (mem_support_iff.mpr haP)
    have hn : Finsupp.weight (1 : I → ℕ) a ≠ n := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
    omega

theorem affineShift_full_coefficient_top {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ)
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n) :
    (affineShiftPullback base direction P).coeff (fullShiftExponent n) =
      (affineShiftPullback base direction (homogeneousComponent n P)).coeff (fullShiftExponent n) := by
  have hc (i : I) : affineShiftCoordinate base direction i ∈
      weightedSupportLE (1 : Fin n → ℕ) ((1 : I → ℕ) i) :=
    (mem_weightedSupportLE_one_iff _ 1).mpr (affineShiftCoordinate_degree _ _ _)
  have hl := weightedSupportLT_aeval (1 : I → ℕ) (1 : Fin n → ℕ)
    (affineShiftCoordinate base direction) hc (sub_topComponent_mem_lowerSupport P hP)
  have hz := full_coefficient_zero_of_lower_support hl
  change (affineShiftPullback base direction (P - homogeneousComponent n P)).coeff
    (fullShiftExponent n) = 0 at hz
  rw [map_sub, coeff_sub] at hz
  exact sub_eq_zero.mp hz

noncomputable def polynomialTopSymbol {I : Type*} (n : ℕ) (P : MvPolynomial I ℝ)
    (direction : Fin n → I → ℝ) : ℝ :=
  (affineShiftPullback (fun _ => 0) direction (homogeneousComponent n P)).coeff (fullShiftExponent n)

theorem affineShift_difference_eq_topSymbol {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ)
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n) (u v : Fin n → ℝ) :
    additiveBoxDifference n
      (fun t (_ : Unit) => eval (fun i => base i + ∑ j, direction j i * t j) P) u v () =
      polynomialTopSymbol n P direction * ∏ i, (u i - v i) := by
  rw [affineShift_full_difference base direction P hP,
    affineShift_full_coefficient_base base direction P hP,
    affineShift_full_coefficient_top (fun _ => 0) direction P hP]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RowShiftTopSymbol
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem row_shifted_site_phase_cauchySchwarz {h : ℕ} {S K X V : Type*}
    [Fintype S] [Fintype K] [Fintype X] [Nonempty X] [AddCommGroup V] (hh : 0 < h)
    (site : S → K → ℤ) (base : K → V) (rows : Fin h → K → ℤ) (shift : X → V)
    (hzero : ∀ s, ∃ i, (∑ k, rows i k * site s k) = 0)
    (phase : (K → V) → ℝ) (test : S → V → ℂ) (htest : ∀ s v, ‖test s v‖ ≤ 1) :
    ‖𝔼 x, character (phase (rowShiftedTuple base rows shift x) : CircleFourier.Circle) *
      ∏ s, test s (integerSiteValue (site s) (rowShiftedTuple base rows shift x))‖ ^ (2 ^ h) ≤
      ‖𝔼 u, 𝔼 v, character ((additiveBoxDifference h
        (fun x (_ : Unit) => phase (rowShiftedTuple base rows shift x)) u v () : ℝ) : CircleFourier.Circle)‖ := by
  simpa only [rowShiftedSite_eq] using shifted_site_phase_cauchySchwarz hh
    (fun s => integerSiteValue (site s) base) (fun s i => ∑ k, rows i k * site s k)
    shift hzero (fun x => phase (rowShiftedTuple base rows shift x)) test htest

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem vector_shift_difference_eq_topSymbol {I : Type*} {n : ℕ}
    (base : I → ℝ) (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n)
    (u v : Fin n → I → ℝ) :
    additiveBoxDifference n
      (fun (w : Fin n → I → ℝ) (_ : Unit) => eval (fun k => base k + ∑ i, w i k) P) u v () =
      polynomialTopSymbol n P (fun i k => u i k - v i k) := by
  let f : Fin n → ℝ → I → ℝ := fun i t k => v i k + (u i k - v i k) * t
  have hu : (fun i => f i 1) = u := by
    funext i k
    dsimp [f]
    ring
  have hv : (fun i => f i 0) = v := by
    funext i k
    dsimp [f]
    ring
  have he := additiveBoxDifference_map n f
    (fun (w : Fin n → I → ℝ) (_ : Unit) => eval (fun k => base k + ∑ i, w i k) P)
    (fun _ => 1) (fun _ => 0) ()
  rw [hu, hv] at he
  rw [← he]
  have hfun :
      (fun (t : Fin n → ℝ) (_ : Unit) => eval (fun k => base k + ∑ i, f i (t i) k) P) =
      (fun (t : Fin n → ℝ) (_ : Unit) => eval (fun k => (base k + ∑ i, v i k) +
        ∑ i, (u i k - v i k) * t i) P) := by
    funext t z
    apply congrArg (fun point : I → ℝ => eval point P)
    funext k
    simp only [f, Finset.sum_add_distrib]
    ring
  rw [hfun]
  simpa only [sub_zero, Finset.prod_const_one, mul_one] using
    affineShift_difference_eq_topSymbol (fun k => base k + ∑ i, v i k)
      (fun i k => u i k - v i k) P hP (fun _ => 1) (fun _ => 0)

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem row_shift_difference_eq_topSymbol {K J X : Type*} {h : ℕ}
    (base : K → J → ℝ) (rows : Fin h → K → ℤ) (shift : X → J → ℝ)
    (P : MvPolynomial (K × J) ℝ) (hP : P.totalDegree ≤ h) (u v : Fin h → X) :
    additiveBoxDifference h
      (fun x (_ : Unit) => eval (fun z => rowShiftedTuple base rows shift x z.1 z.2) P) u v () =
      polynomialTopSymbol h P
        (fun i z => (rows i z.1 : ℝ) * (shift (u i) z.2 - shift (v i) z.2)) := by
  let f : Fin h → X → (K × J) → ℝ := fun i x z => (rows i z.1 : ℝ) * shift x z.2
  have he :
      (fun x (_ : Unit) => eval (fun z => rowShiftedTuple base rows shift x z.1 z.2) P) =
      (fun x (_ : Unit) => eval (fun z => base z.1 z.2 + ∑ i, f i (x i) z) P) := by
    funext x t
    apply congrArg (fun point : (K × J) → ℝ => eval point P)
    funext z
    simp only [rowShiftedTuple, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, f]
    simp only [zsmul_eq_mul]
  rw [he]
  have hm := additiveBoxDifference_map h f
    (fun (w : Fin h → (K × J) → ℝ) (_ : Unit) => eval (fun z => base z.1 z.2 + ∑ i, w i z) P)
    u v ()
  exact hm.trans (by simpa only [f, mul_sub] using
    (vector_shift_difference_eq_topSymbol
      (fun z => base z.1 z.2) P hP (fun i => f i (u i)) (fun i => f i (v i))))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedSmoothProductLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem rectangular_profile_mass_lower {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) {R δ : ℝ} (hR : 0 ≤ R)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hintegral : (∫ x, f x) = 1)
    (hsmall : (2 * R + 2) ^ Fintype.card I * L * δ ≤ 1 / 2) :
    (∏ i, S i) / 2 ≤ ∑' k, rectangularWeight f a S k := by
  have he := rectangularLattice_quadrature f hf a S hS hR hδ hδ1 hmesh hsupport
  rw [hintegral] at he
  have hp : 0 < ∏ i, S i := Finset.prod_pos (fun i _ => hS i)
  have hnorm : (1 / 2 : ℝ) ≤ (∑' k, rectangularWeight f a S k) / ∏ i, S i := by
    have hh := (abs_le.mp he).1
    change -((2 * R + 2) ^ Fintype.card I * L * δ) ≤
      (∑' k, rectangularWeight f a S k) / (∏ i, S i) - 1 at hh
    linarith
  have h := (le_div_iff₀ hp).mp hnorm
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem shiftedSmoothProductMass_lower {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2) :
    (∏ i, S i) / 2 ≤ shiftedSmoothProductMass a S := by
  apply rectangular_profile_mass_lower (smoothProductProfile I) (smoothProductProfile_lipschitz I)
    a S hS zero_le_one hδ hδ1 hmesh (smoothProductProfile_zero_outside I)
    (smoothProductProfile_integral I)
  simpa only [NNReal.coe_mul, NNReal.coe_natCast, show 2 * (1 : ℝ) + 2 = 4 by norm_num] using hsmall

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

theorem polynomialTranslate_add_apply {I R : Type*} [CommRing R]
    (u v : I → R) (P : MvPolynomial I R) :
    polynomialTranslate u (polynomialTranslate v P) = polynomialTranslate (u + v) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, hP, polynomialTranslate_X, map_add, polynomialTranslate_C, Pi.add_apply]
    rw [add_assoc]

noncomputable def polynomialDifference {I R : Type*} [CommRing R] (u : I → R) :
    MvPolynomial I R →ₗ[R] MvPolynomial I R :=
  (polynomialTranslate u).toLinearMap - LinearMap.id

theorem polynomialDifference_apply {I R : Type*} [CommRing R]
    (u : I → R) (P : MvPolynomial I R) :
    polynomialDifference u P = polynomialTranslate u P - P := rfl

theorem polynomialDifference_commute {I R : Type*} [CommRing R]
    (u v : I → R) (P : MvPolynomial I R) :
    polynomialDifference u (polynomialDifference v P) =
      polynomialDifference v (polynomialDifference u P) := by
  simp only [polynomialDifference_apply, map_sub, polynomialTranslate_add_apply]
  rw [add_comm u v]
  abel

theorem polynomialDifference_degree {I R : Type*} [CommRing R]
    (u : I → R) (P : MvPolynomial I R) {d : ℕ} (hP : P.totalDegree ≤ d + 1) :
    (polynomialDifference u P).totalDegree ≤ d := by
  have hd := polynomialTranslate_sub_mem_weightedSupportLT u (1 : I → ℕ)
    (fun _ => by simp) ((mem_weightedSupportLE_one_iff P (d + 1)).mpr hP)
  apply (mem_weightedSupportLE_one_iff _ d).mp
  intro a ha
  have hlt : Finsupp.weight (1 : I → ℕ) a < d + 1 := hd ha
  change Finsupp.weight (1 : I → ℕ) a ≤ d
  omega

theorem polynomialDifference_eval {I R : Type*} [CommRing R]
    (u x : I → R) (P : MvPolynomial I R) :
    eval x (polynomialDifference u P) = eval (x + u) P - eval x P := by
  rw [polynomialDifference_apply, map_sub]
  change aeval x (polynomialTranslate u P) - eval x P = _
  rw [polynomialTranslate, comp_aeval_apply]
  simp only [map_add, aeval_X, aeval_C, Algebra.algebraMap_self_apply]
  rfl

end Erdos3


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem polynomialDifference_C {I R : Type*} [CommRing R] (u : I → R) (c : R) :
    polynomialDifference u (C c) = 0 := by
  rw [polynomialDifference_apply, polynomialTranslate_C, sub_self]

theorem polynomialDifference_row {I R : Type*} [Fintype I] [CommRing R]
    (u a : I → R) :
    polynomialDifference u (rowPolynomial a) = C (∑ i, a i * u i) := by
  simp only [polynomialDifference_apply, rowPolynomial, map_sum, map_mul,
    polynomialTranslate_C, polynomialTranslate_X, mul_add,
    add_sub_cancel_left]

theorem polynomialDifference_affine {I R : Type*} [Fintype I] [CommRing R]
    (u : I → R) (P : MvPolynomial I R) (hP : P.totalDegree ≤ 1) :
    polynomialDifference u P = C (∑ i, polynomialLinearRow P i * u i) := by
  conv_lhs => rw [degree_le_one_eq_constant_add_row P hP]
  rw [map_add, polynomialDifference_C, zero_add, polynomialDifference_row]

theorem polynomialDifference_direction_add {I R : Type*} [Fintype I] [CommRing R]
    (u v : I → R) (P : MvPolynomial I R) (hP : P.totalDegree ≤ 1) :
    polynomialDifference (u + v) P = polynomialDifference u P + polynomialDifference v P := by
  simp only [polynomialDifference_affine _ P hP, Pi.add_apply, mul_add,
    Finset.sum_add_distrib, map_add]

theorem polynomialDifference_direction_smul {I R : Type*} [Fintype I] [CommRing R]
    (c : R) (u : I → R) (P : MvPolynomial I R) (hP : P.totalDegree ≤ 1) :
    polynomialDifference (c • u) P = c • polynomialDifference u P := by
  rw [polynomialDifference_affine _ P hP, polynomialDifference_affine _ P hP,
    smul_eq_C_mul, ← map_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end Erdos3


namespace Erdos3

noncomputable def polynomialIterDifference {I R : Type*} [CommRing R] :
    (n : ℕ) → MvPolynomial I R → (Fin n → I → R) → MvPolynomial I R
  | 0, P, _ => P
  | n + 1, P, u => polynomialIterDifference n (polynomialDifference (u 0) P) (Fin.tail u)

theorem polynomialIterDifference_commute {I R : Type*} [CommRing R] (n : ℕ)
    (v : I → R) (P : MvPolynomial I R) (u : Fin n → I → R) :
    polynomialIterDifference n (polynomialDifference v P) u =
      polynomialDifference v (polynomialIterDifference n P u) := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    simp only [polynomialIterDifference]
    rw [polynomialDifference_commute, ih]

theorem polynomialIterDifference_degree {I R : Type*} [CommRing R] (n d : ℕ)
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ n + d) (u : Fin n → I → R) :
    (polynomialIterDifference n P u).totalDegree ≤ d := by
  induction n generalizing P d with
  | zero => simpa only [polynomialIterDifference, zero_add] using hP
  | succ n ih =>
    exact ih d _ (polynomialDifference_degree (u 0) P (by omega)) (Fin.tail u)


open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3


namespace Erdos3

open scoped Classical

theorem polynomialIterDifference_update_add {I R : Type*} [Fintype I] [CommRing R] (n : ℕ) :
    ∀ (P : MvPolynomial I R), P.totalDegree ≤ n →
      ∀ (u : Fin n → I → R) (j : Fin n) (a b : I → R),
        polynomialIterDifference n P (Function.update u j (a + b)) =
          polynomialIterDifference n P (Function.update u j a) +
            polynomialIterDifference n P (Function.update u j b) := by
  induction n with
  | zero => intro P hP u j; exact Fin.elim0 j
  | succ n ih =>
    intro P hP u j a b
    cases j using Fin.cases with
    | zero =>
      simp only [polynomialIterDifference, Function.update_self, Fin.tail_update_zero,
        polynomialIterDifference_commute]
      exact polynomialDifference_direction_add a b _
        (polynomialIterDifference_degree n 1 P hP (Fin.tail u))
    | succ j =>
      simp only [polynomialIterDifference, Fin.tail_update_succ,
        Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j))]
      exact ih _ (polynomialDifference_degree (u 0) P hP) (Fin.tail u) j a b

theorem polynomialIterDifference_update_smul {I R : Type*} [Fintype I] [CommRing R] (n : ℕ) :
    ∀ (P : MvPolynomial I R), P.totalDegree ≤ n →
      ∀ (u : Fin n → I → R) (j : Fin n) (c : R) (a : I → R),
        polynomialIterDifference n P (Function.update u j (c • a)) =
          c • polynomialIterDifference n P (Function.update u j a) := by
  induction n with
  | zero => intro P hP u j; exact Fin.elim0 j
  | succ n ih =>
    intro P hP u j c a
    cases j using Fin.cases with
    | zero =>
      simp only [polynomialIterDifference, Function.update_self, Fin.tail_update_zero,
        polynomialIterDifference_commute]
      exact polynomialDifference_direction_smul c a _
        (polynomialIterDifference_degree n 1 P hP (Fin.tail u))
    | succ j =>
      simp only [polynomialIterDifference, Fin.tail_update_succ,
        Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j))]
      exact ih _ (polynomialDifference_degree (u 0) P hP) (Fin.tail u) j c a

noncomputable def polynomialIterDifferenceMultilinear {I R : Type*} [Fintype I] [CommRing R]
    (n : ℕ) (P : MvPolynomial I R) (hP : P.totalDegree ≤ n) :
    MultilinearMap R (fun _ : Fin n => I → R) (MvPolynomial I R) :=
  MultilinearMap.mk' (polynomialIterDifference n P)
    (polynomialIterDifference_update_add n P hP) (polynomialIterDifference_update_smul n P hP)

end Erdos3


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem polynomialIterDifference_eval {I R : Type*} [CommRing R] (n : ℕ)
    (P : MvPolynomial I R) (u : Fin n → I → R) (base : I → R) :
    eval base (polynomialIterDifference n P u) =
      additiveBoxDifference n
        (fun (w : Fin n → I → R) (_ : Unit) => eval (fun j => base j + ∑ i, w i j) P)
        u (fun _ => 0) () := by
  induction n generalizing P with
  | zero => simp [polynomialIterDifference, additiveBoxDifference]
  | succ n ih =>
    simp only [polynomialIterDifference, additiveBoxDifference]
    rw [ih]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, zero_add]
    apply congrArg (fun F : (Fin n → I → R) → Unit → R =>
      additiveBoxDifference n F (Fin.tail u) (fun _ => 0) ())
    funext w t
    rw [polynomialDifference_eval]
    apply congrArg (fun value : R => value - eval (fun j => base j + ∑ i, w i j) P)
    apply congrArg (fun point : I → R => eval point P)
    funext j
    simp only [Pi.add_apply]
    ring

theorem polynomialIterDifference_topSymbol {I : Type*} (n : ℕ)
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n)
    (u : Fin n → I → ℝ) (base : I → ℝ) :
    eval base (polynomialIterDifference n P u) = polynomialTopSymbol n P u := by
  rw [polynomialIterDifference_eval]
  simpa only [Pi.zero_apply, sub_zero] using
    vector_shift_difference_eq_topSymbol base P hP u (fun _ => 0)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PairedDiagonalApproximation
namespace OAI

section

namespace Erdos3

noncomputable def polynomialTopSymbolMultilinear {I : Type*} [Fintype I]
    (n : ℕ) (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n) :
    MultilinearMap ℝ (fun _ : Fin n => I → ℝ) ℝ :=
  (MvPolynomial.aeval (fun _ : I => (0 : ℝ))).toLinearMap.compMultilinearMap
    (polynomialIterDifferenceMultilinear n P hP)

theorem polynomialTopSymbolMultilinear_apply {I : Type*} [Fintype I]
    (n : ℕ) (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n) (u : Fin n → I → ℝ) :
    polynomialTopSymbolMultilinear n P hP u = polynomialTopSymbol n P u := by
  change MvPolynomial.eval (fun _ => 0) (polynomialIterDifference n P u) = _
  exact polynomialIterDifference_topSymbol n P hP u _

end Erdos3

end

section

namespace Erdos3

noncomputable def rowTopSymbolMultilinear {K I : Type*} [Fintype K] [Fintype I]
    (n : ℕ) (P : MvPolynomial (K × I) ℝ) (hP : P.totalDegree ≤ n) (a : Fin n → K → ℝ) :
    MultilinearMap ℝ (fun _ : Fin n => I → ℝ) ℝ :=
  (polynomialTopSymbolMultilinear n P hP).compLinearMap (fun i => rowDirectionLinear (a i))

theorem rowTopSymbolMultilinear_apply {K I : Type*} [Fintype K] [Fintype I]
    (n : ℕ) (P : MvPolynomial (K × I) ℝ) (hP : P.totalDegree ≤ n)
    (a : Fin n → K → ℝ) (u : Fin n → I → ℝ) :
    rowTopSymbolMultilinear n P hP a u =
      polynomialTopSymbol n P (fun i z => a i z.1 * u i z.2) := by
  change polynomialTopSymbolMultilinear n P hP (fun i => rowDirectionLinear (a i) (u i)) = _
  rw [polynomialTopSymbolMultilinear_apply]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedSmoothProductAmplitudeTransfer
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem shiftedSmoothProductPMF_translation_test_le {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hS1 : ∀ i, 1 ≤ S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (φ : (I → ℤ) → ℂ) (hφ : ∀ x, ‖φ x‖ ≤ 1) (v : I → ℤ) :
    ‖(∑' x, ((shiftedSmoothProductPMF a S hS hZ x).toReal : ℂ) * φ (x + v)) -
      ∑' x, ((shiftedSmoothProductPMF a S hS hZ x).toReal : ℂ) * φ x‖ ≤
        4 * (3 : ℝ) ^ Fintype.card I *
          (((Fintype.card I : ℝ) * probabilityProfileLipschitz) * ‖rectangularLatticePoint 0 S v‖) := by
  have ht := normalized_rectangular_translation_test_le (smoothProductProfile I)
    (smoothProductProfile_lipschitz I) a S hS1 zero_le_one
    (smoothProductProfile_zero_outside I)
    (shiftedSmoothProductMass_lower a S hS hδ hδ1 hmesh hsmall) φ hφ v
  simpa only [shiftedSmoothProductPMF_toReal, NNReal.coe_mul, NNReal.coe_natCast,
    show 2 * (1 : ℝ) + 1 = 3 by norm_num] using ht

theorem shiftedSmoothProductPMF_shift_transfer {I X : Type*}
    [Fintype I] [Fintype X] [Nonempty X]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hS1 : ∀ i, 1 ≤ S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (shift : X → I → ℤ) {r B : ℝ}
    (hshift : ∀ u, ‖rectangularLatticePoint 0 S (shift u)‖ ≤ r)
    (f : (I → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hlocal : ∀ x, ‖𝔼 u, f (x + shift u)‖ ≤ B) :
    ‖∑' x, ((shiftedSmoothProductPMF a S hS hZ x).toReal : ℂ) * f x‖ ≤
      4 * (3 : ℝ) ^ Fintype.card I * ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * r + B := by
  apply finite_probability_shift_transfer (fun x => (shiftedSmoothProductPMF a S hS hZ x).toReal)
    (rectangularWeightIndices a S 1) (shiftedSmoothProductPMF_toReal_zero_off a S hS hZ)
    (fun _ => ENNReal.toReal_nonneg) (shiftedSmoothProductPMF_toReal_sum a S hS hZ) shift f _ hlocal
  intro u
  apply (shiftedSmoothProductPMF_translation_test_le a S hS hZ hS1 hδ hδ1 hmesh hsmall f hf (shift u)).trans
  calc
    _ ≤ 4 * (3 : ℝ) ^ Fintype.card I *
        (((Fintype.card I : ℝ) * probabilityProfileLipschitz) * r) := by
      gcongr
      exact hshift u
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
namespace OAI

section

namespace Erdos3

noncomputable def residueSmoothPMF {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) : PMF (K × I → ℤ) :=
  (residueSmoothIndexPMF residue modulus hmodulus V hV hZ).map
    (residueLatticeArray residue modulus)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residue_smooth_row_shift_transfer {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] {h : ℕ}
    (N modulus : I → ℕ) (hN : ∀ j, 0 < N j) (hmodulus : ∀ j, 0 < modulus j)
    (rows : Fin h → K → ℤ) (residue : K × I → ℤ)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V))
    (hV1 : ∀ z, 1 ≤ residueProfileWidth modulus V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ z, 1 / residueProfileWidth modulus V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (K × I) *
      ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {C r B : ℝ} (hC : 0 ≤ C) (hrows : ∀ i k, |(rows i k : ℝ)| ≤ C) (hr : 0 ≤ r)
    (hmove : ∀ z, (h : ℝ) * C * ((modulus z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z)
    (Φ : (K → I → ℝ) → ℂ) (hΦ : ∀ b, ‖Φ b‖ ≤ 1)
    (hlocal : ∀ b : K → I → ℝ,
      ‖𝔼 x : Fin h → ∀ j, Fin (N j),
        Φ (rowShiftedTuple b rows
          (fun (y : ∀ j, Fin (N j)) j => (modulus j : ℝ) * ((y j).val : ℝ)) x)‖ ≤ B) :
    ‖∑' x, ((residueSmoothIndexPMF residue modulus hmodulus V hV hZ x).toReal : ℂ) *
      Φ (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (K × I) *
        ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * r + B := by
  let : ∀ j, Nonempty (Fin (N j)) := fun j => ⟨⟨0, hN j⟩⟩
  apply shiftedSmoothProductPMF_shift_transfer (residueProfileCenter residue modulus)
    (residueProfileWidth modulus V) (residueProfileWidth_pos modulus V hmodulus hV)
    hZ hV1 hδ hδ1 hmesh hsmall (integerRowShift (N := N) rows (fun _ => 1))
    (fun x => residueRowShift_normalized_bound rows modulus hmodulus x V hV hC hrows hr hmove)
    (fun x => Φ (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ))) (fun _ => hΦ _)
  intro x
  simpa only [residueLatticeArray_rowShift] using
    hlocal (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DilationPairFiltration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def dilationPairSecond (q : ℚ) : F.dilationPairSubalgebra q →ₗ⁅ℚ⁆ L :=
  (LieHom.snd ℚ L L).comp (F.dilationPairSubalgebra q).incl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LieFiniteProduct
namespace OAI

section

namespace Erdos3

open Module

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)]

variable {R : Type*} [CommRing R] [∀ a, LieAlgebra R (M a)]

variable {L : Type*} [LieRing L] [LieAlgebra R L]

section Coordinates

variable [Fintype α] {κ : α → Type*} [∀ a, Fintype (κ a)]
  [∀ a, LieAlgebra ℚ (M a)]

omit [∀ a, Fintype (κ a)] in

theorem lie_pi_structure_height (f : ∀ a, Basis (κ a) ℚ (M a)) {H : ℕ} (hH : 1 ≤ H)
    (hf : ∀ a i j k, RationalHeightLE (lieStructureConstants (f a) i j k) H) :
    ∀ i j k, RationalHeightLE (lieStructureConstants (Pi.basis f) i j k) H := by
  classical
  rintro ⟨a, i⟩ ⟨b, j⟩ ⟨c, k⟩
  unfold lieStructureConstants
  rw [Pi.basis_repr, lie_pi_apply, Pi.basis_apply, Pi.basis_apply]
  by_cases hac : a = c
  · subst c
    rw [Pi.single_eq_same]
    by_cases hba : b = a
    · subst b
      rw [Pi.single_eq_same]
      exact hf a i j k
    · rw [Pi.single_eq_of_ne (Ne.symm hba), lie_zero, map_zero, Finsupp.zero_apply]
      exact rationalHeightLE_zero hH
  · rw [Pi.single_eq_of_ne (Ne.symm hac), zero_lie, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero hH

end Coordinates
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultidegreeDilationPair
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def MultidegreeLieFiltration.ofLayers
    (P : (σ → ℕ) → Submodule ℚ L) (hmono : Antitone P) (hzero : P 0 = ⊤)
    (hlie : ∀ {a b : σ → ℕ} {x y : L}, x ∈ P a → y ∈ P b → ⁅x, y⁆ ∈ P (a + b))
    (hpositive : multidegreeTotalLayer P 1 = ⊤)
    (bound : σ → ℕ) (hterminal : ∀ a, ¬a ≤ bound → P a = ⊥)
    (s : ℕ) (hs : (∑ i, bound i) ≤ s) : MultidegreeLieFiltration σ L s bound where
  ordinary :=
    { layer := multidegreeTotalLayer P
      antitone := multidegreeTotalLayer_antitone P
      one_eq_top := hpositive
      lie_mem := multidegreeTotalLayer_lie_mem P hlie
      terminal := multidegreeTotalLayer_terminal P bound hterminal s hs }
  layer := P
  antitone := hmono
  zero_eq_top := hzero
  lie_mem := hlie
  terminal := hterminal
  degree_eq := multidegreeTotalLayer_eq P

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHConjugationLinear
namespace OAI

section

namespace Erdos3

open Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]

namespace NilpotentLieBCHGroup

variable {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]

open scoped Manifold ContDiff

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ⁅ℝ⁆ M)

theorem mapReal_basisHomeomorph (g : NilpotentLieBCHGroup L s hnil) :
    basisHomeomorph f (mapReal (hM := hM) φ g) =
      basisCoordinateMap e f φ.toLinearMap (basisHomeomorph e g) := by
  change f.equivFun (φ g.coord) = f.equivFun (φ (e.equivFun.symm (e.equivFun g.coord)))
  rw [LinearEquiv.symm_apply_apply]

theorem mapReal_basisHomeomorph_symm (x : ι → ℝ) :
    mapReal (hnil := hnil) (hM := hM) φ ((basisHomeomorph e).symm x) =
      (basisHomeomorph f).symm (basisCoordinateMap e f φ.toLinearMap x) := by
  apply (basisHomeomorph f).injective
  rw [mapReal_basisHomeomorph e f, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

theorem contMDiff_mapReal (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := basisChartedSpace (hnil := hM) f
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) n (mapReal (hnil := hnil) (hM := hM) φ) := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  apply ContMDiff.of_comp_isOpenEmbedding (basisHomeomorph f).isOpenEmbedding
  have hc := (basisCoordinateMap e f φ.toLinearMap).contDiff.contMDiff.comp
    (contMDiff_basisHomeomorph (hnil := hnil) e n)
  have he : (basisHomeomorph f) ∘ mapReal (hnil := hnil) (hM := hM) φ =
      basisCoordinateMap e f φ.toLinearMap ∘ basisHomeomorph e :=
    funext (mapReal_basisHomeomorph e f φ)
  rw [he]
  exact hc

theorem mfderiv_mapReal_coordinates (g : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := basisChartedSpace (hnil := hM) f
    mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) (mapReal (hnil := hnil) (hM := hM) φ) g v =
      basisCoordinateMap e f φ.toLinearMap v := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  have hm := (contMDiff_mapReal (hnil := hnil) (hM := hM) e f φ 1).mdifferentiableAt
    (x := g) one_ne_zero
  have heq : writtenInExtChartAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) g (mapReal (hM := hM) φ) =
      basisCoordinateMap e f φ.toLinearMap := by
    funext x
    simp only [writtenInExtChartAt, Function.comp_apply, basis_extChartAt_apply,
      basis_extChartAt_symm_apply, mapReal_basisHomeomorph e f, Homeomorph.apply_symm_apply]
  rw [hm.mfderiv, heq]
  simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ,
    ContinuousLinearMap.fderiv]
  rfl

theorem basisCoordinateMap_rightTranslate (g : NilpotentLieBCHGroup L s hnil) (x : ι → ℝ) :
    basisCoordinateMap e f φ.toLinearMap (rightTranslate e g x) =
      rightTranslate f (mapReal (hM := hM) φ g) (basisCoordinateMap e f φ.toLinearMap x) := by
  change basisCoordinateMap e f φ.toLinearMap
    (basisHomeomorph e ((basisHomeomorph e).symm x * g)) = _
  rw [← mapReal_basisHomeomorph e f φ, map_mul, mapReal_basisHomeomorph_symm e f φ]
  rfl

end NilpotentLieBCHGroup
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHLatticeImageGap
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped ContDiff

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

theorem rightVelocity_mapReal (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ⁅ℝ⁆ M)
    (g : NilpotentLieBCHGroup L s hnil) :
    (rightVelocity f (mapReal (hM := hM) φ g)).comp (basisCoordinateMap e f φ.toLinearMap) =
      (basisCoordinateMap e f φ.toLinearMap).comp (rightVelocity e g) := by
  let A := basisCoordinateMap e f φ.toLinearMap
  have hc : rightTranslate f (mapReal (hM := hM) φ g⁻¹) ∘ A = A ∘ rightTranslate e g⁻¹ := by
    funext x
    exact (basisCoordinateMap_rightTranslate e f φ g⁻¹ x).symm
  have hi := (contDiff_rightTranslate e g⁻¹ 1).differentiable (by decide)
  have ho := (contDiff_rightTranslate f (mapReal (hM := hM) φ g⁻¹) 1).differentiable (by decide)
  have hd := congrArg (fun F : (ι → ℝ) → (κ → ℝ) => fderiv ℝ F (basisHomeomorph e g)) hc
  rw [fderiv_comp _ ho.differentiableAt A.differentiableAt,
    fderiv_comp _ A.differentiableAt hi.differentiableAt,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv] at hd
  dsimp only [A] at hd
  rw [← mapReal_basisHomeomorph e f φ, map_inv] at hd
  exact hd

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution
namespace OAI


namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {σ τ υ R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

theorem map_substitute (f : σ → MvPolynomial τ R) (g : V →ₗ[R] W)
    (p : VectorPolynomial σ R V) :
    map g (substitute f p) = substitute f (map g p) := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v => rfl
  | add p q hp hq => simp only [map_add, hp, hq]

theorem substitute_comp (f : σ → MvPolynomial τ R) (g : τ → MvPolynomial υ R)
    (p : VectorPolynomial σ R V) :
    substitute g (substitute f p) = substitute (fun i => MvPolynomial.aeval (R := R) g (f i)) p := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v =>
    simp only [substitute_tmul]
    rw [MvPolynomial.comp_aeval_apply]
  | add p q hp hq => simp only [map_add, hp, hq]

end Erdos3.VectorPolynomial


namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

noncomputable def coefficientModePolynomial {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W) :
    MvPolynomial (K × I) ℝ :=
  ∑ d ∈ (coefficients p).support,
    mapPolynomialCoefficients ((TensorProduct.curry L).flip (coefficients p d))
      (parameterPolynomialPullback (MvPolynomial.monomial d 1))

theorem coefficientModePolynomial_eval {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W)
    (v : K → I → ℝ) :
    MvPolynomial.eval (fun z => v z.1 z.2) (coefficientModePolynomial L p) =
      L (substitute (fun j => rowPolynomial (fun k => v k j)) p) := by
  unfold coefficientModePolynomial
  rw [map_sum]
  conv_rhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, monomial, substitute_tmul,
    mapPolynomialCoefficients_eval, MvPolynomial.algebraMap_eq, parameterPolynomialPullback_eval]
  rfl

theorem coefficientModePolynomial_degree {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W)
    {h : ℕ} (hp : Homogeneous h p) :
    (coefficientModePolynomial L p).totalDegree ≤ h := by
  unfold coefficientModePolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  apply (mapPolynomialCoefficients_degree _ _).trans
  apply parameterPolynomialPullback_degree
  have hsum : d.sum (fun _ n => n) = h := by
    simpa only [Finsupp.degree_eq_weight_one, Finsupp.weight_apply, Pi.one_def,
      smul_eq_mul, mul_one] using homogeneous_support_degree hp hd
  exact (MvPolynomial.totalDegree_monomial_le d 1).trans_eq hsum

end Erdos3.VectorPolynomial


namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adapted_map (H : NilpotentLieFiltration M t) (f : L →ₗ[ℚ] M)
    (hf : ∀ i, ∀ a ∈ F.layer i, f a ∈ H.layer i)
    (w : σ → ℕ) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) :
    H.Adapted w (VectorPolynomial.map f p) := by
  apply (H.adapted_iff_coefficients w _).mpr
  intro α
  rw [coefficients_map]
  exact hf _ _ ((F.adapted_iff_coefficients w p).mp hp α)

end Erdos3.NilpotentLieFiltration


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedAxisScaling
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

theorem isWeightedHomogeneous_aeval_monomial (v : σ → ℕ) (w : τ → ℕ)
    (f : σ → MvPolynomial τ R)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (v i)) (a : σ →₀ ℕ) (r : R) :
    (aeval f (monomial a r)).IsWeightedHomogeneous w (Finsupp.weight v a) := by
  classical
  rw [aeval_monomial]
  have hprod := IsWeightedHomogeneous.prod a.support (fun i => f i ^ a i)
    (fun i => a i * v i) (fun i _ => by simpa using (hf i).pow (a i))
  have hweight : (∑ i ∈ a.support, a i * v i) = Finsupp.weight v a := by
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.cast_id]
  rw [hweight] at hprod
  simpa only [MvPolynomial.algebraMap_eq, Finsupp.prod] using hprod.C_mul r

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreeRankSunflower
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

variable {ι : Type*} [Nonempty ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s r : ℕ}

theorem pi_associatedDegree (F : ∀ i, DegreeRankLieFiltration (L i) s r) :
    (pi F).associatedDegree = NilpotentLieFiltration.pi (fun i => (F i).associatedDegree) := rfl

def piLayerEquiv (F : ∀ i, DegreeRankLieFiltration (L i) s r) (d j : ℕ) :
    (∀ i, (F i).layer d j) ≃ₗ[ℚ] (pi F).layer d j where
  toFun x := ⟨fun i => x i, (mem_pi_layer F d j _).mpr (fun i => (x i).property)⟩
  invFun x i := ⟨x.val i, (mem_pi_layer F d j _).mp x.property i⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem monomial_mem_polynomialFiltration (d i : ℕ) (α : σ →₀ ℕ) {x : L}
    (hx : x ∈ F.layer d i) :
    monomial (R := ℚ) α x ∈ (F.polynomialFiltration (σ := σ)).layer d i :=
  monomial_mem_coefficientSubmodule (F.layer d i) α hx

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem lieTreeEval_mem_length (v : I → L) (d : I → ℕ)
    (hv : ∀ i, v i ∈ F.layer (d i) 1) (a : FreeMagma I) :
    lieTreeEval v a ∈ F.layer (lieTreeWeight d a) a.length := by
  induction a using FreeMagma.rec with
  | of i => exact hv i
  | mul a b ha hb => exact F.lie_mem ha hb

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def horizontalTreeValue (d : I → ℕ) (a : FreeMagma I)
    (v : ∀ i, F.HigherHorizontal (d i)) : L :=
  lieTreeEval (fun i => (F.higherHorizontalRepresentative (d i) (v i)).val) a

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreePermutationFiltration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}

theorem layer_eq_bot_above_step (F : NilpotentLieFiltration L s) {i : ℕ}
    (hi : s < i) : F.layer i = ⊥ := by
  apply bot_unique
  rw [← F.terminal]
  exact F.antitone (by omega)

def raiseStep (F : NilpotentLieFiltration L s) (hst : s ≤ t) : NilpotentLieFiltration L t where
  layer := F.layer
  antitone := F.antitone
  one_eq_top := F.one_eq_top
  lie_mem := F.lie_mem
  terminal := F.layer_eq_bot_above_step (by omega)

end Erdos3.NilpotentLieFiltration

namespace Erdos3

open Module

theorem bchSubgroupCoordinates_changeStep
    {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s t : ℕ}
    (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (ht : LieModule.lowerCentralSeries ℚ L L t = ⊥)
    (e : Basis ι ℚ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hs)) :
    bchSubgroupCoordinates e (Γ.map (NilpotentLieBCHGroup.changeStep hs ht).toMonoidHom) =
      bchSubgroupCoordinates e Γ := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg, heq⟩ := Subgroup.mem_map.mp hx
    have hcoord := congrArg NilpotentLieBCHGroup.coord heq
    have hg' : g = ⟨e.equivFun.symm x⟩ := NilpotentLieBCHGroup.ext hcoord
    change (⟨e.equivFun.symm x⟩ : NilpotentLieBCHGroup L s hs) ∈ Γ
    rwa [← hg']
  · intro hx
    exact Subgroup.mem_map.mpr ⟨⟨e.equivFun.symm x⟩, hx, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorHomogenization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

theorem homogeneous_finset_sum {I A R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    {h : ℕ} (s : Finset A) (p : A → VectorPolynomial I R W)
    (hp : ∀ a ∈ s, Homogeneous h (p a)) : Homogeneous h (∑ a ∈ s, p a) := by
  intro d hd
  simp only [map_sum, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero (fun a ha => hp a ha d hd)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

noncomputable def homogenize {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (h : ℕ) : VectorPolynomial I R W →ₗ[R] VectorPolynomial (Option I) R W :=
  (Finsupp.lsum R (fun d => TensorProduct.mk R (MvPolynomial (Option I) R) W
    (homogenizingMonomial h d))).comp coefficients.toLinearMap

theorem homogenize_apply {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (h : ℕ) (p : VectorPolynomial I R W) :
    homogenize h p = ∑ d ∈ (coefficients p).support,
      homogenizingMonomial h d ⊗ₜ[R] coefficients p d := by
  simp only [homogenize, LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lsum_apply,
    Finsupp.sum, TensorProduct.mk_apply]

theorem dehomogenize_homogenize {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (h : ℕ) (p : VectorPolynomial I R W) :
    substitute dehomogenizingSubstitution (homogenize h p) = p := by
  rw [homogenize_apply, map_sum]
  simp only [substitute_tmul, homogenizingMonomial_dehomogenize]
  exact sum_monomial_coefficients p

theorem homogenize_homogeneous {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (h : ℕ) (p : VectorPolynomial I R W) (hp : DegreeLE (1 : I → ℕ) h p) :
    Homogeneous h (homogenize h p) := by
  rw [homogenize_apply]
  apply homogeneous_finset_sum
  intro d hd
  have hb : d.degree ≤ h := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      (degreeLE_iff (1 : I → ℕ) h p).mp hp d hd
  exact homogeneous_tmul (homogenizingMonomial_homogeneous h d hb) _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DehomogenizedExponent
namespace OAI

section

namespace Erdos3

theorem VectorPolynomial.dehomogenize_monomial {K R W : Type*}
    [CommRing R] [AddCommGroup W] [Module R W]
    (d : Option K →₀ ℕ) (w : W) :
    VectorPolynomial.substitute dehomogenizingSubstitution (VectorPolynomial.monomial (R := R) d w) =
      VectorPolynomial.monomial (R := R) d.some w := by
  simp only [VectorPolynomial.monomial, VectorPolynomial.substitute_tmul, Erdos3.dehomogenize_monomial]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedAmbientModeWitness
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators TensorProduct Classical

theorem exists_bounded_ambient_mode_witness {K J : Type*} [Fintype K] [Fintype J] {q : ℕ}
    (W : Submodule ℝ (J → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {H D C : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (Λ : VectorPolynomial (Option K) ℝ (J → ℝ) →ₗ[ℝ] ℝ) (h : ℕ)
    (hbound : VectorPolynomial.MonomialRowBound Λ h C)
    (hnonfactor : ¬ ∃ M : (Finset (Fin q) → W) →ₗ[ℝ] ℝ,
      ∀ p, VectorPolynomial.Homogeneous h p →
        Λ (VectorPolynomial.map W.subtype p) = M (VectorPolynomial.siteEvaluation
          (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ P : Fin h → MvPolynomial (Option K) ℤ,
      (∀ i, (P i).IsHomogeneous 1 ∧
        realPolynomialMass (map (Int.castRingHom ℝ) (P i)) ≤ integerCubeWitnessBound q H D) ∧
      (∀ s : Finset (Fin q), ∃ i, eval (affineSite root difference s) (P i) = 0) ∧
      (∀ j, |VectorPolynomial.contractedRow Λ (map (Int.castRingHom ℝ) (∏ i, P i)) j| ≤
        C * integerCubeWitnessBound q H D ^ h) ∧
      ∃ w : W, (∑ j, VectorPolynomial.contractedRow Λ
        (map (Int.castRingHom ℝ) (∏ i, P i)) j * w.val j) ≠ 0 := by
  obtain ⟨selection, hdet⟩ := integer_difference_exists_pivot difference hlin
  obtain ⟨forms, hlen, hforms, hz, w, hw⟩ := exists_integral_vector_mode_witness
    root difference selection hdet hH hD hroot hdiff
    (Λ.comp (VectorPolynomial.map W.subtype)) h hnonfactor
  simp only [Fintype.card_fin] at hforms
  subst h
  let P : Fin forms.length → MvPolynomial (Option K) ℤ := forms.get
  have hmem (i : Fin forms.length) : P i ∈ forms := List.get_mem _ _
  have hprod : (∏ i, P i) = forms.prod := by
    rw [← Fin.prod_ofFn, List.ofFn_get]
  refine ⟨P, (fun i => hforms _ (hmem i)), ?_, ?_, w, ?_⟩
  · intro s
    exact List.exists_mem_iff_get.mp (hz s)
  · intro j
    rw [map_prod]
    exact VectorPolynomial.contractedRow_prod_bound Λ
      (fun i => map (Int.castRingHom ℝ) (P i))
      (fun i => (hforms _ (hmem i)).1.map _) (fun i => (hforms _ (hmem i)).2) hC hbound j
  · rw [VectorPolynomial.contractedRow_apply, hprod]
    exact hw

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientSubspace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem affineParameterSubstitution_eval {I K : Type*} [Fintype K]
    (b : Option K → I → ℝ) (t : K → ℝ) (j : I) :
    MvPolynomial.aeval t (affineParameterSubstitution b j) =
      b none j + ∑ k, b (some k) j * t k := by
  change MvPolynomial.eval t (affineParameterSubstitution b j) = _
  rw [affineParameterSubstitution, map_add, MvPolynomial.eval_C, rowPolynomial_eval]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

theorem rowPolynomial_integer_site {I K : Type*} [Fintype K]
    (site : K → ℤ) (b : K → I → ℝ) :
    (fun i => MvPolynomial.aeval (fun k => (site k : ℝ)) (rowPolynomial (fun k => b k i))) =
      integerSiteValue site b := by
  funext i
  change MvPolynomial.eval (fun k => (site k : ℝ)) (rowPolynomial (fun k => b k i)) = _
  rw [rowPolynomial_eval]
  change (∑ k, b k i * (site k : ℝ)) = (∑ k, site k • b k) i
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  change b k i * (site k : ℝ) = site k • b k i
  rw [zsmul_eq_mul, mul_comm]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open CircleFourier _root_.MvPolynomial
open scoped BigOperators Classical

theorem finiteSitePhaseRemoval_of_annihilates {h : ℕ} {S K X V : Type*}
    [Fintype S] [Fintype K] [Fintype X] [Nonempty X] [AddCommGroup V]
    (hh : 0 < h) (site : S → K → ℤ) (rows : Fin h → K → ℤ)
    (hzero : ∀ s, ∃ i, (∑ k, rows i k * site s k) = 0) :
    FiniteSitePhaseRemoval (X := X) (V := V) site rows := by
  intro base shift phase test htest
  exact row_shifted_site_phase_cauchySchwarz hh site base rows shift hzero phase test htest

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSiteRemoval
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial CircleFourier
open scoped BigOperators Classical

theorem finiteSitePhaseRemoval_polynomial {h : ℕ} {S K J X : Type*}
    [Fintype S] [Fintype K] [Fintype X]
    (site : S → K → ℤ) (rows : Fin h → K → ℤ)
    (hremove : FiniteSitePhaseRemoval (X := X) (V := J → ℝ) site rows)
    (base : K → J → ℝ) (shift : X → J → ℝ)
    (P : MvPolynomial (K × J) ℝ) (hP : P.totalDegree ≤ h)
    (test : S → (J → ℝ) → ℂ) (htest : ∀ s v, ‖test s v‖ ≤ 1) :
    ‖𝔼 x, character ((eval (fun z => rowShiftedTuple base rows shift x z.1 z.2) P : ℝ) : CircleFourier.Circle) *
      ∏ s, test s (integerSiteValue (site s) (rowShiftedTuple base rows shift x))‖ ^ (2 ^ h) ≤
      ‖𝔼 u : Fin h → X, 𝔼 v : Fin h → X, character ((polynomialTopSymbol h P
        (fun i z => (rows i z.1 : ℝ) * (shift (u i) z.2 - shift (v i) z.2)) : ℝ) : CircleFourier.Circle)‖ := by
  have hc := hremove base shift (fun tuple => eval (fun z => tuple z.1 z.2) P) test htest
  simpa only [row_shift_difference_eq_topSymbol base rows shift P hP] using hc

theorem row_polynomial_site_cauchySchwarz {h : ℕ} {S K J X : Type*}
    [Fintype S] [Fintype K] [Fintype X] [Nonempty X] (hh : 0 < h)
    (site : S → K → ℤ) (rows : Fin h → K → ℤ)
    (hzero : ∀ s, ∃ i, (∑ k, rows i k * site s k) = 0)
    (base : K → J → ℝ) (shift : X → J → ℝ)
    (P : MvPolynomial (K × J) ℝ) (hP : P.totalDegree ≤ h)
    (test : S → (J → ℝ) → ℂ) (htest : ∀ s v, ‖test s v‖ ≤ 1) :
    ‖𝔼 x, character ((eval (fun z => rowShiftedTuple base rows shift x z.1 z.2) P : ℝ) : CircleFourier.Circle) *
      ∏ s, test s (integerSiteValue (site s) (rowShiftedTuple base rows shift x))‖ ^ (2 ^ h) ≤
      ‖𝔼 u : Fin h → X, 𝔼 v : Fin h → X, character ((polynomialTopSymbol h P
        (fun i z => (rows i z.1 : ℝ) * (shift (u i) z.2 - shift (v i) z.2)) : ℝ) : CircleFourier.Circle)‖ :=
  finiteSitePhaseRemoval_polynomial site rows
    (finiteSitePhaseRemoval_of_annihilates hh site rows hzero) base shift P hP test htest

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientModeLowerTerms
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem fullShiftExponent_multinomial (n : ℕ) : (fullShiftExponent n).multinomial = n.factorial := by
  rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _), Nat.multinomial]
  simp only [fullShiftExponent_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Nat.factorial_one, Finset.prod_const_one, Nat.div_one]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem polynomialTopSymbol_add {I : Type*} (h : ℕ) (P Q : MvPolynomial I ℝ)
    (direction : Fin h → I → ℝ) :
    polynomialTopSymbol h (P + Q) direction =
      polynomialTopSymbol h P direction + polynomialTopSymbol h Q direction := by
  simp only [polynomialTopSymbol, map_add, MvPolynomial.coeff_add]

theorem polynomialTopSymbol_eq_zero_of_degree_lt {I : Type*} {h : ℕ}
    (Q : MvPolynomial I ℝ) (hQ : Q.totalDegree < h) (direction : Fin h → I → ℝ) :
    polynomialTopSymbol h Q direction = 0 := by
  simp only [polynomialTopSymbol, homogeneousComponent_eq_zero h Q hQ, map_zero,
    MvPolynomial.coeff_zero]

theorem polynomialTopSymbol_add_lower {I : Type*} {h : ℕ}
    (P Q : MvPolynomial I ℝ) (hQ : Q.totalDegree < h) (direction : Fin h → I → ℝ) :
    polynomialTopSymbol h (P + Q) direction = polynomialTopSymbol h P direction := by
  rw [polynomialTopSymbol_add, polynomialTopSymbol_eq_zero_of_degree_lt Q hQ, add_zero]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem full_coefficient_linear_pow {R : Type*} [CommRing R] (n : ℕ) (a : Fin n → R) :
    ((∑ i, a i • X i : MvPolynomial (Fin n) R) ^ n).coeff (fullShiftExponent n) =
      (n.factorial : R) * ∏ i, a i := by
  rw [coeff_linearCombination_X_pow_of_fintype, fullShiftExponent_sum]
  simp only [ite_true, fullShiftExponent_multinomial]
  rw [(fullShiftExponent n).prod_fintype _ (fun _ => pow_zero _)]
  simp only [fullShiftExponent_apply, pow_one]

theorem linear_power_full_difference {R : Type*} [CommRing R] (n : ℕ) (a : Fin n → R) :
    additiveBoxDifference n (fun (x : Fin n → R) (_ : Unit) => (∑ i, a i * x i) ^ n)
      (fun _ => 1) (fun _ => 0) () = (n.factorial : R) * ∏ i, a i := by
  have he : (fun (x : Fin n → R) (_ : Unit) => (∑ i, a i * x i) ^ n) =
      (fun x (_ : Unit) => eval x ((∑ i, a i • X i : MvPolynomial (Fin n) R) ^ n)) := by
    funext x _
    simp only [smul_eq_C_mul, map_pow, map_sum, map_mul, eval_C, eval_X]
  rw [he, full_mixed_difference_of_totalDegree _ (linear_pow_totalDegree_le n a),
    full_coefficient_linear_pow]
  simp

theorem linear_power_full_difference_algebra {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (n : ℕ) (a : Fin n → S) :
    additiveBoxDifference n (fun (x : Fin n → R) (_ : Unit) => (∑ i, x i • a i) ^ n)
      (fun _ => 1) (fun _ => 0) () = (n.factorial : S) * ∏ i, a i := by
  have hm := additiveBoxDifference_map n (fun _ => algebraMap R S)
    (fun (x : Fin n → S) (_ : Unit) => (∑ i, a i * x i) ^ n)
    (fun _ => 1) (fun _ => 0) ()
  simp only [map_one, map_zero] at hm
  simpa only [Algebra.smul_def, mul_comm] using hm.trans (linear_power_full_difference n a)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuarticBohrProgression
namespace OAI

section

namespace Erdos3.BohrProgression

theorem exists_proper_progression_of_quartic_bounds {N : ℕ} [NeZero N]
    (B : CyclicBohr.Set N) {C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hB : 0 < B.radius) (hB1 : B.radius ≤ 1)
    (hrank : (B.rank : ℝ) ≤ 1 + C * (p + 1) ^ 4)
    (hwidth : Real.exp (-(C * (p + 1))) ≤ B.radius) :
    ∃ Q : CyclicCenteredGAP N,
      (Q.rank : ℝ) ≤ 2 + C * (p + 1) ^ 4 ∧ Q.Proper ∧ Q.carrier ⊆ B.carrier ∧
      Real.exp (-(11 * (C + 2) ^ 2 * (p + 1) ^ 8)) * N ≤ (Q.carrier.card : ℝ) := by
  obtain ⟨Q, hr, hQ, hsub, hcard⟩ := exists_large_proper_progression_all B hB hB1
    (by positivity : 0 ≤ C * (p + 1)) hwidth
  have hrR : (Q.rank : ℝ) ≤ B.rank + 1 := by exact_mod_cast hr
  refine ⟨Q, by linarith, hQ, hsub, ?_⟩
  let u := p + 1
  let m := (B.rank : ℝ) + 1
  have hu : 1 ≤ u := by dsimp [u]; linarith
  have hu4 : 1 ≤ u ^ 4 := one_le_pow₀ hu
  have huu4 : u ≤ u ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hu (by decide : 1 ≤ (4 : ℕ))
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hm : m ≤ (C + 2) * u ^ 4 := by dsimp [m]; nlinarith
  have hw : C * u ≤ (C + 2) * u ^ 4 := by nlinarith
  have hprod : m * (C * u) ≤ ((C + 2) * u ^ 4) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hm hw (by positivity : 0 ≤ C * u)
      (by positivity : 0 ≤ (C + 2) * u ^ 4)
  have hsquare : m ^ 2 ≤ ((C + 2) * u ^ 4) ^ 2 :=
    pow_le_pow_left₀ hm0 hm 2
  have hcost : m * (C * u) + 10 * m ^ 2 ≤ 11 * (C + 2) ^ 2 * u ^ 8 := by
    calc
      _ ≤ 11 * ((C + 2) * u ^ 4) ^ 2 := by linarith
      _ = _ := by ring
  apply le_trans (b := Real.exp (-(m * (C * u) + 10 * m ^ 2)) * N) ?_ hcard
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
  apply Real.exp_le_exp.mpr
  linarith

end Erdos3.BohrProgression

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFiberCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coefficientConstantCenter :
    CoefficientTorus (K := K) U →+ CoefficientTorus (K := K) U :=
  (constantCoefficientTorusMap U).comp (coefficientEvaluationTorus U 0)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedLieQuotient
namespace OAI

section

namespace Erdos3

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L]

namespace NilpotentLieFiltration

variable {s t : ℕ} (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
  (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
  (S : Set ι) (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))

include hlayers in
theorem supportedQuotientBasis_layers (j : ℕ) :
    (F.quotientLie I hI).layer j = Submodule.span ℚ
      (supportedQuotientBasis b I.toSubmodule S hspan '' {i | j ≤ w i}) := by
  change (F.layer j).map I.toSubmodule.mkQ = _
  rw [hlayers j]
  exact supportedQuotientBasis_map_span b I.toSubmodule S hspan {i | j ≤ w i}

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrTorusApproximation
namespace OAI

section

namespace Erdos3.CyclicBohr.Set

open _root_.Finset
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

@[simp] theorem radius_ndilate (B : Set N) (t : ℝ≥0) :
    (B.ndilate t).radius = t * B.radius := by simp [ndilate]

end Erdos3.CyclicBohr.Set

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealPolynomialBCH
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def polynomialBCHMap (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (P : ι → MvPolynomial σ ℚ) (x : σ → ℤ) : NilpotentLieBCHGroup L s hnil :=
  ⟨e.equivFun.symm (fun i => eval (fun j => (x j : ℚ)) (P i))⟩

omit [Fintype σ] in
@[simp] theorem polynomialBCHMap_coordinates (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (P : ι → MvPolynomial σ ℚ) (x : σ → ℤ) :
    e.equivFun (polynomialBCHMap e hnil P x).coord = fun i => eval (fun j => (x j : ℚ)) (P i) :=
  e.equivFun.apply_symm_apply _

end Erdos3

end

section

namespace Erdos3

open Module _root_.MvPolynomial
open scoped Manifold ContDiff TensorProduct

variable {ι σ L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realPolynomialBCHMap (e : Basis ι ℝ L)
    (P : ι → MvPolynomial σ ℚ) (x : σ → ℝ) : NilpotentLieBCHGroup L s hnil :=
  ⟨e.equivFun.symm (fun i => aeval x (P i))⟩

@[simp] theorem realPolynomialBCHMap_coordinates (e : Basis ι ℝ L)
    (P : ι → MvPolynomial σ ℚ) (x : σ → ℝ) :
    e.equivFun (realPolynomialBCHMap (hnil := hnil) e P x).coord =
      fun i => aeval x (P i) :=
  e.equivFun.apply_symm_apply _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {G : Type*} [Fintype G] [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable def allocatedPrincipalSides : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ :=
  fun j => layerSamplerSides (G := G) B U basis R S.value (.inr j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.GeneratorCells
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace BooleanCutTest

omit [Fintype Ω] in
@[simp]
theorem eval_of_not_mem (A : BooleanCutTest Ω) {x : Ω} (hx : x ∉ A) :
    A.eval x = 0 :=
  finsetIndicator_of_not_mem hx

end BooleanCutTest

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RelativeSliceAffineThreeFactorLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)

def principalAffineIntervalPoint (t : ∀ j, Fin (H j)) : PrincipalIntegerTuples B h Empty L :=
  fun j _ => ⟨start j + (step j : ℤ) * (t j).val, Finset.mem_Ico.mpr
    ⟨(neg_nonpos.mpr (Int.natCast_nonneg _)).trans (hinside j (t j)).1, (hinside j (t j)).2⟩⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.HomogeneousLieSpan
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

structure LieGradingExpansion (v : I → L) (g : I → σ →₀ ℕ) where
  expand : L →ₗ[ℚ] VectorPolynomial σ ℚ L
  expand_tree : ∀ a, expand (lieTreeEval v a) = monomial (lieTreeMultidegree g a) (lieTreeEval v a)
  eval_one : ∀ x, eval (fun _ : σ => (1 : ℚ)) (expand x) = x

namespace LieGradingExpansion

variable {v : I → L} {g : I → σ →₀ ℕ} (E : LieGradingExpansion v g)

noncomputable def component (α : σ →₀ ℕ) : L →ₗ[ℚ] L :=
  (Finsupp.lapply α).comp (coefficients.toLinearMap.comp E.expand)

@[simp] theorem component_apply (α : σ →₀ ℕ) (x : L) :
    E.component α x = coefficients (E.expand x) α := rfl

end LieGradingExpansion
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MarkedLieSpan
namespace OAI

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L]

def markedLieSpan (v : I → L) (w : I → ℕ) (marked : I → Bool) (d k l : ℕ) : Submodule ℚ L :=
  Submodule.span ℚ {x | ∃ a : FreeMagma I, d ≤ lieTreeWeight w a ∧
    k ≤ lieTreeMarkedCount marked a ∧ l ≤ a.length ∧ lieTreeEval v a = x}

theorem markedLieSpan_antitone (v : I → L) (w : I → ℕ) (marked : I → Bool)
    {d e k m l n : ℕ} (hde : d ≤ e) (hkm : k ≤ m) (hln : l ≤ n) :
    markedLieSpan v w marked e m n ≤ markedLieSpan v w marked d k l := by
  apply Submodule.span_mono
  rintro x ⟨a, hd, hk, hl, rfl⟩
  exact ⟨a, hde.trans hd, hkm.trans hk, hln.trans hl, rfl⟩

theorem markedLieSpan_lie_mem (v : I → L) (w : I → ℕ) (marked : I → Bool)
    {d e k m l n : ℕ} {x y : L}
    (hx : x ∈ markedLieSpan v w marked d k l)
    (hy : y ∈ markedLieSpan v w marked e m n) :
    ⁅x, y⁆ ∈ markedLieSpan v w marked (d + e) (k + m) (l + n) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, hd, hk, hl, rfl⟩ := hx
    obtain ⟨b, he, hm, hn, rfl⟩ := hy
    exact Submodule.subset_span ⟨a * b, Nat.add_le_add hd he,
      Nat.add_le_add hk hm, Nat.add_le_add hl hn, rfl⟩
  | zero_left y _ => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right x _ => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left x y z _ _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul_left c x y _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ c h
  | smul_right c x y _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ c h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MarkedPolynomialGenerators
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem markedLieSpan_degree_zero_eq_one (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hw : ∀ i, 0 < w i) (k l : ℕ) :
    markedLieSpan v w marked 0 k l = markedLieSpan v w marked 1 k l := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro x ⟨a, _, hk, hl, rfl⟩
    exact ⟨a, a.length_pos.trans_le (lieTree_length_le_weight w hw a), hk, hl, rfl⟩
  · exact markedLieSpan_antitone v w marked (Nat.zero_le 1) le_rfl le_rfl

end Erdos3

end

end OAI
end


