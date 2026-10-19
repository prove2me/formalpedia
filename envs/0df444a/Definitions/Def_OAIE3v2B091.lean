-- Prove2me | Definitions.Def_OAIE3v2B091
-- name    : OAIE3v2B091
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:22:17.704704+00:00
-- url     : https://prove2.me/theorems/dd8ce7e9-4e38-45af-870f-927fc05f684f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 92 of 311
-- statement:
--   Definitions bundle 92 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B068`, `OAIE3v2B069`, `OAIE3v2B070`, `OAIE3v2B071`, `OAIE3v2B072` of this split.
--
--   Modules: `Estimates/BoundedCommonSiteResidual.lean`, `Estimates/CoefficientRowEvaluation.lean`, `Estimates/HaarShiftImage.lean`, `Estimates/MixedBooleanSiteValues.lean`, `Estimates/PeriodicIsometricAction.lean`, `Estimates/PrincipalCoefficientMarginal.lean`, `Estimates/UniformCommutingCircleDecomposition.lean`, `Fourier/EuclideanJetTorus.lean`, `Fourier/LayeredFourierCharacter.lean`, `Geometry/FiniteSupportApproximation.lean`, `Geometry/GeometricRetainedCommonCover.lean`, `Lattices/CommonIntegerSiteResidual.lean`, `Lattices/RetainedAffineCommonCover.lean`, `Lattices/SelectedResidueApproximation.lean`, `Lattices/SelectedResidueConstantMean.lean`, `Linear/FixedKernelEuclideanDensity.lean`, `Polynomial/ExtendedPolynomialValues.lean`, `Polynomial/FixedKernelPolynomialCover.lean`, `Polynomial/TranslationTopDegree.lean`, `Probability/CommonSectionAmbientDensityMultiple.lean`, `Probability/EuclideanJetDensity.lean`, `Probability/SlicedRemainderDensityFamily.lean`.
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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {T G : Type*} [MeasurableSpace T] [AddCommGroup G]
  [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]

theorem haarShiftDensity_image_law (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ]
    (ν : Measure T) [IsProbabilityMeasure ν]
    {z : T → G} {f : G → ℝ} (hz : Measurable z) (hf : Measurable f)
    (hfi : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x ∂μ) = 1) :
    (ν.prod (realDensityMeasure μ f)).map (fun p => p.2 + z p.1) =
      realDensityMeasure μ (haarShiftDensity ν z f) := by
  let _ := realDensityMeasure_probability μ f hfi hf0 hmass
  apply densityMixture_image_law ν (realDensityMeasure μ f) μ _
    (measurable_snd.add (hz.comp measurable_fst)) (fun t y => f (y - z t))
  · exact hf.comp (measurable_snd.sub (hz.comp measurable_fst))
  · exact fun t => ⟨fun y => hf0 _, hfi.comp_sub_right (z t),
      (integral_sub_right_eq_self f (z t)).trans hmass⟩
  · exact fun t => realDensityMeasure_map_add_right μ f (z t)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalCoefficientMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem boundedCoefficientExponent_card_le {K : Type*} [Fintype K] (h : ℕ) :
    Fintype.card (BoundedCoefficientExponent K h) ≤
      (h + 1) * (Fintype.card K + 1) ^ h := by
  classical
  let code : BoundedCoefficientExponent K h → (Σ n : Fin (h + 1), Fin n.val → K) := fun d =>
    ⟨⟨d.val.toMultiset.toList.length, by
      rw [Multiset.length_toList, Finsupp.card_toMultiset]
      exact Nat.lt_succ_of_le d.property⟩, d.val.toMultiset.toList.get⟩
  have hinj : Function.Injective code := by
    intro d e he
    have hl := congrArg (fun z : Σ n : Fin (h + 1), Fin n.val → K => List.ofFn z.2) he
    change List.ofFn d.val.toMultiset.toList.get = List.ofFn e.val.toMultiset.toList.get at hl
    rw [List.ofFn_get, List.ofFn_get] at hl
    have hm := congrArg (fun l : List K => (l : Multiset K)) hl
    rw [Multiset.coe_toList, Multiset.coe_toList] at hm
    apply Subtype.ext
    ext k
    have hk := congrArg (fun l : Multiset K => l.count k) hm
    simpa only [Finsupp.count_toMultiset] using hk
  have hc := Fintype.card_le_of_injective code hinj
  simp only [Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin] at hc
  calc
    _ ≤ ∑ n : Fin (h + 1), Fintype.card K ^ n.val := hc
    _ ≤ ∑ _n : Fin (h + 1), (Fintype.card K + 1) ^ h := by
      apply Finset.sum_le_sum
      intro n _
      exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ n.isLt))
    _ = _ := by simp

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {σ R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

theorem coefficients_translate_sub_monomial (h : σ → R) (α β : σ →₀ ℕ) (v : V) :
    coefficients (translate h (monomial α v) - monomial α v) β =
      (polynomialTranslate h (MvPolynomial.monomial α 1) -
        MvPolynomial.monomial α 1).coeff β • v := by
  rw [monomial, translate_tmul, ← TensorProduct.sub_tmul, coefficients_tmul]

theorem coefficients_translate_sub (h : σ → R) (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) :
    coefficients (translate h p - p) α = ∑ β ∈ (coefficients p).support,
      (polynomialTranslate h (MvPolynomial.monomial β 1) -
        MvPolynomial.monomial β 1).coeff α • coefficients p β := by
  conv_lhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, ← Finset.sum_sub_distrib,
    Finsupp.finsetSum_apply, coefficients_translate_sub_monomial]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeriodicIsometricAction
namespace OAI

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped BigOperators NNReal

variable {X : Type*} [TopologicalSpace X] [AddAction Circle X] [ContinuousVAdd Circle X]

theorem circleFejerSum_eq_average (N : ℕ) {f : X → ℂ} (hf : Continuous f) (x : X) :
    circleFejerSum N f x = fejerAverage N (fun t : Circle => f (t +ᵥ x)) := by
  have hc : Continuous (fun t : Circle => f (t +ᵥ x)) :=
    hf.comp (continuous_id.vadd continuous_const)
  rw [fejerAverage_eq_sum N hc]
  simp only [circleFejerSum, circleFourierComponent, neg_neg]

theorem circleFejerSum_approximation {N : ℕ} (hN : 0 < N) {f : X → ℂ} (hf : Continuous f)
    {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η)
    (horbit : ∀ (t : Circle) x, ‖f (t +ᵥ x) - f x‖ ≤ L * ‖t‖) (x : X) :
    ‖circleFejerSum N f x - f x‖ ≤ L * (η + 1 / (8 * N * η ^ 2)) := by
  rw [circleFejerSum_eq_average N hf]
  have hc : Continuous (fun t : Circle => f (t +ᵥ x)) :=
    hf.comp (continuous_id.vadd continuous_const)
  have h := norm_fejerAverage_sub_le_explicit hN hc hL hη
    (fun t : Circle => by simpa only [zero_vadd] using horbit t x)
  simpa only [zero_vadd] using h

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {X : Type*} [PseudoMetricSpace X] [AddAction Circle X] [ContinuousVAdd Circle X]

theorem lipschitz_circleFejerSum {N : ℕ} (hN : 0 < N) {f : X → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hact : ∀ t : Circle, Isometry (fun x : X => t +ᵥ x)) :
    LipschitzWith L (circleFejerSum N f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, circleFejerSum_eq_average N hf.continuous, circleFejerSum_eq_average N hf.continuous]
  have hx : Continuous (fun t : Circle => f (t +ᵥ x)) :=
    hf.continuous.comp (continuous_id.vadd continuous_const)
  have hy : Continuous (fun t : Circle => f (t +ᵥ y)) :=
    hf.continuous.comp (continuous_id.vadd continuous_const)
  apply norm_fejerAverage_sub_average_le hN hx hy
  intro t
  rw [← dist_eq_norm]
  exact (hf.dist_le_mul _ _).trans_eq (by rw [(hact t).dist_eq])

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped NNReal BigOperators

namespace IsometricCircleAction

variable {X : Type*} [PseudoMetricSpace X]

theorem smooth_eq_sum (A : IsometricCircleAction X) (N : ℕ) (f : X → ℂ) (x : X) :
    A.smooth N f x = ∑ h ∈ fejerFrequencies N, A.component N h f x := rfl

theorem smooth_lipschitz (A : IsometricCircleAction X) {N : ℕ} (hN : 0 < N)
    {f : X → ℂ} {L : ℝ≥0} (hf : LipschitzWith L f) : LipschitzWith L (A.smooth N f) := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  exact lipschitz_circleFejerSum hN hf A.isometry_act

theorem smooth_error (A : IsometricCircleAction X) {N : ℕ} (hN : 0 < N)
    {f : X → ℂ} (hf : Continuous f) {O η : ℝ} (hO : 0 ≤ O) (hη : 0 < η)
    (ho : ∀ t x, ‖f (A.act t x) - f x‖ ≤ O * ‖t‖) (x : X) :
    ‖A.smooth N f x - f x‖ ≤ O * (η + 1 / (8 * N * η ^ 2)) := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  exact circleFejerSum_approximation hN hf hO hη ho x

end IsometricCircleAction
end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationTopDegree
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {X R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem coefficients_translate_sub_eq_zero_of_degreeLE
    (w : X → ℕ) (hw : ∀ i, 0 < w i) (a : X → R) {n : ℕ}
    (p : VectorPolynomial X R V) (hp : DegreeLE w n p)
    (d : X →₀ ℕ) (hd : n ≤ Finsupp.weight w d) :
    coefficients (translate a p - p) d = 0 := by
  classical
  rw [coefficients_translate_sub]
  apply Finset.sum_eq_zero
  intro b hb
  have hbdeg := (degreeLE_iff w n p).mp hp b hb
  have hc : (polynomialTranslate a (MvPolynomial.monomial b 1) -
      MvPolynomial.monomial b 1).coeff d = 0 := by
    by_contra hne
    have hlt := (polynomialTranslate_monomial_bounds a w hw b).2
      (MvPolynomial.mem_support_iff.mpr hne)
    exact (not_lt_of_ge (hbdeg.trans hd)) hlt
  rw [hc, zero_smul]

theorem degreeLE_translate (w : X → ℕ) (hw : ∀ i, 0 < w i) (a : X → R) {n : ℕ}
    (p : VectorPolynomial X R V) (hp : DegreeLE w n p) :
    DegreeLE w n (translate a p) := by
  intro d hd
  have h := coefficients_translate_sub_eq_zero_of_degreeLE w hw a p hp d hd.le
  simpa only [map_sub, Finsupp.sub_apply, hp d hd, sub_zero] using h

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonIntegerSiteResidual
namespace OAI

section

namespace Erdos3

open scoped Matrix Classical

theorem exists_bounded_integer_site_residual {I S : Type*} [Fintype I] [Fintype S]
    (E : Matrix S I ℤ) {H : ℕ} (hH : 1 ≤ H)
    (hE : ∀ s i, RationalHeightLE (E s i : ℚ) H) :
    ∃ (d : ℕ) (T : Matrix I S ℤ), 0 < d ∧
      (∀ {W : Type*} [AddCommGroup W] [Module ℝ W] (x : I → W),
        matrixModuleAction (fun s i => (E s i : ℝ))
          (matrixModuleAction (fun i s => (T i s : ℝ))
            (matrixModuleAction (fun s i => (E s i : ℝ)) x)) =
          (d : ℝ) • matrixModuleAction (fun s i => (E s i : ℝ)) x) ∧
      (∀ {P : ℝ}, 0 ≤ P → (Fintype.card I : ℝ) ≤ P → (Fintype.card S : ℝ) ≤ P →
        (H : ℝ) ≤ Real.exp P →
        (d : ℝ) ≤ Real.exp ((P + 2) ^ 36) ∧
          ∀ i s, |(T i s : ℝ)| ≤ Real.exp (2 * (P + 2) ^ 36)) := by
  obtain ⟨T, hT, hTH⟩ := exists_bounded_rational_image_section (fun s i => (E s i : ℚ)) hH hE
  refine ⟨matrixDenominator T, clearedMatrix T, matrixDenominator_pos T, ?_, ?_⟩
  · intro W _ _ x
    rw [matrixModuleAction_cleared, map_smul]
    congr 1
    have he := matrixModuleAction_image_section
      (Matrix.of (fun s i => ((E s i : ℚ) : ℝ)))
      (Matrix.of (fun i s => (T i s : ℝ))) (real_matrix_image_section _ T hT) x
    funext s
    simpa only [matrixModuleAction, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.of_apply, Rat.cast_intCast] using congrFun he s
  · intro P hP hI hS hHP
    refine ⟨?_, cleared_image_section_entry_bound T H hTH hP hI hS hHP⟩
    simpa only [Nat.mul_one] using real_image_section_denominator_bound T H 1 hTH hP hS hI hHP
      (by simpa using Real.one_le_exp hP)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedCommonSiteResidual
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_bounded_common_site_residual {J S : Type*} [Fintype J] [Fintype S]
    {I : J → Type*} [∀ j, Fintype (I j)] (E : ∀ j, Matrix S (I j) ℤ)
    (H : J → ℕ) (hH : ∀ j, 1 ≤ H j)
    (hE : ∀ j s i, RationalHeightLE (E j s i : ℚ) (H j)) :
    ∃ (d : ℕ) (T : ∀ j, Matrix (I j) S ℤ), 0 < d ∧
      (∀ j {W : Type*} [AddCommGroup W] [Module ℝ W] (x : I j → W),
        matrixModuleAction (fun s i => (E j s i : ℝ))
          (matrixModuleAction (fun i s => (T j i s : ℝ))
            (matrixModuleAction (fun s i => (E j s i : ℝ)) x)) =
          (d : ℝ) • matrixModuleAction (fun s i => (E j s i : ℝ)) x) ∧
      (∀ {P : ℝ}, 0 ≤ P → (∀ j, (Fintype.card (I j) : ℝ) ≤ P) →
        (Fintype.card S : ℝ) ≤ P → (∀ j, (H j : ℝ) ≤ Real.exp P) →
        (d : ℝ) ≤ Real.exp (Fintype.card J * (P + 2) ^ 36) ∧
          ∀ j i s, |(T j i s : ℝ)| ≤ Real.exp (((Fintype.card J : ℝ) + 2) * (P + 2) ^ 36)) := by
  choose d T hd hT hbound using fun j => exists_bounded_integer_site_residual (E j) (hH j) (hE j)
  let D := ∏ j, d j
  refine ⟨D, fun j i s => (complementaryPeriod d j : ℤ) * T j i s,
    Finset.prod_pos (fun j _ => hd j), ?_, ?_⟩
  · intro j W _ _ x
    rw [matrixModuleAction_int_smul, map_smul, hT j, smul_smul]
    congr 1
    exact_mod_cast (by simpa only [Nat.mul_comm] using period_mul_complementary d j :
      complementaryPeriod d j * d j = D)
  · intro P hP hI hS hHP
    have hD : (D : ℝ) ≤ Real.exp (Fintype.card J * (P + 2) ^ 36) := by
      calc
        (D : ℝ) = ∏ j, (d j : ℝ) := Nat.cast_prod _ _
        _ ≤ ∏ _j : J, Real.exp ((P + 2) ^ 36) :=
          Finset.prod_le_prod (fun j _ => Nat.cast_nonneg _)
            (fun j _ => (hbound j hP (hI j) hS (hHP j)).1)
        _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
    refine ⟨hD, ?_⟩
    intro j i s
    rw [Int.cast_mul, Int.cast_natCast, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg (complementaryPeriod d j) : (0 : ℝ) ≤ complementaryPeriod d j)]
    have hc : (complementaryPeriod d j : ℝ) ≤ Real.exp (Fintype.card J * (P + 2) ^ 36) :=
      (Nat.cast_le.mpr (complementaryPeriod_le_product d hd j)).trans hD
    calc
      _ ≤ Real.exp (Fintype.card J * (P + 2) ^ 36) * Real.exp (2 * (P + 2) ^ 36) :=
        mul_le_mul hc ((hbound j hP (hI j) hS (hHP j)).2 i s) (abs_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteSupportApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem normalized_finite_weight_approximation {X : Type*}
    (v : X → ℝ) (S : Finset X) (hv0 : ∀ x, 0 ≤ v x)
    (hv : ∀ x ∉ S, v x = 0) (hZ : 0 < ∑' x, v x)
    (w f g : X → ℂ) {η : ℝ} (hη : 0 ≤ η)
    (hw : ∀ x ∈ S, ‖w x‖ ≤ 1) (he : ∀ x ∈ S, ‖f x - g x‖ ≤ η) :
    ‖(∑' x, ((v x / (∑' y, v y) : ℝ) : ℂ) * (w x * f x)) -
      ∑' x, ((v x / (∑' y, v y) : ℝ) : ℂ) * (w x * g x)‖ ≤ η := by
  let p := finiteSupportProbability v S hv0 hv hZ
  have hm : p.mean (fun x => ‖w x.val‖) ≤ 1 :=
    (p.mean_mono (fun x => hw x.val x.property)).trans_eq (p.mean_const 1)
  have h := (p.norm_weighted_complexMean_sub_le_mean_norm (fun x => w x.val)
    (fun x => f x.val) (fun x => g x.val) (fun x _ => he x.val x.property)).trans
      ((mul_le_mul_of_nonneg_left hm hη).trans_eq (mul_one η))
  change ‖(finiteSupportProbability v S hv0 hv hZ).complexMean (fun x => w x.val * f x.val) -
    (finiteSupportProbability v S hv0 hv hZ).complexMean (fun x => w x.val * g x.val)‖ ≤ η at h
  rw [finiteSupportProbability_complexMean v S hv0 hv hZ (fun x => w x * f x),
    finiteSupportProbability_complexMean v S hv0 hv hZ (fun x => w x * g x)] at h
  exact h

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

theorem residueSmoothIndexPMF_toReal {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) (x : K × I → ℤ) :
    (residueSmoothIndexPMF residue modulus hmodulus V hV hZ x).toReal =
      smoothProductProfile (K × I) (fun z => (residueLatticeArray residue modulus x z : ℝ) / V z) /
        ∑' y, smoothProductProfile (K × I)
          (fun z => (residueLatticeArray residue modulus y z : ℝ) / V z) := by
  simp only [residueSmoothIndexPMF, shiftedSmoothProductPMF_toReal, shiftedSmoothProductMass,
    rectangularWeight, residueProfile_point residue modulus hmodulus V hV]

end Erdos3

end

section

namespace Erdos3

theorem selectedResidueSmoothPMF_approximation {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (w f g : (K × I → ℤ) → ℂ) {η : ℝ} (hη : 0 ≤ η)
    (hw : ∀ x ∈ rectangularWeightIndices 0 V 1, ‖w x‖ ≤ 1)
    (he : ∀ x ∈ rectangularWeightIndices 0 V 1, ‖f x - g x‖ ≤ η) :
    ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * f x)) -
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * g x)‖ ≤ η := by
  simp_rw [selectedResidueSmoothPMF_toReal]
  exact normalized_finite_weight_approximation _ (rectangularWeightIndices 0 V 1)
    (selectedResidueSmoothWeight_nonneg modulus G V)
    (selectedResidueSmoothWeight_zero_off modulus G V hV) hZ w f g hη hw he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LayeredFourierCharacter
namespace OAI

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

noncomputable def layeredSiteWeight {I K S : Type*} [Fintype K] [Fintype S]
    (Q : MvPolynomial (K × I) ℝ) (site : S → K → ℤ)
    (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) : ℂ :=
  character ((MvPolynomial.eval (fun z => b z.1 z.2) Q : ℝ) : CircleFourier.Circle) *
    ∏ s, test s (integerSiteValue (site s) b)

theorem layeredSiteWeight_norm_le {I K S : Type*} [Fintype K] [Fintype S]
    (Q : MvPolynomial (K × I) ℝ) (site : S → K → ℤ)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1) (b : K → I → ℝ) :
    ‖layeredSiteWeight Q site test b‖ ≤ 1 := by
  rw [layeredSiteWeight, norm_mul, norm_character, one_mul, norm_prod]
  exact Finset.prod_le_one (fun s _ => norm_nonneg _) (fun s _ => htest s _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.EuclideanJetTorus
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

theorem coefficientSiteTorusMap_continuous {K S : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ) :
    Continuous (coefficientSiteTorusMap U site) :=
  continuous_pi (fun j => (integerMatrixTorusMap_continuous _ _).comp
    (coefficientLayerTorus_continuous U j))

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

theorem coefficientBooleanJetTorusMap_continuous {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α) :
    Continuous (coefficientBooleanJetTorusMap U root D rows) :=
  (siteBooleanJetTorusMap_continuous U rows).comp
    (coefficientSiteTorusMap_continuous U (integerAffineCube root D))

theorem coefficientBooleanJetTorusMap_surjective {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (O j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (rows : ∀ j, O j → Finset α) (hinj : ∀ j, Function.Injective (rows j))
    (hdegree : ∀ j o, (rows j o).card ≤ j.val + 1) :
    Function.Surjective (coefficientBooleanJetTorusMap U root D rows) := by
  intro y
  choose v hv using fun j => QuotientAddGroup.mk'_surjective
    (subspaceArrayIntegerLattice (O j) (U j)) (y j)
  choose c hc using fun j => matrixModuleAction_surjective_of_period (W := U j)
    (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) (a ^ (j.val + 1))
    (pow_ne_zero _ ha)
    (boundedCoefficientJetMatrix_period root D a hperiod (j.val + 1) (rows j)
      (hinj j) (hdegree j)) (v j)
  refine ⟨QuotientAddGroup.mk' (coefficientIntegerLattice U) (fun s => c s.1 s.2), ?_⟩
  funext j
  rw [coefficientBooleanJetTorusMap_mk]
  change QuotientAddGroup.mk' _ (matrixModuleAction _ (c j)) = y j
  rw [hc j, hv j]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {O J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem euclideanJetEquiv_continuous [∀ j, Fintype (O j)] :
    Continuous (euclideanJetEquiv (O := O) U) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro o
  exact (euclideanSubspaceTorusEquiv_symm_continuous (U j)).comp
    ((continuous_apply o).comp ((arrayCoordinateEquiv_continuous (U j)).comp (continuous_apply j)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowEvaluation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {K S : Type*} [Fintype K] [Fintype S] {m : ℕ} {J : Fin m → Type*}
  (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ) (q : ℕ)
  (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)

theorem coefficientSiteResidual_cover_on_kernel (x : CoefficientTorus (K := K) U)
    (hx : coefficientSiteTorusMap U site x = 0) :
    linearQuotientEndomorphism (coefficientIntegerLattice U)
      (coefficientSiteResidual U site (fun _ => q) T)
      (coefficientSiteResidual_preserves_lattice U site (fun _ => q) T) x =
        quotientIntegerCover (coefficientIntegerLattice U) q x := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [quotientIntegerCover_mk]
  change QuotientAddGroup.mk' (coefficientIntegerLattice U)
    (coefficientSiteResidual U site (fun _ => q) T v) =
      QuotientAddGroup.mk' (coefficientIntegerLattice U) ((q : ℝ) • v)
  apply QuotientAddGroup.eq.mpr
  intro s a
  have hsite := congrFun hx s.1
  change QuotientAddGroup.mk' (subspaceArrayIntegerLattice S (U s.1))
    (matrixModuleAction (fun t d => (boundedSiteMatrix (s.1.val + 1) site t d : ℝ))
      (coefficientLayerArray U s.1 v)) = 0 at hsite
  have hi := (QuotientAddGroup.eq_zero_iff _).mp hsite
  have ht := integerMatrix_preserves_array_lattice (U s.1) (T s.1) _ hi
  obtain ⟨z, hz⟩ := ht s.2 a
  refine ⟨z, ?_⟩
  change (-((q : ℝ) * (v s).val a -
      (matrixModuleAction (fun d t => (T s.1 d t : ℝ))
        (matrixModuleAction (fun t d => (boundedSiteMatrix (s.1.val + 1) site t d : ℝ))
          (coefficientLayerArray U s.1 v)) s.2).val a) + (q : ℝ) * (v s).val a) = z
  linarith

theorem coefficientSiteResidual_site_zero
    (hT : ∀ j (x : BoundedCoefficientExponent K (j.val + 1) → U j),
      matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ))
        (matrixModuleAction (fun d s => (T j d s : ℝ))
          (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)) x)) =
        (q : ℝ) • matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)) x)
    (x : CoefficientTorus (K := K) U) :
    coefficientSiteTorusMap U site
      (linearQuotientEndomorphism (coefficientIntegerLattice U)
        (coefficientSiteResidual U site (fun _ => q) T)
        (coefficientSiteResidual_preserves_lattice U site (fun _ => q) T) x) = 0 := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  funext j
  change QuotientAddGroup.mk' (subspaceArrayIntegerLattice S (U j))
    (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ))
      (scaledLinearResidual (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)))
        (matrixModuleAction (fun d s => (T j d s : ℝ))) (q : ℝ)
        (coefficientLayerArray U j v))) = 0
  rw [scaledLinearResidual_evaluation _ _ _ (hT j), map_zero]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HaarShiftImage
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem haarShiftDensity_map_eq {T G Y : Type*} [MeasurableSpace T] [AddCommGroup G]
    [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G] [MeasurableSpace Y]
    (μ : Measure G) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν] (z : T → G) (hz : Measurable z)
    (f : G → ℝ) (hfm : Measurable f) (hfi : Integrable f μ)
    (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x ∂μ) = 1)
    (π : G → Y) (hπ : Measurable π) (hinv : ∀ t x, π (x + z t) = π x) :
    (realDensityMeasure μ (haarShiftDensity ν z f)).map π = (realDensityMeasure μ f).map π := by
  let _ := realDensityMeasure_probability μ f hfi hf0 hmass
  have hU : Measurable (fun p : T × G => p.2 + z p.1) :=
    measurable_snd.add (hz.comp measurable_fst)
  rw [← haarShiftDensity_image_law μ ν hz hfm hfi hf0 hmass,
    Measure.map_map hπ hU]
  have he : (π ∘ fun p : T × G => p.2 + z p.1) = π ∘ Prod.snd := by
    funext p
    exact hinv p.1 p.2
  rw [he, ← Measure.map_map hπ measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedBooleanSiteValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

theorem siteFromLowBooleanJets_coefficient {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (x : CoefficientTorus (K := K) U) :
    siteFromLowBooleanJets U (coefficientBooleanJetTorusMap U root D
      (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) x) =
      coefficientSiteTorusMap U (integerAffineCube root D) x := by
  funext j
  change integerMatrixTorusMap (U j) (boundedBooleanReconstructionMatrix α (j.val + 1))
    (integerMatrixTorusMap (U j)
      (booleanJetExtractionMatrix (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α))
      (integerMatrixTorusMap (U j) (boundedSiteMatrix (j.val + 1) (integerAffineCube root D))
        (coefficientLayerTorus U j x))) = _
  rw [integerMatrixTorusMap_comp, integerMatrixTorusMap_comp,
    boundedBooleanReconstruction_siteMatrix]
  rfl

theorem coefficientSiteImage_lowJet_injective {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ) :
    let E := coefficientSiteTorusMap U (integerAffineCube root D)
    Function.Injective (fun y : Set.range E => siteBooleanJetTorusMap U
      (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) y.val) := by
  intro E y z hyz
  obtain ⟨x, hx⟩ := y.property
  obtain ⟨w, hw⟩ := z.property
  apply Subtype.ext
  have he := congrArg (siteFromLowBooleanJets U) hyz
  dsimp only at he
  rw [← hx, ← hw] at he ⊢
  exact (siteFromLowBooleanJets_coefficient U root D x).symm.trans
    (he.trans (siteFromLowBooleanJets_coefficient U root D w))

theorem coefficientSiteImage_lowJet_surjective {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (a : ℤ) (ha : a ≠ 0) (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range) :
    let E := coefficientSiteTorusMap U (integerAffineCube root D)
    Function.Surjective (fun y : Set.range E => siteBooleanJetTorusMap U
      (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) y.val) := by
  intro E z
  obtain ⟨x, hx⟩ := coefficientBooleanJetTorusMap_surjective U root D a ha hperiod
    (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α))
    (fun _ => Subtype.val_injective) (fun _ o => o.property) z
  exact ⟨Set.rangeFactorization E x, hx⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

theorem euclideanCoefficientJetMap_continuous {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α) :
    Continuous (euclideanCoefficientJetMap U root D rows) :=
  (euclideanJetEquiv_continuous U).comp (coefficientBooleanJetTorusMap_continuous U root D rows)

theorem euclideanCoefficientJetMap_surjective {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (rows : ∀ j, O j → Finset α) (hinj : ∀ j, Function.Injective (rows j))
    (hdegree : ∀ j o, (rows j o).card ≤ j.val + 1) :
    Function.Surjective (euclideanCoefficientJetMap U root D rows) :=
  (euclideanJetEquiv U).surjective.comp
    (coefficientBooleanJetTorusMap_surjective U root D a ha hperiod rows hinj hdegree)

theorem euclideanCoefficientJetMap_measurePreserving {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (rows : ∀ j, O j → Finset α) (hinj : ∀ j, Function.Injective (rows j))
    (hdegree : ∀ j o, (rows j o).card ≤ j.val + 1)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)] :
    MeasurePreserving (euclideanCoefficientJetMap U root D rows) μ
      (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) := by
  let ξ := Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
  have hc := euclideanCoefficientJetMap_continuous U root D rows
  have hs := euclideanCoefficientJetMap_surjective U root D a ha hperiod rows hinj hdegree
  let : CompactSpace (EuclideanJetLayers U O) := by
    have h := isCompact_univ.image hc
    rw [Set.image_univ, Set.range_eq_univ.mpr hs] at h
    exact ⟨h⟩
  let : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : O j => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  let : IsProbabilityMeasure ξ := Measure.pi.instIsProbabilityMeasure _
  let : ∀ j, (Measure.pi (fun _ : O j => ν j)).IsAddLeftInvariant :=
    fun _ => Measure.pi.isAddLeftInvariant _
  let : ξ.IsAddLeftInvariant := Measure.pi.isAddLeftInvariant _
  let : μ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := μ) Set.univ isCompact_univ (by simp) }
  let : ξ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := ξ) Set.univ isCompact_univ (by simp) }
  exact AddMonoidHom.measurePreserving hc hs (by simp)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
variable (a : ℤ) (ha : a ≠ 0) (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)

noncomputable def euclideanSiteImageEquiv :
    Set.range (coefficientSiteTorusMap U (integerAffineCube root D)) ≃
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet α (j.val + 1)) :=
  (Equiv.ofBijective (fun y => siteBooleanJetTorusMap U
    (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) y.val)
    ⟨coefficientSiteImage_lowJet_injective U root D,
      coefficientSiteImage_lowJet_surjective U root D a ha hperiod⟩).trans
    (euclideanJetEquiv U).toEquiv

theorem euclideanSiteImageEquiv_continuous :
    Continuous (euclideanSiteImageEquiv U root D a ha hperiod) :=
  (euclideanJetEquiv_continuous U).comp
    ((siteBooleanJetTorusMap_continuous U _).comp continuous_subtype_val)

noncomputable def euclideanSiteImageHomeomorph [CompactSpace (CoefficientTorus (K := K) U)] :
    Set.range (coefficientSiteTorusMap U (integerAffineCube root D)) ≃ₜ
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet α (j.val + 1)) := by
  let : CompactSpace (Set.range (coefficientSiteTorusMap U (integerAffineCube root D))) :=
    isCompact_iff_compactSpace.mp (isCompact_range (coefficientSiteTorusMap_continuous U _))
  exact Continuous.homeoOfEquivCompactToT2 (f := euclideanSiteImageEquiv U root D a ha hperiod)
    (euclideanSiteImageEquiv_continuous U root D a ha hperiod)

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (SiteTorus (Finset α) U)] [BorelSpace (SiteTorus (Finset α) U)]

theorem euclideanSiteImageHomeomorph_haar
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)] :
    (μ.map (Set.rangeFactorization (coefficientSiteTorusMap U (integerAffineCube root D)))).map
        (euclideanSiteImageHomeomorph U root D a ha hperiod) =
      Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet α (j.val + 1) => ν j)) := by
  have hπ := (coefficientSiteTorusMap_continuous U (integerAffineCube root D)).rangeFactorization.measurable
  have he := (euclideanSiteImageHomeomorph U root D a ha hperiod).continuous.measurable
  exact (Measure.map_map he hπ).trans
    (euclideanCoefficientJetMap_measurePreserving U root D a ha hperiod
      (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α))
      (fun _ => Subtype.val_injective) (fun _ o => o.property) μ ν).map_eq

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformCommutingCircleDecomposition
namespace OAI

section

namespace Erdos3.CircleFourier

open scoped NNReal

variable {X α : Type*} [PseudoMetricSpace X]

noncomputable def iteratedCircleSmooth (N : ℕ) (A : α → IsometricCircleAction X) :
    List α → (X → ℂ) → X → ℂ
  | [], f => f
  | i :: is, f => (A i).smooth N (iteratedCircleSmooth N A is f)

theorem iteratedCircleSmooth_lipschitz {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) {f : X → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) : LipschitzWith L (iteratedCircleSmooth N A is f) := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).smooth_lipschitz hN ih

theorem iteratedCircleSmooth_error {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) {f : X → ℂ} {L : ℝ≥0} {ε : ℝ}
    (hf : LipschitzWith L f)
    (hstep : ∀ i ∈ is, ∀ g : X → ℂ, LipschitzWith L g → ∀ x,
      ‖(A i).smooth N g x - g x‖ ≤ ε) (x : X) :
    ‖iteratedCircleSmooth N A is f x - f x‖ ≤ is.length * ε := by
  induction is with
  | nil => simp [iteratedCircleSmooth]
  | cons i is ih =>
    have ht := ih (fun j hj => hstep j (List.mem_cons_of_mem i hj))
    have hs := hstep i (List.mem_cons_self) (iteratedCircleSmooth N A is f)
      (iteratedCircleSmooth_lipschitz hN A is hf) x
    change ‖(A i).smooth N (iteratedCircleSmooth N A is f) x - f x‖ ≤ _
    calc
      _ ≤ ‖(A i).smooth N (iteratedCircleSmooth N A is f) x - iteratedCircleSmooth N A is f x‖ +
          ‖iteratedCircleSmooth N A is f x - f x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε + is.length * ε := add_le_add hs ht
      _ = (i :: is).length * ε := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X α : Type*} [PseudoMetricSpace X]

theorem iteratedCircleSmooth_eq_sum {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) {f : X → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : X) :
    iteratedCircleSmooth N A is f x =
      ∑ k : Fin is.length → FejerChoice N,
        iteratedCircleComponent N A is (fun j => (k j : ℤ)) f x := by
  classical
  induction is generalizing x with
  | nil => simp [iteratedCircleSmooth, iteratedCircleComponent]
  | cons i is ih =>
    have ht : iteratedCircleSmooth N A is f = fun y =>
        ∑ k : Fin is.length → FejerChoice N,
          iteratedCircleComponent N A is (fun j => (k j : ℤ)) f y := funext ih
    change (A i).smooth N (iteratedCircleSmooth N A is f) x = _
    rw [ht, (A i).smooth_eq_sum]
    apply Eq.trans ?_ (sum_fin_tuple_cons is.length (fun k : Fin (is.length + 1) → FejerChoice N =>
      iteratedCircleComponent N A (i :: is) (fun j => (k j : ℤ)) f x)).symm
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro b _
    rw [(A i).component_sum N (b : ℤ) Finset.univ
      (fun k : Fin is.length → FejerChoice N =>
        iteratedCircleComponent N A is (fun j => (k j : ℤ)) f)
      (fun k _ => (iteratedCircleComponent_lipschitz hN A is (fun j => (k j : ℤ)) hf).continuous) x]
    apply Finset.sum_congr rfl
    intro k _
    rfl

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X α : Type*} [PseudoMetricSpace X]

theorem exists_controlled_finite_circle_decomposition
    (A : α → IsometricCircleAction X) (is : List α)
    (hcomm : ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j))
    (f : X → ℂ) (L B D : ℝ≥0) (hf : LipschitzWith L f) (hb : ∀ x, ‖f x‖ ≤ B)
    (horbit : ∀ i ∈ is, ∀ (t : Circle) x, dist ((A i).act t x) x ≤ D * ‖t‖)
    (δ p : ℝ) (hδ : 0 < δ) (hp : 0 ≤ p) (hd : (is.length : ℝ) ≤ p)
    (hLp : (L : ℝ) ≤ Real.exp p) (hDp : (D : ℝ) ≤ Real.exp p) (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4) ∧
      (Fintype.card (Fin is.length → FejerChoice N) : ℝ) ≤ Real.exp (2 * p * (2 * p + 2) ^ 4) ∧
      (∀ k : Fin is.length → FejerChoice N,
        (∀ j, (|(k j : ℤ)| : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4)) ∧
        LipschitzWith L (iteratedCircleComponent N A is (fun j => (k j : ℤ)) f) ∧
        (∀ x, ‖iteratedCircleComponent N A is (fun j => (k j : ℤ)) f x‖ ≤ B) ∧
        ∀ (j : Fin is.length) (t : Circle) x,
          iteratedCircleComponent N A is (fun r => (k r : ℤ)) f ((A (is.get j)).act t x) =
            character ((-(k j : ℤ)) • t) *
              iteratedCircleComponent N A is (fun r => (k r : ℤ)) f x) ∧
      ∀ x, ‖(∑ k : Fin is.length → FejerChoice N,
        iteratedCircleComponent N A is (fun j => (k j : ℤ)) f x) - f x‖ ≤ δ := by
  let O : ℝ := (L : ℝ) * D
  have hO : 0 ≤ O := mul_nonneg L.coe_nonneg D.coe_nonneg
  let ε := δ / (is.length + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hOp : O ≤ Real.exp (2 * p) := by
    calc
      O ≤ Real.exp p * Real.exp p := mul_le_mul hLp hDp D.coe_nonneg (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hεp : ε⁻¹ ≤ Real.exp (2 * p) := by
    have hlen : (is.length : ℝ) + 1 ≤ Real.exp p :=
      (by linarith : (is.length : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
    calc
      ε⁻¹ = ((is.length : ℝ) + 1) * δ⁻¹ := by dsimp [ε]; rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hlen hδp (inv_nonneg.mpr hδ.le) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨N, hN, hcut, hNb⟩ := exists_fejer_cutoff hO hε
  have hNe : (N : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4) :=
    hNb.trans (fejer_cutoff_bound (by linarith : 0 ≤ 2 * p) hO hε hOp hεp)
  refine ⟨N, hN, hNe, ?_, ?_, ?_⟩
  · apply (Nat.cast_le.mpr (card_fejerChoices N is.length)).trans
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg N) hNe _).trans
    rw [← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_ofNat]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hd (by norm_num)) (by positivity))
  · intro k
    refine ⟨?_, iteratedCircleComponent_lipschitz hN A is _ hf,
      iteratedCircleComponent_norm_le hN A is _ hb, ?_⟩
    · intro j
      have hk : (|(k j : ℤ)| : ℝ) < N := by
        exact_mod_cast abs_lt_of_mem_fejerFrequencies (k j).property
      exact hk.le.trans hNe
    · exact fun j => iteratedCircleComponent_character N A is _ hcomm f j
  · intro x
    rw [← iteratedCircleSmooth_eq_sum hN A is hf x]
    have hstep : ∀ i ∈ is, ∀ g : X → ℂ, LipschitzWith L g → ∀ y,
        ‖(A i).smooth N g y - g y‖ ≤ ε := by
      intro i hi g hg y
      have hη : 0 < ε / (2 * (O + 1)) := by positivity
      apply ((A i).smooth_error hN hg.continuous hO hη ?_ y).trans
        (fejer_error_le_of_cutoff hO hε hN hcut)
      intro t z
      rw [← dist_eq_norm]
      exact (hg.dist_le_mul _ _).trans ((mul_le_mul_of_nonneg_left (horbit i hi t z) L.coe_nonneg).trans_eq
        (by dsimp [O]; ring))
    apply (iteratedCircleSmooth_error hN A is hf hstep x).trans
    change (is.length : ℝ) * (δ / (is.length + 1)) ≤ δ
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FixedKernelPolynomialCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

theorem boundedSiteMatrix_mapDomain {K I S : Type*} (h : ℕ) (site : S → I → ℤ) (e : K → I) :
    (boundedSiteMatrix h site).submatrix id (boundedExponentMap e h) =
      boundedSiteMatrix h (fun s k => site s (e k)) := by
  ext s d
  change (d.val.mapDomain e).prod (fun i n => site s i ^ n) = d.val.prod (fun k n => site s (e k) ^ n)
  exact Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedAffineCommonCover
namespace OAI

section

namespace Erdos3

open Polynomial

theorem exists_mode_residue_threshold_exp_budget (m : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ (n d : ℕ) (P F D S ρ ε : ℝ),
      0 ≤ P → (n : ℝ) ≤ P → (d : ℝ) ≤ P →
      0 ≤ F → F ≤ Real.exp P → 0 ≤ D → D ≤ Real.exp P →
      0 ≤ S → S ≤ Real.exp P → 0 < ρ → 1 / ρ ≤ Real.exp P →
      0 < ε → 1 / ε ≤ Real.exp P →
      modeResidueSideThreshold m d D S ρ ε ≤ Real.exp ((P + K) ^ K) ∧
      modeRemovalRankThreshold m n d F D S ρ ε ≤ Real.exp ((P + K) ^ K) := by
  obtain ⟨K₀, _, hbase⟩ := exists_mode_threshold_exp_budget m
  obtain ⟨K, hK, hpoly⟩ := exists_natPolynomial_eval_budget
    ((X + C K₀) ^ K₀ + (2 * X + modeProfileLogPolynomial + 3) + 1)
  refine ⟨K, hK, ?_⟩
  intro n d P F D S ρ ε hP hn hd hF hFP hD hDP hS hSP hρ hρP hε hεP
  obtain ⟨hs, hr⟩ := hbase n d P F D S ρ ε hP hn hd hF hFP hD hDP hS hSP hρ hρP hε hεP
  have hprof := modeProfileLog_nonneg hP
  have hδ := modeRemovalMesh_pos d
  have he : S / (ρ * modeRemovalMesh d) ≤ Real.exp (2 * P + modeProfileLog P + 3) := by
    calc
      _ = S * (1 / ρ) * (1 / modeRemovalMesh d) := by ring
      _ ≤ Real.exp P * Real.exp P * Real.exp (modeProfileLog P + 3) := by
        gcongr
        exact modeRemovalMesh_inv_le_exp d hP hd
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hp : (P + K₀) ^ K₀ + (2 * P + modeProfileLog P + 3) + 1 ≤ (P + K) ^ K := by
    simpa [Polynomial.eval₂_pow, modeProfileLogPolynomial_eval] using hpoly P hP
  have hb0 : 0 ≤ (P + K₀) ^ K₀ := by positivity
  constructor
  · exact (add_le_exp_add_one hb0 (by linarith) hs he).trans (Real.exp_le_exp.mpr hp)
  · exact hr.trans (Real.exp_le_exp.mpr (by linarith))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GeometricRetainedCommonCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem boundedCoefficientExponent_card_le_geometricSiteBudget {K : Type*} [Fintype K]
    (m q : ℕ) {h : ℕ} (hh : h ≤ m) {P : ℝ} (hP : 0 ≤ P)
    (hK : (Fintype.card K : ℝ) ≤ P) :
    (Fintype.card (BoundedCoefficientExponent K h) : ℝ) ≤ geometricSiteBudget m q P := by
  have hc : (Fintype.card (BoundedCoefficientExponent K h) : ℝ) ≤
      ((h : ℝ) + 1) * ((Fintype.card K : ℝ) + 1) ^ h := by
    exact_mod_cast boundedCoefficientExponent_card_le (K := K) h
  apply hc.trans
  calc
    _ ≤ ((m : ℝ) + 1) * (P + 1) ^ (m + 1) := by
      apply mul_le_mul (by exact_mod_cast Nat.add_le_add_right hh 1)
      · exact (pow_le_pow_left₀ (by positivity) (by linarith) h).trans
          (pow_le_pow_right₀ (by linarith) (by omega))
      · positivity
      · positivity
    _ ≤ geometricSiteBudget m q P := le_add_of_nonneg_right (by positivity)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueConstantMean
namespace OAI

section

namespace Erdos3

theorem selectedResidueSmoothPMF_const {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) (c : ℂ) :
    (∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * c) = c := by
  simp_rw [selectedResidueSmoothPMF_toReal]
  rw [← finiteSupportProbability_complexMean _ (rectangularWeightIndices 0 V 1)
    (selectedResidueSmoothWeight_nonneg modulus G V)
    (selectedResidueSmoothWeight_zero_off modulus G V hV) hZ (fun _ => c)]
  exact FiniteProbabilityWeights.complexMean_const _ c

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.EuclideanJetDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

theorem siteImage_density_euclideanJet {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {J : Fin m → Type*}
    [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (SiteTorus (Finset α) U)] [BorelSpace (SiteTorus (Finset α) U)]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (ρ : Measure (CoefficientTorus (K := K) U)) :
    let E := coefficientSiteTorusMap U (integerAffineCube root D)
    let π := Set.rangeFactorization E
    let e := euclideanSiteImageHomeomorph U root D a ha hperiod
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet α (j.val + 1) => ν j))
    ∀ g : Set.range E → ℝ, Continuous g → ∀ {B : ℝ},
      (∀ y, g y ∈ Set.Icc (0 : ℝ) B) → (∫ y, g y ∂μ.map π) = 1 →
      ρ.map π = realDensityMeasure (μ.map π) g →
      let f := fun z => g (e.symm z)
      Continuous f ∧ (∀ z, f z ∈ Set.Icc (0 : ℝ) B) ∧
        Integrable f ξ ∧ (∫ z, f z ∂ξ) = 1 ∧ (∀ y, f (e y) = g y) ∧
        ρ.map (euclideanCoefficientJetMap U root D
          (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α))) =
          realDensityMeasure ξ f := by
  intro E π e ξ g hgc B hcap hmass hlaw f
  let eM := e.toMeasurableEquiv
  have hhaar : (μ.map π).map eM = ξ := euclideanSiteImageHomeomorph_haar U root D a ha hperiod μ ν
  have hfc : Continuous f := hgc.comp e.symm.continuous
  have hfb (z) : f z ∈ Set.Icc (0 : ℝ) B := hcap (e.symm z)
  let : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : BoundedBooleanJet α (j.val + 1) => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  let : IsProbabilityMeasure ξ := Measure.pi.instIsProbabilityMeasure _
  have hfi : Integrable f ξ := Integrable.of_bound hfc.aestronglyMeasurable B
    (ae_of_all _ (fun z => by rw [Real.norm_of_nonneg (hfb z).1]; exact (hfb z).2))
  have hfvalue (y) : f (e y) = g y := congrArg g (e.symm_apply_apply y)
  have hfmass : (∫ z, f z ∂ξ) = 1 := by
    rw [← hhaar, integral_map_equiv]
    change (∫ y, g (e.symm (e y)) ∂μ.map π) = 1
    simpa only [Homeomorph.symm_apply_apply] using hmass
  refine ⟨hfc, hfb, hfi, hfmass, hfvalue, ?_⟩
  have hπ : Measurable π := (coefficientSiteTorusMap_continuous U _).rangeFactorization.measurable
  calc
    _ = (ρ.map π).map eM := (Measure.map_map eM.measurable hπ).symm
    _ = realDensityMeasure ξ f := by
      rw [hlaw, realDensityMeasure_map_equiv, hhaar]
      rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedKernelEuclideanDensity
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

theorem exists_fixed_kernel_bounded_section (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k,
      |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {K : Type*} [Fintype K] (root : K → ℤ) (difference : Fin q → K → ℤ)
    (e : K₀ → K) (_hroot : ∀ k, root (e k) = root₀ k)
    (_hdifference : ∀ i k, difference i (e k) = difference₀ i k),
    ∃ T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) (Finset (Fin q)) ℤ,
      (∀ j s, (∑ i, |(T j i s : ℝ)|) ≤ Real.exp ((P + A) ^ A)) ∧
      ∀ (j : Fin m) {W : Type*} [AddCommGroup W] [Module ℝ W]
        (x : BoundedCoefficientExponent K (j.val + 1) → W),
        let E := boundedSiteMatrix (j.val + 1) (fun s k => affineSite root difference s (some k))
        matrixModuleAction (fun s i => (E s i : ℝ))
          (matrixModuleAction (fun i s => (T j i s : ℝ))
            (matrixModuleAction (fun s i => (E s i : ℝ)) x)) =
          (d : ℝ) • matrixModuleAction (fun s i => (E s i : ℝ)) x := by
  obtain ⟨A, hA, hbudget⟩ := exists_bounded_residual_cover_budget m q
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite
  let site₀ := fun s k => affineSite root₀ difference₀ s (some k)
  let E₀ := fun j : Fin m => boundedSiteMatrix (j.val + 1) site₀
  obtain ⟨d, T₀, hd, hT₀, hbound⟩ := exists_bounded_common_site_residual E₀
    (fun _ => exponentialSiteHeight m P) (fun _ => exponentialSiteHeight_pos m P)
    (fun j => boundedSiteMatrix_height_of_exp m (Nat.succ_le_of_lt j.isLt) site₀ hsite)
  let G := geometricSiteBudget m q P
  have hG : 0 ≤ G := geometricSiteBudget_nonneg m q hP
  have hcard (j : Fin m) : (Fintype.card (BoundedCoefficientExponent K₀ (j.val + 1)) : ℝ) ≤ G :=
    boundedCoefficientExponent_card_le_geometricSiteBudget m q (Nat.succ_le_of_lt j.isLt) hP hK
  obtain ⟨hdb, hTb⟩ := hbound hG hcard (cubeSites_card_le_geometricSiteBudget m q hP)
    (fun _ => (exponentialSiteHeight_le m hP).trans
      (Real.exp_le_exp.mpr (degree_mul_le_geometricSiteBudget m q hP)))
  have hcost : G + ((m : ℝ) + 2) * (G + 2) ^ 36 ≤ (P + A) ^ A := hbudget P hP
  have hpow : 0 ≤ (G + 2) ^ 36 := pow_nonneg (by linarith) _
  refine ⟨d, hd, hdb.trans (Real.exp_le_exp.mpr ?_), ?_⟩
  · simp only [Fintype.card_fin]
    nlinarith
  · intro K _ root difference e hroot hdifference
    let site := fun s k => affineSite root difference s (some k)
    have hs : (fun s k => site s (e k)) = site₀ := by
      funext s k
      simp only [site, site₀, affineSite, hroot, hdifference]
    refine ⟨fun j => extendIntegerSiteSection (boundedExponentMap e (j.val + 1)) (T₀ j), ?_, ?_⟩
    · intro j s
      apply (extendIntegerSiteSection_column_sum_bound _ (T₀ j) (hTb j) s).trans
      simp only [Fintype.card_fin]
      calc
        _ ≤ G * Real.exp (((m : ℝ) + 2) * (G + 2) ^ 36) :=
          mul_le_mul_of_nonneg_right (hcard j) (Real.exp_pos _).le
        _ ≤ Real.exp G * Real.exp (((m : ℝ) + 2) * (G + 2) ^ 36) :=
          mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp G]) (Real.exp_pos _).le
        _ = Real.exp (G + ((m : ℝ) + 2) * (G + 2) ^ 36) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr hcost
    · intro j W _ _ x
      have hc : (boundedSiteMatrix (j.val + 1) site).submatrix id (boundedExponentMap e (j.val + 1)) = E₀ j := by
        rw [boundedSiteMatrix_mapDomain, hs]
      obtain ⟨R, hR⟩ := boundedSiteMatrix_fixed_kernel_factor root₀ (Matrix.of difference₀)
        a ha hperiod (j.val + 1) root (Matrix.of difference)
      exact integerSiteResidual_extend_columns (E₀ j) (boundedSiteMatrix (j.val + 1) site)
        (boundedExponentMap e (j.val + 1)) hc R hR (T₀ j) d (hT₀ j) x

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped BigOperators Classical

theorem exists_fixed_kernel_bounded_section_multiple (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k,
      |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∀ (period : ℕ), 0 < period → (period : ℝ) ≤ Real.exp P →
    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {K : Type*} [Fintype K] (root : K → ℤ) (difference : Fin q → K → ℤ)
    (e : K₀ → K) (_hroot : ∀ k, root (e k) = root₀ k)
    (_hdifference : ∀ i k, difference i (e k) = difference₀ i k),
    ∃ T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) (Finset (Fin q)) ℤ,
      (∀ j s, (∑ i, |(T j i s : ℝ)|) ≤ Real.exp ((P + A) ^ A)) ∧
      ∀ (j : Fin m) {W : Type*} [AddCommGroup W] [Module ℝ W]
        (x : BoundedCoefficientExponent K (j.val + 1) → W),
        let E := boundedSiteMatrix (j.val + 1) (fun s k => affineSite root difference s (some k))
        matrixModuleAction (fun s i => (E s i : ℝ))
          (matrixModuleAction (fun i s => (T j i s : ℝ))
            (matrixModuleAction (fun s i => (E s i : ℝ)) x)) =
          (d : ℝ) • matrixModuleAction (fun s i => (E s i : ℝ)) x := by
  obtain ⟨A₀, _, hsection⟩ := exists_fixed_kernel_bounded_section m q
  obtain ⟨A, hA, hpoly⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C A₀) ^ A₀)
  have hbudget (P : ℝ) (hP : 0 ≤ P) : P + (P + A₀) ^ A₀ ≤ (P + A) ^ A := by
    simpa [Polynomial.eval₂_pow] using hpoly P hP
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite period hp hpP
  obtain ⟨d, hd, hdb, hsection⟩ := hsection root₀ difference₀ a ha hperiod hP hK hsite
  have hbound {x : ℝ} (hx : x ≤ Real.exp ((P + A₀) ^ A₀)) :
      period * x ≤ Real.exp ((P + A) ^ A) := by
    calc
      _ ≤ (period : ℝ) * Real.exp ((P + A₀) ^ A₀) :=
        mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)
      _ ≤ Real.exp P * Real.exp ((P + A₀) ^ A₀) :=
        mul_le_mul_of_nonneg_right hpP (Real.exp_nonneg _)
      _ ≤ _ := by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (hbudget P hP)
  refine ⟨period * d, dvd_mul_right period d, Nat.mul_pos hp hd, ?_, ?_⟩
  · simpa only [Nat.cast_mul] using hbound hdb
  · intro K _ root difference e hroot hdifference
    obtain ⟨T, hTb, hT⟩ := hsection root difference e hroot hdifference
    refine ⟨fun j i s => (period : ℤ) * T j i s, ?_, ?_⟩
    · intro j s
      simp only [Int.cast_mul, Int.cast_natCast, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg period : (0 : ℝ) ≤ period), ← Finset.mul_sum]
      exact hbound (hTb j s)
    · intro j W _ _ x
      dsimp only
      rw [matrixModuleAction_int_smul, map_smul, hT j x, smul_smul, Nat.cast_mul]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CommonSectionAmbientDensityMultiple
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical NNReal

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [MeasurableSpace (CoefficientTorus (K := K) U)]
variable [BorelSpace (CoefficientTorus (K := K) U)]
variable (R : CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := K) U)
variable (hR : ∀ x ∈ coefficientIntegerLattice U, R x ∈ coefficientIntegerLattice U)
variable (μ : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure μ]

noncomputable def coefficientResidualAmbientDensity
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ)
    (z : CoefficientAmbientIndex K J → UnitAddCircle) : ℝ :=
  ∫ y, f (z + coefficientAmbientTorus U
    (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y)) ∂μ

omit [Fintype K] [∀ j, Fintype (J j)] [BorelSpace (CoefficientTorus (K := K) U)]
  [IsProbabilityMeasure μ] in
theorem coefficientResidualAmbientDensity_eq
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ)
    (x : CoefficientTorus (K := K) U) :
    coefficientResidualAmbientDensity U R hR μ f (coefficientAmbientTorus U x) =
      linearQuotientAverage (coefficientIntegerLattice U) R hR μ
        (fun z => f (coefficientAmbientTorus U z)) x := by
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  funext t
  simp only [coefficientAmbientTorus, map_add, Pi.add_apply]

omit [Fintype K] [∀ j, Fintype (J j)] [BorelSpace (CoefficientTorus (K := K) U)] in
theorem coefficientResidualAmbientDensity_bounds
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {C : ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) C) (z) :
    coefficientResidualAmbientDensity U R hR μ f z ∈ Set.Icc (0 : ℝ) C := by
  have h0 : 0 ≤ coefficientResidualAmbientDensity U R hR μ f z :=
    integral_nonneg (fun y => (hf _).1)
  refine ⟨h0, ?_⟩
  have hn := norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall (fun y =>
      show ‖f (z + coefficientAmbientTorus U
        (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y))‖ ≤ C from
      by rw [Real.norm_of_nonneg (hf _).1]; exact (hf _).2))
  change ‖coefficientResidualAmbientDensity U R hR μ f z‖ ≤ C * μ.real Set.univ at hn
  simpa only [probReal_univ, mul_one, Real.norm_of_nonneg h0] using hn

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

variable {K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def coefficientAmbientSiteSection
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)
    (z : JetAmbientIndex (fun _ : Fin m => S) J → UnitAddCircle) :
    CoefficientAmbientIndex K J → UnitAddCircle :=
  fun t => ∑ s, T t.1.1 t.1.2 s • z ⟨t.1.1, s, t.2⟩

noncomputable def coefficientAmbientSiteEvaluation (site : S → K → ℤ)
    (z : CoefficientAmbientIndex K J → UnitAddCircle) :
    JetAmbientIndex (fun _ : Fin m => S) J → UnitAddCircle :=
  fun t => ∑ e, boundedSiteMatrix (t.1.val + 1) site t.2.1 e • z ⟨⟨t.1, e⟩, t.2.2⟩

theorem coefficientAmbientSiteSection_lipschitz
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)
    {L : ℝ≥0} (hT : ∀ j e, ∑ s, ‖T j e s‖ ≤ L) :
    LipschitzWith L (coefficientAmbientSiteSection (J := J) T) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  rintro ⟨⟨j, e⟩, i⟩
  calc
    _ ≤ ∑ s, dist (T j e s • z ⟨j,s,i⟩) (T j e s • w ⟨j,s,i⟩) := dist_sum_sum_le _ _ _
    _ ≤ ∑ s, ‖T j e s‖ * dist z w := by
      apply Finset.sum_le_sum
      intro s _
      rw [dist_eq_norm, ← smul_sub]
      exact (norm_zsmul_le _ _).trans (mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm] using dist_le_pi_dist z w ⟨j,s,i⟩) (norm_nonneg _))
    _ = (∑ s, ‖T j e s‖) * dist z w := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hT j e) dist_nonneg

variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ) (q : ℕ)
variable (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)

local notation "R" => coefficientSiteResidual U site (fun _ => q) T
local notation "hR" => coefficientSiteResidual_preserves_lattice U site (fun _ => q) T

omit [∀ j, Fintype (J j)] in
theorem coefficientAmbientSiteSection_residual (x : CoefficientTorus (K := K) U) :
    coefficientAmbientSiteSection T (coefficientAmbientSiteEvaluation site (coefficientAmbientTorus U x)) +
      coefficientAmbientTorus U (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR x) =
    coefficientAmbientTorus U (quotientIntegerCover (coefficientIntegerLattice U) q x) := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [quotientIntegerCover_mk]
  funext t
  rcases t with ⟨⟨j, e⟩, i⟩
  change (∑ s, T j e s • ∑ a, boundedSiteMatrix (j.val + 1) site s a •
    ((v ⟨j,a⟩).val i : UnitAddCircle)) +
      (((q : ℝ) * (v ⟨j,e⟩).val i -
        (matrixModuleAction (fun a s => (T j a s : ℝ))
          (matrixModuleAction (fun s a => (boundedSiteMatrix (j.val + 1) site s a : ℝ))
            (coefficientLayerArray U j v)) e).val i : ℝ) : UnitAddCircle) =
      (((q : ℝ) * (v ⟨j,e⟩).val i : ℝ) : UnitAddCircle)
  have he : ((matrixModuleAction (fun a s => (T j a s : ℝ))
      (matrixModuleAction (fun s a => (boundedSiteMatrix (j.val + 1) site s a : ℝ))
        (coefficientLayerArray U j v)) e).val i : UnitAddCircle) =
      ∑ s, T j e s • ∑ a, boundedSiteMatrix (j.val + 1) site s a •
        ((v ⟨j,a⟩).val i : UnitAddCircle) := by
    change ((((∑ s : S, (T j e s : ℝ) • ∑ a : BoundedCoefficientExponent K (j.val + 1),
      (boundedSiteMatrix (j.val + 1) site s a : ℝ) • (v ⟨j,a⟩ : U j)) : U j).val i : ℝ) : UnitAddCircle) = _
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, ← zsmul_eq_mul, unitAddCircle_coe_sum, AddCircle.coe_zsmul]
  rw [AddCircle.coe_sub, he]
  exact add_sub_cancel _ _

variable [MeasurableSpace (CoefficientTorus (K := K) U)]
variable [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure μ]

noncomputable def coefficientSectionAmbientDensity
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ)
    (z : JetAmbientIndex (fun _ : Fin m => S) J → UnitAddCircle) : ℝ :=
  coefficientResidualAmbientDensity U R hR μ f (coefficientAmbientSiteSection T z)

omit [∀ j, Fintype (J j)] [BorelSpace (CoefficientTorus (K := K) U)] in
theorem coefficientSectionAmbientDensity_bounds
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {C : ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) C) (z) :
    coefficientSectionAmbientDensity U site q T μ f z ∈ Set.Icc (0 : ℝ) C :=
  coefficientResidualAmbientDensity_bounds U R hR μ f hf _

omit [∀ j, Fintype (J j)] [IsProbabilityMeasure μ] in
theorem coefficientSectionAmbientDensity_eq [μ.IsAddLeftInvariant]
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ)
    (x : CoefficientTorus (K := K) U) :
    coefficientSectionAmbientDensity U site q T μ f
      (coefficientAmbientSiteEvaluation site (coefficientAmbientTorus U x)) =
    linearQuotientAverage (coefficientIntegerLattice U) R hR μ
      (fun z => f (coefficientAmbientTorus U z))
      (quotientIntegerCover (coefficientIntegerLattice U) q x) := by
  let r := linearQuotientEndomorphism (coefficientIntegerLattice U) R hR
  have hadd (a b : CoefficientTorus (K := K) U) :
      coefficientAmbientTorus U (r (a + b)) =
        coefficientAmbientTorus U (r a) + coefficientAmbientTorus U (r b) := by
    funext t
    simp only [map_add, coefficientAmbientTorus, Pi.add_apply]
  have hinv (z : CoefficientAmbientIndex K J → UnitAddCircle) :
      coefficientResidualAmbientDensity U R hR μ f (z + coefficientAmbientTorus U (r x)) =
        coefficientResidualAmbientDensity U R hR μ f z := by
    have ht := integral_add_left_eq_self (μ := μ)
      (fun y => f (z + coefficientAmbientTorus U (r y))) x
    simpa only [coefficientResidualAmbientDensity, hadd, add_assoc] using ht
  rw [coefficientSectionAmbientDensity, ← hinv,
    coefficientAmbientSiteSection_residual U site q T x]
  exact coefficientResidualAmbientDensity_eq U R hR μ f _

end Erdos3.VectorPolynomial

end

end OAI
end


