-- Prove2me | Definitions.Def_OAIE3v2B234
-- name    : OAIE3v2B234
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:33:21.381253+00:00
-- url     : https://prove2.me/theorems/6b189326-8da3-4b13-a608-fd4b49b77e8c
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 239 of 311
-- statement:
--   Definitions bundle 239 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B199`, `OAIE3v2B206`, `OAIE3v2B207`, `OAIE3v2B212`, `OAIE3v2B213`, `OAIE3v2B214`, `OAIE3v2B215`, `OAIE3v2B216` of this split.
--
--   Modules: `Dynamics/AllocatedNarrowPathMarginal.lean`, `Estimates/AllocatedCenteredNarrowPrescribedMarginal.lean`, `Estimates/AllocatedCoverLogBounds.lean`, `Estimates/AllocatedZeroLayerForwardFrontSourceProfile.lean`, `Estimates/AntisymmetricPairVerticalModel.lean`, `Estimates/NativeFrozenComparison.lean`, `Estimates/NativeProductVerticalization.lean`, `Estimates/PreparedFiniteNestedSourceArrays.lean`, `Estimates/PreparedUniformEarlyRadiusWithCutoff.lean`, `Estimates/QuadraticBoundedFamily.lean`, `Estimates/QuadraticCyclicAntisymmetric.lean`, `Estimates/SharedFreeFrozenComparison.lean`, `Estimates/ShiftedVerticalExpansion.lean`, `Estimates/UnitVerticalNativeInverseModels.lean`, `Geometry/AllocatedInactiveSupportBudget.lean`, `Geometry/AllocatedProductChartRadius.lean`, `Linear/AllocatedModularRankCongruenceOutput.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Linear/PreparedFiniteNestedSourceProjectionBudget.lean`, `Nilpotent/AllocatedNiltestSourceSelection.lean`, `Nilpotent/AllocatedNiltestSupportedSlicedDetection.lean`, `Nilpotent/CyclicNiltestDetection.lean`, `Polynomial/NativePolynomialOrbitConstruction.lean`, `Polynomial/PolynomialBoxDetection.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B199
import Definitions.Def_OAIE3v2B206
import Definitions.Def_OAIE3v2B207
import Definitions.Def_OAIE3v2B212
import Definitions.Def_OAIE3v2B213
import Definitions.Def_OAIE3v2B214
import Definitions.Def_OAIE3v2B215
import Definitions.Def_OAIE3v2B216

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativePolynomialOrbitConstruction
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

theorem exists_native_polynomial_orbit_factors (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] (D : RationalFilteredNilmanifold L s d)
      (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ k, D.filtration.layer k = Submodule.span ℚ (b '' {i | k ≤ w i}))
      {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      ∀ (g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (eta : L →ₗ[ℚ] ℚ) (A : σ → ℝ),
      (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      D.filtration.ControlledSymbolFactorization b w hF eta A
        (D.filtration.realPolynomialSymbolHom b w hF (fun _ => 1) g) p →
      Nonempty (NativePolynomialOrbitFactors D g eta A ((p + C) ^ C)) := by
  obtain ⟨a, _, hnormalize⟩ := exists_lattice_normalized_refiltered_factorization s
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 4) ^ 11 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ d _ _ _ D b w hF p hp hD hσ hb g eta A hA hfactor
  let r := (p + 4) ^ 11 + p + 2
  have hgeom : 0 ≤ (p + 4) ^ 11 := by positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpr : p ≤ r := by dsimp [r]; linarith
  have h2r : 2 ≤ r := by dsimp [r]; linarith
  have hgr : (p + 4) ^ 11 ≤ r := by dsimp [r]; linarith
  have hcost : r + (r + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, R, r, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (r + a) ^ a := by positivity
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hfinal : (r + a) ^ a ≤ (p + C) ^ C := by linarith
  have hApos (i : σ) : 0 < A i := (Real.exp_pos _).trans_le (hA i)
  obtain ⟨m₀, hm₀, hin, hout, hE⟩ := D.exists_prescribed_adapted_model
    b w hF hp hD (fun i j => (hb i j).trans (by linarith))
  let E := D.filtration.ofAdaptedBasis b w hF D.lattice m₀ hm₀ hin hout
  have hfactor' : ∀ _j : Unit,
      E.filtration.ControlledSymbolFactorization E.basis w hF eta A
        (E.filtration.realPolynomialSymbolHom E.basis w hF (fun _ => 1) g) r := by
    intro _
    exact NilpotentLieFiltration.ControlledSymbolFactorization.mono
      D.filtration b w hF hfactor hpr hApos
  obtain ⟨U, v, m, κ, slow, middle, rat, hv, hU, hheight, hfreq, hm, hmp, hκ,
      hproduct, hslow, hrat, hmid0, hrat0, hcoeff, _hvalues⟩ :=
    hnormalize E w hF (fun _ : Unit => eta) r hr (hE.mono E hgr)
      (hσ.trans hpr) (by norm_num; linarith) A
      (fun i => (Real.exp_le_exp.mpr hfinal).trans (hA i)) g hfactor'
  exact ⟨{
    basis := b
    weight := w
    adapted := hF
    basis_height := fun i j => (hb i j).trans hpC
    subalgebra := U
    generator := v
    spanning := hv
    graded := hU
    generator_height := fun i j => (hheight i j).trans hfinal
    kills_top := hfreq ()
    denominator := m
    denominator_pos := hm
    denominator_bound := hmp.trans (Real.exp_le_exp.mpr hfinal)
    latticeConstant := κ
    latticeConstant_mem := hκ
    slow := slow
    middle := middle
    rational := rat
    product := hproduct
    slow_bound := fun α i => (hslow α i).trans
      (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hfinal) (monomialScale_pos A hApos α).le)
    rational_grid := hrat
    middle_zero := hmid0
    rational_zero := hrat0
    middle_coefficients := hcoeff }⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedVerticalExpansion
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

theorem exists_controlled_normalized_square (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      (p : ℝ), 0 ≤ p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (T : D.Niltest w), T.ComplexityLE p → ∀ (χ : D.RealGroup → CircleFourier.Circle),
      (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
        T.observable (z • x) = character (χ z) * T.observable x) →
      ∀ h : σ → ℤ, ∃ (n : ℕ)
        (Q : RationalFilteredNilmanifold (D.filtration.squareLieSubalgebra ⧸
          D.filtration.squareFiltration.layerIdeal (s + 1)) s n)
        (S : Q.Niltest w),
        S.normBound = T.normBound ^ 2 ∧ S.ComplexityLE ((p + C) ^ C) ∧
        ∀ x : σ → ℤ, S.eval x = T.eval (fun i => x i + h i) * star (T.eval x) := by
  obtain ⟨a, _, hnorm⟩ := exists_bounded_realified_square_orbit (s + 1)
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz (s + 1) a
  obtain ⟨c, _, hrec⟩ := exists_rationalReconstructionLipschitzBound_exp s
  obtain ⟨C, hC, hbudget⟩ := exists_normalizedSquareComplexityBudget_bound a b c
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp w hw T hT χ hvert h
  obtain ⟨ε, γ, hγ, hε, q, hq⟩ := hnorm D p hp hT.1 w hw h T.orbit
  obtain ⟨A, _, hA, hALip⟩ := hleft D p hp hT.1
  obtain ⟨m, bs, v, hls, N, hN, hin, hout, S, hSB, hS, hSval⟩ :=
    D.exists_square_niltest_with_budget T hp hT a b c hrec ε q χ hvert A hA (hALip ε hε)
  refine ⟨_, _, S, hSB, hS.mono (hbudget p hp), ?_⟩
  intro x
  exact (hSval x).trans (D.filtration.realSquareObservable_recovers_product D.lattice ε γ
    (D.filtration.realification.polynomialOrbitEval w (fun i => x i + h i) T.orbit)
    (D.filtration.realification.polynomialOrbitEval w x T.orbit) hγ T.observable
    (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q) (hq x).1 (hq x).2)

end Erdos3

end

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct

universe u v

theorem exists_vertical_derivative_detection (s : ℕ) :
    ∃ b : ℕ, 2 ≤ b ∧ ∀ c : ℕ,
      BoxNiltestDetection.{u,v} s (fun q => (q + c) ^ c) →
      ∀ {σ : Type v} [Fintype σ] [DecidableEq σ] {L : Type u}
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d) (p q : ℝ),
      0 ≤ p → 0 ≤ q → (Fintype.card σ : ℝ) ≤ q → (p + b) ^ b ≤ q →
      ∀ (w : σ → ℕ), (∀ i, 0 < w i) → ∀ (T : D.Niltest w), T.ComplexityLE p →
      ∀ (χ : D.RealGroup → CircleFourier.Circle),
      (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
        T.observable (z • x) = character (χ z) * T.observable x) →
      ∀ (h a : σ → ℤ) (lengths : σ → ℕ) [∀ i, NeZero (lengths i)] (f : (σ → ℤ) → ℂ),
      (∀ x ∈ translatedIntegerBox a lengths, ‖f x‖ ≤ 1) →
      Real.exp (-q) ≤ ‖finiteCorrelation (translatedIntegerBox a lengths) f (multiplicativeDerivative T.eval h)‖ →
      Real.exp (-((q + c) ^ c)) ≤ finiteSupportGowersNorm (s + 1) (translatedIntegerBox a lengths) f := by
  obtain ⟨b, hb, hsq⟩ := exists_controlled_normalized_square s
  refine ⟨b, hb, ?_⟩
  intro c hI σ _ _ L _ _ d _ _ _ _ D p q hp hq hσ hcost w hw T hT χ hvert h a lengths _ f hf hc
  let K := D.filtration.squareLieSubalgebra
  let M := K ⧸ D.filtration.squareFiltration.layerIdeal (s + 1)
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let : FiniteDimensional ℚ K := inferInstance
  let : FiniteDimensional ℚ M := inferInstance
  let : TopologicalSpace (ℝ ⊗[ℚ] K) := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] K) := inferInstance
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 (Module.finBasis ℚ K)
  let : TopologicalSpace (ℝ ⊗[ℚ] M) := moduleTopology ℝ (ℝ ⊗[ℚ] M)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] M) := IsModuleTopology.topologicalAddGroup ℝ _
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] M) := inferInstance
  let : T2Space (ℝ ⊗[ℚ] M) := realification_moduleTopology_t2 (Module.finBasis ℚ M)
  obtain ⟨n, E, S, _, hS, hval⟩ := hsq D p hp w hw T hT χ hvert h
  have heval : S.conjugate.eval = multiplicativeDerivative T.eval h := by
    funext x
    rw [RationalFilteredNilmanifold.Niltest.eval_conjugate, hval]
    simp only [multiplicativeDerivative, star_mul, star_star]
    rfl
  have hc' : Real.exp (-q) ≤ ‖finiteCorrelation (translatedIntegerBox a lengths) f S.conjugate.eval‖ := by
    rwa [heval]
  exact hI E q hq hσ w hw S.conjugate (hS.mono hcost) a lengths f hf hc'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestDetection
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem boxNiltestDetection_succ.{u,v} {s c : ℕ}
    (hI : BoxNiltestDetection.{u,v} s (fun p => (p + c) ^ c)) :
    ∃ C : ℕ, 2 ≤ C ∧ BoxNiltestDetection.{u,v} (s + 1) (fun p => (p + C) ^ C) := by
  classical
  obtain ⟨av, _, hav⟩ := exists_verticalDecompositionBudget_bound
  obtain ⟨bs, _, hder⟩ := exists_vertical_derivative_detection s
  obtain ⟨C, hC, hbudget⟩ := exists_boxDetectionStepBudget_bound s av bs c
  refine ⟨C, hC, ?_⟩
  intro σ _ _ L _ _ d _ _ _ _ D p hp hσ w hw T hT z lengths _ f hf hc
  let Q := translatedIntegerBox z lengths
  have hQ : Q.Nonempty := translatedIntegerBox_nonempty lengths z
  obtain ⟨η, U, hU, hcorrU, hchar⟩ :=
    T.exists_detection_vertical_mode av hav hp hT hQ f hf hc
  let r := boxModeBudget av p
  let q := boxInductionInputBudget av bs p
  let ℓ := boxRetainedBudget av p
  let ρ := Real.exp (-r)
  let δ := Real.exp (-(ℓ + p))
  let η0 := Real.exp (-((q + c) ^ c))
  let μ := Real.exp (-ℓ)
  let P := fun h : σ → ℤ =>
    ρ ^ 2 / 2 ≤ ‖finiteCorrelation (derivativeSupport Q h)
      (multiplicativeDerivative f h) (multiplicativeDerivative U.eval h)‖ ∧
    δ * Q.card < ((derivativeSupport Q h).card : ℝ)
  have hcost := boxInductionInputBudget_bounds av bs hp
  have hq : 0 ≤ q := hp.trans hcost.2.2
  have hρsq : Real.exp (-q) ≤ ρ ^ 2 / 2 := by
    have hq' : 2 * r + 1 ≤ q := hcost.2.1
    have he : ρ ^ 2 = Real.exp (-2 * r) := by
      dsimp [ρ]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he]
    exact (Real.exp_le_exp.mpr (by linarith : -q ≤ -2 * r - 1)).trans
      (exp_sub_one_le_half_exp (-2 * r))
  have hweight := weight_correlating_large_box_overlaps z lengths f U.eval
    (ρ := ρ) (B := Real.exp (p + 1)) (δ := δ)
    (Real.exp_nonneg _) (Real.exp_pos _) (Real.exp_nonneg _) hf
    (fun x _ => U.eval_budget hU x) hcorrU
  have hμ : μ ≤ ∑ h ∈ cubeDifferenceSupport Q,
      (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) * (if P h then (1 : ℝ) else 0) :=
    (retained_exponential_weight (Fintype.card σ) (r := r) hσ).trans hweight
  have hretained (h : σ → ℤ) (hh : h ∈ cubeDifferenceSupport Q) (hP : P h) :
      δ * Q.card ≤ ((derivativeSupport Q h).card : ℝ) ∧
      η0 ≤ finiteSupportGowersNorm (s + 1) (derivativeSupport Q h) (multiplicativeDerivative f h) := by
    refine ⟨hP.2.le, ?_⟩
    let lens := fun i => ((lengths i : ℤ) - |h i|).toNat
    let origin := fun i => z i + max 0 (-h i)
    let : ∀ i, NeZero (lens i) := fun i => ⟨(box_overlap_length_pos z lengths hh i).ne'⟩
    have hR : derivativeSupport Q h = translatedIntegerBox origin lens :=
      derivativeSupport_translatedIntegerBox z lengths h
    have hunit : ∀ x ∈ translatedIntegerBox origin lens, ‖multiplicativeDerivative f h x‖ ≤ 1 := by
      rw [← hR]
      intro x hx
      obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
      simpa only [multiplicativeDerivative, norm_mul, norm_star, one_mul] using
        mul_le_mul (hf x hx) (hf (x + h) hxh) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hcorr : Real.exp (-q) ≤ ‖finiteCorrelation (translatedIntegerBox origin lens)
        (multiplicativeDerivative f h) (multiplicativeDerivative U.eval h)‖ := by
      rw [← hR]
      exact hρsq.trans hP.1
    have hd := hder c hI D (p + 1) q (by linarith) hq (hσ.trans hcost.2.2) hcost.1
      w hw U hU (fun g => ((realifyFunctional η g.coord : ℝ) : CircleFourier.Circle)) hchar
      h origin lens (multiplicativeDerivative f h) hunit hcorr
    rwa [← hR] at hd
  have hgowers := box_gowers_lower_bound_of_overlaps z lengths s f P
    (Real.exp_nonneg _) (Real.exp_nonneg _) hμ hretained
  have hpow : Real.exp (-boxDetectionStepBudget s av bs c p) ≤
      finiteSupportGowersNorm (s + 2) Q f ^ (2 ^ (s + 2)) :=
    (box_detection_exponential_product s av bs c (Fintype.card σ) hσ).trans hgowers
  have hnorm : 0 ≤ finiteSupportGowersNorm (s + 2) Q f := by
    rw [finiteSupportGowersNorm_eq_restricted (translatedIntegerBox_reflectsPairSums lengths z)]
    exact restrictedGowersNorm_nonneg (s + 1) _ _
  exact (Real.exp_le_exp.mpr (neg_le_neg (hbudget p hp))).trans
    (exp_neg_le_of_pow hnorm (boxDetectionStepBudget_nonneg s av bs c hp)
      (pow_ne_zero _ (by norm_num)) hpow)

theorem exists_boxNiltestDetection.{u,v} (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ BoxNiltestDetection.{u,v} s (fun p => (p + C) ^ C) := by
  induction s with
  | zero =>
    refine ⟨2, le_rfl, ?_⟩
    intro σ _ _ L _ _ d _ _ _ _ D p hp hσ w hw T hT z lengths _ f hf hc
    have hb : 2 * p ≤ (p + (2 : ℕ)) ^ 2 := by
      norm_num only [Nat.cast_ofNat]
      nlinarith [sq_nonneg p]
    exact (Real.exp_le_exp.mpr (neg_le_neg hb)).trans
      (boxNiltestDetection_zero D p hp hσ w hw T hT z lengths f hf hc)
  | succ s ih =>
    obtain ⟨c, _, hc⟩ := ih
    exact boxNiltestDetection_succ hc

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticBoundedFamily
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

attribute [local instance] NativeUnitRankFamily.lie NativeUnitRankFamily.algebra
  NativeUnitRankFamily.topology NativeUnitRankFamily.topologicalAdd
  NativeUnitRankFamily.continuousSMul NativeUnitRankFamily.hausdorff
  NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra
  NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd
  NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

theorem exists_native_correlation_of_unit_products
    {I K : Type} [Fintype I] {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
    (J : Finset (ZMod N))
    (F : NativeUnitRankFamily (fun _ : Unit => 1) s r {h // h ∈ J} I p)
    (M : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) K p)
    (H : Finset {h // h ∈ J}) (hH : H.Nonempty)
    (hdense : Real.exp (-q) * N ≤ (H.card : ℝ)) (hpq : p ≤ q)
    {n₁ n₂ : ℕ} (hn₁ : (n₁ + 1 : ℝ) ≤ Real.exp q) (hn₂ : (n₂ + 1 : ℝ) ≤ Real.exp q)
    (V₁ : F.model.UnitVerticalObservable (F.model.filtration.realification.subgroup s)
      (Fin (n₁ + 1)) q)
    (V₂ : M.model.UnitVerticalObservable
      (M.model.filtration.realification.subgroup (∑ i, mixedCorrelationDegree s i)) (Fin (n₂ + 1)) q)
    (hcorr : ∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N q (fun _ : Unit => fun x =>
      multiplicativeDerivative f h.val x * star (V₂.observable 0 (QuotientGroup.mk
        (M.multi.filtration.realification.polynomialOrbitEval
          (correlationInput (h.val.val : ℤ) (x.val : ℤ)) M.orbit))) *
        star (V₁.observable 0 (QuotientGroup.mk
          (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
            (fun _ => (x.val : ℤ)) (F.orbit h))))))) :
    Nonempty (NativeCorrelationStructure s r N q f) := by
  classical
  obtain ⟨h₀, hh₀⟩ := hH
  let e (h : ZMod N) : {h // h ∈ J} := if hh : h ∈ J then ⟨h, hh⟩ else h₀
  have he (h : {h // h ∈ J}) : e h.val = h := by
    simp only [e, dif_pos h.property]
  let family := F.toVerticalFamily e hpq hn₁ V₁
  let mixed := M.toNilcharacter hpq hn₂ V₂
  let shifts := H.image Subtype.val
  have hcard : shifts.card = H.card := Finset.card_image_of_injective _ Subtype.val_injective
  refine ⟨{
    shifts := shifts
    nonempty := (show H.Nonempty from ⟨h₀, hh₀⟩).image _
    density := by simpa only [ZMod.card, hcard] using hdense
    mixed := mixed
    family := family
    correlation := ?_
  }⟩
  intro h hh
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hh
  obtain ⟨Wh⟩ := hcorr z hz
  refine ⟨Wh.mapCoordinates _ (fun _ => ((0 : Fin (n₂ + 1)), (0 : Fin (n₁ + 1)))) ?_⟩
  intro i x
  have hinput : (fun j => ((correlationInput z.val x j).val : ℤ)) =
      correlationInput (z.val.val : ℤ) (x.val : ℤ) :=
    map_correlationInput (fun a : ZMod N => (a.val : ℤ)) z.val x
  have hmixed : mixed.evalCyclic N (0 : Fin (n₂ + 1)) (correlationInput z.val x) = V₂.observable 0 (QuotientGroup.mk
      (M.multi.filtration.realification.polynomialOrbitEval
        (correlationInput (z.val.val : ℤ) (x.val : ℤ)) M.orbit)) := by
    change (M.toNilcharacter hpq hn₂ V₂).eval (0 : Fin (n₂ + 1)) (fun j => ((correlationInput z.val x j).val : ℤ)) = _
    rw [hinput, M.toNilcharacter_eval]
  have hfamily : family.evalCyclic N (0 : Fin (n₁ + 1)) z.val x = V₁.observable 0 (QuotientGroup.mk
      (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (F.orbit z))) := by
    change (F.toVerticalFamily e hpq hn₁ V₁).eval (0 : Fin (n₁ + 1)) z.val (x.val : ℤ) = _
    rw [F.toVerticalFamily_eval, he]
  change nativeCorrelationResidual f mixed family z.val ((0 : Fin (n₂ + 1)), (0 : Fin (n₁ + 1))) x = _
  simp only [nativeCorrelationResidual, hmixed, hfamily]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeProductVerticalization
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeUnitRankFamily.lie NativeUnitRankFamily.algebra
  NativeUnitRankFamily.topology NativeUnitRankFamily.topologicalAdd
  NativeUnitRankFamily.continuousSMul NativeUnitRankFamily.hausdorff
  NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra
  NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd
  NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

theorem exists_native_correlation_of_sliced_unit_products
    {I K : Type} [Fintype I] {s r N : ℕ} [NeZero N] {p q P : ℝ} {f : ZMod N → ℂ}
    (J : Finset (ZMod N))
    (F : NativeUnitRankFamily (fun _ : Unit => 1) s r {h // h ∈ J} I p)
    (M : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) K p)
    (iM : K) (H : Finset {h // h ∈ J}) (hH : H.Nonempty)
    (hdense : Real.exp (-P) * N ≤ (H.card : ℝ)) (hpP : p ≤ P) (hqP : q ≤ P)
    {n₁ n₂ : ℕ} (hn₁ : (n₁ + 1 : ℝ) ≤ Real.exp q) (hn₂ : (n₂ + 1 : ℝ) ≤ Real.exp q)
    (V₁ : F.model.UnitVerticalObservable (F.model.filtration.realification.subgroup s)
      (Fin (n₁ + 1)) q)
    (V₂ : M.model.UnitVerticalObservable
      (M.model.filtration.realification.subgroup (∑ i, mixedCorrelationDegree s i)) (Fin (n₂ + 1)) q)
    (hcorr : ∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N q (fun _ : Unit => fun x =>
      multiplicativeDerivative f h.val x * star (V₂.observable 0 (QuotientGroup.mk
        (M.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
          (fun _ => (x.val : ℤ)) (M.slice iM (h.val.val : ℤ)).orbit))) *
        star (V₁.observable 0 (QuotientGroup.mk
          (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
            (fun _ => (x.val : ℤ)) (F.orbit h))))))) :
    Nonempty (NativeCorrelationStructure s r N P f) := by
  apply exists_native_correlation_of_unit_products J F M H hH hdense hpP
    (hn₁.trans (Real.exp_le_exp.mpr hqP)) (hn₂.trans (Real.exp_le_exp.mpr hqP))
    (V₁.mono hqP) (V₂.mono hqP)
  intro h hh
  obtain ⟨Wh⟩ := hcorr h hh
  refine ⟨(Wh.mono hqP).mapCoordinates _ id ?_⟩
  intro i x
  change multiplicativeDerivative f h.val x * star (V₂.observable 0 (QuotientGroup.mk
    (M.multi.filtration.realification.polynomialOrbitEval
      (correlationInput (h.val.val : ℤ) (x.val : ℤ)) M.orbit))) *
      star (V₁.observable 0 (QuotientGroup.mk
        (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
          (fun _ => (x.val : ℤ)) (F.orbit h)))) =
    multiplicativeDerivative f h.val x * star (V₂.observable 0 (QuotientGroup.mk
      (M.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (M.slice iM (h.val.val : ℤ)).orbit))) *
      star (V₁.observable 0 (QuotientGroup.mk
        (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
          (fun _ => (x.val : ℤ)) (F.orbit h))))
  rw [M.slice_orbit_eval]

theorem exists_native_sliced_product_correlation
    {I K : Type} [Fintype I] {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    {J : Finset (ZMod N)}
    (F : NativeUnitRankFamily (fun _ : Unit => 1) s r {h // h ∈ J} I p)
    (M : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) K p)
    (iF : I) (iM : K) (h : {h // h ∈ J})
    (hcorr : Nonempty (NativeVectorCorrelation (s - 1) N p (fun _ : Unit => fun x =>
      multiplicativeDerivative f h.val x * star (M.eval iM
        (correlationInput (h.val.val : ℤ) (x.val : ℤ))) *
        star (F.eval h iF (fun _ => (x.val : ℤ)))))) :
    Nonempty (NativeVectorCorrelation (s - 1) N p (fun _ : Unit => fun x =>
      multiplicativeDerivative f h.val x *
        star ((M.slice iM (h.val.val : ℤ)).evalCyclic N (fun _ => x)) *
        star (((F.test iF).withOrbit (F.orbit h)).evalCyclic N (fun _ => x)))) := by
  obtain ⟨Wh⟩ := hcorr
  refine ⟨Wh.mapCoordinates _ id ?_⟩
  intro i x
  change multiplicativeDerivative f h.val x *
    star ((M.slice iM (h.val.val : ℤ)).eval (fun _ => (x.val : ℤ))) *
    star (((F.test iF).withOrbit (F.orbit h)).eval (fun _ => (x.val : ℤ))) = _
  rw [M.slice_eval, F.withOrbit_eval]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalNativeInverseModels
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_native_common_derivative_models {s C : ℕ} (hI : CyclicNativeInverse s C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ gowersNorm (s + 2) f →
      Nonempty (NativeCommonDerivativeModels s N ((p + D) ^ D) f) := by
  classical
  obtain ⟨a, _, hcommon⟩ := RationalFilteredNilmanifold.exists_common_observable_correlators s
  let X : Polynomial ℕ := Polynomial.X
  let Q := Polynomial.C (2 ^ (s + 2)) * X + 2
  let R := (Q + Polynomial.C C) ^ C
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (R + Polynomial.C a) ^ a + 2)
  refine ⟨D, hD, ?_⟩
  intro N _ p hp f hf hG
  let q := derivativeInverseBudget s p
  let r := (q + C) ^ C
  have hq : 0 ≤ q := by dsimp [q, derivativeInverseBudget]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hshared : 0 ≤ (r + a) ^ a := by positivity
  have hcost : q + (r + a) ^ a + 2 ≤ (p + D) ^ D := by
    simpa [Q, R, X, q, r, derivativeInverseBudget, Polynomial.eval₂_pow] using hbudget p hp
  have hsharedD : (r + a) ^ a ≤ (p + D) ^ D := by linarith
  obtain ⟨H, hH, hdense, g, F, hcorr⟩ := exists_native_derivative_correlators hI f hf hp hG
  let J := {h // h ∈ H}
  have hJ : (Finset.univ : Finset J).Nonempty := by
    obtain ⟨h, hh⟩ := hH
    exact ⟨⟨h, hh⟩, Finset.mem_univ _⟩
  obtain ⟨h₀, _, E, hE, H₁, S, _, hH₁, hdense₁, hS, hsame, hcS⟩ :=
    hcommon (fun h : J => (F h).model) (fun h => (F h).test) Finset.univ hJ hr
      (fun h => (F h).complexity) (fun h _ => (F h).norm)
      (fun h x => multiplicativeDerivative f h.val x)
      (fun h _ x => multiplicativeDerivative_norm_le_one f hf h.val x)
      (fun h _ => by simpa only [← (F h).eval] using hcorr h)
  let H' := H₁.image Subtype.val
  let selected (h : ZMod N) : J := if hh : h ∈ H then ⟨h, hh⟩ else h₀
  have hcard : H'.card = H₁.card := Finset.card_image_of_injective _ Subtype.val_injective
  have huniv : (Finset.univ : Finset J).card = H.card := by simp [J]
  have hfinaldensity : Real.exp (-((p + D) ^ D)) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(q + (r + a) ^ a)) * Fintype.card (ZMod N) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg (by linarith)))
          (Nat.cast_nonneg _)
      _ = Real.exp (-((r + a) ^ a)) * (Real.exp (-q) * Fintype.card (ZMod N)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-((r + a) ^ a)) * H.card :=
        mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := by simpa only [hcard, huniv] using hdense₁
  refine ⟨{
    L := (F h₀).L
    dim := (F h₀).dim
    model := E
    geometry := hE.mono E hsharedD
    shifts := H'
    nonempty := hH₁.image _
    density := hfinaldensity
    test := fun h => S (selected h)
    norm := fun h => (hS (selected h)).1
    complexity := fun h => (hS (selected h)).2.2.mono hsharedD
    common_observable := fun h k => hsame (selected h) (selected k)
    correlation := ?_ }⟩
  intro h hh
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hh
  have hselect : selected j.val = j := by simp only [selected, dif_pos j.property]
  rw [hselect]
  exact (Real.exp_le_exp.mpr (neg_le_neg hsharedD)).trans (hcS j hj)

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

theorem exists_normalized_native_inverse_models {s C : ℕ} (hI : CyclicNativeInverse s C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      ∃ R : NativeCommonDerivativeModels s N ((p + D) ^ D) f,
        ∀ h, R.model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0
          (R.test h).orbit = 1 := by
  obtain ⟨a, _, hmodels⟩ := exists_native_common_derivative_models hI
  obtain ⟨b, _, hnormalize⟩ := exists_normalized_native_common_models s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + Polynomial.C b) ^ b)
  refine ⟨D, hD, ?_⟩
  intro N _ p hp f hf hG
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have hcost : ((p + a) ^ a + b) ^ b ≤ (p + D) ^ D := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨B⟩ := hmodels hp f hf hG
  obtain ⟨R, hR⟩ := hnormalize hq hf B
  exact ⟨R.mono hcost, hR⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticCyclicAntisymmetric
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem exists_correlated_corner (f : G → ℂ) (g : G → G → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {ρ : ℝ}
    (hcorr : ρ ≤ 𝔼 h, ‖𝔼 n, multiplicativeDerivative f h n * star (g h n)‖) :
    ∃ b₁ b₂ b₃ : G → ℂ,
      (∀ x, ‖b₁ x‖ ≤ 1) ∧ (∀ y, ‖b₂ y‖ ≤ 1) ∧ (∀ z, ‖b₃ z‖ ≤ 1) ∧
      ρ ≤ (𝔼 x, 𝔼 y, g y x * b₁ x * b₂ y * b₃ (x + y)).re := by
  obtain ⟨c, hc, hphase⟩ := exists_phase_aligned_derivatives f g
  refine ⟨(fun x => star (f x)), (fun y => star (c y)), f, ?_, ?_, hf, ?_⟩
  · intro x
    simpa only [norm_star] using hf x
  · intro y
    simp only [norm_star, hc, le_refl]
  · have heq : (𝔼 x, 𝔼 y, g y x * star (f x) * star (c y) * f (x + y)) =
        star (𝔼 h, 𝔼 n, multiplicativeDerivative f h n * star (star (c h) * g h n)) := by
      calc
        _ = 𝔼 y, 𝔼 x, star (multiplicativeDerivative f y x * star (star (c y) * g y x)) := by
          rw [Finset.expect_comm]
          apply Finset.expect_congr rfl
          intro y _
          apply Finset.expect_congr rfl
          intro x _
          simp only [multiplicativeDerivative, star_mul, star_star]
          ring
        _ = _ := by simp only [expect_star]
    rw [heq, hphase]
    simpa only [Complex.star_def, Complex.conj_re, Complex.ofReal_re] using hcorr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeFrozenComparison
namespace OAI

section

namespace Erdos3

theorem exists_nativeLowerPairModelBudget_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + nativePairModelConstant s) ^ nativePairModelConstant s ≤ (p + C) ^ C ∧
      nativeLowerPairModelBudget s p ≤ (p + C) ^ C := by
  let a := nativePairModelConstant s
  let b := rankUnitDescentConstant s
  let A : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (A + (A + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have ha : 0 ≤ (p + a) ^ a := by positivity
  have hb : 0 ≤ ((p + a) ^ a + b) ^ b := by positivity
  have hsum : (p + a) ^ a + ((p + a) ^ a + b) ^ b ≤ (p + C) ^ C := by
    simpa [A, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨(le_add_of_nonneg_right hb).trans hsum, (le_add_of_nonneg_left ha).trans hsum⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeFrozenComparison
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_fixed_model_frozen_comparison (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type} {σ : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (E : RationalFilteredNilmanifold M (s + 1) e) (φ : L →ₗ⁅ℚ⁆ M)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
      (T : Fin 2 → E.Niltest (fun _ : σ => 1)) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (∀ j, (T j).ComplexityLE p) →
      (∀ j x, ‖(T j).observable x‖ ≤ 1) →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp p →
      ∀ a r : Fin 2 → E.RealGroup,
        (∀ j i, |(E.basis.baseChange ℝ).repr (a j).coord i| ≤ Real.exp p) →
        (∀ j, (E.basis.baseChange ℝ).equivFun (r j).coord ∈ realDenominatorGrid m) →
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x : D.RealGroup,
          (T 0).observable (QuotientGroup.mk (a 0 * realificationMap
            (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ (z * x) * r 0)) *
          star ((T 1).observable (QuotientGroup.mk (a 1 * realificationMap
            (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ (z * x) * r 1))) =
          (T 0).observable (QuotientGroup.mk (a 0 * realificationMap
            (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r 0)) *
          star ((T 1).observable (QuotientGroup.mk (a 1 * realificationMap
            (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r 1)))) →
        Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C)
          (fun x => (T 0).observable (QuotientGroup.mk (a 0 * realificationMap
            (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ
            (D.filtration.realification.polynomialOrbitEval (fun _ => 1) x g) * r 0)) *
          star ((T 1).observable (QuotientGroup.mk (a 1 * realificationMap
            (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ
            (D.filtration.realification.polynomialOrbitEval (fun _ => 1) x g) * r 1))))) := by
  obtain ⟨K, _, hcover⟩ := exists_uniform_frozen_map (s + 1) 1
  obtain ⟨J, _, hdesc⟩ := exists_topInvariant_integer_expansion s
  let X : Polynomial ℕ := Polynomial.X
  let P := X + (X + Polynomial.C K) ^ K + 9
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C J) ^ J)
  refine ⟨C, hC, ?_⟩
  intro L M σ _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ g T p hp hD hT hcap hφ m hm hmb a r ha hr hinv
  obtain ⟨Λ, _hΛ, _hchar, _hnormal, _hfinite, _hindex, n, hn, hin, hout, hF, hmaps⟩ :=
    hcover D E φ p hp hD (hT 0).1 hφ m hm hmb
  let F := D.withLattice Λ n hn hin hout
  let u := (p + K) ^ K
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hmaps' (j : Fin 2) := hmaps (a j) (r j)
    (fun i => (ha j i).trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))) (hr j)
  choose hconj lip hlip hLip using hmaps'
  let S (j : Fin 2) : F.Niltest (fun _ : σ => 1) :=
    F.frozenComplexNiltest E φ (a j) (r j) (hconj j)
      ((T j).withUnitBound (hcap j)) g (lip j) (hLip j)
  have hSc (j : Fin 2) : (S j).ComplexityLE (p + u + 5) := by
    simpa only [show p + 1 + u + 4 = p + u + 5 by ring] using
      F.frozenComplexNiltest_complexity E φ (a j) (r j) (hconj j)
        ((T j).withUnitBound (hcap j)) g (lip j) (hLip j)
        (by linarith : 0 ≤ p + 1) hu hF
        ((T j).withUnitBound_complexity (hcap j) (hT j)) (hlip j)
  have hSn (j : Fin 2) (x : F.Space) : ‖(S j).observable x‖ ≤ 1 := (S j).norm_le x
  let U := (S 0).unitComparison (S 1) (hSn 0) (hSn 1)
  have hUc : U.ComplexityLE (p + u + 9) := by
    simpa only [show p + u + 5 + 4 = p + u + 9 by ring] using
      (S 0).unitComparison_complexity (S 1) (hSn 0) (hSn 1) (hSc 0) (hSc 1)
  have hUi (z : F.RealGroup) (hz : z ∈ F.filtration.realification.subgroup (s + 1))
      (x : F.Space) : U.observable (z • x) = U.observable x := by
    induction x using Quotient.inductionOn with
    | h x => exact hinv z hz x
  obtain ⟨V⟩ := hdesc F U (by positivity : 0 ≤ p + u + 9) hUc hUi
  have hcost : (p + u + 9 + J) ^ J ≤ (p + C) ^ C := by
    simpa [X, P, u, Polynomial.eval₂_pow] using hbudget p hp
  have heval : U.eval = (fun x => (T 0).observable (QuotientGroup.mk (a 0 * realificationMap
      (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fun _ => 1) x g) * r 0)) *
    star ((T 1).observable (QuotientGroup.mk (a 1 * realificationMap
      (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fun _ => 1) x g) * r 1)))) := rfl
  exact ⟨heval ▸ V.mono hcost⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AntisymmetricPairVerticalModel
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_antisymmetric_pair_outer_control :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r), 0 ≤ r →
      R.HasOuterValueControl ((p + q + r + C) ^ C) := by
  obtain ⟨a, _, hcontrol⟩ := exists_native_orbit_outer_control 2 2
  let X : Polynomial ℕ := Polynomial.X
  let B := X + (X + (X + 2) ^ 2 + 3) + 4
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V R hr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := p + q + r
  let b := u + raisedNiltestBudget u + 4
  let t := productNiltestBudget b + u + 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have hBt : antisymmetricPairBudget p q ≤ b := by
    dsimp [antisymmetricPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  have hprodmono : productNiltestBudget (antisymmetricPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (antisymmetricPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  let D := pi V.antisymmetricPairModels
  have hD : D.GeometryComplexityLE t := by
    apply (pi_geometry V.antisymmetricPairModels hB0
      (by simpa using (show (3 : ℝ) ≤ antisymmetricPairBudget p q from
        (by norm_num : (3 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le))
      (fun k => (V.antisymmetricPairTests_complexity k).1)).mono D
    exact (productNiltestBudget_geometry hB0).trans htest
  have hcost : (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  have hN : ∀ _k : Fin 2, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  have hout : R.HasOuterValueControl ((t + a) ^ a) :=
    hcontrol (R.mono hrt hN) ht hD hN (by simp)
  exact R.hasOuterValueControl_mono hout hcost

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedNarrowPathMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_narrow_path_marginal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτhalf : τ ≤ 1 / 2) (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedJointBaseDensity B U basis hb o hR hσ S X p hm
    let Z := selectedJointDensityMass bases stride T widths density
    ∃ (hN : ∀ x, 0 < N x) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∃ hnormalizer : |Z - 1| ≤ Real.exp (-P) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2,
    ∃ hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x,
    ∀ {Sites : Type*} [Fintype Sites] [Nonempty Sites]
      (root : Sites → LayerSamplerVariables G I n B → ℤ)
      (_hroot : ∀ t k, |(root t k : ℝ)| ≤ Real.exp P)
      (hrootSum : ∀ t, (∑ k, |(root t k : ℝ)|) ≤ W),
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
        ((allocatedOriginalPathLaw B U basis hb o hR hσ S X p hm N hN _hW _hτ _hξ
          stride T hmass bases hbases hnormalizer.2.2.1).siteLaw
          (narrowPhysicalSiteMap (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) _hW _hτ _hξ1 N hN hmargin root hrootSum))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) ≤
          6 * positiveProjectionAccuracy P := by
  obtain ⟨A₁, hA₁, hone⟩ := exists_allocated_narrow_oneSite_domination m
  obtain ⟨A₂, hA₂, hnorm⟩ := exists_allocated_narrow_normalization m
  let A := max (max A₁ A₂) 256
  have hA : 256 ≤ A := le_max_right _ _
  have hA₁A : A₁ ≤ A := (le_max_left _ _).trans (le_max_left _ _)
  have hA₂A : A₂ ≤ A := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨A, by omega, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize rank hrank hRank T hT widths bases density Z
  have hthreshold (a : ℕ) (ha : a ≤ A) :
      Real.exp ((P + a) ^ a) ≤ Real.exp ((P + A) ^ A) := by
    have hAr : (256 : ℝ) ≤ A := by exact_mod_cast hA
    have har : (a : ℝ) ≤ A := by exact_mod_cast ha
    apply Real.exp_le_exp.mpr
    exact (pow_le_pow_left₀ (by positivity) (by linarith : P + (a : ℝ) ≤ P + A) a).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ P + A) ha)
  obtain ⟨hwidths, hmass, hone⟩ := hone B U basis S hb o μ ν
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP
    hW hWP hτ hτP hξ hξ1 hξP N
    (fun x => (hthreshold A₁ hA₁A).trans (hsize x)) hrank
    ((hthreshold A₁ hA₁A).trans hRank) T hT
  obtain ⟨_, _, _, hnorm⟩ := hnorm B U basis S hb o μ ν
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP
    hW hWP hτ hτP hξ hξ1 hξP N
    (fun x => (hthreshold A₂ hA₂A).trans (hsize x)) hrank
    ((hthreshold A₂ hA₂A).trans hRank) T hT
  have hN (x) : 0 < N x := by exact_mod_cast (Real.exp_pos _).trans_le (hsize x)
  have hmarginSize (x) : 4 ≤ τ * (N x : ℝ) :=
    spatialTrimMargin_size_of_exp_size hP hτ hτP
      ((spatial_threshold_large hP hA).trans (hsize x))
  have hproper := spatialTrimMargin_proper hτhalf N hN hmarginSize
  have hbases : bases.Nonempty := trimmedIntegerBox_nonempty N _ hproper
  have hbox : (integerBox N).Nonempty := by
    let : ∀ x, NeZero (N x) := fun x => ⟨(hN x).ne'⟩
    exact integerBox_nonempty N
  have hnormalizer : |Z - 1| ≤ Real.exp (-P) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2 := hnorm bases hbases
  have hmargin (x) := (hproper x).le
  refine ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Sites _ _ root hroot hrootSum
  let : Nonempty (integerBox N) := hbox.to_subtype
  let e : integerBox N → X → ℝ := fun x i => (x.val i : ℝ)
  have he : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hc : (x.val i : ℝ) = (y.val i : ℝ) := congrFun hxy i
    exact_mod_cast hc
  have hloss : (∑ x, 2 * (spatialTrimMargin τ N x : ℝ) / N x) ≤ 1 / 2 := by
    have h := spatialTrimMargin_error_bound N hN hmarginSize
    linarith
  have hcard : (Fintype.card (integerBox N) : ℝ) / bases.card ≤ 2 := by
    simpa only [Fintype.card_coe] using trimmedIntegerBox_card_ratio_le_two N _ hproper hloss
  have hcap : 0 ≤ ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j) :=
    Finset.prod_nonneg (fun j _ => earlyConstantDensityCap_nonneg _ _ (hR j) (V j).coe_nonneg)
  have h := selectedJointFiniteLaw_site_excess bases hbases stride T widths hwidths hmass density
    (allocatedJointBaseDensity_nonneg B U basis hb o hR hσ S X p hm)
    hnormalizer.2.2.1 hnormalizer.2.1.1 e he root
    (narrowPhysicalSiteMap (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτ hξ1 N hN hmargin root hrootSum)
    (fun z t => narrowPhysicalSiteMap_cast (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτ hξ1 N hN hmargin root hrootSum z t)
    hcard hcap (fun a t φ hφ => hone a (root t) (hroot t) φ hφ)
  exact h.trans_eq (by ring)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCenteredNarrowPrescribedMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_narrow_prescribed_marginal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P E : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτhalf : τ ≤ 1 / 2) (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((max P E + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((max P E + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedJointBaseDensity B U basis hb o hR hσ S X p hm
    let Z := selectedJointDensityMass bases stride T widths density
    ∃ (hN : ∀ x, 0 < N x) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∃ hnormalizer : |Z - 1| ≤ Real.exp (-E) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2,
    ∃ hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x,
    ∀ {Sites : Type*} [Fintype Sites] [Nonempty Sites]
      (root : Sites → LayerSamplerVariables G I n B → ℤ)
      (_hroot : ∀ t k, |(root t k : ℝ)| ≤ Real.exp P)
      (hrootSum : ∀ t, (∑ k, |(root t k : ℝ)|) ≤ W),
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
        ((allocatedOriginalPathLaw B U basis hb o hR hσ S X p hm N hN _hW _hτ _hξ
          stride T hmass bases hbases hnormalizer.2.2.1).siteLaw
          (narrowPhysicalSiteMap (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) _hW _hτ _hξ1 N hN hmargin root hrootSum))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) ≤
          6 * positiveProjectionAccuracy E := by
  obtain ⟨A, hA, hmarginal⟩ := exists_allocated_narrow_path_marginal m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P E hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize rank hrank hRank T hT widths bases density Z
  have hPP : P ≤ max P E := le_max_left _ _
  have hEP : E ≤ max P E := le_max_right _ _
  have hexp := Real.exp_le_exp.mpr hPP
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, hsite⟩ :=
    hmarginal B U basis S hb o μ ν hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall
      (hP.trans hPP) (hmSize.trans hPP) (hK.trans hPP) (hX.trans hPP) (hdim.trans hPP)
      (fun j => (hRP j).trans hexp) (fun j => (hσP j).trans hexp)
      (fun j => (hcount j).trans hPP) (fun j => (hI j).trans hPP)
      (fun j => (hn j).trans hPP) (fun j => (hJ j).trans hPP)
      (hAP.trans hexp) (hLP.trans hexp) (fun j => (hCP j).trans hexp)
      (fun j => (hVP j).trans hexp) p hp hm stride hs (fun j => (hsP j).trans hexp)
      hW (hWP.trans hexp) hτ (hτP.trans hexp) hτhalf hτdim hξ hξ1 (hξP.trans hexp)
      N hsize hrank hRank T hT
  have hnormalizer' : |Z - 1| ≤ Real.exp (-E) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2 :=
    ⟨hnormalizer.1.trans (Real.exp_le_exp.mpr (neg_le_neg hEP)), hnormalizer.2⟩
  refine ⟨hN, hbases, hbox, hmass, hnormalizer', hmargin, ?_⟩
  intro Sites _ _ root hroot hrootSum
  have h := hsite root (fun t k => (hroot t k).trans hexp) hrootSum
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 6)
  unfold positiveProjectionAccuracy
  exact Real.exp_le_exp.mpr (by linarith)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedInactiveSupportBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)

include h

theorem allocatedNaturalSupportRadius_exp_bound (j : Fin m) (i : Fin (n j)) :
    allocatedNaturalSupportRadius (G := G) B α j i ≤ Real.exp (allocatedNaturalSupportLog D) := by
  have hb := allocatedIntegerBlock_card_le B rowSets h j i
  have hs : ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ D := by
    simpa only [layerIntegerPrincipalSlots_card] using hb
  have hblock := blockJetScaleBound_four_exp (Fintype.card α) (j.val + 1)
    (Fintype.card (B ⟨j, Sum.inr i⟩)) h.nonneg h.cube (h.layer_degree B j) hb
  have hD := h.nonneg
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hc : allocatedNaturalConstantRadius (G := G) B j i ≤ Real.exp (D + 1) := by
    unfold allocatedNaturalConstantRadius
    calc
      _ ≤ Real.exp 1 * Real.exp D := mul_le_mul htwo
        (by linarith [Real.add_one_le_exp D]) (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, add_comm]
  have ha := add_le_exp_add_one (by positivity : 0 ≤ D ^ 2 + 2 * D + 4)
    (by norm_num : (0 : ℝ) ≤ 0) hblock (by norm_num : (1 / 4 : ℝ) ≤ Real.exp 0)
  have ht := add_le_exp_add_one (by positivity : 0 ≤ (D ^ 2 + 2 * D + 4) + 0 + 1)
    (by positivity : 0 ≤ D + 1) ha hc
  exact ht.trans_eq (by
    congr 1
    unfold allocatedNaturalSupportLog
    ring)

theorem allocatedNaturalSiteRadius_exp_bound (j : Fin m) (i : Fin (n j)) :
    allocatedNaturalSiteRadius (G := G) B j i (rowSets j) + 1 / 4 ≤
      Real.exp (allocatedNaturalSiteLog D) := by
  have hD := h.nonneg
  have hrow : ((rowSets j).card : ℝ) ≤ D := by
    simpa only [Fintype.card_coe] using h.rows j
  have hr : ((rowSets j).card : ℝ) ≤ Real.exp D :=
    hrow.trans (show D ≤ Real.exp D by linarith [Real.add_one_le_exp D])
  have hs := allocatedNaturalSupportRadius_exp_bound B rowSets h j i
  have hm : allocatedNaturalSiteRadius (G := G) B j i (rowSets j) ≤
      Real.exp (D + allocatedNaturalSupportLog D) := by
    unfold allocatedNaturalSiteRadius
    exact (mul_le_mul hr hs (allocatedNaturalSupportRadius_nonneg B α j i)
      (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  have ht := add_le_exp_add_one (add_nonneg hD (allocatedNaturalSupportLog_nonneg hD))
    (by norm_num : (0 : ℝ) ≤ 0) hm (by norm_num : (1 / 4 : ℝ) ≤ Real.exp 0)
  exact ht.trans_eq (by
    congr 1
    unfold allocatedNaturalSiteLog allocatedNaturalSupportLog
    ring)

theorem allocatedSiteCoefficientRadius_exp_bound (a : Σ j : Fin m, Fin (n j)) :
    allocatedSiteCoefficientRadius (G := G) B rowSets a ≤ Real.exp (allocatedSiteCoefficientLog D) := by
  have hD := h.nonneg
  have hs := allocatedNaturalSupportRadius_exp_bound B rowSets h a.1 a.2
  have ht := allocatedNaturalSiteRadius_exp_bound B rowSets h a.1 a.2
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ (a.1.val + 1) ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo
      (by norm_num) (a.1.val + 1) (h.layer_degree B a.1)
  unfold allocatedSiteCoefficientRadius
  refine max_le (hs.trans (Real.exp_le_exp.mpr ?_)) ?_
  · unfold allocatedNaturalSupportLog allocatedSiteCoefficientLog
    linarith
  · have hh := (mul_le_mul hp ht
      (by have hn := allocatedNaturalSiteRadius_nonneg (G := G) B a.1 a.2 (rowSets a.1); positivity)
      (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
    exact hh.trans_eq (by
      congr 1
      unfold allocatedSiteCoefficientLog allocatedNaturalSiteLog
      ring)

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCoverLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

theorem allocatedIdealCoverRadius_inverse_from_dimensions {D c : ℝ}
    (h : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)
    (hc : 0 ≤ c) (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ D)
    (hn : ∀ j, (n j : ℝ) ≤ D)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCc : ∀ j, C j ≤ Real.exp c) (j : Fin m) :
    (allocatedIdealCoverRadius (G := G) B rowSets C j)⁻¹ ≤
      Real.exp (8 * allocatedIdealCoverInputLog m D c + 14) := by
  obtain ⟨hL, hLA, hLI, hLW, hLD, hLc⟩ := allocatedIdealCoverInputLog_bounds m h.nonneg hc
  have hde : D ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have heL := Real.exp_le_exp.mpr hLD
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpowtwo : (2 : ℝ) ^ Fintype.card α ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo
      (by norm_num) (Fintype.card α) h.cube
  have hbase : (Fintype.card α : ℝ) + 1 ≤ Real.exp D := by
    linarith [Real.add_one_le_exp D, h.cube]
  have hpow := pow_le_exp_mul_of_le_exp (by positivity) hbase h.nonneg
    (j.val + 1) (h.layer_degree B j)
  have hA : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤
        Real.exp (D ^ 2 + 2 * D) := by
    calc
      _ ≤ Real.exp D * (Real.exp D * Real.exp (D * D)) := by
        gcongr
        exact (h.coefficients j).trans hde
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hIdeal : partitionedIdealRadius α m + 1 ≤ Real.exp (allocatedIdealCoverInputLog m D c) := by
    apply (partitionedIdealRadius_add_one_le_exp α m).trans
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_left h.cube (by positivity : 0 ≤ (m : ℝ) + 1)
    push_cast at hLI
    linarith
  have hWindow (i : Fin (n j)) : allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1 ≤
      Real.exp (allocatedIdealCoverInputLog m D c) := by
    have h1 := one_add_le_exp_succ (allocatedSiteCoefficientLog_nonneg h.nonneg)
      (allocatedSiteCoefficientRadius_exp_bound B rowSets h ⟨j, i⟩)
    have h2 : allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1 ≤
        Real.exp (allocatedSiteCoefficientLog D + 1) := by
      simpa only [add_comm] using h1
    exact h2.trans (Real.exp_le_exp.mpr hLW)
  have hrows : ((rowSets j).card : ℝ) ≤ D := by
    simpa only [Fintype.card_coe] using h.rows j
  exact allocatedIdealCoverRadius_inv_le_exp B rowSets hL C hC j
    (hA.trans (Real.exp_le_exp.mpr hLA)) hIdeal ((hn j).trans (hde.trans heL)) hWindow
    (hrows.trans (hde.trans heL)) ((hI j).trans (hde.trans heL))
    ((hCc j).trans (Real.exp_le_exp.mpr hLc))

theorem allocatedIdealCoverPrimitiveRadius_le {p c : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hq : Fintype.card α ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCc : ∀ j, C j ≤ Real.exp c) (j : Fin m) :
    allocatedIdealCoverPrimitiveRadius m p c ≤ allocatedIdealCoverRadius (G := G) B rowSets C j := by
  have h := allocatedComparisonDimensions_of_primitive (G := G) (α := α)
    (O := fun j => (rowSets j : Type _)) B
    (fun j => (Subtype.val : rowSets j → Finset α)) hq (fun _ => Subtype.val_injective) hp hvars hI hn
  have hpD := (allocatedComparisonDimension_bounds m hp).2.2.1
  have hi := allocatedIdealCoverRadius_inverse_from_dimensions B rowSets h hc
    (fun j => (hI j).trans hpD) (fun j => (hn j).trans hpD) C hC hCc j
  have hr := allocatedIdealCoverRadius_pos (G := G) B rowSets C hC j
  have hinv := (inv_le_inv₀ (Real.exp_pos (allocatedIdealCoverPrimitiveLog m p c)) (inv_pos.mpr hr)).2 hi
  simpa only [allocatedIdealCoverPrimitiveRadius, Real.exp_neg, inv_inv] using hinv

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialBoxDetection
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem exists_polynomial_box_detection.{u,v} (s : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type v} [Fintype σ] [DecidableEq σ] {L : Type u} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ), 0 ≤ p →
      (Fintype.card σ : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) p →
      ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (T : D.Niltest w), T.ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) p) →
      ∀ (a : σ → ℤ) (lengths : σ → ℕ) [∀ i, NeZero (lengths i)] (f : (σ → ℤ) → ℂ),
      (∀ x ∈ translatedIntegerBox a lengths, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖finiteCorrelation (translatedIntegerBox a lengths) f T.eval‖ →
      Real.exp (-((p + C) ^ C)) ≤ finiteSupportGowersNorm (s + 1) (translatedIntegerBox a lengths) f := by
  obtain ⟨c, _, hc⟩ := exists_boxNiltestDetection s
  let R := (Polynomial.X + P + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ _ _ L _ _ d _ _ _ _ D p hp hσ w hw T hT a lengths _ f hf hcorr
  let q := p + P.eval₂ (Nat.castRingHom ℝ) p
  have hP : 0 ≤ P.eval₂ (Nat.castRingHom ℝ) p := natPolynomial_eval_nonneg P hp
  have hq : 0 ≤ q := add_nonneg hp hP
  have hPq : P.eval₂ (Nat.castRingHom ℝ) p ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hcorrq := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hcorr
  have hn := hc D q hq (hσ.trans hPq) w hw T (hT.mono hPq) a lengths f hf hcorrq
  have hbudget : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  exact (Real.exp_le_exp.mpr (neg_le_neg hbudget)).trans hn

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AllocatedNiltestSourceSelection
namespace OAI

universe u v w w₁ w₂ w₃ w₄

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_nested_box_niltest_detection (s : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {I : Type v} [Fintype I] [DecidableEq I] {L : Type u} [LieRing L] [LieAlgebra ℚ L] {dim : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s dim) (p : ℝ), 0 ≤ p →
      (Fintype.card I : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) p →
      ∀ (T : D.Niltest (fun _ : I => 1)), T.ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) p) →
      ∀ (c b : I → ℤ) (m d : ℕ) (H K : I → ℕ), 0 < m → 0 < d → (∀ i, 0 < K i) →
      commonStrideBox b d K ⊆ commonStrideBox c m H →
      ∀ f : (I → ℤ) → ℂ, (∀ x ∈ commonStrideBox b d K, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖finiteCorrelation (commonStrideBox b d K) f
        (fun y => T.eval (commonStrideIndex c m y))‖ →
      Real.exp (-((p + C) ^ C)) ≤ finiteSupportGowersNorm (s + 1) (integerBox K)
        (fun x => f (commonStridePoint b d x)) := by
  obtain ⟨C, hC, hdetect⟩ := exists_polynomial_box_detection s P
  refine ⟨C, hC, ?_⟩
  intro I _ _ L _ _ dim _ _ _ _ D p hp hI T hT c b m d H K hm hd hK hsub f hf hcorr
  obtain ⟨U, hU, heval⟩ := T.exists_nested_box_restriction c b hm hd H K hK hsub
  let _ : ∀ i, NeZero (K i) := fun i => ⟨(hK i).ne'⟩
  have hzero : translatedIntegerBox (0 : I → ℤ) K = integerBox K := by
    simp [translatedIntegerBox, translateSupport]
  have hcorr' : Real.exp (-p) ≤ ‖finiteCorrelation (integerBox K)
      (fun x => f (commonStridePoint b d x)) U.eval‖ := by
    rw [finiteCorrelation_commonStrideBox b hd] at hcorr
    have he : finiteCorrelation (integerBox K) (fun x => f (commonStridePoint b d x)) U.eval =
        finiteCorrelation (integerBox K) (fun x => f (commonStridePoint b d x))
          (fun x => T.eval (commonStrideIndex c m (commonStridePoint b d x))) := by
      apply Finset.expect_congr rfl
      intro x hx
      rw [heval x hx]
    rwa [he]
  have hn := hdetect D p hp hI (fun _ : I => 1) (fun _ => zero_lt_one) U ((hU _).mpr hT)
    0 K (fun x => f (commonStridePoint b d x))
    (fun x hx => hf _ (commonStridePoint_mem b d K (hzero ▸ hx))) (hzero.symm ▸ hcorr')
  simpa only [hzero] using hn

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_finite_site_niltest_detection (s : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {I : Type v} [Fintype I] [DecidableEq I] {L : Type u} [LieRing L] [LieAlgebra ℚ L] {dim : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s dim) (p : ℝ), 0 ≤ p →
      (Fintype.card I : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) p →
      ∀ (U : D.Niltest (fun _ : I => 1)), U.ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) p) →
      ∀ {T : Type w} [Nonempty T] [DecidableEq T] (e : T → I → ℤ), Function.Injective e →
      ∀ (A S : Finset T) (c b : I → ℤ) (m d : ℕ) (H K : I → ℕ),
      0 < m → 0 < d → (∀ i, 0 < K i) → A ⊆ S →
      S.image e = commonStrideBox c m H → A.image e = commonStrideBox b d K →
      ∀ (f w : T → ℂ), (∀ t, ‖f t‖ ≤ 1) →
      (∀ t ∈ S, w t = star (U.eval (commonStrideIndex c m (e t)))) →
      Real.exp (-p) ≤ ‖𝔼 t ∈ A, f t * w t‖ →
      Real.exp (-((p + C) ^ C)) ≤ finiteSupportGowersNorm (s + 1) (integerBox K)
        (fun x => finiteSiteExtension e f (commonStridePoint b d x)) := by
  obtain ⟨C, hC, hdetect⟩ := exists_nested_box_niltest_detection s P
  refine ⟨C, hC, ?_⟩
  intro I _ _ L _ _ dim _ _ _ _ D p hp hI U hU T _ _ e he A S c b m d H K hm hd hK hAS hS hA f w hf hw hc
  have hsub : commonStrideBox b d K ⊆ commonStrideBox c m H := by
    rw [← hA, ← hS]
    exact Finset.image_subset_image hAS
  have heq := finiteSiteExtension_test_mean e he A f w
    (fun y => U.eval (commonStrideIndex c m y)) (fun t ht => hw t (hAS ht))
  rw [heq, hA] at hc
  exact hdetect D p hp hI U hU c b m d H K hm hd hK hsub (finiteSiteExtension e f)
    (fun x _ => finiteSiteExtension_norm_le e f hf x) hc

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

theorem exists_sampled_niltest_cube_detection_with_sides (s : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {I : Type v} [Fintype I] [DecidableEq I]
      {Ω : Type w₁} [Fintype Ω] [Nonempty Ω] {T : Type w₂} [Fintype T] [Nonempty T]
      {X : Type w₃} {J : Ω → Type w₄} [∀ z, Nonempty (J z)]
      {L : ∀ z, J z → Type u} [∀ z j, LieRing (L z j)] [∀ z j, LieAlgebra ℚ (L z j)]
      {dim : ∀ z, J z → ℕ}
      [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] L z j)] [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L z j)]
      [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] L z j)]
      (D : ∀ z j, RationalFilteredNilmanifold (L z j) s (dim z j))
      (U : ∀ z j, (D z j).Niltest (fun _ : I => 1))
      (μ : FiniteProbabilityWeights Ω) (F : Ω → T → X)
      (S : ∀ z, J z → Finset T) (e : T → I → ℤ), Function.Injective e →
      ∀ (c : ∀ z, J z → I → ℤ) (m : ∀ z, J z → ℕ) (H : ∀ z, J z → I → ℕ),
      (∀ z j, 0 < m z j) → (∀ z j, (S z j).image e = commonStrideBox (c z j) (m z j) (H z j)) →
      ∀ (p q : ℝ) (N : I → ℕ), 0 ≤ p → 0 ≤ q →
      (∀ z j, IsDenseCommonStrideBox N p ((S z j).image e)) →
      (Fintype.card I : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) q →
      (∀ z j, (U z j).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) q)) →
      (∀ z j, ((U z j).normBound : ℝ) ≤ 1) →
      ∀ (v : X → ℂ) (α : ℝ), (∀ x, ‖v x‖ ≤ 1) → 0 < α → α ≤ 1 →
      Fintype.card I * Real.exp (-p) ≤ α / 8 → Real.exp (-q) ≤ α / 4 →
      α ≤ sampledSliceSeminorm μ F S
        (fun z j t => star ((U z j).eval (commonStrideIndex (c z j) (m z j) (e t)))) v →
      ∃ (b : I → ℤ) (d : ℕ) (K : I → ℕ), 0 < d ∧ (∀ i, 0 < K i) ∧
        (∀ i, integerProgressionSupport (b i) (d : ℤ) (K i) ⊆ Finset.Ico (0 : ℤ) (N i : ℤ)) ∧
        (∀ i, Real.exp (-(p + 1)) * N i ≤ (K i : ℝ)) ∧
        IsDenseCommonStrideBox N (p + 1) (commonStrideBox b d K) ∧
        commonStrideBox b d K ⊆ Finset.univ.image e ∧
        (Real.exp (-((5 * p + 20) * Fintype.card I + p + 2)) * (α / 2)) *
          Real.exp (-((q + C) ^ C)) ^ (2 ^ (s + 1)) ≤
          (μ.complexMean (fun z => normalizedSupportedCubeSum (s + 1) (integerBox K)
            (fun _ x => finiteSiteExtension e (fun t => v (F z t)) (commonStridePoint b d x)))).re := by
  obtain ⟨C, hC, hdetect⟩ := exists_finite_site_niltest_detection s P
  refine ⟨C, hC, ?_⟩
  intro I _ _ Ω _ _ T _ _ X J _ L _ _ dim _ _ _ _ D U μ F S e he c m H hm hS p q N hp hq
    hslice hI hU hcap v α hv hα hαone hmesh hthreshold hmean
  let w : ∀ z, J z → T → ℂ := fun z j t =>
    star ((U z j).eval (commonStrideIndex (c z j) (m z j) (e t)))
  have hw (z) (j) (t) : ‖w z j t‖ ≤ 1 := by
    simpa only [w, norm_star] using
      ((U z j).norm_eval_le (commonStrideIndex (c z j) (m z j) (e t))).trans (hcap z j)
  obtain ⟨A, hAn, hAdense, G, j, hmass, hcorr⟩ :=
    exists_dense_common_sampled_box_of_seminorm μ F S w e he hp N hslice hw v hv hα hαone hmesh hmean
  have hDense := hAdense
  obtain ⟨b, d, K, hd, hK, hsubsetK, hdenseK, hA⟩ := hAdense
  have hnorm (z : Ω) (hz : z ∈ G) :
      Real.exp (-((q + C) ^ C)) ≤ finiteSupportGowersNorm (s + 1) (integerBox K)
        (fun x => finiteSiteExtension e (fun t => v (F z t)) (commonStridePoint b d x)) := by
    exact hdetect (D z (j z)) q hq hI (U z (j z)) (hU z (j z)) e he A (S z (j z))
      (c z (j z)) b (m z (j z)) d (H z (j z)) K (hm z (j z)) hd hK
      (hcorr z hz).1 (hS z (j z)) hA (fun t => v (F z t)) (w z (j z))
      (fun t => hv _) (fun _ _ => rfl) (hthreshold.trans (hcorr z hz).2)
  refine ⟨b, d, K, hd, hK, hsubsetK, hdenseK, ?_, ?_, ?_⟩
  · rw [← hA]
    exact hDense
  · rw [← hA]
    exact Finset.image_subset_image (Finset.subset_univ A)
  · let _ : ∀ i, NeZero (K i) := fun i => ⟨(hK i).ne'⟩
    exact sampled_normalized_cube_lower_bound (boxReduction_reflectsPairSums K) μ G s
      (fun z x => finiteSiteExtension e (fun t => v (F z t)) (commonStridePoint b d x))
      (Real.exp_nonneg _) hmass hnorm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AllocatedNiltestSupportedSlicedDetection
namespace OAI

section

namespace Erdos3

noncomputable def sampledSupportedSlicedDetectionConstant (s : ℕ) (P : Polynomial ℕ) : ℕ :=
  Classical.choose (exists_sampled_niltest_cube_detection_with_sides.{0,0,0,0,0,0} s P)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedProductChartRadius
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable {D c : ℝ}
variable (hdim : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)
variable (hc : 0 ≤ c) (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ D) (hn : ∀ j, (n j : ℝ) ≤ D)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCc : ∀ j, C j ≤ Real.exp c)

local notation "H" => 8 * allocatedIdealCoverInputLog m D c + 14
local notation "F" => H + 2 * D + 2

include hdim hc hI hn hC hCc in
theorem allocatedProductIdealSiteRadius_exp_bound :
    2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) ≤ Real.exp F := by
  have hD := hdim.nonneg
  have hde : D ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have hH := (allocatedProductChartLog_bounds m hD hc).1
  have hsupport (j : Fin m) : allocatedIdealCoverSupport (G := G) B rowSets j ≤ Real.exp H :=
    (finiteRowChartRadius_support_le_inv (rowSets j).card (Fintype.card (I j))
      (hC j) (allocatedIdealCoverSupport_nonneg B rowSets j)).trans
      (allocatedIdealCoverRadius_inverse_from_dimensions B rowSets hdim hc hI hn C hC hCc j)
  have hrows (j : Fin m) : ((rowSets j).card : ℝ) ≤ D := by
    simpa only [Fintype.card_coe] using hdim.rows j
  have hsum : (∑ j : Fin m, (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j) ≤
      Real.exp (2 * D + H) := by
    calc
      _ ≤ ∑ _j : Fin m, D * Real.exp H := Finset.sum_le_sum (fun j _ =>
        mul_le_mul (hrows j) (hsupport j) (allocatedIdealCoverSupport_nonneg B rowSets j) hD)
      _ = (m : ℝ) * (D * Real.exp H) := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ Real.exp D * (Real.exp D * Real.exp H) :=
        mul_le_mul (hdim.degree.trans hde)
          (mul_le_mul_of_nonneg_right hde (Real.exp_pos _).le)
          (mul_nonneg hD (Real.exp_pos _).le) (Real.exp_pos _).le
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hradius : (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) ≤
      Real.exp (2 * D + H + 1) := by
    change 1 + ∑ j : Fin m, (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j ≤ _
    exact one_add_le_exp_succ (add_nonneg (mul_nonneg (by norm_num) hD) hH) hsum
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ Real.exp 1 * Real.exp (2 * D + H + 1) :=
      mul_le_mul htwo hradius (allocatedProductIdealSiteRadius (G := G) B rowSets).coe_nonneg (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

include hdim hc hI hn hC hCc in
theorem allocatedProductGridRadius_inv_exp_bound (j : Fin m) :
    (allocatedProductGridRadius (G := G) B rowSets C j)⁻¹ ≤
      Real.exp (allocatedProductChartLog m D c) := by
  obtain ⟨_, hF, h2DF, hDF, hcF, _, _⟩ := allocatedProductChartLog_bounds m hdim.nonneg hc
  have hrows : ((rowSets j).card : ℝ) ≤ D := by
    simpa only [Fintype.card_coe] using hdim.rows j
  have hrowadd : ((rowSets j).card : ℝ) + 1 ≤ Real.exp D := by
    linarith [Real.add_one_le_exp D]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsites : (Fintype.card (Finset α) : ℝ) ≤ Real.exp D := by
    simpa only [Fintype.card_finset, Nat.cast_pow, Nat.cast_ofNat, mul_one] using
      pow_le_exp_mul_of_le_exp (by norm_num : (0 : ℝ) ≤ 2) htwo
        (by norm_num : (0 : ℝ) ≤ 1) (Fintype.card α) hdim.cube
  have hrowcount : ((((rowSets j).card + 1) * Fintype.card (Finset α) : ℕ) : ℝ) ≤ Real.exp F := by
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact ((mul_le_mul hrowadd hsites (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (show Real.exp D * Real.exp D = Real.exp (2 * D) by rw [← Real.exp_add]; congr 1; ring)).trans
        (Real.exp_le_exp.mpr h2DF)
  have hDexp : D ≤ Real.exp F :=
    (show D ≤ Real.exp D by linarith [Real.add_one_le_exp D]).trans (Real.exp_le_exp.mpr hDF)
  exact finiteRowChartRadius_inv_le_exp
    (((rowSets j).card + 1) * Fintype.card (Finset α)) (Fintype.card (I j))
    (hC j) (mul_nonneg (by norm_num) (allocatedProductIdealSiteRadius (G := G) B rowSets).coe_nonneg)
    hF hrowcount ((hI j).trans hDexp) ((hCc j).trans (Real.exp_le_exp.mpr hcF))
    (allocatedProductIdealSiteRadius_exp_bound B rowSets hdim hc hI hn C hC hCc)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedUniformEarlyRadiusWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

section Charts

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

theorem allocatedCommonRadius_admissible {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hq : Fintype.card α ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCg : ∀ j, C j ≤ Real.exp g) (j : Fin m) :
    allocatedCommonRadius m p g ≤ allocatedBufferedPhysicalChartRadius (G := G) B α C j ∧
      allocatedCommonRadius m p g ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j ∧
      allocatedCommonRadius m p g ≤ allocatedIdealCoverRadius (G := G) B rowSets C j := by
  obtain ⟨_, hb, hi⟩ := allocatedCommonRadiusLog_bounds m hp hg
  have hbuffer : allocatedCommonRadius m p g ≤ allocatedBufferedPhysicalChartRadius (G := G) B α C j := by
    have hinv := (allocatedBufferedRadius_inverse_from_primitive B hp hg hq hvars hI hn C hC hCg j).trans
      (Real.exp_le_exp.mpr hb)
    have hpos := allocatedBufferedPhysicalChartRadius_pos (G := G) B α C hC j
    have h := (inv_le_inv₀ (Real.exp_pos (allocatedCommonRadiusLog m p g)) (inv_pos.mpr hpos)).2 hinv
    simpa only [allocatedCommonRadius, Real.exp_neg, inv_inv] using h
  refine ⟨hbuffer, hbuffer.trans (allocatedBufferedPhysicalChartRadius_le_original B α C hC j), ?_⟩
  apply le_trans _ (allocatedIdealCoverPrimitiveRadius_le B rowSets hp hg hq hvars hI hn C hC hCg j)
  exact Real.exp_le_exp.mpr (neg_le_neg hi)

end Charts

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

variable {D G R : Type*} {B : D → Type*} [Fintype D] [Fintype G]
    [∀ d, Fintype (B d)] [CommRing R]

omit [Fintype D] [Fintype G] [∀ d, Fintype (B d)] in

theorem samplerLong_killCompl_principal_monomial (inactive : D → Prop) (h : D → ℕ)
    (d : {d // ¬ inactive d}) (b : B d.val) (c : R) :
    killCompl (samplerLongEmbedding (G := G) inactive h).injective
      (monomial (principalCoefficientSlot h d.val b).val c) =
      c • ∏ k ∈ canonicalRankBlock (G := G)
        (B := fun a : {a // ¬ inactive a} => B a.val) (fun a => h a.val) d b, X k := by
  rw [← samplerLongEmbedding_principalExponent inactive h d b,
    killCompl_monomial_mapDomain, principalCoefficientSlot_monomial, smul_eq_C_mul]

theorem canonicalBoundedCoefficient_selected_long_top (inactive : D → Prop) (h : D → ℕ)
    (d : {d // ¬ inactive d}) (hd : 0 < h d.val) {J : ℕ} (block : Fin J ↪ B d.val)
    (fixed : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d.val) → R)
    (c : Fin J → R) (v : SamplerTupleIndex G B h → R) :
    homogeneousComponent (h d.val)
      (conditionPolynomial (samplerLongEmbedding inactive h)
        (samplerLongEmbedding inactive h).injective v
        (modularBoundedCoefficientPolynomial (h d.val)
          (Function.extend (canonicalPrincipalSubblockSlot h d.val block) c fixed))) =
      canonicalSelectedLongTopResidual inactive h d block fixed +
        ∑ j, c j • ∏ k ∈ canonicalRankBlock (G := G)
          (B := fun a : {a // ¬ inactive a} => B a.val)
          (fun a => h a.val) d (block j), X k := by
  have hdegree : (modularBoundedCoefficientPolynomial (h d.val)
      (Function.extend (canonicalPrincipalSubblockSlot h d.val block) c fixed)).totalDegree ≤
        h d.val := by
    apply totalDegree_finsetSum_le
    intro e _
    exact (totalDegree_monomial_le e.val _).trans e.property
  rw [homogeneousComponent_conditionPolynomial_top _ _ _ v (h d.val) hdegree,
    modularBoundedCoefficientPolynomial_selected_top (h d.val) _
      (canonicalPrincipalSubblockSlot_injective h d.val hd block)
      (canonicalPrincipalSubblockSlot_degree h d.val block), map_add, map_sum]
  change canonicalSelectedLongTopResidual inactive h d block fixed + _ = _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact samplerLong_killCompl_principal_monomial inactive h d (block j) (c j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}

noncomputable local instance congruenceIndexFintype [Fintype X] [∀ j, Fintype (E j)]
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :
    Fintype (AllocatedCongruenceCoefficientIndex X E inactive L) := inferInstance

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedZeroLayerForwardFrontSourceProfile
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

noncomputable def preparedFiniteForwardActualFrontLocalMaster
    (m : ℕ) (G : Type) [Fintype G] (count nX : ℕ) (Pdetect : Polynomial ℕ)
    (exponent Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (degree : ℕ)
    (x gainLog stageLog Bstruct pnum Pchart Qstride : ℝ) : ℝ :=
  let u := preparedFiniteForwardPairedSourcePrecision exponent Cdirect stageCountConstant 0
    false x gainLog stageLog
  let pModel := preparedFiniteForwardWork exponent stageCountConstant 0 x
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := allocatedModelTestLog u pModel
  let gain := slicedDetectionGainLog degree (sampledSupportedSlicedDetectionConstant degree Pdetect) count
    pDetect pDetect (2 * u + 4 * pModel + 7)
  let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G (gain + pDetect + 4)
  let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
  let target := gain + 40 + coefficientErrorSpatialLog Pphysical
  let Eprofile := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
  let Prho := 2 * affineProfileInputEnvelope D
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ)
    Eprofile (pDetect + 2) + 2
  preparedFiniteScheduleLocalMaster Pchart D pRadius Qstride Pphysical u pModel Prho target gain

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedSourceArrays
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

noncomputable def preparedFiniteForwardActualLocalMaster
    (m : ℕ) (G : Type) [Fintype G] (count nX : ℕ) (Pdetect : Polynomial ℕ)
    (exponent Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (r : ℕ)
    (x gainLog stageLog Bstruct pnum Pchart Qstride : ℝ) : ℝ :=
  let u := preparedFiniteForwardPairedSourcePrecision exponent Cdirect stageCountConstant r
    true x gainLog stageLog
  let pModel := preparedFiniteForwardWork exponent stageCountConstant r x
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := allocatedModelTestLog u pModel
  let gain := slicedDetectionGainLog r (sampledSupportedSlicedDetectionConstant r Pdetect) count
    pDetect pDetect (2 * u + 4 * pModel + 7)
  let Pk := scalarKernelLogarithmicBudget (Fin (r + 1)) G (gain + pDetect + 4)
  let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
  let target := gain + 40 + coefficientErrorSpatialLog Pphysical
  let Eprofile := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
  let Prho := 2 * affineProfileInputEnvelope D
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ)
    Eprofile (pDetect + 2) + 2
  preparedFiniteScheduleLocalMaster Pchart D pRadius Qstride Pphysical u pModel Prho target gain

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

noncomputable def preparedFiniteNestedSourceMaster
    (m : ℕ) (G : Type) [Fintype G] (count nX : ℕ) (Pdetect : Polynomial ℕ)
    (A Cdirect : ℕ) (constants : ℕ → ℕ)
    (Bstruct pnum Qstride gainLog stageLog : ℝ)
    {outerDepth innerDepth cutoff : ℕ}
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) : ℝ :=
  let degree := preparedFiniteNestedForwardAllDegreeDegree k
  let u := preparedFiniteForwardPairedSourcePrecision A Cdirect constants
    (preparedFiniteNestedForwardAllDegreeStage k).val
    (preparedFiniteNestedForwardAllDegreeIsDirect k)
    (preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k) gainLog stageLog
  let pModel := preparedFiniteForwardWork A constants
    (preparedFiniteNestedForwardAllDegreeStage k).val
    (preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k)
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := allocatedModelTestLog u pModel
  let gain := slicedDetectionGainLog degree
    (sampledSupportedSlicedDetectionConstant degree Pdetect) count
    pDetect pDetect (2 * u + 4 * pModel + 7)
  let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G (gain + pDetect + 4)
  let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
  let target := gain + 40 + coefficientErrorSpatialLog Pphysical
  let Eprofile := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
  let Prho := 2 * affineProfileInputEnvelope D
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ)
    Eprofile (pDetect + 2) + 2
  preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
    Pphysical u pModel Prho target gain

@[simp] theorem preparedFiniteNestedSourceMaster_front
    (m : ℕ) (G : Type) [Fintype G] (count nX : ℕ) (Pdetect : Polynomial ℕ)
    (A Cdirect : ℕ) (constants : ℕ → ℕ)
    (Bstruct pnum Qstride gainLog stageLog : ℝ)
    {outerDepth innerDepth cutoff : ℕ}
    (outer : Fin (outerDepth + 1)) (degree : Fin (cutoff + 1)) :
    preparedFiniteNestedSourceMaster m G count nX Pdetect A Cdirect constants
      Bstruct pnum Qstride gainLog stageLog
      (outer, (0 : Fin (innerDepth + 1)), degree, false) =
    preparedFiniteForwardActualFrontLocalMaster m G count nX Pdetect
      A Cdirect constants degree.val
      (candidateNestedForwardSeed A constants innerDepth outer.val Bstruct)
      gainLog stageLog Bstruct pnum Bstruct Qstride := rfl

@[simp] theorem preparedFiniteNestedSourceMaster_direct
    (m : ℕ) (G : Type) [Fintype G] (count nX : ℕ) (Pdetect : Polynomial ℕ)
    (A Cdirect : ℕ) (constants : ℕ → ℕ)
    (Bstruct pnum Qstride gainLog stageLog : ℝ)
    {outerDepth innerDepth cutoff : ℕ}
    (outer : Fin (outerDepth + 1)) (r : ℕ)
    (hrInner : r < innerDepth + 1) (hrDegree : r < cutoff + 1) :
    preparedFiniteNestedSourceMaster m G count nX Pdetect A Cdirect constants
      Bstruct pnum Qstride gainLog stageLog
      (outer, (⟨r, hrInner⟩ : Fin (innerDepth + 1)),
        (⟨r, hrDegree⟩ : Fin (cutoff + 1)), true) =
    preparedFiniteForwardActualLocalMaster m G count nX Pdetect
      A Cdirect constants r
      (candidateNestedForwardSeed A constants innerDepth outer.val Bstruct)
      gainLog stageLog Bstruct pnum Bstruct Qstride := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedFiniteNestedSourceProjectionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def preparedNestedFrontProjectionEnvelope
    {K : Type*} [Fintype K] (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth : ℕ) (outer inner : K → ℕ) (native : K → ℝ)
    (x gainLog stageLog endpoint : ℝ) : ℝ :=
  endpoint + 1 + ∑ k, preparedFiniteForwardFrontProjectionPrecision
    (preparedFiniteForwardModelPrecision A constants (inner k)
      (candidateNestedForwardSeed A constants innerDepth (outer k) x) gainLog stageLog)
    (preparedFiniteForwardWork A constants (inner k)
      (candidateNestedForwardSeed A constants innerDepth (outer k) x)) (native k)

end Erdos3.VectorPolynomial

end

end OAI
end


