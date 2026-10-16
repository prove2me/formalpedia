-- Prove2me | Definitions.Def_OAIErdos3B1332
-- name    : OAIErdos3B1332
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T19:24:08.301998+00:00
-- url     : https://prove2.me/theorems/9d8e12d3-71a3-4c79-95d2-0072ccf311d9
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1333 of 1346
-- statement:
--   Definitions bundle 1333 of 1346 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1331`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1333 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.ControlledSymbolFactorization.dilate_ratio`, `OAI.Erdos3.NilpotentLieFiltration.ControlledSymbolFactorizationAtFast.dilate_ratio`, `OAI.Erdos3.NilpotentLieFiltration.FullChartControlledFactors.homogeneousPullback_slow`, `OAI.Erdos3.NilpotentLieFiltration.exists_full_chart_major_correlation_witness_of_frozen_productive_local_tests`, `OAI.Erdos3.NilpotentLieFiltration.exists_full_chart_major_correlation_witness_of_native_detections`, `OAI.Erdos3.NilpotentLieFiltration.exists_full_chart_major_correlation_witness_of_prepared_detection`, `OAI.Erdos3.NilpotentLieFiltration.exists_full_chart_major_correlation_witness_of_productive_local_tests`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomialHom_homogeneousPullback`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomialHom_homogeneousPullback_coord`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomialHom_homogeneousPullback_of_chart`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolHom_basis_independent`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolMap_basis_independent`, `OAI.Erdos3.RationalFilteredNilmanifold.pairOrbitSymbol_basis_independent`, `OAI.Erdos3.RationalFilteredNilmanifold.pairOrbitSymbol_scalarAffinePullback`, `OAI.Erdos3.RationalFilteredNilmanifold.pairOrbitSymbol_scalarAffinePullback_inverse_stride`, `OAI.Erdos3.RationalFilteredNilmanifold.pairOrbitSymbol_scalarAffine_substitute`, `OAI.Erdos3.RationalFilteredNilmanifold.pairOrbit_substitute_log`, `OAI.Erdos3.VectorPolynomial.SampledSliceNativeDetection`, `OAI.Erdos3.VectorPolynomial.exists_nativeForecast_ambient_comparison`, `OAI.Erdos3.VectorPolynomial.exists_normalizedTwist_uniform_ambient_haar_budget`, `OAI.Erdos3.VectorPolynomial.majorPhasePlateauBoxSignal`, `OAI.Erdos3.VectorPolynomial.majorPhasePlateauBoxSignal_inside`, `OAI.Erdos3.VectorPolynomial.majorPhasePlateauBoxSignal_norm_le_one`, `OAI.Erdos3.VectorPolynomial.majorPhasePlateauBoxSignal_outside`, `OAI.Erdos3.VectorPolynomial.nativeFiniteExpansion_mean_comparison`, `OAI.Erdos3.VectorPolynomial.nativeForecastAmbientExponent`, `OAI.Erdos3.VectorPolynomial.normalizedTwistAmbientRankInput`, `OAI.Erdos3.VectorPolynomial.normalizedTwistAmbient_error_budget`, `OAI.Erdos3.exists_native_pair_affine_cell_step_drop`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1334

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedTwistUniformAmbientBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

noncomputable def normalizedTwistAmbientRankInput {R : Type*} [Semiring R] (z : R) : R :=
  let Q := 2 * z + 4
  2 * Q * (2 * Q + 2) ^ 4 + (2 * Q + 2) ^ 4 + 4 * Q + 16

theorem normalizedTwistAmbient_error_budget {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    {L : ℝ≥0} (hL : (L : ℝ) ≤ Real.exp P) :
    let Q := 2 * max P E + 4
    let p := normalizedTwistAmbientRankInput (max P E)
    2 * Real.exp (-Q) + Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) +
      (L : ℝ) * Real.exp (-2 * Q) / 2 ≤ Real.exp (-E) := by
  dsimp only
  let Q := 2 * max P E + 4
  let p := normalizedTwistAmbientRankInput (max P E)
  have hz : 0 ≤ max P E := hP.trans (le_max_left _ _)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hPQ : P ≤ Q := by dsimp [Q]; linarith [le_max_left P E]
  have hEQ : E + 4 ≤ Q := by dsimp [Q]; linarith only [le_max_right P E, hE]
  have hp : 2 * Q * (2 * Q + 2) ^ 4 + Q ≤ p := by
    dsimp [p, normalizedTwistAmbientRankInput, Q]
    nlinarith [pow_nonneg (show 0 ≤ 2 * (2 * max P E + 4) + 2 by positivity) 4]
  have ht : Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) ≤ Real.exp (-Q) :=
    Real.exp_le_exp.mpr (by linarith)
  have hl : (L : ℝ) * Real.exp (-2 * Q) ≤ Real.exp (-Q) := by
    calc
      _ ≤ Real.exp Q * Real.exp (-2 * Q) :=
        mul_le_mul_of_nonneg_right (hL.trans (Real.exp_le_exp.mpr hPQ)) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have he : 4 * Real.exp (-Q) ≤ Real.exp (-E) := by
    calc
      _ ≤ Real.exp 4 * Real.exp (-Q) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
      _ = Real.exp (4 - Q) := by rw [← Real.exp_add]; rfl
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  change 2 * Real.exp (-Q) + Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) +
    (L : ℝ) * Real.exp (-2 * Q) / 2 ≤ _
  linarith [Real.exp_pos (-Q)]

theorem exists_normalizedTwist_uniform_ambient_haar_budget (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X : Type} [Fintype X] [DecidableEq X]
      {J : Fin m → Type} [∀ j, Fintype (J j)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
      [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
      (∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) →
      (∀ j α, coefficients (poly j) α ∈ U j) →
      ∀ {periodCap coverCap : ℝ} {L : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
      {P E Rrank : ℝ}, 0 ≤ P → 0 ≤ E →
      (Fintype.card X : ℝ) ≤ P → (Fintype.card (Σ j, J j) : ℝ) ≤ P →
      (L : ℝ) ≤ Real.exp P → (W.cover : ℝ) ≤ Real.exp P → (W.modulus : ℝ) ≤ Real.exp P →
      ∀ (N : X → ℕ),
      (∀ i, Real.exp ((max P E + A) ^ A) ≤ (N i : ℝ)) →
      Real.exp ((max P E + A) ^ A) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      ‖(𝔼 x ∈ integerBox N, W.eval N poly x) -
        (𝔼 x ∈ integerBox N, W.frozenSingleSiteHaarReference U ν
          (fun i => (x i : ZMod W.modulus)) (fun i => (x i : ℝ) / N i))‖ ≤
        Real.exp (-E) := by
  obtain ⟨C, hC, hcomp⟩ := exists_normalizedTwist_uniform_ambient_haar_comparison m
  let B : Polynomial ℕ := (normalizedTwistAmbientRankInput Polynomial.X + Polynomial.C C) ^ C +
    3 * (2 * Polynomial.X + 4) + 16
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget B
  refine ⟨A, hA, ?_⟩
  intro X _ _ J _ U ν _ _ poly hp hm periodCap coverCap L W P E Rrank
    hP hE hX hdim hL hcover hmod N hlarge hRrank hrank
  let z := max P E
  let Q := 2 * z + 4
  let p := normalizedTwistAmbientRankInput z
  have hz : 0 ≤ z := hP.trans (le_max_left _ _)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hPQ : P ≤ Q := by dsimp [Q, z]; linarith [le_max_left P E]
  have hpQ : 3 * Q + 16 ≤ p := by
    change 3 * Q + 16 ≤ 2 * Q * (2 * Q + 2) ^ 4 + (2 * Q + 2) ^ 4 + 4 * Q + 16
    have hprod : 0 ≤ 2 * Q * (2 * Q + 2) ^ 4 := by positivity
    linarith [pow_nonneg (show 0 ≤ 2 * Q + 2 by positivity) 4]
  have hpFreq : (2 * Q + 2) ^ 4 ≤ p := by
    change (2 * Q + 2) ^ 4 ≤ 2 * Q * (2 * Q + 2) ^ 4 + (2 * Q + 2) ^ 4 + 4 * Q + 16
    have hprod : 0 ≤ 2 * Q * (2 * Q + 2) ^ 4 := by positivity
    linarith
  have hPp : P ≤ p := hPQ.trans (by linarith)
  have hb : (p + C) ^ C + 3 * Q + 16 ≤ (z + A) ^ A := by
    simpa [B, p, Q, normalizedTwistAmbientRankInput, Polynomial.eval₂_pow] using hbudget z hz
  have hpNonneg : 0 ≤ p := by linarith
  have hb' : (p + C) ^ C ≤ (z + A) ^ A := by linarith
  have h := hcomp U ν poly hp hm W (Real.exp_pos (-Q)) hQ (hdim.trans hPQ)
    (hL.trans (Real.exp_le_exp.mpr hPQ)) (by rw [Real.exp_neg, inv_inv]) hpQ hpFreq
    (hcover.trans (Real.exp_le_exp.mpr hPp)) (hmod.trans (Real.exp_le_exp.mpr hPQ)) N
    (hX.trans hPp) (fun i => (Real.exp_le_exp.mpr hb).trans (hlarge i))
    ((Real.exp_le_exp.mpr hb').trans hRrank) hrank
  exact h.trans (normalizedTwistAmbient_error_budget hP hE hL)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolGradedCoefficientBound
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local irreducible] realChartSubstitute realGradedSymbolPolynomial realSymbolHomogeneousPullback

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realGradedSymbolPolynomialHom_homogeneousPullback
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (g : F.RealPolynomialSymbolGroup w) :
    F.realGradedSymbolPolynomialHom b ω hF v
      (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ g) =
      realPolynomialChartSubstitution F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot
        β (F.realGradedSymbolPolynomialHom b ω hF w g) := by
  apply NilpotentLieBCHGroup.ext
  exact F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ g.coord

theorem realGradedSymbolPolynomialHom_homogeneousPullback_coord
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (g : F.RealPolynomialSymbolGroup w) :
    (F.realGradedSymbolPolynomialHom b ω hF v
      (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ g)).coord =
      realChartSubstitute β (F.realGradedSymbolPolynomialHom b ω hF w g).coord := by
  rw [F.realGradedSymbolPolynomialHom_homogeneousPullback b ω hF w v β hβ,
    realPolynomialChartSubstitution_coord]

theorem realGradedSymbolPolynomialHom_homogeneousPullback_of_chart
    {ν : Type*} (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (g : F.RealPolynomialSymbolGroup w) (chart : ν → MvPolynomial σ ℝ)
    (E : PolynomialGroup ν F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot)
    (hchart : F.realGradedSymbolPolynomialHom b ω hF w g =
      realPolynomialChartSubstitution F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot
        chart E) :
    (F.realGradedSymbolPolynomialHom b ω hF v
      (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ g)).coord =
      realChartSubstitute (fun i => MvPolynomial.aeval β (chart i)) E.coord := by
  rw [F.realGradedSymbolPolynomialHom_homogeneousPullback_coord b ω hF w v β hβ,
    hchart, realPolynomialChartSubstitution_coord, realChartSubstitute_comp]

theorem FullChartControlledFactors.homogeneousPullback_slow
    {L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {m : ℕ} {X : Type} [Fintype X]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    {budget : ℝ} (hcontrol : FullChartControlledFactors F b ω hF J poly N left right budget)
    (v : τ → ℕ) (β : (X ⊕ (Σ j, J j)) → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (fullTaggedVariableWeight (X := X) J i))
    (T : τ → ℝ) (hT : ∀ i, 0 < T i) {B : ℝ} (hB : 1 ≤ B)
    (hmass : ∀ i, realPolynomialMass (scaleMvPolynomialAxes T
      (MvPolynomial.aeval β (normalizedRealPolynomialChart (fun x => (N x : ℝ))
        (fullTaggedMajorTopCoordinates J poly) i))) ≤ B) :
    F.SymbolSlowBound b ω hF v T
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s *
        Real.exp budget * B ^ s)
      (F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight (X := X) J)
        v β hβ left) := by
  obtain ⟨q, hq, hqB, E, hchart, hbound, hweighted, hdegree, hgrid⟩ :=
    FullChartControlledFactors.exists_degree_bounded_chart F b ω hF J poly N left right hcontrol
  apply F.symbolSlowBound_of_gradedPolynomial b ω hF v T _
  rw [F.realGradedSymbolPolynomialHom_homogeneousPullback_of_chart b ω hF
    (fullTaggedVariableWeight (X := X) J) v β hβ left
    (normalizedRealPolynomialChart (fun x => (N x : ℝ)) (fullTaggedMajorTopCoordinates J poly)) E hchart]
  exact CoefficientBound.realChartSubstitute
    ((F.associatedGradedBasis b ω hF).baseChange ℝ) T hT
    (fun i => MvPolynomial.aeval β
      (normalizedRealPolynomialChart (fun x => (N x : ℝ)) (fullTaggedMajorTopCoordinates J poly) i))
    hbound (Real.exp_pos budget).le hB hdegree hmass

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawPhysicalAmbientHaarComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem nativeFiniteExpansion_mean_comparison {Ω T : Type*} [Fintype T]
    (s : Finset Ω) (hs : s.Nonempty) (w H : Ω → ℂ) (f : T → Ω → ℂ)
    (c ref : T → ℂ) {δ ε M : ℝ} (hε : 0 ≤ ε)
    (hw : ∀ x ∈ s, ‖w x‖ ≤ 1)
    (happ : ∀ x ∈ s, ‖H x - ∑ i, c i * f i x‖ ≤ δ)
    (hcomp : ∀ i, ‖(𝔼 x ∈ s, w x * f i x) - ref i‖ ≤ ε)
    (hmass : ∑ i, ‖c i‖ ≤ M) :
    ‖(𝔼 x ∈ s, w x * H x) - ∑ i, c i * ref i‖ ≤ δ + M * ε := by
  have hexpand (x : Ω) : w x * (∑ i, c i * f i x) =
      ∑ i, c i * (w x * f i x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have happmean : ‖(𝔼 x ∈ s, w x * H x) -
      (𝔼 x ∈ s, ∑ i, c i * (w x * f i x))‖ ≤ δ := by
    rw [← Finset.expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le hs
    intro x hx
    rw [← hexpand, ← mul_sub, norm_mul]
    exact (mul_le_mul_of_nonneg_right (hw x hx) (norm_nonneg _)).trans
      (by simpa only [one_mul] using happ x hx)
  have hsum : ‖(∑ i, c i * (𝔼 x ∈ s, w x * f i x)) -
      ∑ i, c i * ref i‖ ≤ M * ε := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, ‖c i * (𝔼 x ∈ s, w x * f i x) - c i * ref i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c i‖ * ε := by
        apply Finset.sum_le_sum
        intro i _
        rw [← mul_sub, norm_mul]
        exact mul_le_mul_of_nonneg_left (hcomp i) (norm_nonneg _)
      _ = (∑ i, ‖c i‖) * ε := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hmass hε
  have hlinear : (𝔼 x ∈ s, ∑ i, c i * (w x * f i x)) =
      ∑ i, c i * (𝔼 x ∈ s, w x * f i x) := by
    rw [Finset.expect_sum_comm]
    simp only [Finset.mul_expect]
  rw [hlinear] at happmean
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add happmean hsum)

 theorem exists_nativeForecast_ambient_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X : Type} [Fintype X] [DecidableEq X]
      {J : Fin m → Type} [∀ j, Fintype (J j)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
      [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
      (∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) →
      (∀ j α, coefficients (poly j) α ∈ U j) →
      ∀ {pw cw pv cv : ℝ} {Lw Lv : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
      {T : Type} [Fintype T]
      (V : T → NormalizedPolynomialTwist X (Σ j, J j) pv cv Lv)
      (c : T → ℂ) (H : (X → ℤ) → ℂ)
      {P E Rrank δ M : ℝ}, 0 ≤ P → 0 ≤ E →
      (Fintype.card X : ℝ) ≤ P → (Fintype.card (Σ j, J j) : ℝ) ≤ P →
      ((Lw * max 1 (Real.toNNReal cv) + Lv * max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤ Real.exp P →
      (∀ i, ((W.cover * (V i).cover : ℕ) : ℝ) ≤ Real.exp P) →
      (∀ i, ((W.modulus * (V i).modulus : ℕ) : ℝ) ≤ Real.exp P) →
      (∑ i, ‖c i‖) ≤ M → ∀ (N : X → ℕ),
      (∀ i, Real.exp ((max P E + A) ^ A) ≤ (N i : ℝ)) →
      Real.exp ((max P E + A) ^ A) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      (∀ x ∈ integerBox N, ‖H x - ∑ i, c i * (V i).eval N poly x‖ ≤ δ) →
      ‖(𝔼 x ∈ integerBox N, W.eval N poly x * H x) -
        ∑ i, c i * (𝔼 x ∈ integerBox N,
          (W.productUniform (V i)).frozenSingleSiteHaarReference U ν
            (fun a => (x a : ZMod (W.productUniform (V i)).modulus))
            (fun a => (x a : ℝ) / N a))‖ ≤ δ + M * Real.exp (-E) := by
  obtain ⟨A, hA, hcomp⟩ := exists_normalizedTwist_uniform_ambient_haar_budget m
  refine ⟨A, hA, ?_⟩
  intro X _ _ J _ U ν _ _ poly hp hm pw cw pv cv Lw Lv W T _ V c H
    P E Rrank δ M hP hE hX hdim hLip hcover hmod hmass N hlarge hRrank hrank happ
  have hN (x : X) : 0 < N x := by
    exact_mod_cast (Real.exp_pos _).trans_le (hlarge x)
  let : ∀ x, NeZero (N x) := fun x => ⟨(hN x).ne'⟩
  let F := fun i => W.productUniform (V i)
  let ref := fun i => 𝔼 x ∈ integerBox N, (F i).frozenSingleSiteHaarReference U ν
    (fun a => (x a : ZMod (F i).modulus)) (fun a => (x a : ℝ) / N a)
  have hone (i : T) : ‖(𝔼 x ∈ integerBox N, (F i).eval N poly x) - ref i‖ ≤ Real.exp (-E) := by
    exact hcomp U ν poly hp hm (F i) hP hE hX hdim hLip (hcover i) (hmod i)
      N hlarge hRrank hrank
  apply nativeFiniteExpansion_mean_comparison (integerBox N) (integerBox_nonempty N)
    (fun x => W.eval N poly x) H (fun i x => (V i).eval N poly x) c ref
    (Real.exp_pos _).le (fun x _ => W.norm_eval_le N poly x) happ _ hmass
  intro i
  simpa only [F, NormalizedPolynomialTwist.productUniform_eval] using hone i

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]


variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]

include hcompact

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} {X : Type} [Fintype G] [Fintype X] [DecidableEq X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]


variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]

noncomputable def nativeForecastAmbientExponent (m : ℕ) : ℕ :=
  Classical.choose (exists_nativeForecast_ambient_comparison m)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]


variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]

include hcompact

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} {X : Type} [Fintype G] [Fintype X] [DecidableEq X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]


variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativePairAffineCellStepDrop
namespace OAI

universe u

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial
open scoped TensorProduct BigOperators

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e)
    {σ τ ι : Type*}

theorem pairOrbit_substitute_log {w : σ → ℕ} {v : τ → ℕ}
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w)
    (f : σ → MvPolynomial τ ℚ) (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) :
    (pairOrbit D E
      (D.filtration.realification.polynomialOrbitSubstitute f hf p)
      (E.filtration.realification.polynomialOrbitSubstitute f hf q)).log =
      VectorPolynomial.substitute f (pairOrbit D E p q).log := by
  simp only [pairOrbit, NilpotentLieFiltration.piRealOrbit,
    NilpotentLieFiltration.PolynomialOrbit.log, NilpotentLieFiltration.polynomialOrbitOfLog, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases i <;> exact VectorPolynomial.map_substitute f _ _

theorem pairOrbitSymbol_scalarAffine_substitute
    (p : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (q : E.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (r : ℚ) (shift : σ → ℚ) :
    pairOrbitSymbol D E
      (D.filtration.realification.polynomialOrbitSubstitute
        (scalarAffinePolynomial r shift) (scalarAffinePolynomial_support r shift) p)
      (E.filtration.realification.polynomialOrbitSubstitute
        (scalarAffinePolynomial r shift) (scalarAffinePolynomial_support r shift) q) b ω hF =
      (pi (pairModels D E)).filtration.realPolynomialSymbolDilationHom (fun _ => 1) r
        (pairOrbitSymbol D E p q b ω hF) := by
  apply NilpotentLieBCHGroup.ext
  change (pi (pairModels D E)).filtration.realSymbolOfPolynomial b ω hF (fun _ => 1)
      (pairOrbit D E _ _).log =
    (pi (pairModels D E)).filtration.realPolynomialSymbolDilation (fun _ => 1) r
      ((pi (pairModels D E)).filtration.realSymbolOfPolynomial b ω hF (fun _ => 1)
        (pairOrbit D E p q).log)
  rw [pairOrbit_substitute_log, VectorPolynomial.substitute_scalarAffinePolynomial]
  apply NilpotentLieFiltration.realSymbolOfPolynomial_affine
  · exact fun _ => Nat.zero_lt_one
  · exact (pairOrbit D E p q).adapted

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]

theorem pairOrbitSymbol_scalarAffinePullback
    (V : D.Niltest (fun _ : σ => 1)) (W : E.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (r : ℚ) (shift : σ → ℚ) :
    pairOrbitSymbol D E (V.scalarAffinePullback r shift).orbit
      (W.scalarAffinePullback r shift).orbit b ω hF =
      (pi (pairModels D E)).filtration.realPolynomialSymbolDilationHom (fun _ => 1) r
        (pairOrbitSymbol D E V.orbit W.orbit b ω hF) :=
  pairOrbitSymbol_scalarAffine_substitute D E V.orbit W.orbit b ω hF r shift

theorem pairOrbitSymbol_scalarAffinePullback_inverse_stride
    (V : D.Niltest (fun _ : σ => 1)) (W : E.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (Q : ℕ) (hQ : 0 < Q) (shift : σ → ℚ) :
    (pi (pairModels D E)).filtration.realPolynomialSymbolDilationHom (fun _ => 1) ((Q : ℚ)⁻¹)
      (pairOrbitSymbol D E (V.scalarAffinePullback Q shift).orbit
        (W.scalarAffinePullback Q shift).orbit b ω hF) =
      pairOrbitSymbol D E V.orbit W.orbit b ω hF := by
  rw [pairOrbitSymbol_scalarAffinePullback]
  apply NilpotentLieBCHGroup.ext
  simp only [NilpotentLieFiltration.realPolynomialSymbolDilationHom_coord,
    ← NilpotentLieFiltration.realPolynomialSymbolDilation_mul,
    inv_mul_cancel₀ (show (Q : ℚ) ≠ 0 by exact_mod_cast hQ.ne'),
    NilpotentLieFiltration.realPolynomialSymbolDilation_one]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem ControlledSymbolFactorizationAtFast.dilate_ratio
    {η : L →ₗ[ℚ] ℚ} {S T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q r : ℝ}
    {U : LieSubalgebra ℚ F.AssociatedGraded}
    (h : F.ControlledSymbolFactorizationAtFast b ω hF η S X p U)
    (a : ℤ) (d : ℕ) (ha : a ≠ 0) (hd : 0 < d)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hdr : (d : ℝ) ≤ Real.exp r)
    (hphysical : ∀ i, Real.exp (-q) * (|(((a : ℚ) / d : ℚ) : ℝ)| * T i) ≤ S i) :
    F.ControlledSymbolFactorizationAtFast b ω hF η T
      (F.realPolynomialSymbolDilationHom (fun _ => 1) ((a : ℚ) / d) X)
      (p + (s : ℝ) * (q + r)) U := by
  obtain ⟨m, E, P, R, v, hm, hmp, hprod, hE, hR, hv, hgraded, hh, hzero, hP⟩ := h
  have hf : F.SymbolFactorizationIn b ω hF S X p m U :=
    ⟨E, P, R, hprod, hE, hR, hP⟩
  have hcost : p + (s : ℝ) * q ≤ p + (s : ℝ) * (q + r) := by
    have := mul_nonneg (Nat.cast_nonneg s : (0 : ℝ) ≤ s) hr
    nlinarith
  have hp : p ≤ p + (s : ℝ) * (q + r) := le_add_of_nonneg_right (by positivity)
  obtain ⟨E', P', R', hprod', hE', hR', hP'⟩ :=
    (SymbolFactorizationIn.dilate_ratio F b ω hF hf a d ha hd hS hT hq hphysical).mono
      F b ω hF hcost hT
  refine ⟨m * d ^ s, E', P', R', v, Nat.mul_pos hm (pow_pos hd _), ?_, hprod',
    hE', hR', hv, hgraded, (fun i j => (hh i j).trans hp), hzero, hP'⟩
  calc
    ((m * d ^ s : ℕ) : ℝ) = (m : ℝ) * (d : ℝ) ^ s := by push_cast; rfl
    _ ≤ Real.exp p * (Real.exp r) ^ s :=
      mul_le_mul hmp (pow_le_pow_left₀ (Nat.cast_nonneg d) hdr s)
        (by positivity) (Real.exp_pos p).le
    _ = Real.exp (p + (s : ℝ) * r) := by rw [← Real.exp_nat_mul, Real.exp_add]
    _ ≤ Real.exp (p + (s : ℝ) * (q + r)) := by
      apply Real.exp_le_exp.mpr
      have := mul_nonneg (Nat.cast_nonneg s : (0 : ℝ) ≤ s) hq
      nlinarith

theorem ControlledSymbolFactorization.dilate_ratio
    {η : L →ₗ[ℚ] ℚ} {S T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q r : ℝ}
    (h : F.ControlledSymbolFactorization b ω hF η S X p)
    (a : ℤ) (d : ℕ) (ha : a ≠ 0) (hd : 0 < d)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hdr : (d : ℝ) ≤ Real.exp r)
    (hphysical : ∀ i, Real.exp (-q) * (|(((a : ℚ) / d : ℚ) : ℝ)| * T i) ≤ S i) :
    F.ControlledSymbolFactorization b ω hF η T
      (F.realPolynomialSymbolDilationHom (fun _ => 1) ((a : ℚ) / d) X)
      (p + (s : ℝ) * (q + r)) := by
  obtain ⟨U, hU⟩ := h.exists_fastWitness F b ω hF
  obtain ⟨m, E, P, R, v, hdata⟩ :=
    hU.dilate_ratio F b ω hF a d ha hd hS hT hq hr hdr hphysical
  exact ⟨m, E, P, R, U, v, hdata⟩

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_native_pair_affine_cell_step_drop (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ]
      {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (V : D.Niltest (fun _ : σ => 1)) (W : E.Niltest (fun _ : σ => 1))
      {p q r : ℝ} (_hp : 2 ≤ p) (_hq : 0 ≤ q) (_hr : 0 ≤ r)
      (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p)
      (Q : ℕ) (_hQ : 0 < Q) (_hQr : (Q : ℝ) ≤ Real.exp r) (shift : σ → ℤ)
      (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ)
      (_hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
      (_hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
      (_hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        V.observable (z • x) = CircleFourier.character
          ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x)
      (_hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
        W.observable (z • x) = CircleFourier.character
          ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x)
      (origin : σ → ℤ) (lengths : σ → ℕ) (H : σ → ℝ)
      (_hlen : ∀ i, 0 < lengths i) (_hH : ∀ i, 0 < H i)
      (_hσ : (Fintype.card σ : ℝ) ≤ p)
      (_hlarge : ∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ))
      (_hphysical : ∀ i, Real.exp (-q) * (H i / (Q : ℝ)) ≤ lengths i)
      (_hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        V.eval (fun i => (Q : ℤ) * x i + shift i) *
          W.eval (fun i => (Q : ℤ) * x i + shift i)‖),
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra L M))) ℚ (PairAlgebra L M))
        (ω : Fin (finrank ℚ (PairAlgebra L M)) → ℕ)
        (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (b '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        (pi (pairModels D E)).filtration.ControlledSymbolFactorization b ω hF
          (pairFrequency η θ) H (pairOrbitSymbol D E V.orbit W.orbit b ω hF)
          ((p + C) ^ C + (s : ℝ) * (q + r)) := by
  obtain ⟨C, hC, hstep⟩ := exists_native_pair_positive_step_drop s hs
  refine ⟨C, hC, ?_⟩
  intro σ _ _ L M _ _ _ _ d e _ _ _ _ _ _ _ _ D E V W p q r hp hq hr hV hW
    Q hQ hQr shift η θ hηheight hθheight hη hθ origin lengths H hlen hH hσ hlarge hphysical hbias
  let V' := V.scalarAffinePullback (Q : ℚ) (fun i => (shift i : ℚ))
  let W' := W.scalarAffinePullback (Q : ℚ) (fun i => (shift i : ℚ))
  have hV' : V'.ComplexityLE p := hV
  have hW' : W'.ComplexityLE p := hW
  obtain ⟨b, ω, hF, hb, hfactor⟩ := hstep D E V' W' hp hV' hW'
  have hevalV (x : σ → ℤ) : V'.eval x =
      V.eval (fun i => (Q : ℤ) * x i + shift i) := by
    exact_mod_cast V.scalarAffinePullback_eval_integer (Q : ℤ) shift x
  have hevalW (x : σ → ℤ) : W'.eval x =
      W.eval (fun i => (Q : ℤ) * x i + shift i) := by
    exact_mod_cast W.scalarAffinePullback_eval_integer (Q : ℤ) shift x
  have hc := hfactor η θ hηheight hθheight hη hθ origin lengths hlen hσ hlarge
    (by simpa only [hevalV, hevalW] using hbias)
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hratio (i : σ) :
      Real.exp (-q) * (|(((1 : ℚ) / Q : ℚ) : ℝ)| * H i) ≤ (lengths i : ℝ) := by
    convert hphysical i using 1
    push_cast
    rw [abs_div, abs_one, abs_of_pos hQreal]
    ring
  have hf := hc.dilate_ratio (pi (pairModels D E)).filtration b ω hF 1 Q
    (by norm_num) hQ (fun i => by exact_mod_cast hlen i) hH hq hr hQr hratio
  refine ⟨b, ω, hF, hb, ?_⟩

  simpa only [Int.cast_one, one_div, V', W',
    pairOrbitSymbol_scalarAffinePullback_inverse_stride D E V W b ω hF Q hQ
      (fun i => (shift i : ℚ))] using hf

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSymbolBasisIndependence
namespace OAI

universe u

section

namespace Erdos3.NilpotentLieFiltration
open Module
open scoped TensorProduct

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)
  (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (c : Basis κ ℚ L) (ν : κ → ℕ)
  (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
  (w : σ → ℕ)

theorem realPolynomialSymbolMap_basis_independent
    (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolMap b ω hF w p = F.realPolynomialSymbolMap c ν hC w p := by
  obtain ⟨x, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF p
  change F.realSymbolOfPolynomial b ω hF w (F.realAdaptedPolynomialMap w x) =
    F.realSymbolOfPolynomial c ν hC w (F.realAdaptedPolynomialMap w x)
  rw [F.realSymbolOfPolynomial_realAdaptedPolynomialMap,
    F.realSymbolOfPolynomial_realAdaptedPolynomialMap]

theorem realPolynomialSymbolHom_basis_independent
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realPolynomialSymbolHom b ω hF w g = F.realPolynomialSymbolHom c ν hC w g := by
  apply NilpotentLieBCHGroup.ext
  exact F.realPolynomialSymbolMap_basis_independent b ω hF c ν hC w g.coord

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold
open Module

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d e : ℕ} {σ ι κ : Type*} {w : σ → ℕ}

theorem pairOrbitSymbol_basis_independent
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (c : Basis κ ℚ (PairAlgebra L M)) (ν : κ → ℕ)
    (hC : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (c '' {i | k ≤ ν i})) :
    pairOrbitSymbol D E p q b ω hF = pairOrbitSymbol D E p q c ν hC :=
  (pi (pairModels D E)).filtration.realPolynomialSymbolHom_basis_independent
    b ω hF c ν hC w _

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedFullChartNativeDetection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

attribute [local instance] NativeSampleModelFamily.lie NativeSampleModelFamily.algebra NativeSampleModelFamily.topology NativeSampleModelFamily.topologicalAdd NativeSampleModelFamily.continuousSMul NativeSampleModelFamily.hausdorff

theorem exists_full_chart_major_correlation_witness_of_native_detections
    {m k t : ℕ} {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (htk : t < k)
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
    (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J k)))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
    (hβ : ∀ u ∈ integerBox N, ∀ i,
      |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) -
        c i - (β u i : ℝ)| ≤ 1 / 2)
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hperiod : periodCap ≤ Real.exp pMajor) (hcover : coverCap ≤ Real.exp pMajor)
    (hLip : (Lip : ℝ) ≤ Real.exp pMajor) (hΨ : (Ψ.lip : ℝ) ≤ Real.exp pMajor)
    (hN : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hdetected : ∀ j,
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
        (g : integerBox N → ℂ),
        Nonempty (NativeSampleModel (fun _ : X => 1) t pNative
          (fun u : integerBox N => u.val) g) ∧
        Real.exp (-pNative) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
            (fun u => majorPhaseSample J k poly Ψ c
              (coordinate (basis.coord j).toAddMonoidHom
                (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
                  (fullTaggedVariableWeight (X := X) J) fast k
                    (left⁻¹ * Z * right⁻¹).coord))) β (fun _ => 1) u.val)
            (fun u => star (W.eval N poly u.val) * g u)‖) :
    Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
      Z left right N poly U pMajor Rrank C) := by
  obtain ⟨W, g, common, hcorr⟩ := exists_native_major_correlation_family_of_detections
    J N hbox poly Ψ c
    (fun j => coordinate (basis.coord j).toAddMonoidHom
      (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
        (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord)))
    β pNative hpNative hη hdetected
  refine ⟨{
    L := common.L
    step := t
    dim := common.dim
    model := common.model
    lower := htk
    correlation := ?_ }⟩
  unfold FullChartMajorCorrelation
  refine ⟨periodCap, coverCap, Lip, W, (fun j => (common.test j).conjugate),
    Ψ, c, β, hpoly, hcoeff, hβ, ?_, ?_, ?_, hdim, ?_, ?_, hLip, hΨ,
    hN, hRrank, hrank, ?_⟩
  · linarith
  · intro j
    exact ((common.test j).conjugate_complexityLE pMajor).mpr
      ((common.complexity j).mono hproduct)
  · intro j
    exact_mod_cast common.norm j
  · exact fun j => (W j).modulus_bound.trans hperiod
  · exact fun j => (W j).cover_bound.trans hcover
  · intro j
    exact (Real.exp_le_exp.mpr (neg_le_neg hNativeMajor)).trans (hcorr j)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct NNReal

def SampledSliceNativeDetection
    {m : ℕ} {X Ω T : Type} [Fintype X] [DecidableEq X] [Fintype Ω] [Fintype T]
    {Tests : Ω → Type} (J : Fin m → Type) [∀ j, Fintype (J j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (pathLaw : FiniteProbabilityWeights Ω) (physical : Ω → T → X → ℤ)
    (slices : ∀ z, Tests z → Finset T) (weight : ∀ z, Tests z → T → ℂ)
    (degree : ℕ) (pNative α : ℝ) : Prop :=
  ∀ signal : (X → ℤ) → ℂ,
    (∀ u, ‖signal u‖ ≤ 1) →
    (∀ u, u ∉ integerBox N → signal u = 0) →
    α ≤ sampledSliceSeminorm pathLaw physical slices weight signal →
    ∃ (W : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp pNative) (Real.exp pNative) ⟨Real.exp pNative, Real.exp_nonneg _⟩)
      (g : integerBox N → ℂ),
      Nonempty (NativeSampleModel (fun _ : X => 1) degree pNative
        (fun u : integerBox N => u.val) g) ∧
      Real.exp (-pNative) ≤
        ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
          (fun u => signal u.val) (fun u => star (W.eval N poly u.val) * g u)‖

noncomputable def majorPhasePlateauBoxSignal
    {m : ℕ} {X : Type} [Fintype X] [DecidableEq X] (J : Fin m → Type) [∀ j, Fintype (J j)]
    (k : ℕ) (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ) :
    (X → ℤ) → ℂ :=
  (integerBox N : Set (X → ℤ)).indicator (majorPhasePlateauSignal J k poly c P)

theorem majorPhasePlateauBoxSignal_inside
    {m : ℕ} {X : Type} [Fintype X] [DecidableEq X] (J : Fin m → Type) [∀ j, Fintype (J j)]
    (k : ℕ) (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ)
    (u : X → ℤ) (hu : u ∈ integerBox N) :
    majorPhasePlateauBoxSignal J k N poly c P u = majorPhasePlateauSignal J k poly c P u :=
  Set.indicator_of_mem hu _

theorem majorPhasePlateauBoxSignal_outside
    {m : ℕ} {X : Type} [Fintype X] [DecidableEq X] (J : Fin m → Type) [∀ j, Fintype (J j)]
    (k : ℕ) (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ)
    (u : X → ℤ) (hu : u ∉ integerBox N) :
    majorPhasePlateauBoxSignal J k N poly c P u = 0 :=
  Set.indicator_of_notMem hu _

theorem majorPhasePlateauBoxSignal_norm_le_one
    {m : ℕ} {X : Type} [Fintype X] [DecidableEq X] (J : Fin m → Type) [∀ j, Fintype (J j)]
    (k : ℕ) (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ)
    (u : X → ℤ) : ‖majorPhasePlateauBoxSignal J k N poly c P u‖ ≤ 1 := by
  classical
  by_cases hu : u ∈ integerBox N
  · rw [majorPhasePlateauBoxSignal_inside J k N poly c P u hu]
    exact majorPhasePlateauSignal_norm_le_one J k poly c P u
  · rw [majorPhasePlateauBoxSignal_outside J k N poly c P u hu, norm_zero]
    exact zero_le_one

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal

theorem exists_full_chart_major_correlation_witness_of_prepared_detection
    {m k t : ℕ} {X L ι η Ω T : Type}
    [Fintype X] [DecidableEq X] [Fintype η] [Fintype Ω] [Fintype T]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (htk : t < k)
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hN : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    {Tests : Ω → Type} (pathLaw : FiniteProbabilityWeights Ω)
    (physical : Ω → T → X → ℤ) (slices : ∀ z, Tests z → Finset T)
    (weight : ∀ z, Tests z → T → ℂ) (α : ℝ)
    (hdirect : SampledSliceNativeDetection J N hbox poly pathLaw physical slices weight t pNative α)
    (hlarge : ∀ j, α ≤ sampledSliceSeminorm pathLaw physical slices weight
      (majorPhasePlateauBoxSignal J k N poly c
        (coordinate (basis.coord j).toAddMonoidHom
          (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
            (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord))))) :
    Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
      Z left right N poly U pMajor Rrank C) := by
  have hNative0 : 0 ≤ pNative := by linarith
  have hseven : 7 ≤ pMajor := by
    have h := (productNiltestBudget_geometry hNative0).trans hproduct
    nlinarith
  have hkernel : ((majorPhasePlateauKernel (Fintype.card (LowTaggedIndex J k))).lip : ℝ) ≤
      Real.exp pMajor := by
    change (8 : ℝ) ≤ Real.exp pMajor
    linarith [Real.add_one_le_exp pMajor]
  have hexp := Real.exp_le_exp.mpr hNativeMajor
  apply exists_full_chart_major_correlation_witness_of_native_detections
    (Lip := ⟨Real.exp pNative, Real.exp_nonneg _⟩)
    F b ω hF J fast basis Z left right htk N hbox poly hpoly U hcoeff
    (majorPhasePlateauKernel _) c (majorPhaseNearestLift J k poly c)
    (fun u _ i => majorPhaseNearestLift_close J k poly c u i)
    pNative pMajor Rrank C hpNative hη hNativeMajor hproduct hdim
    hexp hexp hexp hkernel hN hRrank hrank
  intro j
  let P := coordinate (basis.coord j).toAddMonoidHom
    (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
      (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord))
  obtain ⟨W, g, hmodel, hcorr⟩ := hdirect (majorPhasePlateauBoxSignal J k N poly c P)
    (majorPhasePlateauBoxSignal_norm_le_one J k N poly c P)
    (majorPhasePlateauBoxSignal_outside J k N poly c P) (hlarge j)
  refine ⟨W, g, hmodel, ?_⟩
  have heq : (fun u : integerBox N => majorPhasePlateauBoxSignal J k N poly c P u.val) =
      fun u : integerBox N => majorPhasePlateauSignal J k poly c P u.val := by
    funext u
    exact majorPhasePlateauBoxSignal_inside J k N poly c P u.val u.property
  rw [heq] at hcorr
  exact hcorr

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_full_chart_major_correlation_witness_of_productive_local_tests
    {m k t : ℕ} {X L ι η Ω I : Type}
    [Fintype X] [DecidableEq X] [Fintype η] [Fintype Ω] [Fintype I] [DecidableEq I]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (htk : t < k)
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hN : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (pathLaw : FiniteProbabilityWeights Ω) (good : η → Finset Ω)
    (localN : I → ℕ) (hlocalN : ∀ i, 0 < localN i)
    (cost : ℝ) (hcost : 0 ≤ cost)
    (physical : Ω → (I → ℤ) → X → ℤ)
    (hphysical : ∀ j z, z ∈ good j → ∀ x,
      x ∈ integerBox localN → physical z x ∈ integerBox N)
    (α : ℝ) (hmass : ∀ j, α ≤ (9 / 10 : ℝ) * pathLaw.mass (good j))
    (hdirect : ∀ chosen : Ω → Option η →
      LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t) localN cost
        (OrdinaryPolynomialPhase.budget t),
      SampledSliceNativeDetection J N hbox poly pathLaw
        (fun z (x : integerBox localN) => physical z x.val)
        (fun z a => (chosen z a).slice.subtypeSites)
        (fun z a (x : integerBox localN) => (chosen z a).weight x.val) t pNative α)
    (hlocal : ∀ j z, z ∈ good j →
      ∃ A : LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t) localN cost
        (OrdinaryPolynomialPhase.budget t),
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.slice.integerPoints,
          majorPhasePlateauSignal J k poly c
            (coordinate (basis.coord j).toAddMonoidHom
              (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
                (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord)))
            (physical z x) * A.weight x‖) :
    Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
      Z left right N poly U pMajor Rrank C) := by
  let phase := fun j => coordinate (basis.coord j).toAddMonoidHom
    (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
      (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord))
  let signal := fun j => majorPhasePlateauBoxSignal J k N poly c (phase j)
  have hlocalBox : ∀ j z, z ∈ good j →
      ∃ A : LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t) localN cost
        (OrdinaryPolynomialPhase.budget t),
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.slice.integerPoints,
          signal j (physical z x) * A.weight x‖ := by
    intro j z hz
    obtain ⟨A, hA⟩ := hlocal j z hz
    refine ⟨A, ?_⟩
    have heq : (𝔼 x ∈ A.slice.integerPoints, signal j (physical z x) * A.weight x) =
        𝔼 x ∈ A.slice.integerPoints,
          majorPhasePlateauSignal J k poly c (phase j) (physical z x) * A.weight x := by
      apply Finset.expect_congr rfl
      intro x hx
      rw [show signal j (physical z x) =
          majorPhasePlateauSignal J k poly c (phase j) (physical z x) from
        majorPhasePlateauBoxSignal_inside J k N poly c (phase j) (physical z x)
          (hphysical j z hz x (A.slice.integerPoints_subset_integerBox hx))]
    rw [heq]
    exact hA
  obtain ⟨chosen, _, hlarge⟩ := exists_productive_localMajorSlice_coordinate_family
    (OrdinaryPolynomialPhase.nilmanifold t) pathLaw good localN hlocalN cost
    (OrdinaryPolynomialPhase.budget t) (9 / 10)
    (OrdinaryPolynomialPhase.zeroLocalMajorSlice localN hlocalN cost hcost)
    physical signal hlocalBox
  apply exists_full_chart_major_correlation_witness_of_prepared_detection
    F b ω hF J fast basis Z left right htk N hbox poly hpoly U hcoeff c
    pNative pMajor Rrank C hpNative hη hNativeMajor hproduct hdim hN hRrank hrank
    pathLaw (fun z (x : integerBox localN) => physical z x.val)
    (fun z a => (chosen z a).slice.subtypeSites)
    (fun z a (x : integerBox localN) => (chosen z a).weight x.val)
    α (hdirect chosen)
  intro j
  exact (hmass j).trans (hlarge j)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators Classical

theorem exists_full_chart_major_correlation_witness_of_frozen_productive_local_tests
    {m k t : ℕ} {X L ι η Ω I : Type}
    [Fintype X] [DecidableEq X] [Fintype η] [Fintype Ω] [Fintype I] [DecidableEq I]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (htk : t < k)
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hN : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (pathLaw : FiniteProbabilityWeights Ω) (good : η → Finset Ω)
    (localN : I → ℕ) (hlocalN : ∀ i, 0 < localN i)
    (keep : I → Prop) (cost Bshort : ℝ) (hcost : 0 ≤ cost)
    (hBshort : 1 ≤ Bshort) (hshort : ∀ i, ¬keep i → (localN i : ℝ) ≤ Bshort)
    (physical : Ω → (I → ℤ) → X → ℤ)
    (hphysical : ∀ j z, z ∈ good j → ∀ x,
      x ∈ integerBox localN → physical z x ∈ integerBox N)
    (α : ℝ) (hmass : ∀ j, α ≤ (9 / 10 : ℝ) * pathLaw.mass (good j))
    (hdirect : ∀ chosen : Ω → Option η →
      LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t) localN (max cost (Real.log Bshort))
        (OrdinaryPolynomialPhase.budget t),
      SampledSliceNativeDetection J N hbox poly pathLaw
        (fun z (x : integerBox localN) => physical z x.val)
        (fun z a => (chosen z a).slice.subtypeSites)
        (fun z a (x : integerBox localN) => (chosen z a).weight x.val) t pNative α)
    (hlocal : ∀ j z, z ∈ good j →
      ∃ fixed : {i // ¬keep i} → ℤ,
        (∀ i, 0 ≤ fixed i ∧ fixed i < localN i.val) ∧
      ∃ A : LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t)
        (fun i : {i // keep i} => localN i.val) cost (OrdinaryPolynomialPhase.budget t),
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.slice.integerPoints,
          majorPhasePlateauSignal J k poly c
            (coordinate (basis.coord j).toAddMonoidHom
              (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
                (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord)))
            (physical z (finiteSplitPoint keep x fixed)) * A.weight x‖) :
    Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
      Z left right N poly U pMajor Rrank C) := by
  apply exists_full_chart_major_correlation_witness_of_productive_local_tests
    F b ω hF J fast basis Z left right htk N hbox poly hpoly U hcoeff c
    pNative pMajor Rrank C hpNative hη hNativeMajor hproduct hdim hN hRrank hrank
    pathLaw good localN hlocalN (max cost (Real.log Bshort))
    (hcost.trans (le_max_left _ _)) physical hphysical α hmass hdirect
  intro j z hz
  obtain ⟨fixed, hfixed, A, hA⟩ := hlocal j z hz
  let starts := frozenShortStarts keep fixed
  have hstarts := frozenShortStarts_inside keep fixed hfixed
  refine ⟨A.freezeShort keep starts hstarts hBshort hshort, ?_⟩
  rw [A.expect_freezeShort keep starts hstarts hBshort hshort
    (fun x => majorPhasePlateauSignal J k poly c
      (coordinate (basis.coord j).toAddMonoidHom
        (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
          (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord)))
      (physical z x))]
  simpa only [starts, frozenLongExtension_shortStarts keep fixed (fun i => (hfixed i).1)] using hA

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

section Consumer

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable (α τ : ℝ)
variable {P : ℝ}

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]

variable [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
  OrdinaryPolynomialPhase.weight s)]
variable [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
  OrdinaryPolynomialPhase.weight s)]
variable [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
  OrdinaryPolynomialPhase.weight s)]
variable [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
  OrdinaryPolynomialPhase.weight s)]

end Consumer
end Erdos3.VectorPolynomial

end

end OAI

end


