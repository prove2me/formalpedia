-- Prove2me | Definitions.Def_OAIE3v2B242
-- name    : OAIE3v2B242
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:59:30.443117+00:00
-- url     : https://prove2.me/theorems/68325ab4-44fa-4850-9755-578c0164820f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 247 of 311
-- statement:
--   Definitions bundle 247 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B301`, `OAIE3v2B220`, `OAIE3v2B224`, `OAIE3v2B226`, `OAIE3v2B227`, `OAIE3v2B228`, `OAIE3v2B230` of this split.
--
--   Modules: `Estimates/AllocatedExternalLocalGlobalMarkedCandidate.lean`, `Estimates/CoveredInducedCorrelationFamily.lean`, `Estimates/TranslationMajorCorrelationIdentity.lean`, `Geometry/AllocatedRecoveredNormalizedTopChart.lean`, `Geometry/FullChartHomogeneousCorrection.lean`, `Polynomial/BufferedSampledCurrentGradePhase.lean`, `Probability/AllocatedRecoveredChartMass.lean`, `Sampling/DetectedTranslationMajorSamplingContainment.lean`, `Sampling/PreparedActualForecastSetup.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B301
import Definitions.Def_OAIE3v2B220
import Definitions.Def_OAIE3v2B224
import Definitions.Def_OAIE3v2B226
import Definitions.Def_OAIE3v2B227
import Definitions.Def_OAIE3v2B228
import Definitions.Def_OAIE3v2B230

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredInducedCorrelationFamily
namespace OAI

section

namespace Erdos3.QuadraticMarked

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

noncomputable def localCharacter {t d : ℕ} (m : ℕ)
    (D : RationalFilteredNilmanifold (Algebra t) 2 d)
    (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ) (g : D.RealGroup) : ℂ :=
  CircleFourier.character ((realifyFunctional η ((evaluation t).baseChange ℝ
    (normalizedMarkedRetraction filtration generators weights marked weight_pos generator_mem t m D g).coord) : ℝ) :
      CircleFourier.Circle)

end Erdos3.QuadraticMarked

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.DetectedTranslationMajorSamplingContainment
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial
open scoped Matrix

universe u v z

theorem exists_detectedTranslation_samplingRank_le_base_span :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {B L : Type} {σ : Type u} {ι : Type v} {J : Type z}
    [Fintype B] [Fintype ι] [Fintype J] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (_hd : 1 ≤ d) {p : ℝ} (_hp : 0 ≤ p)
    (_hB : (Fintype.card B : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hJ : (Fintype.card J : ℝ) ≤ p)
    (_hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (W : LieSubalgebra ℚ
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (v : J → (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hvheight : ∀ j i, rationalLogHeight
      (((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hN).repr (v j) i) ≤ p)
    (E P Q X : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (_hprod : E * P * Q = X)
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
    (_hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : σ => 1) T (Real.exp p) E)
    (_hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra
        b ω hN (fun _ : σ => 1) W))
    (m : ℕ) (_hm : 0 < m) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : σ => 1) m Q)
    (h : ℕ) (R : ℝ) (retained : Submodule ℝ (B → ℝ))
    (_hrank : HasLayerSamplingRank h T R retained
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN X))
    (_hR : Real.exp ((p + C)^C) ≤ R),
    retained ≤ Submodule.span ℝ (Set.range (fun j i =>
      (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ))) := by
  obtain ⟨C, hC, hbudget⟩ := exists_samplingProjectedImage_complete_budget
  refine ⟨C, hC, ?_⟩
  intro B L σ ι J _ _ _ _ _ w d hw hwd _ M hM e D b ω hN hd p hp hB hι hJ
    hb W v hv hvheight E P Q X hprod T hT hE hP m hm hmp hQ h R retained hrank hR
  obtain ⟨hgrid, hrow, hcost⟩ := hbudget (Fintype.card J) (Fintype.card B) p hp hJ hB
  exact detectedTranslation_samplingRank_le_base_span w d hw hwd M hM D b ω hN
    hd hp hB hι hb W v hv hvheight E P Q X hprod T hT hE hP m hm hmp hQ
    h R retained hrank (hgrid.trans hR) (hrow.trans hR) (hcost.trans hR)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped Matrix

theorem exists_majorTranslation_samplingRank_le_real_base_image :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {B L : Type} {σ ι J : Type}
    [Fintype B] [Fintype ι] [Fintype J] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (_hd : 1 ≤ d) {p : ℝ} (_hp : 0 ≤ p)
    (_hB : (Fintype.card B : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hJ : (Fintype.card J : ℝ) ≤ p)
    (_hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (W : LieSubalgebra ℚ
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (v : J → (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hvheight : ∀ j i, rationalLogHeight
      (((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hN).repr (v j) i) ≤ p)
    (F : MvPolynomial (σ ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) d)
    (A : B → MvPolynomial σ ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (partner : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (E P Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (_hprod : E * P * Q = pairOrbitSymbol
      (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
      (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) partner b ω hN)
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
    (_hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : σ => 1) T (Real.exp p) E)
    (_hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra
        b ω hN (fun _ : σ => 1) W))
    (m : ℕ) (_hm : 0 < m) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : σ => 1) m Q)
    (h : ℕ) (R : ℝ) (retained : Submodule ℝ (B → ℝ))
    (_hrank : HasLayerSamplingRank h T R retained
      (ofCoordinates (R := ℝ) (Pi.basisFun ℝ B)
        (fun i => weightedHomogeneousComponent (fun _ : σ => 1) (w i) (A i))))
    (_hR : Real.exp ((p + C)^C) ≤ R),
    retained ≤
      (((W.map (weightedTranslationGradedProjection
        (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
        w d hw hwd (liePiEval (R := ℚ) true)
        (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D))).toSubmodule).baseChange ℝ).map
          (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) := by
  obtain ⟨C, hC, hcontain⟩ := exists_detectedTranslation_samplingRank_le_base_span
  refine ⟨C, hC, ?_⟩
  intro B L σ ι J _ _ _ _ _ w d hw hwd _ M hM e D b ω hN hd p hp hB hι hJ
    hb W v hv hvheight F hF A hA partner E P Q hprod T hT hE hP m hm hmp hQ
    h R retained hrank hR
  rw [← detectedTranslationBase_span_eq_real_image w d hw hwd M hM D W v hv]
  apply hcontain w d hw hwd M hM D b ω hN hd hp hB hι hJ hb W v hv hvheight
    E P Q _ hprod T hT hE hP m hm hmp hQ h R retained _ hR
  rw [detectedTranslationBasePolynomial_majorOrbitSymbol w d hw hwd M hM D b ω hN F hF A hA partner]
  exact hrank

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslationMajorCorrelationIdentity
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped Matrix

universe u v z

theorem exists_detectedTranslation_separated_base :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {B L : Type} {σ : Type u} {ι : Type v} {J : Type z}
    [Fintype B] [Fintype ι] [Fintype J] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (_hd : 1 ≤ d) {p : ℝ} (_hp : 0 ≤ p)
    (_hB : (Fintype.card B : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hJ : (Fintype.card J : ℝ) ≤ p)
    (_hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (W : LieSubalgebra ℚ
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (v : J → (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hvheight : ∀ j i, rationalLogHeight
      (((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hN).repr (v j) i) ≤ p)
    (E P Q X : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (_hprod : E * P * Q = X)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C)^C) ≤ T i)
    (_hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : σ => 1) T (Real.exp p) E)
    (_hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra
        b ω hN (fun _ : σ => 1) W))
    (m : ℕ) (_hm : 0 < m) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : σ => 1) m Q)
    (retained : Submodule ℝ (B → ℝ))
    (_hX : ∀ α, coefficients
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN X) α ∈ retained)
    (_hretained : retained ≤ Submodule.span ℝ (Set.range (fun j i =>
      (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ)))),
    (∀ α, coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN E) α ∈
      Submodule.span ℝ (Set.range (fun j i =>
        (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ)))) ∧
    (∀ α, coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN Q) α ∈
      Submodule.span ℝ (Set.range (fun j i =>
        (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ)))) ∧
    ∀ u : σ → ℝ,
      (detectedTranslationGroupEval w d hw hwd M hM D u E).base ∈
        Submodule.span ℝ (Set.range (fun j i =>
          (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ))) ∧
      (detectedTranslationGroupEval w d hw hwd M hM D u Q).base ∈
        Submodule.span ℝ (Set.range (fun j i =>
          (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ))) := by
  let budget : Polynomial ℕ := (Polynomial.X + 3)^5
  obtain ⟨C, hC, hsep⟩ := exists_vectorPolynomial_subspace_separation budget
  refine ⟨C, hC, ?_⟩
  intro B L σ ι J _ _ _ _ _ w d hw hwd _ M hM e D b ω hN hd p hp hB hι hJ
    hb W v hv hvheight E P Q X hprod T hT hE hP m hm hmp hQ retained hX hretained
  have hbudget : budget.eval₂ (Nat.castRingHom ℝ) p = (p + 3)^5 := by
    simp [budget, Polynomial.eval₂_pow]
  obtain ⟨hpbudget, hsmall, hceil⟩ := detectedTranslationSeparation_budget hp
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  let H : ℕ := ⌈Real.exp ((p + 2)^4)⌉₊
  let A : Matrix B J ℚ := fun i j => detectedTranslationBaseMap w d hw hwd M hM D (v j) i
  have hA : ∀ i j, RationalHeightLE (A i j) H := by
    intro i j
    exact rationalHeightLE_ceil_exp
      (detectedTranslationBaseFunctional_value_logHeight w d hw hwd M hM D
        b ω hN hp hι hb (v j) (hvheight j) i)
  obtain ⟨q, hq, hqbound, hgrid⟩ :=
    detectedTranslationBasePolynomial_exists_coefficient_grid w d hw hwd M hM D
      b ω hN hp hι hb hB m hm hmp Q hQ
  have hslow := detectedTranslationBasePolynomial_slow_coefficients w d hw hwd M hM D
    b ω hN hp hι hb T hTpos E hE
  have hqbudget : (q : ℝ) ≤ Real.exp (budget.eval₂ (Nat.castRingHom ℝ) p) := by
    rw [hbudget]
    exact hqbound.trans (Real.exp_le_exp.mpr hsmall)
  obtain ⟨hEco, hQco, hEeval, hQeval⟩ :=
    hsep A H q (one_le_ceil_exp _) hq hA p hp
      (by rw [hbudget]; exact hB.trans hpbudget)
      (by rw [hbudget]; exact hJ.trans hpbudget)
      (by rw [hbudget]; exact hceil) hqbudget T hT
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN X)
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN E)
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN P)
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN Q)
      (detectedTranslationBasePolynomial_factorization w d hw hwd M hM D b ω hN hd E P Q X hprod)
      (fun α => hretained (hX α))
      (detectedTranslationBasePolynomial_fast_coefficients_mem_span w d hw hwd M hM D b ω hN W v hv P hP)
      (detectedTranslationBasePolynomial_constant w d hw hwd M hM D b ω hN E)
      (detectedTranslationBasePolynomial_constant w d hw hwd M hM D b ω hN Q)
      (fun α i => (hslow α i).trans (by
        rw [hbudget]
        exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hsmall)
          (monomialScale_pos T hTpos α).le)) hgrid
  refine ⟨hEco, hQco, fun u => ?_⟩
  rw [detectedTranslationGroupEval_base w d hw hwd M hM D b ω hN,
    detectedTranslationGroupEval_base w d hw hwd M hM D b ω hN]
  have heval (Y : VectorPolynomial σ ℝ (B → ℝ)) : eval₂ u Y = eval u Y := by
    simpa using (eval₂_algebraMap (S := ℝ) u Y)
  rw [heval, heval]
  exact ⟨hEeval u, hQeval u⟩

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FullChartHomogeneousCorrection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X M : Type} [LieRing M] [LieAlgebra ℚ M]
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

theorem certifiedFullChartDetectedDecomposition_of_vector_detection
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast)
    (hsection : ∀ y, fast.mkQ (lift y) = y)
    (hK₀ : ∀ t ∈ K₀, ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ K₀)
    (hlower : ∀ t ∈ K₀, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF wt j t
        (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ)
    (hdetected : MajorPhaseVectorDetectedConclusion (L := M) J k Utag poly c N budget basis
      (lowTaggedVectorRestrict J k
        (F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord))) :
    CertifiedFullChartDetectedDecomposition F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget := by
  obtain ⟨detectedfast, gen, slow, rat, q, hgen, hgrade, hretain, _, hcoeff,
    hq, hqB, hgrid, _, _, hvalue⟩ := hdetected
  let K := fun i => majorPhaseDetectedRealBase J k (detectedfast i)
  have hquot := fullChart_grade_quotient_of_low_value F b ω hF J k fast
    Z left right K₀ poly N c K slow rat (by with_reducible exact hvalue)
  have hstep := F.restricted_symbol_major_grade_step b ω hF wt fast hfast lift hsection
    k Z left right K₀ (fullTaggedGradedBaseIntersection J k K₀ K)
    (fullTaggedGradedBaseIntersection_subset J k K₀ K)
    (fullTaggedGradedBaseIntersection_rat_dilation J k K₀ K hgrade hK₀)
    (realChartSubstitute chart (lowTaggedVectorExtend J k slow))
    (lowTaggedVectorExtend J k rat) hlower (by with_reducible exact hquot)
  have hcap := lowTaggedVectorExtend_coordinate_coefficient_bound J k
    (fun i => (basis.coord i).toAddMonoidHom) slow (Real.exp budget)
    (Real.exp_pos budget).le hcoeff
  have hden := lowTaggedVectorExtend_coefficients_grid J k
    (fun i => (basis.coord i).toAddMonoidHom) rat q hgrid
  obtain ⟨A, D, hA, hD, _, _, _, _, hnext⟩ := hstep
  have hAc : A = F.restrictedMajorCorrection b ω hF wt fast lift k
      (realChartSubstitute chart (lowTaggedVectorExtend J k slow)) := by
    apply NilpotentLieBCHGroup.ext
    dsimp only [restrictedMajorCorrection]
    with_reducible exact hA
  have hDc : D = F.restrictedMajorCorrection b ω hF wt fast lift k
      (lowTaggedVectorExtend J k rat) := by
    apply NilpotentLieBCHGroup.ext
    dsimp only [restrictedMajorCorrection]
    with_reducible exact hD
  rw [hAc, hDc] at hnext
  have hcertificate := majorPhase_rationalTaggedConstraintCertificate J k
    detectedfast gen K₀ budget hgen
  unfold CertifiedFullChartDetectedDecomposition
  refine ⟨lowTaggedVectorExtend J k slow, lowTaggedVectorExtend J k rat, q,
    fullTaggedGradedBaseIntersection J k K₀ K, hq, hqB,
    fullTaggedGradedBaseIntersection_subset J k K₀ K,
    fullTaggedGradedBaseIntersection_rat_dilation J k K₀ K hgrade hK₀,
    ?_, hcap, hden, ?_, ?_, hcertificate, ?_⟩
  · intro t ht hU
    refine ⟨ht, ?_⟩
    intro i
    change lowTaggedCoordinates J k (fun j a => t (Sum.inr ⟨j, a⟩)) ∈ K i
    apply (lowTaggedCoordinates_mem_iff J k (K i) (hgrade i) _).mpr
    intro j
    exact le_lowTaggedSubspaceFamily J k Utag (K i) (hretain i) j (hU j)
  · with_reducible exact hnext
  · exact ⟨detectedfast, slow, rat, rfl, rfl, rfl⟩
  · with_reducible exact hquot

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BufferedSampledCurrentGradePhase
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial

namespace NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realSymbolGradeQuotientPolynomial_lowTagged_aeval {m : ℕ} {X : Type}
    (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℝ)
    (U : Submodule ℚ F.AssociatedGraded)
    (ℓ : (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)) →ₗ[ℝ] ℝ)
    (x : F.RealPolynomialSymbol (fullTaggedVariableWeight (X := X) J)) :
    aeval β (coordinate ℓ.toAddMonoidHom
      (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J) U k x)) =
    aeval (β ∘ lowTaggedVariableEmbedding J k) (coordinate ℓ.toAddMonoidHom
      (lowTaggedVectorRestrict J k
        (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J) U k x))) := by
  let P := F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J) U k x
  have hP : DegreeLE (fullTaggedVariableWeight J) k P := by
    intro α hα
    exact F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF
      (fullTaggedVariableWeight J) U k x α (Nat.ne_of_gt hα)
  have hc := congrArg (coordinate ℓ.toAddMonoidHom) (lowTaggedVectorExtend_restrict J k P hP)
  rw [coordinate_lowTaggedVectorExtend] at hc
  change aeval β (coordinate ℓ.toAddMonoidHom P) = _
  rw [← hc, MvPolynomial.aeval_rename]

theorem exists_sampledCurrentGrade_lowTagged_lower_phase {m : ℕ} {X η : Type}
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (fullTaggedVariableWeight J i))
    (U : Submodule ℚ F.AssociatedGraded)
    (eQ : Basis η ℚ (F.AssociatedGraded ⧸ U)) (j : η)
    (n : ℕ) (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)) :
    let topβ := fun i => homogeneousComponent (fullTaggedVariableWeight J i) (β i)
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
      (fun _ : τ => 1) topβ
      (fun i => sampledTopPhase_coordinate_homogeneous (fullTaggedVariableWeight J i) (β i))
    ∃ lower : MvPolynomial τ ℝ, lower.totalDegree ≤ n ∧
      aeval (β ∘ lowTaggedVariableEmbedding J (n + 1))
        (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
          (lowTaggedVectorRestrict J (n + 1) (F.realSymbolGradeQuotientPolynomial b ω hF
            (fullTaggedVariableWeight J) U (n + 1) (left⁻¹ * Z * right⁻¹).coord))) =
      homogeneousComponent (n + 1)
        (F.scalarSymbolPolynomial b ω hF (fun _ : τ => 1) ((eQ.coord j).comp U.mkQ)
          ((pull left)⁻¹ * pull Z * (pull right)⁻¹)) + lower := by
  obtain ⟨lower, hdegree, hphase⟩ := F.exists_sampledCurrentGrade_lower_phase b ω hF
    (fullTaggedVariableWeight J) β hβ U (eQ.coord j) n Z left right
  refine ⟨lower, hdegree, ?_⟩
  rw [sampledCurrentGrade_sampledCurrentGrade_realifyFunctional_basis_coord,
    F.realSymbolGradeQuotientPolynomial_lowTagged_aeval b ω hF J (n + 1)] at hphase
  with_reducible exact hphase

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalLocalGlobalMarkedCandidate
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalCandidate
variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f nD nF : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (orbit : Dref.filtration.realification.PolynomialOrbit (fun _ : C.Variables => 1))

noncomputable def ofRefilteredIncludedMark
    (hincluded : ∀ u ∈ C.slice.integerPoints,
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
        (realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u orbit)) =
      realificationMap (hnil := Fref.filtration.lowerCentralSeries_eq_bot)
        (hM := Fmark.filtration.lowerCentralSeries_eq_bot)
        (Fmark.filtration.gradedRefiltrationSubalgebra
          (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).incl
        (Fref.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          (C.chartValues u) markedMiddle)) :
    AllocatedExternalLocalCandidate C Dref Fref.filtration
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle where
  orbit := orbit
  mark_on_slice u hu := by
    apply realificationMap_incl_injective (hnil := Fmark.filtration.lowerCentralSeries_eq_bot)
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    rw [← D.refiltered_mark_realification_commutes Fmark φ hφ W Dref Fref]
    exact hincluded u hu

noncomputable def ofNativeRefilteredMiddle
    (nativeMiddle : (D.filtration.realification.adaptedPolynomialFiltration
      (fun _ : C.Variables => 1)).Group)
    (nativeMark : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fun _ : C.Variables => 1)).Group)
    (hprojection : D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ => 1) nativeMiddle = nativeMark)
    (hinclusion : ∀ u ∈ C.slice.integerPoints,
      realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl
        (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u orbit) =
      D.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ)) nativeMiddle)
    (hmarked : ∀ u ∈ C.slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ)) nativeMark =
      realificationMap (hnil := Fref.filtration.lowerCentralSeries_eq_bot)
        (hM := Fmark.filtration.lowerCentralSeries_eq_bot)
        (Fmark.filtration.gradedRefiltrationSubalgebra
          (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).incl
        (Fref.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          (C.chartValues u) markedMiddle)) :
    AllocatedExternalLocalCandidate C Dref Fref.filtration
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle :=
  ofRefilteredIncludedMark C D Fmark φ hφ W Dref Fref markedMiddle orbit
    (fun point hpoint =>
      (congrArg (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ)
        (hinclusion point hpoint)).trans
      ((D.filtration.realPolynomialGroupMap_value Fmark.filtration φ hφ
        (fun _ => 1) nativeMiddle (fun index => (point index : ℝ))).symm.trans
      ((congrArg (Fmark.filtration.adaptedPolynomialRealValueHom
        (fun _ : C.Variables => 1) (fun index => (point index : ℝ))) hprojection).trans
        (hmarked point hpoint))))

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration.GlobalMarkedNativeFactors

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
    {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
    {w : σ → ℕ} {W : LieSubalgebra ℚ F.AssociatedGraded}
    {g : (F.realification.adaptedPolynomialFiltration w).Group}
    {E R : F.RealPolynomialSymbolGroup w}
    (A : GlobalMarkedNativeFactors F b ω hF w W g E R)
    (Fref : RationalFilteredNilmanifold (F.gradedRefiltrationSubalgebra W) s d)
    (hFref : Fref.filtration = F.gradedRefiltration W)

noncomputable def markedMiddleOn : Fref.filtration.realification.PolynomialOrbit w :=
  (F.gradedRefiltration W).realPolynomialOrbitChangeFiltration
    Fref.filtration hFref w A.markedMiddle

@[simp] theorem markedMiddleOn_log :
    (A.markedMiddleOn Fref hFref).log = A.markedMiddle.log := rfl

theorem markedMiddleOn_values (t : σ → ℝ) :
    realificationMap (hnil := Fref.filtration.lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
      (Fref.filtration.realification.polynomialOrbitRealEval w t
        (A.markedMiddleOn Fref hFref)) =
      F.adaptedPolynomialRealValueHom w t A.middle := by
  apply NilpotentLieBCHGroup.ext
  exact congrArg NilpotentLieBCHGroup.coord (A.middle_values t)

end Erdos3.NilpotentLieFiltration.GlobalMarkedNativeFactors

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

namespace AllocatedExternalLocalChart

variable {M κ : Type*} [LieRing M] [LieAlgebra ℚ M] {s f : ℕ}
    {F : NilpotentLieFiltration M s} {c : Basis κ ℚ M} {ν : κ → ℕ}
    {hF : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})}
    {W : LieSubalgebra ℚ F.AssociatedGraded}
    {g : (F.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors F c ν hF (fullTaggedVariableWeight J) W g EF RF)
    (Fref : RationalFilteredNilmanifold (F.gradedRefiltrationSubalgebra W) s f)
    (hFref : Fref.filtration = F.gradedRefiltration W)

theorem globalMarked_middle_values (u : C.Variables → ℤ) :
    F.adaptedPolynomialRealValueHom (fun _ : C.Variables => 1) (fun i => (u i : ℝ))
      (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart)
        C.integerChart_support factors.middle) =
      realificationMap (hnil := Fref.filtration.lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        (Fref.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          (C.chartValues u) (factors.markedMiddleOn Fref hFref)) := by
  rw [F.adaptedPolynomialRealValueHom_weightedChart]
  have heval : (fun i => MvPolynomial.eval (fun j => (u j : ℝ))
      (integerSampledRealChart C.integerChart i)) =
      (fun i => (C.chartValues u i : ℝ)) := by
    funext i
    exact integerSampledRealChart_eval C.integerChart u i
  rw [heval, ← factors.markedMiddleOn_values Fref hFref,
    polynomialOrbitRealEval_integer]

end AllocatedExternalLocalChart

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedRecoveredNormalizedTopChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_polynomial_remainder
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) (i : J j) :
    aeval (fun x => integerSampledRealChart
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inl x))
      (coordinate (LinearMap.proj i : (J j → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly j)) -
        C ((c j).val i) =
      mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val (sample j) i +
        integerSampledRealChart
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inr ⟨j, i⟩) := by
  apply MvPolynomial.funext
  intro x
  rw [map_sub, map_add, eval_C, mixedLiftPolynomial_eval]
  change aeval x (aeval _ _) - _ = _
  rw [comp_aeval_apply]
  simp only [aeval_eq_eval]
  rw [← coordinate_eval₂]
  have hspatial : (fun z => aeval x (integerSampledRealChart
      (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inl z))) =
      (fun z => (jointIntegerFrame (a, v) none z : ℝ) +
        ∑ k, (jointIntegerFrame (a, v) (some k) z : ℝ) * x k) := by
    funext z
    change aeval x (MvPolynomial.map (Int.castRingHom ℝ)
      (affineFramePolynomial (jointIntegerFrame (a, v)) z)) = _
    rw [affineFramePolynomial_map, affineFramePolynomial_eval]
    rfl
  have hspatial' := hspatial
  simp only [aeval_eq_eval] at hspatial'
  rw [hspatial']
  have heval := eval₂_algebraMap (S := ℝ)
    (fun z => (jointIntegerFrame (a, v) none z : ℝ) +
      ∑ k, (jointIntegerFrame (a, v) (some k) z : ℝ) * x k) (poly j)
  have heval' : eval₂ (fun z => (jointIntegerFrame (a, v) none z : ℝ) +
      ∑ k, (jointIntegerFrame (a, v) (some k) z : ℝ) * x k) (poly j) =
      eval (fun z => (jointIntegerFrame (a, v) none z : ℝ) +
      ∑ k, (jointIntegerFrame (a, v) (some k) z : ℝ) * x k) (poly j) := by
    simpa using heval
  rw [heval']
  exact h.integerFullChart_remainder B U b hb o S hR hσ poly hm hp c a v sample read x j i

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_normalized_top_tag
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (N : X → ℝ) (j : Fin m) (i : J j) :
    aeval (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
        (integerSampledRealChart
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) z))
      (normalizedRealPolynomialChart N (fullTaggedMajorTopCoordinates J poly) (Sum.inr ⟨j, i⟩)) =
      -homogeneousComponent (j.val + 1)
        (mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val (sample j) i) := by
  have hdegree (z : Σ j, J j) :
      coordinate (LinearMap.proj z.2 : (J z.1 → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly z.1) ∈
        weightedSupportLE (fun _ : X => 1) (z.1.val + 1) := by
    apply (mem_weightedSupportLE_iff _ _ _).mpr
    apply (scalar_weightedDegree_le_iff _ _ _).mpr
    intro α hα
    rw [coeff_coordinate, hp z.1 α hα, map_zero]
  change aeval (fun z => homogeneousComponent
    (Sum.elim (fun _ : X => 1) (fun z : Σ j, J j => z.1.val + 1) z)
    (integerSampledRealChart (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) z))
    (normalizedRealPolynomialChart N
      (fun z : Σ j, J j => homogeneousComponent (z.1.val + 1)
        (coordinate (LinearMap.proj z.2 : (J z.1 → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly z.1)))
      (Sum.inr ⟨j, i⟩)) = _
  rw [normalizedRealPolynomialChart_top_inr (fun z : Σ j, J j => z.1.val + 1) N
    (fun z => coordinate (LinearMap.proj z.2 : (J z.1 → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly z.1))
    hdegree _ (allocatedRecoveredIntegerFullChart_support B U b o poly hm c a v sample)]
  have heq := h.integerFullChart_polynomial_remainder B U b hb o S hR hσ poly hm
    hp c a v sample read j i
  have hres : integerSampledRealChart
      (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inr ⟨j, i⟩) -
      aeval (fun x => integerSampledRealChart
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inl x))
        (coordinate (LinearMap.proj i : (J j → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly j)) =
      -mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val (sample j) i -
        C ((c j).val i) := by linear_combination -heq
  rw [hres, map_sub, map_neg]
  have hcenter : homogeneousComponent (j.val + 1)
      (C ((c j).val i) : MvPolynomial (LayerSamplerVariables G I n B) ℝ) = 0 := by
    apply homogeneousComponent_eq_zero
    simp
  rw [hcenter, sub_zero]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedRecoveredChartMass
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_normalized_top_tag_mass
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (N : X → ℝ) (j : Fin m) (i : J j) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (aeval (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
        (integerSampledRealChart (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) z))
        (normalizedRealPolynomialChart N (fullTaggedMajorTopCoordinates J poly) (Sum.inr ⟨j, i⟩)))) ≤
      ((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m := by
  rw [h.integerFullChart_normalized_top_tag B U b hb o S hR hσ poly hm hp c a v sample read N j i]
  exact (normalizedMass_neg_weightedHomogeneousComponent_le _ _ _ _).trans
    (allocatedLayerSupported_normalized_mass_uniform B U b o hR hσ S hσ1 C hC hchart
      hsmall j (sample j) (h.2.2.1 j).2 i)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_normalized_top_mass
    [Fintype X]
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (i : X ⊕ (Σ j, J j)) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (aeval (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
        (integerSampledRealChart (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) z))
        (normalizedRealPolynomialChart (fun x => (N x : ℝ)) (fullTaggedMajorTopCoordinates J poly) i))) ≤
      ((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m := by
  cases i with
  | inl x =>
    apply (allocatedRecoveredIntegerFullChart_spatial_top_mass B U b S o poly hm c a
      N hN hτ hξ v hv sample x).trans
    have hdim : (1 : ℝ) ≤ ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    have hone := mul_le_mul hm (one_le_pow₀ hdim (n := m)) (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    apply (show τ / 8 ≤ 1 by linarith).trans
    simpa only [one_mul] using hone
  | inr z =>
    exact h.integerFullChart_normalized_top_tag_mass B U b hb o S hR hσ poly hm hp c a v
      sample read hσ1 C hC hchart hsmall (fun x => (N x : ℝ)) z.1 z.2

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_frozen_normalized_top_mass
    [Fintype X]
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    (i : X ⊕ (Σ j, J j)) :
    realPolynomialMass (scaleMvPolynomialAxes (fun i : {i // keep i} => layerSamplerBox B U b S i.val)
      (aeval (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
        (integerSampledRealChart (fun z => freezePolynomial keep fixed
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) z))
        (normalizedRealPolynomialChart (fun x => (N x : ℝ)) (fullTaggedMajorTopCoordinates J poly) i))) ≤
      ((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m := by
  change realPolynomialMass (scaleMvPolynomialAxes _
    (aeval (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)))) _)) ≤ _
  rw [aeval_frozen_integer_top (fullTaggedVariableWeight J)
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample)
    (allocatedRecoveredIntegerFullChart_support B U b o poly hm c a v sample)]
  have hT : ∀ k, 0 < layerSamplerBox B U b S k :=
    fun k => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k)
  exact (normalizedMass_freezePolynomial_le keep _ hT 0
    (fun i => by simpa only [Pi.zero_apply, abs_zero] using (hT i.val).le) _).trans
    (h.integerFullChart_normalized_top_mass B U b hb o S hR hσ poly hm hp c a N hN
      hτ hτ1 hξ v hv sample read hσ1 C hC hchart hsmall i)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualForecastSetup
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

section Generic

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

abbrev PreparedActualForecastShortIndex := AllocatedShortIntegerAxis U b S.value

end Generic

end Erdos3.VectorPolynomial

end

end OAI
end


