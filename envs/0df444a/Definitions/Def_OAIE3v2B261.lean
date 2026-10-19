-- Prove2me | Definitions.Def_OAIE3v2B261
-- name    : OAIE3v2B261
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:46:30.132815+00:00
-- url     : https://prove2.me/theorems/69b02777-9fcb-4440-8cdc-61c79bb8ff47
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 268 of 311
-- statement:
--   Definitions bundle 268 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B247`, `OAIE3v2B248`, `OAIE3v2B251`, `OAIE3v2B253` of this split.
--
--   Modules: `Dynamics/NormalizedTwistUniformAmbientBudget.lean`, `Estimates/ActualFiberSlicedBoundedTwistPrecision.lean`, `Estimates/AllocatedExternalCandidateTaggedPairFamily.lean`, `Estimates/AllocatedFrozenTaggedTwistStepDrop.lean`, `Estimates/NormalizedTwistUniformAmbientHaar.lean`, `Estimates/PreparedModularCanonicalDetectorAmbientConsumer.lean`, `Estimates/UnconditionedArbitraryFixedPatchFamily.lean`, `Fourier/MajorPhaseLowFourierExtraction.lean`, `Geometry/NormalizedTwistUniformBoxHaar.lean`, `Lattices/NativePairAffineCellStepDrop.lean`, `Linear/AllocatedFrozenTaggedTwistFixedBasisStepDrop.lean`, `Linear/AllocatedShortRankWitnessWidth.lean`, `Polynomial/PreparedUniformDegreeDirectMasterBudget.lean`, `Sampling/ForecastLawPhysicalAmbientHaarComparison.lean`, `Sampling/PreparedActualForecastSetup.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B247
import Definitions.Def_OAIE3v2B248
import Definitions.Def_OAIE3v2B251
import Definitions.Def_OAIE3v2B253

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.MajorPhaseLowFourierExtraction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial RationalFilteredNilmanifold
open scoped BigOperators TensorProduct Classical

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem exists_normalizedTwist_uniform_box_frequency_comparison (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : Type} [Fintype X] [DecidableEq X]
      {J : Fin m → Type} [∀ j, Fintype (J j)]
      (cover : ℕ), 0 < cover → ∀ (a : (Σ j, J j) → ℤ)
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
      (∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) →
      ∀ (U : ∀ j, Submodule ℝ (J j → ℝ)),
      (∀ j α, coefficients (poly j) α ∈ U j) →
      ∀ (p Rrank : ℝ), 2 ≤ p →
      (cover : ℝ) ≤ Real.exp p → (∀ i, |(a i : ℝ)| ≤ Real.exp p) →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (start : X → ℤ) (K : ℝ), 1 ≤ K → K ≤ Real.exp p →
      ∀ (N : X → ℝ), (∀ i, 0 < N i) →
      ∀ (origin : X → ℤ) (lengths : X → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, N i ≤ K * (q : ℝ) * (lengths i : ℝ)) →
      (Fintype.card X : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1) N Rrank (U j) (poly j)) →
      ‖(𝔼 x ∈ translatedIntegerBox origin lengths,
        (Real.fourierChar (MvPolynomial.eval
          (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ))
          (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ)) -
        (if ∀ j, U j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩))
          then 1 else 0)‖ ≤ Real.exp (-p) := by
  classical
  obtain ⟨C, hC, hremove⟩ := exists_normalizedTwist_high_frequency_removal_on_progression m
  refine ⟨C, hC, ?_⟩
  intro X _ _ J _ cover hcover a poly hpoly U hm p Rrank hp hcoverp ha
    q hq hqp start K hK hKp N hN origin lengths hlengths hNL hdim hlarge hRrank hrank
  by_cases hann : ∀ j, U j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩))
  · rw [if_pos hann, normalizedTwistFrequencyPolynomial_eq_zero_of_annihilates cover a poly U hm hann]
    let : ∀ i, NeZero (lengths i) := fun i => ⟨(hlengths i).ne'⟩
    simp only [map_zero, Real.fourierChar.map_zero_eq_one, Circle.coe_one,
      Finset.expect_const (translatedIntegerBox_nonempty lengths origin), sub_self, norm_zero]
    exact (Real.exp_pos _).le
  · rw [if_neg hann, sub_zero]
    apply le_of_lt
    by_contra! hcorr
    let R := Niltest.const (RationalTorus.trivialNilmanifold 0) (fun _ : X => 1) 1
    have hR : R.ComplexityLE p := RationalTorus.trivialNilmanifold_const_one_complexity 0 _ hp
    have hcap : (R.normBound : ℝ) ≤ 1 := by simp [R, Niltest.const]
    have hcorr' : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        (Real.fourierChar (MvPolynomial.eval
          (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ))
          (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ) * R.eval x‖ := by
      simpa only [R, Niltest.eval_const, mul_one] using hcorr
    have hall := hremove J 0 (RationalTorus.trivialNilmanifold 0) le_rfl R cover hcover a poly hpoly U
      (fun j α _ => hm j α) p Rrank (by linarith) hR hcap hcoverp ha q hq hqp
      start K hK hKp N hN origin lengths hlengths hNL hdim hlarge hRrank
      (fun j _ => hrank j) hcorr'
    exact hann (fun j => hall j (Nat.succ_pos _))

theorem exists_normalizedTwist_uniform_box_fourier_comparison (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : Type} [Fintype X] [DecidableEq X]
      {J : Fin m → Type} [∀ j, Fintype (J j)]
      {F : Type*} [Fintype F] (cover : ℕ), 0 < cover →
      ∀ (frequency : F → (Σ j, J j) → ℤ) (coeff : F → ℂ)
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
      (∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) →
      ∀ (U : ∀ j, Submodule ℝ (J j → ℝ)),
      (∀ j α, coefficients (poly j) α ∈ U j) →
      ∀ (p Rrank : ℝ), 2 ≤ p →
      (cover : ℝ) ≤ Real.exp p → (∀ b i, |(frequency b i : ℝ)| ≤ Real.exp p) →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (start : X → ℤ) (K : ℝ), 1 ≤ K → K ≤ Real.exp p →
      ∀ (N : X → ℝ), (∀ i, 0 < N i) →
      ∀ (origin : X → ℤ) (lengths : X → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, N i ≤ K * (q : ℝ) * (lengths i : ℝ)) →
      (Fintype.card X : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1) N Rrank (U j) (poly j)) →
      ‖(𝔼 x ∈ translatedIntegerBox origin lengths,
        ∑ b, coeff b * (Real.fourierChar (MvPolynomial.eval
          (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ))
          (normalizedTwistFrequencyPolynomial cover (frequency b) poly)) : ℂ)) -
        ∑ b, coeff b * (if ∀ j, U j ≤ LinearMap.ker
          (integerRowLinear (fun i => frequency b ⟨j, i⟩)) then 1 else 0)‖ ≤
        (∑ b, ‖coeff b‖) * Real.exp (-p) := by
  obtain ⟨C, hC, hfreq⟩ := exists_normalizedTwist_uniform_box_frequency_comparison m
  refine ⟨C, hC, ?_⟩
  intro X _ _ J _ F _ cover hcover frequency coeff poly hpoly U hm p Rrank hp hcoverp ha
    q hq hqp start K hK hKp N hN origin lengths hlengths hNL hdim hlarge hRrank hrank
  simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect]
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (hfreq cover hcover (frequency b) poly hpoly U hm p Rrank hp hcoverp (ha b)
      q hq hqp start K hK hKp N hN origin lengths hlengths hNL hdim hlarge hRrank hrank)
    (norm_nonneg _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedTwistUniformBoxHaar
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_normalizedTwist_uniform_progression_haar_comparison (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : Type} [Fintype X] [DecidableEq X]
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
      (residue : X → ZMod W.modulus) (center : X → ℝ)
      {η Q p Rrank : ℝ}, 0 < η → 0 ≤ Q →
      (Fintype.card (Σ j, J j) : ℝ) ≤ Q →
      (L : ℝ) ≤ Real.exp Q → η⁻¹ ≤ Real.exp Q →
      2 ≤ p → (2 * Q + 2) ^ 4 ≤ p →
      (W.cover : ℝ) ≤ Real.exp p →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (start : X → ℤ) (K : ℝ), 1 ≤ K → K ≤ Real.exp p →
      ∀ (N : X → ℝ), (∀ i, 0 < N i) →
      ∀ (origin : X → ℤ) (lengths : X → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, N i ≤ K * (q : ℝ) * (lengths i : ℝ)) →
      (Fintype.card X : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1) N Rrank (U j) (poly j)) →
      ‖(𝔼 x ∈ translatedIntegerBox origin lengths,
        W.frozenTorus residue center (physicalGridFactorInput W.cover poly
          (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ)))) -
        W.frozenSingleSiteHaarReference U ν residue center‖ ≤
        2 * η + Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) := by
  obtain ⟨C, hC, hfourier⟩ := exists_normalizedTwist_uniform_box_fourier_comparison m
  refine ⟨C, hC, ?_⟩
  intro X _ _ J _ U ν _ _ poly hp hm periodCap coverCap L W residue center
    η Q p Rrank hη hQ hdim hL hηQ hp2 hfreq hcover q hq hqp start K hK hKp N hN
    origin lengths hlengths hNL hX hlarge hRrank hrank
  obtain ⟨F, inst, frequency, coeff, _, hfreqB, hmass, herr⟩ :=
    exists_ambient_torus_fourier_approximation (W.frozenTorus residue center) L 1
      (W.frozenTorus_lipschitz residue center) (W.norm_frozenTorus_le residue center)
      hη hQ hdim hL hηQ
  let := inst
  let : ∀ i, NeZero (lengths i) := fun i => ⟨(hlengths i).ne'⟩
  let μ := Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))
  let chart : EuclideanJetLayers U (fun _ => Unit) → (Σ j, J j) → UnitAddCircle :=
    fun y a => coveredJetAmbientTorus U 1 y ⟨a.1, (), a.2⟩
  let f := W.frozenTorus residue center
  let g : ((Σ j, J j) → UnitAddCircle) → ℂ :=
    fun y => ∑ b, coeff b * ambientIntegerCharacter (frequency b) y
  let point (x : X → ℤ) := physicalGridFactorInput W.cover poly
    (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ))
  have hfg (y) : ‖f y - g y‖ ≤ η := herr y
  have hmean : ‖(𝔼 x ∈ translatedIntegerBox origin lengths, f (point x)) -
      (𝔼 x ∈ translatedIntegerBox origin lengths, g (point x))‖ ≤ η := by
    rw [← Finset.expect_sub_distrib]
    exact (RCLike.norm_expect_le (K := ℂ)).trans
      (Finset.expect_le (translatedIntegerBox_nonempty lengths origin) (fun x _ => hfg _))
  have hf : Integrable (fun y => f (chart y)) μ :=
    W.frozenSingleSiteHaarReference_integrable U ν residue center
  have hgi (b : F) : Integrable (fun y => coeff b * ambientIntegerCharacter (frequency b) (chart y)) μ :=
    (singleSiteHaar_ambientIntegerCharacter_integrable U ν (frequency b)).const_mul _
  have hg : Integrable (fun y => g (chart y)) μ := integrable_finsetSum _ (fun b _ => hgi b)
  have hint : ‖(∫ y, g (chart y) ∂μ) - ∫ y, f (chart y) ∂μ‖ ≤ η :=
    probability_integral_approximation μ _ _ hg hf (fun y => by
      simpa only [norm_sub_rev] using hfg (chart y))
  have hge : (∫ y, g (chart y) ∂μ) =
      ∑ b, coeff b * (if ∀ j, U j ≤ LinearMap.ker
        (integerRowLinear (fun i => frequency b ⟨j, i⟩)) then 1 else 0) := by
    rw [show (fun y => g (chart y)) =
      (fun y => ∑ b, coeff b * ambientIntegerCharacter (frequency b) (chart y)) from rfl,
       integral_finsetSum _ (fun b _ => hgi b)]
    apply Finset.sum_congr rfl
    intro b _
    rw [integral_const_mul]
    exact congrArg (coeff b * ·) (singleSiteHaar_ambientIntegerCharacter_integral U ν (frequency b))
  have hcomp := hfourier W.cover W.cover_pos frequency coeff poly hp U hm p Rrank hp2 hcover
    (fun b i => (hfreqB b i).trans (Real.exp_le_exp.mpr hfreq)) q hq hqp start K hK hKp
    N hN origin lengths hlengths hNL hX hlarge hRrank hrank
  have hgpoint (x) : g (point x) = ∑ b, coeff b *
      (Real.fourierChar (MvPolynomial.eval
        (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ))
        (normalizedTwistFrequencyPolynomial W.cover (frequency b) poly)) : ℂ) := by
    simp only [g, point, ambientIntegerCharacter, physicalGrid_character_eq_polynomial_phase]
  rw [← hge] at hcomp
  simp_rw [← hgpoint] at hcomp
  have hmass' : (∑ b, ‖coeff b‖) * Real.exp (-p) ≤
      Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) := by
    calc
      _ ≤ Real.exp (2 * Q * (2 * Q + 2) ^ 4) * Real.exp (-p) :=
        mul_le_mul_of_nonneg_right (by simpa using hmass) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; rfl
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (𝔼 x ∈ translatedIntegerBox origin lengths, f (point x))
    (𝔼 x ∈ translatedIntegerBox origin lengths, g (point x)) (∫ y, f (chart y) ∂μ)
  have ht' := norm_sub_le_norm_sub_add_norm_sub
    (𝔼 x ∈ translatedIntegerBox origin lengths, g (point x))
    (∫ y, g (chart y) ∂μ) (∫ y, f (chart y) ∂μ)
  change ‖(𝔼 x ∈ translatedIntegerBox origin lengths, f (point x)) -
    ∫ y, f (chart y) ∂μ‖ ≤ _
  linarith [hcomp.trans hmass']

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTwistUniformAmbientHaar
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_normalizedTwist_uniform_ambient_haar_comparison (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : Type} [Fintype X] [DecidableEq X]
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
      {η Q p Rrank : ℝ}, 0 < η → 0 ≤ Q →
      (Fintype.card (Σ j, J j) : ℝ) ≤ Q →
      (L : ℝ) ≤ Real.exp Q → η⁻¹ ≤ Real.exp Q →
      3 * Q + 16 ≤ p → (2 * Q + 2) ^ 4 ≤ p →
      (W.cover : ℝ) ≤ Real.exp p → (W.modulus : ℝ) ≤ Real.exp Q →
      ∀ (N : X → ℕ), (Fintype.card X : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C + 3 * Q + 16) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      ‖(𝔼 x ∈ integerBox N, W.eval N poly x) -
        (𝔼 x ∈ integerBox N, W.frozenSingleSiteHaarReference U ν
          (fun i => (x i : ZMod W.modulus)) (fun i => (x i : ℝ) / N i))‖ ≤
        2 * η + Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) +
          (L : ℝ) * Real.exp (-2 * Q) / 2 := by
  obtain ⟨C, hC, hlocal⟩ := exists_normalizedTwist_uniform_progression_haar_comparison m
  refine ⟨C, hC, ?_⟩
  intro X _ _ J _ U ν _ _ poly hp hm periodCap coverCap L W
    η Q p Rrank hη hQ hdim hL hηQ hpQ hfreq hcover hmod N hX hlarge hRrank hrank
  have hp2 : 2 ≤ p := by linarith
  have hpow : 0 ≤ (p + C) ^ C := pow_nonneg (by positivity) _
  have hNloc (i) : Real.exp (3 * Q + 16) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans (hlarge i)
  have hNpos (i) : 0 < (N i : ℝ) := (Real.exp_pos _).trans_le (hNloc i)
  let H (x : X → ℤ) := W.frozenSingleSiteHaarReference U ν
    (fun i => (x i : ZMod W.modulus)) (fun i => (x i : ℝ) / N i)
  obtain ⟨start, length, hpos, hlen, hscale, _, _, hdiam, _, hselect⟩ :=
    exists_correlated_integer_residue_box N W.modulus Q hQ W.modulus_pos hmod hNloc
      (fun x => W.eval N poly x - H x)
  let u (v : X → ℤ) (i : X) : ℤ := (start i : ℤ) + (W.modulus : ℤ) * v i
  let center (i : X) : ℝ := (start i : ℝ) / N i
  let residue (i : X) : ZMod W.modulus := (start i : ZMod W.modulus)
  let F (v : X → ℤ) := W.frozenSpatialEval center poly (u v)
  let H₀ := W.frozenSingleSiteHaarReference U ν residue center
  have hresidue (v) : (fun i => (u v i : ZMod W.modulus)) = residue := by
    funext i
    simp [u, residue]
  have hdist (v) (hv : v ∈ integerBox length) :
      dist (fun i => (u v i : ℝ) / N i) center ≤ Real.exp (-2 * Q) / 4 := by
    apply (dist_pi_le_iff (by positivity)).mpr
    intro i
    simpa only [u, center, Real.dist_eq, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      neg_mul] using hdiam v hv i
  have hFerr (v) (hv : v ∈ integerBox length) :
      ‖W.eval N poly (u v) - F v‖ ≤ (L : ℝ) * (Real.exp (-2 * Q) / 4) :=
    (W.eval_sub_frozenSpatialEval N center poly (u v)).trans
      (mul_le_mul_of_nonneg_left (hdist v hv) L.coe_nonneg)
  have hHerr (v) (hv : v ∈ integerBox length) :
      ‖H (u v) - H₀‖ ≤ (L : ℝ) * (Real.exp (-2 * Q) / 4) := by
    dsimp only [H, H₀]
    rw [hresidue]
    exact ((W.frozenSingleSiteHaarReference_lipschitz U ν residue).norm_sub_le _ _).trans
      (mul_le_mul_of_nonneg_left (hdist v hv) L.coe_nonneg)
  let : ∀ i, NeZero (length i) := fun i => ⟨(hpos i).ne'⟩
  have hmeanerr : ‖(𝔼 v ∈ integerBox length, (W.eval N poly (u v) - H (u v))) -
      (𝔼 v ∈ integerBox length, (F v - H₀))‖ ≤ (L : ℝ) * Real.exp (-2 * Q) / 2 := by
    rw [← Finset.expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le (integerBox_nonempty length)
    intro v hv
    have he : W.eval N poly (u v) - H (u v) - (F v - H₀) =
        (W.eval N poly (u v) - F v) - (H (u v) - H₀) := by ring
    rw [he]
    have hh := (norm_sub_le (W.eval N poly (u v) - F v) (H (u v) - H₀)).trans
      (add_le_add (hFerr v hv) (hHerr v hv))
    convert hh using 1; ring
  have hlong (i) : Real.exp ((p + C) ^ C) ≤ (length i : ℝ) := by
    calc
      _ = Real.exp ((p + C) ^ C + 3 * Q + 16) * Real.exp (-(3 * Q + 16)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ (N i : ℝ) * Real.exp (-(3 * Q + 16)) :=
        mul_le_mul_of_nonneg_right (hlarge i) (Real.exp_nonneg _)
      _ ≤ _ := hlen i
  have hzero : translatedIntegerBox (0 : X → ℤ) length = integerBox length := by
    ext v
    simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
  have hcomp := hlocal U ν poly hp hm W residue center hη hQ hdim hL hηQ hp2 hfreq hcover
    W.modulus W.modulus_pos (hmod.trans (Real.exp_le_exp.mpr (by linarith)))
    (fun i => (start i : ℤ)) (Real.exp (3 * Q + 16))
    (Real.one_le_exp (by positivity)) (Real.exp_le_exp.mpr hpQ)
    (fun i => (N i : ℝ)) hNpos 0 length hpos hscale hX hlong hRrank hrank
  rw [hzero] at hcomp
  have hF (v) : F v = W.frozenTorus residue center (physicalGridFactorInput W.cover poly
      (fun i => (start i : ℝ) + (W.modulus : ℝ) * (v i : ℝ))) := by
    dsimp only [F, NormalizedPolynomialTwist.frozenSpatialEval]
    rw [hresidue]
    simp only [u, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  simp only [Int.cast_natCast] at hcomp
  simp_rw [← hF] at hcomp
  have hcomp' : ‖𝔼 v ∈ integerBox length, (F v - H₀)‖ ≤
      2 * η + Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) := by
    rw [Finset.expect_sub_distrib, Finset.expect_const (integerBox_nonempty length)]
    simpa only [Int.cast_natCast] using hcomp
  change ‖(𝔼 x ∈ integerBox N, W.eval N poly x) - 𝔼 x ∈ integerBox N, H x‖ ≤ _
  rw [← Finset.expect_sub_distrib]
  apply hselect.trans
  change ‖𝔼 v ∈ integerBox length, (W.eval N poly (u v) - H (u v))‖ ≤ _
  have ht := norm_le_norm_sub_add
    (𝔼 v ∈ integerBox length, (W.eval N poly (u v) - H (u v)))
    (𝔼 v ∈ integerBox length, (F v - H₀))
  linarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedTwistUniformAmbientBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedShortRankWitnessWidth
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

theorem allocatedChartResiduePrimePowerWitness_mixedArray_iff_actual
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (x : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (deck : ∀ j, BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → ℤ) :
    allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
      (fun q => (noise q : ZMod M))
      (coefficientSamplerChartResidues M x (fun j q i => (deck j q i : ZMod M))) ↔
      ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
        (allocatedMixedFullArray
          (Sum.elim noise (fun ⟨j,q,i⟩ => (x j).2 i q))
          (fun ⟨j,q,i⟩ => deck j q i) continuous) := by
  exact allocatedChartResiduePrimePowerWitness_sampler_iff_actual
    inactive spatial kernel block C P A M hdiv
    (allocatedMixedFullArray
      (Sum.elim noise (fun ⟨j,q,i⟩ => (x j).2 i q))
      (fun ⟨j,q,i⟩ => deck j q i) continuous) x (fun _ _ _ => rfl)

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

theorem preparedActualForecastShortSelection_injective :
    Function.Injective (preparedActualForecastShortSelection B U b S) :=
  Subtype.val_injective

end Generic

section Prepared

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m) (Jalloc : ℕ)
variable {G : Type*} [Fintype G]
variable {Jout : Fin m → Type*} [∀ j, Fintype (Jout j)]
variable (U : ∀ j, Submodule ℝ (Jout j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ
  (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale (G := G) (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)

theorem enlargedPreparedActualForecastShortSelection_nonempty
    (a : PreparedActualForecastShortIndex (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S) :
    Nonempty (EnlargedPreparedCommonSamplerBlock L Jalloc
      ⟨(preparedActualForecastShortSelection (EnlargedPreparedCommonSamplerBlock L Jalloc)
        U b S a).1,
        Sum.inr (preparedActualForecastShortSelection
          (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S a).2⟩) :=
  Fintype.card_pos_iff.mp (enlargedPreparedCommonSamplerBlock_positive L Jalloc _)

end Prepared

end Erdos3.VectorPolynomial

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActualFiberSlicedBoundedTwistPrecision
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "ActiveInput" => PrincipalTupleIndex (fun a : Active => B (Subtype.val a))
  (fun a : Active => degree (Subtype.val a))

variable {keep : G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n) → Prop} [DecidablePred keep]
variable {q : ℕ}
variable (slice : ResidueBoxSlice
  (fun k : {k // keep k} => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val) q)
variable (hlen : ∀ k, 0 < slice.length k) (fixed : {k // ¬keep k} → ℤ)
variable (hfixed : ∀ k, 0 ≤ fixed k ∧
  fixed k < ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val : ℕ) : ℤ))
variable (hkernel : ∀ g, keep (Sum.inl g))

variable (hactive : ∀ j : PrincipalTupleIndex
  (fun a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a} => B a.val)
  (fun a => layerSamplerDegree I n a.val), keep (Sum.inr ⟨j.1.val, j.2⟩))

include hlen hfixed hactive in

theorem allocatedFiberActiveProgression_common_contained (j : ActiveInput) :
    integerProgressionSupport (slice.fiberParameterStart fixed (Sum.inr ⟨j.1.val, j.2⟩))
      (q : ℤ) (slice.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩)) ⊆
        Finset.Ico (0 : ℤ) (S.value : ℤ) := by
  simpa only [ResidueBoxSlice.fiberParameterStride, if_pos (hactive j)] using
    allocatedFiberActiveProgression_contained B U basis S slice hlen fixed hfixed j

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativePairAffineCellStepDrop
namespace OAI

universe u

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFrozenTaggedTwistStepDrop
namespace OAI

universe u

section

namespace Erdos3

open Module RationalFilteredNilmanifold BooleanCubeKernel
open VectorPolynomial
open scoped TensorProduct BigOperators NNReal

theorem exists_native_twist_variation_slice_step_drop (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {K : Type*}
      [Fintype K] [DecidableEq K] [Nonempty K]
      {P : K → ℕ} {q : ℕ} (S : ResidueBoxSlice P q) (_hq : 0 < q)
      (hlen : ∀ k, 0 < S.length k) {p : ℝ} (_hp : 0 ≤ p)
      (_hS : ∀ k, Real.exp (-p) * (P k : ℝ) ≤ S.length k)
      (_hP : ∀ k, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (P k : ℝ))
      {M : ℕ} (_hM : 0 < M) (_hperiod : (M : ℝ) ≤ Real.exp p)
      (twist : integerBox P → ℂ) (_htwist : ∀ t, ‖twist t‖ ≤ 1)
      {variation : ℝ} (_hvariation_nonneg : 0 ≤ variation)
      (_hvariation_bound : variation ≤ Real.exp p)
      (_hvariation : ∀ u v : integerBox P,
        (∀ k, (u.val k : ZMod M) = (v.val k : ZMod M)) →
        ∀ δ : ℝ, 0 ≤ δ →
        (∀ k, |(u.val k : ℝ) / P k - (v.val k : ℝ) / P k| ≤ δ) →
        ‖twist u - twist v‖ ≤ variation * δ)
      {LG MG : Type u} [LieRing LG] [LieAlgebra ℚ LG] [LieRing MG] [LieAlgebra ℚ MG]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
      [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
      (D : RationalFilteredNilmanifold LG s d) (E : RationalFilteredNilmanifold MG s e)
      (V : D.Niltest (fun _ : K => 1)) (W : E.Niltest (fun _ : K => 1))
      (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p) (_hWnorm : W.normBound ≤ 1)
      (η : LG →ₗ[ℚ] ℚ) (θ : MG →ₗ[ℚ] ℚ)
      (_hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
      (_hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
      (_hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        V.observable (z • x) = CircleFourier.character
          ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x)
      (_hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
        W.observable (z • x) = CircleFourier.character
          ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x)
      (_hK : (Fintype.card K : ℝ) ≤ p)
      (_hbias : Real.exp (-p) ≤ ‖(S.fullSliceLaw hlen).complexMean (fun t =>
        star (twist t) *
          (V.eval t.val * W.eval t.val))‖),
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra LG MG))) ℚ (PairAlgebra LG MG))
        (ω : Fin (finrank ℚ (PairAlgebra LG MG)) → ℕ)
        (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (b '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (b i) j) ≤
          (p + 2 + C) ^ C) ∧
        (pi (pairModels D E)).filtration.ControlledSymbolFactorization b ω hF
          (pairFrequency η θ) (fun k => (P k : ℝ))
          (pairOrbitSymbol D E V.orbit W.orbit b ω hF)
          ((p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23)) := by
  obtain ⟨C, hC, hstep⟩ := exists_native_pair_affine_cell_step_drop s hs
  refine ⟨C, hC, ?_⟩
  intro K _ _ _ P q S hq hlen p hp hS hP M hM hperiod twist htwist
    variation hvariation_nonneg hvariation_bound hvariation
    LG MG _ _ _ _ d e _ _ _ _ _ _ _ _
    D E V W hV hW hWnorm η θ hηheight hθheight hη hθ hK hbias
  have hbudget : 0 ≤ (p + 2 + C) ^ C := by positivity
  have hPfreeze (k : K) : Real.exp (p + (3 * (2 * p + 2) + 16)) ≤ (P k : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans (hP k)
  have hperiod' : ((M : ℕ) : ℝ) ≤ Real.exp (2 * p + 2) :=
    hperiod.trans (Real.exp_le_exp.mpr (by linarith))
  have hfreeze : ∀ u v : integerBox P,
      (∀ k, (u.val k : ZMod M) = (v.val k : ZMod M)) →
      (∀ k, |(u.val k : ℝ) / P k - (v.val k : ℝ) / P k| ≤
        2 * (Real.exp (-(2 * (2 * p + 2))) / 4)) →
      ‖twist u - twist v‖ ≤ variation *
        (2 * (Real.exp (-(2 * (2 * p + 2))) / 4)) := by
    intro u v hres hnear
    exact hvariation u v hres _ (by positivity) hnear
  obtain ⟨T, hTq, hTlen, hTside, hcorr⟩ :=
    NormalizedPolynomialTwist.exists_niltest_pair_correlation_subrectangle_of_variation
      S hq hlen (by linarith : 0 ≤ 2 * p + 2) hS hPfreeze hM hperiod'
      twist htwist hfreeze V W hV hWnorm (Real.exp_pos (-p)) hbias
  have herror : Real.exp p *
      (variation * (2 * (Real.exp (-(2 * (2 * p + 2))) / 4))) ≤
      Real.exp (-p) / 4 := by
    convert nativeTwistedSlice_freezing_error hp hvariation_nonneg hvariation_bound
      (by norm_num : (0 : ℝ) ≤ 1) (le_refl (1 : ℝ)) using 1
    ring
  have hbias' : Real.exp (-(p + 2)) ≤ ‖𝔼 x ∈ translatedIntegerBox (0 : K → ℤ) T.length,
      V.eval (fun k => ((q * M : ℕ) : ℤ) * x k + T.start k) *
        W.eval (fun k => ((q * M : ℕ) : ℤ) * x k + T.start k)‖ :=
    (nativeTwistedSlice_bias_precision p).trans (by linarith)
  have hTside' (k : K) : Real.exp (-(7 * p + 22)) * (P k : ℝ) ≤ T.length k := by
    simpa only [show p + (3 * (2 * p + 2) + 16) = 7 * p + 22 by ring] using hTside k
  have hlong (k : K) : Real.exp ((p + 2 + C) ^ C) ≤ (T.length k : ℝ) := by
    calc
      _ = Real.exp (-(7 * p + 22)) * Real.exp ((p + 2 + C) ^ C + 7 * p + 22) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(7 * p + 22)) * (P k : ℝ) :=
        mul_le_mul_of_nonneg_left (hP k) (Real.exp_nonneg _)
      _ ≤ _ := hTside' k
  have hPpos (k : K) : (0 : ℝ) < P k := (Real.exp_pos _).trans_le (hP k)
  have hphysical (k : K) : Real.exp (-(7 * p + 22)) *
      ((P k : ℝ) / (q * M : ℕ)) ≤ T.length k := by
    apply le_trans _ (hTside' k)
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    exact div_le_self (hPpos k).le (by exact_mod_cast hTq)
  obtain ⟨k₀⟩ := ‹Nonempty K›
  have htwo : 2 ≤ S.length k₀ := by
    have he := S.length_large_of_cost hS hPfreeze k₀
    have ht := Real.add_one_le_exp (3 * (2 * p + 2) + 16)
    have : (2 : ℝ) ≤ S.length k₀ := by linarith
    exact_mod_cast this
  have hstride : ((q * M : ℕ) : ℝ) ≤ Real.exp (2 * p + 1) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ (2 * Real.exp p) * Real.exp p :=
        mul_le_mul (S.stride_le_twice_exp_cost k₀ htwo (hS k₀)) hperiod
          (Nat.cast_nonneg _) (by positivity)
      _ ≤ Real.exp 1 * (Real.exp p * Real.exp p) := by
        have := Real.add_one_le_exp 1
        nlinarith [mul_pos (Real.exp_pos p) (Real.exp_pos p)]
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hp' : p ≤ p + 2 := by linarith
  obtain ⟨b, ω, hF, hb, hf⟩ := hstep D E V W (by linarith : 2 ≤ p + 2)
    (by linarith : 0 ≤ 7 * p + 22) (by linarith : 0 ≤ 2 * p + 1)
    (hV.mono hp') (hW.mono hp') _ hTq hstride (fun k => (T.start k : ℤ)) η θ
    (fun i => (hηheight i).trans hp') (fun i => (hθheight i).trans hp') hη hθ
    0 T.length (fun k => (P k : ℝ)) hTlen hPpos (hK.trans hp') hlong hphysical hbias'
  refine ⟨b, ω, hF, hb, ?_⟩
  convert hf using 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFrozenTaggedTwistFixedBasisStepDrop
namespace OAI

universe u

section

namespace Erdos3
open Module RationalFilteredNilmanifold BooleanCubeKernel
open VectorPolynomial
open scoped TensorProduct BigOperators NNReal

theorem exists_native_twist_variation_slice_fixed_basis_step_drop (s : ℕ) (hs : 1 ≤ s) :
    ∃ C A : ℕ, 2 ≤ C ∧ 2 ≤ A ∧ ∀
      {LG MG : Type u} [LieRing LG] [LieAlgebra ℚ LG] [LieRing MG] [LieAlgebra ℚ MG]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
      [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
      (D : RationalFilteredNilmanifold LG s d) (E : RationalFilteredNilmanifold MG s e)
      {pGeo : ℝ} (_hpGeo : 0 ≤ pGeo)
      (_hGeo : (pi (pairModels D E)).GeometryComplexityLE pGeo),
      ∃ (c : Basis (Fin (finrank ℚ (PairAlgebra LG MG))) ℚ (PairAlgebra LG MG))
        (ν : Fin (finrank ℚ (PairAlgebra LG MG)) → ℕ)
        (hC : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (c '' {i | k ≤ ν i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (c i) j) ≤ pGeo + 1) ∧
        (∀ i j, rationalLogHeight (c.repr ((pi (pairModels D E)).basis i) j) ≤ (pGeo + 3) ^ 5) ∧
        ∀ {K : Type*}
      [Fintype K] [DecidableEq K] [Nonempty K]
      {P : K → ℕ} {q : ℕ} (S : ResidueBoxSlice P q) (_hq : 0 < q)
      (hlen : ∀ k, 0 < S.length k) {p : ℝ} (_hp : 0 ≤ p)
      (_hS : ∀ k, Real.exp (-p) * (P k : ℝ) ≤ S.length k)
      (_hP : ∀ k, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (P k : ℝ))
      {M : ℕ} (_hM : 0 < M) (_hperiod : (M : ℝ) ≤ Real.exp p)
      (twist : integerBox P → ℂ) (_htwist : ∀ t, ‖twist t‖ ≤ 1)
      {variation : ℝ} (_hvariation_nonneg : 0 ≤ variation)
      (_hvariation_bound : variation ≤ Real.exp p)
      (_hvariation : ∀ u v : integerBox P,
        (∀ k, (u.val k : ZMod M) = (v.val k : ZMod M)) →
        ∀ δ : ℝ, 0 ≤ δ →
        (∀ k, |(u.val k : ℝ) / P k - (v.val k : ℝ) / P k| ≤ δ) →
        ‖twist u - twist v‖ ≤ variation * δ)
      (V : D.Niltest (fun _ : K => 1)) (W : E.Niltest (fun _ : K => 1))
      (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p) (_hWnorm : W.normBound ≤ 1)
      (η : LG →ₗ[ℚ] ℚ) (θ : MG →ₗ[ℚ] ℚ)
      (_hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
      (_hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
      (_hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        V.observable (z • x) = CircleFourier.character
          ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x)
      (_hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
        W.observable (z • x) = CircleFourier.character
          ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x)
      (_hK : (Fintype.card K : ℝ) ≤ p)
      (_hbias : Real.exp (-p) ≤ ‖(S.fullSliceLaw hlen).complexMean (fun t =>
        star (twist t) *
          (V.eval t.val * W.eval t.val))‖),
      (pi (pairModels D E)).filtration.ControlledSymbolFactorization c ν hC
        (pairFrequency η θ) (fun k => (P k : ℝ))
        (pairOrbitSymbol D E V.orbit W.orbit c ν hC)
        ((fixedAdaptedSymbolTransferInput pGeo
          (pGeo + p + ((p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23))) + A) ^ A) := by
  obtain ⟨C, hC, hstep⟩ := exists_native_twist_variation_slice_step_drop s hs
  obtain ⟨A, hA, hfixed⟩ := exists_fixed_adapted_symbol_factorization_basis s
  refine ⟨C, A, hC, hA, ?_⟩
  intro LG MG _ _ _ _ d e _ _ _ _ _ _ _ _ D E pGeo hpGeo hGeo
  obtain ⟨c, ν, N, hc, _, _, hforward, hinverse, _, _, _, _, _, htransfer⟩ :=
    hfixed (pi (pairModels D E)) hpGeo hGeo
  refine ⟨c, ν, hc, hforward, hinverse, ?_⟩
  intro K _ _ _ P q S hq hlen p hp hS hP M hM hperiod twist htwist
    variation hvariation_nonneg hvariation_bound hvariation
    V W hV hW hWnorm η θ hηheight hθheight hη hθ hK hbias
  obtain ⟨b, ω, hF, hb, hfactor⟩ := hstep S hq hlen hp hS hP hM hperiod
    twist htwist hvariation_nonneg hvariation_bound hvariation
    D E V W hV hW hWnorm η θ hηheight hθheight hη hθ hK hbias
  let cost := (p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23)
  have hcost : 0 ≤ cost := by dsimp only [cost]; positivity
  have hPpos (k : K) : (0 : ℝ) < P k := (Real.exp_pos _).trans_le (hP k)
  have hqGeo : pGeo ≤ pGeo + p + cost := by linarith
  have hqP : p ≤ pGeo + p + cost := by linarith
  have hqCost : cost ≤ pGeo + p + cost := by linarith
  have hbase : (p + 2 + C) ^ C ≤ cost := by
    dsimp only [cost]
    linarith [show 0 ≤ (s : ℝ) * (9 * p + 23) by positivity]
  have htransferred := htransfer hqGeo (hK.trans hqP) b ω hF
    (fun i j => (hb i j).trans (hbase.trans hqCost)) (fun k => (P k : ℝ)) hPpos
    (pairFrequency η θ) (pairOrbitSymbol D E V.orbit W.orbit b ω hF)
    (hfactor.mono (pi (pairModels D E)).filtration b ω hF hqCost hPpos)
  rw [pairOrbitSymbol_basis_independent D E V.orbit W.orbit b ω hF c ν hc] at htransferred
  exact htransferred

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial RationalFilteredNilmanifold
open scoped BigOperators NNReal Classical TensorProduct

theorem exists_allocated_frozen_tagged_twist_fixed_basis_step_drop
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ C A : ℕ, 2 ≤ C ∧ 2 ≤ A ∧ ∀
      {LG MG : Type u} [LieRing LG] [LieAlgebra ℚ LG] [LieRing MG] [LieAlgebra ℚ MG]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
      [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
      (D : RationalFilteredNilmanifold LG s d) (E : RationalFilteredNilmanifold MG s e)
      {pGeo : ℝ} (_hpGeo : 0 ≤ pGeo)
      (_hGeo : (pi (pairModels D E)).GeometryComplexityLE pGeo),
      ∃ (bFixed : Basis (Fin (finrank ℚ (PairAlgebra LG MG))) ℚ (PairAlgebra LG MG))
        (ωFixed : Fin (finrank ℚ (PairAlgebra LG MG)) → ℕ)
        (hFixed : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (bFixed '' {i | k ≤ ωFixed i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (bFixed i) j) ≤ pGeo + 1) ∧
        (∀ i j, rationalLogHeight (bFixed.repr ((pi (pairModels D E)).basis i) j) ≤ (pGeo + 3) ^ 5) ∧
    ∀ {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I Deck J : Fin m → Type*}
      [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
      {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
      (hbtag : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j)))
      (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
      {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U btag R σ)
      (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j d, coefficients (poly j) d ∈ U j)
      (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
      (c : ∀ j, U j) (a : X → ℤ) (N : X → ℕ) (_hN : ∀ x, 0 < N x)
      {τ ξ : ℝ} (_hτ : 0 < τ) (_hτ1 : τ ≤ 1) (_hξ : ξ ≤ 1)
      (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
      (_hv : v ∈ rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U btag S (fun _ => 0)) τ ξ N) 1)
      (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
      (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ)
      (_hread : AllocatedCenteredFramedRecoveredSampleAt B U btag hbtag o S hR hσ poly hm c a v sample read)
      (_hσ1 : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (_hCgeo : ∀ j, 0 ≤ Cgeo j)
      (_hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
      (_hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
      {periodCap coverCap : ℝ} {L : ℝ≥0}
      (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
      {p : ℝ} (_hp : 0 ≤ p)
      (_hperiod : ((twist.modulus * twist.cover : ℕ) : ℝ) ≤ Real.exp p)
      (_hvariationBound : (L : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p)
      (keep : LayerSamplerVariables G I n B → Prop) [Nonempty {i // keep i}]
      (fixed : {i // ¬keep i} → ℤ)
      (_hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i <
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U btag S) i.val),
      let P := fun i : {i // keep i} =>
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U btag S) i.val
      let β := allocatedFrozenIntegerFullChart B U btag o poly hm c a v sample keep fixed
      ∀ {q : ℕ} (Q : ResidueBoxSlice P q) (_hq : 0 < q)
        (hlen : ∀ i, 0 < Q.length i)
        (_hQ : ∀ i, Real.exp (-p) * (P i : ℝ) ≤ Q.length i)
        (_hP : ∀ i, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (P i : ℝ))
        (V : D.Niltest (fun _ : {i // keep i} => 1))
        (W : E.Niltest (fun _ : {i // keep i} => 1))
        (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p) (_hWnorm : W.normBound ≤ 1)
        (η : LG →ₗ[ℚ] ℚ) (θ : MG →ₗ[ℚ] ℚ)
        (_hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
        (_hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
        (_hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          V.observable (z • x) = CircleFourier.character
            ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x)
        (_hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
          W.observable (z • x) = CircleFourier.character
            ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x)
        (_hK : (Fintype.card {i // keep i} : ℝ) ≤ p)
        (_hbias : Real.exp (-p) ≤ ‖(Q.fullSliceLaw hlen).complexMean (fun t =>
          star (twist.eval N poly (integerSampledSpatial β t.val)) *
            (V.eval t.val * W.eval t.val))‖),
        (pi (pairModels D E)).filtration.ControlledSymbolFactorization bFixed ωFixed hFixed
          (pairFrequency η θ) (fun k => (P k : ℝ))
          (pairOrbitSymbol D E V.orbit W.orbit bFixed ωFixed hFixed)
          ((fixedAdaptedSymbolTransferInput pGeo
            (pGeo + p + ((p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23))) + A) ^ A) := by
  obtain ⟨C, A, hC, hA, hstep⟩ :=
    exists_native_twist_variation_slice_fixed_basis_step_drop s hs
  refine ⟨C, A, hC, hA, ?_⟩
  intro LG MG _ _ _ _ d e _ _ _ _ _ _ _ _ D E pGeo hpGeo hGeo
  obtain ⟨bFixed, ωFixed, hFixed, hforward, hinverse, hlocal⟩ := hstep D E hpGeo hGeo
  refine ⟨bFixed, ωFixed, hFixed, hforward, hinverse, ?_⟩
  intro m G X _ _ I Deck J _ _ n B _ U btag hbtag o R σ S hR hσ poly hm hpoly
    c a N hN τ ξ hτ hτ1 hξ v hv sample read hread hσ1 Cgeo hCgeo hchart hsmall
    periodCap coverCap L twist p hp hperiod hvariationBound keep _ fixed hfixed
  dsimp only
  intro q Q hq hlen hQ hP V W hV hW hWnorm η θ hηheight hθheight hη hθ hK hbias
  have hsmallOne : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 :=
    fun j => (hsmall j).trans (by norm_num)
  apply hlocal Q hq hlen hp hQ hP (mul_pos twist.modulus_pos twist.cover_pos)
    hperiod (fun t => twist.eval N poly (integerSampledSpatial
      (allocatedFrozenIntegerFullChart B U btag o poly hm c a v sample keep fixed) t.val))
    (fun _ => twist.norm_eval_le N poly _)
    (by positivity) hvariationBound ?_
    V W hV hW hWnorm η θ hηheight hθheight hη hθ hK hbias
  intro x y hres δ hδ hcell
  exact hread.frozen_twist_variation B U btag hbtag o S hR hσ poly hm hpoly
    c a N hN hτ hτ1 hξ v hv sample read hσ1 Cgeo hCgeo hchart hsmallOne
    twist keep fixed hfixed x y hres hδ hcell

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairFamily
namespace OAI

universe u

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial RationalFilteredNilmanifold
open scoped BigOperators NNReal Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
  {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]

variable {B}

variable {LG MG : Type u} [LieRing LG] [LieAlgebra ℚ LG]
  [LieRing MG] [LieAlgebra ℚ MG] {s d e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
  [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]

theorem exists_allocatedFrozenTaggedPairInput_fixed_basis_step_drop
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ C A : ℕ, 2 ≤ C ∧ 2 ≤ A ∧ ∀
      {LG MG : Type u} [LieRing LG] [LieAlgebra ℚ LG] [LieRing MG] [LieAlgebra ℚ MG]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
      [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
      (D : RationalFilteredNilmanifold LG s d) (E : RationalFilteredNilmanifold MG s e)
      {pGeo : ℝ} (_hpGeo : 0 ≤ pGeo)
      (_hGeo : (pi (pairModels D E)).GeometryComplexityLE pGeo),
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra LG MG))) ℚ (PairAlgebra LG MG))
        (ω : Fin (finrank ℚ (PairAlgebra LG MG)) → ℕ)
        (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (b '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (b i) j) ≤ pGeo + 1) ∧
        (∀ i j, rationalLogHeight (b.repr ((pi (pairModels D E)).basis i) j) ≤ (pGeo + 3) ^ 5) ∧
      ∀ {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
        {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
        {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
        (Γ : AllocatedFrozenTaggedContext (G := G) (X := X) (J := J) B)
        (Deck : Fin m → Type*) (keep : LayerSamplerVariables G I n B → Prop)
        [Nonempty {i // keep i}] {p : ℝ}
        (input : AllocatedFrozenTaggedPairInput Γ Deck keep D E p)
        (_hP : ∀ i, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (Γ.sides keep i : ℝ)),
        (pi (pairModels D E)).filtration.ControlledSymbolFactorization b ω hF
          (pairFrequency input.η input.θ) (fun k => (Γ.sides keep k : ℝ))
          (pairOrbitSymbol D E input.V.orbit input.W.orbit b ω hF)
          ((fixedAdaptedSymbolTransferInput pGeo
            (pGeo + p + ((p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23))) + A) ^ A) := by
  obtain ⟨C, A, hC, hA, hstep⟩ :=
    exists_allocated_frozen_tagged_twist_fixed_basis_step_drop s hs
  refine ⟨C, A, hC, hA, ?_⟩
  intro LG MG _ _ _ _ d e _ _ _ _ _ _ _ _ D E pGeo hpGeo hGeo
  obtain ⟨b, ω, hF, hforward, hinverse, hlocal⟩ := hstep D E hpGeo hGeo
  refine ⟨b, ω, hF, hforward, hinverse, ?_⟩
  intro m G X _ _ I J _ _ n B _ Γ Deck keep _ p input hP
  exact hlocal B Γ.U Γ.btag Γ.hbtag Γ.o Γ.S Γ.hR Γ.hσ Γ.poly Γ.hm Γ.hpoly
    input.c input.a Γ.N Γ.hN Γ.hτ Γ.hτ1 Γ.hξ input.v input.hv input.sample
    input.read input.hread Γ.hσ1 Γ.Cgeo Γ.hCgeo Γ.hchart Γ.hsmall input.twist
    input.hp input.hperiod input.hvariationBound keep input.fixed input.hfixed
    input.Q input.hq input.hlen input.hQ hP input.V input.W input.hV input.hW
    input.hWnorm input.η input.θ input.hηheight input.hθheight input.hη input.hθ
    input.hK input.hbias

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularCanonicalDetectorAmbientConsumer
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin 1)))
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V Cforward : Fin m → ℝ≥0) (Ksource : ℝ≥0)

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

structure PreparedModularDetectorAmbientBounds
    (r : PreparedModularCanonicalDetectorResources ℝ) (P D pDetect : ℝ) : Prop where
  hPbox : 0 ≤ r.Pbox
  hVlog : 0 ≤ r.Vlog
  hNlog : 0 ≤ r.Nlog
  hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp r.Pbox
  hvolume : allocatedFullGridNaturalVolume B U b S rowSets ≤ Real.exp r.Vlog
  hnormalizer : ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤ Real.exp r.Nlog
  sourceNumerics : AllocatedSourceNumerics B U b S C V r.Pbox
  hbaseAmbient : 0 ≤ r.baseAmbient
  hvbase : r.Vlog ≤ r.baseAmbient
  hnbase : r.Nlog ≤ r.baseAmbient
  hsites : (Fintype.card (Finset (Fin 1)) : ℝ) ≤ r.baseAmbient
  haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ r.baseAmbient
  hKbase : (Ksource : ℝ) ≤ Real.exp r.baseAmbient
  hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp r.baseAmbient
  hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp r.baseAmbient
  hrowsAmbient : ((∑ j, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp r.baseAmbient
  houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ) ≤ r.baseAmbient
  hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp r.baseAmbient
  hQgrid : ∀ a : {a // grid a},
    8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤
        (Real.toNNReal (8 * (D + 1)) : ℝ)
  hDg : 0 ≤ r.Dg
  hvg : 0 ≤ r.v
  hwg : 0 ≤ r.w
  hcube : (Fintype.card (Fin 1) : ℝ) ≤ r.Dg
  hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ r.Dg
  hrowsD : ∀ j, ((rowSets j).card : ℝ) ≤ r.Dg
  htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ r.Dg
  hblocks : ∀ a, (Fintype.card (B a) : ℝ) ≤ r.Dg
  hRv : ∀ j, R j ≤ Real.exp r.v
  hRiGrid : ∀ j, (R j)⁻¹ ≤ Real.exp r.v
  hδw : pDetect + 1 ≤ r.w
  hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
    (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp r.v
  haxesGrid : (Fintype.card {a // grid a} : ℝ) ≤ r.Dg
  hfullAxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ r.Dg
  hfullOutputs : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ) ≤ r.Dg
  hambientCount : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ r.Dg
  hprofileBudget : (probabilityProfileLipschitz : ℝ) ≤ r.Dg
  hBanalytic : 0 ≤ r.Banalytic
  hDanalytic : r.Dg ≤ r.Banalytic
  hcutoffAnalytic : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp r.Banalytic
  hcoordAnalytic : ((Ksource * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤
    Real.exp r.Banalytic
  hgridAnalytic : (Real.toNNReal (8 * (D + 1)) : ℝ) ≤ Real.exp r.Banalytic
  hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P
  hn : ∀ j, (n j : ℝ) ≤ P
  hcoeffEarly : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
    (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P
  hRiEarly : ∀ j, (R j)⁻¹ ≤ Real.exp P
  hVEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V Cforward : Fin m → ℝ≥0) (Ksource : ℝ≥0)

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

structure PreparedModularGeneralEarlyAnalyticBounds
    (r : PreparedModularCanonicalDetectorResources ℝ) (P D pDetect : ℝ) : Prop where
  hQgrid : ∀ a : {a // grid a},
    8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤
        (Real.toNNReal (8 * (D + 1)) : ℝ)
  hDg : 0 ≤ r.Dg
  hvg : 0 ≤ r.v
  hwg : 0 ≤ r.w
  hcube : (Fintype.card (Fin dim) : ℝ) ≤ r.Dg
  hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ r.Dg
  hrowsD : ∀ j, ((rowSets j).card : ℝ) ≤ r.Dg
  htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ r.Dg
  hblocks : ∀ a, (Fintype.card (B a) : ℝ) ≤ r.Dg
  hRv : ∀ j, R j ≤ Real.exp r.v
  hRiGrid : ∀ j, (R j)⁻¹ ≤ Real.exp r.v
  hδw : pDetect + 1 ≤ r.w
  hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
    (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp r.v
  haxesGrid : (Fintype.card {a // grid a} : ℝ) ≤ r.Dg
  hfullAxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ r.Dg
  hfullOutputs : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ) ≤ r.Dg
  hambientCount : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ r.Dg
  hprofileBudget : (probabilityProfileLipschitz : ℝ) ≤ r.Dg
  hBanalytic : 0 ≤ r.Banalytic
  hDanalytic : r.Dg ≤ r.Banalytic
  hcutoffAnalytic : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp r.Banalytic
  hcoordAnalytic : ((Ksource * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤
    Real.exp r.Banalytic
  hgridAnalytic : (Real.toNNReal (8 * (D + 1)) : ℝ) ≤ Real.exp r.Banalytic
  hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P
  hn : ∀ j, (n j : ℝ) ≤ P
  hcoeffEarly : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
    (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P
  hRiEarly : ∀ j, (R j)⁻¹ ≤ Real.exp P
  hVEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V Cforward : Fin m → ℝ≥0) (Ksource : ℝ≥0)

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))

structure PreparedModularGeneralLateAmbientBounds
    (r : PreparedModularCanonicalDetectorResources ℝ) : Prop where
  hPbox : 0 ≤ r.Pbox
  hVlog : 0 ≤ r.Vlog
  hNlog : 0 ≤ r.Nlog
  hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp r.Pbox
  hvolume : allocatedFullGridNaturalVolume B U b S rowSets ≤ Real.exp r.Vlog
  hnormalizer : ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤ Real.exp r.Nlog
  hbaseAmbient : 0 ≤ r.baseAmbient
  hvbase : r.Vlog ≤ r.baseAmbient
  hnbase : r.Nlog ≤ r.baseAmbient
  hsites : (Fintype.card (Finset (Fin dim)) : ℝ) ≤ r.baseAmbient
  haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ r.baseAmbient
  hKbase : (Ksource : ℝ) ≤ Real.exp r.baseAmbient
  hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp r.baseAmbient
  hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp r.baseAmbient
  hrowsAmbient : ((∑ j, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp r.baseAmbient
  houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ) ≤ r.baseAmbient
  hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp r.baseAmbient

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionedArbitraryFixedPatchFamily
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

noncomputable def allocatedNormalizedShearProblem
    {Y : Type*} {s d : ℕ} (keep : LayerSamplerVariables G I n B → Prop)
    (centerLift : ∀ j, U j)
    (hcenter : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun a => centerLift a.1))))
    (productive : Finset A.Path) {massThreshold cost scoreThreshold : ℝ}
    (hmass : massThreshold ≤ A.law.mass productive)
    (source : ∀ z : productive,
      AllocatedReturnedPatchSource (E := E) (A := A) keep centerLift z.val)
    (hshort : ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (patch : PolynomialPatch Y s d)
    [Fintype (PolynomialShearIndex patch.weight)]
    (localForm : productive → PolynomialSlots {i // keep i} d patch.weight)
    (q : productive → ℕ) (hq : ∀ z, 0 < q z)
    (slice : ∀ z, ResidueBoxSlice (fun i : {i // keep i} => A.sides i.val) (q z))
    (hlen : ∀ z i, 0 < (slice z).length i)
    (hlength : ∀ z i, Real.exp (-cost) * (A.sides i.val : ℝ) ≤ (slice z).length i)
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    (hscore : ∀ z, scoreThreshold ≤ ((slice z).fullSliceLaw (hlen z)).mean
      (fun u => (f ((source z).physical u.val) - lam) *
        (patch.form.shearTransformedSlots patch.weight_mono
          ((localForm z).loweringAt (fun i => (u.val i : ℝ)))).patchValue patch.kernel)) :
    AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le)
      (RationalTorus.trivialFiltration s) 0 1
      (fun _ y => (patch.shearObservable y : ℂ))
      (fun x => ((f x - lam : ℝ) : ℂ)) cost massThreshold scoreThreshold where
  productive := productive
  mass := hmass
  chart z := (source z).chart hcenter (slice z) (hq z) (hlen z) (hlength z)
  chart_path _ := rfl
  centerLift := centerLift
  chart_centerLift _ := rfl
  frozen_side _ := hshort
  candidate z := {
    orbit := (localForm z).shearPolynomialOrbit s patch.weight_le
    mark_on_slice := by
      intro u hu
      apply NilpotentLieBCHGroup.ext
      exact Subsingleton.elim _ _ }
  score z := by
    have hs := hscore z
    rw [patch.fullSliceLaw_shearObservable_score (localForm z) (slice z)
      (hq z) (hlen z) (fun u => f ((source z).physical u)) lam] at hs
    exact hs

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeDirectMasterBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

structure PreparedUniformDegreeComparison
    {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    (s : ℕ) (D target Pk Prho Ptail pDetect : ℝ) where
  ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0
  hρ : ∀ partition, 0 < ρ partition
  hρ1 : ∀ partition, ρ partition ≤ 1
  hρlog : ∀ partition, (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho
  t : ℝ
  ht : 0 < t
  htone : t ≤ 1
  htinv : t⁻¹ ≤ Real.exp Ptail
  hs : AllocatedAffineCoveredComparison.{0,0,0,0,0,0,0} (G := G) B
    (fun j : Fin m => (Subtype.val :
      boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) → Finset (Fin (s + 1))))
    (Real.exp (-(pDetect + 1)))
    (Real.exp (-(target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5))) ρ t htone

end Erdos3.VectorPolynomial

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
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable (α τ : ℝ)
variable {P : ℝ}

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

structure PreparedUniformDegreeDirectScalarBounds
    (m s nX nVars : ℕ) (Cdetect : ℕ)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius u pModel pSlice : ℝ) : Prop where
  master_nonneg : 0 ≤ Pmaster
  late : Pmaster ≤ Plate
  chart_master : Pchart ≤ Pmaster
  dimension_master : D ≤ Pmaster
  radius_master : pRadius ≤ Pmaster
  scale_late : Pscale ≤ Plate
  kernel_scale : Pk ≤ Pscale
  kernel_master : Pk ∈ Set.Icc 0 Pmaster
  stride_master : Qstride ∈ Set.Icc 0 Pmaster
  detect_master : allocatedModelTestLog u pModel ∈ Set.Icc 0 Pmaster
  ambient_master : (nX : ℝ) ≤ Pmaster
  u_master : u ∈ Set.Icc 0 Pmaster
  model_master : pModel ∈ Set.Icc 0 Pmaster
  slice_model : pSlice ≤ pModel
  count_model : (nVars : ℝ) ≤ Real.exp pModel
  rho_master : Prho ∈ Set.Icc 0 Pmaster
  target_master : target ∈ Set.Icc 0 Pmaster
  gain_master : pGain ∈ Set.Icc 0 Pmaster
  coarse_master : pGain + 32 ≤ Pmaster
  coarse_lower : pGain + 32 ≤ coarseTarget
  coarse_late : coarseTarget ≤ Plate
  physical_master : Pphysical ∈ Set.Icc 0 Pmaster
  degree_physical : ((m + 1 : ℕ) : ℝ) ≤ Pphysical
  detector_physical : ((s + 2 : ℕ) : ℝ) ≤ Pphysical
  variables_physical : (nVars : ℝ) ≤ Pphysical
  ambient_physical : (nX : ℝ) ≤ Pphysical
  kernel_physical : Pk ≤ Pphysical
  stride_physical : Qstride ≤ Pphysical
  gain_log : slicedDetectionGainLog s Cdetect nVars
    (allocatedModelTestLog u pModel) (allocatedModelTestLog u pModel)
    (2 * u + 4 * pModel + 7) ≤ pGain
  precision : pGain + 32 + coefficientErrorSpatialLog Pphysical + 8 ≤ target
  xi_late : 2 * (spatialPrimitiveEnvelope Pphysical coarseTarget 0 +
    spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical coarseTarget 0)) + 4 ≤ Plate

end Consumer
end Erdos3.VectorPolynomial

end

end OAI
end


