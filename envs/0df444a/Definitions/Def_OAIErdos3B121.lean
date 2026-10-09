-- Prove2me | Definitions.Def_OAIErdos3B121
-- name    : OAIErdos3B121
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T04:55:52.476743+00:00
-- url     : https://prove2.me/theorems/8328be20-5ab1-4521-bef0-48f82a42bf22
-- title:
--   OpenAI Erdős-3 split, definitions bundle 122 of 132
-- statement:
--   Definitions bundle 122 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B120`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 122 available.
--
--   Modules: `OAI.Erdos3.MultidegreeLieFiltration.compareRealOrbit`, `OAI.Erdos3.MultidegreeLieFiltration.compareRealOrbit_projections`, `OAI.Erdos3.MultidegreeLieFiltration.compareRealOrbit_zero`, `OAI.Erdos3.MultidegreeLieFiltration.polarizeRealOrbit`, `OAI.Erdos3.MultidegreeLieFiltration.polarizeRealOrbit_permute`, `OAI.Erdos3.MultidegreeLieFiltration.realPolarizedLog_eval_permute`, `OAI.Erdos3.NativeMultidegreeNilcharacter.casesOn`, `OAI.Erdos3.NativeMultidegreeNilcharacter.constOne`, `OAI.Erdos3.NativeMultidegreeNilcharacter.constOne_eval`, `OAI.Erdos3.NativeMultidegreeNilcharacter.constOne_evalCyclic`, `OAI.Erdos3.NativeMultidegreeNilcharacter.eval`, `OAI.Erdos3.NativeMultidegreeNilcharacter.evalCyclic`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mono`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mono_eval`, `OAI.Erdos3.NativeMultidegreeNilcharacter.norm_eval`, `OAI.Erdos3.NativeMultidegreeNilcharacter.unit_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.top_realSubgroup_commute`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.withLattice`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.withLattice_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonSpaceOrbit_projections`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_normalized_comparison_orbit`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.constOne`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.exists_invariant`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.frozenCover`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.mono`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.onSublattice`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.pullback`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.recOn`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_source_unit_cover`, `OAI.Erdos3.RationalTorus.trivialMultidegreeFiltration`, `OAI.Erdos3.RationalTorus.trivialMultidegreeStructure`, `OAI.Erdos3.RationalTorus.trivialMultidegreeStructure_complexity`, `OAI.Erdos3.VectorPolynomial.arrayCoordinateTorus_coefficientLayer`, `OAI.Erdos3.VectorPolynomial.boundedCoefficientExponent_card_le_geometricSiteBudget`, `OAI.Erdos3.VectorPolynomial.boundedSiteMatrix_height_of_exp`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientCoverLift`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientCoverLift_measurable`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientCoverLift_projection`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDeckSample`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDeckSample_coordinate`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDeckSample_measurable`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDeckSample_projection`, `OAI.Erdos3.VectorPolynomial.centeredAffineCoefficientArray`, `OAI.Erdos3.VectorPolynomial.centeredAffineCoefficientTorus`, `OAI.Erdos3.VectorPolynomial.coefficientArray_factor_of_bounded_site`, `OAI.Erdos3.VectorPolynomial.coefficientArray_factor_to_bounded_site`, `OAI.Erdos3.VectorPolynomial.coefficientBooleanJetTorusMap_layer`, `OAI.Erdos3.VectorPolynomial.coefficientCover_integrable`, `OAI.Erdos3.VectorPolynomial.coefficientCover_integral`, `OAI.Erdos3.VectorPolynomial.coefficientCover_measurePreserving`, `OAI.Erdos3.VectorPolynomial.coefficientDeckJetMap`, `OAI.Erdos3.VectorPolynomial.coefficientEvaluationTorus`, `OAI.Erdos3.VectorPolynomial.coefficientEvaluationTorus_constant`, `OAI.Erdos3.VectorPolynomial.coefficientEvaluationTorus_continuous`, `OAI.Erdos3.VectorPolynomial.coefficientEvaluationTorus_mk`, `OAI.Erdos3.VectorPolynomial.coefficientResidualArray`, `OAI.Erdos3.VectorPolynomial.coefficientResidualArray_evaluation`, `OAI.Erdos3.VectorPolynomial.coefficientResidualArray_factor_iff`, `OAI.Erdos3.VectorPolynomial.coefficientResidualArray_preserves_lattice`, `OAI.Erdos3.VectorPolynomial.coefficientRowPolynomial_centered_affine_eval`, `OAI.Erdos3.VectorPolynomial.constantCoefficientTorusMap`, `OAI.Erdos3.VectorPolynomial.constantCoefficientTorusMap_continuous`, `OAI.Erdos3.VectorPolynomial.constantCoefficientTorusMap_mk`, `OAI.Erdos3.VectorPolynomial.constantCoefficientTorusMap_nonconstant`, `OAI.Erdos3.VectorPolynomial.cubeSites_card_le_geometricSiteBudget`, `OAI.Erdos3.VectorPolynomial.degree_mul_le_geometricSiteBudget`, `OAI.Erdos3.VectorPolynomial.euclideanCoefficientJetMap_apply`, `OAI.Erdos3.VectorPolynomial.exists_covered_coefficient_density`, `OAI.Erdos3.VectorPolynomial.exponentialSiteHeight`, `OAI.Erdos3.VectorPolynomial.exponentialSiteHeight_le`, `OAI.Erdos3.VectorPolynomial.exponentialSiteHeight_pos`, `OAI.Erdos3.VectorPolynomial.geometricSiteBudget`, `OAI.Erdos3.VectorPolynomial.geometricSiteBudget_nonneg`, `OAI.Erdos3.allocatedArrayCenters`, `OAI.Erdos3.allocatedArrayColumns_chart`, `OAI.Erdos3.allocatedArrayProfiles_bound`, `OAI.Erdos3.allocatedArraySupported_iff_rows`, `OAI.Erdos3.allocatedArrayWidths`, `OAI.Erdos3.allocatedArrayWidths_floor`, `OAI.Erdos3.allocatedArrayWidths_pos`, `OAI.Erdos3.allocatedProfile_inverse_exp_bounds`, `OAI.Erdos3.allocatedProfile_inverse_power_bounds`, `OAI.Erdos3.allocatedProjectionPMFs`, `OAI.Erdos3.allocatedScaleLog`, `OAI.Erdos3.allocatedWidthFloor`, `OAI.Erdos3.allocatedWidthFloor_inverse_exp_bound`, `OAI.Erdos3.allocatedWidthFloor_inverse_power_bound`, `OAI.Erdos3.allocatedWidthFloor_pos`, `OAI.Erdos3.arrayCoordinateTorus_integerMatrix`, `OAI.Erdos3.constantIntegerInterpolation_power_bounds`, `OAI.Erdos3.euclideanSubspaceTorusMeasurableEquiv`, `OAI.Erdos3.euclideanSubspaceTorusMeasure`, `OAI.Erdos3.euclideanSubspaceTorusMeasure_invariant`, `OAI.Erdos3.euclideanSubspaceTorusMeasure_mass`, `OAI.Erdos3.euclideanSubspaceTorusMeasure_probability`, `OAI.Erdos3.exists_normalized_chart_lift`, `OAI.Erdos3.exists_uniform_invariantVertical_cost`, `OAI.Erdos3.frozen_quotient_map_smul`, `OAI.Erdos3.integerInterpolationLogEnvelope`, `OAI.Erdos3.integerPolynomialInterpolation`, `OAI.Erdos3.integerPolynomialInterpolationCap`, `OAI.Erdos3.integerPolynomialInterpolationLip`, `OAI.Erdos3.integerPolynomialInterpolation_exp_bounds`, `OAI.Erdos3.integerPolynomialInterpolation_power_bounds`, `OAI.Erdos3.integerPolynomialInterpolation_spec`, `OAI.Erdos3.invariantVerticalBudget`, `OAI.Erdos3.normalizedCoverLift`, `OAI.Erdos3.normalizedCoverLift_continuous`, `OAI.Erdos3.normalizedCoverLift_projection`, `OAI.Erdos3.normalizedLatticeQuotient_eq_of_sub_mem`, `OAI.Erdos3.normalizedLatticeRepresentative`, `OAI.Erdos3.normalizedLatticeRepresentative_continuous`, `OAI.Erdos3.normalizedLatticeRepresentative_mk`, `OAI.Erdos3.principalAxisInterpolation_power_bounds`, `OAI.Erdos3.standardLatticeCoordinates_card`, `OAI.Erdos3.subspaceArrayIntegerLattice_closed`, `OAI.Erdos3.tailAxisInterpolation`, `OAI.Erdos3.tailAxisInterpolationCap`, `OAI.Erdos3.tailAxisInterpolationLip`, `OAI.Erdos3.tailAxisInterpolation_power_bounds`, `OAI.Erdos3.tailAxisInterpolation_spec`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B044
import Definitions.Def_OAIErdos3B119

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CoefficientEvaluationTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def constantCoefficientTorusMap {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    CoefficientTorus (K := Empty) U →+ CoefficientTorus (K := K) U :=
  QuotientAddGroup.map (coefficientIntegerLattice U) (coefficientIntegerLattice U)
    (constantCoefficientArray U).toAddMonoidHom
    (constantCoefficientArray_preserves_lattice U)

noncomputable def coefficientEvaluationTorus {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) :
    CoefficientTorus (K := K) U →+ CoefficientTorus (K := Empty) U :=
  QuotientAddGroup.map (coefficientIntegerLattice U) (coefficientIntegerLattice U)
    (coefficientEvaluationArray U t).toAddMonoidHom
    (coefficientEvaluationArray_preserves_lattice U t)

theorem constantCoefficientTorusMap_mk {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (x : CoefficientArray (K := Empty) U) :
    constantCoefficientTorusMap (K := K) U (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) =
      QuotientAddGroup.mk' (coefficientIntegerLattice U) (constantCoefficientArray U x) := rfl

theorem coefficientEvaluationTorus_mk {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) (x : CoefficientArray (K := K) U) :
    coefficientEvaluationTorus U t (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) =
      QuotientAddGroup.mk' (coefficientIntegerLattice U) (coefficientEvaluationArray U t x) := rfl

theorem coefficientEvaluationTorus_constant {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (y : CoefficientTorus (K := Empty) U) :
    coefficientEvaluationTorus U t (constantCoefficientTorusMap U y) = y := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) y
  rw [constantCoefficientTorusMap_mk, coefficientEvaluationTorus_mk,
    coefficientEvaluationArray_constant]

theorem constantCoefficientTorusMap_continuous {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    Continuous (constantCoefficientTorusMap (K := K) U) := by
  apply (QuotientAddGroup.isQuotientMap_mk (coefficientIntegerLattice U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (constantCoefficientArray U).continuous_of_finiteDimensional

theorem coefficientEvaluationTorus_continuous {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) :
    Continuous (coefficientEvaluationTorus U t) := by
  apply (QuotientAddGroup.isQuotientMap_mk (coefficientIntegerLattice U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (coefficientEvaluationArray U t).continuous_of_finiteDimensional

theorem constantCoefficientTorusMap_nonconstant {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (y : CoefficientTorus (K := Empty) U)
    (s : CoefficientSlot K m) (hs : s.2.val ≠ 0) :
    coefficientCoordinateTorus U (constantCoefficientTorusMap U y) s = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) y
  rw [constantCoefficientTorusMap_mk, coefficientCoordinateTorus_mk]
  have hzero : (fun _ : Unit => constantCoefficientArray (K := K) U x s) = 0 := by
    funext u
    simp [constantCoefficientArray, hs]
  rw [hzero, map_zero]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CenteredAffineCoefficient
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {K V : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (p j) d ∈ U j)

noncomputable def centeredAffineCoefficientArray (center : ∀ j, U j) (frame : Option K → V → ℝ) :
    CoefficientArray (K := K) U :=
  affineSampleCoefficientArray U p hm frame - constantCoefficientArray U (fun s => center s.1)

noncomputable def centeredAffineCoefficientTorus (center : ∀ j, U j) (frame : Option K → V → ℝ) :
    CoefficientTorus (K := K) U :=
  QuotientAddGroup.mk' (coefficientIntegerLattice U) (centeredAffineCoefficientArray U p hm center frame)

theorem coefficientRowPolynomial_centered_affine_eval
    (hp : ∀ j, DegreeLE (1 : V → ℕ) (j.val + 1) (p j))
    (center : ∀ j, U j) (frame : Option K → V → ℝ) (j : Fin m) (i : J j) (x : K → ℝ) :
    MvPolynomial.eval x
        (coefficientRowPolynomial U (centeredAffineCoefficientArray U p hm center frame) j i) =
      eval (fun v => frame none v + ∑ k, frame (some k) v * x k) (p j) i - (center j).val i := by
  rw [centeredAffineCoefficientArray, coefficientRowPolynomial_sub, map_sub,
    coefficientRowPolynomial_constant, MvPolynomial.eval_C,
    coefficientRowPolynomial_affine_eval U p hp hm]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortAxis
namespace OAI

section

namespace Erdos3

noncomputable def tailAxisInterpolation {V : Type*} (T : V → ℝ) (K L s : ℕ) (ε : ℝ)
    (e : V →₀ ℕ) : ℝ → ℝ :=
  if L^(s+1) < K then normalizedIntegerInterpolation K 0 (ε / monomialScale T e)
  else integerMassTent K 0

noncomputable def tailAxisInterpolationCap (L s : ℕ) (ε : ℝ) : ℝ :=
  max (2 * (L : ℝ)^s / ε) ((L : ℝ)^(s+1))

noncomputable def tailAxisInterpolationLip (L s : ℕ) (ε : ℝ) : ℝ :=
  max (2 * (probabilityProfileLipschitz : ℝ) * ((L : ℝ)^s)^2 / ε^2)
    (2 * ((L : ℝ)^(s+1))^2)

theorem tailAxisInterpolation_spec {V : Type*} (T : V → ℝ) (hT : ∀ v, 0 < T v)
    (K L s : ℕ) (hK : 0 < K) (hL : 0 < L) (hTL : ∀ v, T v ≤ L) (ε : ℝ) (hε : 0 < ε)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)
    (e : V →₀ ℕ) (he : e.sum (fun _ n => n) ≤ s) :
    IsIntegerMassInterpolation K (integerAxisTailPMF T hT K L s hK hL hTL ε hε hεL e he)
      (tailAxisInterpolationCap L s ε) (tailAxisInterpolationLip L s ε)
      (tailAxisInterpolation T K L s ε e) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hS := monomialScale_pos T hT e
  have hSL := monomialScale_le_uniform_pow T (fun v => (hT v).le)
    (show (1 : ℝ) ≤ L by exact_mod_cast hL) hTL e he
  by_cases ha : L^(s+1) < K
  · simp only [integerAxisTailPMF, tailAxisInterpolation, ha, ↓reduceDIte, ↓reduceIte]
    apply (normalizedIntegerInterpolation_spec K 0 (ε / monomialScale T e) hKr
      (div_pos hε hS) (integerAxisTail_width T hT hL hTL hε hεL e he ha)).mono
    · apply le_trans _ (le_max_left _ _)
      calc
        2 / (ε / monomialScale T e) = 2 * monomialScale T e / ε := by field_simp
        _ ≤ 2 * (L : ℝ)^s / ε := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hSL (by norm_num)) hε.le
    · apply le_trans _ (le_max_left _ _)
      calc
        2 * (probabilityProfileLipschitz : ℝ) / (ε / monomialScale T e)^2 =
            2 * (probabilityProfileLipschitz : ℝ) * (monomialScale T e)^2 / ε^2 := by field_simp
        _ ≤ 2 * (probabilityProfileLipschitz : ℝ) * ((L : ℝ)^s)^2 / ε^2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hS.le hSL 2) (by positivity)) (sq_nonneg ε)
  · have hbound : (K : ℝ) ≤ (L : ℝ)^(s+1) := by exact_mod_cast (Nat.le_of_not_gt ha)
    simp only [integerAxisTailPMF, tailAxisInterpolation, ha, ↓reduceDIte, ↓reduceIte]
    apply (integerMassTent_spec K hKr 0).mono
    · exact hbound.trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hKr.le hbound 2) (by norm_num)).trans
        (le_max_right _ _)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (Pz : Fin n → Finset J) (j₀ : J) (h L s : ℕ) (hh : 0 < h) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 1 ≤ T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)
variable (hgap : ∀ i, L ^ h < basisAxisScale b i →
  (principalSamplingGapRatio (principalProfileSize R (Pz i).card) * L) ^ h ≤ basisAxisScale b i)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J) * L)

noncomputable def allocatedProjectionPMFs : Fin n → J → PMF ℤ :=
  fun i => allocatedIntegerPolynomialCoordinatePMF (Pz i) j₀ h (basisAxisScale b i) L s
    hh (basisAxisScale_pos b i) hL T (fun v => lt_of_lt_of_le zero_lt_one (hT v)) hTL e he
    R σ hR hσ (hgap i) hεL

local notation "intLaws" => allocatedProjectionPMFs W b Pz j₀ h L s hh hL T hT hTL e he R σ hR hσ hgap hεL

variable (Pc : I → Finset J)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def allocatedArrayCenters {I J V : Type*} (e : J → V →₀ ℕ) (T : V → ℝ)
    (Pc : I → Finset J) (R : ℝ) (i : I) (j : J) : ℝ :=
  coefficientProfileCenter (Pc i) (principalProfileSize R (Pc i).card) j / monomialScale T (e j)

noncomputable def allocatedArrayWidths {I J V : Type*} [Fintype J] (e : J → V →₀ ℕ) (T : V → ℝ)
    (Pc : I → Finset J) (j₀ : J) (R σ : ℝ) (i : I) (j : J) : ℝ :=
  coefficientProfileWidth (Pc i) j₀ (R / 4) (principalProfileSize R (Pc i).card)
    (tailProfileSize R σ (Fintype.card J)) j / monomialScale T (e j)

theorem allocatedArrayWidths_pos {I J V : Type*} [Fintype J] (e : J → V →₀ ℕ) (T : V → ℝ)
    (hT : ∀ v, 0 < T v) (Pc : I → Finset J) (j₀ : J) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ)
    (i : I) (j : J) : 0 < allocatedArrayWidths e T Pc j₀ R σ i j :=
  div_pos (continuousPolynomialDensity_width_pos (Pc i) j₀ hR hσ j) (monomialScale_pos T hT (e j))

theorem allocatedArrayProfiles_bound {I J V : Type*} [Fintype J] (e : J → V →₀ ℕ) (T : V → ℝ)
    (hT : ∀ v, 1 ≤ T v) (Pc : I → Finset J) (j₀ : J) (hc₀ : ∀ i, j₀ ∉ Pc i)
    {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (i : I) (j : J) :
    |allocatedArrayCenters e T Pc R i j| + allocatedArrayWidths e T Pc j₀ R σ i j ≤ R := by
  apply scaledProfile_div_bound (continuousPolynomialDensity_width_pos (Pc i) j₀ hR hσ j).le
    (one_le_monomialScale T hT (e j))
  exact (allocatedProfile_term_bound (Pc i) j₀ (hc₀ i) hR hσ hσ1 j).trans (by linarith)

theorem allocatedArraySupported_iff_rows {I Z J V : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (Pc : I → Finset J) (j₀ : J) (R σ : ℝ)
    (p : Z → J → PMF ℤ) (x : (I → J → ℝ) × (Z → J → ℤ)) :
    mixedArraySupported (allocatedArrayCenters e T Pc R) (allocatedArrayWidths e T Pc j₀ R σ) p x ↔
      (∀ i, continuousPolynomialDensity e T (Pc i) j₀ R σ (x.1 i) ≠ 0) ∧
      (∀ z j, x.2 z j ∈ (p z j).support) :=
  mixedArraySupported_iff_rows _ _ _ _

end Erdos3

end

section

namespace Erdos3

open Module Submodule

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (Pz : Fin n → Finset J) (j₀ : J) (h L s : ℕ) (hh : 0 < h) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 1 ≤ T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)
variable (hgap : ∀ i, L ^ h < basisAxisScale b i →
  (principalSamplingGapRatio (principalProfileSize R (Pz i).card) * L) ^ h ≤ basisAxisScale b i)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J) * L)
variable (Pc : I → Finset J)

local notation "intLaws" => allocatedProjectionPMFs W b Pz j₀ h L s hh hL T hT hTL e he R σ hR hσ hgap hεL

theorem allocatedArrayColumns_chart (o : OrthonormalBasis I ℝ W)
    (hc₀ : ∀ i, j₀ ∉ Pc i) (hz₀ : ∀ i, j₀ ∉ Pz i) (he₀ : e j₀ = 0) (hσ1 : σ ≤ 1)
    (hprincipal : ∀ i j, j ∈ Pz i → monomialScale T (e j) =
      (integerAxisSideLength h (basisAxisScale b i) L (principalProfileSize R (Pz i).card) : ℝ) ^ h)
    {C : ℝ} (hC : 0 ≤ C)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    (j : J) (x : (I → ℝ) × (Fin n → ℤ))
    (hx : mixedCoefficientDensity (fun i => allocatedArrayCenters e T Pc R i j)
      (fun i => allocatedArrayWidths e T Pc j₀ R σ i j) (fun i => intLaws i j) x ≠ 0) :
    normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D := by
  apply mixedCoefficient_small_support W b o hC hR.le hchart hsmall _ _
    (fun i => allocatedArrayWidths_pos e T (fun v => lt_of_lt_of_le zero_lt_one (hT v)) Pc j₀ hR hσ i j)
    (fun i => allocatedArrayProfiles_bound e T hT Pc j₀ hc₀ hR hσ hσ1 i j) _ _ x hx
  intro i k hk
  apply scaledAbs_le_of_bound (one_le_monomialScale T hT (e j))
  exact (allocatedIntegerCoefficient_bound (Pz i) j₀ h (basisAxisScale b i) L s hh
    (basisAxisScale_pos b i) hL T (fun v => lt_of_lt_of_le zero_lt_one (hT v)) hTL e he
    R σ hR hσ hσ1 (hgap i) hεL (hz₀ i) he₀ (hprincipal i) j hk).trans (by linarith)

end Erdos3

end

section

namespace Erdos3

noncomputable def allocatedWidthFloor (R σ : ℝ) (L s a : ℕ) : ℝ :=
  min (R / 4) (min (principalProfileSize R a / 2) (tailProfileSize R σ a)) / (L : ℝ)^s

theorem allocatedWidthFloor_pos {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ)
    {L : ℕ} (hL : 0 < L) (s a : ℕ) : 0 < allocatedWidthFloor R σ L s a := by
  unfold allocatedWidthFloor
  exact div_pos (lt_min (by positivity)
    (lt_min (div_pos (principalProfileSize_pos hR a) (by norm_num)) (tailProfileSize_pos hR hσ a)))
    (pow_pos (Nat.cast_pos.mpr hL) _)

theorem allocatedArrayWidths_floor {I J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v)
    (Pc : I → Finset J) (j₀ : J) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ)
    {L s : ℕ} (hL : 0 < L) (hTL : ∀ v, T v ≤ L)
    (he : ∀ j, (e j).sum (fun _ n => n) ≤ s) (i : I) (j : J) :
    allocatedWidthFloor R σ L s (Fintype.card J) ≤ allocatedArrayWidths e T Pc j₀ R σ i j := by
  classical
  let a := min (R / 4)
    (min (principalProfileSize R (Fintype.card J) / 2) (tailProfileSize R σ (Fintype.card J)))
  have ha : 0 ≤ a := le_of_lt (lt_min (by positivity)
    (lt_min (div_pos (principalProfileSize_pos hR _) (by norm_num)) (tailProfileSize_pos hR hσ _)))
  have hprincipal : principalProfileSize R (Fintype.card J) ≤ principalProfileSize R (Pc i).card := by
    unfold principalProfileSize
    apply div_le_div_of_nonneg_left hR.le (by positivity)
    gcongr
    exact_mod_cast (Pc i).card_le_univ
  have haWidth : a ≤ coefficientProfileWidth (Pc i) j₀ (R / 4)
      (principalProfileSize R (Pc i).card) (tailProfileSize R σ (Fintype.card J)) j := by
    unfold coefficientProfileWidth
    split_ifs
    · exact min_le_left _ _
    · exact ((min_le_right _ _).trans (min_le_left _ _)).trans
        (div_le_div_of_nonneg_right hprincipal (by norm_num))
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hmono := monomialScale_le_uniform_pow T (fun v => (hT v).le)
    (by exact_mod_cast hL) hTL (e j) (he j)
  have hscale := monomialScale_pos T hT (e j)
  change a / (L : ℝ)^s ≤ coefficientProfileWidth (Pc i) j₀ (R / 4)
    (principalProfileSize R (Pc i).card) (tailProfileSize R σ (Fintype.card J)) j / monomialScale T (e j)
  exact (div_le_div_of_nonneg_left ha hscale hmono).trans
    (div_le_div_of_nonneg_right haWidth hscale.le)

end Erdos3

end

section

namespace Erdos3

theorem allocatedProfile_inverse_power_bounds (a : ℕ) {R σ X : ℝ}
    (hR : 0 < R) (hσ : 0 < σ) (hX : 8 ≤ X)
    (hRX : R⁻¹ ≤ X) (hσX : σ⁻¹ ≤ X) (haX : (a : ℝ) + 1 ≤ X) :
    (R / 4)⁻¹ ≤ X^2 ∧ (principalProfileSize R a)⁻¹ ≤ X^3 ∧
      (principalProfileSize R a / 2)⁻¹ ≤ X^4 ∧ (tailProfileSize R σ a)⁻¹ ≤ X^4 := by
  have hX0 : 0 ≤ X := by linarith
  have h2 : (2 : ℝ) ≤ X := by linarith
  have h4 : (4 : ℝ) ≤ X := by linarith
  have hp0 : 0 ≤ (principalProfileSize R a)⁻¹ := inv_nonneg.mpr (principalProfileSize_pos hR a).le
  have hprincipal : (principalProfileSize R a)⁻¹ ≤ X^3 := by
    unfold principalProfileSize
    rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ X * X * X := by gcongr
      _ = _ := by ring
  refine ⟨?_, hprincipal, ?_, ?_⟩
  · rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ X * X := by gcongr
      _ = _ := by ring
  · rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ X * X^3 := by gcongr
      _ = _ := by ring
  · unfold tailProfileSize
    rw [inv_div, div_eq_mul_inv, mul_inv_rev]
    calc
      _ ≤ X * X * (X * X) := by gcongr
      _ = _ := by ring

theorem allocatedWidthFloor_inverse_power_bound (L s m a : ℕ) (hs : s ≤ m)
    {R σ X : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hX : 8 ≤ X)
    (hRX : R⁻¹ ≤ X) (hσX : σ⁻¹ ≤ X) (haX : (a : ℝ) + 1 ≤ X) (hLX : (L : ℝ) ≤ X) :
    (allocatedWidthFloor R σ L s a)⁻¹ ≤ X^(m+4) := by
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 ≤ X := by linarith
  obtain ⟨hρ, _, hγ, hε⟩ := allocatedProfile_inverse_power_bounds a hR hσ hX hRX hσX haX
  have hmin : (min (R/4) (min (principalProfileSize R a / 2) (tailProfileSize R σ a)))⁻¹ ≤ X^4 :=
    inv_min_le_of_inv_le (hρ.trans (pow_le_pow_right₀ hX1 (by norm_num)))
      (inv_min_le_of_inv_le hγ hε)
  have hLs : (L : ℝ)^s ≤ X^m :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hLX s).trans (pow_le_pow_right₀ hX1 hs)
  have hγ0 := (principalProfileSize_pos hR a).le
  have hε0 := (tailProfileSize_pos hR hσ a).le
  have hmin0 : 0 ≤ (min (R/4) (min (principalProfileSize R a / 2) (tailProfileSize R σ a)))⁻¹ := by
    positivity
  rw [allocatedWidthFloor, inv_div, div_eq_mul_inv]
  calc
    _ ≤ X^m * X^4 := by gcongr
    _ = _ := (pow_add _ _ _).symm

end Erdos3

end

section

namespace Erdos3

theorem allocatedProfile_inverse_exp_bounds (a : ℕ) {R σ P : ℝ}
    (hP : 0 ≤ P) (hR : 0 < R) (hσ : 0 < σ)
    (hRP : R⁻¹ ≤ Real.exp P) (hσP : σ⁻¹ ≤ Real.exp P) (haP : (a : ℝ) ≤ P) :
    (R / 4)⁻¹ ≤ Real.exp (4 * (P + 8)) ∧
      (principalProfileSize R a)⁻¹ ≤ Real.exp (4 * (P + 8)) ∧
      (principalProfileSize R a / 2)⁻¹ ≤ Real.exp (4 * (P + 8)) ∧
      (tailProfileSize R σ a)⁻¹ ≤ Real.exp (4 * (P + 8)) := by
  let X := Real.exp (P + 8)
  have hPX : Real.exp P ≤ X := Real.exp_le_exp.mpr (by linarith)
  have hX : 8 ≤ X := by dsimp [X]; linarith [Real.add_one_le_exp (P+8)]
  have hX1 : 1 ≤ X := by linarith
  have haX : (a : ℝ) + 1 ≤ X :=
    (by linarith [Real.add_one_le_exp P] : (a : ℝ) + 1 ≤ Real.exp P).trans hPX
  obtain ⟨hρ, hγ, hγ2, hε⟩ := allocatedProfile_inverse_power_bounds a hR hσ hX
    (hRP.trans hPX) (hσP.trans hPX) haX
  have he : X^4 = Real.exp (4*(P+8)) := by simp only [X, ← Real.exp_nat_mul, Nat.cast_ofNat]
  rw [← he]
  exact ⟨hρ.trans (pow_le_pow_right₀ hX1 (by norm_num)),
    hγ.trans (pow_le_pow_right₀ hX1 (by norm_num)), hγ2, hε⟩

theorem allocatedWidthFloor_inverse_exp_bound (L s m a : ℕ) (hs : s ≤ m)
    {R σ P : ℝ} (hP : 0 ≤ P) (hR : 0 < R) (hσ : 0 < σ)
    (hRP : R⁻¹ ≤ Real.exp P) (hσP : σ⁻¹ ≤ Real.exp P)
    (haP : (a : ℝ) ≤ P) (hLP : (L : ℝ) ≤ Real.exp P) :
    (allocatedWidthFloor R σ L s a)⁻¹ ≤ Real.exp (((m : ℝ)+4)*(P+8)) := by
  let X := Real.exp (P+8)
  have hPX : Real.exp P ≤ X := Real.exp_le_exp.mpr (by linarith)
  have hX : 8 ≤ X := by dsimp [X]; linarith [Real.add_one_le_exp (P+8)]
  have haX : (a : ℝ)+1 ≤ X :=
    (by linarith [Real.add_one_le_exp P] : (a : ℝ)+1 ≤ Real.exp P).trans hPX
  have h := allocatedWidthFloor_inverse_power_bound L s m a hs hR hσ hX
    (hRP.trans hPX) (hσP.trans hPX) haX (hLP.trans hPX)
  simpa only [X, ← Real.exp_nat_mul, Nat.cast_add, Nat.cast_ofNat] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def allocatedScaleLog (P : ℝ) : ℝ := (1+P^2)*(5*P+49)

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialInterpolation
namespace OAI

section

namespace Erdos3

variable {J V : Type*} [Fintype J]

noncomputable def integerPolynomialInterpolation (P : Finset J) (j₀ : J) (h K L s : ℕ)
    (T : V → ℝ) (e : J → V →₀ ℕ) (ρ γ ε : ℝ) (j : J) : ℝ → ℝ := by
  classical
  exact if j = j₀ then constantIntegerInterpolation K ρ
    else if j ∈ P then principalAxisInterpolation h K L γ
    else tailAxisInterpolation T K L s ε (e j)

noncomputable def integerPolynomialInterpolationCap (h L s : ℕ) (ρ γ ε : ℝ) : ℝ :=
  max (constantIntegerInterpolationCap ρ)
    (max (principalAxisInterpolationCap h L γ) (tailAxisInterpolationCap L s ε))

noncomputable def integerPolynomialInterpolationLip (h L s : ℕ) (ρ γ ε : ℝ) : ℝ :=
  max (constantIntegerInterpolationLip ρ)
    (max (principalAxisInterpolationLip h L γ) (tailAxisInterpolationLip L s ε))

omit [Fintype J] in
theorem integerPolynomialInterpolation_spec (P : Finset J) (j₀ : J) (h K L s : ℕ)
    (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
    (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
    (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
    (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
    (hgap : L^h < K → (principalSamplingGapRatio γ * L)^h ≤ K)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L) (j : J) :
    IsIntegerMassInterpolation K
      (integerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he
        ρ γ ε hρ hγ hε hgap hεL j)
      (integerPolynomialInterpolationCap h L s ρ γ ε)
      (integerPolynomialInterpolationLip h L s ρ γ ε)
      (integerPolynomialInterpolation P j₀ h K L s T e ρ γ ε j) := by
  classical
  by_cases hj : j = j₀
  · simp only [integerPolynomialCoordinatePMF, integerPolynomialInterpolation, hj, ↓reduceIte]
    exact (constantIntegerInterpolation_spec K ρ (by exact_mod_cast hK) hρ).mono
      (le_max_left _ _) (le_max_left _ _)
  · by_cases hp : j ∈ P
    · simp only [integerPolynomialCoordinatePMF, integerPolynomialInterpolation, hj, hp, ↓reduceIte]
      exact (principalAxisInterpolation_spec h K L hh hK hL γ hγ hgap).mono
        ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))
    · simp only [integerPolynomialCoordinatePMF, integerPolynomialInterpolation, hj, hp, ↓reduceIte]
      exact (tailAxisInterpolation_spec T hT K L s hK hL hTL ε hε hεL (e j) (he j)).mono
        ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerInterpolationExpBounds
namespace OAI

section

namespace Erdos3

theorem constantIntegerInterpolation_power_bounds {X ρ : ℝ}
    (hX : 8 ≤ X) (hA : (probabilityProfileLipschitz : ℝ) ≤ X)
    (hρ : 0 < ρ) (hρX : ρ⁻¹ ≤ X) :
    constantIntegerInterpolationCap ρ ≤ X^3 ∧ constantIntegerInterpolationLip ρ ≤ X^7 := by
  have hX0 : 0 ≤ X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have h2 : (2 : ℝ) ≤ X := by linarith
  have hc : constantIntegerInterpolationCap ρ ≤ X^3 := by
    unfold constantIntegerInterpolationCap
    rw [div_eq_mul_inv]
    calc
      _ ≤ X * X * X := by gcongr
      _ = _ := by ring
  refine ⟨hc, ?_⟩
  unfold constantIntegerInterpolationLip
  apply max_le
  · have ht : 2 * (probabilityProfileLipschitz : ℝ) / ρ^2 ≤ X^4 := by
      rw [div_eq_mul_inv, ← inv_pow]
      calc
        _ ≤ X * X * X^2 := by gcongr
        _ = _ := by ring
    exact ht.trans (pow_le_pow_right₀ hX1 (by norm_num))
  · have hc0 : 0 ≤ constantIntegerInterpolationCap ρ := by
      unfold constantIntegerInterpolationCap
      positivity
    calc
      _ ≤ X * (X^3)^2 := by gcongr
      _ = _ := by ring

theorem principalAxisInterpolation_power_bounds (h L : ℕ) {X γ : ℝ}
    (hX : 8 ≤ X) (hA : (probabilityProfileLipschitz : ℝ) ≤ X)
    (hγ : 0 < γ) (hγX : γ⁻¹ ≤ X) (hL : (L : ℝ)^h ≤ X) :
    principalAxisInterpolationCap h L γ ≤ X^3 ∧ principalAxisInterpolationLip h L γ ≤ X^7 := by
  have hX0 : 0 ≤ X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have h2 : (2 : ℝ) ≤ X := by linarith
  have h4 : (4 : ℝ) ≤ X := by linarith
  have hX3 : X ≤ X^3 := by simpa only [pow_one] using (pow_le_pow_right₀ hX1 (show 1 ≤ 3 by norm_num))
  constructor
  · unfold principalAxisInterpolationCap
    apply max_le
    · rw [div_eq_mul_inv]
      calc
        _ ≤ X * X * X := by gcongr
        _ = _ := by ring
    · exact hL.trans hX3
  · unfold principalAxisInterpolationLip
    apply max_le
    · have ht : 8 * (probabilityProfileLipschitz : ℝ) * ((L : ℝ)^h)^2 / γ^2 ≤ X^6 := by
        rw [div_eq_mul_inv, ← inv_pow]
        calc
          _ ≤ X * X * X^2 * X^2 := by gcongr
          _ = _ := by ring
      exact ht.trans (pow_le_pow_right₀ hX1 (by norm_num))
    · have ht : 2 * ((L : ℝ)^h)^2 ≤ X^3 := by
        calc
          _ ≤ X * X^2 := by gcongr
          _ = _ := by ring
      exact ht.trans (pow_le_pow_right₀ hX1 (by norm_num))

theorem tailAxisInterpolation_power_bounds (L s : ℕ) {X ε : ℝ}
    (hX : 8 ≤ X) (hA : (probabilityProfileLipschitz : ℝ) ≤ X)
    (hε : 0 < ε) (hεX : ε⁻¹ ≤ X) (hL : (L : ℝ)^s ≤ X) (hL1 : (L : ℝ)^(s+1) ≤ X) :
    tailAxisInterpolationCap L s ε ≤ X^3 ∧ tailAxisInterpolationLip L s ε ≤ X^7 := by
  have hX0 : 0 ≤ X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have h2 : (2 : ℝ) ≤ X := by linarith
  have hX3 : X ≤ X^3 := by simpa only [pow_one] using (pow_le_pow_right₀ hX1 (show 1 ≤ 3 by norm_num))
  constructor
  · unfold tailAxisInterpolationCap
    apply max_le
    · rw [div_eq_mul_inv]
      calc
        _ ≤ X * X * X := by gcongr
        _ = _ := by ring
    · exact hL1.trans hX3
  · unfold tailAxisInterpolationLip
    apply max_le
    · have ht : 2 * (probabilityProfileLipschitz : ℝ) * ((L : ℝ)^s)^2 / ε^2 ≤ X^6 := by
        rw [div_eq_mul_inv, ← inv_pow]
        calc
          _ ≤ X * X * X^2 * X^2 := by gcongr
          _ = _ := by ring
      exact ht.trans (pow_le_pow_right₀ hX1 (by norm_num))
    · have ht : 2 * ((L : ℝ)^(s+1))^2 ≤ X^3 := by
        calc
          _ ≤ X * X^2 := by gcongr
          _ = _ := by ring
      exact ht.trans (pow_le_pow_right₀ hX1 (by norm_num))

theorem integerPolynomialInterpolation_power_bounds (h L s : ℕ) {X ρ γ ε : ℝ}
    (hX : 8 ≤ X) (hA : (probabilityProfileLipschitz : ℝ) ≤ X)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
    (hρX : ρ⁻¹ ≤ X) (hγX : γ⁻¹ ≤ X) (hεX : ε⁻¹ ≤ X)
    (hLh : (L : ℝ)^h ≤ X) (hLs : (L : ℝ)^s ≤ X) (hLs1 : (L : ℝ)^(s+1) ≤ X) :
    integerPolynomialInterpolationCap h L s ρ γ ε ≤ X^3 ∧
      integerPolynomialInterpolationLip h L s ρ γ ε ≤ X^7 := by
  obtain ⟨hc, hl⟩ := constantIntegerInterpolation_power_bounds hX hA hρ hρX
  obtain ⟨pc, pl⟩ := principalAxisInterpolation_power_bounds h L hX hA hγ hγX hLh
  obtain ⟨tc, tl⟩ := tailAxisInterpolation_power_bounds L s hX hA hε hεX hLs hLs1
  exact ⟨max_le hc (max_le pc tc), max_le hl (max_le pl tl)⟩

end Erdos3

end

section

namespace Erdos3

def integerInterpolationLogEnvelope (m : ℕ) (P : ℝ) : ℝ := ((m : ℝ) + 1) * P + 8

theorem integerPolynomialInterpolation_exp_bounds (m h L s : ℕ)
    (hh : h ≤ m) (hs : s ≤ m) {P ρ γ ε : ℝ} (hP : 0 ≤ P)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hL : (L : ℝ) ≤ Real.exp P)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
    (hρP : ρ⁻¹ ≤ Real.exp P) (hγP : γ⁻¹ ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    integerPolynomialInterpolationCap h L s ρ γ ε ≤
        Real.exp (3 * integerInterpolationLogEnvelope m P) ∧
      integerPolynomialInterpolationLip h L s ρ γ ε ≤
        Real.exp (7 * integerInterpolationLogEnvelope m P) := by
  let Q := integerInterpolationLogEnvelope m P
  let X := Real.exp Q
  have hm0 := Nat.cast_nonneg (α := ℝ) m
  have hPQ : P ≤ Q := by dsimp [Q, integerInterpolationLogEnvelope]; nlinarith
  have hQ8 : 8 ≤ Q := by dsimp [Q, integerInterpolationLogEnvelope]; nlinarith
  have hX : 8 ≤ X := by dsimp [X]; linarith [Real.add_one_le_exp Q]
  have hPX : Real.exp P ≤ X := Real.exp_le_exp.mpr hPQ
  have hp (k : ℕ) (hk : k ≤ m + 1) : (L : ℝ)^k ≤ X := by
    calc
      _ ≤ (Real.exp P)^k := pow_le_pow_left₀ (Nat.cast_nonneg _) hL _
      _ = Real.exp ((k : ℝ) * P) := (Real.exp_nat_mul P k).symm
      _ ≤ X := by
        apply Real.exp_le_exp.mpr
        have hkr : (k : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hk
        have hmul := mul_le_mul_of_nonneg_right hkr hP
        dsimp [Q, integerInterpolationLogEnvelope]
        linarith
  have h := integerPolynomialInterpolation_power_bounds h L s hX (hA.trans hPX) hρ hγ hε
    (hρP.trans hPX) (hγP.trans hPX) (hεP.trans hPX) (hp h (by omega)) (hp s (by omega)) (hp (s+1) (by omega))
  simpa only [X, ← Real.exp_nat_mul, Nat.cast_ofNat, Q] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedChartLift
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem normalizedLatticeQuotient_eq_of_sub_mem (u : W) (x : W × (Fin n → ℤ))
    (hx : u.val - normalizedLatticePoint W b x ∈ standardEuclideanLattice D) :
    QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u =
      normalizedLatticeQuotient W b hb x := by
  let z := latticeBasisEquiv (projectedIntegerLattice W) b hb x.2
  let v : W := x.1 - projectedLatticeShift (standardEuclideanLattice D) W z
  have hv : QuotientAddGroup.mk'
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup v =
        normalizedLatticeQuotient W b hb x := rfl
  have hdiff := normalizedLatticePoint_sub_mem_of_mk_eq W b hb v x hv
  have hm : (u - v).val ∈ standardEuclideanLattice D := by
    convert (standardEuclideanLattice D).sub_mem hx hdiff using 1
    simp only [Submodule.coe_sub]
    abel
  exact (QuotientAddGroup.eq_iff_sub_mem.mpr hm).trans hv

theorem exists_normalized_chart_lift (u : W) (v : EuclideanSpace ℝ D)
    (hv : u.val - v ∈ standardEuclideanLattice D) :
    ∃ x : W × (Fin n → ℤ), normalizedLatticePoint W b x = v ∧
      normalizedLatticeQuotient W b hb x =
        QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u := by
  have hproj : Wᗮ.orthogonalProjectionOnto v ∈ span ℤ (Set.range b) := by
    rw [hb]
    apply (projectedIntegerLattice W).neg_mem_iff.mp
    change -(Wᗮ.orthogonalProjectionOnto v) ∈
      (standardEuclideanLattice D).map (Wᗮ.orthogonalProjectionOnto.toLinearMap.restrictScalars ℤ)
    refine ⟨u.val - v, hv, ?_⟩
    change Wᗮ.orthogonalProjectionOnto (u.val - v) = -Wᗮ.orthogonalProjectionOnto v
    rw [map_sub, Wᗮ.orthogonalProjectionOnto_eq_zero_iff.mpr (by simp), zero_sub]
  obtain ⟨z, hz⟩ := normalizedOrthogonalChart_integer_coordinates W b v hproj
  let x : W × (Fin n → ℤ) := ((normalizedOrthogonalChart W b v).1, z)
  have hx : normalizedLatticePoint W b x = v := by
    apply (normalizedOrthogonalChart W b).injective
    change (normalizedOrthogonalChart W b) ((normalizedOrthogonalChart W b).symm
      ((normalizedOrthogonalChart W b v).1, fun i => (z i : ℝ) / basisAxisScale b i)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext rfl (funext (fun i => (hz i).symm))
  refine ⟨x, hx, (normalizedLatticeQuotient_eq_of_sub_mem W b hb u x ?_).symm⟩
  rwa [hx]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GeometricRetainedCommonCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

def geometricSiteBudget (m q : ℕ) (P : ℝ) : ℝ :=
  ((m : ℝ) + 1) * (P + 1) ^ (m + 1) + 2 ^ q

theorem geometricSiteBudget_nonneg (m q : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ geometricSiteBudget m q P := by
  unfold geometricSiteBudget
  positivity

theorem degree_mul_le_geometricSiteBudget (m q : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    (m : ℝ) * (P + 1) ≤ geometricSiteBudget m q P := by
  have hp : P + 1 ≤ (P + 1) ^ (m + 1) := by
    simpa using pow_le_pow_right₀ (by linarith : 1 ≤ P + 1) (show 1 ≤ m + 1 by omega)
  calc
    _ ≤ ((m : ℝ) + 1) * (P + 1) ^ (m + 1) :=
      mul_le_mul (by linarith) hp (by linarith) (by positivity)
    _ ≤ geometricSiteBudget m q P := le_add_of_nonneg_right (by positivity)

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

theorem cubeSites_card_le_geometricSiteBudget (m q : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    (Fintype.card (Finset (Fin q)) : ℝ) ≤ geometricSiteBudget m q P := by
  simp only [Fintype.card_finset, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  exact le_add_of_nonneg_left (by positivity)

noncomputable def exponentialSiteHeight (m : ℕ) (P : ℝ) : ℕ := ⌈Real.exp P⌉₊ ^ m

theorem exponentialSiteHeight_pos (m : ℕ) (P : ℝ) : 0 < exponentialSiteHeight m P := by
  exact pow_pos (Nat.ceil_pos.mpr (Real.exp_pos _)) _

theorem exponentialSiteHeight_le (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    (exponentialSiteHeight m P : ℝ) ≤ Real.exp ((m : ℝ) * (P + 1)) := by
  have hceil : (⌈Real.exp P⌉₊ : ℝ) ≤ Real.exp (P + 1) := by
    calc
      _ ≤ Real.exp P + 1 := (Nat.ceil_lt_add_one (Real.exp_pos P).le).le
      _ ≤ Real.exp P * 2 := by linarith [Real.one_le_exp hP]
      _ ≤ Real.exp P * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos P).le
      _ = Real.exp (P + 1) := (Real.exp_add _ _).symm
  simpa only [exponentialSiteHeight, Nat.cast_pow, Real.exp_nat_mul] using
    pow_le_pow_left₀ (Nat.cast_nonneg _) hceil m

theorem boundedSiteMatrix_height_of_exp {K S : Type*} (m : ℕ) {h : ℕ} (hh : h ≤ m)
    (site : S → K → ℤ) {P : ℝ}
    (hsite : ∀ s k, |(site s k : ℝ)| ≤ Real.exp P)
    (s : S) (d : BoundedCoefficientExponent K h) :
    RationalHeightLE (boundedSiteMatrix h site s d : ℚ) (exponentialSiteHeight m P) := by
  have hceil : 1 ≤ ⌈Real.exp P⌉₊ := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hb : ∀ s k, (site s k).natAbs ≤ ⌈Real.exp P⌉₊ := by
    intro s k
    have he : ((site s k).natAbs : ℝ) ≤ (⌈Real.exp P⌉₊ : ℝ) := by
      simpa using (hsite s k).trans (Nat.le_ceil (Real.exp P))
    exact_mod_cast he
  exact (boundedSiteMatrix_height h site hceil hb s d).mono
    (Nat.pow_le_pow_right hceil hh)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Polynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Polynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalCoefficientCoverLift
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

noncomputable def normalizedLatticeRepresentative (x : W × (Fin n → ℤ)) : W :=
  x.1 - W.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val

theorem normalizedLatticeRepresentative_continuous :
    Continuous (normalizedLatticeRepresentative W b hb) := by
  have hc : Continuous (standardLatticeIntegerLift W b hb) := continuous_of_discreteTopology
  exact continuous_fst.sub (W.orthogonalProjectionOnto.continuous.comp
    (continuous_subtype_val.comp (hc.comp continuous_snd)))

theorem normalizedLatticeRepresentative_mk (x : W × (Fin n → ℤ)) :
    (QuotientAddGroup.mk (normalizedLatticeRepresentative W b hb x) :
      W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) =
      normalizedLatticeQuotient W b hb x :=
  (normalizedLatticeQuotient_linear_lift W b hb x).symm

noncomputable def normalizedCoverLift (d : ℕ) (x : W × (Fin n → ℤ)) :
    W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup :=
  QuotientAddGroup.mk ((d : ℝ)⁻¹ • normalizedLatticeRepresentative W b hb x)

theorem normalizedCoverLift_continuous (d : ℕ) :
    Continuous (normalizedCoverLift W b hb d) := by
  have hc : Continuous (fun _ : W × (Fin n → ℤ) => (d : ℝ)⁻¹) := continuous_const
  exact QuotientAddGroup.continuous_mk.comp
    (hc.smul (normalizedLatticeRepresentative_continuous W b hb))

theorem normalizedCoverLift_projection (d : ℕ) (hd : 0 < d) (x : W × (Fin n → ℤ)) :
    quotientIntegerCover (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d
        (normalizedCoverLift W b hb d x) = normalizedLatticeQuotient W b hb x := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  change quotientIntegerCover _ d (QuotientAddGroup.mk' _
    ((d : ℝ)⁻¹ • normalizedLatticeRepresentative W b hb x)) = _
  rw [quotientIntegerCover_mk, smul_smul, mul_inv_cancel₀ hd0, one_smul]
  exact normalizedLatticeRepresentative_mk W b hb x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
variable (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
variable [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J I : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def canonicalCoefficientCoverLift (d : ℕ)
    (x : CoefficientSamplerArrays (K := K) I n) : CoefficientTorus (K := K) U :=
  (euclideanCoefficientEquiv U).symm (fun j e =>
    normalizedCoverLift (euclideanSubspace (U j)) (b j) (hb j) d
      (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (x j) e)))

omit [Fintype K] in
theorem canonicalCoefficientCoverLift_projection (d : ℕ) (hd : 0 < d)
    (x : CoefficientSamplerArrays (K := K) I n) :
    quotientIntegerCover (coefficientIntegerLattice U) d
        (canonicalCoefficientCoverLift U b hb o d x) = canonicalCoefficientSample U b hb o x := by
  apply (euclideanCoefficientEquiv U).injective
  change euclideanCoefficientEquiv U (d • canonicalCoefficientCoverLift U b hb o d x) = _
  rw [map_nsmul, canonicalCoefficientCoverLift, AddEquiv.apply_symm_apply,
    canonicalCoefficientSample, AddEquiv.apply_symm_apply]
  funext j e
  exact normalizedCoverLift_projection (euclideanSubspace (U j)) (b j) (hb j) d hd _

theorem canonicalCoefficientCoverLift_measurable
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (d : ℕ) : Measurable (canonicalCoefficientCoverLift (K := K) U b hb o d) := by
  apply (euclideanCoefficientMeasurableEquiv U).symm.measurable.comp
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_pi_iff.mpr
  intro e
  exact (normalizedCoverLift_continuous (euclideanSubspace (U j)) (b j) (hb j) d).measurable.comp
    ((orthonormalMixedChart (o j)).measurable.comp ((measurable_pi_apply e).comp
      ((mixedArrayRegroup _ _ _).measurable.comp (measurable_pi_apply j))))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CanonicalCoverLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

theorem coefficientCover_measurePreserving {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 0 < q) :
    MeasurePreserving (quotientIntegerCover (coefficientIntegerLattice U) q) μ μ := by
  have : μ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := μ) Set.univ isCompact_univ (by simp) }
  exact AddMonoidHom.measurePreserving
    (quotientIntegerCover_continuous (coefficientIntegerLattice U) q)
    (quotientIntegerCover_surjective (coefficientIntegerLattice U) q hq) rfl

theorem coefficientCover_integrable {K E : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [NormedAddCommGroup E]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 0 < q) (f : CoefficientTorus (K := K) U → E) (hf : Integrable f μ) :
    Integrable (fun x => f (quotientIntegerCover (coefficientIntegerLattice U) q x)) μ :=
  (coefficientCover_measurePreserving U μ q hq).integrable_comp_of_integrable hf

theorem coefficientCover_integral {K E : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 0 < q) (f : CoefficientTorus (K := K) U → E)
    (hf : AEStronglyMeasurable f μ) :
    (∫ x, f (quotientIntegerCover (coefficientIntegerLattice U) q x) ∂μ) = ∫ x, f x ∂μ := by
  have hp := coefficientCover_measurePreserving U μ q hq
  have hf' : AEStronglyMeasurable f (Measure.map (quotientIntegerCover (coefficientIntegerLattice U) q) μ) := by
    rwa [hp.map_eq]
  simpa only [hp.map_eq] using (integral_map hp.measurable.aemeasurable hf').symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory

instance subspaceArrayIntegerLattice_closed {I D : Type*} (U : Submodule ℝ (D → ℝ)) :
    IsClosed (subspaceArrayIntegerLattice I U : Set (I → U)) := by
  change IsClosed {x : I → U | ∀ i a, ∃ n : ℤ, (x i).val a = n}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro a
  have hc : Continuous (fun x : I → U => (x i).val a) :=
    (continuous_apply a).comp (continuous_subtype_val.comp (continuous_apply i))
  have h : IsClosed {x : I → U | ∃ n : ℤ, (n : ℝ) = (x i).val a} :=
    Real.isClosedEmbedding_intCast.isClosed_range.preimage hc
  simpa only [eq_comm] using h

variable {D : Type*} [Fintype D] (U : Submodule ℝ (D → ℝ))
variable [MeasurableSpace (SubspaceArrayTorus Unit U)] [BorelSpace (SubspaceArrayTorus Unit U)]

noncomputable def euclideanSubspaceTorusMeasurableEquiv :
    (euclideanSubspace U ⧸
      (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup) ≃ᵐ
        SubspaceArrayTorus Unit U := by
  let : BorelSpace (euclideanSubspace U ⧸
      (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup) :=
    QuotientAddGroup.borelSpace
  exact (euclideanSubspaceTorusHomeomorph U).toMeasurableEquiv

variable (ν : Measure (euclideanSubspace U ⧸
  (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup))

noncomputable def euclideanSubspaceTorusMeasure : Measure (SubspaceArrayTorus Unit U) :=
  Measure.map (euclideanSubspaceTorusMeasurableEquiv U) ν

theorem euclideanSubspaceTorusMeasure_probability [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (euclideanSubspaceTorusMeasure U ν) := by
  unfold euclideanSubspaceTorusMeasure
  exact Measure.isProbabilityMeasure_map (euclideanSubspaceTorusMeasurableEquiv U).measurable.aemeasurable

theorem euclideanSubspaceTorusMeasure_invariant [ν.IsAddLeftInvariant] :
    (euclideanSubspaceTorusMeasure U ν).IsAddLeftInvariant :=
  isAddLeftInvariant_map (euclideanSubspaceTorusEquiv U).toAddMonoidHom.toAddHom
    (euclideanSubspaceTorusMeasurableEquiv U).measurable (euclideanSubspaceTorusEquiv U).surjective

theorem euclideanSubspaceTorusMeasure_mass
    (f : (euclideanSubspace U ⧸
      (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup) → ℝ)
    (hf : Integrable f ν) (hm : (∫ x, f x ∂ν) = 1) :
    Integrable (fun y => f ((euclideanSubspaceTorusEquiv U).symm y))
        (euclideanSubspaceTorusMeasure U ν) ∧
      (∫ y, f ((euclideanSubspaceTorusEquiv U).symm y)
        ∂euclideanSubspaceTorusMeasure U ν) = 1 := by
  let e := euclideanSubspaceTorusMeasurableEquiv U
  change Integrable (fun y => f (e.symm y)) (Measure.map e ν) ∧
    (∫ y, f (e.symm y) ∂Measure.map e ν) = 1
  constructor
  · apply (integrable_map_equiv e _).mpr
    simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using hf
  · rw [integral_map_equiv]
    simpa only [MeasurableEquiv.symm_apply_apply] using hm

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

theorem exists_covered_coefficient_density {K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (SiteTorus S U)] [BorelSpace (SiteTorus S U)]
    (site : S → K → ℤ) (q : ℕ) (hq : 0 < q)
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)
    (hT : ∀ j (x : BoundedCoefficientExponent K (j.val + 1) → U j),
      matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ))
        (matrixModuleAction (fun d s => (T j d s : ℝ))
          (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)) x)) =
        (q : ℝ) • matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)) x)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Continuous D) {B : ℝ}
    (hcap : ∀ x, D x ∈ Set.Icc (0 : ℝ) B) (hmass : (∫ x, D x ∂μ) = 1) :
    let E := coefficientSiteTorusMap U site
    let π := Set.rangeFactorization E
    let C := quotientIntegerCover (coefficientIntegerLattice U) q
    let R := coefficientSiteResidual U site (fun _ => q) T
    let hR := coefficientSiteResidual_preserves_lattice U site (fun _ => q) T
    ∃ g : Set.range E → ℝ, Continuous g ∧ (∀ y, g y ∈ Set.Icc (0 : ℝ) B) ∧
      Integrable g (μ.map π) ∧ (∫ y, g y ∂μ.map π) = 1 ∧
      (∀ x, g (π x) = linearQuotientAverage (coefficientIntegerLattice U) R hR μ D (C x)) ∧
      (realDensityMeasure μ (fun x => D (C x))).map π = realDensityMeasure (μ.map π) g := by
  intro E π C R hR
  have hE : Continuous E := coefficientSiteTorusMap_continuous U site
  have hπ : Measurable π := hE.rangeFactorization.measurable
  have hC : Continuous C := quotientIntegerCover_continuous _ q
  have hCp := coefficientCover_measurePreserving U μ q hq
  have hRc := linearQuotientEndomorphism_continuous _ R hR R.continuous_of_finiteDimensional
  have hb (x) : ‖D x‖ ≤ B := by rw [Real.norm_of_nonneg (hcap x).1]; exact (hcap x).2
  let f := linearQuotientAverage (coefficientIntegerLattice U) R hR μ D
  have hfc : Continuous f := BooleanCubeKernel.coefficientResidualAverage_continuous U R hR μ D hD hb
  have hi : Integrable D μ := Integrable.of_bound hD.aestronglyMeasurable B (ae_of_all μ hb)
  have hprob := linearQuotientAverage_probability _ R hR μ hRc.measurable D hD.measurable hi
    (fun x => (hcap x).1) hmass
  have hfiber (x y : CoefficientTorus (K := K) U) (hxy : E x = E y) : f (C x) = f (C y) := by
    exact linearQuotientAverage_cover_eq_of_map_eq (Y := SiteTorus S U)
      (coefficientIntegerLattice U) R hR μ q (coefficientSiteTorusMap U site)
      (coefficientSiteResidual_cover_on_kernel U site q T) D x y hxy
  obtain ⟨g, hgc, hg⟩ := exists_continuous_image_factor E hE (fun x => f (C x)) (hfc.comp hC)
    hfiber
  let _ : IsProbabilityMeasure (μ.map π) := Measure.isProbabilityMeasure_map hπ.aemeasurable
  have hgb (y) : g y ∈ Set.Icc (0 : ℝ) B := by
    obtain ⟨x, hx⟩ := Set.rangeFactorization_surjective y
    rw [← hx, hg]
    refine ⟨hprob.1 _, ?_⟩
    have h := linearQuotientAverage_bound _ R hR μ D hb (C x)
    rwa [Real.norm_of_nonneg (hprob.1 _)] at h
  have hgi : Integrable g (μ.map π) := Integrable.of_bound hgc.aestronglyMeasurable B
    (ae_of_all _ (fun y => by rw [Real.norm_of_nonneg (hgb y).1]; exact (hgb y).2))
  have hgmass : (∫ y, g y ∂μ.map π) = 1 := by
    rw [integral_map hπ.aemeasurable hgc.aestronglyMeasurable]
    change (∫ x, g (Set.rangeFactorization E x) ∂μ) = 1
    simp_rw [hg]
    exact (coefficientCover_integral U μ q hq f hfc.aestronglyMeasurable).trans hprob.2.2
  refine ⟨g, hgc, hgb, hgi, hgmass, hg, ?_⟩
  have hLmass : (∫ x, D (C x) ∂μ) = 1 :=
    (coefficientCover_integral U μ q hq D hD.aestronglyMeasurable).trans hmass
  have hLi : Integrable (fun x => D (C x)) μ := coefficientCover_integrable U μ q hq D hi
  have he (x) : linearQuotientAverage (coefficientIntegerLattice U) R hR μ (fun x => D (C x)) x =
      g (π x) := by
    rw [hg]
    exact (linearQuotientAverage_cover _ R hR μ q hCp D x
      (BooleanCubeKernel.coefficientResidual_section_integrable U R hR μ D hD hb (C x)).aestronglyMeasurable).symm
  have hshift : haarShiftDensity μ (-⇑(linearQuotientEndomorphism (coefficientIntegerLattice U) R hR))
      (fun x => D (C x)) = fun x => g (π x) := by
    funext x
    simpa only [haarShiftDensity, densityMixture, Pi.neg_apply, sub_neg_eq_add, linearQuotientAverage] using he x
  have hlaw := haarShiftDensity_map_eq μ μ (-⇑(linearQuotientEndomorphism (coefficientIntegerLattice U) R hR))
    hRc.measurable.neg (fun x => D (C x)) (hD.comp hC).measurable hLi (fun x => (hcap _).1) hLmass π hπ
    (fun y x => by
      apply Subtype.ext
      change E (x + -linearQuotientEndomorphism _ R hR y) = E x
      rw [map_add, map_neg, coefficientSiteResidual_site_zero U site q T hT, neg_zero, add_zero])
  rw [hshift] at hlaw
  rw [← hlaw]
  exact measurePreserving_realDensity_map μ (μ.map π) π ⟨hπ, rfl⟩ g hgc.measurable hgi (fun y => (hgb y).1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {K : Type*} [Fintype K] {m : ℕ} {J I : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OneSiteCoefficientFactorization
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def coefficientResidualArray {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) :
    CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := K) U :=
  LinearMap.id - (constantCoefficientArray U).comp (coefficientEvaluationArray U t)

theorem coefficientResidualArray_preserves_lattice {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    coefficientResidualArray U t x ∈ coefficientIntegerLattice U :=
  (coefficientIntegerLattice U).sub_mem hx (constantCoefficientArray_preserves_lattice U _
    (coefficientEvaluationArray_preserves_lattice U t x hx))

theorem coefficientResidualArray_evaluation {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (x : CoefficientArray (K := K) U) :
    coefficientEvaluationArray U t (coefficientResidualArray U t x) = 0 := by
  simp only [coefficientResidualArray, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.comp_apply, map_sub, coefficientEvaluationArray_constant, sub_self]

theorem coefficientResidualArray_factor_iff {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (L : CoefficientArray (K := K) U →ₗ[ℝ] ℝ) :
    L.comp (coefficientResidualArray U t) = 0 ↔
      ∃ M : CoefficientArray (K := Empty) U →ₗ[ℝ] ℝ, L = M.comp (coefficientEvaluationArray U t) := by
  constructor
  · intro h
    refine ⟨L.comp (constantCoefficientArray U), ?_⟩
    apply LinearMap.ext
    intro x
    have hx := DFunLike.congr_fun h x
    simpa only [LinearMap.comp_apply, coefficientResidualArray, LinearMap.sub_apply,
      LinearMap.id_apply, map_sub, LinearMap.zero_apply, sub_eq_zero] using hx
  · rintro ⟨M, rfl⟩
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, coefficientResidualArray_evaluation, map_zero,
      LinearMap.zero_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem coefficientArray_factor_to_bounded_site {K S : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (s₀ : S) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (M : CoefficientArray (K := Empty) U →ₗ[ℝ] ℝ)
    (hM : coefficientArrayFunctional U frequency = M.comp (coefficientEvaluationArray U t))
    (j : Fin m) :
    ∃ Mj : (S → U j) →ₗ[ℝ] ℝ,
      ∀ p : VectorPolynomial K ℝ (U j), DegreeLE (1 : K → ℕ) (j.val + 1) p →
        coefficientFunctional (fun d a => (frequency j d a : ℝ)) (map (U j).subtype p) =
          Mj (siteEvaluation (fun _ : S => fun k => (t k : ℝ)) p) := by
  let A : (S → U j) →ₗ[ℝ] (BoundedCoefficientExponent Empty (j.val + 1) → U j) :=
    LinearMap.pi (fun _ => LinearMap.proj s₀)
  let Mj := M.comp ((coefficientLayerInsertion U j).comp A)
  refine ⟨Mj, ?_⟩
  intro p hp
  let v : BoundedCoefficientExponent K (j.val + 1) → U j := fun d => coefficients p d.val
  have hv : boundedArrayPolynomial (j.val + 1) v = p := boundedArrayPolynomial_reconstruct p hp
  have he := DFunLike.congr_fun hM (coefficientLayerInsertion U j v)
  rw [LinearMap.comp_apply, coefficientArrayFunctional_layerInsertion,
    coefficientEvaluationArray_layerInsertion] at he
  rw [← hv, coefficientFunctional_boundedArrayPolynomial, siteEvaluation_boundedArrayPolynomial]
  exact he

theorem coefficientArray_factor_of_bounded_site {K S : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hf : ∀ j, ∃ Mj : (S → U j) →ₗ[ℝ] ℝ,
      ∀ p : VectorPolynomial K ℝ (U j), DegreeLE (1 : K → ℕ) (j.val + 1) p →
        coefficientFunctional (fun d a => (frequency j d a : ℝ)) (map (U j).subtype p) =
          Mj (siteEvaluation (fun _ : S => fun k => (t k : ℝ)) p)) :
    ∃ M : CoefficientArray (K := Empty) U →ₗ[ℝ] ℝ,
      coefficientArrayFunctional U frequency = M.comp (coefficientEvaluationArray U t) := by
  choose Mj hMj using hf
  let A (j : Fin m) : CoefficientArray (K := Empty) U →ₗ[ℝ] (S → U j) :=
    LinearMap.pi (fun _ => LinearMap.proj (⟨j, zeroCoefficientExponent Empty (j.val + 1)⟩ :
      CoefficientSlot Empty m))
  let M : CoefficientArray (K := Empty) U →ₗ[ℝ] ℝ := ∑ j, (Mj j).comp (A j)
  refine ⟨M, ?_⟩
  apply LinearMap.ext
  intro x
  have hj (j : Fin m) :
      subspaceArrayFunctional (U j) (fun d a => (frequency j d.val a : ℝ)) (fun d => x ⟨j, d⟩) =
        Mj j (A j (coefficientEvaluationArray U t x)) := by
    let v : BoundedCoefficientExponent K (j.val + 1) → U j := fun d => x ⟨j, d⟩
    have he := hMj j (boundedArrayPolynomial (j.val + 1) v)
      (boundedArrayPolynomial_degreeLE (j.val + 1) v)
    rw [coefficientFunctional_boundedArrayPolynomial, siteEvaluation_boundedArrayPolynomial] at he
    exact he
  calc
    _ = ∑ j : Fin m, subspaceArrayFunctional (U j)
        (fun d a => (frequency j d.val a : ℝ)) (fun d => x ⟨j, d⟩) := by
      change (∑ s : CoefficientSlot K m, ∑ a, (frequency s.1 s.2.val a : ℝ) * (x s).val a) = _
      rw [Fintype.sum_sigma]
      rfl
    _ = ∑ j, Mj j (A j (coefficientEvaluationArray U t x)) := Finset.sum_congr rfl (fun j _ => hj j)
    _ = _ := by simp only [M, LinearMap.comp_apply, LinearMap.sum_apply]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientJetCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem arrayCoordinateTorus_integerMatrix {I S J : Type*} [Fintype I]
    (U : Submodule ℝ (J → ℝ)) (A : Matrix S I ℤ) (x : SubspaceArrayTorus I U) (s : S) :
    arrayCoordinateTorus U (integerMatrixTorusMap U A x) s =
      ∑ i, A s i • arrayCoordinateTorus U x i := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice I U) x
  simp only [integerMatrixTorusMap_mk, arrayCoordinateTorus_mk]
  let a : S → I → ℤ := A
  let q := QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit U)
  change q (fun _ => matrixModuleAction (fun s i => (a s i : ℝ)) v s) =
    ∑ i, a s i • q (fun _ => v i)
  have he : (fun _ : Unit => matrixModuleAction (fun s i => (a s i : ℝ)) v s) =
      ∑ i, a s i • (fun _ : Unit => v i) := by
    funext u
    simp only [Finset.sum_apply, Pi.smul_apply]
    change (∑ i, (a s i : ℝ) • v i) = ∑ i, a s i • v i
    exact Finset.sum_congr rfl (fun i _ => Int.cast_smul_eq_zsmul ℝ (a s i) (v i))
  rw [he, map_sum]
  exact Finset.sum_congr rfl (fun i _ => map_zsmul q _ _)

namespace VectorPolynomial

theorem arrayCoordinateTorus_coefficientLayer {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (x : CoefficientTorus (K := K) U)
    (j : Fin m) (e : BoundedCoefficientExponent K (j.val + 1)) :
    arrayCoordinateTorus (U j) (coefficientLayerTorus U j x) e =
      coefficientCoordinateTorus U x ⟨j, e⟩ := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rfl

theorem coefficientBooleanJetTorusMap_layer {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (rows : ∀ j, O j → Finset α) (x : CoefficientTorus (K := K) U) (j : Fin m) :
    coefficientBooleanJetTorusMap U root D rows x j =
      integerMatrixTorusMap (U j) (boundedCoefficientJetMatrix root D (j.val + 1) (rows j))
        (coefficientLayerTorus U j x) := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [coefficientBooleanJetTorusMap_mk]
  rfl

theorem euclideanCoefficientJetMap_apply {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
    (x : CoefficientTorus (K := K) U) (j : Fin m) (o : O j) :
    euclideanCoefficientJetMap U root D rows x j o =
      ∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) o e •
        euclideanCoefficientEquiv U x j e := by
  change (euclideanSubspaceTorusEquiv (U j)).symm
    (arrayCoordinateTorus (U j) (coefficientBooleanJetTorusMap U root D rows x j) o) = _
  rw [coefficientBooleanJetTorusMap_layer, arrayCoordinateTorus_integerMatrix, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_zsmul, arrayCoordinateTorus_coefficientLayer]
  rfl

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientDeckImageCongruence
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

attribute [local irreducible] coefficientDeckKernelEquiv

variable {K : Type*} [Fintype K] {m : ℕ} {J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def canonicalCoefficientDeckSample (d : ℕ) (hd : 0 < d)
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) B d) :
    CoefficientTorus (K := K) U :=
  canonicalCoefficientCoverLift U b hb o d x + (coefficientDeckKernelEquiv U bW d hd r).val

omit [Fintype K] in
theorem canonicalCoefficientDeckSample_coordinate (d : ℕ) (hd : 0 < d)
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) B d)
    (j : Fin m) (e : BoundedCoefficientExponent K (j.val + 1)) :
    euclideanCoefficientEquiv U (canonicalCoefficientDeckSample U bW b hb o d hd x r) j e =
      normalizedCoverLift (euclideanSubspace (U j)) (b j) (hb j) d
        (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (x j) e)) +
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd (r j e)).val := by
  simp only [canonicalCoefficientDeckSample, map_add, Pi.add_apply,
    coefficientDeckKernelEquiv_coordinate, canonicalCoefficientCoverLift, AddEquiv.apply_symm_apply]

omit [Fintype K] in
theorem canonicalCoefficientDeckSample_projection (d : ℕ) (hd : 0 < d)
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) B d) :
    quotientIntegerCover (coefficientIntegerLattice (K := K) U) d
        (canonicalCoefficientDeckSample U bW b hb o d hd x r) = canonicalCoefficientSample U b hb o x := by
  rw [canonicalCoefficientDeckSample, map_add, canonicalCoefficientCoverLift_projection U b hb o d hd,
    (coefficientDeckKernelEquiv U bW d hd r).property, add_zero]

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

theorem canonicalCoefficientDeckSample_measurable (d : ℕ) [NeZero d] :
    Measurable (fun p : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d =>
      canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2) := by
  exact ((canonicalCoefficientCoverLift_measurable U b hb o d).comp measurable_fst).add
    ((measurable_subtype_coe.comp (measurable_of_finite
      (coefficientDeckKernelEquiv U bW d (Nat.pos_of_ne_zero (NeZero.ne d))))).comp measurable_snd)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

noncomputable def coefficientDeckJetMap (d : ℕ) :
    CoefficientDeckResidues (K := K) B d →+ (∀ j, O j → B j → ZMod d) where
  toFun r j t := ∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) t e • r j e
  map_zero' := by
    funext j t i
    simp
  map_add' r s := by
    funext j t
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]

variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SourceUnitCover
namespace OAI

section

namespace Erdos3.RationalTorus

open scoped BigOperators

variable {σ : Type*} [Fintype σ]

def trivialMultidegreeFiltration (s : ℕ) (bound : σ → ℕ) :
    MultidegreeLieFiltration σ (Algebra 0) s bound where
  ordinary := trivialFiltration s
  layer _ := ⊤
  antitone _ _ _ := le_rfl
  zero_eq_top := rfl
  lie_mem _ _ := Submodule.mem_top
  terminal _ _ := by
    ext x
    rw [Subsingleton.elim x 0]
    simp only [Submodule.zero_mem]
  degree_eq _ := by
    ext x
    rw [Subsingleton.elim x 0]
    simp only [Submodule.zero_mem]

noncomputable def trivialMultidegreeStructure (s : ℕ) (bound : σ → ℕ) :
    (trivialNilmanifold s).MultidegreeStructure bound := by
  letI := (basis 0).finiteDimensional_of_finite
  exact {
    filtration := trivialMultidegreeFiltration s bound
    ordinary := rfl
    basis := fun _ => Module.finBasis ℚ _
  }

theorem trivialMultidegreeStructure_complexity (s : ℕ) (bound : σ → ℕ) {p : ℝ}
    (hp : 0 ≤ p) : (trivialMultidegreeStructure s bound).ComplexityLE p := by
  refine ⟨trivialNilmanifold_geometry s hp, ?_⟩
  intro a j k
  exact Fin.elim0 k

end Erdos3.RationalTorus

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

variable {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

structure UnitVerticalObservable (D : RationalFilteredNilmanifold L s d)
    (T : Subgroup D.RealGroup) (I : Type*) [Fintype I] (p : ℝ) where
  observable : I → D.Space → ℂ
  unit : ∀ x, ∑ i, ‖observable i x‖ ^ 2 = 1
  norm : ∀ i x, ‖observable i x‖ ≤ 1
  lipBound : ℝ≥0
  lip_bound : (lipBound : ℝ) ≤ Real.exp p
  lipschitz : letI := D.metricSpace; ∀ i, LipschitzWith lipBound (observable i)
  frequency : L →ₗ[ℚ] ℚ
  height : ∀ i, rationalLogHeight (frequency (D.basis i)) ≤ p
  vertical : ∀ i z, z ∈ T → ∀ x, observable i (z • x) =
    CircleFourier.character ((realifyFunctional frequency z.coord : ℝ) : CircleFourier.Circle) *
      observable i x
  integral : ∀ z : D.RealGroup, z ∈ T → z ∈ D.realLattice →
    ∃ n : ℤ, realifyFunctional frequency z.coord = n

namespace UnitVerticalObservable

variable {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p q : ℝ}

noncomputable def mono (V : D.UnitVerticalObservable T I p) (hpq : p ≤ q) :
    D.UnitVerticalObservable T I q :=
  { V with
    lip_bound := V.lip_bound.trans (Real.exp_le_exp.mpr hpq)
    height := fun i => (V.height i).trans hpq }

noncomputable def constOne (D : RationalFilteredNilmanifold L s d) (T : Subgroup D.RealGroup)
    (hp : 0 ≤ p) : D.UnitVerticalObservable T (Fin 1) p where
  observable _ _ := 1
  unit _ := by simp
  norm _ _ := by simp
  lipBound := 0
  lip_bound := (Real.exp_pos p).le
  lipschitz := by
    let := D.metricSpace
    exact fun _ => LipschitzWith.const 1
  frequency := 0
  height _ := by simpa [rationalLogHeight] using hp
  vertical _ _ _ _ := by simp only [realifyFunctional_zero, AddCircle.coe_zero,
    CircleFourier.character_zero, one_mul]
  integral _ _ _ := ⟨0, by simp only [realifyFunctional_zero, Int.cast_zero]⟩

end UnitVerticalObservable

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

theorem frozen_quotient_map_smul {G : Type*} [Group G]
    (Γ Λ : Subgroup G) (a r : G) (f : G ⧸ Γ → G ⧸ Λ)
    (hf : ∀ x : G, f (QuotientGroup.mk x) = QuotientGroup.mk (a * x * r))
    (z : G) (hz : Commute z a) (x : G ⧸ Γ) : f (z • x) = z • f x := by
  induction x using Quotient.inductionOn with
  | h x =>
    change f (QuotientGroup.mk (z * x)) = z • f (QuotientGroup.mk x)
    rw [hf, hf]
    change (QuotientGroup.mk (a * (z * x) * r) : G ⧸ Λ) = QuotientGroup.mk (z * (a * x * r))
    congr 1
    calc
      _ = (a * z) * x * r := by group
      _ = (z * a) * x * r := by rw [hz.eq]
      _ = _ := by group

namespace RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
  {D : RationalFilteredNilmanifold L s d}

namespace DegreeRankStructure

noncomputable def withLattice (R : D.DegreeRankStructure r)
    (Λ : Subgroup D.filtration.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N) :
    (D.withLattice Λ N hN hin hout).DegreeRankStructure r where
  filtration := R.filtration
  associated := R.associated
  basis := R.basis

theorem withLattice_complexity (R : D.DegreeRankStructure r)
    (Λ : Subgroup D.filtration.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)
    {p P : ℝ} (hR : R.ComplexityLE p) (hpP : p ≤ P)
    (hQ : (D.withLattice Λ N hN hin hout).GeometryComplexityLE P) :
    (R.withLattice Λ N hN hin hout).ComplexityLE P :=
  ⟨hQ, fun i j a k => (hR.2 i j a k).trans hpP⟩

theorem top_realSubgroup_commute (R : D.DegreeRankStructure r)
    {z : D.RealGroup} (hz : z ∈ R.realSubgroup s r) (x : D.RealGroup) : Commute z x := by
  apply commute_of_lie_eq_zero
  exact D.filtration.realification.top_layer_central (R.realSubgroup_le_degree s r hz) x.coord

end DegreeRankStructure

variable {I : Type*} [Fintype I]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

namespace UnitVerticalObservable

noncomputable def frozenCover (R : D.DegreeRankStructure r) {p P : ℝ}
    (V : D.UnitVerticalObservable (R.realSubgroup s r) I p)
    (Λ : Subgroup D.filtration.Group) (hΛ : Λ ≤ D.lattice)
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)
    (a u : D.RealGroup) (f : (D.withLattice Λ N hN hin hout).Space → D.Space)
    (hf : ∀ x : D.RealGroup, f (QuotientGroup.mk x) = QuotientGroup.mk (a * x * u))
    (K : ℝ≥0)
    (hLip : letI := (D.withLattice Λ N hN hin hout).metricSpace;
      letI := D.metricSpace; LipschitzWith K f)
    (hpP : p ≤ P) (hK : (V.lipBound * K : ℝ≥0) ≤ Real.exp P) :
    (D.withLattice Λ N hN hin hout).UnitVerticalObservable
      ((R.withLattice Λ N hN hin hout).realSubgroup s r) I P where
  observable i x := V.observable i (f x)
  unit x := V.unit (f x)
  norm i x := V.norm i (f x)
  lipBound := V.lipBound * K
  lip_bound := hK
  lipschitz := by
    let := (D.withLattice Λ N hN hin hout).metricSpace
    let := D.metricSpace
    exact fun i => (V.lipschitz i).comp hLip
  frequency := V.frequency
  height i := (V.height i).trans hpP
  vertical i z hz x := by
    rw [frozen_quotient_map_smul _ _ a u f hf z (R.top_realSubgroup_commute hz a)]
    exact V.vertical i z hz (f x)
  integral z hz hlat := by
    have hsub : (D.withLattice Λ N hN hin hout).realLattice ≤ D.realLattice := Subgroup.map_mono hΛ
    exact V.integral z hz (hsub hlat)

end UnitVerticalObservable
end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators NNReal TensorProduct

noncomputable def invariantVerticalBudget (m : ℕ) (p : ℝ) : ℝ :=
  symmetricUnitBudget m (2 * p) + p + m + 1

namespace RationalFilteredNilmanifold.UnitVerticalObservable

variable {Γ I L : Type*} [Group Γ] [Fintype Γ] [Fintype I]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p : ℝ}
  [MulAction Γ D.Space]

theorem exists_invariant (V : D.UnitVerticalObservable T I p) (hp : 0 ≤ p)
    (hI : (Fintype.card I : ℝ) ≤ Real.exp p) (A : ℝ≥0) (hA : (A : ℝ) ≤ Real.exp p)
    (hact : letI := D.metricSpace; ∀ a : Γ, LipschitzWith A (fun x : D.Space => a • x))
    (hcomm : ∀ (a : Γ) (z : D.RealGroup), z ∈ T → ∀ x : D.Space,
      a • (z • x) = z • (a • x)) :
    ∃ W : D.UnitVerticalObservable T (SymmetricEvaluationIndex (Fintype.card Γ) I)
        (invariantVerticalBudget (Fintype.card Γ) p),
      W.frequency = Fintype.card Γ • V.frequency ∧
      (∀ (a : Γ) k x, W.observable k (a • x) = W.observable k x) ∧
      (Fintype.card (SymmetricEvaluationIndex (Fintype.card Γ) I) : ℝ) ≤
        Real.exp (invariantVerticalBudget (Fintype.card Γ) p) := by
  let := D.metricSpace
  let m := Fintype.card Γ
  have hp2 : 0 ≤ 2 * p := by positivity
  have hbudget : 0 ≤ symmetricUnitBudget m (2 * p) := by
    unfold symmetricUnitBudget
    positivity
  have hbase : symmetricUnitBudget m (2 * p) ≤ invariantVerticalBudget m p := by
    unfold invariantVerticalBudget
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hfreq : p + m + 1 ≤ invariantVerticalBudget m p := by
    unfold invariantVerticalBudget
    linarith
  have hIA : (Fintype.card I : ℝ) ≤ Real.exp (2 * p) :=
    hI.trans (Real.exp_le_exp.mpr (by linarith))
  have hKA : ((V.lipBound * A : ℝ≥0) : ℝ) ≤ Real.exp (2 * p) := by
    simpa only [NNReal.coe_mul, ← Real.exp_add, two_mul] using
      mul_le_mul V.lip_bound hA A.coe_nonneg (Real.exp_pos _).le
  obtain ⟨hcard, hLip⟩ := symmetricUnitBudget_bounds m (Fintype.card I) (V.lipBound * A) hp2 hIA hKA
  obtain ⟨g, hgunit, hgnorm, hglip, hginv, hgphase⟩ :=
    exists_invariant_unit_family (Γ := Γ) V.observable V.lipschitz V.unit hact
  refine ⟨{
    observable := g
    unit := hgunit
    norm := hgnorm
    lipBound := symmetricUnitFamilyLip m (Fintype.card I) (V.lipBound * A)
    lip_bound := hLip.trans (Real.exp_le_exp.mpr hbase)
    lipschitz := hglip
    frequency := m • V.frequency
    height := ?_
    vertical := ?_
    integral := ?_
  }, rfl, hginv, ?_⟩
  · intro i
    exact (show rationalLogHeight ((m • V.frequency) (D.basis i)) ≤ p + m + 1 by
      simpa only [LinearMap.smul_apply, nsmul_eq_mul] using
        rationalLogHeight_nat_mul m (V.height i)).trans hfreq
  · intro k z hz x
    have h := hgphase (z • x) x
      (character ((realifyFunctional V.frequency z.coord : ℝ) : CircleFourier.Circle))
      (norm_character _) (fun a j => by rw [hcomm a z hz, V.vertical j z hz]) k
    simpa only [realifyFunctional_nsmul, AddCircle.coe_nsmul, character_nsmul] using h
  · intro z hz hL
    obtain ⟨n, hn⟩ := V.integral z hz hL
    refine ⟨(m : ℤ) * n, ?_⟩
    rw [realifyFunctional_nsmul, hn]
    simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  · rw [symmetricEvaluationIndex_card]
    exact hcard.trans (Real.exp_le_exp.mpr hbase)

end RationalFilteredNilmanifold.UnitVerticalObservable

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeMultidegreeNilcharacter {σ : Type*} [Fintype σ] (bound : σ → ℕ) (p : ℝ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L (∑ i, bound i) dim
  multi : model.MultidegreeStructure bound
  complexity : multi.ComplexityLE p
  orbit : multi.filtration.realification.PolynomialOrbit
  outputDim : ℕ
  output_pos : 0 < outputDim
  output_bound : (outputDim : ℝ) ≤ Real.exp p
  vertical : model.UnitVerticalObservable (multi.realSubgroup bound) (Fin outputDim) p

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

namespace NativeMultidegreeNilcharacter

variable {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p q : ℝ}
  (W : NativeMultidegreeNilcharacter bound p)

noncomputable def eval (i : Fin W.outputDim) (x : σ → ℤ) : ℂ :=
  W.vertical.observable i (QuotientGroup.mk
    (W.multi.filtration.realification.polynomialOrbitEval x W.orbit))

noncomputable def evalCyclic (N : ℕ) [NeZero N] (i : Fin W.outputDim) (x : σ → ZMod N) : ℂ :=
  W.eval i (fun j => ((x j).val : ℤ))

theorem unit_eval (x : σ → ℤ) : ∑ i, ‖W.eval i x‖ ^ 2 = 1 := W.vertical.unit _

theorem norm_eval (i : Fin W.outputDim) (x : σ → ℤ) : ‖W.eval i x‖ ≤ 1 := W.vertical.norm i _

noncomputable def mono (hpq : p ≤ q) : NativeMultidegreeNilcharacter bound q :=
  { W with
    complexity := W.complexity.mono W.multi hpq
    output_bound := W.output_bound.trans (Real.exp_le_exp.mpr hpq)
    vertical := W.vertical.mono hpq }

theorem mono_eval (hpq : p ≤ q) (i : Fin W.outputDim) (x : σ → ℤ) :
    (W.mono hpq).eval i x = W.eval i x := rfl

noncomputable def constOne (bound : σ → ℕ) (hp : 0 ≤ p) :
    NativeMultidegreeNilcharacter bound p where
  L := RationalTorus.Algebra 0
  dim := 0
  model := RationalTorus.trivialNilmanifold (∑ i, bound i)
  multi := RationalTorus.trivialMultidegreeStructure (∑ i, bound i) bound
  complexity := RationalTorus.trivialMultidegreeStructure_complexity _ _ hp
  orbit := 1
  outputDim := 1
  output_pos := by omega
  output_bound := by simpa only [Nat.cast_one] using Real.one_le_exp hp
  vertical := RationalFilteredNilmanifold.UnitVerticalObservable.constOne _ _ hp

@[simp] theorem constOne_eval (bound : σ → ℕ) (hp : 0 ≤ p) (i : Fin 1) (x : σ → ℤ) :
    (constOne bound hp).eval i x = 1 := rfl

@[simp] theorem constOne_evalCyclic (bound : σ → ℕ) (hp : 0 ≤ p) (N : ℕ) [NeZero N]
    (i : Fin 1) (x : σ → ZMod N) : (constOne bound hp).evalCyclic N i x = 1 := rfl

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M I : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [Fintype I] {s t d e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M t e}
  {T : Subgroup E.RealGroup} {p q : ℝ} (V : E.UnitVerticalObservable T I p)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
  (S : Subgroup D.RealGroup)
  (hS : S ≤ T.comap (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
  (K : ℝ≥0)
  (hLip : letI := D.metricSpace; letI := E.metricSpace;
    LipschitzWith K (D.nativeSpaceMap E φ hφ))
  (hK : ((V.lipBound * K : ℝ≥0) : ℝ) ≤ Real.exp q)
  (hfreq : ∀ i, rationalLogHeight (V.frequency (φ (D.basis i))) ≤ q)

noncomputable def pullback : D.UnitVerticalObservable S I q where
  observable i x := V.observable i (D.nativeSpaceMap E φ hφ x)
  unit x := V.unit (D.nativeSpaceMap E φ hφ x)
  norm i x := V.norm i (D.nativeSpaceMap E φ hφ x)
  lipBound := V.lipBound * K
  lip_bound := hK
  lipschitz := by
    let := D.metricSpace
    let := E.metricSpace
    exact fun i => (V.lipschitz i).comp hLip
  frequency := V.frequency.comp φ.toLinearMap
  height := hfreq
  vertical i z hz x := by
    rw [D.nativeSpaceMap_smul E φ hφ z x, realifyFunctional_comp]
    exact V.vertical i
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ z) (hS hz) _
  integral z hz hlat := by
    obtain ⟨n, hn⟩ := V.integral
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ z)
      (hS hz) ((realificationMap_subgroup φ D.lattice E.lattice hφ) hlat)
    refine ⟨n, ?_⟩
    rw [realifyFunctional_comp]
    exact hn

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct

variable {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s r d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r) {p : ℝ}
  (V : D.UnitVerticalObservable (R.realSubgroup s r) I p)
  (Λ : Subgroup D.filtration.Group) (hΛ : Λ ≤ D.lattice)
  (m : ℕ) (hm : 0 < m)
  (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates D.basis Λ)
  (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid m)

noncomputable def onSublattice :
    (D.withLattice Λ m hm hin hout).UnitVerticalObservable
      ((R.withLattice Λ m hm hin hout).realSubgroup s r) I p where
  observable i := V.observable i ∘ sublatticeProjection D (D.withLattice Λ m hm hin hout) hΛ
  unit x := V.unit _
  norm i x := V.norm i _
  lipBound := V.lipBound
  lip_bound := V.lip_bound
  lipschitz := fun i => sublattice_pullback_lipschitz D (D.withLattice Λ m hm hin hout)
    hΛ rfl (V.observable i) (V.lipschitz i)
  frequency := V.frequency
  height := V.height
  vertical i z hz x := by
    induction x using Quotient.inductionOn with
    | h x => exact V.vertical i z hz (QuotientGroup.mk x)
  integral z hz hlat := V.integral z hz (Subgroup.map_mono hΛ hlat)

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_source_unit_cover :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M I : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s t d e r : ℕ}
      (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r)
      (E : RationalFilteredNilmanifold M t e) (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ},
      0 ≤ p → R.ComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∃ Λ : Subgroup D.filtration.Group,
        Λ ≤ D.lattice ∧ (Λ.subgroupOf D.lattice).Characteristic ∧
        (Λ.subgroupOf D.lattice).Normal ∧ (Λ.subgroupOf D.lattice).FiniteIndex ∧
        (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          (R.withLattice Λ N hN hin hout).ComplexityLE ((p + C) ^ C) ∧
          Λ ≤ E.lattice.comap (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ) ∧
          ∀ V : D.UnitVerticalObservable (R.realSubgroup s r) I p,
            ∃ U : (D.withLattice Λ N hN hin hout).UnitVerticalObservable
                ((R.withLattice Λ N hN hin hout).realSubgroup s r) I ((p + C) ^ C),
              U.frequency = V.frequency ∧ U.lipBound = V.lipBound ∧
              ∀ i x, U.observable i (QuotientGroup.mk x) = V.observable i (QuotientGroup.mk x) := by
  obtain ⟨C, hC, hcover⟩ := exists_native_source_cover
  refine ⟨C, hC, ?_⟩
  intro L M I _ _ _ _ _ _ _ _ _ s t d e r D R E φ p hp hR hE hentries
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast (show 1 ≤ C by omega)
  have hpC : p ≤ (p + C) ^ C := by
    calc
      p ≤ p + C := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (p + C) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega : 1 ≤ C)
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hgeometry, hmap⟩ :=
    hcover D E φ hp hR.1 hE hentries
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout,
    R.withLattice_complexity Λ N hN hin hout hR hpC hgeometry, hmap, ?_⟩
  intro V
  exact ⟨(V.onSublattice R Λ hΛ N hN hin hout).mono hpC, rfl, rfl, fun _ _ => rfl⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.UniformInvariantBudget
namespace OAI

section

namespace Erdos3

theorem exists_uniform_invariantVertical_cost (M : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (m : ℕ), m ≤ M → ∀ p : ℝ, 0 ≤ p →
      invariantVerticalBudget m p ≤ (p + C) ^ C := by
  let B := (Finset.range (M + 1)).sup symmetricUnitConstant
  let X : Polynomial ℕ := Polynomial.X
  let P := Polynomial.C (2 * M + 2) * (2 * X + 1) + Polynomial.C B + X + Polynomial.C M + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro m hm p hp
  have hb : symmetricUnitConstant m ≤ B := Finset.le_sup (f := symmetricUnitConstant)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  have hmr : (m : ℝ) ≤ M := by exact_mod_cast hm
  have hbr : (symmetricUnitConstant m : ℝ) ≤ B := by exact_mod_cast hb
  have hle : invariantVerticalBudget m p ≤
      (2 * M + 2 : ℝ) * (2 * p + 1) + B + p + M + 1 := by
    dsimp [invariantVerticalBudget, symmetricUnitBudget]
    nlinarith
  apply hle.trans
  simpa [P, X] using hbound p hp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedComparisonOrbit
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realPolarizedLog_eval_permute (p : F.realification.adaptedLieSubalgebra)
    (e : Equiv.Perm ι) (he : ∀ i, π (e i) = π i) (x : ι → ℚ) :
    (F.squarefreeBlockPermute π e he).toLinearMap.baseChange ℝ (eval x (F.realPolarizedLog π p)) =
      eval (fun i => x (e.symm i)) (F.realPolarizedLog π p) := by
  rw [F.realPolarizedLog_eval, F.realPolarizedLog_eval]
  simp only [map_sum, LinearMap.map_smul_of_tower, F.realPolarizedCoefficient_permute π p e he]
  symm
  calc
    (∑ a : SquarefreeIndex ι, (a.val.prod fun i n => x (e.symm i) ^ n) •
        F.realPolarizedCoefficient π p a) =
      ∑ a : SquarefreeIndex ι,
        ((SquarefreeIndex.permute e a).val.prod fun i n => x (e.symm i) ^ n) •
        F.realPolarizedCoefficient π p (SquarefreeIndex.permute e a) :=
      (Equiv.sum_comp (SquarefreeIndex.permute e) _).symm
    _ = _ := by simp only [SquarefreeIndex.permute_weight]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def polarizeRealOrbit (p : F.realification.PolynomialOrbit) :
    (F.squarefreeMultidegreeFiltration π).realification.PolynomialOrbit :=
  F.realPolarizedOrbit π
    ⟨PolynomialOrbit.log F.realification p, PolynomialOrbit.adapted F.realification p⟩

theorem polarizeRealOrbit_permute (p : F.realification.PolynomialOrbit)
    (e : Equiv.Perm ι) (he : ∀ i, π (e i) = π i) (x : ι → ℤ) :
    NilpotentLieBCHGroup.mapReal (realificationLieHom (F.squarefreeBlockPermute π e he).toLieHom)
        ((F.squarefreeMultidegreeFiltration π).realification.polynomialOrbitEval x
          (F.polarizeRealOrbit π p)) =
      (F.squarefreeMultidegreeFiltration π).realification.polynomialOrbitEval
        (fun i => x (e.symm i)) (F.polarizeRealOrbit π p) := by
  apply NilpotentLieBCHGroup.ext
  exact F.realPolarizedLog_eval_permute π
    ⟨PolynomialOrbit.log F.realification p, PolynomialOrbit.adapted F.realification p⟩
    e he (fun i => (x i : ℚ))

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def compareRealOrbit (p : F.realification.PolynomialOrbit) :
    (F.comparisonFiltration π).realification.PolynomialOrbit (fun _ : σ => 1) :=
  NilpotentLieFiltration.polynomialOrbitOfLog
    (F := (F.comparisonFiltration π).realification)
    (F.realComparisonLog π ⟨p.log F.realification, p.adapted F.realification⟩)
    (F.realComparisonLog_adapted π ⟨p.log F.realification, p.adapted F.realification⟩)

theorem compareRealOrbit_zero (p : F.realification.PolynomialOrbit) :
    (F.comparisonFiltration π).realification.polynomialOrbitEval (fun _ => 1) 0
      (F.compareRealOrbit π p) = 1 := by
  apply NilpotentLieBCHGroup.ext
  change eval (fun _ => 0)
    (F.realComparisonLog π ⟨p.log F.realification, p.adapted F.realification⟩) = 0
  rw [eval_zero_eq_coefficient, F.realComparisonLog_coefficient, F.realComparisonCoefficient_zero_index]

theorem compareRealOrbit_projections (p : F.realification.PolynomialOrbit)
    (hp : F.realification.polynomialOrbitEval 0 p = 1) (x : σ → ℤ) :
    NilpotentLieBCHGroup.mapReal (realificationLieHom (F.comparisonFirst π))
        ((F.comparisonFiltration π).realification.polynomialOrbitEval (fun _ => 1) x
          (F.compareRealOrbit π p)) = F.realification.polynomialOrbitEval x p ∧
      NilpotentLieBCHGroup.mapReal (realificationLieHom (F.comparisonSecond π))
        ((F.comparisonFiltration π).realification.polynomialOrbitEval (fun _ => 1) x
          (F.compareRealOrbit π p)) =
      (F.squarefreeMultidegreeFiltration π).realification.polynomialOrbitEval
        (fun j => x (π j)) (F.polarizeRealOrbit π p) := by
  have hz : coefficients (p.log F.realification) 0 = 0 := by
    have h := congrArg NilpotentLieBCHGroup.coord hp
    change eval (fun _ => 0) (p.log F.realification) = 0 at h
    rwa [eval_zero_eq_coefficient] at h
  constructor
  · apply NilpotentLieBCHGroup.ext
    exact F.realComparisonLog_first_eval π
      ⟨p.log F.realification, p.adapted F.realification⟩ hz (fun i => (x i : ℚ))
  · apply NilpotentLieBCHGroup.ext
    exact F.realComparisonLog_second_eval π
      ⟨p.log F.realification, p.adapted F.realification⟩ hz (fun i => (x i : ℚ))

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem comparisonSpaceOrbit_projections (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B)
    (E : RationalFilteredNilmanifold
      (M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))
      (max s (Fintype.card (ReplicatedIndex bound))) r)
    (hEL : E.lattice = M.comparisonLattice p B hB hstable)
    (g : M.filtration.realification.PolynomialOrbit)
    (hg : M.filtration.realification.polynomialOrbitEval 0 g = 1) (x : σ → ℤ) :
    let π := fun i : ReplicatedIndex bound => i.1
    let z := (M.filtration.comparisonFiltration π).realification.polynomialOrbitEval
      (fun _ => 1) x (M.filtration.compareRealOrbit π g)
    M.comparisonFirstSpace p B hB hstable E hEL (QuotientGroup.mk z) =
      QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g) ∧
    M.comparisonSecondSpace p B hB hstable E hEL (QuotientGroup.mk z) =
      QuotientGroup.mk ((M.filtration.squarefreeMultidegreeFiltration π).realification.polynomialOrbitEval
        (fun i => x (π i)) (M.filtration.polarizeRealOrbit π g)) := by
  have h := M.filtration.compareRealOrbit_projections
    (fun i : ReplicatedIndex bound => i.1) g hg x
  constructor
  · simpa only [comparisonFirstSpace_mk, realificationMap] using
      congrArg (fun y : D.RealGroup => (QuotientGroup.mk y : D.Space)) h.1
  · simpa only [comparisonSecondSpace_mk, realificationMap] using
      congrArg (fun y : (M.squarefreeModel p B hB hstable).RealGroup =>
        (QuotientGroup.mk y : (M.squarefreeModel p B hB hstable).Space)) h.2

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_normalized_comparison_orbit (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B)
    (E : RationalFilteredNilmanifold
      (M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))
      (max s (Fintype.card (ReplicatedIndex bound))) r)
    (hEF : E.filtration = M.filtration.comparisonFiltration (fun j : ReplicatedIndex bound => j.1))
    (hEL : E.lattice = M.comparisonLattice p B hB hstable)
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ) :
    let g₀ := M.filtration.realification.normalizeMultidegreeOrbit g ε γ
    ∃ h : E.filtration.realification.PolynomialOrbit (fun _ : σ => 1),
      E.filtration.realification.polynomialOrbitEval _ 0 h = 1 ∧
      ∀ x : σ → ℤ,
        ε • M.comparisonFirstSpace p B hB hstable E hEL
          (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval _ x h)) =
            QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g) ∧
        M.comparisonSecondSpace p B hB hstable E hEL
          (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval _ x h)) =
            QuotientGroup.mk
              ((M.filtration.squarefreeMultidegreeFiltration (fun j : ReplicatedIndex bound => j.1)).realification.polynomialOrbitEval
                (fun j => x j.1) (M.filtration.polarizeRealOrbit (fun j : ReplicatedIndex bound => j.1) g₀)) := by
  let π := fun j : ReplicatedIndex bound => j.1
  let g₀ := M.filtration.realification.normalizeMultidegreeOrbit g ε γ
  have hg₀ : M.filtration.realification.polynomialOrbitEval 0 g₀ = 1 :=
    M.filtration.realification.normalizeMultidegreeOrbit_zero g ε γ hfactor
  have hF : (M.filtration.comparisonFiltration π).realification = E.filtration.realification := by rw [hEF]
  let h := (M.filtration.comparisonFiltration π).realification.orbitEquivOfEq hF (fun _ : σ => 1)
    (M.filtration.compareRealOrbit π g₀)
  have heval (x : σ → ℤ) : E.filtration.realification.polynomialOrbitEval _ x h =
      (M.filtration.comparisonFiltration π).realification.polynomialOrbitEval _ x
        (M.filtration.compareRealOrbit π g₀) :=
    (M.filtration.comparisonFiltration π).realification.orbitEquivOfEq_eval hF _ _ x
  refine ⟨h, (heval 0).trans (M.filtration.compareRealOrbit_zero π g₀), fun x => ?_⟩
  rw [heval]
  obtain ⟨h₁, h₂⟩ := M.comparisonSpaceOrbit_projections p B hB hstable E hEL g₀ hg₀ x
  constructor
  · rw [h₁]
    change (QuotientGroup.mk (ε * M.filtration.realification.polynomialOrbitEval x g₀) : D.Space) = _
    change (QuotientGroup.mk (ε * M.filtration.realification.polynomialOrbitEval x
      (M.filtration.realification.normalizeMultidegreeOrbit g ε γ)) : D.Space) = _
    rw [M.filtration.realification.normalizeMultidegreeOrbit_eval]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
    exact QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ)
  · exact h₂

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedResidueLabelCount
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Classical

theorem standardLatticeCoordinates_card {D I J : Type*}
    [Fintype D] [Fintype I] [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) :
    Fintype.card (J ⊕ I) = Fintype.card D := by
  simpa only [Module.finrank_fintype_fun_eq_card] using
    (standardLatticeCoordinates W bW bP hP).finrank_eq.symm

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {n : Fin m → ℕ}
variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

end Erdos3.VectorPolynomial

end

end OAI

end


