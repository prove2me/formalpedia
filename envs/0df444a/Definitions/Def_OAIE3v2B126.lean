-- Prove2me | Definitions.Def_OAIE3v2B126
-- name    : OAIE3v2B126
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:02:08.136983+00:00
-- url     : https://prove2.me/theorems/1d675e83-9580-4477-8583-a7c5cccfe69e
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 128 of 311
-- statement:
--   Definitions bundle 128 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B101`, `OAIE3v2B103`, `OAIE3v2B104`, `OAIE3v2B105`, `OAIE3v2B110`, `OAIE3v2B111`, `OAIE3v2B112`, `OAIE3v2B113` of this split.
--
--   Modules: `Dynamics/PreparedFiniteNestedCanonicalEarlyPrimitiveBudget.lean`, `Estimates/AllocatedErrorInterpolation.lean`, `Estimates/AllocatedFiberCap.lean`, `Estimates/AllocatedIdealSiteReconstruction.lean`, `Estimates/AllocatedOriginalSampleFullSliceLipschitz.lean`, `Estimates/AllocatedOriginalSampleQuadratureUniformBounds.lean`, `Estimates/AllocatedProfileDimensions.lean`, `Estimates/AllocatedRelativeChildSliceGeometry.lean`, `Estimates/AllocatedScalarLogBounds.lean`, `Estimates/AllocatedTailProfileIdentity.lean`, `Estimates/AllocatedTrimmedVectorSite.lean`, `Estimates/CanonicalScalarSourceEnvelope.lean`, `Estimates/CoefficientJetScalar.lean`, `Estimates/FiniteProductCellMean.lean`, `Estimates/PositiveNormalizationError.lean`, `Estimates/RelativePatchSourceTestFinBounds.lean`, `Estimates/UnconditionedSmoothSlopeCap.lean`, `Geometry/AllocatedNaturalChartScale.lean`, `Geometry/CenteredCoefficientDeckChartMeasurable.lean`, `Geometry/ControlledIntegralCoordinates.lean`, `Geometry/MixedCoveredChartCompact.lean`, `Geometry/ProductEquivTransport.lean`, `Geometry/UnconditionedSpatialWidthBudget.lean`, `Lattices/AllocatedResidueInterpolationMixture.lean`, `Lattices/ForecastIntegerAxisSplit.lean`, `Lattices/IntegerPMFNormalizedSource.lean`, `Lattices/SelectedResidueApproximation.lean`, `Lattices/SelectedResidueRefinementMean.lean`, `Lattices/SelectedResidueScalarReindex.lean`, `Lattices/StrideSelectedResidueBadProduct.lean`, `Lattices/WeightedCubeIntegerSupport.lean`, `Linear/AllocatedKernelScaleWithCutoff.lean`, `Linear/SpatialMatrixBlockWideProbability.lean`, `Polynomial/ForecastSlicedEarlyUnrestrictedPolynomialBudget.lean`, `Polynomial/PatchTopNetPolynomialBudget.lean`, `Polynomial/PreparedPolynomialPhysicalBadProductSource.lean`, `Probability/AllocatedDensityParameterBounds.lean`, `Probability/AllocatedFrozenJetDensity.lean`, `Probability/AllocatedLongJetMixture.lean`, `Probability/AllocatedPrescribedRefinedDensity.lean`, `Probability/AllocatedSlicedIdealDensity.lean`, `Probability/CanonicalConstantDensityBound.lean`, `Probability/CylinderJointMass.lean`, `Probability/ObservedDensityTesting.lean`, `Probability/SelectedDensityTestMass.lean`, `Sampling/AllocatedActiveGridPlateau.lean`, `Sampling/AllocatedFrozenGridLaw.lean`, `Sampling/AllocatedLongGridCoordinates.lean`, `Sampling/AllocatedLongGridIntegral.lean`, `Sampling/AllocatedProbabilityGrid.lean`, `Sampling/CeilGridScaleRatio.lean`, `Sampling/ForecastInactiveSlicedCappedContinuousSource.lean`, `Sampling/ForecastJointScaleNormalization.lean`, `Sampling/ForecastRawSpatialBoxReorder.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B101
import Definitions.Def_OAIE3v2B103
import Definitions.Def_OAIE3v2B104
import Definitions.Def_OAIE3v2B105
import Definitions.Def_OAIE3v2B110
import Definitions.Def_OAIE3v2B111
import Definitions.Def_OAIE3v2B112
import Definitions.Def_OAIE3v2B113

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
namespace OAI

section

namespace Erdos3

theorem residueSmoothPMF_congr {K X : Type*} [Fintype K] [Fintype X]
    (r s : K × X → ℤ) (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hrs : ∀ z, (modulus z.2 : ℤ) ∣ s z - r z)
    (hr : 0 < shiftedSmoothProductMass (residueProfileCenter r modulus) (residueProfileWidth modulus V))
    (hs : 0 < shiftedSmoothProductMass (residueProfileCenter s modulus) (residueProfileWidth modulus V)) :
    residueSmoothPMF r modulus hmodulus V hV hr = residueSmoothPMF s modulus hmodulus V hV hs := by
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  simp only [residueSmoothPMF_conditional_weight, residueSmoothWeight_congr r s modulus V hrs]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem selectedResidueSmoothPMF_mixture {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (G : Finset (ColumnResiduePattern K I modulus)) (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (hc : ∀ r : G, 0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus) (residueProfileWidth modulus V))
    (φ : (K × I → ℤ) → ℂ) :
    (∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * φ x) =
      ∑ r : G, (((∑' y, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V y) /
          (∑' y, selectedResidueSmoothWeight modulus G V y) : ℝ) : ℂ) *
        (∑' x, ((residueSmoothPMF (columnResidueRepresentative modulus r.val) modulus hmodulus V hV (hc r) x).toReal : ℂ) * φ x) := by
  have hcell (r : G) : 0 < ∑' x, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x := by
    rw [← residueSmoothWeight_mass _ modulus hmodulus V hV]
    exact hc r
  have ht := selectedResidueSmoothWeight_mass modulus G V hV
  have htotal : 0 < ∑ r : G, ∑' x, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x := by
    rwa [← ht]
  simp_rw [selectedResidueSmoothPMF_toReal, residueSmoothPMF_conditional_weight, ht,
    selectedResidueSmoothWeight_eq_sum]
  exact finite_supported_normalized_mixture _ (rectangularWeightIndices 0 V 1)
    (fun r => residueSmoothWeight_zero_off _ modulus V hV) hcell htotal φ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveNormalizationError
namespace OAI

section

namespace Erdos3

theorem selectedResidueDensityPMF_remove_normalization {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus T W D)
    (f : (K × I → ℤ) → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1) :
    ‖(∑' z, ((selectedResidueDensityPMF modulus T W hW hZ D hD0 hD z).toReal : ℂ)*f z) -
      (∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*((D z : ℂ)*f z))‖ ≤
        |selectedResidueDensityMass modulus T W D-1| := by
  rw [selectedResidueDensityPMF_complexMean]
  apply complex_remove_normalization hD
  rw [← selectedResidueFiniteLaw_complexMean modulus T W hW hZ (fun z => (D z : ℂ)*f z),
    ← selectedResidueFiniteLaw_densityMass modulus T W hW hZ D]
  exact FiniteProbabilityWeights.norm_density_weighted_complexMean_le
    (selectedResidueFiniteLaw modulus T W hW hZ)
    (fun z => D z.val) (fun z => hD0 z.val) (fun z => f z.val) (fun z => hf z.val)

theorem selectedResidueDensityPMF_error_of_bounded_test {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus T W D)
    (f : (K × I → ℤ) → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1)
    {a : ℂ} {ε η : ℝ}
    (herror : ‖(∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*
      (f z*(D z : ℂ)))-a‖ ≤ ε)
    (hmass : |selectedResidueDensityMass modulus T W D-1| ≤ η) :
    ‖(∑' z, ((selectedResidueDensityPMF modulus T W hW hZ D hD0 hD z).toReal : ℂ)*f z)-a‖ ≤ η+ε := by
  have hcomm : (∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*
      ((D z : ℂ)*f z)) =
      ∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*(f z*(D z : ℂ)) := by
    apply tsum_congr
    intro z
    rw [mul_comm (D z : ℂ) (f z)]
  have herror' : ‖(∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*
      ((D z : ℂ)*f z))-a‖ ≤ ε := by
    rw [hcomm]
    exact herror
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add
    ((selectedResidueDensityPMF_remove_normalization modulus T W hW hZ D hD0 hD f hf).trans hmass)
    herror')

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedCubeIntegerSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerGridMass {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) (z : J → ℤ) : ℝ :=
  finiteImageMass p (fun x => integerGridResidue M (Y x)) (integerGridResidue M z)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerGridDensity {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (K M : ℕ) (z : J → ℤ) : ℝ :=
  (K : ℝ) ^ Fintype.card J * integerGridMass p Y M z

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerPMFNormalizedSource
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem scalarCubeResidueWeights_empty_one_mean (L : ℕ) (hL : 0 < L) (f : ℤ → ℝ) :
    (scalarCubeResidueWeights Empty L 1 hL (fun _ => 1) (fun _ => 0)
      (fun _ => by norm_num) (fun _ => le_rfl) (by change 1 ≤ L; exact Nat.succ_le_iff.mpr hL)).mean
      (fun x => f (x none : ℤ)) =
        (∑ k ∈ Finset.Ico 0 (L : ℤ), f k) / (L : ℝ) := by
  rw [scalarCubeResidueWeights_mean]
  calc
    _ = 𝔼 k : coefficientResidueSet L 1 0, f k :=
      Fintype.expect_equiv (emptyScalarCubeResidueEquiv L (fun _ => 1) (fun _ => 0))
        _ _ (fun _ => rfl)
    _ = _ := by
      have hr : coefficientResidueSet L 1 0 = Finset.Ico 0 (L : ℤ) := by
        ext k
        simp only [coefficientResidueSet, Finset.mem_filter]
        exact ⟨And.left, fun hk => ⟨hk, Subsingleton.elim _ _⟩⟩
      rw [hr, Fintype.expect_eq_sum_div_card]
      simp [Finset.sum_attach]

noncomputable def normalizedScalarCubeSourceOfIntegerPMF
    (L : ℕ) (hL : 0 < L) (p : PMF ℤ)
    (hs : ∀ k, p k ≠ 0 → k ∈ Finset.Ico 0 (L : ℤ))
    (w : (Option Empty → ℝ) → ℝ) (B T : ℝ≥0) (hB : 0 < B)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hgrid : ∀ k : ℤ, w (fun _ => (k : ℝ) / L) = L * (p k).toReal) :
    NormalizedScalarCubeSource Empty where
  length := L
  modulusBound := 1
  length_pos := hL
  modulus := fun _ => 1
  residue := fun _ => 0
  modulus_pos := fun _ => by norm_num
  modulus_le := fun _ => le_rfl
  size := by change 1 ≤ L; exact Nat.succ_le_iff.mpr hL
  weight := w
  weightBound := B
  weightLipschitz := T
  weightBound_pos := hB
  weight_range := hw
  weight_lipschitz := hLip
  normalized := by
    have he (x : IntegerScalarCubeBox Empty L) :
        w (fun i => (x i : ℝ) / L) = w (fun _ => (x none : ℝ) / L) := by
      congr 1
      funext i
      cases i with
      | none => rfl
      | some e => exact e.elim
    simp only [he]
    refine (scalarCubeResidueWeights_empty_one_mean L hL
      (fun k => w (fun _ => (k : ℝ) / L))).trans ?_
    simp_rw [hgrid]
    rw [← Finset.mul_sum, pmf_interval_toReal_mass L p hs, mul_one]
    exact div_self (by exact_mod_cast (Nat.ne_of_gt hL))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def normalizedUniformCubeSource (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L) :
    NormalizedScalarCubeSource I where
  length := L
  modulusBound := M
  length_pos := hL
  modulus := m
  residue := r
  modulus_pos := hm
  modulus_le := hmM
  size := hsize
  weight := fun _ => 1
  weightBound := 1
  weightLipschitz := 0
  weightBound_pos := by norm_num
  weight_range := fun _ => by norm_num
  weight_lipschitz := LipschitzWith.const 1
  normalized := (scalarCubeResidueWeights I L M hL m r hm hmM hsize).mean_const 1

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def principalNormalizedSource {K T γ : ℝ}
    (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) :
    NormalizedScalarCubeSource Empty :=
  normalizedScalarCubeSourceOfIntegerPMF
    (principalIntervalLength K T γ) (principalIntervalLength_pos hK hT hγ)
    (principalIntegerPMF K T γ hK hT hγ hlarge)
    (fun k hk => principalIntervalLength_support hK hT hγ hlarge hk)
    (principalIntervalWeight K T γ) 16 (128 * probabilityProfileLipschitz) (by norm_num)
    (principalIntervalWeight_range hK hT hγ hlarge)
    (principalIntervalWeight_lipschitz hK hT hγ hlarge)
    (principalIntervalWeight_grid hK hT hγ hlarge)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

local notation "profile" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

noncomputable def allocatedPrincipalNormalizedSource : NormalizedScalarCubeSource Empty :=
  principalNormalizedSource
    (K := (basisAxisScale (basis j) i : ℝ)) (T := (S.value : ℝ) ^ (j.val + 1))
    (γ := profile)
    (by exact_mod_cast basisAxisScale_pos (basis j) i)
    (pow_pos (by exact_mod_cast S.positive) _) (principalProfileSize_pos (hR j) _)
    (integerAxisPrincipal_width (Nat.zero_lt_succ _) S.positive
      (principalProfileSize_pos (hR j) _) (S.gap j i hactive))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientJetScalar
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}

noncomputable def coefficientJetScalarReference :
    ∀ a : LayerSamplerAxis I n, Measure (CoefficientJetScalar a)
  | ⟨_, .inl _⟩ => (volume : Measure ℝ)
  | ⟨_, .inr _⟩ => (Measure.count : Measure ℤ)

instance coefficientJetScalarReference_sigmaFinite (a : LayerSamplerAxis I n) :
    SigmaFinite (coefficientJetScalarReference a) := by
  rcases a with ⟨j, i | i⟩
  · change SigmaFinite (volume : Measure ℝ)
    infer_instance
  · change SigmaFinite (Measure.count : Measure ℤ)
    infer_instance

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CanonicalConstantDensityBound
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped BigOperators

theorem canonicalMixedDensity_constant_cap {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)
    {R V : ℝ} (hR : 0 < R) (hV : 0 ≤ V) (hv : mixedDensityCovolumeRatio W b ≤ V)
    (y : W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) :
    canonicalMixedDensity W b hb o (fun _ => 0) (fun _ => R / 4)
        (latticeConstantMass W b (fun _ => R / 4) (fun _ => div_pos hR (by norm_num))) y ≤
      earlyConstantDensityCap (Fintype.card I) n R V := by
  have hvolume : ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) ≤
      V * ∏ i, (basisAxisScale b i : ℝ) :=
    (div_le_iff₀ (Finset.prod_pos (fun i _ => basisAxisScale_cast_pos b i))).mp hv
  have hbound (x : W × (Fin n → ℤ)) :
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) *
        orthonormalMixedDensity o (fun _ => 0) (fun _ => R / 4)
          (latticeConstantMass W b (fun _ => R / 4) (fun _ => div_pos hR (by norm_num))) x ≤
        earlyConstantDensityCap (Fintype.card I) n R V := by
    change ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) *
      constantCoefficientDensity (fun _ : I => R / 4) (fun i => (basisAxisScale b i : ℝ))
        (fun _ => R / 4) (basisAxisScale_cast_pos b) (fun _ => div_pos hR (by norm_num))
        ((orthonormalMixedChart o).symm x) ≤ _
    have hc := constantCoefficientDensity_cap (fun _ : I => R / 4)
      (fun _ => div_pos hR (by norm_num)) (fun i => (basisAxisScale b i : ℝ))
      (fun _ => R / 4) (basisAxisScale_cast_pos b) (fun _ => div_pos hR (by norm_num))
      hV hvolume ((orthonormalMixedChart o).symm x)
    exact hc.trans_eq (by simp only [earlyConstantDensityCap, profileWidthFactor,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin])
  exact normalizedQuotientDensity_bound W b hb (standardLatticeSmallBox_isOpen D).measurableSet
    (Set.Subset.rfl) _ (earlyConstantDensityCap_nonneg _ _ hR hV) hbound y

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFiberCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (V : Fin m → ℝ) (hV : ∀ j, 0 ≤ V j)
variable (hv : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hV hv in
theorem allocatedCoefficientFactor_constant_cap
    (s : CoefficientSlot (LayerSamplerVariables G I n B) m) (hs : s.2.val = 0)
    (y : SubspaceArrayTorus Unit (U s.1)) :
    canonicalCoefficientFactor U b hb o (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
        (allocatedLayerIntegerPMFs B U b hR hσ S) s y ≤
      earlyConstantDensityCap (Fintype.card (I s.1)) (n s.1) (R s.1) (V s.1) := by
  rcases s with ⟨j, d⟩
  have hd : d = constantCoefficientSlot _ _ := Subtype.ext hs
  subst d
  simpa only [canonicalCoefficientFactor, allocatedLayerCenters_constant,
    allocatedLayerWidths_constant, allocatedLayerIntegerPMFs_constant] using
    canonicalMixedDensity_constant_cap (euclideanSubspace (U j)) (b j) (hb j) (o j)
      (hR j) (hV j) (hv j) ((euclideanSubspaceTorusEquiv (U j)).symm y)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3

theorem mem_rectangularWeightIndices_zero_iff {I : Type*} [Fintype I]
    (W : I → ℝ) (z : I → ℤ) :
    z ∈ rectangularWeightIndices 0 W 1 ↔ ∀ i, |(z i : ℝ)| ≤ W i := by
  classical
  constructor
  · exact fun hz => rectangularWeightIndices_zero_bound W hz
  · intro hz
    apply Fintype.mem_piFinset.mpr
    intro i
    change z i ∈ sampledWeightIndices 0 (W i) 1
    simp only [sampledWeightIndices, mul_one, zero_sub, zero_add, Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr (abs_le.mp (hz i)).1, Int.le_floor.mpr (abs_le.mp (hz i)).2⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StrideSelectedResidueBadProduct
namespace OAI

section

namespace Erdos3

open scoped Classical

noncomputable def selectedResidueTiltedFiniteLaw {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) :
    FiniteProbabilityWeights (rectangularWeightIndices 0 V 1) :=
  (selectedResidueFiniteLaw modulus G V hV hZ).reweightPositive (fun x => D x.val)
    (fun x => hD0 x.val) (by rw [selectedResidueFiniteLaw_densityMass]; exact hD)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ControlledIntegralCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (e : Basis (Fin d) ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

noncomputable def integralOrderedBasisProduct (B : ℕ) (z : Fin d → ℤ) :
    NilpotentLieBCHGroup L s hnil :=
  orderedBasisProduct e hnil (fun j => (B : ℚ) * (z j : ℚ))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i

include hR hσ hσ1 in
theorem allocatedKernelProfile_bound (d) : |centers d|+widths d ≤ R j :=
  (allocatedProfile_term_bound (layerIntegerPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (layerIntegerPrincipalSlots_not_constant B j i) (hR j) (hσ j) hσ1 d).trans (by linarith [hR j])

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedLongJetMixture
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

noncomputable def allocatedLongJetMap (c : AllocatedLongCoefficients B U basis S) :
    AllocatedLongJetRows B U basis S O :=
  fun a => coefficientJetAxisMap (allocatedPartitionedJetMatrix B U basis S x u v rows) a.val (c a)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueRefinementMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {K X : Type*} [Fintype K] [Fintype X]

noncomputable def selectedResidueCellWeight (modulus : X → ℕ)
    (T : Finset (ColumnResiduePattern K X modulus)) (V : K × X → ℝ) (r : T) : ℝ :=
  (∑' z, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V z) /
    (∑' z, selectedResidueSmoothWeight modulus T V z)

theorem selectedResidueCellWeight_nonneg (modulus : X → ℕ)
    (T : Finset (ColumnResiduePattern K X modulus)) (V : K × X → ℝ) (r : T) :
    0 ≤ selectedResidueCellWeight modulus T V r := by
  apply div_nonneg
  · apply tsum_nonneg
    intro z
    unfold residueSmoothWeight
    split
    · exact (smoothProductProfile_range (K × X) _).1
    · exact le_rfl
  · exact tsum_nonneg (selectedResidueSmoothWeight_nonneg modulus T V)

theorem selectedResidueCellWeight_sum (modulus : X → ℕ)
    (T : Finset (ColumnResiduePattern K X modulus)) (V : K × X → ℝ)
    (hV : ∀ z, 0 < V z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z) :
    (∑ r : T, selectedResidueCellWeight modulus T V r) = 1 := by
  simp only [selectedResidueCellWeight, ← Finset.sum_div]
  rw [← selectedResidueSmoothWeight_mass modulus T V hV, div_self hZ.ne']

theorem selectedResidueSmoothPMF_bounded_mixture (modulus : X → ℕ)
    (hmodulus : ∀ x, 0 < modulus x) (T : Finset (ColumnResiduePattern K X modulus))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus V)) (φ : (K × X → ℤ) → ℂ) :
    (∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) * φ z) =
      ∑ r : T, (selectedResidueCellWeight modulus T V r : ℂ) *
        ∑' z, ((residueSmoothPMF (boundedColumnResidueRepresentative modulus r.val)
          modulus hmodulus V hV (hc r) z).toReal : ℂ) * φ z := by
  have hm (r : T) := residueSmoothMass_congr _ _ modulus hmodulus V hV
    (boundedColumnResidueRepresentative_congr modulus r.val)
  have ho (r : T) : 0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus V) := by rw [hm r]; exact hc r
  rw [selectedResidueSmoothPMF_mixture modulus hmodulus T V hV hZ ho]
  apply Finset.sum_congr rfl
  intro r _
  rw [residueSmoothPMF_congr _ _ modulus hmodulus V hV
    (boundedColumnResidueRepresentative_congr modulus r.val) (ho r) (hc r)]
  rfl

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {K X Y : Type*} [Fintype K] [Fintype X]

theorem selectedResidueSmoothPMF_bind_toReal_mixture
    (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (T : Finset (ColumnResiduePattern K X q))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative q r.val) q)
      (residueProfileWidth q V))
    (F : (K × X → ℤ) → PMF Y) (y : Y) :
    (((selectedResidueSmoothPMF q T V hV hZ).bind F) y).toReal =
      ∑ r : T, selectedResidueCellWeight q T V r *
        (((residueSmoothPMF (boundedColumnResidueRepresentative q r.val)
          q hq V hV (hc r)).bind F) y).toReal := by
  apply Complex.ofReal_injective
  simp only [pmf_bind_toReal, Complex.ofReal_tsum, Complex.ofReal_sum, Complex.ofReal_mul]
  exact selectedResidueSmoothPMF_bounded_mixture q hq T V hV hZ hc
    (fun z => ((F z y).toReal : ℂ))

theorem selectedResidueSmoothPMF_bind_le_of_cells
    (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (T : Finset (ColumnResiduePattern K X q))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative q r.val) q)
      (residueProfileWidth q V))
    (F : (K × X → ℤ) → PMF Y) (y : Y) (δ : ℝ)
    (hbound : ∀ r : T, (((residueSmoothPMF (boundedColumnResidueRepresentative q r.val)
      q hq V hV (hc r)).bind F) y).toReal ≤ δ) :
    (((selectedResidueSmoothPMF q T V hV hZ).bind F) y).toReal ≤ δ := by
  rw [selectedResidueSmoothPMF_bind_toReal_mixture q hq T V hV hZ hc F y]
  calc
    _ ≤ ∑ r : T, selectedResidueCellWeight q T V r * δ :=
      Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (hbound r)
        (selectedResidueCellWeight_nonneg q T V r))
    _ = δ := by rw [← Finset.sum_mul, selectedResidueCellWeight_sum q T V hV hZ, one_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedResidueInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (a : D) (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ L ⟨a, b, v⟩)

noncomputable def principalSupportedAxisSources (b : B a) (v : Fin (h a)) :
    NormalizedScalarCubeSource α :=
  normalizedUniformCubeSource α (L ⟨a, b, v⟩) q (hL ⟨a, b, v⟩) (fun _ => q) (r ⟨a, b, v⟩)
    (fun _ => hq) (fun _ => le_rfl) (hsize b v)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

noncomputable def allocatedPhysicalEntryBudget : ℝ :=
  1 + allocatedPhysicalRootBudget B U basis S c + (S.value : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedPhysicalRootBudget_zero :
    allocatedPhysicalRootBudget B U b S (fun _ => 0) =
      Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ) := by
  simp only [allocatedPhysicalRootBudget, Int.cast_zero, abs_zero, Finset.sum_const_zero, zero_add]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFrozenGridLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

def AllocatedFrozenSupported (a : AllocatedFrozenCoefficients B U b S) : Prop :=
  ∀ (j : Fin m) (i : Fin (n j)) (hi : grid ⟨j, Sum.inr i⟩) d,
    a ⟨⟨j, Sum.inr i⟩, hi⟩ d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S j i d).support

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedFrozenJetDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

noncomputable def allocatedGridJetFactor :
    ∀ a : {a // grid a}, CoefficientJetAxisRow O a.val → ℝ
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, _⟩ => fun z =>
      (integerMatrixImagePMF (boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j))
        (allocatedLayerIntegerPMFs B U b hR hσ S j i) z).toReal

noncomputable def allocatedGridJetDensity (z : AllocatedFrozenJetRows B U b S O) : ℝ :=
  ∏ a, allocatedGridJetFactor B U b hR hσ S x u v rows a (z a)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CeilGridScaleRatio
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

noncomputable def allocatedPrincipalGridScale : ℕ :=
  ⌈gamma * (basisAxisScale (basis j) i : ℝ)⌉₊

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedNaturalChartScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*}
variable {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) (j : Fin m) (i : Fin (n j))

local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i

noncomputable def allocatedPrincipalChartRatio : ℝ :=
  (basisAxisScale (basis j) i : ℝ) / scale

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedProbabilityGrid
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

noncomputable def allocatedGridNormalizedRows (z : AllocatedFrozenJetRows B U b S O) :
    ∀ a : {a // grid a}, O a.val.1 → ℝ
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, ha⟩ => fun t => (z ⟨⟨j, .inr i⟩, ha⟩ t : ℝ) / basisAxisScale (b j) i

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PatchTopNetPolynomialBudget
namespace OAI

section

namespace Erdos3

theorem exists_patch_top_net_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d : ℕ) (M L p : ℝ),
      0 ≤ p → 0 ≤ M → 0 ≤ L → (d : ℝ) ≤ p → M ≤ Real.exp p → L ≤ Real.exp p →
      ∃ N : ℕ, 0 < N ∧ ((N + 1 : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (((N + 1) ^ (d * (d + 1) ^ s) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        patchTopNetError d s N M < 1 / 4 ∧
        L * patchTopNetError d s N M ≤ Real.exp (-p) / 2 := by
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := Polynomial.C s + Polynomial.C s * X + X + 4 +
    Polynomial.C s * Polynomial.C s * X * (X + 1) + 2 * X + 6
  let I : Polynomial ℕ := X * (X + 1) ^ s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget (Q + I * Q)
  refine ⟨C, hC, ?_⟩
  intro d M L p hp hM hL hd hMp hLp
  let q := patchTopNetNumeratorLog s p + 2 * p + 6
  have hq : 0 ≤ q := by
    have := patchTopNetNumeratorLog_nonneg s hp
    dsimp only [q]
    positivity
  have hcount : 0 ≤ p * (p + 1) ^ s := by positivity
  have ht : q + p * (p + 1) ^ s * q ≤ (p + 2) ^ C := by
    simpa [Q, I, X, q, patchTopNetNumeratorLog, Polynomial.eval₂_pow] using hbudget p hp
  have hqp : q ≤ (p + 2) ^ C := by nlinarith
  have hcp : p * (p + 1) ^ s * q ≤ (p + 2) ^ C := by linarith
  obtain ⟨N, hN, hNbound, hsmall, hloss⟩ := exists_small_patch_top_mesh d s hp hM hL hd hMp hLp
  refine ⟨N, hN, hNbound.trans (Real.exp_le_exp.mpr hqp), ?_, hsmall, hloss⟩
  have hdc : ((d * (d + 1) ^ s : ℕ) : ℝ) ≤ p * (p + 1) ^ s := by
    push_cast
    gcongr
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp q) ^ (d * (d + 1) ^ s) := pow_le_pow_left₀ (by positivity) hNbound _
    _ = Real.exp (((d * (d + 1) ^ s : ℕ) : ℝ) * q) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (p * (p + 1) ^ s * q) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hdc hq)
    _ ≤ _ := Real.exp_le_exp.mpr hcp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedDensityParameterBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)

noncomputable def allocatedNormalizedProfileJet (a : LayerSamplerAxis I n)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ)
    (r : SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) (o : O) : ℝ :=
  booleanCoefficient (fun t => MvPolynomial.eval (normalizedCubeTuple input fixedReal y t)
    (allocatedAxisProfilePolynomial B R σ a r)) (rows o)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a)
local notation "activeCoefficient" => ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) grid
local notation "realOutput" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

noncomputable def allocatedNormalizedLongJetMap (y : activeInput → ℝ) :
    (activeCoefficient → ℝ) → (realOutput → ℝ) :=
  sigmaAxisSampler (fun a : {a // ¬grid a} =>
    allocatedNormalizedProfileJet B U basis S x u (rows a.val.1) a.val y)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoveredChartCompact
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable [∀ j, Fintype (O j)] [∀ j, Fintype (E j)]

instance mixedCoveredJetRawReference_isFiniteMeasureOnCompacts (d : ℕ) [NeZero d] :
    IsFiniteMeasureOnCompacts
      (mixedCoveredJetRawReference (I := I) (O := O) (E := E) (n := n) d) := by
  let hc : ∀ j, IsFiniteMeasureOnCompacts
      (Measure.count : Measure (Fin (n j) → O j → ℤ)) := fun j => by
    constructor
    intro K hK
    exact Measure.count_apply_lt_top.mpr hK.finite_of_discrete
  let hm : ∀ j, IsFiniteMeasureOnCompacts
      (mixedArrayReference (I j) (Fin (n j)) (O j)) := fun j => by
    unfold mixedArrayReference
    infer_instance
  unfold mixedCoveredJetRawReference
  infer_instance

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedPrescribedRefinedDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "axis" => coefficientJetAxisEquiv O I n

variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]

noncomputable def allocatedCoveredFixedFactor
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))
    (r : ∀ j, O j → Q j → ZMod d) : ℝ :=
  allocatedGridJetDensity B U b hR hσ S x u v rows (fun a => axis z a.val) *
    coefficientDeckJetDensity root dirs rows d r / coveredJetArrayScale (O := O) U

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedErrorInterpolation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U b S.value

noncomputable def allocatedGridJetScale : ℝ :=
  ∏ a : {a // grid a}, (allocatedGridAxisScale B U b S a : ℝ) ^ Fintype.card (O a.val.1)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedPrincipalIndex_card_le_variables :
    Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) ≤
      Fintype.card (LayerSamplerVariables G I n B) := by
  change _ ≤ Fintype.card (G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n))
  rw [Fintype.card_sum]
  omega

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedActiveGridPlateau
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}

local notation "ig" => allocatedGridIntegerAxis B U b S

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

def allocatedGridIntegerValues (a : gridAxes) (z : CoefficientJetAxisRow (rowTypes) a.val) :
    rowSets (ig a).1 → ℤ := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact z

noncomputable def allocatedGridNaturalScale (a : gridAxes) : ℕ :=
  allocatedPrincipalGridScale (G := G) B U b (R := R) (ig a).1 (ig a).2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTailProfileIdentity
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z]
  [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  (h : D → ℕ) (P : D → Prop) [DecidablePred P]
  (sets : ∀ d : {d // ¬P d}, O d.val → Finset α)
  (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)

noncomputable def activeAveragedSlicedIdealSiteFunction (δ : ℝ≥0) (x : Finset α → D → ℝ) : ℂ :=
  activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets δ center width
    (booleanSiteJets sets (fun s d => x s d.val))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedIdealSiteReconstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "grid" => allocatedGridAxis (I := I) U b S.value

noncomputable def allocatedNormalizedMixedSiteValue
    (w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ)) : LayerSamplerAxis I n → ℝ
  | ⟨j, .inl i⟩ => if grid ⟨j, .inl i⟩ then 0 else (w j).1 i / R j
  | ⟨j, .inr i⟩ => if grid ⟨j, .inr i⟩ then 0 else ((w j).2 i : ℝ) / (basisAxisScale (b j) i : ℝ) / R j

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedLongGridCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U basis S q}

omit [∀ j, Fintype (O j)] in
theorem allocatedLongIntegerSelect_range (q : output) :
    q ∈ Set.range (allocatedLongIntegerSelect B U basis S (O := O)) ↔
      allocatedLongIntegerCoordinate B U basis S q := by
  constructor
  · rintro ⟨z, hz⟩
    exact hz ▸ z.property
  · intro hq
    exact ⟨⟨q, hq⟩, rfl⟩

def allocatedLongRealIndex (j : Fin m) (i : I j)
    (ha : ¬grid ⟨j, .inl i⟩) (o : O j) :
    UnselectedColumn (allocatedLongIntegerSelect B U basis S (O := O)) :=
  ⟨⟨⟨⟨j, .inl i⟩, ha⟩, o⟩, by
    rw [allocatedLongIntegerSelect_range]
    exact fun h => h⟩

def allocatedLongIntegerIndex (j : Fin m) (i : Fin (n j))
    (ha : ¬grid ⟨j, .inr i⟩) (o : O j) : integerOutput :=
  ⟨⟨⟨⟨j, .inr i⟩, ha⟩, o⟩, True.intro⟩

noncomputable def allocatedLongCoordinateScale : output → ℝ
  | ⟨⟨⟨_, .inl _⟩, _⟩, _⟩ => 1
  | ⟨⟨⟨j, .inr i⟩, _⟩, _⟩ => (basisAxisScale (basis j) i : ℝ)

noncomputable def allocatedLongLatticeScale (q : integerOutput) : ℝ :=
  allocatedLongCoordinateScale B U basis S q.val

noncomputable def allocatedLongRowsFromGrid
    (v : UnselectedColumn (allocatedLongIntegerSelect B U basis S (O := O)) → ℝ)
    (k : integerOutput → ℤ) : AllocatedLongJetRows B U basis S O
  | ⟨⟨j, .inl i⟩, ha⟩ => fun o => v (allocatedLongRealIndex B U basis S j i ha o)
  | ⟨⟨j, .inr i⟩, ha⟩ => fun o => k (allocatedLongIntegerIndex B U basis S j i ha o)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedLongGridIntegral
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U basis S q}
local notation "select" => allocatedLongIntegerSelect B U basis S (O := O)
local notation "realOutput" => UnselectedColumn select
local notation "scalar" => fun q : output => CoefficientJetScalar (Subtype.val (Sigma.fst q))

noncomputable def allocatedLongScalarEquiv :
    AllocatedLongJetRows B U basis S O ≃ᵐ (∀ q : output, scalar q) :=
  (MeasurableEquiv.piCongrRight (fun a : {a // ¬grid a} =>
    coefficientJetScalarEquiv O a.val)).trans
    (MeasurableEquiv.piCurry (fun (a : {a // ¬grid a}) (_ : O a.val.1) =>
      CoefficientJetScalar a.val)).symm

noncomputable def allocatedLongRealScalarEquiv (q : realOutput) : ℝ ≃ᵐ scalar q.val := by
  rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
  · exact MeasurableEquiv.refl _
  · exact False.elim (hq ⟨allocatedLongIntegerIndex B U basis S j i ha o, rfl⟩)

noncomputable def allocatedLongIntegerScalarEquiv (q : integerOutput) : ℤ ≃ᵐ scalar (select q) := by
  rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
  · exact False.elim hq
  · exact MeasurableEquiv.refl _

noncomputable def allocatedLongGridEquiv :
    ((realOutput → ℝ) × (integerOutput → ℤ)) ≃ᵐ AllocatedLongJetRows B U basis S O :=
  ((MeasurableEquiv.piCongrRight (allocatedLongRealScalarEquiv B U basis S)).prodCongr
    (MeasurableEquiv.piCongrRight (allocatedLongIntegerScalarEquiv B U basis S))).trans
    ((selectedDependentEquiv select scalar).trans
      (allocatedLongScalarEquiv B U basis S).symm)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

variable [∀ j, DecidableEq (O j)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U basis S q}
local notation "realOutput" => UnselectedColumn (allocatedLongIntegerSelect B U basis S (O := O))

noncomputable def allocatedLongGridMask (v : realOutput → ℝ) (k : integerOutput → ℤ) : ℝ :=
  ∏ a, allocatedLongJetMask B U basis S x rows modulus residue a
    (allocatedLongRowsFromGrid B U basis S v k a)

noncomputable def allocatedLongGridDensityTest (f : (output → ℝ) → ℝ)
    (v : realOutput → ℝ) (qs : Finset (integerOutput → ℤ)) (φ : (integerOutput → ℤ) → ℂ) : ℂ :=
  (∑ k ∈ qs, ((allocatedLongGridMask B U basis S x rows modulus residue v k *
    f (allocatedLongJetRealCoordinates B U basis S (allocatedLongRowsFromGrid B U basis S v k)) : ℝ) : ℂ) * φ k) /
    ((∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U basis S (O := O) a : ℝ) : ℂ)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedSlicedIdealDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable [∀ a, DecidableEq (B a)]
variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable (R σ : Fin m → ℝ)

local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a // ¬P a}
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree P
local notation "Input" => (Σ a : {a : LayerSamplerAxis I n // ¬P a},
  B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)

noncomputable def allocatedFixedPathLiftMap
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (r : Coeff → ℝ) (x : Input → ℝ) : Output → ℝ :=
  (fun o => allocatedFixedPathShift B P R σ r o.1) +
    jointSlicedPrincipal (allocatedFixedPathPrincipal B P R σ r) lower width x

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRelativeChildSliceGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

noncomputable def allocatedOriginalSamplePrincipal (sample : Sample) (a : Active) (b : B a.val) : ℝ :=
  allocatedSampleNormalizedCoefficients B U basis S sample a.val
    (principalCoefficientSlot degree a.val b) / R a.val.1

noncomputable def allocatedOriginalSampleShift (sample : Sample) (a : Active) : ℝ :=
  allocatedSampleNormalizedCoefficients B U basis S sample a.val
    (constantCoefficientSlot vars (degree a.val)) / R a.val.1

variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

noncomputable def allocatedOriginalSampleLiftMap (sample : Sample) (x : Input → ℝ) : Output → ℝ :=
  (fun o => allocatedOriginalSampleShift B U basis S sample o.1) +
    jointSlicedPrincipal (allocatedOriginalSamplePrincipal B U basis S sample) lower width x

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

noncomputable def allocatedOriginalSampleSliceSubstitution : vars → MvPolynomial Input ℝ
  | .inl g => MvPolynomial.C ((x g none : ℝ) / S.value)
  | .inr ⟨a, b, i⟩ =>
      if ha : short a then
        MvPolynomial.C ((u ⟨⟨a, ha⟩, b, i⟩ none : ℝ) / sides ⟨a, b, i⟩)
      else MvPolynomial.C (lower ⟨a, ha⟩ (b, i)) +
        MvPolynomial.C (width ⟨a, ha⟩ (b, i)) * MvPolynomial.X ⟨⟨a, ha⟩, b, i⟩

noncomputable def allocatedOriginalSampleSliceInput (y : Input → ℝ) : vars → ℝ
  | .inl g => (x g none : ℝ) / S.value
  | .inr ⟨a, b, i⟩ =>
      if ha : short a then (u ⟨⟨a, ha⟩, b, i⟩ none : ℝ) / sides ⟨a, b, i⟩
      else lower ⟨a, ha⟩ (b, i) + width ⟨a, ha⟩ (b, i) * y ⟨⟨a, ha⟩, b, i⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleQuadratureUniformBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

noncomputable instance instFintypeAllocatedShortIntegerAxis : Fintype (AllocatedShortIntegerAxis U b L) :=
  inferInstanceAs (Fintype {a : Σ j : Fin m, Fin (n j) //
    basisAxisScale (b a.1) a.2 ≤ L ^ (a.1.val + 1)})

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleFullSliceLipschitz
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree short
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

noncomputable def allocatedOriginalSampleFullSliceMap (sample : Sample) (y : Input → ℝ) (o : Output) : ℝ :=
  MvPolynomial.eval (fun k => MvPolynomial.eval y
      (allocatedOriginalSampleSliceSubstitution B U basis S x u lower width k))
    (monomialArrayPolynomial Subtype.val (allocatedSampleNormalizedCoefficients B U basis S sample o.1.val)) /
      R o.1.val.1

noncomputable def allocatedOriginalSampleTailNoise (t : ℝ) (sample : Sample) : Coeff → ℝ :=
  activeTailRescale degree short (fun a => σ a.1 / t) (noise sample)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastIntegerAxisSplit
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem allocatedActiveIntegerGridScale_pos {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    (L : ℕ) (a : AllocatedActiveIntegerAxis U basis L) :
    0 < allocatedActiveIntegerGridScale U basis R L a :=
  mul_pos (hR a.val.1) (Nat.cast_pos.mpr (basisAxisScale_pos _ _))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

noncomputable def forecastIntegerAxisMerge
    (short : AllocatedShortIntegerAxis U basis L → ℤ)
    (active : AllocatedActiveIntegerAxis U basis L → ℤ)
    (a : Σ j : Fin m, Fin (n j)) : ℤ :=
  if h : basisAxisScale (basis a.1) a.2 ≤ L ^ (a.1.val + 1)
    then short ⟨a, h⟩ else active ⟨a, Nat.lt_of_not_ge h⟩

theorem forecastIntegerAxisMerge_short
    (short : AllocatedShortIntegerAxis U basis L → ℤ)
    (active : AllocatedActiveIntegerAxis U basis L → ℤ)
    (a : AllocatedShortIntegerAxis U basis L) :
    forecastIntegerAxisMerge U basis L short active a.val = short a := by
  rw [forecastIntegerAxisMerge, dif_pos a.property]
  rfl

theorem forecastIntegerAxisMerge_active
    (short : AllocatedShortIntegerAxis U basis L → ℤ)
    (active : AllocatedActiveIntegerAxis U basis L → ℤ)
    (a : AllocatedActiveIntegerAxis U basis L) :
    forecastIntegerAxisMerge U basis L short active a.val = active a := by
  rw [forecastIntegerAxisMerge, dif_neg (Nat.not_le.mpr a.property)]
  rfl

noncomputable def forecastIntegerAxisSplit :
    ((Σ j : Fin m, Fin (n j)) → ℤ) ≃ᵐ
      ((AllocatedShortIntegerAxis U basis L → ℤ) ×
        (AllocatedActiveIntegerAxis U basis L → ℤ)) where
  toFun z := (fun a => z a.val, fun a => z a.val)
  invFun z := forecastIntegerAxisMerge U basis L z.1 z.2
  left_inv z := by
    funext a
    dsimp only [forecastIntegerAxisMerge]
    split <;> rfl
  right_inv z := by
    apply Prod.ext
    · funext a
      exact forecastIntegerAxisMerge_short U basis L z.1 z.2 a
    · funext a
      exact forecastIntegerAxisMerge_active U basis L z.1 z.2 a
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedCappedContinuousSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

theorem slicedFixedUniformSiteLog_nonneg (m : ℕ) {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) :
    0 ≤ slicedFixedUniformSiteLog m p E := by
  unfold slicedFixedUniformSiteLog
  have hs : 0 ≤ ∑ j : Fin m, slicedGridSiteLog j.val 1 (j.val + 1) (j.val + 1) 1 p E :=
    Finset.sum_nonneg (fun j _ => (slicedGridSiteLog_bounds j.val 1 (j.val + 1) (j.val + 1)
      (by norm_num : (0 : ℝ) ≤ 1) hp hE).1)
  positivity

def slicedFixedUniformAccuracyLog (m : ℕ) (D p E : ℝ) : ℝ :=
  uniformProductAccuracyLog D (slicedFixedUniformSiteLog m p 0) E + 1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem slicedFixedUniformSiteLog_mono (m : ℕ) {p E p' E' : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hpp : p ≤ p') (hEE : E ≤ E') :
    slicedFixedUniformSiteLog m p E ≤ slicedFixedUniformSiteLog m p' E' := by
  unfold slicedFixedUniformSiteLog
  apply add_le_add (add_le_add (add_le_add hpp hEE) le_rfl)
  apply Finset.sum_le_sum
  intro j _
  exact slicedGridSiteLog_mono _ _ _ _ zero_le_one hp hE le_rfl hpp hEE

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastJointScaleNormalization
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {X : Type*} [Fintype X]

noncomputable def forecastJointGridScale (R : Fin m → ℝ) (L : ℕ)
    (physicalN : X → ℕ) (τ : ℝ) : X ⊕ AllocatedActiveIntegerAxis U basis L → ℝ :=
  Sum.elim (fun i => τ * physicalN i / 8) (allocatedActiveIntegerGridScale U basis R L)

def forecastJointGridCenter (L : ℕ) (base : X → ℤ) :
    X ⊕ AllocatedActiveIntegerAxis U basis L → ℤ :=
  Sum.elim base (fun _ => 0)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} [Fintype X]
variable {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

 theorem forecastGeometricJacobian_pos {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    (L : ℕ) {gridVolume τ : ℝ} (hgrid : 0 < gridVolume) (hτ : 0 < τ) :
    0 < forecastGeometricJacobian (X := X) (I := I) U basis R L gridVolume τ := by
  unfold forecastGeometricJacobian
  apply inv_pos.mpr
  exact mul_pos (mul_pos (mul_pos (mul_pos (coveredJetArrayScale_pos U) hgrid)
    (pow_pos (div_pos hτ (by norm_num)) _))
    (Finset.prod_pos (fun a _ => hR a.1)))
    (Finset.prod_pos (fun a _ => allocatedActiveIntegerGridScale_pos U basis hR L a))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CenteredCoefficientDeckChartMeasurable
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
attribute [local irreducible] coefficientDeckKernelEquiv canonicalCoefficientDeckSample coefficientSamplerAmbientPoint

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

omit [Fintype K] in
theorem coefficientDeckChartEvent_sample_iff (q : ℕ) [NeZero q]
    (event : CoefficientChartResidues K n E q → Prop)
    (x : CoefficientSamplerArrays (K := K) I n)
    (hx : ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2)
    (r : CoefficientDeckResidues (K := K) E q) :
    coefficientDeckChartEvent U bW b hb o q event
      (canonicalCoefficientDeckSample U bW b hb o q (NeZero.pos q) x r) ↔
      event (coefficientSamplerChartResidues q x r) := by
  constructor
  · rintro ⟨x', r', hx', he, hp⟩
    have h : (x', r') = (x, r) := canonicalCoefficientDeckSample_injOn_smallAmbient U bW b hb o q (NeZero.pos q)
      (x₁ := (x', r')) (x₂ := (x, r)) hx' hx (by exact he)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact hp
  · intro he
    exact ⟨x, r, hx, rfl, he⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpatialMatrixBlockWideProbability
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {G P : Type*} [Fintype G] [Fintype P] {n : ℕ}

theorem spatialMatrixBlock_cellMass_pos
    (q : Fin n → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × Fin n → ℝ) (hV : ∀ z, 0 < V z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (residue : Option (G ⊕ P) × Fin n → ℤ) :
    0 < shiftedSmoothProductMass (residueProfileCenter residue q) (residueProfileWidth q V) := by
  rw [shiftedSmoothProductMass_eq_prod _ _ (residueProfileWidth_pos q V hq hV)]
  exact Finset.prod_pos (fun z _ => shiftedSmoothSampleSum_pos _ (hscale z))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastRawSpatialBoxReorder
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} (I E : Fin m → Type*) [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (N : ℕ) [NeZero N]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

local notation "single" => (fun _ : Fin m => Unit)
local notation "RealAxis" => (Σ j, I j)
local notation "Deck" => ForecastSingleDeckResidues E N
local notation "short" => AllocatedShortIntegerAxis U basis L
local notation "active" => AllocatedActiveIntegerAxis U basis L

noncomputable def forecastRawGridEquiv : MixedCoveredJetSource I single E n N ≃ᵐ
    (((short → ℤ) × Deck) × ((RealAxis → ℝ) × (active → ℤ))) where
  toFun z := (((fun a => (z.1 a.val.1).2 a.val.2 ()), z.2),
    ((fun a => (z.1 a.1).1 a.2 ()), fun a => (z.1 a.val.1).2 a.val.2 ()))
  invFun p := forecastSingleMixedRawPoint I E n N p.2.1
    (forecastIntegerAxisMerge U basis L p.1.1 p.2.2) p.1.2
  left_inv z := by
    apply Prod.ext
    · funext j
      apply Prod.ext
      · funext i t
        cases t
        rfl
      · funext i t
        cases t
        simp only [forecastSingleMixedRawPoint, forecastIntegerAxisMerge]
        split <;> rfl
    · rfl
  right_inv p := by
    apply Prod.ext
    · apply Prod.ext
      · funext a
        exact forecastIntegerAxisMerge_short U basis L p.1.1 p.2.2 a
      · rfl
    · apply Prod.ext
      · rfl
      · funext a
        exact forecastIntegerAxisMerge_active U basis L p.1.1 p.2.2 a
  measurable_toFun := by
    change Measurable (fun z : MixedCoveredJetSource I single E n N =>
      (((fun a : short => (z.1 a.val.1).2 a.val.2 ()), z.2),
        ((fun a : RealAxis => (z.1 a.1).1 a.2 ()),
          fun a : active => (z.1 a.val.1).2 a.val.2 ())))
    fun_prop
  measurable_invFun := by
    unfold forecastSingleMixedRawPoint
    have hm := (forecastIntegerAxisSplit U basis L).symm.measurable
    change Measurable (fun p : ((short → ℤ) × Deck) × ((RealAxis → ℝ) × (active → ℤ)) => (fun j =>
      (fun i (_ : Unit) => p.2.1 ⟨j, i⟩,
        fun i (_ : Unit) => (forecastIntegerAxisSplit U basis L).symm (p.1.1, p.2.2) ⟨j, i⟩), p.1.2))
    fun_prop

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} (I E : Fin m → Type*) [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (N : ℕ) [NeZero N]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ) (X : Type*) [Fintype X]

local notation "single" => (fun _ : Fin m => Unit)
local notation "RealAxis" => (Σ j, I j)
local notation "Deck" => ForecastSingleDeckResidues E N
local notation "RawSource" => MixedCoveredJetSource I single E n N
local notation "short" => AllocatedShortIntegerAxis U basis L
local notation "active" => AllocatedActiveIntegerAxis U basis L
local notation "Target" => Deck × ((RealAxis → ℝ) × ((short → ℤ) × ((X ⊕ active) → ℤ)))

noncomputable def forecastRawSpatialEquiv : ((X → ℤ) × RawSource) ≃ᵐ Target where
  toFun p := (p.2.2, ((fun a => (p.2.1 a.1).1 a.2 ()),
    ((fun a => (p.2.1 a.val.1).2 a.val.2 ()),
      Sum.elim p.1 (fun a => (p.2.1 a.val.1).2 a.val.2 ()))))
  invFun p := ((fun x => p.2.2.2 (Sum.inl x)),
    forecastSingleMixedRawPoint I E n N p.2.1
      (forecastIntegerAxisMerge U basis L p.2.2.1 (fun a => p.2.2.2 (Sum.inr a))) p.1)
  left_inv p := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext j
        apply Prod.ext
        · funext i t
          cases t
          rfl
        · funext i t
          cases t
          simp only [forecastSingleMixedRawPoint, forecastIntegerAxisMerge]
          split <;> rfl
      · rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · funext a
          exact forecastIntegerAxisMerge_short U basis L p.2.2.1
            (fun a => p.2.2.2 (Sum.inr a)) a
        · funext a
          cases a with
          | inl x => rfl
          | inr a =>
            exact forecastIntegerAxisMerge_active U basis L p.2.2.1
              (fun a => p.2.2.2 (Sum.inr a)) a
  measurable_toFun := by
    change Measurable (fun p : (X → ℤ) × RawSource =>
      (p.2.2, ((fun a : RealAxis => (p.2.1 a.1).1 a.2 ()),
        ((fun a : short => (p.2.1 a.val.1).2 a.val.2 ()),
          Sum.elim p.1 (fun a : active => (p.2.1 a.val.1).2 a.val.2 ())))))
    apply Measurable.prodMk measurable_snd.snd
    apply Measurable.prodMk
    · fun_prop
    apply Measurable.prodMk
    · fun_prop
    apply measurable_pi_iff.mpr
    intro a
    cases a <;> fun_prop
  measurable_invFun := by
    have hm := (forecastIntegerAxisSplit U basis L).symm.measurable
    change Measurable (fun p : Target => ((fun x => p.2.2.2 (Sum.inl x)),
      (fun j => (fun i (_ : Unit) => p.2.1 ⟨j,i⟩,
        fun i (_ : Unit) => (forecastIntegerAxisSplit U basis L).symm
          (p.2.2.1, fun a => p.2.2.2 (Sum.inr a)) ⟨j,i⟩), p.1)))
    fun_prop

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedPolynomialPhysicalBadProductSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

noncomputable def preparedBadProductCoefficientExponent (m : ℕ) : ℕ :=
  (exists_preparedBadProductFinalBudget m).choose

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SelectedDensityTestMass
namespace OAI

section

namespace Erdos3

theorem selectedResidueDensityMass_bound_of_constant_test
    {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus T V x)
    (D : (K × I → ℤ) → ℝ) {ε : ℝ}
    (htest : ‖(∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
        ((1 : ℂ) * (D z : ℂ))) -
      ∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) * 1‖ ≤ ε) :
    |selectedResidueDensityMass modulus T V D - 1| ≤ ε := by
  rw [selectedResidueSmoothPMF_const] at htest
  simp only [one_mul] at htest
  rw [← selectedResidueDensityMass_complex modulus T V hV hZ D,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at htest
  exact htest

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedDensityTesting
namespace OAI

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

noncomputable def normalizedObservedDensity (w : Ω → ℝ) (scale : ℝ) (x : ∀ i, X i) : ℝ :=
  scale⁻¹ * observedProductDensity μ p F w x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductCellMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteCellMean_sum {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
    (p : FiniteProbabilityWeights X) (C : X → A) (f : X → ℝ) :
    (∑ a, finiteCellMean p C f a) = p.mean f := by
  unfold finiteCellMean
  rw [← p.mean_sum]
  congr 1
  funext x
  simp

noncomputable def finiteCellWeights {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
    (p : FiniteProbabilityWeights X) (C : X → A) : FiniteProbabilityWeights A where
  weight a := finiteCellMean p C (fun _ => 1) a
  nonneg a := p.mean_nonneg (fun x => by split_ifs <;> norm_num)
  total := by rw [finiteCellMean_sum, p.mean_const]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductEquivTransport
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

theorem productMean_coordinate_transport (p : ∀ i, FiniteProbabilityWeights (X i))
    (q : ∀ i, FiniteProbabilityWeights (Y i)) (F : ∀ i, X i → Y i)
    (hF : ∀ i (f : Y i → ℝ), (p i).mean (fun x => f (F i x)) = (q i).mean f)
    (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi p).mean (fun x => f (fun i => F i (x i))) =
      (FiniteProbabilityWeights.pi q).mean f := by
  classical
  have he (x : ∀ i, X i) : f (fun i => F i (x i)) =
      ∑ y : ∀ i, Y i, f y * ∏ i, if F i (x i) = y i then (1 : ℝ) else 0 := by
    simp_rw [← productCoordinate_indicator]
    simp
  have hi (i : ι) (y : Y i) : (p i).mean (fun z => if F i z = y then (1 : ℝ) else 0) =
      (q i).weight y := by
    rw [hF i (fun z => if z = y then (1 : ℝ) else 0)]
    simp [FiniteProbabilityWeights.mean]
  have hp (y : ∀ i, Y i) : (FiniteProbabilityWeights.pi p).mean
      (fun x => ∏ i, if F i (x i) = y i then (1 : ℝ) else 0) = ∏ i, (q i).weight (y i) := by
    rw [FiniteProbabilityWeights.mean_pi_product p (fun i z => if F i z = y i then (1 : ℝ) else 0)]
    exact Finset.prod_congr rfl (fun i _ => hi i (y i))
  simp_rw [he, FiniteProbabilityWeights.mean_sum, FiniteProbabilityWeights.mean_const_mul, hp]
  unfold FiniteProbabilityWeights.mean
  apply Finset.sum_congr rfl
  intro y _
  change f y * (∏ i, (q i).weight (y i)) = (∏ i, (q i).weight (y i)) * f y
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CylinderJointMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

noncomputable def productCouplingPairing (f : (∀ i, X i) → ℝ) (g : (∀ i, Y i) → ℝ) : ℝ :=
  (FiniteProbabilityWeights.pi (fun i => (c i).law)).mean
    (fun z => f (fun i => (z i).1) * g (fun i => (z i).2))

theorem productCoupling_right_mean (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi (fun i => (c i).law)).mean (fun z => f (fun i => (z i).2)) =
      (FiniteProbabilityWeights.pi ν).mean f :=
  productMean_coordinate_transport _ ν (fun _ => Prod.snd) (fun i => (c i).right_mean) f

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

noncomputable def productCouplingAtomMass (I : Finset ι) (x : ∀ i, X i) (y : ∀ i, Y i) : ℝ :=
  productFiberMass (FiniteProbabilityWeights.pi (fun i => (c i).law)).weight I (fun i => (x i, y i))

theorem productCouplingPairing_indicators (I : Finset ι) (x : ∀ i, X i) (y : ∀ i, Y i) :
    productCouplingPairing c (productFiberIndicator I x) (productFiberIndicator I y) =
      productCouplingAtomMass c I x y := by
  unfold productCouplingPairing productCouplingAtomMass productFiberMass FiniteProbabilityWeights.mean
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  have he : (∀ i ∈ I, z i = (x i, y i)) ↔
      ((∀ i ∈ I, (z i).1 = x i) ∧ (∀ i ∈ I, (z i).2 = y i)) := by
    simp only [Prod.ext_iff, forall_and]
  unfold productFiberIndicator
  dsimp only
  split_ifs <;> norm_num <;> aesop

theorem productCouplingAtomMass_nonneg (I : Finset ι) (x : ∀ i, X i) (y : ∀ i, Y i) :
    0 ≤ productCouplingAtomMass c I x y :=
  productFiberMass_nonneg _ (FiniteProbabilityWeights.pi (fun i => (c i).law)).nonneg I _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_sum_left {α : Type*} (s : Finset α)
    (f : α → (∀ i, X i) → ℝ) (g : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (fun x => ∑ a ∈ s, f a x) g =
      ∑ a ∈ s, productCouplingPairing c (f a) g := by
  simp only [productCouplingPairing, Finset.sum_mul, FiniteProbabilityWeights.mean_sum]

theorem productCouplingAtomMass_sum_left (I : Finset ι)
    (base : ∀ i, X i) (y : ∀ i, Y i) :
    (∑ a : ∀ i : I, X i, productCouplingAtomMass c I (productSubtypePoint I a base) y) =
      productFiberMass (FiniteProbabilityWeights.pi ν).weight I y := by
  simp_rw [← productCouplingPairing_indicators]
  rw [← productCouplingPairing_sum_left]
  simp_rw [productFiberIndicator_sum_subtype]
  simpa only [productCouplingPairing, one_mul, productFiberMass, FiniteProbabilityWeights.mean]
    using productCoupling_right_mean c (productFiberIndicator I y)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionedSmoothSlopeCap
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem selectedResidueSmoothWeight_one {K I : Type*} [Fintype K] [Fintype I]
    (W : K × I → ℝ) (z : K × I → ℤ) :
    selectedResidueSmoothWeight (fun _ => 1) {0} W z =
      rectangularWeight (smoothProductProfile (K × I)) 0 W z := by
  have hp : columnResiduePattern (fun _ : I => 1) z = 0 := Subsingleton.elim _ _
  simp only [selectedResidueSmoothWeight, hp, Finset.mem_singleton, ite_true,
    rectangularWeight, rectangularLatticePoint_zero_origin]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedCanonicalEarlyPrimitiveBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_commonRadiusPrimitive_bound (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      allocatedCommonProductRadiusLog m p p ∈ Set.Icc 0 ((p + C) ^ C) := by
  let Q : Polynomial ℕ := allocatedCommonProductRadiusLog m Polynomial.X Polynomial.X
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, fun p hp => ⟨(allocatedCommonProductRadius_bounds m hp hp).1, ?_⟩⟩
  simpa [Q, allocatedCommonProductRadiusLog, allocatedCommonRadiusLog,
    allocatedBufferedRadiusLog, allocatedBufferedRadiusInput, allocatedProductChartLog,
    allocatedIdealCoverPrimitiveLog, allocatedIdealCoverInputLog, allocatedSiteCoefficientLog,
    allocatedComparisonDimension, Polynomial.eval₂_pow] using hbound p hp

theorem exists_preparedCommonRadiusPrimitive_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ m : ℕ, m ≤ s → ∀ p : ℝ, 0 ≤ p →
      allocatedCommonProductRadiusLog m p p ∈ Set.Icc 0 ((p + C) ^ C) := by
  classical
  choose ex hex hb using fun j : Fin (s + 1) => exists_commonRadiusPrimitive_bound j.val
  let C := 2 + ∑ j, ex j
  refine ⟨C, by dsimp only [C]; omega, ?_⟩
  intro m hm p hp
  let j : Fin (s + 1) := ⟨m, by omega⟩
  have hsum : ex j ≤ ∑ i, ex i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have heC : ex j ≤ C := by dsimp only [C]; omega
  have hCReal : (2 : ℝ) ≤ C := Nat.cast_le.mpr ((hex j).trans heC)
  refine ⟨(hb j p hp).1, (hb j p hp).2.trans ?_⟩
  exact (pow_le_pow_left₀ (by positivity)
    (add_le_add le_rfl (Nat.cast_le.mpr heC)) _).trans
      (pow_le_pow_right₀ (by linarith only [hp, hCReal]) heC)

noncomputable def preparedCommonRadiusPrimitiveExponent (s : ℕ) : ℕ :=
  (exists_preparedCommonRadiusPrimitive_budget s).choose

theorem preparedCommonRadiusPrimitive_bound (s m : ℕ) (hm : m ≤ s)
    {p : ℝ} (hp : 0 ≤ p) :
    allocatedCommonProductRadiusLog m p p ∈
      Set.Icc 0 ((p + preparedCommonRadiusPrimitiveExponent s) ^
        preparedCommonRadiusPrimitiveExponent s) :=
  (exists_preparedCommonRadiusPrimitive_budget s).choose_spec.2 m hm p hp

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchSourceTestFinBounds
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def relativePatchSourceTest {X : Type*} [Fintype X] {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ) (A : PolynomialPatch X s d)
    (y : X → ℝ) : ℝ :=
  (relativeBoxInput N f (fun i => ⌊y i⌋) - a) * A.value y

@[simp] theorem relativePatchSourceTest_integer {X : Type*} [Fintype X] {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ) (A : PolynomialPatch X s d)
    (x : X → ℤ) :
    relativePatchSourceTest N f a A (fun i => (x i : ℝ)) =
      (relativeBoxInput N f x - a) * A.value (fun i => (x i : ℝ)) := by
  simp only [relativePatchSourceTest, Int.floor_intCast]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueScalarReindex
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {K I K' I' : Type*} [Fintype K] [Fintype I] [Fintype K'] [Fintype I']

theorem selectedResidueSmoothWeight_one_reindex
    (e : (K × I) ≃ (K' × I')) (W : K × I → ℝ) (W' : K' × I' → ℝ)
    (hW : ∀ i, W' (e i) = W i) (z : K × I → ℤ) :
    selectedResidueSmoothWeight (fun _ : I' => 1) {0} W' (z ∘ e.symm) =
      selectedResidueSmoothWeight (fun _ : I => 1) {0} W z := by
  simp only [selectedResidueSmoothWeight_one, rectangularWeight,
    rectangularLatticePoint_zero_origin, smoothProductProfile]
  symm
  apply Fintype.prod_equiv e
  intro i
  simp only [Function.comp_apply, e.symm_apply_apply, hW]

theorem selectedResidueSmoothMass_one_reindex
    (e : (K × I) ≃ (K' × I')) (W : K × I → ℝ) (W' : K' × I' → ℝ)
    (hW : ∀ i, W' (e i) = W i) :
    (∑' z, selectedResidueSmoothWeight (fun _ : I' => 1) {0} W' z) =
      ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} W z := by
  let E : (K × I → ℤ) ≃ (K' × I' → ℤ) := Equiv.arrowCongr e (Equiv.refl ℤ)
  calc
    _ = ∑' z, selectedResidueSmoothWeight (fun _ : I' => 1) {0} W' (E z) :=
      (E.tsum_eq _).symm
    _ = _ := tsum_congr (fun z => selectedResidueSmoothWeight_one_reindex e W W' hW z)

end Erdos3

end

end OAI
end


