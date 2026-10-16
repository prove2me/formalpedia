-- Prove2me | Definitions.Def_OAIErdos3B1346
-- name    : OAIErdos3B1346
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T00:42:33.094978+00:00
-- url     : https://prove2.me/theorems/d2036170-3f49-48bd-b3c4-40ce256cde65
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1347 of 1379
-- statement:
--   Definitions bundle 1347 of 1379 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1345`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1347 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.SharedWidthPreparedCenteredModelMarginalDataInterface`, `OAI.Erdos3.VectorPolynomial.SharedWidthPreparedCenteredModelMarginalProjectionInterface`, `OAI.Erdos3.VectorPolynomial.SharedWidthPreparedCenteredModelMarginalRadiusInterface`, `OAI.Erdos3.VectorPolynomial.exists_preparedConcreteSlicedForecastLocalModel_budget`, `OAI.Erdos3.VectorPolynomial.exists_preparedConcreteSlicedForecastPacketLog_budget`, `OAI.Erdos3.VectorPolynomial.exists_preparedConcreteSlicedForecastPrimitiveCapLog_budget`, `OAI.Erdos3.VectorPolynomial.exists_preparedRelativeEndpointForecast_budget`, `OAI.Erdos3.VectorPolynomial.exists_preparedRelativeEndpointInputScale_power_budget`, `OAI.Erdos3.VectorPolynomial.exists_preparedRelativeEndpointUniformKnob_power_budget`, `OAI.Erdos3.VectorPolynomial.exists_preparedSlicedForecastScalarEnvelope`, `OAI.Erdos3.VectorPolynomial.preparedConcreteSlicedForecastPrimitiveCapExponent`, `OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleAnchorGoodRequired`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointForecastExponent`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointGeometryScale`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointGeometryScale_bounds`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointInputBase`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointInputBase_bounds`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointInputScale`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointInputScale_bounds`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointPerturbationExponent`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointPrimitiveExponent`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointUniformKnob`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1347

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedWidthPreparedPerturbativeCertifiedSource
namespace OAI

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
local notation "pDetect" => allocatedModelTestLog u pModel
local notation "qDetect" => allocatedModelTestLog u pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
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
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

def SharedWidthPreparedCenteredModelMarginalDataInterface
    (Pchart Qstride Pmaster Plate _pGain Pphysical coarseTarget : ℝ) : Prop :=
    ∀ (_hstride : ∀ i, 0 < stride i) (_hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (_hC : ∀ j, 0 ≤ C j) (_hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (_hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (_hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (_hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (_hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (_hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (_hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart),
    ∀ {Pmarginal E : ℝ},
    0 ≤ Pmarginal → (m : ℝ) ≤ Pmarginal →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pmarginal →
    (Fintype.card (Fin nX) : ℝ) ≤ Pmarginal →
    (Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) : ℝ) ≤ Pmarginal →
    Pchart ≤ Pmarginal → Qstride ≤ Pmarginal → Pphysical ≤ Pmarginal →
    (∀ j, (R j)⁻¹ ≤ Real.exp Pmarginal) →
    (∀ j, (σ j)⁻¹ ≤ Real.exp Pmarginal) →
    (∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pmarginal) →
    (∀ j, (Fintype.card (I j) : ℝ) ≤ Pmarginal) →
    (∀ j, (n j : ℝ) ≤ Pmarginal) →
    (∀ j, (Fintype.card (J j) : ℝ) ≤ Pmarginal) →
    (S.value : ℝ) ≤ Real.exp Pmarginal →
    (∀ j, σ j ≤ 1) →
    (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) →
    ∀ (hτSpatial : 0 < τ), τ⁻¹ ≤ Real.exp Pphysical →
    τ ≤ 1 / 2 → (nX : ℝ) * τ ≤ 1 / 2 →
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s) (s + 1) Pmaster Plate
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    ∀ {ξn : ℝ} (hξn : 0 < ξn) (hξle : ξn ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect (α / 2))
      Pphysical coarseTarget), ξn⁻¹ ≤ Real.exp Plate →
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    W ≤ Real.exp Pmarginal →
    ∀ (hξone : ξn ≤ 1), ξn⁻¹ ≤ Real.exp Pmarginal →
    let required := max r.required ((max Pmarginal E + preparedCenteredMarginalExponent m) ^
      preparedCenteredMarginalExponent m)
    ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      {Rrank : ℝ},
    (∀ i, Real.exp required ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp required ≤ Rrank →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    cells.Nonempty →
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let Z := selectedJointDensityMass bases stride cells V
      (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem)
    ∃ (hN : ∀ i, 0 < N i) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
      (_hnormalizer : |Z - 1| ≤ Real.exp (-r.E) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2)
      (_hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i),
    let Path := bases × rectangularWeightIndices 0 V 1
    let Zcenter := fun center => selectedJointDensityMass bases stride cells V
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
    ∃ hnormalizerCenter : ∀ center,
      |Zcenter center - 1| ≤ Real.exp (-E) ∧
      Zcenter center ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
      0 < Zcenter center ∧ (Zcenter center)⁻¹ ≤ 2,
    let centeredLaw := fun center => selectedJointFiniteLaw bases hbases stride cells V
      (narrowTrimmedSpatialWidths_pos hW hτSpatial hξn N hN) hmass
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S poly hmem center) (hnormalizerCenter center).2.2.1
    ∃ hweight : ∀ z, Measurable (fun center => (centeredLaw center).weight z),
    let pathLaw := centeredFiniteMarginal μ centeredLaw hweight
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    let e : Sites → LayerSamplerVariables G I n B → ℤ := Subtype.val
    letI : Nonempty Sites := by
      have hpos (k : LayerSamplerVariables G I n B) : 0 < sides k := by
        cases k with
        | inl g => exact S.positive
        | inr j => exact allocatedPrincipalSides_pos B U basis S j
      let : ∀ k, NeZero (sides k) := fun k => ⟨(hpos k).ne'⟩
      exact (integerBox_nonempty sides).to_subtype
    let hrootSum := fun t : Sites => allocatedParameterBox_root_bound B U basis S t
    let physical := narrowPhysicalSiteMap (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτSpatial hξone N hN
      _hmargin e hrootSum
    (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
      (pathLaw.siteLaw physical) Ctail ≤ 6 * positiveProjectionAccuracy E ∧
    ∀ {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
      {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)] [∀ z j, LieAlgebra ℚ (Ldetect z j)]
      {dims : ∀ z, Tests z → ℕ}
      [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
      (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) s (dims z j))
      (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
      (slices : ∀ z, Tests z → Finset Sites)
      (cdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
      (stepdetect : ∀ z, Tests z → ℕ)
      (Hdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ),
    (∀ z j, 0 < stepdetect z j) →
    (∀ z j, (slices z j).image e = commonStrideBox (cdetect z j) (stepdetect z j) (Hdetect z j)) →
    (∀ z j, IsDenseCommonStrideBox
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)) pSlice ((slices z j).image e)) →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect →
    (∀ z j, (Vdetect z j).ComplexityLE (Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect)) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    let budget := r.nativeBudget
    ∀ (signal : (Fin nX → ℤ) → ℂ),
    0 < α →
    (∀ t, ‖signal t‖ ≤ 1) → (∀ t, t ∉ integerBox N → signal t = 0) →
    α ≤ sampledSliceSeminorm pathLaw
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((Vdetect z j).eval
        (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) signal →
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun t : integerBox N => t.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
            (fun t => signal t.val) (fun t => star (twistData.eval N poly t.val) * Fnative t)‖

def SharedWidthPreparedCenteredModelMarginalProjectionInterface
    (Pchart Qstride Pmaster Plate _pGain Pphysical coarseTarget : ℝ) : Prop :=
    ∀ (_hstride : ∀ i, 0 < stride i) (_hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (_hC : ∀ j, 0 ≤ C j) (_hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (_hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (_hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (_hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (_hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (_hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (_hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart),
    ∀ {E : ℝ},
    (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) →
    ∀ (hτSpatial : 0 < τ), τ⁻¹ ≤ Real.exp Pphysical →
    τ ≤ 1 / 2 → (nX : ℝ) * τ ≤ 1 / 2 →
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s) (s + 1) Pmaster Plate
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    ∀ {ξn : ℝ} (hξn : 0 < ξn) (hξle : ξn ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect (α / 2))
      Pphysical coarseTarget), ξn⁻¹ ≤ Real.exp Plate →
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    let hξone : ξn ≤ 1 := hξle.trans (min_le_left _ _)
    let Pmarginal := r.Pproj
    let required := max r.required ((max Pmarginal E + preparedCenteredMarginalExponent m) ^
      preparedCenteredMarginalExponent m)
    ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      {Rrank : ℝ},
    (∀ i, Real.exp required ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp required ≤ Rrank →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    cells.Nonempty →
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let Z := selectedJointDensityMass bases stride cells V
      (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem)
    ∃ (hN : ∀ i, 0 < N i) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
      (_hnormalizer : |Z - 1| ≤ Real.exp (-r.E) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2)
      (_hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i),
    let Path := bases × rectangularWeightIndices 0 V 1
    let Zcenter := fun center => selectedJointDensityMass bases stride cells V
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
    ∃ hnormalizerCenter : ∀ center,
      |Zcenter center - 1| ≤ Real.exp (-E) ∧
      Zcenter center ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
      0 < Zcenter center ∧ (Zcenter center)⁻¹ ≤ 2,
    let centeredLaw := fun center => selectedJointFiniteLaw bases hbases stride cells V
      (narrowTrimmedSpatialWidths_pos hW hτSpatial hξn N hN) hmass
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S poly hmem center) (hnormalizerCenter center).2.2.1
    ∃ hweight : ∀ z, Measurable (fun center => (centeredLaw center).weight z),
    let pathLaw := centeredFiniteMarginal μ centeredLaw hweight
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    let e : Sites → LayerSamplerVariables G I n B → ℤ := Subtype.val
    letI : Nonempty Sites := by
      have hpos (k : LayerSamplerVariables G I n B) : 0 < sides k := by
        cases k with
        | inl g => exact S.positive
        | inr j => exact allocatedPrincipalSides_pos B U basis S j
      let : ∀ k, NeZero (sides k) := fun k => ⟨(hpos k).ne'⟩
      exact (integerBox_nonempty sides).to_subtype
    let hrootSum := fun t : Sites => allocatedParameterBox_root_bound B U basis S t
    let physical := narrowPhysicalSiteMap (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτSpatial hξone N hN
      _hmargin e hrootSum
    (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
      (pathLaw.siteLaw physical) Ctail ≤ 6 * positiveProjectionAccuracy E ∧
    ∀ {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
      {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)] [∀ z j, LieAlgebra ℚ (Ldetect z j)]
      {dims : ∀ z, Tests z → ℕ}
      [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
      (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) s (dims z j))
      (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
      (slices : ∀ z, Tests z → Finset Sites)
      (cdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
      (stepdetect : ∀ z, Tests z → ℕ)
      (Hdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ),
    (∀ z j, 0 < stepdetect z j) →
    (∀ z j, (slices z j).image e = commonStrideBox (cdetect z j) (stepdetect z j) (Hdetect z j)) →
    (∀ z j, IsDenseCommonStrideBox
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)) pSlice ((slices z j).image e)) →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect →
    (∀ z j, (Vdetect z j).ComplexityLE (Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect)) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    let budget := r.nativeBudget
    ∀ (signal : (Fin nX → ℤ) → ℂ),
    0 < α →
    (∀ t, ‖signal t‖ ≤ 1) → (∀ t, t ∉ integerBox N → signal t = 0) →
    α ≤ sampledSliceSeminorm pathLaw
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((Vdetect z j).eval
        (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) signal →
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun t : integerBox N => t.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
            (fun t => signal t.val) (fun t => star (twistData.eval N poly t.val) * Fnative t)‖

def SharedWidthPreparedCenteredModelMarginalRadiusInterface
    (Pchart Qstride Pmaster Plate _pGain Pphysical coarseTarget : ℝ) : Prop :=
    ∀ (_hstride : ∀ i, 0 < stride i) (_hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (_hC : ∀ j, 0 ≤ C j) (_hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (_hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (_hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (_hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (_hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (_hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (_hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart),
    ∀ {E : ℝ},
    ∀ (hτSpatial : 0 < τ), τ⁻¹ ≤ Real.exp Pphysical →
    τ ≤ 1 / 2 → (nX : ℝ) * τ ≤ 1 / 2 →
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s) (s + 1) Pmaster Plate
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    ∀ {ξn : ℝ} (hξn : 0 < ξn) (hξle : ξn ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect (α / 2))
      Pphysical coarseTarget), ξn⁻¹ ≤ Real.exp Plate →
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    let hξone : ξn ≤ 1 := hξle.trans (min_le_left _ _)
    let Pmarginal := r.Pproj
    let required := max r.required ((max Pmarginal E + preparedCenteredMarginalExponent m) ^
      preparedCenteredMarginalExponent m)
    ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      {Rrank : ℝ},
    (∀ i, Real.exp required ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp required ≤ Rrank →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    cells.Nonempty →
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let Z := selectedJointDensityMass bases stride cells V
      (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem)
    ∃ (hN : ∀ i, 0 < N i) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
      (_hnormalizer : |Z - 1| ≤ Real.exp (-r.E) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2)
      (_hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i),
    let Path := bases × rectangularWeightIndices 0 V 1
    let Zcenter := fun center => selectedJointDensityMass bases stride cells V
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
    ∃ hnormalizerCenter : ∀ center,
      |Zcenter center - 1| ≤ Real.exp (-E) ∧
      Zcenter center ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
      0 < Zcenter center ∧ (Zcenter center)⁻¹ ≤ 2,
    let centeredLaw := fun center => selectedJointFiniteLaw bases hbases stride cells V
      (narrowTrimmedSpatialWidths_pos hW hτSpatial hξn N hN) hmass
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S poly hmem center) (hnormalizerCenter center).2.2.1
    ∃ hweight : ∀ z, Measurable (fun center => (centeredLaw center).weight z),
    let pathLaw := centeredFiniteMarginal μ centeredLaw hweight
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    let e : Sites → LayerSamplerVariables G I n B → ℤ := Subtype.val
    letI : Nonempty Sites := by
      have hpos (k : LayerSamplerVariables G I n B) : 0 < sides k := by
        cases k with
        | inl g => exact S.positive
        | inr j => exact allocatedPrincipalSides_pos B U basis S j
      let : ∀ k, NeZero (sides k) := fun k => ⟨(hpos k).ne'⟩
      exact (integerBox_nonempty sides).to_subtype
    let hrootSum := fun t : Sites => allocatedParameterBox_root_bound B U basis S t
    let physical := narrowPhysicalSiteMap (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτSpatial hξone N hN
      _hmargin e hrootSum
    (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
      (pathLaw.siteLaw physical) Ctail ≤ 6 * positiveProjectionAccuracy E ∧
    ∀ {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
      {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)] [∀ z j, LieAlgebra ℚ (Ldetect z j)]
      {dims : ∀ z, Tests z → ℕ}
      [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
      (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) s (dims z j))
      (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
      (slices : ∀ z, Tests z → Finset Sites)
      (cdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
      (stepdetect : ∀ z, Tests z → ℕ)
      (Hdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ),
    (∀ z j, 0 < stepdetect z j) →
    (∀ z j, (slices z j).image e = commonStrideBox (cdetect z j) (stepdetect z j) (Hdetect z j)) →
    (∀ z j, IsDenseCommonStrideBox
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)) pSlice ((slices z j).image e)) →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect →
    (∀ z j, (Vdetect z j).ComplexityLE (Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect)) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    let budget := r.nativeBudget
    ∀ (signal : (Fin nX → ℤ) → ℂ),
    0 < α →
    (∀ t, ‖signal t‖ ≤ 1) → (∀ t, t ∉ integerBox N → signal t = 0) →
    α ≤ sampledSliceSeminorm pathLaw
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((Vdetect z j).eval
        (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) signal →
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun t : integerBox N => t.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
            (fun t => signal t.val) (fun t => star (twistData.eval N poly t.val) * Fnative t)‖

end Consumer
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedAnchorRequiredPower
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedFiniteScheduleAnchorGoodRequired
    (m : ℕ) (Pmaster Plate E B0 Pgood Pprod : ℝ) : ℝ :=
  max
    (max
      (preparedModularGeneralDetectorResources
        (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate).required
      ((max
        (preparedModularGeneralDetectorResources
          (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate).Pproj E +
        preparedCenteredMarginalExponent m) ^ preparedCenteredMarginalExponent m))
    (max (preparedCenteredShortForecastGoodRequired m B0 Pgood)
      ((Pprod + preparedModularGeneralProductivityExponent m) ^
        preparedModularGeneralProductivityExponent m))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedRelativeEndpointForecastBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedConcreteSlicedForecastPacketLog_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (M nX Jalloc : ℕ)
      {r Pdim cost pRadius gainLog Qstride PF Pchart childLog E : ℝ},
      0 ≤ r →
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ r →
      ((nX + m * M : ℕ) : ℝ) ≤ r →
      Pdim ∈ Set.Icc 0 r → cost ∈ Set.Icc 0 r → pRadius ∈ Set.Icc 0 r →
      gainLog ∈ Set.Icc 0 r → Qstride ∈ Set.Icc 0 r → PF ∈ Set.Icc 0 r →
      Pchart ∈ Set.Icc 0 r → childLog ∈ Set.Icc 0 r → E ∈ Set.Icc 0 r →
      preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog E ∈ Set.Icc 0 ((r + C) ^ C) ∧
      preparedConcreteSlicedForecastNativeLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride PF Pchart childLog E ∈ Set.Icc 0 ((r + C) ^ C) ∧
      preparedConcreteSlicedForecastMassLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog E ∈ Set.Icc 0 ((r + C) ^ C) := by
  obtain ⟨Cs, _, hsp⟩ := exists_preparedCenteredForecastSpatialLog_budget
  let Ct : ℕ := ⌈preparedSlicedForecastPrimitiveCap⌉₊
  let Ccut : ℕ := ⌈(normalizedSiteCutoffBound : ℝ)⌉₊
  let X : Polynomial ℕ := Polynomial.X
  let S := 3 * X + 9 + (X + Polynomial.C Cs) ^ Cs
  let Dp := S + Polynomial.C (layerTailDegree m + 1) + 1
  let Tp := Polynomial.C Ct + X + 1
  let Vp := S + 2 * X + 1
  let Kp := (X + Polynomial.C m) * (4 * X + 11)
  let Sp := Polynomial.C (10 * m + 30) * (S + (X + 1) * (X + 1) + 1) ^ 2
  let Bp := 2 * X ^ 2 +
    Polynomial.C (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m)) + X + 11
  let Rp := 20 * X + 32 + Dp + Tp + Vp + Kp + 2 * Sp + Bp + Polynomial.C Ccut
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget
    ((forecastSlicedEarlyPolynomial m).comp Rp + X + 2)
  refine ⟨C, hC, ?_⟩
  intro M nX Jalloc r Pdim cost pRadius gainLog Qstride PF Pchart childLog E
    hr hDbase hDmod hPdim hcost hRadius hGain hStride hPF hChart hChild hE
  let spatial := 3 * r + 9 + (r + Cs) ^ Cs
  let dim := spatial + ((layerTailDegree m + 1 : ℕ) : ℝ) + 1
  let tail := (Ct : ℝ) + r + 1
  let radius := spatial + 2 * r + 1
  let jac := (r + m) * (4 * r + 11)
  let smooth := (10 * (m : ℝ) + 30) * (spatial + (r + 1) * (r + 1) + 1) ^ 2
  let bad := 2 * r ^ 2 +
    (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + r + 11
  let R := 20 * r + 32 + dim + tail + radius + jac + 2 * smooth + bad + Ccut
  have hs0 : 0 ≤ spatial := by dsimp only [spatial]; positivity
  have hd0 : 0 ≤ dim := by dsimp only [dim]; positivity
  have ht0 : 0 ≤ tail := by dsimp only [tail]; positivity
  have hv0 : 0 ≤ radius := by dsimp only [radius]; positivity
  have hk0 : 0 ≤ jac := by dsimp only [jac]; positivity
  have hsm0 : 0 ≤ smooth := by dsimp only [smooth]; positivity
  have hb0 : 0 ≤ bad := by dsimp only [bad]; positivity
  have hcc0 : (0 : ℝ) ≤ Ccut := Nat.cast_nonneg _
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hdR : dim ≤ R := by dsimp only [R]; linarith
  have htR : tail ≤ R := by dsimp only [R]; linarith
  have hvR : radius ≤ R := by dsimp only [R]; linarith
  have hksR : jac + smooth ≤ R := by dsimp only [R]; linarith
  have hsR : smooth ≤ R := by dsimp only [R]; linarith
  have hbR : bad ≤ R := by dsimp only [R]; linarith
  have hrR : r + 1 ≤ R := by dsimp only [R]; linarith
  have hspR : 2 * r + 16 ≤ R := by dsimp only [R]; linarith
  have hcoordR : 3 * r ≤ R := by dsimp only [R]; linarith
  have hcutR : 4 * r + Ccut + 1 ≤ R := by dsimp only [R]; linarith
  let Dbase := allocatedComparisonDimension m
    (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)
  let P := preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost
  let D := P + ((layerTailDegree m + 1 : ℕ) : ℝ) + 1
  let v := P + (Dbase + pRadius + 1)
  let K := preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart
  let Sm := forecastOriginalSmoothBudget m (P + (nX + 1) * (cost + 1))
  let Bad := preparedSlicedForecastBadLog m nX Qstride gainLog
  have hDbase0 : 0 ≤ Dbase := (allocatedComparisonDimension_bounds m (Nat.cast_nonneg _)).1
  have hnX : (nX : ℝ) ≤ r :=
    (Nat.cast_le.mpr (Nat.le_add_right nX (m * M))).trans hDmod
  have hcenter : preparedCenteredForecastSpatialLog Pdim ≤ (r + Cs) ^ Cs :=
    (hsp hPdim.1).trans (pow_le_pow_left₀ (add_nonneg hPdim.1 (Nat.cast_nonneg Cs))
      (add_le_add hPdim.2 le_rfl) Cs)
  have hP0 : 0 ≤ P := by
    apply le_trans _ (le_max_left _ _)
    dsimp only [Dbase] at hDbase0
    positivity
  have hP : P ≤ spatial := by
    unfold P preparedSlicedForecastSpatialBudget
    have hpow : 0 ≤ (r + Cs) ^ Cs := by positivity
    dsimp only [spatial]
    refine max_le ?_ (max_le ?_ ?_) <;> linarith only [hDbase, hnX, hcenter, hcost.2, hr, hpow]
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hD : D ≤ R := (by dsimp only [D, dim]; linarith only [hP] : D ≤ dim).trans hdR
  have hvInput0 : 0 ≤ v := by dsimp only [v]; linarith only [hP0, hDbase0, hRadius.1]
  have hvInput : v ≤ R := (by dsimp only [v, radius]; linarith only [hP, hDbase, hRadius.2] : v ≤ radius).trans hvR
  have htail0 : 0 ≤ preparedSlicedForecastTailLog cost := preparedSlicedForecastTailLog_nonneg hcost.1
  have htail : preparedSlicedForecastTailLog cost ≤ R := by
    apply le_trans _ htR
    have hceil : preparedSlicedForecastPrimitiveCap ≤ (Ct : ℝ) := Nat.le_ceil _
    dsimp only [preparedSlicedForecastTailLog, tail]
    linarith only [hceil, hcost.2]
  have hK0 : 0 ≤ K := by
    dsimp only [K, preparedSlicedForecastJacobianLog]
    have := hRadius.1
    have := hGain.1
    have := hChart.1
    positivity
  have hK : K ≤ jac := by
    have hleft : ((nX + m + m * M : ℕ) : ℝ) ≤ r + m := by
      have hdim : (nX : ℝ) + m * M ≤ r := by simpa only [Nat.cast_add, Nat.cast_mul] using hDmod
      simp only [Nat.cast_add, Nat.cast_mul]
      linarith only [hdim]
    have hright : pRadius + gainLog + nX + Pchart + 11 ≤ 4 * r + 11 := by
      linarith only [hRadius.2, hGain.2, hnX, hChart.2]
    exact mul_le_mul hleft hright
      (by have hn0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg _; linarith only [hRadius.1, hGain.1, hChart.1, hn0])
      (by positivity)
  have harg0 : 0 ≤ P + (nX + 1) * (cost + 1) :=
    add_nonneg hP0 (mul_nonneg (by positivity) (by linarith only [hcost.1]))
  have harg : P + (nX + 1) * (cost + 1) ≤ spatial + (r + 1) * (r + 1) :=
    add_le_add hP (mul_le_mul (add_le_add hnX le_rfl) (add_le_add hcost.2 le_rfl)
      (by linarith only [hcost.1]) (by linarith only [hr]))
  have hSm0 : 0 ≤ Sm := (forecastOriginalSmoothBudget_bounds m harg0).1
  have hSm : Sm ≤ smooth := by
    dsimp only [Sm, smooth, forecastOriginalSmoothBudget]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith only [harg0]) (add_le_add harg le_rfl) 2) (by positivity)
  have hBad0 : 0 ≤ Bad := by
    dsimp only [Bad, preparedSlicedForecastBadLog]
    have := hStride.1
    have := hGain.1
    positivity
  have hBad : Bad ≤ R := by
    apply le_trans _ hbR
    have hmul : 2 * (nX : ℝ) * Qstride ≤ 2 * r * r :=
      mul_le_mul (mul_le_mul_of_nonneg_left hnX (by norm_num)) hStride.2 hStride.1 (by positivity)
    dsimp only [Bad, preparedSlicedForecastBadLog, bad]
    nlinarith only [hmul, hGain.2]
  have hspatial : (gainLog + nX + 8) + 8 ∈ Set.Icc 0 R := by
    have hn0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg _
    exact ⟨by linarith only [hGain.1, hn0], (by linarith only [hGain.2, hnX] : (gainLog + nX + 8) + 8 ≤ 2 * r + 16).trans hspR⟩
  have hcoord : pRadius + PF + Dbase ∈ Set.Icc 0 R :=
    ⟨by linarith only [hRadius.1, hPF.1, hDbase0],
      (by linarith only [hRadius.2, hPF.2, hDbase] : pRadius + PF + Dbase ≤ 3 * r).trans hcoordR⟩
  have hcut : pRadius + PF + 2 * Dbase + normalizedSiteCutoffBound + 1 ∈ Set.Icc 0 R := by
    have hc0 : (0 : ℝ) ≤ normalizedSiteCutoffBound := normalizedSiteCutoffBound.2
    have hceil : (normalizedSiteCutoffBound : ℝ) ≤ Ccut := Nat.le_ceil _
    exact ⟨by linarith only [hRadius.1, hPF.1, hDbase0, hc0],
      (by linarith only [hRadius.2, hPF.2, hDbase, hceil] :
        pRadius + PF + 2 * Dbase + normalizedSiteCutoffBound + 1 ≤ 4 * r + Ccut + 1).trans hcutR⟩
  have hdiag := forecastSlicedEarlyLogs_le_diagonal_of_dimensions m (nX + m * M) (nX + m * M + 1) hR0
    ⟨hD0, hD⟩ ⟨htail0, htail⟩ ⟨hvInput0, hvInput⟩
    ⟨hcost.1, hcost.2.trans (by linarith only [hrR])⟩
    ⟨by linarith only [hChild.1], (add_le_add hChild.2 le_rfl).trans hrR⟩
    ⟨add_nonneg hK0 hSm0, (add_le_add hK hSm).trans hksR⟩
    ⟨hSm0, hSm.trans hsR⟩ ⟨hBad0, hBad⟩
    ⟨by linarith only [hcost.1], (add_le_add hcost.2 le_rfl).trans hrR⟩
    ⟨hE.1, hE.2.trans (by linarith only [hrR])⟩ hspatial hcoord hcut
    (hDmod.trans (by linarith only [hrR]))
    (by simpa only [Nat.cast_add, Nat.cast_one] using (add_le_add hDmod le_rfl).trans hrR)
  let N := preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childLog E
  let Mass := preparedConcreteSlicedForecastMassLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog E
  let Cap := preparedConcreteSlicedForecastCapLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog
  let V := preparedConcreteSlicedForecastPeriodLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childLog E
  have hresult : 0 ≤ N ∧ 0 ≤ Mass ∧ 0 ≤ Cap ∧
      N + Mass + Cap ≤ forecastSlicedEarlyDiagonalBudget m R := by
    simpa only [N, Mass, Cap, preparedConcreteSlicedForecastNativeLog,
      preparedConcreteSlicedForecastMassLog, preparedConcreteSlicedForecastCapLog,
      preparedConcreteSlicedForecastOutputLog, preparedConcreteSlicedForecastPeriodLog,
      preparedSlicedForecastCapLog, actualSlicedForecastModelCapLog,
      actualSlicedForecastModelPeriodLog, D, v, P, Dbase, K, Sm, Bad, add_assoc] using hdiag
  have hV : V = Cap + E + 2 := by
    dsimp only [V, Cap, preparedConcreteSlicedForecastPeriodLog,
      preparedConcreteSlicedForecastCapLog, preparedSlicedForecastCapLog,
      actualSlicedForecastModelPeriodLog, actualSlicedForecastModelCapLog]
    ring
  have hfinal : forecastSlicedEarlyDiagonalBudget m R + r + 2 ≤ (r + C) ^ C := by
    simpa [Rp, Dp, Tp, Vp, Kp, Sp, Bp, S, X, R, spatial, dim, tail, radius, jac, smooth, bad,
      Polynomial.eval₂_comp, Polynomial.eval₂_pow, forecastSlicedEarlyPolynomial_eval] using hpoly r hr
  change V ∈ Set.Icc 0 ((r + C) ^ C) ∧ N ∈ Set.Icc 0 ((r + C) ^ C) ∧ Mass ∈ Set.Icc 0 ((r + C) ^ C)
  exact ⟨⟨by linarith only [hV, hresult.2.2.1, hE.1],
      by linarith only [hV, hresult.1, hresult.2.1, hresult.2.2.2, hE.2, hfinal]⟩,
    ⟨hresult.1, by linarith only [hresult.2.1, hresult.2.2.1, hresult.2.2.2, hr, hfinal]⟩,
    ⟨hresult.2.1, by linarith only [hresult.1, hresult.2.2.1, hresult.2.2.2, hr, hfinal]⟩⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedConcreteSlicedForecastLocalModel_budget (m Cnative : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (M nX Jalloc : ℕ)
      {t Pdim cost pRadius gainLog Qstride PF Pchart childLog u p budget : ℝ},
      0 ≤ t →
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ t →
      ((nX + m * M : ℕ) : ℝ) ≤ t →
      Pdim ∈ Set.Icc 0 t → cost ∈ Set.Icc 0 t → pRadius ∈ Set.Icc 0 t →
      gainLog ∈ Set.Icc 0 t → Qstride ∈ Set.Icc 0 t → PF ∈ Set.Icc 0 t →
      Pchart ∈ Set.Icc 0 t → childLog ∈ Set.Icc 0 t →
      u ∈ Set.Icc 0 t → p ∈ Set.Icc 0 t →
      budget ∈ Set.Icc 0 ((t + Cnative) ^ Cnative) →
      let Edata := 2 * u + 4 * p + 12
      let period := preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog Edata
      let native := preparedConcreteSlicedForecastNativeLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride PF Pchart childLog Edata
      let mass := preparedConcreteSlicedForecastMassLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog Edata
      let commonBudget := max budget (3 * native + 3)
      let Qmodel := max commonBudget (2 * u + 4 * p + max 0 mass + 20)
      period ∈ Set.Icc 0 ((t + C) ^ C) ∧
      native ∈ Set.Icc 0 ((t + C) ^ C) ∧
      mass ∈ Set.Icc 0 ((t + C) ^ C) ∧
      commonBudget ∈ Set.Icc 0 ((t + C) ^ C) ∧
      Qmodel ∈ Set.Icc 0 ((t + C) ^ C) ∧
      Qmodel + 2 ∈ Set.Icc 0 ((t + C) ^ C) ∧
      2 * Qmodel + 2 * u + 4 * p + 34 ∈ Set.Icc 0 ((t + C) ^ C) ∧
      actualForecastDataModelRequired budget native mass u p ∈ Set.Icc 0 ((t + C) ^ C) := by
  obtain ⟨Cp, _, hpacket⟩ := exists_preparedConcreteSlicedForecastPacketLog_budget m
  let X : Polynomial ℕ := Polynomial.X
  let V : Polynomial ℕ := (X + Polynomial.C Cnative) ^ Cnative
  let Z : Polynomial ℕ := (6 * X + 12 + Polynomial.C Cp) ^ Cp
  let F : Polynomial ℕ := 2 * V + 8 * Z + 18 * X + 80
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget F
  refine ⟨C, hC, ?_⟩
  intro M nX Jalloc t Pdim cost pRadius gainLog Qstride PF Pchart childLog u p budget
    ht hDbase hDmod hPdim hcost hRadius hGain hStride hPF hChart hChild hu hp hbudget
    Edata period native mass commonBudget Qmodel
  let r : ℝ := 6 * t + 12
  let v : ℝ := (t + Cnative) ^ Cnative
  let z : ℝ := (r + Cp) ^ Cp
  have hr : 0 ≤ r := by dsimp only [r]; linarith only [ht]
  have htr : t ≤ r := by dsimp only [r]; linarith only [ht]
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hz : 0 ≤ z := by dsimp only [z]; positivity
  change budget ∈ Set.Icc 0 v at hbudget
  have hE0 : 0 ≤ Edata := by dsimp only [Edata]; linarith only [hu.1, hp.1]
  have hE : Edata ≤ r := by dsimp only [Edata, r]; linarith only [hu.2, hp.2]
  obtain ⟨hperiod, hnative, hmass⟩ := hpacket M nX Jalloc hr
    (hDbase.trans htr) (hDmod.trans htr)
    ⟨hPdim.1, hPdim.2.trans htr⟩ ⟨hcost.1, hcost.2.trans htr⟩
    ⟨hRadius.1, hRadius.2.trans htr⟩ ⟨hGain.1, hGain.2.trans htr⟩
    ⟨hStride.1, hStride.2.trans htr⟩ ⟨hPF.1, hPF.2.trans htr⟩
    ⟨hChart.1, hChart.2.trans htr⟩ ⟨hChild.1, hChild.2.trans htr⟩ ⟨hE0, hE⟩
  change period ∈ Set.Icc 0 z at hperiod
  change native ∈ Set.Icc 0 z at hnative
  change mass ∈ Set.Icc 0 z at hmass
  have hcommon0 : 0 ≤ commonBudget := hbudget.1.trans (le_max_left _ _)
  have hcommon : commonBudget ≤ v + 3 * z + 3 :=
    max_le (by linarith only [hbudget.2, hz]) (by linarith only [hnative.2, hv])
  have hQ0 : 0 ≤ Qmodel := hcommon0.trans (le_max_left _ _)
  have hQ : Qmodel ≤ v + 4 * z + 6 * t + 23 := by
    change max commonBudget (2 * u + 4 * p + max 0 mass + 20) ≤ _
    rw [max_eq_right hmass.1]
    exact max_le (by linarith only [hcommon, hz, ht])
      (by linarith only [hu.2, hp.2, hmass.2, hv, hz])
  have hrequired : actualForecastDataModelRequired budget native mass u p =
      u + 2 * p + Qmodel + 32 := rfl
  have hfinal : 2 * v + 8 * z + 18 * t + 80 ≤ (t + C) ^ C := by
    simpa [F, V, Z, X, v, z, r, Polynomial.eval₂_pow] using hpoly t ht
  have hraise : z ≤ (t + C) ^ C := by linarith only [hfinal, hv, hz, ht]
  refine ⟨⟨hperiod.1, hperiod.2.trans hraise⟩,
    ⟨hnative.1, hnative.2.trans hraise⟩, ⟨hmass.1, hmass.2.trans hraise⟩,
    ⟨hcommon0, ?_⟩, ⟨hQ0, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · linarith only [hcommon, hfinal, hv, hz, ht]
  · linarith only [hQ, hfinal, hv, hz, ht]
  · linarith only [hQ0]
  · linarith only [hQ, hfinal, hv, hz, ht]
  · linarith only [hQ0, hu.1, hp.1]
  · linarith only [hQ, hu.2, hp.2, hfinal]
  · linarith only [hrequired, hQ0, hu.1, hp.1]
  · linarith only [hrequired, hQ, hu.2, hp.2, hfinal, hv, hz, ht]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedRelativeEndpointForecast_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (M nX Jalloc : ℕ)
      {t Pdim cost pRadius gainLog Qstride PF Pchart childLog u p budget Pspatial : ℝ},
      0 ≤ t →
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ t →
      ((nX + m * M : ℕ) : ℝ) ≤ t →
      Pdim ∈ Set.Icc 0 t → cost ∈ Set.Icc 0 t → pRadius ∈ Set.Icc 0 t →
      gainLog ∈ Set.Icc 0 t → Qstride ∈ Set.Icc 0 t → PF ∈ Set.Icc 0 t →
      Pchart ∈ Set.Icc 0 t → childLog ∈ Set.Icc 0 t →
      u ∈ Set.Icc 0 t → p ∈ Set.Icc 0 t → budget ∈ Set.Icc 0 t →
      Pspatial ∈ Set.Icc 0 t →
      let Eearly := 2 * u + 4 * p + 12
      let nativeEarly := preparedConcreteSlicedForecastNativeLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride PF Pchart childLog Eearly
      let massEarly := preparedConcreteSlicedForecastMassLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog Eearly
      let Ptest := max budget (3 * nativeEarly + 3)
      let Ecompare := max Ptest (2 * u + 4 * p + max 0 massEarly + 20) + 2 + cost + cost + 8
      let nativeLate := preparedConcreteSlicedForecastNativeLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride PF Pchart childLog (Ecompare + 8)
      let massLate := preparedConcreteSlicedForecastMassLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog (Ecompare + 8)
      let ambient := (max (max Pspatial (2 * max Ptest (3 * nativeLate + 3) + 1))
        (massLate + Ecompare + 8) + nativeForecastAmbientExponent m) ^
          nativeForecastAmbientExponent m
      Ptest ∈ Set.Icc 0 ((t + C) ^ C) ∧
      Ecompare ∈ Set.Icc 0 ((t + C) ^ C) ∧
      nativeEarly ∈ Set.Icc 0 ((t + C) ^ C) ∧
      massEarly ∈ Set.Icc 0 ((t + C) ^ C) ∧
      nativeLate ∈ Set.Icc 0 ((t + C) ^ C) ∧
      massLate ∈ Set.Icc 0 ((t + C) ^ C) ∧
      actualForecastDataModelRequired budget nativeEarly massEarly u p ∈
        Set.Icc 0 ((t + C) ^ C) ∧ ambient ∈ Set.Icc 0 ((t + C) ^ C) := by
  obtain ⟨Cearly, _, hearly⟩ := exists_preparedConcreteSlicedForecastLocalModel_budget m 1
  obtain ⟨Clate, _, hlate⟩ := exists_preparedConcreteSlicedForecastPacketLog_budget m
  let Ca := nativeForecastAmbientExponent m
  let X : Polynomial ℕ := Polynomial.X
  let W : Polynomial ℕ := (X + Polynomial.C Cearly) ^ Cearly
  let R : Polynomial ℕ := W + 3 * X + 20
  let Z : Polynomial ℕ := (R + Polynomial.C Clate) ^ Clate
  let F : Polynomial ℕ := W + R + Z +
    (X + 3 * W + 7 * Z + R + 16 + Polynomial.C Ca) ^ Ca
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget F
  refine ⟨C, hC, ?_⟩
  intro M nX Jalloc t Pdim cost pRadius gainLog Qstride PF Pchart childLog u p budget Pspatial
    ht hD hdim hPdim hcost hRadius hGain hStride hPF hChart hChild hu hp hbudget hSpatial
    Eearly nativeEarly massEarly Ptest Ecompare nativeLate massLate ambient
  let w : ℝ := (t + Cearly) ^ Cearly
  let r : ℝ := w + 3 * t + 20
  let z : ℝ := (r + Clate) ^ Clate
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hz : 0 ≤ z := by dsimp only [z]; positivity
  have htr : t ≤ r := by dsimp only [r]; linarith only [hw, ht]
  have hb : budget ∈ Set.Icc 0 ((t + (1 : ℕ)) ^ (1 : ℕ)) := by
    simpa only [Nat.cast_one, pow_one] using
      (show budget ∈ Set.Icc 0 (t + 1) from ⟨hbudget.1, by linarith only [hbudget.2]⟩)
  obtain ⟨_, hnEarly, hmEarly, hTest, hQ, _, _, hRequired⟩ :=
    hearly M nX Jalloc ht hD hdim hPdim hcost hRadius hGain hStride hPF hChart
      hChild hu hp hb
  change nativeEarly ∈ Set.Icc 0 w at hnEarly
  change massEarly ∈ Set.Icc 0 w at hmEarly
  change Ptest ∈ Set.Icc 0 w at hTest
  change max Ptest (2 * u + 4 * p + max 0 massEarly + 20) ∈ Set.Icc 0 w at hQ
  change actualForecastDataModelRequired budget nativeEarly massEarly u p ∈ Set.Icc 0 w at hRequired
  have hE0 : 0 ≤ Ecompare := by
    dsimp only [Ecompare]
    linarith only [hQ.1, hcost.1]
  have hE : Ecompare + 8 ≤ r := by
    dsimp only [Ecompare, r]
    linarith only [hQ.2, hcost.2, ht]
  have lift {a : ℝ} (ha : a ∈ Set.Icc 0 t) : a ∈ Set.Icc 0 r :=
    ⟨ha.1, ha.2.trans htr⟩
  obtain ⟨_, hnLate, hmLate⟩ := hlate M nX Jalloc hr (hD.trans htr) (hdim.trans htr)
    (lift hPdim) (lift hcost) (lift hRadius) (lift hGain) (lift hStride) (lift hPF)
    (lift hChart) (lift hChild) (show Ecompare + 8 ∈ Set.Icc 0 r from
      ⟨by linarith only [hE0], hE⟩)
  change nativeLate ∈ Set.Icc 0 z at hnLate
  change massLate ∈ Set.Icc 0 z at hmLate
  let a : ℝ := t + 3 * w + 7 * z + r + 16 + Ca
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hmaxTest : max Ptest (3 * nativeLate + 3) ≤ w + 3 * z + 3 := by
    apply max_le
    · linarith only [hTest.2, hz]
    · linarith only [hnLate.2, hw]
  have hmax : max (max Pspatial (2 * max Ptest (3 * nativeLate + 3) + 1))
      (massLate + Ecompare + 8) + Ca ≤ a := by
    have hleft : max Pspatial (2 * max Ptest (3 * nativeLate + 3) + 1) ≤
        t + 3 * w + 7 * z + r + 16 := by
      apply max_le
      · linarith only [hSpatial.2, hw, hz, hr]
      · linarith only [hmaxTest, ht, hw, hz, hr]
    have hright : massLate + Ecompare + 8 ≤ t + 3 * w + 7 * z + r + 16 := by
      linarith only [hmLate.2, hE, ht, hw, hz]
    dsimp only [a]
    exact add_le_add (max_le hleft hright) (le_refl (Ca : ℝ))
  have hbase0 : 0 ≤ max (max Pspatial (2 * max Ptest (3 * nativeLate + 3) + 1))
      (massLate + Ecompare + 8) + Ca := by
    have h0 : 0 ≤ max (max Pspatial (2 * max Ptest (3 * nativeLate + 3) + 1))
        (massLate + Ecompare + 8) :=
      hSpatial.1.trans ((le_max_left _ _).trans (le_max_left _ _))
    exact add_nonneg h0 (Nat.cast_nonneg _)
  have hAmb0 : 0 ≤ ambient := pow_nonneg hbase0 _
  have hAmb : ambient ≤ a ^ Ca := pow_le_pow_left₀ hbase0 hmax _
  have hpower : 0 ≤ a ^ Ca := pow_nonneg ha _
  have hfinal : w + r + z + a ^ Ca ≤ (t + C) ^ C := by
    simpa [F, W, R, Z, X, w, r, z, a, Polynomial.eval₂_pow] using hbound t ht
  have hwFinal : w ≤ (t + C) ^ C := by linarith only [hfinal, hr, hz, hpower]
  have hrFinal : r ≤ (t + C) ^ C := by linarith only [hfinal, hw, hz, hpower]
  have hzFinal : z ≤ (t + C) ^ C := by linarith only [hfinal, hw, hr, hpower]
  refine ⟨⟨hTest.1, hTest.2.trans hwFinal⟩,
    ⟨hE0, (by linarith only [hE] : Ecompare ≤ r).trans hrFinal⟩,
    ⟨hnEarly.1, hnEarly.2.trans hwFinal⟩, ⟨hmEarly.1, hmEarly.2.trans hwFinal⟩,
    ⟨hnLate.1, hnLate.2.trans hzFinal⟩, ⟨hmLate.1, hmLate.2.trans hzFinal⟩,
    ⟨hRequired.1, hRequired.2.trans hwFinal⟩, hAmb0, ?_⟩
  linarith only [hAmb, hfinal, hw, hr, hz]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedSlicedForecastScalarEnvelope
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_preparedSlicedForecastScalarEnvelope (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (M nX Jalloc : ℕ)
      {t Pdim cost pRadius gainLog Qstride Pchart PF childCost : ℝ},
      0 ≤ t →
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ t →
      ((nX + m * M : ℕ) : ℝ) ≤ t →
      Pdim ∈ Set.Icc 0 t → cost ∈ Set.Icc 0 t → pRadius ∈ Set.Icc 0 t →
      gainLog ∈ Set.Icc 0 t → Qstride ∈ Set.Icc 0 t → Pchart ∈ Set.Icc 0 t →
      PF ∈ Set.Icc 0 t → childCost ∈ Set.Icc 0 t →
      let cap := (t + C) ^ C
      preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ∈ Set.Icc 0 cap ∧
      preparedSlicedForecastBadLog m nX Qstride gainLog ∈ Set.Icc 0 cap ∧
      cost + 1 ∈ Set.Icc 0 cap ∧
      gainLog + nX + 8 ∈ Set.Icc 0 cap ∧
      pRadius ∈ Set.Icc 0 cap ∧
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ∈ Set.Icc 0 cap ∧
      preparedSlicedForecastPrimitiveCap ∈ Set.Icc 0 cap ∧
      (m : ℝ) ≤ cap ∧ ((nX + m * M : ℕ) : ℝ) ≤ cap ∧ (nX : ℝ) ≤ cap ∧
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 ∈ Set.Icc 0 cap ∧
      preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart ∈ Set.Icc 0 cap ∧
      PF ∈ Set.Icc 0 cap ∧ childCost + 1 ∈ Set.Icc 0 cap := by
  obtain ⟨Cs, _, hsp⟩ := exists_preparedCenteredForecastSpatialLog_budget
  let Cprim : ℕ := ⌈preparedSlicedForecastPrimitiveCap⌉₊
  let X : Polynomial ℕ := Polynomial.X
  let Sp := 3 * X + 9 + (X + Polynomial.C Cs) ^ Cs
  let Bad := 2 * X ^ 2 +
    Polynomial.C (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m)) + X + 11
  let Jac := (X + Polynomial.C m) * (4 * X + 11)
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget
    (Sp + Bad + Jac + 4 * X + 20 + Polynomial.C Cprim + Polynomial.C m)
  refine ⟨C, hC, ?_⟩
  intro M nX Jalloc t Pdim cost pRadius gainLog Qstride Pchart PF childCost
    ht hDbase hDmod hPdim hcost hRadius hGain hStride hChart hPF hChild cap
  let spatial := 3 * t + 9 + (t + Cs) ^ Cs
  let bad := 2 * t ^ 2 +
    (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + t + 11
  let jac := (t + m) * (4 * t + 11)
  let total := spatial + bad + jac + 4 * t + 20 + Cprim + m
  have hs0 : 0 ≤ spatial := by dsimp [spatial]; positivity
  have hb0 : 0 ≤ bad := by dsimp [bad]; positivity
  have hj0 : 0 ≤ jac := by dsimp [jac]; positivity
  have hprim0 : (0 : ℝ) ≤ Cprim := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have htotal : total ≤ cap := by
    simpa [Sp, Bad, Jac, X, total, spatial, bad, jac, cap, Polynomial.eval₂_pow] using hpoly t ht
  have hsCap : spatial ≤ cap := (by dsimp [total]; linarith : spatial ≤ total).trans htotal
  have hbCap : bad ≤ cap := (by dsimp [total]; linarith : bad ≤ total).trans htotal
  have hjCap : jac ≤ cap := (by dsimp [total]; linarith : jac ≤ total).trans htotal
  have hlinear : 4 * t + 20 ≤ cap := (by dsimp [total]; linarith : 4 * t + 20 ≤ total).trans htotal
  have hprimCap : (Cprim : ℝ) ≤ cap := (by dsimp [total]; linarith : (Cprim : ℝ) ≤ total).trans htotal
  have hmCap : (m : ℝ) ≤ cap := (by dsimp [total]; linarith : (m : ℝ) ≤ total).trans htotal
  have htCap : t ≤ cap := by linarith
  have hDbase0 := (allocatedComparisonDimension_bounds m
    (Nat.cast_nonneg (enlargedPreparedCommonSamplerDimension m M Jalloc))).1
  have hnX : (nX : ℝ) ≤ t :=
    (Nat.cast_le.mpr (Nat.le_add_right nX (m * M))).trans hDmod
  have hnX0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg _
  have hcenter : preparedCenteredForecastSpatialLog Pdim ≤ (t + Cs) ^ Cs :=
    (hsp hPdim.1).trans (pow_le_pow_left₀ (add_nonneg hPdim.1 (Nat.cast_nonneg Cs))
      (add_le_add hPdim.2 le_rfl) Cs)
  have hP0 : 0 ≤ preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost := by
    apply le_trans _ (le_max_left _ _)
    positivity
  have hP : preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ≤ spatial := by
    unfold preparedSlicedForecastSpatialBudget
    have hpow : 0 ≤ (t + Cs) ^ Cs := by positivity
    dsimp only [spatial]
    refine max_le ?_ (max_le ?_ ?_) <;> linarith only [hDbase, hnX, hcenter, hcost.2, ht, hpow]
  have hBad0 : 0 ≤ preparedSlicedForecastBadLog m nX Qstride gainLog := by
    unfold preparedSlicedForecastBadLog
    have := hStride.1
    have := hGain.1
    positivity
  have hBad : preparedSlicedForecastBadLog m nX Qstride gainLog ≤ bad := by
    have hmul : 2 * (nX : ℝ) * Qstride ≤ 2 * t * t :=
      mul_le_mul (mul_le_mul_of_nonneg_left hnX (by norm_num)) hStride.2 hStride.1 (by positivity)
    dsimp only [preparedSlicedForecastBadLog, bad]
    nlinarith only [hmul, hGain.2]
  have hJac0 : 0 ≤ preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart := by
    unfold preparedSlicedForecastJacobianLog
    have := hRadius.1
    have := hGain.1
    have := hChart.1
    positivity
  have hJac : preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart ≤ jac := by
    have hleft : ((nX + m + m * M : ℕ) : ℝ) ≤ t + m := by
      have hdim : (nX : ℝ) + m * M ≤ t := by simpa only [Nat.cast_add, Nat.cast_mul] using hDmod
      simp only [Nat.cast_add, Nat.cast_mul]
      linarith only [hdim]
    have hright : pRadius + gainLog + nX + Pchart + 11 ≤ 4 * t + 11 := by
      linarith only [hRadius.2, hGain.2, hnX, hChart.2]
    exact mul_le_mul hleft hright
      (by linarith only [hRadius.1, hGain.1, hChart.1, hnX0]) (by positivity)
  exact ⟨⟨hP0, hP.trans hsCap⟩, ⟨hBad0, hBad.trans hbCap⟩,
    ⟨by linarith [hcost.1], by linarith [hcost.2]⟩,
    ⟨by linarith [hGain.1], by linarith [hGain.2]⟩,
    ⟨hRadius.1, hRadius.2.trans htCap⟩, ⟨hDbase0, hDbase.trans htCap⟩,
    ⟨zero_le_one.trans preparedSlicedForecastPrimitiveCap_one_le,
      (Nat.le_ceil _).trans hprimCap⟩,
    hmCap, hDmod.trans htCap, hnX.trans htCap,
    ⟨by linarith [hRadius.1], by linarith [hRadius.2]⟩,
    ⟨hJac0, hJac.trans hjCap⟩, ⟨hPF.1, hPF.2.trans htCap⟩,
    ⟨by linarith [hChild.1], by linarith [hChild.2]⟩⟩

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeEndpointNumericalBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedRelativeEndpointForecastExponent (m : ℕ) : ℕ :=
  (exists_preparedRelativeEndpointForecast_budget m).choose

noncomputable def preparedRelativeEndpointPerturbationExponent (m : ℕ) : ℕ :=
  (exists_preparedRelativeEndpointPerturbationLog_budget m).choose

noncomputable def preparedRelativeEndpointGeometryScale (m : ℕ) (t : ℝ) : ℝ :=
  t + (t + preparedRelativeEndpointForecastExponent m) ^
    preparedRelativeEndpointForecastExponent m + 1

noncomputable def preparedRelativeEndpointUniformKnob (m : ℕ) (t : ℝ) : ℝ :=
  let T := preparedRelativeEndpointGeometryScale m t
  4 * T + (T + preparedRelativeEndpointPerturbationExponent m) ^
    preparedRelativeEndpointPerturbationExponent m + (T + 10) ^ (2 * m + 20) + 20

theorem preparedRelativeEndpointGeometryScale_bounds (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ preparedRelativeEndpointGeometryScale m t ∧
    t ≤ preparedRelativeEndpointGeometryScale m t ∧
    (t + preparedRelativeEndpointForecastExponent m) ^
      preparedRelativeEndpointForecastExponent m ≤ preparedRelativeEndpointGeometryScale m t := by
  have hw : 0 ≤ (t + preparedRelativeEndpointForecastExponent m) ^
      preparedRelativeEndpointForecastExponent m := by positivity
  unfold preparedRelativeEndpointGeometryScale
  exact ⟨by linarith only [ht, hw], by linarith only [hw], by linarith only [ht]⟩

theorem exists_preparedRelativeEndpointUniformKnob_power_budget (m inputPower : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x t : ℝ}, 0 ≤ x → t ∈ Set.Icc 0 ((x + 2) ^ inputPower) →
      preparedRelativeEndpointUniformKnob m t ≤ (x + 2) ^ C := by
  let Cf := preparedRelativeEndpointForecastExponent m
  let Cs := preparedRelativeEndpointPerturbationExponent m
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + 2) ^ inputPower
  let T : Polynomial ℕ := P + (P + Polynomial.C Cf) ^ Cf + 1
  let K : Polynomial ℕ := 4 * T + (T + Polynomial.C Cs) ^ Cs +
    (T + 10) ^ (2 * m + 20) + 20
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget K
  refine ⟨C, hC, ?_⟩
  intro x t hx ht
  let p := (x + 2) ^ inputPower
  let b := p + (p + Cf) ^ Cf + 1
  have hp0 : 0 ≤ p := by dsimp only [p]; positivity
  have hT0 := zero_le_one.trans (preparedRelativeEndpointGeometryScale_bounds m ht.1).1
  have hT : preparedRelativeEndpointGeometryScale m t ≤ b := by
    unfold preparedRelativeEndpointGeometryScale
    exact add_le_add (add_le_add ht.2
      (pow_le_pow_left₀ (add_nonneg ht.1 (Nat.cast_nonneg _))
        (add_le_add ht.2 le_rfl) _)) le_rfl
  have hB : preparedRelativeEndpointUniformKnob m t ≤
      4 * b + (b + Cs) ^ Cs + (b + 10) ^ (2 * m + 20) + 20 := by
    unfold preparedRelativeEndpointUniformKnob
    exact add_le_add (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hT (by norm_num))
        (pow_le_pow_left₀ (add_nonneg hT0 (Nat.cast_nonneg _))
          (add_le_add hT le_rfl) _))
      (pow_le_pow_left₀ (by linarith only [hT0]) (add_le_add hT le_rfl) _)) le_rfl
  apply hB.trans
  simpa [K, T, P, X, p, b, Polynomial.eval₂_pow] using hbound x hx

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedRelativeEndpointPrimitiveExponent (m : ℕ) : ℕ :=
  (exists_preparedSlicedForecastScalarEnvelope m).choose

noncomputable def preparedRelativeEndpointInputBase (earlyPower : ℕ) (B : ℝ) : ℝ :=
  (B + 2) ^ earlyPower + B + 1

noncomputable def preparedRelativeEndpointInputScale (m earlyPower : ℕ) (B : ℝ) : ℝ :=
  let a := preparedRelativeEndpointInputBase earlyPower B
  a + (a + preparedRelativeEndpointPrimitiveExponent m) ^
    preparedRelativeEndpointPrimitiveExponent m + 1

theorem preparedRelativeEndpointInputBase_bounds (earlyPower : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    1 ≤ preparedRelativeEndpointInputBase earlyPower B ∧
    B ≤ preparedRelativeEndpointInputBase earlyPower B ∧
    (B + 2) ^ earlyPower + 1 ≤ preparedRelativeEndpointInputBase earlyPower B := by
  have hp : 0 ≤ (B + 2) ^ earlyPower := by positivity
  unfold preparedRelativeEndpointInputBase
  exact ⟨by linarith only [hp, hB], by linarith only [hp], by linarith only [hB]⟩

theorem preparedRelativeEndpointInputScale_bounds (m earlyPower : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    1 ≤ preparedRelativeEndpointInputScale m earlyPower B ∧
    preparedRelativeEndpointInputBase earlyPower B ≤ preparedRelativeEndpointInputScale m earlyPower B ∧
    (preparedRelativeEndpointInputBase earlyPower B + preparedRelativeEndpointPrimitiveExponent m) ^
      preparedRelativeEndpointPrimitiveExponent m ≤ preparedRelativeEndpointInputScale m earlyPower B := by
  have ha := preparedRelativeEndpointInputBase_bounds earlyPower hB
  have ha0 : 0 ≤ preparedRelativeEndpointInputBase earlyPower B := zero_le_one.trans ha.1
  have hw : 0 ≤ (preparedRelativeEndpointInputBase earlyPower B + preparedRelativeEndpointPrimitiveExponent m) ^
      preparedRelativeEndpointPrimitiveExponent m := by positivity
  unfold preparedRelativeEndpointInputScale
  exact ⟨by linarith only [ha.1, hw], by linarith only [hw], by linarith only [ha.1]⟩

theorem exists_preparedRelativeEndpointInputScale_power_budget (m earlyPower : ℕ) :
    ∃ inputPower : ℕ, 2 ≤ inputPower ∧ ∀ {B : ℝ}, 0 ≤ B →
      preparedRelativeEndpointUniformKnob m (preparedRelativeEndpointInputScale m earlyPower B) ≤
        (B + 2) ^ inputPower := by
  let Cp := preparedRelativeEndpointPrimitiveExponent m
  let X : Polynomial ℕ := Polynomial.X
  let a : Polynomial ℕ := (X + 2) ^ earlyPower + X + 1
  let t : Polynomial ℕ := a + (a + Polynomial.C Cp) ^ Cp + 1
  obtain ⟨Cscale, _, hscale⟩ := exists_natPolynomial_fixed_power_budget t
  obtain ⟨C, hC, hknob⟩ := exists_preparedRelativeEndpointUniformKnob_power_budget m Cscale
  refine ⟨C, hC, ?_⟩
  intro B hB
  apply hknob hB
  constructor
  · exact zero_le_one.trans (preparedRelativeEndpointInputScale_bounds m earlyPower hB).1
  · simpa [t, a, X, preparedRelativeEndpointInputScale, preparedRelativeEndpointInputBase,
      Cp, Polynomial.eval₂_pow] using hscale B hB

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedConcreteSlicedForecastPrimitiveCapBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedConcreteSlicedForecastPrimitiveCapLog_budget
    (m Ccontrol Cchild Cprimitive : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (M nX Jalloc : ℕ)
      {b Pdim pRadius gainLog Qstride Pchart childLog : ℝ},
      0 ≤ b →
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ b →
      ((nX + m * M : ℕ) : ℝ) ≤ b →
      Pdim ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      pRadius ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      gainLog ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      Qstride ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      Pchart ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      childLog ∈ Set.Icc 0 ((b + Cchild) ^ Cchild) →
      preparedConcreteSlicedForecastCapLog m M nX Jalloc
        Pdim ((b + Ccontrol) ^ Ccontrol) pRadius gainLog Qstride Pchart childLog ∈
          Set.Icc 0 ((b + C) ^ C) := by
  obtain ⟨Csp, _, hsp⟩ := exists_preparedCenteredForecastSpatialLog_budget
  obtain ⟨Cg, _, hgeneric⟩ := exists_actualSlicedForecastModelCapLog_budget m
  let Cprim : ℕ := ⌈preparedSlicedForecastPrimitiveCap⌉₊
  let X : Polynomial ℕ := Polynomial.X
  let Pr : Polynomial ℕ := (X + Polynomial.C Cprimitive) ^ Cprimitive
  let W : Polynomial ℕ := (X + Polynomial.C Ccontrol) ^ Ccontrol
  let H : Polynomial ℕ := (X + Polynomial.C Cchild) ^ Cchild
  let S : Polynomial ℕ := 2 * X + 8 + (Pr + Polynomial.C Csp) ^ Csp + W + 1
  let Bad : Polynomial ℕ := 2 * X * Pr +
    Polynomial.C (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m)) + Pr + 11
  let Jac : Polynomial ℕ := (X + Polynomial.C m) * (3 * Pr + X + 11)
  let Tail : Polynomial ℕ := Polynomial.C Cprim + W + 1
  let R : Polynomial ℕ := X + S + (X + Pr + 1) + Bad + Jac + (W + 1) + Tail + W + (H + 1)
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C Cg) ^ Cg)
  refine ⟨C, hC, ?_⟩
  intro M nX Jalloc b Pdim pRadius gainLog Qstride Pchart childLog
    hb hDbase hDmod hPdim hRadius hGain hStride hChart hChild
  let primitive : ℝ := (b + Cprimitive) ^ Cprimitive
  let cost : ℝ := (b + Ccontrol) ^ Ccontrol
  let child : ℝ := (b + Cchild) ^ Cchild
  let spatial : ℝ := 2 * b + 8 + (primitive + Csp) ^ Csp + cost + 1
  let bad : ℝ := 2 * b * primitive +
    (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + primitive + 11
  let jac : ℝ := (b + m) * (3 * primitive + b + 11)
  let tail : ℝ := Cprim + cost + 1
  let r : ℝ := b + spatial + (b + primitive + 1) + bad + jac + (cost + 1) + tail + cost + (child + 1)
  have hprimitive0 : 0 ≤ primitive := by dsimp only [primitive]; positivity
  have hcost0 : 0 ≤ cost := by dsimp only [cost]; positivity
  have hchild0 : 0 ≤ child := by dsimp only [child]; positivity
  have hspatial0 : 0 ≤ spatial := by dsimp only [spatial]; positivity
  have hbad0 : 0 ≤ bad := by dsimp only [bad]; positivity
  have hjac0 : 0 ≤ jac := by dsimp only [jac]; positivity
  have htail0 : 0 ≤ tail := by dsimp only [tail]; positivity
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hbr : b ≤ r := by dsimp only [r]; linarith
  have hspatialr : spatial ≤ r := by dsimp only [r]; linarith
  have hscaler : b + primitive + 1 ≤ r := by dsimp only [r]; linarith
  have hbadr : bad ≤ r := by dsimp only [r]; linarith
  have hjacr : jac ≤ r := by dsimp only [r]; linarith
  have hcostr : cost + 1 ≤ r := by dsimp only [r]; linarith
  have htailr : tail ≤ r := by dsimp only [r]; linarith
  have hchildr : child + 1 ≤ r := by dsimp only [r]; linarith
  have hDbase0 := (allocatedComparisonDimension_bounds m
    (Nat.cast_nonneg (enlargedPreparedCommonSamplerDimension m M Jalloc))).1
  have hnX : (nX : ℝ) ≤ b := by
    have hnonneg : (0 : ℝ) ≤ m * M := by positivity
    have hdim : (nX : ℝ) + m * M ≤ b := by
      simpa only [Nat.cast_add, Nat.cast_mul] using hDmod
    linarith only [hdim, hnonneg]
  have hcenter : preparedCenteredForecastSpatialLog Pdim ≤ (primitive + Csp) ^ Csp :=
    (hsp hPdim.1).trans (pow_le_pow_left₀ (add_nonneg hPdim.1 (Nat.cast_nonneg Csp))
      (add_le_add hPdim.2 (le_refl (Csp : ℝ))) Csp)
  have hP0 : 0 ≤ preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost := by
    apply le_trans _ (le_max_left _ _)
    positivity
  have hP : preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ≤ spatial := by
    unfold preparedSlicedForecastSpatialBudget
    apply max_le
    · dsimp only [spatial]
      have hpow : 0 ≤ (primitive + Csp) ^ Csp := by positivity
      linarith only [hDbase, hnX, hpow, hcost0]
    · apply max_le
      · dsimp only [spatial]
        linarith only [hcenter, hb, hcost0]
      · dsimp only [spatial]
        have hpow : 0 ≤ (primitive + Csp) ^ Csp := by positivity
        linarith only [hb, hpow]
  have hscale0 : 0 ≤ allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 := by
    linarith only [hDbase0, hRadius.1]
  have hscale : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 ≤ r := by
    apply le_trans _ hscaler
    linarith only [hDbase, hRadius.2]
  have hbadInput0 : 0 ≤ preparedSlicedForecastBadLog m nX Qstride gainLog := by
    unfold preparedSlicedForecastBadLog
    have := hStride.1
    have := hGain.1
    positivity
  have hbadInput : preparedSlicedForecastBadLog m nX Qstride gainLog ≤ r := by
    apply le_trans _ hbadr
    have hmul : 2 * (nX : ℝ) * Qstride ≤ 2 * b * primitive :=
      mul_le_mul (mul_le_mul_of_nonneg_left hnX (by norm_num)) hStride.2 hStride.1
        (by positivity)
    dsimp only [preparedSlicedForecastBadLog, bad]
    nlinarith only [hmul, hGain.2]
  have hjacInput0 : 0 ≤ preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart := by
    unfold preparedSlicedForecastJacobianLog
    have := hRadius.1
    have := hGain.1
    have := hChart.1
    positivity
  have hjacInput : preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart ≤ r := by
    apply le_trans _ hjacr
    have hleft : ((nX + m + m * M : ℕ) : ℝ) ≤ b + m := by
      have hdim : (nX : ℝ) + m * M ≤ b := by
        simpa only [Nat.cast_add, Nat.cast_mul] using hDmod
      simp only [Nat.cast_add, Nat.cast_mul]
      linarith only [hdim]
    have hright : pRadius + gainLog + nX + Pchart + 11 ≤ 3 * primitive + b + 11 := by
      linarith only [hRadius.2, hGain.2, hnX, hChart.2]
    have hnX0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg nX
    exact mul_le_mul hleft hright
      (by linarith only [hRadius.1, hGain.1, hChart.1, hnX0]) (by positivity)
  have htailInput0 : 0 ≤ preparedSlicedForecastTailLog cost :=
    preparedSlicedForecastTailLog_nonneg hcost0
  have htailInput : preparedSlicedForecastTailLog cost ≤ r := by
    apply le_trans _ htailr
    have hprimitive : preparedSlicedForecastPrimitiveCap ≤ (Cprim : ℝ) := Nat.le_ceil _
    dsimp only [preparedSlicedForecastTailLog, tail]
    linarith only [hprimitive]
  have hcap := hgeneric (nX + m * M) nX hr0 (hDmod.trans hbr) (hnX.trans hbr)
    ⟨hP0, hP.trans hspatialr⟩ ⟨hscale0, hscale⟩ ⟨hbadInput0, hbadInput⟩
    ⟨by linarith only [hcost0], hcostr⟩ ⟨hjacInput0, hjacInput⟩
    ⟨by linarith only [hcost0], hcostr⟩ ⟨htailInput0, htailInput⟩
    ⟨hcost0, by linarith only [hcostr]⟩
    ⟨by linarith only [hChild.1], (add_le_add hChild.2 (le_refl (1 : ℝ))).trans hchildr⟩
  have hfinal : (r + Cg) ^ Cg ≤ (b + C) ^ C := by
    simpa [R, S, Bad, Jac, Tail, W, H, Pr, X, r, spatial, bad, jac, tail, cost, child, primitive,
      Polynomial.eval₂_pow] using hpoly b hb
  exact ⟨hcap.1, hcap.2.trans hfinal⟩

noncomputable def preparedConcreteSlicedForecastPrimitiveCapExponent
    (m Ccontrol Cchild Cprimitive : ℕ) : ℕ :=
  Classical.choose (exists_preparedConcreteSlicedForecastPrimitiveCapLog_budget m Ccontrol Cchild Cprimitive)

end Erdos3.VectorPolynomial

end

end OAI

end


