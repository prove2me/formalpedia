-- Prove2me | Definitions.Def_OAIE3v2B284
-- name    : OAIE3v2B284
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T07:13:23.163396+00:00
-- url     : https://prove2.me/theorems/f5466bc5-c334-475b-b549-673b4fd31bfb
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 297 of 311
-- statement:
--   Definitions bundle 297 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B277` of this split.
--
--   Modules: `Dynamics/PreparedFiniteNestedCanonicalEarlyPrimitiveBudget.lean`, `Estimates/PreparedFiniteNestedAnchorRequiredPower.lean`, `Estimates/SharedWidthPreparedModularGeneralDirectDetectionFreeTrim.lean`, `Linear/PreparedCenteredMarginalProjectionBounds.lean`, `Sampling/PreparedCenteredShortForecastGoodInterface.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B277

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedCenteredMarginalProjectionBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem preparedCenteredMarginalProjectionBounds
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {s : ℕ} {Pmaster Plate D : ℝ} (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hd : AllocatedComparisonDimensions (G := G) B (Fin (s + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type)) D)
    (hD : D ≤ Pmaster) {nX : ℕ} (hnX : (nX : ℝ) ≤ Pmaster)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (hσLate : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate)
    (hLLate : (S.value : ℝ) ≤ Real.exp Plate) :
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s)
      (s + 1) Pmaster Plate
    PreparedCenteredMarginalProjectionBounds B U basis S nX Pmaster Plate r.Pproj := by
  intro r
  have hproj : r.Pproj = 4 * (Plate + 8) ^ 2 := rfl
  have hPlate : 0 ≤ Plate := hMaster.trans hLate
  have hLproj : Plate ≤ r.Pproj := by
    nlinarith only [hproj, hPlate, sq_nonneg Plate]
  have hExpLate := Real.exp_le_exp.mpr hLproj
  have hPproj : Pmaster ≤ r.Pproj := hLate.trans hLproj
  have h2Pproj : 2 * Pmaster ≤ r.Pproj := by
    nlinarith only [hproj, hPlate, hLate, sq_nonneg Plate]
  have hframeProj : (2 * Pmaster + 1) * Pmaster ≤ r.Pproj := by
    have hsq : Pmaster^2 ≤ Plate^2 := pow_le_pow_left₀ hMaster hLate 2
    nlinarith only [hproj, hPlate, hLate, hsq, sq_nonneg Plate]
  have hExp := Real.exp_le_exp.mpr hPproj
  have hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ 2 * Pmaster :=
    (preparedModularGeneralDetector_variable_count B
      (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) hd).trans
        (by linarith only [hD])
  have hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) : ℝ) ≤ r.Pproj := by
    rw [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact (mul_le_mul (add_le_add_left hvars 1) hnX (Nat.cast_nonneg _) (by positivity)).trans
      (by simpa only [add_comm] using hframeProj)
  obtain ⟨hI, hn⟩ := preparedModularGeneralDetector_layer_axes B
    (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) hd
  have hJ (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ r.Pproj :=
    (Nat.cast_le.mpr (allocatedAmbientDimension_le_axes U basis o j)).trans
      (hd.axes.trans (hD.trans hPproj))
  have hWproj : allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ Real.exp r.Pproj :=
    (preparedModularGeneralDetector_physical_root B
      (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) U basis S hd
        (hD.trans hLate) hLLate).trans
      (Real.exp_le_exp.mpr (by nlinarith only [hproj, hPlate, hLate, sq_nonneg Plate]))
  exact {
    Pproj_nonneg := hMaster.trans hPproj
    master_projection := hPproj
    late_projection := hLproj
    m_projection := hd.degree.trans (hD.trans hPproj)
    variables_projection := hvars.trans h2Pproj
    X_projection := by simpa only [Fintype.card_fin] using hnX.trans hPproj
    frame_projection := hframe
    coefficient_projection := fun j => (hd.coefficients j).trans (hD.trans hPproj)
    I_projection := fun j => (hI j).trans (hD.trans hPproj)
    n_projection := fun j => (hn j).trans (hD.trans hPproj)
    J_projection := hJ
    Rinv_projection := fun j => (hRP j).trans hExp
    σinv_projection := fun j => (hσLate j).trans hExpLate
    S_projection := hLLate.trans hExpLate
    root_projection := hWproj
    profile_projection := ((hd.profile.trans (hD.trans hPproj)).trans
      (by linarith [Real.add_one_le_exp r.Pproj])) }

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedWidthPreparedModularGeneralDirectDetectionFreeTrim
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (pDetect qDetect α : ℝ)
variable {P : ℝ}

local notation "grid" => allocatedGridAxis (I := I) U basis S.value

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

def AllocatedPreparedNativeInterfaceGeneralSharedWidth
    (Pchart P _D target Pk Prho Qstride : ℝ) (K : ℝ≥0) : Prop :=
    ∀ (_hMkP : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp P)
    (_hMkPk : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp Pk)
    (_hQstride : 0 ≤ Qstride)
    (_hstride : ∀ i, 0 < stride i)
    (_hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ)
    (_hC : ∀ j, 0 ≤ C j)
    (_hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (_hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    {Pbox Vlog Nlog Mlog baseAmbient : ℝ}
    (_hPbox : 0 ≤ Pbox)
    (_hVlog : 0 ≤ Vlog)
    (_hNlog : 0 ≤ Nlog)
    (_hMlog : 0 ≤ Mlog)
    (_hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Pbox)
    (_hvolume : allocatedFullGridNaturalVolume B U basis S rowSets ≤ Real.exp Vlog)
    (_hnormalizer : ‖((allocatedProductIdealNormalizer B U basis S rowSets : ℝ) : ℂ)⁻¹‖ ≤ Real.exp Nlog)
    (_hmaskLog : (Fintype.card (LayerSamplerAxis I n) : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (selectedRows j) * (((m + 1 : ℕ) : ℝ) * Pk)) ≤ Mlog)
    (_hbaseAmbient : 0 ≤ baseAmbient)
    (_hvbase : Vlog ≤ baseAmbient)
    (_hnbase : Nlog ≤ baseAmbient)
    (_hmbase : Mlog ≤ baseAmbient)
    (_hsites : (Fintype.card (Finset (Fin (s + 1))) : ℝ) ≤ baseAmbient)
    (_haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ baseAmbient)
    (_hlabelLog : (∑ j, (n j : ℝ) * (((m + 1 : ℕ) : ℝ) * Pk)) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (((m + 1 : ℕ) : ℝ) * Pk) ≤ baseAmbient)
    (_hKbase : (K : ℝ) ≤ Real.exp baseAmbient)
    (_hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (_hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp baseAmbient)
    (_hperiodLog : ((m + 1 : ℕ) : ℝ) * Pk ≤ baseAmbient)
    (_hrowsAmbient : ((∑ j : Fin m, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (_houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ baseAmbient)
    (_hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp baseAmbient)
    (Qgrid : ℝ≥0)
    (_hQgrid : ∀ a : {a // allocatedGridAxis (I := I) U basis S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U basis S a).1 (allocatedGridIntegerAxis B U basis S a).2) : ℝ) + 1) ≤ Qgrid)
    (Ag : ℝ≥0)
    (_hAg : LipschitzWith Ag Real.smoothTransition)
    (_hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (_hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg : ℝ}
    (_hDg : 0 ≤ Dg)
    (_hvg : 0 ≤ vg)
    (_hwg : 0 ≤ wg)
    (_hcube : (Fintype.card (Fin (s + 1)) : ℝ) ≤ Dg)
    (_hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (_hrowsD : ∀ j : Fin m, ((boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card : ℝ) ≤ Dg)
    (_htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ Dg)
    (_hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ Dg)
    (_hRv : ∀ j, R j ≤ Real.exp vg)
    (_hRiGrid : ∀ j, (R j)⁻¹ ≤ Real.exp vg)
    (_hδw : pDetect + 1 ≤ wg)
    (_hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp vg)
    (_haxesGrid : (Fintype.card {a // grid a} : ℝ) ≤ Dg)
    (_hfullAxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ Dg)
    (_hfullOutputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ Dg)
    (_hambientCount : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ Dg)
    (_hprofileBudget : (probabilityProfileLipschitz : ℝ) ≤ Dg)
    {Banalytic : ℝ}
    (_hBanalytic : 0 ≤ Banalytic)
    (_hDanalytic : Dg ≤ Banalytic)
    (_hcutoffAnalytic : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Banalytic)
    (_hcoordAnalytic : ((K * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp Banalytic)
    (_hgridAnalytic : (Qgrid : ℝ) ≤ Real.exp Banalytic)
    {Pnum : ℝ}
    (_hPnum : 0 ≤ Pnum)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum)
    (_hn : ∀ j, (n j : ℝ) ≤ Pnum)
    (_hcoeffEarly : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
    (_hRiEarly : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
    (_hVEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Real.exp Pnum)
    {Pproj coarseTarget Ecoarse pGain : ℝ},
    let ambientQ := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1)) (Fintype.card (Fin (s + 1)))
      (Pbox + Prho + Vlog + Nlog + Mlog + target)
    let ambientBudget := affineAmbientPrimitiveBudget baseAmbient ambientQ
    ∀ {τ Pphysical : ℝ},
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    ∀ {ξn : ℝ} (hξn : 0 < ξn), ξn ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) Pphysical coarseTarget →
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      (signal : ((Fin nX) → ℤ) → ℂ),
    (∀ u ∈ integerBox N, ‖signal u‖ ≤ 1) →
    (∀ u, u ∉ integerBox N → signal u = 0) →
    ∀ {lossTarget Psample Rrank Sstride εsample ηsample : ℝ},
    (∀ i, 0 < stride i) → (∀ i, 0 < N i) → (hτSpatial : 0 < τ) →
    0 ≤ Psample → (Fintype.card (Fin nX) : ℝ) ≤ Psample →
    (Fintype.card (Option (Fin (s + 1)) × (Fin nX)) : ℝ) ≤ Psample →
    0 ≤ Sstride → Sstride ≤ Real.exp Psample → 0 < εsample →
    1 / τ ≤ Real.exp Psample → 1 / εsample ≤ Real.exp Psample →
    (∀ i, (stride i : ℝ) ≤ Sstride) →
    let A := Classical.choose (exists_translated_physical_jet_l1_perturbation.{0,0,0} m (s + 1))
    (∀ i, Real.exp ((Psample + A) ^ A) ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp ((Psample + A) ^ A) ≤ Rrank →
    0 < ηsample → (Fintype.card (CoefficientAmbientIndex (Fin (s + 1)) J) : ℝ) ≤ Psample →
    ambientBudget ≤ Psample →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin (s + 1)) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Psample →
    ηsample⁻¹ ≤ Real.exp Psample →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    (_hPhysicalNonneg : 0 ≤ Pphysical) → (_hMkPhysicalBound : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp Pphysical) →
    (_hmPhysicalBound : ((m + 1 : ℕ) : ℝ) ≤ Pphysical) → (_hCoarseNonneg : 0 ≤ coarseTarget) →
    (_hDimPhysicalBound : (((s + 1) + 1 : ℕ) : ℝ) ≤ Pphysical) →
    (_hGPhysicalBound : (Fintype.card G : ℝ) ≤ Pphysical) →
    (_hXPhysicalBound : (Fintype.card (Fin nX) : ℝ) ≤ Pphysical) →
    lossTarget + coefficientErrorSpatialLog Pphysical + 8 ≤ target →
    ηsample ≤ Real.exp (-target) → εsample ≤ Real.exp (-target) →
    let Amass := Classical.choose (exists_allocatedAffineModelMass_budget m (s + 1))
    let Aanalytic := Classical.choose (exists_allocatedAffineAnalytic_budget m (s + 1))
    let Fmodel := (m * (2 : ℝ) ^ Fintype.card (Fin (s + 1))) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (selectedRows j) * ((m + 1 : ℕ) * Pk))
    let Cgrid := Classical.choose (exists_preparedModularCanonicalDetector_grid_parameters.{0} m (s + 1) Ag)
    let Qlog := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
    let tg := ((s + 1 : ℕ) : ℝ) + Qlog + (pDetect + 1) + 1
    let pg := (Cgrid : ℝ) + (((s + 1) + 1 : ℕ) : ℝ) * Qlog + (pDetect + 1) + 4
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    ∀ {Pnative : ℝ}, 0 ≤ Pnative →
    Dg ∈ Set.Icc 0 Pnative → p ∈ Set.Icc 0 Pnative → vg ∈ Set.Icc 0 Pnative →
    Fmodel ∈ Set.Icc 0 Pnative → Prho ∈ Set.Icc 0 Pnative → Pk ∈ Set.Icc 0 Pnative →
    target ∈ Set.Icc 0 Pnative → Banalytic ∈ Set.Icc 0 Pnative →
    Pphysical ∈ Set.Icc 0 Pnative → Ecoarse ∈ Set.Icc 0 Pnative → pGain ∈ Set.Icc 0 Pnative →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pphysical) →
    1 / τ ≤ Real.exp Pphysical →
    Real.exp (-pGain) / 2 ≤ (allocatedDetectedGain s (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) / 2 →
    pGain + 32 ≤ Pproj → pGain + 32 ≤ coarseTarget →
    pGain + 32 ≤ Ecoarse → pGain + 32 ≤ lossTarget →
    ∀ (Cproj Vproj : Fin m → ℝ≥0),
    let Acover := Classical.choose (exists_allocated_canonical_constructed_projection.{0,0,0,0,0} m (s + 1))
    let coverLog := (Pproj + ((s + 1) + 2 : ℕ) + Acover) ^ Acover
    let Asample := Classical.choose (exists_allocatedCanonicalProjection_composed_budget m (s + 1) Acover)
    let Pmass := (Pproj + Asample) ^ Asample
    coverLog ≤ baseAmbient → coverLog ≤ Psample → Pmass ≤ Psample →
    (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ Cproj j * ‖z‖) →
    (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vproj j) →
    (Fintype.card (Fin nX) : ℝ) ≤ Pmass →
    (Fintype.card (Option (Fin (s + 1)) × Fin nX) : ℝ) ≤ Pmass →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pmass) → 1 / τ ≤ Real.exp Pmass →
    let AmassWindow := Classical.choose (exists_translated_physical_jet_density_window_mass.{0,0,0,max 0 0 0} m (s + 1))
    (∀ i, Real.exp ((Pmass + AmassWindow) ^ AmassWindow) ≤ (N i : ℝ)) →
    Real.exp ((Pmass + AmassWindow) ^ AmassWindow) ≤ Rrank →
    (Fintype.card (CoefficientAmbientIndex (Fin (s + 1)) J) : ℝ) ≤ Pmass →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin (s + 1)) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Pmass →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Pphysical →
    1 ≤ Pproj → (m : ℝ) ≤ Pproj →
    (Fintype.card G : ℝ) ≤ Pproj → (S.value : ℝ) ≤ Real.exp Pproj →
    ((m + 1 : ℕ) : ℝ) * Pk ≤ Pproj →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pproj → W ≤ Real.exp Pproj →
    (∀ j, (R j)⁻¹ ≤ Real.exp Pproj) → (∀ j, (σ j)⁻¹ ≤ Real.exp Pproj) →
    (∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pproj) →
    (∀ j, (Fintype.card (I j) : ℝ) ≤ Pproj) → (∀ j, (n j : ℝ) ≤ Pproj) →
    (∀ j, (Fintype.card (J j) : ℝ) ≤ Pproj) →
    (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pproj →
    (∀ j, (Cproj j : ℝ) ≤ Real.exp Pproj) → (∀ j, (Vproj j : ℝ) ≤ Real.exp Pproj) →
    (Fintype.card (Fin nX) : ℝ) ≤ Pproj →
    (Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) : ℝ) ≤ Pproj →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pproj) → τ⁻¹ ≤ Real.exp Pproj → ξn⁻¹ ≤ Real.exp Pproj →
    let Aproj := Classical.choose (Classical.choose_spec
      (exists_allocated_canonical_constructed_projection.{0,0,0,0,0} m (s + 1)))
    (∀ i, Real.exp ((Pproj + Aproj) ^ Aproj) ≤ (N i : ℝ)) →
    Real.exp ((Pproj + Aproj) ^ Aproj) ≤ Rrank →
    ∀ {Pside : ℝ}, Pproj ≤ Pside → Pmass ≤ Pside →
    Pphysical ≤ Pside → coarseTarget ≤ Pside →
    (∀ i, Real.exp ((Pside + Classical.choose (exists_allocatedCanonicalSpatial_cutoff.{0,0,0,0} m)) ^
      Classical.choose (exists_allocatedCanonicalSpatial_cutoff.{0,0,0,0} m) + Pproj) ≤ (N i : ℝ)) →
    cells.Nonempty → ∀ (bases : Finset (Fin nX → ℤ)), (hbases : bases.Nonempty) →
    ∀ (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z),
    (htotal : 0 < selectedJointDensityMass bases stride cells V
      (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem)) →
    let Path := bases × rectangularWeightIndices 0 V 1
    let pathLaw := allocatedOriginalPathLaw B U basis hb o hR hσ S (Fin nX) poly hmem N
      (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i))) hW hτSpatial hξn stride cells hmass bases hbases htotal
    ∀ {Tdetect : Type} [Fintype Tdetect] [Nonempty Tdetect]
      (e : Tdetect → LayerSamplerVariables G I n B → ℤ), Function.Injective e →
    ∀ {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
      {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)] [∀ z j, LieAlgebra ℚ (Ldetect z j)]
      {dims : ∀ z, Tests z → ℕ}
      [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
      (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) s (dims z j))
      (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
      (slices : ∀ z, Tests z → Finset Tdetect)
      (cdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
      (stepdetect : ∀ z, Tests z → ℕ)
      (Hdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ),
    (∀ z j, 0 < stepdetect z j) →
    (∀ z j, (slices z j).image e = commonStrideBox (cdetect z j) (stepdetect z j) (Hdetect z j)) →
    0 ≤ pDetect → 0 ≤ qDetect →
    (∀ z j, IsDenseCommonStrideBox
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)) pDetect ((slices z j).image e)) →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect →
    (∀ z j, (Vdetect z j).ComplexityLE (Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect)) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    0 < α → α ≤ 1 →
    Fintype.card (LayerSamplerVariables G I n B) * Real.exp (-pDetect) ≤ α / 8 →
    Real.exp (-qDetect) ≤ α / 4 →
    α ≤ sampledSliceSeminorm pathLaw
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((Vdetect z j).eval (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) signal →
    (s + 1) * (s + 3) ≤ Fintype.card G → (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) ≤ S.value →
    let C := Classical.choose (exists_canonicalSlicedNative_input_budget m (s + 1) Amass Aanalytic)
    let Bbudget := (Pnative + C) ^ C
    let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{0,0,0,0,0,0} m (s + 1))
    let Anative := Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)
    let A := Classical.choose (exists_normalizedNative_uniform_budget m Anorm Anative)
    let budget := (Bbudget + A) ^ A
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun u : integerBox N => u.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
            (fun u => signal u.val) (fun u => star (twistData.eval N poly u.val) * Fnative u)‖

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedCenteredShortForecastGoodInterface
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_preparedCentered_short_forecastGoodData (m : ℕ) :
    ∃ A Asp : ℕ, 4 ≤ A ∧ 2 ≤ Asp ∧
    (∀ {P₀ gainLog : ℝ} {n : ℕ}, 0 ≤ P₀ → 0 < n → (n : ℝ) ≤ P₀ →
      0 ≤ gainLog → gainLog ≤ P₀ →
      (spatialMatrixBlockThreshold n (jointSpatialError gainLog))⁻¹ ≤
        Real.exp ((P₀ + Asp) ^ Asp)) ∧
    ∀ {nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (B0 Vlog gainLog gain : ℝ) (Q : ℕ)
    (_hsource : PreparedShortCertifiedSameScaleBadProductInterface prep U b S B0 (gainLog + 8) Vlog Q)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) + 1) * R j ≤ 1/4)
    {Pchart Pmaster Plate D Pwidth P₀ P : ℝ}
    (_hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp Pchart)
    (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp Pchart)
    (_hchartB : Pchart ≤ B0)
    (_hMaster : 0 ≤ Pmaster) (_hLate : Pmaster ≤ Plate)
    (_hd : AllocatedComparisonDimensions (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (Fin (0 + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1) : Type)) D)
    (_hD : D ≤ Pmaster) (_hnMaster : (nX : ℝ) ≤ Pmaster)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate)
    (_hS : (S.value : ℝ) ≤ Real.exp Plate)
    (_hprojection : (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate).Pproj ≤ Pwidth)
    (_hphysical : jointPhysicalBaseLog Pwidth (gainLog + 8) Vlog ≤ B0)
    (_hVlog : 0 ≤ Vlog) (_hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (_hP₀ : 0 ≤ P₀) (_hnP₀ : (nX : ℝ) ≤ P₀) (_hgP₀ : gainLog ≤ P₀)
    (_hcutoffP : (P₀ + Asp) ^ Asp ≤ P)
    (_hBP : B0 ≤ P) (_hwidthP : Pwidth ≤ P)
    (_hg : 0 ≤ gainLog) (_hgP : gainLog + 8 ≤ P) (_hgain : Real.exp (-gainLog) ≤ gain)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (stride : Fin nX → ℕ) (_hstride : ∀ x, 0 < stride x)
    (_hstrideP : ∀ x, (stride x : ℝ) ≤ Real.exp Pwidth)
    {τ ξ : ℝ} (hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp Pwidth)
    (hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp Pwidth),
    let W := allocatedPhysicalRootBudget (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (fun _ => 0)
    let required := max
      ((((B0 + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m) +
        allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m)
      ((P + A) ^ A)
    ∀ (N : Fin nX → ℕ) (hN : ∀ x, 0 < N x),
    (∀ x, Real.exp required ≤ (N x : ℝ)) →
    ∀ {Rs : ℝ},
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun x => (N x : ℝ)) Rs (U j) (poly j)) →
    Real.exp required ≤ Rs →
    ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride)),
    cells.Nonempty →
    let width := narrowTrimmedSpatialWidths (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (J := PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) W τ ξ N
    let hwidth := narrowTrimmedSpatialWidths_pos
      (allocatedPhysicalRootBudget_nonneg (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (fun _ => 0)) hτ hξ N hN
    ∀ (bases : Finset (Fin nX → ℤ)) (hbases : bases.Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z)
      {Eforecast : ℝ}
      (hnormalizerCenter : ∀ center,
        let Z := selectedJointDensityMass bases stride cells width
          (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center)
        |Z - 1| ≤ Real.exp (-Eforecast) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
          0 < Z ∧ Z⁻¹ ≤ 2)
      (_hnX : 0 < nX)
      (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))),
    ∃ (c : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → ∀ j, U j), Measurable c ∧
      (∀ center, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c center s.1)))) ∧
    ∃ (sample : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
      (read : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ),
      (∀ center a, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) center (c center) a (sample center a) (read center a)) ∧
      let law := fun center => selectedJointFiniteLaw bases hbases stride cells width hwidth hmass (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center) (allocatedCenteredJointDensity_nonneg (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center) (hnormalizerCenter center).2.2.1
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
        ∃ bad : Set (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U ×
          (bases × rectangularWeightIndices 0 width 1)),
          MeasurableSet bad ∧ (centeredFiniteProbabilityMeasure μ law).real bad ≤ (gain / 4) / 4 ∧
          ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, z ∉ bad →
            AllocatedCenteredFramedRecoveredSampleAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o S hR hσ poly hm
              (c z.1) z.2.1.val z.2.2.val (sample z.1 z.2.1.val z.2.2.val) (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val)) ∧
            (∏ p ∈ primes, p ^ largestTestedBadDepth depth (allocatedActualPrimeBad (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val))) ≤ (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius (gainLog + 8)) ∧
            ∀ t : Fin 2, spatialMatrixBlockThreshold nX (jointSpatialError gainLog) / 2 <
              |Matrix.det (fun i j : Fin nX =>
                spatialMatrixNormalizedEntries e width z.2.2.val (t,j,i))| := by
  obtain ⟨A, Asp, hA, hAsp, hκ, hgood⟩ := exists_preparedCentered_short_jointGoodPolynomial m
  refine ⟨A, Asp, hA, hAsp, hκ, ?_⟩
  intro nX M X₀ J₀ prep U b R σ S B0 Vlog gainLog gain Q hsource E _ bW hb o C V hC hV
    hR hσ hσ1 Cinv hCinv hchart hsmall Pchart Pmaster Plate D Pwidth P₀ P
    hprofile hCP hVP hchartB hMaster hLate hd hD hnMaster hRi hσi hS hprojection
    hphysical hVlog hQexp hP₀ hnP₀ hgP₀ hcutoffP hBP hwidthP hg hgP hgain
    _ _ _ _ μ _ _ ν _ _ poly hp hm stride hstride hstrideP τ ξ hτ hτP hξ hξ1 hξP
    W required N hN hsize Rs hrank hRs cells hcells width hwidth bases hbases hmass
    Eforecast hnormalizerCenter hnX e
  have hproj := preparedCenteredMarginalProjectionBounds (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S o
    (s := 0) hMaster hLate hd hD hnMaster hRi hσi hS
  have hPwidth : 0 ≤ Pwidth := hproj.Pproj_nonneg.trans hprojection
  have hP : 0 ≤ P := hPwidth.trans hwidthP
  have hprojP := hprojection.trans hwidthP
  have hExpProjection := Real.exp_le_exp.mpr hprojP
  have hExpWidth := Real.exp_le_exp.mpr hwidthP
  have hExpChart := Real.exp_le_exp.mpr hchartB
  have hExpPhysical := Real.exp_le_exp.mpr hphysical
  have hW : 0 ≤ W := allocatedPhysicalRootBudget_nonneg (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (fun _ => 0)
  have hWP : W ≤ Real.exp Pwidth := hproj.root_projection.trans
    (Real.exp_le_exp.mpr hprojection)
  obtain ⟨_, _, _, _, hρ, hρinv, hSmax, hSmaxB, hstrideMax, hwide⟩ :=
    jointPhysicalScalarBudget (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (J := PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)))
      hPwidth hW hWP hτ hτP hξ hξ1 hξP (by linarith : 0 ≤ gainLog + 8)
      hVlog Q hQexp stride hstrideP
  have hsizeMod (x) := (Real.exp_le_exp.mpr (le_max_left _ _)).trans (hsize x)
  have hsizeSpatial (x) := (Real.exp_le_exp.mpr (le_max_right _ _)).trans (hsize x)
  have hRsMod := (Real.exp_le_exp.mpr (le_max_left _ _)).trans hRs
  have hRsSpatial := (Real.exp_le_exp.mpr (le_max_right _ _)).trans hRs
  exact hgood prep U b S B0 Vlog gainLog gain Q hsource bW hb o C V hC hV
    hR hσ hσ1 Cinv hCinv hchart hsmall (hprofile.trans hExpChart)
    (fun j => (hCP j).trans hExpChart) (fun j => (hVP j).trans hExpChart)
    μ ν poly hp hm hρ (hρinv.trans hExpPhysical) stride hstride
    hSmax (hSmaxB.trans hExpPhysical) hstrideMax N hsizeMod hrank hRsMod
    cells hcells width hwidth (hwide N hN) bases hbases hmass
    (fun center => (hnormalizerCenter center).2.2.1)
    hP₀ hnP₀ hgP₀ hcutoffP hP hBP hg hgP hgain
    (hproj.m_projection.trans hprojP) (hproj.variables_projection.trans hprojP)
    (by simpa only [Fintype.card_fin] using hproj.X_projection.trans hprojP)
    (hproj.frame_projection.trans hprojP)
    (fun j => (hproj.Rinv_projection j).trans hExpProjection)
    (fun j => (hproj.σinv_projection j).trans hExpProjection)
    (fun j => (hproj.coefficient_projection j).trans hprojP)
    (fun j => (hproj.I_projection j).trans hprojP)
    (fun j => (hproj.n_projection j).trans hprojP)
    (fun j => (hproj.J_projection j).trans hprojP)
    (hproj.S_projection.trans hExpProjection)
    (fun x => (hstrideP x).trans hExpWidth) hW (hWP.trans hExpWidth)
    hτ (hτP.trans hExpWidth) hξ hξ1 (hξP.trans hExpWidth)
    hsizeSpatial hRsSpatial rfl hnX e

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

noncomputable def preparedCenteredShortForecastGoodExponent (m : ℕ) : ℕ :=
  (exists_preparedCentered_short_forecastGoodData m).choose

noncomputable def preparedCenteredShortForecastSpatialExponent (m : ℕ) : ℕ :=
  (exists_preparedCentered_short_forecastGoodData m).choose_spec.choose

noncomputable def preparedCenteredShortForecastGoodRequired (m : ℕ) (B0 Pgood : ℝ) : ℝ :=
  max ((((B0 + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m) +
    allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m)
    ((Pgood + preparedCenteredShortForecastGoodExponent m) ^ preparedCenteredShortForecastGoodExponent m)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedCanonicalEarlyPrimitiveBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteNestedSourceNative_budget
    {outerDepth innerDepth cutoff : ℕ} (m : ℕ) (G : Type) [Fintype G]
    (count nX A Cdirect : ℕ) (constants : ℕ → ℕ)
    {Bstruct pnum Qstride gainLog stageLog : ℝ}
    (hcutoff : cutoff ≤ m) (hA : 2 ≤ A) (hB : 0 ≤ Bstruct)
    (hnum : pnum ∈ Set.Icc 0 Bstruct) (hstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hg : gainLog ∈ Set.Icc 0 Bstruct) (hs : stageLog ∈ Set.Icc 0 Bstruct)
    (hcount : (count : ℝ) ≤ Bstruct) (hnX : (nX : ℝ) ≤ Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (Plate : ℝ) (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
    let seed := preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k
    let stage := (preparedFiniteNestedForwardAllDegreeStage k).val
    let C := preparedFiniteNestedSourceNativeExponent m cutoff Cdirect
    preparedFiniteNestedSourceNative m G count nX (preparedFiniteForwardDetectorPolynomial cutoff)
      A Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate k ∈ Set.Icc 0
        ((preparedFiniteForwardSourcePrecision A constants stage seed gainLog stageLog +
          preparedFiniteForwardWork A constants stage seed + C) ^ C) := by
  intro seed stage C
  let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
  let Cresource := preparedFiniteForwardActualNativeBudgetExponent m Pdetect
  have hseed : Bstruct ≤ seed :=
    le_preparedFiniteNestedForwardAllDegreeSeed A constants hA hB k
  have hseed0 : 0 ≤ seed := hB.trans hseed
  have hg' : gainLog ∈ Set.Icc 0 seed := ⟨hg.1, hg.2.trans hseed⟩
  have hs' : stageLog ∈ Set.Icc 0 seed := ⟨hs.1, hs.2.trans hseed⟩
  let d : Fin (m + 1) := ⟨preparedFiniteNestedForwardAllDegreeDegree k,
    Nat.lt_succ_of_le (preparedFiniteNestedForwardAllDegreeDegree_le hcutoff k)⟩
  have hresource := (Classical.choose_spec (exists_preparedFiniteForwardActualNativeBudget m Pdetect)).2
    d A Cdirect constants stage (preparedFiniteNestedForwardAllDegreeIsDirect k)
    (G := G) hA hseed0 hg' hs'
    ⟨hB, hseed⟩ ⟨hnum.1, hnum.2.trans hseed⟩ ⟨hB, hseed⟩
    ⟨hstride.1, hstride.2.trans hseed⟩
    (hcount.trans hseed) (hnX.trans hseed) (hG.trans hseed) Plate
  have hn := hresource.2.2.1
  refine ⟨hn.1, hn.2.trans ?_⟩
  exact preparedFiniteForwardAllSlotResource_budget A Cdirect Cresource constants stage
    (preparedFiniteNestedForwardAllDegreeIsDirect k) hseed0 hg' hs'

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

end OAI
end


