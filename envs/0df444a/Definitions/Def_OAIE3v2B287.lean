-- Prove2me | Definitions.Def_OAIE3v2B287
-- name    : OAIE3v2B287
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T07:24:49.840422+00:00
-- url     : https://prove2.me/theorems/0dda3b12-c703-4258-945f-fd5d49329dcb
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 300 of 311
-- statement:
--   Definitions bundle 300 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B277`, `OAIE3v2B278` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidateTaggedPairLongUniformFactors.lean`, `Estimates/SharedWidthPreparedPerturbativeCertifiedSource.lean`, `Sampling/SharedWidthPreparedShortForecastSourceModelAttachment.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B277
import Definitions.Def_OAIE3v2B278

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairLongUniformFactors
namespace OAI

universe u

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit

theorem exists_allocatedExternalCandidateTaggedPairFamily_long_common_factors
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ C Cbasis K T : ℕ, 2 ≤ C ∧ 2 ≤ Cbasis ∧ 2 ≤ K ∧ 2 ≤ T ∧
    ∀ {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

    {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Ω] [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
    {d₀ t : ℕ} {d : Pivot → ℕ}
    {D : RationalFilteredNilmanifold LG s d₀}
    {E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j)}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p periodCap coverCap : ℝ} {Lip : ℝ≥0}
    {H : Finset Ω},
    ∀ {α : Type*} [Fintype α] {pGeo bnd : ℝ},
      0 ≤ pGeo → 0 ≤ bnd →
      (∀ j, (pi (pairModels D (E j))).GeometryComplexityLE pGeo) →
      pGeo ≤ bnd → (pGeo + 3) ^ 5 ≤ bnd →
      (Fintype.card α : ℝ) ≤ bnd → (Fintype.card Pivot : ℝ) ≤ bnd →
    ∀ (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG MG i)) (ω : α → ℕ)
      (hF : ∀ k, (optionProduct D E).filtration.layer k =
        Submodule.span ℚ (e '' {i | k ≤ ω i})),
      (∀ i j k, rationalLogHeight (e.repr ⁅e i, e j⁆ k) ≤ bnd) →
      (∀ i k, rationalLogHeight ((optionProduct D E).basis.repr (e i) k) ≤ bnd) →
      let localCost := allocatedFrozenTaggedPairBudget s C Cbasis pGeo p
      let r := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let P := r + (r + K) ^ K
    ∀ (outer : FiniteProbabilityWeights Ω), 0 < outer.mass H →
    ∀ (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
      (keepLong : LayerSamplerVariables G I n B → Prop)
      (_hsub : ∀ i, keepLong i → keep i)
      [Nonempty {i // keepLong i}], (Fintype.card {i // keepLong i} : ℝ) ≤ bnd →
      (∀ i : {i // keepLong i}, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤
        (A.sides i.val : ℝ)) →
      (∀ i : {i // keepLong i}, Real.exp ((P + 2) ^ T) ≤ (A.sides i.val : ℝ)) →
      let q := (P + 2) ^ T + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
      F.LongCommonFactors keepLong outer e ω hF q := by
  obtain ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, hcommon⟩ :=
    exists_allocatedFrozenTaggedFamily_common_factors s hs
  refine ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, ?_⟩
  intro m G X _ _ I J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells center
    _ A Deck Ω Pivot _ _ LG LM MG _ _ _ _ _ _ _ _ _ _ _ _ _ _ d₀ t d D E Fmark φ marked
    keep cost p periodCap coverCap Lip H
    α _ pGeo bnd hpGeo hbnd hGeo hpGeoB hInvB hα hPivot e ω hF
    hstructure he localCost r P outer hH F keepLong hsub _ hkeep hlong hcommonLong
  obtain ⟨input, hinput⟩ := F.exists_long_pair_inputs keepLong hsub
  have hresult := hcommon D E hpGeo F.hp hbnd hGeo hpGeoB hInvB hα hPivot
    e ω hF hstructure he B F.context Deck keepLong hkeep
    hlong hcommonLong outer H hH (F.extendedLongJointOrbit keepLong) F.η F.θ input
    (fun a j c w hc => by
      rw [F.extendedLongJointOrbit_mem keepLong a.val a.property]
      exact (hinput a j).2.2 c w hc)
    (fun a j => (hinput a j).1) (fun a j => (hinput a j).2.1)
  exact hresult

end Erdos3.VectorPolynomial

end

end OAI
end

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
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog u pModel
local notation "qDetect" => allocatedModelTestLog u pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SharedWidthPreparedShortForecastSourceModelAttachment
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
variable {nX : ℕ}
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
variable (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog uSource pModel
local notation "qDetect" => allocatedModelTestLog uSource pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
variable (τ u p forecastCap : ℝ)
local notation "α" => forecastAugmentedUnitThreshold u p Kslice (max 1 Ctail) forecastCap
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

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]

variable (Good : ∀ (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ)),
  (∀ j ex, coefficients (poly j) ex ∈ U j) →
  ∀ (width : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ)),
    (CoefficientTorus (K := LayerSamplerVariables G I n B) U →
      FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1)) → Prop)

def SharedWidthPreparedCenteredForecastModelExtraDataInterface
    (Pchart Qstride Pmaster Plate _pGain Pphysical coarseTarget extraRequired : ℝ) : Prop :=
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
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    ∀ {ξn : ℝ} (hξn : 0 < ξn)
      (hξle : ξn ≤ normalizedTupleNarrowWidth (Fin nX)
        (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
        (allocatedDetectedKernelCutoff 0 G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect (α / 2))
        Pphysical coarseTarget),
    ξn⁻¹ ≤ Real.exp Plate →
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    let _hξone : ξn ≤ 1 := hξle.trans (min_le_left _ _)
    let Pmarginal := r.Pproj
    let modelRequired := max r.required ((max Pmarginal E + preparedCenteredMarginalExponent m) ^
      preparedCenteredMarginalExponent m)
    let required := max modelRequired extraRequired
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
    ∀ (hN : ∀ i, 0 < N i) (hbases : bases.Nonempty) (_hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
      (_hnormalizer : |Z - 1| ≤ Real.exp (-r.E) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2)
      (_hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i),
    let _Path := bases × rectangularWeightIndices 0 V 1
    let Zcenter := fun center => selectedJointDensityMass bases stride cells V
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
    ∀ hnormalizerCenter : ∀ center,
      |Zcenter center - 1| ≤ Real.exp (-E) ∧
      Zcenter center ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
      0 < Zcenter center ∧ (Zcenter center)⁻¹ ≤ 2,
    let centeredLaw := fun center => selectedJointFiniteLaw bases hbases stride cells V
      (narrowTrimmedSpatialWidths_pos hW hτSpatial hξn N hN) hmass
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S poly hmem center) (hnormalizerCenter center).2.2.1
    Good poly hmem V bases centeredLaw

end Erdos3.VectorPolynomial

end

end OAI
end


