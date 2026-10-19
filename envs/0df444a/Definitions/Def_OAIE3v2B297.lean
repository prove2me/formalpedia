-- Prove2me | Definitions.Def_OAIE3v2B297
-- name    : OAIE3v2B297
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T09:34:19.110856+00:00
-- url     : https://prove2.me/theorems/6b142f54-a18e-432e-a56c-02a335dd4fbc
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 311 of 311
-- statement:
--   Definitions bundle 311 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B295`, `OAIE3v2B296` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidatePreparedPhysicalConclusion.lean`, `Estimates/PreparedRelativePositiveNativeRuleCanonical.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeOrdinaryTerminal.lean`, `Polynomial/AllocatedNestedSourceDegreeGlobalization.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B295
import Definitions.Def_OAIE3v2B296

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeOrdinaryTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit
  weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree realGradedSymbolPolynomial

noncomputable section

theorem exists_allocatedExternalCandidateSpatialNativeFamily_actual_physical_terminal
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ Cgeometry C Cbasis K T : ℕ, 2 ≤ Cgeometry ∧ 2 ≤ C ∧ 2 ≤ Cbasis ∧ 2 ≤ K ∧ 2 ≤ T ∧
    ∀ {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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

    {Deck : Fin m → Type} {Pivot : Type} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {dMark : ℕ} {Mmark : RationalFilteredNilmanifold LM s dMark} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Mmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Mmark.filtration φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip),
    ∀ {qVertical : ℝ}, pNative ≤ qVertical → pLocal + r + 1 ≤ qVertical →
      verticalDecompositionBudget qVertical ≤ p →
      r + verticalDecompositionBudget qVertical + 2 ≤ p →
    ∀ (H : Finset A.Path), 0 < A.law.mass H →
      (∀ a ∈ H, ∀ j, Real.exp (-r) ≤ ‖F.correlation a j‖) →
    ∀ (pGeometry : ℝ), 2 ≤ pGeometry → D.GeometryComplexityLE pGeometry →
      Mmark.GeometryComplexityLE pGeometry →
      ∀ (hφ : ∀ k, ∀ z ∈ D.filtration.layer k, φ z ∈ Mmark.filtration.layer k),
      (∀ i j, rationalLogHeight (Mmark.basis.repr (φ (D.basis j)) i) ≤ pGeometry) →
      pNative ≤ pGeometry → (Fintype.card Pivot : ℝ) ≤ pGeometry →
    ∀ (js : List Pivot) {dQ : ℕ}
      (Q : RationalFilteredNilmanifold
        (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) s dQ)
      (hQ : Q.filtration = D.filtration.pivotQuotientFiltration φ F.η js)
      (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal φ F.η js, φ x = 0),
      Q.GeometryComplexityLE pGeometry →
      (∀ i j, rationalLogHeight
        (Q.basis.repr (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)
          (D.basis j)) i) ≤ pGeometry) →
      let pGeo := (pGeometry + 2) ^ 2
      let jointGeo := (pGeometry + 3) ^ 2
      let adaptedBudget := (jointGeo + 2) ^ Cgeometry
      let bnd := adaptedBudget + (pGeo + 3) ^ 5 + pGeo + jointGeo + pGeometry + p + 2
      let localCost := allocatedFrozenTaggedPairBudget s C Cbasis pGeo p
      let jointCost := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let P := jointCost + (jointCost + K) ^ K
      let initialShortLog := max ((p + 2 + C) ^ C + 7 * p + 22) ((P + 2) ^ T)
      let keepLong := fun i => keep i ∧ Real.exp initialShortLog ≤ (A.sides i : ℝ)
    ∀ [Nonempty {i // keepLong i}],
      let qCommon := (P + 2) ^ T + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
      let pProj := max qCommon 0 + adaptedBudget + 1
      let markInput := nativeOptionFixedSourceQuotientMarkInput pGeometry
      let markBudget := (markInput + 2) ^ nativeOptionFixedSourceMarkExponent.{0, 0}
      let pTerminal := (pProj + 2) ^ 4 + markInput + markBudget + jointGeo +
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2
    ∀ (source : A.InnerSourceProfile s)
      (_hFastInput : allocatedCandidateCommonFastBudget s pTerminal ≤ source.x)
      (_hblocks : (s : ℝ) * (markInput * m) ≤ source.x)
      (_hShortInput : max cost initialShortLog ≤ (source.x + source.Cprimitive) ^ source.Cprimitive)
      (_hNativeInput : (pProj + 2) ^ 3 + qCommon ≤
        (source.x + source.Cprimitive) ^ source.Cprimitive)
      (massLog : ℝ) (hmass : Real.exp (-massLog) ≤ A.law.mass H)
      (_hMassInput : verticalDecompositionBudget qVertical * (Fintype.card Pivot : ℝ) +
        ((qCommon + 2) ^ 5 + qCommon) + massLog ≤ source.gainLog)
      (separation : ℝ)
      (_hseparation : certifiedAffineLongSideBound
        (preparedFiniteForwardCumulative source.scheduleExponent
          AllocatedExternalCandidateSampler.degreeSourceCountConstants s source.x) ≤ separation)
      [∀ r, TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
      [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
      [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
      [∀ r, T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
      (sourceCenter : ∀ j, U j)
      (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
      (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
      (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
      (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
      (scoreThreshold : ℝ)
      (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)
      (descended : (X → ℤ) → Q.Space → ℂ)
      (hrecovery : ∀ x (g : D.RealGroup),
        descended x (QuotientGroup.mk
          (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot)
            (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) g)) =
          observable x (QuotientGroup.mk g)),
      ∃ geometry : (optionProduct D (fun j => (F.native j).model)).AdaptedMapGeometryData
          (optionProduct Q (fun j => (F.native j).model))
          (optionMarkedLieMap (L := fun j => (F.native j).L)
            (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)))
          jointGeo adaptedBudget,
      ∃ markGeometry : (optionProduct Q (fun j => (F.native j).model)).FixedSourceAdaptedMarkGeometryData
          (optionProduct Mmark (fun j => (F.native j).model)) geometry.target
          (optionMarkedLieMap (L := fun j => (F.native j).L)
            (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker))
          markInput markBudget,
      let hmarkΦ := D.nativeOptionFixedSourceQuotientMark_mem_layer Mmark
        (D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (by rw [D.filtration.terminal]; exact bot_le) Q hQ
        (fun j => (F.native j).model) φ hker hφ geometry.target
      let hMark : ∀ k, (NilpotentLieFiltration.pi (optionFiltrations Mmark.filtration
          (fun j => (F.native j).model.filtration))).layer k =
          Submodule.span ℚ (markGeometry.target.basis '' {i | k ≤ markGeometry.target.weight i}) := by
        intro k
        exact Mmark.optionAdaptedModel_layers (fun j => (F.native j).model) markGeometry.target k
      F.ActualAdaptedPivotQuotientLongPhysicalTerminal keepLong H sourceCenter hpath hcenter hfrozen
        observable weight scoreThreshold hscore geometry.source.basis geometry.source.weight
        geometry.source.layers js Q hQ hker descended hrecovery geometry.target
        markGeometry.target.basis markGeometry.target.weight hMark hmarkΦ
        source.scheduleExponent source.Cprimitive source.x separation qVertical qCommon pProj := by
  obtain ⟨Cgeometry, C, Cbasis, K, T, hCgeometry, hC, hCbasis, hK, hT, hfactor⟩ :=
    exists_allocatedExternalCandidateSpatialNativeFamily_native_long_geometry_factors s hs
  refine ⟨Cgeometry, C, Cbasis, K, T, hCgeometry, hC, hCbasis, hK, hT, ?_⟩
  intro m G X _ _ I J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells center
    _ A Deck Pivot _ LG LM _ _ _ _ _ _ _ _ d₀ D dMark Mmark φ marked
    keep cost p pLocal pNative r periodCap coverCap Lip F
    qVertical hpq hprecision hfrequency hbudget H hH hcorr
    pGeometry hpGeometry hD hMmark hφ hmark hpNative hPivot js dQ Q hQ hker hQGeometry hmap
    pGeo jointGeo adaptedBudget bnd localCost jointCost P initialShortLog keepLong _ qCommon pProj
    markInput markBudget pTerminal source hFastInput hblocks hShortInput hNativeInput
    massLog hmass hMassInput separation hseparation _ _ _ _
    sourceCenter hpath hcenter hfrozen observable weight scoreThreshold hscore descended hrecovery
  classical
  have hpGeometry0 : 0 ≤ pGeometry := (by norm_num : (0 : ℝ) ≤ 2).trans hpGeometry
  have hlong (i : {i // keepLong i}) :
      Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (A.sides i.val : ℝ) :=
    (Real.exp_le_exp.mpr (le_max_left _ _)).trans i.property.2
  have hcommonLong (i : {i // keepLong i}) :
      Real.exp ((P + 2) ^ T) ≤ (A.sides i.val : ℝ) :=
    (Real.exp_le_exp.mpr (le_max_right _ _)).trans i.property.2
  obtain ⟨geometry, hproduced⟩ := hfactor F hpq hprecision hfrequency hbudget H hH hcorr
    pGeometry hpGeometry hD hpNative hPivot js Q hQ hker hQGeometry hmap
    keepLong (fun _ hi => hi.1) hlong hcommonLong sourceCenter hpath hcenter hfrozen
    observable weight scoreThreshold hscore descended hrecovery
  have hAtoms (j : Pivot) : (F.native j).model.GeometryComplexityLE pGeometry :=
    (F.native j).complexity.1.mono (F.native j).model hpNative
  obtain ⟨markGeometry, hmarkFiltration, hmarked⟩ :=
    D.exists_nativeOptionFixedSourceQuotientMarkGeometry Mmark
      (D.filtration.pivotAnnihilatorIdeal φ F.η js)
      (by rw [D.filtration.terminal]; exact bot_le) Q hQ
      (fun j => (F.native j).model) φ hker hφ geometry.target
      hpGeometry0 hD hMmark hQGeometry hAtoms hPivot hmap hmark geometry.target_forward
  refine ⟨geometry, markGeometry, ?_⟩
  intro hmarkΦ hMark
  let stageKeep := source.stageKeep
  let Hbr := ⌈Real.exp markBudget⌉₊
  have hMarkInput0 : 0 ≤ markInput :=
    (nativeOptionFixedSourceQuotientMarkInput_bounds hpGeometry0).1
  have hMarkBudget0 : 0 ≤ markBudget := by dsimp only [markBudget]; positivity
  have hJoint0 : 0 ≤ jointGeo := by dsimp only [jointGeo]; positivity
  have hProj0 : 0 ≤ (pProj + 2) ^ 4 := by positivity
  have hSampler0 : (0 : ℝ) ≤ Fintype.card (LayerSamplerVariables G I n B) := Nat.cast_nonneg _
  have hTerminal0 : 0 ≤ pTerminal := by
    dsimp only [pTerminal]
    linarith only [hProj0, hMarkInput0, hMarkBudget0, hJoint0, hSampler0]
  have hJointTerminal : jointGeo ≤ pTerminal := by
    dsimp only [pTerminal]
    linarith only [hProj0, hMarkInput0, hMarkBudget0, hSampler0]
  have hMarkInputTerminal : markInput ≤ pTerminal := by
    dsimp only [pTerminal]
    linarith only [hProj0, hMarkBudget0, hJoint0, hSampler0]
  have hMarkBudgetTerminal : markBudget + 1 ≤ pTerminal := by
    dsimp only [pTerminal]
    linarith only [hProj0, hMarkInput0, hJoint0, hSampler0]
  have hProjTerminal : (pProj + 2) ^ 4 ≤ pTerminal := by
    dsimp only [pTerminal]
    linarith only [hMarkInput0, hMarkBudget0, hJoint0, hSampler0]
  have hSamplerTerminal : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pTerminal := by
    dsimp only [pTerminal]
    linarith only [hProj0, hMarkInput0, hMarkBudget0, hJoint0]
  have hTerminalX : pTerminal ≤ source.x :=
    (allocatedCandidateCommonFastBudget_bounds s hTerminal0).2.2.trans hFastInput
  have hHbr := source.markHeight_bounds hMarkBudget0 (hMarkBudgetTerminal.trans hTerminalX)
  have hHnonempty : H.Nonempty := by
    by_contra he
    have hzero : A.law.mass H = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp he]
      simp [FiniteProbabilityWeights.mass]
    linarith only [hH, hzero]
  obtain ⟨a, ha⟩ := hHnonempty
  have hshort : ∀ i, ¬keepLong i →
      (A.sides i : ℝ) ≤ Real.exp (max cost initialShortLog) :=
    allocatedCandidate_initialLong_excluded_bound (fun i => (A.sides i : ℝ)) keep
      (fun i hi => hfrozen a ha ⟨i, hi⟩)
  have hstageLong := source.stageKeep_subset_initialLong keepLong hShortInput hshort
  have hcost : cost ≤ (source.x + source.Cprimitive) ^ source.Cprimitive :=
    (le_max_left _ _).trans hShortInput
  let : Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1)
      geometry.target.weight) := symbolBasisIndexFintype _ _ s (fun _ => Nat.zero_lt_one)
        (geometry.target.model.filtration.adaptedBasis_weight_le_step
          geometry.target.model.basis geometry.target.weight geometry.target.model_layers)
  let : Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1)
      markGeometry.target.weight) := symbolBasisIndexFintype _ _ s (fun _ => Nat.zero_lt_one)
        (markGeometry.target.model.filtration.adaptedBasis_weight_le_step
          markGeometry.target.model.basis markGeometry.target.weight markGeometry.target.model_layers)
  let (r : ℕ) : Fintype (SymbolBasisIndex (fun _ : {i // stageKeep r i} => 1)
      geometry.target.weight) := symbolBasisIndexFintype _ _ s (fun _ => Nat.zero_lt_one)
        (geometry.target.model.filtration.adaptedBasis_weight_le_step
          geometry.target.model.basis geometry.target.weight geometry.target.model_layers)
  let (r : ℕ) : Fintype (SymbolBasisIndex (fun _ : {i // stageKeep r i} => 1)
      markGeometry.target.weight) := symbolBasisIndexFintype _ _ s (fun _ => Nat.zero_lt_one)
        (markGeometry.target.model.filtration.adaptedBasis_weight_le_step
          markGeometry.target.model.basis markGeometry.target.weight markGeometry.target.model_layers)
  have hblocksActual : ((s * (Fintype.card (Fin (finrank ℚ
      (∀ i : Option Pivot, optionLieSpace LM (fun j => (F.native j).L) i))) * m) : ℕ) : ℝ) ≤
      source.x := by
    simpa only [Fintype.card_fin, Nat.cast_mul] using
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right markGeometry.target_dimension (Nat.cast_nonneg m))
        (Nat.cast_nonneg s)).trans hblocks
  exact AllocatedExternalCandidateSpatialNativeFamily.ActualAdaptedPivotQuotientLongFactors.exists_affine_physical_terminal
    F keepLong H sourceCenter hpath hcenter hfrozen
    observable weight scoreThreshold hscore geometry.source.basis geometry.source.weight
    geometry.source.layers js Q hQ hker descended hrecovery geometry.target hproduced
    stageKeep (fun r _ => hstageLong r)
    markGeometry.target.basis markGeometry.target.weight hMark hmarkΦ
    pTerminal source.rankThreshold Hbr hTerminal0
    (geometry.target_dimension.trans hJointTerminal)
    (by simpa only [Fintype.card_fin] using markGeometry.target_dimension.trans hMarkInputTerminal)
    (by simpa only [Fintype.card_fin] using geometry.source_dimension.trans hJointTerminal)
    hSamplerTerminal hProjTerminal
    source.scheduleExponent source.x source.gainLog source.stageLog source.x_nonneg
    source.gain_range source.stage_range source.Cprimitive source.Csource
    source.sourceNative source.pTest source.detectionLoss source.source_nonneg source.source_bound
    source.base_exponent source.phase_exponent source.primitive_pos hFastInput hHbr.1
    source.tags_input source.layers_input hblocksActual hHbr.2 hcost
    markGeometry.entries_height (Nat.one_le_of_lt markGeometry.entries_height_pos)
    (markGeometry.entries_bound.trans (Real.exp_le_exp.mpr
      ((le_add_of_nonneg_right zero_le_one).trans hMarkBudgetTerminal)))
    hNativeInput markGeometry.entries
    (fun i j k => rationalHeightLE_ceil_exp (markGeometry.target_structure i j k))
    source.stageKeep_kept source.stageKeep_frozen source.test_floor
    (source.detectionLoss_le_spatialNativeMass (Pivot := Pivot) hmass hMassInput)
    source.detection source.size_floor source.rank_floor source.sampling_rank hs
    separation hseparation

end
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidatePreparedPhysicalConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit
  weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree realGradedSymbolPolynomial

noncomputable section

theorem exists_primitiveFrontQuotient_actual_physical_terminal
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ Cgeometry C Cbasis K T : ℕ, 2 ≤ Cgeometry ∧ 2 ≤ C ∧ 2 ≤ Cbasis ∧ 2 ≤ K ∧ 2 ≤ T ∧
    ∀ {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M s f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    {p : ℝ} {e : ℕ} (source : A.DegreeSourceProfile s p e)
    (data : P₀.PrimitiveFrontQuotientData FmarkNative source)
    (hp : 0 ≤ p)
    (hφ : ∀ k, ∀ z ∈ D.filtration.layer k, φ z ∈ FmarkNative.filtration.layer k),
      PrimitiveFrontQuotientPhysicalTerminalAt FmarkNative P₀ source data
        Cgeometry C Cbasis K T hp hφ := by
  obtain ⟨Cgeometry, C, Cbasis, K, T, hCgeometry, hC, hCbasis, hK, hT, hterminal⟩ :=
    exists_allocatedExternalCandidateSpatialNativeFamily_actual_physical_terminal s hs
  refine ⟨Cgeometry, C, Cbasis, K, T, hCgeometry, hC, hCbasis, hK, hT, ?_⟩
  intro m G X _ _ _ I E J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells center
    _ A L M _ _ _ _ d D f FmarkNative φ marked _ _ _ _ observable weight
    cost massThreshold scoreThreshold P₀ p e source data hp hφ
  dsimp only [PrimitiveFrontQuotientPhysicalTerminalAt]
  intro _ hFastInput hblocks hShortInput hNativeInput hMassInput separation hseparation _ _ _ _
  let F := data.factorFamily hp
  let pGeometry := source.front.geometryBudget
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 data.quotient.basis
  obtain ⟨desc⟩ := data.exists_descendedFamily
  have bounds := source.front.factorGeometryBudget hp
  refine ⟨desc, ?_⟩
  exact hterminal F bounds.native_vertical bounds.local_vertical bounds.vertical_factor bounds.correlation_factor
      data.retained data.mass_pos (data.factorFamily_correlation_bound hp)
      pGeometry bounds.geometry_two (data.source_geometry_bound hp) (data.mark_geometry_bound hp)
      hφ (data.mark_height_bound hp) (data.native_geometry_bound hp) (data.pivot_card_bound hp)
      (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList
      data.quotient (data.factorFamily_quotient_filtration hp) data.ideal_killed
      (data.quotient_geometry_bound hp) (data.quotient_projection_bound hp)
      source.inner hFastInput hblocks hShortInput hNativeInput source.front.familyParameter
      data.mass hMassInput separation hseparation
      P₀.centerLift (data.factorFamily_path_eq hp) (fun a _ => data.factorFamily_center_eq hp a)
      (fun a _ i => data.frozen_side a i)
      (fun x => (data.front.prep.selected.tests x).observable) weight
      (Real.exp (-AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p)))
      (data.factorFamily_score hp) (fun x => (desc.tests x).observable) desc.recovery

end
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit
  weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree realGradedSymbolPolynomial

noncomputable section

section PrimitiveResult
variable {s : ℕ}
variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {d : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M (s + 1) f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    {p : ℝ} {e : ℕ} (source : A.DegreeSourceProfile (s + 1) p e)
    (data : P₀.PrimitiveFrontQuotientData FmarkNative source)

omit [DecidableEq X] in

theorem PrimitiveFrontQuotientPhysicalTerminalAt.toCanonical
    (Cgeometry C Cbasis K T : ℕ) (hp : 0 ≤ p)
    (hφ : ∀ k, ∀ z ∈ D.filtration.layer k, φ z ∈ FmarkNative.filtration.layer k)
    (hproduce : PrimitiveFrontQuotientPhysicalTerminalAt FmarkNative P₀ source data
      Cgeometry C Cbasis K T hp hφ)
    [Nonempty G] (hcostlt : cost < source.inner.x)
    (hgain : source.inner.x ≤ source.inner.gainLog)
    (hscale : Real.exp source.inner.x ≤ (S.value : ℝ)) :
      let pFactor := source.front.factorBudget
      let pGeometry := source.front.geometryBudget
      let qVertical := 3 * source.front.familyParameter + 1
      let pGeo := (pGeometry + 2) ^ 2
      let jointGeo := (pGeometry + 3) ^ 2
      let adaptedBudget := (jointGeo + 2) ^ Cgeometry
      let bnd := adaptedBudget + (pGeo + 3) ^ 5 + pGeo + jointGeo + pGeometry + pFactor + 2
      let localCost := allocatedFrozenTaggedPairBudget (s + 1) C Cbasis pGeo pFactor
      let jointCost := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let stageInput := jointCost + (jointCost + K) ^ K
      let initialShortLog := max ((pFactor + 2 + C) ^ C + 7 * pFactor + 22)
        ((stageInput + 2) ^ T)
      let qCommon := (stageInput + 2) ^ T + (((stageInput + 2) ^ 2 + 2) ^ 63 + 1) + stageInput + 1
      let pProj := max qCommon 0 + adaptedBudget + 1
      let markInput := nativeOptionFixedSourceQuotientMarkInput pGeometry
      let markBudget := (markInput + 2) ^ nativeOptionFixedSourceMarkExponent.{0, 0}
      let pTerminal := (pProj + 2) ^ 4 + markInput + markBudget + jointGeo +
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2
      allocatedCandidateCommonFastBudget (s + 1) pTerminal ≤ source.inner.x →
      ((s + 1 : ℕ) : ℝ) * (markInput * m) ≤ source.inner.x →
      max cost initialShortLog ≤ source.inner.x →
      (pProj + 2) ^ 3 + qCommon ≤ source.inner.x →
      verticalDecompositionBudget qVertical *
        (Fintype.card (KernelProjectionPresentPivot data.front.prep.selected.code) : ℝ) +
        ((qCommon + 2) ^ 5 + qCommon) + source.front.familyParameter ≤ source.inner.x →
      adaptedBudget ≤ source.inner.x → markBudget ≤ source.inner.x →
      jointGeo ≤ source.inner.x → (pProj + 2) ^ 4 ≤ source.inner.x →
      pGeometry ≤ source.inner.x → source.front.familyParameter ≤ source.inner.x →
      PrimitiveFrontQuotientCanonicalPhysicalTerminalAt FmarkNative P₀ source data
        Cgeometry C Cbasis K T hp hφ := by
  intro pFactor pGeometry qVertical pGeo jointGeo adaptedBudget bnd localCost jointCost
    stageInput initialShortLog qCommon pProj markInput markBudget pTerminal
    hfast hblocks hshort hnative hmass hadapted hmark hjoint hprojection hgeometry hfamily
  let keepLong := fun i => data.front.keep i ∧ Real.exp initialShortLog ≤ (A.sides i : ℝ)
  have hfull := source.inner.input_le_physicalBudget
  have hprimitive : source.inner.x ≤
      (source.inner.x + source.inner.Cprimitive) ^ source.inner.Cprimitive := by
    have hC : (1 : ℝ) ≤ source.inner.Cprimitive := Nat.one_le_cast.mpr source.inner.primitive_pos
    have hbase : 1 ≤ source.inner.x + source.inner.Cprimitive := by
      linarith only [source.inner.x_nonneg, hC]
    calc
      _ ≤ source.inner.x + source.inner.Cprimitive := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (source.inner.x + source.inner.Cprimitive) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hbase source.inner.primitive_pos
  have hlong : initialShortLog ≤ source.inner.x := (le_max_right _ _).trans hshort
  let : Nonempty {i // keepLong i} := data.initialLong_nonempty hcostlt hlong hscale
  change adaptedBudget ≤ source.inner.physicalBudget ∧
    markBudget ≤ source.inner.physicalBudget ∧ jointGeo ≤ source.inner.physicalBudget ∧
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ source.inner.physicalBudget ∧
    (pProj + 2) ^ 4 ≤ source.inner.physicalBudget ∧
    (pProj + 2) ^ 3 + qCommon ≤ source.inner.physicalBudget ∧
    cost ≤ source.inner.physicalBudget ∧
    (∀ i, ¬keepLong i → (A.sides i : ℝ) ≤ Real.exp source.inner.physicalBudget) ∧
    Real.exp (-source.inner.physicalBudget) ≤
      Real.exp (-AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p)) ∧
    Real.exp (-source.inner.physicalBudget) ≤
      Real.exp (-(verticalDecompositionBudget qVertical *
        (Fintype.card (KernelProjectionPresentPivot data.front.prep.selected.code) : ℝ) +
        ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass data.retained ∧
    pGeometry ≤ source.inner.physicalBudget ∧
    source.front.familyParameter ≤ source.inner.physicalBudget ∧ _
  refine ⟨hadapted.trans hfull, hmark.trans hfull, hjoint.trans hfull,
    source.inner.variables_input.trans hfull, hprojection.trans hfull, hnative.trans hfull,
    hcostlt.le.trans hfull, ?_, ?_, ?_, hgeometry.trans hfull, hfamily.trans hfull, ?_⟩
  · intro i hi
    exact (data.initialLong_excluded_bound initialShortLog i hi).trans
      (Real.exp_le_exp.mpr (hshort.trans hfull))
  · exact Real.exp_le_exp.mpr (neg_le_neg
      ((source.front.familyBudget hp).projection.trans (hfamily.trans hfull)))
  · calc
      _ ≤ Real.exp (-(verticalDecompositionBudget qVertical *
          (Fintype.card (KernelProjectionPresentPivot data.front.prep.selected.code) : ℝ) +
          ((qCommon + 2) ^ 5 + qCommon))) * Real.exp (-source.front.familyParameter) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        simpa only [neg_add] using neg_le_neg (hmass.trans hfull)
      _ ≤ _ := mul_le_mul_of_nonneg_left data.mass (Real.exp_nonneg _)
  · apply OrdinaryPolynomialPhase.withCanonicalTopology
    intro _ _ _ _
    exact hproduce hfast hblocks (hshort.trans hprimitive) (hnative.trans hprimitive)
      (hmass.trans hgain) source.inner.separation source.inner.affine_floor

end PrimitiveResult

end
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit
  weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree realGradedSymbolPolynomial

noncomputable section

theorem exists_primitiveFrontQuotient_canonical_physical_terminal
    (s : ℕ) :
    ∃ Cgeometry C Cbasis K T Cfit : ℕ,
      2 ≤ Cgeometry ∧ 2 ≤ C ∧ 2 ≤ Cbasis ∧ 2 ≤ K ∧ 2 ≤ T ∧ 2 ≤ Cfit ∧
    ∀ {m : ℕ} {G X : Type} [Fintype G] [Nonempty G] [Fintype X] [DecidableEq X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {d : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M (s + 1) f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    {p : ℝ} {e : ℕ} (source : A.DegreeSourceProfile (s + 1) p e)
    (data : P₀.PrimitiveFrontQuotientData FmarkNative source)
    (hp : 0 ≤ p)
    (hφ : ∀ k, ∀ z ∈ D.filtration.layer k, φ z ∈ FmarkNative.filtration.layer k)
    (_hcost : cost ≤ p)
    (_hfit : (source.front.familyParameter + 2) ^ Cfit ≤ source.inner.x)
    (_hgain : source.inner.x ≤ source.inner.gainLog)
    (_hscale : Real.exp source.inner.x ≤ (S.value : ℝ)),
      PrimitiveFrontQuotientCanonicalPhysicalTerminalAt FmarkNative P₀ source data
        Cgeometry C Cbasis K T hp hφ := by
  obtain ⟨Cgeometry, C, Cbasis, K, T, hCgeometry, hC, hCbasis, hK, hT, hterminal⟩ :=
    exists_primitiveFrontQuotient_actual_physical_terminal (s + 1) (by omega)
  obtain ⟨Cfit, hCfit, hbudget⟩ := exists_candidateFrontActual_power_budget (s + 1)
    (positiveKernelNativeDescentExponent (s + 1)) Cgeometry C Cbasis K T
    nativeOptionFixedSourceMarkExponent.{0, 0}
  refine ⟨Cgeometry, C, Cbasis, K, T, Cfit, hCgeometry, hC, hCbasis, hK, hT, hCfit, ?_⟩
  intro m G X _ _ _ _ I E J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells center
    _ A L M _ _ _ _ d D f FmarkNative φ marked _ _ _ _ observable weight
    cost massThreshold scoreThreshold P₀ p e source data hp hφ hcost hfit hgain hscale
  have family := source.front.familyBudget hp
  have hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      source.front.familyParameter := by
    simpa only [Fintype.card_subtype_true] using family.keepCard (fun _ => True)
  obtain ⟨hcap, _, _, _, _, hnative, hmcap, hvCap, _⟩ := source.front.familyCap_bounds hp
  have hcapFamily := (candidateFrontFamilyBounds source.front.familyCap source.front.nativeBudget m
    (Fintype.card (LayerSamplerVariables G I n B)) hcap hnative hmcap hvCap).2.1
  have hlayers : (m : ℝ) ≤ source.front.familyParameter := hmcap.trans hcapFamily
  have hscl := hbudget m source.front.familyParameter family.hpFamily hlayers
    cost (Fintype.card (LayerSamplerVariables G I n B))
    (Fintype.card (KernelProjectionPresentPivot data.front.prep.selected.code))
    source.front.familyParameter (hcost.trans family.cost)
    ⟨Nat.cast_nonneg _, hvariables⟩ ⟨Nat.cast_nonneg _, data.pivot_card⟩ le_rfl
  obtain ⟨_, hfast, hshort, hnativeInput, _, _, hmass, hblocks, hfamily,
    hgeometry, hadapted, hmark, hjoint, hprojection, _⟩ := hscl
  have hcostlt : cost < source.inner.x := by
    have hbase : 1 ≤ source.front.familyParameter + 2 :=
      (by norm_num : (1 : ℝ) ≤ 2).trans (le_add_of_nonneg_left family.hpFamily)
    have hpower : source.front.familyParameter + 2 ≤
        (source.front.familyParameter + 2) ^ Cfit := by
      calc
        _ = (source.front.familyParameter + 2) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ hbase (by omega)
    exact (lt_of_le_of_lt (hcost.trans family.cost)
      (lt_add_of_pos_right _ (by norm_num : (0 : ℝ) < 2))).trans_le
      (hpower.trans hfit)
  exact PrimitiveFrontQuotientPhysicalTerminalAt.toCanonical FmarkNative P₀ source data
    Cgeometry C Cbasis K T hp hφ (hterminal FmarkNative P₀ source data hp hφ)
    hcostlt hgain hscale
    (hfast.trans hfit) (hblocks.trans hfit) (hshort.trans hfit) (hnativeInput.trans hfit)
    (hmass.trans hfit) (hadapted.trans hfit) (hmark.trans hfit) (hjoint.trans hfit)
    (hprojection.trans hfit) (hgeometry.trans hfit) (hfamily.trans hfit)

end
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedNestedSourceDegreeGlobalization
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

theorem exists_degreeGlobalizationAt_source_successor (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {m : ℕ} {G X : Type} [Fintype G] [Nonempty G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)
    (weight : (X → ℤ) → ℂ) (p : ℝ) (e : ℕ)
    (source : A.DegreeSourceProfile (s + 1) p e),
    0 ≤ p →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
    (source.front.familyParameter + 2) ^ C ≤ source.inner.x →
    source.inner.x ≤ source.inner.gainLog →
    Real.exp source.inner.x ≤ (S.value : ℝ) →
    ∀ outputCost : ℝ,
    A.DegreeGlobalizationAt (E := E) weight s
      (refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2)
      source.inner.recursiveParameter outputCost →
    source.inner.recursiveParameter ≤ outputCost →
    A.DegreeGlobalizationAt (E := E) weight (s + 1) e p (3 * outputCost + 2) := by
  classical
  obtain ⟨Cgeometry, Cpair, Cbasis, K, T, C, _, _, _, _, _, hC, hterminal⟩ :=
    exists_primitiveFrontQuotient_canonical_physical_terminal s
  refine ⟨C, hC, ?_⟩
  intro m G X _ _ _ I E J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells
    center _ A weight p e source hp hvariables hfit hgain hscale outputCost lowerIH houtput
    L M _ _ _ _ _ _ _ _ d f D Fmark φ hφ hsurj hD hFmark hmark
    marked observable ℓ hℓ hLip hpositive hnet hweight P
  obtain ⟨data⟩ := P.exists_primitiveFrontQuotientData Fmark source (by omega) hp hp le_rfl
    hvariables hD hFmark (fun i j => hmark j i) ℓ hℓ hLip hpositive hweight
    le_rfl le_rfl hnet
  have produced := hterminal Fmark P source data hp hφ le_rfl hfit hgain hscale
  exact AllocatedExternalCandidateProblem.PrimitiveFrontQuotientData.conclusion_of_canonicalPhysicalTerminal
    Fmark P source data hp hφ hsurj hweight hnet outputCost lowerIH houtput produced

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal
attribute [local irreducible] AllocatedExternalCandidateSampler.DegreeGlobalizationAt

theorem exists_degreeGlobalizationAt_of_nested_source_profiles (total : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {m : ℕ} {G X : Type} [Fintype G] [Nonempty G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)
    (weight : (X → ℤ) → ℂ) (initial exponent innerDepth : ℕ) (x : ℝ)
    (source : ∀ j : Fin total,
      A.DegreeSourceProfile (total - (j.val + 1) + 1)
        (candidateNestedForwardSeed exponent
          AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (2 * j.val) x)
        (candidateNestedDegreeNetExponent total initial j.val)),
    2 ≤ exponent → 0 ≤ x →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x →
    (∀ j, (source j).inner.x = candidateNestedForwardSeed exponent
      AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (2 * j.val + 1) x) →
    (∀ j, ((source j).front.familyParameter + 2) ^ C ≤ (source j).inner.x) →
    (∀ j, (source j).inner.x ≤ (source j).inner.gainLog) →
    Real.exp (candidateNestedForwardSeed exponent
      AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (2 * total) x) ≤
        (S.value : ℝ) →
    (∀ j, (source j).inner.recursiveParameter ≤ candidateNestedForwardSeed exponent
      AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (2 * (j.val + 1)) x) →
    A.DegreeGlobalizationAt (E := E) weight total initial x
      (candidateDegreeReturnBudget total (candidateNestedForwardSeed exponent
        AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (2 * total) x)) := by
  classical
  let Cstep : ℕ → ℕ := fun s => Classical.choose (exists_degreeGlobalizationAt_source_successor s)
  let C := 2 + ∑ s ∈ Finset.range total, Cstep s
  have hC : 2 ≤ C := by dsimp [C]; omega
  have hstepC {s : ℕ} (hs : s < total) : Cstep s ≤ C := by
    have hsum := Finset.single_le_sum (f := Cstep) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr hs)
    dsimp only [C]
    omega
  refine ⟨C, hC, ?_⟩
  intro m G X _ _ _ I E J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells
    center _ A weight initial exponent innerDepth x source hA hx hvariables
    hinner hfront hgain hscale hrecursive
  apply A.degreeGlobalizationAt_nested (E := E) weight total initial exponent innerDepth
    AllocatedExternalCandidateSampler.degreeSourceCountConstants hA hx
  intro j hj q hq lower
  let index : Fin total := ⟨j, hj⟩
  let profile := source index
  have hp : 0 ≤ candidateNestedForwardSeed exponent
      AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (2 * j) x :=
    candidateNestedForwardSeed_nonneg exponent _ innerDepth (2 * j) hx
  have hvars := hvariables.trans
    (le_candidateNestedForwardSeed exponent
      AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (2 * j) hA hx)
  have hsmall : Cstep (total - (j + 1)) ≤ C := hstepC (by omega)
  have hf0 := (profile.front.familyBudget hp).hpFamily
  have hfit : (profile.front.familyParameter + 2) ^ Cstep (total - (j + 1)) ≤
      profile.inner.x :=
    (pow_le_pow_right₀ (by linarith only [hf0]) hsmall).trans (hfront index)
  have hsize : Real.exp profile.inner.x ≤ (S.value : ℝ) := by
    apply le_trans _ hscale
    apply Real.exp_le_exp.mpr
    rw [show profile.inner.x = candidateNestedForwardSeed exponent
      AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (2 * j + 1) x from hinner index]
    exact candidateNestedForwardSeed_monotone exponent _ innerDepth hA hx (by omega)
  have hrec := hrecursive index
  have recur := AllocatedExternalCandidateSampler.DegreeGlobalizationAt.mono_input A lower
    profile.inner.recursiveParameter_nonneg hrec
  have current := (Classical.choose_spec
    (exists_degreeGlobalizationAt_source_successor (total - (j + 1)))).2
    (E := E) A weight _ _ profile hp hvars hfit (hgain index) hsize q recur (hrec.trans hq)
  have hd : total - j = total - (j + 1) + 1 := by omega
  simpa only [hd] using current

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativePositiveNativeRuleCanonical
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open AllocatedExternalCandidateSampler
open scoped BigOperators Classical TensorProduct NNReal
attribute [local irreducible] AllocatedExternalCandidateSampler.DegreeGlobalizationAt

theorem exists_degreeGlobalizationAt_of_nested_source_data
    (total resourceLayers Cprimitive : ℕ) (Pdetect : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {m : ℕ} {G X : Type} [Fintype G] [Nonempty G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)
    (weight : (X → ℤ) → ℂ) (initial exponent outerDepth innerDepth cutoff Cdirect : ℕ)
    (x pnum Qstride gainLog stageLog Plate : ℝ)
    (hExponent : C ≤ exponent) (houter : 2 * total ≤ outerDepth)
    (hdepth : total + 1 ≤ innerDepth) (hcutoff : total ≤ cutoff)
    (hresource : total ≤ resourceLayers)
    (hx : 0 ≤ x) (hnum : pnum ∈ Set.Icc 0 x) (hstride : Qstride ∈ Set.Icc 0 x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hlayers : (m : ℝ) ≤ x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hX : (Fintype.card X : ℝ) ≤ x) (hG : (Fintype.card G : ℝ) ≤ x)
    (source : ∀ j : Fin total,
      A.DegreeSourceProfile (total - (j.val + 1) + 1)
        (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth (2 * j.val) x)
        (candidateNestedDegreeNetBound total initial)),
    (∀ j, (source j).inner.x = candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth (2 * j.val + 1) x) →
    (∀ j, (source j).inner.gainLog = candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth (2 * j.val + 1) x) →
    (∀ j, (source j).front.u = preparedFiniteForwardModelPrecision exponent degreeSourceCountConstants
      0 (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth (2 * j.val) x)
      gainLog stageLog) →
    (∀ j, (source j).front.pModel = preparedFiniteForwardWork exponent degreeSourceCountConstants
      0 (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth (2 * j.val) x)) →
    (∀ j, (source j).front.nativeBudget = preparedFiniteNestedSourceNative resourceLayers G
      (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X) Pdetect
      exponent Cdirect degreeSourceCountConstants x pnum Qstride gainLog stageLog Plate
      ((⟨2 * j.val, by omega⟩ : Fin (outerDepth + 1)), (0 : Fin (innerDepth + 1)),
        (⟨total - (j.val + 1) + 1, by omega⟩ : Fin (cutoff + 1)), false)) →
    (∀ j, (source j).inner.Cprimitive = Cprimitive) →
    (∀ j, (source j).inner.scheduleExponent = exponent) →
    Real.exp (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth (2 * total) x) ≤
      (S.value : ℝ) →
    A.DegreeGlobalizationAt (E := E) weight total initial x
      (candidateDegreeReturnBudget total
        (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth (2 * total) x)) := by
  obtain ⟨Cstep, hCstep, hglobal⟩ := exists_degreeGlobalizationAt_of_nested_source_profiles total
  let Cfront := preparedFiniteNestedFrontFitExponent resourceLayers Pdetect Cstep
  let Crec := candidateSourceRecursiveUniformExponent total Cprimitive
  let C := 2 + Cfront + Crec
  have hC : 2 ≤ C := by dsimp only [C]; omega
  refine ⟨C, hC, ?_⟩
  intro m G X _ _ _ I E J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells
    center _ A weight initial exponent outerDepth innerDepth cutoff Cdirect
    x pnum Qstride gainLog stageLog Plate hExponent houter hdepth hcutoff hresource
    hx hnum hstride hg hs hlayers hvariables hX hG source hinner hgain hu hmodel hnative
    hprimitive hschedule hscale
  have hA : 2 ≤ exponent := hC.trans hExponent
  have hfrontExp : Cfront ≤ exponent := by dsimp only [C] at hExponent; omega
  have hrecExp : Crec ≤ exponent := by dsimp only [C] at hExponent; omega
  let reduced := fun j : Fin total => (source j).mono_netExponent
    (candidateNestedForwardSeed_nonneg exponent degreeSourceCountConstants innerDepth (2 * j.val) hx)
    (candidateNestedDegreeNetExponent_le_bound total initial (Nat.le_of_lt j.isLt))
  apply hglobal (E := E) A weight initial exponent innerDepth x reduced hA hx hvariables
  · exact hinner
  · intro j
    have hd : total - (j.val + 1) + 1 ≤ total := by omega
    have hfit := (source j).front.familyParameter_pow_le_next_seed
      resourceLayers Pdetect Cstep exponent Cdirect degreeSourceCountConstants
      outerDepth innerDepth cutoff ⟨2 * j.val, by omega⟩
      x pnum Qstride gainLog stageLog Plate hfrontExp (by omega) hx
      (hd.trans hcutoff) (hd.trans hresource) hnum hstride hg hs hlayers hvariables hX hG
      ⟨candidateNestedForwardSeed_nonneg exponent degreeSourceCountConstants innerDepth (2 * j.val) hx,
        le_rfl⟩ (hu j) (hmodel j) (hnative j)
    change ((source j).front.familyParameter + 2) ^ Cstep ≤ (source j).inner.x
    rw [hinner j]
    exact hfit
  · intro j
    change (source j).inner.x ≤ (source j).inner.gainLog
    rw [hinner j, hgain j]
  · exact hscale
  · intro j
    exact (source j).inner.recursiveParameter_le_next_degree_seed_of_uniform
      Cprimitive exponent innerDepth total j.val (by omega) hrecExp hdepth hx
      (hprimitive j) (hschedule j) (hinner j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open AllocatedExternalCandidateSampler
open scoped BigOperators Classical TensorProduct NNReal
attribute [local irreducible] AllocatedExternalCandidateSampler.DegreeGlobalizationAt

theorem exists_degreeGlobalizationAt_of_complete_nested_source_data
    (total resourceLayers Cprimitive : ℕ) (Pdetect : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {m : ℕ} {G X : Type} [Fintype G] [Nonempty G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)
    (weight : (X → ℤ) → ℂ) (initial exponent outerDepth innerDepth cutoff Cdirect Csource : ℕ)
    (x pnum Qstride gainLog stageLog Plate : ℝ)
    (_hExponent : C ≤ exponent) (_houter : 2 * total + 1 ≤ outerDepth)
    (_hdepth : total + 1 ≤ innerDepth) (_hcutoff : total ≤ cutoff)
    (_hresource : total ≤ resourceLayers)
    (_hx : 0 ≤ x) (_hnum : pnum ∈ Set.Icc 0 x) (_hstride : Qstride ∈ Set.Icc 0 x)
    (_hg : gainLog ∈ Set.Icc 0 x) (_hs : stageLog ∈ Set.Icc 0 x)
    (_hlayers : (m : ℝ) ≤ x)
    (_hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (_hX : (Fintype.card X : ℝ) ≤ x) (_hG : (Fintype.card G : ℝ) ≤ x),
    (∀ (outerFront outerInner : Fin (outerDepth + 1)) (d : ℕ),
      ∀ (hd : d ≤ cutoff), d ≤ innerDepth → ∀ pInput : ℝ,
      pInput ∈ Set.Icc 0
        (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth outerFront.val x) →
      pInput ≤ candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth outerInner.val x →
      ∃ profile : A.DegreeSourceProfile d pInput (candidateNestedDegreeNetBound total initial),
        profile.inner.x = candidateNestedForwardSeed exponent degreeSourceCountConstants
          innerDepth outerInner.val x ∧
        profile.inner.gainLog = candidateNestedForwardSeed exponent degreeSourceCountConstants
          innerDepth outerInner.val x ∧
        profile.front.u = preparedFiniteForwardModelPrecision exponent degreeSourceCountConstants 0
          (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth outerFront.val x)
          gainLog stageLog ∧
        profile.front.pModel = preparedFiniteForwardWork exponent degreeSourceCountConstants 0
          (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth outerFront.val x) ∧
        profile.front.nativeBudget = preparedFiniteNestedSourceNative resourceLayers G
          (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X) Pdetect exponent Cdirect
          degreeSourceCountConstants x pnum Qstride gainLog stageLog Plate
          (outerFront, (0 : Fin (innerDepth + 1)), ⟨d, Nat.lt_succ_of_le hd⟩, false) ∧
        profile.inner.Cprimitive = Cprimitive ∧
        profile.inner.scheduleExponent = exponent ∧ profile.inner.Csource = Csource) →
    Real.exp (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth outerDepth x) ≤
      (S.value : ℝ) →
    A.DegreeGlobalizationAt (E := E) weight total initial x
      (preparedFiniteForwardParameter exponent degreeSourceCountConstants innerDepth
        (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth outerDepth x) + 1) := by
  classical
  obtain ⟨Cdata, hCdata, hglobal⟩ :=
    exists_degreeGlobalizationAt_of_nested_source_data total resourceLayers Cprimitive Pdetect
  let C := 2 + Cdata + preparedNestedEndpointReturnExponent total
  have hC : 2 ≤ C := by dsimp only [C]; omega
  refine ⟨C, hC, ?_⟩
  intro m G X _ _ _ I E J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells
    center _ A weight initial exponent outerDepth innerDepth cutoff Cdirect Csource
    x pnum Qstride gainLog stageLog Plate hExponent houter hdepth hcutoff hresource
    hx hnum hstride hg hs hlayers hvariables hX hG hprofiles hscale
  have hA : 2 ≤ exponent := hC.trans hExponent
  have hdata : Cdata ≤ exponent := by dsimp only [C] at hExponent; omega
  have hreturn : preparedNestedEndpointReturnExponent total ≤ exponent := by
    dsimp only [C] at hExponent
    omega
  let front : Fin total → Fin (outerDepth + 1) := fun j => ⟨2 * j.val, by omega⟩
  let inner : Fin total → Fin (outerDepth + 1) := fun j => ⟨2 * j.val + 1, by omega⟩
  have hchosen := fun j : Fin total => hprofiles (front j) (inner j)
    (total - (j.val + 1) + 1) (by omega) (by omega)
    (candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth (2 * j.val) x)
    ⟨candidateNestedForwardSeed_nonneg exponent degreeSourceCountConstants innerDepth (2 * j.val) hx,
      le_rfl⟩
    (candidateNestedForwardSeed_monotone exponent degreeSourceCountConstants innerDepth hA hx
      (show 2 * j.val ≤ 2 * j.val + 1 by omega))
  choose source hproperties using hchosen
  have hterminalScale : Real.exp (candidateNestedForwardSeed exponent degreeSourceCountConstants
      innerDepth (2 * total) x) ≤ (S.value : ℝ) :=
    (Real.exp_le_exp.mpr (candidateNestedForwardSeed_monotone exponent degreeSourceCountConstants
      innerDepth hA hx (by omega : 2 * total ≤ outerDepth))).trans hscale
  have rule := hglobal (E := E) A weight initial exponent outerDepth innerDepth cutoff Cdirect
    x pnum Qstride gainLog stageLog Plate hdata (by omega) hdepth hcutoff hresource
    hx hnum hstride hg hs hlayers hvariables hX hG source
    (fun j => (hproperties j).1) (fun j => (hproperties j).2.1)
    (fun j => (hproperties j).2.2.1) (fun j => (hproperties j).2.2.2.1)
    (fun j => (hproperties j).2.2.2.2.1) (fun j => (hproperties j).2.2.2.2.2.1)
    (fun j => (hproperties j).2.2.2.2.2.2.1) hterminalScale
  have hout := candidateDegreeReturnBudget_le_endpointParameter total exponent degreeSourceCountConstants
    innerDepth outerDepth innerDepth hreturn (by omega) houter hx
  exact DegreeGlobalizationAt.mono_output A rule (by linarith only [hout])

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedRelativeNativeSourceExponent (s : ℕ) : ℕ :=
  (exists_degreeGlobalizationAt_of_complete_nested_source_data s s
    (preparedCommonRadiusPrimitiveExponent s) (preparedFiniteForwardDetectorPolynomial s)).choose

noncomputable def preparedRelativePositiveExtra (s : ℕ) : ℕ :=
  4 + preparedRelativeNativeSourceExponent s + preparedRelativeEndpointCapExponent s +
    preparedNestedEndpointDimensionExponent s

noncomputable def preparedRelativePositiveSourceExponent (s : ℕ) : ℕ :=
  preparedFiniteNestedSourceExponent s s (candidateNestedDegreeNetBound s 0)
    (preparedCommonRadiusPrimitiveExponent s) 2 (preparedRelativePositiveExtra s)

noncomputable def preparedRelativePositiveEarlyExponent (s : ℕ) : ℕ :=
  (exists_preparedFiniteNestedCanonicalEarlyPrimitive_budget s (2 * s + 2) (s + 1) s
    (candidateNestedDegreeNetBound s 0) (preparedCommonRadiusPrimitiveExponent s) 2
    (preparedRelativePositiveExtra s) AllocatedExternalCandidateSampler.degreeSourceCountConstants).choose

noncomputable def preparedRelativePositiveInputExponent (s : ℕ) : ℕ :=
  (exists_preparedRelativeEndpointInputScale_power_budget s
    (preparedRelativePositiveEarlyExponent s)).choose

end Erdos3.VectorPolynomial

end

end OAI
end


