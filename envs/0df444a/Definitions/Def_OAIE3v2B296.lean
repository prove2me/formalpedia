-- Prove2me | Definitions.Def_OAIE3v2B296
-- name    : OAIE3v2B296
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T09:16:53.806307+00:00
-- url     : https://prove2.me/theorems/9d34cc4b-386f-44a3-9a8e-647e512deada
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 310 of 311
-- statement:
--   Definitions bundle 310 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B310`, `OAIE3v2B293`, `OAIE3v2B294` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidatePreparedPhysicalConclusion.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeOrdinaryTerminal.lean`, `Polynomial/PreparedFiniteNestedDegreeSourceProfileScalars.lean`, `Polynomial/ScalarNestedSourceDegreeGlobalization.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B310
import Definitions.Def_OAIE3v2B293
import Definitions.Def_OAIE3v2B294

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

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
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

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {Deck : Fin m → Type} {Pivot : Type} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

    (keepLong : LayerSamplerVariables G I n B → Prop)
    (H : Finset A.Path)
    (sourceCenter : ∀ j, U j)
    (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
    (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
    (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    (scoreThreshold : ℝ)
    (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)

variable {α : Type} [Fintype α]
    (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i))
    (ω : α → ℕ)
    (hF : ∀ k, (optionProduct D (fun j => (F.native j).model)).filtration.layer k =
      Submodule.span ℚ (e '' {i | k ≤ ω i}))
    (js : List Pivot)
    {dQ : ℕ}
    (Q : RationalFilteredNilmanifold (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) s dQ)
    (hQ : Q.filtration = D.filtration.pivotQuotientFiltration φ F.η js)
    (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal φ F.η js, φ x = 0)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) g)) =
        observable x (QuotientGroup.mk g))
    (adapted : (optionProduct Q (fun j => (F.native j).model)).AdaptedModelData)

local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

theorem ActualAdaptedPivotQuotientLongFactors.exists_affine_physical_terminal
    {qVertical qCommon pProj : ℝ}
    (hproduced : F.ActualAdaptedPivotQuotientLongFactors keepLong H sourceCenter hpath hcenter hfrozen
      observable weight scoreThreshold hscore e ω hF js Q hQ hker descended hrecovery adapted
      qVertical qCommon pProj)
    (stageKeep : ℕ → LayerSamplerVariables G I n B → Prop)
    (hstageLong : ∀ r < s, ∀ i, stageKeep r i → keepLong i)
    {κ : Type} [Fintype κ]
    (bMark : Basis κ ℚ (∀ i : Option Pivot, optionLieSpace LM (fun j => (F.native j).L) i))
    (ν : κ → ℕ)
    (hMark : ∀ k, (NilpotentLieFiltration.pi (optionFiltrations Fmark (fun j => ((fun j => (F.native j).model) j).filtration))).layer k = Submodule.span ℚ (bMark '' {i | k ≤ ν i}))
    (hmarkΦ : ∀ k, ∀ z ∈ (adapted.model.filtration).layer k, (optionMarkedLieMap (L := fun j => (F.native j).L) (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker)) z ∈ (NilpotentLieFiltration.pi (optionFiltrations Fmark (fun j => ((fun j => (F.native j).model) j).filtration))).layer k)
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) adapted.weight)]
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ν)]
    [∀ r, Fintype (SymbolBasisIndex
      (fun _ : {i : LayerSamplerVariables G I n B // stageKeep r i} => 1) adapted.weight)]
    [∀ r, Fintype (SymbolBasisIndex
      (fun _ : {i : LayerSamplerVariables G I n B // stageKeep r i} => 1) ν)]
    [∀ r, TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (pGeometry Rrank : ℝ) (Hbr : ℕ)
    (hpGeometry : 0 ≤ pGeometry)
    (hSourceGeometry : (finrank ℚ (∀ i : Option Pivot,
      optionLieSpace (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (fun j => (F.native j).L) i) : ℝ) ≤ pGeometry)
    (hMarkedGeometry : (Fintype.card κ : ℝ) ≤ pGeometry)
    (hGeneratorGeometry : (Fintype.card α : ℝ) ≤ pGeometry)
    (hSamplerGeometry : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pGeometry)
    (hQuotientGeometry : (pProj + 2) ^ 4 ≤ pGeometry)
    (scheduleExponent : ℕ) (x gainLog stageLog : ℝ)
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (Cprimitive Csource : ℕ) (sourceNative pTest detectionLoss : ℕ → ℝ)
    (hSourceNonneg : ∀ r < s, 0 ≤ sourceNative r)
    (hSourceBound : ∀ r < s, sourceNative r ≤
      (preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
        preparedFiniteForwardWork scheduleExponent countConstants r x + Csource) ^ Csource)
    (hBaseExponent : allocatedCandidateStageBaseExponent s m Cprimitive ≤ scheduleExponent)
    (hphaseExponent : ∀ r < s,
      allocatedCandidateCompositePhaseConstant s m 1
        (allocatedCandidatePromotedMajorConstant Csource) r ≤ scheduleExponent)
    (hCprimitive : 1 ≤ Cprimitive)
    (hGeometryBase : allocatedCandidateCommonFastBudget s pGeometry ≤ x)
    (hHbr : 1 ≤ Hbr)
    (hTagsBase : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x)
    (hmEarly : (m : ℝ) ≤ x)
    (hblocksEarly : ((s * (Fintype.card κ * m) : ℕ) : ℝ) ≤ x)
    (hHbrBase : (Hbr : ℝ) ≤ Real.exp x)
    (hcost : cost ≤ (x + Cprimitive) ^ Cprimitive)
    (HMap : ℕ) (hHMap : 1 ≤ HMap)
    (hHMapGeometry : (HMap : ℝ) ≤ Real.exp pGeometry)
    (hNativeBase : (pProj + 2) ^ 3 + qCommon ≤ (x + Cprimitive) ^ Cprimitive)
    (hentries : ∀ i j, RationalHeightLE (bMark.repr ((optionMarkedLieMap (L := fun j => (F.native j).L) (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker)) (adapted.model.basis j)) i) HMap)
    (hbracket : ∀ i j z, RationalHeightLE (bMark.repr ⁅bMark i, bMark j⁆ z) Hbr)
    (hkept : ∀ r, ∀ i, stageKeep r i → Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) ≤ (A.sides i : ℝ))
    (hfrozenStage : ∀ r, ∀ i, ¬stageKeep r i → (A.sides i : ℝ) ≤ Real.exp
      (allocatedCandidateStageSlice s m Cprimitive
        (preparedFiniteForwardParameter scheduleExponent countConstants r x)))
    (hTest : ∀ r < s, OrdinaryPolynomialPhase.budget r ≤ pTest r)
    (hDetectionLoss : ∀ r < s, detectionLoss r ≤ (9 / 10 : ℝ) *
      (Real.exp (-(verticalDecompositionBudget qVertical * Fintype.card Pivot +
        ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass H))
    (hdirect : ∀ r < s, A.NativeDetection r (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x))
      (pTest r) (sourceNative r) (detectionLoss r))
    (hN : ∀ i, Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ (N i : ℝ))
    (hRrank : Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hs : 0 < s) (separation : ℝ)
    (hseparation : certifiedAffineLongSideBound
      (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ separation) :
    F.ActualAdaptedPivotQuotientLongPhysicalTerminal keepLong H sourceCenter hpath hcenter hfrozen
      observable weight scoreThreshold hscore e ω hF js Q hQ hker descended hrecovery adapted
      bMark ν hMark hmarkΦ scheduleExponent Cprimitive x separation qVertical qCommon pProj := by
  classical
  obtain ⟨retained, hsub, hmass, hpos, theta, W, v, den, hv, hW, hvH, hzero,
    hden, hdenBound, denQ, hdenQ, hdenQBound, hdiv, hvQ, hWQ, hvQH, hfactorQ,
    htop, hgradedTop⟩ := hproduced
  let source := F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
    scoreThreshold hscore retained hsub hmass
  let target := (source.withKeep keep (fun _ => rfl)).adaptedOptionQuotient
    (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit) (D.filtration.pivotAnnihilatorIdeal φ F.η js)
    (by rw [D.filtration.terminal]; exact bot_le) Q hQ hker descended hrecovery adapted
  let V := W.map (((optionProduct D (fun j => (F.native j).model)).filtration).associatedGradedMap (adapted.model.filtration) (optionMarkedLieMap (L := fun j => (F.native j).L) (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js))) (D.optionQuotientMap_mem_layer (D.filtration.pivotAnnihilatorIdeal φ F.η js) (by rw [D.filtration.terminal]; exact bot_le) Q hQ (fun j => (F.native j).model)))
  let vQ := ((optionProduct D (fun j => (F.native j).model)).filtration).gradedImageSpanningFamily (adapted.model.filtration) (optionMarkedLieMap (L := fun j => (F.native j).L) (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js))) (D.optionQuotientMap_mem_layer (D.filtration.pivotAnnihilatorIdeal φ F.η js) (by rw [D.filtration.terminal]; exact bot_le) Q hQ (fun j => (F.native j).model)) v
  have hpGeometryX : pGeometry ≤ x :=
    (allocatedCandidateCommonFastBudget_bounds s hpGeometry).2.2.trans hGeometryBase
  have hprimitive : x ≤ (x + Cprimitive) ^ Cprimitive := by
    have hC : (1 : ℝ) ≤ Cprimitive := by exact_mod_cast hCprimitive
    have hbase : 1 ≤ x + Cprimitive := by linarith
    exact (le_add_of_nonneg_right (Nat.cast_nonneg Cprimitive)).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hbase hCprimitive)
  have hdenQBase : (denQ : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive) :=
    hdenQBound.trans (Real.exp_le_exp.mpr
      ((hQuotientGeometry.trans hpGeometryX).trans hprimitive))
  have hOriginal (z : target.productive) :
      (adapted.model.filtration).HasCommonRefilteredOrbitFactors adapted.model.basis adapted.weight adapted.model_layers
        (fun i : {i : LayerSamplerVariables G I n B // keepLong i} => (A.sides i.val : ℝ))
        ((pProj + 2) ^ 3 + qCommon) denQ V
        ((adapted.model.filtration).weightedAdaptedRealChartHom
          (fun _ : (target.chart z).Variables => 1)
          (fun _ : {i : LayerSamplerVariables G I n B // keepLong i} => 1)
          ((target.chart z).axisPolynomial keepLong (fun _ => 0))
          ((target.chart z).axisPolynomial_support keepLong (fun _ => 0))
          ((adapted.model.filtration).realification.polynomialOrbitCoordinates
            (fun _ => 1) (target.candidate z).orbit)) :=
    hfactorQ z
  have hselectedMass : 0 < Real.exp
      (-(verticalDecompositionBudget qVertical * Fintype.card Pivot +
        ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass H := by
    apply mul_pos (Real.exp_pos _)
    apply hpos.trans_le
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => A.law.nonneg a)
  have ht := target.exists_zero_restricted_native_common_affine_physical_terminal stageKeep
    adapted.model.basis adapted.weight adapted.model_layers bMark ν hMark hmarkΦ V
    vQ hvQ hWQ pGeometry Rrank Hbr hpGeometry
    (by simpa only [Fintype.card_fin] using hSourceGeometry) hMarkedGeometry
    (by simpa only [Fintype.card_fin] using hGeneratorGeometry) hSamplerGeometry
    (fun a i => (hvQH a i).trans hQuotientGeometry)
    scheduleExponent x gainLog stageLog hx hgain hstage Cprimitive Csource
    sourceNative pTest detectionLoss hSourceNonneg hSourceBound hBaseExponent hphaseExponent
    hCprimitive hGeometryBase hHbr hTagsBase hmEarly hblocksEarly hHbrBase hcost
    HMap denQ ((pProj + 2) ^ 3 + qCommon) hHMap hdenQ hHMapGeometry hdenQBase
    hNativeBase hentries hbracket keepLong hstageLong hOriginal F.hτ1 F.hξ F.hσ1 F.Cgeo F.hCgeo F.hchart F.hsmall
    F.hpoly hkept hfrozenStage hTest hDetectionLoss hdirect hN hRrank hrank
    hs hselectedMass separation hseparation
  obtain ⟨qDim, hdim, eQ, lift, hfast, hsection, hterminal⟩ := ht
  refine ⟨retained, hsub, hmass, hpos, theta, W, v, den, hv, hW, hvH, hzero,
    hden, hdenBound, denQ, hdenQ, hdenQBound, hdiv, hvQ, hWQ, hvQH, hfactorQ,
    htop, hgradedTop, ?_⟩
  have hηBase : (Fintype.card (Fin qDim) : ℝ) ≤ x := by
    simpa only [Fintype.card_fin] using
      (Nat.cast_le.mpr hdim).trans (hMarkedGeometry.trans hpGeometryX)
  have hblocks : ((s * (Fintype.card (Fin qDim) * m) : ℕ) : ℝ) ≤ x := by
    simpa only [Fintype.card_fin] using
      (Nat.cast_le.mpr (Nat.mul_le_mul_left s (Nat.mul_le_mul_right m hdim))).trans hblocksEarly
  have hXEarly : (Fintype.card X : ℝ) ≤ x := by
    have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
      simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
    exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hsum
  have hJEarly : (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
    have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
      simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
    exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans hsum
  have hNEarly : ∀ i, 1 ≤ N i := by
    intro i
    have hpositive : 0 < N i := by exact_mod_cast ((Real.exp_pos _).trans_le (hN i))
    exact Nat.succ_le_iff.mpr hpositive
  refine ⟨qDim, hdim, eQ, lift, hfast, hsection, hx, hXEarly, hmEarly, hJEarly,
    hηBase, hblocks, hNEarly, ?_⟩
  dsimp only at hterminal ⊢
  exact hterminal

end AllocatedExternalCandidateSpatialNativeFamily

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

def PrimitiveFrontQuotientPhysicalTerminalAt (Cgeometry C Cbasis K T : ℕ)
    (hp : 0 ≤ p)
    (hφ : ∀ k, ∀ z ∈ D.filtration.layer k, φ z ∈ FmarkNative.filtration.layer k) : Prop :=
      let F := data.factorFamily hp
      let pFactor := source.front.factorBudget
      let pGeometry := source.front.geometryBudget
      let qVertical := 3 * source.front.familyParameter + 1
      let pGeo := (pGeometry + 2) ^ 2
      let jointGeo := (pGeometry + 3) ^ 2
      let adaptedBudget := (jointGeo + 2) ^ Cgeometry
      let bnd := adaptedBudget + (pGeo + 3) ^ 5 + pGeo + jointGeo + pGeometry + pFactor + 2
      let localCost := allocatedFrozenTaggedPairBudget s C Cbasis pGeo pFactor
      let jointCost := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let stageInput := jointCost + (jointCost + K) ^ K
      let initialShortLog := max ((pFactor + 2 + C) ^ C + 7 * pFactor + 22)
        ((stageInput + 2) ^ T)
      let keepLong := fun i => data.front.keep i ∧ Real.exp initialShortLog ≤ (A.sides i : ℝ)
    ∀ [Nonempty {i // keepLong i}],
      let qCommon := (stageInput + 2) ^ T + (((stageInput + 2) ^ 2 + 2) ^ 63 + 1) + stageInput + 1
      let pProj := max qCommon 0 + adaptedBudget + 1
      let markInput := nativeOptionFixedSourceQuotientMarkInput pGeometry
      let markBudget := (markInput + 2) ^ nativeOptionFixedSourceMarkExponent.{0, 0}
      let pTerminal := (pProj + 2) ^ 4 + markInput + markBudget + jointGeo +
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2
    ∀ (hFastInput : allocatedCandidateCommonFastBudget s pTerminal ≤ source.inner.x)
      (hblocks : (s : ℝ) * (markInput * m) ≤ source.inner.x)
      (hShortInput : max cost initialShortLog ≤
        (source.inner.x + source.inner.Cprimitive) ^ source.inner.Cprimitive)
      (hNativeInput : (pProj + 2) ^ 3 + qCommon ≤
        (source.inner.x + source.inner.Cprimitive) ^ source.inner.Cprimitive)
      (hMassInput : verticalDecompositionBudget qVertical *
        (Fintype.card (KernelProjectionPresentPivot data.front.prep.selected.code) : ℝ) +
        ((qCommon + 2) ^ 5 + qCommon) + source.front.familyParameter ≤ source.inner.gainLog)
      (separation : ℝ)
      (hseparation : certifiedAffineLongSideBound
        (preparedFiniteForwardCumulative source.inner.scheduleExponent
          AllocatedExternalCandidateSampler.degreeSourceCountConstants s source.inner.x) ≤ separation)
      [∀ r, TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
      [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
      [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
      [∀ r, T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)],
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))
      letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal)) :=
        IsModuleTopology.topologicalAddGroup ℝ _
      letI := realification_moduleTopology_t2 data.quotient.basis
      ∃ desc : data.DescendedFamily,
      ∃ geometry : (optionProduct D (fun j => (F.native j).model)).AdaptedMapGeometryData
          (optionProduct data.quotient (fun j => (F.native j).model))
          (optionMarkedLieMap (L := fun j => (F.native j).L)
            (lieQuotientMap data.front.prep.nativeQuotientIdeal)) jointGeo adaptedBudget,
      ∃ markGeometry : (optionProduct data.quotient (fun j => (F.native j).model)).FixedSourceAdaptedMarkGeometryData
          (optionProduct FmarkNative (fun j => (F.native j).model)) geometry.target
          (optionMarkedLieMap (L := fun j => (F.native j).L)
            (quotientInducedMark data.front.prep.nativeQuotientIdeal φ data.ideal_killed))
          markInput markBudget,
      let hmarkΦ := D.nativeOptionFixedSourceQuotientMark_mem_layer FmarkNative
        data.front.prep.nativeQuotientIdeal data.front.prep.nativeQuotientIdeal_terminal
        data.quotient data.quotient_filtration (fun j => (F.native j).model)
        φ data.ideal_killed hφ geometry.target
      let hMark : ∀ k, (NilpotentLieFiltration.pi (optionFiltrations FmarkNative.filtration
          (fun j => (F.native j).model.filtration))).layer k =
          Submodule.span ℚ (markGeometry.target.basis '' {i | k ≤ markGeometry.target.weight i}) := by
        intro k
        exact FmarkNative.optionAdaptedModel_layers (fun j => (F.native j).model) markGeometry.target k
      F.ActualAdaptedPivotQuotientLongPhysicalTerminal keepLong data.retained P₀.centerLift
        (data.factorFamily_path_eq hp) (fun a _ => data.factorFamily_center_eq hp a)
        (fun a _ i => data.frozen_side a i)
        (fun x => (data.front.prep.selected.tests x).observable) weight
        (Real.exp (-AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p)))
        (data.factorFamily_score hp) geometry.source.basis geometry.source.weight
        geometry.source.layers
        (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList
        data.quotient (data.factorFamily_quotient_filtration hp) data.ideal_killed
        (fun x => (desc.tests x).observable) desc.recovery geometry.target
        markGeometry.target.basis markGeometry.target.weight hMark hmarkΦ
        source.inner.scheduleExponent source.inner.Cprimitive source.inner.x separation qVertical qCommon pProj

end PrimitiveResult

end
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedFiniteNestedDegreeSourceProfileScalars
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {X₀ J₀ G X : Type} [Fintype G] [Fintype X]
    (prep : RankPreparationFamily X₀ J₀ m)
    {B : LayerSamplerAxis (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) → Type}
    [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ ((prep j).Coord → ℝ)}
    {b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ ((prep j).Coord → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern
      (Option (LayerSamplerVariables G (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((prep j).Coord)) (euclideanSubspace (U j)))]
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

local notation "countConstants" => degreeSourceCountConstants

variable (outerDepth innerDepth cutoff exponent Cprimitive Cslice Cdirect M Jalloc : ℕ)
    (Bstruct gainLog stageLog Qstride Plate E endpoint rankThreshold : ℝ)

local notation "Slots" => PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
local notation "count" => Fintype.card (LayerSamplerVariables G
    (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B)
local notation "pnum" => (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)
local notation "seed" => candidateNestedForwardSeed exponent countConstants innerDepth
local notation "native" => preparedFiniteNestedSourceNative m G count (Fintype.card X)
    (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect countConstants
    Bstruct pnum Qstride gainLog stageLog Plate
local notation "slotSeed" => preparedFiniteNestedForwardAllDegreeSeed exponent countConstants Bstruct
local notation "slotStage" => preparedFiniteNestedForwardAllDegreeStage
local notation "slotDegree" => preparedFiniteNestedForwardAllDegreeDegree

attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.nestedDegreeSourceSiteNonempty
noncomputable def preparedFiniteNestedDegreeSourceProfile
    (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ} {p chartLog : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ m) (hdepth : degree ≤ innerDepth)
    (hFrontExponent : preparedFiniteForwardFrontProfileExponent e ≤ exponent)
    (hCapExponent : preparedCommonRadiusDensityCapNestedExponent m ≤ exponent)
    (hInnerExponent : allocatedCandidateForwardScheduleExponent degree m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent m
          (preparedFiniteForwardDetectorPolynomial cutoff))) 2 ≤ exponent)
    (hCslice : 1 ≤ Cslice) (hSliceExponent : Cslice + 1 ≤ exponent)
    (hInnerSlice : allocatedCandidateStageSliceExponent degree m Cprimitive ≤ Cslice)
    (hprimitive : 1 ≤ Cprimitive)
    (hBstruct : 0 ≤ Bstruct) (hg : gainLog ∈ Set.Icc 0 Bstruct)
    (hs : stageLog ∈ Set.Icc 0 Bstruct) (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M) (hnum : pnum ≤ Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (htags : (Fintype.card (X ⊕ (Σ j, (prep j).Coord)) : ℝ) ≤ Bstruct)
    (hvariables : (count : ℝ) ≤ Bstruct)
    (hpFront : p ∈ Set.Icc 0 (seed outerFront.val Bstruct))
    (hpInner : p ≤ seed outerInner.val Bstruct)
    (hξ : ξ ≤ 1) (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (Vtail : Fin m → ℝ≥0) (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Bstruct)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hendpoint : 0 ≤ endpoint)
    (hE : preparedNestedFrontProjectionEnvelope exponent countConstants innerDepth
      (fun k : Slots => (preparedFiniteNestedForwardAllDegreeOuter k).val)
      (fun k : Slots => (slotStage k).val) native
      Bstruct gainLog stageLog endpoint ≤ E)
    (hNative : ∀ k : Slots, sampler.NativeDetection (slotDegree k)
      ((preparedFiniteForwardParameter exponent countConstants (slotStage k).val (slotSeed k) + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants
            (slotStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
            (slotSeed k) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k))))
      (native k)
      (Real.exp (-(2 * preparedFiniteForwardModelPrecision exponent countConstants
        (slotStage k).val (slotSeed k) gainLog stageLog +
        4 * preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k) + 8))))
    (hexcess :
      (FiniteProbabilityWeights.uniformFinset (integerBox N) sampler.integerBox_nonempty).excessMass
        (sampler.law.siteLaw (sampler.physicalBox hξ hmargin))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous prep j))
          (preparedSamplerTransverse prep j) (R j) (Vtail j)) ≤
        6 * positiveProjectionAccuracy E)
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ (N i : ℝ))
    (hrank : Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ rankThreshold)
    (hsampling : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) rankThreshold (U j) (poly j))
    (hτ : τ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hCbound : ∀ j, C j ≤ Real.exp chartLog) (hallow : chartLog + 1 ≤ Bstruct)
    (hRadius : ∀ j, R j = allocatedCommonProductRadius m Bstruct Bstruct) :
    sampler.DegreeSourceProfile degree p e := by
  have hA : 2 ≤ exponent :=
    (preparedFiniteForwardFrontProfileExponent_two_le e).trans hFrontExponent
  have hseed0 (o : ℕ) : 0 ≤ seed o Bstruct :=
    candidateNestedForwardSeed_nonneg exponent countConstants innerDepth o hBstruct
  have hseed (o : ℕ) : Bstruct ≤ seed o Bstruct :=
    le_candidateNestedForwardSeed exponent countConstants innerDepth o hA hBstruct
  have hX : (Fintype.card X : ℝ) ≤ Bstruct := by
    have h : Fintype.card X ≤ Fintype.card (X ⊕ (Σ j, (prep j).Coord)) := by
      rw [Fintype.card_sum]
      exact Nat.le_add_right _ _
    exact (Nat.cast_le.mpr h).trans htags
  obtain ⟨_, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions prep Jalloc hM
  have hmnum : m ≤ enlargedPreparedCommonSamplerDimension m M Jalloc := by
    unfold enlargedPreparedCommonSamplerDimension
    omega
  have hcap := prepared_commonRadius_densityCap_nested_bound m exponent hCapExponent
    prep le_rfl M Jalloc hM Bstruct hBstruct hnum Vtail hVtail hprofile
    countConstants innerDepth outerFront.val 0
  have hcapR : 4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous prep j))
      (preparedSamplerTransverse prep j) (R j) (Vtail j) ≤
      Real.exp (preparedFiniteForwardWork exponent countConstants 0 (seed outerFront.val Bstruct)) := by
    simpa only [hRadius] using hcap
  let kFront : Slots := (outerFront, 0, ⟨degree, Nat.lt_succ_of_le hdegree⟩, false)
  let entry := fun k : Slots => preparedFiniteForwardFrontProjectionPrecision
    (preparedFiniteForwardModelPrecision exponent countConstants (slotStage k).val
      (slotSeed k) gainLog stageLog)
    (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k)) (native k)
  have hentry : ∀ k, 0 ≤ entry k := by
    intro k
    have hsk := hseed (preparedFiniteNestedForwardAllDegreeOuter k).val
    exact preparedFiniteForwardFrontProjectionPrecision_nonneg
      (preparedFiniteForward_model_precision_bounds exponent countConstants (slotStage k).val
        (hseed0 _) ⟨hg.1, hg.2.trans hsk⟩ ⟨hs.1, hs.2.trans hsk⟩).1
      (preparedFiniteForwardWork_nonneg exponent countConstants (slotStage k).val (hseed0 _))
  have hprojection : entry kFront ≤ E := by
    have hsingle : entry kFront ≤ ∑ k, entry k :=
      Finset.single_le_sum (fun k _ => hentry k) (Finset.mem_univ kFront)
    have he : endpoint + 1 + ∑ k, entry k ≤ E := hE
    linarith only [hsingle, he, hendpoint]
  have hfrontDetection := hNative kFront
  simp only [kFront, preparedFiniteNestedForwardAllDegreeStage_slot,
    preparedFiniteNestedForwardAllDegreeDegree_slot, preparedFiniteNestedForwardAllDegreeSeed_slot,
    preparedFiniteNestedForwardAllDegreeIsDirect_slot, Fin.val_zero,
    preparedFiniteForwardParameter_zero, preparedFiniteForwardPairedSourcePrecision_model,
    preparedFiniteNestedSourceNative, preparedFiniteNestedSourceMaster_front] at hfrontDetection
  have hfrontProjection := hprojection
  simp only [entry, kFront, preparedFiniteNestedForwardAllDegreeStage_slot,
    preparedFiniteNestedForwardAllDegreeSeed_slot, Fin.val_zero,
    preparedFiniteNestedSourceNative, preparedFiniteNestedForwardAllDegreeDegree_slot,
    preparedFiniteNestedSourceMaster_front, preparedFiniteForwardFrontProjectionPrecision] at hfrontProjection
  let front := sampler.preparedFiniteForwardActualFrontSourceProfile cutoff exponent Cslice Cdirect
    countConstants hFrontExponent hCslice hSliceExponent (hdegree.trans hcutoff)
    (hseed0 _) hpFront ⟨hg.1, hg.2.trans (hseed _)⟩ ⟨hs.1, hs.2.trans (hseed _)⟩
    ⟨hBstruct, hseed _⟩ ⟨Nat.cast_nonneg _, hnum.trans (hseed _)⟩
    ⟨hBstruct, hseed _⟩ ⟨hQstride.1, hQstride.2.trans (hseed _)⟩
    (hvariables.trans (hseed _)) (hX.trans (hseed _)) (hG.trans (hseed _))
    hξ hmargin hcapR hfrontProjection hfrontDetection hexcess
  have hinnerDetection : ∀ r < degree, sampler.NativeDetection r
      ((preparedFiniteForwardParameter exponent countConstants r (seed outerInner.val Bstruct) + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true
            (seed outerInner.val Bstruct) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants r (seed outerInner.val Bstruct))))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m r) (r + 1)
        (preparedFiniteForwardActualLocalMaster m G count (Fintype.card X)
          (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect countConstants r
          (seed outerInner.val Bstruct) gainLog stageLog Bstruct pnum Bstruct Qstride) Plate).nativeBudget
      (Real.exp (-(2 * preparedFiniteForwardModelPrecision exponent countConstants r
        (seed outerInner.val Bstruct) gainLog stageLog +
        4 * preparedFiniteForwardWork exponent countConstants r (seed outerInner.val Bstruct) + 8))) := by
    intro r hr
    have hi : r < innerDepth + 1 := Nat.lt_succ_of_le (hr.le.trans hdepth)
    have hd : r < cutoff + 1 := Nat.lt_succ_of_le (hr.le.trans hdegree)
    simpa only [preparedFiniteNestedForwardAllDegreeStage_slot,
      preparedFiniteNestedForwardAllDegreeDegree_slot, preparedFiniteNestedForwardAllDegreeSeed_slot,
      preparedFiniteNestedForwardAllDegreeIsDirect_slot, preparedFiniteNestedSourceNative,
      preparedFiniteNestedSourceMaster_direct] using
        hNative (outerInner, ⟨r, hi⟩, ⟨r, hd⟩, true)
  let inner := preparedFiniteForwardActualInnerSourceProfile sampler degree cutoff exponent
    Cprimitive Cslice Cdirect (seed outerInner.val Bstruct) gainLog stageLog Bstruct pnum
    Bstruct Qstride Plate rankThreshold (hseed0 _)
    ⟨hg.1, hg.2.trans (hseed _)⟩ ⟨hs.1, hs.2.trans (hseed _)⟩ hprimitive hdegree hcutoff
    ⟨hBstruct, hseed _⟩ ⟨Nat.cast_nonneg _, hnum.trans (hseed _)⟩
    ⟨hBstruct, hseed _⟩ ⟨hQstride.1, hQstride.2.trans (hseed _)⟩
    (hG.trans (hseed _)) hInnerExponent hInnerSlice hinnerDetection
    (htags.trans (hseed _)) ((Nat.cast_le.mpr hmnum).trans (hnum.trans (hseed _)))
    (hvariables.trans (hseed _)) hsize hrank hsampling
  have hstrong : ∀ r < degree, sampler.NativeDetection r
      (allocatedCandidateStageSlice degree m inner.Cprimitive
        (preparedFiniteForwardParameter inner.scheduleExponent countConstants r inner.x))
      (inner.pTest r) (inner.sourceNative r) (Real.exp (-(seed outerInner.val Bstruct)) / 2) := by
    intro r hr
    have hb0 : 0 ≤ preparedFiniteForwardParameter exponent countConstants r
        (seed outerInner.val Bstruct) :=
      preparedFiniteForwardParameter_nonneg exponent countConstants r (hseed0 _)
    have hCtwo : 2 ≤ Cslice :=
      (allocatedCandidateStageSlice_bounds degree m Cprimitive hb0).1.trans hInnerSlice
    have hslice : allocatedCandidateStageSlice degree m Cprimitive
        (preparedFiniteForwardParameter exponent countConstants r (seed outerInner.val Bstruct)) ≤
        (preparedFiniteForwardParameter exponent countConstants r (seed outerInner.val Bstruct) + Cslice) ^ Cslice := by
      unfold allocatedCandidateStageSlice
      apply (pow_le_pow_left₀ (add_nonneg hb0 (Nat.cast_nonneg _))
        (add_le_add le_rfl (Nat.cast_le.mpr hInnerSlice)) _).trans
      exact pow_le_pow_right₀ (by
        have hCtwoReal : (2 : ℝ) ≤ Cslice := Nat.cast_le.mpr hCtwo
        linarith only [hb0, hCtwoReal]) hInnerSlice
    exact AllocatedExternalCandidateSampler.NativeDetection.mono_tests sampler
      (hinnerDetection r hr) hslice le_rfl
      (preparedFiniteForwardFixedCenterThreshold_le_seed_half exponent countConstants r
        hA (hseed0 _) hg.1 hs.1)
  let innerStrong := inner.with_gain_detection (seed outerInner.val Bstruct)
    (hg.2.trans (hseed _)) le_rfl (fun _ => Real.exp (-(seed outerInner.val Bstruct)) / 2)
    (fun _ _ => div_nonneg (Real.exp_nonneg _) (by norm_num)) (fun _ _ => le_rfl) hstrong
  exact sampler.preparedCommonRadiusDegreeSourceProfile front innerStrong hpInner
    hτ hσone hpoly C hC hchart hCbound hallow hBstruct hvariables
    (fun j => (Nat.cast_le.mpr (hI j)).trans hnum)
    (fun j => (Nat.cast_le.mpr (hn j)).trans hnum) hRadius

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScalarNestedSourceDegreeGlobalization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

local notation "countConstants" => degreeSourceCountConstants

variable (q outerDepth innerDepth cutoff exponent Cprimitive Cslice Cdirect : ℕ)
    (Bstruct gainLog stageLog Qstride Plate : ℝ)
local notation "Slots" => PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
local notation "count" => Fintype.card (LayerSamplerVariables G I n B)
local notation "pnum" => (Fintype.card G : ℝ)
local notation "seed" => candidateNestedForwardSeed exponent countConstants innerDepth
local notation "native" => preparedFiniteNestedSourceNative q G count (Fintype.card X)
    (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect countConstants
    Bstruct pnum Qstride gainLog stageLog Plate
local notation "slotSeed" => preparedFiniteNestedForwardAllDegreeSeed exponent countConstants Bstruct
local notation "slotStage" => preparedFiniteNestedForwardAllDegreeStage
local notation "slotDegree" => preparedFiniteNestedForwardAllDegreeDegree
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

local instance zeroLayerNestedDegreeSiteNonempty_r682199_1 : Nonempty A.Site := A.site_nonempty
noncomputable def zeroLayerNestedDegreeSourceProfile
    (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ} {p : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ q) (hdepth : degree ≤ innerDepth)
    (hFrontExponent : preparedFiniteForwardFrontProfileExponent e ≤ exponent)
    (hInnerExponent : allocatedCandidateForwardScheduleExponent degree 0 Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent q
          (preparedFiniteForwardDetectorPolynomial cutoff))) 2 ≤ exponent)
    (hCslice : 1 ≤ Cslice) (hSliceExponent : Cslice + 1 ≤ exponent)
    (hInnerSlice : allocatedCandidateStageSliceExponent degree 0 Cprimitive ≤ Cslice)
    (hprimitive : 1 ≤ Cprimitive)
    (hBstruct : 0 ≤ Bstruct) (hg : gainLog ∈ Set.Icc 0 Bstruct)
    (hs : stageLog ∈ Set.Icc 0 Bstruct) (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (hX : (Fintype.card X : ℝ) ≤ Bstruct)
    (hpFront : p ∈ Set.Icc 0 (seed outerFront.val Bstruct))
    (hpInner : p ≤ seed outerInner.val Bstruct)
    (hξ : ξ ≤ 1)
    {surplus L : ℝ} (hsurplus : 0 < surplus) (hsurplus1 : surplus ≤ 1)
    (htrim : τ = unconditionedSpatialTrimFraction (Fintype.card X) surplus)
    (hN : ∀ i, unconditionedSpatialWidthCutoff
      (allocatedExternalCandidateRootBudget B U b S) τ L ≤ (N i : ℝ))
    (hNative : ∀ k : Slots, A.NativeDetection (slotDegree k)
      ((preparedFiniteForwardParameter exponent countConstants (slotStage k).val (slotSeed k) + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants
            (slotStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
            (slotSeed k) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k))))
      (native k)
      (preparedFiniteNestedForwardFixedCenterThreshold exponent countConstants Bstruct gainLog stageLog k))
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ (N i : ℝ)) :
    A.DegreeSourceProfile degree p e := by
  have hA : 2 ≤ exponent :=
    (preparedFiniteForwardFrontProfileExponent_two_le e).trans hFrontExponent
  have hseed0 (o : ℕ) : 0 ≤ seed o Bstruct :=
    candidateNestedForwardSeed_nonneg exponent countConstants innerDepth o hBstruct
  have hseed (o : ℕ) : Bstruct ≤ seed o Bstruct :=
    le_candidateNestedForwardSeed exponent countConstants innerDepth o hA hBstruct
  have hvariables : (count : ℝ) ≤ Bstruct := by
    simpa only [zeroLayerVariables_card] using hG
  have htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ Bstruct := by
    simpa using hX
  let kFront : Slots := (outerFront, 0, ⟨degree, Nat.lt_succ_of_le hdegree⟩, false)
  have hfrontDetection := hNative kFront
  simp only [kFront, preparedFiniteNestedForwardAllDegreeStage_slot,
    preparedFiniteNestedForwardAllDegreeDegree_slot,
    preparedFiniteNestedForwardAllDegreeIsDirect_slot, Fin.val_zero,
    preparedFiniteForwardParameter_zero, preparedFiniteForwardPairedSourcePrecision_model,
    preparedFiniteNestedSourceNative, preparedFiniteNestedSourceMaster_front,
    preparedFiniteNestedForwardFixedCenterThreshold, preparedFiniteNestedForwardAllDegreeSeed] at hfrontDetection
  let front := A.zeroLayerForwardFrontSourceProfile q cutoff exponent Cslice Cdirect
    countConstants hFrontExponent hCslice hSliceExponent (hdegree.trans hcutoff)
    (hseed0 _) hpFront ⟨hg.1, hg.2.trans (hseed _)⟩ ⟨hs.1, hs.2.trans (hseed _)⟩
    ⟨hBstruct, hseed _⟩ ⟨Nat.cast_nonneg _, hG.trans (hseed _)⟩
    ⟨hBstruct, hseed _⟩ ⟨hQstride.1, hQstride.2.trans (hseed _)⟩
    (hvariables.trans (hseed _)) (hX.trans (hseed _)) (hG.trans (hseed _))
    hξ hsurplus hsurplus1 htrim hN hfrontDetection
  have hinnerDetection : ∀ r < degree, A.NativeDetection r
      ((preparedFiniteForwardParameter exponent countConstants r (seed outerInner.val Bstruct) + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true
            (seed outerInner.val Bstruct) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants r (seed outerInner.val Bstruct))))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q r) (r + 1)
        (preparedFiniteForwardActualLocalMaster q G count (Fintype.card X)
          (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect countConstants r
          (seed outerInner.val Bstruct) gainLog stageLog Bstruct pnum Bstruct Qstride) Plate).nativeBudget
      (Real.exp (-(2 * preparedFiniteForwardModelPrecision exponent countConstants r
        (seed outerInner.val Bstruct) gainLog stageLog +
        4 * preparedFiniteForwardWork exponent countConstants r (seed outerInner.val Bstruct) + 8))) := by
    intro r hr
    have hi : r < innerDepth + 1 := Nat.lt_succ_of_le (hr.le.trans hdepth)
    have hd : r < cutoff + 1 := Nat.lt_succ_of_le (hr.le.trans hdegree)
    simpa only [preparedFiniteNestedForwardAllDegreeStage_slot,
      preparedFiniteNestedForwardAllDegreeDegree_slot, preparedFiniteNestedForwardAllDegreeSeed_slot,
      preparedFiniteNestedForwardAllDegreeIsDirect_slot, preparedFiniteNestedSourceNative,
      preparedFiniteNestedSourceMaster_direct, preparedFiniteNestedForwardFixedCenterThreshold,
      preparedFiniteNestedForwardAllDegreeSeed] using
        hNative (outerInner, ⟨r, hi⟩, ⟨r, hd⟩, true)
  let rankThreshold := Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
    (seed outerInner.val Bstruct))
  let inner := preparedFiniteForwardActualResourceLayerInnerSourceProfile A q degree cutoff exponent
    Cprimitive Cslice Cdirect (seed outerInner.val Bstruct) gainLog stageLog Bstruct pnum
    Bstruct Qstride Plate rankThreshold (hseed0 _)
    ⟨hg.1, hg.2.trans (hseed _)⟩ ⟨hs.1, hs.2.trans (hseed _)⟩ hprimitive hdegree hcutoff
    ⟨hBstruct, hseed _⟩ ⟨Nat.cast_nonneg _, hG.trans (hseed _)⟩
    ⟨hBstruct, hseed _⟩ ⟨hQstride.1, hQstride.2.trans (hseed _)⟩
    (hG.trans (hseed _)) hInnerExponent hInnerSlice hinnerDetection
    (htags.trans (hseed _)) (by simpa using hseed0 outerInner.val)
    (hvariables.trans (hseed _)) hsize le_rfl (fun j => Fin.elim0 j)
  have hstrong : ∀ r < degree, A.NativeDetection r
      (allocatedCandidateStageSlice degree 0 inner.Cprimitive
        (preparedFiniteForwardParameter inner.scheduleExponent countConstants r inner.x))
      (inner.pTest r) (inner.sourceNative r) (Real.exp (-(seed outerInner.val Bstruct)) / 2) := by
    intro r hr
    have hb0 : 0 ≤ preparedFiniteForwardParameter exponent countConstants r
        (seed outerInner.val Bstruct) :=
      preparedFiniteForwardParameter_nonneg exponent countConstants r (hseed0 _)
    have hCtwo : 2 ≤ Cslice :=
      (allocatedCandidateStageSlice_bounds degree 0 Cprimitive hb0).1.trans hInnerSlice
    have hslice : allocatedCandidateStageSlice degree 0 Cprimitive
        (preparedFiniteForwardParameter exponent countConstants r (seed outerInner.val Bstruct)) ≤
        (preparedFiniteForwardParameter exponent countConstants r (seed outerInner.val Bstruct) + Cslice) ^ Cslice := by
      unfold allocatedCandidateStageSlice
      apply (pow_le_pow_left₀ (add_nonneg hb0 (Nat.cast_nonneg _))
        (add_le_add le_rfl (Nat.cast_le.mpr hInnerSlice)) _).trans
      exact pow_le_pow_right₀ (by
        have hCtwoReal : (2 : ℝ) ≤ Cslice := Nat.cast_le.mpr hCtwo
        linarith only [hb0, hCtwoReal]) hInnerSlice
    exact AllocatedExternalCandidateSampler.NativeDetection.mono_tests A
      (hinnerDetection r hr) hslice le_rfl
      (preparedFiniteForwardFixedCenterThreshold_le_seed_half exponent countConstants r
        hA (hseed0 _) hg.1 hs.1)
  let innerStrong := inner.with_gain_detection (seed outerInner.val Bstruct)
    (hg.2.trans (hseed _)) le_rfl (fun _ => Real.exp (-(seed outerInner.val Bstruct)) / 2)
    (fun _ _ => div_nonneg (Real.exp_nonneg _) (by norm_num)) (fun _ _ => le_rfl) hstrong
  have hτ : τ ≤ 1 := by
    rw [htrim]
    exact (unconditionedSpatialTrimFraction_bounds (Fintype.card X) hsurplus hsurplus1).2.1.trans (by norm_num)
  exact A.zeroLayerDegreeSourceProfile front innerStrong hpInner hτ

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel AllocatedExternalCandidateSampler
open scoped Classical BigOperators NNReal TensorProduct

def PreparedScalarNestedPowerDegreeProfiles
    (s outerDepth innerDepth exponent Cprimitive Cdirect : ℕ)
    (entropies : Fin (s + 1) → ℕ)
    (basePower earlyExponent latePower sizeExponent : ℕ) : Prop :=
  ∀ {nX : ℕ} {p : ℝ}, 2 ≤ p → (nX : ℝ) ≤ p →
    ∀ {I₀ J₀ : Fin 0 → Type} [∀ j, Fintype (I₀ j)] [∀ j, Fintype (J₀ j)]
      {n₀ : Fin 0 → ℕ} {B₀ : LayerSamplerAxis I₀ n₀ → Type} [∀ a, Fintype (B₀ a)]
      {U₀ : ∀ j, Submodule ℝ (J₀ j → ℝ)}
      {b₀ : ∀ j, Basis (Fin (n₀ j)) ℝ (euclideanSubspace (U₀ j))ᗮ}
      {R₀ σ₀ : Fin 0 → ℝ}
      {S₀ : LayerSamplerScale (G := Fin (scalarNativeDimension s)) B₀ U₀ b₀ R₀ σ₀}
      {hb₀ : ∀ j, span ℤ (Set.range (b₀ j)) = projectedIntegerLattice (euclideanSubspace (U₀ j))}
      {o₀ : ∀ j, OrthonormalBasis (I₀ j) ℝ (euclideanSubspace (U₀ j))}
      {hR₀ : ∀ j, 0 < R₀ j} {hσ₀ : ∀ j, 0 < σ₀ j}
      {N : Fin nX → ℕ} {poly₀ : ∀ j, VectorPolynomial (Fin nX) ℝ (J₀ j → ℝ)}
      {hmem₀ : ∀ j e, coefficients (poly₀ j) e ∈ U₀ j}
      {τ ξ₀ : ℝ}
      {center₀ : CoefficientTorus
        (K := LayerSamplerVariables (Fin (scalarNativeDimension s)) I₀ n₀ B₀) U₀}
      [∀ j, IsZLattice ℝ
        (latticeSection (standardEuclideanLattice (J₀ j)) (euclideanSubspace (U₀ j)))]
      (A₀ : AllocatedExternalCandidateSampler B₀ U₀ b₀ S₀ hb₀ o₀ hR₀ hσ₀
        N poly₀ hmem₀ τ ξ₀ (fun _ : Fin nX => 1) {0} center₀),
      ξ₀ ≤ 1 →
      τ = unconditionedSpatialTrimFraction nX (Real.exp (-p)) →
      Real.exp ((p + 2) ^ earlyExponent) ≤ S₀.value →
      (S₀.value : ℝ) ≤ Real.exp ((p + 2) ^ latePower) →
      (∀ i, Real.exp ((p + 2) ^ sizeExponent) ≤ (N i : ℝ)) →
      let Bstruct := (p + 2) ^ basePower
      let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth s
      let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
      let stage : K → ℕ := fun k => (preparedFiniteNestedForwardAllDegreeStage k).val
      let seed : K → ℝ := preparedFiniteNestedForwardAllDegreeSeed exponent degreeSourceCountConstants Bstruct
      let sourceU := fun k : K => preparedFiniteForwardPairedSourcePrecision exponent Cdirect
        degreeSourceCountConstants (stage k) (preparedFiniteNestedForwardAllDegreeIsDirect k)
        (seed k) Bstruct Bstruct
      let modelLog := fun k : K => preparedFiniteForwardWork exponent degreeSourceCountConstants
        (stage k) (seed k)
      let Cslice := preparedFiniteNestedSourceSliceExponent 0 s Cprimitive
      let sliceLog := fun k : K =>
        (preparedFiniteForwardParameter exponent degreeSourceCountConstants (stage k) (seed k) + Cslice) ^ Cslice
      let α := preparedFiniteNestedForwardFixedCenterThreshold exponent degreeSourceCountConstants
        Bstruct Bstruct Bstruct
      let Pdetect := preparedFiniteForwardDetectorPolynomial s
      let outerSeed := candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth
      ∃ Plate : ℝ, 0 ≤ Plate ∧
        (∀ k : K, A₀.NativeDetection (degree k) (sliceLog k)
          (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
          (preparedFiniteNestedSourceNative (max s 1) (Fin (scalarNativeDimension s))
            (scalarNativeDimension s) nX Pdetect exponent Cdirect degreeSourceCountConstants
            Bstruct (scalarNativeDimension s) 0 Bstruct Bstruct Plate k) (α k)) ∧
        (∀ (outer : Fin (outerDepth + 1)) (degree : Fin (s + 1)) (i : Fin nX),
          Real.exp (preparedFiniteForwardCumulative exponent degreeSourceCountConstants degree.val
            (outerSeed outer.val Bstruct)) ≤ (N i : ℝ)) ∧
        ∀ (entropySlot : Fin (s + 1)) (outerFront outerInner : Fin (outerDepth + 1)),
          outerFront ≤ outerInner → ∀ (d : ℕ) (hd : d ≤ s) (pNorm : ℝ),
          pNorm ∈ Set.Icc 0 (outerSeed outerFront.val Bstruct) →
          ∃ P : A₀.DegreeSourceProfile d pNorm (entropies entropySlot),
            P.inner.x = outerSeed outerInner.val Bstruct ∧
            P.inner.gainLog = outerSeed outerInner.val Bstruct ∧
            P.front.u = preparedFiniteForwardModelPrecision exponent degreeSourceCountConstants 0
              (outerSeed outerFront.val Bstruct) Bstruct Bstruct ∧
            P.front.pModel = preparedFiniteForwardWork exponent degreeSourceCountConstants 0
              (outerSeed outerFront.val Bstruct) ∧
            P.front.nativeBudget = preparedFiniteNestedSourceNative (max s 1)
              (Fin (scalarNativeDimension s)) (scalarNativeDimension s) nX Pdetect
              exponent Cdirect degreeSourceCountConstants Bstruct (scalarNativeDimension s) 0
              Bstruct Bstruct Plate
              ((outerFront, 0, ⟨d, Nat.lt_succ_of_le hd⟩, false) : K)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel AllocatedExternalCandidateSampler
open scoped Classical BigOperators NNReal TensorProduct

def PreparedScalarNestedPowerDegreeProfilesFull
    (s outerDepth innerDepth exponent Cprimitive Cdirect : ℕ)
    (entropies : Fin (s + 1) → ℕ)
    (basePower earlyExponent latePower sizeExponent : ℕ) : Prop :=
  ∀ {nX : ℕ} {p : ℝ}, 2 ≤ p → (nX : ℝ) ≤ p →
    ∀ {I₀ J₀ : Fin 0 → Type} [∀ j, Fintype (I₀ j)] [∀ j, Fintype (J₀ j)]
      {n₀ : Fin 0 → ℕ} {B₀ : LayerSamplerAxis I₀ n₀ → Type} [∀ a, Fintype (B₀ a)]
      {U₀ : ∀ j, Submodule ℝ (J₀ j → ℝ)}
      {b₀ : ∀ j, Basis (Fin (n₀ j)) ℝ (euclideanSubspace (U₀ j))ᗮ}
      {R₀ σ₀ : Fin 0 → ℝ}
      {S₀ : LayerSamplerScale (G := Fin (scalarNativeDimension s)) B₀ U₀ b₀ R₀ σ₀}
      {hb₀ : ∀ j, span ℤ (Set.range (b₀ j)) = projectedIntegerLattice (euclideanSubspace (U₀ j))}
      {o₀ : ∀ j, OrthonormalBasis (I₀ j) ℝ (euclideanSubspace (U₀ j))}
      {hR₀ : ∀ j, 0 < R₀ j} {hσ₀ : ∀ j, 0 < σ₀ j}
      {N : Fin nX → ℕ} {poly₀ : ∀ j, VectorPolynomial (Fin nX) ℝ (J₀ j → ℝ)}
      {hmem₀ : ∀ j e, coefficients (poly₀ j) e ∈ U₀ j}
      {τ ξ₀ : ℝ}
      {center₀ : CoefficientTorus
        (K := LayerSamplerVariables (Fin (scalarNativeDimension s)) I₀ n₀ B₀) U₀}
      [∀ j, IsZLattice ℝ
        (latticeSection (standardEuclideanLattice (J₀ j)) (euclideanSubspace (U₀ j)))]
      (A₀ : AllocatedExternalCandidateSampler B₀ U₀ b₀ S₀ hb₀ o₀ hR₀ hσ₀
        N poly₀ hmem₀ τ ξ₀ (fun _ : Fin nX => 1) {0} center₀),
      ξ₀ ≤ 1 →
      τ = unconditionedSpatialTrimFraction nX (Real.exp (-p)) →
      Real.exp ((p + 2) ^ earlyExponent) ≤ S₀.value →
      (S₀.value : ℝ) ≤ Real.exp ((p + 2) ^ latePower) →
      (∀ i, Real.exp ((p + 2) ^ sizeExponent) ≤ (N i : ℝ)) →
      let Bstruct := (p + 2) ^ basePower
      let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth s
      let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
      let stage : K → ℕ := fun k => (preparedFiniteNestedForwardAllDegreeStage k).val
      let seed : K → ℝ := preparedFiniteNestedForwardAllDegreeSeed exponent degreeSourceCountConstants Bstruct
      let sourceU := fun k : K => preparedFiniteForwardPairedSourcePrecision exponent Cdirect
        degreeSourceCountConstants (stage k) (preparedFiniteNestedForwardAllDegreeIsDirect k)
        (seed k) Bstruct Bstruct
      let modelLog := fun k : K => preparedFiniteForwardWork exponent degreeSourceCountConstants
        (stage k) (seed k)
      let Cslice := preparedFiniteNestedSourceSliceExponent 0 s Cprimitive
      let sliceLog := fun k : K =>
        (preparedFiniteForwardParameter exponent degreeSourceCountConstants (stage k) (seed k) + Cslice) ^ Cslice
      let α := preparedFiniteNestedForwardFixedCenterThreshold exponent degreeSourceCountConstants
        Bstruct Bstruct Bstruct
      let Pdetect := preparedFiniteForwardDetectorPolynomial s
      let outerSeed := candidateNestedForwardSeed exponent degreeSourceCountConstants innerDepth
      ∃ Plate : ℝ, 0 ≤ Plate ∧
        (∀ k : K, A₀.NativeDetection (degree k) (sliceLog k)
          (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
          (preparedFiniteNestedSourceNative (max s 1) (Fin (scalarNativeDimension s))
            (scalarNativeDimension s) nX Pdetect exponent Cdirect degreeSourceCountConstants
            Bstruct (scalarNativeDimension s) 0 Bstruct Bstruct Plate k) (α k)) ∧
        (∀ (outer : Fin (outerDepth + 1)) (degree : Fin (s + 1)) (i : Fin nX),
          Real.exp (preparedFiniteForwardCumulative exponent degreeSourceCountConstants degree.val
            (outerSeed outer.val Bstruct)) ≤ (N i : ℝ)) ∧
        ∀ (entropySlot : Fin (s + 1)) (outerFront outerInner : Fin (outerDepth + 1)),
          outerFront ≤ outerInner → ∀ (d : ℕ) (hd : d ≤ s) (pNorm : ℝ),
          pNorm ∈ Set.Icc 0 (outerSeed outerFront.val Bstruct) →
          ∃ P : A₀.DegreeSourceProfile d pNorm (entropies entropySlot),
            P.inner.x = outerSeed outerInner.val Bstruct ∧
            P.inner.gainLog = outerSeed outerInner.val Bstruct ∧
            P.front.u = preparedFiniteForwardModelPrecision exponent degreeSourceCountConstants 0
              (outerSeed outerFront.val Bstruct) Bstruct Bstruct ∧
            P.front.pModel = preparedFiniteForwardWork exponent degreeSourceCountConstants 0
              (outerSeed outerFront.val Bstruct) ∧
            P.front.nativeBudget = preparedFiniteNestedSourceNative (max s 1)
              (Fin (scalarNativeDimension s)) (scalarNativeDimension s) nX Pdetect
              exponent Cdirect degreeSourceCountConstants Bstruct (scalarNativeDimension s) 0
              Bstruct Bstruct Plate
              ((outerFront, 0, ⟨d, Nat.lt_succ_of_le hd⟩, false) : K) ∧
            P.inner.Cprimitive = Cprimitive ∧
            P.inner.scheduleExponent = exponent ∧
            P.inner.Csource = preparedFiniteForwardInnerSourceExponent Cdirect
              (preparedFiniteForwardActualNativeBudgetExponent (max s 1) Pdetect)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel AllocatedExternalCandidateSampler
open scoped Classical BigOperators NNReal TensorProduct
attribute [local irreducible] AllocatedExternalCandidateSampler.DegreeGlobalizationAt

def ScalarNestedSourceDegreeGlobalization
    (s initial exponent basePower earlyExponent latePower sizeExponent : ℕ) : Prop :=
  ∀ {nX : ℕ} {p : ℝ}, 2 ≤ p → (nX : ℝ) ≤ p →
    ∀ {I₀ E₀ J₀ : Fin 0 → Type} [∀ j, Fintype (I₀ j)] [∀ j, Fintype (J₀ j)]
      {n₀ : Fin 0 → ℕ} {B₀ : LayerSamplerAxis I₀ n₀ → Type} [∀ a, Fintype (B₀ a)]
      {U₀ : ∀ j, Submodule ℝ (J₀ j → ℝ)}
      {b₀ : ∀ j, Basis (Fin (n₀ j)) ℝ (euclideanSubspace (U₀ j))ᗮ}
      {R₀ σ₀ : Fin 0 → ℝ}
      {S₀ : LayerSamplerScale (G := Fin (scalarNativeDimension s)) B₀ U₀ b₀ R₀ σ₀}
      {hb₀ : ∀ j, span ℤ (Set.range (b₀ j)) = projectedIntegerLattice (euclideanSubspace (U₀ j))}
      {o₀ : ∀ j, OrthonormalBasis (I₀ j) ℝ (euclideanSubspace (U₀ j))}
      {hR₀ : ∀ j, 0 < R₀ j} {hσ₀ : ∀ j, 0 < σ₀ j}
      {N : Fin nX → ℕ} {poly₀ : ∀ j, VectorPolynomial (Fin nX) ℝ (J₀ j → ℝ)}
      {hmem₀ : ∀ j e, coefficients (poly₀ j) e ∈ U₀ j}
      {τ ξ₀ : ℝ}
      {center₀ : CoefficientTorus
        (K := LayerSamplerVariables (Fin (scalarNativeDimension s)) I₀ n₀ B₀) U₀}
      [∀ j, IsZLattice ℝ
        (latticeSection (standardEuclideanLattice (J₀ j)) (euclideanSubspace (U₀ j)))]
      (A₀ : AllocatedExternalCandidateSampler B₀ U₀ b₀ S₀ hb₀ o₀ hR₀ hσ₀
        N poly₀ hmem₀ τ ξ₀ (fun _ : Fin nX => 1) {0} center₀),
      ξ₀ ≤ 1 →
      τ = unconditionedSpatialTrimFraction nX (Real.exp (-p)) →
      Real.exp ((p + 2) ^ earlyExponent) ≤ S₀.value →
      (S₀.value : ℝ) ≤ Real.exp ((p + 2) ^ latePower) →
      (∀ i, Real.exp ((p + 2) ^ sizeExponent) ≤ (N i : ℝ)) →
      let Bstruct := (p + 2) ^ basePower
      let finalSeed := candidateNestedForwardSeed exponent degreeSourceCountConstants (s + 1)
        (2 * s) Bstruct
      Real.exp finalSeed ≤ (S₀.value : ℝ) →
      ∀ weight : (Fin nX → ℤ) → ℂ,
        A₀.DegreeGlobalizationAt (E := E₀) weight s initial Bstruct
          (candidateDegreeReturnBudget s finalSeed)

end Erdos3.VectorPolynomial

end

end OAI
end


