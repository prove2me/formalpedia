-- Prove2me | Definitions.Def_OAIE3v2B293
-- name    : OAIE3v2B293
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T08:48:47.483986+00:00
-- url     : https://prove2.me/theorems/96cd6074-16c3-4327-bd2f-981727cb1e9f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 307 of 311
-- statement:
--   Definitions bundle 307 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B288`, `OAIE3v2B289`, `OAIE3v2B290` of this split.
--
--   Modules: `Dynamics/AllocatedExternalCandidateSourcePhysicalBudgetBounds.lean`, `Dynamics/PreparedFiniteNestedFrontNativeBudget.lean`, `Estimates/AllocatedCandidateZeroRestrictedNativeCommonPhysicalTerminal.lean`, `Estimates/AllocatedCandidateZeroRestrictedNativeCommonTerminal.lean`, `Estimates/AllocatedFrozenPrefixStageData.lean`, `Polynomial/AllocatedNestedDegreeInduction.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B288
import Definitions.Def_OAIE3v2B289
import Definitions.Def_OAIE3v2B290

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFrozenPrefixStageData
namespace OAI

section

namespace Erdos3.VectorPolynomial

open NilpotentLieFiltration
open scoped Classical

local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

theorem allocatedCandidateStage_keep_subset_initialLong
    {σ : Type*} (side : σ → ℝ) (initialLong keep : σ → Prop)
    (s m Cprimitive scheduleExponent r : ℕ) {x initialShortCost : ℝ}
    (hx : 0 ≤ x)
    (hshortCost : initialShortCost ≤ (x + Cprimitive) ^ Cprimitive)
    (hshort : ∀ i, ¬initialLong i → side i ≤ Real.exp initialShortCost)
    (hkept : ∀ i, keep i →
      Real.exp (allocatedCandidateStageSlice s m Cprimitive
        (preparedFiniteForwardParameter scheduleExponent countConstants r x)) ≤ side i) :
    ∀ i, keep i → initialLong i := by
  intro i hi
  by_contra hnot
  have hstrict := Real.exp_lt_exp.mpr
    (allocatedCandidateStage_cost_lt_slice s m Cprimitive hx
      (le_preparedFiniteForwardParameter scheduleExponent countConstants r hx) hshortCost)
  exact (not_lt_of_ge (hshort i hnot)) (hstrict.trans_le (hkept i hi))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCandidateZeroRestrictedNativeCommonTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : ℕ → LayerSamplerVariables G I n B → Prop)
    {ι κ η : Type} {χ : ℕ → Type} [Fintype ι] [Fintype κ] [∀ r, Fintype (χ r)] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

theorem exists_forward_terminal_of_zero_restricted_candidates
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ν)]
    [∀ r, Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ω)]
    [∀ r, Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ν)]
    [∀ r, TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
    (hfast : BasisGradedSubmodule (Fmark.associatedGradedBasis bF ν hF) ν (fast).toSubmodule)
    (hsection : ∀ y, (fast).toSubmodule.mkQ (lift y) = y)
    (Bphase Bbound pTree Rrank : ℝ) (Hbr qS : ℕ)
    (scheduleExponent : ℕ) (x gainLog stageLog : ℝ)
    (T : CertifiedFullChartFiniteHistory.BudgetedBranchTree Fmark bF ν hF J
      (fast).toSubmodule (eQ.baseChange ℝ) lift Z U poly N Bphase
      (fun r => preparedFiniteForwardCap scheduleExponent countConstants r x) s pTree)
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (Cprimitive Csource : ℕ) (sourceNative pTest α : ℕ → ℝ)
    (hSourceNonneg : ∀ r < s, 0 ≤ sourceNative r)
    (hSourceBound : ∀ r < s, sourceNative r ≤
      (preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
        preparedFiniteForwardWork scheduleExponent countConstants r x + Csource) ^ Csource)
    (hBaseExponent : allocatedCandidateStageBaseExponent s m Cprimitive ≤ scheduleExponent)
    (hphaseExponent : ∀ r < s,
      allocatedCandidateCompositePhaseConstant s m 1
        (allocatedCandidatePromotedMajorConstant Csource) r ≤ scheduleExponent)
    (hHbr : 1 ≤ Hbr) (hqS : 0 < qS)
    (hκBase : (Fintype.card κ : ℝ) ≤ x)
    (hTagsBase : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x)
    (hηBase : (Fintype.card η : ℝ) ≤ x)
    (hHbrBase : (Hbr : ℝ) ≤ Real.exp x) (hqSBase : (qS : ℝ) ≤ Real.exp x)
    (hBboundBase : Bbound ≤ Real.exp x)
    (hstructure : ∀ i j z, RationalHeightLE ((Fmark.associatedGradedBasis bF ν hF).repr
      ⁅Fmark.associatedGradedBasis bF ν hF i, Fmark.associatedGradedBasis bF ν hF j⁆ z) Hbr)
    (hentry : ∀ i j, |((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤ Bbound)
    (hgrid : ∀ j, (fun i => ((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS)
    (hcost : cost ≤ (x + Cprimitive) ^ Cprimitive)
    (HMap l H Hθ : ℕ) (qNative : ℝ)
    (hHMap : 1 ≤ HMap) (hl : 0 < l) (hH : 1 ≤ H)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hlExp : (l : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHExp : (H : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHθExp : (Hθ : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hqNative : qNative ≤ (x + Cprimitive) ^ Cprimitive)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex
      (fun _ : LayerSamplerVariables G I n B => 1) ω) : ℝ) ≤
        (x + Cprimitive) ^ Cprimitive)
    (htarget : (Fintype.card (SymbolBasisIndex
      (fun _ : LayerSamplerVariables G I n B => 1) ν) : ℝ) ≤
        (x + Cprimitive) ^ Cprimitive)
    (hκ : (Fintype.card κ : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hχ : ∀ r < s, (Fintype.card (χ r) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hsampler : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (vg : ∀ r, χ r → Fmark.PolynomialSymbol
      (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1))
    (hspan : ∀ r < s, span ℚ (Set.range (vg r)) =
      (Fmark.symbolPointwiseSubalgebra bF ν hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) fast).toSubmodule)
    (hvg : ∀ r < s, ∀ i z, RationalHeightLE
      ((Fmark.polynomialSymbolBasis bF ν hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1)).repr (vg r i) z) H)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hstageLong : ∀ r < s, ∀ i, keep r i → initialLong i)
    (hOriginal : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i : LayerSamplerVariables G I n B // initialLong i} => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
        (fun _ : {i : LayerSamplerVariables G I n B // initialLong i} => 1)
        ((P.chart z).axisPolynomial initialLong (fun _ => 0))
        ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P.candidate z).orbit)))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hkept : ∀ r, ∀ i, keep r i → Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) ≤ (A.sides i : ℝ))
    (hfrozen : ∀ r, ∀ i, ¬keep r i → (A.sides i : ℝ) ≤ Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)))
    (hTest : ∀ r < s, OrdinaryPolynomialPhase.budget r ≤ pTest r)
    (hα : ∀ r < s, α r ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : ∀ r < s, A.NativeDetection r (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) (pTest r) (sourceNative r) (α r))
    (hN : ∀ i, Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ (N i : ℝ))
    (hRrank : Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    ∃ history ∈ T.level s,
      FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2
        (preparedFiniteForwardWork scheduleExponent countConstants s x) ∧
      RationalTaggedConstraintCertificate J Set.univ history.K
        (preparedFiniteForwardCumulative scheduleExponent countConstants s x)
        (s * (Fintype.card η * m)) ∧
      ∀ point ∈ history.K,
        eval₂ point (Fmark.realGradedSymbolPolynomial bF ν hF (fullTaggedVariableWeight J)
          (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈
            (fast).toSubmodule.baseChange ℝ := by
  let shortCost : ℕ → ℝ := fun r => allocatedCandidateStageSlice s m Cprimitive
    (preparedFiniteForwardParameter scheduleExponent countConstants r x)
  have hrefinement (r : ℕ) : Nonempty (P.AxisFreezing (fun _ => keep r) (shortCost r)) :=
    P.exists_forward_axisFreezing (keep r) Cprimitive scheduleExponent r x hx hcost
      (hkept r) (hfrozen r)
  let freezing : ∀ r, P.AxisFreezing (fun _ => keep r) (shortCost r) :=
    fun r => Classical.choice (hrefinement r)
  have hkeep : ∀ r, ∀ z : (freezing r).problem.productive,
      ((freezing r).problem.chart z).keep = keep r := fun _ _ => rfl
  apply exists_forward_terminal_of_native_stage_data (χ := χ)
    (fun r => max cost (shortCost r)) (fun _ => massThreshold) (fun _ => scoreThreshold)
    (fun r => (freezing r).problem) keep hkeep bD ω hD bF ν hF hφ W
    eQ lift hfast hsection Bphase Bbound pTree Rrank Hbr qS
    scheduleExponent x gainLog stageLog T hx hgain hstage Cprimitive Csource sourceNative
    hSourceNonneg hSourceBound hBaseExponent hphaseExponent hHbr hqS hκBase hTagsBase
    hηBase hHbrBase hqSBase hBboundBase hstructure hentry hgrid
  intro r hr
  have hphase := allocatedCandidateForwardMajor_cap s m Cprimitive Csource
    scheduleExponent r hx hgain hstage (hSourceNonneg r hr) (hSourceBound r hr)
    hBaseExponent (hphaseExponent r hr)
  have hscale := Real.exp_le_exp.mpr (hphase.trans
    (preparedFiniteForwardCap_le_cumulative scheduleExponent countConstants hx hr))
  exact ⟨(freezing r).historyStageData_of_zero_restricted_factors (χ := χ r) (keep r) (hkeep r)
    bD ω hD bF ν hF hφ W eQ r (Nat.le_of_lt hr)
    Cprimitive x (preparedFiniteForwardParameter scheduleExponent countConstants r x)
    (preparedFiniteForwardCumulative scheduleExponent countConstants r x) Rrank
    (allocatedCandidateTerminalPhaseConstant s m 1 r) hx
    (le_preparedFiniteForwardParameter scheduleExponent countConstants r hx)
    (preparedFiniteForward_prefix_bounds scheduleExponent countConstants r hx).1.2
    hcost HMap l H Hθ qNative hHMap hl hH hHMapExp hlExp hHExp hHθExp hqNative hentries
    ((Nat.cast_le.mpr (ordinarySymbolSubtype_card_le (keep r) ω)).trans hsource)
    ((Nat.cast_le.mpr (ordinarySymbolSubtype_card_le (keep r) ν)).trans htarget)
    hκ (hχ r hr) hηBase htags hsampler hJ hbracket
    (vg r) (hspan r hr) (hvg r hr) hθ initialLong
    (fun z i hi => hstageLong r hr i hi) hOriginal hτ hξ hσone Cgeo hCgeo hchart hsmall hpoly
    (pTest r) (sourceNative r) (α r) (hSourceNonneg r hr) (hkept r) (hfrozen r)
    (hTest r hr) (hα r hr) (hdirect r hr) (fun i => hscale.trans (hN i))
    (hscale.trans hRrank) hrank⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : ℕ → LayerSamplerVariables G I n B → Prop)
    {ι κ η : Type} {χ : ℕ → Type} [Fintype ι] [Fintype κ] [∀ r, Fintype (χ r)] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

theorem exists_early_forward_terminal_of_zero_restricted_candidates
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ν)]
    [∀ r, Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ω)]
    [∀ r, Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ν)]
    [∀ r, TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
    (hfast : BasisGradedSubmodule (Fmark.associatedGradedBasis bF ν hF) ν (fast).toSubmodule)
    (hsection : ∀ y, (fast).toSubmodule.mkQ (lift y) = y)
    (Bbound Rrank : ℝ) (Hbr qS : ℕ)
    (scheduleExponent : ℕ) (x gainLog stageLog : ℝ)
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (Cprimitive Csource : ℕ) (sourceNative pTest α : ℕ → ℝ)
    (hSourceNonneg : ∀ r < s, 0 ≤ sourceNative r)
    (hSourceBound : ∀ r < s, sourceNative r ≤
      (preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
        preparedFiniteForwardWork scheduleExponent countConstants r x + Csource) ^ Csource)
    (hBaseExponent : allocatedCandidateStageBaseExponent s m Cprimitive ≤ scheduleExponent)
    (hphaseExponent : ∀ r < s,
      allocatedCandidateCompositePhaseConstant s m 1
        (allocatedCandidatePromotedMajorConstant Csource) r ≤ scheduleExponent)
    (hHbr : 1 ≤ Hbr) (hqS : 0 < qS)
    (hκBase : (Fintype.card κ : ℝ) ≤ x)
    (hTagsBase : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x)
    (hηBase : (Fintype.card η : ℝ) ≤ x)
    (hmEarly : (m : ℝ) ≤ x)
    (hblocksEarly : ((s * (Fintype.card η * m) : ℕ) : ℝ) ≤ x)
    (hHbrBase : (Hbr : ℝ) ≤ Real.exp x) (hqSBase : (qS : ℝ) ≤ Real.exp x)
    (hBboundBase : Bbound ≤ Real.exp x)
    (hstructure : ∀ i j z, RationalHeightLE ((Fmark.associatedGradedBasis bF ν hF).repr
      ⁅Fmark.associatedGradedBasis bF ν hF i, Fmark.associatedGradedBasis bF ν hF j⁆ z) Hbr)
    (hentry : ∀ i j, |((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤ Bbound)
    (hgrid : ∀ j, (fun i => ((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS)
    (hcost : cost ≤ (x + Cprimitive) ^ Cprimitive)
    (HMap l H Hθ : ℕ) (qNative : ℝ)
    (hHMap : 1 ≤ HMap) (hl : 0 < l) (hH : 1 ≤ H)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hlExp : (l : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHExp : (H : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHθExp : (Hθ : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hqNative : qNative ≤ (x + Cprimitive) ^ Cprimitive)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex
      (fun _ : LayerSamplerVariables G I n B => 1) ω) : ℝ) ≤
        (x + Cprimitive) ^ Cprimitive)
    (htarget : (Fintype.card (SymbolBasisIndex
      (fun _ : LayerSamplerVariables G I n B => 1) ν) : ℝ) ≤
        (x + Cprimitive) ^ Cprimitive)
    (hκ : (Fintype.card κ : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hχ : ∀ r < s, (Fintype.card (χ r) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hsampler : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (vg : ∀ r, χ r → Fmark.PolynomialSymbol
      (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1))
    (hspan : ∀ r < s, span ℚ (Set.range (vg r)) =
      (Fmark.symbolPointwiseSubalgebra bF ν hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) fast).toSubmodule)
    (hvg : ∀ r < s, ∀ i z, RationalHeightLE
      ((Fmark.polynomialSymbolBasis bF ν hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1)).repr (vg r i) z) H)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hstageLong : ∀ r < s, ∀ i, keep r i → initialLong i)
    (hOriginal : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i : LayerSamplerVariables G I n B // initialLong i} => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
        (fun _ : {i : LayerSamplerVariables G I n B // initialLong i} => 1)
        ((P.chart z).axisPolynomial initialLong (fun _ => 0))
        ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P.candidate z).orbit)))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hkept : ∀ r, ∀ i, keep r i → Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) ≤ (A.sides i : ℝ))
    (hfrozen : ∀ r, ∀ i, ¬keep r i → (A.sides i : ℝ) ≤ Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)))
    (hTest : ∀ r < s, OrdinaryPolynomialPhase.budget r ≤ pTest r)
    (hα : ∀ r < s, α r ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : ∀ r < s, A.NativeDetection r (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) (pTest r) (sourceNative r) (α r))
    (hN : ∀ i, Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ (N i : ℝ))
    (hRrank : Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    let hXEarly : (Fintype.card X : ℝ) ≤ x := by
      have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
        simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
      exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hsum
    let hJEarly : (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
      have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
        simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
      exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans hsum
    let hNEarly : ∀ i, 1 ≤ N i := by
      intro i
      have hpos : 0 < N i := by
        exact_mod_cast ((Real.exp_pos _).trans_le (hN i))
      exact Nat.succ_le_iff.mpr hpos
    let T := CertifiedFullChartFiniteHistory.earlyForwardBranchTree
      Fmark bF ν hF J (fast).toSubmodule (eQ.baseChange ℝ) lift Z U poly N
      s scheduleExponent x hx hXEarly hmEarly hJEarly hηBase hblocksEarly
      (fun j ex _ => hm j ex) hNEarly
    ∃ history ∈ T.level s,
      FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2
        (preparedFiniteForwardWork scheduleExponent countConstants s x) ∧
      RationalTaggedConstraintCertificate J Set.univ history.K
        (preparedFiniteForwardCumulative scheduleExponent countConstants s x)
        (s * (Fintype.card η * m)) ∧
      ∀ point ∈ history.K,
        eval₂ point (Fmark.realGradedSymbolPolynomial bF ν hF (fullTaggedVariableWeight J)
          (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈
            (fast).toSubmodule.baseChange ℝ := by
  intro hXEarly hJEarly hNEarly T
  exact P.exists_forward_terminal_of_zero_restricted_candidates keep bD ω hD bF ν hF hφ W
    eQ lift hfast hsection (preparedFiniteForwardCumulative scheduleExponent countConstants s x) Bbound
    (preparedFiniteForwardParameter scheduleExponent countConstants s x) Rrank Hbr qS scheduleExponent x
    gainLog stageLog T hx hgain hstage Cprimitive Csource sourceNative pTest α hSourceNonneg hSourceBound
    hBaseExponent hphaseExponent hHbr hqS hκBase hTagsBase hηBase hHbrBase hqSBase hBboundBase hstructure
    hentry hgrid hcost HMap l H Hθ qNative hHMap hl hH hHMapExp hlExp hHExp hHθExp hqNative hentries
    hsource htarget hκ hχ htags hsampler hJ hbracket vg hspan hvg hθ initialLong hstageLong hOriginal hτ hξ hσone Cgeo hCgeo
    hchart hsmall hpoly hkept hfrozen hTest hα hdirect hN hRrank hrank

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : ℕ → LayerSamplerVariables G I n B → Prop)
    {ι κ η γ : Type} [Fintype ι] [Fintype κ] [Fintype η] [Fintype γ]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

theorem exists_early_forward_terminal_of_zero_restricted_fast_generators
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ν)]
    [∀ r, Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ω)]
    [∀ r, Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ν)]
    [∀ r, TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
    (hfast : BasisGradedSubmodule (Fmark.associatedGradedBasis bF ν hF) ν (fast).toSubmodule)
    (hsection : ∀ y, (fast).toSubmodule.mkQ (lift y) = y)
    (Bbound Rrank : ℝ) (Hbr qS : ℕ)
    (scheduleExponent : ℕ) (x gainLog stageLog : ℝ)
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (Cprimitive Csource : ℕ) (sourceNative pTest α : ℕ → ℝ)
    (hSourceNonneg : ∀ r < s, 0 ≤ sourceNative r)
    (hSourceBound : ∀ r < s, sourceNative r ≤
      (preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
        preparedFiniteForwardWork scheduleExponent countConstants r x + Csource) ^ Csource)
    (hBaseExponent : allocatedCandidateStageBaseExponent s m Cprimitive ≤ scheduleExponent)
    (hphaseExponent : ∀ r < s,
      allocatedCandidateCompositePhaseConstant s m 1
        (allocatedCandidatePromotedMajorConstant Csource) r ≤ scheduleExponent)
    (hHbr : 1 ≤ Hbr) (hqS : 0 < qS)
    (hκBase : (Fintype.card κ : ℝ) ≤ x)
    (hTagsBase : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x)
    (hηBase : (Fintype.card η : ℝ) ≤ x)
    (hmEarly : (m : ℝ) ≤ x)
    (hblocksEarly : ((s * (Fintype.card η * m) : ℕ) : ℝ) ≤ x)
    (hHbrBase : (Hbr : ℝ) ≤ Real.exp x) (hqSBase : (qS : ℝ) ≤ Real.exp x)
    (hBboundBase : Bbound ≤ Real.exp x)
    (hstructure : ∀ i j z, RationalHeightLE ((Fmark.associatedGradedBasis bF ν hF).repr
      ⁅Fmark.associatedGradedBasis bF ν hF i, Fmark.associatedGradedBasis bF ν hF j⁆ z) Hbr)
    (hentry : ∀ i j, |((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤ Bbound)
    (hgrid : ∀ j, (fun i => ((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS)
    (hcost : cost ≤ (x + Cprimitive) ^ Cprimitive)
    (HMap l H Hθ : ℕ) (qNative : ℝ)
    (hHMap : 1 ≤ HMap) (hl : 0 < l) (hH : 1 ≤ H)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hlExp : (l : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHExp : (H : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHθExp : (Hθ : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hqNative : qNative ≤ (x + Cprimitive) ^ Cprimitive)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex
      (fun _ : LayerSamplerVariables G I n B => 1) ω) : ℝ) ≤
        (x + Cprimitive) ^ Cprimitive)
    (htarget : (Fintype.card (SymbolBasisIndex
      (fun _ : LayerSamplerVariables G I n B => 1) ν) : ℝ) ≤
        (x + Cprimitive) ^ Cprimitive)
    (hκ : (Fintype.card κ : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hsampler : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (fastGenerators : γ → Fmark.AssociatedGraded)
    (hfastSpan : span ℚ (Set.range fastGenerators) = (fast).toSubmodule)
    (hfastHeight : ∀ a i, RationalHeightLE
      ((Fmark.associatedGradedBasis bF ν hF).repr (fastGenerators a) i) H)
    (hgeneratorCount :
      ((Fintype.card (SymbolBasisIndex
        (fun _ : LayerSamplerVariables G I n B => 1) ν) * Fintype.card γ : ℕ) : ℝ) ≤
          (x + Cprimitive) ^ Cprimitive)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hstageLong : ∀ r < s, ∀ i, keep r i → initialLong i)
    (hOriginal : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i : LayerSamplerVariables G I n B // initialLong i} =>
        (A.sides i.val : ℝ)) qNative l W
      (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
        (fun _ : {i : LayerSamplerVariables G I n B // initialLong i} => 1)
        ((P.chart z).axisPolynomial initialLong (fun _ => 0))
        ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P.candidate z).orbit)))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hkept : ∀ r, ∀ i, keep r i → Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) ≤ (A.sides i : ℝ))
    (hfrozen : ∀ r, ∀ i, ¬keep r i → (A.sides i : ℝ) ≤ Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)))
    (hTest : ∀ r < s, OrdinaryPolynomialPhase.budget r ≤ pTest r)
    (hα : ∀ r < s, α r ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : ∀ r < s, A.NativeDetection r (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) (pTest r) (sourceNative r) (α r))
    (hN : ∀ i, Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ (N i : ℝ))
    (hRrank : Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    let hXEarly : (Fintype.card X : ℝ) ≤ x := by
      have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
        simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
      exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hsum
    let hJEarly : (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
      have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
        simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
      exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans hsum
    let hNEarly : ∀ i, 1 ≤ N i := by
      intro i
      have hpos : 0 < N i := by
        exact_mod_cast ((Real.exp_pos _).trans_le (hN i))
      exact Nat.succ_le_iff.mpr hpos
    let T := CertifiedFullChartFiniteHistory.earlyForwardBranchTree
      Fmark bF ν hF J (fast).toSubmodule (eQ.baseChange ℝ) lift Z U poly N
      s scheduleExponent x hx hXEarly hmEarly hJEarly hηBase hblocksEarly
      (fun j ex _ => hm j ex) hNEarly
    ∃ history ∈ T.level s,
      FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2
        (preparedFiniteForwardWork scheduleExponent countConstants s x) ∧
      RationalTaggedConstraintCertificate J Set.univ history.K
        (preparedFiniteForwardCumulative scheduleExponent countConstants s x)
        (s * (Fintype.card η * m)) ∧
      ∀ point ∈ history.K,
        eval₂ point (Fmark.realGradedSymbolPolynomial bF ν hF (fullTaggedVariableWeight J)
          (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈
            (fast).toSubmodule.baseChange ℝ := by
  intro hXEarly hJEarly hNEarly T
  let χ : ℕ → Type := fun r =>
    SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ν × γ
  let vg := fun r => Fmark.pointwiseSymbolSpanningFamily bF ν hF
    (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) fastGenerators
  have hχ (r : ℕ) (_hr : r < s) : (Fintype.card (χ r) : ℝ) ≤
      (x + Cprimitive) ^ Cprimitive := by
    have hcard := ordinarySymbolSubtype_card_le (keep r) ν
    have hmul := Nat.mul_le_mul_right (Fintype.card γ) hcard
    exact (Nat.cast_le.mpr (by simpa only [χ, Fintype.card_prod] using hmul)).trans hgeneratorCount
  have hspan (r : ℕ) (_hr : r < s) : span ℚ (Set.range (vg r)) =
      (Fmark.symbolPointwiseSubalgebra bF ν hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) fast).toSubmodule :=
    Fmark.pointwiseSymbolSpanningFamily_span bF ν hF _ fast hfast fastGenerators hfastSpan
  have hvg (r : ℕ) (_hr : r < s) : ∀ a i, RationalHeightLE
      ((Fmark.polynomialSymbolBasis bF ν hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1)).repr (vg r a) i) H :=
    Fmark.pointwiseSymbolSpanningFamily_height bF ν hF _ fastGenerators hH hfastHeight
  exact P.exists_early_forward_terminal_of_zero_restricted_candidates keep bD ω hD bF ν hF hφ W
    eQ lift hfast hsection Bbound Rrank Hbr qS scheduleExponent x
    gainLog stageLog hx hgain hstage Cprimitive Csource sourceNative pTest α hSourceNonneg hSourceBound
    hBaseExponent hphaseExponent hHbr hqS hκBase hTagsBase hηBase hmEarly hblocksEarly
    hHbrBase hqSBase hBboundBase hstructure hentry hgrid hcost HMap l H Hθ qNative
    hHMap hl hH hHMapExp hlExp hHExp hHθExp hqNative hentries hsource htarget hκ hχ htags
    hsampler hJ hbracket vg hspan hvg hθ initialLong hstageLong hOriginal hτ hξ hσone Cgeo hCgeo hchart hsmall
    hpoly hkept hfrozen hTest hα hdirect hN hRrank hrank

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : ℕ → LayerSamplerVariables G I n B → Prop)
    {ι κ γ : Type} [Fintype ι] [Fintype κ] [Fintype γ]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

theorem exists_early_forward_terminal_of_zero_restricted_native_common_factors
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ν)]
    [∀ r, Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ω)]
    [∀ r, Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ν)]
    [∀ r, TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (v : γ → D.filtration.AssociatedGraded)
    (hv : span ℚ (Set.range v) = W.toSubmodule)
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis bD ω hD) ω W.toSubmodule)
    (pGeometry Rrank : ℝ) (Hbr : ℕ)
    (hpGeometry : 0 ≤ pGeometry)
    (hιGeometry : (Fintype.card ι : ℝ) ≤ pGeometry)
    (hκGeometry : (Fintype.card κ : ℝ) ≤ pGeometry)
    (hγGeometry : (Fintype.card γ : ℝ) ≤ pGeometry)
    (hsamplerGeometry : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pGeometry)
    (hvGeometry : ∀ a i, rationalLogHeight
      ((D.filtration.associatedGradedBasis bD ω hD).repr (v a) i) ≤ pGeometry)
    (scheduleExponent : ℕ) (x gainLog stageLog : ℝ)
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (Cprimitive Csource : ℕ) (sourceNative pTest α : ℕ → ℝ)
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
    (HMap l : ℕ) (qNative : ℝ)
    (hHMap : 1 ≤ HMap) (hl : 0 < l)
    (hHMapGeometry : (HMap : ℝ) ≤ Real.exp pGeometry)
    (hlExp : (l : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hqNative : qNative ≤ (x + Cprimitive) ^ Cprimitive)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) Hbr)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hstageLong : ∀ r < s, ∀ i, keep r i → initialLong i)
    (hOriginal : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
        (fun _ : {i // initialLong i} => 1)
        ((P.chart z).axisPolynomial initialLong (fun _ => 0))
        ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P.candidate z).orbit)))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hkept : ∀ r, ∀ i, keep r i → Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) ≤ (A.sides i : ℝ))
    (hfrozen : ∀ r, ∀ i, ¬keep r i → (A.sides i : ℝ) ≤ Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)))
    (hTest : ∀ r < s, OrdinaryPolynomialPhase.budget r ≤ pTest r)
    (hα : ∀ r < s, α r ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : ∀ r < s, A.NativeDetection r (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) (pTest r) (sourceNative r) (α r))
    (hN : ∀ i, Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ (N i : ℝ))
    (hRrank : Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    ∃ (qDim : ℕ) (hdim : qDim ≤ Fintype.card κ)
      (eQ : Basis (Fin qDim) ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
      (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded),
    BasisGradedSubmodule (Fmark.associatedGradedBasis bF ν hF) ν (fast).toSubmodule ∧
    Function.RightInverse lift (fast).toSubmodule.mkQ ∧
    let hηBase : (Fintype.card (Fin qDim) : ℝ) ≤ x := by
      simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hdim).trans (hκGeometry.trans
        ((allocatedCandidateCommonFastBudget_bounds s hpGeometry).2.2.trans hGeometryBase))
    let hblocks : ((s * (Fintype.card (Fin qDim) * m) : ℕ) : ℝ) ≤ x := by
      simpa only [Fintype.card_fin] using
        (Nat.cast_le.mpr (Nat.mul_le_mul_left s (Nat.mul_le_mul_right m hdim))).trans hblocksEarly
    let hXEarly : (Fintype.card X : ℝ) ≤ x := by
      have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
        simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
      exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hsum
    let hJEarly : (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
      have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
        simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
      exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans hsum
    let hNEarly : ∀ i, 1 ≤ N i := by
      intro i
      have hpos : 0 < N i := by
        exact_mod_cast ((Real.exp_pos _).trans_le (hN i))
      exact Nat.succ_le_iff.mpr hpos
    let T := CertifiedFullChartFiniteHistory.earlyForwardBranchTree
      Fmark bF ν hF J (fast).toSubmodule (eQ.baseChange ℝ) lift Z U poly N
      s scheduleExponent x hx hXEarly hmEarly hJEarly hηBase hblocks
      (fun j ex _ => hm j ex) hNEarly
    ∃ history ∈ T.level s,
      FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2
        (preparedFiniteForwardWork scheduleExponent countConstants s x) ∧
      RationalTaggedConstraintCertificate J Set.univ history.K
        (preparedFiniteForwardCumulative scheduleExponent countConstants s x)
        (s * (Fintype.card (Fin qDim) * m)) ∧
      ∀ point ∈ history.K,
        eval₂ point (Fmark.realGradedSymbolPolynomial bF ν hF (fullTaggedVariableWeight J)
          (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈
            (fast).toSubmodule.baseChange ℝ := by
  classical
  have hpGeometryX : pGeometry ≤ x :=
    (allocatedCandidateCommonFastBudget_bounds s hpGeometry).2.2.trans hGeometryBase
  have hGeomX : allocatedCandidateCommonFastGeometryLog pGeometry ≤ x :=
    (allocatedCandidateCommonFastBudget_bounds s hpGeometry).1.trans hGeometryBase
  have hprimitive : x ≤ (x + Cprimitive) ^ Cprimitive := by
    have hC : (1 : ℝ) ≤ Cprimitive := by exact_mod_cast hCprimitive
    have hbase : 1 ≤ x + Cprimitive := by linarith
    exact (le_add_of_nonneg_right (Nat.cast_nonneg Cprimitive)).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hbase hCprimitive)
  have hκBase : (Fintype.card κ : ℝ) ≤ x := hκGeometry.trans hpGeometryX
  have hκ : (Fintype.card κ : ℝ) ≤ (x + Cprimitive) ^ Cprimitive := hκBase.trans hprimitive
  have htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤
      (x + Cprimitive) ^ Cprimitive := hTagsBase.trans hprimitive
  have hsampler : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      (x + Cprimitive) ^ Cprimitive := (hsamplerGeometry.trans hpGeometryX).trans hprimitive
  have hsymbolPower : (pGeometry + (s + 3)) ^ (s + 3) ≤ pointwiseFastSectionInput s pGeometry := by
    have hnonneg : 0 ≤ (pGeometry + (s + 3)) ^ (s + 3) := by positivity
    unfold pointwiseFastSectionInput
    nlinarith only [hnonneg, sq_nonneg ((pGeometry + (s + 3)) ^ (s + 3)), hpGeometry]
  have hsymbolBase : (pGeometry + (s + 3)) ^ (s + 3) ≤ (x + Cprimitive) ^ Cprimitive :=
    ((hsymbolPower.trans (allocatedCandidateCommonFastBudget_bounds s hpGeometry).2.1).trans
      hGeometryBase).trans hprimitive
  have hsource : (Fintype.card (SymbolBasisIndex
      (fun _ : LayerSamplerVariables G I n B => 1) ω) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive :=
    (D.filtration.symbolBasisIndex_card_le_spanning_budget bD ω hD _ (fun _ => Nat.zero_lt_one)
      hpGeometry hιGeometry hsamplerGeometry).trans hsymbolBase
  have htarget : (Fintype.card (SymbolBasisIndex
      (fun _ : LayerSamplerVariables G I n B => 1) ν) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive :=
    (Fmark.symbolBasisIndex_card_le_spanning_budget bF ν hF _ (fun _ => Nat.zero_lt_one)
      hpGeometry hκGeometry hsamplerGeometry).trans hsymbolBase
  have hJ (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive := by
    have hinj : Function.Injective (fun z : J j => (Sum.inr ⟨j, z⟩ : X ⊕ (Σ j, J j))) := by
      intro a b hab
      exact eq_of_heq (Sigma.mk.inj (Sum.inr.inj hab)).2
    exact (Nat.cast_le.mpr (Fintype.card_le_of_injective _ hinj)).trans htags
  have hφGeometry (i : ι) (j : κ) : rationalLogHeight (bF.repr (φ (bD i)) j) ≤ pGeometry :=
    rationalLogHeight_le_of_height (hentries j i) hHMapGeometry
  obtain ⟨qDim, hdim, eQ, lift, qS, hfast, hsection, _hsectionReal, hqS,
      hqSBound, hentry, hgrid, hθ, _hHθ, hHθBound⟩ :=
    D.filtration.exists_allocatedCandidateCommonFastGeometry Fmark φ hφ bD ω hD bF ν hF
      W v hv hW hpGeometry hιGeometry hκGeometry hγGeometry hvGeometry hφGeometry
  refine ⟨qDim, hdim, eQ, lift, hfast, hsection, ?_⟩
  intro hηBase hblocks hXEarly hJEarly hNEarly T
  let Hfast : ℕ := ⌈Real.exp ((pGeometry + 2) ^ 4)⌉₊
  let H : ℕ := max Hbr Hfast
  have hH : 1 ≤ H := hHbr.trans (Nat.le_max_left _ _)
  have hHfastBound : (Hfast : ℝ) ≤ Real.exp x :=
    (allocatedCandidateCommonFastGeneratorHeight_le hpGeometry).trans (Real.exp_le_exp.mpr hGeomX)
  have hHBound : (H : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive) := by
    have hmax : (H : ℝ) ≤ Real.exp x := by
      simpa only [H, Nat.cast_max] using max_le hHbrBase hHfastBound
    exact hmax.trans (Real.exp_le_exp.mpr hprimitive)
  have hHMapBound : (HMap : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive) :=
    hHMapGeometry.trans (Real.exp_le_exp.mpr (hpGeometryX.trans hprimitive))
  have hstructure (i j z : κ) : RationalHeightLE
      ((Fmark.associatedGradedBasis bF ν hF).repr
        ⁅Fmark.associatedGradedBasis bF ν hF i, Fmark.associatedGradedBasis bF ν hF j⁆ z) Hbr := by
    rw [Fmark.associatedGradedBasis_bracket]
    split_ifs
    · exact hbracket i j z
    · exact rationalHeightLE_zero hHbr
  let fastGenerators := D.filtration.gradedImageSpanningFamily Fmark φ hφ v
  have hfastSpan : span ℚ (Set.range fastGenerators) = (fast).toSubmodule :=
    D.filtration.gradedImageSpanningFamily_span Fmark φ hφ W v hv
  have hfastHeight (a : γ) (i : κ) : RationalHeightLE
      ((Fmark.associatedGradedBasis bF ν hF).repr (fastGenerators a) i) H := by
    apply (rationalHeightLE_ceil_exp
      (D.filtration.gradedImageSpanningFamily_logHeight Fmark φ hφ bD ω hD bF ν hF v
        hpGeometry hιGeometry hvGeometry hφGeometry a i)).mono
    exact Nat.le_max_right _ _
  have hgeneratorCount :
      ((Fintype.card (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ν) *
        Fintype.card γ : ℕ) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive := by
    have hcount := Fmark.pointwiseSpanningIndex_card_le (γ := γ) bF ν hF
      (fun _ : LayerSamplerVariables G I n B => 1) (fun _ => Nat.zero_lt_one)
      hpGeometry hκGeometry hγGeometry hsamplerGeometry
    apply (show _ ≤ pointwiseFastSectionInput s pGeometry by
      simpa only [Fintype.card_prod, Nat.cast_mul] using hcount).trans
    exact ((allocatedCandidateCommonFastBudget_bounds s hpGeometry).2.1.trans hGeometryBase).trans hprimitive
  exact P.exists_early_forward_terminal_of_zero_restricted_fast_generators keep bD ω hD bF ν hF hφ W
    eQ lift hfast hsection (Real.exp (allocatedCandidateCommonFastGeometryLog pGeometry))
    Rrank Hbr qS scheduleExponent x gainLog stageLog hx hgain hstage Cprimitive Csource
    sourceNative pTest α hSourceNonneg hSourceBound hBaseExponent hphaseExponent hHbr hqS
    hκBase hTagsBase hηBase hmEarly hblocks hHbrBase
    (hqSBound.trans (Real.exp_le_exp.mpr hGeomX)) (Real.exp_le_exp.mpr hGeomX)
    hstructure hentry hgrid hcost HMap l H (allocatedCandidateCommonFastCoordinateHeight pGeometry)
    qNative hHMap hl hH hHMapBound hlExp hHBound
    (hHθBound.trans (Real.exp_le_exp.mpr (hGeomX.trans hprimitive))) hqNative hentries
    hsource htarget hκ htags hsampler hJ
    (fun i j z => (hbracket i j z).mono (Nat.le_max_left _ _))
    fastGenerators hfastSpan hfastHeight hgeneratorCount hθ initialLong hstageLong hOriginal hτ hξ hσone Cgeo hCgeo
    hchart hsmall hpoly hkept hfrozen hTest hα hdirect hN hRrank hrank

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedNestedDegreeInduction
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
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

namespace AllocatedExternalCandidateSampler

def DegreeSourceProfile.mono_netExponent {degree e f : ℕ} {p : ℝ}
    (source : A.DegreeSourceProfile degree p f) (hp : 0 ≤ p) (hef : e ≤ f) :
    A.DegreeSourceProfile degree p e :=
  { source with front := source.front.mono_netExponent hp hef }

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
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
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

noncomputable def preparedCommonRadiusDegreeSourceProfile
    {degree e : ℕ} {p Bstruct Pchart : ℝ}
    (front : sampler.FrontSourceProfile degree p e)
    (inner : sampler.InnerSourceProfile degree) (hInput : p ≤ inner.x)
    (hτ : τ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hallow : Pchart + 1 ≤ Bstruct) (hB : 0 ≤ Bstruct)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Bstruct)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Bstruct)
    (hn : ∀ j, (n j : ℝ) ≤ Bstruct)
    (hRadius : ∀ j, R j = allocatedCommonProductRadius m Bstruct Bstruct) :
    sampler.DegreeSourceProfile degree p e := by
  let rows : Fin m → Finset (Finset (Fin 0)) := fun _ => {∅}
  letI : ∀ j, Nonempty (rows j) := fun _ => ⟨⟨∅, by simp [rows]⟩⟩
  have hsmall := (preparedUniformEarlyRadius_eighth (G := G) B rows hB hB
    (by simp) hvars hI hn C hC hCbound hallow).1
  refine {
    front := front
    inner := inner
    input_inner := hInput
    trim_le_one := hτ
    width_le_one := hσone
    polynomial_degree := hdegree
    chartConstant := C
    chartConstant_nonneg := hC
    chart_bound := hchart
    chart_small := ?_
  }
  intro j
  simpa only [hRadius j, mul_assoc] using hsmall j

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateSourcePhysicalBudgetBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module
open scoped TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSampler.InnerSourceProfile
variable {s : ℕ} (source : A.InnerSourceProfile (s + 1))

theorem recursiveParameter_polynomial : source.recursiveParameter ≤
    (candidateSourceBackendPolynomial s).eval₂ (Nat.castRingHom ℝ) source.physicalBudget :=
  (candidateSourceBackendPolynomial_bounds s source.physicalBudget_nonneg).recursive

theorem affine_floor :
    certifiedAffineLongSideBound
      (nativePhysicalTerminalAffineBudget (s + 1) source.scheduleExponent source.x) ≤
      source.separation := by
  have h := nativePhysicalTerminalBudgets_nonneg (s + 1) m source.Cprimitive
    source.scheduleExponent source.x_nonneg
  have hcenter := (allocatedCandidateTerminalFullInput_bounds (s + 1) m source.Cprimitive
    source.x_nonneg h.2.1 h.1).2.2.2.2.2.2.1
  exact candidatePhysicalOrdinaryBudget_separation s source.physicalBudget_nonneg h.1 hcenter

end AllocatedExternalCandidateSampler.InnerSourceProfile
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedFrontNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open AllocatedExternalCandidateProblem

theorem exists_preparedFiniteForwardFrontFamily_budget (Cnative : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ)
      (m cardVars : ℕ) {x p gainLog stageLog native : ℝ},
      2 ≤ A → 0 ≤ x → p ∈ Set.Icc 0 x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      (m : ℝ) ≤ x → (cardVars : ℝ) ≤ x →
      let u := preparedFiniteForwardModelPrecision A stageCountConstant 0 x gainLog stageLog
      let w := preparedFiniteForwardWork A stageCountConstant 0 x
      let t := preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant 0 false
        x gainLog stageLog + w
      native ∈ Set.Icc 0 ((t + Cnative) ^ Cnative) →
      candidateFrontFamilyParameter
        (p + positiveKernelPreparationParameter (2 * p) + u + w + native + m + cardVars + 3) ∈
          Set.Icc 0 ((t + C) ^ C) := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedFiniteForwardFrontFamilyScalar_budget Cnative
  refine ⟨C, hC, ?_⟩
  intro A Cdirect stageCountConstant m cardVars x p gainLog stageLog native
    hA hx hp hg hs hm hvars u w t hn
  have hprecision := preparedFiniteForward_model_precision_bounds A stageCountConstant 0 hx hg hs
  have hu : 0 ≤ u := hprecision.1
  have hw : 0 ≤ w := preparedFiniteForwardWork_nonneg A stageCountConstant 0 hx
  have hxw : x ≤ w := by
    have hscalar := preparedFiniteForward_model_scalar_bounds A stageCountConstant 0 0
      hA hx (by simpa only [Nat.cast_zero] using hx)
    simpa only [preparedFiniteForwardParameter_zero] using hscalar.2.1
  have htEq : t = u + 3 * w + 1 := by
    dsimp only [t]
    rw [preparedFiniteForwardPairedSourcePrecision_model]
    have heq : preparedFiniteForwardSourcePrecision A stageCountConstant 0 x gainLog stageLog =
        u + 2 * w + 1 := hprecision.2.2.1
    rw [heq]
    ring
  have ht : 0 ≤ t := by linarith only [htEq, hu, hw]
  have hwt : w ≤ t := by linarith only [htEq, hu, hw]
  have hxt : x ≤ t := hxw.trans hwt
  exact hbound m cardVars ht ⟨hp.1, hp.2.trans hxt⟩
    ⟨hu, by linarith only [htEq, hw]⟩ ⟨hw, hwt⟩ (hm.trans hxt) (hvars.trans hxt) hn

theorem exists_preparedFiniteForwardFrontFamily_polynomial_later_work_budget
    (Cnative : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ), C ≤ A → ∀ (Cdirect : ℕ)
      (stageCountConstant : ℕ → ℕ) (innerDepth m cardVars : ℕ)
      {x p gainLog stageLog native : ℝ},
      1 ≤ innerDepth → 0 ≤ x → p ∈ Set.Icc 0 x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      (m : ℝ) ≤ x → (cardVars : ℝ) ≤ x →
      let u := preparedFiniteForwardModelPrecision A stageCountConstant 0 x gainLog stageLog
      let w := preparedFiniteForwardWork A stageCountConstant 0 x
      let t := preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant 0 false
        x gainLog stageLog + w
      native ∈ Set.Icc 0 ((t + Cnative) ^ Cnative) →
      P.eval₂ (Nat.castRingHom ℝ)
        (candidateFrontFamilyParameter
          (p + positiveKernelPreparationParameter (2 * p) + u + w + native + m + cardVars + 3)) ≤
            preparedFiniteForwardWork A stageCountConstant innerDepth x := by
  obtain ⟨Cf, _, hfamily⟩ := exists_preparedFiniteForwardFrontFamily_budget Cnative
  obtain ⟨C, hC, hpoly⟩ := exists_preparedFiniteForward_local_polynomial_le_later_work Cf P
  refine ⟨C, hC, ?_⟩
  intro A hCA Cdirect stageCountConstant innerDepth m cardVars x p gainLog stageLog native
    hdepth hx hp hg hs hm hvars u w t hn
  have hf := hfamily A Cdirect stageCountConstant m cardVars (hC.trans hCA) hx hp hg hs hm hvars hn
  exact hpoly A Cdirect stageCountConstant innerDepth hx hg hs hCA hdepth hf

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

theorem exists_preparedFiniteNestedFrontFamily_polynomial_next_seed
    (q : ℕ) (Pdetect P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ (exponent Cdirect : ℕ) (constants : ℕ → ℕ)
      (outerDepth innerDepth cutoff targetLayers count nX : ℕ)
      (G : Type) [Fintype G]
      (outer : Fin (outerDepth + 1)) (degree : Fin (cutoff + 1))
      (Bstruct pnum Qstride gainLog stageLog Plate p : ℝ),
      C ≤ exponent → 1 ≤ innerDepth → 0 ≤ Bstruct → degree.val ≤ q →
      pnum ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct →
      gainLog ∈ Set.Icc 0 Bstruct → stageLog ∈ Set.Icc 0 Bstruct →
      (targetLayers : ℝ) ≤ Bstruct → (count : ℝ) ≤ Bstruct →
      (nX : ℝ) ≤ Bstruct → (Fintype.card G : ℝ) ≤ Bstruct →
      let x := candidateNestedForwardSeed exponent constants innerDepth outer.val Bstruct
      p ∈ Set.Icc 0 x →
      let native := preparedFiniteNestedSourceNative q G count nX Pdetect exponent Cdirect constants
        Bstruct pnum Qstride gainLog stageLog Plate
        (outer, (0 : Fin (innerDepth + 1)), degree, false)
      let u := preparedFiniteForwardModelPrecision exponent constants 0 x gainLog stageLog
      let w := preparedFiniteForwardWork exponent constants 0 x
      P.eval₂ (Nat.castRingHom ℝ)
        (candidateFrontFamilyParameter (p +
          AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) +
          u + w + native + targetLayers + count + 3)) ≤
        candidateNestedForwardSeed exponent constants innerDepth (outer.val + 1) Bstruct := by
  let Cnative := preparedFiniteForwardActualNativeBudgetExponent q Pdetect
  obtain ⟨C, hC, hbound⟩ :=
    exists_preparedFiniteForwardFrontFamily_polynomial_later_work_budget Cnative P
  refine ⟨C, hC, ?_⟩
  intro exponent Cdirect constants outerDepth innerDepth cutoff targetLayers count nX G _
    outer degree Bstruct pnum Qstride gainLog stageLog Plate p hCA hdepth hB hdegree
    hnum hstride hg hs htarget hcount hnX hG x hp native u w
  have hA : 2 ≤ exponent := hC.trans hCA
  have hx : 0 ≤ x := candidateNestedForwardSeed_nonneg exponent constants innerDepth outer.val hB
  have hBx : Bstruct ≤ x := le_candidateNestedForwardSeed exponent constants innerDepth outer.val hA hB
  have lift {r : ℝ} (hr : r ∈ Set.Icc 0 Bstruct) : r ∈ Set.Icc 0 x := ⟨hr.1, hr.2.trans hBx⟩
  have hnative := preparedFiniteNestedSourceNative_front_mem q G count nX Pdetect
    exponent Cdirect constants (innerDepth := innerDepth) outer degree Plate hA hB hdegree hnum hstride hg hs hcount hnX hG
  exact (hbound exponent hCA Cdirect constants innerDepth targetLayers count
    hdepth hx hp (lift hg) (lift hs) (htarget.trans hBx) (hcount.trans hBx) hnative).trans
    (candidateNestedForwardWork_le_next_seed exponent constants innerDepth outer.val innerDepth hB le_rfl)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCandidateZeroRestrictedNativeCommonPhysicalTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : ℕ → LayerSamplerVariables G I n B → Prop)
    {ι κ γ : Type} [Fintype ι] [Fintype κ] [Fintype γ]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

theorem exists_zero_restricted_native_common_affine_physical_terminal
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ν)]
    [∀ r, Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ω)]
    [∀ r, Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ν)]
    [∀ r, TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (v : γ → D.filtration.AssociatedGraded)
    (hv : span ℚ (Set.range v) = W.toSubmodule)
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis bD ω hD) ω W.toSubmodule)
    (pGeometry Rrank : ℝ) (Hbr : ℕ)
    (hpGeometry : 0 ≤ pGeometry)
    (hιGeometry : (Fintype.card ι : ℝ) ≤ pGeometry)
    (hκGeometry : (Fintype.card κ : ℝ) ≤ pGeometry)
    (hγGeometry : (Fintype.card γ : ℝ) ≤ pGeometry)
    (hsamplerGeometry : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pGeometry)
    (hvGeometry : ∀ a i, rationalLogHeight
      ((D.filtration.associatedGradedBasis bD ω hD).repr (v a) i) ≤ pGeometry)
    (scheduleExponent : ℕ) (x gainLog stageLog : ℝ)
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (Cprimitive Csource : ℕ) (sourceNative pTest α : ℕ → ℝ)
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
    (HMap l : ℕ) (qNative : ℝ)
    (hHMap : 1 ≤ HMap) (hl : 0 < l)
    (hHMapGeometry : (HMap : ℝ) ≤ Real.exp pGeometry)
    (hlExp : (l : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hqNative : qNative ≤ (x + Cprimitive) ^ Cprimitive)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) Hbr)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hstageLong : ∀ r < s, ∀ i, keep r i → initialLong i)
    (hOriginal : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
        (fun _ : {i // initialLong i} => 1)
        ((P.chart z).axisPolynomial initialLong (fun _ => 0))
        ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P.candidate z).orbit)))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hkept : ∀ r, ∀ i, keep r i → Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) ≤ (A.sides i : ℝ))
    (hfrozen : ∀ r, ∀ i, ¬keep r i → (A.sides i : ℝ) ≤ Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)))
    (hTest : ∀ r < s, OrdinaryPolynomialPhase.budget r ≤ pTest r)
    (hα : ∀ r < s, α r ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : ∀ r < s, A.NativeDetection r (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) (pTest r) (sourceNative r) (α r))
    (hN : ∀ i, Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ (N i : ℝ))
    (hRrank : Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hs : 0 < s) (hmass : 0 < massThreshold)
    (separation : ℝ)
    (hseparation : certifiedAffineLongSideBound
      (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ separation) :
    let pFull := allocatedCandidateTerminalFullInput s m Cprimitive x
      (preparedFiniteForwardWork scheduleExponent countConstants s x)
      (preparedFiniteForwardCumulative scheduleExponent countConstants s x)
    ∃ (qDim : ℕ) (hdim : qDim ≤ Fintype.card κ)
      (eQ : Basis (Fin qDim) ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
      (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded),
    BasisGradedSubmodule (Fmark.associatedGradedBasis bF ν hF) ν (fast).toSubmodule ∧
    Function.RightInverse lift (fast).toSubmodule.mkQ ∧
    let hηBase : (Fintype.card (Fin qDim) : ℝ) ≤ x := by
      simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hdim).trans (hκGeometry.trans
        ((allocatedCandidateCommonFastBudget_bounds s hpGeometry).2.2.trans hGeometryBase))
    let hblocks : ((s * (Fintype.card (Fin qDim) * m) : ℕ) : ℝ) ≤ x := by
      simpa only [Fintype.card_fin] using
        (Nat.cast_le.mpr (Nat.mul_le_mul_left s (Nat.mul_le_mul_right m hdim))).trans hblocksEarly
    let hXEarly : (Fintype.card X : ℝ) ≤ x := by
      have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
        simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
      exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hsum
    let hJEarly : (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
      have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
        simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
      exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans hsum
    let hNEarly : ∀ i, 1 ≤ N i := by
      intro i
      have hpos : 0 < N i := by
        exact_mod_cast ((Real.exp_pos _).trans_le (hN i))
      exact Nat.succ_le_iff.mpr hpos
    let T := CertifiedFullChartFiniteHistory.earlyForwardBranchTree
      Fmark bF ν hF J (fast).toSubmodule (eQ.baseChange ℝ) lift Z U poly N
      s scheduleExponent x hx hXEarly hmEarly hJEarly hηBase hblocks
      (fun j ex _ => hm j ex) hNEarly
    let pAffine := preparedFiniteForwardCumulative scheduleExponent countConstants s x
    let budget := preparedFiniteForwardWork scheduleExponent countConstants s x
    ∃ history ∈ T.level s,
      FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2
        (preparedFiniteForwardWork scheduleExponent countConstants s x) ∧
      RationalTaggedConstraintCertificate J Set.univ history.K
        (preparedFiniteForwardCumulative scheduleExponent countConstants s x)
        (s * (Fintype.card (Fin qDim) * m)) ∧
      (∀ point ∈ history.K,
        eval₂ point (Fmark.realGradedSymbolPolynomial bF ν hF (fullTaggedVariableWeight J)
          (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈
            (fast).toSubmodule.baseChange ℝ) ∧
      Nonempty (P.AffinePhysicalTerminalData bF ν hF hφ W (eQ.baseChange ℝ) lift
        pAffine budget pAffine pFull 4 history separation) := by
  classical
  intro pFull
  obtain ⟨qDim, hdim, eQ, lift, hfast, hsection, hterminal⟩ :=
    P.exists_early_forward_terminal_of_zero_restricted_native_common_factors keep bD ω hD bF ν hF hφ W
      v hv hW pGeometry Rrank Hbr hpGeometry hιGeometry hκGeometry hγGeometry hsamplerGeometry
      hvGeometry scheduleExponent x gainLog stageLog hx hgain hstage Cprimitive Csource
      sourceNative pTest α hSourceNonneg hSourceBound hBaseExponent hphaseExponent hCprimitive
      hGeometryBase hHbr hTagsBase hmEarly hblocksEarly hHbrBase hcost HMap l qNative hHMap hl
      hHMapGeometry hlExp hqNative hentries hbracket initialLong hstageLong hOriginal hτ hξ hσone Cgeo hCgeo hchart hsmall
      hpoly hkept hfrozen hTest hα hdirect hN hRrank hrank
  refine ⟨qDim, hdim, eQ, lift, hfast, hsection, ?_⟩
  intro hηBase hblocks hXEarly hJEarly hNEarly T pAffine budget
  obtain ⟨history, hmem, hcontrol, hcertificate, hterminalFast⟩ := hterminal
  have hA : 1 ≤ scheduleExponent :=
    (by omega : 1 ≤ 2).trans
      ((allocatedCandidateStageBaseExponent_bounds s m Cprimitive).1.trans hBaseExponent)
  have hxcum := le_preparedFiniteForwardCumulative scheduleExponent countConstants s hx hA hs
  have hcum : 0 ≤ pAffine := hx.trans hxcum
  have hwork : 0 ≤ budget := preparedFiniteForwardWork_nonneg scheduleExponent countConstants s hx
  have hfull := allocatedCandidateTerminalFullInput_bounds s m Cprimitive hx hwork hcum
  have hxFull : x ≤ pFull := hfull.2.2.1
  have hpFull : 0 ≤ pFull := hfull.1
  have hGeometryFull : pGeometry ≤ pFull :=
    ((allocatedCandidateCommonFastBudget_bounds s hpGeometry).2.2.trans hGeometryBase).trans hxFull
  have hvarsX : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x :=
    hsamplerGeometry.trans ((allocatedCandidateCommonFastBudget_bounds s hpGeometry).2.2.trans hGeometryBase)
  have hdenFull := allocatedCandidateTerminalFullInput_denominator_bound s m Cprimitive hx hwork hcum
  have hmassFull := allocatedCandidateTerminalFullInput_mass_bound s m Cprimitive
    (Fintype.card (X ⊕ (Σ j, J j))) (Fintype.card (LayerSamplerVariables G I n B))
    hx hwork hcum hTagsBase hvarsX
  refine ⟨history, hmem, hcontrol, hcertificate, hterminalFast, ?_⟩
  exact P.exists_affinePhysicalTerminalData bF ν hF hφ W (eQ.baseChange ℝ) lift
    pAffine budget pAffine history hfast hcontrol hcertificate hcum
    (hJEarly.trans hxcum) (hblocks.trans hxcum) hpoly hτ hξ hσone
    Cgeo hCgeo hchart (fun j => (hsmall j).trans (by norm_num)) hmass Hbr 4 pFull
    hHbr hpFull (hκGeometry.trans hGeometryFull) (hTagsBase.trans hxFull)
    (hHbrBase.trans (Real.exp_le_exp.mpr hxFull)) hdenFull hbracket
    (hsamplerGeometry.trans hGeometryFull) hmassFull separation hseparation

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end


