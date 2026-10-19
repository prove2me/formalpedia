-- Prove2me | Definitions.Def_OAIE3v2B288
-- name    : OAIE3v2B288
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T08:25:58.932059+00:00
-- url     : https://prove2.me/theorems/ba27aabd-486f-4529-b858-11d0ca0d4a54
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 301 of 311
-- statement:
--   Definitions bundle 301 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B062`, `OAIE3v2B309`, `OAIE3v2B280`, `OAIE3v2B281`, `OAIE3v2B282` of this split.
--
--   Modules: `Dynamics/PreparedFiniteNestedFrontNativeBudget.lean`, `Estimates/AllocatedCandidateStageDataConstruction.lean`, `Estimates/AllocatedCandidateZeroRestrictedNativeCommonTerminal.lean`, `Estimates/AllocatedExternalCandidatePrimitiveFrontDescentData.lean`, `Estimates/AllocatedFrozenPrefixStageData.lean`, `Lattices/AllocatedAffinePhysicalBoundsSuccessor.lean`, `Linear/AllocatedExternalCandidateCommonKeepPositiveKernelPreparation.lean`, `Polynomial/AllocatedNestedDegreeInduction.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B062
import Definitions.Def_OAIE3v2B309
import Definitions.Def_OAIE3v2B280
import Definitions.Def_OAIE3v2B281
import Definitions.Def_OAIE3v2B282

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedExternalCandidateCommonKeepPositiveKernelPreparation
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
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
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace CommonKeepPositiveKernelPreparation

variable {P} {p : ℝ} {e : ℕ} (front : P.CommonKeepPositiveKernelPreparation p e)

theorem conclusion_of_selected
    {q : ℝ} (hq : 0 ≤ q)
    (out : front.prep.selected.problem.Conclusion q (Real.exp (-q)) (Real.exp (-q)))
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp q)
    (hσone : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤
      Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) :
    Nonempty (P.Conclusion (3 * q + 2) (Real.exp (-(3 * q + 2)))
      (Real.exp (-(3 * q + 2)))) := by
  obtain ⟨restored⟩ := front.prep.conclusion_of_selected hq out hweight
    hσone Cgeo hCgeo hchart hsmall hpoly
  exact ⟨front.refinement.conclusion
    (front.refinement.problem.conclusion_of_withKeep front.keep front.hkeep restored)⟩

end CommonKeepPositiveKernelPreparation
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCandidateStageDataConstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer allocatedFrozenCurrentGradeResetConstant

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
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    {ι κ χ η : Type} [Fintype ι] [Fintype κ] [Fintype χ] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "Vars" => {i : LayerSamplerVariables G I n B // keep i}
local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "Q" => P.withKeep keep hkeep

noncomputable def historyStageData_of_base_bound
    [instSymbolD : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [instSymbolF : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (r : ℕ) (hr : r ≤ s)
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (Bstage budget pMajor Rrank : ℝ) (C : ℕ)
    (v : ℝ) (hv : 2 ≤ v) (hbudget : budget ≤ v) (hBstage : Bstage ≤ v)
    (sliceCost : ℝ) (hSliceCost : sliceCost ≤ v)
    (hdense : ∀ z : P.productive, IsDenseCommonStrideBox (fun i : Vars => A.sides i.val)
      sliceCost ((Q).chart z).slice.integerPoints)
    (HMap l H Hθ : ℕ) (qNative : ℝ)
    (hHMap : 1 ≤ HMap) (hl : 0 < l) (hH : 1 ≤ H)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp v) (hlExp : (l : ℝ) ≤ Real.exp v)
    (hHExp : (H : ℝ) ≤ Real.exp v) (hHθExp : (Hθ : ℝ) ≤ Real.exp v)
    (hqNative : qNative ≤ v)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ω) : ℝ) ≤ v)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν) : ℝ) ≤ v)
    (hκ : (Fintype.card κ : ℝ) ≤ v) (hχ : (Fintype.card χ : ℝ) ≤ v)
    (hη : (Fintype.card η : ℝ) ≤ v)
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ v)
    (hsampler : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ v)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ v)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (vg : χ → Fmark.PolynomialSymbol (fun _ : Vars => 1))
    (hspan : span ℚ (Set.range vg) =
      (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ : Vars => 1) fast).toSubmodule)
    (hvg : ∀ i z, RationalHeightLE
      ((Fmark.polynomialSymbolBasis bF ν hF (fun _ : Vars => 1)).repr (vg i) z) H)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (hfactor : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : Vars => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.realification.polynomialOrbitCoordinates _ ((Q).candidate z).orbit))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (pSlice pTest pNative α : ℝ)
    (hSlice : allocatedCandidateStageSliceLog s m v ≤ pSlice)
    (hkept : ∀ i, keep i → Real.exp pSlice ≤ (A.sides i : ℝ))
    (hfrozen : ∀ i, ¬keep i → (A.sides i : ℝ) ≤ Real.exp pSlice)
    (hNative : v ≤ pNative)
    (hTest : OrdinaryPolynomialPhase.budget r ≤ pTest)
    (hMajor : productNiltestBudget pNative + pNative + v + 2 ≤ pMajor)
    (hα : α ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : A.NativeDetection r pSlice pTest pNative α)
    (hNmajor : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    HistoryStageData (χ := χ) (instSymbolD := instSymbolD) (instSymbolF := instSymbolF)
      (P := P) (keep := keep) (hkeep := hkeep) (bD := bD) (ω := ω) (hD := hD)
      (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W)
      eQ r 1 Bstage budget pMajor Rrank C := by
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv
  obtain ⟨hresetInput, hresetInput0⟩ := allocatedCandidateStage_reset_bounds s m hv
  obtain ⟨hlocalInput, hlocalV, _⟩ := allocatedCandidateStage_local_bounds s m hv
  obtain ⟨hSlice0, hresetSlice, hinterpolate, hthreshold⟩ :=
    allocatedCandidateStage_slice_bounds s m hv
  have hpSlice0 : 0 ≤ pSlice := hSlice0.trans hSlice
  have hlocalCost := allocatedCandidateStage_localCost_le_slice s m r hv hr
  have hVars : (Fintype.card Vars : ℝ) ≤ v :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le keep)).trans hsampler
  have hpNative0 : 0 ≤ pNative := hv0.trans hNative
  have hproduct0 : 0 ≤ productNiltestBudget pNative :=
    (sq_nonneg _).trans (productNiltestBudget_geometry hpNative0)
  have hNativeMajor : pNative ≤ pMajor := by linarith only [hproduct0, hv0, hMajor]
  have hproduct : productNiltestBudget pNative ≤ pMajor := by
    linarith only [hpNative0, hv0, hMajor]
  have hvMajor : v ≤ pMajor := by linarith only [hproduct0, hpNative0, hMajor]
  refine {
    hr := hr
    HMap := HMap
    l := l
    pMap := v
    hHMap := hHMap
    hl := hl
    hpMap := hv0
    hentries := hentries
    hsource := hsource
    htarget := htarget
    hHMapExp := hHMapExp
    hlExp := hlExp
    H := H
    p := allocatedCandidateStageResetInput s m v
    qNative := qNative
    hH := hH
    hp := hresetInput0
    hκ := hκ.trans hresetInput
    hVars := hVars.trans hresetInput
    hχ := hχ.trans hresetInput
    hHExp := hHExp.trans (Real.exp_le_exp.mpr hresetInput)
    hbracket := hbracket
    hcommon := allocatedCandidateStage_common_bound s m hv hbudget
    hmapSlow := ?_
    hallowance := ?_
    hNreset := ?_
    vg := vg
    hspan := hspan
    hvg := hvg
    hτ := hτ
    hξ := hξ
    hσone := hσone
    Cgeo := Cgeo
    hCgeo := hCgeo
    hchart := hchart
    hsmall := hsmall
    hpoly := hpoly
    pK := v
    Mbound := 1
    LongSide := Real.exp pSlice
    hpK := hv0
    hBstage := hBstage
    hJ := hJ
    hM := by norm_num
    hcap := fun j => (hsmall j).trans (by norm_num)
    hLong := Real.one_le_exp_iff.mpr hpSlice0
    hlong := ?_
    hthreshold := ?_
    hlength := ?_
    hfactor := hfactor
    Hθ := Hθ
    pLocal := allocatedCandidateStageLocalInput s m v
    hθ := hθ
    hpLocal := hlocalInput
    hLocalDim := hVars.trans hlocalV
    hLocalSize := ?_
    hLocalDen := ?_
    hNLocal := ?_
    pSlice := pSlice
    pTest := pTest
    pNative := pNative
    hpNative := hv.trans hNative
    hη := hη.trans hNative
    hNativeMajor := hNativeMajor
    hproduct := hproduct
    hdim := ?_
    hNmajor := hNmajor
    hRrank := hRrank
    hrank := hrank
    Bshort := Real.exp pSlice
    hBshort := Real.one_le_exp_iff.mpr hpSlice0
    hshort := hfrozen
    α := α
    hα := hα
    hdirect := hdirect
    hslice := ?_
    htest := hTest }
  · simpa only [pow_one] using allocatedCandidateStage_mapSlow_bound s m hv hqNative
  · simpa only [pow_one, Nat.cast_add, Nat.cast_one] using
      allocatedCandidateStage_allowance s m (Fintype.card (X ⊕ (Σ j, J j)))
        (Fintype.card (LayerSamplerVariables G I n B)) hv htags hsampler hbudget
  · intro i
    change Real.exp (allocatedCandidateStageResetLog s m v) ≤ (A.sides i.val : ℝ)
    exact (Real.exp_le_exp.mpr (hresetSlice.trans hSlice)).trans (hkept i.val i.property)
  · intro i hi
    have he : layerSamplerBox B U btag S i = (A.sides i : ℝ) := by cases i <;> rfl
    rw [he]
    exact hkept i hi
  · rw [mul_one, ← Real.exp_nat_mul]
    exact Real.exp_lt_exp.mpr (hthreshold.trans_le hSlice)
  · intro z
    apply ((Q).chart z).degree_lt_slice_length_of_dense s (hdense z)
    intro i
    apply (Real.exp_le_exp.mpr ?_).trans (hkept i.val i.property)
    have hi : sliceCost + (s : ℝ) + 1 ≤ v + (s : ℝ) + 1 := by
      linarith only [hSliceCost]
    exact hi.trans (hinterpolate.trans hSlice)
  · exact allocatedCandidateStage_localSize_bound s m (Fintype.card κ) Hθ hv hκ hHθExp
  · simpa only [Nat.cast_pow, allocatedCandidateStageResetLog] using
      allocatedCandidateStage_localDen_bound s m (Fintype.card κ) Hθ hv hκ hHθExp
  · intro i
    exact (Real.exp_le_exp.mpr (hlocalCost.trans hSlice)).trans (hkept i.val i.property)
  · simpa only [Fintype.card_sum] using htags.trans hvMajor
  · rw [Real.log_exp]
    exact max_le (hlocalCost.trans hSlice) le_rfl

noncomputable def historyStageData_of_native_source
    [instSymbolD : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [instSymbolF : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (r : ℕ) (hr : r ≤ s)
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (Bstage budget Rrank : ℝ) (C : ℕ)
    (v : ℝ) (hv : 2 ≤ v) (hbudget : budget ≤ v) (hBstage : Bstage ≤ v)
    (sliceCost : ℝ) (hSliceCost : sliceCost ≤ v)
    (hdense : ∀ z : P.productive, IsDenseCommonStrideBox (fun i : Vars => A.sides i.val)
      sliceCost ((Q).chart z).slice.integerPoints)
    (HMap l H Hθ : ℕ) (qNative : ℝ)
    (hHMap : 1 ≤ HMap) (hl : 0 < l) (hH : 1 ≤ H)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp v) (hlExp : (l : ℝ) ≤ Real.exp v)
    (hHExp : (H : ℝ) ≤ Real.exp v) (hHθExp : (Hθ : ℝ) ≤ Real.exp v)
    (hqNative : qNative ≤ v)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ω) : ℝ) ≤ v)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν) : ℝ) ≤ v)
    (hκ : (Fintype.card κ : ℝ) ≤ v) (hχ : (Fintype.card χ : ℝ) ≤ v)
    (hη : (Fintype.card η : ℝ) ≤ v)
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ v)
    (hsampler : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ v)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ v)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (vg : χ → Fmark.PolynomialSymbol (fun _ : Vars => 1))
    (hspan : span ℚ (Set.range vg) =
      (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ : Vars => 1) fast).toSubmodule)
    (hvg : ∀ i z, RationalHeightLE
      ((Fmark.polynomialSymbolBasis bF ν hF (fun _ : Vars => 1)).repr (vg i) z) H)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (hfactor : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : Vars => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.realification.polynomialOrbitCoordinates _ ((Q).candidate z).orbit))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (pSlice pTest sourceNative α : ℝ)
    (hSlice : allocatedCandidateStageSliceLog s m v ≤ pSlice)
    (hkept : ∀ i, keep i → Real.exp pSlice ≤ (A.sides i : ℝ))
    (hfrozen : ∀ i, ¬keep i → (A.sides i : ℝ) ≤ Real.exp pSlice)
    (hsourceNative : 0 ≤ sourceNative)
    (hTest : OrdinaryPolynomialPhase.budget r ≤ pTest)
    (hα : α ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : A.NativeDetection r pSlice pTest sourceNative α)
    (hNmajor : ∀ i, Real.exp (((allocatedCandidateNativeMajorBudget (sourceNative + v + 2) v) + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp (((allocatedCandidateNativeMajorBudget (sourceNative + v + 2) v) + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    HistoryStageData (χ := χ) (instSymbolD := instSymbolD) (instSymbolF := instSymbolF)
      (P := P) (keep := keep) (hkeep := hkeep) (bD := bD) (ω := ω) (hD := hD)
      (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W)
      eQ r 1 Bstage budget
      (allocatedCandidateNativeMajorBudget (sourceNative + v + 2) v) Rrank C := by
  exact P.historyStageData_of_base_bound keep hkeep bD ω hD bF ν hF hφ W
    eQ r hr Bstage budget (allocatedCandidateNativeMajorBudget (sourceNative + v + 2) v)
    Rrank C v hv hbudget hBstage sliceCost hSliceCost hdense
    HMap l H Hθ qNative hHMap hl hH hHMapExp hlExp hHExp hHθExp hqNative
    hentries hsource htarget hκ hχ hη htags hsampler hJ hbracket vg hspan hvg hθ hfactor
    hτ hξ hσone Cgeo hCgeo hchart hsmall hpoly
    pSlice pTest (sourceNative + v + 2) α hSlice hkept hfrozen
    (by linarith only [hsourceNative]) hTest (by rfl) hα
    (hdirect.mono_native (by linarith only [hv])) hNmajor hRrank hrank

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFrozenPrefixStageData
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer allocatedFrozenCurrentGradeResetConstant

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
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    {ι κ χ η : Type} [Fintype ι] [Fintype κ] [Fintype χ] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "Vars" => {i : LayerSamplerVariables G I n B // keep i}
local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "Q" => P.withKeep keep hkeep

noncomputable def historyStageData_of_prefix_bounds
    [instSymbolD : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [instSymbolF : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (r : ℕ) (hr : r ≤ s)
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (Cprimitive : ℕ) (x b Bstage Rrank : ℝ) (C : ℕ)
    (hx : 0 ≤ x) (hxb : x ≤ b) (hBstage : Bstage ≤ b)
    (sliceCost : ℝ) (hSliceCost : sliceCost ≤ (x + Cprimitive) ^ Cprimitive)
    (hdense : ∀ z : P.productive, IsDenseCommonStrideBox (fun i : Vars => A.sides i.val)
      sliceCost ((Q).chart z).slice.integerPoints)
    (HMap l H Hθ : ℕ) (qNative : ℝ)
    (hHMap : 1 ≤ HMap) (hl : 0 < l) (hH : 1 ≤ H)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hlExp : (l : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHExp : (H : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHθExp : (Hθ : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hqNative : qNative ≤ (x + Cprimitive) ^ Cprimitive)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ω) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hκ : (Fintype.card κ : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hχ : (Fintype.card χ : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hη : (Fintype.card η : ℝ) ≤ x)
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hsampler : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (vg : χ → Fmark.PolynomialSymbol (fun _ : Vars => 1))
    (hspan : span ℚ (Set.range vg) =
      (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ : Vars => 1) fast).toSubmodule)
    (hvg : ∀ i z, RationalHeightLE
      ((Fmark.polynomialSymbolBasis bF ν hF (fun _ : Vars => 1)).repr (vg i) z) H)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (hfactor : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : Vars => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.realification.polynomialOrbitCoordinates _ ((Q).candidate z).orbit))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (pTest sourceNative α : ℝ)
    (hsourceNative : 0 ≤ sourceNative)
    (hkept : ∀ i, keep i → Real.exp (allocatedCandidateStageSlice s m Cprimitive b) ≤ (A.sides i : ℝ))
    (hfrozen : ∀ i, ¬keep i → (A.sides i : ℝ) ≤ Real.exp (allocatedCandidateStageSlice s m Cprimitive b))
    (hTest : OrdinaryPolynomialPhase.budget r ≤ pTest)
    (hα : α ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : A.NativeDetection r (allocatedCandidateStageSlice s m Cprimitive b) pTest sourceNative α)
    (hNmajor : ∀ i, Real.exp ((allocatedCandidateNativeMajorBudget
      (sourceNative + allocatedCandidateStageBase s m Cprimitive b + 2)
      (allocatedCandidateStageBase s m Cprimitive b) + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((allocatedCandidateNativeMajorBudget
      (sourceNative + allocatedCandidateStageBase s m Cprimitive b + 2)
      (allocatedCandidateStageBase s m Cprimitive b) + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    HistoryStageData (χ := χ) (instSymbolD := instSymbolD) (instSymbolF := instSymbolF)
      (P := P) (keep := keep) (hkeep := hkeep) (bD := bD) (ω := ω) (hD := hD)
      (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W)
      eQ r 1 Bstage
        ((allocatedCandidateForwardControlInput s (Fintype.card η) b +
          allocatedCandidateTerminalControlConstant s m 1) ^
          allocatedCandidateTerminalControlConstant s m 1)
        (allocatedCandidateNativeMajorBudget
          (sourceNative + allocatedCandidateStageBase s m Cprimitive b + 2)
          (allocatedCandidateStageBase s m Cprimitive b)) Rrank C := by
  have hb0 : 0 ≤ b := hx.trans hxb
  have hprimitive := allocatedCandidateStage_primitive_le_base s m Cprimitive hx hxb
  obtain ⟨hv, hbBase⟩ := allocatedCandidateStageBase_bounds s m Cprimitive hb0
  have hcontrol := allocatedCandidateStage_control_le_base s m Cprimitive
    (Fintype.card η) hb0 (hη.trans hxb)
  have hslice := (allocatedCandidateStageSlice_bounds s m Cprimitive hb0).2
  have hexp := Real.exp_le_exp.mpr hprimitive
  exact P.historyStageData_of_native_source keep hkeep bD ω hD bF ν hF hφ W
    eQ r hr Bstage
    ((allocatedCandidateForwardControlInput s (Fintype.card η) b +
      allocatedCandidateTerminalControlConstant s m 1) ^
      allocatedCandidateTerminalControlConstant s m 1)
    Rrank C (allocatedCandidateStageBase s m Cprimitive b) hv hcontrol
    (hBstage.trans hbBase) sliceCost (hSliceCost.trans hprimitive) hdense
    HMap l H Hθ qNative hHMap hl hH
    (hHMapExp.trans hexp) (hlExp.trans hexp) (hHExp.trans hexp) (hHθExp.trans hexp)
    (hqNative.trans hprimitive) hentries (hsource.trans hprimitive) (htarget.trans hprimitive)
    (hκ.trans hprimitive) (hχ.trans hprimitive) ((hη.trans hxb).trans hbBase)
    (htags.trans hprimitive) (hsampler.trans hprimitive) (fun j => (hJ j).trans hprimitive)
    hbracket vg hspan hvg hθ hfactor hτ hξ hσone Cgeo hCgeo hchart hsmall hpoly
    (allocatedCandidateStageSlice s m Cprimitive b) pTest sourceNative α
    hslice hkept hfrozen hsourceNative hTest hα hdirect hNmajor hRrank hrank

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.degreeSourceProfileSiteNonempty
structure DegreeSourceProfile (degree : ℕ) (p : ℝ) (e : ℕ) where
  front : A.FrontSourceProfile degree p e
  inner : A.InnerSourceProfile degree
  input_inner : p ≤ inner.x
  trim_le_one : τ ≤ 1
  width_le_one : ∀ j, σ j ≤ 1
  polynomial_degree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)
  chartConstant : Fin m → ℝ
  chartConstant_nonneg : ∀ j, 0 ≤ chartConstant j
  chart_bound : ∀ j v,
    ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ chartConstant j * ‖v‖
  chart_small : ∀ j, chartConstant j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedFrontNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

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

namespace AllocatedExternalCandidateSampler.FrontSourceProfile

variable {degree e : ℕ} {p : ℝ} (source : A.FrontSourceProfile degree p e)

noncomputable def frontTermLog : ℝ :=
  2 * source.frontModelBudget + 2 * source.u + 4 * source.pModel + 34

noncomputable def frontCorrelationLoss : ℝ :=
  AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) +
    AllocatedExternalCandidateProblem.positiveKernelPreparationBinLog (2 * p) e +
    (source.frontModelBudget + 2) + 4

end AllocatedExternalCandidateSampler.FrontSourceProfile
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

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

namespace AllocatedExternalCandidateSampler.FrontSourceProfile

variable {degree e : ℕ} {p : ℝ} (source : A.FrontSourceProfile degree p e)

noncomputable def geometryBudget : ℝ :=
  source.familyParameter +
    (source.familyParameter + 2) ^
      RationalFilteredNilmanifold.positiveKernelNativeDescentExponent degree + 2

structure FactorGeometryBudget : Prop where
  geometry_two : 2 ≤ source.geometryBudget
  geometry_input : source.familyParameter ≤ source.geometryBudget
  geometry_descent :
    (source.familyParameter + 2) ^
      RationalFilteredNilmanifold.positiveKernelNativeDescentExponent degree ≤
        source.geometryBudget
  factor_input : source.familyParameter ≤ source.factorBudget
  factor_nonneg : 0 ≤ source.factorBudget
  vertical_nonneg : 0 ≤ 3 * source.familyParameter + 1
  native_vertical : max source.nativeBudget 3 ≤ 3 * source.familyParameter + 1
  local_vertical :
    AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) +
      source.frontCorrelationLoss + 1 ≤ 3 * source.familyParameter + 1
  vertical_factor : verticalDecompositionBudget (3 * source.familyParameter + 1) ≤
    source.factorBudget
  correlation_factor : source.frontCorrelationLoss +
    verticalDecompositionBudget (3 * source.familyParameter + 1) + 2 ≤ source.factorBudget

end AllocatedExternalCandidateSampler.FrontSourceProfile
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
  CertifiedFullChartFiniteHistory.outer allocatedFrozenCurrentGradeResetConstant

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

namespace AllocatedExternalCandidateProblem.AxisFreezing

variable {cost massThreshold scoreThreshold : ℝ}
    {P0 : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {keepOld : P0.productive → LayerSamplerVariables G I n B → Prop}
    {shortCost : ℝ} (freezing : P0.AxisFreezing keepOld shortCost)
    (commonKeep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : freezing.problem.productive,
      (freezing.problem.chart z).keep = commonKeep)
    {ι κ χ η : Type} [Fintype ι] [Fintype κ] [Fintype χ] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "Vars" => {i : LayerSamplerVariables G I n B // commonKeep i}
local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)

noncomputable def historyStageData_of_zero_restricted_factors
    [instSymbolD : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [instSymbolF : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (r : ℕ) (hr : r ≤ s)
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (Cprimitive : ℕ) (x b Bstage Rrank : ℝ) (C : ℕ)
    (hx : 0 ≤ x) (hxb : x ≤ b) (hBstage : Bstage ≤ b)
    (hcost : cost ≤ (x + Cprimitive) ^ Cprimitive)
    (HMap l H Hθ : ℕ) (qNative : ℝ)
    (hHMap : 1 ≤ HMap) (hl : 0 < l) (hH : 1 ≤ H)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hlExp : (l : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHExp : (H : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHθExp : (Hθ : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hqNative : qNative ≤ (x + Cprimitive) ^ Cprimitive)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ω) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hκ : (Fintype.card κ : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hχ : (Fintype.card χ : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hη : (Fintype.card η : ℝ) ≤ x)
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hsampler : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (vg : χ → Fmark.PolynomialSymbol (fun _ : Vars => 1))
    (hspan : span ℚ (Set.range vg) =
      (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ : Vars => 1) fast).toSubmodule)
    (hvg : ∀ i z, RationalHeightLE
      ((Fmark.polynomialSymbolBasis bF ν hF (fun _ : Vars => 1)).repr (vg i) z) H)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hstageLong : ∀ z : P0.productive, ∀ i, keepOld z i → initialLong i)
    (hOriginal : ∀ z : P0.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i : LayerSamplerVariables G I n B // initialLong i} => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.weightedAdaptedRealChartHom (fun _ : (P0.chart z).Variables => 1)
        (fun _ : {i : LayerSamplerVariables G I n B // initialLong i} => 1)
        ((P0.chart z).axisPolynomial initialLong (fun _ => 0))
        ((P0.chart z).axisPolynomial_support initialLong (fun _ => 0))
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P0.candidate z).orbit)))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (pTest sourceNative α : ℝ)
    (hsourceNative : 0 ≤ sourceNative)
    (hkept : ∀ i, commonKeep i → Real.exp (allocatedCandidateStageSlice s m Cprimitive b) ≤ (A.sides i : ℝ))
    (hfrozen : ∀ i, ¬commonKeep i → (A.sides i : ℝ) ≤ Real.exp (allocatedCandidateStageSlice s m Cprimitive b))
    (hTest : OrdinaryPolynomialPhase.budget r ≤ pTest)
    (hα : α ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : A.NativeDetection r (allocatedCandidateStageSlice s m Cprimitive b) pTest sourceNative α)
    (hNmajor : ∀ i, Real.exp ((allocatedCandidateNativeMajorBudget
      (sourceNative + allocatedCandidateStageBase s m Cprimitive b + 2)
      (allocatedCandidateStageBase s m Cprimitive b) + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((allocatedCandidateNativeMajorBudget
      (sourceNative + allocatedCandidateStageBase s m Cprimitive b + 2)
      (allocatedCandidateStageBase s m Cprimitive b) + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    HistoryStageData (χ := χ) (instSymbolD := instSymbolD) (instSymbolF := instSymbolF)
      (P := freezing.problem) (keep := commonKeep) (hkeep := hkeep) (bD := bD) (ω := ω) (hD := hD)
      (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W)
      eQ r 1 Bstage
        ((allocatedCandidateForwardControlInput s (Fintype.card η) b +
          allocatedCandidateTerminalControlConstant s m 1) ^
          allocatedCandidateTerminalControlConstant s m 1)
        (allocatedCandidateNativeMajorBudget
          (sourceNative + allocatedCandidateStageBase s m Cprimitive b + 2)
          (allocatedCandidateStageBase s m Cprimitive b)) Rrank C := by
  exact freezing.problem.historyStageData_of_prefix_bounds
    commonKeep hkeep bD ω hD bF ν hF hφ W eQ r hr
    Cprimitive x b Bstage Rrank C hx hxb hBstage
    cost hcost (fun z => freezing.withKeep_slice_dense commonKeep hkeep z)
    HMap l H Hθ qNative hHMap hl hH hHMapExp hlExp hHExp hHθExp
    hqNative hentries hsource htarget hκ hχ hη htags hsampler hJ
    hbracket vg hspan hvg hθ
    (fun z => freezing.withKeep_nativeFactors_of_zero_restriction commonKeep hkeep
      initialLong hstageLong bD ω hD qNative l W z
      (hOriginal z))
    hτ hξ hσone Cgeo hCgeo hchart hsmall hpoly
    pTest sourceNative α hsourceNative hkept hfrozen hTest hα hdirect hNmajor hRrank hrank

end AllocatedExternalCandidateProblem.AxisFreezing
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidatePrimitiveFrontDescentData
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
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
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M t f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked observable weight
      cost massThreshold scoreThreshold)

structure PrimitiveFrontQuotientData {p : ℝ} {e : ℕ}
    (source : A.DegreeSourceProfile s p e) where
  front : P.CommonKeepPositiveKernelPreparation p e
  retained : Finset A.Path
  retained_subset : retained ⊆ front.prep.selected.retained
  mass_pos : 0 < A.law.mass retained
  mass : Real.exp (-source.front.familyParameter) ≤ A.law.mass retained
  family_nonneg : 0 ≤ source.front.familyParameter
  source_geometry : D.GeometryComplexityLE source.front.familyParameter
  mark_geometry : FmarkNative.GeometryComplexityLE source.front.familyParameter
  mark_height : ∀ i j, rationalLogHeight
    (FmarkNative.basis.repr (φ (D.basis j)) i) ≤ source.front.familyParameter
  pivot_card : (Fintype.card (KernelProjectionPresentPivot front.prep.selected.code) : ℝ) ≤
    source.front.familyParameter
  rawFamily : AllocatedExternalCandidateSpatialNativeFamily A E A.Path
    (KernelProjectionPresentPivot front.prep.selected.code) D FmarkNative.filtration φ marked
    front.keep cost source.front.familyParameter (positiveKernelPreparationParameter (2 * p))
    (max source.front.nativeBudget 3) source.front.frontCorrelationLoss
    (Real.exp (max source.front.nativeBudget 3)) (Real.exp (max source.front.nativeBudget 3))
    ⟨Real.exp (max source.front.nativeBudget 3), Real.exp_nonneg _⟩
  sourceChart_eq : rawFamily.sourceChart = front.problem.precenterChart front.prep.positive_mass
  sourceCandidate_heq : ∀ a, HEq (rawFamily.sourceCandidate a)
    (front.problem.precenterCandidate front.prep.positive_mass a)
  frequencies_eq : rawFamily.η = (fun k => front.prep.early.eta
    (kernelProjectionSelectedPivot front.prep.selected.code k))
  correlation : ∀ a ∈ retained, ∀ k,
    Real.exp (-source.front.frontCorrelationLoss) ≤ ‖rawFamily.correlation a k‖
  path_eq : ∀ a ∈ retained, (rawFamily.sourceChart a).path = a
  center_eq : ∀ a, (rawFamily.sourceChart a).centerLift = P.centerLift
  score : ∀ a ∈ retained, Real.exp (-positiveKernelPreparationParameter (2 * p)) ≤
    (rawFamily.sourceCandidate a).score (fun x => (front.prep.selected.tests x).observable) weight
  ideal_killed : ∀ x ∈ front.prep.nativeQuotientIdeal, φ x = 0
  quotientDimension : ℕ
  quotientDimension_le : quotientDimension ≤ d
  quotient : RationalFilteredNilmanifold (L ⧸ front.prep.nativeQuotientIdeal) s quotientDimension
  quotient_filtration : quotient.filtration = D.filtration.quotientLie
    front.prep.nativeQuotientIdeal front.prep.nativeQuotientIdeal_terminal
  quotient_lattice : quotient.lattice = D.lattice.map (D.filtration.quotientStepHom
    front.prep.nativeQuotientIdeal front.prep.nativeQuotientIdeal_terminal)
  quotient_geometry : quotient.GeometryComplexityLE
    ((source.front.familyParameter + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s)
  quotient_projection : ∀ i j, rationalLogHeight (quotient.basis.repr
    (lieQuotientMap front.prep.nativeQuotientIdeal (D.basis j)) i) ≤
      (source.front.familyParameter + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s
  quotient_mark : ∀ i j, rationalLogHeight (FmarkNative.basis.repr
    (quotientInducedMark front.prep.nativeQuotientIdeal φ ideal_killed (quotient.basis j)) i) ≤
      quotientInducedMarkHeightBudget ((source.front.familyParameter + 2) ^
        RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s)
  descent :
    letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ front.prep.nativeQuotientIdeal))
    letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ front.prep.nativeQuotientIdeal)) :=
      IsModuleTopology.topologicalAddGroup ℝ _
    letI := realification_moduleTopology_t2 quotient.basis
    ∃ descended : (X → ℤ) → quotient.Niltest (fullTaggedVariableWeight (X := X) J),
      (∀ x, (descended x).UnitIntervalValued) ∧
      (∀ x y, ‖(descended x).observable y‖ ≤ 1) ∧
      (∀ x, (descended x).ComplexityLE
        ((source.front.familyParameter + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s)) ∧
      (∀ x, letI := quotient.metricSpace;
        LipschitzWith
          ⟨Real.exp ((source.front.familyParameter + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s),
            Real.exp_nonneg _⟩ (descended x).observable) ∧
      (∀ x (g : D.RealGroup), (descended x).observable (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := quotient.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap front.prep.nativeQuotientIdeal) g)) =
          (front.prep.selected.tests x).observable (QuotientGroup.mk g)) ∧
      (∀ x y η, (∀ z, ‖observable x z - observable y z‖ ≤ η) →
        ∀ z, ‖(descended x).observable z - (descended y).observable z‖ ≤ η) ∧
      ∀ entropy : ℝ → ℝ,
        (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ count : ℕ, (count : ℝ) ≤ entropy η ∧
          ∃ rep : Fin count → integerBox N,
            ∀ x ∈ integerBox N, ∃ i, ∀ y,
              ‖observable x y - observable (rep i).val y‖ ≤ η) →
        ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ count : ℕ, (count : ℝ) ≤ entropy η ∧
          ∃ rep : Fin count → integerBox N,
            ∀ x ∈ integerBox N, ∃ i, ∀ y,
              ‖(descended x).observable y - (descended (rep i).val).observable y‖ ≤ η

namespace PrimitiveFrontQuotientData

variable {FmarkNative P} {p : ℝ} {e : ℕ} {source : A.DegreeSourceProfile s p e}
    (data : P.PrimitiveFrontQuotientData FmarkNative source)

noncomputable def family := data.rawFamily.withFrequencies
  (fun k => data.front.prep.early.eta
    (kernelProjectionSelectedPivot data.front.prep.selected.code k)) data.frequencies_eq

@[simp] theorem family_eta : data.family.η =
    (fun k => data.front.prep.early.eta
      (kernelProjectionSelectedPivot data.front.prep.selected.code k)) := rfl

@[simp] theorem family_sourceChart : data.family.sourceChart = data.rawFamily.sourceChart := rfl

@[simp] theorem family_sourceCandidate : data.family.sourceCandidate = data.rawFamily.sourceCandidate := rfl

@[simp] theorem family_correlation (a : A.Path)
    (k : KernelProjectionPresentPivot data.front.prep.selected.code) :
    data.family.correlation a k = data.rawFamily.correlation a k := rfl

end PrimitiveFrontQuotientData

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffinePhysicalBoundsSuccessor
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
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

namespace AllocatedExternalCandidateProblem

variable {L M : Type} {nMarkedBasis : ℕ} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (c : Basis (Fin nMarkedBasis) ℚ M)
    (ν : Fin nMarkedBasis → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i}))
    {η : Type} [Fintype η]
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (Fmark.filtration.AssociatedGraded ⧸
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule)))
    (lift : (Fmark.filtration.AssociatedGraded ⧸
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule) →ₗ[ℚ]
        Fmark.filtration.AssociatedGraded)
    (Bphase budget pAffine pFull separation : ℝ)
    (history : CertifiedFullChartFiniteHistory Fmark.filtration c ν hF J
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule
      basis lift
      (Fmark.filtration.realPolynomialSymbolHom c ν hF (fullTaggedVariableWeight J)
        (Fmark.filtration.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked))
      Set.univ U poly N Bphase (s + 1))
    (data : P.AffinePhysicalTerminalData c ν hF hφ W basis lift
      Bphase budget pAffine pFull 4 history separation)
    (hcost : Real.exp cost ≤ separation)

variable {Fmark φ hφ P W c ν hF basis lift Bphase budget pAffine pFull separation history data hcost}

noncomputable def AffinePhysicalTerminalData.successorInputsOfBounds
    (data : P.AffinePhysicalTerminalData c ν hF hφ W basis lift
      Bphase budget pAffine pFull 4 history separation)
    (p0 : ℝ) (hp0 : 0 ≤ p0) (hpFull : 0 ≤ pFull)
    (hseparation : separation = Real.exp (candidatePrimitiveFreezingCutoff s 1
      (allocatedAffineCanonicalBudget s p0 pFull)))
    (hDgeo : D.GeometryComplexityLE p0) (hFgeo : Fmark.GeometryComplexityLE p0)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p0)
    (hmarkedDim : (nMarkedBasis : ℝ) ≤ p0)
    (hsection : ∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p0)
    (hσ1 : ∀ j, σ j ≤ 1)
    (Hchart : Fin m → ℝ) (hHchart : ∀ j, 0 ≤ Hchart j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Hchart j * ‖v‖)
    (hsmall : ∀ j, Hchart j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p0)
    (hscore : Real.exp (-p0) ≤ scoreThreshold)
    (hcost0 : cost ≤ p0)
    (hmass : Real.exp (-p0) ≤
      Real.exp (-((2 * certifiedAffineCenterBudget pAffine + 3) ^ 3)) * massThreshold)
    (ω : Fin d → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (D.basis '' {i | j ≤ ω i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hD) ω W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1) (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p0)
    (hLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    {Generator : Type} [Fintype Generator]
    (v : Generator → D.filtration.AssociatedGraded)
    (hspan : span ℚ (Set.range v) = W.toSubmodule)
    (hcount : (Fintype.card Generator : ℝ) ≤ p0)
    (hcForward : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p0)
    (hmark : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p0)
    (hv : ∀ i j, rationalLogHeight
      ((D.filtration.associatedGradedBasis D.basis ω hD).repr (v i) j) ≤ p0)
    (htop : ∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) → φ x = 0 → x = 0)
    {e : ℕ}
    (hnet : ∀ accuracy : ℝ, 0 < accuracy → accuracy ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((p0 + Real.log (1 / accuracy) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖observable x y - observable (centers i).val y‖ ≤ accuracy)
    (outputCost : ℝ)
    (lowerIH : A.DegreeGlobalizationAt (E := E) weight s
      (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2)
      (finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
        (allocatedAffineCanonicalBudget s p0 pFull)) outputCost) :
    data.SuccessorInputs (allocatedAffineCanonicalBudget s p0 pFull) e outputCost := by
  have bounds := allocatedAffineCanonicalBudget_bounds s hp0 hpFull
  refine {
    nonnegative := bounds.nonnegative
    separation_eq := hseparation
    source_geometry := hDgeo.mono D bounds.input
    retained_count := ?_
    marked_dimension := hmarkedDim.trans bounds.input
    section_height := fun i j => (hsection i j).trans bounds.input
    physical_budget := bounds.physical
    scale_le_one := hσ1
    chart_bound := Hchart
    chart_nonnegative := hHchart
    chart_norm := hchart
    chart_small := hsmall
    polynomial_degree := hpoly
    weight_bound := fun x => (hweight x).trans (Real.exp_le_exp.mpr bounds.input)
    score_bound := (Real.exp_le_exp.mpr (neg_le_neg bounds.input)).trans hscore
    cost_bound := hcost0.trans bounds.input
    mass_log := p0
    mass_log_bound := bounds.input
    mass_bound := hmass
    weights := ω
    adapted := hD
    graded := hW
    surjective := hsurj
    width_le_one := hξ1
    lipschitz_constant := ℓ
    lipschitz_bound := hℓ.trans (Real.exp_le_exp.mpr bounds.input)
    lipschitz := hLip
    positive := hpositive
    marked_geometry := hFgeo.mono Fmark bounds.input
    Generator := Generator
    generator_fintype := inferInstance
    generators := v
    generator_span := hspan
    generator_count := hcount.trans bounds.input
    marked_basis_height := fun i j => (hcForward i j).trans bounds.input
    mark_height := fun i j => (hmark i j).trans bounds.input
    generator_height := fun i j => (hv i j).trans bounds.input
    top_kernel := htop
    net := ?_
    lower_degree := lowerIH }
  · exact (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans
      (hvariables.trans bounds.input)
  · intro accuracy hacc hacc1
    obtain ⟨count, hcount, centers, hcenters⟩ := hnet accuracy hacc hacc1
    refine ⟨count, hcount.trans (Real.exp_le_exp.mpr ?_), centers, hcenters⟩
    have hlog : 0 ≤ Real.log (1 / accuracy) :=
      Real.log_nonneg ((one_le_div hacc).mpr hacc1)
    exact pow_le_pow_left₀ (by positivity) (by linarith [bounds.input]) e

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end


