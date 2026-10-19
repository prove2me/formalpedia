-- Prove2me | Definitions.Def_OAIE3v2B275
-- name    : OAIE3v2B275
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T07:17:19.19417+00:00
-- url     : https://prove2.me/theorems/d43a5d95-6c9a-40d5-8156-3bf56800a4a5
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 287 of 311
-- statement:
--   Definitions bundle 287 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B306`, `OAIE3v2B307`, `OAIE3v2B270`, `OAIE3v2B271` of this split.
--
--   Modules: `Dynamics/AllocatedCandidateNestedTerminalUniformLayersBudget.lean`, `Dynamics/AllocatedCandidateStageScalarBudget.lean`, `Estimates/AllocatedCandidateStageDataConstruction.lean`, `Estimates/AllocatedExternalCandidateLocalFixedCenterFront.lean`, `Estimates/AllocatedExternalCandidatePrimitiveFrontDescentData.lean`, `Estimates/AllocatedExternalCandidateRealThreshold.lean`, `Fourier/AllocatedExternalCandidateSpatialNativeFrequencyTransport.lean`, `Lattices/CertifiedAffineNormalizedBudget.lean`, `Linear/AllocatedExternalCandidateCommonKeepPositiveKernelPreparation.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B306
import Definitions.Def_OAIE3v2B307
import Definitions.Def_OAIE3v2B270
import Definitions.Def_OAIE3v2B271

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateRealThreshold
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace AxisFreezing

variable {P} {bound : ℝ}
    (freezing : P.AxisFreezing (P.realThresholdKeep bound) (candidateSideCutoffCost bound))

theorem realThreshold_long (z : P.productive) (i : LayerSamplerVariables G I n B)
    (hi : (freezing.problem.chart z).keep i) :
    (candidateSideCutoff bound : ℝ) ≤ layerSamplerBox B U b S i := by
  have hs : candidateSideCutoff bound ≤ A.sides i := hi.2
  have he : layerSamplerBox B U b S i = (A.sides i : ℝ) := by
    cases i <;> rfl
  rw [he]
  exact_mod_cast hs

theorem realThreshold_strict_long (z : P.productive) (i : LayerSamplerVariables G I n B)
    (hi : (freezing.problem.chart z).keep i) :
    bound < layerSamplerBox B U b S i :=
  (lt_candidateSideCutoff bound).trans_le (freezing.realThreshold_long z i hi)

end AxisFreezing

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedCandidateStageScalarBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open NilpotentLieFiltration

noncomputable def allocatedCandidateStageResetLog (s m : ℕ) (v : ℝ) : ℝ :=
  (allocatedCandidateStageResetInput s m v + allocatedFrozenCurrentGradeResetConstant s 1) ^
    allocatedFrozenCurrentGradeResetConstant s 1

noncomputable def allocatedCandidateStageLocalInput (s m : ℕ) (v : ℝ) : ℝ :=
  allocatedCandidateStageResetLog s m v + v ^ 2 + 2 * v + 2

noncomputable def allocatedCandidateStageSliceLog (s m : ℕ) (v : ℝ) : ℝ :=
  (allocatedCandidateStageLocalInput s m v + (s + 401 : ℕ)) ^ (s + 401) +
    2 * (v + 2) ^ 9 + v + s + 4

attribute [local irreducible] allocatedFrozenCurrentGradeResetConstant
  allocatedCandidateStageResetLog allocatedCandidateStageLocalInput allocatedCandidateStageSliceLog

theorem allocatedCandidateStage_resetLog_nonneg (s m : ℕ) {v : ℝ} (hv : 2 ≤ v) :
    0 ≤ allocatedCandidateStageResetLog s m v := by
  unfold allocatedCandidateStageResetLog
  exact pow_nonneg (add_nonneg (allocatedCandidateStage_reset_bounds s m hv).2
    (Nat.cast_nonneg _)) _

theorem allocatedCandidateStage_local_bounds (s m : ℕ) {v : ℝ} (hv : 2 ≤ v) :
    1 ≤ allocatedCandidateStageLocalInput s m v ∧
    v ≤ allocatedCandidateStageLocalInput s m v ∧
    allocatedCandidateStageResetLog s m v ≤ allocatedCandidateStageLocalInput s m v := by
  have hR := allocatedCandidateStage_resetLog_nonneg s m hv
  have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
  unfold allocatedCandidateStageLocalInput
  exact ⟨by linarith only [hR, hv, hv2], by linarith only [hR, hv, hv2],
    by linarith only [hv, hv2]⟩

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

structure HistoryStageData
    [instSymbolD : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [instSymbolF : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (r a : ℕ)
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (Bstage budget pMajor Rrank : ℝ) (C : ℕ) : Type where
  hr : r ≤ s
  HMap : ℕ
  l : ℕ
  pMap : ℝ
  hHMap : 1 ≤ HMap
  hl : 0 < l
  hpMap : 0 ≤ pMap
  hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap
  hsource : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ω) : ℝ) ≤ pMap
  htarget : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν) : ℝ) ≤ pMap
  hHMapExp : (HMap : ℝ) ≤ Real.exp pMap
  hlExp : (l : ℝ) ≤ Real.exp pMap
  H : ℕ
  p : ℝ
  qNative : ℝ
  hH : 1 ≤ H
  hp : 0 ≤ p
  hκ : (Fintype.card κ : ℝ) ≤ p
  hVars : (Fintype.card Vars : ℝ) ≤ p
  hχ : (Fintype.card χ : ℝ) ≤ p
  hHExp : (H : ℝ) ≤ Real.exp p
  hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H
  hcommon : Real.exp budget * Real.exp ((pMap + 2) ^ 4) ≤ Real.exp p
  hmapSlow : Real.exp ((pMap + 2) ^ 3 + qNative) ≤ Real.exp ((p + 2) ^ a)
  hallowance :
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s * Real.exp budget *
        (((m + 1 : ℕ) : ℝ) * ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) ^ s)
        ≤ Real.exp ((p + 2) ^ a)
  hNreset : ∀ i : Vars, Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
      allocatedFrozenCurrentGradeResetConstant s a) ≤ (A.sides i.val : ℝ)
  vg : χ → Fmark.PolynomialSymbol (fun _ : Vars => 1)
  hspan : span ℚ (Set.range vg) = (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ : Vars => 1) fast).toSubmodule
  hvg : ∀ i z, RationalHeightLE ((Fmark.polynomialSymbolBasis bF ν hF (fun _ : Vars => 1)).repr (vg i) z) H
  hτ : τ ≤ 1
  hξ : ξ ≤ 1
  hσone : ∀ j, σ j ≤ 1
  Cgeo : Fin m → ℝ
  hCgeo : ∀ j, 0 ≤ Cgeo j
  hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖
  hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8
  hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)
  pK : ℝ
  Mbound : ℝ
  LongSide : ℝ
  hpK : 0 ≤ pK
  hBstage : Bstage ≤ pK
  hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ pK
  hM : 0 ≤ Mbound
  hcap : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ Mbound
  hLong : 1 ≤ LongSide
  hlong : ∀ i, keep i → LongSide ≤ layerSamplerBox B U btag S i
  hthreshold : Real.exp ((pK + 2) ^ 9) ^ 2 * Mbound < LongSide
  hlength : ∀ z : P.productive, ∀ i, s < ((Q).chart z).slice.length i
  hfactor : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : Vars => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.realification.polynomialOrbitCoordinates _ ((Q).candidate z).orbit)
  Hθ : ℕ
  pLocal : ℝ
  hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ
  hpLocal : 1 ≤ pLocal
  hLocalDim : (Fintype.card Vars : ℝ) ≤ pLocal
  hLocalSize : (Fintype.card κ : ℝ) * Hθ * Real.exp
      ((p + allocatedFrozenCurrentGradeResetConstant s a) ^ allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal
  hLocalDen : ((Hθ ^ Fintype.card κ : ℕ) : ℝ) * Real.exp
      ((p + allocatedFrozenCurrentGradeResetConstant s a) ^ allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal
  hNLocal : ∀ i : Vars, Real.exp ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) ≤ (A.sides i.val : ℝ)
  pSlice : ℝ
  pTest : ℝ
  pNative : ℝ
  hpNative : 2 ≤ pNative
  hη : (Fintype.card η : ℝ) ≤ pNative
  hNativeMajor : pNative ≤ pMajor
  hproduct : productNiltestBudget pNative ≤ pMajor
  hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor
  hNmajor : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ)
  hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank
  hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)
  Bshort : ℝ
  hBshort : 1 ≤ Bshort
  hshort : ∀ i, ¬keep i → (A.sides i : ℝ) ≤ Bshort
  α : ℝ
  hα : α ≤ (9 / 10 : ℝ) * massThreshold
  hdirect : A.NativeDetection r pSlice pTest pNative α
  hslice : max ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) (Real.log Bshort) ≤ pSlice
  htest : OrdinaryPolynomialPhase.budget r ≤ pTest

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CertifiedAffineNormalizedBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct

attribute [local irreducible] HasCommonRefilteredOrbitFactors polynomialOrbitCoordinates
  weightedAdaptedRealChartHom

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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}

namespace Refinement

variable {newCost newMass newScore : ℝ}
    (refinement : P.Refinement newCost newMass newScore)

theorem nativeFactors
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (hOriginal : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
        (fun i : (P.chart z).Variables => (A.sides i.val : ℝ)) q l W
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P.candidate z).orbit))
    (z : refinement.problem.productive) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : (refinement.problem.chart z).Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (refinement.problem.candidate z).orbit) :=
  hOriginal ⟨z.val, refinement.subset z.property⟩

end Refinement

namespace CertifiedThresholdAffineRefinement

variable {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p separation : ℝ}
    (selected : P.CertifiedThresholdAffineRefinement K p separation)

theorem nativeFactors
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (hOriginal : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
        (fun i : (P.chart z).Variables => (A.sides i.val : ℝ)) q l W
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P.candidate z).orbit))
    (z : selected.problem.productive) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : (selected.problem.chart z).Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (selected.problem.candidate z).orbit) :=
  selected.affine.refinement.nativeFactors bD ω hD q l W
    (fun a => selected.freezing.problem_nativeFactors bD ω hD q l W a (hOriginal a)) z

end CertifiedThresholdAffineRefinement
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct

attribute [local irreducible] HasCommonRefilteredOrbitFactors polynomialOrbitCoordinates
  weightedAdaptedRealChartHom

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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}

namespace CertifiedThresholdAffineRefinement

variable {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p separation : ℝ}
    (selected : P.CertifiedThresholdAffineRefinement K p separation)

theorem nativeFactors_of_zero_restriction
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hsub : ∀ z i, P.realThresholdKeep separation z i → initialLong i)
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (hzero : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
        (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
        (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
          (fun _ : {i // initialLong i} => 1)
          ((P.chart z).axisPolynomial initialLong (fun _ => 0))
          ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
          (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
            (P.candidate z).orbit)))
    (z : selected.problem.productive) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : (selected.problem.chart z).Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (selected.problem.candidate z).orbit) :=
  selected.affine.refinement.nativeFactors bD ω hD q l W
    (fun a => selected.freezing.problem_nativeFactors_of_zero_restriction
      initialLong hsub bD ω hD q l W a (hzero a)) z

theorem withKeep_nativeFactors_of_zero_restriction
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : selected.problem.productive, (selected.problem.chart z).keep = keep)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hsub : ∀ z i, P.realThresholdKeep separation z i → initialLong i)
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (hzero : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
        (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
        (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
          (fun _ : {i // initialLong i} => 1)
          ((P.chart z).axisPolynomial initialLong (fun _ => 0))
          ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
          (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
            (P.candidate z).orbit)))
    (z : selected.problem.productive) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        ((selected.problem.withKeep keep hkeep).candidate z).orbit) :=
  (selected.problem.candidate z).hasCommonRefilteredOrbitFactors_withKeep
    keep (hkeep z) bD ω hD q l W (selected.nativeFactors_of_zero_restriction initialLong hsub bD ω hD q l W hzero z)

end CertifiedThresholdAffineRefinement
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedCandidateNestedTerminalUniformLayersBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def uniformLayersAffinePolynomial : Polynomial ℕ :=
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + ((X + 2) ^ 2 + 2) ^ 63
  2 * X + (Q + 2) ^ 10 + (Q + 2) ^ 8 + 1

attribute [local irreducible] certifiedAffineCenterBudget
  preparedFiniteForwardParameter preparedFiniteForwardWork preparedFiniteForwardCap
  preparedFiniteForwardBranch preparedFiniteForwardCumulative

end Erdos3.VectorPolynomial

end

end OAI
end

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

theorem positiveKernelPreparationExponent_ge_two :
    2 ≤ positiveKernelPreparationExponent :=
  (Classical.choose_spec (exists_externalFamilyPrecenterProjectionData.{0, 0, 0})).1

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem

noncomputable def positiveKernelMarkovPrecisionParameter (p : ℝ) (e : ℕ) : ℝ :=
  (positiveKernelPreparationParameter p + positiveKernelPreparationBinLog p e) +
    (2 * positiveKernelPreparationParameter p + positiveKernelPreparationBinLog p e + 4) +
    (p + positiveKernelPreparationParameter p) + 2

end Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateLocalFixedCenterFront
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
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

namespace PrecenterKernelSelection
variable {P} {p q : ℝ}
    {T : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)}
    {early : ExternalFamilyPrecenterProjectionData T p q}
    {top : Submodule ℚ L} {htop : top ≤ D.filtration.layer s}
    {hpos : 0 < A.law.mass P.productive}
    (selected : P.PrecenterKernelSelection early top htop hpos)

omit [∀ j, Fintype (J j)] in

theorem contracted_member_net {Bin : Type} (representative : Bin → integerBox N)
    {ε : ℝ}
    (hnet : ∀ x : integerBox N, ∃ i, ∀ y,
      ‖(T x.val).observable y - (T (representative i).val).observable y‖ ≤ ε) :
    ∀ f (x : integerBox N), ∃ i, ∀ y,
      ‖(early.U f x.val).observable y - (early.U f (representative i).val).observable y‖ ≤ ε := by
  intro f x
  obtain ⟨i, hi⟩ := hnet x
  exact ⟨i, early.contractive f x.val (representative i).val ε hi⟩

end PrecenterKernelSelection
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedExternalCandidateSpatialNativeFrequencyTransport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {A} {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ t : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

variable (eta : Pivot → LG →ₗ[ℚ] ℚ) (h : F.η = eta)

@[simp] theorem withFrequencies_localTest (a : Ω) (j : Pivot) :
    (F.withFrequencies eta h).localTest a j = F.localTest a j := rfl

@[simp] theorem withFrequencies_jointOrbit (a : Ω) :
    (F.withFrequencies eta h).jointOrbit a = F.jointOrbit a := rfl

@[simp] theorem withFrequencies_physicalBox (a : Ω)
    (u : integerBox (fun i : {i // keep i} => A.sides i.val)) :
    (F.withFrequencies eta h).physicalBox a u = F.physicalBox a u := rfl

@[simp] theorem withFrequencies_sitePhysicalBox (a : Ω) (site : A.Site) :
    (F.withFrequencies eta h).sitePhysicalBox a site = F.sitePhysicalBox a site := rfl

@[simp] theorem withFrequencies_correlation (a : Ω) (j : Pivot) :
    (F.withFrequencies eta h).correlation a j = F.correlation a j := rfl

end AllocatedExternalCandidateSpatialNativeFamily

end

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
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.PositiveKernelPreparation

variable {cost massThreshold scoreThreshold p : ℝ} {e : ℕ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    (prep : P.PositiveKernelPreparation p e)

noncomputable abbrev nativeQuotientIdeal : LieIdeal ℚ L :=
  D.filtration.pivotAnnihilatorIdeal φ
    (fun k => prep.early.eta (kernelProjectionSelectedPivot prep.selected.code k))
    (Finset.univ : Finset (KernelProjectionPresentPivot prep.selected.code)).toList

theorem nativeQuotientIdeal_terminal :
    D.filtration.layer (s + 1) ≤ prep.nativeQuotientIdeal.toSubmodule := by
  rw [D.filtration.terminal]
  exact bot_le

end AllocatedExternalCandidateProblem.PositiveKernelPreparation
end Erdos3.VectorPolynomial

end

end OAI
end


