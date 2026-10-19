-- Prove2me | Definitions.Def_OAIE3v2B283
-- name    : OAIE3v2B283
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T07:27:00.130291+00:00
-- url     : https://prove2.me/theorems/c1512327-ba41-406f-9a8c-10a26b00b919
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 296 of 311
-- statement:
--   Definitions bundle 296 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B275`, `OAIE3v2B276`, `OAIE3v2B277`, `OAIE3v2B278` of this split.
--
--   Modules: `Dynamics/AllocatedCandidateNestedTerminalUniformLayersBudget.lean`, `Estimates/AllocatedCandidateGeneratedFastTerminal.lean`, `Estimates/AllocatedCandidateStageDataConstruction.lean`, `Estimates/AllocatedExternalCandidateRealThreshold.lean`, `Estimates/PreparedScalarNestedPowerDetection.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeAutomaticLongGeometry.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeBudget.lean`, `Geometry/AllocatedExternalLocalCandidateOptionQuotientChart.lean`, `Lattices/CertifiedAffineNormalizedBudget.lean`, `Linear/AllocatedExternalCandidateCommonKeepPositiveKernelPreparation.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B275
import Definitions.Def_OAIE3v2B276
import Definitions.Def_OAIE3v2B277
import Definitions.Def_OAIE3v2B278

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

theorem exists_realThresholdAxisFreezing (bound : ℝ) :
    ∃ freezing : P.AxisFreezing (P.realThresholdKeep bound) (candidateSideCutoffCost bound),
      (∀ z : P.productive, ∀ i, (freezing.problem.chart z).keep i →
        (candidateSideCutoff bound : ℝ) ≤ layerSamplerBox B U b S i) ∧
      (∀ z : P.productive, ∀ i, (freezing.problem.chart z).keep i →
        bound < layerSamplerBox B U b S i) := by
  obtain ⟨freezing⟩ := P.exists_thresholdAxisFreezing (candidateSideCutoff bound)
  exact ⟨freezing, freezing.realThreshold_long, freezing.realThreshold_strict_long⟩

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
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "Q" => P.withKeep keep hkeep

theorem exists_history_full_chart_major_correlation_witness_of_lengths
    [Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
    (r a : ℕ) (hr : r ≤ s)
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (Bhistory Bstage budget : ℝ)
    (history : CertifiedFullChartFiniteHistory Fmark bF ν hF J (fast).toSubmodule
      (eQ.baseChange ℝ) lift Z Set.univ U poly N Bhistory r)
    (hcontrol : FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2 budget)
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ history.K Bstage
      (r * (Fintype.card η * m)))
    (HMap l : ℕ) (pMap : ℝ) (hHMap : 1 ≤ HMap) (hl : 0 < l) (hpMap : 0 ≤ pMap)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ω) : ℝ) ≤ pMap)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν) : ℝ) ≤ pMap)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp pMap) (hlExp : (l : ℝ) ≤ Real.exp pMap)
    (H : ℕ) (p qNative : ℝ) (hH : 1 ≤ H) (hp : 0 ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hVars : (Fintype.card Vars : ℝ) ≤ p)
    (hχ : (Fintype.card χ : ℝ) ≤ p) (hHExp : (H : ℝ) ≤ Real.exp p)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (hcommon : Real.exp budget * Real.exp ((pMap + 2) ^ 4) ≤ Real.exp p)
    (hmapSlow : Real.exp ((pMap + 2) ^ 3 + qNative) ≤ Real.exp ((p + 2) ^ a))
    (hallowance :
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s * Real.exp budget *
        (((m + 1 : ℕ) : ℝ) * ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) ^ s)
        ≤ Real.exp ((p + 2) ^ a))
    (hNreset : ∀ i : Vars, Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
      allocatedFrozenCurrentGradeResetConstant s a) ≤ (A.sides i.val : ℝ))
    (vg : χ → Fmark.PolynomialSymbol (fun _ : Vars => 1))
    (hspan : span ℚ (Set.range vg) = (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ : Vars => 1) fast).toSubmodule)
    (hvg : ∀ i z, RationalHeightLE ((Fmark.polynomialSymbolBasis bF ν hF (fun _ : Vars => 1)).repr (vg i) z) H)
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (pK Mbound LongSide : ℝ) (hpK : 0 ≤ pK) (hBstage : Bstage ≤ pK)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ pK) (hM : 0 ≤ Mbound)
    (hcap : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ Mbound)
    (hLong : 1 ≤ LongSide) (hlong : ∀ i, keep i → LongSide ≤ layerSamplerBox B U btag S i)
    (hthreshold : Real.exp ((pK + 2) ^ 9) ^ 2 * Mbound < LongSide)
    (hlength : ∀ z : P.productive, ∀ i, s < ((Q).chart z).slice.length i)
    (hfactor : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : Vars => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.realification.polynomialOrbitCoordinates _ ((Q).candidate z).orbit))
    (Hθ : ℕ) (pLocal : ℝ)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (hpLocal : 1 ≤ pLocal) (hLocalDim : (Fintype.card Vars : ℝ) ≤ pLocal)
    (hLocalSize : (Fintype.card κ : ℝ) * Hθ * Real.exp
      ((p + allocatedFrozenCurrentGradeResetConstant s a) ^ allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal)
    (hLocalDen : ((Hθ ^ Fintype.card κ : ℕ) : ℝ) * Real.exp
      ((p + allocatedFrozenCurrentGradeResetConstant s a) ^ allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal)
    (hNLocal : ∀ i : Vars, Real.exp ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) ≤ (A.sides i.val : ℝ))
    (pSlice pTest pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hNmajor : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (Bshort : ℝ) (hBshort : 1 ≤ Bshort)
    (hshort : ∀ i, ¬keep i → (A.sides i : ℝ) ≤ Bshort)
    (α : ℝ) (hα : α ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : A.NativeDetection r pSlice pTest pNative α)
    (hslice : max ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) (Real.log Bshort) ≤ pSlice)
    (htest : OrdinaryPolynomialPhase.budget r ≤ pTest) :
    Nonempty (FullChartMajorCorrelationWitness Fmark bF ν hF J (r + 1)
      (fast).toSubmodule (eQ.baseChange ℝ) Z history.outer.1 history.outer.2
      N poly U pMajor Rrank C) := by
  obtain ⟨reset, _, _, hlocal⟩ :=
    P.exists_history_current_grade_local_niltests keep hkeep bD ω hD bF ν hF hφ W
      eQ lift r a hr Bhistory Bstage budget history hcontrol hcertificate
      HMap l pMap hHMap hl hpMap hentries hsource htarget hHMapExp hlExp
      H p qNative hH hp hκ hVars hχ hHExp hbracket hcommon hmapSlow hallowance
      hNreset vg hspan hvg hτ hξ hσone Cgeo hCgeo hchart hsmall hpoly
      pK Mbound LongSide hpK hBstage hJ hM hcap hLong hlong hthreshold hlength hfactor
      Hθ pLocal hθ hpLocal hLocalDim hLocalSize hLocalDen hNLocal
  have hpLocal0 : 0 ≤ pLocal := le_trans (by norm_num) hpLocal
  apply exists_allocated_full_chart_major_correlation_witness_of_frozen_local_niltests
    A Fmark bF ν hF (fast).toSubmodule (eQ.baseChange ℝ) Z history.outer.1 history.outer.2
    (by omega) hpoly
    (fun i => (P.centerLift (lowTaggedIndex J (r + 1) i).1).val (lowTaggedIndex J (r + 1) i).2)
    pSlice pTest pNative pMajor Rrank C hpNative hη hNativeMajor hproduct hdim
    hNmajor hRrank hrank (fun _ => P.productive) keep
    ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) Bshort (by positivity) hBshort hshort hξ
    α (fun _ => hα.trans (mul_le_mul_of_nonneg_left P.mass (by norm_num)))
    hdirect hslice htest (fun _ _ => Hθ ^ Fintype.card κ * reset) (fun _ _ _ => 0)
  intro j z hz
  let zz : P.productive := ⟨z, hz⟩
  exact ⟨((Q).chart zz).fixed, ((Q).chart zz).fixed_in_box, hlocal j zz (fun _ => 0)⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCandidateGeneratedFastTerminal
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
    (stageCost stageMass stageScore : ℕ → ℝ)
    (Pstage : ∀ r, AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      (stageCost r) (stageMass r) (stageScore r))
    (keep : ℕ → LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ r, ∀ z : (Pstage r).productive, ((Pstage r).chart z).keep = keep r)
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

theorem exists_budgeted_tree_terminal_of_stage_refinements
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
    (aControl aLocal : ℕ)
    (Bphase Bbound pTree Rrank : ℝ) (Hbr qS : ℕ)
    (cap cumulative pControl pPhase : ℕ → ℝ)
    (T : CertifiedFullChartFiniteHistory.BudgetedBranchTree Fmark bF ν hF J
      (fast).toSubmodule (eQ.baseChange ℝ) lift Z U poly N Bphase cap s pTree)
    (hHbr : 1 ≤ Hbr) (hqS : 0 < qS)
    (hpControl : ∀ r ≤ s, 0 ≤ pControl r)
    (hcumulative : ∀ r ≤ s, 0 ≤ cumulative r)
    (hmono : ∀ r < s, cumulative r ≤ cumulative (r + 1))
    (hcap : ∀ r < s, cap r ≤ cumulative (r + 1))
    (hprefix : ∀ r ≤ s, ∀ j < r, cap j ≤ cumulative r)
    (hdetect : ∀ r < s,
      (pPhase r + allocatedCandidateTerminalPhaseConstant s m aControl r) ^
        allocatedCandidateTerminalPhaseConstant s m aControl r ≤ cap r)
    (hκControl : ∀ r ≤ s, (Fintype.card κ : ℝ) ≤ pControl r)
    (hTagsControl : ∀ r ≤ s, (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ pControl r)
    (hHbrExp : ∀ r ≤ s, (Hbr : ℝ) ≤ Real.exp (pControl r))
    (hstructure : ∀ i j z, RationalHeightLE ((Fmark.associatedGradedBasis bF ν hF).repr
      ⁅Fmark.associatedGradedBasis bF ν hF i, Fmark.associatedGradedBasis bF ν hF j⁆ z) Hbr)
    (hden : ∀ r ≤ s, (qS : ℝ) * Real.exp ((s : ℝ) * (Fintype.card η : ℝ) * cumulative r) ≤
      Real.exp (pControl r))
    (hcost : ∀ r ≤ s, (Fintype.card η : ℝ) * Bbound * Real.exp (cumulative r) ≤
      Real.exp ((pControl r + 2) ^ aControl))
    (hentry : ∀ i j, |((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤ Bbound)
    (hgrid : ∀ j, (fun i => ((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS)
    (hdata : ∀ r, r < s → Nonempty
      (HistoryStageData (χ := χ r) (P := Pstage r) (keep := keep r) (hkeep := hkeep r)
        (bD := bD) (ω := ω) (hD := hD) (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W) eQ r aLocal
        (cumulative r)
        ((pControl r + allocatedCandidateTerminalControlConstant s m aControl) ^
          allocatedCandidateTerminalControlConstant s m aControl)
        (pPhase r) Rrank (allocatedCandidateTerminalPhaseConstant s m aControl r))) :
    ∃ history ∈ T.level s,
      FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2
        ((pControl s + allocatedCandidateTerminalControlConstant s m aControl) ^
          allocatedCandidateTerminalControlConstant s m aControl) ∧
      RationalTaggedConstraintCertificate J Set.univ history.K (cumulative s)
        (s * (Fintype.card η * m)) ∧
      ∀ point ∈ history.K,
        eval₂ point (Fmark.realGradedSymbolPolynomial bF ν hF (fullTaggedVariableWeight J)
          (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈
            (fast).toSubmodule.baseChange ℝ := by
  have hconstants := Classical.choose_spec (Classical.choose_spec
    (exists_certified_budgeted_tree_terminal_constants s m aControl)).2
  obtain ⟨hcontrolled, hterminal⟩ := hconstants.2
    Fmark bF ν hF J (fast).toSubmodule (eQ.baseChange ℝ) lift hfast hsection
    Z U poly N Bphase Bbound pTree Rrank Hbr qS cap cumulative pControl pPhase T
    hHbr hqS hpControl hcumulative hmono hcap hprefix hdetect hκControl hTagsControl
    hHbrExp hstructure hden hcost hentry hgrid
  apply hterminal
  intro r hr history hmem
  obtain ⟨data⟩ := hdata r hr
  exact (Pstage r).exists_history_full_chart_major_correlation_witness_of_lengths (keep r) (hkeep r) bD ω hD bF ν hF hφ W
    eQ lift r aLocal data.hr Bphase (cumulative r)
    ((pControl r + allocatedCandidateTerminalControlConstant s m aControl) ^
      allocatedCandidateTerminalControlConstant s m aControl)
    history (hcontrolled r (Nat.le_of_lt hr) history hmem)
    (T.stage_bounds hmono hcap r (Nat.le_of_lt hr) history hmem).certificate
    data.HMap data.l data.pMap data.hHMap data.hl data.hpMap data.hentries data.hsource
    data.htarget data.hHMapExp data.hlExp data.H data.p data.qNative data.hH data.hp
    data.hκ data.hVars data.hχ data.hHExp data.hbracket data.hcommon data.hmapSlow
    data.hallowance data.hNreset data.vg data.hspan data.hvg data.hτ data.hξ data.hσone
    data.Cgeo data.hCgeo data.hchart data.hsmall data.hpoly data.pK data.Mbound data.LongSide
    data.hpK data.hBstage data.hJ data.hM data.hcap data.hLong data.hlong data.hthreshold
    data.hlength data.hfactor data.Hθ data.pLocal data.hθ data.hpLocal data.hLocalDim
    data.hLocalSize data.hLocalDen data.hNLocal data.pSlice data.pTest data.pNative (pPhase r)
    Rrank (allocatedCandidateTerminalPhaseConstant s m aControl r) data.hpNative data.hη
    data.hNativeMajor data.hproduct data.hdim data.hNmajor data.hRrank data.hrank
    data.Bshort data.hBshort data.hshort data.α data.hα data.hdirect data.hslice data.htest

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
    (stageCost stageMass stageScore : ℕ → ℝ)
    (Pstage : ∀ r, AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      (stageCost r) (stageMass r) (stageScore r))
    (keep : ℕ → LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ r, ∀ z : (Pstage r).productive, ((Pstage r).chart z).keep = keep r)
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

theorem exists_forward_controlled_terminal_of_stage_refinements
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
    (aLocal : ℕ)
    (Bphase Bbound pTree Rrank : ℝ) (Hbr qS : ℕ)
    (scheduleExponent : ℕ) (x gainLog stageLog : ℝ)
    (T : CertifiedFullChartFiniteHistory.BudgetedBranchTree Fmark bF ν hF J
      (fast).toSubmodule (eQ.baseChange ℝ) lift Z U poly N Bphase
      (fun r => preparedFiniteForwardCap scheduleExponent countConstants r x) s pTree)
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (Cnative : ℕ) (pMajor : ℕ → ℝ)
    (hMajorNonneg : ∀ r < s, 0 ≤ pMajor r)
    (hMajorBound : ∀ r < s, pMajor r ≤
      (preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
        preparedFiniteForwardWork scheduleExponent countConstants r x + Cnative) ^ Cnative)
    (hphaseExponent : ∀ r < s,
      allocatedCandidateCompositePhaseConstant s m 1 Cnative r ≤ scheduleExponent)
    (hSchedule : 2 ≤ scheduleExponent) (hsSchedule : s + 3 ≤ scheduleExponent)
    (hControlSchedule : 4 * allocatedCandidateTerminalControlConstant s m 1 ≤ scheduleExponent)
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
    (hdata : ∀ r, r < s → Nonempty
      (HistoryStageData (χ := χ r) (P := Pstage r) (keep := keep r) (hkeep := hkeep r)
        (bD := bD) (ω := ω) (hD := hD) (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W) eQ r aLocal
        (preparedFiniteForwardCumulative scheduleExponent countConstants r x)
        ((allocatedCandidateForwardControlInput s (Fintype.card η)
          (preparedFiniteForwardParameter scheduleExponent countConstants r x) +
          allocatedCandidateTerminalControlConstant s m 1) ^
          allocatedCandidateTerminalControlConstant s m 1)
        (pMajor r) Rrank (allocatedCandidateTerminalPhaseConstant s m 1 r))) :
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
  let pControl : ℕ → ℝ := fun r => allocatedCandidateForwardControlInput s (Fintype.card η)
    (preparedFiniteForwardParameter scheduleExponent countConstants r x)
  have hinput (r : ℕ) := allocatedCandidateForwardControlInput_bounds s (Fintype.card η)
    (preparedFiniteForwardParameter_nonneg scheduleExponent countConstants r hx)
  have hbase (r : ℕ) : x ≤ pControl r :=
    (le_preparedFiniteForwardParameter scheduleExponent countConstants r hx).trans (hinput r).2.1
  have hwork (r : ℕ) :
      (pControl r + allocatedCandidateTerminalControlConstant s m 1) ^
        allocatedCandidateTerminalControlConstant s m 1 ≤
      preparedFiniteForwardWork scheduleExponent countConstants r x := by
    rw [preparedFiniteForwardWork_eq]
    exact allocatedCandidateForwardControlInput_power_bound s (Fintype.card η)
      (allocatedCandidateTerminalControlConstant s m 1) scheduleExponent
      (preparedFiniteForwardParameter_nonneg scheduleExponent countConstants r hx)
      (hηBase.trans (le_preparedFiniteForwardParameter scheduleExponent countConstants r hx))
      hSchedule hsSchedule hControlSchedule
  have hden : ∀ r ≤ s, (qS : ℝ) * Real.exp ((s : ℝ) * (Fintype.card η : ℝ) *
      preparedFiniteForwardCumulative scheduleExponent countConstants r x) ≤ Real.exp (pControl r) := by
    intro r hr
    exact allocatedCandidateForwardControlInput_denominator_bound s (Fintype.card η) qS
      (preparedFiniteForwardParameter_nonneg scheduleExponent countConstants r hx)
      (le_preparedFiniteForwardParameter scheduleExponent countConstants r hx)
      (preparedFiniteForward_prefix_bounds scheduleExponent countConstants r hx).1.2 hqSBase
  have hcost : ∀ r ≤ s, (Fintype.card η : ℝ) * Bbound *
      Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants r x) ≤
        Real.exp ((pControl r + 2) ^ (1 : ℕ)) := by
    intro r hr
    simpa only [pow_one] using allocatedCandidateForwardControlInput_cost_bound s (Fintype.card η)
      (le_preparedFiniteForwardParameter scheduleExponent countConstants r hx)
      (preparedFiniteForward_prefix_bounds scheduleExponent countConstants r hx).1.2 hηBase hBboundBase
  have hdetect (r : ℕ) (hr : r < s) :
      (pMajor r + allocatedCandidateTerminalPhaseConstant s m 1 r) ^
        allocatedCandidateTerminalPhaseConstant s m 1 r ≤
      preparedFiniteForwardCap scheduleExponent countConstants r x := by
    have h := Classical.choose_spec (exists_preparedFiniteForward_composed_phase_cap Cnative
      (allocatedCandidateTerminalPhaseConstant s m 1 r))
    exact h.2 scheduleExponent countConstants r (hphaseExponent r hr) hx hgain hstage
      (hMajorNonneg r hr) (hMajorBound r hr)
  obtain ⟨history, hmem, hcontrol, hcertificate, hterminal⟩ :=
    exists_budgeted_tree_terminal_of_stage_refinements stageCost stageMass stageScore Pstage keep hkeep
      bD ω hD bF ν hF hφ W eQ lift hfast hsection 1 aLocal Bphase Bbound pTree Rrank Hbr qS
      (fun r => preparedFiniteForwardCap scheduleExponent countConstants r x)
      (fun r => preparedFiniteForwardCumulative scheduleExponent countConstants r x)
      pControl pMajor T hHbr hqS (fun r _ => (hinput r).1)
      (fun r _ => (preparedFiniteForward_prefix_bounds scheduleExponent countConstants r hx).1.1)
      (fun r _ => preparedFiniteForwardCumulative_le_succ scheduleExponent countConstants r hx)
      (fun r _ => preparedFiniteForwardCap_le_cumulative_succ scheduleExponent countConstants r hx)
      (fun r _ j hj => preparedFiniteForwardCap_le_cumulative scheduleExponent countConstants hx hj)
      hdetect (fun r _ => hκBase.trans (hbase r)) (fun r _ => hTagsBase.trans (hbase r))
      (fun r _ => hHbrBase.trans (Real.exp_le_exp.mpr (hbase r))) hstructure hden hcost hentry hgrid hdata
  exact ⟨history, hmem,
    FullChartControlledFactors.mono Fmark bF ν hF J poly N history.outer.1 history.outer.2 hcontrol (hwork s),
    hcertificate, hterminal⟩

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
    (stageCost stageMass stageScore : ℕ → ℝ)
    (Pstage : ∀ r, AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      (stageCost r) (stageMass r) (stageScore r))
    (keep : ℕ → LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ r, ∀ z : (Pstage r).productive, ((Pstage r).chart z).keep = keep r)
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

theorem exists_forward_terminal_of_native_stage_data
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
    (Cprimitive Csource : ℕ) (sourceNative : ℕ → ℝ)
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
    (hdata : ∀ r, r < s → Nonempty
      (HistoryStageData (χ := χ r) (P := Pstage r) (keep := keep r) (hkeep := hkeep r)
        (bD := bD) (ω := ω) (hD := hD) (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W) eQ r 1
        (preparedFiniteForwardCumulative scheduleExponent countConstants r x)
        ((allocatedCandidateForwardControlInput s (Fintype.card η)
          (preparedFiniteForwardParameter scheduleExponent countConstants r x) +
          allocatedCandidateTerminalControlConstant s m 1) ^
          allocatedCandidateTerminalControlConstant s m 1)
        (allocatedCandidateNativeMajorBudget
          (sourceNative r + allocatedCandidateStageBase s m Cprimitive
            (preparedFiniteForwardParameter scheduleExponent countConstants r x) + 2)
          (allocatedCandidateStageBase s m Cprimitive
            (preparedFiniteForwardParameter scheduleExponent countConstants r x))) Rrank (allocatedCandidateTerminalPhaseConstant s m 1 r))) :
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
  let v : ℕ → ℝ := fun r => allocatedCandidateStageBase s m Cprimitive
    (preparedFiniteForwardParameter scheduleExponent countConstants r x)
  let pMajor : ℕ → ℝ := fun r =>
    allocatedCandidateNativeMajorBudget (sourceNative r + v r + 2) (v r)
  have hv (r : ℕ) : 0 ≤ v r := (by norm_num : (0 : ℝ) ≤ 2).trans
    (allocatedCandidateStageBase_bounds s m Cprimitive
      (preparedFiniteForwardParameter_nonneg scheduleExponent countConstants r hx)).1
  have ht (r : ℕ) : 0 ≤ preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
      preparedFiniteForwardWork scheduleExponent countConstants r x :=
    add_nonneg (preparedFiniteForward_model_precision_bounds scheduleExponent countConstants r hx hgain hstage).2.1
      (preparedFiniteForwardWork_nonneg scheduleExponent countConstants r hx)
  have hvt (r : ℕ) : v r ≤ preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
      preparedFiniteForwardWork scheduleExponent countConstants r x :=
    (allocatedCandidateStageBase_le_forwardWork s m Cprimitive scheduleExponent countConstants r hx hBaseExponent).trans
      (le_add_of_nonneg_left
        (preparedFiniteForward_model_precision_bounds scheduleExponent countConstants r hx hgain hstage).2.1)
  have hMajorNonneg (r : ℕ) (hr : r < s) : 0 ≤ pMajor r := by
    apply allocatedCandidateNativeMajorBudget_nonneg _ (hv r)
    linarith only [hSourceNonneg r hr, hv r]
  have hMajorBound (r : ℕ) (hr : r < s) : pMajor r ≤
      (preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
        preparedFiniteForwardWork scheduleExponent countConstants r x +
        allocatedCandidatePromotedMajorConstant Csource) ^ allocatedCandidatePromotedMajorConstant Csource := by
    exact (Classical.choose_spec
      (exists_allocated_candidate_promoted_native_major_budget Csource)).2 _ _ _
      (ht r) (hv r) (hvt r) (hSourceNonneg r hr) (hSourceBound r hr)
  have hBase := allocatedCandidateStageBaseExponent_bounds s m Cprimitive
  exact exists_forward_controlled_terminal_of_stage_refinements stageCost stageMass stageScore Pstage keep hkeep
    bD ω hD bF ν hF hφ W eQ lift hfast hsection 1 Bphase Bbound pTree Rrank Hbr qS
    scheduleExponent x gainLog stageLog T hx hgain hstage
    (allocatedCandidatePromotedMajorConstant Csource) pMajor hMajorNonneg hMajorBound hphaseExponent
    (hBase.1.trans hBaseExponent) (hBase.2.1.trans hBaseExponent)
    (hBase.2.2.1.trans hBaseExponent) hHbr hqS hκBase hTagsBase hηBase hHbrBase hqSBase
    hBboundBase hstructure hentry hgrid hdata

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

local notation "countConstants" =>
  (fun n => NilpotentLieFiltration.fullChartStageCountConstant (n + 1) 254)

theorem allocatedCandidateForwardMajor_cap
    (s m Cprimitive Csource A r : ℕ)
    {x gainLog stageLog sourceNative : ℝ}
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (hSourceNonneg : 0 ≤ sourceNative)
    (hSourceBound : sourceNative ≤
      (preparedFiniteForwardSourcePrecision A countConstants r x gainLog stageLog +
        preparedFiniteForwardWork A countConstants r x + Csource) ^ Csource)
    (hBaseExponent : allocatedCandidateStageBaseExponent s m Cprimitive ≤ A)
    (hphaseExponent : allocatedCandidateCompositePhaseConstant s m 1
      (allocatedCandidatePromotedMajorConstant Csource) r ≤ A) :
    (allocatedCandidateNativeMajorBudget
        (sourceNative + allocatedCandidateStageBase s m Cprimitive
          (preparedFiniteForwardParameter A countConstants r x) + 2)
        (allocatedCandidateStageBase s m Cprimitive
          (preparedFiniteForwardParameter A countConstants r x)) +
      allocatedCandidateTerminalPhaseConstant s m 1 r) ^
        allocatedCandidateTerminalPhaseConstant s m 1 r ≤
      preparedFiniteForwardCap A countConstants r x := by
  let v := allocatedCandidateStageBase s m Cprimitive
    (preparedFiniteForwardParameter A countConstants r x)
  let pMajor := allocatedCandidateNativeMajorBudget (sourceNative + v + 2) v
  have hv : 0 ≤ v := (by norm_num : (0 : ℝ) ≤ 2).trans
    (allocatedCandidateStageBase_bounds s m Cprimitive
      (preparedFiniteForwardParameter_nonneg A countConstants r hx)).1
  have hprecision :=
    (preparedFiniteForward_model_precision_bounds A countConstants r hx hgain hstage).2.1
  have ht : 0 ≤ preparedFiniteForwardSourcePrecision A countConstants r x gainLog stageLog +
      preparedFiniteForwardWork A countConstants r x :=
    add_nonneg hprecision (preparedFiniteForwardWork_nonneg A countConstants r hx)
  have hvt : v ≤ preparedFiniteForwardSourcePrecision A countConstants r x gainLog stageLog +
      preparedFiniteForwardWork A countConstants r x :=
    (allocatedCandidateStageBase_le_forwardWork s m Cprimitive A countConstants r hx
      hBaseExponent).trans (le_add_of_nonneg_left hprecision)
  have hMajorNonneg : 0 ≤ pMajor := by
    apply allocatedCandidateNativeMajorBudget_nonneg _ hv
    linarith only [hSourceNonneg, hv]
  have hMajorBound : pMajor ≤
      (preparedFiniteForwardSourcePrecision A countConstants r x gainLog stageLog +
        preparedFiniteForwardWork A countConstants r x +
        allocatedCandidatePromotedMajorConstant Csource) ^ allocatedCandidatePromotedMajorConstant Csource :=
    (Classical.choose_spec
      (exists_allocated_candidate_promoted_native_major_budget Csource)).2 _ _ _
      ht hv hvt hSourceNonneg hSourceBound
  exact (Classical.choose_spec
    (exists_preparedFiniteForward_composed_phase_cap
      (allocatedCandidatePromotedMajorConstant Csource)
      (allocatedCandidateTerminalPhaseConstant s m 1 r))).2
    A countConstants r hphaseExponent hx hgain hstage hMajorNonneg hMajorBound

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

attribute [local irreducible] integerProgressionSupport

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
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem exists_certifiedThresholdAffineRefinement
    (hσone : ∀ j, σ j ≤ 1)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) {p : ℝ} {blocks : ℕ}
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ K p blocks)
    (hretained : ∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ U j) → t ∈ K)
    (hp : 0 ≤ p) (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hblocks : (blocks : ℝ) ≤ p)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hcap : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ Real.exp p)
    (separation : ℝ) (hseparation : certifiedAffineLongSideBound p ≤ separation)
    (hmass : 0 < massThreshold) :
    Nonempty (P.CertifiedThresholdAffineRefinement K p separation) := by
  obtain ⟨freezing, hlong, _⟩ := P.exists_realThresholdAxisFreezing separation
  have hthreshold : Real.exp ((p + 2) ^ 9) ^ 2 * Real.exp p <
      (candidateSideCutoff separation : ℝ) :=
    hseparation.trans_lt (lt_candidateSideCutoff separation)
  obtain ⟨affine⟩ := freezing.problem.exists_certifiedAffineRefinement
    hσone K hcertificate hretained hp hdim hblocks Cgeo hCgeo hchart hpoly hcap
    hlong hthreshold hmass
  exact ⟨⟨freezing, affine⟩⟩

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

noncomputable def uniformLayersTerminalPolynomial (s Cprimitive : ℕ) : Polynomial ℕ :=
  (Polynomial.X + Polynomial.C Cprimitive) ^ Cprimitive + Polynomial.X + Polynomial.X +
    Polynomial.C s * Polynomial.X * uniformLayersAffinePolynomial +
    uniformLayersAffinePolynomial + Polynomial.C s + Polynomial.X + 10

attribute [local irreducible] certifiedAffineCenterBudget
  preparedFiniteForwardParameter preparedFiniteForwardWork preparedFiniteForwardCap
  preparedFiniteForwardBranch preparedFiniteForwardCumulative

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeBudget
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

theorem exists_taggedPairFamily [Fintype Ω]
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    {q : ℝ} (hpq : pNative ≤ q) (hprecision : pLocal + r + 1 ≤ q)
    (hfrequency : verticalDecompositionBudget q ≤ p)
    (hbudget : r + verticalDecompositionBudget q + 2 ≤ p)
    (hcorr : ∀ a ∈ H, ∀ j, Real.exp (-r) ≤ ‖F.correlation a j‖) :
    ∃ (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      Real.exp (-verticalDecompositionBudget q * Fintype.card Pivot) * outer.mass H ≤
        outer.mass retained ∧
      ∃ selectedFamily : AllocatedExternalCandidateTaggedPairFamily A Deck
          {a // a ∈ retained} Pivot D (fun j => (F.native j).model) Fmark φ marked
          keep cost p periodCap coverCap Lip,
        (∀ a, selectedFamily.sourceChart a = F.sourceChart a.val) ∧
        (∀ a, HEq (selectedFamily.sourceCandidate a) (F.sourceCandidate a.val)) ∧
        selectedFamily.reference = (fun a => F.reference a.val) ∧
        selectedFamily.twist = (fun a => F.twist a.val) ∧
        selectedFamily.η = F.η ∧
        (∀ j, selectedFamily.ambient j = (F.native j).test.fullTaggedSpatial J) ∧
        ∀ a, selectedFamily.jointOrbit a = F.jointOrbit a.val := by
  classical
  have hfull (a : Ω) (ha : a ∈ H) (j : Pivot) :
      Real.exp (-r) ≤
        ‖((F.chart a).slice.fullSliceLaw
          ((F.chart a).slice.length_pos_of_dense (F.chart a).dense)).complexMean (fun u =>
          (star ((F.twist a j).eval N poly (F.physicalBox a u).val) *
            F.nativeValue j (F.physicalBox a u)) * (F.localTest a j).eval u.val)‖ := by
    exact F.rawCorrelation_fullSliceLaw a j (hcorr a ha j)
  obtain ⟨freq, V, retained, hsub, hpos, hmass, hcert, hheight, hvert, hselected⟩ :=
    exists_spatialNative_slice_tagged_vertical_partners
      (Ω := Ω) (Pivot := Pivot) (K := {i // keep i})
      (N := fun i : {i // keep i} => A.sides i.val)
      (pNative := pNative) (pLocal := pLocal) (r := r) (q := q) J poly D
      (fun x : integerBox N => x.val) F.nativeValue F.native F.localTest outer H hH
      (fun a _ => (F.chart a).step) (fun a _ => (F.chart a).slice)
      (fun a _ _ => (F.chart a).step_pos)
      (fun a _ i => (F.chart a).slice.length_pos_of_dense (F.chart a).dense i)
      F.physicalBox (fun a k => ((F.chart a).centerLift k).val)
      (fun a j u => (F.twist a j).eval N poly (F.physicalBox a u).val)
      F.hpLocal F.hr hpq hprecision
      (fun a _ j => F.hV a j)
      (fun a _ j u => (F.twist a j).norm_eval_le N poly _) hfull
  let selectedFamily : AllocatedExternalCandidateTaggedPairFamily A Deck
      {a // a ∈ retained} Pivot D (fun j => (F.native j).model) Fmark φ marked
      keep cost p periodCap coverCap Lip := {
    hpoly := F.hpoly
    hτ1 := F.hτ1
    hξ := F.hξ
    hσ1 := F.hσ1
    Cgeo := F.Cgeo
    hCgeo := F.hCgeo
    hchart := F.hchart
    hsmall := F.hsmall
    sourceChart := fun a => F.sourceChart a.val
    keep_eq := fun a => F.keep_eq a.val
    sourceCandidate := fun a => F.sourceCandidate a.val
    reference := fun a => F.reference a.val
    ambient := fun j => (F.native j).test.fullTaggedSpatial J
    selected := V
    selected_orbit := fun j => (hcert j).1
    twist := fun a => F.twist a.val
    hp := F.hp
    hcost := F.hcost
    hperiod := fun a => F.hperiod a.val
    hvariation := F.hvariation
    hV := fun a j => (F.hV a.val j).mono F.hlocal
    hW := fun j => (hcert j).2.1.mono F.hnative
    hWnorm := fun j => (hcert j).2.2
    η := F.η
    θ := freq
    hηheight := F.hηheight
    hθheight := fun j i => (hheight j i).trans hfrequency
    hη := fun a => F.hη a.val
    hθ := hvert
    hK := F.hK
    hcorr := by
      intro a j
      exact F.selectedCorrelation_localLaw V a.val j
        ((exp_correlation_bound hbudget).trans (hselected a.val a.property j)) }
  exact ⟨retained, hsub, hpos, hmass, selectedFamily,
    (fun _ => rfl), (fun _ => HEq.rfl), rfl, rfl, rfl, (fun _ => rfl), (fun _ => rfl)⟩

end AllocatedExternalCandidateSpatialNativeFamily

end

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

theorem exists_commonKeepPositiveKernelPreparation
    (p : ℝ) (e : ℕ) (hp : 0 ≤ p)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hD : D.GeometryComplexityLE p)
    (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p)
    (hmass : Real.exp (-p) ≤ massThreshold)
    (hscore : Real.exp (-p) ≤ scoreThreshold)
    (hξ1 : ξ ≤ 1)
    (hnet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖observable x y - observable (centers i).val y‖ ≤ η) :
    Nonempty (P.CommonKeepPositiveKernelPreparation p e) := by
  obtain ⟨keep, refinement, hkeep⟩ := P.exists_common_keep_refinement_exp
    ((Real.exp_pos _).le.trans hmass) hvariables
  have hp2 : p ≤ 2 * p := by linarith
  have hmass2 : Real.exp (-(2 * p)) ≤ massThreshold * Real.exp (-p) := by
    calc
      Real.exp (-(2 * p)) = Real.exp (-p) * Real.exp (-p) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ massThreshold * Real.exp (-p) :=
        mul_le_mul_of_nonneg_right hmass (Real.exp_nonneg _)
  have hnet2 : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((2 * p + Real.log (1 / η) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖observable x y - observable (centers i).val y‖ ≤ η := by
    intro η hη hη1
    obtain ⟨count, hcount, centers, hcenters⟩ := hnet η hη hη1
    refine ⟨count, hcount.trans (Real.exp_le_exp.mpr ?_), centers, hcenters⟩
    have hlog : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((one_le_div hη).mpr hη1)
    exact pow_le_pow_left₀ (by positivity) (by linarith) e
  obtain ⟨prep⟩ := (refinement.problem.withKeep keep hkeep).exists_positiveKernelPreparation
    (2 * p) e (by positivity) (hD.mono D hp2) ℓ
    (hℓ.trans (Real.exp_le_exp.mpr hp2)) hLip hpositive
    (fun x => (hweight x).trans (Real.exp_le_exp.mpr hp2)) hmass2
    ((Real.exp_le_exp.mpr (neg_le_neg hp2)).trans hscore) hξ1 hnet2
  exact ⟨{ keep := keep, refinement := refinement, hkeep := hkeep, prep := prep }⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedScalarNestedPowerDetection
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def PreparedScalarNestedPowerDetection
    (s outerDepth innerDepth exponent Cslice Cdirect : ℕ) (constants : ℕ → ℕ)
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
      τ = unconditionedSpatialTrimFraction nX (Real.exp (-p)) →
      Real.exp ((p + 2) ^ earlyExponent) ≤ S₀.value →
      (S₀.value : ℝ) ≤ Real.exp ((p + 2) ^ latePower) →
      (∀ i, Real.exp ((p + 2) ^ sizeExponent) ≤ (N i : ℝ)) →
      let Bstruct := (p + 2) ^ basePower
      let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth s
      let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
      let stage : K → ℕ := fun k => (preparedFiniteNestedForwardAllDegreeStage k).val
      let seed : K → ℝ := preparedFiniteNestedForwardAllDegreeSeed exponent constants Bstruct
      let sourceU := fun k : K => preparedFiniteForwardPairedSourcePrecision exponent Cdirect
        constants (stage k) (preparedFiniteNestedForwardAllDegreeIsDirect k) (seed k) Bstruct Bstruct
      let modelLog := fun k : K => preparedFiniteForwardWork exponent constants (stage k) (seed k)
      let sliceLog := fun k : K =>
        (preparedFiniteForwardParameter exponent constants (stage k) (seed k) + Cslice) ^ Cslice
      let α := preparedFiniteNestedForwardFixedCenterThreshold exponent constants Bstruct Bstruct Bstruct
      let Pdetect := preparedFiniteForwardDetectorPolynomial s
      ∃ Plate : ℝ, 0 ≤ Plate ∧
        (∀ k : K, A₀.NativeDetection (degree k) (sliceLog k)
          (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
          (preparedFiniteNestedSourceNative (max s 1) (Fin (scalarNativeDimension s))
            (scalarNativeDimension s) nX Pdetect exponent Cdirect constants
            Bstruct (scalarNativeDimension s) 0 Bstruct Bstruct Plate k) (α k)) ∧
        ∀ (outer : Fin (outerDepth + 1)) (degree : Fin (s + 1)) (i : Fin nX),
          Real.exp (preparedFiniteForwardCumulative exponent constants degree.val
            (candidateNestedForwardSeed exponent constants innerDepth outer.val Bstruct)) ≤ (N i : ℝ)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalLocalCandidateOptionQuotientChart
namespace OAI

section

universe u v

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    {cost : ℝ} {C : AllocatedExternalLocalChart (E := Deck) A cost}
    {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {P : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ j, LieRing (P j)] [∀ j, LieAlgebra ℚ (P j)]
    {s d dQ : ℕ} {dp : Pivot → ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (ideal : LieIdeal ℚ L) (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)
    (hker : ∀ x ∈ ideal, φ x = 0)
    (partners : ∀ j, RationalFilteredNilmanifold (P j) s (dp j))
    (partnerOrbit : ∀ j, (partners j).filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))

attribute [local irreducible] NilpotentLieFiltration.realPolynomialGroupMap
    NilpotentLieFiltration.weightedAdaptedRealChartHom

theorem optionJoint_lieQuotient_chart_polynomialCoordinates
    {K : Type*} (β : C.Variables → MvPolynomial K ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : K => 1) 1) :
    (optionProduct Q partners).filtration.weightedAdaptedRealChartHom
      (fun _ : C.Variables => 1) (fun _ : K => 1) β hβ
      ((optionProduct Q partners).filtration.realification.polynomialOrbitCoordinates
        (fun _ : C.Variables => 1)
        ((candidate.lieQuotient ideal hI Q hQ hker).optionJoint partners partnerOrbit).orbit) =
      (optionProduct D partners).filtration.realPolynomialGroupMap
        (optionProduct Q partners).filtration
        (optionMarkedLieMap (L := P) (lieQuotientMap ideal))
        (D.optionQuotientMap_mem_layer ideal hI Q hQ partners)
        (fun _ : K => 1)
        ((optionProduct D partners).filtration.weightedAdaptedRealChartHom
          (fun _ : C.Variables => 1) (fun _ : K => 1) β hβ
          ((optionProduct D partners).filtration.realification.polynomialOrbitCoordinates
            (fun _ : C.Variables => 1) (candidate.optionJoint partners partnerOrbit).orbit)) := by
  calc
    _ = (optionProduct Q partners).filtration.weightedAdaptedRealChartHom
        (fun _ : C.Variables => 1) (fun _ : K => 1) β hβ
        ((optionProduct D partners).filtration.realPolynomialGroupMap
          (optionProduct Q partners).filtration
          (optionMarkedLieMap (L := P) (lieQuotientMap ideal))
          (D.optionQuotientMap_mem_layer ideal hI Q hQ partners)
          (fun _ : C.Variables => 1)
          ((optionProduct D partners).filtration.realification.polynomialOrbitCoordinates
            (fun _ : C.Variables => 1) (candidate.optionJoint partners partnerOrbit).orbit)) :=
      congrArg ((optionProduct Q partners).filtration.weightedAdaptedRealChartHom
        (fun _ : C.Variables => 1) (fun _ : K => 1) β hβ)
        (candidate.optionJoint_lieQuotient_polynomialCoordinates
          ideal hI Q hQ hker partners partnerOrbit)
    _ = _ := ((optionProduct D partners).filtration.realPolynomialGroupMap_weightedAdaptedRealChartHom
      (optionProduct Q partners).filtration
      (optionMarkedLieMap (L := P) (lieQuotientMap ideal))
      (D.optionQuotientMap_mem_layer ideal hI Q hQ partners)
      (fun _ : C.Variables => 1) (fun _ : K => 1) β hβ
      ((optionProduct D partners).filtration.realification.polynomialOrbitCoordinates
        (fun _ : C.Variables => 1) (candidate.optionJoint partners partnerOrbit).orbit)).symm

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeAutomaticLongGeometry
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
  weightedAdaptedRealChartHom realPolynomialGroupMap

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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {Deck : Fin m → Type*} {Pivot : Type*} [Fintype Pivot]
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

variable {α : Type*} [Fintype α]
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

def ActualAdaptedPivotQuotientLongFactors (qVertical qCommon pProj : ℝ) : Prop :=
  ∃ (retained : Finset A.Path) (hsub : retained ⊆ H)
    (hmass : Real.exp (-(verticalDecompositionBudget qVertical * Fintype.card Pivot +
      ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass H ≤ A.law.mass retained),
    0 < A.law.mass retained ∧
    ∃ (theta : ∀ j, (F.native j).L →ₗ[ℚ] ℚ)
      (W : LieSubalgebra ℚ (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
      (v : Fin (Fintype.card α) →
        (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
      (den : ℕ),
      Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
      BasisGradedSubmodule
        ((optionProduct D (fun j => (F.native j).model)).filtration.associatedGradedBasis e ω hF)
        ω W.toSubmodule ∧
      (∀ i k, rationalLogHeight
        (((optionProduct D (fun j => (F.native j).model)).filtration.associatedGradedBasis
          e ω hF).repr (v i) k) ≤ qCommon) ∧
      (∀ j x, x ∈ (optionProduct D (fun j => (F.native j).model)).filtration.realGradedRefiltrationLayer W s →
        realifyFunctional ((pairFrequency (F.η j) (theta j)).comp
          (optionPairProjection j).toLinearMap) x = 0) ∧
      0 < den ∧ (den : ℝ) ≤ Real.exp qCommon ∧
      let source := F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
        scoreThreshold hscore retained hsub hmass
      let target := (source.withKeep keep (fun _ => rfl)).adaptedOptionQuotient
        (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)
        (D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (by rw [D.filtration.terminal]; exact bot_le) Q hQ hker descended hrecovery adapted
      let F₀ := (optionProduct D (fun j => (F.native j).model)).filtration
      let FQ := adapted.model.filtration
      let ψ := optionMarkedLieMap (L := fun j => (F.native j).L)
        (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js))
      let hψ := D.optionQuotientMap_mem_layer
        (D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (by rw [D.filtration.terminal]; exact bot_le) Q hQ (fun j => (F.native j).model)
      let V := W.map (F₀.associatedGradedMap FQ ψ hψ)
      let vQ := F₀.gradedImageSpanningFamily FQ ψ hψ v
      ∃ denQ : ℕ, 0 < denQ ∧ (denQ : ℝ) ≤ Real.exp ((pProj + 2) ^ 4) ∧ den ∣ denQ ∧
        Submodule.span ℚ (Set.range vQ) = V.toSubmodule ∧
        BasisGradedSubmodule
          (FQ.associatedGradedBasis adapted.model.basis adapted.weight adapted.model_layers)
          adapted.weight V.toSubmodule ∧
        (∀ a i, rationalLogHeight
          ((FQ.associatedGradedBasis adapted.model.basis adapted.weight adapted.model_layers).repr
            (vQ a) i) ≤ (pProj + 2) ^ 4) ∧
        (∀ z : target.productive,
          FQ.HasCommonRefilteredOrbitFactors adapted.model.basis adapted.weight adapted.model_layers
            (fun i : {i // keepLong i} => (A.sides i.val : ℝ)) ((pProj + 2) ^ 3 + qCommon) denQ V
            (FQ.weightedAdaptedRealChartHom
              (fun _ : {i // keep i} => 1) (fun _ : {i // keepLong i} => 1)
              ((target.chart z).axisPolynomial keepLong (fun _ => 0))
              ((target.chart z).axisPolynomial_support keepLong (fun _ => 0))
              (FQ.realification.polynomialOrbitCoordinates (fun _ => 1)
                (target.candidate z).orbit))) ∧
        (∀ x ∈ FQ.gradedRefiltrationLayer V s,
          optionMarkedLieMap (L := fun j => (F.native j).L)
            (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker) x = 0 →
          x = 0) ∧
        (∀ (Gmark : NilpotentLieFiltration
            (∀ i : Option Pivot, optionLieSpace LM (fun j => (F.native j).L) i) s)
          (hmarked : ∀ k, ∀ x ∈ FQ.layer k,
            optionMarkedLieMap (L := fun j => (F.native j).L)
              (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker) x ∈
                Gmark.layer k),
          ∀ a ∈ V,
            basisGradeProjection
              (FQ.associatedGradedBasis adapted.model.basis adapted.weight adapted.model_layers)
              adapted.weight s a = a →
            FQ.associatedGradedMap Gmark
              (optionMarkedLieMap (L := fun j => (F.native j).L)
                (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker))
              hmarked a = 0 → a = 0)

theorem LongCommonFactors.toActualAdaptedPivotQuotientLongFactors
    {qVertical qCommon pProj : ℝ}
    (hcommon : F.LongCommonFactors keepLong A.law H e ω hF qVertical qCommon)
    {height : ℕ}
    (hentries : ∀ i j, RationalHeightLE
      (adapted.basis.repr
        (optionMarkedLieMap (L := fun j => (F.native j).L)
          (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) (e j)) i) height)
    (hpProj : 0 ≤ pProj) (hqProj : qCommon ≤ pProj)
    (hsource : (Fintype.card α : ℝ) ≤ pProj)
    (htarget : (finrank ℚ (∀ i : Option Pivot,
      optionLieSpace (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (fun j => (F.native j).L) i) : ℝ) ≤ pProj)
    (hheight : (height : ℝ) ≤ Real.exp pProj) :
    F.ActualAdaptedPivotQuotientLongFactors keepLong H sourceCenter hpath hcenter hfrozen
      observable weight scoreThreshold hscore e ω hF js Q hQ hker descended hrecovery adapted
      qVertical qCommon pProj := by
  obtain ⟨theta, W, v, den, retained, hsub, hpos, hmass, hv, hW, hvH, hzero,
    hden, hdenBound, hfactor⟩ := hcommon
  let source := F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
    scoreThreshold hscore retained hsub hmass
  let target := (source.withKeep keep (fun _ => rfl)).adaptedOptionQuotient
    (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)
    (D.filtration.pivotAnnihilatorIdeal φ F.η js)
    (by rw [D.filtration.terminal]; exact bot_le) Q hQ hker descended hrecovery adapted
  let F₀ := (optionProduct D (fun j => (F.native j).model)).filtration
  let FQ := adapted.model.filtration
  let ψ := optionMarkedLieMap (L := fun j => (F.native j).L)
    (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js))
  let hψ := D.optionQuotientMap_mem_layer (D.filtration.pivotAnnihilatorIdeal φ F.η js)
    (by rw [D.filtration.terminal]; exact bot_le) Q hQ (fun j => (F.native j).model)
  obtain ⟨denQ, hdenQ, hdenQBound, hdiv, htransport⟩ :=
    F₀.exists_common_refiltered_mapped_orbit_factors
      (σ := {i // keepLong i}) FQ e ω hF
      adapted.model.basis adapted.weight adapted.model_layers ψ hψ
      hentries hpProj hsource (by simpa only [Fintype.card_fin] using htarget) hheight
      den hden (hdenBound.trans (Real.exp_le_exp.mpr hqProj))
  obtain ⟨hvQ, hWQ, hvQH⟩ :=
    F₀.gradedImage_bounded_spanning FQ ψ hψ e ω hF
      adapted.model.basis adapted.weight adapted.model_layers W v hv hW
      hpProj hsource (fun a i => (hvH a i).trans hqProj)
      (fun i j => rationalLogHeight_le_of_height (hentries j i) hheight)
  have hfactorLong (z : source.productive) :
      F₀.HasCommonRefilteredOrbitFactors e ω hF
        (fun i : {i // keepLong i} => (A.sides i.val : ℝ)) qCommon den W
        (F₀.weightedAdaptedRealChartHom
          (fun _ : {i // keep i} => 1) (fun _ : {i // keepLong i} => 1)
          ((source.chart z).axisPolynomial keepLong (fun _ => 0))
          ((source.chart z).axisPolynomial_support keepLong (fun _ => 0))
          (F₀.realification.polynomialOrbitCoordinates (fun _ => 1)
            ((source.optionJoint (fun j => (F.native j).model)
              (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)).candidate z).orbit)) := by
    have hc := hfactor z.val z.property
    change F₀.HasCommonRefilteredOrbitFactors e ω hF
      (fun i : {i // keepLong i} => (A.sides i.val : ℝ)) qCommon den W
      (F₀.realification.polynomialOrbitCoordinates (fun _ => 1)
        (piRealOrbit (fun i => (optionFactors D (fun j => (F.native j).model) i).filtration)
          (F.longJointOrbit keepLong z.val))) at hc
    rw [F.longJointOrbit_polynomialCoordinates keepLong z.val] at hc
    exact hc
  refine ⟨retained, hsub, hmass, hpos, theta, W, v, den, hv, hW, hvH, hzero,
    hden, hdenBound, denQ, hdenQ, hdenQBound, hdiv, hvQ, hWQ, hvQH, ?_, ?_, ?_⟩
  · intro z
    have ht := htransport (fun i => (A.sides i.val : ℝ))
      (fun i => by exact_mod_cast A.sides_pos i.val) qCommon W _ (hfactorLong z)
    have he := ((source.withKeep keep (fun _ => rfl)).candidate z).optionJoint_lieQuotient_chart_polynomialCoordinates
        (D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (by rw [D.filtration.terminal]; exact bot_le) Q hQ hker
        (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)
        ((target.chart z).axisPolynomial keepLong (fun _ => 0))
        ((target.chart z).axisPolynomial_support keepLong (fun _ => 0))
    exact Eq.mpr (congrArg
      (FQ.HasCommonRefilteredOrbitFactors adapted.model.basis adapted.weight adapted.model_layers
        (fun i : {i // keepLong i} => (A.sides i.val : ℝ)) ((pProj + 2) ^ 3 + qCommon) denQ
        (W.map (F₀.associatedGradedMap FQ ψ hψ))) he) ht
  · exact optionNativeCommonPivotQuotientFast_top_kernel_eq_zero
      D (fun j => (F.native j).model) φ F.η js hker W theta hzero Q hQ
      e ω hF adapted.basis adapted.weight adapted.layers hW
  · exact optionNativeCommonPivotQuotientFast_graded_top_kernel
      D (fun j => (F.native j).model) φ F.η js hker W theta hzero Q hQ
      e ω hF adapted.basis adapted.weight adapted.layers hW

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

end OAI
end


