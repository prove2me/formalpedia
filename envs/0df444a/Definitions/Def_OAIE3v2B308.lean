-- Prove2me | Definitions.Def_OAIE3v2B308
-- name    : OAIE3v2B308
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T07:22:57.119055+00:00
-- url     : https://prove2.me/theorems/a5c7280e-83b2-4c9a-aa78-78878fedf1af
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 285 of 311
-- statement:
--   Definitions bundle 285 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B260`, `OAIE3v2B273` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidateAxisFreezingConclusion.lean`, `Lattices/AllocatedAffineCanonicalBackendBudget.lean`, `Lattices/AllocatedAffinePhysicalTerminalReset.lean`, `Lattices/CertifiedAffineNormalizedBudget.lean`, `Linear/AllocatedExternalCandidateCommonKeepPositiveKernelPreparation.lean`, `Polynomial/AllocatedNestedDegreeInduction.lean`, `Sampling/PreparedRelativePositiveForecastSource.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B260
import Definitions.Def_OAIE3v2B273

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAxisFreezingConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

attribute [local irreducible] integerProgressionSupport IsDenseCommonStrideBox ResidueBoxSlice.integerPoints

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

variable {P} {keep : P.productive → LayerSamplerVariables G I n B → Prop}
    {shortCost : ℝ} (freezing : P.AxisFreezing keep shortCost)

theorem extendSlice_dense (z : P.productive) {step : ℕ}
    (slice : ResidueBoxSlice (fun i : {i // keep z i} => A.sides i.val) step)
    (hstep : 0 < step) {outputCost : ℝ}
    (hdense : IsDenseCommonStrideBox (fun i : {i // keep z i} => A.sides i.val)
      outputCost slice.integerPoints) :
    IsDenseCommonStrideBox (fun i : (P.chart z).Variables => A.sides i.val)
      (max outputCost shortCost) (freezing.extendSlice z slice).integerPoints :=
by
  have h := slice.extendAxes_dense (N := A.sides)
    (oldKeep := (P.chart z).keep) (keep := keep z)
    (P.chart z).slice (freezing.fixed z) (freezing.fixed_mem z) hstep
    (outCost := outputCost) (by
      simpa only [isDenseCommonStrideBox_classical_iff,
        ResidueBoxSlice.integerPoints_classical_eq] using hdense)
    (freezing.removed_side z)
  simpa only [isDenseCommonStrideBox_classical_iff,
    ResidueBoxSlice.integerPoints_classical_eq, extendSlice] using h

theorem extendSlice_inside (z : P.productive) {step : ℕ}
    (slice : ResidueBoxSlice (fun i : {i // keep z i} => A.sides i.val) step)
    (hinside : slice.integerPoints ⊆ (freezing.problem.chart z).slice.integerPoints) :
    (freezing.extendSlice z slice).integerPoints ⊆ (P.chart z).slice.integerPoints :=
by
  intro x hx
  have hx' : x ∈ (slice.extendAxes (N := A.sides)
      (oldKeep := (P.chart z).keep) (keep := keep z)
      (P.chart z).slice (freezing.fixed z) (freezing.fixed_mem z)).integerPoints := by
    simpa only [ResidueBoxSlice.integerPoints_classical_eq, extendSlice] using hx
  have haxis : ResidueBoxSlice.axisInsertion (P.chart z).keep (keep z) (freezing.fixed z) =
      (P.chart z).axisPoint (keep z) (freezing.fixed z) := rfl
  have himage := slice.extendAxes_integerPoints (N := A.sides)
    (oldKeep := (P.chart z).keep) (keep := keep z)
    (P.chart z).slice (freezing.keep_subset z) (freezing.fixed z) (freezing.fixed_mem z)
  simp only [ResidueBoxSlice.integerPoints_classical_eq, haxis] at himage
  simp only [ResidueBoxSlice.integerPoints_classical_eq] at hx'
  rw [himage] at hx'
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx'
  apply freezing.problem_slice_inside z
  apply hinside
  simpa only [ResidueBoxSlice.integerPoints_classical_eq] using hu

noncomputable def conclusion {outputCost outputMass outputScore : ℝ}
    (out : freezing.problem.Conclusion outputCost outputMass outputScore) :
    P.Conclusion (max outputCost shortCost) outputMass outputScore where
  ambient := out.ambient
  marked := out.marked
  retained := out.retained
  subset := freezing.conclusion_subset out
  mass := out.mass
  step := out.step
  step_pos := out.step_pos
  slice z := freezing.extendSlice ⟨z.val, freezing.conclusion_subset out z.property⟩ (out.slice z)
  dense z := freezing.extendSlice_dense ⟨z.val, freezing.conclusion_subset out z.property⟩
    (out.slice z) (out.step_pos z) (out.dense z)
  inside z := freezing.extendSlice_inside ⟨z.val, freezing.conclusion_subset out z.property⟩
    (out.slice z) (out.inside z)
  score z := (out.score z).trans_eq
    (freezing.ambientScore_extendSlice out.ambient
      ⟨z.val, freezing.conclusion_subset out z.property⟩ (out.slice z)).symm

end AxisFreezing
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

namespace CertifiedThresholdAffineRefinement

variable {P} {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p separation : ℝ}
    (selected : P.CertifiedThresholdAffineRefinement K p separation)

noncomputable def conclusion {outputCost outputMass outputScore : ℝ}
    (out : selected.problem.Conclusion outputCost outputMass outputScore) :
    P.Conclusion (max outputCost (candidateSideCutoffCost separation)) outputMass outputScore :=
  selected.freezing.conclusion (selected.affine.refinement.conclusion out)

end CertifiedThresholdAffineRefinement

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.CertifiedThresholdAffineRefinement

variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p separation : ℝ}

theorem original_dense (selected : P.CertifiedThresholdAffineRefinement K p separation)
    (z : selected.problem.productive) :
    IsDenseCommonStrideBox
      (fun i : (selected.problem.chart z).Variables => A.sides i.val) cost
      (selected.problem.chart z).slice.integerPoints := by
  rw [selected.affine.slice_points z]
  exact selected.freezing.problem_slice_dense
    ⟨z.val, selected.affine.refinement.subset z.property⟩

end AllocatedExternalCandidateProblem.CertifiedThresholdAffineRefinement
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffinePhysicalTerminalReset
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct BigOperators
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realChartSubstitute PolynomialRationalGrid PolynomialSlowBound
  CertifiedFullChartFiniteHistory.outer

theorem exists_allocatedCertifiedAffineControlledGlobalTerminal (t a : ℕ) :
    ∃ Ce Cr : ℕ, 2 ≤ Ce ∧ 2 ≤ Cr ∧
    ∀ {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
      {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
      {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ i, Fintype (B i)]
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
      {sampler : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
      {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
      {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
      {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
      {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
      {cost massThreshold scoreThreshold : ℝ}
      (P : AllocatedExternalCandidateProblem (E := E) sampler D Fmark φ marked observable weight
        cost massThreshold scoreThreshold)
      {ι η : Type} [Fintype ι] [Fintype η]
      (bF : Basis ι ℚ M) (ω : ι → ℕ)
      (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ω i}))
      (W : LieSubalgebra ℚ Fmark.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (Fmark.AssociatedGraded ⧸ W.toSubmodule)))
      (lift : (Fmark.AssociatedGraded ⧸ W.toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
      (Z : Fmark.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (Bphase budget pAffine : ℝ)
      (history : CertifiedFullChartFiniteHistory Fmark bF ω hF J W.toSubmodule basis lift
        Z Set.univ U poly N Bphase t)
      (affine : P.CertifiedAffineRefinement history.K pAffine),
      BasisGradedSubmodule (Fmark.associatedGradedBasis bF ω hF) ω W.toSubmodule →
      FullChartControlledFactors Fmark bF ω hF J poly N history.outer.1 history.outer.2 budget →
      (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
      Fmark.realPolynomialSymbolHom bF ω hF (fullTaggedVariableWeight (X := X) J)
        (Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked) = Z →
      τ ≤ 1 → ξ ≤ 1 → (∀ j, σ j ≤ 1) →
    ∀ (Cgeo : Fin m → ℝ), (∀ j, 0 ≤ Cgeo j) →
      (∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖) →
      (∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1) →
    ∀ (H : ℕ) (pFull : ℝ), 1 ≤ H → 0 ≤ pFull →
      (Fintype.card ι : ℝ) ≤ pFull →
      (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ pFull →
      (H : ℝ) ≤ Real.exp pFull →
      Real.exp budget * (Real.exp ((m : ℝ) * certifiedAffineCenterBudget pAffine)) ^ t ≤
        Real.exp pFull →
      (∀ i j k, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ k) H) →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pFull →
      (((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ t * Real.exp budget *
        (actualCandidateSlowProjectionMassBudget m
          (Fintype.card (LayerSamplerVariables G I n B)) pFull
          (((pAffine + ((pAffine+2)^2+2)^63)+2)^8)) ^ t ≤ Real.exp ((pFull + 2) ^ a)) →
      let wt := fullTaggedVariableWeight (X := X) J
      let β := affine.globalChart
      let δ := affine.slowChart
      let pull := Fmark.realSymbolHomogeneousPullbackHom bF ω hF wt wt
        (fun i => weightedHomogeneousComponent wt (wt i) (β i))
        (fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      0 < affine.commonDenominator ∧
      (affine.commonDenominator : ℝ) ≤ Real.exp ((m : ℝ) * certifiedAffineCenterBudget pAffine) ∧
      ∃ q nFinal : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
        0 < nFinal ∧ (nFinal : ℝ) ≤ Real.exp ((pFull + Cr) ^ Cr) ∧
        q * affine.commonDenominator ^ t ∣ nFinal ∧
        ∃ factors : GlobalMarkedNativeFactors Fmark bF ω hF wt W
          (Fmark.weightedAdaptedRealChartHom wt wt β affine.globalChart_support
            (Fmark.realification.polynomialOrbitCoordinates wt marked))
          (pull history.outer.1) (pull history.outer.2),
          Fmark.PolynomialRationalGrid bF wt nFinal factors.right ∧
          (∀ z : affine.refinement.problem.productive,
            let C := affine.refinement.problem.chart z
            Fmark.PolynomialSlowBound bF (fun _ : C.Variables => 1)
              (fun i => (sampler.sides i.val : ℝ)) (Real.exp ((pFull + Ce) ^ Ce))
              (Fmark.weightedAdaptedRealChartHom wt (fun _ : C.Variables => 1)
                (integerSampledRealChart C.integerChart) C.integerChart_support factors.left)) ∧
          ∀ {Υ : Type} [Fintype Υ] (v : Υ → ℕ), (∀ i, 0 < v i) →
            (Fintype.card Υ : ℝ) ≤ pFull →
            ∀ (γ : (X ⊕ (Σ j, J j)) → MvPolynomial Υ ℝ)
              (hγ : ∀ i, γ i ∈ weightedSupportLE v (wt i))
              (T : Υ → ℝ), (∀ i, 0 < T i) →
            ∀ mass : ℝ, 1 ≤ mass →
              (∀ i, realPolynomialMass
                (scaleMvPolynomialAxes T (MvPolynomial.aeval γ (δ i))) ≤ mass) →
              (((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ t *
                Real.exp budget * mass ^ t ≤ Real.exp ((pFull + 2) ^ a)) →
              Fmark.PolynomialSlowBound bF v T (Real.exp ((pFull + Ce) ^ Ce))
                (Fmark.weightedAdaptedRealChartHom wt v γ hγ factors.left) := by
  classical
  obtain ⟨Ce, Cr, hCe, hCr, hterminal⟩ := exists_allocatedCertifiedAffineGlobalTerminal t a
  refine ⟨Ce, Cr, hCe, hCr, ?_⟩
  intro m G X _ _ I E J _ _ n B _ U btag Rad σ S hb o hRad hσ N poly hm
    τ ξ stride cells center _ sampler L M _ _ _ _ s d D Fmark φ marked observable weight
    cost massThreshold scoreThreshold P ι η _ _ bF ω hF W basis lift Z Bphase budget pAffine
    history affine hW hcontrol hpoly hZ hτ1 hξ1 hσ1 Cgeo hCgeo hchart hsmall
    H pFull hH hpFull hι hvars hHp hden hbracket hsample hmass
  obtain ⟨hDpos, hDbound, q, nFinal, hq, hqB, hn, hnB, hdiv, factors, hgrid, hslow⟩ :=
    hterminal P bF ω hF W basis lift Z Bphase budget pAffine history affine hW hcontrol
      hpoly hZ H pFull hH hpFull hι hvars hHp hden hbracket
  refine ⟨hDpos, hDbound, q, nFinal, hq, hqB, hn, hnB, hdiv, factors,
    hgrid, ?_, hslow⟩
  intro z
  let C := affine.refinement.problem.chart z
  have hretained (x) (hx : ∀ j, (fun i => x (Sum.inr ⟨j,i⟩)) ∈ U j) : x ∈ history.K :=
    history.retained x (Set.mem_univ _) hx
  have hdim (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ pFull := by
    exact (Nat.cast_le.mpr (Fintype.card_le_of_injective
      (fun i : J j => (Sum.inr ⟨j,i⟩ : X ⊕ (Σ j,J j)))
      (by intro i k h; simpa using h))).trans hvars
  have hlocal : (Fintype.card C.Variables : ℝ) ≤ pFull :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le C.keep)).trans hsample
  have hside (i : C.Variables) : (0 : ℝ) < sampler.sides i.val :=
    Nat.cast_pos.mpr (sampler.sides_pos i.val)
  apply hslow (fun _ : C.Variables => 1) (fun _ => Nat.zero_lt_one) hlocal
    (integerSampledRealChart C.integerChart) C.integerChart_support
    (fun i => (sampler.sides i.val : ℝ)) hside
    (actualCandidateSlowProjectionMassBudget m
      (Fintype.card (LayerSamplerVariables G I n B)) pFull
      (((pAffine + ((pAffine+2)^2+2)^63)+2)^8))
    (actualCandidateSlowProjectionMassBudget_one_le _ _ hpFull) ?_ hmass
  intro i
  exact affine.slowChart_mass_sides hretained hpFull hdim hτ1 hξ1 hpoly hσ1
    Cgeo hCgeo hchart hsmall z i

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineCanonicalBackendBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open NilpotentLieFiltration

theorem allocatedAffineResetLogBudget_nonnegative (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ allocatedAffineResetLogBudget s p := by
  unfold allocatedAffineResetLogBudget markedNativeLiftInput fullMarkedNativeInput
    pointwiseFastSectionInput
  positivity

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
open scoped BigOperators Classical TensorProduct

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

theorem positive_mass : 0 < A.law.mass selected.retained :=
  (mul_pos hpos (Real.exp_pos _)).trans_le selected.mass

end PrecenterKernelSelection
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

local instance degreeSourceProfileSiteNonempty : Nonempty A.Site := A.site_nonempty

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedRelativePositiveForecastSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

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

local instance instNonemptySite : Nonempty A.Site := A.site_nonempty

end Erdos3.VectorPolynomial

end

end OAI
end


