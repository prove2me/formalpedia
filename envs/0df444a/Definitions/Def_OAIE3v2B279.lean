-- Prove2me | Definitions.Def_OAIE3v2B279
-- name    : OAIE3v2B279
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T07:35:23.805314+00:00
-- url     : https://prove2.me/theorems/1ea36a27-7e44-409c-8248-d75b7d82bfc3
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 291 of 311
-- statement:
--   Definitions bundle 291 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B308` of this split.
--
--   Modules: `Lattices/AllocatedAffineCanonicalBackendBudget.lean`, `Lattices/AllocatedAffinePhysicalTerminalReset.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B308

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffinePhysicalTerminalReset
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct BigOperators Classical
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realChartSubstitute PolynomialRationalGrid PolynomialSlowBound
  CertifiedFullChartFiniteHistory.outer

theorem exists_allocatedCertifiedAffineGlobalPhysicalTerminal (t a : ℕ) :
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
          (∀ x ∈ integerBox N, ∀ i,
            |(bF.baseChange ℝ).repr
              (Fmark.realification.polynomialOrbitEval wt (P.physicalIntegerPoint x)
                ((Fmark.realification.polynomialOrbitCoordinates wt).symm factors.left)).coord i| ≤
              Real.exp ((pFull + Ce) ^ Ce)) ∧
          (∀ x : X → ℤ, (bF.baseChange ℝ).equivFun
            (Fmark.realification.polynomialOrbitEval wt (P.physicalIntegerPoint x)
              ((Fmark.realification.polynomialOrbitCoordinates wt).symm factors.right)).coord ∈
              realDenominatorGrid nFinal) ∧
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
  obtain ⟨Ce, Cr, hCe, hCr, hterminal⟩ :=
    exists_allocatedCertifiedAffineControlledGlobalTerminal t a
  refine ⟨Ce, Cr, hCe, hCr, ?_⟩
  intro m G X _ _ I E J _ _ n B _ U btag Rad σ S hb o hRad hσ N poly hm
    τ ξ stride cells center _ sampler L M _ _ _ _ s d D Fmark φ marked observable weight
    cost massThreshold scoreThreshold P ι η _ _ bF ω hF W basis lift Z Bphase budget pAffine
    history affine hW hcontrol hpoly hZ hτ1 hξ1 hσ1 Cgeo hCgeo hchart hsmall
    H pFull hH hpFull hι hvars hHp hden hbracket hsample hmass
  obtain ⟨hDpos, hDbound, q, nFinal, hq, hqB, hn, hnB, hdiv, factors,
      hgrid, hlocal, hcharts⟩ :=
    hterminal P bF ω hF W basis lift Z Bphase budget pAffine history affine hW hcontrol
      hpoly hZ hτ1 hξ1 hσ1 Cgeo hCgeo hchart hsmall H pFull hH hpFull hι hvars hHp
      hden hbracket hsample hmass
  refine ⟨hDpos, hDbound, q, nFinal, hq, hqB, hn, hnB, hdiv, factors,
    hgrid, hlocal, ?_, ?_, hcharts⟩
  · intro x hx i
    have hretained (y) (hy : ∀ j, (fun i => y (Sum.inr ⟨j,i⟩)) ∈ U j) : y ∈ history.K :=
      history.retained y (Set.mem_univ _) hy
    have hdim (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ pFull := by
      exact (Nat.cast_le.mpr (Fintype.card_le_of_injective
        (fun i : J j => (Sum.inr ⟨j,i⟩ : X ⊕ (Σ j,J j)))
        (by intro i k h; simpa using h))).trans hvars
    rw [← Fmark.realification.polynomialOrbitRealEval_integer,
      Fmark.nativeFrozenMarkedOrbitCoordinates_symm_realEval]
    apply Fmark.value_bound_of_terminal_chart_control bF (fullTaggedVariableWeight J)
      affine.slowChart pFull budget a Ce hpFull factors.left hcharts _
      (actualCandidateSlowProjectionMassBudget m
        (Fintype.card (LayerSamplerVariables G I n B)) pFull
        (((pAffine + ((pAffine+2)^2+2)^63)+2)^8))
      (actualCandidateSlowProjectionMassBudget_one_le _ _ hpFull) ?_ hmass i
    intro z
    exact (affine.slowChart_physical_abs_le hretained hdim x hx z).trans
      (actualCandidateSlowProjectionMassBudget_max_le _ _ hpFull)
  · intro x
    rw [← Fmark.realification.polynomialOrbitRealEval_integer,
      Fmark.nativeFrozenMarkedOrbitCoordinates_symm_realEval]
    exact Fmark.polynomialRationalGrid_value bF (fullTaggedVariableWeight J)
      nFinal factors.right hgrid (P.physicalIntegerPoint x)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped Classical TensorProduct BigOperators
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

noncomputable def allocatedEarlyAffineLeftExponent (s a : ℕ) : ℕ :=
  Classical.choose (exists_allocatedCertifiedAffineGlobalPhysicalTerminal s a)

noncomputable def allocatedEarlyAffineRightExponent (s a : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (exists_allocatedCertifiedAffineGlobalPhysicalTerminal s a))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedAffineResetNativeBudget (s : ℕ) (pFull pMap q : ℝ) : ℝ :=
  affineResetNativeBudget (allocatedEarlyAffineLeftExponent (s + 1) 4) pFull pMap q

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

noncomputable def allocatedAffineResetRightLog (s : ℕ) (pFull : ℝ) : ℝ :=
  (pFull + allocatedEarlyAffineRightExponent (s + 1) 4) ^
    allocatedEarlyAffineRightExponent (s + 1) 4

noncomputable def allocatedAffineResetLeftLog (s : ℕ) (pFull : ℝ) : ℝ :=
  (pFull + allocatedEarlyAffineLeftExponent (s + 1) 4) ^
    allocatedEarlyAffineLeftExponent (s + 1) 4

noncomputable def allocatedAffineResetMapBudget (s : ℕ) (p0 pFull : ℝ) : ℝ :=
  ordinaryImagePointwiseBudget (s + 1) (s + 1) p0 + allocatedAffineResetHeightLog p0 + 1 + p0 +
    allocatedAffineResetRightLog s pFull

noncomputable def allocatedAffineCanonicalNativeBudget (s : ℕ) (p0 pFull : ℝ) : ℝ :=
  allocatedAffineResetNativeBudget s pFull (allocatedAffineResetMapBudget s p0 pFull) p0

noncomputable def allocatedAffineCanonicalBudget (s : ℕ) (p0 pFull : ℝ) : ℝ :=
  p0 + pFull + allocatedAffineResetMapBudget s p0 pFull +
    allocatedAffineCanonicalNativeBudget s p0 pFull +
    allocatedAffineResetLogBudget s (allocatedAffineCanonicalNativeBudget s p0 pFull) +
    allocatedAffineResetCompareLog s (allocatedAffineCanonicalNativeBudget s p0 pFull) +
    allocatedAffineResetLeftLog s pFull + (s + 2 : ℕ)

structure AllocatedAffineResetMapBudgetBounds (s : ℕ) (p0 pFull : ℝ) : Prop where
  nonnegative : 0 ≤ allocatedAffineResetMapBudget s p0 pFull
  input : p0 ≤ allocatedAffineResetMapBudget s p0 pFull
  pointwise : ordinaryImagePointwiseBudget (s + 1) (s + 1) p0 ≤
    allocatedAffineResetMapBudget s p0 pFull
  height : allocatedAffineResetHeightLog p0 + 1 ≤ allocatedAffineResetMapBudget s p0 pFull
  denominatorLog : p0 + allocatedAffineResetRightLog s pFull ≤
    allocatedAffineResetMapBudget s p0 pFull

structure AllocatedAffineCanonicalBudgetBounds (s : ℕ) (p0 pFull : ℝ) : Prop where
  nonnegative : 0 ≤ allocatedAffineCanonicalBudget s p0 pFull
  map_nonnegative : 0 ≤ allocatedAffineResetMapBudget s p0 pFull
  native_nonnegative : 0 ≤ allocatedAffineCanonicalNativeBudget s p0 pFull
  input : p0 ≤ allocatedAffineCanonicalBudget s p0 pFull
  full : pFull ≤ allocatedAffineCanonicalBudget s p0 pFull
  map : allocatedAffineResetMapBudget s p0 pFull ≤ allocatedAffineCanonicalBudget s p0 pFull
  native : allocatedAffineCanonicalNativeBudget s p0 pFull ≤ allocatedAffineCanonicalBudget s p0 pFull
  native_input : p0 ≤ allocatedAffineCanonicalNativeBudget s p0 pFull
  native_full : pFull ≤ allocatedAffineCanonicalNativeBudget s p0 pFull
  native_map : allocatedAffineResetMapBudget s p0 pFull ≤ allocatedAffineCanonicalNativeBudget s p0 pFull
  reset : allocatedAffineResetLogBudget s (allocatedAffineCanonicalNativeBudget s p0 pFull) ≤
    allocatedAffineCanonicalBudget s p0 pFull
  compare : allocatedAffineResetCompareLog s (allocatedAffineCanonicalNativeBudget s p0 pFull) ≤
    allocatedAffineCanonicalBudget s p0 pFull
  physical : allocatedAffineResetLeftLog s pFull ≤ allocatedAffineCanonicalBudget s p0 pFull
  interpolation_log : p0 + (s + 2 : ℕ) ≤ allocatedAffineCanonicalBudget s p0 pFull

structure AllocatedAffineCanonicalExpBounds (s : ℕ) (p0 pFull : ℝ) : Prop where
  map_absorption : Real.exp ((allocatedAffineResetMapBudget s p0 pFull + 2) ^ 4) ≤
    Real.exp (allocatedAffineCanonicalNativeBudget s p0 pFull)
  physical_absorption : Real.exp (allocatedAffineResetLeftLog s pFull) ≤
    Real.exp ((allocatedAffineCanonicalNativeBudget s p0 pFull + 2) ^ (1 : ℕ))
  original_absorption : Real.exp p0 ≤
    Real.exp ((allocatedAffineCanonicalNativeBudget s p0 pFull + 2) ^ (1 : ℕ))
  mapped_absorption : Real.exp ((allocatedAffineResetMapBudget s p0 pFull + 2) ^ 3 + p0) ≤
    Real.exp ((allocatedAffineCanonicalNativeBudget s p0 pFull + 2) ^ (1 : ℕ))
  compare_cutoff : Real.exp
      (allocatedAffineResetCompareLog s (allocatedAffineCanonicalNativeBudget s p0 pFull)) ≤
    Real.exp (candidatePrimitiveFreezingCutoff s 1 (allocatedAffineCanonicalBudget s p0 pFull))
  cost_cutoff : ∀ cost : ℝ, cost ≤ p0 → Real.exp cost ≤
    Real.exp (candidatePrimitiveFreezingCutoff s 1 (allocatedAffineCanonicalBudget s p0 pFull))
  interpolation : ∀ cost : ℝ, cost ≤ p0 → Real.exp cost * (s + 2 : ℕ) ≤
    Real.exp (candidatePrimitiveFreezingCutoff s 1 (allocatedAffineCanonicalBudget s p0 pFull))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open NilpotentLieFiltration

structure AllocatedAffineCanonicalBackendBounds (s : ℕ) (p0 pFull upper : ℝ) : Prop where
  canonical : allocatedAffineCanonicalBudget s p0 pFull ≤ upper
  recursive : finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
    (allocatedAffineCanonicalBudget s p0 pFull) ≤ upper
  cutoff : candidatePrimitiveFreezingCutoff s 1
    (allocatedAffineCanonicalBudget s p0 pFull) ≤ upper
  cutoff_cost : candidateSideCutoffCost
    (Real.exp (candidatePrimitiveFreezingCutoff s 1
      (allocatedAffineCanonicalBudget s p0 pFull))) ≤ upper

end Erdos3.VectorPolynomial

end

end OAI
end


