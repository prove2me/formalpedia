-- Prove2me | Definitions.Def_OAIE3v2B292
-- name    : OAIE3v2B292
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T08:45:41.038996+00:00
-- url     : https://prove2.me/theorems/2d6fe5f5-cab4-4e80-b78a-18cef453628c
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 305 of 311
-- statement:
--   Definitions bundle 305 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B288`, `OAIE3v2B289` of this split.
--
--   Modules: `Dynamics/PreparedFiniteNestedFrontNativeBudget.lean`, `Estimates/AllocatedExternalCandidatePreparedPhysicalConclusion.lean`, `Estimates/AllocatedExternalCandidatePrimitiveFrontDescentData.lean`, `Lattices/AllocatedAffinePhysicalBoundsSuccessor.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B288
import Definitions.Def_OAIE3v2B289

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

noncomputable def frontRawMassLoss : ℝ :=
  2 * p + AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) +
    p * (AllocatedExternalCandidateProblem.positiveKernelPreparationBinLog (2 * p) e +
      source.frontTermLog) + 2

structure LossBudget : Prop where
  projection_nonneg :
    0 ≤ AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p)
  bin_nonneg : 0 ≤ AllocatedExternalCandidateProblem.positiveKernelPreparationBinLog (2 * p) e
  bin_le_u : AllocatedExternalCandidateProblem.positiveKernelPreparationBinLog (2 * p) e ≤ source.u
  model_nonneg : 0 ≤ source.frontModelBudget
  model_bound : source.frontModelBudget ≤ 6 * source.familyCap + 20
  term_bound : source.frontTermLog ≤ 18 * source.familyCap + 74
  localPrecision : AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) ≤
    source.familyParameter
  correlation_nonneg : 0 ≤ source.frontCorrelationLoss
  correlation : source.frontCorrelationLoss ≤ source.familyParameter
  rawMass_nonneg : 0 ≤ source.frontRawMassLoss
  rawMass : source.frontRawMassLoss ≤ source.familyParameter

theorem lossBudget (hp : 0 ≤ p) : source.LossBudget := by
  have hp2 : 0 ≤ 2 * p := by positivity
  have hq := AllocatedExternalCandidateProblem.positiveKernelPreparationParameter_nonneg hp2
  have hbin := AllocatedExternalCandidateProblem.positiveKernelPreparationBinLog_nonneg hp2 e
  have hmarkov := source.markov_precision
  unfold AllocatedExternalCandidateProblem.positiveKernelMarkovPrecisionParameter at hmarkov
  have hbinU : AllocatedExternalCandidateProblem.positiveKernelPreparationBinLog (2 * p) e ≤
      source.u := by linarith only [hmarkov, hp, hq, hbin]
  obtain ⟨_, hpCap, hqCap, huCap, hmodelCap, hnativeCap, _, _, hcap⟩ :=
    source.familyCap_bounds hp
  obtain ⟨hQ0, hQ, hr0, hr, hM0, hM⟩ := candidateFrontSourceLossBounds
    source.familyCap p
    (AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p))
    source.u source.pModel source.nativeBudget
    (AllocatedExternalCandidateProblem.positiveKernelPreparationBinLog (2 * p) e)
    hcap hp hq source.u_nonneg source.model_nonneg source.native_nonneg hbin
    hpCap hqCap huCap hmodelCap hnativeCap hbinU
  refine ⟨hq, hbin, hbinU, hQ0, hQ, ?_, (source.familyBudget hp).projection,
    ?_, ?_, hM0, hM⟩
  · dsimp only [frontTermLog, frontModelBudget]
    linarith only [hQ, huCap, hmodelCap]
  · dsimp only [frontCorrelationLoss, frontModelBudget]
    linarith only [hr0]
  · change _ ≤ candidateFrontFamilyParameter source.familyCap
    dsimp only [frontCorrelationLoss, frontModelBudget, candidateFrontFamilyParameter]
    linarith only [hr]

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

theorem factorGeometryBudget (hp : 0 ≤ p) : source.FactorGeometryBudget := by
  have family := source.familyBudget hp
  have loss := source.lossBudget hp
  have hP := family.hpFamily
  have hdesc : 0 ≤ (source.familyParameter + 2) ^
      RationalFilteredNilmanifold.positiveKernelNativeDescentExponent degree := by positivity
  have hvertical : 0 ≤ 3 * source.familyParameter + 1 := by positivity
  have hdecomp := verticalDecompositionBudget_nonneg hvertical
  have hn := family.native
  have hl := family.projection
  have hr := loss.correlation
  refine ⟨?_, ?_, ?_, ?_, ?_, hvertical, ?_, ?_, ?_, ?_⟩
  · dsimp only [geometryBudget]
    linarith only [hP, hdesc]
  · dsimp only [geometryBudget]
    linarith only [hdesc]
  · dsimp only [geometryBudget]
    linarith only [hP]
  · dsimp only [factorBudget]
    linarith only [hP, hdecomp]
  · dsimp only [factorBudget]
    linarith only [hP, hdecomp]
  · linarith only [hP, hn]
  · linarith only [hP, hl, hr]
  · dsimp only [factorBudget]
    linarith only [hP]
  · dsimp only [factorBudget]
    linarith only [hP, hr]

end AllocatedExternalCandidateSampler.FrontSourceProfile
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
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  symbolPointwiseSubalgebra realificationLieSubalgebra PolynomialRationalGrid PolynomialSlowBound
  HasCommonRefilteredOrbitFactors polynomialOrbitCoordinates associatedGradedMap realPolynomialGroupMap
  AllocatedExternalCandidateProblem.Refinement.problem
  realSymbolHomogeneousPullbackHom CertifiedFullChartFiniteHistory.outer

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

include data in
theorem conclusion_of_affinePhysicalTerminal_bounds_degreeRule
    {γ : Type} [Fintype γ]
    (p0 : ℝ) (hp0 : 0 ≤ p0) (hpFull : 0 ≤ pFull)
    (hDgeo : D.GeometryComplexityLE p0) (hFgeo : Fmark.GeometryComplexityLE p0)
    (hcForward : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p0)
    (hMap : ∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p0)
    (ω : Fin d → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (D.basis '' {i | j ≤ ω i}))
    (v : γ → D.filtration.AssociatedGraded)
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hD) ω W.toSubmodule)
    (hvspan : span ℚ (Set.range v) = W.toSubmodule)
    (hγ : (Fintype.card γ : ℝ) ≤ p0)
    (hvHeight : ∀ j i, rationalLogHeight
      ((D.filtration.associatedGradedBasis D.basis ω hD).repr (v j) i) ≤ p0)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p0)
    (q : ℝ) (l : ℕ) (hq0 : q ≤ p0) (hl : 0 < l) (hlBound : (l : ℝ) ≤ Real.exp p0)
    (hcost0 : cost ≤ p0)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hshort : ∀ i, ¬initialLong i → (A.sides i : ℝ) ≤ Real.exp p0)
    (hzero : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors D.basis ω hD
        (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
        (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
          (fun _ : {i // initialLong i} => 1) ((P.chart z).axisPolynomial initialLong (fun _ => 0))
          ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
          (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) (P.candidate z).orbit)))
    (hseparation : separation = Real.exp (candidatePrimitiveFreezingCutoff s 1
      (allocatedAffineCanonicalBudget s p0 pFull)))
    (hσ1 : ∀ j, σ j ≤ 1)
    (Hchart : Fin m → ℝ) (hHchart : ∀ j, 0 ≤ Hchart j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Hchart j * ‖v‖)
    (hsmall : ∀ j, Hchart j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p0)
    (hscore : Real.exp (-p0) ≤ scoreThreshold)
    (hmass : Real.exp (-p0) ≤
      Real.exp (-((2 * certifiedAffineCenterBudget pAffine + 3) ^ 3)) * massThreshold)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1) (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p0)
    (hLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hmark : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p0)
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
    Nonempty (P.Conclusion (max outputCost (candidateSideCutoffCost separation))
      (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  have hc := (D.nativeResetBracketGeometry Fmark c hp0 hDgeo hFgeo hcForward).2.1
  let input := data.successorInputsOfBounds p0 hp0 hpFull hseparation hDgeo hFgeo
    hvariables (by simpa only [Fintype.card_fin] using hc) hMap hσ1 Hchart hHchart hchart
    hsmall hpoly hweight hscore hcost0 hmass ω hD hW hsurj hξ1 ℓ hℓ hLip hpositive
    v hvspan hγ hcForward hmark hvHeight htop hnet outputCost lowerIH
  exact P.conclusion_of_normalized_affinePhysicalTerminal_zeroRestricted_degreeRule
    Fmark φ hφ W c ν hF basis lift Bphase budget pAffine pFull separation history data
    p0 hp0 hpFull hDgeo hFgeo hcForward hMap ω hD v hW hvspan hγ hvHeight hvariables
    q l hq0 hl hlBound hcost0 initialLong hshort hzero input

end AllocatedExternalCandidateProblem
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

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace CommonKeepPositiveKernelPreparation
variable {P} {p : ℝ} {e : ℕ} (front : P.CommonKeepPositiveKernelPreparation p e)

theorem exists_sourceProfile_spatialNativeFamily
    (source : A.DegreeSourceProfile s p e)
    (hp : 0 ≤ p) (hcost0 : 0 ≤ cost) (hcost : cost ≤ p)
    (hD : D.GeometryComplexityLE p)
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p)
    (hmass : Real.exp (-p) ≤ massThreshold) :
    let q := positiveKernelPreparationParameter (2 * p)
    let binLog := positiveKernelPreparationBinLog (2 * p) e
    let commonBudget := max source.front.nativeBudget 3
    let Qmodel := max commonBudget (2 * source.front.u + 4 * source.front.pModel + 20)
    let coefficientLog := Qmodel + 2
    let termLog := 2 * Qmodel + 2 * source.front.u + 4 * source.front.pModel + 34
    ∃ (retained : Finset A.Path), retained ⊆ front.prep.selected.retained ∧
      0 < A.law.mass retained ∧
      Real.exp (-(p * (binLog + termLog))) * (A.law.mass front.prep.selected.retained / 2) ≤
        A.law.mass retained ∧
      Real.exp (-(2 * p + q + p * (binLog + termLog) + 2)) ≤ A.law.mass retained ∧
      ∃ F : AllocatedExternalCandidateSpatialNativeFamily A E A.Path
          (KernelProjectionPresentPivot front.prep.selected.code) D Fmark φ marked front.keep cost
          source.front.familyParameter q commonBudget (q + binLog + coefficientLog + 4)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩,
        F.sourceChart = front.problem.precenterChart front.prep.positive_mass ∧
        (∀ a, HEq (F.sourceCandidate a) (front.problem.precenterCandidate front.prep.positive_mass a)) ∧
        F.η = (fun k => front.prep.early.eta
          (kernelProjectionSelectedPivot front.prep.selected.code k)) ∧
        (∀ a ∈ retained, ∀ k,
          Real.exp (-(q + binLog + coefficientLog + 4)) ≤ ‖F.correlation a k‖) ∧
        (∀ a ∈ retained, (F.sourceChart a).path = a) ∧
        (∀ a, (F.sourceChart a).centerLift = P.centerLift) ∧
        (∀ a ∈ retained, Real.exp (-q) ≤ (F.sourceCandidate a).score
          (fun x => (front.prep.selected.tests x).observable) weight) := by
  intro q binLog commonBudget Qmodel coefficientLog termLog
  let : Nonempty (Fin front.prep.binCount) := Fin.pos_iff_nonempty.mp front.prep.binCount_pos
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  have hp2 : 0 ≤ 2 * p := by positivity
  have hq : 0 ≤ q := positiveKernelPreparationParameter_nonneg hp2
  have hbin : 0 ≤ binLog := positiveKernelPreparationBinLog_nonneg hp2 e
  have hcard : (Fintype.card (Fin front.prep.binCount) : ℝ) ≤ Real.exp binLog := by
    simpa only [Fintype.card_fin] using front.prep.binCard
  have hdim : (finrank ℚ ↥(D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap) : ℝ) ≤ p := by
    have h := Submodule.finrank_le (D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap)
    rw [finrank_eq_card_basis D.basis, Fintype.card_fin] at h
    exact (Nat.cast_le.mpr h).trans hD.1
  have hweight' : ∀ x ∈ integerBox N, ‖weight x‖ ≤ Real.exp (2 * p + 3) := by
    intro x _
    exact (hweight x).trans (Real.exp_le_exp.mpr (by linarith only [hp]))
  have hmassSource : Real.exp (-(2 * p)) ≤ A.law.mass front.problem.productive := by
    calc
      _ = Real.exp (-p) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ massThreshold * Real.exp (-p) := mul_le_mul_of_nonneg_right hmass (Real.exp_nonneg _)
      _ ≤ _ := front.problem.mass
  have hmarkov : (q + binLog) + (q + q + binLog + 4) + (2 * p + q) + 2 ≤ source.front.u := by
    convert source.front.markov_precision using 1
    dsimp only [q, binLog, positiveKernelMarkovPrecisionParameter]
    ring
  have budget := source.front.familyBudget hp
  obtain ⟨retained, hsub, hpos', hmass', hmassAll, F, hFC, hFcandidate, hFeta, hcorr,
      hpath, hcenter, hscore⟩ :=
    front.prep.selected.exists_localFixedCenter_spatialNativeFamily
      front.prep.representative front.prep.net source.front.narrow source.front.u_nonneg
      source.front.model_nonneg source.front.input_model source.front.native_nonneg
      source.front.slice_nonneg source.front.test_nontrivial source.front.slice_log
      source.front.marginal_one source.front.marginal_bound source.front.projection_precision
      source.front.detection source.front.physical_excess hq hbin hcard hdim hweight'
      hcost0 (hcost.trans source.front.input_slice) source.front.projection_test hmassSource
      hmarkov le_rfl front.keep front.problem_keep source.polynomial_degree
      source.trim_le_one source.width_le_one source.chartConstant source.chartConstant_nonneg
      source.chart_bound source.chart_small budget.hpFamily (hcost.trans budget.cost)
      budget.projection budget.period budget.variation (budget.keepCard front.keep)
  refine ⟨retained, hsub, hpos', hmass', ?_, F, hFC, hFcandidate, hFeta, hcorr, hpath, hcenter, hscore⟩
  calc
    _ = Real.exp (-(q + p * (binLog + termLog) + 2)) * Real.exp (-(2 * p)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(q + p * (binLog + termLog) + 2)) * A.law.mass front.problem.productive :=
      mul_le_mul_of_nonneg_left hmassSource (Real.exp_nonneg _)
    _ ≤ _ := hmassAll

end CommonKeepPositiveKernelPreparation
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

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

namespace PrimitiveFrontQuotientData

variable {FmarkNative P} {p : ℝ} {e : ℕ} {source : A.DegreeSourceProfile s p e}
    (data : P.PrimitiveFrontQuotientData FmarkNative source)

noncomputable def factorFamily (hp : 0 ≤ p) :=
  data.family.withBudget source.front.factorBudget
    (source.front.factorGeometryBudget hp).factor_input

@[simp] theorem factorFamily_eta (hp : 0 ≤ p) : (data.factorFamily hp).η =
    (fun k => data.front.prep.early.eta
      (kernelProjectionSelectedPivot data.front.prep.selected.code k)) := rfl

@[simp] theorem factorFamily_sourceChart (hp : 0 ≤ p) :
    (data.factorFamily hp).sourceChart = data.rawFamily.sourceChart := rfl

@[simp] theorem factorFamily_sourceCandidate (hp : 0 ≤ p) :
    (data.factorFamily hp).sourceCandidate = data.rawFamily.sourceCandidate := rfl

@[simp] theorem factorFamily_native (hp : 0 ≤ p) :
    (data.factorFamily hp).native = data.rawFamily.native := rfl

@[simp] theorem factorFamily_correlation (hp : 0 ≤ p) (a : A.Path)
    (k : KernelProjectionPresentPivot data.front.prep.selected.code) :
    (data.factorFamily hp).correlation a k = data.rawFamily.correlation a k := rfl

end PrimitiveFrontQuotientData
end AllocatedExternalCandidateProblem
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
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
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
    {Pivot : Type} [Fintype Pivot]
    {pFamily pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A E A.Path Pivot D Fmark φ marked
      front.keep cost pFamily pLocal pNative r periodCap coverCap Lip)
    (H : Finset A.Path) (hH : H ⊆ front.prep.selected.retained)
    (hsourceChart : F.sourceChart = front.problem.precenterChart front.prep.positive_mass)
    (sourceCenter : ∀ j, U j)
    (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
    (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
    (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬front.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (hscore : ∀ a ∈ H, Real.exp (-positiveKernelPreparationParameter (2 * p)) ≤
      (F.sourceCandidate a).score (fun x => (front.prep.selected.tests x).observable) weight)
    (retained : Finset A.Path) (hsub : retained ⊆ H)
    {selectedMass : ℝ} (hmass : selectedMass ≤ A.law.mass retained)

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

include hH hsourceChart in

theorem conclusion_of_actualNativeQuotient
    (ideal : LieIdeal ℚ L) (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    {dQ : ℕ} (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)
    (hker : ∀ x ∈ ideal, φ x = 0)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup), descended x (QuotientGroup.mk
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap ideal) g)) =
      (front.prep.selected.tests x).observable (QuotientGroup.mk g))
    (adapted : (RationalFilteredNilmanifold.optionProduct Q
      (fun j => (F.native j).model)).AdaptedModelData)
    {outputCost : ℝ} (hout : 0 ≤ outputCost)
    (result : (((F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen
      (fun x => (front.prep.selected.tests x).observable) weight
      (Real.exp (-positiveKernelPreparationParameter (2 * p))) hscore
      retained hsub hmass).withKeep front.keep (fun _ => rfl)).adaptedOptionQuotient
        (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)
        ideal hI Q hQ hker descended hrecovery adapted).Conclusion
          outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost)))
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp outputCost)
    (hσone : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤
      Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) :
    Nonempty (P.Conclusion (3 * outputCost + 2)
      (Real.exp (-(3 * outputCost + 2))) (Real.exp (-(3 * outputCost + 2)))) := by
  have hcharts (a : A.Path) (ha : a ∈ H) :
      F.sourceChart a = front.prep.selected.problem.chart ⟨a, hH ha⟩ := by
    rw [hsourceChart]
    exact front.problem.precenterChart_mem front.prep.positive_mass a
      (front.prep.selected.subset (hH ha))
  obtain ⟨selected⟩ := F.conclusion_of_actualSourceAdaptedOptionQuotient H
    sourceCenter hpath hcenter hfrozen (fun x => (front.prep.selected.tests x).observable)
    weight (Real.exp (-positiveKernelPreparationParameter (2 * p))) hscore
    front.prep.selected.problem hH hcharts retained hsub hmass
    ideal hI Q hQ hker descended hrecovery adapted result
  exact front.conclusion_of_selected hout selected hweight hσone Cgeo hCgeo
    hchart hsmall hpoly

end CommonKeepPositiveKernelPreparation
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end


