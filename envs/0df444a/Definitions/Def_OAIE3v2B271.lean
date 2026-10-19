-- Prove2me | Definitions.Def_OAIE3v2B271
-- name    : OAIE3v2B271
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T06:56:27.682478+00:00
-- url     : https://prove2.me/theorems/476d6695-1bd8-4001-9e32-d34b7398b5d0
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 282 of 311
-- statement:
--   Definitions bundle 282 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B304`, `OAIE3v2B305`, `OAIE3v2B265`, `OAIE3v2B266` of this split.
--
--   Modules: `Dynamics/AllocatedCandidateBudgetedTreeTerminal.lean`, `Dynamics/AllocatedNativeDetectionBudgetMonotonicity.lean`, `Estimates/AllocatedCandidateGeneratedFastTerminal.lean`, `Estimates/AllocatedCandidateZeroRestrictedNativeCommonTerminal.lean`, `Estimates/AllocatedExternalCandidateAdaptedOptionQuotientFactors.lean`, `Estimates/AllocatedExternalCandidateFrozenNativeFactors.lean`, `Estimates/AllocatedExternalCandidateShearBufferedModel.lean`, `Estimates/AllocatedFrozenPrefixStageData.lean`, `Estimates/AllocatedZeroLayerFixedCenterExcess.lean`, `Estimates/InheritedTaggedQuotientPrecenterMasks.lean`, `Fourier/AllocatedExternalCandidateSpatialNativeFrequencyTransport.lean`, `Lattices/CertifiedAffineCutoffCost.lean`, `Linear/AllocatedExternalCandidateNormalizedKernelRestoration.lean`, `Polynomial/AllocatedExternalCandidateFixedCenterDegreeModel.lean`, `Probability/AllocatedExternalCandidateFrozenStageDensity.lean`, `Probability/AllocatedExternalCandidateRetainedSliceLaw.lean`, `Sampling/AllocatedExternalCandidateActualShearForecastScore.lean`, `Sampling/AllocatedExternalCandidatePhysicalScore.lean`, `Sampling/AllocatedExternalRetainedForecastModel.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B304
import Definitions.Def_OAIE3v2B305
import Definitions.Def_OAIE3v2B265
import Definitions.Def_OAIE3v2B266

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidatePhysicalScore
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    (D : RationalFilteredNilmanifold L r d) (Fmark : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)

namespace AllocatedExternalCandidateProblem
variable {A D Fmark φ marked observable weight cost massThreshold scoreThreshold}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

variable (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hσ1 H hH hchart hsmall hp

theorem ambientScore_eq_physical
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (z : P.productive) (points : Finset ((P.chart z).Variables → ℤ))
    (hpoints : points ⊆ (P.chart z).slice.integerPoints) :
    P.ambientScore ambient z points =
      (𝔼 u ∈ points, weight ((P.chart z).physical u) *
        observable ((P.chart z).physical u)
          (P.ambientPhysicalValue ambient ((P.chart z).physical u))).re := by
  unfold ambientScore ambientPhysicalValue
  apply congrArg Complex.re
  apply Finset.expect_congr rfl
  intro u hu
  rw [P.chartValues_eq_physicalIntegerPoint hσ1 H hH hchart hsmall hp z u (hpoints hu)]

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalCandidateRetainedSliceLaw
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {A} {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace Conclusion

variable (out : P.Conclusion outputCost outputMass outputScore)

variable (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hσ1 H hH hchart hsmall hp

theorem siteLaw_ambientPhysicalValue_score
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (z : out.retained) :
    ((out.siteLaw z).complexMean (fun site => weight (A.physical z.val site) *
      observable (A.physical z.val site)
        (P.ambientPhysicalValue ambient (A.physical z.val site)))).re =
      P.ambientScore ambient ⟨z.val, out.subset z.property⟩ (out.slice z).integerPoints := by
  rw [P.ambientScore_eq_physical hσ1 H hH hchart hsmall hp ambient
    ⟨z.val, out.subset z.property⟩ _ (out.inside z)]
  exact congrArg Complex.re (out.siteLaw_complexMean_physical z (fun x =>
    weight x * observable x (P.ambientPhysicalValue ambient x)))

theorem siteLaw_score (z : out.retained) :
    outputScore ≤ ((out.siteLaw z).complexMean (fun site => weight (A.physical z.val site) *
      observable (A.physical z.val site)
        (P.ambientPhysicalValue out.ambient (A.physical z.val site)))).re := by
  rw [out.siteLaw_ambientPhysicalValue_score hσ1 H hH hchart hsmall hp]
  exact out.score z

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InheritedTaggedQuotientPrecenterMasks
namespace OAI

section

universe u

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f : ℕ}
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

theorem refilteredFrozenObservable_recovery_of_coveredDiagram
    {inputDenominator k : ℕ} {p coverCost dictBound : ℝ}
    (rightDictionary : D.NativeGridRightDictionary inputDenominator dictBound)
    (covered : RationalFilteredNilmanifold.AllocatedMarkedCoveredLowerDiagram
      D Fmark φ hφ W k rightDictionary.denominator p coverCost)
    (left right : D.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hLip : ∀ x ∈ integerBox N, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x ∈ integerBox N, ∀ y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hleft : ∀ x ∈ integerBox N, ∀ i,
      |(D.basis.baseChange ℝ).repr
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          (P.physicalIntegerPoint x) left).coord i| ≤ Real.exp ((p + 2) ^ k))
    (hright : ∀ x ∈ integerBox N,
      (D.basis.baseChange ℝ).equivFun
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          (P.physicalIntegerPoint x) right).coord ∈ realDenominatorGrid inputDenominator) :
    letI := moduleTopology ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))
    letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))) :=
      IsModuleTopology.topologicalAddGroup ℝ _
    letI := realification_moduleTopology_t2 covered.Fref.basis
    letI := moduleTopology ℝ (ℝ ⊗[ℚ]
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ covered.Dref.filtration.layerIdeal (s + 1)))
    letI : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ covered.Dref.filtration.layerIdeal (s + 1))) :=
      IsModuleTopology.topologicalAddGroup ℝ _
    letI := realification_moduleTopology_t2 covered.Q.basis
    letI := covered.Q.metricSpace
    letI := covered.Fref.metricSpace
    let diagram := covered.Dref.markedTopQuotientDiagram covered.Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) covered.Q
    let K : ℝ≥0 := ⟨Real.exp covered.pCover, (Real.exp_pos _).le⟩
    ∀ x ∈ integerBox N, ∀ source,
      positiveImageSlice diagram K
        (P.refilteredFrozenObservable A Fmark φ W covered.Dref left right x)
        (diagram source).2 (diagram source).1 =
          P.refilteredFrozenObservable A Fmark φ W covered.Dref left right x source := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 covered.Fref.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ]
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ covered.Dref.filtration.layerIdeal (s + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ covered.Dref.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 covered.Q.basis
  let := covered.Q.metricSpace
  let := covered.Fref.metricSpace
  dsimp only
  intro x hx
  apply rightDictionary.markedTopQuotient_recovery D Fmark φ hφ W
    covered.Dref covered.Fref covered.Q ⟨Real.exp covered.pCover, (Real.exp_pos _).le⟩
    (observable x)
    (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
      (P.physicalIntegerPoint x) left)
    (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
      (P.physicalIntegerPoint x) right) (hright x hx)
  dsimp only
  intro j
  exact covered.recovery
    (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
      (P.physicalIntegerPoint x) left)
    (rightDictionary.representative j) (hleft x hx)
    (rightDictionary.representative_bounds j).2 (observable x) ℓ hℓ
    (hLip x hx) (hpositive x hx)

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedZeroLayerFixedCenterExcess
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

theorem NativeDetection.mono_tests
    {degree : ℕ} {pSlice pTest pNative α pSlice' pTest' α' : ℝ}
    (h : A.NativeDetection degree pSlice pTest pNative α)
    (hs : pSlice' ≤ pSlice) (ht : pTest' ≤ pTest) (ha : α ≤ α') :
    A.NativeDetection degree pSlice' pTest' pNative α' := by
  intro Tests _ Ldetect _ _ dims _ _ _ _ Ddetect Vdetect slices origin step length
    hstep hshape hdense hcomplex hnorm signal hsignal hsupp hlarge
  exact h Ddetect Vdetect slices origin step length hstep hshape
    (fun z j => (hdense z j).mono hs)
    (fun z j => (hcomplex z j).mono ht) hnorm signal hsignal hsupp (ha.trans hlarge)

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

local instance instNonemptySite : Nonempty A.Site := A.site_nonempty

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial
open Module Submodule BooleanCubeKernel
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

local instance fixedCenterEndpointSiteNonempty : Nonempty A.Site := A.site_nonempty

end AllocatedExternalCandidateSampler
end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedNativeDetectionBudgetMonotonicity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped TensorProduct NNReal

theorem SampledSliceNativeDetection.mono_native
    {m : ℕ} {X Ω T : Type} [Fintype X] [DecidableEq X] [Fintype Ω] [Fintype T]
    {Tests : Ω → Type} {J : Fin m → Type} [∀ j, Fintype (J j)]
    {N : X → ℕ} {hbox : (integerBox N).Nonempty}
    {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {pathLaw : FiniteProbabilityWeights Ω} {physical : Ω → T → X → ℤ}
    {slices : ∀ z, Tests z → Finset T} {weight : ∀ z, Tests z → T → ℂ}
    {degree : ℕ} {pNative pNative' α : ℝ}
    (h : SampledSliceNativeDetection J N hbox poly pathLaw physical slices weight
      degree pNative α)
    (hpNative : pNative ≤ pNative') :
    SampledSliceNativeDetection J N hbox poly pathLaw physical slices weight
      degree pNative' α := by
  intro signal hsignal hsupp hlarge
  obtain ⟨W, g, ⟨model⟩, hcorr⟩ := h signal hsignal hsupp hlarge
  have hexp := Real.exp_le_exp.mpr hpNative
  have hLip : (⟨Real.exp pNative, Real.exp_nonneg _⟩ : ℝ≥0) ≤
      ⟨Real.exp pNative', Real.exp_nonneg _⟩ := hexp
  refine ⟨W.mono hexp hexp hLip, g, ⟨model.mono hpNative⟩, ?_⟩
  change Real.exp (-pNative') ≤
    ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
      (fun u => signal u.val) (fun u => star (W.eval N poly u.val) * g u)‖
  exact (Real.exp_le_exp.mpr (neg_le_neg hpNative)).trans hcorr

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateSampler

variable {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

theorem NativeDetection.mono_native
    {degree : ℕ} {pSlice pTest pNative pNative' α : ℝ}
    (h : A.NativeDetection degree pSlice pTest pNative α)
    (hpNative : pNative ≤ pNative') :
    A.NativeDetection degree pSlice pTest pNative' α := by
  intro Tests _ Ldetect _ _ dims _ _ _ _ Ddetect Vdetect slices origin step length
    hstep hshape hdense hcomplex hnorm
  exact (h Ddetect Vdetect slices origin step length hstep hshape hdense hcomplex hnorm).mono_native
    hpNative

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedCandidateBudgetedTreeTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

noncomputable def allocatedCandidateTerminalControlConstant (s m a : ℕ) : ℕ :=
  Classical.choose (exists_certified_budgeted_tree_terminal_constants s m a)

noncomputable def allocatedCandidateTerminalPhaseConstant (s m a : ℕ) : ℕ → ℕ :=
  Classical.choose (Classical.choose_spec
    (exists_certified_budgeted_tree_terminal_constants s m a)).2

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateFrozenNativeFactors
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
    {L M ι : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (keep : LayerSamplerVariables G I n B → Prop) (hkeep : C.keep = keep)

theorem hasCommonRefilteredOrbitFactors_withKeep
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (h : D.filtration.HasCommonRefilteredOrbitFactors bD ω hF
      (fun i : C.Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) candidate.orbit)) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hF
      (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (candidate.withKeep keep hkeep).orbit) := by
  cases hkeep
  exact h

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

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

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)

def axisVariableEquiv : {i // keep i} ≃ {i : C.Variables // keep i.val} where
  toFun i := ⟨⟨i.val, hkeep i.val i.property⟩, i.property⟩
  invFun i := ⟨i.val.val, i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

include hkeep in

theorem hasCommonRefilteredOrbitFactors_axisPolynomial
    {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s : ℕ}
    (F : NilpotentLieFiltration L s) (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : C.Variables => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors bD ω hF
      (fun i : C.Variables => (A.sides i.val : ℝ)) q l W g) :
    F.HasCommonRefilteredOrbitFactors bD ω hF
      (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W
      (F.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
        (fun _ : {i // keep i} => 1) (C.axisPolynomial keep fixed)
        (C.axisPolynomial_support keep fixed) g) := by
  let localKeep : C.Variables → Prop := fun i => keep i.val
  let β := frozenCoordinate localKeep (fun i => (fixed i : ℝ))
  let e := C.axisVariableEquiv keep hkeep
  let γ : {i : C.Variables // localKeep i} → MvPolynomial {i // keep i} ℝ :=
    fun i => MvPolynomial.X (e.symm i)
  have hβ := frozenCoordinate_support localKeep (fun i => (fixed i : ℝ))
  have hγ : ∀ i, γ i ∈ weightedSupportLE (fun _ : {i // keep i} => 1) 1 :=
    fun i => weightedSupportLE_X (fun _ : {i // keep i} => 1) (e.symm i)
  have hf := HasCommonRefilteredOrbitFactors.freeze F bD ω hF localKeep
    (fun i => (fixed i : ℝ)) (fun i : C.Variables => (A.sides i.val : ℝ)) q l W g h
  have hr := HasCommonRefilteredOrbitFactors.reindex F bD ω hF e
    (fun i : {i : C.Variables // localKeep i} => (A.sides i.val.val : ℝ)) q l W
    (F.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
      (fun _ : {i : C.Variables // localKeep i} => 1) β hβ g) hf
  have hcomp : (fun i => MvPolynomial.aeval γ (β i)) = C.axisPolynomial keep fixed := by
    funext i
    by_cases hi : keep i.val <;>
      simp [β, γ, e, localKeep, frozenCoordinate, axisVariableEquiv, axisPolynomial, hi]
  have hcompose := F.weightedAdaptedRealChartHom_comp
    (fun _ : C.Variables => 1) (fun _ : {i : C.Variables // localKeep i} => 1)
    (fun _ : {i // keep i} => 1) β γ hβ hγ
    (weightedRealChart_comp_support _ _ _ β γ hβ hγ) g
  rw [← hcompose] at hr
  simpa only [hcomp, e, axisVariableEquiv, Equiv.coe_fn_mk] using hr

end AllocatedExternalLocalChart

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable {cost shortCost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

theorem hasCommonRefilteredOrbitFactors_freezeAxes
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (h : D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : C.Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) candidate.orbit)) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (candidate.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).orbit) := by
  change D.filtration.HasCommonRefilteredOrbitFactors bD ω hD _ q l W
    (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
      (D.filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
        (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed) candidate.orbit))
  rw [D.filtration.polynomialOrbitRealChart_polynomialCoordinates]
  exact C.hasCommonRefilteredOrbitFactors_axisPolynomial keep hkeep
    D.filtration bD ω hD fixed q l W _ h

end AllocatedExternalLocalCandidate

namespace AllocatedExternalCandidateProblem.AxisFreezing

variable {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {keep : P.productive → LayerSamplerVariables G I n B → Prop}
    {shortCost : ℝ} (freezing : P.AxisFreezing keep shortCost)

theorem problem_nativeFactors
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (z : P.productive)
    (h : D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : (P.chart z).Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (P.candidate z).orbit)) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : (freezing.problem.chart z).Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (freezing.problem.candidate z).orbit) :=
  (P.candidate z).hasCommonRefilteredOrbitFactors_freezeAxes (shortCost := shortCost)
    (keep z) (freezing.keep_subset z) (freezing.fixed z) (freezing.fixed_mem z)
    bD ω hD q l W h

end AllocatedExternalCandidateProblem.AxisFreezing

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalCandidateFrozenStageDensity
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

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (keep : LayerSamplerVariables G I n B → Prop) (hkeep : C.keep = keep)

theorem withKeep_dense_of_dense {densityCost : ℝ}
    (hdense : IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
      densityCost C.slice.integerPoints) :
    IsDenseCommonStrideBox (fun i : {i // keep i} => A.sides i.val)
      densityCost (C.withKeep keep hkeep).slice.integerPoints := by
  cases hkeep
  exact hdense

end AllocatedExternalLocalChart

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFrozenPrefixStageData
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedCandidateStageBaseExponent (s m Cprimitive : ℕ) : ℕ :=
  max 2 (max (s + 3)
    (max (4 * allocatedCandidateTerminalControlConstant s m 1) Cprimitive))

noncomputable def allocatedCandidateStageBase (s m Cprimitive : ℕ) (b : ℝ) : ℝ :=
  (b + allocatedCandidateStageBaseExponent s m Cprimitive) ^
    allocatedCandidateStageBaseExponent s m Cprimitive

 theorem allocatedCandidateStageBaseExponent_bounds (s m Cprimitive : ℕ) :
    2 ≤ allocatedCandidateStageBaseExponent s m Cprimitive ∧
    s + 3 ≤ allocatedCandidateStageBaseExponent s m Cprimitive ∧
    4 * allocatedCandidateTerminalControlConstant s m 1 ≤
      allocatedCandidateStageBaseExponent s m Cprimitive ∧
    Cprimitive ≤ allocatedCandidateStageBaseExponent s m Cprimitive := by
  unfold allocatedCandidateStageBaseExponent
  exact ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _),
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)⟩

 theorem allocatedCandidateStageBase_bounds (s m Cprimitive : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    2 ≤ allocatedCandidateStageBase s m Cprimitive b ∧
    b ≤ allocatedCandidateStageBase s m Cprimitive b := by
  let C := allocatedCandidateStageBaseExponent s m Cprimitive
  have hC : (2 : ℝ) ≤ C := Nat.cast_le.mpr (allocatedCandidateStageBaseExponent_bounds s m Cprimitive).1
  have hbase : 1 ≤ b + C := by linarith
  have hp : b + C ≤ (b + C) ^ C := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase
      (show 1 ≤ C by have := (allocatedCandidateStageBaseExponent_bounds s m Cprimitive).1; omega)
  change 2 ≤ (b + C) ^ C ∧ b ≤ (b + C) ^ C
  exact ⟨(show 2 ≤ b + C by linarith).trans hp, (le_add_of_nonneg_right (Nat.cast_nonneg C)).trans hp⟩

 theorem allocatedCandidateStage_primitive_le_base (s m Cprimitive : ℕ)
    {x b : ℝ} (hx : 0 ≤ x) (hxb : x ≤ b) :
    (x + Cprimitive) ^ Cprimitive ≤ allocatedCandidateStageBase s m Cprimitive b := by
  let C := allocatedCandidateStageBaseExponent s m Cprimitive
  have hC := (allocatedCandidateStageBaseExponent_bounds s m Cprimitive).2.2.2
  have hCtwo : (2 : ℝ) ≤ C := Nat.cast_le.mpr
    (allocatedCandidateStageBaseExponent_bounds s m Cprimitive).1
  change _ ≤ (b + C) ^ C
  exact (pow_le_pow_left₀ (add_nonneg hx (Nat.cast_nonneg _))
    (add_le_add hxb (Nat.cast_le.mpr hC)) Cprimitive).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ b + C) hC)

 theorem allocatedCandidateStage_control_le_base (s m Cprimitive d : ℕ)
    {b : ℝ} (hb : 0 ≤ b) (hd : (d : ℝ) ≤ b) :
    (allocatedCandidateForwardControlInput s d b + allocatedCandidateTerminalControlConstant s m 1) ^
      allocatedCandidateTerminalControlConstant s m 1 ≤ allocatedCandidateStageBase s m Cprimitive b := by
  have h := allocatedCandidateStageBaseExponent_bounds s m Cprimitive
  exact allocatedCandidateForwardControlInput_power_bound s d
    (allocatedCandidateTerminalControlConstant s m 1)
    (allocatedCandidateStageBaseExponent s m Cprimitive) hb hd h.1 h.2.1 h.2.2.1

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

noncomputable def allocatedCandidateCompositePhaseConstant
    (s m a Cnative r : ℕ) : ℕ :=
  Classical.choose (exists_preparedFiniteForward_composed_phase_cap Cnative
    (allocatedCandidateTerminalPhaseConstant s m a r))

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

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

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

theorem hasCommonRefilteredOrbitFactors_axisPolynomial_of_zero_restriction
    (keep initialLong : LayerSamplerVariables G I n B → Prop)
    (hsub : ∀ i, keep i → initialLong i)
    {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s : ℕ}
    (F : NilpotentLieFiltration L s) (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : C.Variables => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors bD ω hF
      (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
      (F.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
        (fun _ : {i // initialLong i} => 1) (C.axisPolynomial initialLong (fun _ => 0))
        (C.axisPolynomial_support initialLong (fun _ => 0)) g)) :
    F.HasCommonRefilteredOrbitFactors bD ω hF
      (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W
      (F.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
        (fun _ : {i // keep i} => 1) (C.axisPolynomial keep fixed)
        (C.axisPolynomial_support keep fixed) g) := by
  let pureLong := F.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
    (fun _ : {i // initialLong i} => 1) (C.axisPolynomial initialLong (fun _ => 0))
    (C.axisPolynomial_support initialLong (fun _ => 0)) g
  have hpure := HasCommonRefilteredOrbitFactors.nested_freeze F bD ω hF
    initialLong keep hsub 0 (fun i => (A.sides i : ℝ)) q l W pureLong h
  apply HasCommonRefilteredOrbitFactors.of_symbol_eq F bD ω hF
    (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W _ _ hpure
  have haxis : C.axisPolynomial keep fixed =
      nestedFrozenCoordinate C.keep keep (fun i => (fixed i : ℝ)) := rfl
  have hzero : C.axisPolynomial initialLong (fun _ => 0) =
      nestedFrozenCoordinate C.keep initialLong 0 := by
    funext i
    simp only [axisPolynomial, nestedFrozenCoordinate, Pi.zero_apply, Int.cast_zero]
  have hactual : F.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
      (fun _ : {i // keep i} => 1) (C.axisPolynomial keep fixed)
      (C.axisPolynomial_support keep fixed) g =
      F.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
        (fun _ : {i // keep i} => 1)
        (nestedFrozenCoordinate C.keep keep (fun i => (fixed i : ℝ)))
        (nestedFrozenCoordinate_support C.keep keep (fun i => (fixed i : ℝ))) g := by
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    simp only [weightedAdaptedRealChartHom_coord]
    rw [haxis]
  have hlong : pureLong =
      F.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
        (fun _ : {i // initialLong i} => 1)
        (nestedFrozenCoordinate C.keep initialLong 0)
        (nestedFrozenCoordinate_support C.keep initialLong 0) g := by
    dsimp only [pureLong]
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    simp only [weightedAdaptedRealChartHom_coord]
    rw [hzero]
  rw [hactual, hlong]
  exact F.realPolynomialSymbolHom_nested_nested_frozenCoordinate bD ω hF
    C.keep initialLong keep hsub (fun i => (fixed i : ℝ)) g

end AllocatedExternalLocalChart

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable {cost shortCost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

theorem hasCommonRefilteredOrbitFactors_freezeAxes_of_zero_restriction
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hsub : ∀ i, keep i → initialLong i)
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (h : D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
        (fun _ : {i // initialLong i} => 1) (C.axisPolynomial initialLong (fun _ => 0))
        (C.axisPolynomial_support initialLong (fun _ => 0))
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) candidate.orbit))) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (candidate.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).orbit) := by
  change D.filtration.HasCommonRefilteredOrbitFactors bD ω hD _ q l W
    (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
      (D.filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
        (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed) candidate.orbit))
  rw [D.filtration.polynomialOrbitRealChart_polynomialCoordinates]
  exact C.hasCommonRefilteredOrbitFactors_axisPolynomial_of_zero_restriction keep initialLong hsub
    D.filtration bD ω hD fixed q l W _ h

end AllocatedExternalLocalCandidate

namespace AllocatedExternalCandidateProblem.AxisFreezing

variable {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {keep : P.productive → LayerSamplerVariables G I n B → Prop}
    {shortCost : ℝ} (freezing : P.AxisFreezing keep shortCost)

theorem problem_nativeFactors_of_zero_restriction
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hstageLong : ∀ z i, keep z i → initialLong i)
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (z : P.productive)
    (h : D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
        (fun _ : {i // initialLong i} => 1) ((P.chart z).axisPolynomial initialLong (fun _ => 0))
        ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) (P.candidate z).orbit))) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : (freezing.problem.chart z).Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (freezing.problem.candidate z).orbit) :=
  (P.candidate z).hasCommonRefilteredOrbitFactors_freezeAxes_of_zero_restriction
    (shortCost := shortCost) (keep z) (freezing.keep_subset z) (freezing.fixed z)
    (freezing.fixed_mem z) initialLong (hstageLong z) bD ω hD q l W h

theorem withKeep_nativeFactors_of_zero_restriction
    (commonKeep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : freezing.problem.productive,
      (freezing.problem.chart z).keep = commonKeep)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hstageLong : ∀ z i, keep z i → initialLong i)
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (z : P.productive)
    (h : D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
        (fun _ : {i // initialLong i} => 1) ((P.chart z).axisPolynomial initialLong (fun _ => 0))
        ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) (P.candidate z).orbit))) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // commonKeep i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        ((freezing.problem.withKeep commonKeep hkeep).candidate z).orbit) :=
  (freezing.problem.candidate z).hasCommonRefilteredOrbitFactors_withKeep
    commonKeep (hkeep z) bD ω hD q l W
    (freezing.problem_nativeFactors_of_zero_restriction initialLong hstageLong bD ω hD q l W z h)

end AllocatedExternalCandidateProblem.AxisFreezing

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAdaptedOptionQuotientFactors
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable section

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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t dQ : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (ideal : LieIdeal ℚ L) (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)
    (hker : ∀ x ∈ ideal, φ x = 0)

namespace AllocatedExternalCandidateProblem

variable {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked
      observable weight cost massThreshold scoreThreshold)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap ideal) g)) =
        observable x (QuotientGroup.mk g))

theorem lieQuotientProblem_ambientScore
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (z : P.productive) (points : Finset ((P.chart z).Variables → ℤ)) :
    (P.lieQuotientProblem ideal hI Q hQ hker descended hrecovery).ambientScore
      (D.quotientOrbit ideal hI Q hQ ambient) z points = P.ambientScore ambient z points := by
  unfold ambientScore
  simp only [lieQuotientProblem, D.quotientOrbit_eval, hrecovery]

end AllocatedExternalCandidateProblem

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalRetainedForecastModel
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {A} {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace Conclusion

variable (out : P.Conclusion outputCost outputMass outputScore)

local instance instNonemptySite_1 : Nonempty A.Site := A.site_nonempty

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateShearBufferedModel
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem.Conclusion

variable {A} {Y M : Type} [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    (patch : PolynomialPatch Y s d) [Fintype (PolynomialShearIndex patch.weight)]
    {Fmark : NilpotentLieFiltration M t}
    {φ : PolynomialShearLieAlgebra patch.weight ℚ →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    {cost massThreshold scoreThreshold outputCost outputMass outputScore : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le) Fmark φ marked
      (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
      cost massThreshold scoreThreshold}
    (out : P.Conclusion outputCost outputMass outputScore)

local instance instNonemptySite_2 : Nonempty A.Site := A.site_nonempty

end AllocatedExternalCandidateProblem.Conclusion
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

def withFrequencies (eta : Pivot → LG →ₗ[ℚ] ℚ) (h : F.η = eta) :
    AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip :=
  { F with
    η := eta
    hηheight := by simpa only [← h] using F.hηheight
    hη := by simpa only [← h] using F.hη }

variable (eta : Pivot → LG →ₗ[ℚ] ℚ) (h : F.η = eta)

@[simp] theorem withFrequencies_eta : (F.withFrequencies eta h).η = eta := rfl

@[simp] theorem withFrequencies_sourceChart :
    (F.withFrequencies eta h).sourceChart = F.sourceChart := rfl

@[simp] theorem withFrequencies_sourceCandidate :
    (F.withFrequencies eta h).sourceCandidate = F.sourceCandidate := rfl

@[simp] theorem withFrequencies_reference :
    (F.withFrequencies eta h).reference = F.reference := rfl

@[simp] theorem withFrequencies_nativeValue :
    (F.withFrequencies eta h).nativeValue = F.nativeValue := rfl

@[simp] theorem withFrequencies_native :
    (F.withFrequencies eta h).native = F.native := rfl

@[simp] theorem withFrequencies_twist :
    (F.withFrequencies eta h).twist = F.twist := rfl

@[simp] theorem withFrequencies_chart (a : Ω) :
    (F.withFrequencies eta h).chart a = F.chart a := rfl

@[simp] theorem withFrequencies_candidate (a : Ω) :
    (F.withFrequencies eta h).candidate a = F.candidate a := rfl

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CertifiedAffineCutoffCost
namespace OAI

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

namespace AllocatedExternalLocalChart
variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

noncomputable def tagAnchor (j : Fin m) : J j → ℝ :=
  fun i => MvPolynomial.eval (0 : C.Variables → ℝ)
    (integerSampledRealChart C.integerChart (Sum.inr ⟨j, i⟩))

end AllocatedExternalLocalChart

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedExternalCandidateNormalizedKernelRestoration
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem conclusion_of_kernel_projection
    (tests : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J))
    (htests : ∀ x, (tests x).UnitIntervalValued)
    (hobs : ∀ x, (tests x).observable = observable x)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (hkernel : K ≤ LinearMap.ker φ.toLinearMap)
    (retained : Finset A.Path) (hsub : retained ⊆ P.productive)
    {newMass newScore : ℝ} (hmass : newMass ≤ A.law.mass retained)
    (hscore : ∀ z : retained, newScore ≤
      (P.candidate ⟨z.val,hsub z.property⟩).score
        (fun x => ((tests x).kernelProjection K hK).observable) weight)
    {outputCost outputMass outputScore Bweight : ℝ}
    (out : (P.restrictObservable (fun x => ((tests x).kernelProjection K hK).observable)
      retained hsub hmass hscore).Conclusion outputCost outputMass outputScore)
    (hOutMass : 0 < outputMass) (hOutScore : 0 < outputScore) (hB : 0 < Bweight)
    (hweight : ∀ x, ‖weight x‖ ≤ Bweight)
    (hσone : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ)+1)*R j) ≤ 1/8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (poly j)) :
    Nonempty (P.Conclusion outputCost (outputScore/(2*Bweight)*outputMass) (outputScore/2)) := by
  let projected := P.restrictObservable (fun x => ((tests x).kernelProjection K hK).observable)
    retained hsub hmass hscore
  have hpos : 0 < A.law.mass out.retained := hOutMass.trans_le out.mass
  have hne : out.retained.Nonempty := by
    apply Finset.nonempty_of_ne_empty
    intro he
    simp [he, FiniteProbabilityWeights.mass] at hpos
  obtain ⟨a₀,ha₀⟩ := hne
  let localLaw (a : A.Path) : FiniteProbabilityWeights A.Site :=
    if ha : a ∈ out.retained then out.siteLaw ⟨a,ha⟩ else out.siteLaw ⟨a₀,ha₀⟩
  have hlaw (a : A.Path) (ha : a ∈ out.retained) :
      localLaw a = out.siteLaw ⟨a,ha⟩ := by
    simp only [localLaw, dif_pos ha]
  have hprojected (a : A.Path) (ha : a ∈ out.retained) :
      outputScore ≤ ((localLaw a).complexMean (fun site =>
        weight (A.physical a site) *
        (((tests (A.physical a site)).kernelProjection K hK).withOrbit out.ambient).eval
          (projected.physicalIntegerPoint (A.physical a site)))).re := by
    rw [hlaw a ha]
    exact out.siteLaw_score hσone Cgeo hCgeo hchart hsmall hpoly ⟨a,ha⟩
  obtain ⟨ambient,hmark,zshift,_hshift,_hcoord,_hshiftmark,_hobs,kept,hkept,_hkeptpos,hmassKept,hrestored⟩ :=
    RationalFilteredNilmanifold.Niltest.exists_external_kernelProjection_prescribed_marked_orbit
      tests htests Fmark φ K hK hkernel out.ambient marked out.marked
      A.law out.retained hpos localLaw A.physical
      (fun a site => projected.physicalIntegerPoint (A.physical a site))
      (fun a site => weight (A.physical a site)) hB hOutScore
      (fun a _ site => hweight (A.physical a site)) hprojected
  refine ⟨{
    ambient := ambient
    marked := hmark
    retained := kept
    subset := fun a ha => hsub (out.subset (hkept ha))
    mass := (mul_le_mul_of_nonneg_left out.mass (by positivity)).trans hmassKept
    step := fun a => out.step ⟨a.val,hkept a.property⟩
    step_pos := fun a => out.step_pos ⟨a.val,hkept a.property⟩
    slice := fun a => out.slice ⟨a.val,hkept a.property⟩
    dense := fun a => out.dense ⟨a.val,hkept a.property⟩
    inside := fun a => out.inside ⟨a.val,hkept a.property⟩
    score := ?_ }⟩
  intro a
  let old : out.retained := ⟨a.val,hkept a.property⟩
  have hs := hrestored a.val a.property
  rw [hlaw a.val old.property] at hs
  have he : ((out.siteLaw old).complexMean (fun site =>
      weight (A.physical a.val site) * ((tests (A.physical a.val site)).withOrbit ambient).eval
        (projected.physicalIntegerPoint (A.physical a.val site)))).re =
      P.ambientScore ambient ⟨a.val,hsub (out.subset old.property)⟩
        (out.slice old).integerPoints := by
    change ((out.siteLaw old).complexMean (fun site => weight (A.physical a.val site) *
      (tests (A.physical a.val site)).observable (P.ambientPhysicalValue ambient (A.physical a.val site)))).re = _
    simp_rw [hobs]
    rw [P.ambientScore_eq_physical hσone Cgeo hCgeo hchart hsmall hpoly ambient
      ⟨a.val,hsub (out.subset old.property)⟩ _ (out.inside old)]
    exact congrArg Complex.re (out.siteLaw_complexMean_physical old (fun x =>
      weight x * observable x (P.ambientPhysicalValue ambient x)))
  exact hs.trans_eq he

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem conclusion_of_kernel_projection_normalized
    (tests : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J))
    (htests : ∀ x, (tests x).UnitIntervalValued)
    (hobs : ∀ x, (tests x).observable = observable x)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (hkernel : K ≤ LinearMap.ker φ.toLinearMap)
    (retained : Finset A.Path) (hsub : retained ⊆ P.productive)
    {newMass newScore : ℝ} (hmass : newMass ≤ A.law.mass retained)
    (hscore : ∀ z : retained, newScore ≤
      (P.candidate ⟨z.val,hsub z.property⟩).score
        (fun x => ((tests x).kernelProjection K hK).observable) weight)
    {p : ℝ} (hp : 0 ≤ p)
    (out : (P.restrictObservable (fun x => ((tests x).kernelProjection K hK).observable)
      retained hsub hmass hscore).Conclusion p (Real.exp (-p)) (Real.exp (-p)))
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p)
    (hσone : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ)+1)*R j) ≤ 1/8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (poly j)) :
    Nonempty (P.Conclusion (3*p+2) (Real.exp (-(3*p+2))) (Real.exp (-(3*p+2)))) := by
  obtain ⟨restored⟩ := P.conclusion_of_kernel_projection tests htests hobs K hK hkernel
    retained hsub hmass hscore out (Real.exp_pos _) (Real.exp_pos _) (Real.exp_pos p)
    hweight hσone Cgeo hCgeo hchart hsmall hpoly
  obtain ⟨hcost, hmass', hscore'⟩ := kernel_restoration_exp_budget hp
  exact ⟨restored.mono hcost hmass' hscore'⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedExternalCandidateFixedCenterDegreeModel
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

local instance fixedCenterDegreeSiteNonempty : Nonempty A.Site := A.site_nonempty

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateActualShearForecastScore
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical NNReal Matrix TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
variable {I J Eout : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
  [∀ j, Fintype (Eout j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {N : X → ℕ} {τ ξ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable (qnum qLate : ActualFixedSpatialSlicedForecastNumerics s)
variable {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
variable {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
variable {hmem : ∀ j d, coefficients (poly j) d ∈ U j}
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable {stride : X → ℕ}
variable {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hmem
  τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem.Conclusion
local instance instNonemptySite_5 : Nonempty A.Site := A.site_nonempty

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
end


