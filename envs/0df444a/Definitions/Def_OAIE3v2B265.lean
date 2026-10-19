-- Prove2me | Definitions.Def_OAIE3v2B265
-- name    : OAIE3v2B265
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T06:35:44.762978+00:00
-- url     : https://prove2.me/theorems/27b72fe7-f52b-4d6e-baa1-a31849766bdc
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 274 of 311
-- statement:
--   Definitions bundle 274 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B257`, `OAIE3v2B303`, `OAIE3v2B259` of this split.
--
--   Modules: `Dynamics/AllocatedExternalCandidatePrimitivePhysicalBudget.lean`, `Dynamics/AllocatedExternalCandidateResetSuccessor.lean`, `Estimates/AllocatedExternalCandidateFiniteFreezingDictionaryProducer.lean`, `Estimates/AllocatedExternalCandidateThresholdSuccessor.lean`, `Estimates/AllocatedExternalCandidateUniformSuccessor.lean`, `Estimates/InheritedTaggedQuotientPrecenterMasks.lean`, `Geometry/AllocatedExternalCandidateNativeMiddleCoordinates.lean`, `Geometry/AllocatedExternalCandidateRefilteredSupportedStep.lean`, `Linear/PreparedDeterminingMatrixBudget.lean`, `Linear/PreparedFiniteNestedSourceProjectionBudget.lean`, `Sampling/AllocatedExternalCandidateNativeFrozenScore.lean`, `Sampling/AllocatedExternalCandidatePhysicalScore.lean`, `Sampling/PreparedEarlyLateSamplerGeometry.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B257
import Definitions.Def_OAIE3v2B303
import Definitions.Def_OAIE3v2B259

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

theorem chartValues_eq_physicalIntegerPoint (z : P.productive)
    (u : (P.chart z).Variables → ℤ) (hu : u ∈ (P.chart z).slice.integerPoints) :
    (P.chart z).chartValues u = P.physicalIntegerPoint ((P.chart z).physical u) :=
  (P.chart z).chartValues_eq_physicalIntegerPoint_of_center
    hσ1 H hH hchart hsmall hp P.centerLift (P.chart_centerLift z) u hu

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InheritedTaggedQuotientPrecenterMasks
namespace OAI

section

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

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
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
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    (hQ : Q.filtration = Dref.filtration.quotientTop)
    (QF : RationalFilteredNilmanifold
      ((Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) ⧸
        Fref.filtration.layerIdeal (s + 1)) s nQF)
    (hQF : QF.filtration = Fref.filtration.quotientTop)
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace Fref.Space]

variable (left right : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (K : ℝ≥0)

noncomputable def refilteredFrozenObservable (x : X → ℤ) (source : Dref.RealGroup) : ℂ :=
  observable x (QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) (P.physicalIntegerPoint x) left *
      realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl source *
      D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) (P.physicalIntegerPoint x) right))

noncomputable def refilteredQuotientObservable (x : X → ℤ) : Q.Space → ℂ :=
  positiveImageSlice (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) K
    (P.refilteredFrozenObservable A Fmark φ W Dref left right x)
    (QuotientGroup.mk (Fref.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
      (P.physicalIntegerPoint x) markedMiddle))

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateNativeFrozenScore
namespace OAI

section

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

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
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
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    (hQ : Q.filtration = Dref.filtration.quotientTop)
    (QF : RationalFilteredNilmanifold
      ((Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) ⧸
        Fref.filtration.layerIdeal (s + 1)) s nQF)
    (hQF : QF.filtration = Fref.filtration.quotientTop)
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace Fref.Space]

variable (left right : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (K : ℝ≥0)

variable (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)
    (hrecovery : ∀ x source, positiveImageSlice (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) K
      (P.refilteredFrozenObservable A Fmark φ W Dref left right x)
      (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).2
      (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).1 =
        P.refilteredFrozenObservable A Fmark φ W Dref left right x source)

noncomputable def refilteredFrozenScore (z : P.productive) : ℝ :=
  (𝔼 u ∈ (P.chart z).slice.integerPoints, weight ((P.chart z).physical u) *
    P.refilteredFrozenObservable A Fmark φ W Dref left right ((P.chart z).physical u)
      (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit)).re

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

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

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
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
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)

variable (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (hsection : Function.RightInverse sectionMap φ)
    (leftMark rightMark : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (kE kR : D.RealGroup)
    (hkE : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ kE = 1)
    (hkR : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ kR = 1)
    (localLeft localRight : ∀ z : P.productive,
      (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : (P.chart z).Variables => 1)).Group)
    (localLeftMark localRightMark : ∀ z : P.productive,
      (Fmark.filtration.realification.adaptedPolynomialFiltration
        (fun _ : (P.chart z).Variables => 1)).Group)
    (hfactor : ∀ z : P.productive,
      localLeft z * P.refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref
        markedMiddle middle z * localRight z =
      D.filtration.realification.polynomialOrbitCoordinates _ (P.candidate z).orbit)
    (hleft : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localLeftMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => ((P.chart z).chartValues u i : ℝ)) leftMark)
    (hright : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localRightMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => ((P.chart z).chartValues u i : ℝ)) rightMark)
    (hcoset : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom (fun _ => 1)
        (fun i => (u i : ℝ))
        ((D.filtration.filteredRealPolynomialSection Fmark.filtration (fun _ => 1)
          sectionMap hSectionFilt (localRightMark z))⁻¹ * localRight z)) : D.Space) =
        QuotientGroup.mk kR)
    (tests : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J))
    (htests : ∀ x, (tests x).observable = observable x)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] in
include hsection hkE hkR hfactor hleft hright in

theorem refilteredFrozen_mark_on_slice
    (hprojLeft : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ => 1) (localLeft z) = localLeftMark z)
    (hprojRight : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ => 1) (localRight z) = localRightMark z)
    (z : P.productive) (u : (P.chart z).Variables → ℤ)
    (hu : u ∈ (P.chart z).slice.integerPoints) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u)
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark kE) *
        realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) *
        D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u)
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark kR)) =
      Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) marked := by
  have he := D.filtration.frozenMarkedOuter_product_mark_eq Fmark.filtration φ hφ
    sectionMap hSectionFilt hsection (fun _ : (P.chart z).Variables => 1)
    (D.filtration.realification.polynomialOrbitCoordinates _ (P.candidate z).orbit)
    (localLeft z)
    (P.refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z)
    (localRight z) (hfactor z) (localLeftMark z) (localRightMark z)
    (hprojLeft z) (hprojRight z) (fullTaggedVariableWeight (X := X) J) leftMark rightMark kE kR hkE hkR
    (fun i => (u i : ℝ)) (fun i => ((P.chart z).chartValues u i : ℝ))
    (hleft z u hu) (hright z u hu)
  simp only [NilpotentLieFiltration.nativeFrozenMarkedOrbitCoordinates_realValue,
    P.refilteredLocalCoordinates_value A Fmark φ hφ W Dref hDref Fref markedMiddle middle,
    polynomialOrbitRealEval_integer] at he
  exact he.trans ((P.candidate z).mark_on_slice u hu)

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateFiniteFreezingDictionaryProducer
namespace OAI

section

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

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
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
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)

variable (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (hsection : Function.RightInverse sectionMap φ)
    (leftMark rightMark : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (kE kR : D.RealGroup)
    (hkE : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ kE = 1)
    (hkR : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ kR = 1)
    (localLeft localRight : ∀ z : P.productive,
      (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : (P.chart z).Variables => 1)).Group)
    (localLeftMark localRightMark : ∀ z : P.productive,
      (Fmark.filtration.realification.adaptedPolynomialFiltration
        (fun _ : (P.chart z).Variables => 1)).Group)
    (hleft : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localLeftMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => ((P.chart z).chartValues u i : ℝ)) leftMark)
    (hright : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localRightMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => ((P.chart z).chartValues u i : ℝ)) rightMark)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] in
include hleft hright hσ1 H hH hchart hsmall hp in

theorem refilteredFrozenObservable_eq_localFrozen
    (z : P.productive) (u : (P.chart z).Variables → ℤ)
    (hu : u ∈ (P.chart z).slice.integerPoints) :
    P.refilteredFrozenObservable A Fmark φ W Dref
      (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark kE)
      (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark kR)
      ((P.chart z).physical u)
      (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) =
    observable ((P.chart z).physical u) (QuotientGroup.mk
      (D.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (D.filtration.frozenMarkedLeft Fmark.filtration (fun _ => 1) sectionMap hSectionFilt
            (localLeftMark z) kE *
          P.refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z *
          D.filtration.frozenMarkedRight Fmark.filtration (fun _ => 1) sectionMap hSectionFilt
            (localRightMark z) kR))) := by
  have hl := D.filtration.frozenMarkedLeftOrbit_realEval_eq_local Fmark.filtration (fullTaggedVariableWeight (X := X) J)
    sectionMap hSectionFilt leftMark kE (fun _ : (P.chart z).Variables => 1)
    (localLeftMark z) (fun i => (u i : ℝ))
    (fun i => ((P.chart z).chartValues u i : ℝ)) (hleft z u hu)
  have hr := D.filtration.frozenMarkedRightOrbit_realEval_eq_local Fmark.filtration (fullTaggedVariableWeight (X := X) J)
    sectionMap hSectionFilt rightMark kR (fun _ : (P.chart z).Variables => 1)
    (localRightMark z) (fun i => (u i : ℝ))
    (fun i => ((P.chart z).chartValues u i : ℝ)) (hright z u hu)
  simp only [polynomialOrbitRealEval_integer] at hl hr
  have htags := P.chartValues_eq_physicalIntegerPoint hσ1 H hH hchart hsmall hp z u hu
  unfold refilteredFrozenObservable
  rw [← htags, hl, hr]
  simp only [map_mul,
    P.refilteredLocalCoordinates_value A Fmark φ hφ W Dref hDref Fref markedMiddle middle]

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

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

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
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
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)

variable {Index : Type*} [Fintype Index] [Nonempty Index]
    (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (leftMark rightMark : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (leftCenter rightCenter : Index → D.RealGroup)

theorem exists_frozen_refinement_of_local_slices
    {newCost frozenThreshold Bweight ε : ℝ}
    (hcost : cost ≤ newCost) (hBweight : 0 ≤ Bweight) (hε : 0 ≤ ε)
    (step : P.productive → ℕ) (hstep : ∀ z, 0 < step z)
    (slice : ∀ z : P.productive,
      ResidueBoxSlice (fun i : (P.chart z).Variables => A.sides i.val) (step z))
    (hdense : ∀ z, IsDenseCommonStrideBox (fun i : (P.chart z).Variables => A.sides i.val)
      newCost (slice z).integerPoints)
    (hinside : ∀ z, (slice z).integerPoints ⊆ (P.chart z).slice.integerPoints)
    (label : P.productive → Index)
    (hweight : ∀ z, ∀ u ∈ (slice z).integerPoints, ‖weight ((P.chart z).physical u)‖ ≤ Bweight)
    (herror : ∀ z, ∀ u ∈ (slice z).integerPoints,
      ‖observable ((P.chart z).physical u) ((P.candidate z).value u) -
        P.refilteredFrozenObservable A Fmark φ W Dref
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            leftMark (leftCenter (label z)))
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            rightMark (rightCenter (label z)))
          ((P.chart z).physical u)
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit)‖ ≤ ε)
    (hfrozen : ∀ z, frozenThreshold ≤
      (𝔼 u ∈ (slice z).integerPoints, weight ((P.chart z).physical u) *
        P.refilteredFrozenObservable A Fmark φ W Dref
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            leftMark (leftCenter (label z)))
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            rightMark (rightCenter (label z)))
          ((P.chart z).physical u)
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit)).re) :
    ∃ chosen : Index,
      ∃ refinement : P.Refinement newCost
        (massThreshold / (Fintype.card Index : ℝ)) (frozenThreshold - Bweight * ε),
      ∀ z : refinement.problem.productive, frozenThreshold ≤
        refinement.problem.refilteredFrozenScore A Fmark φ hφ W Dref Fref
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            leftMark (leftCenter chosen))
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            rightMark (rightCenter chosen)) markedMiddle
          (refinement.refilteredMiddle hφ W Dref Fref markedMiddle middle) z := by
  have hscore (z : P.productive) : frozenThreshold - Bweight * ε ≤
      (𝔼 u ∈ (slice z).integerPoints, weight ((P.chart z).physical u) *
        observable ((P.chart z).physical u) ((P.candidate z).value u)).re := by
    have he := complex_expect_error_le (slice z).integerPoints
      (fun u => weight ((P.chart z).physical u) *
        observable ((P.chart z).physical u) ((P.candidate z).value u))
      (fun u => weight ((P.chart z).physical u) *
        P.refilteredFrozenObservable A Fmark φ W Dref
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            leftMark (leftCenter (label z)))
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            rightMark (rightCenter (label z)))
          ((P.chart z).physical u)
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit))
      (mul_nonneg hBweight hε) (by
        intro u hu
        rw [← mul_sub, norm_mul]
        exact mul_le_mul (hweight z u hu) (herror z u hu) (norm_nonneg _) hBweight)
    have hre := (Complex.abs_re_le_norm _).trans he
    rw [Complex.sub_re] at hre
    have hlo := (abs_le.mp hre).1
    have hs := hfrozen z
    linarith
  let initial : P.Refinement newCost massThreshold (frozenThreshold - Bweight * ε) := {
    retained := P.productive
    subset := fun _ hz => hz
    mass := P.mass
    cost_le := hcost
    step := step
    step_pos := hstep
    slice := slice
    dense := hdense
    inside := hinside
    scoreLower := hscore }
  obtain ⟨chosen, paths, hpaths, hmass, hlabel⟩ := initial.exists_common_label label
  let refinement := initial.restrictPaths paths hpaths hmass
  refine ⟨chosen, refinement, ?_⟩
  intro z
  have hl : label ⟨z.val, hpaths z.property⟩ = chosen := hlabel z
  have hs := hfrozen ⟨z.val, hpaths z.property⟩
  rw [hl] at hs
  exact hs

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

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

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
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
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)

namespace Refinement

variable {A Fmark φ P} {newCost newMass newScore : ℝ}
    (refinement : P.Refinement newCost newMass newScore)
    (left right : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))

theorem refiltered_mark_on_slice
    (hmarkFactor : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
            ((P.chart z).chartValues u) left *
          realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl
            (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) *
          D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
            ((P.chart z).chartValues u) right) =
        Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((P.chart z).chartValues u) marked)
    (z : refinement.problem.productive) (u : (refinement.problem.chart z).Variables → ℤ)
    (hu : u ∈ (refinement.problem.chart z).slice.integerPoints) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((refinement.problem.chart z).chartValues u) left *
        realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u
            ((refinement.refilteredMiddle hφ W Dref Fref markedMiddle middle) z).orbit) *
        D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((refinement.problem.chart z).chartValues u) right) =
      Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
        ((refinement.problem.chart z).chartValues u) marked :=
  hmarkFactor ⟨z.val, refinement.subset z.property⟩ u (refinement.inside z hu)

end Refinement
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateRefilteredSupportedStep
namespace OAI

section

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

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
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
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    (hQ : Q.filtration = Dref.filtration.quotientTop)
    (QF : RationalFilteredNilmanifold
      ((Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) ⧸
        Fref.filtration.layerIdeal (s + 1)) s nQF)
    (hQF : QF.filtration = Fref.filtration.quotientTop)
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace Fref.Space]

variable (left right : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (K : ℝ≥0)

variable (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)
    (allowed : (X → ℤ) → Prop)
    (hphysical : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      allowed ((P.chart z).physical u))
    (hrecovery : ∀ x, allowed x → ∀ source, positiveImageSlice (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) K
      (P.refilteredFrozenObservable A Fmark φ W Dref left right x)
      (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).2
      (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).1 =
        P.refilteredFrozenObservable A Fmark φ W Dref left right x source)

include hσ1 H hH hchart hsmall hp hphysical hrecovery in

theorem refilteredQuotientCandidate_score_eq_frozen_on (z : P.productive) :
    ((middle z).topQuotient Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref) Q hQ QF hQF).score
      (P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q left right markedMiddle K)
      weight = P.refilteredFrozenScore A Fmark φ hφ W Dref Fref left right markedMiddle middle z := by
  unfold AllocatedExternalLocalCandidate.score refilteredFrozenScore
  apply congrArg Complex.re
  apply Finset.expect_congr rfl
  intro u hu
  congr 1
  rw [AllocatedExternalLocalCandidate.topQuotient_value]
  have htags := P.chartValues_eq_physicalIntegerPoint hσ1 H hH hchart hsmall hp z u hu
  have hmark := (middle z).mark_on_slice u hu
  rw [htags] at hmark
  have hr := hrecovery ((P.chart z).physical u) (hphysical z u hu)
    (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit)
  simp only [RationalFilteredNilmanifold.markedTopQuotientDiagram, hmark] at hr
  exact hr

variable {frozenScoreThreshold : ℝ}
    (hscore : ∀ z : P.productive, frozenScoreThreshold ≤
      P.refilteredFrozenScore A Fmark φ hφ W Dref Fref left right markedMiddle middle z)

noncomputable def refilteredQuotientScoredProblem_on :
    AllocatedExternalCandidateProblem (E := E) A Q QF.filtration
      (Dref.topQuotientMarkedMap Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref)) (Fref.topQuotientOrbit QF hQF markedMiddle)
      (P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q left right markedMiddle K)
      weight cost massThreshold frozenScoreThreshold where
  productive := P.productive
  mass := P.mass
  chart := P.chart
  chart_path := P.chart_path
  centerLift := P.centerLift
  chart_centerLift := P.chart_centerLift
  frozen_side := P.frozen_side
  candidate z := (middle z).topQuotient Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref) Q hQ QF hQF
  score z := by
    rw [P.refilteredQuotientCandidate_score_eq_frozen_on A Fmark φ hφ W Dref hDref Fref hFref
      Q hQ QF hQF left right markedMiddle K hσ1 H hH hchart hsmall hp middle allowed hphysical hrecovery z]
    exact hscore z

variable (hmarkFactor : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) left *
        realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) *
        D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) right) =
      Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) marked)

include hmarkFactor in

theorem conclusion_of_refilteredQuotientScored_on
    (db : Basis ι ℚ L) (dw : ι → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (db '' {i | j ≤ dw i}))
    (fb : Basis κ ℚ M) (fw : κ → ℕ)
    (hfb : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (fb '' {i | j ≤ fw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis db dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    {outputCost outputMass outputScore : ℝ}
    (lower : (P.refilteredQuotientScoredProblem_on A Fmark φ hφ W Dref hDref Fref hFref
      Q hQ QF hQF left right markedMiddle K hσ1 H hH hchart hsmall hp middle allowed hphysical hrecovery hscore).Conclusion
      outputCost outputMass outputScore) :
    Nonempty (P.Conclusion outputCost outputMass outputScore) := by
  have hcompat : Dref.topQuotientMarkedOrbit Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref) Q hQ QF hQF lower.ambient =
      Fref.topQuotientOrbit QF hQF markedMiddle := by
    apply Subtype.ext
    apply NilpotentLieBCHGroup.ext
    exact lower.marked
  obtain ⟨ambientMiddle, _, hmarkedMiddle, hevalMiddle⟩ :=
    Dref.exists_marked_topQuotientOrbit_lift_externalFamily_on Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref) Q hQ QF hQF K
      (P.refilteredFrozenObservable A Fmark φ W Dref left right) allowed hrecovery
      (D.refilteredMarkedMap_layer_surjective Fmark φ hφ W Dref hDref Fref hFref
        db dw hdb fb fw hfb hW hsurj)
      lower.ambient markedMiddle hcompat
  let candidate := D.externalCandidateOrbit W Dref hDref (fullTaggedVariableWeight (X := X) J) left right ambientMiddle
  obtain ⟨restored, hmark, _, hkeep⟩ :=
    D.filtration.exists_formal_marked_orbit_restoration Fmark.filtration φ hφ
      fb fw hfb hsurj (fullTaggedVariableWeight (X := X) J) candidate marked
  have hretained (z : P.productive) (u : (P.chart z).Variables → ℤ)
      (hu : u ∈ (P.chart z).slice.integerPoints) :
      D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) restored =
        D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) candidate := by
    have hk := hkeep (fun i => ((P.chart z).chartValues u i : ℝ)) (by
      simpa only [polynomialOrbitRealEval_integer] using
        P.refilteredScoredAssembly_mark_on_slice A Fmark φ hφ W Dref hDref Fref left right
          markedMiddle middle hmarkFactor ambientMiddle hmarkedMiddle z u hu)
    simpa only [polynomialOrbitRealEval_integer] using hk
  refine ⟨{
    ambient := restored
    marked := hmark
    retained := lower.retained
    subset := lower.subset
    mass := lower.mass
    step := lower.step
    step_pos := lower.step_pos
    slice := lower.slice
    dense := lower.dense
    inside := lower.inside
    score := ?_
  }⟩
  intro z
  apply (lower.score z).trans_eq
  unfold ambientScore
  apply congrArg Complex.re
  apply Finset.expect_congr rfl
  intro u hu
  let zp : P.productive := ⟨z.val, lower.subset z.property⟩
  have huOriginal : u ∈ (P.chart zp).slice.integerPoints := lower.inside z hu
  have htags := P.chartValues_eq_physicalIntegerPoint hσ1 H hH hchart hsmall hp zp u huOriginal
  change weight ((P.chart zp).physical u) *
      P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q left right markedMiddle K
        ((P.chart zp).physical u)
        (QuotientGroup.mk (Q.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((P.chart zp).chartValues u) lower.ambient)) =
    weight ((P.chart zp).physical u) * observable ((P.chart zp).physical u)
      (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
        ((P.chart zp).chartValues u) restored))
  congr 1
  rw [hretained zp u huOriginal]
  have ha := D.externalCandidateOrbit_realEval W Dref hDref (fullTaggedVariableWeight (X := X) J) left right ambientMiddle
    (fun i => ((P.chart zp).chartValues u i : ℝ))
  simp only [polynomialOrbitRealEval_integer] at ha
  change _ = observable ((P.chart zp).physical u)
    (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
      ((P.chart zp).chartValues u) (D.externalCandidateOrbit W Dref hDref (fullTaggedVariableWeight (X := X) J) left right ambientMiddle)))
  rw [ha]
  have hr := hevalMiddle ((P.chart zp).physical u) (hphysical zp u huOriginal)
    (fun i => ((P.chart zp).chartValues u i : ℝ))
  simp only [polynomialOrbitRealEval_integer] at hr
  simpa only [refilteredQuotientObservable, refilteredFrozenObservable, ← htags] using hr

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateUniformSuccessor
namespace OAI

section

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

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
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
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)

variable (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (hsection : Function.RightInverse sectionMap φ)
    (leftMark rightMark : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (kE kR : D.RealGroup)
    (hkE : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ kE = 1)
    (hkR : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ kR = 1)
    (localLeft localRight : ∀ z : P.productive,
      (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : (P.chart z).Variables => 1)).Group)
    (localLeftMark localRightMark : ∀ z : P.productive,
      (Fmark.filtration.realification.adaptedPolynomialFiltration
        (fun _ : (P.chart z).Variables => 1)).Group)
    (hfactor : ∀ z : P.productive,
      localLeft z * P.refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref
        markedMiddle middle z * localRight z =
      D.filtration.realification.polynomialOrbitCoordinates _ (P.candidate z).orbit)
    (hleft : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localLeftMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => ((P.chart z).chartValues u i : ℝ)) leftMark)
    (hright : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localRightMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => ((P.chart z).chartValues u i : ℝ)) rightMark)

namespace Refinement

variable {A Fmark φ P} {newCost newMass newScore : ℝ}
    (refinement : P.Refinement newCost newMass newScore)

include hsection hkE hkR hfactor hleft hright

theorem nativeFrozen_mark_on_slice
    (hprojLeft : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ => 1) (localLeft z) = localLeftMark z)
    (hprojRight : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ => 1) (localRight z) = localRightMark z)
    (z : refinement.problem.productive) (u : (refinement.problem.chart z).Variables → ℤ)
    (hu : u ∈ (refinement.problem.chart z).slice.integerPoints) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((refinement.problem.chart z).chartValues u)
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J)
            sectionMap hSectionFilt leftMark kE) *
        realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u
            ((refinement.refilteredMiddle hφ W Dref Fref markedMiddle middle) z).orbit) *
        D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((refinement.problem.chart z).chartValues u)
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J)
            sectionMap hSectionFilt rightMark kR)) =
      Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
        ((refinement.problem.chart z).chartValues u) marked := by
  apply refinement.refiltered_mark_on_slice hφ W Dref Fref markedMiddle middle
    (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J)
      sectionMap hSectionFilt leftMark kE)
    (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J)
      sectionMap hSectionFilt rightMark kR) ?_ z u hu
  exact P.refilteredFrozen_mark_on_slice A Fmark φ hφ W Dref hDref Fref markedMiddle middle
    sectionMap hSectionFilt hsection leftMark rightMark kE kR hkE hkR
    localLeft localRight localLeftMark localRightMark hfactor hleft hright hprojLeft hprojRight

end Refinement
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateNativeMiddleCoordinates
namespace OAI

section

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

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
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
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)

theorem refilteredLocalCoordinates_eq_of_log
    (nativeMiddle : ∀ z : P.productive,
      (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : (P.chart z).Variables => 1)).Group)
    (hlog : ∀ z, map
      (realLieHomToRat (realificationLieHom
        (D.filtration.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        (middle z).orbit.log = ((nativeMiddle z).coord :
          VectorPolynomial (P.chart z).Variables ℚ (ℝ ⊗[ℚ] L)))
    (z : P.productive) :
    P.refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z =
      nativeMiddle z := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact hlog z

theorem refilteredLocalCoordinates_factor_of_log
    (left nativeMiddle right : ∀ z : P.productive,
      (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : (P.chart z).Variables => 1)).Group)
    (hlog : ∀ z, map
      (realLieHomToRat (realificationLieHom
        (D.filtration.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        (middle z).orbit.log = ((nativeMiddle z).coord :
          VectorPolynomial (P.chart z).Variables ℚ (ℝ ⊗[ℚ] L)))
    (hfactor : ∀ z, left z * nativeMiddle z * right z =
      D.filtration.realification.polynomialOrbitCoordinates _ (P.candidate z).orbit)
    (z : P.productive) :
    left z * P.refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref
      markedMiddle middle z * right z =
      D.filtration.realification.polynomialOrbitCoordinates _ (P.candidate z).orbit := by
  rw [P.refilteredLocalCoordinates_eq_of_log A Fmark φ hφ W Dref hDref Fref
    markedMiddle middle nativeMiddle hlog z]
  exact hfactor z

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateResetSuccessor
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realChartSubstitute realPolynomialGroupMap associatedGradedMap gradedRefiltrationMap

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
    {L M κ : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    {c : Basis κ ℚ M} {ν : κ → ℕ}
    {hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i})}
    {g : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors Fmark.filtration c ν hF (fullTaggedVariableWeight J)
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) g EF RF)
    (slow : ℝ) (denominator : ℕ)

namespace AllocatedExternalGlobalNativeResetFamily

variable {Fmark φ hφ P keep hkeep W factors slow denominator}

noncomputable def leftMark
    (_reset : AllocatedExternalGlobalNativeResetFamily Fmark φ hφ P keep hkeep W factors slow denominator) :
    Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J) :=
  (Fmark.filtration.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J)).symm factors.left

variable (reset : AllocatedExternalGlobalNativeResetFamily
    Fmark φ hφ P keep hkeep W factors slow denominator)

variable {nD nF : ℕ}
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

theorem candidate_included_log (z : (P.withKeep keep hkeep).productive) :
    map (realLieHomToRat (realificationLieHom
      (D.filtration.gradedRefiltrationSubalgebra W).incl)).toLinearMap
      (reset.candidate Dref hDref Fref hFref z).orbit.log =
      ((reset.localMiddle z).coord : VectorPolynomial {i // keep i} ℚ (ℝ ⊗[ℚ] L)) :=
  reset.native_log z

end AllocatedExternalGlobalNativeResetFamily
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedDeterminingMatrixBudget
namespace OAI

section

namespace Erdos3

open Module Submodule VectorPolynomial BohrLattice.MinkowskiSecondBox
open scoped BigOperators

namespace RankPreparationLayer

variable {X J : Type} (L : RankPreparationLayer X J)

attribute [local irreducible] rank

theorem shortIntegralBasisNormBound_le_exp {H R : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hcoord : (Fintype.card L.Coord : ℝ) ≤ p)
    (hcols : (Fintype.card L.Column : ℝ) ≤ p)
    (hrows : (Fintype.card L.Row : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hR : (R : ℝ) ≤ Real.exp p) :
    L.shortIntegralBasisNormBound H R ≤ Real.exp ((p + 2) ^ 124) := by
  have hrank : (L.rank : ℝ) ≤ p :=
    (Nat.cast_le.mpr L.rank_le_coord_card).trans hcoord
  have hgen := jointSpaceGeneratorHeight_le_exp
    (Fintype.card L.Coord) (Fintype.card L.Column) (Fintype.card L.Row) H R
    hp hcoord hcols hrows hH hR
  have hfront : (L.rank : ℝ) * L.rank.factorial * minkowskiSecondConstant L.rank ≤
      Real.exp (4 * (p + 1) ^ 2) := by
    calc
      _ ≤ projectedAxisNormBudget L.rank := by
        unfold projectedAxisNormBudget
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (show (L.rank : ℝ) ≤ L.rank + 1 by linarith) (Nat.cast_nonneg _))
          (minkowskiSecondConstant_nonneg L.rank)
      _ ≤ Real.exp (4 * ((L.rank : ℝ) + 1) ^ 2) := projectedAxisNormBudget_le_exp L.rank
      _ ≤ _ := Real.exp_le_exp.mpr (by gcongr)
  have hcoordexp : (Fintype.card L.Coord : ℝ) ≤ Real.exp p :=
    hcoord.trans (by linarith only [Real.add_one_le_exp p])
  have hpow :
      (jointSpaceGeneratorHeight (Fintype.card L.Coord) (Fintype.card L.Column)
        (Fintype.card L.Row) H R : ℝ) ^ (Fintype.card L.Coord * Fintype.card L.Coord) ≤
      Real.exp (p ^ 2 * (p + 2) ^ 120) := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hgen _).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    simp only [Nat.cast_mul]
    calc
      (Fintype.card L.Coord : ℝ) * Fintype.card L.Coord * (p + 2) ^ 120 ≤
          (p * p) * (p + 2) ^ 120 := by gcongr
      _ = _ := by rw [pow_two]
  have hnorm : L.shortIntegralBasisNormBound H R ≤
      Real.exp (4 * (p + 1) ^ 2 + p + p ^ 2 * (p + 2) ^ 120) := by
    unfold shortIntegralBasisNormBound
    calc
      _ ≤ Real.exp (4 * (p + 1) ^ 2) *
          (Real.exp p * Real.exp (p ^ 2 * (p + 2) ^ 120)) := by
        apply mul_le_mul hfront (mul_le_mul hcoordexp hpow (by positivity)
          (Real.exp_nonneg _)) (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [Real.exp_add, Real.exp_add, mul_assoc]
  apply hnorm.trans (Real.exp_le_exp.mpr ?_)
  have hbase : 1 ≤ p + 2 := by linarith
  have hsmall : 4 * (p + 1) ^ 2 + p ≤ 5 * (p + 2) ^ 2 := by nlinarith
  have hcube : (5 : ℝ) ≤ (p + 2) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      (by linarith : (2 : ℝ) ≤ p + 2) 3
    norm_num at h
    linarith
  have hsmall' : 4 * (p + 1) ^ 2 + p ≤ (p + 2) ^ 5 := by
    apply hsmall.trans
    calc
      5 * (p + 2) ^ 2 ≤ (p + 2) ^ 3 * (p + 2) ^ 2 := by gcongr
      _ = _ := by rw [← pow_add]
  have hmain : p ^ 2 * (p + 2) ^ 120 ≤ (p + 2) ^ 122 := by
    calc
      _ ≤ (p + 2) ^ 2 * (p + 2) ^ 120 := by gcongr; linarith
      _ = _ := by rw [← pow_add]
  have hsmall122 := hsmall'.trans (pow_le_pow_right₀ hbase (by decide : 5 ≤ 122))
  calc
    _ ≤ (p + 2) ^ 122 + (p + 2) ^ 122 := add_le_add hsmall122 hmain
    _ = 2 * (p + 2) ^ 122 := (two_mul _).symm
    _ ≤ (p + 2) * (p + 2) ^ 122 := by gcongr; linarith
    _ = (p + 2) ^ 123 := (pow_succ' (p + 2) 122).symm
    _ ≤ (p + 2) ^ 124 := pow_le_pow_right₀ hbase (by decide)

theorem exists_bounded_integral_basis {d H R : ℕ} {p : ℝ}
    (hL : L.Valid d H R) (hH : 1 ≤ H) (hR : 1 ≤ R)
    (hp : 0 ≤ p) (hcoord : (Fintype.card L.Coord : ℝ) ≤ p)
    (hcols : (Fintype.card L.Column : ℝ) ≤ p)
    (hrows : (Fintype.card L.Row : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hRp : (R : ℝ) ≤ Real.exp p) :
    ∃ bW : Basis (Fin L.rank) ℤ
      (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space)),
      ∀ a, ‖(bW a).val‖ ≤ Real.exp ((p + 2) ^ 124) := by
  obtain ⟨bW, hbW⟩ := L.exists_short_integral_basis hL hH hR
  exact ⟨bW, fun a => (hbW a).trans
    (L.shortIntegralBasisNormBound_le_exp hp hcoord hcols hrows hHp hRp)⟩

end RankPreparationLayer

namespace RankPreparationFamily

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.exists_bounded_integral_bases
    {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p)
    (hcoord : ∀ j, (Fintype.card (L j).Coord : ℝ) ≤ p)
    (hcols : ∀ j, (Fintype.card (L j).Column : ℝ) ≤ p)
    (hrows : ∀ j, (Fintype.card (L j).Row : ℝ) ≤ p) :
    ∃ bW : ∀ j, Basis (PreparedSamplerContinuous L j) ℤ
      (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)),
      ∀ j a, ‖(bW j a).val‖ ≤ Real.exp ((p + 2) ^ preparedIntegralBasisExponent m) := by
  let q := (p + 2) ^ budgetDepthExponent 38 m
  have hpq : p ≤ q := le_power_budget hp (preparationExponent_pos m)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hheight (j : Fin m) :
      (preparationHeight p (m - 1 - j.val) : ℝ) ≤ Real.exp q :=
    (Nat.cast_le.mpr (preparationHeight_mono hp (by omega : m - 1 - j.val ≤ m))).trans
      (preparationHeight_le_exp p m)
  have hRpq : (R : ℝ) ≤ Real.exp q := hRp.trans (Real.exp_le_exp.mpr hpq)
  have heach (j : Fin m) := (L j).exists_bounded_integral_basis
    (hL j) (preparationHeight_pos hp _) hR hq
    ((hcoord j).trans hpq) ((hcols j).trans hpq) ((hrows j).trans hpq)
    (hheight j) hRpq
  choose bW hbW using heach
  refine ⟨bW, fun j a => (hbW j a).trans (Real.exp_le_exp.mpr ?_)⟩
  exact shifted_power_budget_le hp (budgetDepthExponent 38 m) 124

theorem PreparedHeights.exists_bounded_integral_bases_of_sized
    {p : ℝ} {R D t T : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p)
    (hsize : L.Sized D t) (ht : t ≤ T)
    (hcap : (preparationCoordinateCap m D T : ℝ) ≤ p) :
    ∃ bW : ∀ j, Basis (PreparedSamplerContinuous L j) ℤ
      (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)),
      ∀ j a, ‖(bW j a).val‖ ≤ Real.exp ((p + 2) ^ preparedIntegralBasisExponent m) := by
  apply hL.exists_bounded_integral_bases L hp hR hRp
  · intro j
    exact (Nat.cast_le.mpr (preparationCoordinateCap_bounds hsize ht j).1).trans hcap
  · intro j
    exact (Nat.cast_le.mpr (preparationCoordinateCap_bounds hsize ht j).2.1).trans hcap
  · intro j
    have h := (preparationCoordinateCap_bounds hsize ht j).2.2
    exact (Nat.cast_le.mpr (Nat.le_trans (Nat.le_succ _) h)).trans hcap

end RankPreparationFamily
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedEarlyLateSamplerGeometry
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.exists_early_late_sampler_geometry
    {pPrep pLate : ℝ} {R D t T : ℕ} (hL : L.PreparedHeights pPrep R)
    (hpPrep : 0 ≤ pPrep) (hR : 1 ≤ R) (hPrepLate : pPrep ≤ pLate)
    (hRLate : (R : ℝ) ≤ Real.exp pLate)
    (hsize : L.Sized D t) (ht : t ≤ T)
    (hcapLate : (preparationCoordinateCap m D T : ℝ) ≤ pLate) :
    let M := preparationCoordinateCap m D T
    ∃ (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ
        (euclideanSubspace (L j).space)ᗮ)
      (_o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ
        (euclideanSubspace (L j).space))
      (bW : ∀ j, Basis (PreparedSamplerContinuous L j) ℤ
        (latticeSection (standardEuclideanLattice (L j).Coord)
          (euclideanSubspace (L j).space))),
      (∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (L j).space)) ∧
      (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j) z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j)).symm z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ≤
          Real.exp (allocatedUniformChartLog (M : ℝ))) ∧
      (∀ j a, ‖(bW j a).val‖ ≤
        Real.exp ((pLate + 2) ^ preparedIntegralBasisExponent m)) ∧
      (∀ j i, (basisAxisScale (b j) i : ℝ) ≤
        Real.exp ((pLate + 2) ^ preparedIntegralBasisExponent m)) := by
  intro M
  have hLate := hL.mono_parameter L hpPrep hPrepLate
  have hpLate : 0 ≤ pLate := hpPrep.trans hPrepLate
  obtain ⟨b, o, _oldIntegralBasis, hb, hf, hi, hv⟩ :=
    hL.exists_canonical_sampler_geometry L hpPrep hR
      (fun j => (preparationCoordinateCap_bounds hsize ht j).1)
  obtain ⟨bW, hbW⟩ := hLate.exists_bounded_integral_bases_of_sized L
    hpLate hR hRLate hsize ht hcapLate
  refine ⟨b, o, bW, hb, hf, hi, hv, hbW, ?_⟩
  apply hLate.basisAxisScale_le_exp L b hb hpLate hRLate
  · intro j
    exact (Nat.cast_le.mpr (preparationCoordinateCap_bounds hsize ht j).1).trans hcapLate
  · intro j
    exact (Nat.cast_le.mpr (preparationCoordinateCap_bounds hsize ht j).2.1).trans hcapLate
  · intro j
    have h := (preparationCoordinateCap_bounds hsize ht j).2.2
    exact (Nat.cast_le.mpr (Nat.le_trans (Nat.le_succ _) h)).trans hcapLate

end Erdos3.RankPreparationFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidatePrimitivePhysicalBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open NilpotentLieFiltration RationalFilteredNilmanifold

theorem candidateGeneratedPhysicalScalarBounds (s A : ℕ) {p pOuter : ℝ}
    (hp : 0 ≤ p) (hpOuter : 0 ≤ pOuter) (hpOuterBound : pOuter ≤ (p + A) ^ A) :
    GeneratedPhysicalSuccessorScalarBounds s A
      (candidateGeneratedPhysicalBudgetExponent s A) p pOuter :=
  (Classical.choose_spec (exists_generatedPhysicalSuccessorScalarBounds s A)).2
    p hp pOuter hpOuter hpOuterBound

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open RationalFilteredNilmanifold

theorem candidatePrimitivePhysicalBudgetExponent_ge_two (s a : ℕ) :
    2 ≤ candidatePrimitivePhysicalBudgetExponent s a :=
  candidateGeneratedPhysicalBudgetExponent_ge_two s (candidateFreezingOuterExponent s a)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateThresholdSuccessor
namespace OAI

section

namespace Erdos3.VectorPolynomial
open NilpotentLieFiltration RationalFilteredNilmanifold

theorem candidatePrimitiveFreezingCutoff_add_two_le_geometry (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    candidatePrimitiveFreezingCutoff s a p + 2 ≤
      candidatePrimitivePhysicalGeometryParameter s a p := by
  let Cfree := nativeMarkedFreezingExponent (s + 1) a
  let outerExponent := candidateFreezingOuterExponent s a
  let B := frozenMarkedPhysicalExponent (s + 1)
  let R := allocatedRightDictionaryExponent (s + 1)
  let outer := candidateCoveredOuterParameter outerExponent p
  let right := candidateCoveredRightParameter outerExponent B p
  let dict := candidateCoveredDictionaryParameter outerExponent B R p
  have houter : nativeMarkedFreezingPhysicalParameter p Cfree ≤ outer :=
    candidatePrimitivePhysicalOuterParameter_bound s a hp
  have houter0 : 0 ≤ outer := by dsimp [outer, candidateCoveredOuterParameter]; positivity
  have hdict0 : 0 ≤ dict := by
    dsimp [dict, candidateCoveredDictionaryParameter, candidateCoveredRightParameter,
      candidateCoveredOuterParameter]
    positivity
  have hB : 2 ≤ B := frozenMarkedPhysicalExponent_ge_two (s + 1)
  have hright : outer ≤ right := by
    apply (le_power_budget houter0 (by omega : 1 ≤ B)).trans
    dsimp [right, candidateCoveredRightParameter]
    exact pow_le_pow_left₀ (by positivity)
      (add_le_add le_rfl (by exact_mod_cast hB : (2 : ℝ) ≤ B)) B
  have hlarge : 3 ≤ (p + 3) ^ 36 := by
    have hpow : p + 3 ≤ (p + 3) ^ 36 := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ p + 3)
        (by norm_num : (1 : ℕ) ≤ 36)
    linarith
  have hblog : (p + Cfree) ^ Cfree + 3 ≤ outer := by
    dsimp [nativeMarkedFreezingPhysicalParameter] at houter
    linarith
  change p + 2 * (p + Cfree) ^ Cfree + 2 + 2 ≤ p + outer + right + dict + 1
  linarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedFiniteNestedSourceProjectionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def preparedConditionalExcessRequired (m : ℕ) (Plate E : ℝ) : ℝ :=
  (max (4 * (Plate + 8) ^ 2) E + allocatedExternalConditionalExcessExponent m) ^
    allocatedExternalConditionalExcessExponent m

end Erdos3.VectorPolynomial

end

end OAI
end


