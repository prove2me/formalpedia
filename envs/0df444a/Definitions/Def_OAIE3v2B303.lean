-- Prove2me | Definitions.Def_OAIE3v2B303
-- name    : OAIE3v2B303
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T06:21:45.215657+00:00
-- url     : https://prove2.me/theorems/76005a65-d1bd-42f5-9954-5cd3d098d330
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 265 of 311
-- statement:
--   Definitions bundle 265 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B258` of this split.
--
--   Modules: `Dynamics/AllocatedExternalCandidateExponentialFreezingBudget.lean`, `Dynamics/AllocatedExternalCandidatePrimitivePhysicalBudget.lean`, `Estimates/AllocatedExternalCandidateFiniteFreezingDictionaryProducer.lean`, `Estimates/AllocatedExternalCandidateObservableRestriction.lean`, `Estimates/PreparedDetectedCanonicalNativeSource.lean`, `Estimates/PreparedModularGeneralProductivityEarlyGain.lean`, `Geometry/ActualFixedSpatialRetainedModulusBudget.lean`, `Geometry/ActualFixedSpatialRetainedPatchEndpoint.lean`, `Linear/ActualFixedSpatialSlicedRetainedKernelComparison.lean`, `Polynomial/PolynomialPatchTaggedBufferedScore.lean`, `Sampling/AllocatedExternalCandidateNativeFrozenScore.lean`, `Sampling/AllocatedExternalCandidatePhysicalScore.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B258

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

noncomputable def physicalIntegerPoint (x : X → ℤ) : X ⊕ (Σ j, J j) → ℤ :=
  fullTaggedPhysicalIntegerPoint J poly (fun j => (P.centerLift j).val) x

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

    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)

noncomputable def refilteredLocalCoordinates (z : P.productive) :
    (D.filtration.realification.adaptedPolynomialFiltration
      (fun _ : (P.chart z).Variables => 1)).Group :=
  D.filtration.realification.polynomialOrbitCoordinates _
    (D.includedRefilteredOrbit W Dref hDref _ (middle z).orbit)

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] in

theorem refilteredLocalCoordinates_value (z : P.productive)
    (u : (P.chart z).Variables → ℤ) :
    D.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
      (P.refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z) =
      realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl
        (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) := by
  simpa only [refilteredLocalCoordinates,
    NilpotentLieFiltration.nativeFrozenMarkedOrbitCoordinates_realValue,
    polynomialOrbitRealEval_integer] using
      D.includedRefilteredOrbit_realEval W Dref hDref (fun _ => 1) (middle z).orbit
        (fun i => (u i : ℝ))

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

    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)

namespace Refinement
variable {A Fmark φ P} {newCost newMass newScore : ℝ}
    (refinement : P.Refinement newCost newMass newScore)

noncomputable def refilteredMiddle : ∀ z : refinement.problem.productive,
    AllocatedExternalLocalCandidate (refinement.problem.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      markedMiddle := fun z =>
  (middle ⟨z.val, refinement.subset z.property⟩).refineSlice
    (refinement.step z) (refinement.step_pos z) (refinement.slice z) (refinement.dense z)
    (refinement.inside z)

end Refinement

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateExponentialFreezingBudget
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

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace Refinement
variable {P} {newCost newMass newScore : ℝ}
    (refinement : P.Refinement newCost newMass newScore)

noncomputable def mono {cost' mass' score' : ℝ}
    (hcost : newCost ≤ cost') (hmass : mass' ≤ newMass) (hscore : score' ≤ newScore) :
    P.Refinement cost' mass' score' where
  retained := refinement.retained
  subset := refinement.subset
  mass := hmass.trans refinement.mass
  cost_le := refinement.cost_le.trans hcost
  step := refinement.step
  step_pos := refinement.step_pos
  slice := refinement.slice
  dense z := (refinement.dense z).mono hcost
  inside := refinement.inside
  scoreLower z := hscore.trans (refinement.scoreLower z)

end Refinement
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedDetectedCanonicalNativeSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (0 + 1))))
variable (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (pDetect qDetect α : ℝ)
variable {P : ℝ}

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

structure AllocatedEarlyNativeSourceGeometry
    (Pchart P D target Pk Prho Qstride pDetect : ℝ) (K : ℝ≥0) where
  hP : 0 ≤ P
  hRP : ∀ j, R j ≤ Real.exp P
  hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P
  hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P
  hcount : ∀ j : Fin m, (Fintype.card
    (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P
  hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (0 + 1)) selectedRows D
  hPk : 0 ≤ Pk
  hPrho : 0 ≤ Prho
  htarget : 0 ≤ target
  hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target (pDetect + 1)
    (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤ S.value
  η : ℝ
  hη0 : 0 ≤ η
  hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4))
  ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0
  t : ℝ
  htone : t ≤ 1
  hs : AllocatedAffineCoveredComparison.{0, 0, _, _, _, _, _} (G := G) B rows
    (Real.exp (-(pDetect + 1))) η ρ t htone
  hρ : ∀ partition, 0 < ρ partition
  hρ1 : ∀ partition, ρ partition ≤ 1
  hρlog : ∀ partition, (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho
  hσsmall : ∀ j, σ j ≤ t
  T : Fin m → ℝ
  hT : ∀ j, partitionedIdealRadius (Fin (0 + 1)) m + 1 ≤ T j
  hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
    (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card (Fin (0 + 1)) *
        ((Fintype.card (Fin (0 + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j
  siteRadius : ℝ≥0
  hrone : 1 ≤ siteRadius
  hradius : ∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)
  hbudgets : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) → (∀ j, C j ≤ Real.exp Pchart) →
    (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
    (∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
    (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (0 + 1))) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)
  hK : ∀ j, (R j)⁻¹ ≤ K

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralProductivityEarlyGain
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1))))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (pDetect qDetect α : ℝ)
variable {P : ℝ}

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

structure AllocatedEarlyNativeSourceGeometryGeneral
    (Pchart P D target Pk Prho Qstride pDetect : ℝ) (K : ℝ≥0) where
  hP : 0 ≤ P
  hRP : ∀ j, R j ≤ Real.exp P
  hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P
  hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P
  hcount : ∀ j : Fin m, (Fintype.card
    (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P
  hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) selectedRows D
  hPk : 0 ≤ Pk
  hPrho : 0 ≤ Prho
  htarget : 0 ≤ target
  hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target (pDetect + 1)
    (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤ S.value
  η : ℝ
  hη0 : 0 ≤ η
  hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4))
  ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0
  t : ℝ
  htone : t ≤ 1
  hs : AllocatedAffineCoveredComparison.{0, 0, _, _, _, _, _} (G := G) B rows
    (Real.exp (-(pDetect + 1))) η ρ t htone
  hρ : ∀ partition, 0 < ρ partition
  hρ1 : ∀ partition, ρ partition ≤ 1
  hρlog : ∀ partition, (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho
  hσsmall : ∀ j, σ j ≤ t
  T : Fin m → ℝ
  hT : ∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j
  hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
    (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) *
        ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j
  siteRadius : ℝ≥0
  hrone : 1 ≤ siteRadius
  hradius : ∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)
  hbudgets : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) → (∀ j, C j ≤ Real.exp Pchart) →
    (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
    (∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
    (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)
  hK : ∀ j, (R j)⁻¹ ≤ K

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialRetainedModulusBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

namespace VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

attribute [local instance] retainedLabelDecidableEq

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.smallReferencePrimeNeZero
attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.smallReferenceModulusNeZero
noncomputable def retainedCRTReferenceForecast {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (gridVolume : ℝ) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) : ℝ :=
  rationalInactiveForecast inactive (fun _ => path.referenceRetainedCRTInputLaw cutoff) gridPoint
    (fun i => integerLongPolynomialOutput path.referencePolynomial (raw i)
      (path.referenceRetainedCRTModulus cutoff))
    (path.referenceRetainedCRTModulus cutoff) gridVolume z
    (fun j => ZMod.castHom (path.referenceRetainedCRTModulus_dvd cutoff)
      (ZMod (path.referenceRetainedCRTModulus cutoff)) (β j))

noncomputable def retainedCRTIndependentForecast {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (gridVolume : ℝ) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) : ℝ :=
  rationalInactiveForecast inactive
    (fun _ => crtPrimePowerPolynomialLaw
      (V := LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B)
      (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
      (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val)) gridPoint
    (fun i => crtPrimePowerIntegerPolynomialOutput
      (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
      (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val)
      (fun p : path.referenceRetainedPrimes cutoff => path.prescribed p.val.val)
      (primePower_crt_coprime (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
        (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val)
        (fun p => path.prime p.val.val p.val.property)
        (Subtype.val_injective.comp Subtype.val_injective))
      (path.localReferencePolynomial (raw i)) (fun p => path.origin p.val))
    (path.referenceRetainedCRTModulus cutoff) gridVolume z
    (fun j => ZMod.castHom (path.referenceRetainedCRTModulus_dvd cutoff)
      (ZMod (path.referenceRetainedCRTModulus cutoff)) (β j))

omit [Fintype Tsp] in
theorem referenceRetainedCRTModulus_pos (cutoff : ℕ) :
    0 < path.referenceRetainedCRTModulus cutoff := by
  rw [path.referenceRetainedCRTModulus_eq]
  exact path.referenceRetainedModulus_pos cutoff

end ActualFixedSpatialForecastPath
end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualFixedSpatialSlicedRetainedKernelComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

noncomputable def recoveredG
    (v : X → ℝ) (r : X → ZMod slice.path.referenceModulus)
    (β : Fin d → ℤ) (y : Fin d → ℝ) : ℝ := by
  letI : NeZero slice.path.referenceModulus := ⟨slice.path.referenceModulus_pos.ne'⟩
  exact forecastLawRecoveredKernel B U b S slice.principalLaw
    (slice.density hB) selected slice.path.sample slice.path.commonTuple
    (fun _ => slice.path.referenceInputLaw)
    (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
      (fun k => (z k.1 k.2 : ℤ)) slice.path.referenceModulus t j)
    slice.path.referenceModulus (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW v r
    (fun a => β (e.symm a)) (fun a => y (e.symm a))

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

local instance fullReferenceNonzero : NeZero slice.path.referenceModulus :=
  ⟨slice.path.referenceModulus_pos.ne'⟩
local instance retainedReferenceNonzero (cutoff : ℕ) :
    NeZero (slice.path.referenceRetainedCRTModulus cutoff) :=
  ⟨by rw [slice.path.referenceRetainedCRTModulus_eq];
      exact (slice.path.referenceRetainedModulus_pos cutoff).ne'⟩

noncomputable def retainedRecoveredG (cutoff : ℕ)
    (v : X → ℝ) (r : X → ZMod (slice.path.referenceRetainedCRTModulus cutoff))
    (β : Fin d → ℤ) (y : Fin d → ℝ) : ℝ :=
  forecastLawRecoveredKernel B U b S slice.principalLaw
    (slice.density hB) selected slice.path.sample slice.path.commonTuple
    (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff)
    (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
      (fun k => (z k.1 k.2 : ℤ)) (slice.path.referenceRetainedCRTModulus cutoff) t j)
    (slice.path.referenceRetainedCRTModulus cutoff)
    (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW v r
    (fun a => β (e.symm a)) (fun a => y (e.symm a))

noncomputable def recoveredRationalFactor
    (r : X → ZMod slice.path.referenceModulus) (β : Fin d → ℤ) : ℝ :=
  forecastLawRecoveredRationalFactor B U b S slice.principalLaw selected
    slice.path.sample slice.path.commonTuple (fun _ => slice.path.referenceInputLaw)
    (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
      (fun k => (z k.1 k.2 : ℤ)) slice.path.referenceModulus t j)
    slice.path.referenceModulus (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    hb bW r (fun a => β (e.symm a))

noncomputable def retainedRecoveredRationalFactor (cutoff : ℕ)
    (r : X → ZMod (slice.path.referenceRetainedCRTModulus cutoff)) (β : Fin d → ℤ) : ℝ :=
  forecastLawRecoveredRationalFactor B U b S slice.principalLaw selected
    slice.path.sample slice.path.commonTuple (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff)
    (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
      (fun k => (z k.1 k.2 : ℤ)) (slice.path.referenceRetainedCRTModulus cutoff) t j)
    (slice.path.referenceRetainedCRTModulus cutoff)
    (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ)) hb bW r
    (fun a => β (e.symm a))

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

local instance retainedBoundsReferenceNonzero (cutoff : ℕ) :
    NeZero (slice.path.referenceRetainedCRTModulus cutoff) :=
  ⟨(slice.path.referenceRetainedCRTModulus_pos cutoff).ne'⟩

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialRetainedPatchEndpoint
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

noncomputable def scaledRetainedRecoveredG (cutoff : ℕ) (κ : ℝ)
    (v : X → ℝ) (r : X → ZMod (slice.path.referenceRetainedCRTModulus cutoff))
    (β : Fin d → ℤ) (y : Fin d → ℝ) : ℝ :=
  κ * slice.retainedRecoveredG selected hB o bW hb e cutoff v r β y

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidatePrimitivePhysicalBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open NilpotentLieFiltration RationalFilteredNilmanifold

noncomputable def candidateGeneratedPhysicalGeometryParameter (s A : ℕ) (p : ℝ) : ℝ :=
  candidateCoveredGeometryParameter A (frozenMarkedPhysicalExponent (s + 1))
    (allocatedRightDictionaryExponent (s + 1)) p

structure GeneratedPhysicalSuccessorScalarBounds (s A C : ℕ) (p pOuter : ℝ) : Prop where
  input_budget : (p + A) ^ A ≤ (p + C) ^ C
  geometry_one : 1 ≤ candidateGeneratedPhysicalGeometryParameter s A p
  input_geometry : p ≤ candidateGeneratedPhysicalGeometryParameter s A p
  outer_geometry : pOuter ≤ candidateGeneratedPhysicalGeometryParameter s A p
  outer_budget : pOuter ≤ (p + C) ^ C
  physical_geometry :
    (pOuter + frozenMarkedPhysicalExponent (s + 1)) ^ frozenMarkedPhysicalExponent (s + 1) ≤
      candidateGeneratedPhysicalGeometryParameter s A p
  right_geometry :
    ((pOuter + frozenMarkedPhysicalExponent (s + 1)) ^ frozenMarkedPhysicalExponent (s + 1) +
      allocatedRightDictionaryExponent (s + 1)) ^ allocatedRightDictionaryExponent (s + 1) ≤
      candidateGeneratedPhysicalGeometryParameter s A p
  geometry_budget : candidateGeneratedPhysicalGeometryParameter s A p ≤ (p + C) ^ C
  covered_budget :
    (candidateGeneratedPhysicalGeometryParameter s A p + allocatedCoveredLowerExponent s 1) ^
      allocatedCoveredLowerExponent s 1 ≤ (p + C) ^ C
  geometry_recursive :
    candidateGeneratedPhysicalGeometryParameter s A p ≤ finiteFreezingRecursiveParameter C p
  covered_recursive :
    (candidateGeneratedPhysicalGeometryParameter s A p + allocatedCoveredLowerExponent s 1) ^
      allocatedCoveredLowerExponent s 1 ≤ finiteFreezingRecursiveParameter C p

theorem exists_generatedPhysicalSuccessorScalarBounds (s A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → ∀ pOuter : ℝ,
      0 ≤ pOuter → pOuter ≤ (p + A) ^ A →
      GeneratedPhysicalSuccessorScalarBounds s A C p pOuter := by
  obtain ⟨C, hC, hbound⟩ := exists_candidateCoveredParameters_bound A
    (frozenMarkedPhysicalExponent (s + 1)) (allocatedRightDictionaryExponent (s + 1))
    (allocatedCoveredLowerExponent s 1)
  refine ⟨C, hC, ?_⟩
  intro p hp pOuter hpOuter hpOuterBound
  obtain ⟨houterBudget, hgeoBudget, hcoverBudget, hpGeo, hRightGeo, hDictGeo,
    hGeoRec, hCoverRec⟩ := hbound p hp
  have hgeometry := candidateCoveredGeometryParameter_bounds A
    (frozenMarkedPhysicalExponent (s + 1)) (allocatedRightDictionaryExponent (s + 1)) hp
  have hphysical :
      (pOuter + frozenMarkedPhysicalExponent (s + 1)) ^ frozenMarkedPhysicalExponent (s + 1) ≤
        candidateCoveredRightParameter A (frozenMarkedPhysicalExponent (s + 1)) p := by
    unfold candidateCoveredRightParameter candidateCoveredOuterParameter
    exact pow_le_pow_left₀
      (by positivity : 0 ≤ pOuter + (frozenMarkedPhysicalExponent (s + 1) : ℝ))
      (by linarith)
      (frozenMarkedPhysicalExponent (s + 1))
  have hright :
      ((pOuter + frozenMarkedPhysicalExponent (s + 1)) ^ frozenMarkedPhysicalExponent (s + 1) +
        allocatedRightDictionaryExponent (s + 1)) ^ allocatedRightDictionaryExponent (s + 1) ≤
        candidateCoveredDictionaryParameter A (frozenMarkedPhysicalExponent (s + 1))
          (allocatedRightDictionaryExponent (s + 1)) p := by
    unfold candidateCoveredDictionaryParameter
    exact pow_le_pow_left₀
      (by positivity : 0 ≤
        (pOuter + frozenMarkedPhysicalExponent (s + 1)) ^ frozenMarkedPhysicalExponent (s + 1) +
          (allocatedRightDictionaryExponent (s + 1) : ℝ))
      (by linarith)
      (allocatedRightDictionaryExponent (s + 1))
  exact {
    input_budget := houterBudget
    geometry_one := hgeometry.1
    input_geometry := hpGeo
    outer_geometry := hpOuterBound.trans hgeometry.2.2.1
    outer_budget := hpOuterBound.trans houterBudget
    physical_geometry := hphysical.trans hRightGeo
    right_geometry := hright.trans hDictGeo
    geometry_budget := hgeoBudget
    covered_budget := hcoverBudget
    geometry_recursive := hGeoRec
    covered_recursive := hCoverRec }

noncomputable def candidateGeneratedPhysicalBudgetExponent (s A : ℕ) : ℕ :=
  Classical.choose (exists_generatedPhysicalSuccessorScalarBounds s A)

theorem candidateGeneratedPhysicalBudgetExponent_ge_two (s A : ℕ) :
    2 ≤ candidateGeneratedPhysicalBudgetExponent s A :=
  (Classical.choose_spec (exists_generatedPhysicalSuccessorScalarBounds s A)).1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open RationalFilteredNilmanifold

noncomputable def candidatePrimitivePhysicalBudgetExponent (s a : ℕ) : ℕ :=
  candidateGeneratedPhysicalBudgetExponent s (candidateFreezingOuterExponent s a)

noncomputable def candidatePrimitivePhysicalGeometryParameter (s a : ℕ) (p : ℝ) : ℝ :=
  candidateGeneratedPhysicalGeometryParameter s (candidateFreezingOuterExponent s a) p

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateObservableRestriction
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

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

noncomputable def restrictObservable
    (newObservable : (X → ℤ) → D.Space → ℂ)
    (retained : Finset A.Path) (hsub : retained ⊆ P.productive)
    {newMass newScore : ℝ} (hmass : newMass ≤ A.law.mass retained)
    (hscore : ∀ z : retained,
      newScore ≤ (P.candidate ⟨z.val,hsub z.property⟩).score newObservable weight) :
    AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked newObservable weight
      cost newMass newScore where
  productive := retained
  mass := hmass
  chart z := P.chart ⟨z.val,hsub z.property⟩
  chart_path z := P.chart_path ⟨z.val,hsub z.property⟩
  centerLift := P.centerLift
  chart_centerLift z := P.chart_centerLift ⟨z.val,hsub z.property⟩
  frozen_side z := P.frozen_side ⟨z.val,hsub z.property⟩
  candidate z := P.candidate ⟨z.val,hsub z.property⟩
  score := hscore

@[simp] theorem restrictObservable_physicalIntegerPoint
    (newObservable : (X → ℤ) → D.Space → ℂ)
    (retained : Finset A.Path) (hsub : retained ⊆ P.productive)
    {newMass newScore : ℝ} (hmass : newMass ≤ A.law.mass retained)
    (hscore : ∀ z : retained,
      newScore ≤ (P.candidate ⟨z.val,hsub z.property⟩).score newObservable weight) :
    (P.restrictObservable newObservable retained hsub hmass hscore).physicalIntegerPoint =
      P.physicalIntegerPoint := rfl

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchTaggedBufferedScore
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open VectorPolynomial

variable {X : Type*} {m n : ℕ} {J : Fin m → Type*}

theorem taggedShearOrbitReindexChart_degree (e : Fin n ≃ Sigma J)
    (v : X ⊕ Sigma J) :
    taggedShearOrbitReindexChart e v ∈
      weightedSupportLE (Sum.elim (fun _ : X => 1) (fun i => (e i).1.val + 1))
        (fullTaggedVariableWeight J v) := by
  have h := weightedSupportLE_X (R := ℝ)
    (Sum.elim (fun _ : X => 1) (fun i => (e i).1.val + 1)) (Sum.map id e.symm v)
  cases v with
  | inl x => exact h
  | inr a => simpa only [taggedShearOrbitReindexChart, Sum.map_inr, Sum.elim_inr,
      Equiv.apply_symm_apply] using h

end Erdos3

end

end OAI
end


