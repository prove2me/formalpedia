-- Prove2me | Definitions.Def_OAIE3v2B302
-- name    : OAIE3v2B302
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:43:58.398016+00:00
-- url     : https://prove2.me/theorems/43a9c5bb-c05b-4e64-8a80-2b6936ce2f84
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 258 of 311
-- statement:
--   Definitions bundle 258 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B252` of this split.
--
--   Modules: `Dynamics/AllocatedExternalCandidatePrimitivePhysicalBudget.lean`, `Estimates/AllocatedExternalCandidateAxisFreezingConclusion.lean`, `Estimates/AllocatedExternalCandidateKeptSymbolFactors.lean`, `Estimates/AllocatedExternalCandidateRefinementLabels.lean`, `Estimates/AllocatedExternalCandidateTaggedPairFamily.lean`, `Estimates/AllocatedExternalCandidateThresholdSuccessor.lean`, `Estimates/AllocatedExternalLocalFiniteFreezing.lean`, `Estimates/AllocatedExternalLocalGlobalMarkedCandidate.lean`, `Geometry/ActualFixedSpatialRetainedPatchEndpoint.lean`, `Geometry/AllocatedExternalLocalChartKeepBounds.lean`, `Linear/ActualCandidateSlowProjectionMass.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B252

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalLocalFiniteFreezing
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

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : F.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (candidate : AllocatedExternalLocalCandidate C D F φ marked)

variable (sectionMap : M →ₗ[ℚ] L)
    (hsectionLayer : ∀ j, ∀ y ∈ F.layer j, sectionMap y ∈ D.filtration.layer j)
    (EF RF : (F.realification.adaptedPolynomialFiltration (fun _ : C.Variables => 1)).Group)
    (middle : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : C.Variables => 1)).Group)

noncomputable def freezingFrozenValue
    (tests : (X → ℤ) → D.Niltest (fun _ : C.Variables => 1))
    (left right : D.RealGroup) (u : C.Variables → ℤ) : ℂ :=
  (tests (C.physical u)).markedFrozenValue F (fun _ : C.Variables => 1)
    sectionMap hsectionLayer EF RF middle left right u

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateRefinementLabels
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

theorem exists_common_label {Label : Type*} [Fintype Label] [Nonempty Label]
    (label : refinement.retained → Label) :
    ∃ chosen : Label, ∃ paths : Finset A.Path, ∃ hpaths : paths ⊆ refinement.retained,
      ∃ hmass : newMass / (Fintype.card Label : ℝ) ≤ A.law.mass paths,
        ∀ z : (refinement.restrictPaths paths hpaths hmass).retained,
          label ⟨z.val, hpaths z.property⟩ = chosen := by
  classical
  let code (z : A.Path) : Label :=
    if hz : z ∈ refinement.retained then label ⟨z, hz⟩ else Classical.choice inferInstance
  obtain ⟨chosen, hchosen⟩ := A.law.exists_code_fiber_mass refinement.retained code
  let paths := refinement.retained.filter (fun z => code z = chosen)
  have hpaths : paths ⊆ refinement.retained := Finset.filter_subset _ _
  have hmass : newMass / (Fintype.card Label : ℝ) ≤ A.law.mass paths :=
    (div_le_div_of_nonneg_right refinement.mass (Nat.cast_nonneg _)).trans hchosen
  refine ⟨chosen, paths, hpaths, hmass, ?_⟩
  intro z
  have he := (Finset.mem_filter.mp z.property).2
  simpa only [code, dif_pos (hpaths z.property)] using he

end Refinement
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalLocalChartKeepBounds
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
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)

noncomputable def conclusion_of_withKeep {outputCost outputMass outputScore : ℝ}
    (result : (P.withKeep keep hkeep).Conclusion outputCost outputMass outputScore) :
    P.Conclusion outputCost outputMass outputScore := by
  have hex (z : result.retained) :
      ∃ slice : ResidueBoxSlice
          (fun i : (P.chart ⟨z.val, result.subset z.property⟩).Variables => A.sides i.val)
          (result.step z),
        IsDenseCommonStrideBox
          (fun i : (P.chart ⟨z.val, result.subset z.property⟩).Variables => A.sides i.val)
          outputCost slice.integerPoints ∧
        slice.integerPoints ⊆ (P.chart ⟨z.val, result.subset z.property⟩).slice.integerPoints ∧
        outputScore ≤ P.ambientScore result.ambient ⟨z.val, result.subset z.property⟩
          slice.integerPoints := by
    exact (P.chart ⟨z.val, result.subset z.property⟩).withKeep_slice_transport
      keep (hkeep _) (result.slice z) (result.dense z) (result.inside z)
      (fun x y => weight x * observable x (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          y result.ambient))) (result.score z)
  choose slice hdense hinside hscore using hex
  exact
    { ambient := result.ambient
      marked := result.marked
      retained := result.retained
      subset := result.subset
      mass := result.mass
      step := result.step
      step_pos := result.step_pos
      slice := slice
      dense := hdense
      inside := hinside
      score := hscore }

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct
attribute [local irreducible] weightedAdaptedRealChartHom

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

theorem withKeep_chart_fixed
    (β : X ⊕ (Σ j, J j) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ)
    (hfixed : ∀ x : C.Variables → ℝ,
      (fun v => MvPolynomial.eval
        (fun i => MvPolynomial.eval x (integerSampledRealChart C.integerChart i)) (β v)) =
      (fun i => MvPolynomial.eval x (integerSampledRealChart C.integerChart i))) :
    ∀ x : (C.withKeep keep hkeep).Variables → ℝ,
      (fun v => MvPolynomial.eval
        (fun i => MvPolynomial.eval x
          (integerSampledRealChart (C.withKeep keep hkeep).integerChart i)) (β v)) =
      (fun i => MvPolynomial.eval x
        (integerSampledRealChart (C.withKeep keep hkeep).integerChart i)) := by
  cases hkeep
  exact hfixed

theorem withKeep_polynomialSlowBound
    {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (basis : Basis κ ℚ L)
    (g : (F.realification.adaptedPolynomialFiltration (fullTaggedVariableWeight (X := X) J)).Group)
    (M : ℝ)
    (hslow : F.PolynomialSlowBound basis (fun _ : C.Variables => 1)
      (fun i : C.Variables => (A.sides i.val : ℝ)) M
      (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart)
        C.integerChart_support g)) :
    F.PolynomialSlowBound basis (fun _ : (C.withKeep keep hkeep).Variables => 1)
      (fun i : (C.withKeep keep hkeep).Variables => (A.sides i.val : ℝ)) M
      (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : (C.withKeep keep hkeep).Variables => 1)
        (integerSampledRealChart (C.withKeep keep hkeep).integerChart)
        (C.withKeep keep hkeep).integerChart_support g) := by
  cases hkeep
  exact hslow

theorem withKeep_dense (dCost : ℝ)
    (hdense : IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
      dCost C.slice.integerPoints) :
    IsDenseCommonStrideBox (fun i : (C.withKeep keep hkeep).Variables => A.sides i.val)
      dCost (C.withKeep keep hkeep).slice.integerPoints := by
  cases hkeep
  exact hdense

theorem withKeep_original_dense :
    IsDenseCommonStrideBox (fun i : (C.withKeep keep hkeep).Variables => A.sides i.val)
      cost (C.withKeep keep hkeep).slice.integerPoints :=
  C.withKeep_dense keep hkeep cost C.dense

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairFamily
namespace OAI

universe u

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

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

variable (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hσ1 H hH hchart hsmall hp

theorem chartValues_eq_physicalIntegerPoint_on_slice (u : C.Variables → ℤ)
    (hu : u ∈ C.slice.integerPoints) :
    C.chartValues u = fullTaggedPhysicalIntegerPoint J poly
      (fun j => (C.centerLift j).val) (C.physical u) :=
  C.chartValues_eq_physicalIntegerPoint hσ1 H hH hchart hsmall hp u
    (C.slice.integerPoints_subset_integerBox hu)

theorem chartValues_eq_physicalIntegerPoint_of_center
    (c : ∀ j, U j) (hc : C.centerLift = c) (u : C.Variables → ℤ)
    (hu : u ∈ C.slice.integerPoints) :
    C.chartValues u = fullTaggedPhysicalIntegerPoint J poly
      (fun j => (c j).val) (C.physical u) := by
  rw [← hc]
  exact C.chartValues_eq_physicalIntegerPoint_on_slice hσ1 H hH hchart hsmall hp u hu

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

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

namespace AllocatedExternalCandidateTaggedPairFamily

variable {A} {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
    {s d₀ t : ℕ} {d : Pivot → ℕ}
    {D : RationalFilteredNilmanifold LG s d₀}
    {E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j)}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck Ω Pivot D E Fmark φ marked
      keep cost p periodCap coverCap Lip)

def jointOrbit (a : Ω) : ∀ i : Option Pivot,
    (optionFactors D E i).filtration.realification.PolynomialOrbit
      (fun _ : {i // keep i} => 1)
  | none => (F.candidate a).orbit
  | some j => ((F.ambient j).integerChartPullback (fun _ : {i // keep i} => 1)
      (F.chart a).integerChart (F.chart a).integerChart_support).orbit

end AllocatedExternalCandidateTaggedPairFamily

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalLocalGlobalMarkedCandidate
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
    {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

namespace AllocatedExternalLocalCandidate

variable {L M κ : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f nD nF : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    {c : Basis κ ℚ M} {ν : κ → ℕ}
    {hF : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})}
    {g : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors Fmark.filtration c ν hF (fullTaggedVariableWeight J)
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) g EF RF)
    (nativeMiddle : (D.filtration.realification.adaptedPolynomialFiltration
      (fun _ : C.Variables => 1)).Group)
    (native : (D.filtration.gradedRefiltration W).realification.PolynomialOrbit
      (fun _ : C.Variables => 1))
    (hprojection : D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ => 1) nativeMiddle =
      Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart)
        C.integerChart_support factors.middle)
    (hlog : map
      (realLieHomToRat (realificationLieHom
        (D.filtration.gradedRefiltrationSubalgebra W).incl)).toLinearMap native.log =
      (nativeMiddle.coord : VectorPolynomial C.Variables ℚ (ℝ ⊗[ℚ] L)))

noncomputable def ofGlobalMarkedNativeMiddle :
    AllocatedExternalLocalCandidate C Dref Fref.filtration
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      (factors.markedMiddleOn Fref hFref) :=
  ofNativeRefilteredMiddle C D Fmark φ hφ W Dref Fref
    (factors.markedMiddleOn Fref hFref)
    ((D.filtration.gradedRefiltration W).realPolynomialOrbitChangeFiltration
      Dref.filtration hDref (fun _ : C.Variables => 1) native)
    nativeMiddle _ hprojection
    (by
      intro u _
      rw [← polynomialOrbitRealEval_integer]
      apply NilpotentLieBCHGroup.ext
      exact congrArg NilpotentLieBCHGroup.coord
        (D.filtration.native_refiltered_orbit_real_value W
          (fun _ : C.Variables => 1) native _ hlog (fun i => (u i : ℝ))))
    (by
      intro u _
      exact C.globalMarked_middle_values factors Fref hFref u)

@[simp] theorem ofGlobalMarkedNativeMiddle_orbit_log :
    (ofGlobalMarkedNativeMiddle C D Fmark φ hφ W Dref hDref Fref hFref
      factors nativeMiddle native hprojection hlog).orbit.log = native.log := rfl

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialRetainedPatchEndpoint
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def bufferedSpatialWeight {Ω Θ : Type*} {m : ℕ}
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ) (T : Ω → (Fin m → ℤ) → ℝ)
    (G : Θ → Ω → (Fin m → ℤ) → ℝ) (z : Θ) (u : Ω) : ℝ :=
  ∑' b, χ.value (fun i => x u i - (b i : ℝ)) * G z u b * T u b

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidatePrimitivePhysicalBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open RationalFilteredNilmanifold

noncomputable def candidateFreezingOuterExponent (s a : ℕ) : ℕ :=
  Classical.choose (exists_nativeMarkedFreezingPhysicalParameter_bound
    (nativeMarkedFreezingExponent (s + 1) a))

noncomputable def candidatePrimitivePhysicalOuterParameter (s a : ℕ) (p : ℝ) : ℝ :=
  nativeMarkedFreezingPhysicalParameter p (nativeMarkedFreezingExponent (s + 1) a)

theorem candidatePrimitivePhysicalOuterParameter_bound (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    candidatePrimitivePhysicalOuterParameter s a p ≤
      (p + candidateFreezingOuterExponent s a) ^ candidateFreezingOuterExponent s a :=
  (Classical.choose_spec (exists_nativeMarkedFreezingPhysicalParameter_bound
    (nativeMarkedFreezingExponent (s + 1) a))).2 p hp

theorem candidatePrimitivePhysicalOuterParameter_nonneg (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ candidatePrimitivePhysicalOuterParameter s a p :=
  hp.trans (nativeMarkedFreezingPhysicalParameter_bounds hp
    (nativeMarkedFreezingExponent (s + 1) a)).1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAxisFreezingConclusion
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

variable {cost shortCost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)

variable (fixed : {i : C.Variables // ¬keep i.val} → ℤ)

noncomputable def axisPoint (u : {i // keep i} → ℤ) : C.Variables → ℤ :=
  fun i => if hi : keep i.val then u ⟨i.val, hi⟩ else fixed ⟨i, hi⟩

end AllocatedExternalLocalChart

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateKeptSymbolFactors
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

attribute [local irreducible] realChartSubstitute

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
    {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)

theorem mark_log_on_slice (u : C.Variables → ℤ) (hu : u ∈ C.slice.integerPoints) :
    eval₂ (fun i => (u i : ℝ))
      (map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) candidate.orbit.log) =
    eval₂ (fun i => (u i : ℝ))
      (realChartSubstitute (integerSampledRealChart C.integerChart) marked.log) := by
  have he := candidate.mark_on_slice u hu
  rw [← D.filtration.realification.polynomialOrbitRealEval_integer _ candidate.orbit u,
    ← Fmark.realification.polynomialOrbitRealEval_integer _ marked (C.chartValues u)] at he
  have hc := congrArg NilpotentLieBCHGroup.coord he
  rw [eval₂_map, eval₂_realChartSubstitute]
  refine hc.trans ?_
  apply congrArg (fun z => eval₂ z marked.log)
  funext i
  exact (integerSampledRealChart_eval C.integerChart u i).symm

theorem chart_mark_degreeLE :
    DegreeLE (fun _ : C.Variables => 1) t
      (realChartSubstitute (integerSampledRealChart C.integerChart) marked.log) :=
  Fmark.realification.adapted_degreeLE _
    (Fmark.adapted_realChartSubstitute_weightedSupport
      (fullTaggedVariableWeight J) (fun _ : C.Variables => 1)
      (integerSampledRealChart C.integerChart) C.integerChart_support marked.adapted)

theorem formal_mark (hlength : ∀ i, max s t < C.slice.length i) :
    map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) candidate.orbit.log =
      realChartSubstitute (integerSampledRealChart C.integerChart) marked.log := by
  refine eq_of_eval₂_eq_on_residueBoxSlice C.slice C.step_pos ?_ ?_ hlength ?_
  · intro α hα
    exact (candidate.orbit.degreeLE.map _ ) α ((le_max_left s t).trans_lt hα)
  · intro α hα
    exact chart_mark_degreeLE α ((le_max_right s t).trans_lt hα)
  · intro j
    exact candidate.mark_log_on_slice _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

theorem formal_mark_group
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (hlength : ∀ i, max s t < C.slice.length i) :
    D.filtration.realPolynomialGroupMap Fmark φ hφ (fun _ : C.Variables => 1)
      (D.filtration.realification.polynomialOrbitCoordinates _ candidate.orbit) =
    Fmark.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
      (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart) C.integerChart_support
      (Fmark.realification.polynomialOrbitCoordinates _ marked) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact candidate.formal_mark hlength

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

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
    {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalChart

theorem degree_lt_slice_length_of_dense (r : ℕ) {sliceCost : ℝ}
    (hdense : IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
      sliceCost C.slice.integerPoints)
    (hlong : ∀ i : C.Variables,
      Real.exp (sliceCost + (r : ℝ) + 1) ≤ (A.sides i.val : ℝ)) :
    ∀ i, r < C.slice.length i := by
  intro i
  have hlength := C.slice.length_lower_of_dense C.step_pos hdense i
  have hlower : Real.exp ((r : ℝ) + 1) ≤ (C.slice.length i : ℝ) := by
    calc
      _ = Real.exp (-sliceCost) * Real.exp (sliceCost + (r : ℝ) + 1) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-sliceCost) * (A.sides i.val : ℝ) :=
        mul_le_mul_of_nonneg_left (hlong i) (Real.exp_nonneg _)
      _ ≤ _ := hlength
  have hstrict : (r : ℝ) < (C.slice.length i : ℝ) := by
    linarith [Real.add_one_le_exp ((r : ℝ) + 1)]
  exact_mod_cast hstrict

end AllocatedExternalLocalChart

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

theorem adaptedChart_eq_of_chart_eq
    {V K L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : V → ℕ) (v : K → ℕ)
    (β γ : V → MvPolynomial K ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i))
    (heq : β = γ) (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.weightedAdaptedRealChartHom w v β hβ g = F.weightedAdaptedRealChartHom w v γ hγ g := by
  cases heq
  rfl

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
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)

theorem withKeep_chart_integerChart (z : P.productive) :
    ((P.withKeep keep hkeep).chart z).integerChart =
      allocatedFrozenIntegerFullChart B U b o poly hm P.centerLift
        z.val.1.val z.val.2.val (P.chart z).sample keep
        ((P.withKeep keep hkeep).chart z).fixed := by
  change allocatedFrozenIntegerFullChart B U b o poly hm (P.chart z).centerLift
      (P.chart z).path.1.val (P.chart z).path.2.val (P.chart z).sample keep
      ((P.withKeep keep hkeep).chart z).fixed = _
  rw [P.chart_centerLift z, P.chart_path z]

end AllocatedExternalCandidateProblem
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

noncomputable def candidatePrimitiveFreezingCutoff (s a : ℕ) (p : ℝ) : ℝ :=
  p + 2 * (p + nativeMarkedFreezingExponent (s + 1) a) ^
    nativeMarkedFreezingExponent (s + 1) a + 2

theorem candidatePrimitiveFreezingCutoff_ge_input (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ candidatePrimitiveFreezingCutoff s a p := by
  unfold candidatePrimitiveFreezingCutoff
  have : 0 ≤ (p + nativeMarkedFreezingExponent (s + 1) a) ^
      nativeMarkedFreezingExponent (s + 1) a := by positivity
  linarith

theorem candidatePrimitiveFreezingCutoff_floor (s a : ℕ) {p densityCost side : ℝ}
    (hp : 0 ≤ p) (hdensity : densityCost ≤ p)
    (hside : Real.exp (candidatePrimitiveFreezingCutoff s a p) ≤ side) :
    Real.exp densityCost * max 2
      (2 * Real.exp ((p + nativeMarkedFreezingExponent (s + 1) a) ^
          nativeMarkedFreezingExponent (s + 1) a) *
        max 1 (Real.exp ((p + nativeMarkedFreezingExponent (s + 1) a) ^
          nativeMarkedFreezingExponent (s + 1) a))) ≤ side := by
  apply (finiteFreezing_floor_le_exp (by positivity)).trans
  apply le_trans (Real.exp_le_exp.mpr ?_) hside
  unfold candidatePrimitiveFreezingCutoff
  linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open NilpotentLieFiltration RationalFilteredNilmanifold

theorem candidatePrimitiveFreezingCutoff_integer_cost (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    candidateSideCutoffCost (Real.exp (candidatePrimitiveFreezingCutoff s a p)) ≤
      candidatePrimitiveFreezingCutoff s a p + 2 :=
  candidateSideCutoffCost_exp_bound
    (hp.trans (candidatePrimitiveFreezingCutoff_ge_input s a hp))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualCandidateSlowProjectionMass
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem fullTaggedRealMatrixProjection_rowSum_le
    (P : ∀ j, Matrix (J j) (J j) ℚ) {B : ℝ}
    (hP : ∀ j i a, rationalLogHeight (P j i a) ≤ B) (j : Fin m) (i : J j) :
    (∑ a : J j, |fullTaggedRealMatrixProjection J P j (Pi.single a 1) i|) ≤
      (Fintype.card (J j) : ℝ) * Real.exp B := by
  calc
    _ ≤ ∑ _a : J j, Real.exp B := by
      apply Finset.sum_le_sum
      intro a _
      rw [fullTaggedRealMatrixProjection_single]
      exact (rational_abs_real_le_numerator (P j i a)).trans
        ((rationalLogHeight_le_iff _ _).mp (hP j i a)).1
    _ = _ := by simp

theorem fullTaggedRealMatrixProjection_slow_mass_row_le
    (P : ∀ j, Matrix (J j) (J j) ℚ) {B d : ℝ}
    (hP : ∀ j i a, rationalLogHeight (P j i a) ≤ B)
    (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ d) (nVars : ℕ)
    (j : Fin m) (i : J j) :
    (∑ a : J j, |fullTaggedRealMatrixProjection J P j (Pi.single a 1) i|) *
      (((m + 1 : ℕ) : ℝ) * ((nVars + 1 : ℕ) : ℝ) ^ m) ≤
      d * Real.exp B * (((m + 1 : ℕ) : ℝ) * ((nVars + 1 : ℕ) : ℝ) ^ m) := by
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact (fullTaggedRealMatrixProjection_rowSum_le J P hP j i).trans
    (mul_le_mul_of_nonneg_right (hdim j) (Real.exp_nonneg B))

end Erdos3.VectorPolynomial

end

end OAI
end


