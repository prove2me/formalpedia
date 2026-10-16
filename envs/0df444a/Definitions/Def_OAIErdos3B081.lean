-- Prove2me | Definitions.Def_OAIErdos3B081
-- name    : OAIErdos3B081
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T01:46:33.347985+00:00
-- url     : https://prove2.me/theorems/14d7adca-40f4-466d-911f-4d49f00168b7
-- title:
--   OpenAI Erdős-3 split, definitions bundle 82 of 1379
-- statement:
--   Definitions bundle 82 of 1379 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B080`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 82 available.
--
--   Modules: `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.fullTaggedSpatial`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.fullTaggedSpatial_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.fullTaggedSpatial_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.fullTaggedSpatial_eval_physical`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.fullTaggedSpatial_normBound`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.residualPacket`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.residualPacket_retained`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.residualPacket_weight`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.retainedResidualPacket`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.retainedResidualPacket_weight`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.boxedPhysical`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.boxedPhysical_val`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.candidate`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.chart`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.chart_localLaw`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.correlation`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.exists_taggedPairFamily`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.exp_correlation_bound`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.extend`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.extend_correlation`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.extend_jointOrbit`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.extend_native`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.extend_nativeValue`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.extend_sourceCandidate`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.extend_sourceChart`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.extend_η`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.jointOrbit`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.localTest`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.physicalBox`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.physicalBox_val`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.positiveMassRetract`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.positiveMassRetract_mem`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.rawCorrelation_fullSliceLaw`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.rec`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.reindex`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.reindex_correlation`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.reindex_jointOrbit`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.reindex_native`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.reindex_nativeValue`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.reindex_sourceCandidate`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.reindex_sourceChart`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.reindex_η`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.selectedCorrelation_localLaw`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.sitePhysicalBox`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.withBudget`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.withBudget_candidate`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.withBudget_chart`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.withBudget_correlation`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.withBudget_eta`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.withBudget_jointOrbit`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.withBudget_native`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.withBudget_nativeValue`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.withBudget_reference`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.withBudget_sourceCandidate`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.withBudget_sourceChart`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.withBudget_twist`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.withFactorBudget`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.withFactorBudget_correlation`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.withFactorBudget_eta`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.withFactorBudget_native`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.withFactorBudget_sourceCandidate`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.withFactorBudget_sourceChart`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSpatialNativeFamily.withFactorBudget_twist`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.admissibleFullPacket`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.admissibleFullPacket_expect`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.admissibleFullPacket_site_expect`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.candidateVariableDecidableEq`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.localLaw_residual_le_exp_of_uniform`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.localLaw_residual_le_exp_of_uniform_budget`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.localLaw_residual_le_exp_of_universal_native_budget`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.localLaw_residual_le_of_uniform`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.normalizedSlicePacket`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.normalizedSlicePacket_weight`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.sliceTest`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.sliceTest_complexity`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.sliceTest_eval`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.sliceTest_eval_on_slice`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.sliceTest_lipBound`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.sliceTest_normBound`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.sliceTest_observable`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.fixedNatural`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.fixedNatural_lt`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.frozenLongExtension_fixedNatural`, `OAI.Erdos3.VectorPolynomial.fullTaggedSpatialIntegerChart`, `OAI.Erdos3.VectorPolynomial.fullTaggedSpatialIntegerChart_support`, `OAI.Erdos3.VectorPolynomial.spatialNativeFactorParameter`, `OAI.Erdos3.VectorPolynomial.spatialNativeVerticalParameter`, `OAI.Erdos3.exists_spatialNative_slice_tagged_vertical_partners`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1344
import Definitions.Def_OAIErdos3B1351

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidatePrecenterNativePartners
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

def boxedPhysical (hξ1 : ξ ≤ 1) (z : A.Path) (site : A.Site) : integerBox N :=
  ⟨A.physical z site, A.physical_mem_integerBox hξ1 z site⟩

@[simp] theorem boxedPhysical_val (hξ1 : ξ ≤ 1) (z : A.Path) (site : A.Site) :
    (A.boxedPhysical hξ1 z site).val = A.physical z site := rfl

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {Ω Freq Bin : Type*} [Fintype Ω] [Fintype Bin] [Nonempty Bin]
    {LG LM : Type*} [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d t rank : ℕ} (D : RationalFilteredNilmanifold LG s d)
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {cost : ℝ} (C : Ω → AllocatedExternalLocalChart (E := Deck) A cost)
    (candidate : ∀ a, AllocatedExternalLocalCandidate (C a) D Fmark φ marked)
    (hξ1 : ξ ≤ 1)

end AllocatedExternalCandidateSampler

end

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalRetainedResidual
namespace OAI

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

namespace AllocatedExternalLocalCandidate

variable {A} {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M V : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    {w : V → ℕ} (reference : D.Niltest w)

noncomputable def sliceTest : D.Niltest (fun _ : C.Variables => 1) :=
  (reference.withOrbit candidate.orbit).scalarAffinePullback
    (C.step : ℚ) (fun i => (C.slice.start i : ℚ))

@[simp] theorem sliceTest_normBound :
    (candidate.sliceTest reference).normBound = reference.normBound := rfl

@[simp] theorem sliceTest_lipBound :
    (candidate.sliceTest reference).lipBound = reference.lipBound := rfl

@[simp] theorem sliceTest_observable :
    (candidate.sliceTest reference).observable = reference.observable := rfl

@[simp] theorem sliceTest_complexity (p : ℝ) :
    (candidate.sliceTest reference).ComplexityLE p ↔ reference.ComplexityLE p := Iff.rfl

theorem sliceTest_eval (j : C.Variables → ℤ) :
    (candidate.sliceTest reference).eval j =
      reference.observable (candidate.value
        (commonStridePoint (fun i => (C.slice.start i : ℤ)) C.step j)) := by
  have h := (reference.withOrbit candidate.orbit).scalarAffinePullback_eval_integer
    (C.step : ℤ) (fun i => (C.slice.start i : ℤ)) j
  have hpoint : (fun i => (C.step : ℤ) * j i + (C.slice.start i : ℤ)) =
      commonStridePoint (fun i => (C.slice.start i : ℤ)) C.step j := by
    funext i
    exact add_comm _ _
  rw [hpoint] at h
  simpa only [sliceTest, Int.cast_natCast, RationalFilteredNilmanifold.Niltest.withOrbit_eval,
    value] using h

theorem sliceTest_eval_on_slice (u : C.Variables → ℤ) (hu : u ∈ C.slice.integerPoints) :
    (candidate.sliceTest reference).eval
      (commonStrideIndex (fun i => (C.slice.start i : ℤ)) C.step u) =
      reference.observable (candidate.value u) := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
  rw [C.slice_index, candidate.sliceTest_eval, ← C.slice.integerPoint_eq]

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable section

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

namespace AllocatedExternalLocalCandidate

variable {A} {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M V : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    {w : V → ℕ} (reference : D.Niltest w)

local instance candidateVariableDecidableEq : DecidableEq C.Variables := Subtype.instDecidableEq

noncomputable def normalizedSlicePacket {p : ℝ} (hreference : reference.ComplexityLE p) :
    LocalMajorSliceTest D (fun i : C.Variables => A.sides i.val) cost p where
  stride := C.step
  stride_pos := C.step_pos
  slice := C.slice
  dense := by
    have he : candidateVariableDecidableEq (C := C) = Classical.decEq C.Variables :=
      Subsingleton.elim _ _
    rw [he]
    exact C.dense
  test := (candidate.sliceTest reference).conjugate.expNormalize p
  norm := by
    exact_mod_cast ((candidate.sliceTest reference).conjugate.expNormalize_norm hreference)
  complexity := (candidate.sliceTest reference).conjugate.expNormalize_complexity hreference

theorem normalizedSlicePacket_weight {p : ℝ} (hreference : reference.ComplexityLE p)
    (u : C.Variables → ℤ) (hu : u ∈ C.slice.integerPoints) :
    (candidate.normalizedSlicePacket reference hreference).weight u =
      (Real.exp (-p) : ℂ) * reference.observable (candidate.value u) := by
  have he : candidateVariableDecidableEq (C := C) = Classical.decEq C.Variables :=
    Subsingleton.elim _ _
  have hu' : u ∈ @ResidueBoxSlice.integerPoints C.Variables _ _ _ (Classical.decEq _) C.slice := by
    rw [← he]
    exact hu
  change star (((candidate.sliceTest reference).conjugate.expNormalize p).eval
    (commonStrideIndex (fun i => (C.slice.start i : ℤ)) C.step u)) = _
  rw [RationalFilteredNilmanifold.Niltest.expNormalize_eval,
    RationalFilteredNilmanifold.Niltest.eval_conjugate,
    candidate.sliceTest_eval_on_slice reference u hu', star_mul, star_star]
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

end AllocatedExternalLocalCandidate

namespace AllocatedExternalLocalChart
variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

noncomputable def fixedNatural (i : LayerSamplerVariables G I n B) : ℕ :=
  if hi : C.keep i then 0 else (C.fixed ⟨i, hi⟩).toNat

theorem fixedNatural_lt (i : LayerSamplerVariables G I n B) (hi : ¬C.keep i) :
    C.fixedNatural i < A.sides i := by
  simp only [fixedNatural, dif_neg hi]
  have h := C.fixed_in_box ⟨i, hi⟩
  have he : ((C.fixed ⟨i, hi⟩).toNat : ℤ) = C.fixed ⟨i, hi⟩ :=
    Int.toNat_of_nonneg h.1
  exact_mod_cast (show ((C.fixed ⟨i, hi⟩).toNat : ℤ) < (A.sides i : ℤ) by
    rw [he]
    exact h.2)

theorem frozenLongExtension_fixedNatural (u : C.Variables → ℤ) :
    frozenLongExtension C.keep C.fixedNatural u = C.parameter u := by
  funext i
  by_cases hi : C.keep i
  · simp only [frozenLongExtension, AllocatedExternalLocalChart.parameter,
      finiteSplitPoint, dif_pos hi]
  · simp only [frozenLongExtension, AllocatedExternalLocalChart.parameter,
      finiteSplitPoint, fixedNatural, dif_neg hi]
    exact Int.toNat_of_nonneg (C.fixed_in_box ⟨i, hi⟩).1

end AllocatedExternalLocalChart

namespace AllocatedExternalLocalCandidate

variable {A} {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M V : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    {w : V → ℕ} (reference : D.Niltest w)

attribute [local instance] candidateVariableDecidableEq

noncomputable def admissibleFullPacket {p : ℝ} (hreference : reference.ComplexityLE p)
    (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost) :
    LocalMajorSliceTest D A.sides cost p where
  stride := C.step
  stride_pos := C.step_pos
  slice := C.slice.freezeShort C.keep C.fixedNatural C.fixedNatural_lt
  dense := by
    have h := (candidate.normalizedSlicePacket reference hreference).slice.freezeShort_dense
      C.keep C.fixedNatural C.fixedNatural_lt C.step_pos
      (candidate.normalizedSlicePacket reference hreference).dense
      (Real.one_le_exp hcost) (fun i hi => hshort ⟨i, hi⟩)
    simpa only [Real.log_exp, max_self, normalizedSlicePacket] using h
  test := (candidate.normalizedSlicePacket reference hreference).test.liftLong C.keep
  norm := (candidate.normalizedSlicePacket reference hreference).norm
  complexity := (candidate.normalizedSlicePacket reference hreference).complexity

theorem admissibleFullPacket_expect {p : ℝ} (hreference : reference.ComplexityLE p)
    (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (signal : (LayerSamplerVariables G I n B → ℤ) → ℂ) :
    (𝔼 site ∈ (candidate.admissibleFullPacket reference hreference hcost hshort).slice.subtypeSites,
      signal site.val * (candidate.admissibleFullPacket reference hreference hcost hshort).weight site.val) =
      (Real.exp (-p) : ℂ) * C.localLaw.complexMean
        (fun site => signal site.val * reference.observable (candidate.siteValue site)) := by
  let short := candidate.normalizedSlicePacket reference hreference
  let full := short.freezeShort C.keep C.fixedNatural C.fixedNatural_lt
    (Real.one_le_exp hcost) (fun i hi => hshort ⟨i, hi⟩)
  have hmean := short.expect_freezeShort C.keep C.fixedNatural C.fixedNatural_lt
    (Real.one_le_exp hcost) (fun i hi => hshort ⟨i, hi⟩) signal
  have hleft :
      (𝔼 site ∈ (candidate.admissibleFullPacket reference hreference hcost hshort).slice.subtypeSites,
        signal site.val * (candidate.admissibleFullPacket reference hreference hcost hshort).weight site.val) =
      𝔼 u ∈ C.slice.integerPoints,
        signal (C.parameter u) * short.weight u := by
    rw [(candidate.admissibleFullPacket reference hreference hcost hshort).slice.expect_subtypeSites
      (fun x => signal x * (candidate.admissibleFullPacket reference hreference hcost hshort).weight x)]
    simpa only [admissibleFullPacket, full, short, Real.log_exp, max_self,
      C.frozenLongExtension_fixedNatural, normalizedSlicePacket,
      LocalMajorSliceTest.freezeShort, LocalMajorSliceTest.weight] using hmean
  rw [hleft]
  change _ = (Real.exp (-p) : ℂ) * C.localLaw.complexMean
    (fun site => signal site.val * reference.observable (candidate.value (C.retainedParameter site.val)))
  rw [C.localLaw_complexMean_parameter
    (fun x => signal x * reference.observable (candidate.value (C.retainedParameter x)))]
  rw [Finset.mul_expect]
  have he : candidateVariableDecidableEq (C := C) = Classical.decEq C.Variables :=
    Subsingleton.elim _ _
  have hpoints := congrArg
    (fun dec : DecidableEq C.Variables =>
      @ResidueBoxSlice.integerPoints C.Variables _ _ _ dec C.slice) he
  rw [hpoints]
  apply Finset.expect_congr rfl
  intro u hu
  have hu' : u ∈ C.slice.integerPoints := by
    rw [hpoints]
    exact hu
  rw [candidate.normalizedSlicePacket_weight reference hreference u hu']
  change signal (C.parameter u) * ((Real.exp (-p) : ℂ) * reference.observable (candidate.value u)) =
    (Real.exp (-p) : ℂ) * (signal (C.parameter u) *
      reference.observable (candidate.value (C.retainedParameter (C.parameter u))))
  rw [C.retainedParameter_parameter]
  ring

theorem admissibleFullPacket_site_expect {p : ℝ} (hreference : reference.ComplexityLE p)
    (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (err : A.Site → ℂ) :
    (𝔼 site ∈ (candidate.admissibleFullPacket reference hreference hcost hshort).slice.subtypeSites,
      err site * (candidate.admissibleFullPacket reference hreference hcost hshort).weight site.val) =
      (Real.exp (-p) : ℂ) * C.localLaw.complexMean
        (fun site => err site * reference.observable (candidate.siteValue site)) := by
  let signal : (LayerSamplerVariables G I n B → ℤ) → ℂ :=
    Function.extend Subtype.val err (fun _ => 0)
  have heval (site : A.Site) : signal site.val = err site :=
    Subtype.val_injective.extend_apply _ _ site
  have h := candidate.admissibleFullPacket_expect reference hreference hcost hshort signal
  simpa only [heval] using h

theorem localLaw_residual_le_of_uniform {p ε : ℝ} (hreference : reference.ComplexityLE p)
    (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (err : A.Site → ℂ)
    (hUniform : ∀ packet : LocalMajorSliceTest D A.sides cost p,
      ‖𝔼 site ∈ packet.slice.subtypeSites, err site * packet.weight site.val‖ ≤ ε) :
    ‖C.localLaw.complexMean
      (fun site => err site * reference.observable (candidate.siteValue site))‖ ≤
        Real.exp p * ε := by
  have h := hUniform (candidate.admissibleFullPacket reference hreference hcost hshort)
  rw [candidate.admissibleFullPacket_site_expect reference hreference hcost hshort err,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-p))] at h
  calc
    _ = Real.exp p * (Real.exp (-p) * ‖C.localLaw.complexMean
        (fun site => err site * reference.observable (candidate.siteValue site))‖) := by
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp p * ε := mul_le_mul_of_nonneg_left h (Real.exp_nonneg p)

theorem localLaw_residual_le_exp_of_uniform {p Eres : ℝ}
    (hreference : reference.ComplexityLE p) (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (err : A.Site → ℂ)
    (hUniform : ∀ packet : LocalMajorSliceTest D A.sides cost p,
      ‖𝔼 site ∈ packet.slice.subtypeSites, err site * packet.weight site.val‖ ≤
        Real.exp (-Eres)) :
    ‖C.localLaw.complexMean
      (fun site => err site * reference.observable (candidate.siteValue site))‖ ≤
        Real.exp (p - Eres) := by
  simpa only [← Real.exp_add, sub_eq_add_neg] using
    candidate.localLaw_residual_le_of_uniform reference hreference hcost hshort err hUniform

theorem localLaw_residual_le_exp_of_uniform_budget
    {p Eres sliceBudget testBudget : ℝ}
    (hreference : reference.ComplexityLE p) (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (hSliceBudget : cost ≤ sliceBudget) (hTestBudget : p ≤ testBudget)
    (err : A.Site → ℂ)
    (hUniform : ∀ packet : LocalMajorSliceTest D A.sides sliceBudget testBudget,
      ‖𝔼 site ∈ packet.slice.subtypeSites, err site * packet.weight site.val‖ ≤
        Real.exp (-Eres)) :
    ‖C.localLaw.complexMean
      (fun site => err site * reference.observable (candidate.siteValue site))‖ ≤
        Real.exp (p - Eres) := by
  apply candidate.localLaw_residual_le_exp_of_uniform reference hreference hcost hshort err
  intro packet
  exact hUniform (packet.mono hSliceBudget hTestBudget)

end AllocatedExternalLocalCandidate
end
end Erdos3.VectorPolynomial

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

end AllocatedExternalLocalChart

namespace AllocatedExternalLocalCandidate
variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M V : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    {w : V → ℕ} (reference : D.Niltest w)
    {budget : ℝ} (hnorm : (reference.normBound : ℝ) ≤ 1)
    (hcomplex : reference.ComplexityLE budget)

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable section

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

namespace AllocatedExternalLocalChart
variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

variable {L : Type} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

end AllocatedExternalLocalChart
end
end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable section

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

namespace AllocatedExternalLocalCandidate

variable {A} {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L : Type} {M V : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    {w : V → ℕ} (reference : D.Niltest w)

theorem localLaw_residual_le_exp_of_universal_native_budget
    {p Eres sliceBudget testBudget : ℝ}
    (hreference : reference.ComplexityLE p) (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (hSliceBudget : cost ≤ sliceBudget) (hTestBudget : p ≤ testBudget)
    (err : A.Site → ℂ)
    (hUniform : ∀ packet : UniversalLocalMajorSliceTest A.sides s sliceBudget testBudget,
      ‖𝔼 site ∈ packet.slice.subtypeSites, err site * packet.weight site.val‖ ≤
        Real.exp (-Eres)) :
    ‖C.localLaw.complexMean
      (fun site => err site * reference.observable (candidate.siteValue site))‖ ≤
        Real.exp (p - Eres) := by
  apply candidate.localLaw_residual_le_exp_of_uniform_budget reference hreference hcost hshort
    hSliceBudget hTestBudget err
  intro packet
  exact hUniform (UniversalLocalMajorSliceTest.ofLocalMajorSliceTest packet)

end AllocatedExternalLocalCandidate
end
end Erdos3.VectorPolynomial

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
    {sliceBudget testBudget : ℝ}
    (hbudget : 0 ≤ sliceBudget) (hcost : outputCost ≤ sliceBudget)
    (htest : 2 ≤ testBudget)
    (hshort : ∀ z : out.retained, ∀ i : {i // ¬(P.chart ⟨z.val, out.subset z.property⟩).keep i},
      (A.sides i.val : ℝ) ≤ Real.exp sliceBudget)

noncomputable def retainedResidualPacket (z : out.retained) :
    LocalMajorSliceTest (RationalTorus.trivialNilmanifold 0) A.sides sliceBudget testBudget where
  stride := out.step z
  stride_pos := out.step_pos z
  slice := (out.slice z).freezeShort (P.chart ⟨z.val, out.subset z.property⟩).keep
    (P.chart ⟨z.val, out.subset z.property⟩).fixedNatural
    (P.chart ⟨z.val, out.subset z.property⟩).fixedNatural_lt
  dense := by
    let C := P.chart ⟨z.val, out.subset z.property⟩
    have he : Classical.decEq C.Variables = Subtype.instDecidableEq :=
      Subsingleton.elim _ _
    have hd : @IsDenseCommonStrideBox C.Variables _ Subtype.instDecidableEq
        (fun i => A.sides i.val) outputCost
        (@ResidueBoxSlice.integerPoints C.Variables _ _ _ Subtype.instDecidableEq (out.slice z)) := by
      rw [← he]
      exact out.dense z
    have h : IsDenseCommonStrideBox A.sides (max outputCost (Real.log (Real.exp sliceBudget)))
        ((out.slice z).freezeShort C.keep C.fixedNatural C.fixedNatural_lt).integerPoints := by
      exact (out.slice z).freezeShort_dense C.keep C.fixedNatural C.fixedNatural_lt
        (out.step_pos z) hd (Real.one_le_exp hbudget) (fun i hi => hshort z ⟨i, hi⟩)
    simpa only [Real.log_exp, max_eq_right hcost] using h
  test := RationalFilteredNilmanifold.Niltest.const (RationalTorus.trivialNilmanifold 0) _ 1
  norm := by change ‖(1 : ℂ)‖ ≤ 1; exact le_of_eq norm_one
  complexity := RationalTorus.trivialNilmanifold_const_one_complexity 0 _ htest

@[simp] theorem retainedResidualPacket_weight (z : out.retained)
    (x : LayerSamplerVariables G I n B → ℤ) :
    (out.retainedResidualPacket hbudget hcost htest hshort z).weight x = 1 := by
  simp [LocalMajorSliceTest.weight, retainedResidualPacket]

noncomputable def residualPacket (z : A.Path) :
    LocalMajorSliceTest (RationalTorus.trivialNilmanifold 0) A.sides sliceBudget testBudget :=
  if hz : z ∈ out.retained then out.retainedResidualPacket hbudget hcost htest hshort ⟨z, hz⟩
  else LocalMajorSliceTest.full A.sides A.sides_pos sliceBudget testBudget hbudget
    (RationalFilteredNilmanifold.Niltest.const (RationalTorus.trivialNilmanifold 0) _ 1)
    (by simp [RationalFilteredNilmanifold.Niltest.const])
    (RationalTorus.trivialNilmanifold_const_one_complexity 0 _ htest)

@[simp] theorem residualPacket_weight (z : A.Path)
    (x : LayerSamplerVariables G I n B → ℤ) :
    (out.residualPacket hbudget hcost htest hshort z).weight x = 1 := by
  unfold residualPacket
  split_ifs
  · exact out.retainedResidualPacket_weight hbudget hcost htest hshort _ x
  · simp [LocalMajorSliceTest.weight, LocalMajorSliceTest.full]

@[simp] theorem residualPacket_retained (z : out.retained) :
    out.residualPacket hbudget hcost htest hshort z.val =
      out.retainedResidualPacket hbudget hcost htest hshort z := by
  simp only [residualPacket, dif_pos z.property]

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

def spatialNativeVerticalParameter (pNative pLocal r : ℝ) : ℝ :=
  max pNative 0 + pLocal + r + 1

def spatialNativeFactorParameter (p pNative pLocal r : ℝ) : ℝ :=
  max p (r + verticalDecompositionBudget (spatialNativeVerticalParameter pNative pLocal r) + 2)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {X : Type*} (J : Fin m → Type*)

noncomputable def fullTaggedSpatialIntegerChart (x : X) : MvPolynomial (X ⊕ (Σ j, J j)) ℤ :=
  MvPolynomial.X (Sum.inl x)

theorem fullTaggedSpatialIntegerChart_support (x : X) :
    integerSampledRealChart (fullTaggedSpatialIntegerChart (X := X) J) x ∈
      weightedSupportLE (fullTaggedVariableWeight J) 1 := by
  change MvPolynomial.map (Int.castRingHom ℝ) (MvPolynomial.X (Sum.inl x)) ∈ _
  rw [MvPolynomial.map_X]
  exact weightedSupportLE_X (fullTaggedVariableWeight J) (Sum.inl x)

end Erdos3.VectorPolynomial

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open VectorPolynomial
open scoped TensorProduct

variable {m : ℕ} {X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}
    (Q : D.Niltest (fun _ : X => 1)) (J : Fin m → Type*)

noncomputable def fullTaggedSpatial : D.Niltest (fullTaggedVariableWeight (X := X) J) :=
  Q.integerChartPullback (fullTaggedVariableWeight J) (fullTaggedSpatialIntegerChart J)
    (fullTaggedSpatialIntegerChart_support J)

@[simp] theorem fullTaggedSpatial_eval (u : X ⊕ (Σ j, J j) → ℤ) :
    (Q.fullTaggedSpatial J).eval u = Q.eval (fun x => u (Sum.inl x)) := by
  rw [fullTaggedSpatial, integerChartPullback_eval]
  simp only [fullTaggedSpatialIntegerChart, MvPolynomial.eval_X]

@[simp] theorem fullTaggedSpatial_eval_physical
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (u : X → ℤ) :
    (Q.fullTaggedSpatial J).eval (fullTaggedPhysicalIntegerPoint J poly c u) = Q.eval u := by
  rw [fullTaggedSpatial_eval]
  rfl

@[simp] theorem fullTaggedSpatial_normBound :
    (Q.fullTaggedSpatial J).normBound = Q.normBound := rfl

@[simp] theorem fullTaggedSpatial_complexity (p : ℝ) :
    (Q.fullTaggedSpatial J).ComplexityLE p ↔ Q.ComplexityLE p := Iff.rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

namespace Erdos3.NativeSampleModel

open VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra NativeSampleModel.topology NativeSampleModel.topologicalAdd NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {m s : ℕ} {X T : Type*} {p : ℝ}
    {sample : T → X → ℤ} {f : T → ℂ}
    (Q : NativeSampleModel (fun _ : X => 1) s p sample f)
    (J : Fin m → Type*) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))

end Erdos3.NativeSampleModel

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators Classical

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra NativeSampleModel.topology NativeSampleModel.topologicalAdd NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

theorem exists_spatialNative_slice_tagged_vertical_partners
    {Ω Pivot K X T LG : Type*} [Fintype Ω] [Fintype Pivot] [Fintype K] [DecidableEq K]
    [LieRing LG] [LieAlgebra ℚ LG]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {m s d : ℕ} (J : Fin m → Type*)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (D : RationalFilteredNilmanifold LG s d)
    {pNative : ℝ} (sample : T → X → ℤ)
    (nativeValue : Pivot → T → ℂ)
    (native : ∀ j, NativeSampleModel (fun _ : X => 1) s pNative sample (nativeValue j))
    (P : Ω → Pivot → D.Niltest (fun _ : K => 1))
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    {N : K → ℕ} (stride : Ω → Pivot → ℕ)
    (S : ∀ a j, ResidueBoxSlice N (stride a j))
    (hstride : ∀ a ∈ H, ∀ j, 0 < stride a j)
    (hlen : ∀ a j i, 0 < (S a j).length i)
    (physical : Ω → integerBox N → T)
    (center : Ω → ∀ j, J j → ℝ)
    (twist : Ω → Pivot → integerBox N → ℂ)
    {pLocal r q : ℝ} (hpLocal : 0 ≤ pLocal) (hr : 0 ≤ r) (hpq : pNative ≤ q)
    (hprecision : pLocal + r + 1 ≤ q)
    (hP : ∀ a ∈ H, ∀ j, (P a j).ComplexityLE pLocal)
    (htwist : ∀ a ∈ H, ∀ j t, ‖twist a j t‖ ≤ 1)
    (hcorr : ∀ a ∈ H, ∀ j, Real.exp (-r) ≤
      ‖((S a j).fullSliceLaw (hlen a j)).complexMean (fun t =>
        (star (twist a j t) * nativeValue j (physical a t)) * (P a j).eval t.val)‖) :
    ∃ (freq : ∀ j, (native j).L →ₗ[ℚ] ℚ)
      (V : ∀ j, (native j).model.Niltest (fullTaggedVariableWeight (X := X) J))
      (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      Real.exp (-verticalDecompositionBudget q * Fintype.card Pivot) * outer.mass H ≤
        outer.mass retained ∧
      (∀ j, (V j).orbit = ((native j).test.fullTaggedSpatial J).orbit ∧
        (V j).ComplexityLE pNative ∧ (V j).normBound ≤ 1) ∧
      (∀ j i, rationalLogHeight (freq j ((native j).model.basis i)) ≤
        verticalDecompositionBudget q) ∧
      (∀ j z, z ∈ (native j).model.filtration.realification.subgroup s → ∀ x,
        (V j).observable (z • x) = character
          ((realifyFunctional (freq j) z.coord : ℝ) : CircleFourier.Circle) * (V j).observable x) ∧
      ∀ a ∈ retained, ∀ j,
        Real.exp (-r) / (2 * Real.exp (verticalDecompositionBudget q)) ≤
          ‖((S a j).fullSliceLaw (hlen a j)).complexMean (fun t =>
            star (twist a j t) * ((P a j).eval t.val *
              (V j).eval (fullTaggedPhysicalIntegerPoint J poly (center a)
                (sample (physical a t)))))‖ := by
  have hnativeCorr (a : Ω) (ha : a ∈ H) (j : Pivot) :
      Real.exp (-r) ≤ ‖((S a j).fullSliceLaw (hlen a j)).complexMean (fun t =>
        ((P a j).eval t.val * star (twist a j t)) *
          (native j).test.eval (sample (physical a t)))‖ := by
    convert hcorr a ha j using 2
    congr 1
    funext t
    rw [(native j).eval]
    ring
  obtain ⟨freq, V, retained, hsub, hpos, hmass, hcert, hheight, hvert, _hint,
      _hpres, hselected⟩ := exists_sliceLaw_localPivot_weighted_native_vertical_partners
    (fun j => (native j).model) (fun _ _ => D) (fun j => (native j).test) P
    outer H hH stride S hstride hlen (fun a t => sample (physical a t)) (fun _ _ t => t.val)
    (fun a j t => star (twist a j t)) hpLocal hr hpq hprecision
    (fun j => (native j).complexity) (fun j => by exact_mod_cast (native j).norm)
    hP (fun a ha j t => by simpa only [norm_star] using htwist a ha j t) hnativeCorr
  refine ⟨freq, (fun j => (V j).fullTaggedSpatial J), retained,
    hsub, hpos, hmass, ?_, hheight, hvert, ?_⟩
  · intro j
    refine ⟨?_, (hcert j).1, ?_⟩
    · simp only [Niltest.fullTaggedSpatial, Niltest.integerChartPullback,
        Niltest.withOrbit, (hcert j).2.1]
    · exact_mod_cast (hcert j).2.2.2.2
  · intro a ha j
    convert hselected a ha j using 2
    congr 1
    funext t
    rw [Niltest.fullTaggedSpatial_eval_physical]
    ring

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra NativeSampleModel.topology NativeSampleModel.topologicalAdd NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

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

structure AllocatedExternalCandidateSpatialNativeFamily
    (Deck : Fin m → Type*) (Ω Pivot : Type*) [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ t : ℕ}
    (D : RationalFilteredNilmanifold LG s d₀)
    (Fmark : NilpotentLieFiltration LM t) (φ : LG →ₗ⁅ℚ⁆ LM)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (keep : LayerSamplerVariables G I n B → Prop)
    (cost p pLocal pNative r periodCap coverCap : ℝ) (Lip : ℝ≥0) where
  hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)
  hτ1 : τ ≤ 1
  hξ : ξ ≤ 1
  hσ1 : ∀ j, σ j ≤ 1
  Cgeo : Fin m → ℝ
  hCgeo : ∀ j, 0 ≤ Cgeo j
  hchart : ∀ j x,
    ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖
  hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8
  sourceChart : Ω → AllocatedExternalLocalChart (E := Deck) A cost
  keep_eq : ∀ a, (sourceChart a).keep = keep
  sourceCandidate : ∀ a, AllocatedExternalLocalCandidate (sourceChart a) D Fmark φ marked
  reference : Ω → Pivot → D.Niltest (fullTaggedVariableWeight (X := X) J)
  nativeValue : Pivot → integerBox N → ℂ
  native : ∀ j, NativeSampleModel (fun _ : X => 1) s pNative
    (fun x : integerBox N => x.val) (nativeValue j)
  twist : Ω → Pivot → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip
  hp : 0 ≤ p
  hpLocal : 0 ≤ pLocal
  hr : 0 ≤ r
  hcost : cost ≤ p
  hlocal : pLocal ≤ p
  hnative : pNative ≤ p
  hperiod : ∀ a j, (((twist a j).modulus * (twist a j).cover : ℕ) : ℝ) ≤ Real.exp p
  hvariation : (Lip : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
    ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p
  hV : ∀ a j, (reference a j).ComplexityLE pLocal
  η : Pivot → LG →ₗ[ℚ] ℚ
  hηheight : ∀ j i, rationalLogHeight (η j (D.basis i)) ≤ p
  hη : ∀ a j z, z ∈ D.filtration.realification.subgroup s → ∀ x,
    (reference a j).observable (z • x) = CircleFourier.character
      ((realifyFunctional (η j) z.coord : ℝ) : CircleFourier.Circle) * (reference a j).observable x
  hK : (Fintype.card {i // keep i} : ℝ) ≤ p

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

def chart (a : Ω) : AllocatedExternalLocalChart (E := Deck) A cost :=
  (F.sourceChart a).withKeep keep (F.keep_eq a)

def candidate (a : Ω) : AllocatedExternalLocalCandidate (F.chart a) D Fmark φ marked :=
  (F.sourceCandidate a).withKeep keep (F.keep_eq a)

def localTest (a : Ω) (j : Pivot) : D.Niltest (fun _ : {i // keep i} => 1) :=
  (F.reference a j).withOrbit (F.candidate a).orbit

def jointOrbit (a : Ω) : ∀ i : Option Pivot,
    (optionFactors D (fun j => (F.native j).model) i).filtration.realification.PolynomialOrbit
      (fun _ : {i // keep i} => 1)
  | none => (F.candidate a).orbit
  | some j => (((F.native j).test.fullTaggedSpatial J).integerChartPullback
      (fun _ : {i // keep i} => 1)
      (F.chart a).integerChart (F.chart a).integerChart_support).orbit

def physicalBox (a : Ω) (u : integerBox (fun i : {i // keep i} => A.sides i.val)) :
    integerBox N :=
  ⟨A.physical (F.chart a).path ((F.chart a).site u.val u.property),
    A.physical_mem_integerBox F.hξ _ _⟩

@[simp] theorem physicalBox_val (a : Ω)
    (u : integerBox (fun i : {i // keep i} => A.sides i.val)) :
    (F.physicalBox a u).val = (F.chart a).physical u.val := rfl

def sitePhysicalBox (a : Ω) (site : A.Site) : integerBox N :=
  ⟨A.physical (F.sourceChart a).path site,
    A.physical_mem_integerBox F.hξ _ _⟩

def correlation (a : Ω) (j : Pivot) : ℂ :=
  (F.sourceChart a).localLaw.complexMean (fun site =>
    star ((F.twist a j).eval N poly (F.sitePhysicalBox a site).val) *
      ((F.reference a j).observable ((F.sourceCandidate a).siteValue site) *
        F.nativeValue j (F.sitePhysicalBox a site)))

@[simp] theorem chart_localLaw (a : Ω) :
    (F.chart a).localLaw = (F.sourceChart a).localLaw :=
  (F.sourceChart a).withKeep_localLaw A keep (F.keep_eq a)

theorem rawCorrelation_fullSliceLaw (a : Ω) (j : Pivot)
    (hcorr : Real.exp (-r) ≤ ‖F.correlation a j‖) :
    Real.exp (-r) ≤
      ‖((F.chart a).slice.fullSliceLaw
        ((F.chart a).slice.length_pos_of_dense (F.chart a).dense)).complexMean (fun u =>
        (star ((F.twist a j).eval N poly (F.physicalBox a u).val) *
          F.nativeValue j (F.physicalBox a u)) * (F.localTest a j).eval u.val)‖ := by
  have hm := (F.chart a).localLaw_complexMean_eq_fullSliceLaw_site (fun site =>
    star ((F.twist a j).eval N poly (F.sitePhysicalBox a site).val) *
      ((F.reference a j).observable ((F.sourceCandidate a).siteValue site) *
        F.nativeValue j (F.sitePhysicalBox a site)))
  rw [F.chart_localLaw] at hm
  unfold correlation at hcorr
  rw [hm] at hcorr
  convert hcorr using 2
  congr 1
  funext u
  have hv : (F.sourceCandidate a).siteValue ((F.chart a).site u.val u.property) =
      (F.candidate a).value u.val := by
    rw [← (F.sourceCandidate a).withKeep_siteValue keep (F.keep_eq a)]
    change (F.candidate a).value
      ((F.chart a).retainedParameter ((F.chart a).parameter u.val)) = _
    rw [(F.chart a).retainedParameter_parameter]
  simp only [localTest, hv]
  change (star ((F.twist a j).eval N poly (F.physicalBox a u).val) *
      F.nativeValue j (F.physicalBox a u)) *
      (F.reference a j).observable ((F.candidate a).value u.val) =
    star ((F.twist a j).eval N poly (F.physicalBox a u).val) *
      ((F.reference a j).observable ((F.candidate a).value u.val) *
        F.nativeValue j (F.physicalBox a u))
  ring

theorem selectedCorrelation_localLaw
    (V : ∀ j, (F.native j).model.Niltest (fullTaggedVariableWeight (X := X) J))
    (a : Ω) (j : Pivot)
    (hcorr : Real.exp (-p) ≤
      ‖((F.chart a).slice.fullSliceLaw
        ((F.chart a).slice.length_pos_of_dense (F.chart a).dense)).complexMean (fun u =>
        star ((F.twist a j).eval N poly (F.physicalBox a u).val) *
          ((F.localTest a j).eval u.val *
            (V j).eval (fullTaggedPhysicalIntegerPoint J poly
              (fun k => ((F.chart a).centerLift k).val) (F.physicalBox a u).val)))‖) :
    Real.exp (-p) ≤ ‖(F.sourceChart a).localLaw.complexMean (fun site =>
      star ((F.twist a j).eval N poly (A.physical (F.sourceChart a).path site)) *
        ((F.reference a j).observable
            ((F.candidate a).value ((F.chart a).retainedParameter site.val)) *
          (V j).eval (fullTaggedPhysicalIntegerPoint J poly
            (fun k => ((F.sourceChart a).centerLift k).val)
            (A.physical (F.sourceChart a).path site))))‖ := by
  have hm := (F.chart a).localLaw_complexMean_eq_fullSliceLaw_site (fun site =>
    star ((F.twist a j).eval N poly (A.physical (F.sourceChart a).path site)) *
      ((F.reference a j).observable
          ((F.candidate a).value ((F.chart a).retainedParameter site.val)) *
        (V j).eval (fullTaggedPhysicalIntegerPoint J poly
          (fun k => ((F.sourceChart a).centerLift k).val)
          (A.physical (F.sourceChart a).path site))))
  rw [F.chart_localLaw] at hm
  rw [hm]
  convert hcorr using 2
  congr 1
  funext u
  change star ((F.twist a j).eval N poly (F.physicalBox a u).val) *
      ((F.reference a j).observable
          ((F.candidate a).value ((F.chart a).retainedParameter ((F.chart a).parameter u.val))) *
        (V j).eval (fullTaggedPhysicalIntegerPoint J poly
          (fun k => ((F.chart a).centerLift k).val) (F.physicalBox a u).val)) = _
  rw [(F.chart a).retainedParameter_parameter]
  rfl

theorem exp_correlation_bound {q : ℝ}
    (hbudget : r + verticalDecompositionBudget q + 2 ≤ p) :
    Real.exp (-p) ≤ Real.exp (-r) / (2 * Real.exp (verticalDecompositionBudget q)) := by
  apply (Real.exp_le_exp.mpr (neg_le_neg hbudget)).trans
  apply (le_div_iff₀ (by positivity)).mpr
  have he : Real.exp (-(r + verticalDecompositionBudget q + 2)) *
      (2 * Real.exp (verticalDecompositionBudget q)) = 2 * Real.exp (-r - 2) := by
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  rw [he]
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ Real.exp 2 * Real.exp (-r - 2) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp (-r) := by rw [← Real.exp_add]; congr 1; ring

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

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {Ω Freq Bin : Type} [Fintype Ω] [Fintype Bin] [Nonempty Bin]
    {LG LM : Type} [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d t rank : ℕ} (D : RationalFilteredNilmanifold LG s d)
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {cost : ℝ} (C : Ω → AllocatedExternalLocalChart (E := Deck) A cost)
    (candidate : ∀ a, AllocatedExternalLocalCandidate (C a) D Fmark φ marked)
    (hξ1 : ξ ≤ 1)

end AllocatedExternalCandidateSampler
end
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra NativeSampleModel.topology NativeSampleModel.topologicalAdd NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

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

def withBudget (q : ℝ) (hpq : p ≤ q) :
    AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
      keep cost q pLocal pNative r periodCap coverCap Lip where
  hpoly := F.hpoly
  hτ1 := F.hτ1
  hξ := F.hξ
  hσ1 := F.hσ1
  Cgeo := F.Cgeo
  hCgeo := F.hCgeo
  hchart := F.hchart
  hsmall := F.hsmall
  sourceChart := F.sourceChart
  keep_eq := F.keep_eq
  sourceCandidate := F.sourceCandidate
  reference := F.reference
  nativeValue := F.nativeValue
  native := F.native
  twist := F.twist
  hp := F.hp.trans hpq
  hpLocal := F.hpLocal
  hr := F.hr
  hcost := F.hcost.trans hpq
  hlocal := F.hlocal.trans hpq
  hnative := F.hnative.trans hpq
  hperiod := fun a j => (F.hperiod a j).trans (Real.exp_le_exp.mpr hpq)
  hvariation := F.hvariation.trans (Real.exp_le_exp.mpr hpq)
  hV := F.hV
  η := F.η
  hηheight := fun j i => (F.hηheight j i).trans hpq
  hη := F.hη
  hK := F.hK.trans hpq

@[simp] theorem withBudget_sourceChart (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).sourceChart = F.sourceChart := rfl

@[simp] theorem withBudget_sourceCandidate (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).sourceCandidate = F.sourceCandidate := rfl

@[simp] theorem withBudget_reference (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).reference = F.reference := rfl

@[simp] theorem withBudget_nativeValue (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).nativeValue = F.nativeValue := rfl

@[simp] theorem withBudget_native (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).native = F.native := rfl

@[simp] theorem withBudget_twist (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).twist = F.twist := rfl

@[simp] theorem withBudget_eta (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).η = F.η := rfl

@[simp] theorem withBudget_chart (q : ℝ) (hpq : p ≤ q) (a : Ω) :
    (F.withBudget q hpq).chart a = F.chart a := rfl

@[simp] theorem withBudget_candidate (q : ℝ) (hpq : p ≤ q) (a : Ω) :
    (F.withBudget q hpq).candidate a = F.candidate a := rfl

@[simp] theorem withBudget_jointOrbit (q : ℝ) (hpq : p ≤ q) (a : Ω) :
    (F.withBudget q hpq).jointOrbit a = F.jointOrbit a := rfl

@[simp] theorem withBudget_correlation (q : ℝ) (hpq : p ≤ q) (a : Ω) (j : Pivot) :
    (F.withBudget q hpq).correlation a j = F.correlation a j := rfl

def withFactorBudget :
    AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
      keep cost (spatialNativeFactorParameter p pNative pLocal r)
      pLocal pNative r periodCap coverCap Lip :=
  F.withBudget (spatialNativeFactorParameter p pNative pLocal r) (le_max_left _ _)

@[simp] theorem withFactorBudget_sourceChart :
    F.withFactorBudget.sourceChart = F.sourceChart := rfl

@[simp] theorem withFactorBudget_sourceCandidate :
    F.withFactorBudget.sourceCandidate = F.sourceCandidate := rfl

@[simp] theorem withFactorBudget_native : F.withFactorBudget.native = F.native := rfl

@[simp] theorem withFactorBudget_twist : F.withFactorBudget.twist = F.twist := rfl

@[simp] theorem withFactorBudget_eta : F.withFactorBudget.η = F.η := rfl

@[simp] theorem withFactorBudget_correlation (a : Ω) (j : Pivot) :
    F.withFactorBudget.correlation a j = F.correlation a j := rfl

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeReindex
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra NativeSampleModel.topology NativeSampleModel.topologicalAdd NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

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

def reindex {Ω' : Type*} (f : Ω' → Ω) :
    AllocatedExternalCandidateSpatialNativeFamily A Deck Ω' Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip where
  hpoly := F.hpoly
  hτ1 := F.hτ1
  hξ := F.hξ
  hσ1 := F.hσ1
  Cgeo := F.Cgeo
  hCgeo := F.hCgeo
  hchart := F.hchart
  hsmall := F.hsmall
  sourceChart := fun a => F.sourceChart (f a)
  keep_eq := fun a => F.keep_eq (f a)
  sourceCandidate := fun a => F.sourceCandidate (f a)
  reference := fun a => F.reference (f a)
  nativeValue := F.nativeValue
  native := F.native
  twist := fun a => F.twist (f a)
  hp := F.hp
  hpLocal := F.hpLocal
  hr := F.hr
  hcost := F.hcost
  hlocal := F.hlocal
  hnative := F.hnative
  hperiod := fun a => F.hperiod (f a)
  hvariation := F.hvariation
  hV := fun a => F.hV (f a)
  η := F.η
  hηheight := F.hηheight
  hη := fun a => F.hη (f a)
  hK := F.hK

@[simp] theorem reindex_nativeValue {Ω' : Type*} (f : Ω' → Ω) :
    (F.reindex f).nativeValue = F.nativeValue := rfl

@[simp] theorem reindex_native {Ω' : Type*} (f : Ω' → Ω) :
    (F.reindex f).native = F.native := rfl

@[simp] theorem reindex_η {Ω' : Type*} (f : Ω' → Ω) :
    (F.reindex f).η = F.η := rfl

@[simp] theorem reindex_sourceChart {Ω' : Type*} (f : Ω' → Ω) (a : Ω') :
    (F.reindex f).sourceChart a = F.sourceChart (f a) := rfl

@[simp] theorem reindex_sourceCandidate {Ω' : Type*} (f : Ω' → Ω) (a : Ω') :
    (F.reindex f).sourceCandidate a = F.sourceCandidate (f a) := rfl

@[simp] theorem reindex_correlation {Ω' : Type*} (f : Ω' → Ω) (a : Ω') (j : Pivot) :
    (F.reindex f).correlation a j = F.correlation (f a) j := rfl

@[simp] theorem reindex_jointOrbit {Ω' : Type*} (f : Ω' → Ω) (a : Ω') :
    (F.reindex f).jointOrbit a = F.jointOrbit (f a) := rfl

def positiveMassRetract [Fintype Ω]
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (a : Ω) : {a // a ∈ H} := by
  have hne : H.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty,
      lt_self_iff_false] at hH)
  exact if ha : a ∈ H then ⟨a, ha⟩ else ⟨hne.choose, hne.choose_spec⟩

@[simp] theorem positiveMassRetract_mem [Fintype Ω]
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (a : Ω) (ha : a ∈ H) :
    positiveMassRetract outer H hH a = ⟨a, ha⟩ := by
  simp only [positiveMassRetract, dif_pos ha]

variable [Fintype Ω] (outer : FiniteProbabilityWeights Ω) (H : Finset Ω)
    (hH : 0 < outer.mass H)
    (FH : AllocatedExternalCandidateSpatialNativeFamily A Deck {a // a ∈ H} Pivot
      D Fmark φ marked keep cost p pLocal pNative r periodCap coverCap Lip)

def extend : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
    keep cost p pLocal pNative r periodCap coverCap Lip :=
  FH.reindex (positiveMassRetract outer H hH)

@[simp] theorem extend_nativeValue :
    (FH.extend outer H hH).nativeValue = FH.nativeValue := rfl

@[simp] theorem extend_native :
    (FH.extend outer H hH).native = FH.native := rfl

@[simp] theorem extend_η :
    (FH.extend outer H hH).η = FH.η := rfl

@[simp] theorem extend_sourceChart (a : Ω) (ha : a ∈ H) :
    (FH.extend outer H hH).sourceChart a = FH.sourceChart ⟨a, ha⟩ := by
  change FH.sourceChart (positiveMassRetract outer H hH a) = _
  rw [positiveMassRetract_mem outer H hH a ha]

@[simp] theorem extend_sourceCandidate (a : Ω) (ha : a ∈ H) :
    HEq ((FH.extend outer H hH).sourceCandidate a) (FH.sourceCandidate ⟨a, ha⟩) := by
  change HEq (FH.sourceCandidate (positiveMassRetract outer H hH a)) _
  rw [positiveMassRetract_mem outer H hH a ha]

@[simp] theorem extend_correlation (a : Ω) (ha : a ∈ H) (j : Pivot) :
    (FH.extend outer H hH).correlation a j = FH.correlation ⟨a, ha⟩ j := by
  change FH.correlation (positiveMassRetract outer H hH a) j = _
  rw [positiveMassRetract_mem outer H hH a ha]

@[simp] theorem extend_jointOrbit (a : Ω) (ha : a ∈ H) :
    (FH.extend outer H hH).jointOrbit a = FH.jointOrbit ⟨a, ha⟩ := by
  change FH.jointOrbit (positiveMassRetract outer H hH a) = _
  rw [positiveMassRetract_mem outer H hH a ha]

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

end OAI

end


