-- Prove2me | Definitions.Def_OAIE3v2B306
-- name    : OAIE3v2B306
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T06:49:47.76917+00:00
-- url     : https://prove2.me/theorems/f8c9278d-922f-432c-9a52-38ec80180543
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 278 of 311
-- statement:
--   Definitions bundle 278 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B305`, `OAIE3v2B265`, `OAIE3v2B268` of this split.
--
--   Modules: `Dynamics/AllocatedExternalCandidatePrecenterPaths.lean`, `Estimates/AllocatedExternalCandidateLocalFixedCenterFront.lean`, `Estimates/AllocatedExternalCandidateSelectedDescentRegularity.lean`, `Estimates/AllocatedExternalCandidateTaggedPairLongUniformFactors.lean`, `Estimates/PreparedCanonicalRelativeEndpointBounds.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeAutomaticLongGeometry.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeReindex.lean`, `Linear/AllocatedExternalCandidateCommonKeepPositiveKernelPreparation.lean`, `Nilpotent/AllocatedKeptCommonCurrentGradeLocalNiltest.lean`, `Sampling/PreparedCanonicalPaddedSamplerData.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B305
import Definitions.Def_OAIE3v2B265
import Definitions.Def_OAIE3v2B268

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeReindex
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

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidatePrecenterPaths
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
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

noncomputable def precenterChart (hpos : 0 < A.law.mass P.productive)
    (a : A.Path) : AllocatedExternalLocalChart (E := E) A cost :=
  P.chart (AllocatedExternalCandidateSpatialNativeFamily.positiveMassRetract
    A.law P.productive hpos a)

noncomputable def precenterCandidate (hpos : 0 < A.law.mass P.productive)
    (a : A.Path) : AllocatedExternalLocalCandidate (P.precenterChart hpos a) D Fmark φ marked :=
  P.candidate (AllocatedExternalCandidateSpatialNativeFamily.positiveMassRetract
    A.law P.productive hpos a)

@[simp] theorem precenterChart_mem (hpos : 0 < A.law.mass P.productive)
    (a : A.Path) (ha : a ∈ P.productive) : P.precenterChart hpos a = P.chart ⟨a, ha⟩ := by
  unfold precenterChart
  rw [AllocatedExternalCandidateSpatialNativeFamily.positiveMassRetract_mem]

@[simp] theorem precenterCandidate_mem (hpos : 0 < A.law.mass P.productive)
    (a : A.Path) (ha : a ∈ P.productive) :
    HEq (P.precenterCandidate hpos a) (P.candidate ⟨a, ha⟩) := by
  change HEq (P.candidate (AllocatedExternalCandidateSpatialNativeFamily.positiveMassRetract
    A.law P.productive hpos a)) (P.candidate ⟨a, ha⟩)
  rw [AllocatedExternalCandidateSpatialNativeFamily.positiveMassRetract_mem]

@[simp] theorem precenterChart_path (hpos : 0 < A.law.mass P.productive)
    (a : A.Path) (ha : a ∈ P.productive) : (P.precenterChart hpos a).path = a := by
  rw [P.precenterChart_mem hpos a ha]
  exact P.chart_path _

@[simp] theorem precenterChart_center (hpos : 0 < A.law.mass P.productive)
    (a : A.Path) : (P.precenterChart hpos a).centerLift = P.centerLift :=
  P.chart_centerLift _

@[simp] theorem precenterChart_keep (hpos : 0 < A.law.mass P.productive)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ a, (P.chart a).keep = keep) (a : A.Path) :
    (P.precenterChart hpos a).keep = keep := hkeep _

theorem precenterCandidate_score_mem_eq (hpos : 0 < A.law.mass P.productive)
    (a : A.Path) (ha : a ∈ P.productive)
    (newObservable : (X → ℤ) → D.Space → ℂ) :
    (P.precenterCandidate hpos a).score newObservable weight =
      (P.candidate ⟨a, ha⟩).score newObservable weight := by
  change (P.candidate (AllocatedExternalCandidateSpatialNativeFamily.positiveMassRetract
    A.law P.productive hpos a)).score newObservable weight = _
  rw [AllocatedExternalCandidateSpatialNativeFamily.positiveMassRetract_mem]

end AllocatedExternalCandidateProblem
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

structure PrecenterKernelSelection
    {p q : ℝ}
    {T : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)}
    (early : ExternalFamilyPrecenterProjectionData T p q)
    (top : Submodule ℚ L) (htop : top ≤ D.filtration.layer s)
    (hpos : 0 < A.law.mass P.productive) where
  code : Fin (finrank ℚ top) → Option early.Freq
  tests : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)
  test_bounds : ∀ x, (tests x).UnitIntervalValued ∧ (tests x).ComplexityLE q ∧
    (tests x).orbit = (T x).orbit
  identity : ∀ x, tests x = (T x).kernelProjection (frequencyCodeKernel top early.eta code)
    ((finiteFrequencyKernel_le top _ _).trans htop)
  invariant : ∀ a (z : D.RealGroup), z.coord ∈ (frequencyCodeKernel top early.eta code).baseChange ℝ →
    ∀ x, (tests a).observable (z • x) = (tests a).observable x
  retained : Finset A.Path
  subset : retained ⊆ P.productive
  mass : A.law.mass P.productive * Real.exp (-q) ≤ A.law.mass retained
  pivots : ∀ a ∈ retained, ∀ i f, code i = some f → Real.exp (-q) <
    ‖(P.precenterChart hpos a).localLaw.complexMean (fun site =>
      weight (A.physical (P.precenterChart hpos a).path site) *
        (early.U f (A.physical (P.precenterChart hpos a).path site)).observable
          ((P.precenterCandidate hpos a).siteValue site))‖
  scores : ∀ a ∈ retained, Real.exp (-q) ≤
    (P.precenterCandidate hpos a).score (fun x => (tests x).observable) weight

namespace PrecenterKernelSelection
variable {P} {p q : ℝ}
    {T : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)}
    {early : ExternalFamilyPrecenterProjectionData T p q}
    {top : Submodule ℚ L} {htop : top ≤ D.filtration.layer s}
    {hpos : 0 < A.law.mass P.productive}
    (selected : P.PrecenterKernelSelection early top htop hpos)

noncomputable def problem :
    AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked
      (fun x => (selected.tests x).observable) weight cost
      (A.law.mass P.productive * Real.exp (-q)) (Real.exp (-q)) :=
  P.restrictObservable (fun x => (selected.tests x).observable) selected.retained selected.subset
    selected.mass (fun a => by
      rw [← P.precenterCandidate_score_mem_eq hpos a.val (selected.subset a.property)]
      exact selected.scores a.val a.property)

@[simp] theorem problem_productive : selected.problem.productive = selected.retained := rfl

end PrecenterKernelSelection
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
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

noncomputable def positiveKernelPreparationExponent : ℕ :=
  Classical.choose (exists_externalFamilyPrecenterProjectionData.{0, 0, 0})

noncomputable def positiveKernelPreparationParameter (p : ℝ) : ℝ :=
  (p + 5) ^ positiveKernelPreparationExponent

noncomputable def positiveKernelPreparationBinLog (p : ℝ) (e : ℕ) : ℝ :=
  (2 * p + positiveKernelPreparationParameter p + 5 + e) ^ e

structure PositiveKernelPreparation (p : ℝ) (e : ℕ) where
  positive_mass : 0 < A.law.mass P.productive
  tests : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)
  tests_observable : ∀ x, (tests x).observable = observable x
  tests_unit : ∀ x, (tests x).UnitIntervalValued
  tests_complexity : ∀ x, (tests x).ComplexityLE (p + 3)
  early : ExternalFamilyPrecenterProjectionData tests (p + 3)
    (positiveKernelPreparationParameter p)
  selected : P.PrecenterKernelSelection early
    (D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap) inf_le_left positive_mass
  binCount : ℕ
  binCount_pos : 0 < binCount
  representative : Fin binCount → integerBox N
  net : ∀ x : integerBox N, ∃ i, ∀ y,
    ‖(tests x.val).observable y - (tests (representative i).val).observable y‖ ≤
      Real.exp (-((p + 3) + positiveKernelPreparationParameter p + 2))
  binCard : (binCount : ℝ) ≤ Real.exp (positiveKernelPreparationBinLog p e)

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
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

structure CommonKeepPositiveKernelPreparation (p : ℝ) (e : ℕ) where
  keep : LayerSamplerVariables G I n B → Prop
  refinement : P.Refinement cost (massThreshold * Real.exp (-p)) scoreThreshold
  hkeep : ∀ z : refinement.problem.productive, (refinement.problem.chart z).keep = keep
  prep : (refinement.problem.withKeep keep hkeep).PositiveKernelPreparation (2 * p) e

namespace CommonKeepPositiveKernelPreparation

variable {P} {p : ℝ} {e : ℕ} (front : P.CommonKeepPositiveKernelPreparation p e)

noncomputable def problem := front.refinement.problem.withKeep front.keep front.hkeep

@[simp] theorem problem_keep (z : front.problem.productive) :
    (front.problem.chart z).keep = front.keep := rfl

end CommonKeepPositiveKernelPreparation
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateLocalFixedCenterFront
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

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

local instance fixedCenterUniversalSiteNonempty : Nonempty A.Site := A.site_nonempty

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

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

local instance actualFixedCenterFrontSiteNonempty : Nonempty A.Site := A.site_nonempty

end PrecenterKernelSelection
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateSelectedDescentRegularity
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

noncomputable def nativeInvariantFamilyDescentExponent (t : ℕ) : ℕ :=
  Classical.choose (exists_idealInvariant_niltest_budget.{0, 0} t)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairLongUniformFactors
namespace OAI

universe u

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
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

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}

local notation "Γ" => A.frozenTaggedContext hpoly hτ1 hξ hσ1 Cgeo hCgeo hchart hsmall
  periodCap coverCap Lip

namespace AllocatedFrozenTaggedPairInput

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := Deck) A cost)
    {LG MG LM : Type u} [LieRing LG] [LieAlgebra ℚ LG]
    [LieRing MG] [LieAlgebra ℚ MG] [LieRing LM] [LieAlgebra ℚ LM]
    {s d e t : ℕ} {D : RationalFilteredNilmanifold LG s d}
    {E : RationalFilteredNilmanifold MG s e} {Fmark : NilpotentLieFiltration LM t}
    {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (reference : D.Niltest (fullTaggedVariableWeight (X := X) J))
    (partner : E.Niltest (fullTaggedVariableWeight (X := X) J))
    (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    {p : ℝ} (hp : 0 ≤ p) (hretained : ∀ i : C.Variables,
      Real.exp (-p) * (A.sides i.val : ℝ) ≤ C.slice.length i)
    (hperiod : ((twist.modulus * twist.cover : ℕ) : ℝ) ≤ Real.exp p)
    (hvariation : (Lip : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
      ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p)
    (hV : reference.ComplexityLE p) (hW : partner.ComplexityLE p)
    (hWnorm : partner.normBound ≤ 1)
    (η : LG →ₗ[ℚ] ℚ) (θ : MG →ₗ[ℚ] ℚ)
    (hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
    (hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
      reference.observable (z • x) = CircleFourier.character
        ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * reference.observable x)
    (hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
      partner.observable (z • x) = CircleFourier.character
        ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * partner.observable x)
    (hK : (Fintype.card C.Variables : ℝ) ≤ p)

def ofCandidate_of_retainedLength
    (hcorr : Real.exp (-p) ≤
      ‖(C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean (fun t =>
        star (twist.eval N poly (C.physical t.val)) *
          (reference.observable (candidate.value t.val) * partner.eval (C.chartValues t.val)))‖) :
    AllocatedFrozenTaggedPairInput Γ Deck C.keep D E p where
  twist := twist
  c := C.centerLift
  a := C.path.1.val
  v := C.path.2.val
  hv := by
    change C.path.2.val ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1
    simpa only [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq]
      using C.path.2.property
  sample := C.sample
  read := C.read
  hread := C.recovered
  fixed := C.fixed
  hfixed := C.fixed_in_box
  q := C.step
  Q := C.slice
  hq := C.step_pos
  hlen := C.slice.length_pos_of_dense C.dense
  hQ := hretained
  V := reference.withOrbit candidate.orbit
  W := partner.integerChartPullback (fun _ : C.Variables => 1) C.integerChart C.integerChart_support
  hp := hp
  hperiod := hperiod
  hvariationBound := hvariation
  hV := hV
  hW := hW
  hWnorm := hWnorm
  η := η
  θ := θ
  hηheight := hηheight
  hθheight := hθheight
  hη := hη
  hθ := hθ
  hK := hK
  hbias := by
    change Real.exp (-p) ≤
      ‖(C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean (fun t =>
        star (twist.eval N poly (integerSampledSpatial C.integerChart t.val)) *
          ((reference.withOrbit candidate.orbit).eval t.val *
            (partner.integerChartPullback (fun _ : C.Variables => 1)
              C.integerChart C.integerChart_support).eval t.val))‖
    simp only [C.integerChart_spatial, Niltest.integerChartPullback_eval,
      Niltest.withOrbit_eval]
    exact hcorr

variable (hcorr : Real.exp (-p) ≤
  ‖(C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean (fun t =>
    star (twist.eval N poly (C.physical t.val)) *
      (reference.observable (candidate.value t.val) * partner.eval (C.chartValues t.val)))‖)

local notation "candidateInput" => ofCandidate_of_retainedLength A hpoly hτ1 hξ hσ1 Cgeo hCgeo hchart hsmall
  C candidate reference partner twist hp hretained hperiod hvariation hV hW hWnorm
  η θ hηheight hθheight hη hθ hK hcorr

@[simp] theorem ofCandidate_of_retainedLength_V_orbit :
    (candidateInput).V.orbit = candidate.orbit := rfl

@[simp] theorem ofCandidate_of_retainedLength_W_orbit :
    (candidateInput).W.orbit =
      (partner.integerChartPullback (fun _ : C.Variables => 1)
        C.integerChart C.integerChart_support).orbit := rfl

end AllocatedFrozenTaggedPairInput

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AllocatedKeptCommonCurrentGradeLocalNiltest
namespace OAI

section

namespace Erdos3
open Module VectorPolynomial Submodule BooleanCubeKernel RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag R σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U btag S hb o hR hσ N poly hm τ ξ stride cells center)

namespace NilpotentLieFiltration

theorem exists_allocated_full_chart_major_correlation_witness_of_frozen_local_niltests
    {k t : ℕ} {L ι η : Type} [Fintype η]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (htk : t < k)
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (pSlice pTest pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hN : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (good : η → Finset A.Path)
    (keep : LayerSamplerVariables G I n B → Prop)
    (cost Bshort : ℝ) (hcost : 0 ≤ cost)
    (hBshort : 1 ≤ Bshort) (hshort : ∀ i, ¬keep i → (A.sides i : ℝ) ≤ Bshort)
    (hξ : ξ ≤ 1)
    (α : ℝ) (hmass : ∀ j, α ≤ (9 / 10 : ℝ) * A.law.mass (good j))
    (hdirect : A.NativeDetection t pSlice pTest pNative α)
    (hslice : max cost (Real.log Bshort) ≤ pSlice)
    (htest : OrdinaryPolynomialPhase.budget t ≤ pTest)
    (strideBound : η → A.Path → ℕ)
    (score : η → A.Path → ({i : LayerSamplerVariables G I n B // keep i} → ℤ) → ℝ)
    (hlocal : ∀ j z, z ∈ good j →
      ∃ fixed : {i // ¬keep i} → ℤ,
        (∀ i, 0 ≤ fixed i ∧ fixed i < A.sides i.val) ∧
      ∃ q : ℕ, 0 < q ∧ q ≤ strideBound j z ∧
      ∃ slice : ResidueBoxSlice (fun i : {i // keep i} => A.sides i.val) q,
        IsDenseCommonStrideBox (fun i : {i // keep i} => A.sides i.val) cost slice.integerPoints ∧
        (𝔼 x : (∀ i : {i // keep i}, Fin (A.sides i.val)),
          score j z (fun i => ((x i).val : ℤ))) ≤
          (𝔼 x ∈ slice.integerPoints, score j z x) ∧
      ∃ T : (OrdinaryPolynomialPhase.nilmanifold t).Niltest (fun _ : {i // keep i} => 1),
        T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget t) ∧
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ slice.integerPoints,
          majorPhasePlateauSignal J k poly c
            (coordinate (basis.coord j).toAddMonoidHom
              (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
                (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord)))
            (jointIntegerPhysicalSite (finiteSplitPoint keep x fixed) (z.1.val, z.2.val)) *
              star (T.eval (commonStrideIndex (fun i => (slice.start i : ℤ)) q x))‖) :
    Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
      Z left right N poly U pMajor Rrank C) := by
  apply exists_allocated_full_chart_major_correlation_witness_of_frozen_local_tests
    A F b ω hF fast basis Z left right htk hpoly c pSlice pTest pNative pMajor Rrank C
    hpNative hη hNativeMajor hproduct hdim hN hRrank hrank good keep cost Bshort
    hcost hBshort hshort hξ α hmass hdirect hslice htest
  intro j z hz
  obtain ⟨fixed, hfixed, q, hq, _, slice, hdense, _, T, hnorm, hcomplex, hcorr⟩ := hlocal j z hz
  let packet : LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t)
      (fun i : {i // keep i} => A.sides i.val) cost (OrdinaryPolynomialPhase.budget t) :=
    { stride := q
      stride_pos := hq
      slice := slice
      dense := hdense
      test := T
      norm := by rw [hnorm]; norm_num
      complexity := hcomplex }
  exact ⟨fixed, hfixed, packet, hcorr⟩

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCanonicalRelativeEndpointBounds
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m q : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.exists_padded_early_late_sampler_geometry
    {pPrep pLate : ℝ} {R D t T : ℕ} (hL : L.PreparedHeights pPrep R)
    (hmq : m ≤ q) (hpPrep : 0 ≤ pPrep) (hR : 1 ≤ R) (hPrepLate : pPrep ≤ pLate)
    (hRLate : (R : ℝ) ≤ Real.exp pLate)
    (hsize : L.Sized D t) (ht : t ≤ T)
    (hcapLate : (preparationCoordinateCap q D T : ℝ) ≤ pLate) :
    let M := preparationCoordinateCap q D T
    ∃ (b : ∀ j, Basis (Fin (preparedSamplerTransverse (L.pad q) j)) ℝ
        (euclideanSubspace (L.pad q j).space)ᗮ)
      (_o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous (L.pad q) j) ℝ
        (euclideanSubspace (L.pad q j).space))
      (bW : ∀ j, Basis (PreparedSamplerContinuous (L.pad q) j) ℤ
        (latticeSection (standardEuclideanLattice (L.pad q j).Coord)
          (euclideanSubspace (L.pad q j).space))),
      (∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (L.pad q j).space)) ∧
      (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (L.pad q j).space) (b j) z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (L.pad q j).space) (b j)).symm z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (L.pad q j).space) (b j) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (L.pad q j).space) (b j) ≤
          Real.exp (allocatedUniformChartLog (M : ℝ))) ∧
      (∀ j a, ‖(bW j a).val‖ ≤
        Real.exp ((pLate + 2) ^ preparedIntegralBasisExponent q)) ∧
      (∀ j i, (basisAxisScale (b j) i : ℝ) ≤
        Real.exp ((pLate + 2) ^ preparedIntegralBasisExponent q)) := by
  exact (hL.pad hmq hpPrep).exists_early_late_sampler_geometry (L.pad q)
    hpPrep hR hPrepLate hRLate (hsize.pad hmq) ht hcapLate

end Erdos3.RankPreparationFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeAutomaticLongGeometry
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ τ : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
    (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ} {v : τ → ℕ}

attribute [local irreducible] realChartSubstitute polynomialOrbitRealChart
  weightedAdaptedRealChartHom

theorem piRealOrbit_polynomialOrbitRealChart_log
    (g : ∀ i, (F i).realification.PolynomialOrbit w)
    (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) :
    (piRealOrbit F (fun i => (F i).polynomialOrbitRealChart w v β hβ (g i))).log =
      realChartSubstitute β (piRealOrbit F g).log := by
  simp only [piRealOrbit, PolynomialOrbit.log, polynomialOrbitOfLog, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change VectorPolynomial.map ((realProductSingle i).restrictScalars ℚ)
    ((F i).polynomialOrbitRealChart w v β hβ (g i)).log =
      realChartSubstitute β
        (VectorPolynomial.map ((realProductSingle i).restrictScalars ℚ) (g i).log)
  rw [polynomialOrbitRealChart_log]
  exact (realChartSubstitute_map β (realProductSingle i) (g i).log).symm

attribute [local irreducible] piRealOrbit

theorem piRealOrbit_polynomialOrbitRealChart_coordinates
    (g : ∀ i, (F i).realification.PolynomialOrbit w)
    (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) :
    (pi F).realification.polynomialOrbitCoordinates v
      (piRealOrbit F (fun i => (F i).polynomialOrbitRealChart w v β hβ (g i))) =
        (pi F).weightedAdaptedRealChartHom w v β hβ
          ((pi F).realification.polynomialOrbitCoordinates w (piRealOrbit F g)) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact (piRealOrbit_polynomialOrbitRealChart_log F g β hβ).trans
    ((pi F).weightedAdaptedRealChartHom_coord w v β hβ
      ((pi F).realification.polynomialOrbitCoordinates w (piRealOrbit F g))).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedCanonicalPaddedSamplerData
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule MeasureTheory VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
    (K : Type) [Fintype K]

structure CanonicalSamplerMeasures where
  lattice : ∀ j, IsZLattice ℝ
    (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))
  coefficientCompact : CompactSpace (CoefficientTorus (K := K) (fun j => (L j).space))
  coefficientBorel : BorelSpace (CoefficientTorus (K := K) (fun j => (L j).space))
  rowCompact : CompactSpace (CoefficientTorus (K := Fin (0 + 1)) (fun j => (L j).space))
  rowBorel : BorelSpace (CoefficientTorus (K := Fin (0 + 1)) (fun j => (L j).space))
  siteBorel : BorelSpace (SiteTorus (Finset (Fin (0 + 1))) (fun j => (L j).space))
  layer : ∀ j, Measure (euclideanSubspace (L j).space ⧸
    (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)).toAddSubgroup)
  layerInvariant : ∀ j, (layer j).IsAddLeftInvariant
  layerProbability : ∀ j, IsProbabilityMeasure (layer j)
  coefficient : Measure (CoefficientTorus (K := K) (fun j => (L j).space))
  coefficientInvariant : coefficient.IsAddLeftInvariant
  coefficientProbability : IsProbabilityMeasure coefficient
  row : Measure (CoefficientTorus (K := Fin (0 + 1)) (fun j => (L j).space))
  rowInvariant : row.IsAddLeftInvariant
  rowProbability : IsProbabilityMeasure row

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

open Module Submodule MeasureTheory VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
    (K : Type) [Fintype K]

structure CanonicalSamplerData (M : ℕ) (pLate : ℝ) where
  measures : L.CanonicalSamplerMeasures K
  b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ
    (euclideanSubspace (L j).space)ᗮ
  o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ
    (euclideanSubspace (L j).space)
  bW : ∀ j, Basis (PreparedSamplerContinuous L j) ℤ
    (latticeSection (standardEuclideanLattice (L j).Coord)
      (euclideanSubspace (L j).space))
  span_eq : ∀ j, span ℤ (Set.range (b j)) =
    projectedIntegerLattice (euclideanSubspace (L j).space)
  chart_bound : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j) z‖ ≤
    Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖
  inverse_chart_bound : ∀ j z,
    ‖(normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j)).symm z‖ ≤
      Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖
  covolume_bound : ∀ j,
    0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ∧
    mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ≤
      Real.exp (allocatedUniformChartLog (M : ℝ))
  integral_basis_bound : ∀ j a, ‖(bW j a).val‖ ≤
    Real.exp ((pLate + 2) ^ preparedIntegralBasisExponent m)
  axis_bound : ∀ j i, (basisAxisScale (b j) i : ℝ) ≤
    Real.exp ((pLate + 2) ^ preparedIntegralBasisExponent m)

end Erdos3.RankPreparationFamily

end

end OAI
end


