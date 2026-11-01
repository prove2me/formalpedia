-- Prove2me | Definitions.Def_OAIQ075A012
-- name    : OAIQ075A012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:04:59.152082+00:00
-- url     : https://prove2.me/theorems/b7a05de4-96eb-4c8f-a46b-5c143f5eab7e
-- title:
--   Definitions bundle OAIQ075A012 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 94 declarations of OpenAI's Lean: 40 definitions, 10 instances and 44 theorems. The definitions and types are `OAI.KadisonSimilarity.allPairLabels`, `OAI.KadisonSimilarity.boundedFormOperator`, `OAI.KadisonSimilarity.boundedOperatorForms`, `OAI.KadisonSimilarity.finiteProjectionJoin`, `OAI.KadisonSimilarity.fixedCycleLabelingsEquiv`, `OAI.KadisonSimilarity.grothendieckFamilyLinear`, `OAI.KadisonSimilarity.grothendieckFamilyMap`, `OAI.KadisonSimilarity.haarTwirl`, `OAI.KadisonSimilarity.halfSpectralProjectionElement`, `OAI.KadisonSimilarity.halfTraceProjectionDataOfOrthogonal`, `OAI.KadisonSimilarity.insertedCycleLabelingsEquiv`, `OAI.KadisonSimilarity.internalIsometryRow`, `OAI.KadisonSimilarity.leftSpectralCut`, `OAI.KadisonSimilarity.matrixUnitsOfSystem`, `OAI.KadisonSimilarity.normalRangeSupport`, `OAI.KadisonSimilarity.pairingPolynomial`, `OAI.KadisonSimilarity.partialIsometryCornerMap`, `OAI.KadisonSimilarity.polarPartialIsometry`, `OAI.KadisonSimilarity.polarRangeIsometry`, `OAI.KadisonSimilarity.projectionJoin`, `OAI.KadisonSimilarity.reindexedCycleLabelingsEquiv`, `OAI.KadisonSimilarity.restrictBoundedHom`, `OAI.KadisonSimilarity.restrictStarRepresentation`, `OAI.KadisonSimilarity.roundingCStar`, `OAI.KadisonSimilarity.roundingPreGNSNorm`, `OAI.KadisonSimilarity.sourcePairLabels`, `OAI.KadisonSimilarity.sourcePairingTest`, `OAI.KadisonSimilarity.testPairLabels`, `OAI.KadisonSimilarity.testPairingTest`, `OAI.KadisonSimilarity.tracialWordCoefficient`, `OAI.KadisonSimilarity.weakOperatorIntegral`, `OAI.NaimarkZFC.cyclicPreGNS`, `OAI.NaimarkZFC.gnsOrbit`, `OAI.NaimarkZFC.orbitCLM`, `OAI.NaimarkZFC.orbitMap`, `OAI.NaimarkZFC.peakingExpectation`, `OAI.NaimarkZFC.positiveCLM`, `OAI.NaimarkZFC.positiveOfSquares`, `OAI.NaimarkZFC.restrictState`, `OAI.NaimarkZFC.vectorFunctional`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_Ultrapower`, `KadisonSimilarity_Derivation_BoundedHomRestriction`, `KadisonSimilarity_Derivation_FactorizationGeometry`, `KadisonSimilarity_Derivation_GrothendieckUltrapower`, `KadisonSimilarity_FreeProduct_DyadicHaarUnitary`, `KadisonSimilarity_FreeProduct_HaarSymmetrization`, `KadisonSimilarity_Representation_CountableProjectionJoin`, `KadisonSimilarity_Representation_FiniteTypeIStructure`, `KadisonSimilarity_Representation_NormalSupportTransport`, `KadisonSimilarity_Representation_NormalizedContractions`, `KadisonSimilarity_Representation_PolarPartialIsometry`, `KadisonSimilarity_Representation_ProperlyInfiniteEstimate`, `KadisonSimilarity_Representation_SpectralCutBounds`, `KadisonSimilarity_Representation_SpectralRoundingDischarge`, `KadisonSimilarity_Representation_SpectralStepDischarge`, `KadisonSimilarity_Representation_WeakOperatorCompactness`, `KadisonSimilarity_Representation_WeakOperatorIntegral`, `KadisonSimilarity_Tensor_EndpointPairings`, `KadisonSimilarity_Tensor_InvariantCycles`, `KadisonSimilarity_Tensor_PairingLabels`, `KadisonSimilarity_Tensor_TensorDensity`, `KadisonSimilarity_Tensor_TensorPairings`, `KadisonSimilarity_Tracial_ProjectionJoinTrace`, `KadisonSimilarity_Tracial_TracialHalfProjectionData`, `KadisonSimilarity_Tracial_TracialSmallCornerTransfer`, `Naimark_Basic`, `Naimark_States`, `TracialCohomology_RepresentationLimits`.
--
--   **Imports.** It imports the published bundle `Def_KadisonSimilarity`; the bundles `OAIQ075A000`, `OAIQ075A002`, `OAIQ075A003`, `OAIQ075A004`, `OAIQ075A005` and `OAIQ075A006` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ075A017`; the statement `OAI_KadisonSimilarity_ae_joint_fiber_scalar_center`; the proof of `OAI.BoundedHochschild.KadisonRingrose.factorization_of_complete_bound`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A000
import Definitions.Def_OAIQ075A002
import Definitions.Def_OAIQ075A003
import Definitions.Def_OAIQ075A004
import Definitions.Def_OAIQ075A005
import Definitions.Def_OAIQ075A006

section
-- module Solutions.OAIQ075_KS.Compat
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
instance vonNeumannAlgebraStarOrderedRing {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : StarOrderedRing P :=
  Subtype.starOrderedRing P.toStarSubalgebra
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Ultrapower
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UltrapowerBridge

section
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (l : Filter ℕ)

instance instStarRingTracialQuotient : StarRing (TracialQuotient τ l) where
  star_involutive a := Quotient.inductionOn a (fun a => by
    change quotientMap τ l (star (star a)) = quotientMap τ l a
    rw [star_star])
  star_mul a b := Quotient.inductionOn₂ a b (fun a b => by
    change quotientMap τ l (star (a*b)) = quotientMap τ l (star b*star a)
    rw [star_mul])
  star_add a b := Quotient.inductionOn₂ a b (fun a b => by
    change quotientMap τ l (star (a+b)) = quotientMap τ l (star a+star b)
    rw [star_add])

instance instStarModuleComplexTracialQuotient : StarModule ℂ (TracialQuotient τ l) where
  star_smul c a := Quotient.inductionOn a (fun a =>
    congrArg (quotientMap τ l) (star_smul c a))

end

open Filter
open scoped Topology

end UltrapowerBridge

/-! Commutation with every bounded subalgebra sequence implies uniform coordinate commutator decay. -/
open Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_FactorizationGeometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitIntoClosure_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the kernel of a star intertwiner

A surjective intertwiner with a bounded right inverse restricts to an
isomorphism on the orthogonal complement of its kernel. Orthogonal
projection does not increase the right-inverse norm, which retains the
sharp bound needed for quantitative similarity.
-/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Restriction of a star representation to a closed invariant subspace. -/
def restrictStarRepresentation (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (M : ClosedSubmodule ℂ K)
    (hM : ∀ a x, x ∈ M → σ a x ∈ M) : A →⋆ₐ[ℂ] (M →L[ℂ] M) where
  toFun a := (σ a).restrict (hM a)
  map_zero' := by ext x; simp
  map_one' := by ext x; simp
  map_add' a b := by ext x; simp
  map_mul' a b := by ext x; simp [mul_apply_eq_comp]
  commutes' c := by ext x; simp [Algebra.algebraMap_eq_smul_one]
  map_star' a := by
    let : CompleteSpace M.toSubmodule := M.isClosed.completeSpace_coe
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ (y : K) (σ (star a) (x : K)) =
      inner ℂ y (((σ a).restrict (hM a)).adjoint x)
    rw [map_star, star_eq_adjoint, adjoint_inner_right, adjoint_inner_right]
    rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_BoundedHomRestriction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.boundedHomOrbit_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.listOrbitSum_append _root_.OAI.KadisonSimilarity.listOrbitSum_nil _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitIntoClosure_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.KadisonSimilarity.sharpHom_apply _root_.OAI.KadisonSimilarity.sharpVectorMap_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction of a bounded homomorphism to a closed invariant subspace.
Similarity passes to this restriction through its orthogonal compression. -/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def restrictBoundedHom (π : BoundedUnitalHom A H) (M : ClosedSubmodule ℂ H)
    (hM : ∀ a x, x ∈ M → π.1 a x ∈ M) : BoundedUnitalHom A M := by
  let ρ : A →ₐ[ℂ] (M →L[ℂ] M) := {
    toFun := fun a => (π.1 a).restrict (hM a)
    map_zero' := by ext x; simp
    map_one' := by ext x; simp
    map_add' := by intro a b; ext x; simp
    map_mul' := by intro a b; ext x; simp [mul_apply_eq_comp]
    commutes' := by intro c; ext x; simp [Algebra.algebraMap_eq_smul_one] }
  let f : A →L[ℂ] (H →L[ℂ] H) := ⟨π.1.toLinearMap, π.2⟩
  have hn (a : A) : ‖ρ a‖ ≤ ‖f‖ * ‖a‖ := by
    apply opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro x
    change ‖π.1 a (x : H)‖ ≤ _
    exact ((π.1 a).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (f.le_opNorm a) (norm_nonneg x))
  exact ⟨ρ, AddMonoidHomClass.continuous_of_bound ρ ‖f‖ hn⟩

@[simp] theorem restrictBoundedHom_apply (π : BoundedUnitalHom A H)
    (M : ClosedSubmodule ℂ H) (hM : ∀ a x, x ∈ M → π.1 a x ∈ M) (a : A) (x : M) :
    ((restrictBoundedHom π M hM).1 a x : H) = π.1 a x := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ProperlyInfiniteEstimate
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The properly infinite commutator estimate. Internal orthogonal isometries
supply the row, and Dickson supplies its actual commutator error bounds. -/

noncomputable section
namespace KadisonSimilarity

open scoped CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual row of a finite family of internal isometries. -/
def internalIsometryRow (P : VonNeumannAlgebra H) {n : ℕ} (v : Fin n → P) :
    HilbertCopies H n →L[ℂ] H := sumColumns (fun i => (v i : H →L[ℂ] H))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralStepDischarge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete spectral cut projections

We construct the spectral cuts from the closed range of the positive part.
The construction takes place in the represented Hilbert space; bicommutant
closure proves membership in the given von Neumann algebra.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem rangeSupport_commutes (B T : H →L[ℂ] H)
    (h : Commute B T) (hs : Commute B (star T)) : Commute (rangeSupport B) T := by
  exact Generator.starProjection_commutes_of_invariant _ T
    (fun _ hx => operatorRangeClosure_invariant B T h hx)
    (fun _ hx => operatorRangeClosure_invariant B (star T) hs hx)

theorem rangeSupport_mem (P : VonNeumannAlgebra H) (B : H →L[ℂ] H) (hB : B ∈ P) :
    rangeSupport B ∈ P := by
  suffices rangeSupport B ∈ P.commutant.commutant by simpa using this
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  have h : Commute B T := VonNeumannAlgebra.mem_commutant_iff.mp hT B hB
  have hs : Commute B (star T) := VonNeumannAlgebra.mem_commutant_iff.mp
    (star_mem hT) B hB
  exact (rangeSupport_commutes B T h hs).eq.symm

theorem upperSpectralCut_mem (P : VonNeumannAlgebra H) (A : H →L[ℂ] H)
    (hA : A ∈ P) (t : ℝ) : upperSpectralCut A t ∈ P := by
  apply rangeSupport_mem P
  let : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
    change IsClosed P.carrier
    rw [← P.centralizer_centralizer']
    exact Set.isClosed_centralizer _
  apply cfcₙ_mem (𝕜' := ℂ) (s := P.toStarSubalgebra) (fun x : ℝ => x⁺)
  apply P.toStarSubalgebra.sub_mem hA
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact P.toStarSubalgebra.smul_mem P.one_mem (t : ℂ)

theorem positive_rangeSupport_mem (P : VonNeumannAlgebra H)
    (A : H →L[ℂ] H) (hA : A ∈ P) : rangeSupport A⁺ ∈ P := by
  simpa only [upperSpectralCut, zero_smul, sub_zero] using upperSpectralCut_mem P A hA 0

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_GrothendieckUltrapower
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.constantHilbertInclusion_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded families turn approximate unitary norm attainment into exact
attainment. The source is the ordinary bounded product C-star algebra; only
the Hilbert target needs an ultraproduct. -/

noncomputable section
namespace KadisonSimilarity
open NuclearUltrapower Filter
open scoped ENNReal Topology ComplexOrder

variable {B H : Type*} [CStarAlgebra B] [Nontrivial B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Coordinatewise application, with the ultralimit seminorm on its target. -/
def grothendieckFamilyLinear (ω : Ultrafilter ℕ) (T : B →L[ℂ] H) :
    lp (fun _ : ℕ => B) ∞ →ₗ[ℂ] UltraPreHilbert (fun _ : ℕ => H) ω where
  toFun X := (⟨fun i => T (X i), memℓp_infty ⟨‖T‖ * ‖X‖, by
    rintro _ ⟨i, rfl⟩
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm ENNReal.top_ne_zero X i) (norm_nonneg T))⟩⟩ :
        lp (fun _ : ℕ => H) ∞)
  map_add' X Y := by apply Subtype.ext; funext i; exact map_add T _ _
  map_smul' c X := by apply Subtype.ext; funext i; exact map_smul T _ _

@[simp] theorem grothendieckFamilyLinear_apply (ω : Ultrafilter ℕ) (T : B →L[ℂ] H)
    (X : lp (fun _ : ℕ => B) ∞) (i : ℕ) :
    UltraPreHilbert.family ω (grothendieckFamilyLinear ω T X) i = T (X i) := rfl

/-- The family map into the completed Hilbert ultraproduct. -/
def grothendieckFamilyMap (ω : Ultrafilter ℕ) (T : B →L[ℂ] H) :
    lp (fun _ : ℕ => B) ∞ →L[ℂ] HilbertUltraproduct (fun _ : ℕ => H) ω :=
  UniformSpace.Completion.toComplₗᵢ.toContinuousLinearMap.comp
    ((grothendieckFamilyLinear ω T).mkContinuous ‖T‖ (fun X => by
      apply le_of_tendsto (UltraPreHilbert.norm_tendsto ω _)
      exact Eventually.of_forall fun i =>
        (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          (lp.norm_apply_le_norm ENNReal.top_ne_zero X i) (norm_nonneg T))))

@[simp] theorem grothendieckFamilyMap_apply (ω : Ultrafilter ℕ) (T : B →L[ℂ] H)
    (X : lp (fun _ : ℕ => B) ∞) :
    grothendieckFamilyMap ω T X =
      (grothendieckFamilyLinear ω T X : HilbertUltraproduct (fun _ : ℕ => H) ω) := rfl

@[simp] theorem grothendieckUnitaryFamily_apply (u : ℕ → unitary B) (i : ℕ) :
    (grothendieckUnitaryFamily u : lp (fun _ : ℕ => B) ∞) i = u i := rfl

section Positive
variable [PartialOrder B] [StarOrderedRing B]

attribute [local instance] OAI.KadisonSimilarity.instCStarAlgebraSubtypePreLpNatMemAddSubgroupLpTopENNReal_solutions
local instance instNontrivialSubtypePreLpNatMemAddSubgroupLpTopENNReal_solutions_r727a7b_1 : Nontrivial (lp (fun _ : ℕ => B) ∞) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have he := congrArg (fun X : lp (fun _ : ℕ => B) ∞ => X 0) h
  exact zero_ne_one he
attribute [local instance] OAI.KadisonSimilarity.instPartialOrderSubtypePreLpNatMemAddSubgroupLpTopENNReal_solutions
attribute [local instance] OAI.KadisonSimilarity.instStarOrderedRingSubtypePreLpNatMemAddSubgroupLpTopENNReal_solutions
@[simp] theorem grothendieckRestrict_apply (f : lp (fun _ : ℕ => B) ∞ →ₚ[ℂ] ℂ) (b : B) :
    grothendieckRestrict f b = f (grothendieckConstant b) := rfl

end Positive

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_InvariantCycles
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing centered singleton cycles

A fixed point contributes the trace of its matrix argument. Factorization
of the coordinate contraction shows that vanishing on
centered singleton tails does not require an additional invariant-theory input.
-/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

noncomputable instance permutationCyclesDecidableEq (π : Equiv.Perm ι) :
    DecidableEq (PermutationCycles π) := Classical.decEq _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_PairingLabels
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Disjoint labels for the pairing test

The cycle classes of one perfect matching index disjoint label pools. This
isolates that matching while allowing the labels of same-side pairs to vary.
-/

noncomputable section
namespace KadisonSimilarity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {k l : ℕ}

instance sourcePairClassDecidable (P : PerfectMatching (Fin k ⊕ Fin l))
    (q : PermutationCycles P.1) : Decidable (IsSourcePairClass P q) := Classical.propDecidable _

instance testPairClassDecidable (P : PerfectMatching (Fin k ⊕ Fin l))
    (q : PermutationCycles P.1) : Decidable (IsTestPairClass P q) := Classical.propDecidable _

instance sourcePairClassesFintype (P : PerfectMatching (Fin k ⊕ Fin l)) :
    Fintype (SourcePairClasses P) := Fintype.ofFinite _

instance testPairClassesFintype (P : PerfectMatching (Fin k ⊕ Fin l)) :
    Fintype (TestPairClasses P) := Fintype.ofFinite _

/-- The source tuple uses a variable label on each source-source pair and a
fixed label on each source-test pair. The cycle class separates the pools. -/
def sourcePairLabels (P : PerfectMatching (Fin k ⊕ Fin l)) {M : ℕ}
    (f : SourcePairClasses P → Fin M) (i : Fin k) : PermutationCycles P.1 × ℕ :=
  let q : PermutationCycles P.1 := ⟦Sum.inl i⟧
  (q, if h : IsSourcePairClass P q then (f ⟨q, h⟩).val else 0)

/-- The analogous tuple on the test side. -/
def testPairLabels (P : PerfectMatching (Fin k ⊕ Fin l)) {M : ℕ}
    (g : TestPairClasses P → Fin M) (j : Fin l) : PermutationCycles P.1 × ℕ :=
  let q : PermutationCycles P.1 := ⟦Sum.inr j⟧
  (q, if h : IsTestPairClass P q then (g ⟨q, h⟩).val else 0)

def allPairLabels (P : PerfectMatching (Fin k ⊕ Fin l)) {M : ℕ}
    (f : SourcePairClasses P → Fin M) (g : TestPairClasses P → Fin M)
    (s : Fin k ⊕ Fin l) : PermutationCycles P.1 × ℕ :=
  let q : PermutationCycles P.1 := ⟦s⟧
  (q, if h : IsSourcePairClass P q then (f ⟨q, h⟩).val
    else if h : IsTestPairClass P q then (g ⟨q, h⟩).val else 0)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorPairings
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Hilbert tensor tests excluding same-side pairings

The source and test vectors are finite sums of actual elementary Hilbert
tensors. Their orthonormal summands give the square-root norm growth, whereas
the isolated pairing coefficient grows with the full number of labels.
-/

noncomputable section
namespace KadisonSimilarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {k l : ℕ}

/-- Independent label choices on source-source pairs. -/
def sourcePairingTest (P : PerfectMatching (Fin k ⊕ Fin l))
    (h : PermutationCycles P.1 × ℕ → E) (M : ℕ) : CompletedTensorWord E k := by
  classical
  exact ∑ f : SourcePairClasses P → Fin M,
    completedTensorWord (fun i => h (sourcePairLabels P f i))

/-- Independent label choices on test-test pairs. -/
def testPairingTest (P : PerfectMatching (Fin k ⊕ Fin l))
    (h : PermutationCycles P.1 × ℕ → E) (M : ℕ) : CompletedTensorWord E l := by
  classical
  exact ∑ g : TestPairClasses P → Fin M,
    completedTensorWord (fun j => h (testPairLabels P g j))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorDensity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Passing finite-stage pairing identities to completed tensor words

Continuity and density extend the coefficient identity on a common matrix
stage to arbitrary letters. The final vanishing statement then uses actual
totality of elementary Hilbert tensors.
-/

noncomputable section
namespace KadisonSimilarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual pairing polynomial, with one bilinear factor per pair.
An injective rank function chooses a representative of each pair. -/
def pairingPolynomial (rank : ι → ℕ) (B : E →L[ℂ] E →L[ℂ] ℂ)
    (P : PerfectMatching ι) (v : ι → E) : ℂ :=
  ∏ i ∈ Finset.univ.filter (fun i => rank i < rank (P.1 i)), B (v i) (v (P.1 i))

variable {k l : ℕ}

/-- Coefficients with the test letters conjugated by the tracial involution. -/
def tracialWordCoefficient (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (J : E → E) (v : Fin k ⊕ Fin l → E) : ℂ :=
  inner ℂ (completedTensorWord (fun j => J (v (Sum.inr j))))
    (Y (completedTensorWord (fun i => v (Sum.inl i))))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_EndpointPairings
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Factorization of matrix contractions along pairs

This is the finite combinatorial bridge between the cycle expansion and the
bilinear pairing polynomials: each two-cycle contributes exactly one trace of
a product. The normalization uses the actual number of matching orbits.
-/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

instance matchingRepresentativesFintype (rank : ι → ℕ) (P : PerfectMatching ι) :
    Fintype (MatchingRepresentatives rank P) := Fintype.ofFinite _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DyadicHaarUnitary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Haar unitary in each corner of a diffuse finite tracial von Neumann
algebra, constructed as a norm limit of finite dyadic spectral sums. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge Filter
open scoped BigOperators Topology CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}
  (τ : TracialRepresentation M)
  (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)

local instance haarAlgebra_closed : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) :=
  Generator.Tracial.base_norm_closed M

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_WeakOperatorCompactness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak-operator compactness of a norm ball, obtained from compact scalar
matrix-coefficient discs and the Hilbert-space representation of bounded forms. -/

noncomputable section
namespace KadisonSimilarity

open scoped Topology
open ContinuousLinearMapWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def boundedOperatorForms (R : ℝ) : Set (H → H → ℂ) :=
  {f | IsOperatorForm f ∧ ∀ x y, ‖f x y‖ ≤ R * ‖x‖ * ‖y‖}

def boundedFormOperator (R : ℝ) (f : boundedOperatorForms (H := H) R) :
    H →WOT[ℂ] H :=
  ofCLM (operatorOfForm f.val f.property.1 R f.property.2)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_WeakOperatorIntegral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak operator integrals built from scalar integrals. In particular this
permits averaging a strongly continuous unitary action without assuming
continuity in the operator norm. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory ContinuousLinearMap

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure X) [IsProbabilityMeasure μ]

omit [CompleteSpace H] [IsProbabilityMeasure μ] in
theorem isOperatorForm_integral (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) : IsOperatorForm (integralOperatorForm μ A) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y z
    simp only [integralOperatorForm, map_add, inner_add_left]
    exact integral_add (hA x z) (hA y z)
  · intro c x y
    simp only [integralOperatorForm, map_smul, inner_smul_left]
    exact integral_const_mul (star c) _
  · intro x y z
    simp only [integralOperatorForm, inner_add_right]
    exact integral_add (hA x y) (hA x z)
  · intro c x y
    simp only [integralOperatorForm, inner_smul_right]
    exact integral_const_mul c _

/-- The weak integral of a uniformly bounded, weakly integrable field. -/
def weakOperatorIntegral (A : X → H →L[ℂ] H) (hA : WeaklyIntegrable μ A)
    (R : ℝ) (hbound : ∀ g, ‖A g‖ ≤ R) : H →L[ℂ] H :=
  operatorOfForm (integralOperatorForm μ A) (isOperatorForm_integral μ A hA) R
    (norm_integralOperatorForm_le μ A hbound)

@[simp] theorem weakOperatorIntegral_inner (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) (R : ℝ) (hbound : ∀ g, ‖A g‖ ≤ R) (x y : H) :
    inner ℂ (weakOperatorIntegral μ A hA R hbound x) y =
      ∫ g, inner ℂ (A g x) y ∂μ := operatorOfForm_inner ..

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_HaarSymmetrization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar symmetrization, defined through weak scalar integrals. This applies
to the compact matrix-unitary actions used in the free-product argument. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory ContinuousLinearMap

variable {Γ H K : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (μ : Measure Γ) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]

/-- The Haar average is an actual bounded operator, with its weak integral
constructed through Hilbert-space duality. -/
def haarTwirl (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (T : H →L[ℂ] H) (hI : WeaklyIntegrable μ (unitaryConjugate U T)) : H →L[ℂ] H :=
  weakOperatorIntegral μ (unitaryConjugate U T) hI ‖T‖ (norm_unitaryConjugate_le U hU T)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NormalSupportTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Range supports are preserved by star isomorphisms between concrete von
Neumann algebras. The proof uses their algebraic least-support property, so
no continuity in the weak operator topology is assumed. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The range support viewed as an element of its original normal algebra. -/
def normalRangeSupport (M : VonNeumannAlgebra H) (a : M.toStarSubalgebra) :
    M.toStarSubalgebra := ⟨rangeSupport (a : H →L[ℂ] H), rangeSupport_mem M a a.property⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.Naimark_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u v w
namespace NaimarkZFC


section GNS

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem positive_norm_apply_le (f : A →ₚ[ℂ] ℂ) (a : A) :
    ‖f a‖ ≤ (f 1).re * ‖a‖ := by
  calc
    ‖f a‖ = ‖⟪gnsVector f, f.gnsStarAlgHom a (gnsVector f)⟫_ℂ‖ :=
      congrArg norm (gnsVector_coefficient f a).symm
    _ ≤ ‖gnsVector f‖ * ‖f.gnsStarAlgHom a (gnsVector f)‖ := norm_inner_le_norm _ _
    _ ≤ ‖gnsVector f‖ * (‖f.gnsStarAlgHom a‖ * ‖gnsVector f‖) := by
      gcongr
      exact (f.gnsStarAlgHom a).le_opNorm _
    _ ≤ ‖gnsVector f‖ * (‖a‖ * ‖gnsVector f‖) := by
      gcongr
      exact NonUnitalStarAlgHom.norm_apply_le f.gnsStarAlgHom a
    _ = (f 1).re * ‖a‖ := by rw [← gnsVector_norm_sq]; ring

def positiveCLM (f : A →ₚ[ℂ] ℂ) : A →L[ℂ] ℂ :=
  f.toLinearMap.mkContinuous (f 1).re (positive_norm_apply_le f)

@[simp] theorem positiveCLM_apply (f : A →ₚ[ℂ] ℂ) (a : A) : positiveCLM f a = f a := rfl

theorem positiveCLM_norm (f : A →ₚ[ℂ] ℂ) : ‖positiveCLM f‖ = (f 1).re := by
  have hpos : 0 ≤ f 1 := f.map_nonneg zero_le_one
  apply le_antisymm
  · exact (positiveCLM f).opNorm_le_bound hpos.1 (positive_norm_apply_le f)
  · calc
      (f 1).re = ‖f 1‖ := Complex.re_eq_norm.mpr hpos
      _ = ‖positiveCLM f 1‖ := rfl
      _ ≤ ‖positiveCLM f‖ * ‖(1 : A)‖ := (positiveCLM f).le_opNorm 1
      _ ≤ ‖positiveCLM f‖ * 1 := by
        gcongr
        exact (IsStarProjection.one A).norm_le _
      _ = ‖positiveCLM f‖ := mul_one _

def positiveOfSquares (f : A →L[ℂ] ℂ)
    (hf : ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re) :
    A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ f.toLinearMap fun x hx => by
    have hx' := StarOrderedRing.nonneg_iff.mp hx
    refine AddSubmonoid.closure_induction (fun x hx => ?_) (by simp)
      (fun x y _ _ hx hy => ?_) hx'
    · obtain ⟨a, rfl⟩ := hx
      exact ⟨(hf a).2, (hf a).1.symm⟩
    · simpa only [map_add] using add_nonneg hx hy

@[simp] theorem positiveOfSquares_apply (f : A →L[ℂ] ℂ)
    (hf : ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re) (a : A) :
    positiveOfSquares f hf a = f a := rfl

@[simp] theorem positiveCLM_positiveOfSquares (f : A →L[ℂ] ℂ)
    (hf : ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re) :
    positiveCLM (positiveOfSquares f hf) = f := by ext; rfl

theorem isState_iff (f : A →L[ℂ] ℂ) :
    IsState f ↔ f 1 = 1 ∧
      ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re := by
  constructor
  · rintro ⟨hnorm, hpos⟩
    refine ⟨?_, hpos⟩
    have hre : (f 1).re = 1 := by
      rw [← positiveOfSquares_apply f hpos 1, ← positiveCLM_norm,
        positiveCLM_positiveOfSquares, hnorm]
    have him : (f 1).im = 0 := by simpa using (hpos 1).1
    exact Complex.ext hre him
  · rintro ⟨hone, hpos⟩
    refine ⟨?_, hpos⟩
    have hn := positiveCLM_norm (positiveOfSquares f hpos)
    simpa only [positiveCLM_positiveOfSquares, positiveOfSquares_apply, hone,
      Complex.one_re] using hn

omit [PartialOrder A] [StarOrderedRing A] in

theorem state_norm_apply_le (f : A →L[ℂ] ℂ) (hf : IsState f) (a : A) : ‖f a‖ ≤ ‖a‖ := by
  simpa [hf.1] using f.le_opNorm a

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem starAlgHomCLM_apply (φ : A →⋆ₐ[ℂ] B) (a : A) :
    starAlgHomCLM φ a = φ a := rfl

def restrictState (φ : A →⋆ₐ[ℂ] B) (f : B →L[ℂ] ℂ) : A →L[ℂ] ℂ :=
  f.comp (starAlgHomCLM φ)

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem restrictState_apply (φ : A →⋆ₐ[ℂ] B) (f : B →L[ℂ] ℂ) (a : A) :
    restrictState φ f a = f (φ a) := rfl

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def orbitMap (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) : A →ₗ[ℂ] H where
  toFun a := π a x
  map_add' a b := by simp
  map_smul' c a := by simp

@[simp] theorem orbitMap_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) (a : A) :
    orbitMap π x a = π a x := rfl

def orbitCLM (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) : A →L[ℂ] H :=
  (orbitMap π x).mkContinuous ‖x‖ fun a => by
    calc
      ‖π a x‖ ≤ ‖π a‖ * ‖x‖ := (π a).le_opNorm x
      _ ≤ ‖a‖ * ‖x‖ := mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le π a) (norm_nonneg x)
      _ = ‖x‖ * ‖a‖ := mul_comm _ _

def vectorFunctional (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) : A →L[ℂ] ℂ :=
  (innerSL ℂ x).comp (orbitCLM π x)

@[simp] theorem vectorFunctional_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) (a : A) :
    vectorFunctional π x a = ⟪x, π a x⟫_ℂ := rfl

@[simp] theorem vectorFunctional_square (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) (a : A) :
    vectorFunctional π x (star a * a) = (‖π a x‖ : ℂ) ^ 2 := by
  rw [vectorFunctional_apply, map_mul, map_star]
  change ⟪x, (ContinuousLinearMap.adjoint (π a)) ((π a) x)⟫_ℂ = _
  simp [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]

@[simp] theorem vectorFunctional_one (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1) (x : H) :
    vectorFunctional π x 1 = (‖x‖ : ℂ) ^ 2 := by
  simp [hone, inner_self_eq_norm_sq_to_K]

variable [PartialOrder A] [StarOrderedRing A]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[simp] theorem dominatedPreGNS_apply (f g : A →ₚ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (g (star a * a)).re ≤ C * (f (star a * a)).re) (a : A) :
    dominatedPreGNS f g C hC hdom (f.toPreGNS a) = g.toPreGNS a := rfl

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def cyclicPreGNS (f : A →ₚ[ℂ] ℂ) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ) : f.PreGNS →ₗᵢ[ℂ] H where
  toLinearMap := (orbitMap π ξ).comp f.ofPreGNS.toLinearMap
  norm_map' x := by
    change ‖π (f.ofPreGNS x) ξ‖ = √(f (star (f.ofPreGNS x) * f.ofPreGNS x)).re
    rw [hcoeff, map_mul, map_star]
    change ‖π (f.ofPreGNS x) ξ‖ =
      √(⟪ξ, (π (f.ofPreGNS x)).adjoint (π (f.ofPreGNS x) ξ)⟫_ℂ).re
    rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    rw [← RCLike.ofReal_pow]
    change ‖π (f.ofPreGNS x) ξ‖ = √(‖π (f.ofPreGNS x) ξ‖ ^ 2)
    exact (Real.sqrt_sq (norm_nonneg _)).symm

@[simp] theorem cyclicPreGNS_apply (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ) (a : A) :
    cyclicPreGNS f π ξ hcoeff (f.toPreGNS a) = π a ξ := rfl

end GNS

section FaithfulMoments

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def gnsOrbit (f : A →ₚ[ℂ] ℂ) : A →L[ℂ] f.GNS :=
  LinearMap.mkContinuous
    { toFun := fun a => f.gnsStarAlgHom a (gnsVector f)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
    ‖gnsVector f‖ fun a => by
      calc
        ‖f.gnsStarAlgHom a (gnsVector f)‖ ≤ ‖f.gnsStarAlgHom a‖ * ‖gnsVector f‖ :=
          (f.gnsStarAlgHom a).le_opNorm _
        _ ≤ ‖a‖ * ‖gnsVector f‖ := by
          gcongr
          exact NonUnitalStarAlgHom.norm_apply_le _ _
        _ = ‖gnsVector f‖ * ‖a‖ := mul_comm _ _

@[simp] theorem gnsOrbit_apply (f : A →ₚ[ℂ] ℂ) (a : A) :
    gnsOrbit f a = (f.toPreGNS a : f.GNS) := gns_apply_vector f a

@[simp] theorem gnsOrbit_norm (f : A →ₚ[ℂ] ℂ) (a : A) :
    ‖gnsOrbit f a‖ = Real.sqrt (f (star a * a)).re := by
  simp only [gnsOrbit_apply, Completion.norm_coe, PositiveLinearMap.preGNS_norm_def,
    PositiveLinearMap.ofPreGNS_toPreGNS]

end FaithfulMoments

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.Naimark_States
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

variable {A : Type*} [CStarAlgebra A] (e : A) (he : IsStarProjection e)

open scoped ComplexOrder InnerProductSpace
open UniformSpace
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem isClosed_weakStates : IsClosed (weakStates A) := by
  have hone : IsClosed {f : WeakDual ℂ A | f 1 = 1} :=
    isClosed_eq (WeakDual.eval_continuous 1) continuous_const
  have hpos (a : A) : IsClosed {f : WeakDual ℂ A |
      (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re} :=
    (isClosed_eq (Complex.continuous_im.comp (WeakDual.eval_continuous _)) continuous_const).inter
      (isClosed_le continuous_const (Complex.continuous_re.comp (WeakDual.eval_continuous _)))
  have h := hone.inter (isClosed_iInter hpos)
  simpa only [weakStates, isState_iff, WeakDual.toStrongDual_apply, Set.ofPred_and,
    Set.ofPred_forall] using h

theorem isCompact_weakStates : IsCompact (weakStates A) := by
  apply (WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 1).of_isClosed_subset
    isClosed_weakStates
  intro f hf
  change f.toStrongDual ∈ Metric.closedBall 0 1
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact le_of_eq hf.1

theorem state_eq_one_of_projection_le (f : A →L[ℂ] ℂ) (hf : IsState f)
    (p q : A) (hq : IsStarProjection q) (hpq : p ≤ q) (hfp : f p = 1) : f q = 1 := by
  have hmono := (positiveOfSquares f hf.2).monotone
  apply le_antisymm
  · have hh := hmono hq.le_one
    change f q ≤ f 1 at hh
    rwa [((isState_iff f).mp hf).1] at hh
  · have hh := hmono hpq
    change f p ≤ f q at hh
    rwa [hfp] at hh

theorem Peaks.tendsto_supported {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (g : ℕ → A →L[ℂ] ℂ) (hg : ∀ n, IsState (g n)) (hgn : ∀ n, g n (p n) = 1) :
    Tendsto (fun n => StrongDual.toWeakDual (g n)) atTop (𝓝 (StrongDual.toWeakDual f)) := by
  apply isCompact_weakStates.tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall hg)
  intro k hk hcluster
  apply WeakDual.toStrongDual.injective
  apply hp.2.2.2.2 _ hk
  intro m
  have hclosed : IsClosed {z : WeakDual ℂ A | z (p m) = 1} :=
    isClosed_eq (WeakDual.eval_continuous _) continuous_const
  apply hclosed.mem_of_mapClusterPt hcluster
  filter_upwards [eventually_ge_atTop m] with n hn
  exact state_eq_one_of_projection_le (g n) (hg n) (p n) (p m) (hp.1 m) (hp.2.1 hn) (hgn n)

theorem Peaks.tendsto_supported_apply {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (g : ℕ → A →L[ℂ] ℂ) (hg : ∀ n, IsState (g n)) (hgn : ∀ n, g n (p n) = 1) (a : A) :
    Tendsto (fun n => g n a) atTop (𝓝 (f a)) :=
  ((WeakDual.eval_continuous a).tendsto _).comp (hp.tendsto_supported g hg hgn)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem cornerState_isState (f : A →L[ℂ] ℂ) (hf : IsState f)
    (p : A) (hp : IsStarProjection p) (hpos : 0 < (f p).re) : IsState (cornerState f p) := by
  apply (isState_iff _).mpr
  constructor
  · rw [cornerState_apply, mul_one, hp.isIdempotentElem.eq, state_projection_real f hf p hp]
    simp only [Complex.ofReal_re]
    rw [Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hpos), Complex.ofReal_one]
  · intro a
    have heq : p * (star a * a) * p = star (a * p) * (a * p) := by
      rw [star_mul, hp.isSelfAdjoint.star_eq]
      noncomm_ring
    rw [cornerState_apply, heq]
    simp only [Complex.smul_im, Complex.smul_re, smul_eq_mul,
      (hf.2 (a * p)).1, mul_zero, true_and]
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt hpos)) (hf.2 (a * p)).2

theorem Peaks.tendsto_atomState {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a : A) :
    Tendsto (fun n => cornerState τ (peakAtom p n) a) atTop (𝓝 (f a)) := by
  apply hp.tendsto_supported_apply
  · intro n
    exact cornerState_isState τ hτ _ (hp.peakAtom_projection n) (hpos n)
  · intro n
    exact cornerState_eq_one τ hτ _ _ (hp.peakAtom_projection n) (hp.1 n)
      (hp.peakAtom_le n) (hpos n)

open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped ComplexOrder InnerProductSpace ComplexStarModule
open UniformSpace

open scoped Topology
open Filter

variable {A : Type*} [CStarAlgebra A] {ι : Type*}

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem Peaks.summable_expectationTail {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a : A) :
    Summable (fun n => (cornerState τ (peakAtom p n) a - f a) • peakAtom p n) :=
  summable_orthogonalProjection _ hp.peakAtom_projection hp.peakAtom_orthogonal _
    (by simpa using (hp.tendsto_atomState τ hτ hpos a).sub_const (f a))

theorem Peaks.peakingExpectationFun_add {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a b : A) :
    peakingExpectationFun p f τ (a + b) =
      peakingExpectationFun p f τ a + peakingExpectationFun p f τ b := by
  have heq (n : ℕ) :
      (cornerState τ (peakAtom p n) (a+b) - f (a+b)) • peakAtom p n =
        (cornerState τ (peakAtom p n) a - f a) • peakAtom p n +
        (cornerState τ (peakAtom p n) b - f b) • peakAtom p n := by
    rw [map_add, map_add, add_sub_add_comm, add_smul]
  simp only [peakingExpectationFun, peakDiagonal]
  simp_rw [heq]
  rw [(hp.summable_expectationTail τ hτ hpos a).tsum_add
    (hp.summable_expectationTail τ hτ hpos b), map_add, add_smul]
  abel

theorem Peaks.norm_peakingExpectationFun_le {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a : A) :
    ‖peakingExpectationFun p f τ a‖ ≤ ‖a‖ := by
  exact hp.norm_peakDiagonal_le hp0 _ _ (hp.tendsto_atomState τ hτ hpos a) _ (norm_nonneg _)
    (state_norm_apply_le _ hp.2.2.1 _)
    (fun n => state_norm_apply_le _ (cornerState_isState _ hτ _ (hp.peakAtom_projection n)
      (hpos n)) _)

def peakingExpectation {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) : A →L[ℂ] A :=
  LinearMap.mkContinuous
    { toFun := peakingExpectationFun p f τ
      map_add' := hp.peakingExpectationFun_add τ hτ hpos
      map_smul' := peakingExpectationFun_smul p f τ }
    1 (fun a => by
      change ‖peakingExpectationFun p f τ a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using hp.norm_peakingExpectationFun_le hp0 τ hτ hpos a)

@[simp] theorem peakingExpectation_apply {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a : A) :
    peakingExpectation hp hp0 τ hτ hpos a = peakingExpectationFun p f τ a := rfl

open scoped ComplexOrder MatrixOrder CStarAlgebra
open Matrix

open scoped CStarAlgebra

open Filter Topology
open scoped ComplexOrder ComplexStarModule

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_RepresentationLimits
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Representation limits for bounded Hochschild cohomology. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaPatching.Rep
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaCorners
variable {G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

instance instPartialOrder : PartialOrder (Rep G M) where
  le v w := v.support ≤ w.support ∧ ∀ g, w g*v.support=v g
  le_refl v := ⟨le_rfl,v.mul_support⟩
  le_trans v w z hvw hwz := by
    refine ⟨hvw.1.trans hwz.1,fun g => ?_⟩
    have hp := (v.support_projection.le_iff_mul_eq_right w.support_projection).mp hvw.1
    calc
      z g*v.support = z g*(w.support*v.support) := by rw [hp]
      _ = v g := by rw [←mul_assoc,hwz.2,hvw.2]
  le_antisymm v w hvw hwv := by
    apply ext; intro g
    have hp := le_antisymm hvw.1 hwv.1
    simpa only [hp,w.mul_support] using (hvw.2 g).symm

end PopaPatching.Rep

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_PolarPartialIsometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete right supports in a finite tracial von Neumann algebra

The partial isometry is constructed by extending the isometry
`sqrt(x* x) ξ ↦ x ξ` from its dense range and setting it to zero on the
orthogonal complement. Bicommutant closure keeps that operator in the algebra.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Isometry from the initial closed range to the ambient Hilbert space. -/
def polarRangeIsometry (x : H →L[ℂ] H) : operatorRangeClosure (polarModulus x) →ₗᵢ[ℂ] H :=
  x.toLinearMap.extendOfIsometry (rangeIntoClosure_dense (polarModulus x))
    (fun ξ => (polarModulus_norm_apply x ξ).symm)

@[simp] theorem polarRangeIsometry_apply (x : H →L[ℂ] H) (ξ : H) :
    polarRangeIsometry x (rangeIntoClosure (polarModulus x) ξ) = x ξ :=
  LinearMap.extendOfIsometry_eq _ _ _ _

/-- The actual partial isometry, extended by zero. -/
def polarPartialIsometry (x : H →L[ℂ] H) : H →L[ℂ] H :=
  (polarRangeIsometry x).toContinuousLinearMap.comp
    (operatorRangeClosure (polarModulus x)).orthogonalProjectionOnto

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialSmallCornerTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small-corner commutator estimate transports along a partial isometry
in the algebra commuting with the implementing operator. Projection
comparison then supplies that partial isometry in the prescribed factor. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

/-- The final support condition and the initial projection identity imply
that the partial isometry lands in the requested corner. -/
theorem mul_eq_self_of_final_projection (e f v : P) (hf : IsStarProjection f)
    (hv : star v * v = f) (hev : e * (v * star v) = v * star v) : e * v = v := by
  have hvf := mul_initial_projection f v hf hv
  calc
    e * v = e * (v * f) := by rw [hvf]
    _ = (e * (v * star v)) * v := by rw [← hv]; noncomm_ring
    _ = (v * star v) * v := by rw [hev]
    _ = v * f := by rw [← hv]; noncomm_ring
    _ = v := hvf

/-- Conjugation by the partial isometry is an actual ambient corner element. -/
def partialIsometryCornerMap (e f : P) (he : IsStarProjection e) (hf : IsStarProjection f)
    (v : P) (hv : star v * v = f) (hev : e * (v * star v) = v * star v)
    (z : CStarCorner f hf) : CStarCorner e he :=
  ⟨v * (z : P) * star v, by
    have hel := mul_eq_self_of_final_projection e f v hf hv hev
    have her : star v * e = star v := by
      simpa only [star_mul, he.isSelfAdjoint.star_eq] using congrArg star hel
    constructor
    · rw [← mul_assoc, ← mul_assoc, hel]
    · rw [mul_assoc, her]⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralRoundingDischarge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The one-half spectral rounding inequality

The cutoff is the support of the positive part of `2a-1`.  Its polynomial
order inequality implies the required L² inequality for every positive
functional on a concrete von Neumann algebra.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem halfSpectralProjection_mem (P : VonNeumannAlgebra H)
    (a : H →L[ℂ] H) (ha : a ∈ P) : halfSpectralProjection a ∈ P :=
  positive_rangeSupport_mem P _ (P.toStarSubalgebra.sub_mem
    (by simpa only [two_mul] using P.toStarSubalgebra.add_mem ha ha) P.one_mem)

section VonNeumann
variable (P : VonNeumannAlgebra H)

/-- The spectral projection as an element of the von Neumann algebra. -/
def halfSpectralProjectionElement (a : P.toStarSubalgebra) : P.toStarSubalgebra :=
  ⟨halfSpectralProjection a, halfSpectralProjection_mem P a a.property⟩

local instance roundingCStar : CStarAlgebra P.toStarSubalgebra := {}
attribute [local instance] OAI.KadisonSimilarity.roundingOrder
local instance roundingStarOrder : StarOrderedRing P.toStarSubalgebra :=
  Subtype.starOrderedRing P.toStarSubalgebra

local instance roundingCFC_r727a7b_1 :
    NonUnitalContinuousFunctionalCalculus ℝ P.toStarSubalgebra IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
local instance roundingDecompose_r727a7b_1 : SelfAdjointDecompose P.toStarSubalgebra where
  exists_nonneg_sub_nonneg {a} ha :=
    ⟨a⁺, a⁻, CFC.posPart_nonneg a, CFC.negPart_nonneg a, (CFC.posPart_sub_negPart a ha).symm⟩
variable (τ : P.toStarSubalgebra →ₚ[ℂ] ℂ)
local instance roundingPreGNSNorm : SeminormedAddCommGroup τ.PreGNS :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := τ.preGNSpreInnerProdSpace)

end VonNeumann

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ProjectionJoinTrace
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite joins of projections and their trace bound. These elementary
support identities are used to control countable unions of small spectral
projections in the normal representation argument. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Join formed from the orthogonal part of the second projection. -/
def projectionJoin (M : VonNeumannAlgebra H) (p q : M.toStarSubalgebra) :
    M.toStarSubalgebra := p + normalRangeSupport M ((1 - p) * q)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CountableProjectionJoin
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable projection joins with the trace bound inherited from finite
unions. Only the concrete faithful vector trace is used for the limit. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def finiteProjectionJoin (M : VonNeumannAlgebra H)
    (p : ℕ → M.toStarSubalgebra) : ℕ → M.toStarSubalgebra
  | 0 => 0
  | n + 1 => projectionJoin M (finiteProjectionJoin M p n) (p n)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralCutBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative high spectral cuts. The discarded part has small operator
norm, and positivity bounds the trace of the retained projection. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Trace
open Filter
open scoped Topology

/-- The high left spectral cut of an element of the normal algebra. -/
def leftSpectralCut (M : VonNeumannAlgebra H) (x : M.toStarSubalgebra) (ε : ℝ) :
    M.toStarSubalgebra :=
  ⟨upperSpectralCut ((x : H →L[ℂ] H) * star (x : H →L[ℂ] H)) (ε ^ 2),
    upperSpectralCut_mem M _
      (M.toStarSubalgebra.mul_mem x.property (M.toStarSubalgebra.star_mem' x.property)) _⟩

end Trace
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NormalizedContractions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Naturality of normalized permutation contractions under trace-preserving
matrix algebra maps, proved by deleting one permutation vertex at a time. -/

noncomputable section
namespace KadisonSimilarity

open Finset

universe u
variable {ι : Type u} {α β : Type*} [Fintype ι] [decι : DecidableEq ι]

/-- Removing an inserted vertex preserves the set of cycle-constant labels. -/
def insertedCycleLabelingsEquiv (p : Equiv.Perm ι) (b : ι) (β : Type*) :
    CycleConstantLabelings (insertPermutationVertex p b) β ≃ CycleConstantLabelings p β where
  toFun f := ⟨fun i => f.1 (some i), by
    intro i
    by_cases hi : i = b
    · subst i
      have h₀ := f.2 none
      have hb := f.2 (some b)
      simp only [insertPermutationVertex_none] at h₀
      simp only [insertPermutationVertex_self] at hb
      exact h₀.trans hb
    · simpa only [insertPermutationVertex_other p b i hi] using f.2 (some i)⟩
  invFun f := ⟨fun i => i.elim (f.1 b) f.1, by
    intro i
    cases i with
    | none => simpa only [insertPermutationVertex_none, Option.elim_some, Option.elim_none] using f.2 b
    | some i =>
      by_cases hi : i = b
      · subst i
        simp
      · simp only [insertPermutationVertex_other p b i hi, Option.elim_some]
        exact f.2 i⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    cases i with
    | none =>
      have h := f.2 (some b)
      simpa only [insertPermutationVertex_self, Option.elim_none] using h.symm
    | some i => rfl
  right_inv f := rfl

/-- A new fixed point contributes an independent constant label. -/
def fixedCycleLabelingsEquiv (p : Equiv.Perm ι) (β : Type*) :
    CycleConstantLabelings p.optionCongr β ≃ β × CycleConstantLabelings p β where
  toFun f := (f.1 none, ⟨fun i => f.1 (some i), fun i => f.2 (some i)⟩)
  invFun f := ⟨fun i => i.elim f.1 f.2.1, by
    intro i
    cases i with
    | none => rfl
    | some i => exact f.2.2 i⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    cases i <;> rfl
  right_inv f := rfl

variable [Fintype α] [DecidableEq α]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Vertex reindexing does not change cycle-constant labels. -/
def reindexedCycleLabelingsEquiv (e : ι ≃ κ) (p : Equiv.Perm ι) (β : Type*) :
    CycleConstantLabelings (e.permCongr p) β ≃ CycleConstantLabelings p β where
  toFun f := ⟨fun i => f.1 (e i), by
    intro i
    simpa only [Equiv.permCongr_apply, e.symm_apply_apply] using f.2 (e i)⟩
  invFun f := ⟨fun i => f.1 (e.symm i), by
    intro i
    simpa only [Equiv.permCongr_apply, e.symm_apply_apply] using f.2 (e.symm i)⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    exact congrArg f.1 (e.apply_symm_apply i)
  right_inv f := by
    apply Subtype.ext
    funext i
    exact congrArg f.1 (e.symm_apply_apply i)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialHalfProjectionData
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered reflection used by the dihedral test is constructed from a
half-trace projection. Completing a smaller projection by an orthogonal
projection of the complementary trace supplies that projection; no centered
symmetry is assumed in this algebraic step. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

/-- Completing a small corner by an orthogonal complement of the missing
trace produces a half-trace projection containing the original corner. -/
def halfTraceProjectionDataOfOrthogonal (τ : P →ₗ[ℂ] ℂ) {e q : P}
    (he : IsStarProjection e) (hq : IsStarProjection q) (heq : e * q = 0)
    {t : ℂ} (hetrace : τ e = t) (hqtrace : τ q = 1 / 2 - t) :
    HalfTraceProjectionData τ e where
  projection := e + q
  isProjection := he.add hq heq
  trace_half := by rw [map_add, hetrace, hqtrace]; ring
  left_support := by
    have hqe : q * e = 0 := by
      simpa only [star_mul, he.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, star_zero]
        using congrArg star heq
    rw [add_mul, he.isIdempotentElem.eq, hqe, add_zero]
  right_support := by rw [mul_add, he.isIdempotentElem.eq, heq, add_zero]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FiniteTypeIStructure
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite factor with a nonzero abelian projection is a full matrix algebra.
The homogeneous central piece is the unit because the center is scalar. -/

noncomputable section
namespace KadisonSimilarity

open BoundedHochschild.KadisonRingrose HochschildCorners HochschildMatrixSystems
open scoped ComplexOrder

def matrixUnitsOfSystem {A : Type*} [CStarAlgebra A] {n : ℕ}
    (E : MatrixSystem A n) : Generator.MatrixUnitSystem (Fin n) A where
  entry := E.entry
  star_entry := E.star_entry
  mul_entry := E.entry_mul
  total := E.sum_diagonal

universe u

end KadisonSimilarity

end

end OAI
end


