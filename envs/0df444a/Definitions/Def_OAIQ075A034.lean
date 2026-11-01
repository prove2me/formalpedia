-- Prove2me | Definitions.Def_OAIQ075A034
-- name    : OAIQ075A034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:48:35.644138+00:00
-- url     : https://prove2.me/theorems/af96663c-2bf3-46eb-a2cb-6a3c40a7d98c
-- title:
--   Definitions bundle OAIQ075A034 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 3 definitions and 5 theorems. The definitions and types are `OAI.KadisonSimilarity.dyadicCornerTrace`, `OAI.KadisonSimilarity.generatedUltrapowerOperator`, `OAI.KadisonSimilarity.reducedWordCompressionModel`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`KadisonSimilarity_FreeProduct_DyadicHaarUnitary`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/DyadicHaarUnitary.lean), [`KadisonSimilarity_FreeProduct_FreeCompressionDischarge`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/FreeCompressionDischarge.lean), [`KadisonSimilarity_Representation_FiniteTypeIStructure`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/FiniteTypeIStructure.lean), [`KadisonSimilarity_Tracial_ConcreteRealSequence`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/ConcreteRealSequence.lean), [`KadisonSimilarity_Tracial_FiniteFactorPresentation`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/FiniteFactorPresentation.lean), [`KadisonSimilarity_Tracial_FiniteFactorTrace`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/FiniteFactorTrace.lean), [`KadisonSimilarity_Tracial_UltrapowerGeneratedTransfer`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/UltrapowerGeneratedTransfer.lean).
--
--   **Imports.** It imports the bundles `OAIQ075A027`, `OAIQ075A028`, `OAIQ075A029` and `OAIQ075A030` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ075A036`; the proof of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_from_local_published_inputs`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ075A027
import Definitions.Def_OAIQ075A028
import Definitions.Def_OAIQ075A029
import Definitions.Def_OAIQ075A030

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DyadicHaarUnitary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.BoundedHochschild.WeakSubspace.preannihilator_closed_instance _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCStarQuotient.starSubalgebra_closed _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildCorners.corner_closed _root_.OAI.HochschildMatrixSystems.MatrixSystem.commutant_closed _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerClosed _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.algebra_closed _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

attribute [local instance] OAI.KadisonSimilarity.haarAlgebra_closed
def dyadicCornerTrace (p : AlgebraProjection M) : CStarCorner p.val p.property →L[ℂ] ℂ :=
  ({ toFun := fun a => τ.trace (a : M.toStarSubalgebra)
     map_add' := fun _ _ => inner_add_right _ _ _
     map_smul' := fun _ _ => inner_smul_right _ _ _ } :
    CStarCorner p.val p.property →ₗ[ℂ] ℂ).mkContinuous 1 (fun a => by
      change ‖τ.trace (a : M.toStarSubalgebra)‖ ≤ 1 * ‖(a : M.toStarSubalgebra)‖
      rw [one_mul]
      exact (τ.norm_trace_le_norm₂ (a : M.toStarSubalgebra)).trans
        (τ.norm₂_le_norm (a : M.toStarSubalgebra)))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeCompressionDischarge
attribute [-instance] _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first-letter compression model on the concrete reduced product. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

def reducedWordCompressionModel (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
    (hgen : ReducedWordGenerated G A D) : ReducedWordCompressionModel G A D := by
  let W := freeCompressionHead G A D hτ hf hgen
  let U := W.unitary
  let S := centeredWordSpace G D A false
  let T := leadingWordSpace G D A true
  letI : CompleteSpace S.toSubmodule := S.isClosed.completeSpace_coe
  letI : CompleteSpace T.toSubmodule := T.isClosed.completeSpace_coe
  let j := leadingIntoCentered G D A true
  let v := U.toLinearIsometry.comp T.toSubmodule.subtypeₗᵢ
  let b := U.toLinearIsometry.comp S.toSubmodule.subtypeₗᵢ
  let c := freeCreationIsometry G D A D true rfl hτ hf
  have hST : S.toSubmoduleᗮ = T.toSubmodule :=
    centeredWordSpace_orthogonal G D A hτ hf (reducedWordGenerated_swap G A D hτ hgen) false
  have hp : firstLetterProjection (G.baseVector A 1) (isometryRangeProjection j) =
      isometryRangeProjection v :=
    firstLetterProjection_of_inclusion _ j v (freeCompressionAfterInclusion G A D hτ hf hgen)
  refine {
    tail := centeredWordSpace G D A true
    before := S
    head := W
    tailProjection := isometryRangeProjection j
    projection_adjoint := isometryRangeProjection_adjoint j
    projection_sq := isometryRangeProjection_sq j
    projection_norm := isometryRangeProjection_norm j
    includeBefore := b
    create := U.toLinearIsometry.comp c
    complement := ?_
    create_range := ?_
    create_word := ?_ }
  · change isometryRangeProjection b = 1 - firstLetterProjection (G.baseVector A 1)
      (isometryRangeProjection j)
    rw [hp]
    exact isometryRangeProjection_complement U S T hST
  · intro d hd x
    have hc : c (hilbertTensorInsert (G.baseSymmetryLetter D d hd) x) ∈ T :=
      freeCreationIsometry_mem G D A D true rfl hτ hf _
    let y : T := ⟨_, hc⟩
    change firstLetterProjection (G.baseVector A 1) (isometryRangeProjection j) (v y) = v y
    rw [hp, isometryRangeProjection_apply]
  · intro d hd x
    change U (G.left (d : P) (U.symm (U (x : H)))) =
      U (c (hilbertTensorInsert (G.baseSymmetryLetter D d hd) x))
    rw [U.symm_apply_apply]
    exact congrArg U (freeCreationIsometry_left G D A D true rfl hτ hf d hd x).symm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_UltrapowerGeneratedTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two compressions used in the finite-factor argument are combined
here. The resulting operator on the generated algebra retains commutation,
all prescribed small-corner bounds, and the original commutator norm. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b : A, τA (a * b) = τA (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

local notation "τQ" => quotientTrace τB hB ω trB

variable (L D : StarSubalgebra ℂ (Ultrapower τB hB ω trB))
  [IsClosed (L : Set (Ultrapower τB hB ω trB))]

attribute [local instance] OAI.KadisonSimilarity.generatedAlgebraCStar
attribute [local instance] OAI.KadisonSimilarity.generatedAlgebraOrder
attribute [local instance] OAI.KadisonSimilarity.generatedAlgebraStarOrder
attribute [local instance] OAI.KadisonSimilarity.generatedPreGNSNorm
attribute [local instance] OAI.KadisonSimilarity.generatedGNSNorm
local instance generatedGNSInner_r0db8cb_1 :
    InnerProductSpace ℂ (restrictedPositiveTrace (quotientTrace τB hB ω trB) L).GNS :=
  inferInstance
/-- The concrete operator after Hilbert-ultrapower and generated-algebra
compression. No operator on the generated algebra is chosen independently. -/
def generatedUltrapowerOperator (T : τB.GNS →L[ℂ] τB.GNS) :
    (restrictedPositiveTrace τQ L).GNS →L[ℂ] (restrictedPositiveTrace τQ L).GNS :=
  generatedGNSCompression τQ L (tracialUltrapowerCompression τB hB ω trB T)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConcreteRealSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dyadic signs in a diffuse finite tracial von Neumann algebra form
the real tracial sequence required by the matrix-tower construction. The
underlying projections have compatible dyadic refinements and
orthogonality relations. -/

noncomputable section
namespace KadisonSimilarity

open UltrapowerBridge Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

variable (τ : TracialRepresentation M)
  (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)

theorem concreteRademacher_trace (n : ℕ) :
    concreteTraceLinear τ (concreteRademacher τ hdiff n) = 0 := by
  change τ.trace (dyadicRademacher τ hdiff ⟨1, IsStarProjection.one _⟩ n) = 0
  have h := dyadicRademacher_centered_over_previous τ hdiff
    ⟨1, IsStarProjection.one _⟩ n (fun _ => 1)
  rw [dyadicEval_one τ hdiff ⟨1, IsStarProjection.one _⟩ n] at h
  simpa only [one_mul] using h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FiniteFactorTrace
attribute [-instance] _root_.OAI.KadisonSimilarity.concretePredual_separable _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Faithful normal tracial states on concrete finite factors. The only
structural assumptions are finiteness and a scalar center. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder
open BoundedHochschild BoundedHochschild.KadisonRingrose

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

/-- Finiteness gives a normalized normal trace; a scalar center makes it
faithful. This constructs the finite-factor trace rather than assuming it. -/
theorem exists_faithful_normal_trace [Nontrivial H]
    (hfinite : FiniteAlgebra M.toStarSubalgebra)
    (hfactor : ∀ a : M.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ M.toStarSubalgebra c) :
    ∃ τ : M.toStarSubalgebra →ₚ[ℂ] ℂ,
      TraceInPredual (concretePredualEquiv M) τ ∧ τ 1 = 1 ∧
      (∀ a b, τ (a * b) = τ (b * a)) ∧
      (∀ a, τ (star a * a) = 0 → a = 0) ∧ HasNormalGNS τ := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  let ξ := (‖x‖⁻¹ : ℝ) • x
  have hξ : ‖ξ‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  obtain ⟨τ, hτ, hτ1, htr, _⟩ := exists_normal_tracial_average (concretePredualEquiv M)
    hfinite (vectorPositiveFunctional M ξ) (vectorPositiveFunctional_normal M ξ)
  have h1 : τ 1 = 1 := hτ1.trans (vectorPositiveFunctional_one M ξ hξ)
  refine ⟨τ, hτ, h1, htr, normal_trace_faithful_of_center
    (concretePredualEquiv M) τ hτ htr ?_,
    hasNormalGNS_of_predual (concretePredualEquiv M) τ hτ htr⟩
  intro p _ hcentral hp
  obtain ⟨c, rfl⟩ := hfactor p hcentral
  have hc : c = 0 := by
    simpa only [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_eq_mul, mul_one] using hp
  rw [hc, map_zero]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FiniteTypeIStructure
attribute [-instance] _root_.OAI.KadisonSimilarity.concretePredual_separable _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : VonNeumannAlgebra H)

attribute [local instance] OAI.KadisonSimilarity.finiteTypeIStructureClosed
theorem finiteMatrixFactorModel_of_homogeneous_unit
    (hfactor : ∀ a : P.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ P.toStarSubalgebra c)
    (hhom : HomogeneousTypeICorner (1 : P.toStarSubalgebra)) :
    Nonempty (FiniteMatrixFactorModel P) := by
  obtain ⟨hp, n, E, i, hi⟩ := hhom
  let e := unitCornerEquiv hp
  let E' : MatrixSystem P.toStarSubalgebra n := E.mapEquiv e
  have hi' : FinitePathMain.AbelianProjection (E'.entry i i) := abelian_map_equiv e hi
  let f := (matrixUnitsOfSystem E').hom
  have hsurj : Function.Surjective f :=
    matrixSystem_surjective_of_abelian_diagonal hfactor E' i hi'
  refine ⟨{
    size := n
    size_ne_zero := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
    inclusion := P.toStarSubalgebra.subtype.comp f
    mem := fun a => (f a).property
    surjective := ?_ }⟩
  intro T hT
  obtain ⟨a, ha⟩ := hsurj ⟨T, hT⟩
  exact ⟨a, congrArg Subtype.val ha⟩

/-- A finite factor containing a nonzero abelian projection has the exact
finite matrix model used in the type-I commutator estimate. -/
theorem finiteMatrixFactorModel_of_abelian_projection [Nontrivial H]
    (hfinite : FiniteAlgebra P.toStarSubalgebra)
    (hfactor : ∀ a : P.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ P.toStarSubalgebra c)
    (p : P.toStarSubalgebra) (hp : FinitePathMain.AbelianProjection p) (hp0 : p ≠ 0) :
    Nonempty (FiniteMatrixFactorModel P) := by
  obtain ⟨τ, _, _, htr, hf, _⟩ := exists_faithful_normal_trace P hfinite hfactor
  obtain ⟨z, hz, hz0, hhom⟩ := exists_homogeneous_piece_of_abelian_trace
    (concretePredualEquiv P) τ htr hf hp hp0
  have hz1 : z = 1 := (central_projection_zero_or_one hfactor z hz.1
    (fun a => (hz.2 a).eq)).resolve_left hz0
  exact finiteMatrixFactorModel_of_homogeneous_unit P hfactor (hz1 ▸ hhom)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FiniteFactorPresentation
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite diffuse branch has a constructed normal trace and an actual
irreducible matrix source. Its sole remaining local input is Popa freeness. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open BoundedHochschild.KadisonRingrose
open scoped ComplexOrder

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : VonNeumannAlgebra H)

attribute [instance] FiniteFactorPresentation.normed FiniteFactorPresentation.innerProduct
  FiniteFactorPresentation.complete

attribute [local instance] OAI.KadisonSimilarity.finitePresentationClosed
/-- The structural factor split is proved before invoking any free-position input. -/
theorem factor_structural_cases [Nontrivial H]
    (hfactor : ∀ a : P.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ P.toStarSubalgebra c) :
    IsII1Factor P.toStarSubalgebra ∨ HasInternalIsometryRows P ∨
      Nonempty (FiniteMatrixFactorModel P) := by
  by_cases hfinite : FiniteAlgebra P.toStarSubalgebra
  · by_cases hab : ∃ p : P.toStarSubalgebra, FinitePathMain.AbelianProjection p ∧ p ≠ 0
    · obtain ⟨p, hp, hp0⟩ := hab
      exact Or.inr (Or.inr (finiteMatrixFactorModel_of_abelian_projection P
        hfinite hfactor p hp hp0))
    · left
      refine {
        nonzero := zero_ne_one
        weaklyClosed := vonNeumann_wotClosed P
        factor := fun a ha => hfactor a (fun b => (ha b).symm)
        finite := hfinite
        diffuse := diffuse_projections_of_no_abelian_projection (concretePredualEquiv P) ?_ }
      intro p hp
      by_contra hp0
      exact hab ⟨p, hp, hp0⟩
  · exact Or.inr (Or.inl (internal_isometry_rows_of_infinite_factor P hfactor hfinite))

end KadisonSimilarity

end

end OAI
end


