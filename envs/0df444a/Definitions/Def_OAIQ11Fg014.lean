-- Prove2me | Definitions.Def_OAIQ11Fg014
-- name    : OAIQ11Fg014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T09:50:56.459345+00:00
-- url     : https://prove2.me/theorems/358a8de7-e671-40de-b01a-53541412c987
-- title:
--   Definitions bundle OAIQ11Fg014 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 18 definitions and 9 theorems. The definitions and types are `OAI.Generator.Tracial.ExactOrderedMoments`, `OAI.Generator.Tracial.IsDimensionSpectralValue`, `OAI.Generator.Tracial.ProductGaps`, `OAI.Generator.Tracial.ReducedOrderedMoments`, `OAI.Generator.Tracial.boundedCornerCenter`, `OAI.Generator.Tracial.boundedCornerScalar`, `OAI.Generator.Tracial.constantSequenceUnitary`, `OAI.Generator.Tracial.coordinateGroupRing`, `OAI.Generator.Tracial.cyclicFamilyValue`, `OAI.Generator.Tracial.cyclicResidualFamily`, `OAI.Generator.Tracial.productCenteredFamily`, `OAI.Generator.Tracial.productFamilyValue`, `OAI.Generator.Tracial.quotientCornerCenter`, `OAI.Generator.Tracial.remainderSequence`, `OAI.Generator.Tracial.residualWordFamily`, `OAI.Generator.Tracial.residualWordValue`, `OAI.Generator.Tracial.sequenceEval`, `OAI.Generator.Tracial.unitaryCoordinate`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_CoordinatePerturbation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/CoordinatePerturbation.lean), [`FactorGeneration_LocalizedStates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LocalizedStates.lean), [`FactorGeneration_NormalTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/NormalTrace.lean), [`FactorGeneration_PerturbationBounds`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/PerturbationBounds.lean), [`FactorGeneration_ProductWords`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ProductWords.lean), [`FactorGeneration_QuotientCorners`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/QuotientCorners.lean), [`FactorGeneration_QuotientRepresentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/QuotientRepresentation.lean), [`FactorGeneration_ResidualMoments`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ResidualMoments.lean), [`FactorGeneration_SpectralDimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralDimension.lean).
--
--   **Imports.** It imports the bundles `OAIQ11Fg009`, `OAIQ11Fg010` and `OAIQ11Fg011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ11Fg015`, `OAIQ11Fg016` and `OAIQ11Fg024`; the statements `OAI_Generator_FiniteMatrixStage_exists_countable_tensor_refinement`, `OAI_Generator_FiniteMatrixStage_exists_refinement_descent`, `OAI_Generator_FiniteMatrixStage_exists_tensor_refinement_descent`, `OAI_Generator_Tracial_SuccessiveCoordinateHaar_haarSequence_quotient`, `OAI_Generator_Tracial_algebraMixedTail_normalize`, `OAI_Generator_Tracial_conditionalExpectation_nonneg`, `OAI_Generator_Tracial_coordinateGroupRing_gram_limits`, `OAI_Generator_Tracial_coordinateGroupRing_quotient_single`, `OAI.Generator.Tracial.exactOrderedMoments_add_of_cyclic`, `OAI.Generator.Tracial.exactOrderedMoments_partial_limit`, `OAI.Generator.Tracial.exists_coordinate_ordered_unitary`, `OAI.Generator.Tracial.exists_coordinate_reduced_unitary`, `OAI_Generator_Tracial_freeGroup_quotient`, `OAI_Generator_Tracial_integerValueWord_closedSpan`, `OAI_Generator_Tracial_integerWord_closed_endpoints`, `OAI_Generator_Tracial_patchPartialSequence_bounded`, `OAI_Generator_Tracial_patchPartialSequence_extends`, `OAI_Generator_Tracial_patchPartialSequence_mem`, `OAI_Generator_Tracial_productFamily_last`, `OAI_Generator_Tracial_productGapList_members`, `OAI_Generator_Tracial_product_reduced_moment`, `OAI_Generator_Tracial_quotient_patch_residual_bound`, `OAI_Generator_Tracial_residualWordFamily_compression_centered`, `OAI_Generator_Tracial_residualWordFamily_contains_outer_run`, `OAI_Generator_Tracial_residualWordFamily_contains_run`, `OAI_Generator_Tracial_sandwich_trace_closedSpan`, `OAI_Generator_Tracial_subalgebra_mem_centered_closedSpan`, `OAI_Generator_Tracial_traceClip_mem_original` and `OAI.Generator.Tracial.tracial_remainder_of_coordinate_moments`; the proofs of `OAI_Generator_Tracial_SuccessiveCoordinateHaar_haarSequence_quotient`, `OAI_Generator_Tracial_algebraMixedTail_normalize`, `OAI_Generator_Tracial_conditionalExpectation_nonneg`, `OAI_Generator_Tracial_conditionalExpectation_norm_le`, `OAI_Generator_Tracial_coordinateGroupRing_gram_limits`, `OAI_Generator_Tracial_coordinateGroupRing_quotient_single`, `OAI.Generator.Tracial.exactOrderedMoments_add_of_cyclic`, `OAI.Generator.Tracial.exactOrderedMoments_partial_limit`, `OAI_Generator_Tracial_exists_component_controlled_refinement`, `OAI_Generator_Tracial_exists_coordinate_haar_endpoints`, `OAI.Generator.Tracial.exists_coordinate_reduced_unitary`, `OAI.Generator.Tracial.exists_eventually_centered_corner_representatives`, `OAI_Generator_Tracial_freeGroup_quotient`, `OAI_Generator_Tracial_integerValueWord_closedSpan`, `OAI_Generator_Tracial_integerWord_closed_endpoints`, `OAI_Generator_Tracial_patchPartialSequence_bounded`, `OAI_Generator_Tracial_patchPartialSequence_extends`, `OAI_Generator_Tracial_patchPartialSequence_mem`, `OAI_Generator_Tracial_productFamily_last`, `OAI_Generator_Tracial_productGapList_members`, `OAI_Generator_Tracial_product_reduced_moment`, `OAI_Generator_Tracial_quotient_patch_residual_bound`, `OAI_Generator_Tracial_residualWordFamily_compression_centered`, `OAI_Generator_Tracial_residualWordFamily_contains_outer_run`, `OAI_Generator_Tracial_residualWordFamily_contains_run`, `OAI_Generator_Tracial_sandwich_trace_closedSpan`, `OAI_Generator_Tracial_subalgebra_mem_centered_closedSpan` and `OAI.Generator.Tracial.tracial_remainder_of_coordinate_moments`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ11Fg009
import Definitions.Def_OAIQ11Fg010
import Definitions.Def_OAIQ11Fg011

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ResidualMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Valid residual-corner identities in the actual quotient. Compression
centering requires two exact moments; global centering alone is insufficient. -/

/-! A countable family containing every original coefficient and every old
nonempty ordered signed word, with both optional endpoints retained. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def residualWordValue (v : Q τ ω) (x : ℕ → Q τ ω) : ResidualWordIndex → Q τ ω
  | .inl i => x i
  | .inr (first,last,xs,s) => optionalCoefficient x first *
      algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++ [(s,optionalCoefficient x last)])

def residualWordFamily (v : Q τ ω) (x : ℕ → Q τ ω) (i : ℕ) : Q τ ω :=
  match Encodable.decode (α := ResidualWordIndex) i with
  | none => 0
  | some k => residualWordValue τ ω v x k

/-! Ordered mixed words grouped at each increment letter. The intervening
old runs are actual members of the previously enumerated residual family. -/

end

/-! Cyclic endpoint correction for residual patching. Outer endpoints are
multiplied before compression, and the scalar part is handled separately. -/
section
open UltrapowerBridge Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def ExactOrderedMoments (w : Q τ ω) (x : ℕ → Q τ ω) : Prop :=
  ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
    quotientTrace τ ω (optionalCoefficient x first * algebraPatchingWord w
      (xs.map (fun a => (a.1,x a.2)) ++ [(s,optionalCoefficient x last)]))=0

end

/-! Countable supported family for actual residual patching, including centered
cyclic products of the two outer blocks. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def quotientCornerCenter (f z : Q τ ω) : Q τ ω :=
  f*z*f-(quotientTrace τ ω (f*z*f)/quotientTrace τ ω f) • f

def cyclicFamilyValue (f : Q τ ω) (y : ℕ → Q τ ω) : CyclicFamilyIndex → Q τ ω
  | .inl i => f*y i*f
  | .inr (a,b) => quotientCornerCenter τ ω f (optionalCoefficient y b*optionalCoefficient y a)

def cyclicResidualFamily (f : Q τ ω) (y : ℕ → Q τ ω) (i : ℕ) : Q τ ω :=
  match Encodable.decode (α := CyclicFamilyIndex) i with
  | none => 0
  | some k => cyclicFamilyValue τ ω f y k

end

/-! Exact preservation of every original ordered moment under orthogonal
patching, once the constructed cyclic residual family has exact moments. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ProductWords
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Exact signed-word expansion for a product of two unitaries. A unit gap
is allowed only between equal signs; opposite signs retain a centered gap. -/

section

open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

/-- Centered coefficients may separate arbitrary signs; unit coefficients may
only separate equal signs. This excludes cancellation through an internal unit. -/
def ProductGaps (x : ℕ → Q τ ω) (s : Bool) : List (Q τ ω × Bool) → Prop
  | [] => True
  | (d,t)::xs => ((∃ i,x i=d) ∨ (d=1 ∧ s=t)) ∧ ProductGaps x t xs

def ReducedOrderedMoments (t : Q τ ω) (x : ℕ → Q τ ω) : Prop :=
  ∀ a b : Option ℕ,∀ s : Bool,∀ xs : List (Q τ ω × Bool),
    ProductGaps τ ω x s xs →
    quotientTrace τ ω (optionalCoefficient x a*betweenWord t s xs (optionalCoefficient x b))=0

end

/-! The actual countable centered coefficients needed to expand words in UV. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def productFamilyValue (u : Q τ ω) (x : ℕ → Q τ ω) : ProductFamilyIndex → Q τ ω
  | .inl i => x i
  | .inr (.inl (s,i)) => if s then star u*optionalCoefficient x i else optionalCoefficient x i*u
  | .inr (.inr i) => star u*x i*u

def productCenteredFamily (u : Q τ ω) (x : ℕ → Q τ ω) (n : ℕ) : Q τ ω :=
  match Encodable.decode (α := ProductFamilyIndex) n with
  | none => 0
  | some i => productFamilyValue τ ω u x i

end

/-! Expand positive-length signed powers into individual letters. Repeated
letters have unit gaps; boundaries between powers retain centered coefficients. -/

open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_QuotientCorners
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Exact coordinate centering in projection corners whose traces have a
uniform positive lower bound. The corner scalar is divided by its actual
trace; no global-centering-to-corner-centering implication is assumed. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem corner_trace_norm_lower (f : Bounded M) (δ : ℝ)
    (hlower : ∀ j,δ ≤ (τ.trace (f.val j)).re) (j : ℕ) :
    δ ≤ ‖τ.trace (f.val j)‖ := (hlower j).trans (Complex.re_le_norm _)

def boundedCornerScalar (f b : Bounded M) (hf : ∀ j,IsStarProjection (f.val j))
    (δ : ℝ) (hδ : 0 < δ) (hlower : ∀ j,δ ≤ (τ.trace (f.val j)).re) : Bounded M :=
  ⟨fun j => (τ.trace (b.val j)/τ.trace (f.val j)) • f.val j,by
    obtain ⟨C,hC,hb⟩ := b.property
    refine ⟨C/δ,div_nonneg hC hδ.le,fun j => ?_⟩
    rw [norm_smul]
    apply (mul_le_of_le_one_right (norm_nonneg _) (hf j).norm_le).trans
    rw [norm_div]
    exact div_le_div₀ hC
      (((τ.norm_trace_le_norm₂ _).trans (τ.norm₂_le_norm _)).trans (hb j))
      hδ (corner_trace_norm_lower τ f δ hlower j)⟩

def boundedCornerCenter (f a : Bounded M) (hf : ∀ j,IsStarProjection (f.val j))
    (δ : ℝ) (hδ : 0 < δ) (hlower : ∀ j,δ ≤ (τ.trace (f.val j)).re) : Bounded M :=
  f*a*f-boundedCornerScalar τ f (f*a*f) hf δ hδ hlower

end

/-! A projection sequence of positive quotient trace can be changed on an
ultrafilter-null set so every coordinate corner has uniformly positive trace.
Coordinates are replaced only by the unit, preserving subalgebra membership. -/
open Filter
open scoped Topology

/-! A projection sequence of positive quotient trace can be changed on an
ultrafilter-null set so every coordinate corner has uniformly positive trace.
Coordinates are replaced only by the unit, preserving subalgebra membership. -/
open Filter
open scoped Topology

/-! Scalar normalization preserves exact corner support and centering. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_QuotientRepresentation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Complete operator-norm bounded sequences and their contractive map to the
actual quotient trace Hilbert space. This map is not asserted injective. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem boundedMap_surjective : Function.Surjective (boundedMap (M := M)) := by
  intro a
  obtain ⟨C, _, hC⟩ := a.property
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroupDiscrete a.val C hC, ?_⟩
  apply Subtype.ext
  funext n
  rfl

end

/-! The faithful constant embedding into the tracial quotient, with its trace and trace norm, for every ultrafilter. -/
open Filter
open scoped Topology

/-! Left multiplication by bounded representatives on the completed trace
Hilbert space. The quotient ideal, not an assumed operator action, determines
which representatives induce the same operator. -/
open Filter
open scoped Topology

/-! Faithful concrete Hilbert-space representation of the tracial quotient
star algebra. Weak operator closedness of its image is not claimed here. -/
open Filter
open scoped Topology

/-! The standard completion/continuous-linear-map structures are not new hypotheses. -/

/-! Fixed-index selection for bounded coordinate representatives. -/
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def sequenceEval (n : ℕ) : Sequences M →ₐ[ℂ] M.toStarSubalgebra where
  toFun a := a n
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CoordinatePerturbation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Group-ring maps from actual bounded unitary coordinates, with quotient
transport and coordinate Gram limits. -/
section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def coordinateGroupRing {A : Type*} (v : A → unitary (Sequences M)) :
    MonoidAlgebra ℂ (FreeGroup A) →ₐ[ℂ] Sequences M :=
  MonoidAlgebra.lift ℂ (Sequences M) (FreeGroup A)
    ((unitary (Sequences M)).subtype.comp (FreeGroup.lift v))

end

/-! Prefix labels and conjugate-word Gram identities for free-group perturbations. -/

section

/-! The finite-prefix analytic bound in the actual bounded-sequence/tracial
quotient realization. Word moments remain explicit premises: no free-Haar
existence or perturbation construction is asserted by this transport theorem. -/
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def remainderSequence (n : ℕ) (α : ℝ)
    (Φ : MonoidAlgebra ℂ (FreeGroup (PrefixLabel n)) →ₐ[ℂ] Sequences M) : Sequences M :=
  ((finitePerturbationRows n α).map (fun r => NormedSpace.exp (Φ r))).prod -
    1 - ((finitePerturbationRows n α).map Φ).sum

end

/-! The literal bounded coordinate model of the finite-prefix free group.
The t_j sequences are the witnesses retained by the successive construction. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def constantSequenceUnitary (u : unitary M.toStarSubalgebra) : unitary (Sequences M) :=
  ⟨constantSequence (u : M.toStarSubalgebra),Unitary.map_mem constantSequence u.property⟩

end

/-! The one literal bounded skew-adjoint perturbation K = i h. Every formal
row is its conjugate by the corresponding actual coordinate prefix. -/
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
open scoped BigOperators

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralDimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite spectral weights of the constructed projection dimension obey an
operator-norm bound. No linear trace on noncommuting elements is assumed. -/

/-! Construct the unique real spectral dimension value of each self-adjoint
operator by norm approximation. Global noncommuting additivity is not asserted. -/
section
open Filter
open scoped BigOperators Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

/-- Approximation specification, not an assumed linear trace. -/
def IsDimensionSpectralValue (x : M.toStarSubalgebra) (t : ℂ) : Prop :=
  ∀ (Q : CornerPartition ⟨1,IsStarProjection.one _⟩) (c : Fin Q.size → ℂ),
    (∀ i, Commute (Q.piece i).val x) →
      ‖t-∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)‖ ≤
        ‖x-∑ i, c i • (Q.piece i).val‖

theorem IsDimensionSpectralValue.unique
    {x : M.toStarSubalgebra} (hx : IsSelfAdjoint x) {s t : ℂ}
    (hs : IsDimensionSpectralValue hfactor hdiff x s)
    (ht : IsDimensionSpectralValue hfactor hdiff x t) : s=t := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply eq_of_all_dyadic_errors
  intro n
  obtain ⟨Q,c,_,hQ,herr⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ x hx (1/2^n) (by positivity)
  have hcomm := hQ x (Commute.refl x) (Commute.one_left x)
  have hs' := hs Q (fun i => (c i : ℂ)) hcomm
  have ht' := ht Q (fun i => (c i : ℂ)) hcomm
  simp only [one_mul,mul_one] at herr
  let w : ℂ := ∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)
  have htri := dist_triangle s w t
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev w t] at htri
  dsimp only [w] at htri
  have hnorm : ‖s-t‖ ≤ 2/2^n := by
    rw [show (2 : ℝ)/2^n=2*(1/2^n) by ring]
    linarith
  simpa only [sub_zero,abs_of_nonneg (norm_nonneg _)] using hnorm

end

/-! The constructed spectral value is bounded and extends the actual
projection dimension. These laws do not assert noncommuting additivity. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem IsDimensionSpectralValue.norm_le {x : M.toStarSubalgebra} {t : ℂ}
    (ht : IsDimensionSpectralValue hfactor hdiff x t) : ‖t‖ ≤ ‖x‖ := by
  have h := ht (CornerPartition.single ⟨1,IsStarProjection.one _⟩) (fun _ => 0)
    (fun _ => Commute.one_left x)
  simpa only [zero_mul,zero_smul,Finset.sum_const_zero,sub_zero] using h

theorem IsDimensionSpectralValue.on_projection (p : AlgebraProjection M) {t : ℂ}
    (ht : IsDimensionSpectralValue hfactor hdiff p.val t) :
    t=(traceFreeDimension hfactor hdiff p : ℂ) := by
  classical
  let r : AlgebraProjection M := ⟨1-p.val,p.property.one_sub⟩
  let a (b : Bool) : AlgebraProjection M := if b then r else p
  have hpr : p.val*r.val=0 := by
    change p.val*(1-p.val)=0
    rw [mul_sub,mul_one,p.property.isIdempotentElem.eq,sub_self]
  have ho (b c : Bool) (hbc : b≠c) : (a b).val*(a c).val=0 := by
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact hpr
    · exact PartialIsometry.orthogonal_reverse p r hpr
    · exact (hbc rfl).elim
  have ha : (∑ b : Bool, (a b).val)=(1 : M.toStarSubalgebra) := by
    change (∑ b : Bool, (if b then r else p).val)=1
    simp only [Fintype.sum_bool,ite_true, if_true,Bool.false_eq_true,ite_false, if_false]
    change (1-p.val)+p.val=1
    abel
  let Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) :=
    CornerPartition.ofFamily a ho ha
  let e : Fin Q.size ≃ Bool := (Fintype.equivFin Bool).symm
  let c (i : Fin Q.size) : ℂ := if e i then 0 else 1
  have hQ (i : Fin Q.size) : Commute (Q.piece i).val p.val := by
    change Commute (a (e i)).val p.val
    cases h : e i
    · exact Commute.refl p.val
    · exact (Commute.one_left p.val).sub_left (Commute.refl p.val)
  have hs : (∑ i, c i • (Q.piece i).val)=p.val := by
    change (∑ i, (if e i then (0 : ℂ) else 1) • (a (e i)).val)=p.val
    exact (Equiv.sum_comp e (fun b : Bool => (if b then (0 : ℂ) else 1) • (a b).val)).trans
      (by simp [a])
  have hw : (∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))=
      (traceFreeDimension hfactor hdiff p : ℂ) := by
    change (∑ i, (if e i then (0 : ℂ) else 1)*
      (traceFreeDimension hfactor hdiff (a (e i)) : ℂ))=_
    exact (Equiv.sum_comp e (fun b : Bool => (if b then (0 : ℂ) else 1)*
      (traceFreeDimension hfactor hdiff (a b) : ℂ))).trans (by simp [a])
  have h := ht Q c hQ
  rw [hs,sub_self,norm_zero] at h
  exact (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))).trans hw

end

/-! Finite-family tests and real homogeneity for the constructed spectral value.
These statements do not assert additivity for noncommuting operators. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem IsDimensionSpectralValue.family_bound {x : M.toStarSubalgebra} {t : ℂ}
    (ht : IsDimensionSpectralValue hfactor hdiff x t)
    {I : Type*} [Fintype I] (q : I → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0)
    (hs : ∑ i, (q i).val=(1 : M.toStarSubalgebra))
    (c : I → ℂ) (hc : ∀ i, Commute (q i).val x) :
    ‖t-∑ i, c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ ≤
      ‖x-∑ i, c i • (q i).val‖ := by
  classical
  let Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) :=
    CornerPartition.ofFamily q ho hs
  let e : Fin Q.size ≃ I := (Fintype.equivFin I).symm
  have h := ht Q (fun i => c (e i)) (fun i => hc (e i))
  change ‖t-∑ i, c (e i)*(traceFreeDimension hfactor hdiff (q (e i)) : ℂ)‖ ≤
    ‖x-∑ i, c (e i) • (q (e i)).val‖ at h
  rw [Equiv.sum_comp e (fun i => c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)),
    Equiv.sum_comp e (fun i => c i • (q i).val)] at h
  exact h

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LocalizedStates
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Localization of actual signed vector/dimension values. Fixed strict
sublevel sets, rather than a limiting strict inequality, supply Zorn bounds. -/
open Filter
open scoped Topology

/-! Tight multiplicative localization of an actual Hilbert vector functional
against the constructed projection dimension. The corner is constructed. -/

/-! Positive spectral approximants inside an actual projection corner, and
extension of localized projection inequalities to positive operators. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.cornerValueCStar
attribute [local instance] OAI.Generator.Tracial.cornerValueOrder
local instance cornerValuePreorder_r512477_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.cornerValueLE
attribute [local instance] OAI.Generator.Tracial.cornerValueStarOrder
theorem IsDimensionSpectralValue.corner_bound
    {x : M.toStarSubalgebra} {t : ℂ} (ht : IsDimensionSpectralValue hfactor hdiff x t)
    (p : AlgebraProjection M) (hpx : Commute p.val x)
    (Q : CornerPartition p) (c : Fin Q.size → ℂ) (hc : ∀ i, Commute (Q.piece i).val x) :
    ‖t-∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)‖ ≤
      ‖x-∑ i, c i • (Q.piece i).val‖ := by
  classical
  let r : AlgebraProjection M := ⟨1-p.val,p.property.one_sub⟩
  let q : Fin Q.size ⊕ Unit → AlgebraProjection M := Sum.elim Q.piece (fun _ => r)
  let d : Fin Q.size ⊕ Unit → ℂ := Sum.elim c (fun _ => 0)
  have ho (i j : Fin Q.size ⊕ Unit) (h : i≠j) : (q i).val*(q j).val=0 := by
    cases i with
    | inl i =>
      cases j with
      | inl j => exact Q.orthogonal i j (fun he => h (congrArg Sum.inl he))
      | inr j =>
        change (Q.piece i).val*(1-p.val)=0
        rw [mul_sub,mul_one,projection_mul_of_le (Q.piece_le i),sub_self]
    | inr i =>
      cases j with
      | inl j =>
        change (1-p.val)*(Q.piece j).val=0
        rw [sub_mul,one_mul,show p.val*(Q.piece j).val=(Q.piece j).val from Q.piece_le j,sub_self]
      | inr j => exact (h (congrArg Sum.inr (Subsingleton.elim i j))).elim
  have hs : (∑ i, (q i).val)=(1 : M.toStarSubalgebra) := by
    simp only [q,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fintype.sum_unique,Q.total]
    change p.val+(1-p.val)=1
    abel
  have hqc (i : Fin Q.size ⊕ Unit) : Commute (q i).val x := by
    cases i with
    | inl i => exact hc i
    | inr i => exact (Commute.one_left x).sub_left hpx
  have hh := ht.family_bound hfactor hdiff q ho hs d hqc
  simpa only [q,d,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,zero_mul,zero_smul,
    Finset.sum_const_zero,add_zero] using hh

end

/-! Projection localization yields actual positive-operator inequalities for
bounded linear functionals, and a nearly cyclic functional on the corner. -/
open scoped BigOperators CStarAlgebra

/-! An actual positive normalized vector functional with arbitrarily small
multiplicative failure of cyclicity on a nonzero corner. No trace is assumed. -/
open scoped CStarAlgebra

/-! A full finite matrix partition can be rebased into every nonzero corner.
The legs are constructed partial isometries, not assumed matrix units. -/
open scoped BigOperators

/-! Extension of a vector functional through actual matrix-partition legs.
Finite coefficient identities transfer the corner quadratic inequality. -/
open scoped BigOperators CStarAlgebra

/-! Globally defined positive unital linear functionals with arbitrarily small multiplicative quadratic trace error. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A genuine linear state with exact equality of real quadratic values,
constructed from the original finite factor predicates by scalar compactness. -/

/-! Construction of a tracial state on the original concrete finite diffuse factor without a supplied trace. -/

/-! Every positive normalized tracial functional agrees with the dimension on
all projections. Lower and upper dyadic bounds use actual partial isometries. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.stateDimensionCStar
attribute [local instance] OAI.Generator.Tracial.stateDimensionOrder
local instance stateDimensionPreorder_r512477_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.stateDimensionLE
attribute [local instance] OAI.Generator.Tracial.stateDimensionStarOrder
theorem tracialFunctional_dyadic_subset_re (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (h1 : φ 1=1) (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    (n : ℕ) (s : Finset (DyadicIndex n)) :
    (φ ((traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n).subset s).val).re=
      dyadicWeight n s := by
  let E := traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n
  have he (i : DyadicIndex n) : (φ (E.leg i).target.val).re=(φ E.base.val).re := by
    exact congrArg Complex.re (tracialFunctional_equivalent φ htrace
      (show (E.leg i).target.Equivalent E.base from
        AlgebraProjection.equivalent_symm ⟨E.leg i,E.initial i,rfl⟩))
  have ht := congrArg (fun x : M.toStarSubalgebra => (φ x).re) E.total
  simp only [map_sum,Complex.re_sum,he,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,card_dyadicIndex,Nat.cast_pow,Nat.cast_ofNat,h1,Complex.one_re] at ht
  have hb : (φ E.base.val).re=1/(2 : ℝ)^n := by
    apply (eq_div_iff (ne_of_gt (pow_pos (by norm_num : (0 : ℝ)<2) n))).mpr
    nlinarith [ht]
  change (φ (E.subset s).val).re=_
  rw [E.subset_val,map_sum,Complex.re_sum]
  simp only [he,hb,Finset.sum_const,nsmul_eq_mul]
  change (s.card : ℝ)*(1/2^n)=(s.card : ℝ)/2^n
  ring

end

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.spectralAdditivityCStar
local instance spectralAdditivityOrder_r512477_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralAdditivityPreorder_r512477_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance spectralAdditivityLE_r512477_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance spectralAdditivityStarOrder_r512477_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
theorem functional_isDimensionSpectralValue (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (hnorm : ‖φ‖ ≤ 1)
    (hproj : ∀ p : AlgebraProjection M, φ p.val=(traceFreeDimension hfactor hdiff p : ℂ))
    (x : M.toStarSubalgebra) : IsDimensionSpectralValue hfactor hdiff x (φ x) := by
  intro Q c _
  have he : φ (∑ i, c i • (Q.piece i).val)=
      ∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
    simp only [map_sum,map_smul,smul_eq_mul,hproj]
  rw [← he,← map_sub]
  simpa only [one_mul] using φ.le_of_opNorm_le hnorm (x-∑ i, c i • (Q.piece i).val)

end

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_PerturbationBounds
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Exact 2 ell signed coefficients in each formal row. In particular the
identity prefix label is still a nonidentity basis letter in the formal group. -/

/-! Exact trace-two-norm of the single common logarithmic perturbation. -/
namespace Tracial

/-! Sharp trace-two-norm displacement of a skew-adjoint exponential, via the
real path t ↦ exp(t K). This proves the scalar-calculus estimate used in the
manuscript without an extra exponential factor. -/

/-! A single coordinate satisfies the size and correlation bounds for the
literal word. Its P-valued unitary letters are the retained construction. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def unitaryCoordinate (a : unitary (Sequences M)) (n : ℕ) : unitary M.toStarSubalgebra :=
  ⟨(a : Sequences M) n,⟨congrArg (fun b : Sequences M => b n) a.property.1,
    congrArg (fun b : Sequences M => b n) a.property.2⟩⟩

end

/-! The manuscript's two perturbation inequalities, constructed under explicit
faithful vector-trace, irreducibility, diffuseness and trace-vector separability
data. No perturbation endpoint or free-moment premise is assumed. -/
open UltrapowerBridge Filter

end Tracial

end Generator

end

end OAI
end


