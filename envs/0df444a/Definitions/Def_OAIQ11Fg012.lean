-- Prove2me | Definitions.Def_OAIQ11Fg012
-- name    : OAIQ11Fg012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T09:45:31.975138+00:00
-- url     : https://prove2.me/theorems/550de31b-126f-4bd1-a5b3-712f0d2ebd52
-- title:
--   Definitions bundle OAIQ11Fg012 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 80 declarations of OpenAI's Lean: 27 definitions, 3 instances and 50 theorems. The definitions and types are `OAI.Generator.Tracial.CornerPartition.fromRepresentedCorner`, `OAI.Generator.Tracial.PartialUnitary.fromRepresentedCorner`, `OAI.Generator.Tracial.conditionalExpectationCLM`, `OAI.Generator.Tracial.cornerCentered`, `OAI.Generator.Tracial.cornerCompress`, `OAI.Generator.Tracial.cornerCompressOperator`, `OAI.Generator.Tracial.cornerEmbedding`, `OAI.Generator.Tracial.functionalSubspaceEvaluationLinear`, `OAI.Generator.Tracial.functionalSubspaceWeakBall`, `OAI.Generator.Tracial.functionalSubspaceWeakEvaluation`, `OAI.Generator.Tracial.maskPartialSequence`, `OAI.Generator.Tracial.normalizedCornerVector`, `OAI.Generator.Tracial.patchPartialSequence`, `OAI.Generator.Tracial.projectionInSubalgebra`, `OAI.Generator.Tracial.relativeGenerated`, `OAI.Generator.Tracial.relativeTraceSpace`, `OAI.Generator.Tracial.representedCorner`, `OAI.Generator.Tracial.representedCornerTrace`, `OAI.Generator.Tracial.representedSubcorner`, `OAI.Generator.Tracial.signedCornerUnitary`, `OAI.Generator.Tracial.subalgebraResidual`, `OAI.Generator.Tracial.traceFreeDyadicReference`, `OAI.Generator.Tracial.traceFreeDyadicSibling`, `OAI.Generator.Tracial.unitResidualPatch`, `OAI.Generator.embeddedCoefficientMap`, `OAI.Generator.perturbationRows`, `OAI.Generator.rowSignedWord`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_CornerIndependence`, `FactorGeneration_CornerTrace`, `FactorGeneration_CyclicPredual`, `FactorGeneration_Dimension`, `FactorGeneration_DyadicComparison`, `FactorGeneration_Expectations`, `FactorGeneration_FiniteComparison`, `FactorGeneration_LocalPatches`, `FactorGeneration_LocalizedStates`, `FactorGeneration_LongWords`, `FactorGeneration_PartialUnitaries`, `FactorGeneration_PerturbationBounds`, `FactorGeneration_RelativeGeneration`, `FactorGeneration_RepresentedCorners`, `FactorGeneration_ResidualCompletion`, `FactorGeneration_SpectralStates`, `FactorGeneration_SpectralTruncation`.
--
--   **Imports.** It imports the published bundle `Def_FactorGeneration`; the bundles `OAIQ11Fg007`, `OAIQ11Fg008`, `OAIQ11Fg009` and `OAIQ11Fg010` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ11Fg020`; the statements `OAI_Generator_Tracial_conjugateWord_formula`, `OAI_Generator_Tracial_conjugate_reduced_word_zero`, `OAI_Generator_Tracial_coordinateGroupRing_gram_limits`, `OAI_Generator_Tracial_coordinateGroupRing_quotient_single`, `OAI.Generator.Tracial.exists_strict_admissible_unit_patch`, `OAI_Generator_Tracial_freeGroup_quotient`, `OAI.Generator.Tracial.representedCorner_factor`, `OAI.Generator.Tracial.representedCorner_irreducible`, `OAI_Generator_Tracial_unitaryRepresentation_gram`, `OAI_Generator_Tracial_unitaryRepresentation_mk` and `OAI_Generator_Tracial_unitaryRepresentation_prefix`; the proofs of `OAI.Generator.FiniteMatrixStage.exists_irreducible_matrix_generated_II1`, `OAI.Generator.FiniteMatrixStage.exists_matrix_generated_centered_partition`, `OAI_Generator_Tracial_conjugateWord_formula`, `OAI_Generator_Tracial_conjugate_reduced_word_zero`, `OAI_Generator_Tracial_coordinateGroupRing_gram_limits`, `OAI_Generator_Tracial_coordinateGroupRing_quotient_single`, `OAI.Generator.Tracial.exists_irreducible_matrix_energy_descent`, `OAI.Generator.Tracial.exists_irreducible_two_generated_subfactor`, `OAI.Generator.Tracial.exists_strict_admissible_unit_patch`, `OAI.Generator.Tracial.exists_supported_corner_partial_sequence`, `OAI.Generator.Tracial.exists_unitResidual_local_compression`, `OAI_Generator_Tracial_freeGroup_quotient`, `OAI.Generator.Tracial.predualFunctional_mem_cyclicPredual`, `OAI.Generator.Tracial.representedCorner_factor`, `OAI.Generator.Tracial.representedCorner_irreducible`, `OAI_Generator_Tracial_unitaryRepresentation_gram`, `OAI_Generator_Tracial_unitaryRepresentation_mk` and `OAI_Generator_Tracial_unitaryRepresentation_prefix`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ11Fg007
import Definitions.Def_OAIQ11Fg008
import Definitions.Def_OAIQ11Fg009
import Definitions.Def_OAIQ11Fg010

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CornerTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Trace estimates in the actual ambient algebra. The corner scalar uses
its normalized trace. These estimates do not assume or assert the existence
of a local-quantizing projection. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def cornerCentered (p : AlgebraProjection M) (x : M.toStarSubalgebra) : M.toStarSubalgebra :=
  p.val*x*p.val - cornerScalar τ p x • p.val

end

/-! Actual noncommutative L1 on the coordinate algebra: trace(sqrt(x* x)).
The supported L2-to-L1 estimate retains the square root of the support trace.
No quantizing projection or conditional expectation theorem is assumed. -/

/-! A finite compression-energy estimate yields a nonzero corner projection with simultaneous L1 control. -/

/-! The scalar trace estimate for a term with two supported patch letters.
It reduces to the actual compressed middle coefficient and keeps trace(q),
not trace(p), as the scale of the error. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_PartialUnitaries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Popa's extension order on actual supported partial unitaries, and its
exact L2 distance identity. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace PartialUnitary

theorem support_le_of_extends {v w : PartialUnitary M} (h : Extends v w) :
    v.support ≤ w.support := by
  have hv : w.support.val*v.val=v.val := by
    calc w.support.val*v.val = w.support.val*(w.val*v.support.val) := by rw [h]
         _ = v.val := by rw [← mul_assoc,w.unitary.support_mul]; exact h
  change w.support.val*v.support.val=v.support.val
  calc w.support.val*v.support.val = w.support.val*(v.val*star v.val) := by rw [v.unitary.final]
       _ = v.support.val := by rw [← mul_assoc,hv,v.unitary.final]

theorem extends_refl (v : PartialUnitary M) : Extends v v := v.unitary.mul_support

theorem extends_trans {u v w : PartialUnitary M} (huv : Extends u v) (hvw : Extends v w) :
    Extends u w := by
  change w.val*u.support.val=u.val
  calc w.val*u.support.val = w.val*(v.support.val*u.support.val) := by
         rw [show v.support.val*u.support.val=u.support.val from support_le_of_extends huv]
       _ = u.val := by rw [← mul_assoc,hvw,huv]

instance instPartialOrder : PartialOrder (PartialUnitary M) where
  le := Extends
  le_refl := extends_refl
  le_trans _ _ _ := extends_trans
  le_antisymm v w hvw hwv := by
    apply ext
    have hs := le_antisymm (support_le_of_extends hvw) (support_le_of_extends hwv)
    change w.val*v.support.val=v.val at hvw
    rw [hs,w.unitary.mul_support] at hvw
    exact hvw.symm

end PartialUnitary

end

/-! Actual L2 limits of partial unitaries and upper bounds of increasing
sequences, using their exact support-trace distance. -/

/-! Actual orthogonal corner unitaries from dyadic trace cuts. These supply
weakly vanishing scalar matrix coefficients for the scalar-commutant case
of Popa's coordinate nonintertwining criterion. -/

/-! Popa 1308.3982v3, §1.5, scalar-target specialization. The sequence is
constructed from actual dyadic trace cuts in each nonzero corner; neither
nonintertwining nor Haar existence is an assumption. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralTruncation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Positivity of the tracial pairing does not require the two positive
operators to commute. These estimates will control spectral truncation. -/

/-! Upper spectral truncation of a self-adjoint operator. The truncation
remains in the original operator ball and has a positive discarded part. -/

/-! Spectral truncation forces a self-adjoint least-distance point in a
subalgebra ball to have norm at most the norm of the ambient test operator. -/

/-! Two-sided spectral clipping and trace-norm control. The auxiliary trace
is explicit; the trace-free construction supplies it on its actual closure. -/
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.clippingCStar
local instance clippingOrder_rdd429d_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance clippingStarOrder_rdd429d_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
theorem traceClip_distance (τ : TracialRepresentation M) (a x : M.toStarSubalgebra)
    (ha : IsSelfAdjoint a) (hx : IsSelfAdjoint x) :
    τ.norm₂ (traceClip a ‖x‖-x) ≤ τ.norm₂ (a-x) := by
  have h₁ := upperTruncate_distance τ a x ha hx
  have h₂ := upperTruncate_distance τ (-upperTruncate a ‖x‖) (-x)
    (upperTruncate_selfAdjoint a ha ‖x‖).neg hx.neg
  rw [norm_neg] at h₂
  have hn (b : M.toStarSubalgebra) : τ.norm₂ (-b) = τ.norm₂ b := norm_neg _
  have he : traceClip a ‖x‖-x = -(upperTruncate (-upperTruncate a ‖x‖) ‖x‖-(-x)) := by
    dsimp [traceClip]; abel
  have he' : -upperTruncate a ‖x‖-(-x) = -(upperTruncate a ‖x‖-x) := by abel
  rw [he',hn] at h₂
  rw [he,hn]
  have hnonneg : 0 ≤ τ.norm₂ (a-x) := norm_nonneg _
  nlinarith [sq_nonneg (τ.norm₂ ((a-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺)),
    sq_nonneg (τ.norm₂ ((-upperTruncate a ‖x‖-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺))]

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The orthogonal subalgebra representative of a self-adjoint ambient
operator is constructed, with its operator norm bound. -/

/-! A bounded trace-preserving subalgebra projection from self-adjoint least-distance points. Tracial orthogonality gives uniqueness and the bimodule identities. -/
section
open scoped ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem conditionalExpectation_mem (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    (conditionalExpectation τ hNM x).val ∈ N :=
  (exists_bounded_subalgebra_representative τ hNM x).choose_spec.1
theorem conditionalExpectation_bound (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    ‖conditionalExpectation τ hNM x‖ ≤ 2*‖x‖ :=
  (exists_bounded_subalgebra_representative τ hNM x).choose_spec.2.1
theorem conditionalExpectation_orthogonal (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-conditionalExpectation τ hNM x) :=
  (exists_bounded_subalgebra_representative τ hNM x).choose_spec.2.2

theorem conditionalExpectation_eq_of_orthogonal (hNM : N ≤ M)
    (x y : M.toStarSubalgebra) (hy : y.val ∈ N)
    (h : TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-y)) :
    conditionalExpectation τ hNM x=y :=
  subalgebra_representative_unique τ x _ y (conditionalExpectation_mem τ hNM x) hy
    (conditionalExpectation_orthogonal τ hNM x) h

theorem conditionalExpectation_add (hNM : N ≤ M) (x y : M.toStarSubalgebra) :
    conditionalExpectation τ hNM (x+y)=conditionalExpectation τ hNM x+conditionalExpectation τ hNM y := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact N.add_mem (conditionalExpectation_mem τ hNM x) (conditionalExpectation_mem τ hNM y)
  · have h := (conditionalExpectation_orthogonal τ hNM x).add τ
      (conditionalExpectation_orthogonal τ hNM y)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    abel

theorem conditionalExpectation_smul (hNM : N ≤ M) (z : ℂ) (x : M.toStarSubalgebra) :
    conditionalExpectation τ hNM (z • x)=z • conditionalExpectation τ hNM x := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact N.smul_mem (conditionalExpectation_mem τ hNM x) z
  · simpa only [smul_sub] using (conditionalExpectation_orthogonal τ hNM x).smul τ z

def conditionalExpectationCLM (hNM : N ≤ M) : M.toStarSubalgebra →L[ℂ] M.toStarSubalgebra :=
  LinearMap.mkContinuous
    { toFun := conditionalExpectation τ hNM
      map_add' := conditionalExpectation_add τ hNM
      map_smul' := conditionalExpectation_smul τ hNM }
    2 (conditionalExpectation_bound τ hNM)

end

/-! The constructed expectation preserves adjoints, is a bimodule map,
and is the orthogonal projection for the trace norm. -/

/-! Positivity of the constructed expectation. The negative spectral part
is an actual subalgebra test operator; tracial orthogonality eliminates it. -/

/-! The constructed expectation satisfies the Schwarz inequality and is
contractive in operator norm. -/

/-! Actual nested subalgebras satisfy the expectation tower identity.
The resulting energy identity is the decreasing-subfactor step of A.1.2. -/

/-! Conditional expectations onto a decreasing sequence of actual
subalgebras converge in L2. This supplies the limiting argument in A.1.2;
it does not construct that source's decreasing subfactors. -/
open Filter
open scoped Topology BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_RepresentedCorners
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed _root_.OAI.Generator.predualFunctionals_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual corner on pH. Extension by zero identifies its operators with
supported ambient operators; weak closedness is proved by WOT continuity. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (p : AlgebraProjection M)

def representedCorner : VonNeumannAlgebra (cornerSpace p) :=
  vonNeumannOfWOTClosed (cornerStarAlgebra p) (cornerStarAlgebra_wotClosed p)

def cornerEmbedding : (representedCorner p).toStarSubalgebra →⋆ₙₐ[ℂ] M.toStarSubalgebra where
  toFun a := ⟨cornerExtend p a.val,a.property⟩
  map_zero' := Subtype.ext (cornerExtend_zero p)
  map_add' a b := Subtype.ext (cornerExtend_add p a.val b.val)
  map_mul' a b := Subtype.ext (cornerExtend_mul p a.val b.val)
  map_smul' c a := Subtype.ext (cornerExtend_smul p c a.val)
  map_star' a := Subtype.ext (cornerExtend_star p a.val)

theorem cornerEmbedding_injective : Function.Injective (cornerEmbedding p) := by
  intro a b h
  exact Subtype.ext (cornerExtend_injective p (congrArg Subtype.val h))

@[simp] theorem cornerEmbedding_one : cornerEmbedding p 1=p.val :=
  Subtype.ext (cornerExtend_one p)
@[simp] theorem cornerEmbedding_left (a : (representedCorner p).toStarSubalgebra) :
    p.val*cornerEmbedding p a=cornerEmbedding p a := Subtype.ext (cornerExtend_left p a.val)
@[simp] theorem cornerEmbedding_right (a : (representedCorner p).toStarSubalgebra) :
    cornerEmbedding p a*p.val=cornerEmbedding p a := Subtype.ext (cornerExtend_right p a.val)

/-! Compression and extension are inverse on supported operators. -/

def cornerCompressOperator (x : H →L[ℂ] H) : cornerSpace p →L[ℂ] cornerSpace p :=
  (cornerProject p).comp (x.comp (cornerSpace p).subtypeL)

@[simp] theorem cornerCompressOperator_apply (x : H →L[ℂ] H) (y : cornerSpace p) :
    (cornerCompressOperator p x y).val=p.val.val (x y.val) := rfl

theorem cornerExtend_compress (x : H →L[ℂ] H) :
    cornerExtend p (cornerCompressOperator p x)=p.val.val*x*p.val.val := by ext y; rfl

@[simp] theorem cornerCompress_extend (x : cornerSpace p →L[ℂ] cornerSpace p) :
    cornerCompressOperator p (cornerExtend p x)=x := by
  apply cornerExtend_injective p
  rw [cornerExtend_compress,cornerExtend_left,cornerExtend_right]

def cornerCompress (x : M.toStarSubalgebra) : (representedCorner p).toStarSubalgebra :=
  ⟨cornerCompressOperator p x.val,by
    change cornerExtend p (cornerCompressOperator p x.val) ∈ M
    rw [cornerExtend_compress]
    exact M.mul_mem (M.mul_mem p.val.property x.property) p.val.property⟩

@[simp] theorem cornerEmbedding_compress (x : M.toStarSubalgebra) :
    cornerEmbedding p (cornerCompress p x)=p.val*x*p.val := Subtype.ext (cornerExtend_compress p x.val)

@[simp] theorem cornerCompress_embedding (x : (representedCorner p).toStarSubalgebra) :
    cornerCompress p (cornerEmbedding p x)=x := Subtype.ext (cornerCompress_extend p x.val)

end

/-! The normalized faithful vector trace on the actual corner pH. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (p : AlgebraProjection M)

theorem corner_norm₂_pos (hp : p.val ≠ 0) : 0 < τ.norm₂ p.val :=
  lt_of_le_of_ne (norm_nonneg _) (fun h => hp ((τ.norm₂_eq_zero_iff _).mp h.symm))

def normalizedCornerVector : cornerSpace p :=
  ((τ.norm₂ p.val : ℂ)⁻¹) • cornerProject p τ.vector

theorem normalizedCornerVector_norm (hp : p.val ≠ 0) : ‖normalizedCornerVector τ p‖=1 := by
  change ‖((τ.norm₂ p.val : ℂ)⁻¹) • cornerProject p τ.vector‖=1
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ τ.norm₂ p.val from norm_nonneg _)]
  change (τ.norm₂ p.val)⁻¹*τ.norm₂ p.val=1
  exact inv_mul_cancel₀ (corner_norm₂_pos τ p hp).ne'

theorem normalizedCornerVector_pairing (a : (representedCorner p).toStarSubalgebra) :
    inner ℂ (normalizedCornerVector τ p) (a.val (normalizedCornerVector τ p))=
      ((τ.norm₂ p.val : ℂ)^2)⁻¹ * τ.trace (cornerEmbedding p a) := by
  simp only [normalizedCornerVector,map_smul,inner_smul_left,inner_smul_right,
    map_inv₀,Complex.conj_ofReal]
  rw [cornerProject_inner]
  change (τ.norm₂ p.val : ℂ)⁻¹*((τ.norm₂ p.val : ℂ)⁻¹*τ.trace (cornerEmbedding p a))=_
  ring

def representedCornerTrace (hp : p.val ≠ 0) : TracialRepresentation (representedCorner p) where
  vector := normalizedCornerVector τ p
  norm_vector := normalizedCornerVector_norm τ p hp
  cyclic a b := by
    change inner ℂ (normalizedCornerVector τ p) ((a*b).val (normalizedCornerVector τ p))=
      inner ℂ (normalizedCornerVector τ p) ((b*a).val (normalizedCornerVector τ p))
    rw [normalizedCornerVector_pairing,normalizedCornerVector_pairing,map_mul,map_mul,τ.trace_mul_comm]
  separating a ha := by
    apply cornerEmbedding_injective p
    rw [map_zero]
    apply τ.separating
    have h : ((τ.norm₂ p.val : ℂ)⁻¹) • (a.val (cornerProject p τ.vector))=0 := by
      simpa only [normalizedCornerVector,map_smul] using ha
    have hscalar : (τ.norm₂ p.val : ℂ)⁻¹ ≠ 0 :=
      inv_ne_zero (Complex.ofReal_ne_zero.mpr (corner_norm₂_pos τ p hp).ne')
    have hz := (smul_eq_zero.mp h).resolve_left hscalar
    exact congrArg Subtype.val hz

end

/-! Subcorner inclusion, inherited diffuseness/irreducibility, and L2 separability. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (p : AlgebraProjection M)

def projectionInSubalgebra (hpN : p.val.val ∈ N) : AlgebraProjection N :=
  ⟨⟨p.val.val,hpN⟩,⟨Subtype.ext (congrArg (fun a : M.toStarSubalgebra => a.val) p.property.isIdempotentElem.eq),
    Subtype.ext (congrArg (fun a : M.toStarSubalgebra => a.val) p.property.isSelfAdjoint.star_eq)⟩⟩

/-- Both corners act on the same pH; only the membership predicate changes. -/
def representedSubcorner (hpN : p.val.val ∈ N) : VonNeumannAlgebra (cornerSpace p) :=
  representedCorner (projectionInSubalgebra p hpN)

theorem representedSubcorner_le (hpN : p.val.val ∈ N) (hNM : N ≤ M) :
    representedSubcorner p hpN ≤ representedCorner p := fun _ h => hNM h

end

/-! Transport actual unit partitions on pH to ambient partitions of p. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (p : AlgebraProjection M)
namespace CornerPartition
variable (Q : CornerPartition (identityProjection (representedCorner p)))

def fromRepresentedCorner : CornerPartition p where
  size := Q.size
  piece i := ⟨cornerEmbedding p (Q.piece i).val,(Q.piece i).property.map (cornerEmbedding p)⟩
  orthogonal i j hij := by
    change cornerEmbedding p (Q.piece i).val*cornerEmbedding p (Q.piece j).val=0
    rw [← map_mul,Q.orthogonal i j hij,map_zero]
  total := by
    change (∑ i,cornerEmbedding p (Q.piece i).val)=p.val
    rw [← map_sum,Q.total]
    exact cornerEmbedding_one p

end CornerPartition

end

/-! Actual centered pNp pinching partitions and local pieces. The corner,
normalized trace, structural properties, and separability are constructed. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LocalPatches
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Construct local patches in the actual f=1 residual. Both residual trace
terms are retained. Admissibility of the full extended word family is not asserted. -/

/-! A single actual residual patch controls every finite internal word of the
source family. All scalar moment premises are proved from admissibility. -/

/-! Trace estimates for each actual binary-mask term, using the constructed
finite families. No moment estimate or middle-family extraction is assumed. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def signedCornerUnitary {q : AlgebraProjection M} (w : CornerUnitary q) (s : Bool) :
    CornerUnitary q := if s then w.adjoint else w

@[simp] theorem signedCornerUnitary_val {q : AlgebraProjection M} (w : CornerUnitary q) (s : Bool) :
    (signedCornerUnitary w s).val=signedLetter w.val s := by cases s <;> rfl

end

/-! Strict support growth for the actual f=1 admissible set. The single patch
is chosen from the finite coefficient families before any word is tested. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem unitResidual_orthogonal (v : PartialUnitary M) (q : AlgebraProjection M)
    (hq : q ≤ unitResidual v) : v.support.val*q.val=0 := by
  change (1-v.support.val)*q.val=q.val at hq
  have hh : q.val-v.support.val*q.val=q.val := by simpa only [sub_mul,one_mul] using hq
  exact sub_eq_self.mp hh

def unitResidualPatch (v : PartialUnitary M) (q : AlgebraProjection M) (w : CornerUnitary q)
    (hq : q ≤ unitResidual v) : PartialUnitary M :=
  ⟨⟨v.support.val+q.val,v.support.property.add q.property (unitResidual_orthogonal v q hq)⟩,
    v.unitary.patch w (unitResidual_orthogonal v q hq)⟩

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CornerIndependence
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Extension of actual partial unitaries and ordered words from pH.
The empty word maps to p, so word transport retains a final p. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (p : AlgebraProjection M)

def PartialUnitary.fromRepresentedCorner (v : PartialUnitary (representedCorner p)) :
    PartialUnitary M where
  support := ⟨cornerEmbedding p v.support.val,v.support.property.map (cornerEmbedding p)⟩
  unitary := ⟨cornerEmbedding p v.val, by
    exact (congrArg (fun x => x * cornerEmbedding p v.val)
      (map_star (cornerEmbedding p) v.val).symm).trans
        ((map_mul (cornerEmbedding p) (star v.val) v.val).symm.trans
          (congrArg (cornerEmbedding p) v.unitary.initial)), by
    exact (congrArg (fun x => cornerEmbedding p v.val * x)
      (map_star (cornerEmbedding p) v.val).symm).trans
        ((map_mul (cornerEmbedding p) v.val (star v.val)).symm.trans
          (congrArg (cornerEmbedding p) v.unitary.final))⟩

end

/-! Finite partial independence in every nonzero represented subcorner,
with actual ambient support, membership and trace estimates. -/

/-! Ordered-word transport with ambient unit endpoints, and contractive
compression of supported centered coefficients. -/

/-! Diagonal partial independence in genuinely varying Hilbert-space corners.
The result retains an actual ambient partial-unitary sequence. -/
open Filter
open scoped Topology

/-! Actual coordinate partial-unitary witnesses in supported corners, followed
by exact quotient moments and the ambient quarter-support bound. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CyclicPredual
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A concrete candidate predual: the norm-closed complex span of vector
functionals from the faithful cyclic trace representation, with completeness,
separability, and an isometric evaluation map. -/

/-! Every functional in the constructed norm-closed vector-functional space is
weak-operator continuous on each bounded ball of the original algebra. -/
open Filter
open scoped Topology

/-! Recover every functional on the constructed predual from an actual algebra
element, using compact bounded balls and weak-dual Hahn--Banach separation. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

instance predualWeakLocallyConvex : LocallyConvexSpace ℝ (WeakDual ℂ (cyclicPredual τ)) :=
  inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ (cyclicPredual τ))))

end

/-! Evaluation surjectivity for any subspace of bounded-unit-ball WOT-continuous
functionals. Compactness and Hahn--Banach supply actual algebra elements. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (F : Submodule ℂ (StrongDual ℂ M.toStarSubalgebra))

@[simp] theorem functionalSubspaceEvaluation_apply (a : M.toStarSubalgebra) (f : F) :
    functionalSubspaceEvaluation F a f = f.val a := rfl

def functionalSubspaceEvaluationLinear : M.toStarSubalgebra →ₗ[ℂ] StrongDual ℂ F where
  toFun := functionalSubspaceEvaluation F
  map_add' a b := by ext f; exact map_add f.val a b
  map_smul' c a := by ext f; exact map_smul f.val c a

def functionalSubspaceWeakEvaluation : M.toStarSubalgebra →ₗ[ℂ] WeakDual ℂ F :=
  StrongDual.toWeakDual.toLinearMap.comp (functionalSubspaceEvaluationLinear F)

def functionalSubspaceWeakBall (C : ℝ) : Set (WeakDual ℂ F) :=
  functionalSubspaceWeakEvaluation F '' {a | ‖a‖ ≤ C}

end

/-! Exact characterization of the cyclic predual by WOT continuity on the
unit ball. No continuity of an arbitrary given-predual evaluation is assumed
or asserted here. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_FiniteComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! The closed span of algebra translates of a projection range gives its
central support. All operators act on the original Hilbert space; no trace,
cyclic vector, separability, finiteness, or comparison theorem is assumed. -/

/-! The original finiteness predicate excludes proper self-equivalence of a
projection. Projection comparison is connected to the unchanged IsII1Factor
predicate, with no representation, trace, or separability premise. -/

/-! Arbitrary-chain bounds with moving orthogonal initial and final supports, obtained from successive fixed-multiplier weak operator limits without a trace. -/

/-! Complete actual partial isometries to unitaries in a finite factor.
The construction uses projection comparison and finiteness, without a trace. -/
open scoped CStarAlgebra
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.unitaryPolarCStar
attribute [local instance] OAI.Generator.Tracial.unitaryPolarOrder
local instance unitaryPolarStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hfinite in
theorem exists_unitary_polar_decomposition (x : M.toStarSubalgebra) :
    ∃ u : unitary M.toStarSubalgebra, (u : M.toStarSubalgebra)*CFC.sqrt (star x*x)=x := by
  obtain ⟨v,hvx,hvi,_⟩ := exists_polar_decomposition x
  let a := CFC.sqrt (star x*x)
  let w : PartialIsometry M := ⟨rangeProjection a,v,hvi⟩
  obtain ⟨u,hu⟩ := w.exists_unitary_extension hfactor hfinite
  have ha : w.support.val*a=a := rangeProjection_mul a
  refine ⟨u,?_⟩
  calc (u : M.toStarSubalgebra)*a = (u : M.toStarSubalgebra)*(w.support.val*a) := by rw [ha]
    _ = w.val*a := by rw [← mul_assoc,hu]
    _ = x := hvx

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_DyadicComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Halving every projection in a diffuse factor without a trace.
Maximality leaves no residual corner: a diffuse residual splits into two
nonzero orthogonal projections, and a polar link gives a strict extension. -/

/-! Finite partitions with explicit equivalence witnesses and compatible binary
refinement. The common initial projection is halved once and its two pieces
are transported to every old piece, so all new pieces remain equivalent. -/

/-! Actual sums of countable orthogonal partial isometries, including least
initial/final support identities. No trace or countable-cofinality premise. -/
namespace Tracial

/-! Projection equivalence and subequivalence are witnessed by actual partial
isometries in the original algebra. No dimension or trace oracle is used. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-! Finiteness excludes an infinite family of nonzero equivalent orthogonal
projections. The shift and both of its least supports are constructed. -/

/-- The infinite shift omits the first range. Finiteness then forces that
range, and hence the common source projection, to be zero. -/
theorem traceFree_finite_orthogonal_copies_eq_zero
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (r : AlgebraProjection M) (a : ℕ → PartialIsometry M)
    (hs : ∀ i, (a i).support=r)
    (ho : ∀ i j, i≠j → (a i).target.val*(a j).target.val=0) : r.val=0 := by
  let w (i : ℕ) := PartialIsometry.rangeLink (a i) (a (i+1)) ((hs i).trans (hs (i+1)).symm)
  have hw₁ (i : ℕ) : (w i).support=(a i).target := rfl
  have hw₂ (i : ℕ) : (w i).target=(a (i+1)).target := PartialIsometry.rangeLink_target _ _ _
  obtain ⟨v,hv,hvp,hvq⟩ := PartialIsometry.traceFree_orthogonal_sum w
    (by intro i j h; rw [hw₁,hw₁]; exact ho i j h)
    (by intro i j h; rw [hw₂,hw₂]; exact ho (i+1) (j+1) (by omega))
  have hle : v.target ≤ v.support := by
    apply (hvq v.support).mpr
    intro i
    rw [hw₂,← hw₁ (i+1)]
    exact PartialIsometry.support_mono (hv (i+1))
  have he : v.target=v.support := v.target_eq_support_of_finite hfinite hle
  let c : AlgebraProjection M := ⟨1-(a 0).target.val,(a 0).target.property.one_sub⟩
  have hc : v.target ≤ c := by
    apply (hvq c).mpr
    intro i
    rw [hw₂]
    change (1-(a 0).target.val)*(a (i+1)).target.val=(a (i+1)).target.val
    rw [sub_mul,one_mul,ho 0 (i+1) (by omega),sub_zero]
  have h0 : (a 0).target ≤ c := by
    apply (PartialIsometry.support_mono (hv 0)).trans
    rw [← he]
    exact hc
  have hz : (a 0).target.val=0 := by
    change (1-(a 0).target.val)*(a 0).target.val=(a 0).target.val at h0
    rw [sub_mul,one_mul,(a 0).target.property.isIdempotentElem.eq,sub_self] at h0
    exact h0.symm
  have ha : (a 0).val=0 := by
    have h := (a 0).target_mul
    rw [hz,zero_mul] at h
    exact h.symm
  rw [← hs 0,← (a 0).initial,ha,star_zero,zero_mul]

/-- Subequivalence into every member of an orthogonal sequence is impossible
for a nonzero projection in a finite algebra. -/
theorem traceFree_finite_subequivalent_orthogonal_eq_zero
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (r : AlgebraProjection M) (q : ℕ → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0)
    (h : ∀ i, r.Subequivalent (q i)) : r.val=0 := by
  choose a hs ht using h
  exact traceFree_finite_orthogonal_copies_eq_zero hfinite r a hs (by
    intro i j hij
    exact projection_orthogonal_of_le (ho i j hij) (ht i) (ht j))

/-! Finite comparison and cancellation with actual partial isometries.
No trace, dimension, or representation is assumed. -/
end Tracial

/-! Actual finite sums of orthogonal partial isometries and finite subsets of
equivalent partitions. The finite subset is arbitrary, without an index order. -/
open scoped BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

theorem subset_univ (E : EquivalentPartition p ι) : E.subset Finset.univ=p :=
  Subtype.ext E.total

/-- A bijection of subsets gives a sum of explicit matrix-unit links. -/
theorem subset_equivalent_of_equiv (E : EquivalentPartition p ι) (s t : Finset ι)
    (e : s ≃ t) : (E.subset s).Equivalent (E.subset t) := by
  let a (i : s) := E.link i.val (e i).val
  obtain ⟨v,_,hs,ht⟩ := PartialIsometry.exists_finsetSum a Finset.univ
    (by
      intro i _ j _ hij
      exact E.orthogonal i.val j.val (fun h => hij (Subtype.ext h)))
    (by
      intro i _ j _ hij
      change (E.link i.val (e i).val).target.val*(E.link j.val (e j).val).target.val=0
      rw [E.link_target,E.link_target]
      exact E.orthogonal _ _ (fun h => hij (e.injective (Subtype.ext h))))
  refine ⟨v,Subtype.ext ?_,Subtype.ext ?_⟩
  · rw [hs]
    change (∑ i : s, (E.leg i.val).target.val)=∑ i ∈ s, (E.leg i).target.val
    simpa only [Finset.attach_eq_univ] using
      (Finset.sum_attach s (fun i => (E.leg i).target.val))
  · rw [ht]
    change (∑ i : s, (E.link i.val (e i).val).target.val)=_
    simp only [E.link_target]
    rw [e.sum_comp (fun i : t => (E.leg i.val).target.val)]
    change (∑ i : t, (E.leg i.val).target.val)=∑ i ∈ t, (E.leg i).target.val
    simpa only [Finset.attach_eq_univ] using
      (Finset.sum_attach t (fun i => (E.leg i).target.val))

theorem subset_equivalent_of_card_eq (E : EquivalentPartition p ι) (s t : Finset ι)
    (h : s.card=t.card) : (E.subset s).Equivalent (E.subset t) :=
  E.subset_equivalent_of_equiv s t (Finset.equivOfCardEq h)

/-! Exact finite cardinal comparison of sums of equivalent nonzero projections.
Finiteness prevents a larger collection from embedding in a smaller one. -/

end EquivalentPartition
end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Archimedean comparison for the constructed dyadic reference projections.
Orthogonal sibling corners supply copies for the finite-algebra shift argument. -/
section
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

def traceFreeDyadicReference (p : AlgebraProjection M) (n : ℕ) : AlgebraProjection M :=
  ((traceFreeDyadicPartition hfactor hdiff p n).leg (dyadicFalseIndex n)).target

def traceFreeDyadicSibling (p : AlgebraProjection M) (n : ℕ) : AlgebraProjection M :=
  ((traceFreeDyadicPartition hfactor hdiff p (n+1)).leg (dyadicFalseIndex n,true)).target

theorem traceFreeDyadic_child_le (p : AlgebraProjection M) (n : ℕ)
    (i : DyadicIndex n) (b : Bool) :
    ((traceFreeDyadicPartition hfactor hdiff p (n+1)).leg (i,b)).target ≤
      ((traceFreeDyadicPartition hfactor hdiff p n).leg i).target :=
  PartialIsometry.compose_target_le _ _ (by
    rw [EquivalentPartition.initial]
    exact EquivalentPartition.bound _ b)

theorem traceFreeDyadicReference_antitone (p : AlgebraProjection M) :
    Antitone (traceFreeDyadicReference hfactor hdiff p) := by
  apply antitone_nat_of_succ_le
  intro n
  exact traceFreeDyadic_child_le hfactor hdiff p n (dyadicFalseIndex n) false

theorem traceFreeDyadicSibling_le (p : AlgebraProjection M) (n : ℕ) :
    traceFreeDyadicSibling hfactor hdiff p n ≤ traceFreeDyadicReference hfactor hdiff p n :=
  traceFreeDyadic_child_le hfactor hdiff p n (dyadicFalseIndex n) true

theorem traceFreeDyadicReference_sibling_orthogonal (p : AlgebraProjection M) (n : ℕ) :
    (traceFreeDyadicReference hfactor hdiff p (n+1)).val*
      (traceFreeDyadicSibling hfactor hdiff p n).val=0 := by
  apply EquivalentPartition.orthogonal
  exact fun h => Bool.false_ne_true (congrArg Prod.snd h)

theorem traceFreeDyadicSibling_orthogonal (p : AlgebraProjection M) (i j : ℕ) (hij : i≠j) :
    (traceFreeDyadicSibling hfactor hdiff p i).val*
      (traceFreeDyadicSibling hfactor hdiff p j).val=0 := by
  have hlt (i j : ℕ) (h : i<j) :
      (traceFreeDyadicSibling hfactor hdiff p i).val*
        (traceFreeDyadicSibling hfactor hdiff p j).val=0 := by
    apply projection_orthogonal_of_le
      (PartialIsometry.orthogonal_reverse _ _
        (traceFreeDyadicReference_sibling_orthogonal hfactor hdiff p i)) le_rfl
    exact (traceFreeDyadicSibling_le hfactor hdiff p j).trans
      (traceFreeDyadicReference_antitone hfactor hdiff p (by omega))
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · exact PartialIsometry.orthogonal_reverse _ _ (hlt j i h)

theorem traceFreeDyadicReference_equivalent_sibling (p : AlgebraProjection M) (n : ℕ) :
    (traceFreeDyadicReference hfactor hdiff p (n+1)).Equivalent
      (traceFreeDyadicSibling hfactor hdiff p n) := by
  let E := traceFreeDyadicPartition hfactor hdiff p (n+1)
  exact ⟨E.link (dyadicFalseIndex (n+1)) (dyadicFalseIndex n,true),
    E.link_support _ _,E.link_target _ _⟩

/-- A projection that embeds in every dyadic reference corner must be zero.
Finiteness is used through the constructed infinite shift, not through a trace. -/
theorem traceFree_dyadic_archimedean
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p r : AlgebraProjection M)
    (h : ∀ n, r.Subequivalent (traceFreeDyadicReference hfactor hdiff p n)) : r.val=0 := by
  apply traceFree_finite_subequivalent_orthogonal_eq_zero hfinite r
    (traceFreeDyadicSibling hfactor hdiff p)
    (traceFreeDyadicSibling_orthogonal hfactor hdiff p)
  intro n
  exact AlgebraProjection.subequivalent_trans (h (n+1))
    (traceFreeDyadicReference_equivalent_sibling hfactor hdiff p n).subequivalent

/-- Every nonzero projection eventually fails to fit into the dyadic corners. -/
theorem traceFree_exists_dyadic_obstruction
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p r : AlgebraProjection M) (hr : r.val≠0) :
    ∃ n, ¬r.Subequivalent (traceFreeDyadicReference hfactor hdiff p n) := by
  by_contra hn
  exact hr (traceFree_dyadic_archimedean hfactor hdiff hfinite p r
    (by simpa only [not_exists,not_not] using hn))

/-- Every nonzero projection contains an equivalent copy of every sufficiently
small dyadic reference piece. This supplies the positivity input for dimension. -/
theorem traceFree_eventually_dyadic_subequivalent
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p r : AlgebraProjection M) (hr : r.val≠0) :
    ∃ n, ∀ m, n ≤ m → (traceFreeDyadicReference hfactor hdiff p m).Subequivalent r := by
  obtain ⟨n,hn⟩ := traceFree_exists_dyadic_obstruction hfactor hdiff hfinite p r hr
  have he : (traceFreeDyadicReference hfactor hdiff p n).Subequivalent r :=
    (AlgebraProjection.subequivalent_total hfactor r _).resolve_left hn
  refine ⟨n,fun m hm => ?_⟩
  exact AlgebraProjection.subequivalent_trans (AlgebraProjection.subequivalent_of_le
    (traceFreeDyadicReference_antitone hfactor hdiff p hm)) he

end Tracial

end

/-! Finite rounding by actual subset projections. A maximal fitting subset
leaves a remainder smaller in comparison than any unused equivalent piece. -/

/-! Classification of projection comparison by the constructed finite
dimension, and a wrapper for exactly the original IsII1Factor predicate.
No normality or trace-extension claim is made here. -/

/-! Bounds and concrete dyadic upper approximants for the constructed
projection dimension. These finite estimates do not assume continuity. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralStates
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Additivity on commuting self-adjoint operators, proved using actual common
spectral refinements. The commutation hypothesis is essential to this proof. -/
open scoped BigOperators

/-! Positive spectral approximants, positivity of the constructed scalar, and
order preservation on commuting self-adjoint operators. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace SpectralInterval
variable {x : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

theorem child_endpoints (hI : I.lo ≤ I.hi) (b : Bool) :
    I.lo ≤ (I.child hx b).lo ∧ (I.child hx b).lo ≤ (I.child hx b).hi ∧
      (I.child hx b).hi ≤ I.hi := by
  cases b <;> dsimp [child,low,high,midpoint]
  · exact ⟨le_rfl,by linarith,by linarith⟩
  · exact ⟨by linarith,by linarith,le_rfl⟩

theorem level_endpoints (hI : I.lo ≤ I.hi) : ∀ n i,
    I.lo ≤ (I.level hx n i).lo ∧ (I.level hx n i).lo ≤ (I.level hx n i).hi ∧
      (I.level hx n i).hi ≤ I.hi
  | 0,_ => ⟨le_rfl,hI,le_rfl⟩
  | n+1,i => by
    have h := level_endpoints hI n i.1
    have hchild := (I.level hx n i.1).child_endpoints hx h.2.1 i.2
    exact ⟨h.1.trans hchild.1,hchild.2.1,hchild.2.2.trans h.2.2⟩

end SpectralInterval

attribute [local instance] OAI.Generator.Tracial.spectralValueCStar
attribute [local instance] OAI.Generator.Tracial.spectralValueOrder
attribute [local instance] OAI.Generator.Tracial.spectralValuePreorder
attribute [local instance] OAI.Generator.Tracial.spectralValueLE
attribute [local instance] OAI.Generator.Tracial.spectralValueStarOrder
/-- A positive operator has arbitrarily accurate finite positive spectral
approximants preserving its entire commutant. -/
theorem exists_positive_spectral_approximation
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))
      (c : Fin Q.size → ℝ),
      (∀ i, 0 ≤ c i) ∧
      (∀ y : M.toStarSubalgebra, Commute x y → ∀ i, Commute (Q.piece i).val y) ∧
      ‖x-∑ i, (c i : ℂ) • (Q.piece i).val‖ < ε := by
  let I : SpectralInterval x :=
    { proj := ⟨1,IsStarProjection.one _⟩
      lo := 0
      hi := ‖x‖
      lower := by simpa only [one_mul,mul_one,Complex.ofReal_zero,zero_smul,sub_zero] using hx
      upper := (initialSpectralInterval ⟨1,IsStarProjection.one _⟩ x hx.isSelfAdjoint).upper }
  have hI : I.lo ≤ I.hi := norm_nonneg x
  obtain ⟨n,hn⟩ := I.exists_approximant hx.isSelfAdjoint hI ε hε
  let e := (Fintype.equivFin (DyadicIndex n)).symm
  refine ⟨I.partition hx.isSelfAdjoint n,fun i => (I.level hx.isSelfAdjoint n (e i)).lo,?_,?_,?_⟩
  · intro i
    exact (I.level_endpoints hx.isSelfAdjoint hI n (e i)).1
  · intro y hy i
    exact I.partition_commutes hx.isSelfAdjoint hy (Commute.one_left y) n i
  · change ‖x-∑ i, ((I.level hx.isSelfAdjoint n (e i)).lo : ℂ) •
        (I.level hx.isSelfAdjoint n (e i)).proj.val‖ < ε
    rw [Equiv.sum_comp e (fun i => ((I.level hx.isSelfAdjoint n i).lo : ℂ) •
      (I.level hx.isSelfAdjoint n i).proj.val)]
    change ‖1*x*1-∑ i, ((I.level hx.isSelfAdjoint n i).lo : ℂ) •
      (I.level hx.isSelfAdjoint n i).proj.val‖ < ε at hn
    simpa only [one_mul,mul_one] using hn

end

/-! A nonzero positive operator dominates a positive multiple of an actual
nonzero spectral projection. This proves faithfulness without linearity. -/
open scoped CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.spectralFaithfulCStar
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulOrder
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulPreorder
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulLE
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulStarOrder
theorem positive_spectral_cut_domination
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (t : ℝ) :
    (t : ℂ) • (cornerSpectralCut ⟨1,IsStarProjection.one _⟩ x t).val ≤ x := by
  let p : AlgebraProjection M := ⟨1,IsStarProjection.one _⟩
  let q := cornerSpectralCut p x t
  have hl : 0 ≤ q.val*x*q.val-(t : ℂ) • q.val := cornerSpectralCut_lower p x hx.isSelfAdjoint t
  have hr := star_left_conjugate_nonneg hx (1-q.val)
  rw [star_sub,star_one,q.property.isSelfAdjoint.star_eq] at hr
  have hsum := add_nonneg hl hr
  have he := cornerSpectralPartition_pinch p x hx.isSelfAdjoint t
  rw [cornerSpectralPartition,CornerPartition.binary_pinch] at he
  change q.val*x*q.val+(1-q.val)*x*(1-q.val)=1*x*1 at he
  simp only [one_mul,mul_one] at he
  have he' : q.val*x*q.val-(t : ℂ) • q.val+(1-q.val)*x*(1-q.val)=x-(t : ℂ) • q.val := by
    rw [show q.val*x*q.val-(t : ℂ) • q.val+(1-q.val)*x*(1-q.val)=
      (q.val*x*q.val+(1-q.val)*x*(1-q.val))-(t : ℂ) • q.val by abel,he]
  rw [he'] at hsum
  exact sub_nonneg.mp hsum

theorem positive_spectral_cut_ne_zero
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (t : ℝ) (ht : 0 ≤ t) (htx : t < ‖x‖) :
    (cornerSpectralCut ⟨1,IsStarProjection.one _⟩ x t).val ≠ 0 := by
  intro hz
  have h := cornerSpectralCut_upper ⟨1,IsStarProjection.one _⟩ x hx.isSelfAdjoint t
  dsimp only at h
  rw [hz,sub_zero,one_mul,mul_one] at h
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg (sub_nonpos.mp h) hx
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg ht] at hn
  have hone := (IsStarProjection.one M.toStarSubalgebra).norm_le
  have hb : ‖x‖ ≤ t := hn.trans (by nlinarith)
  exact (not_lt_of_ge hb) htx

end

/-! Unitary conjugacy preserves projection dimension and its constructed
spectral extension. No trace identity is assumed. -/
open scoped BigOperators

/-! The constructed scalar agrees on x*x and xx*, by an actual unitary polar
decomposition. This is a quadratic identity, not unrestricted additivity. -/
open scoped CStarAlgebra

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

attribute [local instance] OAI.Generator.Tracial.cornerValueCStar
attribute [local instance] OAI.Generator.Tracial.cornerValueOrder
local instance cornerValuePreorder_rdd429d_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.cornerValueLE
attribute [local instance] OAI.Generator.Tracial.cornerValueStarOrder
/-- A positive operator supported by p is approximated inside that same corner. -/
theorem exists_positive_corner_spectral_approximation
    (p : AlgebraProjection M) (x : M.toStarSubalgebra) (hx : 0 ≤ x)
    (hpx : p.val*x=x) (ε : ℝ) (hε : 0<ε) :
    ∃ (Q : CornerPartition p) (c : Fin Q.size → ℝ),
      (∀ i, 0 ≤ c i) ∧ (∀ i, Commute (Q.piece i).val x) ∧
      ‖x-∑ i, (c i : ℂ) • (Q.piece i).val‖ < ε := by
  have hxp : x*p.val=x := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq,hx.isSelfAdjoint.star_eq]
      using congrArg star hpx
  let I : SpectralInterval x :=
    { proj := p
      lo := 0
      hi := ‖x‖
      lower := by simpa only [hpx,hxp,Complex.ofReal_zero,zero_smul,sub_zero] using hx
      upper := (initialSpectralInterval p x hx.isSelfAdjoint).upper }
  have hI : I.lo ≤ I.hi := norm_nonneg x
  obtain ⟨n,hn⟩ := I.exists_approximant hx.isSelfAdjoint hI ε hε
  let e := (Fintype.equivFin (DyadicIndex n)).symm
  refine ⟨I.partition hx.isSelfAdjoint n,fun i => (I.level hx.isSelfAdjoint n (e i)).lo,?_,?_,?_⟩
  · intro i
    exact (I.level_endpoints hx.isSelfAdjoint hI n (e i)).1
  · intro i
    exact I.partition_commutes hx.isSelfAdjoint (Commute.refl x) (hpx.trans hxp.symm) n i
  · change ‖x-∑ i, ((I.level hx.isSelfAdjoint n (e i)).lo : ℂ) •
        (I.level hx.isSelfAdjoint n (e i)).proj.val‖ < ε
    rw [Equiv.sum_comp e (fun i => ((I.level hx.isSelfAdjoint n i).lo : ℂ) •
      (I.level hx.isSelfAdjoint n i).proj.val)]
    change ‖p.val*x*p.val-∑ i, ((I.level hx.isSelfAdjoint n i).lo : ℂ) •
      (I.level hx.isSelfAdjoint n i).proj.val‖ < ε at hn
    simpa only [hpx,hxp] using hn

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
-- module Solutions.OAIQ11_FG.FactorGeneration_LongWords
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Factorial coefficient majorization in every homogeneous degree. -/

/-! The nonlinear remainder of the actual ordered convolution-operator
exponentials, evaluated at δ₁, without assumed degree estimates. -/

/-! Signed rows B_k and positive rows A_k with free basis indexed by prefix ratios in FreeGroup Nat. -/
section
open scoped BigOperators
open Generator.CoefficientOrder Generator.FreeConvolution
local notation "G" => FreeGroup ℕ
local notation "F" => FreeGroup G

attribute [local instance] OAI.Generator.instDecidableEqFreeGroupNat_solutions_1
attribute [local instance] OAI.Generator.instDecidableEqFreeGroupNat_solutions_2
def perturbationRows (n : ℕ) (α : ℝ) :
    List (MonoidAlgebra ℂ F × MonoidAlgebra ℝ F) := List.ofFn (perturbationRow (n := n) α)

end

/-! Transfer of the nonlinear estimate to an algebra with a continuous Hilbert
realization and orthonormal reduced-word images, without an independence hypothesis. -/

/-! The exact finite free basis and its injective realization in a countable free basis. -/
section
open scoped BigOperators
open Generator.FreeConvolution
local notation "G" => FreeGroup ℕ
local notation "F" => FreeGroup G

local instance instDecidableEqFreeGroupNat_solutions_3_rdd429d_1 : DecidableEq G := Classical.decEq _
def embeddedCoefficientMap (n : ℕ) :
    MonoidAlgebra ℂ (FreeGroup (PrefixLabel n)) →ₗ[ℂ] SquareSpace F :=
  (ContinuousLinearMap.apply ℂ (SquareSpace F) delta).toLinearMap.comp
    (regular.toLinearMap.comp (prefixRingEmbedding n).toLinearMap)

end

/-! Exact finite-basis version of the source's nonlinear estimate. Unlike the
ambient transport lemma, only reduced words in F_S occur in the hypothesis. -/
open scoped BigOperators InnerProductSpace

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ResidualCompletion
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual residual projections, null-set masking, and coordinatewise
orthogonal partial-unitary patching. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def maskPartialSequence (S : Set ℕ) (v : ℕ → PartialUnitary M) : ℕ → PartialUnitary M :=
  fun j => @ite (PartialUnitary M) (j ∈ S) (Classical.propDecidable _) (v j) zeroPartialUnitary

def patchPartialSequence (v w : ℕ → PartialUnitary M)
    (h : ∀ j,(v j).support.val*(w j).support.val=0) : ℕ → PartialUnitary M :=
  fun j => ⟨⟨(v j).support.val+(w j).support.val,
    (v j).support.property.add (w j).support.property (h j)⟩,
      (v j).unitary.patch (w j).unitary (h j)⟩

end

/-! An actual positive residual support increment with exact ordered moments
for arbitrary countably many centered compressed quotient coefficients. -/
open Filter

/-! Faithful-trace completion criterion and the exact quarter-increment
residual estimate for actual orthogonal coordinate patches. -/

/-! Actual moment-preserving residual extensions, retaining coordinate partial
unitaries in N and the quantitative decrease of residual support. -/

/-! Iteration of actual moment-preserving partial-unitary extensions. Every
stage retains its coordinate representatives and a geometric residual bound. -/

/-! Coordinatewise monotone upper bounds and quantitative convergence in the
actual quotient two-norm. No completeness of the quotient is assumed. -/
open UltrapowerBridge Filter
open scoped Topology

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
section
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators InnerProductSpace
open FreeConvolution

def rowSignedWord {ell : ℕ} (k : Fin ell) (a : Fin ell × Bool) :
    FreeGroup (PrefixLabel ell) := letter (pairLabel k a.1,a.2)

end

/-! Exact trace-two-norm of the single common logarithmic perturbation. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_RelativeGeneration
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite star polynomials in one unitary variable and coefficients in
an included von Neumann algebra. Both uniform operator bounds and continuity
of trace-vector evaluation are proved by recursion on the expression. -/
open Filter
open scoped Topology

/-! The literal algebra W*(N,u), its trace Hilbert subspace, and density of
actual N-coefficient star-polynomial values in that subspace. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

def relativeGenerated (u : TraceUnitary τ) : VonNeumannAlgebra H :=
  vonNeumannOfWOTClosed (wstar (relativeGenerators (N := N) τ u)) (wstar_closed _)

namespace RelativePolynomial

theorem valueAlgebra_le (u : TraceUnitary τ) :
    valueAlgebra (N := N) τ u ≤ (relativeGenerated (N := N) τ u).toStarSubalgebra :=
  StarAlgebra.adjoin_le (subset_wstar _)

end RelativePolynomial

def relativeTraceSpace (u : TraceUnitary τ) : Submodule ℂ H :=
  vectorOrbitClosure (relativeGenerated (N := N) τ u).toStarSubalgebra τ.vector

instance relativeTraceSpace_complete (u : TraceUnitary τ) :
    CompleteSpace (relativeTraceSpace (N := N) τ u) :=
  inferInstanceAs (CompleteSpace (vectorOrbitClosure _ _))

theorem polynomialVector_mem (p : Generator.RelativePolynomial N.toStarSubalgebra)
    (u : TraceUnitary τ) : RelativePolynomial.sectionVector τ hNM p u ∈
      relativeTraceSpace (N := N) τ u :=
  Submodule.le_topologicalClosure _ ⟨⟨(RelativePolynomial.eval τ hNM p u).val,
    RelativePolynomial.valueAlgebra_le τ u (RelativePolynomial.eval_mem τ hNM p u)⟩,rfl⟩

end Tracial

/-! The literal interleaved word belongs to W*(N,u), is unitary, and has
trace norm one. The printed perturbation-size bound tends to zero. -/
open Filter
open scoped Topology

/-! Projection continuity for generated algebras, using the complete trace-unitary metric, dense polynomial sections, and trace-vector separability. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

/-! The bounded conditional expectation agrees with the actual Hilbert
projection. Proper subalgebras have a unitary outside them, yielding the
nonzero represented residual used by thm:relative-generation. -/

def subalgebraResidual (x : M.toStarSubalgebra) : M.toStarSubalgebra :=
  x-conditionalExpectation τ hNM x

end Tracial

end Generator

end

end OAI
end


