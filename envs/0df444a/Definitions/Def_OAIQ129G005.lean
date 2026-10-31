-- Prove2me | Definitions.Def_OAIQ129G005
-- name    : OAIQ129G005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T20:16:56.604562+00:00
-- url     : https://prove2.me/theorems/0bb0c961-4023-4cc0-b1d0-17e77caafe6c
-- title:
--   Definitions bundle OAIQ129G005 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 139 declarations of OpenAI's Lean: 72 definitions, 2 inductive types or structures, 2 instances and 63 theorems. The definitions and types are `OAI.Generator.FactorTraceUnitary.unitaryEquiv`, `OAI.Generator.FiniteMatrixStage.generatedVonNeumann`, `OAI.Generator.FiniteMatrixStage.stageVonNeumann`, `OAI.Generator.MatrixUnitSystem.bellPartition`, `OAI.Generator.MatrixUnitSystem.bellPiece`, `OAI.Generator.Tracial.CornerPartition.Refines`, `OAI.Generator.Tracial.CornerPartition.blockStarAlgebra`, `OAI.Generator.Tracial.CornerPartition.blockVonNeumann`, `OAI.Generator.Tracial.CornerPartition.fromRepresentedCorner`, `OAI.Generator.Tracial.CornerUnitary`, `OAI.Generator.Tracial.CornerUnitary.adjoint`, `OAI.Generator.Tracial.CornerUnitary.patch`, `OAI.Generator.Tracial.PartialUnitary`, `OAI.Generator.Tracial.PartialUnitary.Extends`, `OAI.Generator.Tracial.PartialUnitary.completed`, `OAI.Generator.Tracial.PartialUnitary.fromRepresentedCorner`, `OAI.Generator.Tracial.PartialUnitary.val`, `OAI.Generator.Tracial.algebraPositiveResolvent`, `OAI.Generator.Tracial.ambientAbsoluteValue`, `OAI.Generator.Tracial.clippingCStar`, `OAI.Generator.Tracial.cornerCompress`, `OAI.Generator.Tracial.cornerCompressOperator`, `OAI.Generator.Tracial.cornerEmbedding`, `OAI.Generator.Tracial.cornerExtend`, `OAI.Generator.Tracial.cornerProject`, `OAI.Generator.Tracial.cornerSpace`, `OAI.Generator.Tracial.cornerStarAlgebra`, `OAI.Generator.Tracial.dominationCStar`, `OAI.Generator.Tracial.dominationLE`, `OAI.Generator.Tracial.dominationOrder`, `OAI.Generator.Tracial.dyadicSign`, `OAI.Generator.Tracial.expectationContractiveCStar`, `OAI.Generator.Tracial.expectationContractiveLE`, `OAI.Generator.Tracial.expectationContractiveOrder`, `OAI.Generator.Tracial.expectationContractivePreorder`, `OAI.Generator.Tracial.expectationPosCStar`, `OAI.Generator.Tracial.expectationPosLE`, `OAI.Generator.Tracial.expectationPosOrder`, `OAI.Generator.Tracial.identityProjection`, `OAI.Generator.Tracial.includedProjection` and 34 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_Bicommutant`, `FactorGeneration_CoordinateUnitaries`, `FactorGeneration_CornerIndependence`, `FactorGeneration_Expectations`, `FactorGeneration_LocalPatches`, `FactorGeneration_MatrixAlgebras`, `FactorGeneration_MatrixExpectation`, `FactorGeneration_MatrixSequence`, `FactorGeneration_MonotoneTrace`, `FactorGeneration_NormalTrace`, `FactorGeneration_OperatorLimits`, `FactorGeneration_PartialUnitaries`, `FactorGeneration_PatchingWords`, `FactorGeneration_Pinching`, `FactorGeneration_ProjectionLimits`, `FactorGeneration_RepresentedCorners`, `FactorGeneration_ResidualCompletion`, `FactorGeneration_ResidualEstimates`, `FactorGeneration_SpectralApproximation`, `FactorGeneration_SpectralTruncation`, `FactorGeneration_Subfactors`, `FactorGeneration_TraceHilbert`, `FactorGeneration_TraceTransport`, `RelativeGeneration_OriginalUnitary`.
--
--   **Imports.** It imports the published bundle `Def_FactorGeneration`; the bundles `OAIQ129G000` and `OAIQ129G001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ129G008` and `OAIQ129G009`; the statements `OAI.Generator.Tracial.exists_scalar_pinching_for_matrixUnits_q129`, `OAI.Generator.Tracial.representedCorner_factor_q129` and `OAI.Generator.Tracial.representedCorner_irreducible_q129`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ129G000
import Definitions.Def_OAIQ129G001

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Bicommutant
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Finite diagonal amplification and the projection onto a simultaneous
operator orbit. These are the analytic ingredients of the bicommutant theorem. -/

/-! The double commutant theorem for actual unital star subalgebras of B(H).
Finite simultaneous strong approximation constructs a WOT-convergent net.
No bounded approximation or separable-predual theorem is claimed here. -/
section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vonNeumannOfWOTClosed (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S) :
    VonNeumannAlgebra H where
  toStarSubalgebra := S
  centralizer_centralizer' := wotClosed_bicommutant S hS

end

/-! Countable algebraic generators give a separable star algebra using only
continuous addition and scalar multiplication. No multiplication continuity is
required, so the result applies to the two-norm on a tracial quotient. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_OperatorLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Operator-norm completeness of the manuscript's concrete algebra, derived
from its actual double-commutant property. No quotient completeness is assumed. -/
namespace Tracial

/-! Bounded operator families have weak operator ultralimits. This is proved
from Banach--Alaoglu and Riesz representation, not assumed as compactness. -/
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! Operator-norm balls of an actual von Neumann algebra are compact for the
weak operator topology, using the previously constructed operator ultralimits. -/

theorem weakOperatorBall_isCompact (M : VonNeumannAlgebra H) (C : ℝ) :
    IsCompact (weakOperatorBall M C) := by
  classical
  by_cases hC : 0 ≤ C
  · apply isCompact_iff_ultrafilter_le_nhds'.mpr
    intro ω hω
    let a : (H →WOT[ℂ] H) → M.toStarSubalgebra := fun T =>
      if h : T ∈ weakOperatorBall M C then ⟨T.toCLM,h.1⟩ else 0
    have ha (T : H →WOT[ℂ] H) : ‖a T‖ ≤ C := by
      dsimp [a]
      split_ifs with h
      · exact h.2
      · change ‖(0 : H →L[ℂ] H)‖ ≤ C
        simpa only [norm_zero] using hC
    obtain ⟨T,hT,ht⟩ := exists_weak_operator_ultralimit ω (fun U => (a U).val) C hC ha
    have hm := weak_operator_limit_mem M a T ht
    refine ⟨ContinuousLinearMapWOT.ofCLM T,⟨hm,hT⟩,?_⟩
    have hl : Tendsto (fun U => ContinuousLinearMapWOT.ofCLM (a U).val)
        (ω : Filter (H →WOT[ℂ] H)) (𝓝 (ContinuousLinearMapWOT.ofCLM T)) :=
      ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr ht
    have he : (fun U => ContinuousLinearMapWOT.ofCLM (a U).val) =ᶠ[ω] id := by
      filter_upwards [show ∀ᶠ U in (ω : Filter (H →WOT[ℂ] H)),U ∈ weakOperatorBall M C from hω]
        with U hU
      simp only [a,dite_eq_left hU,ContinuousLinearMapWOT.ofCLM_toCLM,id_eq]
    exact hl.congr' he
  · have he : weakOperatorBall M C=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro T hT
      exact hC ((norm_nonneg _).trans hT.2)
    rw [he]
    exact isCompact_empty

end Tracial

/-! Operator order bounds are closed in the weak operator topology. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ProjectionLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.CornerPartition.single_pinch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero projection in a diffuse tracial algebra contains nonzero projections of arbitrarily small trace. -/

/-! Monotone projection limits with trace bounds, giving chain bounds for prescribed trace cuts. -/

/-! Exact trace cuts in a diffuse coordinate algebra. -/

/-! Algebraic part of Popa 1308.3982v3, Lemma 3.2: adding a supported
partial unitary in the residual corner. The small mixed-word estimates and
the existence of an appropriate patch are separate analytic requirements. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- An actual operator with identical initial and final support p. -/
structure CornerUnitary (p : AlgebraProjection M) where
  val : M.toStarSubalgebra
  initial : star val * val = p.val
  final : val * star val = p.val

namespace CornerUnitary
variable {p q : AlgebraProjection M}

theorem mul_support (v : CornerUnitary p) : v.val*p.val=v.val := by
  have htr : star v.val*(v.val*p.val)=p.val := by
    rw [← mul_assoc,v.initial,p.property.isIdempotentElem.eq]
  have he : star (v.val-v.val*p.val)*(v.val-v.val*p.val)=0 := by
    simp only [star_sub,star_mul,p.property.isSelfAdjoint.star_eq,sub_mul,mul_sub,
      mul_assoc,v.initial,htr,p.property.isIdempotentElem.eq,sub_self]
  exact (sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp he)).symm

theorem support_mul (v : CornerUnitary p) : p.val*v.val=v.val := by
  calc p.val*v.val = (v.val*star v.val)*v.val := by rw [v.final]
       _ = v.val*(star v.val*v.val) := mul_assoc _ _ _
       _ = v.val := by rw [v.initial,v.mul_support]

def adjoint (v : CornerUnitary p) : CornerUnitary p :=
  ⟨star v.val,by simpa only [star_star] using v.final,
    by simpa only [star_star] using v.initial⟩

theorem mul_eq_zero (v : CornerUnitary p) (w : CornerUnitary q) (hpq : p.val*q.val=0) :
    v.val*w.val=0 := by
  calc v.val*w.val = (v.val*p.val)*(q.val*w.val) := by rw [v.mul_support,w.support_mul]
       _ = v.val*(p.val*q.val)*w.val := by simp only [mul_assoc]
       _ = 0 := by rw [hpq,mul_zero,zero_mul]

def patch (v : CornerUnitary p) (w : CornerUnitary q) (hpq : p.val*q.val=0) :
    CornerUnitary ⟨p.val+q.val,p.property.add q.property hpq⟩ where
  val := v.val+w.val
  initial := by
    have hqp : q.val*p.val=0 := by
      simpa only [star_mul,p.property.isSelfAdjoint.star_eq,q.property.isSelfAdjoint.star_eq,star_zero]
        using congrArg star hpq
    have h₁ : star v.val*w.val=0 := v.adjoint.mul_eq_zero w hpq
    have h₂ : star w.val*v.val=0 := w.adjoint.mul_eq_zero v hqp
    change star (v.val+w.val)*(v.val+w.val)=p.val+q.val
    rw [star_add,add_mul,mul_add,mul_add,v.initial,w.initial,h₁,h₂,add_zero,zero_add]
  final := by
    have hqp : q.val*p.val=0 := by
      simpa only [star_mul,p.property.isSelfAdjoint.star_eq,q.property.isSelfAdjoint.star_eq,star_zero]
        using congrArg star hpq
    have h₁ : v.val*star w.val=0 := v.mul_eq_zero w.adjoint hpq
    have h₂ : w.val*star v.val=0 := w.mul_eq_zero v.adjoint hqp
    change (v.val+w.val)*star (v.val+w.val)=p.val+q.val
    rw [star_add,add_mul,mul_add,mul_add,v.final,w.final,h₁,h₂,add_zero,zero_add]

theorem norm_sq (v : CornerUnitary p) : ‖v.val‖*‖v.val‖=‖p.val‖ := by
  rw [← CStarRing.norm_star_mul_self,v.initial]

theorem norm_le_one (v : CornerUnitary p) : ‖v.val‖ ≤ 1 := by
  have he := v.norm_sq
  have hp := p.property.norm_le
  nlinarith [norm_nonneg v.val]

end CornerUnitary

end

/-! Dyadic projections inside a diffuse algebra with faithful trace. -/

/-! Finite spectral sums in the constructed dyadic projection algebras. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable {ι : Type*} [Fintype ι]

def projectionSum (a : ι → AlgebraProjection M) (c : ι → ℂ) : M.toStarSubalgebra :=
  ∑ i, c i • (a i).val

theorem projectionSum_star (a : ι → AlgebraProjection M) (c : ι → ℂ) :
    star (projectionSum a c)=projectionSum a (fun i => star (c i)) := by
  simp only [projectionSum,star_sum,star_smul,(a _).property.isSelfAdjoint.star_eq]

theorem projectionSum_mul (a : ι → AlgebraProjection M)
    (ha : ∀ i j, i ≠ j → (a i).val*(a j).val=0) (c d : ι → ℂ) :
    projectionSum a c*projectionSum a d=projectionSum a (fun i => c i*d i) := by
  classical
  unfold projectionSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single i]
  · rw [smul_mul_assoc,mul_smul_comm,smul_smul,(a i).property.isIdempotentElem.eq]
  · intro j _ hji
    rw [smul_mul_assoc,mul_smul_comm,ha i j hji.symm,smul_zero,smul_zero]
  · simp

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_PartialUnitaries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.CornerPartition.single_pinch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Popa's extension order on actual supported partial unitaries, and its
exact L2 distance identity. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

structure PartialUnitary (M : VonNeumannAlgebra H) where
  support : AlgebraProjection M
  unitary : CornerUnitary support

namespace PartialUnitary
abbrev val (v : PartialUnitary M) := v.unitary.val

def Extends (v w : PartialUnitary M) : Prop := w.val*v.support.val=v.val

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

@[ext] theorem ext {v w : PartialUnitary M} (h : v.val=w.val) : v=w := by
  have hp : v.support=w.support := by
    apply Subtype.ext
    calc v.support.val = star v.val*v.val := v.unitary.initial.symm
         _ = star w.val*w.val := by rw [h]
         _ = w.support.val := w.unitary.initial
  cases v with | mk p v =>
    cases w with | mk q w =>
      dsimp at hp
      subst q
      congr 1
      cases v
      cases w
      congr 1

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
section
open Filter
open scoped Topology BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)

def dyadicSign (n : ℕ) (i : DyadicIndex (n+1)) : ℂ := if i.2 then -1 else 1

end

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_PatchingWords
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Ordered signed mixed words in Popa 1308.3982v3, Lemma 3.2.
The L2 continuity estimate keeps the order of every coefficient. -/

/-! The scalar-commutant specialization of the error-constrained chain and
Zorn step in Popa 1308.3982v3 Lemma 3.2. The internal coefficients are in F;
only the two endpoints may be 1. No local-quantization or growth assumption. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def zeroPartialUnitary : PartialUnitary M :=
  ⟨⟨0,IsStarProjection.zero _⟩,⟨0,by simp,by simp⟩⟩

end

/-! The error-constrained partial unitaries stay in the prescribed algebra P,
while all word coefficients and the trace live in M. This prevents replacing
the source inclusion P subset M by the trivial inclusion M subset M. -/

/-! Finite enumeration of the actual ordered word family. Only endpoints may
be 1. The middle segments retain all signs and their precise lengths. -/

/-! The two moment bounds in Popa Lemma 3.2 equation (6), derived from
admissibility for the actual signed internal segment, including length zero. -/

/-! Actual noncommutative binary expansion in Popa Lemma 3.2, equation (1).
Each list entry retains the number of patch letters used and its ordered
operator product. There is no commuting-coefficient hypothesis. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Pinching
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite pinching in the actual ambient algebra. The squared L2 energy
is a sum of the energies of the mutually orthogonal compression blocks.
These identities do not postulate a local-quantizing partition. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-! Actual compression energies and the energy lost by finite pinching.
No existence statement about small-energy partitions is assumed here. -/

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

/-! Partition refinement decreases the actual compression energy. The final
selection theorem retains membership in the prescribed subalgebra. -/

def Refines (R : CornerPartition p) : Prop := ∀ i, ∃ j, R.piece i ≤ Q.piece j

end CornerPartition

end

/-! Actual finite refinement of a corner partition by partitions of its blocks.
The dependent family of block sizes is flattened without changing any piece.
No small-energy partition is an input to these constructions. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace CornerPartition
variable {p : AlgebraProjection M}

variable (Q : CornerPartition p) (R : (i : Fin Q.size) → CornerPartition (Q.piece i))

theorem blockFamily_total :
    (∑ a : (i : Fin Q.size) × Fin (R i).size, ((R a.1).piece a.2).val) = p.val := by
  rw [Fintype.sum_sigma]
  simpa only [(R _).total] using Q.total

end CornerPartition

end

/-! Centered energy and the block scalar term that refinement preserves.
A blockwise descent applies to centered compressions, not to their full energy. -/

/-! Energy of compatible block refinements, including the scalar term.
The scalar term is necessary even when the original operator has trace zero. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_SpectralApproximation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Common finite refinements of two commuting corner partitions. -/

/-! Finite spectral approximation for an actual normal operator. -/
section
open scoped BigOperators ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def identityProjection (M : VonNeumannAlgebra H) : AlgebraProjection M := ⟨1,IsStarProjection.one _⟩

end

/-! Transport constructed spectral partitions through an actual inclusion of
von Neumann algebras on the same Hilbert space. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def includedProjection (h : N ≤ M) (p : AlgebraProjection N) : AlgebraProjection M :=
  ⟨algebraInclusion h p.val,by
    constructor
    · change algebraInclusion h p.val * algebraInclusion h p.val = algebraInclusion h p.val
      rw [← map_mul,p.property.isIdempotentElem.eq]
    · change star (algebraInclusion h p.val)=algebraInclusion h p.val
      rw [← map_star,p.property.isSelfAdjoint.star_eq]⟩

def includedUnitPartition (h : N ≤ M) (Q : CornerPartition (identityProjection N)) :
    CornerPartition (identityProjection M) where
  size := Q.size
  piece i := includedProjection h (Q.piece i)
  orthogonal i j hij := by
    change algebraInclusion h (Q.piece i).val * algebraInclusion h (Q.piece j).val=0
    rw [← map_mul,Q.orthogonal i j hij,map_zero]
  total := by
    change (∑ i,algebraInclusion h (Q.piece i).val)=1
    rw [← map_sum,Q.total]
    exact map_one (algebraInclusion h)

end

/-! Finite simultaneous spectral approximation of any commuting self-adjoint
family, preserving a prior partition and the entire common commutant. -/

/-! Finite orthogonal families can be completed to unit partitions. Refining
blocks retains explicit disjoint index sets whose sums recover those blocks. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Subfactors
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual von Neumann algebra of operators in N commuting with a finite
projection partition. Its double-commutant identity and completeness are
proved, so spectral approximation can be performed inside this algebra. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}
namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

def blockStarAlgebra (N : VonNeumannAlgebra H) : StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {a | a ∈ N ∧ ∀ i, (Q.piece i).val.val*a=a*(Q.piece i).val.val}
  zero_mem' := ⟨N.zero_mem,by simp⟩
  one_mem' := ⟨N.one_mem,by simp⟩
  add_mem' ha hb := ⟨N.add_mem ha.1 hb.1,by
    intro i
    simp only [mul_add,add_mul,ha.2 i,hb.2 i]⟩
  mul_mem' ha hb := ⟨N.mul_mem ha.1 hb.1,by
    intro i
    rw [← mul_assoc,ha.2 i,mul_assoc,hb.2 i,← mul_assoc]⟩
  algebraMap_mem' c := ⟨N.toStarSubalgebra.algebraMap_mem c,by
    intro i
    exact (Algebra.commutes c _).symm⟩
  star_mem' ha := ⟨star_mem ha.1,by
    intro i
    have hs : star (Q.piece i).val.val=(Q.piece i).val.val :=
      congrArg Subtype.val (Q.piece i).property.isSelfAdjoint.star_eq
    simpa only [star_mul,hs] using (congrArg star (ha.2 i)).symm⟩

theorem blockStarAlgebra_bicommutant (N : VonNeumannAlgebra H) :
    Set.centralizer (Set.centralizer (Q.blockStarAlgebra N : Set (H →L[ℂ] H))) =
      (Q.blockStarAlgebra N : Set (H →L[ℂ] H)) := by
  apply Set.Subset.antisymm
  · intro a ha
    refine ⟨?_,?_⟩
    · change a ∈ (N : Set (H →L[ℂ] H))
      rw [← N.centralizer_centralizer]
      intro b hb
      exact ha b (fun c hc => hb c hc.1)
    · intro i
      apply ha
      intro b hb
      exact (hb.2 i).symm
  · intro a ha b hb
    exact (hb a ha).symm

def blockVonNeumann (N : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra := Q.blockStarAlgebra N
  centralizer_centralizer' := Q.blockStarAlgebra_bicommutant N

end CornerPartition

end

/-! Irreducibility passes to actual corners. Spectral approximation reduces
self-adjoint corner commutants to their projections; no corner-factor or
normalized-trace existence statement is assumed. -/

/-! The relative commutant of a finite block algebra consists of scalars on
each block. This statement is proved from coordinate irreducibility. -/

/-! Orthogonality to the prescribed subalgebra is stronger than global
centering. It is preserved by compressions and conjugations from that
subalgebra and removes every block scalar term exactly. -/

/-! A corner whose only projections are zero and its unit is scalar.
The proof constructs spectral approximations; minimality is not a scalar-corner axiom. -/

/-! Diffuseness descends to an irreducible von Neumann subalgebra of a
diffuse finite tracial algebra. Finiteness follows from the actual faithful trace. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_SpectralTruncation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Positivity of the tracial pairing does not require the two positive
operators to commute. These estimates will control spectral truncation. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
local instance tracePairingCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance tracePairingOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance tracePairingPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance tracePairingLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance tracePairingStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! Upper spectral truncation of a self-adjoint operator. The truncation
remains in the original operator ball and has a positive discarded part. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance truncationCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance truncationOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance truncationLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance truncationStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

def upperTruncate (a : M.toStarSubalgebra) (C : ℝ) : M.toStarSubalgebra :=
  a-(a-algebraMap ℝ M.toStarSubalgebra C)⁺

theorem upperTruncate_cfc (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    upperTruncate a C = cfc (fun t : ℝ => min t C) a := by
  have hf : (fun t : ℝ => min t C) = fun t => t-(t-C)⁺ := by
    funext t
    simp only [_root_.posPart_def]
    by_cases h : t ≤ C
    · rw [min_eq_left h,max_eq_right (sub_nonpos.mpr h),sub_zero]
    · rw [min_eq_right (le_of_not_ge h),max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
      ring
  rw [hf,cfc_sub (fun t : ℝ => t) (fun t => (t-C)⁺) a,cfc_id' ℝ a]
  unfold upperTruncate
  congr 1
  rw [CFC.posPart_def,cfcₙ_eq_cfc]
  have hs : cfc (fun t : ℝ => t-C) a = a-algebraMap ℝ M.toStarSubalgebra C := by
    rw [cfc_sub (fun t : ℝ => t) (fun _ => C) a,cfc_id' ℝ a,cfc_const C a ha]
  rw [← hs,← cfc_comp (fun t : ℝ => t⁺) (fun t => t-C) a]
  rfl

theorem upperTruncate_selfAdjoint (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    IsSelfAdjoint (upperTruncate a C) :=
  ha.sub (CFC.posPart_nonneg _).isSelfAdjoint

theorem upperTruncate_norm_le (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a)
    (C R : ℝ) (hC : 0 ≤ C) (hR : ‖a‖ ≤ R) : ‖upperTruncate a C‖ ≤ R := by
  obtain (hH | hH) := subsingleton_or_nontrivial H
  · have ha0 : a=0 := Subtype.ext (Subsingleton.elim _ _)
    have hz : upperTruncate a C=0 := Subtype.ext (Subsingleton.elim _ _)
    simpa only [hz,norm_zero] using (norm_nonneg a).trans hR
  rw [upperTruncate_cfc a ha C]
  apply norm_cfc_le ((norm_nonneg a).trans hR)
  intro t ht
  have htR := (spectrum.norm_le_norm_of_mem ht).trans hR
  rw [Real.norm_eq_abs,abs_le] at htR ⊢
  exact ⟨le_min htR.1 (by linarith), (min_le_left _ _).trans htR.2⟩

theorem upperTruncate_discard_mul (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    (a-algebraMap ℝ M.toStarSubalgebra C)⁺ * upperTruncate a C =
      C • (a-algebraMap ℝ M.toStarSubalgebra C)⁺ := by
  let b := a-algebraMap ℝ M.toStarSubalgebra C
  have hb : IsSelfAdjoint b := ha.sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all C))
  have he : upperTruncate a C = algebraMap ℝ M.toStarSubalgebra C-b⁻ := by
    have hh := CFC.posPart_sub_negPart b hb
    have heq : a=b+algebraMap ℝ M.toStarSubalgebra C := by dsimp [b]; abel
    change a-b⁺=algebraMap ℝ M.toStarSubalgebra C-b⁻
    nth_rw 1 [heq]
    nth_rw 1 [← hh]
    abel
  rw [he,mul_sub,CFC.posPart_mul_negPart,sub_zero,
    Algebra.algebraMap_eq_smul_one,mul_smul_comm,mul_one]

end

/-! Spectral truncation forces a self-adjoint least-distance point in a
subalgebra ball to have norm at most the norm of the ambient test operator. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}
local instance interiorCStar (A : VonNeumannAlgebra H) : CStarAlgebra A.toStarSubalgebra := {}
local instance interiorOrder (A : VonNeumannAlgebra H) : PartialOrder A.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance interiorPreorder (A : VonNeumannAlgebra H) : Preorder A.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance interiorLE (A : VonNeumannAlgebra H) : LE A.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toLE
local instance interiorStarOrder (A : VonNeumannAlgebra H) : StarOrderedRing A.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem selfAdjoint_norm_le_of_bounds (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a)
    (C : ℝ) (hC : 0 ≤ C) (hu : a ≤ algebraMap ℝ M.toStarSubalgebra C)
    (hl : -a ≤ algebraMap ℝ M.toStarSubalgebra C) : ‖a‖ ≤ C := by
  obtain (hA | hA) := subsingleton_or_nontrivial M.toStarSubalgebra
  · simpa only [Subsingleton.elim a 0,norm_zero] using hC
  have hpos : ∀ t ∈ spectrum ℝ a,t ≤ C := by
    apply (cfc_le_iff (fun t : ℝ => t) (fun _ => C) a).mp
    rw [cfc_id' ℝ a ha,cfc_const C a ha]
    exact hu
  have hneg : ∀ t ∈ spectrum ℝ a,-t ≤ C := by
    apply (cfc_le_iff (fun t : ℝ => -t) (fun _ => C) a).mp
    rw [cfc_neg (fun t : ℝ => t) a,cfc_id' ℝ a ha,cfc_const C a ha]
    exact hl
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum ha with h | h
  · exact hpos _ h
  · simpa using hneg _ h

end

/-! Two-sided spectral clipping and trace-norm control. The auxiliary trace
is explicit; the trace-free construction supplies it on its actual closure. -/
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance clippingCStar : CStarAlgebra M.toStarSubalgebra := {}

local instance clippingOrder_r45111e_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance clippingStarOrder_r45111e_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
theorem traceSymmetrize_selfAdjoint (a : M.toStarSubalgebra) : IsSelfAdjoint (traceSymmetrize a) := by
  change star ((2 : ℂ)⁻¹ • (a+star a)) = (2 : ℂ)⁻¹ • (a+star a)
  simp [add_comm]

theorem traceSymmetrize_eq_self (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) :
    traceSymmetrize a = a := by
  simp only [traceSymmetrize,ha.star_eq,← two_smul ℂ a,smul_smul]
  norm_num

theorem traceSymmetrize_sub (a b : M.toStarSubalgebra) :
    traceSymmetrize (a-b) = traceSymmetrize a-traceSymmetrize b := by
  simp only [traceSymmetrize,star_sub,smul_add,smul_sub]
  abel

def traceClip (a : M.toStarSubalgebra) (C : ℝ) : M.toStarSubalgebra :=
  -upperTruncate (-upperTruncate a C) C

theorem traceClip_selfAdjoint (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    IsSelfAdjoint (traceClip a C) :=
  (upperTruncate_selfAdjoint _ (upperTruncate_selfAdjoint a ha C).neg C).neg

theorem traceClip_cfc (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    traceClip a C = cfc (fun t : ℝ => -min (-min t C) C) a := by
  rw [traceClip,upperTruncate_cfc _ (upperTruncate_selfAdjoint a ha C).neg C,
    upperTruncate_cfc a ha C,← cfc_neg (fun t : ℝ => min t C) a,
    ← cfc_comp (fun t : ℝ => min t C) (fun t : ℝ => -min t C) a]
  simp only [Function.comp_def]
  rw [cfc_neg (fun t : ℝ => min (-min t C) C) a]

theorem traceClip_norm_le (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a)
    (C : ℝ) (hC : 0 ≤ C) : ‖traceClip a C‖ ≤ C := by
  rw [traceClip_cfc a ha C]
  apply norm_cfc_le hC
  intro t _
  rw [Real.norm_eq_abs,abs_le]
  constructor
  · exact neg_le_neg (min_le_right _ _)
  · have h : -C ≤ min (-min t C) C :=
      le_min (neg_le_neg (min_le_right _ _)) (by linarith)
    linarith

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The orthogonal subalgebra representative of a self-adjoint ambient
operator is constructed, with its operator norm bound. -/

/-! A bounded trace-preserving subalgebra projection from self-adjoint least-distance points. Tracial orthogonality gives uniqueness and the bimodule identities. -/

/-! The constructed expectation preserves adjoints, is a bimodule map,
and is the orthogonal projection for the trace norm. -/

/-! Positivity of the constructed expectation. The negative spectral part
is an actual subalgebra test operator; tracial orthogonality eliminates it. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
local instance expectationPosCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance expectationPosOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance expectationPosPreorder_r45111e_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance expectationPosLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE

end

/-! The constructed expectation satisfies the Schwarz inequality and is
contractive in operator norm. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
local instance expectationContractiveCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance expectationContractiveOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance expectationContractivePreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance expectationContractiveLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE

end

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Equal-trace finite partitions extend to actual matrix units in the same
factor. The theorem also retains a prescribed corner as the sum of diagonals. -/
open scoped BigOperators

/-! The matrix-unit image in the original represented algebra, with its
finite dimensionality and weak-operator closedness proved. -/
open scoped BigOperators

/-! The actual relative commutant in M is a diffuse scalar-center von
Neumann algebra, with the restricted faithful trace available from M. -/

/-! Explicit Bell projections in two equal finite matrix factors. -/
open scoped BigOperators

/-! Exact normalized traces of constructed matrix algebras and all their
commuting product refinements. -/
open scoped BigOperators
namespace MatrixUnitSystem

open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n : ℕ} [NeZero n]
variable (E F : MatrixUnitSystem (ZMod n) M.toStarSubalgebra)
variable (hc : ∀ i j k l,Commute (E.entry i j) (F.entry k l))

def bellPiece (s f : ZMod n) : AlgebraProjection M :=
  ⟨(E.product F hc).hom (Bell.projection s f),by
    constructor
    · show (E.product F hc).hom (Bell.projection s f) *
        (E.product F hc).hom (Bell.projection s f) = _
      rw [← map_mul,Bell.projection_mul,ite_eq_left ⟨rfl,rfl⟩]
    · show star ((E.product F hc).hom (Bell.projection s f)) = _
      rw [← map_star,Bell.projection_star]⟩

theorem bellPiece_orthogonal (a b : ZMod n × ZMod n) (h : a≠b) :
    (E.bellPiece F hc a.1 a.2).val * (E.bellPiece F hc b.1 b.2).val = 0 := by
  change (E.product F hc).hom _ * (E.product F hc).hom _ = 0
  rw [← map_mul,Bell.projection_mul,ite_eq_right (fun he => h (Prod.ext he.1 he.2)),map_zero]

theorem bellPiece_total :
    (∑ a : ZMod n × ZMod n,(E.bellPiece F hc a.1 a.2).val) = 1 := by
  change (∑ a : ZMod n × ZMod n,(E.product F hc).hom (Bell.projection a.1 a.2))=1
  rw [← map_sum,Fintype.sum_prod_type,Bell.projection_total,map_one]

def bellPartition : CornerPartition (identityProjection M) where
  size := Fintype.card (ZMod n × ZMod n)
  piece i := let a := (Fintype.equivFin (ZMod n × ZMod n)).symm i
    E.bellPiece F hc a.1 a.2
  orthogonal _ _ h := E.bellPiece_orthogonal F hc _ _
    (fun he => h ((Fintype.equivFin (ZMod n × ZMod n)).symm.injective he))
  total := ((Fintype.equivFin (ZMod n × ZMod n)).symm.sum_comp
    (fun a => (E.bellPiece F hc a.1 a.2).val)).trans (E.bellPiece_total F hc)

end MatrixUnitSystem

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixSequence
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Finite matrix stages and a quantified refinement operation, including
zero expectation. Reindexing changes no represented algebra. -/

/-! Iterated compatible full matrix refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/

/-! L2 separability supplies a countable centered dense family. The constructed
matrix sequence has scalar common relative commutant in the ambient algebra. -/

/-! The actual weakly closed star algebra generated by the increasing finite
matrix stages. Its ambient relative commutant is scalar. This does not yet
package a diffuse II1 subfactor or derive the representation hypotheses. -/

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/
section
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def generatedVonNeumann (A : ℕ → FiniteMatrixStage N) : VonNeumannAlgebra H :=
  vonNeumannOfWOTClosed (generated A) (generated_closed A)

end FiniteMatrixStage

end

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixExpectation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Construct contractive expectations onto the actual finite matrix stages.
For every element of their weak closure, these expectations converge in L2
and remain in its operator norm ball. -/
open Filter
open scoped Topology
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def stageVonNeumann (E : FiniteMatrixStage N) : VonNeumannAlgebra H :=
  vonNeumannOfWOTClosed E.units.concreteAlgebra E.units.concreteAlgebra_wotClosed

theorem stageVonNeumann_le (E : FiniteMatrixStage N) : E.stageVonNeumann ≤ N :=
  E.units.concreteAlgebra_le

end FiniteMatrixStage

/-! Construct scalarizing partitions for an actual finite matrix algebra
inside a diffuse finite factor. No chain or pinching hypothesis is assumed. -/

/-! Finite matrix approximation and Bell partitions give actual small
pinching energy. The commuting matrix factor is constructed, not assumed. -/
open Filter
open scoped BigOperators Topology

/-! The actual finite-stage conditional expectations converge strongly and
adjoint-strongly on every vector in the given representation. The generated
algebra also has a constructed separable faithful cyclic Hilbert representation. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_RepresentedCorners
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual corner on pH. Extension by zero identifies its operators with
supported ambient operators; weak closedness is proved by WOT continuity. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (p : AlgebraProjection M)

def cornerSpace : Submodule ℂ H where
  carrier := {x | p.val.val x=x}
  zero_mem' := by simp
  add_mem' hx hy := by simp_all
  smul_mem' c x hx := by simp_all

@[simp] theorem mem_cornerSpace (x : H) : x ∈ cornerSpace p ↔ p.val.val x=x := Iff.rfl

instance cornerSpace_complete : CompleteSpace (cornerSpace p) := by
  have hc : IsClosed (cornerSpace p : Set H) := isClosed_eq p.val.val.continuous continuous_id
  exact hc.completeSpace_coe

def cornerProject : H →L[ℂ] cornerSpace p :=
  p.val.val.codRestrict (cornerSpace p) (fun x => by
    change p.val.val (p.val.val x)=p.val.val x
    exact congrArg (fun a : M.toStarSubalgebra => a.val x) p.property.isIdempotentElem.eq)

@[simp] theorem cornerProject_coe (x : H) : (cornerProject p x).val=p.val.val x := rfl
@[simp] theorem cornerProject_subtype (x : cornerSpace p) : cornerProject p x.val=x :=
  Subtype.ext x.property

theorem cornerProject_inner (x : H) (y : cornerSpace p) :
    inner ℂ (cornerProject p x) y=inner ℂ x y.val := by
  change inner ℂ (p.val.val x) y.val=inner ℂ x y.val
  have hs : star p.val.val=p.val.val := congrArg Subtype.val p.property.isSelfAdjoint.star_eq
  rw [← hs,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left,y.property]

def cornerExtend (a : cornerSpace p →L[ℂ] cornerSpace p) : H →L[ℂ] H :=
  (cornerSpace p).subtypeL.comp (a.comp (cornerProject p))

@[simp] theorem cornerExtend_apply (a : cornerSpace p →L[ℂ] cornerSpace p) (x : H) :
    cornerExtend p a x=(a (cornerProject p x)).val := rfl

@[simp] theorem cornerExtend_zero : cornerExtend p 0=0 := by ext x; rfl
@[simp] theorem cornerExtend_add (a b : cornerSpace p →L[ℂ] cornerSpace p) :
    cornerExtend p (a+b)=cornerExtend p a+cornerExtend p b := by ext x; rfl
@[simp] theorem cornerExtend_smul (c : ℂ) (a : cornerSpace p →L[ℂ] cornerSpace p) :
    cornerExtend p (c • a)=c • cornerExtend p a := by ext x; rfl
@[simp] theorem cornerExtend_one : cornerExtend p 1=p.val.val := by ext x; rfl
@[simp] theorem cornerExtend_mul (a b : cornerSpace p →L[ℂ] cornerSpace p) :
    cornerExtend p (a*b)=cornerExtend p a*cornerExtend p b := by
  ext x
  simp only [mul_apply_eq_comp,cornerExtend_apply,cornerProject_subtype]

@[simp] theorem cornerExtend_star (a : cornerSpace p →L[ℂ] cornerSpace p) :
    cornerExtend p (star a)=star (cornerExtend p a) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [cornerExtend_apply,← cornerProject_inner,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (a (cornerProject p y)) (cornerProject p x)=_
  rw [← inner_conj_symm,cornerProject_inner,inner_conj_symm]
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem cornerExtend_injective : Function.Injective (cornerExtend p) := by
  intro a b hab
  ext x
  have h := congrArg (fun T : H →L[ℂ] H => T x.val) hab
  simpa only [cornerExtend_apply,cornerProject_subtype] using h

@[simp] theorem cornerExtend_left (a : cornerSpace p →L[ℂ] cornerSpace p) :
    p.val.val*cornerExtend p a=cornerExtend p a := by
  ext x
  exact (a (cornerProject p x)).property

@[simp] theorem cornerExtend_right (a : cornerSpace p →L[ℂ] cornerSpace p) :
    cornerExtend p a*p.val.val=cornerExtend p a := by
  rw [← cornerExtend_one p,← cornerExtend_mul,mul_one]

def cornerStarAlgebra : StarSubalgebra ℂ (cornerSpace p →L[ℂ] cornerSpace p) where
  carrier := {a | cornerExtend p a ∈ M}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' ha hb := by simpa using M.add_mem ha hb
  mul_mem' ha hb := by simpa using M.mul_mem ha hb
  algebraMap_mem' c := by
    change cornerExtend p (c • 1) ∈ M
    simpa using M.toStarSubalgebra.smul_mem p.val.property c
  star_mem' ha := by simpa using star_mem ha

theorem cornerExtend_wot_continuous : Continuous (fun a : cornerSpace p →WOT[ℂ] cornerSpace p =>
    ContinuousLinearMapWOT.ofCLM (cornerExtend p a.toCLM)) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro x y
  simp only [ContinuousLinearMapWOT.ofCLM_apply,cornerExtend_apply,← cornerProject_inner]
  exact ContinuousLinearMapWOT.continuous_inner_apply continuous_id _ _

theorem cornerStarAlgebra_wotClosed : WOTClosed (cornerStarAlgebra p) :=
  (vonNeumann_wotClosed M).preimage (cornerExtend_wot_continuous p)

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_ResidualEstimates
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Correct residual-corner trace identity for arbitrary f. The first term
is trace(f*x), not trace(x); they agree when f=1. This is the distinction
at Popa 1308.3982v3 Lemma 3.2, equation (5). -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def residualCorner (f : AlgebraProjection M) (v : PartialUnitary M) (hv : v.support ≤ f) :
    AlgebraProjection M :=
  ⟨f.val-v.support.val,v.support.property.sub_of_mul_eq_right f.property hv⟩

end

/-! The justified f=1 scalar estimate in the support-growth argument.
Every estimate is tied to the current partial unitary's actual residual;
there is no arbitrary-corner centering assertion. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def unitResidual (v : PartialUnitary M) : AlgebraProjection M :=
  ⟨1-v.support.val,v.support.property.one_sub⟩

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_LocalPatches
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_CornerIndependence
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_ResidualCompletion
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_CoordinateUnitaries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Complete each supported partial unitary by the identity on its orthogonal
complement. If the quotient support is one, the quotient value is unchanged. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def PartialUnitary.completed (v : PartialUnitary M) : M.toStarSubalgebra :=
  v.val+(1-v.support.val)

end

/-! Ordered independence with actual coordinate unitaries in the included
algebra, obtained by completing the constructed partial-unitary coordinates. -/

/-! Two coordinate-unitary witnesses produce the reduced-moment Haar precursor
while retaining actual unitary coordinates in the included algebra. -/

/-! Full integer endpoint moments and an actual included coordinate-unitary
Haar witness, before imposing an operator topology on generated algebras. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MonotoneTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Bounded positive monotone nets have actual least upper bounds in M.
Every displayed vector-trace bound passes to the constructed bound. -/
section
open Filter
open scoped Topology
namespace Tracial

/-! Positivity, order, and faithfulness of the actual vector trace, using
ambient operator order throughout. No identification with subtype spectral
order is needed. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem ambient_sqrt_mem (a : M.toStarSubalgebra) (ha : 0 ≤ a.val) :
    CFC.sqrt a.val ∈ M.toStarSubalgebra := by
  let : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := base_norm_closed M
  rw [CFC.sqrt_eq_real_sqrt a.val ha, cfcₙ_eq_cfc Real.continuous_sqrt.continuousOn]
  exact cfc_mem (𝕜' := ℂ) Real.sqrt a.property

end Tracial

end

/-! Absolute values in the represented algebra, with ambient order bounds
and the actual trace two-norm. -/
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def ambientAbsoluteValue (a : M.toStarSubalgebra) : M.toStarSubalgebra :=
  ⟨CFC.abs a.val, ambient_sqrt_mem (star a*a) (star_mul_self_nonneg a.val)⟩

end Tracial

/-! The bounded monotone transform a ↦ 1 - (1+a)⁻¹ of positive operators.
Its bounds prepare a construction of decreasing order majorants from small
trace tails. No tail majorant or predual continuity is asserted here. -/

/-! Decreasing positive order majorants for positive contractions with
summable trace. The finite-tail resolvents and their least upper bounds are
constructed in the actual algebra. -/
open Filter
open scoped Topology BigOperators
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def algebraPositiveResolvent (a : M.toStarSubalgebra) : M.toStarSubalgebra := by
  let : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := base_norm_closed M
  exact ⟨positiveResolvent a.val,
    cfc_mem (𝕜' := ℂ) (fun t : ℝ => 1 - (1+t)⁻¹) a.property⟩

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A genuine linear state with exact equality of real quadratic values,
constructed from the original finite factor predicates by scalar compactness. -/

/-! Construction of a tracial state on the original concrete finite diffuse factor without a supplied trace. -/

/-! Every positive normalized tracial functional agrees with the dimension on
all projections. Lower and upper dyadic bounds use actual partial isometries. -/

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance dominationCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance dominationOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance dominationPreorder_r45111e_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance dominationLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance dominationStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceNormalCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceNormalOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceNormalPreorder_r45111e_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance traceNormalLE_r45111e_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance traceNormalStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_TraceHilbert
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A separate type with the constructed trace inner product. Its norm is the
trace two-norm; the original concrete algebra retains its operator norm.
Lean's inner product is linear in the second argument. -/

/-! The trace two-norm bound for left multiplication uses the original
operator norm and positivity of a concrete sandwich. -/

/-! Bounded left multiplication on the actual constructed trace Hilbert space.
All representation laws are proved on its dense algebraic subspace. -/

/-! Bounded right multiplication and its commutation with the constructed
left action. These supply separation on the actual double commutant. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertRightCStar : CStarAlgebra M.toStarSubalgebra := {}

end

/-! The actual double commutant of the new representation, with a constructed
faithful tracial vector. Equality with the original image is a later theorem. -/

/-! The constructed representation is WOT continuous on every original
operator-norm ball. This does not assert whole-carrier WOT continuity. -/
open scoped ComplexConjugate CStarAlgebra BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertWOTCStar : CStarAlgebra M.toStarSubalgebra := {}

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_TraceTransport
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Literal weak-operator generation under a concrete star-algebra isomorphism.
Continuity is explicitly for the restricted WOT, not the operator norm topology.
This transport does not construct a trace representation of a finite factor. -/

/-! Compact original image balls and spectral clipping identify the actual
bicommutant with the original algebra's represented image. -/
open Filter
open scoped ComplexConjugate ComplexStarModule CStarAlgebra Pointwise Topology
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertImageCStar : CStarAlgebra M.toStarSubalgebra := {}

end

/-! Algebraic and isometric transport of factor structure and existential Banach preduals. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertTransportCStar : CStarAlgebra M.toStarSubalgebra := {}

end Tracial

/-! First step of generation transport: compact balls and closed vector balls
for the represented intersection with any original WOT-closed subalgebra. -/
open Filter
open scoped Topology CStarAlgebra
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceSubalgebraBallCStar : CStarAlgebra M.toStarSubalgebra := {}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

variable (Q : StarSubalgebra ℂ (H →L[ℂ] H))

local instance traceSubalgebraBallOrder_r45111e_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceSubalgebraBallStarOrder_r45111e_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
theorem traceClip_mem_original (hQ : WOTClosed Q) (a : M.toStarSubalgebra)
    (haQ : a.val ∈ Q) (ha : IsSelfAdjoint a) (C : ℝ) : (traceClip a C).val ∈ Q := by
  let P := Q.comap M.toStarSubalgebra.subtype
  let : IsClosed (P : Set M.toStarSubalgebra) :=
    (hQ.preimage ContinuousLinearMapWOT.continuous_ofCLM).preimage continuous_subtype_val
  change traceClip a C ∈ P
  rw [traceClip_cfc a ha C]
  exact cfc_mem (𝕜' := ℂ) (fun t : ℝ => -min (-min t C) C) haQ

end Tracial

/-! Closed images of original WOT-closed subalgebras in the constructed representation. -/
open Filter
open scoped Topology CStarAlgebra ComplexStarModule
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceSubalgebraImageCStar : CStarAlgebra M.toStarSubalgebra := {}

end

/-! Generation pullback for the actual constructed trace representation. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceGenerationTransportCStar : CStarAlgebra M.toStarSubalgebra := {}

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.RelativeGeneration_OriginalUnitary
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

/- Normalized trace-two topology on actual unitaries of the original factor.
   The wrapper avoids Mathlib's existing operator-norm topology on unitary S. -/
open scoped Topology
namespace Generator
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {S : StarSubalgebra ℂ (H →L[ℂ] H)}

open Tracial
variable (S) (hS : IsII1Factor S)
local notation "hf" => hS.factor_smul
local notation "hu" => hS.one_ne_zero

namespace FactorTraceUnitary

/-- Forgetting the metric wrapper preserves every genuine unitary of the original factor. -/
def unitaryEquiv : FactorTraceUnitary S hS ≃ unitary S where
  toFun := toUnitary
  invFun element := ⟨element⟩
  left_inv element := by cases element; rfl
  right_inv element := rfl

end FactorTraceUnitary
end Generator

end

end OAI
end


