-- Prove2me | Definitions.Def_OAIQ129G011
-- name    : OAIQ129G011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T20:37:03.411005+00:00
-- url     : https://prove2.me/theorems/79c7cc36-df7d-4868-84a5-854a215fcf13
-- title:
--   Definitions bundle OAIQ129G011 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 73 declarations of OpenAI's Lean: 42 definitions, 2 inductive types or structures, 5 instances and 24 theorems. The definitions and types are `OAI.Generator.FiniteMatrixStage.energy`, `OAI.Generator.FiniteMatrixStage.stageExpectation`, `OAI.Generator.Tracial.CoordinateHaarData`, `OAI.Generator.Tracial.CornerPartition.scalarEnergy`, `OAI.Generator.Tracial.ExactOrderedMoments`, `OAI.Generator.Tracial.HaarEndpoints`, `OAI.Generator.Tracial.L2`, `OAI.Generator.Tracial.PatchingAdmissible`, `OAI.Generator.Tracial.PatchingAdmissibleIn`, `OAI.Generator.Tracial.ProductGaps`, `OAI.Generator.Tracial.ReducedIntegerGaps`, `OAI.Generator.Tracial.ReducedOrderedMoments`, `OAI.Generator.Tracial.RelativePolynomial.eval`, `OAI.Generator.Tracial.RelativePolynomial.sectionVector`, `OAI.Generator.Tracial.RelativePolynomial.valueAlgebra`, `OAI.Generator.Tracial.SignedReducedGaps`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.commonPerturbation`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.coordinatePrefix`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.coordinateTarget`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.coordinateVariables`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.haarSequence`, `OAI.Generator.Tracial.boundedCompletedUnitary`, `OAI.Generator.Tracial.boundedPartialUnitary`, `OAI.Generator.Tracial.boundedToSequence`, `OAI.Generator.Tracial.boundedUnitarySequence`, `OAI.Generator.Tracial.conditionalExpectation`, `OAI.Generator.Tracial.constantQuotient`, `OAI.Generator.Tracial.constantSequence`, `OAI.Generator.Tracial.constantSequenceUnitary`, `OAI.Generator.Tracial.cornerScalar`, `OAI.Generator.Tracial.inclusion`, `OAI.Generator.Tracial.integerValueWord`, `OAI.Generator.Tracial.quotientInnerCore`, `OAI.Generator.Tracial.quotientL2AddCommGroup`, `OAI.Generator.Tracial.quotientL2AddCommMonoid`, `OAI.Generator.Tracial.quotientOperatorAlgebra`, `OAI.Generator.Tracial.quotientOperatorNonAssocSemiring`, `OAI.Generator.Tracial.quotientOperatorSemiring`, `OAI.Generator.Tracial.relativeGenerated` and 4 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_CoordinatePerturbation`, `FactorGeneration_CoordinateUnitaries`, `FactorGeneration_CornerTrace`, `FactorGeneration_Expectations`, `FactorGeneration_HaarPatches`, `FactorGeneration_HaarSequences`, `FactorGeneration_LaurentMoments`, `FactorGeneration_MatrixExpectation`, `FactorGeneration_MatrixSequence`, `FactorGeneration_PatchingWords`, `FactorGeneration_Pinching`, `FactorGeneration_ProductWords`, `FactorGeneration_QuotientHilbert`, `FactorGeneration_QuotientRepresentation`, `FactorGeneration_RelativeGeneration`, `FactorGeneration_ResidualMoments`, `FactorGeneration_Ultrapower`.
--
--   **Imports.** It imports the published bundle `Def_FactorGeneration`; the bundles `OAIQ129G008` and `OAIQ129G009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ129G013` and `OAIQ129G014`; the statements `OAI.Generator.FiniteMatrixStage.exists_finite_matrix_energy_budget_q129`, `OAI.Generator.FiniteMatrixStage.exists_tensor_iterated_energy_descent_q129`, `OAI.Generator.Tracial.exists_coordinate_ordered_unitary_q129`, `OAI_Generator_Tracial_exists_quotient_corner_partial_sequence_q129`, `OAI_Generator_Tracial_exists_residual_quotient_increment_q129` and `OAI.Generator.Tracial.nonempty_successiveCoordinateHaar_q129`; the proofs of `OAI.Generator.Tracial.exists_finite_partial_independence_q129` and `OAI_Generator_Tracial_exists_quotient_corner_partial_sequence_q129`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ129G008
import Definitions.Def_OAIQ129G009

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Ultrapower
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace UltrapowerBridge

section
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (l : Filter ℕ)

instance (priority := high) q129StarMul : StarMul (TracialQuotient τ l) := inferInstance
instance (priority := high) q129UGroup : Group (unitary (TracialQuotient τ l)) := inferInstance
instance (priority := high) q129UDivInvMonoid : DivInvMonoid (unitary (TracialQuotient τ l)) := inferInstance

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_CornerTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

/-- The scalar conditional expectation in pMp, expressed in ambient coordinates. -/
def cornerScalar (p : AlgebraProjection M) (x : M.toStarSubalgebra) : ℂ :=
  τ.trace (p.val*x*p.val) / τ.trace p.val

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_PatchingWords
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
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

def PatchingAdmissible (f : AlgebraProjection M) (F : Set M.toStarSubalgebra)
    (n : ℕ) (ε : ℕ → ℝ) (v : PartialUnitary M) : Prop :=
  v.support ≤ f ∧ ∀ x₀ ∈ F ∪ {1}, ∀ xs : List (Bool × M.toStarSubalgebra),
    1 ≤ xs.length → xs.length ≤ n → patchingCoefficients F xs →
      ‖τ.trace (x₀*patchingWord v.val xs)‖ ≤ ε xs.length*(τ.trace v.support.val).re

end

/-! The error-constrained partial unitaries stay in the prescribed algebra P,
while all word coefficients and the trace live in M. This prevents replacing
the source inclusion P subset M by the trivial inclusion M subset M. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M P : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hPM : P ≤ M)

include hPM

def PatchingAdmissibleIn (f : AlgebraProjection M) (F : Set M.toStarSubalgebra)
    (n : ℕ) (ε : ℕ → ℝ) (v : PartialUnitary M) : Prop :=
  PatchingAdmissible τ f F n ε v ∧ v.val.val ∈ P

end

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
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
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

/-! Actual finite refinement of a corner partition by partitions of its blocks.
The dependent family of block sizes is flattened without changing any piece.
No small-energy partition is an input to these constructions. -/

/-! Centered energy and the block scalar term that refinement preserves.
A blockwise descent applies to centered compressions, not to their full energy. -/

/-! Energy of compatible block refinements, including the scalar term.
The scalar term is necessary even when the original operator has trace zero. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)
variable (R : (i : Fin Q.size) → CornerPartition (Q.piece i))

/-- The part of the compression energy fixed by the current block traces. -/
def scalarEnergy (x : M.toStarSubalgebra) : ℝ :=
  ∑ i, ‖cornerScalar τ (Q.piece i) x‖^2 * (τ.trace (Q.piece i).val).re

end CornerPartition

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
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
section
open scoped ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem exists_selfAdjoint_expectation (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    ∃ c : N.toStarSubalgebra, IsSelfAdjoint c ∧ ‖c‖ ≤ ‖x‖ ∧
      TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-coordinateInclusion hNM c) := by
  obtain ⟨c,hc,hcR,hmin,hvar⟩ := exists_selfAdjoint_ball_variational τ hNM x (‖x‖+1)
    (by positivity)
  have hcn := selfAdjoint_ball_minimum_norm τ hNM x hx (‖x‖+1) c hc hcR hmin
  let r := x-coordinateInclusion hNM c
  have hr : IsSelfAdjoint r := hx.sub (included_selfAdjoint hNM c hc)
  have hreal (a : N.toStarSubalgebra) (ha : IsSelfAdjoint a) :
      (τ.trace (coordinateInclusion hNM a*r)).re=0 := by
    let t : ℝ := 1/(‖a‖+1)
    have ht : 0<t := by dsimp [t]; positivity
    have hta : ‖t • a‖ ≤ 1 := by
      rw [norm_smul,Real.norm_of_nonneg ht.le]
      dsimp [t]
      rw [one_div_mul_eq_div,div_le_one (by positivity)]
      linarith [norm_nonneg a]
    have hp := hvar (c+t • a) (hc.add ((IsSelfAdjoint.all t).smul ha))
      ((norm_add_le _ _).trans (by linarith))
    have hm := hvar (c-t • a) (hc.sub ((IsSelfAdjoint.all t).smul ha))
      ((norm_sub_le _ _).trans (by linarith))
    have hep : c+t • a-c=t • a := by abel
    have hem : c-t • a-c=-(t • a) := by abel
    rw [hep,← Complex.coe_smul,map_smul,map_smul,inner_smul_right] at hp
    rw [hem,map_neg,map_neg,inner_neg_right,← Complex.coe_smul,map_smul,map_smul,inner_smul_right] at hm
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.neg_re] at hp hm
    change t*(inner ℂ (baseVector τ r) (baseVector τ (coordinateInclusion hNM a))).re ≤ 0 at hp
    change -(t*(inner ℂ (baseVector τ r) (baseVector τ (coordinateInclusion hNM a))).re) ≤ 0 at hm
    have hzero : (inner ℂ (baseVector τ r) (baseVector τ (coordinateInclusion hNM a))).re=0 := by
      nlinarith
    rw [baseVector_inner_trace,hr.star_eq,τ.trace_mul_comm] at hzero
    exact hzero
  have hSA (a : N.toStarSubalgebra) (ha : IsSelfAdjoint a) :
      τ.trace (coordinateInclusion hNM a*r)=0 :=
    Complex.ext (hreal a ha) (selfAdjoint_pairing_im τ _ r (included_selfAdjoint hNM a ha) hr)
  refine ⟨c,hc,hcn,?_⟩
  intro a
  let aN : N.toStarSubalgebra := ⟨(a : M.toStarSubalgebra).val,a.property⟩
  have hd := realPart_add_I_smul_imaginaryPart aN
  have he : (a : M.toStarSubalgebra)=coordinateInclusion hNM
      ((ℜ aN : N.toStarSubalgebra)+Complex.I • (ℑ aN : N.toStarSubalgebra)) := by
    rw [hd]; rfl
  change τ.trace ((a : M.toStarSubalgebra)*r)=0
  rw [he,map_add,map_smul,add_mul,smul_mul_assoc,cornerTrace_add,cornerTrace_smul,
    hSA _ (ℜ aN).property,hSA _ (ℑ aN).property,mul_zero,add_zero]

end

/-! A bounded trace-preserving subalgebra projection from self-adjoint least-distance points. Tracial orthogonality gives uniqueness and the bimodule identities. -/
section
open scoped ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

namespace TraceOrthogonal
variable {P : StarSubalgebra ℂ M.toStarSubalgebra} {x y : M.toStarSubalgebra}
theorem sub (hx : TraceOrthogonal τ P x) (hy : TraceOrthogonal τ P y) :
    TraceOrthogonal τ P (x-y) := by
  intro a
  rw [mul_sub,trace_sub,hx a,hy a,sub_self]
end TraceOrthogonal

theorem exists_bounded_subalgebra_representative (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    ∃ y : M.toStarSubalgebra, y.val ∈ N ∧ ‖y‖ ≤ 2*‖x‖ ∧
      TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-y) := by
  obtain ⟨a,ha,hna,hoa⟩ := exists_selfAdjoint_expectation τ hNM (ℜ x) (ℜ x).property
  obtain ⟨b,hb,hnb,hob⟩ := exists_selfAdjoint_expectation τ hNM (ℑ x) (ℑ x).property
  let y := coordinateInclusion hNM a+Complex.I • coordinateInclusion hNM b
  refine ⟨y,N.add_mem a.property (N.smul_mem b.property _),?_,?_⟩
  · calc ‖y‖ ≤ ‖a‖+‖b‖ := by
           change ‖y‖ ≤ ‖coordinateInclusion hNM a‖+‖coordinateInclusion hNM b‖
           simpa only [y,norm_smul,Complex.norm_I,one_mul] using
             norm_add_le (coordinateInclusion hNM a) (Complex.I • coordinateInclusion hNM b)
         _ ≤ 2*‖x‖ := by
           have hr := hna.trans (realPart.norm_le x)
           have hi := hnb.trans (imaginaryPart.norm_le x)
           linarith
  · have h := hoa.add τ (hob.smul τ Complex.I)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [y]
    rw [smul_sub]
    nth_rw 1 [← realPart_add_I_smul_imaginaryPart x]
    abel

def conditionalExpectation (hNM : N ≤ M) (x : M.toStarSubalgebra) : M.toStarSubalgebra :=
  (exists_bounded_subalgebra_representative τ hNM x).choose

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
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace FiniteMatrixStage
open Tracial
variable {N M : VonNeumannAlgebra H}

def energy (E : FiniteMatrixStage N) (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) : ℝ :=
  τ.norm₂ (conditionalExpectation τ (E.commutant_le hNM) x)^2

end FiniteMatrixStage

end

/-! Iterated compatible full matrix refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/

/-! L2 separability supplies a countable centered dense family. The constructed
matrix sequence has scalar common relative commutant in the ambient algebra. -/

/-! The actual weakly closed star algebra generated by the increasing finite
matrix stages. Its ambient relative commutant is scalar. This does not yet
package a diffuse II1 subfactor or derive the representation hypotheses. -/

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/

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

def stageExpectation (E : FiniteMatrixStage N) (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) : M.toStarSubalgebra :=
  conditionalExpectation τ (E.stageVonNeumann_le.trans hNM) x

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_HaarPatches
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The same ordered signed words in any star algebra, with exact transport
through bounded sequence evaluation and the actual quotient homomorphism. -/

/-! The finite-error f=1 conclusion of Popa Lemma 3.2, for the irreducible
scalar-commutant inclusion with the explicit represented-factor hypotheses. -/

/-! A countable diagonal construction with actual vanishing ordered moments.
The countable coefficients may vary with the sequence coordinate. -/
open Filter
open scoped Topology

/-! Actual positive-support partial independence in the bounded-sequence
tracial quotient. Freeness is expressed by domination of atTop. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def boundedPartialUnitary (v : ℕ → PartialUnitary M) : Bounded M :=
  ⟨fun j => (v j).val,1,zero_le_one,fun j => (v j).unitary.norm_le_one⟩

end

/-! Exact multilinearity factors for ordered words; no factors are inverted
and signs affect only the partial-unitary letters. -/

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_QuotientHilbert
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.restrictedTrace_norm₂ _root_.OAI.Generator.Tracial.restrictedTrace_trace _root_.OAI.Generator.Tracial.traceCyclicOperator_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual trace Hilbert completion of the bounded-sequence tracial quotient.
The vector-trace representation is explicit data; its existence for an arbitrary
factor is not asserted here. No free-independence premise occurs. -/
open Filter
open scoped Topology ComplexConjugate
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def traceLinear : Q τ ω →ₗ[ℂ] ℂ where
  toFun := quotientTrace τ ω
  map_add' := trace_add τ ω
  map_smul' := trace_smul τ ω

theorem trace_pair (a b : M.toStarSubalgebra) :
    τ.trace (star a*b) = inner ℂ ((a : H →L[ℂ] H) τ.vector)
      ((b : H →L[ℂ] H) τ.vector) := by
  unfold TracialRepresentation.trace
  change inner ℂ τ.vector ((star (a : H →L[ℂ] H)) ((b : H →L[ℂ] H) τ.vector)) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

theorem trace_pair_conj (a b : Q τ ω) :
    star (quotientTrace τ ω (star b*a)) = quotientTrace τ ω (star a*b) := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      change star (traceRep τ ω (star b*a)) = traceRep τ ω (star a*b)
      apply tendsto_nhds_unique ((traceRep_tendsto τ ω (star b*a)).star)
      have ht := traceRep_tendsto τ ω (star a*b)
      change Tendsto (fun n => τ.trace (star (a.val n)*b.val n)) _ _ at ht
      change Tendsto (fun n => star (τ.trace (star (b.val n)*a.val n))) _ _
      convert ht using 1
      all_goals try with_reducible_and_instances rfl
      funext n
      simp only [trace_pair]
      exact inner_conj_symm _ _

theorem trace_square_nonneg (a : Q τ ω) :
    0 ≤ (quotientTrace τ ω (star a*a)).re := by
  induction a using Quotient.inductionOn with
  | h a =>
    have ht := Complex.continuous_re.continuousAt.tendsto.comp (traceRep_tendsto τ ω (star a*a))
    change 0 ≤ (traceRep τ ω (star a*a)).re
    apply ge_of_tendsto ht
    exact Eventually.of_forall (fun n => by
      change 0 ≤ (τ.trace (star (a.val n)*a.val n)).re
      rw [τ.trace_star_mul]
      simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using sq_nonneg (τ.norm₂ (a.val n)))

/-- The quotient two-norm is the ultralimit of the coordinate two-norms. -/
theorem norm₂_tendsto (a : Bounded M) :
    Tendsto (fun n => τ.norm₂ (a.val n)) (ω : Filter ℕ)
      (𝓝 (Real.sqrt (quotientTrace τ ω (star (quotientMap τ (ω : Filter ℕ) a) *
        quotientMap τ (ω : Filter ℕ) a)).re)) := by
  change Tendsto (fun n => τ.norm₂ (a.val n)) (ω : Filter ℕ)
    (𝓝 (Real.sqrt (traceRep τ ω (star a*a)).re))
  have ht := (Complex.continuous_re.continuousAt.tendsto.comp (traceRep_tendsto τ ω (star a*a))).sqrt
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  change τ.norm₂ (a.val n) = Real.sqrt (τ.trace (star (a.val n)*a.val n)).re
  rw [τ.trace_star_mul, ← Complex.ofReal_pow, Complex.ofReal_re]
  exact (Real.sqrt_sq (show 0 ≤ τ.norm₂ (a.val n) from norm_nonneg _)).symm

theorem trace_square_faithful (a : Q τ ω)
    (ha : quotientTrace τ ω (star a*a) = 0) : a = 0 := by
  induction a using Quotient.inductionOn with
  | h a =>
    change quotientMap τ (ω : Filter ℕ) a = quotientMap τ (ω : Filter ℕ) 0
    apply (quotientMap_eq_iff τ (ω : Filter ℕ) a 0).mpr
    have ht := norm₂_tendsto τ ω a
    change quotientTrace τ ω (star (quotientMap τ (ω : Filter ℕ) a) *
      quotientMap τ (ω : Filter ℕ) a) = 0 at ha
    simpa [TraceRel, ha] using ht

/-- The norm here is the trace norm, not the operator norm. -/
@[instance_reducible] def quotientInnerCore : InnerProductSpace.Core ℂ (Q τ ω) where
  inner a b := quotientTrace τ ω (star a*b)
  conj_inner_symm := trace_pair_conj τ ω
  re_inner_nonneg := trace_square_nonneg τ ω
  add_left a b c := by simp only [star_add, add_mul, trace_add]
  smul_left a b c := by simp only [star_smul, smul_mul_assoc, trace_smul]; rfl
  definite := trace_square_faithful τ ω

instance quotientNormedAddCommGroup : NormedAddCommGroup (Q τ ω) :=
  (quotientInnerCore τ ω).toNormedAddCommGroup
instance quotientInnerProductSpace : InnerProductSpace ℂ (Q τ ω) :=
  .ofCore { quotientInnerCore τ ω with }

@[simp] theorem inner_eq_trace (a b : Q τ ω) :
    inner ℂ a b = quotientTrace τ ω (star a*b) := rfl

/-- Genuine complete complex Hilbert space for the quotient trace. -/
abbrev L2 := UniformSpace.Completion (Q τ ω)

def inclusion : Q τ ω →ₗᵢ[ℂ] L2 τ ω :=
  UniformSpace.Completion.toComplₗᵢ

@[simp] theorem inclusion_inner (a b : Q τ ω) :
    inner ℂ (inclusion τ ω a) (inclusion τ ω b) = quotientTrace τ ω (star a*b) := by
  exact UniformSpace.Completion.inner_coe (𝕜 := ℂ) a b

end

/-! Centering actual bounded representatives changes no centered quotient
class. Every such class is a nonzero scalar multiple of a coordinatewise
centered contraction representative. -/
open Filter
open scoped Topology

/-! Trace Cauchy–Schwarz and unitary invariance on the tracial quotient. -/
open Filter
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

@[simp] theorem quotient_norm_one : ‖(1 : Q τ ω)‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_eq_trace, star_one, one_mul, quotientTrace_one]
  norm_num

@[simp] theorem quotient_trace_sub (a b : Q τ ω) :
    quotientTrace τ ω (a-b) = quotientTrace τ ω a-quotientTrace τ ω b :=
  (traceLinear τ ω).map_sub a b

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ResidualMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Valid residual-corner identities in the actual quotient. Compression
centering requires two exact moments; global centering alone is insufficient. -/

/-! A countable family containing every original coefficient and every old
nonempty ordered signed word, with both optional endpoints retained. -/

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

/-! Exact preservation of every original ordered moment under orthogonal
patching, once the constructed cyclic residual family has exact moments. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ProductWords
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

/-! Expand positive-length signed powers into individual letters. Repeated
letters have unit gaps; boundaries between powers retain centered coefficients. -/

open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_QuotientRepresentation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.restrictedTrace_norm₂ _root_.OAI.Generator.Tracial.restrictedTrace_trace _root_.OAI.Generator.Tracial.traceCyclicOperator_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

/-- The actual star-algebra quotient map on complete bounded sequences. -/
def sequenceQuotient : Sequences M →⋆ₐ[ℂ] Q τ ω :=
  (quotientStarAlgHom τ (ω : Filter ℕ)).comp boundedMap

theorem sequence_norm_tendsto (a : Sequences M) :
    Tendsto (fun n => τ.norm₂ (a n)) (ω : Filter ℕ) (𝓝 ‖sequenceQuotient τ ω a‖) := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_eq_trace]
  exact norm₂_tendsto τ ω (boundedMap a)

theorem sequenceQuotient_norm_le (a : Sequences M) :
    ‖sequenceQuotient τ ω a‖ ≤ ‖a‖ := by
  apply le_of_tendsto (sequence_norm_tendsto τ ω a)
  exact Eventually.of_forall (fun n => (τ.norm₂_le_norm (a n)).trans (a.norm_coe_le_norm n))

/-- The continuous Hilbert realization used by the analytic remainder theorem. -/
def sequenceInclusion : Sequences M →L[ℂ] L2 τ ω :=
  LinearMap.mkContinuous
    { toFun := fun a => inclusion τ ω (sequenceQuotient τ ω a)
      map_add' := by intros; simp only [map_add]
      map_smul' := by intros; simp only [map_smul]; rfl } 1
    (by
      intro a
      change ‖inclusion τ ω (sequenceQuotient τ ω a)‖ ≤ 1*‖a‖
      rw [LinearIsometry.norm_map, one_mul]
      exact sequenceQuotient_norm_le τ ω a)

@[simp] theorem sequenceInclusion_apply (a : Sequences M) :
    sequenceInclusion τ ω a = inclusion τ ω (sequenceQuotient τ ω a) := rfl

end

/-! The faithful constant embedding into the tracial quotient, with its trace and trace norm, for every ultrafilter. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def constantSequence : M.toStarSubalgebra →⋆ₐ[ℂ] Sequences M where
  toFun := BoundedContinuousFunction.const ℕ
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def constantQuotient : M.toStarSubalgebra →⋆ₐ[ℂ] Q τ ω :=
  (sequenceQuotient τ ω).comp constantSequence

@[simp] theorem constantQuotient_trace (a : M.toStarSubalgebra) :
    quotientTrace τ ω (constantQuotient τ ω a) = τ.trace a := by
  exact tendsto_nhds_unique (traceRep_tendsto τ ω (boundedMap (constantSequence a)))
    tendsto_const_nhds

@[simp] theorem constantQuotient_norm (a : M.toStarSubalgebra) :
    ‖constantQuotient τ ω a‖ = τ.norm₂ a := by
  exact tendsto_nhds_unique (sequence_norm_tendsto τ ω (constantSequence a)) tendsto_const_nhds

@[simp] theorem constantQuotient_inner (a b : M.toStarSubalgebra) :
    inner ℂ (inclusion τ ω (constantQuotient τ ω a))
      (inclusion τ ω (constantQuotient τ ω b)) = τ.trace (star a*b) := by
  rw [inclusion_inner, ← map_star, ← map_mul, constantQuotient_trace]

end

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
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

@[instance_reducible] def quotientL2AddCommMonoid : AddCommMonoid (L2 τ ω) :=
  (inferInstance : NormedAddCommGroup (L2 τ ω)).toAddCommGroup.toAddCommMonoid

@[instance_reducible] def quotientL2AddCommGroup : AddCommGroup (L2 τ ω) :=
  (inferInstance : NormedAddCommGroup (L2 τ ω)).toAddCommGroup

attribute [local instance] quotientL2AddCommMonoid quotientL2AddCommGroup

@[instance_reducible] def quotientOperatorSemiring : Semiring (L2 τ ω →L[ℂ] L2 τ ω) :=
  (inferInstance : NormedRing (L2 τ ω →L[ℂ] L2 τ ω)).toRing.toSemiring

@[instance_reducible] def quotientOperatorNonAssocSemiring : NonUnitalNonAssocSemiring (L2 τ ω →L[ℂ] L2 τ ω) :=
  (inferInstance : NormedRing (L2 τ ω →L[ℂ] L2 τ ω)).toRing.toSemiring.toNonUnitalSemiring.toNonUnitalNonAssocSemiring

attribute [local instance] quotientOperatorSemiring quotientOperatorNonAssocSemiring

@[instance_reducible] def quotientOperatorAlgebra : Algebra ℂ (L2 τ ω →L[ℂ] L2 τ ω) :=
  ContinuousLinearMap.algebra

attribute [local instance] quotientOperatorAlgebra

theorem quotientOperatorSemitopology : IsSemitopologicalSemiring (L2 τ ω →L[ℂ] L2 τ ω) :=
  inferInstance

end

/-! Fixed-index selection for bounded coordinate representatives. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_LaurentMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Extend exact moments by separate trace continuity in the two-norm. No
joint continuity of quotient multiplication, or operator-norm structure on Q,
is assumed. -/
section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

/-! Extend exact moments by separate trace continuity in the two-norm. No
joint continuity of quotient multiplication, or operator-norm structure on Q,
is assumed. -/

def integerValueWord (v : unitary (Q τ ω)) (n : ℤ) : List (Q τ ω × ℤ) → Q τ ω → Q τ ω
  | [],b => (↑(v^n) : Q τ ω)*b
  | (d,m)::xs,b => (↑(v^n) : Q τ ω)*d*integerValueWord v m xs b

end

/-! Construct an included Haar unitary and the full nonzero-integer endpoint
formula over any two-norm-separable unital subalgebra of the actual quotient. -/

/-! Extend a trace identity in each factor to the closed linear span of its
allowed values. This uses separate continuity only. -/

/-! Construct an included Haar unitary and the full nonzero-integer endpoint
formula over any two-norm-separable unital subalgebra of the actual quotient. -/

/-! From the endpoint formula to every alternating word shape. -/
open UltrapowerBridge Filter

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

def boundedCompletedUnitary (u : ℕ → PartialUnitary M) : Bounded M :=
  boundedPartialUnitary u+(1-boundedPartialSupport u)

@[simp] theorem boundedCompletedUnitary_apply (u : ℕ → PartialUnitary M) (j : ℕ) :
    (boundedCompletedUnitary u).val j=(u j).completed := rfl

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_HaarSequences
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! One constructed Haar extension retains endpoint moments, represented
norm-closed freeness, and an actual unitary sequence in the included algebra. -/
section
attribute [local instance] quotientL2AddCommMonoid quotientL2AddCommGroup
  quotientOperatorSemiring quotientOperatorNonAssocSemiring quotientOperatorAlgebra
  quotientOperatorSemitopology
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

/-- Full endpoint formula; the internal factors alone must be centered. -/
def HaarEndpoints (D : Subalgebra ℂ (Q τ ω)) (t : unitary (Q τ ω)) : Prop :=
  ∀ c ∈ D,∀ d ∈ D,∀ n : ℤ,n ≠ 0 → ∀ xs : List (Q τ ω × ℤ),
    (∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧ z.2 ≠ 0) →
    quotientTrace τ ω (c*integerValueWord τ ω t n xs d)=0

structure CoordinateHaarData (hNM : N ≤ M) (D : Subalgebra ℂ (Q τ ω)) where
  t : unitary (Q τ ω)
  coordinates : Bounded N
  unitary_coordinates : ∀ j,coordinates.val j ∈ unitary N.toStarSubalgebra
  represents : quotientInclusion τ hNM (ω : Filter ℕ)
    (quotientMap (restrictedTrace τ hNM) (ω : Filter ℕ) coordinates)=(t : Q τ ω)
  endpoints : HaarEndpoints τ ω D t

end

/-! Scalar expansion of same-sign gaps. Opposite-sign gaps must be centered,
so deleting a scalar gap can never cancel an entire power. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def ReducedIntegerGaps (D : Subalgebra ℂ (Q τ ω)) : ℤ → List (Q τ ω × ℤ) → Prop
  | _,[] => True
  | n,(d,m)::xs => d ∈ D ∧ m ≠ 0 ∧
      (quotientTrace τ ω d=0 ∨ SamePowerSign n m) ∧ ReducedIntegerGaps D m xs

/-! Expand nonzero integer powers into signs while retaining the exact rule:
only an equal-sign gap may have a nonzero scalar part. -/

def SignedReducedGaps (D : Subalgebra ℂ (Q τ ω)) : Bool → List (Q τ ω × Bool) → Prop
  | _,[] => True
  | s,(d,t)::xs => d ∈ D ∧ (s ≠ t → quotientTrace τ ω d=0) ∧ SignedReducedGaps D t xs

end

/-! Absorption of base-algebra unitaries, with signed scalar gap expansions. -/

/-! Successive Haar choices in algebraic star subalgebras of the tracial quotient, with freeness retained in their represented operator-norm closures. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

structure SuccessiveCoordinateHaar (hNM : N ≤ M) (seed : Set (Q τ ω)) where
  algebra : ℕ → StarSubalgebra ℂ (Q τ ω)
  step : ∀ j,CoordinateHaarData τ ω hNM (algebra j).toSubalgebra
  initial : algebra 0=StarAlgebra.adjoin ℂ seed
  successor : ∀ j,algebra (j+1)=StarAlgebra.adjoin ℂ
    (insert ((step j).t : Q τ ω) (algebra j : Set (Q τ ω)))
  separable : ∀ j,TopologicalSpace.IsSeparable (algebra j : Set (Q τ ω))

end

/-! Free variables and prefixes with Haar endpoint properties of W and y=zW*. Coordinates are retained in the sequence data. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_CoordinatePerturbation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

def boundedToSequence (b : Bounded M) : Sequences M :=
  Classical.choose (boundedMap_surjective b)

theorem boundedToSequence_map (b : Bounded M) : boundedMap (boundedToSequence b)=b :=
  Classical.choose_spec (boundedMap_surjective b)

theorem boundedToSequence_apply (b : Bounded M) (k : ℕ) : boundedToSequence b k=b.val k :=
  congrArg (fun a : Bounded M => a.val k) (boundedToSequence_map b)

def boundedUnitarySequence (b : Bounded M) (hb : ∀ k,b.val k ∈ unitary M.toStarSubalgebra) :
    unitary (Sequences M) :=
  ⟨boundedToSequence b,by
    apply Unitary.mem_iff.mpr
    constructor <;> apply BoundedContinuousFunction.ext <;> intro k
    · change star (boundedToSequence b k)*boundedToSequence b k=1
      rw [boundedToSequence_apply]
      exact Unitary.star_mul_self_of_mem (hb k)
    · change boundedToSequence b k*star (boundedToSequence b k)=1
      rw [boundedToSequence_apply]
      exact Unitary.mul_star_self_of_mem (hb k)⟩

end

/-! Prefix labels and conjugate-word Gram identities for free-group perturbations. -/

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

variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def SuccessiveCoordinateHaar.haarSequence (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (j : ℕ) : unitary (Sequences M) :=
  boundedUnitarySequence (boundedInclusion hNM (F.step j).coordinates)
    (fun k => Unitary.map_mem (coordinateInclusion hNM) ((F.step j).unitary_coordinates k))

def SuccessiveCoordinateHaar.coordinateVariables (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary M.toStarSubalgebra) : ℕ → unitary (Sequences M)
  | 0 => F.haarSequence τ ω 0
  | j+1 => constantSequenceUnitary u*F.haarSequence τ ω (j+1)

def SuccessiveCoordinateHaar.coordinateTarget (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) : unitary (Sequences M) :=
  constantSequenceUnitary z*(FreeGroup.lift (F.coordinateVariables τ ω u) (freePrefix (ell+1)))⁻¹

end

/-! The one literal bounded skew-adjoint perturbation K = i h. Every formal
row is its conjugate by the corresponding actual coordinate prefix. -/
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def SuccessiveCoordinateHaar.coordinatePrefix (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary M.toStarSubalgebra) (k : ℕ) : unitary (Sequences M) :=
  FreeGroup.lift (F.coordinateVariables τ ω u) (freePrefix k)

def SuccessiveCoordinateHaar.commonPerturbation (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) : Sequences M :=
  (α/(2*ell)) • ∑ j : Fin ell,
    let a : Sequences M := ↑((F.coordinatePrefix τ ω u (j.val+1))⁻¹ *
      F.coordinateTarget τ ω u z ell * F.coordinatePrefix τ ω u (j.val+1))
    a-star a

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_RelativeGeneration
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite star polynomials in one unitary variable and coefficients in
an included von Neumann algebra. Both uniform operator bounds and continuity
of trace-vector evaluation are proved by recursion on the expression. -/
open Filter
open scoped Topology

namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)
namespace RelativePolynomial

def eval : Generator.RelativePolynomial N.toStarSubalgebra → TraceUnitary τ → M.toStarSubalgebra
  | .coeff a, _ => coordinateInclusion hNM a
  | .indeterminate, u => u.algebra τ
  | .add p q, u => eval p u+eval q u
  | .mul p q, u => eval p u*eval q u
  | .smul z p, u => z • eval p u
  | .adjoint p, u => star (eval p u)

def sectionVector (p : Generator.RelativePolynomial N.toStarSubalgebra) (u : TraceUnitary τ) : H :=
  (eval τ hNM p u).val τ.vector

end RelativePolynomial
end Tracial

/-! The literal algebra W*(N,u), its trace Hilbert subspace, and density of
actual N-coefficient star-polynomial values in that subspace. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

def relativeGenerators (u : TraceUnitary τ) : Set (H →L[ℂ] H) :=
  (N : Set (H →L[ℂ] H)) ∪ {(u.algebra τ).val}

def relativeGenerated (u : TraceUnitary τ) : VonNeumannAlgebra H :=
  vonNeumannOfWOTClosed (wstar (relativeGenerators (N := N) τ u)) (wstar_closed _)

namespace RelativePolynomial

def valueAlgebra (u : TraceUnitary τ) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  StarAlgebra.adjoin ℂ (relativeGenerators (N := N) τ u)

theorem eval_mem (p : Generator.RelativePolynomial N.toStarSubalgebra) (u : TraceUnitary τ) :
    (eval τ hNM p u).val ∈ valueAlgebra (N := N) τ u := by
  induction p with
  | coeff a => exact StarAlgebra.subset_adjoin ℂ _ (Or.inl a.property)
  | indeterminate => exact StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)
  | add p q hp hq => exact (valueAlgebra (N := N) τ u).add_mem hp hq
  | mul p q hp hq => exact (valueAlgebra (N := N) τ u).mul_mem hp hq
  | smul z p hp => exact (valueAlgebra (N := N) τ u).smul_mem hp z
  | adjoint p hp => exact (valueAlgebra (N := N) τ u).star_mem' hp

theorem valueAlgebra_le (u : TraceUnitary τ) :
    valueAlgebra (N := N) τ u ≤ (relativeGenerated (N := N) τ u).toStarSubalgebra :=
  StarAlgebra.adjoin_le (subset_wstar _)

end RelativePolynomial

end Tracial

/-! The literal interleaved word belongs to W*(N,u), is unitary, and has
trace norm one. The printed perturbation-size bound tends to zero. -/
open Filter
open scoped Topology

/-! Projection continuity for generated algebras, using the complete trace-unitary metric, dense polynomial sections, and trace-vector separability. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end


