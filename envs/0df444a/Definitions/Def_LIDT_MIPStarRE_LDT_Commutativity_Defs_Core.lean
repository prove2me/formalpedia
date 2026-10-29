-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
-- name    : LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:38:00.906025+00:00
-- url     : https://prove2.me/theorems/69594e7b-0d74-427a-83eb-8339718a97db
-- title:
--   LIDT definitions: LDT / Commutativity / Defs / Core
-- statement:
--   This bundle defines the question, outcome, and operator vocabulary for the evaluated-slice commutativity argument. It connects evaluated-slice samples with their full-slice questions, packages ordered products and sandwiches on a bipartite space, and defines the postprocessed evaluated measurement family.
--
--   Principal definitions:
--   - `EvaluatedSliceQuestion`: the pair of sampled points used by an evaluated-slice question.
--   - `EvaluatedSliceOutcome`: the pair of field values obtained by evaluating the selected slice polynomials.
--   - `FullSliceQuestion`: the two height coordinates underlying a full-slice sample.
--   - `FullSliceOutcome`: the pair of slice polynomials associated with those heights.
--   - `leftOrderedProductOpFamily`: the ordered product placed on the left tensor factor.
--   - `sandwichByOuterSubMeas`: the operator sandwich with an outer submeasurement factor.
--   - `fullSliceQuestionOfEvaluatedSlice`: the full-slice question underlying an evaluated-slice question.
--   - `evaluatedPointFamily`: the postprocessed measurement family indexed by a point and height.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Commutativity/Defs/Core.lean#L32-L242

-- Generated from MIPStarRE/LDT/Commutativity/Defs/Core.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/-!
# Section 11 commutativity: core definitions

Outcome and question abbreviations for the evaluated-slice, full-slice, and
stability steps of the Section 11 commutativity argument.

## References

- `references/ldt-paper/commutativity-points.tex`
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.Quantum
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (params : Parameters) [FieldModel params.q]

/-- Evaluated-slice questions consist of the two sampled points in the next
ambient space. Their height coordinates are later retained as a full-slice
question. -/
abbrev EvaluatedSliceQuestion (params : Parameters) := Point params.next × Point params.next

/-- Evaluated-slice outcomes are the two field values obtained after evaluating
the selected slice polynomials at the sampled points. -/
abbrev EvaluatedSliceOutcome (params : Parameters) := Fq params × Fq params

/-- Full-slice questions are the two height coordinates associated with an
evaluated-slice sample. -/
abbrev FullSliceQuestion (params : Parameters) := Fq params × Fq params

/-- Full-slice outcomes are the pair of slice polynomials measured at the two
height coordinates of a full-slice question. -/
abbrev FullSliceOutcome (params : Parameters) [FieldModel params.q] :=
  Polynomial params × Polynomial params






/-- Ordered product placed on the left tensor factor of the bipartite space `ι × ι`. -/
noncomputable def leftOrderedProductOpFamily {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    OpFamily (α × β) (ι × ι) :=
  OpFamily.leftPlacedOpFamily (ιB := ι) (orderedProductOpFamily A B)



/-- Sandwiched product `A_a B_b A_a`.

Its total operator should be the sum-of-sandwiches
`∑_a A_a (∑_b B_b) A_a` whenever `α` is finitely enumerable. -/
noncomputable def sandwichByOuterSubMeas {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    SubMeas (α × β) ι where
  outcome := fun ab =>
    match ab with
    | (a, b) =>
        A.outcome a * B.outcome b * A.outcome a
  total :=
    ∑ a : α, A.outcome a * B.total * A.outcome a
  outcome_pos := fun ⟨a, b⟩ =>
    IsSelfAdjoint.conjugate_nonneg
      (c := A.outcome a)
      (a := B.outcome b)
      (B.outcome_pos b)
      (A.outcome_hermitian a)
  sum_eq_total := calc
    ∑ ab : α × β, A.outcome ab.1 * B.outcome ab.2 * A.outcome ab.1 =
        ∑ a : α, ∑ b : β, A.outcome a * B.outcome b * A.outcome a := by
          rw [Fintype.sum_prod_type]
    _ = ∑ a : α, A.outcome a * B.total * A.outcome a := by
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [← Matrix.sum_mul, ← Matrix.mul_sum, B.sum_eq_total]
  total_le_one := calc
    ∑ a : α, A.outcome a * B.total * A.outcome a
      ≤ ∑ a : α, A.outcome a := by
          refine Finset.sum_le_sum ?_
          intro a ha
          calc
            A.outcome a * B.total * A.outcome a ≤ A.outcome a * A.outcome a := by
              simpa using
                IsSelfAdjoint.conjugate_le_conjugate
                  (c := A.outcome a)
                  B.total_le_one
                  (A.outcome_hermitian a)
            _ ≤ A.outcome a :=
              sq_le_self (A.outcome_pos a) (SubMeas.outcome_le_one A a)
    _ = A.total := by
        rw [A.sum_eq_total]
    _ ≤ 1 := A.total_le_one

/-- The full-slice question underlying an evaluated-slice sample. -/
def fullSliceQuestionOfEvaluatedSlice (params : Parameters)
    (q : EvaluatedSliceQuestion params) : FullSliceQuestion params :=
  (pointHeight params q.1, pointHeight params q.2)

/-- The postprocessed family `((u,x) ↦ G^x_[g(u)=a])`. -/
noncomputable def evaluatedPointFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  IdxPolyFamily.evaluatedAtNextPoint family

/-- Left tensor-placement for the evaluated family `G^x_[g(u)=a]`
on the bipartite space `d * d`. -/
noncomputable def evaluatedPointFamilyLeft (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Point params.next) (Fq params) (ι × ι) :=
  fun u => leftPlacedSubMeas (ιB := ι) (evaluatedPointFamily params family u)

/-- Right tensor-placement for the evaluated family `G^x_[g(u)=a]`
on the bipartite space `d * d`. -/
noncomputable def evaluatedPointFamilyRight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Point params.next) (Fq params) (ι × ι) :=
  fun u => rightPlacedSubMeas (ιA := ι) (evaluatedPointFamily params family u)

/-- The first evaluated factor `G^x_[g(u)=a]`. -/
noncomputable def evaluatedSliceFirstFactor (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (Fq params) ι :=
  fun q => evaluatedPointFamily params family q.1

/-- The second evaluated factor `G^y_[h(v)=b]`. -/
noncomputable def evaluatedSliceSecondFactor (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (Fq params) ι :=
  fun q => evaluatedPointFamily params family q.2

/-- The ordered evaluated-slice product `(G^x_[g(u)=a] G^y_[h(v)=b]) ⊗ I`
on the bipartite space `d * d`. -/
noncomputable def evaluatedSliceProductLeft (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxOpFamily (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    leftOrderedProductOpFamily
      (evaluatedSliceFirstFactor params family q)
      (evaluatedSliceSecondFactor params family q)

/-- The reversed evaluated-slice product `(G^y_[h(v)=b] G^x_[g(u)=a]) ⊗ I`
on the bipartite space `d * d`. -/
noncomputable def evaluatedSliceProductRight (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxOpFamily (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily
        (evaluatedSliceFirstFactor params family q)
        (evaluatedSliceSecondFactor params family q)





/-- The first full slice measurement `G^x`. -/
def fullSliceFirstFactor (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (FullSliceQuestion params) (Polynomial params) ι :=
  fun q => (family.meas q.1).toSubMeas

/-- The second full slice measurement `G^y`. -/
def fullSliceSecondFactor (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (FullSliceQuestion params) (Polynomial params) ι :=
  fun q => (family.meas q.2).toSubMeas

/-- The ordered full-slice product `(G^x_g G^y_h) ⊗ I`
on the bipartite space `d * d`. -/
noncomputable def fullSliceProductLeft (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxOpFamily (FullSliceQuestion params) (FullSliceOutcome params) (ι × ι) :=
  fun q =>
    leftOrderedProductOpFamily
      (fullSliceFirstFactor params family q)
      (fullSliceSecondFactor params family q)

/-- The reversed full-slice product `(G^y_h G^x_g) ⊗ I`
on the bipartite space `d * d`. -/
noncomputable def fullSliceProductRight (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxOpFamily (FullSliceQuestion params) (FullSliceOutcome params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily
        (fullSliceFirstFactor params family q)
        (fullSliceSecondFactor params family q)

/-- Evaluate a pair of full-slice outcomes at the sampled points `((u,x),(v,y))`. -/
noncomputable def evaluateFullSliceOutcomeAtQuestion (params : Parameters) [FieldModel params.q]
    (q : EvaluatedSliceQuestion params) :
    FullSliceOutcome params → EvaluatedSliceOutcome params :=
  fun gh =>
    (gh.1 (truncatePoint params q.1), gh.2 (truncatePoint params q.2))






end MIPStarRE.LDT.Commutativity

end

end LIDT


