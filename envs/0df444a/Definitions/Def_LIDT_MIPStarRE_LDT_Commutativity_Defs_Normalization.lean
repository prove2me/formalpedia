-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
-- name    : LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:42:46.975084+00:00
-- url     : https://prove2.me/theorems/4944e16b-0291-4122-a8ff-1ac7d88c53a1
-- title:
--   LIDT definitions: LDT / Commutativity / Defs / Normalization
-- statement:
--   This bundle defines the sandwiched operators and square families used in the normalization condition of the commutativity argument. It organizes the inner outcome sum, its total operator, and the two orderings of the resulting positive square across the outer outcome index.
--
--   Principal definitions:
--   - `normalizationConditionSandwichedOperator`: the operator obtained by sandwiching the first measurement with the second.
--   - `normalizationConditionSandwichedFamily`: the family indexed by the inner outcome.
--   - `normalizationConditionSandwichedTotalFamily`: the inner-outcome sum for each outer outcome.
--   - `normalizationConditionSandwichedTotalOperator`: the formal summed operator.
--   - `normalizationConditionSquareFamily`: the ordinary square family of the summed operator.
--   - `normalizationConditionAdjointSquareFamily`: the adjoint-square family.
--   - `normalizationConditionSquareOperator`: the sum of ordinary squares over outer outcomes.
--   - `normalizationConditionAdjointSquareOperator`: the sum of adjoint squares over outer outcomes.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Commutativity/Defs/Normalization.lean#L29-L217

-- Generated from MIPStarRE/LDT/Commutativity/Defs/Normalization.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
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

open scoped _root_.Matrix

namespace LIDT

/-!
# Section 11 commutativity: normalization definitions

The normalization-condition sandwich `C_{a,b} = Q_b P_a Q_b` and the associated
indexed submeasurement family used in `lem:normalization-condition`.

## References

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
/-- The operator `C_{a,b} = Q_b P_a Q_b` from `lem:normalization-condition`.

We propagate explicit `matrix` from the input operators so that
the sum `∑_b C_{a,b}` accumulates correctly. -/
noncomputable def normalizationConditionSandwichedOperator {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι)
    (a : OutcomeA) (b : OutcomeB) : MIPStarRE.Quantum.Op ι :=
  Q.outcome b * P.outcome a * Q.outcome b

/-- The sandwiched operators sum to at most the identity. -/
private theorem normalizationConditionSandwichedOperator_sum_le_one
    {OutcomeA OutcomeB : Type*} [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) (a : OutcomeA) :
    ∑ b : OutcomeB, normalizationConditionSandwichedOperator P Q a b ≤ 1 := by
  calc
    ∑ b : OutcomeB, normalizationConditionSandwichedOperator P Q a b
      ≤ ∑ b : OutcomeB, Q.outcome b := by
          refine Finset.sum_le_sum ?_
          intro b hb
          simpa [normalizationConditionSandwichedOperator, Q.proj b] using
            IsSelfAdjoint.conjugate_le_conjugate
              (c := Q.outcome b)
              (SubMeas.outcome_le_one P a)
              (Q.outcome_hermitian b)
    _ = Q.total := by rw [Q.sum_eq_total]
    _ ≤ 1 := Q.total_le_one

/-- The sandwiched family `b ↦ Q_b P_a Q_b`. -/
noncomputable def normalizationConditionSandwichedFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) :
    IdxSubMeas OutcomeA OutcomeB ι :=
  fun a =>
    { outcome := fun b => normalizationConditionSandwichedOperator P Q a b
      total :=
        ∑ b : OutcomeB, normalizationConditionSandwichedOperator P Q a b
      outcome_pos := fun b => by
        simpa [normalizationConditionSandwichedOperator] using
          IsSelfAdjoint.conjugate_nonneg
            (c := Q.outcome b)
            (a := P.outcome a)
            (P.outcome_pos a)
            (Q.outcome_hermitian b)
      sum_eq_total := rfl
      total_le_one := by
        exact normalizationConditionSandwichedOperator_sum_le_one P Q a }

/-- The total family `a ↦ ∑_b C_{a,b}` from `lem:normalization-condition`. -/
noncomputable def normalizationConditionSandwichedTotalFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) :
    IdxSubMeas OutcomeA Unit ι :=
  fun a => postprocess (normalizationConditionSandwichedFamily P Q a) (fun _ => ())

/-- The formal operator `∑_b C_{a,b}` from `lem:normalization-condition`. -/
noncomputable def normalizationConditionSandwichedTotalOperator {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι)
    (a : OutcomeA) : MIPStarRE.Quantum.Op ι :=
  (normalizationConditionSandwichedTotalFamily P Q a).total

 theorem normalizationConditionSandwichedTotalSum_le_one
    {OutcomeA OutcomeB : Type*} [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι)
    {F : OutcomeA → MIPStarRE.Quantum.Op ι}
    (hF : ∀ a, F a ≤ normalizationConditionSandwichedTotalOperator P Q a) :
    ∑ a : OutcomeA, F a ≤ 1 := by
  calc
    ∑ a : OutcomeA, F a
      ≤ ∑ a : OutcomeA, normalizationConditionSandwichedTotalOperator P Q a := by
          refine Finset.sum_le_sum ?_
          intro a ha
          exact hF a
    _ = ∑ a : OutcomeA, ∑ b : OutcomeB, normalizationConditionSandwichedOperator P Q a b := by
          simp [normalizationConditionSandwichedTotalOperator,
            normalizationConditionSandwichedTotalFamily, postprocess,
            normalizationConditionSandwichedFamily]
    _ = ∑ ab : OutcomeA × OutcomeB, normalizationConditionSandwichedOperator P Q ab.1 ab.2 := by
          simpa using
            (Fintype.sum_prod_type' (f := fun a b =>
              normalizationConditionSandwichedOperator P Q a b)).symm
    _ = ∑ b : OutcomeB, ∑ a : OutcomeA, normalizationConditionSandwichedOperator P Q a b := by
          simpa using
            (Fintype.sum_prod_type_right' (f := fun a b =>
              normalizationConditionSandwichedOperator P Q a b))
    _ = ∑ b : OutcomeB, Q.outcome b * P.total * Q.outcome b := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          change ∑ a : OutcomeA, Q.outcome b * P.outcome a * Q.outcome b =
            Q.outcome b * P.total * Q.outcome b
          rw [← Matrix.sum_mul, ← Matrix.mul_sum, P.sum_eq_total]
    _ ≤ ∑ b : OutcomeB, Q.outcome b := by
          refine Finset.sum_le_sum ?_
          intro b hb
          simpa [Q.proj b] using
            IsSelfAdjoint.conjugate_le_conjugate
              (c := Q.outcome b)
              P.total_le_one
              (Q.outcome_hermitian b)
    _ = Q.total := by
          rw [Q.sum_eq_total]
    _ ≤ 1 := Q.total_le_one

 theorem normalizationConditionSandwichedTotalOperator_hermitian
    {OutcomeA OutcomeB : Type*} [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) (a : OutcomeA) :
    (normalizationConditionSandwichedTotalOperator P Q a)ᴴ =
      normalizationConditionSandwichedTotalOperator P Q a :=
  (Matrix.nonneg_iff_posSemidef.mp
    (by
      simpa [normalizationConditionSandwichedTotalOperator] using
        SubMeas.total_nonneg (normalizationConditionSandwichedTotalFamily P Q a))).isHermitian.eq

 theorem normCondSandwichedTotal_sq_le
    {OutcomeA OutcomeB : Type*} [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) (a : OutcomeA) :
    normalizationConditionSandwichedTotalOperator P Q a *
        normalizationConditionSandwichedTotalOperator P Q a ≤
      normalizationConditionSandwichedTotalOperator P Q a := by
  have hRle : normalizationConditionSandwichedTotalOperator P Q a ≤ 1 := by
    simpa [normalizationConditionSandwichedTotalOperator] using
      (normalizationConditionSandwichedTotalFamily P Q a).total_le_one
  have hR_nonneg : 0 ≤ normalizationConditionSandwichedTotalOperator P Q a := by
    simpa [normalizationConditionSandwichedTotalOperator] using
      SubMeas.total_nonneg (normalizationConditionSandwichedTotalFamily P Q a)
  exact sq_le_self
    hR_nonneg
    hRle

/-- The family `a ↦ (∑_b C_{a,b})(∑_b C_{a,b})^†`. -/
noncomputable def normalizationConditionSquareFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) :
    SubMeas OutcomeA ι where
  outcome := fun a =>
    normalizationConditionSandwichedTotalOperator P Q a *
      (normalizationConditionSandwichedTotalOperator P Q a)ᴴ
  total :=
    ∑ a : OutcomeA,
      normalizationConditionSandwichedTotalOperator P Q a *
        (normalizationConditionSandwichedTotalOperator P Q a)ᴴ
  outcome_pos := fun a =>
    (Matrix.posSemidef_self_mul_conjTranspose
      (normalizationConditionSandwichedTotalOperator P Q a)).nonneg
  sum_eq_total := rfl
  total_le_one := by
    exact normalizationConditionSandwichedTotalSum_le_one P Q fun a => by
      simpa [normalizationConditionSandwichedTotalOperator_hermitian P Q a] using
        normCondSandwichedTotal_sq_le P Q a

/-- The family `a ↦ (∑_b C_{a,b})^†(∑_b C_{a,b})`. -/
noncomputable def normalizationConditionAdjointSquareFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) :
    SubMeas OutcomeA ι where
  outcome := fun a =>
    (normalizationConditionSandwichedTotalOperator P Q a)ᴴ *
      normalizationConditionSandwichedTotalOperator P Q a
  total :=
    ∑ a : OutcomeA,
      (normalizationConditionSandwichedTotalOperator P Q a)ᴴ *
        normalizationConditionSandwichedTotalOperator P Q a
  outcome_pos := fun a =>
    (Matrix.posSemidef_conjTranspose_mul_self
      (normalizationConditionSandwichedTotalOperator P Q a)).nonneg
  sum_eq_total := rfl
  total_le_one := by
    exact normalizationConditionSandwichedTotalSum_le_one P Q fun a => by
      simpa [normalizationConditionSandwichedTotalOperator_hermitian P Q a] using
        normCondSandwichedTotal_sq_le P Q a

/-- The operator `∑_a (∑_b C_{a,b})(∑_b C_{a,b})^†`. -/
noncomputable def normalizationConditionSquareOperator {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) : MIPStarRE.Quantum.Op ι :=
  (normalizationConditionSquareFamily P Q).total

/-- The operator `∑_a (∑_b C_{a,b})^†(∑_b C_{a,b})`. -/
noncomputable def normalizationConditionAdjointSquareOperator {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) : MIPStarRE.Quantum.Op ι :=
  (normalizationConditionAdjointSquareFamily P Q).total

/-- The identity bound appearing in `lem:normalization-condition`. -/
def normalizationConditionIdentityBound {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (_P : SubMeas OutcomeA ι) (_Q : ProjSubMeas OutcomeB ι) : MIPStarRE.Quantum.Op ι :=
  1


end MIPStarRE.LDT.Commutativity

end

end LIDT


