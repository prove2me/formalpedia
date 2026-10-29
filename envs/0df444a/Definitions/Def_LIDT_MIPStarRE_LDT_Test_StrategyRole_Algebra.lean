-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
-- name    : LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:38:32.80808+00:00
-- url     : https://prove2.me/theorems/941c65ed-9bb3-4db4-bdc0-ceba75021f42
-- title:
--   LIDT definitions: LDT / Test / StrategyRole / Algebra
-- statement:
--   This bundle defines the block-diagonal role-register measurement used to symmetrize Alice and Bob. It combines the two role blocks and records the outcome and total operators of the resulting measurement.
--
--   Principal definitions:
--   - `roleSymmetrizedMeasurement`: the block-diagonal role-register measurement.
--   - `roleSymmetrizedMeasurement_outcome`: its effect at a given role-tagged outcome.
--   - `roleSymmetrizedMeasurement_total`: its total operator.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/StrategyRole/Algebra.lean#L63-L96

-- Generated from MIPStarRE/LDT/Test/StrategyRole/Algebra.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/-!
# Role-register algebraic identities for the low individual degree test

Role-pair projection algebra, symmetrized measurement definitions, and expectation
identities for the classical role-register symmetrized state.
-/

@[expose] public section

namespace MIPStarRE.LDT

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

/-! ### Role-pair projection algebra -/









/-- Block-diagonal role-register measurement built from an Alice-block and a Bob-block POVM.

This is the measurement-level analogue of `symmetrizedIdxProjMeas`: the `Role.A`
sector carries `MA`, and the `Role.B` sector carries `MB`. -/
noncomputable def roleSymmetrizedMeasurement {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (MA MB : Measurement Outcome ι) : Measurement Outcome (Role × ι) where
  toSubMeas :=
    { outcome := fun a => roleCond Role.A (MA.outcome a) + roleCond Role.B (MB.outcome a)
      total := 1
      outcome_pos := fun a => add_nonneg
        (roleCond_nonneg Role.A (MA.outcome_pos a))
        (roleCond_nonneg Role.B (MB.outcome_pos a))
      sum_eq_total := Finset.sum_add_distrib.trans <|
        (congrArg₂ (· + ·)
          (roleCond_finset_sum Role.A Finset.univ MA.outcome)
          (roleCond_finset_sum Role.B Finset.univ MB.outcome)).trans <|
        (congrArg₂ (fun X Y => roleCond Role.A X + roleCond Role.B Y)
          MA.sum_eq MB.sum_eq).trans roleCond_one_sum
      total_le_one := le_rfl }
  total_eq_one := rfl

@[simp] theorem roleSymmetrizedMeasurement_outcome {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (MA MB : Measurement Outcome ι) (a : Outcome) :
    (roleSymmetrizedMeasurement MA MB).outcome a =
      roleCond Role.A (MA.outcome a) + roleCond Role.B (MB.outcome a) :=
  rfl

@[simp] theorem roleSymmetrizedMeasurement_total {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (MA MB : Measurement Outcome ι) :
    (roleSymmetrizedMeasurement MA MB).total = 1 :=
  rfl



-- Formal version of the role-register calculation in
-- `references/ldt-paper/inductive_step.tex`, lines 45--66, together with the
-- cross-term-vanishing observation at line 105.  The symmetrized state is
-- supported only on the `A/B` and `B/A` role sectors, while the symmetrized
-- measurements are block diagonal in the standard role basis.
-- Consequently, after taking the normalized trace, an `A/B` sector sees only
-- the left `A` block and right `B` principal block, and the role-reversed sector
-- gives the analogous statement.  These are trace identities, not operator
-- identities: arbitrary off-diagonal role blocks of `Y` need not vanish, but
-- they do not contribute to the paper's expectation calculation.














-- The `Role.A` block of the left tensor only sees the `Role.B` principal block
-- of the right tensor against the classically role-symmetrized state.




-- The `Role.B` block of the left tensor only sees the `Role.A` principal block
-- of the right tensor against the classically role-symmetrized state.




end MIPStarRE.LDT

end

end LIDT


