-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Test_Classical
-- name    : LIDT_MIPStarRE_LDT_Test_Classical
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:36:10.217671+00:00
-- url     : https://prove2.me/theorems/97d23a9b-0f3e-4379-bcce-43889df65f7f
-- title:
--   LIDT definitions: LDT / Test / Classical
-- statement:
--   This bundle defines deterministic classical strategies and acceptance probabilities for the low-individual-degree test. It includes axis-parallel and restricted-diagonal acceptance predicates, uniform indicator averages, role-tagged branch probabilities, and the full classical passing condition.
--
--   Principal definitions:
--   - `TwoProverClassicalLIDStrategy`: deterministic point and line answers for the classical test.
--   - `axisParallelAccepts`: acceptance on an axis-parallel branch instance.
--   - `restrictedDiagonalAccepts`: acceptance on a restricted diagonal branch instance.
--   - `indicatorAcceptanceProbability`: the uniform average of a decidable acceptance indicator.
--   - `roleTaggedAcceptanceProbability`: the role-tagged acceptance probability.
--   - `axisParallelAcceptanceProbability`: the axis-parallel branch probability.
--   - `selfConsistencyAcceptanceProbability`: the self-consistency branch probability.
--   - `ClassicallyPassesLowIndividualDegreeTest`: the full classical passing predicate.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/Classical.lean#L24-L313

-- Generated from MIPStarRE/LDT/Test/Classical.lean by skeleton subtraction.
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
# Section 3 — Classical two-prover strategies

Deterministic classical strategy data and acceptance probabilities for the
paper's two-prover classical low individual degree test from
`references/ldt-paper/test_definition.tex`.

The role-average lemmas below make explicit the same branch decomposition used
by the paper-faithful two-space projective strategy container `ProjStrat`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- Deterministic classical answers for the two provers in the low individual
degree test. -/
structure TwoProverClassicalLIDStrategy (params : Parameters) [FieldModel params.q] where
  /-- Prover A's answer to a point query. -/
  pointAnswerA : Point params → Fq params
  /-- Prover A's answer to an axis-parallel line query. -/
  axisParallelAnswerA : AxisParallelLine params → AxisLinePolynomial params
  /-- Prover A's answer to a diagonal-line query. -/
  diagonalAnswerA : DiagonalLine params → DiagonalLinePolynomial params
  /-- Prover B's answer to a point query. -/
  pointAnswerB : Point params → Fq params
  /-- Prover B's answer to an axis-parallel line query. -/
  axisParallelAnswerB : AxisParallelLine params → AxisLinePolynomial params
  /-- Prover B's answer to a diagonal-line query. -/
  diagonalAnswerB : DiagonalLine params → DiagonalLinePolynomial params

namespace TwoProverClassicalLIDStrategy

/-- Whether the deterministic strategy is accepted on a sampled axis-parallel
branch instance. -/
def axisParallelAccepts {params : Parameters} [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params)
    (rs : Role × AxisParallelTestSample params) : Prop :=
  let r := rs.1
  let s := rs.2
  let ℓ : AxisParallelLine params := { base := s.1, direction := s.2 }
  let u : Point params := s.1
  match r with
  | .A => strategy.axisParallelAnswerA ℓ zeroCoord = strategy.pointAnswerB u
  | .B => strategy.pointAnswerA u = strategy.axisParallelAnswerB ℓ zeroCoord

/-- Whether the deterministic strategy is accepted on a sampled `j`-restricted
diagonal branch instance. -/
def restrictedDiagonalAccepts {params : Parameters} [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params)
    (j : Fin params.m)
    (rs : Role × RestrictedDiagonalSample params j) : Prop :=
  let r := rs.1
  let s := rs.2
  let ℓ : DiagonalLine params :=
    { base := s.1, direction := extendRestrictedDirection j s.2 }
  let u : Point params := s.1
  match r with
  | .A => strategy.diagonalAnswerA ℓ zeroCoord = strategy.pointAnswerB u
  | .B => strategy.pointAnswerA u = strategy.diagonalAnswerB ℓ zeroCoord

/-- Average the indicator of a decidable predicate over a uniform sample space. -/
noncomputable def indicatorAcceptanceProbability {β : Type*}
    [Fintype β] [DecidableEq β] [Nonempty β]
    (p : β → Prop) : Error := by
  classical
  exact avgOver (uniformDistribution β) fun s => if p s then (1 : Error) else 0

/-- Average the paper's role-tagged acceptance predicate over `Role × β`. -/
noncomputable def roleTaggedAcceptanceProbability {β : Type*}
    [Fintype β] [DecidableEq β] [Nonempty β]
    (pA pB : β → Prop) : Error := by
  classical
  exact avgOver (uniformDistribution (Role × β)) fun rs =>
    if match rs.1 with
      | Role.A => pA rs.2
      | Role.B => pB rs.2
    then (1 : Error) else 0







/-- Acceptance probability of the axis-parallel branch of the classical low
individual degree test. -/
noncomputable def axisParallelAcceptanceProbability {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) : Error :=
  roleTaggedAcceptanceProbability
    (fun s : AxisParallelTestSample params =>
      strategy.axisParallelAccepts (Role.A, s))
    (fun s : AxisParallelTestSample params =>
      strategy.axisParallelAccepts (Role.B, s))



/-- Acceptance probability of the self-consistency branch of the classical low
individual degree test. -/
noncomputable def selfConsistencyAcceptanceProbability {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) : Error :=
  indicatorAcceptanceProbability fun u : Point params =>
    strategy.pointAnswerA u = strategy.pointAnswerB u





/-- Acceptance probability of the `j`-restricted diagonal branch. -/
noncomputable def restrictedDiagonalAcceptanceProbability {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params)
    (j : Fin params.m) : Error :=
  roleTaggedAcceptanceProbability
    (fun s : RestrictedDiagonalSample params j =>
      strategy.restrictedDiagonalAccepts j (Role.A, s))
    (fun s : RestrictedDiagonalSample params j =>
      strategy.restrictedDiagonalAccepts j (Role.B, s))







/-- Acceptance probability of the full diagonal branch of the classical low
individual degree test.

The branch first samples `j : Fin params.m` uniformly and then a role-tagged
restricted diagonal sample for that `j`. The theorem
`diagonalAcceptanceProbability_eq_roleAverage` below makes the restricted-
diagonal averaging order explicit on the classical side, matching the paper's
role-first presentation. -/
noncomputable def diagonalAcceptanceProbability {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m, strategy.restrictedDiagonalAcceptanceProbability j



/-- Acceptance probability of the full classical low individual degree test,
averaging the three branches with equal probability. -/
noncomputable def lowIndividualDegreeAcceptanceProbability {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) : Error :=
  (strategy.axisParallelAcceptanceProbability +
      strategy.selfConsistencyAcceptanceProbability +
      strategy.diagonalAcceptanceProbability) / 3



/-- Passing the paper's deterministic two-prover classical low individual degree
test with error `eps`, stated in acceptance-probability form.

This name is deliberately distinct from `ProjStrat.PassesLowIndividualDegreeTest`
so this paper-faithful classical predicate does not collide by dot notation with
the projective strategy predicate.  The precise branch comparison is exposed
concretely by `lowIndividualDegreeAcceptanceProbability_eq_branchAverage`. -/
structure ClassicallyPassesLowIndividualDegreeTest {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalLIDStrategy params) (eps : Error) : Prop where
  /-- The modeled classical acceptance probability is at least `1 - eps`. -/
  acceptanceLowerBound :
    1 - eps ≤ strategy.lowIndividualDegreeAcceptanceProbability

end TwoProverClassicalLIDStrategy









end Test

end MIPStarRE.LDT

end

end LIDT


