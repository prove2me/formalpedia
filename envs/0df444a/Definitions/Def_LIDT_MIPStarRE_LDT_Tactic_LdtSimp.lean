-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_LdtSimp
-- name    : LIDT_MIPStarRE_LDT_Tactic_LdtSimp
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:34:13.325125+00:00
-- url     : https://prove2.me/theorems/416bce83-a599-49e3-a784-a533904e0ec2
-- title:
--   LIDT definitions: LDT / Tactic / LdtSimp
-- statement:
--   This bundle records the declarations in the audited `ldt_simp` simplifier registry. The registry makes common distribution, distance, consistency, measurement-conversion, and tensor-lifting expressions reducible to the forms used by the LDT proofs.
--
--   Principal definitions:
--   - `avgOver`: registered finite-support averaging operation.
--   - `uniformDistribution`: registered uniform finite distribution.
--   - `sddError`: registered scalar state-dependent-distance error expression.
--   - `sddErrorOp`: registered operator-family distance error expression.
--   - `bipartiteConsError`: registered bipartite consistency error expression.
--   - `bipartiteSSCError`: registered bipartite strong self-consistency error expression.
--   - **IdxMeas.toIdxSubMeas**: registered `IdxMeas` conversion from indexed measurements to indexed submeasurements.
--   - **SubMeas.liftLeft**: registered `SubMeas` left-register lift of a submeasurement family.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Tactic/LdtSimp.lean#L1-L60

-- Generated from MIPStarRE/LDT/Tactic/LdtSimp.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_LdtSimpAttr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic.Attr.Register

namespace LIDT

/-!
# Audited `ldt_simp` whitelist

The `ldt_simp` simp set is opt-in proof infrastructure for common LDT
bookkeeping.  It deliberately avoids broad global `[simp]` changes.

Initial whitelist:

* **Averages and constant families:** `avgOver`, `uniformDistribution`, and
  `constSubMeasFamily`.  These unfold a project-local finite-support average or
  a constant wrapper and are used repeatedly when a `Unit`-indexed paper average
  is reduced to its single questionwise term.
* **Relation-level average wrappers:** `sddError`, `sddErrorOp`,
  `bipartiteConsError`, and `bipartiteSSCError`.  These expose the
  corresponding questionwise defect under the average without changing any
  inequality direction.
* **Measurement-family wrappers:** `IdxMeas.toIdxSubMeas`,
  `IdxSubMeas.liftLeft`, `IdxSubMeas.liftRight`, `SubMeas.liftLeft`,
  `SubMeas.liftRight`, and `ProjSubMeas.liftLeft`.  These are definitional
  projections/placements used in left/right-register handoff proofs.
* **Tensor normal forms:** the basic left/right tensor product identities below.
  They reduce products and adjoints of explicit tensor placements to local
  products or `opTensor` forms, matching the formulas used by existing proofs.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

attribute [ldt_simp]
  avgOver uniformDistribution constSubMeasFamily
  sddError sddErrorOp bipartiteConsError bipartiteSSCError
  IdxMeas.toIdxSubMeas IdxSubMeas.liftLeft IdxSubMeas.liftRight
  SubMeas.liftLeft SubMeas.liftRight ProjSubMeas.liftLeft
  leftTensor_mul_leftTensor rightTensor_mul_rightTensor
  leftTensor_mul_rightTensor_eq_opTensor rightTensor_mul_leftTensor_eq_opTensor
  leftTensor_conjTranspose rightTensor_conjTranspose
  leftTensor_one rightTensor_one

section Examples



end Examples

end MIPStarRE.LDT

-- This module exports attribute registrations, not new declarations. Its examples
-- are intentionally anonymous, so the end-of-file private-module check is inapplicable.
set_option linter.privateModule false

end

end LIDT


