-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
-- name    : LIDT_MIPStarRE_LDT_Tactic_AvgCongr
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:32:03.951331+00:00
-- url     : https://prove2.me/theorems/42fdf048-c4e9-4039-940e-8bb2ca0e9bdf
-- title:
--   LIDT definitions: LDT / Tactic / AvgCongr
-- statement:
--   This bundle defines the peeling mode used by the `avg_congr` tactic. It distinguishes ordinary and support-restricted average peeling for the tactic implementation.
--
--   Principal definitions:
--   - `AvgCongrPeelKind`: the ordinary and support-restricted peeling modes.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Tactic/AvgCongr.lean#L43-L147

-- Generated from MIPStarRE/LDT/Tactic/AvgCongr.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Lean.Elab.Tactic
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/- Prove2Me definition submissions do not admit custom parser or tactic
registrations. Reachable `avg_congr` invocations are lowered at their exact
parser ranges. The QPBT consumer separately reaches the compiler-generated
`SizeOf` instance for this source-private helper, so retain its parent type. -/
inductive AvgCongrPeelKind where
  | plain
  | onSupport

end LIDT


