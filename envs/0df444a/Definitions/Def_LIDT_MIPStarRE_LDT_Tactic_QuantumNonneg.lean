-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
-- name    : LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:32:31.587564+00:00
-- url     : https://prove2.me/theorems/37a24c6e-f100-411a-b71a-3b73965f9b04
-- title:
--   LIDT definitions: LDT / Tactic / QuantumNonneg
-- statement:
--   This bundle preserves the compatibility name for the quantum nonnegativity tactic used by the source project. Reachable tactic invocations have already been lowered, so the declaration serves as an importable compatibility marker rather than a new mathematical construction.
--
--   Principal definitions:
--   - `quantum_nonneg`: the compatibility declaration for the quantum nonnegativity tactic.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Tactic/QuantumNonneg.lean#L26-L45

-- Generated from MIPStarRE/LDT/Tactic/QuantumNonneg.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

namespace LIDT

/- Prove2Me definition submissions do not admit custom parser or macro
registrations. Every reachable `quantum_nonneg` invocation is lowered at its
exact parser range; this empty compatibility bundle preserves source imports. -/

end LIDT


