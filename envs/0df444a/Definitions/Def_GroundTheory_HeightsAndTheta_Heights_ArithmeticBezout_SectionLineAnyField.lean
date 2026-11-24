-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SectionLineAnyField
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SectionLineAnyField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:50.192271+00:00
-- url     : https://prove2.me/theorems/bb33f0ac-8f1a-43f8-9c7b-09eef9db4be2
-- title:
--   Section Line Any Field
-- statement:
--   Definitions and structural lemmas for Section Line Any Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SectionLineAnyField.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial LineChowForm
noncomputable section
namespace SectionLine
variable (F : Type) [Field F]
def coeffX0Alt : Fin 2 → F := fun j => if j = 0 then 1 else 0
def coeffX1 : Fin 2 → F := fun j => if j = 0 then 0 else 1
def pointChowForm : MvPolynomial (Fin 1 × Fin 2) F := X (0, 1)
end SectionLine
end
end GroundTheory.Heights₂.Heights


