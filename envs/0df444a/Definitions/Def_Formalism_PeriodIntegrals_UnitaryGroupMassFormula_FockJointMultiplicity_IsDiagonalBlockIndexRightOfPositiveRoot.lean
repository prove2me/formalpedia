-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_IsDiagonalBlockIndexRightOfPositiveRoot
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_IsDiagonalBlockIndexRightOfPositiveRoot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:59.584493+00:00
-- url     : https://prove2.me/theorems/4124c466-d165-424e-a966-410d1b3d9f6b
-- title:
--   Is Diagonal Block Index Right Of Positive Root
-- statement:
--   Definitions and structural lemmas for Is Diagonal Block Index Right Of Positive Root, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/IsDiagonalBlockIndexRightOfPositiveRoot.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistPad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial FockH1Action PI.FJM
noncomputable section
namespace PI.FJMX
variable {p q r s : ℕ}
def leftPositiveIndicator (x : Ix p q) : Ln p q r s → ℕ := fun v => if v.1 = x ∧ linePos v = true then 1 else 0
def leftNegativeIndicator (x : Ix p q) : Ln p q r s → ℕ := fun v => if v.1 = x ∧ linePos v = false then 1 else 0
def rightPositiveIndicator (y : Ix r s) : Ln p q r s → ℕ := fun v => if v.2 = y ∧ linePos v = true then 1 else 0
def rightNegativeIndicator (y : Ix r s) : Ln p q r s → ℕ := fun v => if v.2 = y ∧ linePos v = false then 1 else 0
end PI.FJMX


