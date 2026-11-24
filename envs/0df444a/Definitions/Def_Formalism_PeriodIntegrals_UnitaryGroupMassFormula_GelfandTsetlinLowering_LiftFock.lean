-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftFock
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftFock
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:02.57984+00:00
-- url     : https://prove2.me/theorems/183eef89-7aa3-4041-91e5-3546df36d67a
-- title:
--   Lift Fock
-- statement:
--   Definitions and structural lemmas for Lift Fock, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftFock.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.REAL MvPolynomial
namespace Fock6
def wa {r n : ℕ} (c : Fin r) : Fin r × Fin n → ℕ := fun v => if v.1 = c then 1 else 0
def rw1 {r n : ℕ} (c : Fin r) : Fin r × Fin n → ℤ := fun v => ((wa c v : ℕ) : ℤ)
end Fock6
end PI.WGL


