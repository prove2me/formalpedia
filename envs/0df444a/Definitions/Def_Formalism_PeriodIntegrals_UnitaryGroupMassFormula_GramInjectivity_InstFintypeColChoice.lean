-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramInjectivity_InstFintypeColChoice
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramInjectivity_InstFintypeColChoice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:31.712801+00:00
-- url     : https://prove2.me/theorems/f70724bf-b129-40d1-a1a8-c4f1379e6552
-- title:
--   Inst Fintype Col Choice
-- statement:
--   Definitions and structural lemmas for Inst Fintype Col Choice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramInjectivity/InstFintypeColChoice.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwInjective
import Definitions.Def_Formalism_PeriodIntegrals_WwCauchyBinet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramInjectivity_GramVanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WwInjectiveWork
open MvPolynomial PI.WwInjective PI.WwInjective.KM
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
noncomputable instance instFintypeColChoice : Fintype (ColChoice N nu) := by
  unfold ColChoice; infer_instance
end PI.WwInjectiveWork


