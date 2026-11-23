-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CauchyBinet_WwCauchyBinetMain
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CauchyBinet_WwCauchyBinetMain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:43:45.520288+00:00
-- url     : https://prove2.me/theorems/131a339b-37c2-4d62-a596-ad746e49b378
-- title:
--   Ww Cauchy Binet Main
-- statement:
--   Definitions and structural lemmas for Ww Cauchy Binet Main, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CauchyBinet/WwCauchyBinetMain.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwCauchyBinet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace PI.WwCauchyBinetWork
open PI.WwCauchyBinet
instance fintypeColChoice {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ)
    (nu : Lt → YoungDiagram) : Fintype (KM.ColChoice N nu) :=
  inferInstanceAs (Fintype (∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N))
end PI.WwCauchyBinetWork


