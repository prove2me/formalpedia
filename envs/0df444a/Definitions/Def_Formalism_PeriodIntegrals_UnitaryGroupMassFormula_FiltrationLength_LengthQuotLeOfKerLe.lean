-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiltrationLength_LengthQuotLeOfKerLe
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiltrationLength_LengthQuotLeOfKerLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:41:57.368073+00:00
-- url     : https://prove2.me/theorems/38c18387-3c7d-4ca4-821b-45f2e4fdeb07
-- title:
--   Length Quot Le Of Ker Le
-- statement:
--   Definitions and structural lemmas for Length Quot Le Of Ker Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiltrationLength/LengthQuotLeOfKerLe.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FiltLen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.FiltrationLength
open Submodule
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
noncomputable def ell (B A : Submodule R W) : ℕ∞ :=
  Module.length R (↥B ⧸ A.comap B.subtype)
end PI.FiltrationLength


