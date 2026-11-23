-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_GTLower
-- name    : Formalism_PeriodIntegrals_GTLower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:26.136377+00:00
-- url     : https://prove2.me/theorems/1ac800bb-495c-4e6b-8931-62aafeb894f8
-- title:
--   GTLower
-- statement:
--   Definitions and structural lemmas for GTLower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/GTLower.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI
open Formalism.BasicNotions MvPolynomial
def GTLower : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg → Branch h lam sg
end PI


