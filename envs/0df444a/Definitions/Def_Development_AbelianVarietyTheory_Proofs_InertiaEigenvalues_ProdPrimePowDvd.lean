-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ProdPrimePowDvd
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ProdPrimePowDvd
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:52:05.222232+00:00
-- url     : https://prove2.me/theorems/441a65bb-16a4-4195-bcac-b5a0d033e2a7
-- title:
--   Prod Prime Pow Dvd
-- statement:
--   Definitions and structural lemmas for Prod Prime Pow Dvd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ProdPrimePowDvd.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
namespace GlobalTheory.Per
section
variable {O : Type} [CommRing O] [IsLocalRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {L : Type} [Field L] [Algebra O L]
end
end GlobalTheory.Per


