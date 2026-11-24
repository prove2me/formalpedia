-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FunDen
-- name    : Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FunDen
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:10:38.142434+00:00
-- url     : https://prove2.me/theorems/c52a69da-daa5-496d-ab88-c434b6cb97ab
-- title:
--   Fun Den
-- statement:
--   Definitions and structural lemmas for Fun Den, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FunDen.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_VpBounds
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FunKit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (betaBound_vp cE_vp n_vp c_vp a0 delta_vp)
noncomputable section
namespace UpperTheory.Ram.Fun
end UpperTheory.Ram.Fun
end


