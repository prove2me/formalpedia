-- Prove2me | Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_JumpsPFilAntitoneOfLe
-- name    : Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_JumpsPFilAntitoneOfLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:08.297817+00:00
-- url     : https://prove2.me/theorems/c204f8b3-0e8d-40db-b301-0e2b6b3d2163
-- title:
--   Jumps PFil Antitone Of Le
-- statement:
--   Definitions and structural lemmas for Jumps PFil Antitone Of Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/JumpsPFilAntitoneOfLe.lean

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.WeaklyAdmissibleFiltrations
namespace FilPhi
variable {LL : Type} [Field LL] {D : Type} [AddCommGroup D] [Module LL D]
  {n : ℕ} {Emb : Type} [Fintype Emb]
end FilPhi
open FilPhi
end Formalism.WeaklyAdmissibleFiltrations


