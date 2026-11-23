-- Prove2me | Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_RankOne
-- name    : Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_RankOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:35.642+00:00
-- url     : https://prove2.me/theorems/bcf21c46-5213-49c4-af1d-2b8bddbfe232
-- title:
--   Rank One
-- statement:
--   Definitions and structural lemmas for Rank One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/RankOne.lean

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
open Module
namespace FilPhi
variable {LL : Type} [Field LL] {D : Type} [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
  {n : ℕ} {Emb : Type} [Fintype Emb]
end FilPhi
end Formalism.WeaklyAdmissibleFiltrations


