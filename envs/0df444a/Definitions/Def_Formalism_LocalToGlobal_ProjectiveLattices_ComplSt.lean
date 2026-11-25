-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ComplSt
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ComplSt
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:43:27.455833+00:00
-- url     : https://prove2.me/theorems/80f5d905-f6c2-423f-84c4-95fd511e88b8
-- title:
--   Compl St
-- statement:
--   Definitions and structural lemmas for Compl St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ComplSt.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.Pj
def ComplSt : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W],
    ∃ (T : CDVR) (ι : W →+* T.V), IsLocalHom ι ∧ ∃ ϖ : W, Irreducible ϖ ∧ Irreducible (ι ϖ)
end Formalism.L2.Pj


