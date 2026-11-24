-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_AdIndexEq
-- name    : Formalism_PeriodIntegrals_AdIndexEq
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T12:24:39.941615+00:00
-- url     : https://prove2.me/theorems/212e26cc-95c3-4721-8e45-440cf4bc5b99
-- title:
--   Ad Index Eq
-- statement:
--   Definitions and structural lemmas for Ad Index Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/AdIndexEq.lean

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.AdIndexEq
open Formalism.MainNotions.S
def Ksub (I : AutInst) : Subgroup I.Gf :=
  (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype
def IndexEq : Prop :=
  ∀ (I : AutInst) (x : I.Gf),
    ((Ksub I).map (MulAut.conj x).toMonoidHom).relIndex (Ksub I) =
      ((Ksub I).map (MulAut.conj x⁻¹).toMonoidHom).relIndex (Ksub I)
end PI.AdIndexEq
end


