-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_FrameTransportCM
-- name    : Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_FrameTransportCM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:08.309009+00:00
-- url     : https://prove2.me/theorems/442cb6fb-97aa-4a5e-828d-2a26e75347d1
-- title:
--   Frame Transport CM
-- statement:
--   Definitions and structural lemmas for Frame Transport CM, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/UnitTraceSumBounds/FrameTransportCM.lean

import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_FrameTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace Formalism.MainNotions.Ext
def FrameTransportCM : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → FrameTransport F E σ
end Formalism.MainNotions.Ext


