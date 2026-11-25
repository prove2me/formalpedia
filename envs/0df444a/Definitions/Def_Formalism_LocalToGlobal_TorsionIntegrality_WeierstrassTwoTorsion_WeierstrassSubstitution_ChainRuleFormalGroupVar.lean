-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ChainRuleFormalGroupVar
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ChainRuleFormalGroupVar
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:54:28.355553+00:00
-- url     : https://prove2.me/theorems/33bc20bf-304a-4fc4-a3b5-89fb6f6f0b60
-- title:
--   Chain Rule Formal Group Var
-- statement:
--   Definitions and structural lemmas for Chain Rule Formal Group Var, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ChainRuleFormalGroupVar.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementM
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
namespace Formalism.L2.Th1.A
namespace More
section Tools
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable (W : WeierstrassCurve R)
end Tools
end More
open More
namespace More
end More
namespace More
end More
namespace More
end More
namespace More
variable {K : Type u} [Field K] (W : WeierstrassCurve K) (S : Subring K)
end More
namespace More
variable {K : Type u} {L : Type v} [Field K] [Field L] (φ : K →+* L)
end More
end Formalism.L2.Th1.A


