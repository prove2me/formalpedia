-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:30.786805+00:00
-- url     : https://prove2.me/theorems/5f224d60-cc92-4a72-a210-13b82b635cc2
-- title:
--   WPoint
-- statement:
--   Definitions and structural lemmas for WPoint, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WPoint.lean

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
namespace Formalism.ELL
namespace WeierstrassPointSeriesTail
def wTail {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R) : PowerSeries R :=
  C W.a₁ * X * w + C W.a₂ * X ^ 2 * w + C W.a₃ * w ^ 2 + C W.a₄ * X * w ^ 2 + C W.a₆ * w ^ 3
end WeierstrassPointSeriesTail
end Formalism.ELL


