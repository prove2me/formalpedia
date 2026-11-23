-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:58:07.40528+00:00
-- url     : https://prove2.me/theorems/5f727027-d4f7-4030-b4cc-2fab0230f199
-- title:
--   Curve Ser
-- statement:
--   Definitions and structural lemmas for Curve Ser, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/CurveSer.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
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
namespace CurveSer
section Tools
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
end Tools
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
section Map
variable {S : Type v} [CommRing S] (φ : R →+* S)
end Map
end CurveSer
open CurveSer
end Formalism.L2.Th1.A


