-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecompositionGlNonarchimedean
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecompositionGlNonarchimedean
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:43.125742+00:00
-- url     : https://prove2.me/theorems/b2eafe05-fcc6-4641-ac0a-12f3e0c23bb8
-- title:
--   Cartan Decomposition Gl Nonarchimedean
-- statement:
--   Definitions and structural lemmas for Cartan Decomposition Gl Nonarchimedean, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CartanDecompositionGlNonarchimedean.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanExists
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace GlobalTheory.CompanionTheory.CartGL.UnitBall
variable (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]
noncomputable def ball : ValuationSubring L :=
  by apply _root_.UpperTheory.Reformulated.B.BallSubgroup.ball <;> assumption
variable {L}
variable {p : Lˣ}
def unif (hp : IsUnif p) : ball L := ⟨p, hp.1.le⟩
end GlobalTheory.CompanionTheory.CartGL.UnitBall
namespace GlobalTheory.CompanionTheory.CartGL
end GlobalTheory.CompanionTheory.CartGL


