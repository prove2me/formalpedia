-- Prove2me | Definitions.Def_Formalism_SharpRestriction_InertJacobiLevels_ExtraGat
-- name    : Formalism_SharpRestriction_InertJacobiLevels_ExtraGat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:21.412806+00:00
-- url     : https://prove2.me/theorems/4c4619d9-1a2b-4817-9d31-ef3e560e500a
-- title:
--   Extra Gat
-- statement:
--   Definitions and structural lemmas for Extra Gat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/InertJacobiLevels/ExtraGat.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.Inhab
open Formalism.MainNotions.G MvPolynomial
variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
def levAll (P : Places p O Kf) : Level P where
  Γ := (∀ v, GL (Fin (P.m + 1)) (P.Qq v)) × ℤˣ
  act := fun v => (Pi.evalMonoidHom _ v).comp (MonoidHom.fst _ _)
  χ := (Units.map ((Int.castRingHom O : ℤ →+* O) : ℤ →* O)).comp (MonoidHom.snd _ _)
variable (P : Places p O Kf)
def sgnEl : (levAll P).Γ := ((1 : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)), (-1 : ℤˣ))
end Formalism.MainNotions.Inhab
end


