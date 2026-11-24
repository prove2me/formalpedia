-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:27:49.956863+00:00
-- url     : https://prove2.me/theorems/05600225-9a1f-4348-a82b-a5224241ec69
-- title:
--   Frame Facts
-- statement:
--   Definitions and structural lemmas for Frame Facts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
def twHom (χ : φ.GG →* ℂˣ) : φ.GG →* ℂ :=
  (Units.coeHom ℂ).comp φ.chC * Misc2.conjHom χ
def orbEmb (τ : φ.GG) (x : ℤˣ × φ.MA) : φ.GG :=
  ((if x.1 = 1 then 1 else φ.sg.1) * τ.1, x.2 * τ.2)
def InTranslate (T : Finset ℕ) (u₀ x : φ.A) : Prop := ∃ s ∈ T, x = φ.dig s + u₀
end Formalism.HC.Frame
end


