-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_LatticeIndexOfSmith
-- name    : Development_AutomorphicSpectrum_Proofs_TwistedProofs_LatticeIndexOfSmith
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T16:26:55.239974+00:00
-- url     : https://prove2.me/theorems/b00ea888-dc39-4719-9a18-8bc5a27f0b67
-- title:
--   Lattice Index Of Smith
-- statement:
--   Definitions and structural lemmas for Lattice Index Of Smith, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/LatticeIndexOfSmith.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.BorelUMod.UpLatIndex
noncomputable section
namespace GlobalTheory.CompanionTheory.InertIndex
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
def boxLat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (c : Fin n → ℤ) :
    AddSubgroup (Fin n → L) :=
  AddSubgroup.pi Set.univ fun i => ordBall L (c i)
end GlobalTheory.CompanionTheory.InertIndex
end


