-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_Imports
-- name    : Development_AutomorphicArithmetic_CharacterBoxes_Imports
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T18:31:39.1361+00:00
-- url     : https://prove2.me/theorems/d12a3171-d60e-4c70-a61c-a07e86526b8e
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CharacterBoxes/Imports.lean

import Definitions.Def_Development_AutomorphicArithmetic_CoprimeRanks_SecondSetNoRelation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace UpperTheory.Top
open Formalism.BasicNotions Formalism.HC HostParam.Seam
def admitted (R : Ranks) (H0 : HostAx R.toFrame) : Prop :=
  ∀ (b : ℕ) (c : Choices R.toFrame H0.toHostRaw), FieldRows H0.toHostRaw b →
    (4 * R.t * R.r + 1 < H0.q ∧ 4 * R.t * R.r + 1 < H0.d) →
    ∃ D : Host R, D.toHostAx = H0 ∧ D.splitBound = b ∧ HEq (HostNF.ofHost D).ch c
end UpperTheory.Top
end


