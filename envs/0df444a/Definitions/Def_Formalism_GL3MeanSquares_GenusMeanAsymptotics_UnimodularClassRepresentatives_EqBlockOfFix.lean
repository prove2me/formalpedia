-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EqBlockOfFix
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EqBlockOfFix
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:51:09.583584+00:00
-- url     : https://prove2.me/theorems/9b060cd0-7d57-49b6-9806-1cf1526f4526
-- title:
--   Eq Block Of Fix
-- statement:
--   Definitions and structural lemmas for Eq Block Of Fix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EqBlockOfFix.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace Formalism.HermitianLattices.Ext.L3.PinE
variable {A : Type*} [CommRing A] [StarRing A] {κ : Type} [Fintype κ] [DecidableEq κ]
def e₀ : Unit ⊕ κ → A := Pi.single (Sum.inl ()) 1
def HH (H' : Matrix κ κ A) : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A := fromBlocks 1 0 0 H'
end Formalism.HermitianLattices.Ext.L3.PinE


