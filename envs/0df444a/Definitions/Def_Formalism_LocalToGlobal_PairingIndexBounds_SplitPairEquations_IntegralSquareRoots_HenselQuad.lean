-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_IntegralSquareRoots_HenselQuad
-- name    : Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_IntegralSquareRoots_HenselQuad
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T20:59:07.241294+00:00
-- url     : https://prove2.me/theorems/8ca4a964-2c2a-4755-adfa-40f0978c8e49
-- title:
--   Hensel Quad
-- statement:
--   Definitions and structural lemmas for Hensel Quad, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/SplitPairEquations/IntegralSquareRoots/HenselQuad.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace Formalism.L2.PairingIndexBounds.Eq.J.Neg
def Rep (q d m : ℕ) : Prop :=
  ∃ α β γ δ : ZMod m, (α ^ 2 + (q : ZMod m) * β ^ 2) * (γ ^ 2 + (d : ZMod m) * δ ^ 2) = -1
end Formalism.L2.PairingIndexBounds.Eq.J.Neg


