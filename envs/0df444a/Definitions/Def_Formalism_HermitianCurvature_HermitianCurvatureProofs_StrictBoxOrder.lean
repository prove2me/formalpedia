-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictBoxOrder
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictBoxOrder
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T16:34:14.786578+00:00
-- url     : https://prove2.me/theorems/34f03973-15c5-4aad-8208-6b0f27e29ed2
-- title:
--   Strict Box Order
-- statement:
--   Definitions and structural lemmas for Strict Box Order, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StrictBoxOrder.lean

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P.StrictBoxOrder
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
def IsWt {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (v : V) : Prop := ∀ c, ∃ t : ℂ, E c c v = t • v
end Formalism.FourierDecayAlt.P.StrictBoxOrder
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
end Formalism.FourierDecayAlt.P


