-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ProductIntervalFrames
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ProductIntervalFrames
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:56:00.916153+00:00
-- url     : https://prove2.me/theorems/ea69a596-44ba-4744-9c12-3cef0fee15d4
-- title:
--   Product Interval Frames
-- statement:
--   Definitions and structural lemmas for Product Interval Frames, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ProductIntervalFrames.lean

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
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
namespace Formalism.FourierDecayAlt.P.ProductIntervalFrames
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
abbrev par (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) : M.Par := ⟨n + 1, r, T, T', u, u⟩
end Formalism.FourierDecayAlt.P.ProductIntervalFrames
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
end Formalism.FourierDecayAlt.P


