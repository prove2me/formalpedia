-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperB
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperB
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T07:10:26.84607+00:00
-- url     : https://prove2.me/theorems/d6c7e793-826e-4f9f-8c3c-0faaa48ec228
-- title:
--   PNTDHHyper B
-- statement:
--   Definitions and structural lemmas for PNTDHHyper B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHHyperB.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
def lw (n : ℕ) : ℝ := Real.log n / n
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp


