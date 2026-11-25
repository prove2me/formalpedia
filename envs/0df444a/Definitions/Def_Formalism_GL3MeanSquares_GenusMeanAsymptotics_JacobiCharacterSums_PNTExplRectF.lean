-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectF
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectF
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T07:23:33.310726+00:00
-- url     : https://prove2.me/theorems/322fe0e2-5670-4fcc-a853-c984b13f3701
-- title:
--   PNTExpl Rect F
-- statement:
--   Definitions and structural lemmas for PNTExpl Rect F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplRectF.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
def exBdry (x₀ x₁ y₀ y₁ : ℝ) : Set ℂ :=
  {w : ℂ | x₀ ≤ w.re ∧ w.re ≤ x₁ ∧ y₀ ≤ w.im ∧ w.im ≤ y₁ ∧
    (w.re = x₀ ∨ w.re = x₁ ∨ w.im = y₀ ∨ w.im = y₁)}
end Formalism.HermitianLattices.Ext.PrimesInProgressions


