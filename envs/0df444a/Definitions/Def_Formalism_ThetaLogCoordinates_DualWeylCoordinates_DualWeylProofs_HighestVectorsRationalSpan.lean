-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsRationalSpan
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsRationalSpan
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T11:47:44.880915+00:00
-- url     : https://prove2.me/theorems/c714a73e-f8cf-4cda-99dc-ae2c84b3d67c
-- title:
--   Highest Vectors Rational Span
-- statement:
--   Definitions and structural lemmas for Highest Vectors Rational Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestVectorsRationalSpan.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
def qd_f {M : GLMod n} (CF : ColFam M) (a : qb_Idx CF → ℚ) (j : CF.J) : GLCoord ℚ n :=
  ∑ I : {I : TIdx (CF.mu j) // StdT I}, a ⟨j, I⟩ • mapCoord ℚ (brk (CF.mu j) I.1)
end Formalism.InvariantFactorPaths.ColumnFamilies


