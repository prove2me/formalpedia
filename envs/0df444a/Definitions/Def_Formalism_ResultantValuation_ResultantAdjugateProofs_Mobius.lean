-- Prove2me | Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Mobius
-- name    : Formalism_ResultantValuation_ResultantAdjugateProofs_Mobius
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:16:01.144919+00:00
-- url     : https://prove2.me/theorems/5635444b-bad6-4f52-9be2-c2c95862cf79
-- title:
--   Mobius
-- statement:
--   Definitions and structural lemmas for Mobius, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Mobius.lean

import Definitions.Def_Formalism_ResultantValuation_SubspaceCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.ResultantValuation
namespace QBinomialResultantAdjugate
def qb (q : ℤ) : ℕ → ℕ → ℤ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qb q n k + q ^ (k + 1) * qb q n (k + 1)
end QBinomialResultantAdjugate
end Formalism.ResultantValuation


