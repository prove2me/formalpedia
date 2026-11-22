-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoiceCount
-- name    : Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoiceCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:13:13.376797+00:00
-- url     : https://prove2.me/theorems/332fc588-6600-4dc1-bf7a-5b11d60f6557
-- title:
--   Tops Choice Count
-- statement:
--   Definitions and structural lemmas for Tops Choice Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoiceCount.lean

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.G0
namespace TopsCount
def a (m : ℕ) (δ : ℝ) (j : ℕ) : ℝ := (m.choose j : ℝ) * δ ^ j * (1 - δ) ^ (m - j)
def A (m : ℕ) (δ : ℝ) (K : ℕ) : ℝ := ∑ j ∈ range K, a m δ j
end TopsCount
end Formalism.G0


