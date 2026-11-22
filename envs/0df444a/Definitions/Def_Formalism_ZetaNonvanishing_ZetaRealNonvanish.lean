-- Prove2me | Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
-- name    : Formalism_ZetaNonvanishing_ZetaRealNonvanish
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:37.420962+00:00
-- url     : https://prove2.me/theorems/b13d6763-5e7b-4027-900c-53af245bbec9
-- title:
--   Zeta Real Nonvanish
-- statement:
--   Definitions and structural lemmas for Zeta Real Nonvanish, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean

import Definitions.Def_Formalism_ZetaRealNonvanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
namespace Formalism
namespace ZRN
def e (n : ℕ) (s : ℂ) : ℂ :=
  (1 - s) * ((n : ℂ) + 1) ^ (-s) + ((n : ℂ) + 1) ^ (1 - s) - ((n : ℂ) + 2) ^ (1 - s)
def F (s : ℂ) : ℂ := ∑' n, e n s
def er (n : ℕ) (σ : ℝ) : ℝ :=
  (1 - σ) * ((n : ℝ) + 1) ^ (-σ) + ((n : ℝ) + 1) ^ (1 - σ) - ((n : ℝ) + 2) ^ (1 - σ)
end ZRN
end Formalism


