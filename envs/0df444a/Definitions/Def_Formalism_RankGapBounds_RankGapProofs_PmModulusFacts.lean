-- Prove2me | Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
-- name    : Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:01:29.165173+00:00
-- url     : https://prove2.me/theorems/76a889f6-ca07-4113-9d17-ef6dd6fdf361
-- title:
--   Pm Modulus Facts
-- statement:
--   Definitions and structural lemmas for Pm Modulus Facts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/PmModulusFacts.lean

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.RankGapBounds.LocalQuadraticParts
open Finset
noncomputable def pmW (k : ℕ) : ℝ := (1 + Real.log ((k : ℝ) + 1)) / ((k : ℝ) + 1) ^ 2
end Formalism.RankGapBounds.LocalQuadraticParts


