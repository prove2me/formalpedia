-- Prove2me | Definitions.Def_Formalism_ZetaNonvanishing_MellinSAux
-- name    : Formalism_ZetaNonvanishing_MellinSAux
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:34.143258+00:00
-- url     : https://prove2.me/theorems/d2e00f0f-3968-4f63-9a6f-b081dbb9b861
-- title:
--   Mellin SAux
-- statement:
--   Definitions and structural lemmas for Mellin SAux, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSAux.lean

import Definitions.Def_Formalism_ZetaRealNonvanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace Formalism
def mxS (n : ℕ) (x : ℝ) : ℝ := max (x / n - 1) 0
end Formalism


