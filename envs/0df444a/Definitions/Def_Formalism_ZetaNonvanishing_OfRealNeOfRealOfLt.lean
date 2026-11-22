-- Prove2me | Definitions.Def_Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt
-- name    : Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:08:43.659732+00:00
-- url     : https://prove2.me/theorems/f66f98ed-d7d1-4521-9724-76baebcf959c
-- title:
--   Of Real Ne Of Real Of Lt
-- statement:
--   Definitions and structural lemmas for Of Real Ne Of Real Of Lt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/OfRealNeOfRealOfLt.lean

import Definitions.Def_Formalism_ZetaNonvanishing_RiemannZetaOneNeZeroOfRealMemIoo
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
section Fam
variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
  (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ)
end Fam
end Formalism


