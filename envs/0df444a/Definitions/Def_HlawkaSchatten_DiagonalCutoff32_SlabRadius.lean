-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalCutoff32_SlabRadius
-- name    : HlawkaSchatten_DiagonalCutoff32_SlabRadius
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-10-16T14:18:41.156244+00:00
-- url     : https://prove2.me/theorems/7a72e1be-04b3-48bd-9688-ae33bdfd338b
-- title:
--   Slab envelope radius for the cutoff-32 window
-- statement:
--   The slab envelope radius $q(p)$ assigns to each exponent $p$ the rational envelope level of the slab containing it, for the partition of $[32,50]$ into the slabs $[32,33]$, $[33,34]$, $[34,36]$, $[36,38]$, $[38,40]$, $[40,42]$, $[42,45]$, $[45,50]$ (each slab owns its right endpoint):
--
--   $$q(p)=\begin{cases}0.3851 & p\le 33\\ 0.3839 & 33<p\le 34\\ 0.3827 & 34<p\le 36\\ 0.3806 & 36<p\le 38\\ 0.3786 & 38<p\le 40\\ 0.37682 & 40<p\le 42\\ 0.3752 & 42<p\le 45\\ 0.3730 & p>45.\end{cases}$$
--
--   It is the common parameter of the slab envelope bounds and of the slab-wise localization of a Hlawka counterexample in the cutoff-32 argument.
--
--   **Formalization Note** The value for $p>50$ is the last branch and is not used.
-- source:
--   Sharp diagonal Hlawka constant campaign, cutoff-32 entry (https://prove2.me/campaigns/sharp-diagonal-hlawka-constant); definitions of the foundation mission (Ezzeri Esa, Apache-2.0).

import Mathlib.Data.Real.Basic

/-
Cutoff-32 development for the sharp diagonal Hlawka constant. Builds on Ezzeri Esa's Apache-2.0
Hlawka-Schatten construction (Definitions.Def_HlawkaSchatten_*). Released under Apache 2.0.
-/

namespace HlawkaSchatten.DiagonalCutoff32

/-- The envelope radius `q_k` of the slab containing `p` (slabs [32,33], [33,34], [34,36], [36,38],
[38,40], [40,42], [42,45], [45,50]; a slab owns its right endpoint). -/
noncomputable def slabRadius (p : ℝ) : ℝ :=
  if p ≤ 33 then 3851/10000 else if p ≤ 34 then 3839/10000 else if p ≤ 36 then 3827/10000
  else if p ≤ 38 then 3806/10000 else if p ≤ 40 then 3786/10000
  else if p ≤ 42 then 37682/100000 else if p ≤ 45 then 3752/10000 else 3730/10000

end HlawkaSchatten.DiagonalCutoff32


