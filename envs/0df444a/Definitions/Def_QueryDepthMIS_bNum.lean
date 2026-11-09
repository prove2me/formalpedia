-- Prove2me | Definitions.Def_QueryDepthMIS_bNum
-- name    : QueryDepthMIS_bNum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:26:36.400668+00:00
-- url     : https://prove2.me/theorems/1e6ffb18-e515-4c3b-a95e-b19dd7d64fd6
-- title:
--   Number of intervals $b = 1 + \lfloor \log_{1+\alpha} n \rfloor$
-- statement:
--   The number of geometric intervals covering $\{1, \dots, n\}$:
--   $$
--   b = 1 + \lfloor \log_{1+\alpha} n \rfloor .
--   $$
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.14

import Mathlib

set_option autoImplicit false

namespace QueryDepthMIS

/-- The number of intervals `b = 1 + ⌊log_{1+α} n⌋` (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.14). -/
noncomputable def bNum (α : ℝ) (n : ℕ) : ℕ := 1 + ⌊Real.logb (1 + α) n⌋₊

end QueryDepthMIS


