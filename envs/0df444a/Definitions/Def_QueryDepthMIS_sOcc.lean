-- Prove2me | Definitions.Def_QueryDepthMIS_sOcc
-- name    : QueryDepthMIS_sOcc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:28:31.152162+00:00
-- url     : https://prove2.me/theorems/170e0dce-0757-433a-8d0f-e8276ac1956a
-- title:
--   Occupancy $s_i = |P \cap I_i|$
-- statement:
--   For a sequence of positions $P$, $s_i = |P \cap I_i|$ is the number of positions of $P$ in the interval $I_i$. The interval $I_i$ is **occupied** if $s_i > 0$.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.14

import Mathlib
import Definitions.Def_QueryDepthMIS_Iv

set_option autoImplicit false

namespace QueryDepthMIS

/-- The occupancy `s_i = |P ∩ I_i|` of the interval `I_i` by the position sequence `P` (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…),
§3.4, p.14). `I_i` is occupied if `s_i > 0`. -/
noncomputable def sOcc (α : ℝ) (n : ℕ) (P : List ℕ) (i : ℕ) : ℕ :=
  (P.toFinset ∩ Iv α n i).card

end QueryDepthMIS


