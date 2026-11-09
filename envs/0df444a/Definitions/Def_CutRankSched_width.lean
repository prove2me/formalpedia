-- Prove2me | Definitions.Def_CutRankSched_width
-- name    : CutRankSched_width
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:34:51.462303+00:00
-- url     : https://prove2.me/theorems/d62acf9b-e2c4-4d89-9220-43b3a1f194ea
-- title:
--   Vertex-separation width $w^\circ$
-- statement:
--   The **vertex-separation width** of $X^\circ$ in the given order is
--   $$
--   w^\circ = \max_{0 \le k \le n} |F^\circ_k| .
--   $$
--   It is a maximum over the cuts of the fixed trace order, not a minimum over permutations.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.3, p.5

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_frontier

set_option autoImplicit false

namespace CutRankSched

/-- The vertex-separation width `w° = max_{0 ≤ k ≤ n} |F°_k|` of `X°` in the given order
(Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.3, p.5); a maximum over the cuts of the fixed order, not a minimum over orders. -/
noncomputable def width (I : Instance) : ℕ :=
  (Finset.range (I.n + 1)).sup fun k => (frontier I k).card

end CutRankSched


