-- Prove2me | Definitions.Def_CutRankSched_Supplement_vsw
-- name    : CutRankSched_Supplement_vsw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:50:14.219846+00:00
-- url     : https://prove2.me/theorems/7e844211-fe15-4996-937b-0a6da09c85de
-- title:
--   The vertex-separation width $\mathrm{vsw}(G)$ of a numbered graph
-- statement:
--   For a graph $G$ on $\{0,\dots,N-1\}$ taken in the order of its numbering, its **vertex-separation width** is
--   $$
--   \mathrm{vsw}(G)=\max_{0\le k\le N}\bigl|\{\,j<k : \exists h\ge k,\ \{j,h\}\in E(G)\,\}\bigr| ,
--   $$
--   the same formula as the width $w^\circ$ of $X^\circ$ in the fixed event order.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.3, p.5, and Theorem 7.1, p.14

import Mathlib

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- The vertex-separation width of a graph `G` on `{0, …, N−1}` in the order of its numbering
(Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.3, p.5, and Theorem 7.1, p.14): `max_{0 ≤ k ≤ N} |{j < k : ∃ h ≥ k, {j, h} ∈ E(G)}|`
(0-based cuts, the same formula as the base `CutRankSched.width`). -/
noncomputable def vsw {N : ℕ} (G : SimpleGraph (Fin N)) : ℕ := by
  classical
  exact (Finset.range (N + 1)).sup fun k =>
    (Finset.univ.filter fun j : Fin N => j.val < k ∧ ∃ h : Fin N, k ≤ h.val ∧ G.Adj j h).card

end Supplement

end CutRankSched


