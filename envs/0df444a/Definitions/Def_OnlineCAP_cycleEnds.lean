-- Prove2me | Definitions.Def_OnlineCAP_cycleEnds
-- name    : OnlineCAP_cycleEnds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:34.362208+00:00
-- url     : https://prove2.me/theorems/c101d75f-3696-486c-933f-41a103beec39
-- title:
--   The standard cycle on n vertices
-- statement:
--   The **standard cycle** on $v_0,\dots,v_{n-1}$ has the $n$ edges $\{v_i,v_{i+1 \bmod n}\}$, $i=0,\dots,n-1$, i.e. the vertices in the cyclic order $v_0,v_1,\dots,v_{n-1},v_0$.
--
--   **Formalization Note** Every cycle on $n$ labelled vertices is a relabelling of this one. For $n=2$ it consists of two parallel edges (a 2-edge-connected multigraph), for $n=1$ of one loop.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Problem 2.2, p.9; §3.1, p.10

import Mathlib

namespace OnlineCAP

/-- **The standard cycle on `n` vertices.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Problem 2.2, p.9, and §3.1, p.10 (PDF p.10):
"Order the vertices of G as V = (v0, v1, . . . , vn−1, v0) along the cycle".

Edge `i` joins `v_i` and `v_{i+1 mod n}`, for `i = 0, …, n − 1`.

**Formalization Note.** Every cycle on `n` labelled vertices is a relabelling of this one. For
`n = 2` it has two parallel edges between `v₀` and `v₁` (a 2-edge-connected multigraph), and for
`n = 1` one loop. -/
def cycleEnds (n : ℕ) (i : Fin n) : Sym2 (Fin n) :=
  s(i, ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

end OnlineCAP


