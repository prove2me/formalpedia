-- Prove2me | Definitions.Def_TractableComposite_gridPt
-- name    : TractableComposite_gridPt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:45.375996+00:00
-- url     : https://prove2.me/theorems/e8d25ac0-4417-4f83-b340-1936c4ac4795
-- title:
--   The grid point $\Pi(\pi,k)$
-- statement:
--   For a movement vector $\pi$ and $k\in\{0,\dots,dn\}$, $\Pi(\pi,k)=p_0+\sum_{j=1}^{k}e_{\pi_j}$ is the grid point reached after the first $k$ moves: its $i$-th coordinate counts the moves among the first $k$ that go in direction $i$.
--
--   **Formalization Note.** Each coordinate is capped at $n$, which never binds for a movement vector.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), §2.2, p.7

import Mathlib

namespace TractableComposite

/-- **The grid point Π(π, k)**, p.7: `Π(π,k) = p₀ + ∑_{j=1}^{k} e_{πⱼ}`, the point of `{0,…,n}^d` reached
after the first `k` moves. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), p.7.

**Formalization Note.** Coordinate `i` counts the moves `t < k` (0-based) with `π t = i`; it is capped
at `n` so that it is a `Fin (n+1)` (the cap is never active for a movement vector, `IsMovement`). -/
def gridPt {d n : ℕ} (π : Fin (d * n) → Fin d) (k : ℕ) (i : Fin d) : Fin (n + 1) :=
  ⟨min (Finset.univ.filter (fun t : Fin (d * n) => t.val < k ∧ π t = i)).card n, by omega⟩

end TractableComposite


