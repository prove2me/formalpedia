-- Prove2me | Definitions.Def_TractableComposite_IsMovement
-- name    : TractableComposite_IsMovement
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:48.544187+00:00
-- url     : https://prove2.me/theorems/1cc35a58-000f-4ae1-a51a-9805d2fd5abe
-- title:
--   Movement vectors of monotone staircases
-- statement:
--   A movement vector is $\pi=(\pi_1,\dots,\pi_{dn})$ with $\pi_k\in\{1,\dots,d\}$ and exactly $n$ entries equal to each $i$. It encodes a monotone lattice path from $(0,\dots,0)$ to $(n,\dots,n)$ in $\{0,\dots,n\}^d$, the $k$-th move going one step in direction $\pi_k$.
--
--   **Formalization Note.** Moves and directions are 0-based.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), §2.2, p.7

import Mathlib

namespace TractableComposite

/-- **Movement vectors of monotone staircases**, §2.2, p.7: `π = (π₁, …, π_dn)` with `πₖ ∈ {1,…,d}`
and exactly `n` moves in each coordinate direction. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), p.7.

**Formalization Note.** `π : Fin (d*n) → Fin d` is 0-based in both the move index (`π t` is the
`(t+1)`-th move) and the direction. -/
def IsMovement {d n : ℕ} (π : Fin (d * n) → Fin d) : Prop :=
  ∀ i, (Finset.univ.filter (fun t => π t = i)).card = n

end TractableComposite


