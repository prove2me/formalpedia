-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_stepSign
-- name    : KawasakiSOS_Threshold_stepSign
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:10.691209+00:00
-- url     : https://prove2.me/theorems/479ea2db-2322-4db4-a58d-783c8ab7b48d
-- title:
--   The two orientations $\pm1$ of an edge of $C_k$
-- statement:
--   An ordered pair $(i,j)$ of adjacent columns of $C_k$ is $(i,i+s)$ with $s\in\{+1,-1\}$. This definition gives the offset $s$ as an element of $\mathbb Z_k$.
--
--   **Formalization Note** The orientation is indexed by a Boolean, so that there are $2k$ oriented choices for every $k$. At $k=2$ both orientations give the offset $1$, which records the two parallel edges of $C_2$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2)

import Mathlib

namespace KawasakiSOS.Threshold

/-- The offset `+1` or `−1` of an oriented choice. Formalization Note: indexed by `Bool` rather than by the set `{1, −1} ⊆ ℤ_k`, because at `k = 2` those two elements coincide while the paper still counts `2k` ordered pairs.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2). -/
def stepSign {k : ℕ} (s : Bool) : ZMod k := if s then 1 else -1

end KawasakiSOS.Threshold


