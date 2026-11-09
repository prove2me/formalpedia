-- Prove2me | Definitions.Def_DerandSq_prunedX
-- name    : DerandSq_prunedX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:05:16.009302+00:00
-- url     : https://prove2.me/theorems/c068f6d0-57d5-480c-bdb6-fd0ff936bf62
-- title:
--   The pruned graph $X$
-- statement:
--   Root $T_d \circledS H$ at the identity $e \in \Gamma_d$. The root lies in $d$ copies of $H$, the ones placed at its tree neighbours $m_1, \dots, m_d$. For $i_0 \in [d]$, remove the copy placed at $m_{i_0}$, i.e. delete the edges
--   $$
--   \{m_{i_0} m_i,\ m_{i_0} m_j\}, \qquad \{i, j\} \in E(H)
--   $$
--   (this copy contains $e = m_{i_0} m_{i_0}$). The paper's graph **$X$** is the connected component of $e$ in the result: every vertex of $X$ lies in $d - 1$ forward copies of $H$, and every non-root vertex also in a parent copy. The number $c_p$ of closed walks of length $p$ at $e$ in $X$ is the coefficient of the generating function $C_H(z)$ of (4.11).
--
--   **Formalization Note** The component is not cut out explicitly: a closed walk from $e$ never leaves the component of $e$, so $c_p$ is the closed-walk count at $e$ in the graph with those edges deleted.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), §4.2, p.22

import Mathlib
import Definitions.Def_DerandSq_dsTree

namespace DerandSq

/-- The pruned graph `X` of Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), §4.2, p.22: `T_d Ⓢ H` "after removing one of the copies
adjacent to the root". The root is `e`, its tree neighbours are `m_1, …, m_d`, and the copy of
`H` placed at the tree vertex `m_{i₀}` has the edges `{m_{i₀} m_i, m_{i₀} m_j}`,
`{i, j} ∈ E(H)` (it contains `e = m_{i₀} m_{i₀}`); this graph is `T_d Ⓢ H` with those edges
deleted.

**Formalization Note** `X` is the connected component of `e` in this graph. The component is not
cut out explicitly: closed walks from `e` stay in it, so `c_p = closedWalks (prunedX H i₀) 1 p`. -/
def prunedX {d : ℕ} (H : SimpleGraph (Fin d)) (i₀ : Fin d) : SimpleGraph (Gam d) :=
  (dsTree H).deleteEdges
    {e | ∃ i j, H.Adj i j ∧ e = s(mGen i₀ * mGen i, mGen i₀ * mGen j)}

end DerandSq


