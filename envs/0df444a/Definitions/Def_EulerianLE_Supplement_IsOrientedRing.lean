-- Prove2me | Definitions.Def_EulerianLE_Supplement_IsOrientedRing
-- name    : EulerianLE_Supplement_IsOrientedRing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:17:23.097195+00:00
-- url     : https://prove2.me/theorems/abcf8124-0c17-48cb-b918-a01d7c7900af
-- title:
--   Oriented rings of $n\ge 1$ nodes
-- statement:
--   Let $G$ be a port-numbered network, $n\ge1$, $e:\{0,\dots,n-1\}\to V$ a bijection (write $v_i=e(i)$), and at every node $v$ a choice of two ports $\mathrm{cw}(v)$ and $\mathrm{ccw}(v)$. Then $(G,e,\mathrm{cw},\mathrm{ccw})$ is an **oriented ring** when
--
--   1. every node has degree $2$ and $\mathrm{cw}(v)\neq\mathrm{ccw}(v)$, and
--   2. for every $i$, the edge at the CW port of $v_i$ joins it to the CCW port of $v_{i+1}$, indices modulo $n$.
--
--   So $v_0,v_1,\dots,v_{n-1}$ is the clockwise order, $v_0$'s CW neighbour is $v_1$ and its CCW neighbour is $v_{n-1}$. This is the setting of the paper's OR protocol (Appendix D).
--
--   **Formalization Note** $n=1$ (one node whose two ports are joined by a self-loop) and $n=2$ (two parallel edges) are rings, as the paper's "$n\ge 1$" allows. The labelling is for analysis only: the programs see only which port is CW.
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), App. D, pp.47–48 (PDF pp.49–50)

import Mathlib
import Definitions.Def_EulerianLE_Network

namespace EulerianLE.Supplement

/-- An **oriented ring** of `n` nodes (Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader
Election on Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), App. D, pp.47–48,
PDF pp.49–50): "fix an oriented ring of n ≥ 1 nodes … each node has a designated clockwise (CW) port
and a designated counterclockwise (CCW) port … we label all nodes v₀, v₁, …, v_{n−1} in clockwise
order … indices are taken modulo n".

The labelling `e i = vᵢ` is a bijection `Fin n ≃ V`; every node has degree 2 with two different ports
`cw v` and `ccw v`, and the edge at the CW port of `vᵢ` joins it to the CCW port of `v_{i+1}`
(`finRotate n i = i + 1 mod n`).

**Formalization Note.** `n = 1` (a self-loop joining the two ports of `v₀`) and `n = 2` (two parallel
edges) are rings. The labelling is for analysis only; the programs see only which port is CW. -/
def IsOrientedRing (G : Network) (n : ℕ) (e : Fin n ≃ G.V) (cw ccw : ∀ v, Fin (G.deg v)) : Prop :=
  0 < n ∧ (∀ v, G.deg v = 2) ∧ (∀ v, cw v ≠ ccw v) ∧
  ∀ i : Fin n, G.link ⟨e i, cw (e i)⟩ = ⟨e (finRotate n i), ccw (e (finRotate n i))⟩

end EulerianLE.Supplement


