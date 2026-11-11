-- Prove2me | Definitions.Def_DetConnSketch_Main_UniversalGraph
-- name    : DetConnSketch_Main_UniversalGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:41:21.00621+00:00
-- url     : https://prove2.me/theorems/360e3c58-ef72-4271-8bc9-d5914b2fb058
-- title:
--   The universal graph $P_n$ on all graphs, adjacent when $G\setminus H$ and $H\setminus G$ have different components (Definition 2.1)
-- statement:
--   Fix a vertex set $V$. The **universal graph** on $V$ has one vertex for every simple graph on $V$. Two distinct graphs $G, H$ are adjacent when the connected components of
--   $$G - G\cap H = G \setminus H \qquad\text{and}\qquad H - H \cap G = H \setminus G$$
--   are different, that is, when the reachability relations of $G\setminus H$ and $H \setminus G$ on $V$ differ. The paper's $P_n$ is the universal graph on $n$ labeled vertices ($2^{\binom n2}$ vertices); Lemma 8.3 uses $P_{4k}$ on the $4k$ lifted vertices of $K_{k,k}$.
--
--   Its chromatic number $\chi(P_n)$ controls the deterministic one-way connected-components complexity (Claim 2.2): two graphs that conflict in $P_n$ must receive different messages.
--
--   **Formalization Note.** `universalGraph V : SimpleGraph (SimpleGraph V)`, with `Adj G H := G ≠ H ∧ (G \ H).Reachable ≠ (H \ G).Reachable`; $P_n$ is `universalGraph (Fin n)`.
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 14 (PDF 18), Definition 2.1; p. 48 (PDF 52), Eq. (1)

import Mathlib

namespace DetConnSketch.Main

/-!
# The universal graph `P_n` (Definition 2.1)

Khanna, Putterman, Sudan, *Deterministic Connectivity Sketches Under Edge Deletions*,
arXiv:2611.06626 (copy sha256 fff87f5b…), p. 14, Definition 2.1; p. 48, Eq. (1).

The vertices of the universal graph on a vertex type `V` are all simple graphs on `V`. Two
distinct graphs `G, H` are adjacent when the connected components of `G − G ∩ H = G \ H` and of
`H − H ∩ G = H \ G` differ, i.e. when their reachability relations on `V` differ. The paper's
`P_n` is `universalGraph (Fin n)`; Lemma 8.3 uses `P_{4k}` on the lifted vertex type of
`K_{k,k}` (`DetConnSketch.Main.LiftVertex k`, `4k` vertices).
-/

/-- The universal graph on simple graphs with vertex type `V` (Definition 2.1). -/
def universalGraph (V : Type) : SimpleGraph (SimpleGraph V) where
  Adj G H := G ≠ H ∧ (G \ H).Reachable ≠ (H \ G).Reachable
  symm := by
    constructor
    intro G H h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    constructor
    intro G h
    exact h.1 rfl

end DetConnSketch.Main


