-- Prove2me | Definitions.Def_DetConnSketch_Main_CutSize
-- name    : DetConnSketch_Main_CutSize
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:41:22.108203+00:00
-- url     : https://prove2.me/theorems/35591541-6619-40b6-9486-1df7a79e026b
-- title:
--   Cut size $\delta_G(S)$: the number of edges with exactly one endpoint in $S$
-- statement:
--   For a graph $G$ on a finite vertex set $V$ and a set $S \subseteq V$ (a **cut** $(S, V\setminus S)$), the **cut size**
--   $$\delta_G(S) = \#\{\, \{u,v\} \in E(G) : u \in S,\ v \notin S \,\}$$
--   is the number of edges of $G$ with exactly one endpoint in $S$.
--
--   **Formalization Note.** `cutSize G S` counts the ordered pairs $(u, v)$ with $G$-adjacent $u \in S$, $v \notin S$; each crossing edge has exactly one such orientation, so this is the number of crossing edges. `S : Finset V`.
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 20 (PDF 24), Lemma 4.2; p. 21 (PDF 25), Lemma 4.3

import Mathlib

namespace DetConnSketch.Main

/-!
# Cut size `δ_G(S)`

Khanna, Putterman, Sudan, *Deterministic Connectivity Sketches Under Edge Deletions*,
arXiv:2611.06626 (copy sha256 fff87f5b…), pp. 20–21 (Lemmas 4.2, 4.3).

For a graph `G` on a finite vertex type and a cut `S ⊆ V`, `δ_G(S)` is the number of edges of
`G` with exactly one endpoint in `S`. Each such edge is counted once, as the ordered pair
`(u, v)` with `u ∈ S`, `v ∉ S`.
-/

open Classical in
/-- `δ_G(S)`: the number of edges of `G` crossing the cut `(S, V ∖ S)`. -/
noncomputable def cutSize {V : Type} [Fintype V] (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (Finset.univ.filter fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S).card

end DetConnSketch.Main


