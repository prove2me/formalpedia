-- Prove2me | Definitions.Def_SemiStreamReach_Main_BatchedDijkstra
-- name    : SemiStreamReach_Main_BatchedDijkstra
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:51:30.164376+00:00
-- url     : https://prove2.me/theorems/05a2a43d-11f5-46be-9b92-36c6109848cd
-- title:
--   BoundedSSSP (Problem 13): block distances, $\tau$-skeletons, $U_B$, $U_F$, and the batched Dijkstra algorithm (Algorithm 1)
-- statement:
--   **Problem 13 (BoundedSSSP).** A directed graph $G$ with positive weights, a set $H_0$ of positive-weight edges and blocks $\mathcal B$ are given; $H=H_0\cup\bigcup_B TC_w((G\cup H_0)[B])$. Given $\alpha>0$, a source $s$ and an integer radius $R\ge0$, compute for each $v$ the distance $\mathrm{dist}_{G_\alpha\cup H_\alpha}(s,v)$ if it is at most $R$, and $\infty$ otherwise. Write $G_0=G\cup H_0$ and $\mathrm{dist}_B(u,v)=\mathrm{dist}_{G_0[B]}(u,v)$.
--
--   **Block distances.** In round $r$, with $S$ the set of vertices settled before round $r$ and $d(u)\in\mathbb N$ their estimates, the block distance of $v\in B$ is
--   $$d_B(v)=\min_{u\in B\cap S}\Big(d(u)+\frac{\mathrm{dist}_B(u,v)}{\alpha}\Big),$$
--   and $U_B$ is the set of $v\in B\setminus S$ for which some $u\in B\cap S$ reaching $v$ in $G_0[B]$ has $d(u)+\lceil \mathrm{dist}_B(u,v)/\alpha\rceil\le r$.
--
--   **Skeletons.** For an integer $\tau\ge1$, a **$\tau$-skeleton** $F$ of $G_0[B]$ without the edges into $\mathrm{Known}_B$ contains, for each $a\in B$, the $\tau$ lightest edges $(a,b)$ of $G_0$ with $b\in B\setminus\mathrm{Known}_B$, or all of them if there are fewer than $\tau$. With $\mathrm{Known}_B=B\cap S$ stored with the values $d_B(u)$,
--   $$d_F(v)=\min_{u\in \mathrm{Known}_B}\Big(d_B(u)+\frac{\mathrm{dist}_F(u,v)}{\alpha}\Big),\qquad U_F=\{v\in B\setminus\mathrm{Known}_B : d_F(v)\le r\}.$$
--
--   **Algorithm 1.** BatchedDijkstra$(s,R)$ starts with $d(s)=0$, $d(v)=\infty$ otherwise, $\mathrm{Known}_B=\emptyset$ and $\mathrm{next}_B=\infty$. In each round $r=0,\dots,R$ it (a) runs SearchBlock$(B,r)$ for each block with $\mathrm{next}_B=r$, gives the returned vertices $U_B$ the estimate $r$ and sets $\mathrm{next}_B\leftarrow\lceil e_B\rceil$; (b) inserts each vertex $u$ with $d(u)=r$ into every $\mathrm{Known}_B$ with $u\in B$ that lacks it, storing $d_B(u)\leftarrow r$ and setting $\mathrm{next}_B\leftarrow r+1$; (c) relaxes all edges $(u,v)$ of $G_0$ with $d(u)=r$: $d(v)\leftarrow\min\{d(v),d(u)+\lceil w(u,v)/\alpha\rceil\}$. SearchBlock$(B,r)$ tries $\tau=2^i$ for $i=0,\dots,\lceil\log_2 n\rceil$: it builds a $\tau$-skeleton $F$, computes $d_F$ and $U_F$, and at the first $\tau$ with $|U_F|<\tau$ inserts $U_F$ into $\mathrm{Known}_B$ with $d_B(v)\leftarrow d_F(v)$ and returns $U_F$ and $e_B=\min\{d_F(v):v\in B\setminus\mathrm{Known}_B\}$.
--
--   **Formalization Note.** `G0` is one weighted graph standing for $G\cup H_0$. Values are in `ℝ≥0∞` ($\infty=\top$). The skeleton used by a search is an arbitrary function `sk r B Known_B τ` constrained only by `IsSkeleton` (any tie-breaking), and the theorems quantify over all such functions. Searches of one round are applied together (each reads only its own block's data). If no $\tau$ succeeds (impossible by the paper's analysis) the search returns nothing and $e_B=\infty$. `roundedUnion G0 Bk α` is $G_\alpha\cup H_\alpha$.
-- source:
--   Hoppenworth, Li, Mahabadi, Tarnawski, Semi-Streaming Reachability and Shortest Paths in n^{1/3+o(1)} Passes, arXiv:2611.05061 (PDF sha256 c1b64474…), pp. 14-15 (PDF 16-17), Problem 13; pp. 16-19 (PDF 18-21), §4.3 and Algorithm 1

import Mathlib
import Definitions.Def_SemiStreamReach_Main_Distances

open scoped ENNReal
open Classical

namespace SemiStreamReach.Main

/-! # BoundedSSSP: block distances, τ-skeletons, and the batched Dijkstra algorithm (Algorithm 1)

Hoppenworth, Li, Mahabadi, Tarnawski, arXiv:2611.05061 (PDF sha256 c1b64474…), §4.1 Problem 13
(pp. 14–15, PDF 16–17) and §4.3 (pp. 16–20, PDF 18–22).

Problem 13: a graph `G` with positive weights, a stored set `H0` of positive-weight edges and blocks
`B`, `H = H0 ∪ ⋃_B TC_w((G ∪ H0)[B])`; given `α > 0`, a source `s` and an integer radius `R ≥ 0`,
compute `dist_{G_α ∪ H_α}(s, v)` if it is at most `R`, and `∞` otherwise. Inside a block,
`dist_B(u, v) = dist_{(G ∪ H0)[B]}(u, v)` (p. 14).

* p. 17: "For a block B, let U_B be the set of vertices v ∈ B not settled before round r for which
  some block-closure edge (u, v) ∈ TC_w((G ∪ H0)[B]) with u settled before round r satisfies
  d(u) + ⌈dist_B(u, v)/α⌉ ≤ r." "the block distance of a vertex v ∈ B is
  d_B(v) = min_{u ∈ B settled before round r} (d(u) + dist_B(u, v)/α)."
* p. 18: "for each vertex a ∈ B, the skeleton F contains the τ lightest edges (a, b) of G ∪ H0 with
  b ∈ B \ Known_B, or all of them if there are fewer than τ." (footnote 12: parallel edges keep only
  the lightest.)
* p. 18–19: "d_F(v) = min_{u ∈ Known_B} (d_B(u) + dist_F(u, v)/α) for all v ∈ B",
  "U_F = {v ∈ B \ Known_B : d_F(v) ≤ r}".
* Algorithm 1 (p. 18, PDF 20): BatchedDijkstra(s, R) and SearchBlock(B, r).

**Formalization Note.** `G0` is the graph `G ∪ H0` (one weighted graph, lightest edge per pair).
`S` is the set of vertices settled before round `r` and `d : V → ℕ` their (integer) estimates.
A `τ`-skeleton is any graph meeting the description on p. 18, with any tie-breaking among equally
light edges (`IsSkeleton`). In Algorithm 1, estimates, stored block distances and `next_B` are
values in `ℝ≥0∞` (`⊤` = `∞`); the choice of skeleton in a search is an arbitrary function `sk` of
the round, the block, the current set `Known_B` and `τ`, and the statements quantify over every such
function. Within a round, the searches of the blocks with `next_B = r` (lines 6–8) are applied
together (each search reads only its own block's data), then the settled vertices are inserted
(lines 9–11; the assignment `next_B ← r + 1` of line 11 comes after line 8), then all edges of
`G ∪ H0` out of the vertices with `d(u) = r` are relaxed (line 12) with their rounded weights
`⌈w(u, v)/α⌉`. SearchBlock tries `τ = 2^i` for `i = 0, …, ⌈log₂ n⌉` (`n = |V|`) and returns at the
first `τ` with `|U_F| < τ`; if no `τ` succeeds (which the paper shows cannot happen) it returns
nothing new and `e_B = ∞`. The blocks are indexed by a finite type `ι`. -/

variable {V : Type*}

/-- The block distance `d_B(v) = min_{u ∈ B ∩ S} (d(u) + dist_B(u, v)/α)` (p. 17), where `S` is the
set of vertices settled before the round and `d` their estimates; `⊤` if no settled vertex of `B`
reaches `v` inside the block. -/
noncomputable def blockDist (G0 : WGraph V) (B S : Finset V) (d : V → ℕ) (α : ℝ) (v : V) :
    ℝ≥0∞ :=
  ⨅ u ∈ B ∩ S, ((d u : ℕ) : ℝ≥0∞) + dist (induced G0 ↑B) u v / ENNReal.ofReal α

/-- `F` is a `τ`-skeleton of `(G0)[B]` without the edges into `K` (p. 18): its edges are edges of
`G0` (same weights) from a vertex of `B` to a vertex of `B \ K`, and for each `a ∈ B` it keeps
`min(τ, deg)` of the edges `(a, b)` with `b ∈ B \ K`, each at most as heavy as every dropped one. -/
def IsSkeleton (G0 : WGraph V) (B K : Finset V) (τ : ℕ) (F : WGraph V) : Prop :=
  (∀ a b, F a b ≠ ⊤ → a ∈ B ∧ b ∈ B ∧ b ∉ K ∧ F a b = G0 a b) ∧
  ∀ a ∈ B,
    ((B \ K).filter (fun b => F a b ≠ ⊤)).card =
        min τ ((B \ K).filter (fun b => G0 a b ≠ ⊤)).card ∧
    ∀ b ∈ B \ K, ∀ b' ∈ B \ K, F a b ≠ ⊤ → G0 a b' ≠ ⊤ → F a b' = ⊤ → G0 a b ≤ G0 a b'

/-- `d_F(v) = min_{u ∈ K} (stored(u) + dist_F(u, v)/α)`, computed in a skeleton `F` from the
vertices of `K = Known_B` with their stored block distances. -/
noncomputable def skelDist (F : WGraph V) (K : Finset V) (stored : V → ℝ≥0∞) (α : ℝ) (v : V) :
    ℝ≥0∞ :=
  ⨅ u ∈ K, stored u + dist F u v / ENNReal.ofReal α

/-- `U_F = {v ∈ B \ Known_B : d_F(v) ≤ r}` when `Known_B = B ∩ S` is stored with the block
distances `d_B`. -/
noncomputable def setUF (G0 F : WGraph V) (B S : Finset V) (d : V → ℕ) (α : ℝ) (r : ℕ) :
    Finset V :=
  (B \ S).filter (fun v => skelDist F (B ∩ S) (blockDist G0 B S d α) α v ≤ (r : ℝ≥0∞))

/-- `U_B` (p. 17): the vertices `v ∈ B` not settled before round `r` for which some block-closure
edge `(u, v)` of `B` with `u` settled satisfies `d(u) + ⌈dist_B(u, v)/α⌉ ≤ r`. -/
noncomputable def setUB (G0 : WGraph V) (B S : Finset V) (d : V → ℕ) (α : ℝ) (r : ℕ) :
    Finset V :=
  (B \ S).filter (fun v => ∃ u ∈ B ∩ S, Reaches (induced G0 ↑B) u v ∧
    ((d u : ℕ) : ℝ≥0∞) + ceilE (dist (induced G0 ↑B) u v / ENNReal.ofReal α) ≤ (r : ℝ≥0∞))

/-- The state of BatchedDijkstra: estimates `d`, and for each block `Known_B`, the stored block
distances and `next_B`. -/
structure BDState (V ι : Type*) where
  d : V → ℝ≥0∞
  known : ι → Finset V
  stored : ι → V → ℝ≥0∞
  next : ι → ℝ≥0∞

/-- One attempt of SearchBlock with a given `τ` and skeleton `F` (lines 17–22): if `|U_F| < τ`,
return `U_F`, the stored values updated with `d_B(v) ← d_F(v)` on `U_F`, and
`e_B = min {d_F(v) : v ∈ B \ (Known_B ∪ U_F)}`. -/
noncomputable def searchAttempt (F : WGraph V) (B K : Finset V) (stored : V → ℝ≥0∞) (α : ℝ)
    (r τ : ℕ) : Option (Finset V × (V → ℝ≥0∞) × ℝ≥0∞) :=
  let dF := skelDist F K stored α
  let UF := (B \ K).filter (fun v => dF v ≤ (r : ℝ≥0∞))
  if UF.card < τ then
    some (UF, fun v => if v ∈ UF then dF v else stored v, ⨅ v ∈ B \ (K ∪ UF), dF v)
  else none

/-- SearchBlock(B, r) (lines 14–22): `τ = 2^i` for `i = 0, …, ⌈log₂ n⌉`, with skeleton `sk τ`;
the first successful attempt is returned. -/
noncomputable def searchBlock [Fintype V] (sk : ℕ → WGraph V) (B K : Finset V)
    (stored : V → ℝ≥0∞) (α : ℝ) (r : ℕ) : Finset V × (V → ℝ≥0∞) × ℝ≥0∞ :=
  ((List.range (Nat.clog 2 (Fintype.card V) + 1)).findSome?
      (fun i => searchAttempt (sk (2 ^ i)) B K stored α r (2 ^ i))).getD (∅, stored, ⊤)

/-- Round `r` of BatchedDijkstra (lines 6–12). `sk r i K τ` is the `τ`-skeleton used when block
`i` is searched in round `r` with `Known_B = K`. -/
noncomputable def bdRound {ι : Type*} [Fintype V] (G0 : WGraph V) (Bk : ι → Finset V) (α : ℝ)
    (sk : ℕ → ι → Finset V → ℕ → WGraph V) (r : ℕ) (st : BDState V ι) : BDState V ι :=
  let srch : ι → Finset V × (V → ℝ≥0∞) × ℝ≥0∞ := fun i =>
    searchBlock (sk r i (st.known i)) (Bk i) (st.known i) (st.stored i) α r
  -- lines 6–8: search each block with `next_B = r`; its `U_B` gets the estimate `r`
  let d1 : V → ℝ≥0∞ := fun v =>
    if ∃ i, st.next i = (r : ℝ≥0∞) ∧ v ∈ (srch i).1 then (r : ℝ≥0∞) else st.d v
  let known1 : ι → Finset V := fun i =>
    if st.next i = (r : ℝ≥0∞) then st.known i ∪ (srch i).1 else st.known i
  let stored1 : ι → V → ℝ≥0∞ := fun i =>
    if st.next i = (r : ℝ≥0∞) then (srch i).2.1 else st.stored i
  let next1 : ι → ℝ≥0∞ := fun i =>
    if st.next i = (r : ℝ≥0∞) then ceilE (srch i).2.2 else st.next i
  -- lines 9–11: settle the vertices with `d(u) = r`
  let new : ι → Finset V := fun i => (Bk i).filter (fun u => d1 u = (r : ℝ≥0∞) ∧ u ∉ known1 i)
  let known2 : ι → Finset V := fun i => known1 i ∪ new i
  let stored2 : ι → V → ℝ≥0∞ := fun i u => if u ∈ new i then (r : ℝ≥0∞) else stored1 i u
  let next2 : ι → ℝ≥0∞ := fun i =>
    if (new i).Nonempty then (((r + 1 : ℕ)) : ℝ≥0∞) else next1 i
  -- line 12: relax the edges of `G ∪ H0` out of the settled vertices
  let d2 : V → ℝ≥0∞ := fun v =>
    min (d1 v) (⨅ (u : V) (_ : d1 u = (r : ℝ≥0∞)), d1 u + rounded G0 α u v)
  ⟨d2, known2, stored2, next2⟩

/-- The initial state (lines 2–4): `d(s) = 0`, `d(v) = ∞` otherwise, `Known_B = ∅`,
`next_B = ∞`. -/
noncomputable def bdInit {ι : Type*} (s : V) : BDState V ι :=
  ⟨fun v => if v = s then 0 else ⊤, fun _ => ∅, fun _ _ => ⊤, fun _ => ⊤⟩

/-- BatchedDijkstra(s, R) (Algorithm 1): rounds `r = 0, 1, …, R`; returns the estimates `d`. -/
noncomputable def batchedDijkstra {ι : Type*} [Fintype V] (G0 : WGraph V) (Bk : ι → Finset V)
    (α : ℝ) (sk : ℕ → ι → Finset V → ℕ → WGraph V) (s : V) (R : ℕ) : V → ℝ≥0∞ :=
  ((List.range (R + 1)).foldl (fun st r => bdRound G0 Bk α sk r st) (bdInit s)).d

/-- The graph `G_α ∪ H_α` with `H = H0 ∪ ⋃_B TC_w((G ∪ H0)[B])`, for `G0 = G ∪ H0`. -/
noncomputable def roundedUnion {ι : Type*} (G0 : WGraph V) (Bk : ι → Finset V) (α : ℝ) :
    WGraph V :=
  rounded (fun u v => G0 u v ⊓ ⨅ i, closureOn G0 (↑(Bk i) : Set V) u v) α

end SemiStreamReach.Main


