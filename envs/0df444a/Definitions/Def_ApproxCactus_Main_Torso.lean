-- Prove2me | Definitions.Def_ApproxCactus_Main_Torso
-- name    : ApproxCactus_Main_Torso
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:01:10.593257+00:00
-- url     : https://prove2.me/theorems/536c1a25-8f72-4017-bdbc-6dd70b280388
-- title:
--   Componental and irrelevant separations, torsos of stars, lifts and the numbers (n choose ⩽ k − 1)
-- statement:
--   For a separation $s$ of $G$ and a component $K$ of $G-\mathrm{sep}(s)$, the separation $(K\cup N(K),V(G)\setminus K)$ is a **componental separation at $s$**. A separation $s'$ is **$(\beta,k)$-irrelevant** if it has order $<k$ and is componental at some $\beta$-broad separation of order exactly $k$.
--
--   The **torso** of a set $\sigma=\{(A_i,B_i)\}$ of separations is the graph on $\bigcap_i B_i$ (all of $V(G)$ if $\sigma=\emptyset$) in which two distinct vertices are adjacent if they are adjacent in $G$ or both lie in a common separator $A_i\cap B_i$. If $s=(A,B)$ is a separation of the torso $Z$ and $\hat s=(\hat A,\hat B)$ a separation of $G$ with $A=\hat A\cap V(Z)$, $B=\hat B\cap V(Z)$ and $\mathrm{sep}(s)=\mathrm{sep}(\hat s)$, then $\hat s$ is a **lift** of $s$ (Definition 9.23). Finally $\binom{n}{\le k-1}=\sum_{i=0}^{k-1}\binom ni$ (with $\binom ni=0$ for $i>n$; the empty sum $0$ when $k=0$).
--
--   Formalization note: the torso is a `SimpleGraph` on the subtype of vertices in `torsoVerts σ`, so separations of the torso are pairs of `Finset`s of that subtype.
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), pp. 22, 95, 112, 115 (PDF 25, 98, 115, 118), §3.2, Definition 9.23, §11.1, §11.2

import Definitions.Def_ApproxCactus_Main_Separations

namespace ApproxCactus.Main

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `s' = (A', B')` is a **componental separation at `s`** (§11.1, p. 112): for some component `K`
of `G − sep(s)`, `s' = (V(K) ∪ N(K), V(G − K))`. -/
def IsComponentalAt (G : SimpleGraph V) (s s' : Finset V × Finset V) : Prop :=
  ∃ K : Set V, IsComponentOf G (s.1 ∩ s.2) K ∧
    (↑s'.1 : Set V) = K ∪ nbhd G K ∧ (↑s'.2 : Set V) = Kᶜ

/-- `s'` is **`(β, k)`-irrelevant** (§11.1, p. 112): a componental `(< k)`-separation at some
`β`-broad `k`-separation of `G`. -/
def IsIrrelevant (G : SimpleGraph V) (β k : ℕ) (s' : Finset V × Finset V) : Prop :=
  order s' < k ∧ ∃ s : Finset V × Finset V, IsSep G s ∧ order s = k ∧ β ≤ breadth s ∧
    IsComponentalAt G s s'

/-- The vertex set `⋂_i B_i` of the torso of `σ = {(A_i, B_i)}` (all of `V(G)` for `σ = ∅`). -/
noncomputable def torsoVerts (σ : Set (Finset V × Finset V)) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∀ s ∈ σ, v ∈ s.2)

/-- The **torso** of `σ = {(A_i, B_i)}` (§3.2, p. 22): the graph obtained from `G[⋂_i B_i]` by
making every separator `A_i ∩ B_i` into a clique (on the torso's vertex set). It is a simple graph
on the subtype of vertices in `torsoVerts σ`; for `σ = ∅` it is `G`. -/
def torso (G : SimpleGraph V) (σ : Set (Finset V × Finset V)) :
    SimpleGraph {v : V // v ∈ torsoVerts σ} :=
  SimpleGraph.fromRel (fun u v =>
    G.Adj u.1 v.1 ∨ ∃ s ∈ σ, u.1 ∈ s.1 ∩ s.2 ∧ v.1 ∈ s.1 ∩ s.2)

/-- **Lift** (Definition 9.23, p. 95). Let `σ` be a star with torso `H`, `s = (A, B)` a separation
of `H` and `ŝ = (Â, B̂)` a separation of `G`. Then `ŝ` is a lift of `s` if `A = Â ∩ V(H)`,
`B = B̂ ∩ V(H)` and `sep(s) = sep(ŝ)` (vertices of `H` viewed as vertices of `G`). -/
def IsLift (G : SimpleGraph V) (σ : Set (Finset V × Finset V))
    (s : Finset {v : V // v ∈ torsoVerts σ} × Finset {v : V // v ∈ torsoVerts σ})
    (ŝ : Finset V × Finset V) : Prop :=
  IsSep (torso G σ) s ∧ IsSep G ŝ ∧
    ŝ.1 ∩ torsoVerts σ = s.1.map (Function.Embedding.subtype _) ∧
    ŝ.2 ∩ torsoVerts σ = s.2.map (Function.Embedding.subtype _) ∧
    ŝ.1 ∩ ŝ.2 = (s.1 ∩ s.2).map (Function.Embedding.subtype _)

/-- `(n choose ⩽ k − 1) = Σ_{i=0}^{k−1} (n choose i)` (p. 115, with `(n choose i) = 0` for
`i > n`), written `Σ_{i < k}` so that it is the empty sum `0` for `k = 0`. -/
def chooseBelow (n k : ℕ) : ℕ := ∑ i ∈ Finset.range k, n.choose i

end ApproxCactus.Main


