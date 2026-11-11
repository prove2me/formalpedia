-- Prove2me | Definitions.Def_SemiStreamReach_Main_LateLevel
-- name    : SemiStreamReach_Main_LateLevel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:51:36.051613+00:00
-- url     : https://prove2.me/theorems/f776a0c1-0b77-40eb-9deb-26d026b0c0c5
-- title:
--   Balls $R^{\pm}_d$, pivot blocks $B_p$, $(1+\varepsilon)$-approximate block closures, and the indices $i,j$ of a piece at a late level
-- statement:
--   For a graph $G'$, a vertex $v$ and $d\ge0$: $R^+_d(G',v)=\{u:\mathrm{dist}_{G'}(v,u)\le d\}$, $R^-_d(G',v)=\{u:\mathrm{dist}_{G'}(u,v)\le d\}$ and $R^\pm_d(G',v)=R^-_d(G',v)\cup R^+_d(G',v)$. At a late level, each pivot $p$ of $G'$ has a radius $\rho_p$, an **in-ball** $R^-_{\rho_p}(G',p)$, an **out-ball** $R^+_{\rho_p}(G',p)$ and a **block**
--   $$B_p=R^\pm_{\rho_p+D_r}(G',p).$$
--   The **$(1+\varepsilon)$-approximate block closure** of $B_p$ has an edge $(u,v)$ for each pair $(u,v)\in TC(G'[B_p])$, with a weight between $\mathrm{dist}_{G'[B_p]}(u,v)$ and $(1+\varepsilon)\,\mathrm{dist}_{G'[B_p]}(u,v)$. The **core subgraph with the empty label** is induced by the vertices of $G'$ in no pivot's ball. For a path $Q=\langle v_0,\dots,v_\ell\rangle$, $i$ is the largest index with $v_i$ in the in-ball of some pivot ($i=-1$ if none) and $j$ the smallest index with $v_j$ in the out-ball of some pivot ($j=\ell+1$ if none).
--
--   **Formalization Note.** Pivots are a set `Pi`, radii a function `ρ`, the scale $D_r$ a real `D`. `lastInIdx` is $i$ (an integer), `firstOutIdx` is $j$, `coreVertices` the vertex set of the core subgraph, `IsPathIn G Q` says $Q$ is a nonempty list without repeated vertex whose consecutive pairs are edges.
-- source:
--   Hoppenworth, Li, Mahabadi, Tarnawski, Semi-Streaming Reachability and Shortest Paths in n^{1/3+o(1)} Passes, arXiv:2611.05061 (PDF sha256 c1b64474…), p. 23 (PDF 25), balls; p. 28 (PDF 30), approximate block closures; p. 31 (PDF 33), blocks, pieces, i and j, footnote 15

import Mathlib
import Definitions.Def_SemiStreamReach_Main_Distances

open scoped ENNReal
open Classical

namespace SemiStreamReach.Main

/-! # Balls, pivot blocks, approximate block closures and the pieces of a path at a late level

Hoppenworth, Li, Mahabadi, Tarnawski, arXiv:2611.05061 (PDF sha256 c1b64474…).

* p. 23 (PDF 25): "R^+_d(G′, v) = {u : dist_{G′}(v, u) ≤ d}, R^−_d(G′, v) = {u : dist_{G′}(u, v) ≤ d},
  and R^±_d(G′, v) = R^−_d(G′, v) ∪ R^+_d(G′, v)."
* p. 31 (PDF 33): at a late level `r`, each pivot `p` of a subgraph `G′` has a radius `ρ_p` and
  "records its block B_p = R^±_{ρ_p + D_r}(G′, p)"; its in-ball is `R^−_{ρ_p}(G′, p)` and its
  out-ball `R^+_{ρ_p}(G′, p)`. "The recursion continues only in the core subgraph of G′ with the
  empty label, which is induced by the vertices of G′ that do not lie in any pivot's ball."
* p. 28 (PDF 30): "the (1 + ε)-approximate block closure of B_p has an edge (u, v) for each pair
  (u, v) ∈ TC(G′[B_p]), with a weight between dist_{G′[B_p]}(u, v) and (1 + ε) dist_{G′[B_p]}(u, v)."
* p. 31 (PDF 33): "Consider a piece Q = ⟨v_0, …, v_ℓ⟩ of P at a late level r ≥ r_0, in a subgraph
  G′. … Let i be the largest index such that v_i lies in the in-ball of some pivot of G′. Similarly,
  let j be the smallest index such that v_j lies in the out-ball of some pivot of G′." Footnote 15:
  "We let i = −1 or j = ℓ + 1 if there is no such vertex."

**Formalization Note.** `G′` is a weighted graph on a vertex type `V` (its whole vertex set), the
pivots a set `Π ⊆ V` and the radii a function `ρ : V → ℝ`; `D` stands for the scale `D_r`. The path
`Q` is a list of vertices `v_0, …, v_ℓ` (`ℓ = Q.length − 1`). `lastInIdx` is `i` (an integer, `−1`
if no vertex of `Q` is in an in-ball) and `firstOutIdx` is `j` (`ℓ + 1 = Q.length` if none). The
core subgraph with the empty label is described by its vertex set `coreVertices`. -/

variable {V : Type*}

/-- The in-ball `R^−_ρ(G, p) = {u : dist_G(u, p) ≤ ρ}`. -/
def inBall (G : WGraph V) (p : V) (ρ : ℝ) : Set V := {u | dist G u p ≤ ENNReal.ofReal ρ}

/-- The out-ball `R^+_ρ(G, p) = {u : dist_G(p, u) ≤ ρ}`. -/
def outBall (G : WGraph V) (p : V) (ρ : ℝ) : Set V := {u | dist G p u ≤ ENNReal.ofReal ρ}

/-- `R^±_ρ(G, p)`, the union of the in-ball and the out-ball. -/
def ballPM (G : WGraph V) (p : V) (ρ : ℝ) : Set V := inBall G p ρ ∪ outBall G p ρ

/-- The block `B_p = R^±_{ρ_p + D}(G, p)` of a pivot `p` with radius `ρ_p`, at scale `D`. -/
def pivotBlock (G : WGraph V) (p : V) (ρp D : ℝ) : Set V := ballPM G p (ρp + D)

/-- `C` is a `(1 + ε)`-approximate block closure of the block `B` of `G`: it has an edge `(u, v)`
exactly for the pairs `u, v ∈ B` with `v` reachable from `u` in `G[B]`, with weight between
`dist_{G[B]}(u, v)` and `(1 + ε) dist_{G[B]}(u, v)`. -/
def IsApproxBlockClosure (G : WGraph V) (B : Set V) (ε : ℝ) (C : WGraph V) : Prop :=
  ∀ u v,
    ((u ∈ B ∧ v ∈ B ∧ Reaches (induced G B) u v) →
      dist (induced G B) u v ≤ C u v ∧ C u v ≤ ENNReal.ofReal (1 + ε) * dist (induced G B) u v) ∧
    (¬ (u ∈ B ∧ v ∈ B ∧ Reaches (induced G B) u v) → C u v = ⊤)

/-- `Q` is a (simple) path in `G`: nonempty, no repeated vertex, consecutive vertices joined by
edges of `G`. -/
def IsPathIn (G : WGraph V) (Q : List V) : Prop :=
  Q ≠ [] ∧ Q.Nodup ∧ List.IsChain (fun a b => G a b ≠ ⊤) Q

/-- The index `i`: the largest index of a vertex of `Q` in the in-ball of some pivot, `−1` if none. -/
noncomputable def lastInIdx (G : WGraph V) (Pi : Set V) (ρ : V → ℝ) (Q : List V) : ℤ :=
  (((Finset.range Q.length).filter
      (fun k => ∃ hk : k < Q.length, ∃ p ∈ Pi, Q[k] ∈ inBall G p (ρ p))).sup (· + 1) : ℕ) - 1

/-- The index `j`: the smallest index of a vertex of `Q` in the out-ball of some pivot,
`ℓ + 1 = Q.length` if none. -/
noncomputable def firstOutIdx (G : WGraph V) (Pi : Set V) (ρ : V → ℝ) (Q : List V) : ℕ :=
  if h : ∃ k, ∃ hk : k < Q.length, ∃ p ∈ Pi, Q[k] ∈ outBall G p (ρ p) then Nat.find h
  else Q.length

/-- The vertex set of the core subgraph with the empty label: the vertices in no pivot's in-ball
or out-ball. -/
def coreVertices (G : WGraph V) (Pi : Set V) (ρ : V → ℝ) : Set V :=
  {v | ∀ p ∈ Pi, v ∉ inBall G p (ρ p) ∧ v ∉ outBall G p (ρ p)}

end SemiStreamReach.Main


