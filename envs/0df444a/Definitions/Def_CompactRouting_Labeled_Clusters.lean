-- Prove2me | Definitions.Def_CompactRouting_Labeled_Clusters
-- name    : CompactRouting_Labeled_Clusters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:05:47.064924+00:00
-- url     : https://prove2.me/theorems/34889959-f4ea-4244-9c72-60ac65e254e5
-- title:
--   Heights, pivots with the tie rule, and clusters $C(w)$ (§2.1)
-- statement:
--   Let $G$ be a connected graph with positive weights, $k\ge2$ and $V=A_0\supseteq A_1\supseteq\cdots\supseteq A_{k-1}\supseteq A_k=\emptyset$ a hierarchy with $A_{k-1}\ne\emptyset$. For $X\subseteq V$ write $d(u,X)=\min_{x\in X}d(u,x)$ with $d(u,\emptyset)=\infty$, and let $p(u,X)$ be a vertex of $X$ closest to $u$. The **height** of $u$ at level $i$ is $h_i(u)=d(u,A_i)$. The **pivots** of $u$ are
--   $$p_{k-1}(u)=p(u,A_{k-1}),\qquad p_i(u)=\begin{cases}p_{i+1}(u)&\text{if }h_i(u)=h_{i+1}(u),\\ p(u,A_i)&\text{otherwise}\end{cases}\quad(i<k-1),$$
--   so $d(u,p_i(u))=h_i(u)$. The **cluster** of $w$ with respect to $Y$ is $C(w,Y)=\{v\in V: d(w,v)<d(v,Y)\}$; $C_i(w)=C(w,A_{i+1})$, and for $w\in A_i\setminus A_{i+1}$ the cluster of $w$ is $C(w)=C_i(w)$. Bunches $B_i(u)=\{w\in A_i: d(u,w)<d(u,A_{i+1})\}$ and $B(u)=\bigcup_{i\in[k]}B_i(u)$ are the published `bunchAt` and `bunch`.
--
--   **Formalization Note.** `height A i u` is the real number $h_i(u)$ (the `WithTop` value $d(u,A_i)$ with $\infty$ sent to $0$; it is finite for $i<k$). `IsPivots A p` is a predicate on a pivot map $p:\mathbb N\to V\to V$: any choice among closest vertices is allowed, the tie rule is enforced. `topLevel A w` is the largest $i\le k$ with $w\in A_i$, i.e. the level $i$ with $w\in A_i\setminus A_{i+1}$.
-- source:
--   Lifshitz, Chechik, Kadria, Roditty, Optimal (Randomized) Compact Routing Schemes, arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 5 (§2, d(u, X), p(u, X)) and p. 6 (§2.1, heights, pivots, clusters)

import Mathlib
import Definitions.Def_TZLevelsADO_Hierarchy

/-!
# Heights, pivots with the tie rule, and clusters

Lifshitz, Chechik, Kadria, Roditty, *Optimal (Randomized) Compact Routing Schemes*,
arXiv:2611.04744 (held version, sha256 d7e0fc67…), §2 p. 5 (`d(u, X)`, `p(u, X)`) and §2.1
p. 6 (heights, pivots, bunches, clusters).

Conventions.
* The hierarchy `V = A_0 ⊇ ⋯ ⊇ A_{k-1} ⊇ A_k = ∅` is the published `TZLevelsADO.Hierarchy`
  (which includes `A_{k-1} ≠ ∅`, needed for `p_{k-1}(u) = p(u, A_{k-1})` to exist); bunches
  `B_i(u) = B(u, A_i, A_{i+1})` and `B(u)` are the published `bunchAt` and `bunch`, and
  `d(u, X)` is the published `distToSet` (value `⊤ = ∞` on `∅`).
* `height A i u` is the real number `h_i(u) = d(u, A_i)` for `i < k` (where `A_i ≠ ∅`).
* `IsPivots A p` says that `p` is a choice of pivots following the page's rule:
  `p_{k-1}(u)` is a vertex of `A_{k-1}` closest to `u`, and for `i < k - 1`,
  `p_i(u) = p_{i+1}(u)` if `h_i(u) = h_{i+1}(u)` and otherwise `p_i(u)` is a vertex of `A_i`
  closest to `u`. Ties among closest vertices may be broken in any way.
* `cluster A w` is `C(w) = C_i(w) = C(w, A_{i+1})` for the level `i` with `w ∈ A_i \ A_{i+1}`.
-/

namespace CompactRouting.Labeled

open TZLevelsADO

/-- §2.1, p. 6: the height `h_i(u) = d(u, A_i)` as a real number (finite for `i < k`). -/
noncomputable def height {G : Graph} {k : ℕ} (A : Hierarchy G k) (i : ℕ) (u : Fin G.n) : ℝ :=
  WithTop.untopD 0 (distToSet G (A.A i) u)

/-- §2.1, p. 6: `p` is a choice of pivots `p_i(u)` (`i ∈ [k]`) following the page's rule
`p_{k-1}(u) = p(u, A_{k-1})`, and for `i < k - 1`, `p_i(u) = p_{i+1}(u)` if
`h_i(u) = h_{i+1}(u)`, `p_i(u) = p(u, A_i)` otherwise, where `p(u, X)` is a vertex of `X`
closest to `u`. -/
def IsPivots {G : Graph} {k : ℕ} (A : Hierarchy G k) (p : ℕ → Fin G.n → Fin G.n) : Prop :=
  ∀ u : Fin G.n,
    (p (k - 1) u ∈ A.A (k - 1) ∧ ∀ w ∈ A.A (k - 1), dist G u (p (k - 1) u) ≤ dist G u w) ∧
    ∀ i : ℕ, i + 1 < k →
      (distToSet G (A.A i) u = distToSet G (A.A (i + 1)) u → p i u = p (i + 1) u) ∧
      (distToSet G (A.A i) u ≠ distToSet G (A.A (i + 1)) u →
        p i u ∈ A.A i ∧ ∀ w ∈ A.A i, dist G u (p i u) ≤ dist G u w)

/-- The level `i` of `w`, i.e. the largest `i ≤ k` with `w ∈ A_i`; since `A_0 = V` and
`A_k = ∅`, it is the unique `i ∈ [k]` with `w ∈ A_i \ A_{i+1}`. -/
def topLevel {G : Graph} {k : ℕ} (A : Hierarchy G k) (w : Fin G.n) : ℕ :=
  Nat.findGreatest (fun i => w ∈ A.A i) k

/-- §2.1, p. 6: the cluster `C(w, Y) = {v ∈ V | d(w, v) < d(v, Y)}`. -/
noncomputable def clusterOf (G : Graph) (Y : Finset (Fin G.n)) (w : Fin G.n) :
    Finset (Fin G.n) := by
  classical
  exact Finset.univ.filter fun v => ((dist G w v : ℝ) : WithTop ℝ) < distToSet G Y v

/-- §2.1, p. 6: `C_i(w) = C(w, A_{i+1})`. -/
noncomputable def clusterAt {G : Graph} {k : ℕ} (A : Hierarchy G k) (i : ℕ) (w : Fin G.n) :
    Finset (Fin G.n) :=
  clusterOf G (A.A (i + 1)) w

/-- §2.1, p. 6: the cluster `C(w) = C_i(w)` for `w ∈ A_i \ A_{i+1}`. -/
noncomputable def cluster {G : Graph} {k : ℕ} (A : Hierarchy G k) (w : Fin G.n) :
    Finset (Fin G.n) :=
  clusterAt A (topLevel A w) w

end CompactRouting.Labeled


