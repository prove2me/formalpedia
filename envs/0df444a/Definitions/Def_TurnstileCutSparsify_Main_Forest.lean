-- Prove2me | Definitions.Def_TurnstileCutSparsify_Main_Forest
-- name    : TurnstileCutSparsify_Main_Forest
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:40:23.221512+00:00
-- url     : https://prove2.me/theorems/52aed554-2c72-4967-bae2-145d00300632
-- title:
--   Rooted forests, fundamental cuts, query cuts (5), accurate query cuts (Definition 4.1), approximate Gomory–Hu trees and query forests (Lemma 7.2)
-- statement:
--   A **rooted forest** on $V$ assigns every non-root vertex $v$ a parent; the tree edge $q=\{v,\mathrm{par}\,v\}$ carries a weight $\tau_q$. The **fundamental cut** $S_q$ of a tree edge is the vertex set of the component of the tree minus $q$ that contains the root. For $u,v$ in one tree, $q$ lies on the $u$–$v$ path exactly when one of $u,v$ lies below $q$.
--
--   **Query cuts (5).** A pair $e=uv$ is **eligible** if $u,v$ lie in a common tree. Choosing a minimum-weight edge $q(e)$ on the $u$–$v$ path (ties broken deterministically) gives the query weight $\kappa_e=\tau_{q(e)}$, the query cut $S_e=S_{q(e)}$ and the scale $t_e(k)=2^{-k}\kappa_e/\beta$.
--
--   **Definition 4.1.** The query cuts are **accurate** (for a weight vector $x$) if the eligible pairs are exactly the pairs with $\lambda_e(x)>0$ and every eligible pair satisfies (6): $.9\lambda_e\le\kappa_e\le1.1\lambda_e$, $|e\cap S_e|=1$, $x(S_e,V\setminus S_e)\le\kappa_e/.9$.
--
--   **Approximate Gomory–Hu trees** (Li–Panigrahi, p. 11). A $(1+\varepsilon_0)$-approximate Gomory–Hu tree of a connected graph $H$ is a weighted tree $T$ on $V(H)$ such that for all vertices $u\neq v$ and a minimum-weight edge $q$ on the $u$–$v$ path of $T$, the component of $T-q$ containing $u$ is a cut of $H$ of weight at most $(1+\varepsilon_0)\lambda_H(u,v)$, and this weight equals the weight of $q$.
--
--   **Query forests** (the conclusion of Lemma 7.2). The trees are the connected components $C_a$ of $H$ with at least two vertices, each rooted at $r_a=\min C_a$; every tree edge has $\tau_q=w_H(S_q,V\setminus S_q)>0$; and $\lambda_H(u,v)\le\tau_q\le1.01\lambda_H(u,v)$ for all distinct $u,v\in C_a$ and every minimum-weight edge $q$ on their path.
--
--   **Formalization Note** `RootedForest n` = `par : Fin n → Option (Fin n)`, `τ : Fin n → ℝ` (a tree edge is named by its lower endpoint); `IsAcyclic`: following parents reaches a root; `fundCut F v = treeOf F v \ subtree F v`; `OnPath`, `IsMinPathEdge`; `QueryChoice F q`: `q e` is a minimum-weight edge on the path of every eligible `e`; `qWeight`, `qCut`; `Accurate x F q`; `IsApproxGH ε₀ x T` for a spanning tree (exactly one root) in parent form, with "every minimum-weight edge" (equivalent to "a", since every tree edge is the unique path edge of its own endpoints); `IsQueryForest x F`: a vertex of a one-vertex component is a childless root. `RatForest` carries weights `num/den`; `encRatForest`/`decodeRatForest` write and read it as `3n` words (parent codes `0` = root, `p + 1`; numerators; positive denominators).
-- source:
--   Lin, Mirrokni, Woodruff (2026), Near-Optimal Space and Time Cut Sparsification in Turnstile Streams, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), §2.3 p. 11, (5)–(6) p. 13, Definition 4.1 p. 15, Lemma 7.2 p. 29

import Mathlib
import Definitions.Def_TurnstileCutSparsify_Main_Graph
import Definitions.Def_TurnstileCutSparsify_Main_Streaming

open scoped BigOperators Classical

noncomputable section

namespace TurnstileCutSparsify.Main

open TurnstileRank.TightBounds.RAM

/-!
# Rooted forests, query cuts, accurate query cuts and approximate Gomory–Hu trees

Lin, Mirrokni, Woodruff, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…),
§2.3 p. 11 (Gomory–Hu trees, approximate Gomory–Hu trees after Li–Panigrahi), §3.1 (5)–(6) p. 13
(query cuts), Definition 4.1 p. 15 (accurate query cuts), Lemma 7.2 p. 29 (query forests).

* A rooted forest on `[n]` is a parent map `par` (`none` at a root) with a weight `τ v` on the
  tree edge `q = {v, par v}` of every non-root `v`; a tree edge is named by its lower endpoint.
  `IsAcyclic`: following parents from any vertex reaches a root.
* `subtree F v`: the vertices having `v` as an ancestor (or equal to `v`). `sameTree F u v`: `u` and
  `v` have a common root. `fundCut F v = treeOf F v \ subtree F v` is the fundamental cut `S_q` of
  the tree edge `q` above `v`: the vertex set of the component of the tree minus `q` that contains
  the root.
* `onPath F u v q`: for `u, v` in one tree, the tree edge `q` lies on the `u`–`v` path, i.e. exactly
  one of `u, v` lies below `q`. `IsMinPathEdge F u v q`: `q` is a minimum-weight edge of that path.
* Query cuts (5): a pair `e` is eligible when its endpoints lie in a common tree; a choice `q(e)` of
  a minimum-weight edge on its path (`QueryChoice`, any deterministic tie-breaking) gives the query
  weight `κ_e = τ_{q(e)}` and the query cut `S_e = S_{q(e)}`.
* `Accurate x F q` is Definition 4.1 for the weight vector `x`: the eligible pairs are exactly the
  pairs with `λ_e(x) > 0`, and every eligible pair satisfies (6):
  `.9 λ_e ≤ κ_e ≤ 1.1 λ_e`, `|e ∩ S_e| = 1`, `x(S_e, V \ S_e) ≤ κ_e / .9`.
* `IsApproxGH ε₀ x T` (Li–Panigrahi, p. 11): `T` is a spanning tree of `[n]` (one root) and, for
  all distinct `u, v` and every minimum-weight edge `q` on the `u`–`v` path of `T`, the component
  of `T − q` containing `u` is a cut of `x` of weight at most `(1 + ε₀) λ_x(u, v)`, and this weight
  equals the weight of `q`.
* `IsQueryForest x F` is the conclusion of Lemma 7.2: the trees of `F` are the connected components
  of `x` with at least two vertices, each rooted at its smallest vertex (a vertex of a one-vertex
  component is a root without children), and (1) `τ_q = x(S_q, V \ S_q) > 0` for every tree edge,
  (2) `λ_x(u, v) ≤ τ_q ≤ 1.01 λ_x(u, v)` for distinct `u, v` of one tree and every minimum-weight
  edge `q` on their path.
* `RatForest`: a rooted forest with rational weights `num / den` (the form in which forests are
  input to and output by word-RAM programs); `encRatForest` writes it as `3n` words (parent codes,
  `0` for a root and `p + 1` for parent `p`; numerators; denominators), and `decodeRatForest` reads
  it from cells `0, …, 3n − 1`.
-/

variable {n : ℕ}

/-- A rooted forest on `[n]`: parent map and tree-edge weights. -/
structure RootedForest (n : ℕ) where
  par : Fin n → Option (Fin n)
  τ : Fin n → ℝ

namespace RootedForest

variable (F : RootedForest n)

/-- The `k`-th ancestor (`none` past the root). -/
def anc : ℕ → Fin n → Option (Fin n)
  | 0, v => some v
  | k + 1, v => (anc k v).bind F.par

/-- Following parents from any vertex reaches a root. -/
def IsAcyclic : Prop := ∀ v, ∃ k, F.anc k v = none

/-- `a` is an ancestor of `v` or `v` itself. -/
def IsAncOf (a v : Fin n) : Prop := ∃ k, F.anc k v = some a

/-- The vertices below the tree edge above `v` (including `v`). -/
def subtree (v : Fin n) : Finset (Fin n) := Finset.univ.filter fun y => F.IsAncOf v y

/-- `u` and `v` lie in a common tree. -/
def SameTree (u v : Fin n) : Prop := ∃ r, F.par r = none ∧ F.IsAncOf r u ∧ F.IsAncOf r v

/-- The vertex set of the tree containing `v`. -/
def treeOf (v : Fin n) : Finset (Fin n) := Finset.univ.filter fun y => F.SameTree v y

/-- The fundamental cut `S_q` of the tree edge `q` above `v`: the side of its tree minus `q`
containing the root. -/
def fundCut (v : Fin n) : Finset (Fin n) := F.treeOf v \ F.subtree v

/-- The tree edge above `q` lies on the `u`–`v` tree path. -/
def OnPath (u v q : Fin n) : Prop := F.par q ≠ none ∧ (F.IsAncOf q u ↔ ¬ F.IsAncOf q v)

/-- The tree edge above `q` is a minimum-weight edge on the `u`–`v` tree path. -/
def IsMinPathEdge (u v q : Fin n) : Prop :=
  F.OnPath u v q ∧ ∀ y, F.OnPath u v y → F.τ q ≤ F.τ y

/-- A spanning tree: acyclic with exactly one root. -/
def IsSpanningTree : Prop := F.IsAcyclic ∧ ∃! r, F.par r = none

end RootedForest

/-- A pair is eligible when its endpoints lie in a common tree. -/
def Eligible (F : RootedForest n) (e : Pair n) : Prop := F.SameTree e.lo e.hi

/-- `q` chooses, for every eligible pair, a minimum-weight edge on its tree path. -/
def QueryChoice (F : RootedForest n) (q : Pair n → Fin n) : Prop :=
  ∀ e, Eligible F e → F.IsMinPathEdge e.lo e.hi (q e)

/-- The query weight `κ_e = τ_{q(e)}` (5). -/
def qWeight (F : RootedForest n) (q : Pair n → Fin n) (e : Pair n) : ℝ := F.τ (q e)

/-- The query cut `S_e = S_{q(e)}` (5). -/
def qCut (F : RootedForest n) (q : Pair n → Fin n) (e : Pair n) : Finset (Fin n) :=
  F.fundCut (q e)

/-- Definition 4.1: the query cuts of `(F, q)` are accurate for the weight vector `x`. -/
def Accurate (x : Pair n → ℝ) (F : RootedForest n) (q : Pair n → Fin n) : Prop :=
  ∀ e, (Eligible F e ↔ 0 < conn x e) ∧
    (Eligible F e → 0.9 * conn x e ≤ qWeight F q e ∧ qWeight F q e ≤ 1.1 * conn x e ∧
      crosses (qCut F q e) e ∧ cut x (qCut F q e) ≤ qWeight F q e / 0.9)

/-- The component of `T − q` containing `u` (`q` the tree edge above the vertex `q`). -/
def sideOf (T : RootedForest n) (q u : Fin n) : Finset (Fin n) :=
  if T.IsAncOf q u then T.subtree q else Finset.univ \ T.subtree q

/-- A `(1 + ε₀)`-approximate Gomory–Hu tree of `x` (Li–Panigrahi). -/
def IsApproxGH (ε₀ : ℝ) (x : Pair n → ℝ) (T : RootedForest n) : Prop :=
  T.IsSpanningTree ∧ ∀ u v : Fin n, u ≠ v → ∀ q, T.IsMinPathEdge u v q →
    cut x (sideOf T q u) ≤ (1 + ε₀) * connV x u v ∧ cut x (sideOf T q u) = T.τ q

/-- The conclusion of Lemma 7.2 for the graph `x`: a query forest. -/
def IsQueryForest (x : Pair n → ℝ) (F : RootedForest n) : Prop :=
  F.IsAcyclic ∧
  (∀ u v, F.SameTree u v ↔ (supportGraph x).Reachable u v) ∧
  (∀ r, F.par r = none ↔ ∀ y, (supportGraph x).Reachable r y → r ≤ y) ∧
  (∀ v, F.par v ≠ none → F.τ v = cut x (F.fundCut v) ∧ 0 < F.τ v) ∧
  (∀ u v, u ≠ v → F.SameTree u v → ∀ q, F.IsMinPathEdge u v q →
    connV x u v ≤ F.τ q ∧ F.τ q ≤ 1.01 * connV x u v)

/-- A rooted forest with rational weights `num v / den v`. -/
structure RatForest (n : ℕ) where
  par : Fin n → Option (Fin n)
  num : Fin n → ℕ
  den : Fin n → ℕ

/-- The real-weighted forest of a `RatForest`. -/
def RatForest.toForest (F : RatForest n) : RootedForest n :=
  ⟨F.par, fun v => (F.num v : ℝ) / (F.den v : ℝ)⟩

/-- The `3n` words of a `RatForest`: parent codes, numerators, denominators. -/
def encRatForest (F : RatForest n) : List ℕ :=
  (List.ofFn fun v => match F.par v with | none => 0 | some p => p.val + 1) ++
    (List.ofFn F.num) ++ (List.ofFn F.den)

/-- Read a `RatForest` from cells `0, …, 3n − 1` (every denominator positive). -/
def decodeRatForest {S : ℕ} (n : ℕ) (m : Mem S) : Option (RatForest n) :=
  if (∀ i < 3 * n, (rd m i).isSome) ∧ (∀ i < n, (rd m i).getD 0 ≤ n) ∧
      (∀ i < n, 0 < (rd m (2 * n + i)).getD 0) then
    some ⟨fun v => match (rd m v.val).getD 0 with
        | 0 => none
        | p + 1 => if hp : p < n then some ⟨p, hp⟩ else none,
      fun v => (rd m (n + v.val)).getD 0, fun v => (rd m (2 * n + v.val)).getD 0⟩
  else none

end TurnstileCutSparsify.Main


