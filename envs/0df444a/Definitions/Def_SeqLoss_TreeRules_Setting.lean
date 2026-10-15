-- Prove2me | Definitions.Def_SeqLoss_TreeRules_Setting
-- name    : SeqLoss_TreeRules_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:56.199582+00:00
-- url     : https://prove2.me/theorems/74c15a12-072f-4f20-92db-f1dfdbdcaf54
-- title:
--   pp. 15–17, 25 — loss trees, V(T), N(T), losses, continuous label-invariant rules, φ^λ (Definition 2), T_n, ℓ_n, P^v, [v], T^v
-- statement:
--   This file fixes the tree model of Section 5 of Gudmundsson, Hougaard and Ko.
--
--   1. **Trees.** Agents are natural numbers and an edge $ij \in \mathbb N\times\mathbb N$ records that agent $i$ causes a loss to agent $j$. A finite edge set $T$ covers the vertices $V(T)=\bigcup_{ij\in T}\{i,j\}$. It is a **tree** if it has a root $r\in V(T)$ with no incoming edge, every other vertex of $V(T)$ has exactly one incoming edge, and every vertex of $V(T)$ is reached from $r$ along edges. The **non-leaf vertices** $N(T)=\{i : ij\in T \text{ for some } j\}$ are the agents who share the losses; leaves are victims only and carry no liability. A vertex of $T$ with no incoming edge is the **root** (the initiator).
--
--   2. **Losses.** A loss function is $\ell:\mathbb N\times\mathbb N\to\mathbb R_{\ge 0}$; $\ell(ij)$ is the loss agent $i$ causes agent $j$. The total loss of a tree is $L=\sum_{e\in T}\ell(e)$.
--
--   3. **Rules.** A rule assigns to each tree $T$, loss $\ell$ and agent $i\in N(T)$ a liability $\varphi_i(T,\ell)$. It is required that, for every tree $T$ and loss $\ell$:
--      - $\varphi_i(T,\ell)\ge 0$ for each $i\in N(T)$;
--      - $\sum_{i\in N(T)}\varphi_i(T,\ell)=L$;
--      - **label invariance** (footnote 9): for every bijection $\pi:\mathbb N\to\mathbb N$, with $T^\pi=\{\pi(i)\pi(j) : ij\in T\}$, and every loss $\ell^\pi$ with $\ell^\pi(\pi(i)\pi(j))=\ell(ij)$ for each $ij\in T$, one has $\varphi_i(T,\ell)=\varphi_{\pi(i)}(T^\pi,\ell^\pi)$ for each $i\in N(T)$;
--      - **continuity** (the standing assumption of Section 2): $\varphi_i(T,a\ell)\to\varphi_i(T,\ell)$ as $a\to 1$, for each $i\in N(T)$.
--
--   4. **The fixed-fraction rule** $\varphi^\lambda$ (Definition 2): agent $i$ pays the fraction $\lambda$ of the losses it causes directly, and the root $r$ pays in addition $(1-\lambda)L$:
--   $$\varphi^\lambda_i(T,\ell)=\lambda\sum_{ij\in T}\ell(ij)+\begin{cases}(1-\lambda)L & i=r,\\ 0 & \text{otherwise.}\end{cases}$$
--
--   5. **Elementary tree problems** (p. 17): $T_n=\{12,23,\dots,(n,n+1)\}$ and $\ell_n$ zero everywhere except $\ell_n(n,n+1)=1$; $e_n\equiv(T_n,\ell_n)$.
--
--   6. **Paths and subtrees** (p. 25): for a vertex $v$, $P^v\subseteq T$ is the set of edges on the path from the root to $v$, $[v]=|V(P^v)|$ is the number of vertices on that path, and $T^v\subseteq T$ is the maximal subtree of $T$ rooted at $v$ (every edge whose tail is $v$ or a descendant of $v$). In Figure 2, $T=\{12,13,24,25,36\}$ and $v=2$ give $P^v=\{12\}$, $[v]=2$, $T^v=\{24,25\}$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** A tree is a `Finset (ℕ × ℕ)`; the three tree conditions above are, for a finite edge set, the paper's "one root vertex and, for every vertex, a unique path to the root", and they force $T\neq\emptyset$. Lean's $\mathbb N$ contains $0$ while the paper's starts at $1$; under label invariance the extra label is harmless. A rule is a function `φ T ℓ i` defined on all edge sets, functions and naturals, but only its values at trees, non-negative losses and agents $i\in N(T)$ carry meaning, and every condition and statement of the mission quantifies only over those. Label invariance quantifies over every non-negative $\ell^\pi$ agreeing with $\ell$ on $T^\pi$, as footnote 9 does. Continuity is not restated in Section 5 but is standing from Section 2 and is used in the proof of Proposition 3. The root in $\varphi^\lambda$ is detected as the vertex with no incoming edge, not hard-coded as label 1. $[v]$ is computed as $|P^v|+1$.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 7 (continuity), pp. 15–17 (§5, Definition 2, footnote 9, T_n and ℓ_n), p. 25 (P^v, [v], T^v)

import Mathlib

namespace SeqLoss.TreeRules

/-- The vertices `V(T) = ⋃_{ij ∈ T} {i, j}` covered by an edge set `T ⊆ ℕ × ℕ` (p. 15). -/
def V (T : Finset (ℕ × ℕ)) : Finset ℕ := T.image Prod.fst ∪ T.image Prod.snd

/-- The non-leaf vertices `N(T)`: the vertices with an outgoing edge, i.e. the agents who share
the losses (p. 15). -/
def N (T : Finset (ℕ × ℕ)) : Finset ℕ := T.image Prod.fst

/-- The edge relation of `T`: `a → b` iff `(a, b) ∈ T` (agent `a` causes a loss to agent `b`). -/
def Edge (T : Finset (ℕ × ℕ)) (a b : ℕ) : Prop := (a, b) ∈ T

/-- `T` is a tree (p. 15): it has a root vertex `r ∈ V(T)` with no incoming edge, every other
vertex has exactly one incoming edge, and every vertex is reached from the root along edges.
For a finite edge set this is the paper's "one root vertex and, for every vertex, a unique path to
the root"; in particular `T` is nonempty. -/
def IsTree (T : Finset (ℕ × ℕ)) : Prop :=
  ∃ r ∈ V T, (∀ e ∈ T, e.2 ≠ r) ∧ (∀ v ∈ V T, v ≠ r → ∃! u, (u, v) ∈ T) ∧
    ∀ v ∈ V T, Relation.ReflTransGen (Edge T) r v

/-- `i` is the root (initiator) of the tree `T`: a vertex of `T` with no incoming edge. -/
def IsRootOf (T : Finset (ℕ × ℕ)) (i : ℕ) : Prop := i ∈ V T ∧ ∀ e ∈ T, e.2 ≠ i

/-- A loss function `ℓ : E → ℝ_{≥0}` (p. 16): `ℓ (i, j)` is the loss agent `i` causes agent `j`. -/
def IsTreeLoss (ℓ : ℕ × ℕ → ℝ) : Prop := ∀ e, 0 ≤ ℓ e

/-- Relabelling of a tree by a bijection `π : ℕ → ℕ` (footnote 9): `T^π = {π(i)π(j) | ij ∈ T}`. -/
def relabel (π : ℕ ≃ ℕ) (T : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  T.map (π.prodCongr π).toEmbedding

/-- A (continuous, label-invariant) rule on loss trees (pp. 7, 16 and footnote 9).
`φ T ℓ i` is agent `i`'s liability `φ_i(T, ℓ)`; only its values at trees `T`, losses `ℓ` and
agents `i ∈ N(T)` carry meaning. For every tree `T` and loss `ℓ`:
1. liabilities are non-negative;
2. they add up to the total loss `L = ∑_{e ∈ T} ℓ(e)`;
3. invariance to agent labels: for every bijection `π` of `ℕ` and every loss `ℓ^π` with
   `ℓ^π(π(i), π(j)) = ℓ(i, j)` for `ij ∈ T`, `φ_i(T, ℓ) = φ_{π(i)}(T^π, ℓ^π)`;
4. continuity (§2's standing assumption, footnote 3): `φ_i(T, aℓ) → φ_i(T, ℓ)` as `a → 1`. -/
def IsTreeRule (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ) : Prop :=
  ∀ T, IsTree T → ∀ ℓ, IsTreeLoss ℓ →
    (∀ i ∈ N T, 0 ≤ φ T ℓ i) ∧
    (∑ i ∈ N T, φ T ℓ i = ∑ e ∈ T, ℓ e) ∧
    (∀ (π : ℕ ≃ ℕ) (ℓ' : ℕ × ℕ → ℝ), IsTreeLoss ℓ' → (∀ e ∈ T, ℓ' (π e.1, π e.2) = ℓ e) →
      ∀ i ∈ N T, φ T ℓ i = φ (relabel π T) ℓ' (π i)) ∧
    (∀ i ∈ N T, Filter.Tendsto (fun a : ℝ => φ T (a • ℓ) i) (nhds 1) (nhds (φ T ℓ i)))

/-- The fixed-fraction rule `φ^λ` on trees (Definition 2, p. 16): agent `i` pays the fraction `λ`
of the losses it causes directly, and the initiator (the root, the vertex with no incoming edge)
pays in addition `(1 - λ) L`. -/
def fixedFractionTree (lam : ℝ) (T : Finset (ℕ × ℕ)) (ℓ : ℕ × ℕ → ℝ) (i : ℕ) : ℝ :=
  lam * ∑ e ∈ T.filter (fun e => e.1 = i), ℓ e +
    if (∀ e ∈ T, e.2 ≠ i) then (1 - lam) * ∑ e ∈ T, ℓ e else 0

/-- `P^v` (p. 25): the edges of the path from the root to `v`, i.e. the edges `(a, b) ∈ T` whose
head `b` is an ancestor of `v` or `v` itself. -/
noncomputable def pathTo (T : Finset (ℕ × ℕ)) (v : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact T.filter (fun e => Relation.ReflTransGen (Edge T) e.2 v)

/-- `[v] = |V(P^v)|` (p. 25): the number of vertices on the path from the root to `v`
(`= |P^v| + 1`; the root has `[r] = 1`). -/
noncomputable def depth (T : Finset (ℕ × ℕ)) (v : ℕ) : ℕ := (pathTo T v).card + 1

/-- `T^v` (p. 25): the maximal sub-tree of `T` with root `v`, i.e. the edges `(a, b) ∈ T` whose
tail `a` is `v` or a descendant of `v`. -/
noncomputable def subtreeAt (T : Finset (ℕ × ℕ)) (v : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact T.filter (fun e => Relation.ReflTransGen (Edge T) v e.1)

/-- The chain `T_n = {12, 23, …, (n, n+1)}` (p. 17). -/
def treeChain (n : ℕ) : Finset (ℕ × ℕ) := (Finset.Icc 1 n).image (fun i => (i, i + 1))

/-- The loss `ℓ_n` (p. 17): zero everywhere except `ℓ_n(n, n+1) = 1`. Together with `T_n` it is
the elementary tree problem `e_n ≡ (T_n, ℓ_n)`. -/
def chainLoss (n : ℕ) (e : ℕ × ℕ) : ℝ := if e = (n, n + 1) then 1 else 0

end SeqLoss.TreeRules


