-- Prove2me | Definitions.Def_SBMThreshold_Main_Paths
-- name    : SBMThreshold_Main_Paths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:03.024659+00:00
-- url     : https://prove2.me/theorems/89aa2cc6-fd4a-40fd-855e-e12203b0c42d
-- title:
--   Definitions 2.4–2.6, 4.1, 4.6, Assumption 2.7 — paths, path weights X_γ, N^(k)_{u,v} and Y_{u,v}, edge types, ℓ-tangles, standing assumptions
-- statement:
--   This file fixes the combinatorial objects and standing assumptions of Mossel, Neeman and Sly.
--
--   **Paths (Definition 2.4).** A path of length $k$ is a sequence $\gamma=(u_0,\dots,u_k)$ of vertices with $u_i\ne u_{i-1}$ for all $i$; it is a path in the complete graph, not necessarily in $G$. Its edge set is $E(\gamma)=\{\{u_{i-1},u_i\}\}$ and its vertex set $V(\gamma)=\{u_0,\dots,u_k\}$. It is *non-backtracking* if $u_i\ne u_{i+2}$ for $0\le i\le k-2$, and *self-avoiding* if $u_0,\dots,u_k$ are distinct. A *simple cycle* of length $z\ge3$ is a sequence $u_0,\dots,u_z$ with $u_z=u_0$ and $u_0,\dots,u_{z-1}$ distinct. The multiplicity $m_e(\gamma)$ of an edge $e$ is the number of $i$ with $\{u_{i-1},u_i\}=e$.
--
--   **Edge types (Definition 4.1).** The step $(u_i,u_{i+1})$ is *new* if $u_{i+1}\notin\{u_0,\dots,u_i\}$; *old* if it is not new and $\{u_i,u_{i+1}\}=\{u_j,u_{j+1}\}$ for some $j<i$; and *returning* otherwise. $k_n(\gamma)$, $k_o(\gamma)$, $k_r(\gamma)$ count the new, old and returning steps.
--
--   **Weights (Definition 2.5).** For a graph $G$ put $W_e=\mathbf 1_{e\in E(G)}-d/n$ with $d=(a+b)/2$, and for a path $X_\gamma=\prod_{i=1}^k W_{\{u_{i-1},u_i\}}$. Then
--   $$
--   N^{(k)}_{u,v}=\sum_{\gamma\in\Gamma^{\mathrm{NB}}_{k,u,v}}X_\gamma ,\qquad Y_{u,v}=\sum_{\gamma\in\Gamma^{\mathrm{SAW}}_{u,v}}X_\gamma ,
--   $$
--   the sums over the non-backtracking, respectively self-avoiding, paths of length $k$ from $u$ to $v$.
--
--   **Tangles (Definitions 2.6, 4.6).** A subgraph $H$ of $G$ is an $\ell$-tangle if it is connected, any two of its vertices are at distance at most $2\ell$ in $H$, and it contains two cycles, i.e. $|E(H)|\ge|V(H)|+1$. $G$ is $\ell$-tangle-free if it has no $\ell$-tangle. A path $\gamma$ has $t$ $\ell$-tangles, $t=t(\gamma)$, if $t$ is the least value of $\sum_{e\in F}m_e(\gamma)$ over the sets $F\subseteq E(\gamma)$ for which the graph $(V(\gamma),E(\gamma)\setminus F)$ is $\ell$-tangle-free.
--
--   **Assumption 2.7.** For positive sequences $a_n,b_n$ with $d_n,s_n$ as above and a sequence $\ell_n$: $d_n,|s_n|\le n^{c_n/\log\log n}$ for all large $n$, for some $c_n\to0$ (that is, $s,d=n^{o(1/\log\log n)}$); and $\log\log n\ll\ell_n\ll\sqrt{\log n}$.
--
--   **Preamble of Theorem 2.8.** $s_n^2/d_n\ge\lambda>1$ for all $n$; $\alpha>0$ satisfies $n^2d_n^{\alpha\log n}\le s_n^{2\alpha\log n}$ for every $n$; and $k=\lceil\alpha\log n\rceil$.
--
--   These objects carry the path-counting lemmas of §4, the moment computations of §5 and the tangle estimates of §6.
--
--   **Formalization Note** A path of length $k$ is a map `Fin (k+1) → Fin n`; its $i$-th step goes from `γ i.castSucc` to `γ i.succ`. Definition 2.6 is encoded by its first clause; the cyclomatic condition $|E(H)|\ge|V(H)|+1$ for connected $H$ is "contains two cycles". Distances are taken in $H$ itself, with $H$ connected, so no junk value of a diameter enters. Tangle-freeness of $(V(\gamma),E(\gamma)\setminus F)$ is evaluated on the graph on all of `Fin n` with that edge set; the extra isolated vertices do not change it. The minimum defining $t(\gamma)$ is a natural-number infimum of a nonempty set ($F=E(\gamma)$ always qualifies). "$\log\log n\ll\ell_n$" is $\ell_n/\log\log n\to\infty$, and "$\ell_n\ll\sqrt{\log n}$" is $\ell_n/\sqrt{\log n}\to0$; logarithms are natural. $s^{2\alpha\log n}$ is written $(s^2)^{\alpha\log n}$, a real power of a nonnegative base, since $s$ may be negative.
-- source:
--   Mossel, Neeman and Sly, A Proof of the Block Model Threshold Conjecture, arXiv:1311.4115v4, p. 4, Definitions 2.4, 2.5; p. 5, Definition 2.6, Assumption 2.7, preamble of Theorem 2.8; p. 17, Definition 4.1; p. 19, Definition 4.6; p. 21, Lemma 5.1 (simple cycle)

import Mathlib
import Definitions.Def_SBMThreshold_Main_Setting

namespace SBMThreshold.Main

/-! Mossel, Neeman and Sly, arXiv:1311.4115v4: paths in the complete graph (Definition 2.4, p. 4),
path weights and the path sums `N^{(k)}_{u,v}`, `Y_{u,v}` (Definition 2.5, p. 4; Theorem 2.8, p. 5),
ℓ-tangles (Definition 2.6, p. 5; Definition 4.6, p. 19), the edge types of a path (Definition 4.1,
p. 17), and the standing assumptions (Assumption 2.7, p. 5; the preamble of Theorem 2.8, p. 5).

A path of length `k` is `γ : Fin (k+1) → Fin n`, the sequence `γ 0, …, γ k`; its `i`-th step,
`i : Fin k`, goes from `γ i.castSucc` to `γ i.succ`. -/

open Finset Filter Topology
open scoped Classical

/-- A path (Definition 2.4): consecutive vertices differ. -/
def IsPath {n k : ℕ} (γ : Fin (k + 1) → Fin n) : Prop :=
  ∀ i : Fin k, γ i.castSucc ≠ γ i.succ

/-- A non-backtracking path (Definition 2.4): a path with `γ i ≠ γ (i+2)` for `0 ≤ i ≤ k-2`. -/
def IsNonBacktracking {n k : ℕ} (γ : Fin (k + 1) → Fin n) : Prop :=
  IsPath γ ∧ ∀ (i : ℕ) (h : i + 2 ≤ k), γ ⟨i, by omega⟩ ≠ γ ⟨i + 2, by omega⟩

/-- A self-avoiding path (Definition 2.4): all vertices `γ 0, …, γ k` are distinct. -/
def IsSelfAvoiding {n k : ℕ} (γ : Fin (k + 1) → Fin n) : Prop :=
  Function.Injective γ

/-- A simple cycle of length `z ≥ 3` (Lemma 5.1, p. 21), as the closed sequence `ζ 0, …, ζ z` with
`ζ z = ζ 0` and `ζ 0, …, ζ (z-1)` distinct. -/
def IsSimpleCycle {n z : ℕ} (ζ : Fin (z + 1) → Fin n) : Prop :=
  3 ≤ z ∧ ζ 0 = ζ (Fin.last z) ∧ Function.Injective (fun i : Fin z => ζ i.castSucc)

/-- The undirected edge `{γ i, γ (i+1)}` crossed by the `i`-th step. -/
def stepEdge {n k : ℕ} (γ : Fin (k + 1) → Fin n) (i : Fin k) : Sym2 (Fin n) :=
  s(γ i.castSucc, γ i.succ)

/-- `E(γ)`, the set of edges `{u_{i-1}, u_i}` of the path (Definition 2.4). -/
def pathEdges {n k : ℕ} (γ : Fin (k + 1) → Fin n) : Finset (Sym2 (Fin n)) :=
  univ.image (stepEdge γ)

/-- `V(γ) = {u_0, …, u_k}` (Definition 2.4). -/
def pathVertices {n k : ℕ} (γ : Fin (k + 1) → Fin n) : Finset (Fin n) :=
  univ.image γ

/-- The multiplicity `m_e(γ)`: the number of times `γ` crosses the edge `e` (Definition 4.6). -/
def edgeMult {n k : ℕ} (γ : Fin (k + 1) → Fin n) (e : Sym2 (Fin n)) : ℕ :=
  (univ.filter (fun i : Fin k => stepEdge γ i = e)).card

/-! ### Edge types (Definition 4.1, p. 17) -/

/-- The `i`-th step is *new*: its endpoint `γ (i+1)` differs from all of `γ 0, …, γ i`. -/
def IsNewStep {n k : ℕ} (γ : Fin (k + 1) → Fin n) (i : Fin k) : Prop :=
  ∀ j : Fin (k + 1), j ≤ i.castSucc → γ j ≠ γ i.succ

/-- The `i`-th step is *old*: it is not new, and its undirected edge was crossed by an earlier
step. -/
def IsOldStep {n k : ℕ} (γ : Fin (k + 1) → Fin n) (i : Fin k) : Prop :=
  ¬ IsNewStep γ i ∧ ∃ j : Fin k, j < i ∧ stepEdge γ j = stepEdge γ i

/-- The `i`-th step is *returning*: neither new nor old (its endpoint was visited before, but its
edge was not crossed before). -/
def IsReturningStep {n k : ℕ} (γ : Fin (k + 1) → Fin n) (i : Fin k) : Prop :=
  ¬ IsNewStep γ i ∧ ¬ IsOldStep γ i

/-- `k_n(γ)`, the number of new steps. -/
noncomputable def kNew {n k : ℕ} (γ : Fin (k + 1) → Fin n) : ℕ := (univ.filter (IsNewStep γ)).card

/-- `k_o(γ)`, the number of old steps. -/
noncomputable def kOld {n k : ℕ} (γ : Fin (k + 1) → Fin n) : ℕ := (univ.filter (IsOldStep γ)).card

/-- `k_r(γ)`, the number of returning steps. -/
noncomputable def kRet {n k : ℕ} (γ : Fin (k + 1) → Fin n) : ℕ := (univ.filter (IsReturningStep γ)).card

/-! ### Path weights (Definition 2.5, p. 4; Theorem 2.8, p. 5) -/

/-- `W_e = 1_{e ∈ E(G)} - d/n` with `d = (a+b)/2`. -/
noncomputable def edgeW (n : ℕ) (a b : ℝ) (G : SimpleGraph (Fin n)) (e : Sym2 (Fin n)) : ℝ :=
  (if e ∈ G.edgeSet then 1 else 0) - dPar a b / n

/-- `X_γ = ∏_{i=1}^k W_{(u_{i-1}, u_i)}`. -/
noncomputable def pathX (n : ℕ) (a b : ℝ) {k : ℕ} (γ : Fin (k + 1) → Fin n)
    (G : SimpleGraph (Fin n)) : ℝ :=
  ∏ i : Fin k, edgeW n a b G (stepEdge γ i)

/-- `N^{(k)}_{u,v} = Σ_{γ ∈ Γ^NB_{k,u,v}} X_γ`, over the non-backtracking paths of length `k`
from `u` to `v`. -/
noncomputable def pathN (n : ℕ) (a b : ℝ) (k : ℕ) (u v : Fin n) (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ γ ∈ univ.filter (fun γ : Fin (k + 1) → Fin n =>
      IsNonBacktracking γ ∧ γ 0 = u ∧ γ (Fin.last k) = v), pathX n a b γ G

/-- `Y_{u,v} = Σ_{γ ∈ Γ^SAW_{u,v}} X_γ`, over the self-avoiding paths of length `k` from `u` to
`v`. -/
noncomputable def pathY (n : ℕ) (a b : ℝ) (k : ℕ) (u v : Fin n) (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ γ ∈ univ.filter (fun γ : Fin (k + 1) → Fin n =>
      IsSelfAvoiding γ ∧ γ 0 = u ∧ γ (Fin.last k) = v), pathX n a b γ G

/-! ### Tangles (Definition 2.6, p. 5; Definition 4.6, p. 19) -/

/-- `H ⊆ G` is an ℓ-tangle: a connected graph of diameter at most `2ℓ` (in its own graph metric)
that contains two cycles, i.e. has at least `|V(H)| + 1` edges. -/
def IsTangle {n : ℕ} (ℓ : ℕ) {G : SimpleGraph (Fin n)} (H : G.Subgraph) : Prop :=
  H.Connected ∧ (∀ x y : H.verts, H.coe.dist x y ≤ 2 * ℓ) ∧
    H.verts.ncard + 1 ≤ H.edgeSet.ncard

/-- `G` is ℓ-tangle-free: no subgraph of `G` is an ℓ-tangle. -/
def TangleFree {n : ℕ} (ℓ : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ H : G.Subgraph, ¬ IsTangle ℓ H

/-- The graph `(V(γ), E(γ) ∖ F)` of a path with the edges `F` deleted (isolated vertices of
`Fin n` outside `V(γ)` do not affect tangle-freeness). -/
def pathGraphMinus {n k : ℕ} (γ : Fin (k + 1) → Fin n) (F : Finset (Sym2 (Fin n))) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (↑(pathEdges γ \ F) : Set (Sym2 (Fin n)))

/-- `t(γ)`, the number of ℓ-tangles of `γ` (Definition 4.6): the minimal number of edges,
counted with multiplicity `m_e(γ)`, whose deletion makes `γ` ℓ-tangle-free. The set is nonempty:
deleting `F = E(γ)` leaves the empty graph, which is ℓ-tangle-free. -/
noncomputable def tangleCount {n k : ℕ} (ℓ : ℕ) (γ : Fin (k + 1) → Fin n) : ℕ :=
  sInf {t : ℕ | ∃ F ⊆ pathEdges γ, TangleFree ℓ (pathGraphMinus γ F) ∧
    ∑ e ∈ F, edgeMult γ e = t}

/-! ### Standing assumptions -/

/-- Assumption 2.7 (p. 5), for sequences `a_n, b_n > 0` and `ℓ_n`: `s, d = n^{o(1/log log n)}`,
i.e. there is `c_n → 0` with `d_n, |s_n| ≤ n^{c_n / log log n}` for all large `n`; and
`log log n ≪ ℓ_n ≪ √(log n)`. -/
structure Assumption27 (a b : ℕ → ℝ) (ℓ : ℕ → ℕ) : Prop where
  a_pos : ∀ n, 0 < a n
  b_pos : ∀ n, 0 < b n
  growth : ∃ c : ℕ → ℝ, Tendsto c atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
    dPar (a n) (b n) ≤ (n : ℝ) ^ (c n / Real.log (Real.log n)) ∧
    |sPar (a n) (b n)| ≤ (n : ℝ) ^ (c n / Real.log (Real.log n))
  ell_lower : Tendsto (fun n : ℕ => (ℓ n : ℝ) / Real.log (Real.log n)) atTop atTop
  ell_upper : Tendsto (fun n : ℕ => (ℓ n : ℝ) / Real.sqrt (Real.log n)) atTop (𝓝 0)

/-- The preamble of Theorem 2.8 (p. 5): `s_n²/d_n ≥ λ > 1` for all `n`, and `α > 0` with
`n² d^{α log n} ≤ s^{2α log n}` for every `n` (written `(s²)^{α log n}`). -/
structure Theorem28Params (a b : ℕ → ℝ) (lam α : ℝ) : Prop where
  one_lt_lam : 1 < lam
  ratio : ∀ n, lam ≤ sPar (a n) (b n) ^ 2 / dPar (a n) (b n)
  alpha_pos : 0 < α
  alpha_choice : ∀ n : ℕ, (n : ℝ) ^ 2 * dPar (a n) (b n) ^ (α * Real.log n) ≤
    (sPar (a n) (b n) ^ 2) ^ (α * Real.log n)

/-- `k = ⌈α log n⌉` (Theorem 2.8). -/
noncomputable def pathLen (α : ℝ) (n : ℕ) : ℕ := ⌈α * Real.log n⌉₊

end SBMThreshold.Main


