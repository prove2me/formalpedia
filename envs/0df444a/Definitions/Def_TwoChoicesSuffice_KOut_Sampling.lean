-- Prove2me | Definitions.Def_TwoChoicesSuffice_KOut_Sampling
-- name    : TwoChoicesSuffice_KOut_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:37.76119+00:00
-- url     : https://prove2.me/theorems/64d34a6a-7ada-4e3d-9933-3fee2120d11e
-- title:
--   Random $k$-out sampling with replacement and intercomponent edges
-- statement:
--   Let $G=(V,E_G)$ be a finite simple undirected graph with $n=|V|$ vertices, and let $k\ge0$ be an integer. In **$k$-out sampling with replacement** every vertex $v$ independently makes $k$ ordered choices $s_1(v),\dots,s_k(v)$, each a uniformly random neighbour of $v$ (equivalently, a uniformly random incident edge $v\,s_i(v)$, since $G$ is simple); repetitions are allowed. An ordered outcome $\sigma=(s_i(v))_{v\in V,\,1\le i\le k}$ therefore has probability
--   $$
--   \Pr[\sigma]=\prod_{\substack{v\in V\\\deg_G(v)>0}}\deg_G(v)^{-k}.
--   $$
--   An isolated vertex has no incident edge; it makes the single dummy choice $s_i(v)=v$, which never produces an edge and contributes a probability factor of $1$. Given an outcome and a set of admissible positions, the sampled spanning subgraph contains the edge $uw\in E_G$ exactly when $u$ chose $w$ or $w$ chose $u$ at an admissible position. In particular $H^r_G(\sigma)$ is the union of the first $r$ choices of all vertices, and $H^k_G=H^k_G(\sigma)$ is the random $k$-out subgraph; the coupling gives $H^1_G(\sigma)\subseteq H^2_G(\sigma)\subseteq\dots\subseteq H^k_G(\sigma)$.
--
--   For a spanning subgraph $H\subseteq G$ the **intercomponent** (crossing) edges are
--   $$
--   X_G(H)=\{uw\in E_G:\ u\text{ and }w\text{ lie in different connected components of }H\},\qquad x_G(H)=|X_G(H)|,
--   $$
--   each original undirected edge counted once. Expectations $\mathbb E$ of functions of the outcome are averages over the finite set of ordered outcomes.
--
--   These objects are the sampling model, the coupling and the quantity bounded throughout the mission.
--
--   **Formalization Note** The vertex set is an arbitrary finite type `V` (a relabelling of $\{1,\dots,n\}$). Outcomes are functions `σ : V → Fin k → V` in the product finset `outcomes G k`; `kOutExpect` divides by its cardinality, which is positive (`outcomes_nonempty`, proved in the file), also for $n=0$, $k=0$ or isolated vertices. `prefixGraph G σ r` is $H^r_G(\sigma)$ (positions $i<r$, zero-based), `choiceGraph` the general version with an arbitrary set of admissible positions, `crossingCount G H` is $x_G(H)$.
-- source:
--   Yanyu Chen, Yu Chen, STOC 2027 submission #372 (October 2026), §3 (Preliminary and the coupling σ_v), printed p. 6, PDF p. 7

import Mathlib

open scoped Classical

namespace TwoChoicesSuffice.KOut

variable {V : Type*} [Fintype V]

/-- The set of admissible values of one choice made by the vertex `v`: its `G`-neighbours
(equivalently, its incident edges, since `G` is simple). An isolated vertex has no incident
edge; it gets the single dummy value `v` itself, which never produces an edge because `G`
is loopless. Source: §3, PDF p. 7 (printed p. 6). -/
noncomputable def choiceSet (G : SimpleGraph V) (v : V) : Finset V :=
  if (Finset.univ.filter (G.Adj v)).Nonempty then Finset.univ.filter (G.Adj v) else {v}

/-- The ordered outcomes of `k`-out sampling with replacement: every vertex `v` makes `k`
ordered choices `σ v 0, …, σ v (k-1)`, each in `choiceSet G v`, repetitions allowed.
The uniform law on this finite set is the product of independent uniform choices, i.e.
every outcome has probability `∏_v deg_G(v)^{-k}` (isolated vertices contribute a factor
one). Source: §3, PDF p. 7 (printed p. 6). -/
noncomputable def outcomes (G : SimpleGraph V) (k : ℕ) : Finset (V → Fin k → V) :=
  Fintype.piFinset fun v => Fintype.piFinset fun _ : Fin k => choiceSet G v

/-- Expectation of a real-valued function of the ordered `k`-choice outcome under the
`k`-out law with replacement: the average over the (nonempty, see `outcomes_nonempty`)
finite outcome set. -/
noncomputable def kOutExpect (G : SimpleGraph V) (k : ℕ) (f : (V → Fin k → V) → ℝ) : ℝ :=
  (∑ σ ∈ outcomes G k, f σ) / ((outcomes G k).card : ℝ)

/-- The spanning subgraph of `G` formed by the choices `σ v i` at those positions `(v, i)`
satisfying `P v i`; an edge `uw` of `G` is present iff `u` chose `w` or `w` chose `u` at an
admissible position. -/
def choiceGraph (G : SimpleGraph V) {k : ℕ} (σ : V → Fin k → V) (P : V → Fin k → Prop) :
    SimpleGraph V where
  Adj u w := G.Adj u w ∧ ((∃ i, P u i ∧ σ u i = w) ∨ (∃ i, P w i ∧ σ w i = u))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

/-- `H^r_G(σ)`: the union of the first `r` choices of every vertex (positions `i < r`).
For `σ ∈ outcomes G k`, `prefixGraph G σ k` is the random `k`-out subgraph `H^k_G`, and
`prefixGraph G σ r ≤ prefixGraph G σ k` for `r ≤ k` is the paper's coupling. -/
def prefixGraph (G : SimpleGraph V) {k : ℕ} (σ : V → Fin k → V) (r : ℕ) : SimpleGraph V :=
  choiceGraph G σ (fun _ i => i.val < r)

/-- `X_G(H)`: the original undirected edges of `G` whose endpoints lie in different
connected components of `H` (each undirected edge once). Source: §3, PDF p. 7. -/
noncomputable def crossingEdges (G H : SimpleGraph V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∀ u w : V, e = s(u, w) → ¬ H.Reachable u w

/-- `x_G(H) = |X_G(H)|`, the number of intercomponent (crossing) edges. -/
noncomputable def crossingCount (G H : SimpleGraph V) : ℕ :=
  (crossingEdges G H).card

lemma choiceSet_nonempty (G : SimpleGraph V) (v : V) : (choiceSet G v).Nonempty := by
  unfold choiceSet
  split_ifs with h
  · exact h
  · exact Finset.singleton_nonempty v

/-- The outcome set is never empty, so `kOutExpect` is a genuine average (no division by
zero), also when `V` is empty, `k = 0`, or `G` has isolated vertices. -/
lemma outcomes_nonempty (G : SimpleGraph V) (k : ℕ) : (outcomes G k).Nonempty :=
  Fintype.piFinset_nonempty.2 fun v =>
    Fintype.piFinset_nonempty.2 fun _ => choiceSet_nonempty G v

end TwoChoicesSuffice.KOut


