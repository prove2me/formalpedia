-- Prove2me | Definitions.Def_StrictCompatLB_MeanField_GraphConditions
-- name    : StrictCompatLB_MeanField_GraphConditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:36.764696+00:00
-- url     : https://prove2.me/theorems/c13b6c1c-2d68-44d2-a144-ddcd5ff6de8d
-- title:
--   Defs. 3.1, 3.3 — compatibility graph sequences, proportional sparsity, the subcriticality condition and connectivity
-- statement:
--   Consider a sequence of bipartite **compatibility graphs** $G_N=(V_N,W_N,E_N)$, $N\ge 1$, between a set $V_N$ of $N$ servers and a set $W_N$ of $M(N)$ dispatchers, with $E_N\subseteq V_N\times W_N$. For a dispatcher $w\in W_N$ write $\mathcal N_w=\{v\in V_N:(v,w)\in E_N\}$ for its neighbourhood (the servers that can process task type $w$), and for a server $v$ write $\mathcal N_v=\{w\in W_N:(v,w)\in E_N\}$.
--
--   1. **Proportional sparsity** (Definition 3.1). The sequence is proportionally sparse if for every $\varepsilon>0$
--   $$\sup_{U\subseteq V_N}\Big|\Big\{w\in W_N:\Big|\frac{|\mathcal N_w\cap U|}{|\mathcal N_w|}-\frac{|U|}{N}\Big|\ge\varepsilon\Big\}\Big|\Big/M(N)\;\longrightarrow\;0\qquad(N\to\infty).$$
--   Equivalently: for every $\varepsilon>0$ and $\delta>0$ there is $N_0$ such that for every $N\ge N_0$ and every $U\subseteq V_N$, at most $\delta M(N)$ dispatchers $w$ satisfy $\big||\mathcal N_w\cap U|/|\mathcal N_w|-|U|/N\big|\ge\varepsilon$.
--
--   2. **Subcriticality** (Definition 3.3), for a sample size $d$. Put $k_w=\min(d,|\mathcal N_w|)$. The sequence satisfies the subcriticality condition if there are weights $\gamma^U_w(v)\ge 0$, indexed by $N$, $w\in W_N$ and $U\subseteq V_N$, each $\gamma^U_w$ a probability distribution on $U$ when $U\neq\emptyset$, such that
--   $$\limsup_{N\to\infty}\max_{v\in V_N}\frac{N}{M(N)}\sum_{w\in W_N}\binom{|\mathcal N_w|}{k_w}^{-1}\sum_{\substack{U\subseteq\mathcal N_w\\ |U|=k_w}}\gamma^U_w(v)\;\le\;1 .$$
--   Here "$\limsup\le 1$" means: for every $\varepsilon>0$, for all sufficiently large $N$, every server's value is at most $1+\varepsilon$.
--
--   3. **Connectivity.** The sequence consists of connected graphs if for every $N\ge 1$ the bipartite graph on the vertex set $V_N\sqcup W_N$ with edge set $E_N$ is connected (§2: "we assume $G_N$ to be connected"; Definition 3.1: "a sequence of connected graphs").
--
--   Proportional sparsity is the expansion property under which the occupancy process on $G_N$ has the same mean-field limit as on the complete bipartite graph; subcriticality bounds the load any server can receive and yields stability and tightness of the steady states.
--
--   **Formalization Note** $V_N$ is `Fin N`, $W_N$ is `Fin (M N)`, $E_N$ is a `Finset (Fin N × Fin (M N))`. Proportional sparsity is the limit condition (3.1) alone; connectivity is the separate predicate `IsConnectedSeq` (via `SimpleGraph.Connected` on `Fin N ⊕ Fin (M N)`), so that both appear as hypotheses wherever the paper assumes them. A dispatcher with $|\mathcal N_w|=0$ contributes the ratio $0/0$, which Lean evaluates to $0$; connected graphs have no such dispatcher for $N\ge1$. In (3.2) the paper asks for a probability distribution on every $U\subseteq V_N$, including $U=\emptyset$, which has none; here only nonempty $U$ are constrained (the sum only uses $|U|=k_w$, which is $0$ only when $\mathcal N_w=\emptyset$). The paper normalises by $\binom{|\mathcal N_w|}{d}^{-1}$, which is $1/0$ when $|\mathcal N_w|<d$; here the normaliser is $\binom{|\mathcal N_w|}{k_w}^{-1}$, the number of summed subsets, which agrees with the paper when $|\mathcal N_w|\ge d$ and matches the sampling of JSQ(d) without replacement used in (H.5).
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 8, §2 (model, connectivity); p. 10, Definition 3.1, (3.1); p. 11, Definition 3.3, (3.2)

import Mathlib

open Finset Filter

namespace StrictCompatLB.MeanField

/-! Sequences of bipartite compatibility graphs `G_N = (V_N, W_N, E_N)` with `V_N = Fin N`
(servers) and `W_N = Fin (M N)` (dispatchers), and the graph conditions of
Rutten & Mukherjee, arXiv:2008.07562v2: proportional sparsity (Def. 3.1, (3.1), p. 10)
and the subcriticality condition (Def. 3.3, (3.2), p. 11), and connectivity (§2, p. 8). -/

/-- The neighbourhood `𝒩_w ⊆ V_N` of dispatcher `w ∈ W_N` in `G_N` (§2, p. 8). -/
def nbrW (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ) (w : Fin (M N)) :
    Finset (Fin N) :=
  Finset.univ.filter (fun v => (v, w) ∈ G N)

/-- The neighbourhood `𝒩_v ⊆ W_N` of server `v ∈ V_N` in `G_N` (App. A, p. 31). -/
def nbrV (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ) (v : Fin N) :
    Finset (Fin (M N)) :=
  Finset.univ.filter (fun w => (v, w) ∈ G N)

/-- Proportional sparsity, condition (3.1) of Definition 3.1: for every `ε > 0`,
`sup_{U ⊆ V_N} |{w ∈ W_N : | |𝒩_w ∩ U|/|𝒩_w| − |U|/N | ≥ ε}| / M(N) → 0`, written as
"for every `δ > 0`, eventually in `N`, every `U ⊆ V_N` has at most `δ M(N)` such `w`".
Connectivity of `G_N` is not part of this definition. -/
def IsPropSparse (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ U : Finset (Fin N),
    (((Finset.univ.filter (fun w : Fin (M N) =>
        ε ≤ |((nbrW M G N w ∩ U).card : ℝ) / ((nbrW M G N w).card : ℝ)
              - (U.card : ℝ) / (N : ℝ)|)).card : ℕ) : ℝ) ≤ δ * (M N : ℝ)

/-- The subcriticality condition (3.2) of Definition 3.3, with sample size `d`: there are
weights `γ N w U v = γ^U_w(v)`, a probability distribution on each nonempty `U ⊆ V_N`
(nonnegative, zero off `U`, summing to one over `U`), such that
`limsup_N max_v (N/M(N)) Σ_w C(|𝒩_w|, k_w)⁻¹ Σ_{U ⊆ 𝒩_w, |U| = k_w} γ^U_w(v) ≤ 1`
with `k_w = min(d, |𝒩_w|)`; the `limsup ≤ 1` is written as "for every `ε > 0`, eventually
every server's load is at most `1 + ε`". -/
def IsSubcritical (d : ℕ) (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) : Prop :=
  ∃ γ : (N : ℕ) → Fin (M N) → Finset (Fin N) → Fin N → ℝ,
    (∀ N w U v, 0 ≤ γ N w U v) ∧
    (∀ N w U v, v ∉ U → γ N w U v = 0) ∧
    (∀ N w U, U.Nonempty → ∑ v ∈ U, γ N w U v = 1) ∧
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ v : Fin N,
      (N : ℝ) / (M N : ℝ) *
        ∑ w : Fin (M N),
          ((Nat.choose (nbrW M G N w).card (min d (nbrW M G N w).card) : ℕ) : ℝ)⁻¹ *
            ∑ U ∈ (nbrW M G N w).powersetCard (min d (nbrW M G N w).card), γ N w U v
        ≤ 1 + ε

/-- The compatibility graph `G_N` as a simple graph on the disjoint union `V_N ⊕ W_N`
(servers on the left, dispatchers on the right): `v` and `w` are adjacent iff `(v, w) ∈ E_N`. -/
def compatGraph (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ) :
    SimpleGraph (Fin N ⊕ Fin (M N)) :=
  SimpleGraph.fromRel (fun a b => ∃ v w, a = Sum.inl v ∧ b = Sum.inr w ∧ (v, w) ∈ G N)

/-- "`{G_N}` is a sequence of connected graphs" (Def. 3.1, p. 10; §2, p. 8: "we assume `G_N` to
be connected"): for every `N ≥ 1` the bipartite graph `G_N` on `V_N ⊕ W_N` is connected. -/
def IsConnectedSeq (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) : Prop :=
  ∀ N : ℕ, 1 ≤ N → (compatGraph M G N).Connected

end StrictCompatLB.MeanField


