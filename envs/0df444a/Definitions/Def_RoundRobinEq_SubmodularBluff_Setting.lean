-- Prove2me | Definitions.Def_RoundRobinEq_SubmodularBluff_Setting
-- name    : RoundRobinEq_SubmodularBluff_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:17:43.098704+00:00
-- url     : https://prove2.me/theorems/a1ffb64d-8194-440f-b791-a03ba9221403
-- title:
--   pp. 4–7 — valuations, submodularity, rankings, Mechanism 1 (Round-Robin), α-EF1, α-approximate PNE
-- statement:
--   This file fixes the model of §2 of the paper. There are $n\ge 1$ agents $N=[n]$ and a finite set $M$ of goods with $m=|M|$.
--
--   1. **Valuations.** Agent $i$ has a valuation $v_i:2^M\to\mathbb R$ that is *normalized*, $v_i(\emptyset)=0$, and *non-decreasing*, $v_i(S)\le v_i(T)$ for $S\subseteq T$; together these give $v_i\ge 0$. The *marginal value* of $T$ with respect to $S$ is
--   $$v_i(T\mid S)=v_i(T\cup S)-v_i(S),$$
--   and $v_i(g\mid S)$ abbreviates $v_i(\{g\}\mid S)$.
--   2. **Valuation classes** (p. 5). $v$ is *submodular* if $v(g\mid S)\ge v(g\mid T)$ for all $S\subseteq T\subseteq M$ and $g\notin T$; it is *additive* if $v(S\cup T)=v(S)+v(T)$ whenever $S\cap T=\emptyset$.
--   3. **Preference rankings.** A reported ranking $\succ_i$ is a total order on $M$, written as the list of all goods, most preferred first, each exactly once. For a set $T$, $\mathrm{top}(\succ,T)$ is the first good of the list lying in $T$.
--   4. **Mechanism 1 (Round-Robin).** Given a reported profile $\succ=(\succ_1,\dots,\succ_n)$, the agents act in rounds in the order $1,2,\dots,n$; at each step the acting agent receives $\mathrm{top}(\succ_i,S)$, where $S$ is the set of goods still available. Round-Robin$(\succ)$ returns the bundles $(A_1,\dots,A_n)$.
--   5. **Definition 2.3 ($\alpha$-EF1).** An allocation $(A_1,\dots,A_n)$ is $\alpha$-EF1 if for every pair $i,j$ with $A_j\neq\emptyset$ there is $g\in A_j$ with
--   $$v_i(A_i)\ge \alpha\cdot v_i(A_j\setminus\{g\}).$$
--   6. **Definition 2.4 ($\alpha$-approximate PNE).** A profile $\succ$ of rankings is an $\alpha$-approximate pure Nash equilibrium of Mechanism 1 if for every agent $i$ and every ranking $\succ_i'$,
--   $$\alpha\cdot v_i\big(\mathcal M(\succ_i',\succ_{-i})\big)\le v_i\big(\mathcal M(\succ)\big),$$
--   where $v_i(\mathcal M(\cdot))$ is agent $i$'s true value for her bundle.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Agents are `Fin n` and steps are numbered from $0$: step $t$ is taken by agent $t \bmod n$ (0-based) in round $\lfloor t/n\rfloor$, so the paper's step $(r-1)n+i$ (1-based round $r$ and agent $i$) is step $(r-1)n+(i-1)$. `allocBefore σ t` is the set of goods allocated in steps $0,\dots,t-1$, `pick σ t` the good allocated at step $t$, and `roundRobin σ i` the bundle of agent $i$ over the first $m$ steps. Valuations take values in $\mathbb R$ rather than $\mathbb R_{\ge0}$; non-negativity follows from normalization and monotonicity. Deviations in the PNE definition range over rankings only, as in Definition 2.4 ("for every total order, i.e., permutation").
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, pp. 4–7, §2 (p. 5 valuation classes; p. 6 Definitions 2.3, 2.4; p. 7 Mechanism 1)

import Mathlib
import Definitions.Def_RoundRobinEq_CancelableBluff_Setting

namespace RoundRobinEq.SubmodularBluff

/-! ### Valuations (p. 5) -/

/-- Submodularity in the paper's RoundRobinEq.CancelableBluff.marginal form (p. 5):
`v(g | S) ≥ v(g | T)` for all `S ⊆ T ⊆ M` and `g ∉ T`. -/
def IsSubmodular {M : Type*} [DecidableEq M] (v : Finset M → ℝ) : Prop :=
  ∀ (S T : Finset M) (g : M), S ⊆ T → g ∉ T → RoundRobinEq.CancelableBluff.marginal v {g} T ≤ RoundRobinEq.CancelableBluff.marginal v {g} S

/-- Additivity (p. 5): `v(S ∪ T) = v(S) + v(T)` whenever `S ∩ T = ∅`. -/
def IsAdditive {M : Type*} [DecidableEq M] (v : Finset M → ℝ) : Prop :=
  ∀ S T : Finset M, Disjoint S T → v (S ∪ T) = v S + v T

/-! ### Preference rankings (p. 5) -/

/-! ### Mechanism 1, Round-Robin (p. 7)

Steps are numbered `0, 1, 2, …`; step `t` is taken by agent `t % n` (0-based), in round `t / n`.
The paper's step `(r-1)n + i` (1-based round `r`, 1-based agent `i`) is step `(r-1)*n + (i-1)`. -/

/-! ### Fairness and equilibria (p. 6) -/

end RoundRobinEq.SubmodularBluff


