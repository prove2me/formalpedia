-- Prove2me | Definitions.Def_RoundRobinEq_CancelableEF1_Setting
-- name    : RoundRobinEq_CancelableEF1_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:17:34.523346+00:00
-- url     : https://prove2.me/theorems/a430de95-61fe-4437-95ba-411bcb22ca32
-- title:
--   pp. 4–7 — valuations, cancelable and subadditive functions, rankings, Mechanism 1 (Round-Robin), α-EF1, α-approximate PNE
-- statement:
--   We fix the model of §2 of Amanatidis, Birmpas, Lazos, Leonardi and Reiffenhäuser. There are $n \ge 1$ agents $N = [n]$ and a finite set $M$ of goods, $m = |M|$.
--
--   1. A **valuation** of an agent is a function $v : 2^M \to \mathbb{R}$ that is normalized, $v(\emptyset) = 0$, and non-decreasing, $v(S) \le v(T)$ whenever $S \subseteq T$. The **marginal value** of $T$ with respect to $S$ is $v(T \mid S) = v(T \cup S) - v(S)$, and $v(g \mid S) = v(\{g\} \mid S)$.
--   2. $v$ is **cancelable** if for all $S, T \subseteq M$ and $g \in M \setminus (S \cup T)$,
--   $$v(S \cup \{g\}) > v(T \cup \{g\}) \implies v(S) > v(T),$$
--   and **subadditive** if $v(S \cup T) \le v(S) + v(T)$ for all $S, T \subseteq M$.
--   3. A **preference ranking** $\succ_i$ is a total order on $M$; $\mathrm{top}(\succ, T)$ is the $\succ$-largest good of $T$. A **profile** is a vector $\succ = (\succ_1, \dots, \succ_n)$ of rankings; $(\succ'_i, \succ_{-i})$ replaces the ranking of agent $i$ by $\succ'_i$.
--   4. **Round-Robin** (Mechanism 1) on a profile $\succ$ runs $k = \lceil m/n \rceil$ rounds; in each round agents $1, \dots, n$ in turn receive $\mathrm{top}(\succ_i, S)$ from the set $S$ of goods still available. It returns the bundles $(A_1, \dots, A_n)$.
--   5. (Definition 2.3) An allocation $(A_1, \dots, A_n)$ is **$\alpha$-EF1** with respect to valuations $(v_i)_{i \in N}$ if for every pair $i, j \in N$ with $A_j \neq \emptyset$ there is a good $g \in A_j$ with
--   $$v_i(A_i) \ge \alpha \cdot v_i(A_j \setminus \{g\}).$$
--   6. (Definition 2.4) A profile $\succ$ is an **$\alpha$-approximate pure Nash equilibrium** (PNE) of Round-Robin if for every agent $i$ and every total order $\succ'_i$ of $M$,
--   $$\alpha \cdot v_i\big(\mathrm{RR}(\succ'_i, \succ_{-i})_i\big) \le v_i\big(\mathrm{RR}(\succ)_i\big).$$
--   7. A **strict truthful ranking** for an agent with valuation $v$ is a total order $\succ^*$ of $M$ that is a strict version of the true preference ranking $\succcurlyeq^*_{|\emptyset}$: whenever $v(\{g\}) > v(\{g'\})$, the good $g$ precedes $g'$; goods of equal singleton value may appear in any order.
--
--   These objects are the vocabulary of Theorem 4.5 and its proof: the mechanism only sees rankings, while envy-freeness is measured with the true valuations.
--
--   **Formalization Note** Agents are `Fin n` (agent $i$ of the paper is `i - 1`) and goods a `Fintype` `M`. Valuations are real-valued; non-negativity follows from normalization and monotonicity. A ranking is a duplicate-free list containing every good, most preferred first, and $\mathrm{top}$ returns an `Option`. Round-Robin is run step by step, 0-based: step $t$ belongs to agent $t \bmod n$ and round $t / n$, `allocBefore σ t` is the set of goods allocated in steps $0, \dots, t-1$, `pick σ t` is the good allocated at step $t$, and the bundle of agent $i$ collects the goods picked at $i$'s steps among the first $m$; the paper's step $(r-1)n + i$ is step `(r-1)*n + (i-1)`. Deviations in the PNE definition range over rankings only, exactly as in Definition 2.4.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, pp. 4–7, §2 (valuation classes p. 5, Definitions 2.3–2.4 p. 6, Mechanism 1 p. 7), strict truthful ranking pp. 5, 7, 18

import Mathlib
import Definitions.Def_RoundRobinEq_CancelableBluff_Setting

namespace RoundRobinEq.CancelableEF1

/-! Amanatidis et al., *Round-Robin Beyond Additive Agents*, arXiv:2301.13652v1, §2, pp. 4–7.
Agents are `Fin n` (the paper's agent `i` is `i − 1`), goods a finite type `M`, a valuation of an
agent is a function `Finset M → ℝ`. Steps of Round-Robin are 0-based: step `t` is taken by agent
`t % n`, in (0-based) round `t / n`. -/

variable {M : Type*} [DecidableEq M]

/-- Subadditive (p. 5): `v(S ∪ T) ≤ v(S) + v(T)` for all `S, T ⊆ M`. -/
def IsSubadditive (v : Finset M → ℝ) : Prop :=
  ∀ S T : Finset M, v (S ∪ T) ≤ v S + v T

variable [Fintype M] {n : ℕ} [NeZero n]

/-- The goods allocated in steps `0, …, t − 1` of Round-Robin(σ) (Mechanism 1, p. 7). -/
def allocBefore (σ : Fin n → List M) : ℕ → Finset M
  | 0 => ∅
  | t + 1 =>
    match RoundRobinEq.CancelableBluff.top (σ (RoundRobinEq.CancelableBluff.agentAt n t)) (Finset.univ \ allocBefore σ t) with
    | some g => insert g (allocBefore σ t)
    | none => allocBefore σ t

/-- The good allocated at (0-based) step `t` of Round-Robin(σ): the top available good of the
active agent's reported ranking (`none` once no good is left). -/
def pick (σ : Fin n → List M) (t : ℕ) : Option M :=
  RoundRobinEq.CancelableBluff.top (σ (RoundRobinEq.CancelableBluff.agentAt n t)) (Finset.univ \ allocBefore σ t)

/-- The bundle `A_i` returned by Round-Robin(σ) (Mechanism 1, p. 7): the goods picked at agent
`i`'s steps among the first `m = |M|` steps. -/
def roundRobin (σ : Fin n → List M) (i : Fin n) : Finset M :=
  ((Finset.range (Fintype.card M)).filter (fun t => RoundRobinEq.CancelableBluff.agentAt n t = i)).biUnion
    (fun t => (pick σ t).toFinset)

/-- Definition 2.3 (p. 6): the allocation `A` is `α`-EF1 with respect to the valuations `v` if for
every pair of agents `i, j` with `A_j ≠ ∅` there is a good `g ∈ A_j` with
`v_i(A_i) ≥ α · v_i(A_j \ {g})`. -/
def IsApproxEF1 (α : ℝ) (v : Fin n → Finset M → ℝ) (A : Fin n → Finset M) : Prop :=
  ∀ i j : Fin n, (A j).Nonempty → ∃ g ∈ A j, α * v i ((A j).erase g) ≤ v i (A i)

/-- Definition 2.4 (p. 6): the profile of rankings `σ` is an `α`-approximate pure Nash equilibrium
of Round-Robin: for every agent `i` and every ranking `τ` (a permutation of `M`),
`α · v_i(RR(τ, σ_{-i})_i) ≤ v_i(RR(σ)_i)`. -/
def IsApproxPNE (α : ℝ) (v : Fin n → Finset M → ℝ) (σ : Fin n → List M) : Prop :=
  (∀ i, RoundRobinEq.CancelableBluff.IsRanking (σ i)) ∧
    ∀ (i : Fin n) (τ : List M), RoundRobinEq.CancelableBluff.IsRanking τ →
      α * v i (roundRobin (Function.update σ i τ) i) ≤ v i (roundRobin σ i)

/-- `τ` is a strict version of the true preference ranking `≽*_{i|∅}` of an agent with valuation
`v` (pp. 5, 7, 18): a ranking that puts `g` before `g'` whenever `v({g}) > v({g'})`; goods of equal
singleton value may appear in either order. -/
def IsStrictTruthfulFor (v : Finset M → ℝ) (τ : List M) : Prop :=
  RoundRobinEq.CancelableBluff.IsRanking τ ∧ ∀ g g' : M, v {g'} < v {g} → τ.idxOf g < τ.idxOf g'

end RoundRobinEq.CancelableEF1


