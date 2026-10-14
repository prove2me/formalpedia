-- Prove2me | Definitions.Def_RoundRobinEq_SubmodularEF1_Setting
-- name    : RoundRobinEq_SubmodularEF1_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:17:42.332245+00:00
-- url     : https://prove2.me/theorems/cc7dd919-16de-4a31-a4e8-05ef9afef1b7
-- title:
--   pp. 4–7, 11, 15, 20 — valuations, submodularity, rankings, Mechanism 1 (Round-Robin), α-EF1, α-approximate PNE, Algorithms 3–4
-- statement:
--   This file fixes the model of Amanatidis, Birmpas, Lazos, Leonardi and Reiffenhäuser (§2, pp. 4–7) and the auxiliary objects of §4 used in the proof of Theorem 4.4.
--
--   **Agents, goods, valuations.** There are $n\ge 1$ agents $N$ and a finite set $M$ of $m$ goods. Agent $i$ has a valuation $v_i : 2^M\to\mathbb R$. For $S,T\subseteq M$ the *marginal value* of $T$ with respect to $S$ is
--   $$v(T\mid S) = v(T\cup S) - v(S),$$
--   and $v(g\mid S)$ stands for $v(\{g\}\mid S)$. A function $v$ is *non-decreasing* if $v(S)\le v(T)$ whenever $S\subseteq T$; it is a *valuation* if moreover it is normalized, $v(\emptyset)=0$. It is *submodular* if
--   $$v(g\mid S)\ \ge\ v(g\mid T)\qquad\text{for all } S\subseteq T\subseteq M,\ g\notin T .$$
--
--   **Rankings and Round-Robin.** Each agent reports a *preference ranking*, a total order $\succ_i$ on $M$; $\mathrm{top}(\succ,T)$ is the $\succ$-largest good of $T$. A profile is $\succ=(\succ_1,\dots,\succ_n)$, and $(\succ'_i,\succ_{-i})$ replaces agent $i$'s report by $\succ'_i$. The Round-Robin mechanism (Mechanism 1) runs $m$ steps; at step $t$ (counting from $0$) agent $t \bmod n$ receives $\mathrm{top}(\succ_{t \bmod n},S)$, where $S$ is the set of goods not yet allocated. The output is the allocation $(A_1,\dots,A_n)$, $A_i$ being the goods agent $i$ received. We also record the set of goods allocated in the first $t$ steps, the good picked at step $t$, and the goods agent $i$ received in the first $t$ steps.
--
--   **Fairness and equilibria.** An allocation is *$\alpha$-EF1* (Definition 2.3) if for all agents $i,j$ with $A_j\ne\emptyset$ there is a good $g\in A_j$ with
--   $$v_i(A_i)\ \ge\ \alpha\cdot v_i(A_j\setminus\{g\});$$
--   it is $\alpha$-EF1 *from agent $i$'s perspective* if this holds for that fixed $i$ and every $j$. A profile $\succ$ is an *$\alpha$-approximate pure Nash equilibrium* (Definition 2.4) if for every agent $i$ and every total order $\succ'_i$ of $M$,
--   $$\alpha\cdot v_i\big(\text{Round-Robin}(\succ'_i,\succ_{-i})_i\big)\ \le\ v_i\big(\text{Round-Robin}(\succ)_i\big).$$
--
--   **Algorithm 4 (greedy response, p. 15).** A ranking $\succ'_i$ is a greedy response of agent $i$ to $\succ_{-i}$ if, in Round-Robin$(\succ'_i,\succ_{-i})$, every good agent $i$ receives has maximum marginal value, with respect to the goods $i$ already holds, among all goods still available at that step. Every output of Algorithm 4, whatever its tie-breaking and its completion of the ranking, has this property.
--
--   **Algorithm 3 (greedy renaming, p. 11).** Given $x_1,x_2,\dots$ and a set $Y$, a listing $y'_1,\dots,y'_{|Y|}$ of $Y$ is an Algorithm 3 order if each $y'_j$ minimizes $v_i(\cdot\mid\{x_1,\dots,x_{j-1}\})$ over $\{y'_1,\dots,y'_j\}$.
--
--   **Splitting a bundle (p. 20).** If $y_1,\dots,y_k$ lists a bundle $A_j$ in the order its goods are allocated in some run, $Y_1=\{y_3,y_5,\dots\}$ and $Y_2=\{y_2,y_4,\dots\}$ are the goods of $A_j\setminus\{y_1\}$ with odd and with even index.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Goods are a type `M` with `[Fintype M] [DecidableEq M]`, bundles are `Finset M`, and valuations are real-valued; non-negativity of a valuation follows from normalization and monotonicity, so the paper's codomain $\mathbb R_{\ge0}$ is recovered. A ranking is a list `l` with `l.Nodup` containing every good, most preferred first, and `top l T` is `l.find? (· ∈ T)`, an `Option` that is `none` only when $T$ has no good of `l`. Agents are `Fin n` with `[NeZero n]`, 0-based; step `t` (0-based) is taken by agent `t % n`. `allocBefore σ t` is the set of goods allocated in steps $0,\dots,t-1$, `pick σ t` the good allocated at step `t`, `roundRobin σ i` the bundle $A_i$ (the picks at agent $i$'s steps among the first $m$), and `bundleBefore σ i t` the goods $i$ received before step `t`. In `IsApproxPNE`, deviations range over rankings only, as in Definition 2.4, and the reports themselves are required to be rankings. Algorithms 3 and 4 are encoded relationally (`IsAlg3Order`, `IsGreedyResponse`): the relation is satisfied by every output of the algorithm for every tie-breaking, so a theorem stated for all relational solutions is at least as strong as the paper's. Sequences such as $x_r$, $y_a$, $y'_j$ are functions `ℕ → M`, 0-based; `IsTimeOrderedEnum σ' A k y` says that `y 0, …, y (k-1)` lists $A$ without repetition in order of allocation in Round-Robin$(\sigma')$. `Yone y k` and `Ytwo y k` are $Y_1$ (0-based indices $2,4,\dots$) and $Y_2$ (0-based indices $1,3,\dots$).
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, pp. 4–7, §2 (marginal value, valuation classes, Theorem 2.1 context, Definitions 2.3–2.4, Mechanism 1); p. 11, Algorithm 3; p. 15, Algorithm 4; p. 20, proof of Theorem 4.4 (Y_1, Y_2)

import Mathlib
import Definitions.Def_RoundRobinEq_CancelableBluff_Setting

namespace RoundRobinEq.SubmodularEF1

variable {M : Type} [Fintype M] [DecidableEq M]

/-- Marginal value (p. 5): `v(T | S) = v(T ∪ S) − v(S)`; `v(g | S)` is `marginal v {g} S`. -/
def marginal (v : Finset M → ℝ) (T S : Finset M) : ℝ :=
  v (T ∪ S) - v S

/-- Non-decreasing (monotone), p. 5: `v(S) ≤ v(T)` for any `S ⊆ T ⊆ M`. -/
def IsNonDecreasing (v : Finset M → ℝ) : Prop :=
  ∀ S T : Finset M, S ⊆ T → v S ≤ v T

/-- A valuation function (p. 4–5): normalized (`v(∅) = 0`) and non-decreasing. -/
def IsValuation (v : Finset M → ℝ) : Prop :=
  v ∅ = 0 ∧ IsNonDecreasing v

/-- Submodular, p. 5: `v(g | S) ≥ v(g | T)` for any `S ⊆ T ⊆ M` and `g ∉ T`. -/
def IsSubmodular (v : Finset M → ℝ) : Prop :=
  ∀ (S T : Finset M) (g : M), S ⊆ T → g ∉ T → marginal v {g} T ≤ marginal v {g} S

/-- A preference ranking (a total order on `M`, p. 5), written as the list of all goods,
most preferred first, each good exactly once. -/
def IsRanking (l : List M) : Prop :=
  l.Nodup ∧ ∀ g : M, g ∈ l

/-- `top(≻, T)` (p. 5): the first good of the ranking `l` that lies in `T` (`none` if there is none). -/
def top (l : List M) (T : Finset M) : Option M :=
  l.find? (fun g => decide (g ∈ T))

/-- Mechanism 1 (Round-Robin, p. 7) on the reported profile `σ`: the set of goods allocated in
the (0-based) steps `0, …, t − 1`. At step `t` the agent `RoundRobinEq.CancelableBluff.agentAt n t` receives
`top(σ (RoundRobinEq.CancelableBluff.agentAt n t), M \ allocBefore σ t)`. -/
def allocBefore {n : ℕ} [NeZero n] (σ : Fin n → List M) : ℕ → Finset M
  | 0 => ∅
  | t + 1 =>
    match top (σ (RoundRobinEq.CancelableBluff.agentAt n t)) (Finset.univ \ allocBefore σ t) with
    | some g => insert g (allocBefore σ t)
    | none => allocBefore σ t

/-- The good allocated at (0-based) step `t` of Round-Robin(σ). -/
def pick {n : ℕ} [NeZero n] (σ : Fin n → List M) (t : ℕ) : Option M :=
  top (σ (RoundRobinEq.CancelableBluff.agentAt n t)) (Finset.univ \ allocBefore σ t)

/-- The bundle `A_i` returned by Round-Robin(σ) (Mechanism 1, p. 7): the goods picked at agent
`i`'s steps among the first `m = |M|` steps. -/
def roundRobin {n : ℕ} [NeZero n] (σ : Fin n → List M) (i : Fin n) : Finset M :=
  ((Finset.range (Fintype.card M)).filter (fun t => RoundRobinEq.CancelableBluff.agentAt n t = i)).biUnion
    (fun t => (pick σ t).toFinset)

/-- The goods agent `i` has received in the (0-based) steps `0, …, t − 1` of Round-Robin(σ). -/
def bundleBefore {n : ℕ} [NeZero n] (σ : Fin n → List M) (i : Fin n) (t : ℕ) : Finset M :=
  ((Finset.range t).filter (fun s => RoundRobinEq.CancelableBluff.agentAt n s = i)).biUnion (fun s => (pick σ s).toFinset)

/-- Definition 2.3 (p. 6): the allocation `A` is `α`-EF1 if for all agents `i, j` with
`A_j ≠ ∅` there is `g ∈ A_j` with `v_i(A_i) ≥ α · v_i(A_j \ {g})`. -/
def IsApproxEF1 {n : ℕ} (α : ℝ) (v : Fin n → Finset M → ℝ) (A : Fin n → Finset M) : Prop :=
  ∀ i j : Fin n, (A j).Nonempty → ∃ g ∈ A j, α * v i ((A j).erase g) ≤ v i (A i)

/-- `α`-EF1 from agent `i`'s perspective (p. 6), for agent `i`'s valuation `vi`: for every agent
`j` with `A_j ≠ ∅` there is `g ∈ A_j` with `v_i(A_i) ≥ α · v_i(A_j \ {g})`. -/
def IsApproxEF1From {n : ℕ} (α : ℝ) (vi : Finset M → ℝ) (A : Fin n → Finset M) (i : Fin n) :
    Prop :=
  ∀ j : Fin n, (A j).Nonempty → ∃ g ∈ A j, α * vi ((A j).erase g) ≤ vi (A i)

/-- Definition 2.4 (p. 6): `σ` is an `α`-approximate pure Nash equilibrium of Round-Robin: every
report is a ranking, and for every agent `i` and every ranking `τ`,
`α · v_i(RR(τ, σ_{−i})_i) ≤ v_i(RR(σ)_i)`. -/
def IsApproxPNE {n : ℕ} [NeZero n] (α : ℝ) (v : Fin n → Finset M → ℝ) (σ : Fin n → List M) :
    Prop :=
  (∀ i, IsRanking (σ i)) ∧
    ∀ (i : Fin n) (τ : List M), IsRanking τ →
      α * v i (roundRobin (Function.update σ i τ) i) ≤ v i (roundRobin σ i)

/-- Algorithm 4 (p. 15), relationally: `τ` is a greedy response of agent `i` (with valuation
`vi`) to `σ_{−i}` when `τ` is a ranking and, in Round-Robin(τ, σ_{−i}), at each of agent `i`'s
steps `t < m` the good picked has maximum marginal value, with respect to the goods `i` received
before step `t`, among all goods still unallocated at step `t`. Every output of Algorithm 4
(for any tie-breaking and any completion) satisfies this. -/
def IsGreedyResponse {n : ℕ} [NeZero n] (vi : Finset M → ℝ) (σ : Fin n → List M) (i : Fin n)
    (τ : List M) : Prop :=
  IsRanking τ ∧
    ∀ t < Fintype.card M, RoundRobinEq.CancelableBluff.agentAt n t = i → ∀ g : M, pick (Function.update σ i τ) t = some g →
      ∀ h : M, h ∉ allocBefore (Function.update σ i τ) t →
        marginal vi {h} (bundleBefore (Function.update σ i τ) i t) ≤
          marginal vi {g} (bundleBefore (Function.update σ i τ) i t)

/-- `y` enumerates the set `A` (of `k` goods) as `y 0, …, y (k − 1)`, without repetition, in the
order in which the goods are allocated in Round-Robin(σ'): a good with a larger index is never
allocated before a good with a smaller index. -/
def IsTimeOrderedEnum {n : ℕ} [NeZero n] (σ' : Fin n → List M) (A : Finset M) (k : ℕ)
    (y : ℕ → M) : Prop :=
  (Finset.range k).image y = A ∧ Set.InjOn y (Finset.range k : Set ℕ) ∧
    ∀ a b : ℕ, a < b → b < k → ∀ t : ℕ, y b ∈ allocBefore σ' t → y a ∈ allocBefore σ' t

/-- `Y_1` (p. 20): the goods of `A_j \ {y_1}` with odd (1-based) index, i.e. `y_3, y_5, …`;
0-based these are `y a` with `a` even and `a ≥ 2`, `a < k`. -/
def Yone (y : ℕ → M) (k : ℕ) : Finset M :=
  ((Finset.range k).filter (fun a => 2 ≤ a ∧ a % 2 = 0)).image y

/-- `Y_2` (p. 20): the goods of `A_j \ {y_1}` with even (1-based) index, i.e. `y_2, y_4, …`;
0-based these are `y a` with `a` odd, `a < k`. -/
def Ytwo (y : ℕ → M) (k : ℕ) : Finset M :=
  ((Finset.range k).filter (fun a => a % 2 = 1)).image y

/-- Algorithm 3 (p. 11), relationally: `y'` lists the set `Y` as `y' 0, …, y' (|Y| − 1)` (the
paper's `y'_1, …, y'_{|Y|}`), and for each `j < |Y|`, `y' j` minimizes the marginal value
`v_i(· | {x_0, …, x_{j−1}})` among `y' 0, …, y' j` (the paper's
`y'_j = argmin_{g ∈ Z} v_i(g | {x_1, …, x_{j−1}})`, `Z = {y'_1, …, y'_j}`). Every output of
Algorithm 3 (for any tie-breaking) satisfies this. -/
def IsAlg3Order (vi : Finset M → ℝ) (x : ℕ → M) (Y : Finset M) (y' : ℕ → M) : Prop :=
  (Finset.range Y.card).image y' = Y ∧
    ∀ j < Y.card, ∀ t ≤ j,
      marginal vi {y' j} ((Finset.range j).image x) ≤ marginal vi {y' t} ((Finset.range j).image x)

end RoundRobinEq.SubmodularEF1


