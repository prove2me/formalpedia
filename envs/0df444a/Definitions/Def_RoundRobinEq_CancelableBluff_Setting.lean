-- Prove2me | Definitions.Def_RoundRobinEq_CancelableBluff_Setting
-- name    : RoundRobinEq_CancelableBluff_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:27:41.107016+00:00
-- url     : https://prove2.me/theorems/b3ad99a0-5fcc-4331-bdfc-b3fdd2f86d7b
-- title:
--   pp. 4–8 — valuations, cancelability, rankings, Mechanism 1 (Round-Robin), α-EF1, α-approximate PNE, the bluff profile
-- statement:
--   This file fixes the model of §2 (pp. 4–7) and the bluff profile of §3.1 (pp. 7–8) of Amanatidis, Birmpas, Lazos, Leonardi and Reiffenhäuser.
--
--   There are $n \ge 1$ agents $N = [n]$ and a finite set $M$ of $m = |M|$ indivisible goods. Each agent $i$ has a **valuation function** $v_i : 2^M \to \mathbb R$, which is
--
--   1. **normalized**: $v_i(\emptyset) = 0$;
--   2. **non-decreasing**: $v_i(S) \le v_i(T)$ whenever $S \subseteq T \subseteq M$.
--
--   The **marginal value** of $T$ with respect to $S$ is $v_i(T \mid S) = v_i(T \cup S) - v_i(S)$. A valuation $v$ is **cancelable** if for all $S, T \subseteq M$ and every good $g \in M \setminus (S \cup T)$,
--   $$
--   v(S \cup \{g\}) > v(T \cup \{g\}) \;\Longrightarrow\; v(S) > v(T).
--   $$
--
--   A **preference ranking** $\succ$ is a total order on $M$, written as the list of all goods, most preferred first. For a set $T$, $\mathrm{top}(\succ, T)$ is the most preferred good of $T$ (undefined if $T = \emptyset$). A **profile** is a vector $\boldsymbol\succ = (\succ_1, \dots, \succ_n)$ of reported rankings; $(\succ_i', \boldsymbol\succ_{-i})$ replaces agent $i$'s report by $\succ_i'$.
--
--   **Round-Robin** (Mechanism 1, p. 7) runs in steps: at step $t$ agent $t \bmod n$ (agents and steps counted from $0$) receives $\mathrm{top}(\succ_{t \bmod n}, S)$, where $S$ is the set of goods not allocated in earlier steps, and that good leaves $S$. After $m$ steps every good is allocated; $A_i$ is the set of goods agent $i$ received, and $(A_1, \dots, A_n)$ is the allocation returned by Round-Robin$(\boldsymbol\succ)$.
--
--   An allocation $(A_1, \dots, A_n)$ is **$\alpha$-EF1** (Definition 2.3, p. 6) if for all agents $i, j$ with $A_j \neq \emptyset$ there is a good $g \in A_j$ with
--   $$
--   v_i(A_i) \ge \alpha \cdot v_i(A_j \setminus \{g\}).
--   $$
--   A profile of rankings $\boldsymbol\succ$ is an **$\alpha$-approximate pure Nash equilibrium** (Definition 2.4, p. 6) of Round-Robin if for every agent $i$ and every ranking $\succ_i'$ of $M$,
--   $$
--   \alpha \cdot v_i\big(A_i(\succ_i', \boldsymbol\succ_{-i})\big) \le v_i\big(A_i(\boldsymbol\succ)\big),
--   $$
--   where $A_i(\cdot)$ is agent $i$'s bundle under Round-Robin; $\alpha = 1$ is an exact PNE.
--
--   A profile $\boldsymbol\succ^* = (\succ_1^*, \dots, \succ_n^*)$ is a **strict variant of the truthful profile** (p. 7) if every $\succ_i^*$ is a ranking that lists the goods by non-increasing singleton value: $v_i(\{g\}) > v_i(\{g'\})$ implies $g \succ_i^* g'$, with ties broken in an arbitrary fixed way. Let $h_1, h_2, \dots, h_m$ be the goods in the order in which Round-Robin$(\boldsymbol\succ^*)$ allocates them and $\succ^{\mathrm b}$ the ranking $h_1 \succ^{\mathrm b} h_2 \succ^{\mathrm b} \cdots \succ^{\mathrm b} h_m$. The **bluff profile** (p. 8) is $\boldsymbol\succ^{\mathrm b} = (\succ^{\mathrm b}, \dots, \succ^{\mathrm b})$: every agent reports the order in which the truthful run allocated the goods.
--
--   These objects are the shared vocabulary of the missions drawn from this paper: Theorem 3.2 says that the bluff profile is an exact PNE when all valuations are cancelable, and Theorems 3.7, 4.4 and 4.5 concern approximate PNE and α-EF1 of Round-Robin.
--
--   **Formalization Note** Agents are `Fin n` with `[NeZero n]`, goods a `Fintype` with decidable equality. Valuations are real-valued; `IsValuation` is normalized plus non-decreasing, and nonnegativity follows from the two. A ranking is a duplicate-free list containing every good; `top l T` is the first entry of `l` lying in `T`, as an `Option`. Steps are 0-based: the paper's step $(r-1)n + i$ (round $r$, agent $i$, both from 1) is step `(r-1)*n + (i-1)`, taken by agent `t % n`. `allocBefore σ t` is the set of goods allocated in steps $0, \dots, t-1$, `pick σ t` the good allocated at step $t$, and `roundRobin σ i` agent $i$'s bundle over the first $m$ steps; for rankings this is exactly the output of Mechanism 1, whose $\lceil m/n\rceil$ rounds allocate nothing after step $m$. `pickOrder σ` is the list $h_1, \dots, h_m$ (its 0-based entry $t$ is $h_{t+1}$), and `bluff σ` gives every agent that list. In `IsApproxPNE` deviations range over rankings only, as in Definition 2.4, and the reported profile itself must consist of rankings. `IsStrictTruthful v σ` requires each `σ i` to be a ranking in which a good of strictly larger singleton value comes strictly earlier (`List.idxOf`); any tie-breaking is allowed.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, pp. 4–8, §2 (model, p. 5 valuation classes, Definitions 2.3 and 2.4 p. 6, Mechanism 1 p. 7, strict truthful profile p. 7), §3.1 (bluff profile pp. 7–8)

import Mathlib

namespace RoundRobinEq.CancelableBluff

/-- Marginal value `v(T | S) = v(T ∪ S) - v(S)` (p. 5). The value of a single good `g` given `S`
is `marginal v {g} S`. -/
def marginal {M : Type*} [DecidableEq M] (v : Finset M → ℝ) (T S : Finset M) : ℝ :=
  v (T ∪ S) - v S

/-- A valuation function: normalized (`v ∅ = 0`) and non-decreasing (pp. 4–5). -/
def IsValuation {M : Type*} (v : Finset M → ℝ) : Prop :=
  v ∅ = 0 ∧ ∀ S T : Finset M, S ⊆ T → v S ≤ v T

/-- Cancelable (p. 5): `v(S ∪ {g}) > v(T ∪ {g}) ⇒ v(S) > v(T)` for all `S, T ⊆ M` and
`g ∈ M \ (S ∪ T)`. -/
def IsCancelable {M : Type*} [DecidableEq M] (v : Finset M → ℝ) : Prop :=
  ∀ (S T : Finset M) (g : M), g ∉ S ∪ T → v (insert g T) < v (insert g S) → v T < v S

/-- A preference ranking (a total order on `M`, p. 5), written as the list of all goods, most
preferred first, each good exactly once. -/
def IsRanking {M : Type*} (l : List M) : Prop :=
  l.Nodup ∧ ∀ g, g ∈ l

/-- `top(≻, T)`: the first good of the ranking `l` that lies in `T` (`none` if there is none). -/
def top {M : Type*} [DecidableEq M] (l : List M) (T : Finset M) : Option M :=
  l.find? (fun g => decide (g ∈ T))

/-- The agent who acts at the 0-based step `t` of Round-Robin: agent `t mod n`. -/
def agentAt (n : ℕ) [NeZero n] (t : ℕ) : Fin n :=
  ⟨t % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

/-- The goods allocated in steps `0, …, t - 1` of Round-Robin (Mechanism 1, p. 7) run on the
reported profile `σ`. -/
def allocBefore {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M]
    (σ : Fin n → List M) : ℕ → Finset M
  | 0 => ∅
  | t + 1 =>
    match top (σ (agentAt n t)) (Finset.univ \ allocBefore σ t) with
    | some g => insert g (allocBefore σ t)
    | none => allocBefore σ t

/-- The good allocated at the 0-based step `t` of Round-Robin(σ): the acting agent's top
available good. -/
def pick {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M]
    (σ : Fin n → List M) (t : ℕ) : Option M :=
  top (σ (agentAt n t)) (Finset.univ \ allocBefore σ t)

/-- The bundle `A_i` returned by Round-Robin(σ) (Mechanism 1, p. 7): the goods picked at agent
`i`'s steps among the first `m = |M|` steps. -/
def roundRobin {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M]
    (σ : Fin n → List M) (i : Fin n) : Finset M :=
  ((Finset.range (Fintype.card M)).filter (fun t => agentAt n t = i)).biUnion
    (fun t => (pick σ t).toFinset)

/-- Definition 2.3 (p. 6): the allocation `A` is `α`-EF1 if for all agents `i, j` with
`A_j ≠ ∅` there is a good `g ∈ A_j` with `v_i(A_i) ≥ α · v_i(A_j \ {g})`. -/
def IsApproxEF1 {n : ℕ} {M : Type*} [DecidableEq M] (α : ℝ) (v : Fin n → Finset M → ℝ)
    (A : Fin n → Finset M) : Prop :=
  ∀ i j : Fin n, (A j).Nonempty → ∃ g ∈ A j, α * v i ((A j).erase g) ≤ v i (A i)

/-- Definition 2.4 (p. 6): the profile `σ` of rankings is an `α`-approximate pure Nash
equilibrium of Round-Robin if no agent `i` gains more than a factor `1/α` by reporting any other
ranking `τ`: `α · v_i(A_i(τ, σ_{-i})) ≤ v_i(A_i(σ))`. -/
def IsApproxPNE {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M] (α : ℝ)
    (v : Fin n → Finset M → ℝ) (σ : Fin n → List M) : Prop :=
  (∀ i, IsRanking (σ i)) ∧
    ∀ (i : Fin n) (τ : List M), IsRanking τ →
      α * v i (roundRobin (Function.update σ i τ) i) ≤ v i (roundRobin σ i)

/-- `σ` is a strict variant of the truthful profile (p. 7): every agent reports a ranking that
lists the goods by non-increasing singleton value `v_i({g})`, ties broken in any fixed way. -/
def IsStrictTruthful {n : ℕ} {M : Type*} [DecidableEq M] (v : Fin n → Finset M → ℝ) (σ : Fin n → List M) :
    Prop :=
  ∀ i, IsRanking (σ i) ∧
    ∀ g g' : M, v i {g'} < v i {g} → (σ i).idxOf g < (σ i).idxOf g'

/-- `h_1, …, h_m`: the goods in the order in which Round-Robin(σ) allocates them (pp. 7–8). -/
def pickOrder {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M]
    (σ : Fin n → List M) : List M :=
  (List.range (Fintype.card M)).filterMap (pick σ)

/-- The bluff profile `≻^b` (p. 8): every agent reports `h_1 ≻ h_2 ≻ ⋯ ≻ h_m`, the order in
which Round-Robin(σ) allocated the goods. -/
def bluff {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M]
    (σ : Fin n → List M) : Fin n → List M :=
  fun _ => pickOrder σ

end RoundRobinEq.CancelableBluff


