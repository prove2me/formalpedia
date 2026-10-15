-- Prove2me | Definitions.Def_SecretaryAdvice_Memoryless_Setting
-- name    : SecretaryAdvice_Memoryless_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:11.849251+00:00
-- url     : https://prove2.me/theorems/41a8a66d-b1f9-4cd6-9739-f18798935870
-- title:
--   §2, §2.2, §3, pp. 6–9 — secretaries with advice: signaling structures, information, policies, winning probability, NF, HI, memoryless policies
-- statement:
--   This file sets up the secretary problem with advice of §2 and the two signal-structure properties of §2.2.
--
--   **Outcomes and signaling structures.** There are $n$ secretaries arriving in a fixed order $1,\dots,n$ and a finite signal space $\mathcal S$. An outcome is a pair $(r,s)$ where $r_i\in[n]$ is the rank of the $i$-th secretary and $s_i\in\mathcal S$ is its signal; ties among ranks are allowed. A **signaling structure** is a known joint distribution $\mathbb P$ of $(r_1,\dots,r_n,s_1,\dots,s_n)$, given by nonnegative weights summing to $1$, such that every outcome of positive probability has $r_i=n$ for at least one $i$.
--
--   **Events.** $r_i=n$ says that $i$ has the top rank. The **best-so-far event** of equation (1) is
--   $$T_i=\{\,r_i\ge r_j \text{ for all } j<i\,\}.$$
--
--   **Information and policies.** At round $i$ the algorithm observes the relative comparisons $\preceq_{1..i}$ among the first $i$ arrivals together with their signals $s_1,\dots,s_i$, and nothing else. A **policy** maps, for each round $i$, this information to a stopping probability in $[0,1]$. Under a policy $q$ the probability of picking $i$ is
--   $$q_i(\preceq_{1..i},s_{1..i})\prod_{j<i}\bigl(1-q_j(\preceq_{1..j},s_{1..j})\bigr),$$
--   and the **winning probability** is $\sum_i \mathbb E\bigl[\mathbf 1\{r_i=n\}\cdot \mathbb P[i\text{ is picked}]\bigr]$. A policy is **memoryless** when its stopping probability at round $i$ depends only on $i$, on whether $T_i$ holds, and on the current signal $s_i$.
--
--   **Non-Filtering (Definition 6).** For all $j<i$ and all signal values,
--   $$\mathbb P[\preceq_{1..j},s_1,\dots,s_j\mid T_j,s_j]=\mathbb P[\preceq_{1..j},s_1,\dots,s_j\mid T_j,s_j,T_i,s_i].$$
--
--   **History-Irrelevance (Definition 7).** Conditioned on $(T_i,s_i)$, the information $(\preceq_{1..i},s_1,\dots,s_i)$ and the event $r_i=n$ are independent.
--
--   These objects are shared by every statement of the mission: Theorem 8 and Propositions 9 and 10 are statements about them.
--
--   **Formalization Note** Secretaries are indexed by `Fin n`, 0-based (Lean index $i$ is the paper's secretary $i+1$) and ranks are 0-based (Lean rank $n-1$ is the paper's top rank $n$). The signal space is a finite type, so every probability is a finite sum (`prob`, `expectOn`); continuous signal spaces such as Example 2's are outside this formalization. The information at round $i$ is the table of comparisons $r_a\le r_b$ for $a,b\le i$ together with the signals $s_0,\dots,s_i$; a policy is a function of this information only, never of the outcome. Policies are randomized (values in $[0,1]$). Conditional statements in NF and HI are written cross-multiplied, $\mathbb P[A\cap C]\,\mathbb P[C']=\mathbb P[A\cap C']\,\mathbb P[C]$, so that they say nothing on null conditioning events instead of using $0/0=0$. HI conditions on both values $b$ of the indicator of $T_i$ (the case $T_i$ false is automatic, because $r_i=n$ implies $T_i$).
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, pp. 6–9, §2 (Model, equation (1)), Definition 6, Definition 7, §3 (Memoryless Policies)

import Mathlib

namespace SecretaryAdvice.Memoryless

/-- An outcome of the secretary problem with advice on `n` secretaries and signal space `S`:
the (0-based) ranks `r : Fin n → Fin n` and the signals `s : Fin n → S` of the secretaries,
indexed by arrival time (Lean time `i` is the paper's secretary `i + 1`, Lean rank `r` is the
paper's rank `r + 1`, so the paper's top rank `n` is Lean rank `n - 1`). Ties are allowed. -/
abbrev Outcome (n : ℕ) (S : Type) := (Fin n → Fin n) × (Fin n → S)

/-- A signaling structure (§2): a known joint distribution of ranks and signals, given by a
probability weight on the finite outcome space, supported on outcomes in which some secretary
has the top rank `n` (Lean rank `n - 1`). -/
structure SignalingStructure (n : ℕ) (S : Type) [Fintype S] where
  /-- probability weight of each outcome -/
  w : Outcome n S → ℝ
  nonneg : ∀ ω, 0 ≤ w ω
  sum_eq_one : ∑ ω, w ω = 1
  top_exists : ∀ ω, w ω ≠ 0 → ∃ i : Fin n, (ω.1 i).val + 1 = n

variable {n : ℕ} {S : Type} [Fintype S]

open Classical in
/-- `prob μ E = P[E]`, the probability of an event `E` under the signaling structure `μ`. -/
noncomputable def prob (μ : SignalingStructure n S) (E : Outcome n S → Prop) : ℝ :=
  ∑ ω, if E ω then μ.w ω else 0

open Classical in
/-- `expectOn μ f E = E[f · 1_E]`, the expectation of `f` restricted to the event `E`. -/
noncomputable def expectOn (μ : SignalingStructure n S) (f : Outcome n S → ℝ)
    (E : Outcome n S → Prop) : ℝ :=
  ∑ ω, if E ω then μ.w ω * f ω else 0

/-- The rank of secretary `i` is the top rank (the paper's `r_i = n`). -/
def IsTop (i : Fin n) (ω : Outcome n S) : Prop := (ω.1 i).val + 1 = n

/-- The best-so-far event `T_i = {i ⪰ j ; ∀ j < i}` of equation (1). -/
def T (i : Fin n) (ω : Outcome n S) : Prop := ∀ j : Fin n, j < i → ω.1 j ≤ ω.1 i

/-- The signal `s_i` of secretary `i`. -/
def sig (i : Fin n) (ω : Outcome n S) : S := ω.2 i

/-- The embedding of the first `i + 1` arrivals `{0, …, i}` into `Fin n`. -/
def emb (i : Fin n) : Fin (i.val + 1) → Fin n := Fin.castLE (Nat.succ_le_of_lt i.isLt)

/-- The information available at (Lean) round `i`: the pairwise comparisons `a ⪰ b` among the
first `i + 1` arrivals, and their signals; this is `(⪯_{1..i+1}, s_1, …, s_{i+1})`. -/
abbrev Info (n : ℕ) (S : Type) (i : Fin n) : Type :=
  (Fin (i.val + 1) → Fin (i.val + 1) → Bool) × (Fin (i.val + 1) → S)

/-- The information revealed at round `i` by the outcome `ω`: the entry `(a, b)` of the
comparison table is `true` iff `r_a ≤ r_b` (i.e. `b ⪰ a`), for `a, b ≤ i`. -/
def info (i : Fin n) (ω : Outcome n S) : Info n S i :=
  (fun a b => decide (ω.1 (emb i a) ≤ ω.1 (emb i b)), fun a => ω.2 (emb i a))

/-- Whether the information says the current secretary `i` is best so far. -/
def bestSoFar {i : Fin n} (x : Info n S i) : Bool :=
  decide (∀ a : Fin (i.val + 1), x.1 a (Fin.last i.val) = true)

/-- The signal of the current secretary `i`, read off the information. -/
def lastSignal {i : Fin n} (x : Info n S i) : S := x.2 (Fin.last i.val)

/-- A (randomized) policy: at each round `i`, a stopping probability that is a function of the
information available at round `i` only. -/
abbrev Policy (n : ℕ) (S : Type) := (i : Fin n) → Info n S i → ℝ

/-- A policy is valid when every stopping probability lies in `[0, 1]`. -/
def ValidPolicy (q : Policy n S) : Prop := ∀ i x, 0 ≤ q i x ∧ q i x ≤ 1

/-- The probability that the policy `q` picks secretary `i` on the outcome `ω`: it does not stop
at any round `j < i` and stops at round `i`. -/
def pickProb (q : Policy n S) (i : Fin n) (ω : Outcome n S) : ℝ :=
  q i (info i ω) * ∏ j ∈ Finset.Iio i, (1 - q j (info j ω))

/-- The winning probability of `q`: the probability that it stops at a secretary of top rank,
`∑_i P[i is picked ∧ r_i = n]`. -/
noncomputable def win (μ : SignalingStructure n S) (q : Policy n S) : ℝ :=
  ∑ i, expectOn μ (pickProb q i) (IsTop i)

/-- A memoryless policy (§3): the stopping probability at round `i` depends only on `i`, on
whether `T_i` holds, and on the current signal `s_i`. -/
def IsMemoryless (q : Policy n S) : Prop :=
  ∃ m : Fin n → Bool → S → ℝ, ∀ i x, q i x = m i (bestSoFar x) (lastSignal x)

/-- Non-Filtering (Definition 6), cross-multiplied: for `j < i`, the conditional law of the
round-`j` information given `(T_j, s_j = s')` equals that given `(T_j, s_j = s', T_i, s_i = s)`. -/
def NonFiltering (μ : SignalingStructure n S) : Prop :=
  ∀ (i j : Fin n), j < i → ∀ (x : Info n S j) (s' s : S),
    prob μ (fun ω => info j ω = x ∧ T j ω ∧ sig j ω = s') *
        prob μ (fun ω => T j ω ∧ sig j ω = s' ∧ T i ω ∧ sig i ω = s) =
      prob μ (fun ω => info j ω = x ∧ T j ω ∧ sig j ω = s' ∧ T i ω ∧ sig i ω = s) *
        prob μ (fun ω => T j ω ∧ sig j ω = s')

/-- History-Irrelevance (Definition 7), cross-multiplied: conditioned on the value `b` of the
indicator of `T_i` and on `s_i = s`, the round-`i` information and the event `r_i = n` are
independent. -/
def HistoryIrrelevance (μ : SignalingStructure n S) : Prop :=
  ∀ (i : Fin n) (x : Info n S i) (s : S) (b : Bool),
    prob μ (fun ω => info i ω = x ∧ IsTop i ω ∧ (T i ω ↔ b = true) ∧ sig i ω = s) *
        prob μ (fun ω => (T i ω ↔ b = true) ∧ sig i ω = s) =
      prob μ (fun ω => info i ω = x ∧ (T i ω ↔ b = true) ∧ sig i ω = s) *
        prob μ (fun ω => IsTop i ω ∧ (T i ω ↔ b = true) ∧ sig i ω = s)

end SecretaryAdvice.Memoryless


