-- Prove2me | Definitions.Def_PriceIgnorance_Pairwise_Algorithms
-- name    : PriceIgnorance_Pairwise_Algorithms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:12:17.925145+00:00
-- url     : https://prove2.me/theorems/64282c1c-71f9-40a3-b05b-499735009707
-- title:
--   Randomized online stopping algorithms in fixed and in uniformly random order, and $\mathrm{val}(A,V)$
-- statement:
--   An **online algorithm** sees the values one at a time. At each step it either stops and accrues the current value, or rejects it for good and continues. If it never stops it accrues $0$. Algorithms may be randomized. $\mathrm{val}(A,v)$ is the expected value that $A$ accrues on the value vector $v$, taken over $A$'s internal randomness (Notation, p. 3).
--
--   1. **Fixed order (prophet inequality).** The values arrive in the order $v_0,v_1,\dots,v_{n-1}$. At step $i$, having seen $v_0,\dots,v_i$, the algorithm stops with probability $p_i(v_0,\dots,v_i)\in[0,1]$, using fresh randomness. Each $p_i$ is Borel measurable. Then
--   $$\mathrm{val}(A,v)=\sum_{i} v_i\; p_i(v_0,\dots,v_i)\prod_{j<i}\big(1-p_j(v_0,\dots,v_j)\big).$$
--   $A$ is **deterministic** when every $p_i$ takes only the values $0$ and $1$.
--   2. **Random order (prophet secretary).** The arrival order is a uniformly random permutation $\sigma$ of the indices. It is independent of the values and of the algorithm's randomness. At step $j$ the algorithm has seen the identities and values $(\sigma_0,v_{\sigma_0}),\dots,(\sigma_j,v_{\sigma_j})$ and stops with probability $p_j$ of this history. $\mathrm{val}(A,v)$ is the accrued value averaged over $\sigma$ and the internal randomness (p. 7):
--   $$\mathrm{val}(A,v)=\frac1{n!}\sum_{\sigma}\sum_j v_{\sigma_j}\,p_j(h_j)\prod_{l<j}\big(1-p_l(h_l)\big),\qquad h_j=\big((\sigma_0,v_{\sigma_0}),\dots,(\sigma_j,v_{\sigma_j})\big).$$
--   3. An **arrival model** consists of the class $\mathrm{ALG}$ of algorithms for each $n$ together with their value function. `fixedOrder` and `randomOrder` are the two models of the paper.
--
--   The same class $\mathrm{ALG}$ serves for correlation-blind and correlation-aware algorithms. The difference between the two lies only in the order of quantifiers in the ratios.
--
--   **Formalization Note** A randomized algorithm is encoded by its behavioural stopping probabilities. For a single decision maker who remembers the whole history, these give exactly the same value functions as probability mixtures of deterministic algorithms (Kuhn's theorem). Lemma 3.4(b) states this mixture representation on finite grids. Steps are 0-based (`Fin n`), and $\sigma_j$ is the index of the $j$-th arrival.
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 1; p. 3, Notation; p. 7 (random order); p. 9, Definition 3.13

import Mathlib

/-!
# Randomized online algorithms for the prophet and prophet secretary problems

Abdallah, Wajc, *Price of Ignorance in Pairwise-Independent Prophet Inequalities*, STOC 2027
submission (manuscript sha256 c79626fd…), p. 1 (§1), p. 3 (Notation: `ALG`, `val(A, V)`),
p. 7 (random order: `val(A, V)` averaged over a uniformly random order), p. 9 (Definition 3.13).

* **Fixed order** (prophet inequality). At step `i` (0-based) the algorithm has seen
  `V_0, …, V_i` and stops (accruing `V_i`) with probability `stopProb i (V_0, …, V_i) ∈ [0, 1]`,
  using fresh internal randomness; otherwise it continues. A randomized algorithm is encoded by
  these behavioural stopping probabilities (measurable in the history); it is deterministic when
  every probability is `0` or `1`. `val A v` is its expected accrued value on the value vector `v`
  over its internal randomness (`0` if it never stops).
* **Random order** (prophet secretary). The arrival order `σ` is a uniformly random permutation of
  the indices, independent of the values and of the algorithm's randomness. At step `j` the
  algorithm has seen the identities and values `(σ 0, v (σ 0)), …, (σ j, v (σ j))`.
  `val A v` averages the accrued value over `σ` and the internal randomness.
* An `ArrivalModel` packages the class of algorithms and its value function, so that the
  competitive ratio and the price of ignorance are defined once for both models.
-/

namespace PriceIgnorance.Pairwise

/-- The history at step `i` in fixed order: the values `v 0, …, v i`. -/
def hist {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : Fin (i.val + 1) → ℝ :=
  fun j => v ⟨j.val, by omega⟩

/-- A randomized online stopping algorithm for `n` values arriving in the fixed order
`0, 1, …, n - 1`, given by its stopping probability at every history. -/
structure OnlineAlg (n : ℕ) where
  /-- probability of stopping at step `i` after seeing `v 0, …, v i` -/
  stopProb : (i : Fin n) → (Fin (i.val + 1) → ℝ) → ℝ
  measurable_stopProb : ∀ i, Measurable (stopProb i)
  stopProb_mem : ∀ i h, stopProb i h ∈ Set.Icc (0 : ℝ) 1

/-- Probability that the fixed-order algorithm `A` stops exactly at step `i` on values `v`. -/
noncomputable def OnlineAlg.stopAt {n : ℕ} (A : OnlineAlg n) (v : Fin n → ℝ) (i : Fin n) : ℝ :=
  A.stopProb i (hist v i) *
    ∏ j ∈ Finset.univ.filter (fun j : Fin n => j < i), (1 - A.stopProb j (hist v j))

/-- `val(A, v)`: the expected value accrued by `A` on `v` (over its internal randomness). -/
noncomputable def OnlineAlg.val {n : ℕ} (A : OnlineAlg n) (v : Fin n → ℝ) : ℝ :=
  ∑ i, A.stopAt v i * v i

/-- A deterministic fixed-order algorithm: every stopping probability is `0` or `1`. -/
def OnlineAlg.IsDeterministic {n : ℕ} (A : OnlineAlg n) : Prop :=
  ∀ i h, A.stopProb i h = 0 ∨ A.stopProb i h = 1

/-- The history at step `j` under arrival order `σ` (`σ j` is the index of the `j`-th arrival):
the identities and values of the first `j + 1` arrivals. -/
def histRO {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → ℝ) (j : Fin n) :
    Fin (j.val + 1) → Fin n × ℝ :=
  fun l => (σ ⟨l.val, by omega⟩, v (σ ⟨l.val, by omega⟩))

/-- A randomized online stopping algorithm for the prophet secretary problem with `n` values:
at step `j` it stops with a probability depending on the identities and values seen so far. -/
structure OnlineAlgRO (n : ℕ) where
  /-- probability of stopping at step `j` after seeing the first `j + 1` (identity, value) pairs -/
  stopProb : (j : Fin n) → (Fin (j.val + 1) → Fin n × ℝ) → ℝ
  measurable_stopProb : ∀ j, Measurable (stopProb j)
  stopProb_mem : ∀ j h, stopProb j h ∈ Set.Icc (0 : ℝ) 1

/-- Probability that `A` stops exactly at step `j` on values `v` under arrival order `σ`. -/
noncomputable def OnlineAlgRO.stopAt {n : ℕ} (A : OnlineAlgRO n) (σ : Equiv.Perm (Fin n))
    (v : Fin n → ℝ) (j : Fin n) : ℝ :=
  A.stopProb j (histRO σ v j) *
    ∏ l ∈ Finset.univ.filter (fun l : Fin n => l < j), (1 - A.stopProb l (histRO σ v l))

/-- Expected value accrued by `A` on `v` under the fixed arrival order `σ`. -/
noncomputable def OnlineAlgRO.valOrder {n : ℕ} (A : OnlineAlgRO n) (σ : Equiv.Perm (Fin n))
    (v : Fin n → ℝ) : ℝ :=
  ∑ j, A.stopAt σ v j * v (σ j)

/-- `val(A, v)` in random order: the accrued value averaged over a uniformly random arrival
order `σ` and the algorithm's internal randomness (p. 7). -/
noncomputable def OnlineAlgRO.val {n : ℕ} (A : OnlineAlgRO n) (v : Fin n → ℝ) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin n), A.valOrder σ v

/-- A deterministic random-order algorithm: every stopping probability is `0` or `1`. -/
def OnlineAlgRO.IsDeterministic {n : ℕ} (A : OnlineAlgRO n) : Prop :=
  ∀ j h, A.stopProb j h = 0 ∨ A.stopProb j h = 1

/-- An arrival model: for every number `n` of values, the class `ALG` of online algorithms and
their value function `val(A, v)`. -/
structure ArrivalModel where
  Alg : ℕ → Type
  val : {n : ℕ} → Alg n → (Fin n → ℝ) → ℝ

/-- The prophet inequality: values arrive in the fixed order `0, …, n - 1`. -/
noncomputable def fixedOrder : ArrivalModel where
  Alg := OnlineAlg
  val := fun A v => A.val v

/-- The prophet secretary problem: values arrive in a uniformly random order, independent of the
values, with identities revealed. -/
noncomputable def randomOrder : ArrivalModel where
  Alg := OnlineAlgRO
  val := fun A v => A.val v

end PriceIgnorance.Pairwise


