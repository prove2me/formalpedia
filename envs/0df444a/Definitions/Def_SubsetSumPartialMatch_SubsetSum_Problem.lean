-- Prove2me | Definitions.Def_SubsetSumPartialMatch_SubsetSum_Problem
-- name    : SubsetSumPartialMatch_SubsetSum_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:47.05141+00:00
-- url     : https://prove2.me/theorems/1033d71e-c838-4a27-9857-5e6096a57a4f
-- title:
--   The subset sum problem and the runtime predicate
-- statement:
--   An instance of **subset sum** consists of integers $z=(z_1,\dots,z_n)\in\mathbb Z^n$ and a target $\tau\in\mathbb Z$. A **solution** is a vector $c\in\{0,1\}^n$ with $c\cdot z=\tau$. Zero and negative entries are legal, equal entries remain separate choices, and the empty selection is allowed. The input length $L(z,\tau)$ is the total bit length of the words $n,\tau,z_1,\dots,z_n$.
--
--   An **input-length envelope** of size $2^{o(n)}$ is a function $B:\mathbb N\to\mathbb N$ with $B(n)\ge 1$ and $\log_2 B(n)/n\to 0$.
--
--   The predicate $\mathrm{Solves}(e)$ says that subset sum is solved by a randomized algorithm in time $O(2^{en})$: there is one finite program $P$, chosen before anything else, such that
--
--   1. on every instance and every random tape, $P$ halts and outputs either *no solution* or a valid solution $c$;
--   2. on every instance that has a solution, $P$ outputs *no solution* with probability at most $e^{-n/2}$;
--   3. for every envelope $B$ of size $2^{o(n)}$ there are constants $C>0$ and $N$, independent of the instance and of the tape, such that every run on an instance with $n\ge N$ and $L(z,\tau)\le B(n)$ uses at most $C\,2^{en}$ charged bit operations.
--
--   This one predicate carries both Theorem 2.2 and Theorem 4.1. It is a worst-case bound over random tapes, not a bound on expected time, and it asks for a witness, not a yes/no answer.
--
--   **Formalization Note** The source writes "randomized algorithm" without an error bound in its theorem statements. The bound $e^{-n/2}$ is the one its proof delivers (p. 14: $n^2$ attempts, each succeeding with probability at least $1/(2n)$), and it is stronger than any fixed constant error.
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 2 (formal problem statement), p. 9 (§2, first paragraph)

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_RAM

namespace SubsetSumPartialMatch.SubsetSum

/-- `c ∈ {0,1}^n` is a solution of the instance `(z, τ)`: `c · z = τ`. Entries of `z` and `τ` are
arbitrary integers; equal entries are separate choices and the empty selection is allowed. -/
def IsSolution {n : ℕ} (z : Fin n → ℤ) (τ : ℤ) (c : Fin n → Bool) : Prop :=
  ∑ i, (if c i then z i else 0) = τ

/-- The machine words of an instance: `n`, the target `τ`, then `z_1, …, z_n`. -/
def instanceWords {n : ℕ} (z : Fin n → ℤ) (τ : ℤ) : List ℤ :=
  (n : ℤ) :: τ :: List.ofFn z

/-- The input length `L(z, τ)` of an instance, in bits. -/
def instanceBits {n : ℕ} (z : Fin n → ℤ) (τ : ℤ) : ℕ := wordsLen (instanceWords z τ)

/-- The output `no solution`. -/
def noSolutionWords : List ℤ := [0]

/-- The output announcing the witness `c`. -/
def solutionWords {n : ℕ} (c : Fin n → Bool) : List ℤ :=
  1 :: List.ofFn fun i => if c i then 1 else 0

/-- `B` is an input-length envelope of size `2^{o(n)}`: `B n ≥ 1` and `log₂ (B n) / n → 0`. -/
def IsSubexpEnvelope (B : ℕ → ℕ) : Prop :=
  (∀ n, 1 ≤ B n) ∧
    Filter.Tendsto (fun n : ℕ => Real.logb 2 (B n) / n) Filter.atTop (nhds 0)

/-- Subset sum is solved by a randomized algorithm in time `O(2^{e n})`.

One finite program `P`, fixed before everything else, has these properties.
1. On every instance and every random tape it halts, and its output is `no solution` or a valid
   witness. So `no solution` is the only possible output on a no-instance and no returned witness
   is ever wrong.
2. On every instance with a solution, it answers `no solution` with probability at most
   `exp (-n / 2)`.
3. For every input-length envelope `B` of size `2^{o(n)}` there are `C, N`, independent of the
   instance and of the tape, such that every run on an instance with `n ≥ N` and `L ≤ B n` uses at
   most `C · 2^{e n}` charged bit operations. -/
def SolvesSubsetSumIn (e : ℝ) : Prop :=
  ∃ P : Program,
    (∀ (n : ℕ) (z : Fin n → ℤ) (τ : ℤ) (ω : ℕ → Bool),
      Outputs P ω (instanceWords z τ) noSolutionWords ∨
        ∃ c, IsSolution z τ c ∧ Outputs P ω (instanceWords z τ) (solutionWords c)) ∧
    (∀ (n : ℕ) (z : Fin n → ℤ) (τ : ℤ), (∃ c, IsSolution z τ c) →
      tapeMeasure {ω | Outputs P ω (instanceWords z τ) noSolutionWords} ≤
        ENNReal.ofReal (Real.exp (-(n : ℝ) / 2))) ∧
    ∀ B : ℕ → ℕ, IsSubexpEnvelope B → ∃ (C : ℝ) (N : ℕ), 0 < C ∧
      ∀ n ≥ N, ∀ (z : Fin n → ℤ) (τ : ℤ), instanceBits z τ ≤ B n →
        ∀ ω, CostWithin P ω (instanceWords z τ) (C * (2 : ℝ) ^ (e * n))

end SubsetSumPartialMatch.SubsetSum


