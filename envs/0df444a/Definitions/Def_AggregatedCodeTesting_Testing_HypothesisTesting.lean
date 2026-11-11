-- Prove2me | Definitions.Def_AggregatedCodeTesting_Testing_HypothesisTesting
-- name    : AggregatedCodeTesting_Testing_HypothesisTesting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:14.72385+00:00
-- url     : https://prove2.me/theorems/1a5c9dd2-a77d-4be6-add0-a52e93686cec
-- title:
--   §2 — randomized $N$-sample tests, their two errors, and the sample complexity $N^*$
-- statement:
--   Let $P$ and $Q$ be mass functions on a finite observation space $\mathcal X$. A **randomized $N$-sample test** is a function $T:\mathcal X^N\to[0,1]$ of the $N$ observations only; $T(x_1,\dots,x_N)$ is the probability of declaring the second hypothesis $Q$. Its two errors are
--
--   $$
--   \mathrm{err}_P(T)=\sum_{x\in\mathcal X^N}\Big(\prod_{i=1}^N P(x_i)\Big)T(x),\qquad
--   \mathrm{err}_Q(T)=\sum_{x\in\mathcal X^N}\Big(\prod_{i=1}^N Q(x_i)\Big)\big(1-T(x)\big),
--   $$
--
--   the probabilities of a wrong decision when the observations are i.i.d. from $P$, respectively from $Q$. The **sample complexity** $N^*(P,Q)$ is the least $N$ for which some randomized test has both errors at most $1/4$; it is $+\infty$ when no $N$ suffices (for instance when $P=Q$).
--
--   These are the testing notions of the paper's model section: deciding between two known hypotheses with error at most $1/4$ under either hypothesis, with $N^*(\ell,\ell')$ the minimum number of samples. Every test, randomized or not, enters the minimum.
--
--   **Formalization Note.** $N^*$ takes values in $\mathbb N\cup\{\infty\}$ (`ℕ∞`), so the minimum is defined even when no test succeeds.
-- source:
--   Jianxin Wang, Zixuan Wang, Chenxu Pang, Chaoen Xiao, Lei Zhang, Zaitian Fu, Conghui Zheng, Yiyang Zou, STOC 2027 submission #1555 (October 2026), §2 (testing and N*(ℓ,ℓ′)), printed p. 3 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1555.pdf

import Mathlib

namespace AggregatedCodeTesting.Testing

/-! # Simple binary hypothesis testing with `N` independent samples

Wang–Wang–Pang–Xiao–Zhang–Fu–Zheng–Zou, STOC 2027 submission #1555, §2, printed p. 3
(PDF p. 4): "Testing means deciding between two known offset profiles with error at most 1/4
under either hypothesis. Write `N*(ℓ, ℓ′)` for the minimum number of samples."

These definitions are generic: `P` and `Q` are mass functions on a finite observation space
`α`; a test sees only the `N` observations. -/

variable {α : Type} [Fintype α] [DecidableEq α]

/-- A randomized `N`-sample test: a function of the `N` observations only, with values in
`[0, 1]`, read as the probability of declaring the **second** hypothesis. -/
def IsRandomizedTest {N : ℕ} (T : (Fin N → α) → ℝ) : Prop :=
  ∀ xs, 0 ≤ T xs ∧ T xs ≤ 1

/-- Error under the first hypothesis `P`: `E_{P^{⊗N}}[T]`, the probability of declaring the
second hypothesis when the `N` observations are i.i.d. from `P`. -/
noncomputable def errorFirst {N : ℕ} (P : α → ℝ) (T : (Fin N → α) → ℝ) : ℝ :=
  ∑ xs : Fin N → α, (∏ i, P (xs i)) * T xs

/-- Error under the second hypothesis `Q`: `E_{Q^{⊗N}}[1 - T]`. -/
noncomputable def errorSecond {N : ℕ} (Q : α → ℝ) (T : (Fin N → α) → ℝ) : ℝ :=
  ∑ xs : Fin N → α, (∏ i, Q (xs i)) * (1 - T xs)

/-- Some randomized `N`-sample test has both errors at most `ε`. -/
def CanTest (P Q : α → ℝ) (N : ℕ) (ε : ℝ) : Prop :=
  ∃ T : (Fin N → α) → ℝ, IsRandomizedTest T ∧ errorFirst P T ≤ ε ∧ errorSecond Q T ≤ ε

/-- The sample complexity `N*(P, Q)`: the least `N` for which some randomized test has both
errors at most `1/4`; it is `⊤` when no sample size suffices (e.g. `P = Q`). -/
noncomputable def sampleComplexity (P Q : α → ℝ) : ℕ∞ :=
  ⨅ (N : ℕ) (_ : CanTest P Q N (1 / 4)), (N : ℕ∞)

end AggregatedCodeTesting.Testing


