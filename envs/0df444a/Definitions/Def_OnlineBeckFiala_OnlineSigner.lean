-- Prove2me | Definitions.Def_OnlineBeckFiala_OnlineSigner
-- name    : OnlineBeckFiala_OnlineSigner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:33:21.300949+00:00
-- url     : https://prove2.me/theorems/011d69ed-23dc-44e2-bf89-8bc3b77a626e
-- title:
--   Randomized online signing algorithm; prefix sums; $d$-sparse inputs in $[-1,1]^n$
-- statement:
--   An **online signing algorithm** in dimension $n$ receives vectors $a_1,a_2,\dots\in\mathbb R^n$ one at a time and, on receiving $a_t$, immediately and irrevocably outputs a sign $\varepsilon_t\in\{-1,1\}$. It is **randomized** if it has access to private randomness: a probability space $(\Omega,\mathcal F,P)$ and, for each input sequence $a$ and time $t$, a random variable $\varepsilon_t=\varepsilon_t(a,\omega)$. It is **online** if $\varepsilon_t$ depends on the input only through $a_1,\dots,a_t$: two input sequences that agree up to time $t$ produce the same $\varepsilon_t$ for every $\omega$. The adversary is **oblivious**: the input sequence is fixed in advance, independently of $\omega$.
--
--   For such an algorithm the **prefix sums** are
--   $$S_t=\sum_{s\le t}\varepsilon_s a_s ,$$
--   and its **prefix discrepancy** on $a_1,\dots,a_T$ is $\max_{t\le T}\|S_t\|_\infty$. The input class of the main theorem consists of sequences $a_1,\dots,a_T\in[-1,1]^n$ with at most $d$ nonzero coordinates in each vector.
--
--   These objects state the main theorem and Proposition 2.7. The clause that every sign is $\pm1$ excludes partial colorings, which would make the problem trivial; the online clause excludes offline signings.
--
--   **Formalization Note** Times are 0-based: the paper's $a_1,\dots,a_T$ are `a 0, …, a (T-1)` of a sequence `ℕ → (Fin n → ℝ)`, and the prefix sum at time `t` sums over `s = 0, …, t`. The input constraints are imposed on the first $T$ vectors only. $\|\cdot\|_\infty$ is Mathlib's norm on `Fin n → ℝ`. Obliviousness holds because the law $P$ is part of the algorithm and does not depend on the input.
-- source:
--   Altschuler, Tikhomirov, Online Beck–Fiala Down to Logarithmic Sparsity, arXiv:2607.14238 (held version, sha256 5a1529d2…), p.1 (online model), p.2 Theorem 1.1

import Mathlib

open MeasureTheory

namespace OnlineBeckFiala

/-- **Randomized online signing algorithm** (the online model of p.1 and of Theorem 1.1, p.2).
Altschuler, Tikhomirov, *Online Beck–Fiala Down to Logarithmic Sparsity*, arXiv:2607.14238
(held version, sha256 5a1529d2…), p.1: "the vectors are sequentially revealed to the algorithm which
must immediately and irrevocably choose signs ε1, . . . , εT … “online” refers to the algorithmic
restriction that εt is chosen just as a function of a1, . . . , at, while “oblivious” refers to the
fact that the vectors a1, . . . , aT … are fixed ahead of time".

An `OnlineSigner n` consists of a probability space `(Ω, P)` (the algorithm's private randomness)
and a sign rule `sign a t ω`, the sign `ε_t` chosen at time `t` on the input sequence `a` when the
randomness is `ω`, such that
* every sign is `1` or `-1` (`sign_pm`): a genuine signing, not a partial coloring;
* `sign a t` depends only on `a 0, …, a t` (`online`);
* every `sign a t` is measurable in `ω` (`meas`).

**Formalization Note.** Times are 0-based: the paper's `a₁, …, a_T` are `a 0, …, a (T-1)`, and the
input is a whole sequence `ℕ → (Fin n → ℝ)` of which only the first `T` entries matter (by `online`).
The adversary is oblivious because `P` does not depend on the input: the input is fixed first and
then the probability of an event in `ω` is computed. One shared sample space for all times is the
usual model of an algorithm with private random bits. -/
structure OnlineSigner (n : ℕ) where
  /-- The sample space of the algorithm's randomness. -/
  Ω : Type
  /-- Its σ-algebra. -/
  [mΩ : MeasurableSpace Ω]
  /-- The law of the randomness. -/
  P : Measure Ω
  /-- `P` is a probability measure. -/
  [prob : IsProbabilityMeasure P]
  /-- `sign a t ω` is the sign `ε_t` output at time `t` on input `a` with randomness `ω`. -/
  sign : (ℕ → (Fin n → ℝ)) → ℕ → Ω → ℝ
  /-- Signs are `±1`. -/
  sign_pm : ∀ a t ω, sign a t ω = 1 ∨ sign a t ω = -1
  /-- The sign at time `t` is a function of `a 0, …, a t` (and the randomness) only. -/
  online : ∀ (a a' : ℕ → (Fin n → ℝ)) (t : ℕ), (∀ s ≤ t, a s = a' s) → sign a t = sign a' t
  /-- Each sign is a random variable. -/
  meas : ∀ a t, Measurable (sign a t)

attribute [instance] OnlineSigner.mΩ OnlineSigner.prob

/-- The prefix sum `∑_{s ≤ t} ε_s a_s` (0-based: `s = 0, …, t`) produced by the algorithm `alg` on
input `a` with randomness `ω`. Its sup norm `‖·‖` (Mathlib's norm on `Fin n → ℝ`) is `‖·‖_∞`. -/
noncomputable def prefixSum {n : ℕ} (alg : OnlineSigner n) (a : ℕ → (Fin n → ℝ)) (t : ℕ)
    (ω : alg.Ω) : Fin n → ℝ :=
  ∑ s ∈ Finset.range (t + 1), alg.sign a s ω • a s

/-- The input class of Theorem 1.1, p.2: the first `T` vectors `a 0, …, a (T-1)` lie in `[-1, 1]^n`
and have at most `d` nonzero coordinates each. Later entries are unconstrained. -/
def IsSparseBox {n : ℕ} (d T : ℕ) (a : ℕ → (Fin n → ℝ)) : Prop :=
  ∀ s < T, (∀ i, |a s i| ≤ 1) ∧ (Finset.univ.filter (fun i => a s i ≠ 0)).card ≤ d

end OnlineBeckFiala


