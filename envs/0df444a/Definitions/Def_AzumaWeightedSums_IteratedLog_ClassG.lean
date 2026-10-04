-- Prove2me | Definitions.Def_AzumaWeightedSums_IteratedLog_ClassG
-- name    : AzumaWeightedSums_IteratedLog_ClassG
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:06:34.498497+00:00
-- url     : https://prove2.me/theorems/89bee0d7-2dfe-4455-accf-743e0e8104fc
-- title:
--   Martingale differences and class [G] with $\tau(x_n)\le 1$
-- statement:
--   Let $(\Omega,\mathfrak A,P)$ be a probability space and $(\mathfrak A_n)_{n\ge 0}$ an increasing family of sub-$\sigma$-fields of $\mathfrak A$. A sequence of real random variables $(x_n)_{n\ge 1}$ is a **martingale-difference sequence** with respect to $(\mathfrak A_n)$ if, for every $n\ge 1$, the variable $x_n$ is $\mathfrak A_n$-measurable and integrable, and
--   $$
--   E\{x_n\mid\mathfrak A_{n-1}\}=0\quad\text{a.s.}
--   $$
--
--   The sequence belongs to **class [G] with $\tau(x_n)\le 1$** if it is a martingale-difference sequence, $\exp(t x_n)$ is integrable for every $n\ge1$ and every real $t$, and for every $n\ge 1$ and every real $t$
--   $$
--   E\{\exp(t x_n)\mid\mathfrak A_{n-1}\}\le \exp(t^2/2)\quad\text{a.s.}
--   $$
--   In Azuma's notation, property [G] asks for nonnegative constants $c_n$ with $E\{\exp(tx_n)\mid\mathfrak A_{n-1}\}\le\exp(c_n^2t^2/2)$ a.s. for every real $t$, and $\tau(x_n)$ is the smallest such $c_n$; the condition $\tau(x_n)\le 1$ says exactly that $c_n=1$ is admissible.
--
--   Class [G] is a conditional sub-Gaussian condition on the increments of a martingale. It contains every martingale-difference sequence with $|x_n|\le 1$ a.s. (Remark 1 of the paper), and also unbounded, Gaussian-like increments.
--
--   **Formalization Note** The sequence is indexed from $1$ and $x_0$ is ignored. The paper fixes $\mathfrak A_0=\{\emptyset,\Omega\}$; here $\mathfrak A_0$ is an arbitrary sub-$\sigma$-field, so the paper's case is an instance and every theorem stated over this class is at least as strong as the paper's. The quantifier order is the paper's: for each $t$, the inequality holds almost surely. The integrability of $\exp(tx_n)$ is required explicitly, because Lean's conditional expectation of a non-integrable function is $0$, which would make the bound vacuous.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), https://doi.org/10.2748/tmj/1178243286, p. 357, §1, property [G] (with τ(x_n) ≦ 1 as in Lemma 2, p. 358, and Theorem 2, p. 362)

import Mathlib

open MeasureTheory

namespace AzumaWeightedSums.IteratedLog

/-- Martingale differences with respect to the filtration `ℱ` (Azuma 1967, §1, p. 357),
indexed from `1` as in the paper (`x 0` is ignored): for every `n ≥ 1`, `x n` is
`ℱ n`-measurable and integrable, and `E{x_n | ℱ_{n-1}} = 0` almost surely. -/
def IsMartingaleDiff {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ mΩ) (x : ℕ → Ω → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    StronglyMeasurable[ℱ n] (x n) ∧ Integrable (x n) μ ∧ μ[x n | ℱ (n - 1)] =ᵐ[μ] 0

/-- Property [G] of Azuma 1967 (§1, p. 357) with `τ(x_n) ≤ 1` for all `n`, i.e. with the
admissible constant `c_n = 1`: `(x_n)` is a martingale-difference sequence for `ℱ`, each
`exp (t x_n)` is integrable, and for every `n ≥ 1` and every real `t`,
`E{exp(t x_n) | ℱ_{n-1}} ≤ exp(t²/2)` almost surely. -/
def IsCondSubgaussianOne {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ mΩ) (x : ℕ → Ω → ℝ) : Prop :=
  IsMartingaleDiff μ ℱ x ∧
  (∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, Integrable (fun ω => Real.exp (t * x n ω)) μ) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ t : ℝ,
    μ[fun ω => Real.exp (t * x n ω) | ℱ (n - 1)] ≤ᵐ[μ] fun _ => Real.exp (t ^ 2 / 2))

end AzumaWeightedSums.IteratedLog


