-- Prove2me | Definitions.Def_FewExperts_hedgeWeights
-- name    : FewExperts_hedgeWeights
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:13.987396+00:00
-- url     : https://prove2.me/theorems/f201b4f2-e199-49e5-aab8-dd3173120b06
-- title:
--   Hedge (multiplicative weights) on gain streams, rate $\sqrt{\ln n/T}$
-- statement:
--   **Hedge** with learning rate $\eta$ on $n$ gain streams $x_1,\dots,x_n$, where $x_j(u)$ is the gain of stream $j$ at round $u\ge1$. At round $t$ it predicts the weights
--
--   $$
--   w_t(j)=\frac{\exp\bigl(\eta\sum_{u=1}^{t-1}x_j(u)\bigr)}{\sum_{k}\exp\bigl(\eta\sum_{u=1}^{t-1}x_k(u)\bigr)} ,
--   $$
--
--   and its gain at round $t$ is $\sum_j w_t(j)\,x_j(t)$. The rate used with horizon $T$ is $\eta=\sqrt{\ln n/T}$.
--
--   A stream may be the gain sequence of an expert or of an algorithm. This lets the same definition cover Hedge on the sampled experts (Algorithm 4) and the two-expert Hedge on a baseline and an expert (Algorithm 3).
--
--   **Formalization Note** For $T=0$ the rate is $0$ (Lean's $x/0=0$).
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), Lemma 2, p.14 (PDF p.15); Algorithm 4, line 6, p.20 (PDF p.21)

import Mathlib

namespace FewExperts

/-- **Hedge (multiplicative weights) on gain streams.**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), Lemma 2, p.14 (PDF 15) ("Hedge algorithm (multiplicative weights) [FS97, Section
2]"), used with rate `√(ln m / T)` in Algorithm 4, line 6, p.20.

`hedgeWeights η X j = exp(η X_j) / ∑_k exp(η X_k)`: the exponential weights with learning rate
`η` on the vector `X` of cumulative gains of `n` streams. -/
noncomputable def hedgeWeights {n : ℕ} (η : ℝ) (X : Fin n → ℝ) (j : Fin n) : ℝ :=
  Real.exp (η * X j) / ∑ k, Real.exp (η * X k)

/-- Hedge's prediction at round `t ≥ 1` on the gain streams `x j u` (`j` a stream, `u ≥ 1` a
round): the weights `hedgeWeights η` on the cumulative gains `∑_{u=1}^{t-1} x j u` of the rounds
before `t`.

**Formalization Note** The experts of Hedge are arbitrary `[0, 1]`-valued gain streams, so that
an *algorithm* can be one of them (the two-expert Hedge on `B` and `i*` of Algorithm 3, p.16). -/
noncomputable def hedgeAt {n : ℕ} (η : ℝ) (x : Fin n → ℕ → ℝ) (t : ℕ) : Fin n → ℝ :=
  hedgeWeights η (fun j => ∑ u ∈ Finset.Ico 1 t, x j u)

/-- Hedge's (mixed) gain at round `t`: `∑_j w_t(j) x_j(t)`. -/
noncomputable def hedgeGain {n : ℕ} (η : ℝ) (x : Fin n → ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ j, hedgeAt η x t j * x j t

/-- The learning rate `√(ln n / T)` of Hedge with `n` experts over the horizon `T` (Algorithm 4,
line 6, p.20, with `n = m`).

**Formalization Note** `ln` is `Real.log`. For `T = 0` the rate is `0` (Lean's `x / 0 = 0`). -/
noncomputable def hedgeRate (n T : ℕ) : ℝ := Real.sqrt (Real.log n / T)

end FewExperts


