-- Prove2me | Definitions.Def_MeanOnlyProphet_expectedReward
-- name    : MeanOnlyProphet_expectedReward
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:59.376132+00:00
-- url     : https://prove2.me/theorems/a4a6eb72-6268-47a7-8c8f-fd2f21c8cde6
-- title:
--   Expected reward $\mathbb E[\mathrm{ALG}]$ of the randomly shifted threshold rule
-- statement:
--   Fix a threshold function $\theta$, a law $\mu$ and $n\ge1$. The **randomly shifted threshold rule** draws $U$ uniformly from $[0,1]$, independently of the i.i.d. values $X_1,\dots,X_n\sim\mu$, assigns the $i$-th arrival the virtual time $\sigma_i=(i-U)/n$, and accepts the first value with
--   $$
--   X_i>\mathbb E[X^*]\cdot\theta\!\left(\frac{i-U}{n}\right);
--   $$
--   if the first $n-1$ values are rejected it accepts $X_n$. Its reward $\mathrm{ALG}$ is the accepted value, and the definition is its expectation $\mathbb E[\mathrm{ALG}]$.
--
--   The definition also provides the sample law (values, then $U$), the stopping index for a general scale $m$ in place of $\mathbb E[X^*]$, and the reward at a sample point. The rule uses only $n$ and $\mathbb E[X^*]$.
--
--   **Formalization Note** The sample space is $\mathbb R^n\times\mathbb R$ with law `(Measure.pi fun _ => μ).prod (volume.restrict (Icc 0 1))`. Arrivals are 0-based: Lean's index $j$ is the paper's $i=j+1$, so $\sigma=((j+1)-U)/n$, computed in $\mathbb R$. Acceptance is strict, and the last arrival is always accepted when reached. The scale is `prophetMean μ n`.
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), §3.4, p.11 (PDF p.12); App. A.2, p.28 (PDF p.29)

import Mathlib
import Definitions.Def_MeanOnlyProphet_prophetMean

open MeasureTheory

namespace MeanOnlyProphet

/-- **Sample space of the randomly shifted rule.** Feng, Jin, Wu, Xiang, *Mean-only Prophet
Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…), §3.4, p.11 (PDF p.12): "Draw U
uniformly from [0, 1], independently of the values."

The law of `(X_1, …, X_n, U)`: `n` i.i.d. draws from `μ`, independent of `U` uniform on `[0,1]`.

**Formalization Note.** The sample space is `(Fin n → ℝ) × ℝ` (values, then the shift `U`), with
measure `(Measure.pi fun _ => μ).prod (volume.restrict (Set.Icc 0 1))`. -/
noncomputable def sampleMeasure (μ : Measure ℝ) (n : ℕ) : Measure ((Fin n → ℝ) × ℝ) :=
  (Measure.pi fun _ : Fin n => μ).prod (volume.restrict (Set.Icc (0 : ℝ) 1))

/-- **Stopping index of the randomly shifted threshold rule.** Feng, Jin, Wu, Xiang, *Mean-only
Prophet Inequalities*, arXiv:2610.24711 (held version), §3.4, p.11 (PDF p.12): "We accept the first
value satisfying Xi > E[X∗] · θ((i−U)/n). If the first n − 1 variables are rejected, we accept Xn."

`stopIdx θ m n x u` is the least index `j` with `m · θ(((j+1) − u)/n) < x_j`, or the last index if
there is none.

**Formalization Note.** Indices are 0-based: Lean's `j : Fin n` is the paper's arrival `i = j + 1`, so
the virtual arrival time `σ_i = (i − U)/n` is `((j : ℝ) + 1 - u) / n`, computed in `ℝ`. Acceptance is
strict (`<`) and the last arrival (`⊤ : Fin n`) is always accepted when reached. The scale `m` is the
known mean `E[X*]`; the rule reads the law only through `m`. -/
noncomputable def stopIdx (θ : ℝ → ℝ) (m : ℝ) (n : ℕ) [NeZero n] (x : Fin n → ℝ) (u : ℝ) : Fin n := by
  classical
  exact (Finset.univ.filter
    (fun j : Fin n => m * θ (((j : ℝ) + 1 - u) / n) < x j ∨ j = ⊤)).min' ⟨⊤, by simp⟩

/-- **Reward `ALG` of the randomly shifted threshold rule**: the value accepted at `stopIdx`.
Feng, Jin, Wu, Xiang, arXiv:2610.24711 (held version), §2, p.5 and §3.4, p.11. The rule always
accepts some value (the last one is forced), so the reward is `x` at the stopping index. -/
noncomputable def reward (θ : ℝ → ℝ) (m : ℝ) (n : ℕ) [NeZero n] (x : Fin n → ℝ) (u : ℝ) : ℝ :=
  x (stopIdx θ m n x u)

/-- **Expected reward `E[ALG]` of the randomly shifted threshold rule with thresholds
`E[X*] · θ((i − U)/n)`.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711
(held version, sha256 c68bfec4…), §3.4, p.11 (PDF p.12), Theorem 3.5's algorithm.

`expectedReward θ μ n = E[ALG]` where the values are i.i.d. `μ`, `U` is uniform on `[0,1]`, and the
scale is `m = prophetMean μ n`.

**Formalization Note.** The expectation is the Bochner integral over `sampleMeasure μ n`. For
nonnegative values with finite mean the reward lies between `0` and `max_i x_i`, so it is integrable. -/
noncomputable def expectedReward (θ : ℝ → ℝ) (μ : Measure ℝ) (n : ℕ) [NeZero n] : ℝ :=
  ∫ p, reward θ (prophetMean μ n) n p.1 p.2 ∂(sampleMeasure μ n)

end MeanOnlyProphet


