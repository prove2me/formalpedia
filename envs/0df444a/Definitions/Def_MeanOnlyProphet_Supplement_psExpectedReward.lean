-- Prove2me | Definitions.Def_MeanOnlyProphet_Supplement_psExpectedReward
-- name    : MeanOnlyProphet_Supplement_psExpectedReward
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:27:13.228492+00:00
-- url     : https://prove2.me/theorems/8dfb855e-7451-48fe-a907-23c91b7c5120
-- title:
--   Expected reward $\mathbb E[\mathrm{ALG}]$ of the prophet-secretary threshold rule
-- statement:
--   Let $n\ge1$ and let $\mu_1,\dots,\mu_n$ be probability laws on $\mathbb R$. In the **prophet secretary** model the values $X_1,\dots,X_n$ are independent with $X_i\sim\mu_i$ (the laws may differ), and each $X_i$ receives an arrival time $t_i$ drawn uniformly from $[0,1]$, independently of everything else; values are seen in increasing order of arrival time. The prophet's benchmark is
--   $$
--   \mathbb E[X^*]=\mathbb E\Big[\max_{1\le i\le n}X_i\Big].
--   $$
--   Given a threshold function $\theta$, the **non-adaptive threshold rule** accepts the first arriving value with
--   $$
--   X_i>\mathbb E[X^*]\cdot\theta(t_i),
--   $$
--   and receives $0$ if no value is accepted. The definition provides $\mathbb E[X^*]$, the sample law, the rule's reward $\mathrm{ALG}$ at a sample point (for a general scale $m$ in place of $\mathbb E[X^*]$), and its expectation $\mathbb E[\mathrm{ALG}]$.
--
--   These are the objects of Theorems 1.2, 4.2 and C.13: the rule uses only $n$ and $\mathbb E[X^*]$; under the paper's normalization $\mathbb E[X^*]=1$ the threshold is $\theta(t_i)$ itself.
--
--   **Formalization Note** The sample space is $\mathbb R^n\times\mathbb R^n$ (values, then arrival times) with law `(Measure.pi μ).prod (Measure.pi fun _ => volume.restrict (Icc 0 1))`. Acceptance is strict. Ties between arrival times, which have probability zero, are broken by the least index. There is no forced acceptance. The expectations are Bochner integrals, which are the true expectations for nonnegative values with finite means.
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), §2, p.5 (PDF p.6); §4.1, p.12 (PDF p.13); App. C.2, p.48 (PDF p.49)

import Mathlib
import Definitions.Def_SamuelCahnProphet_Median_Setting

open MeasureTheory

namespace MeanOnlyProphet.Supplement

/-- **The prophet's benchmark `E[X*]` for independent, not necessarily identical values.** Feng, Jin,
Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…), §2, p.5
(PDF p.6): "Let X1, . . . , Xn be independent nonnegative random variables. Write X∗ = max1≤i≤n {Xi}.
… In the prophet secretary setting, their distributions may differ".

`psProphetMean μ = ∫ max_i x_i d(μ_1 ⊗ ⋯ ⊗ μ_n)(x)`.

**Formalization Note.** The values are the coordinates of `x : Fin n → ℝ` under the product law
`Measure.pi μ`; the maximum is the published `SamuelCahnProphet.Median.maxX`. The expectation is a
Bochner integral: it is the true `E[X*]` whenever every `μ i` has a finite mean. `n ≥ 1` is `NeZero n`. -/
noncomputable def psProphetMean {n : ℕ} [NeZero n] (μ : Fin n → Measure ℝ) : ℝ :=
  ∫ x, SamuelCahnProphet.Median.maxX (fun (i : Fin n) (y : Fin n → ℝ) => y i) x ∂(Measure.pi μ)

/-- **Sample law of the prophet-secretary model.** Feng, Jin, Wu, Xiang, arXiv:2610.24711 (held
version), §2, p.5 (PDF p.6): "we represent the random order of variables by independent arrival times
ti drawn uniformly from [0, 1] for variable Xi , independent of other variables."

**Formalization Note.** The sample space is `(Fin n → ℝ) × (Fin n → ℝ)`: the values `x`, then the
arrival times `t`; the law is `Measure.pi μ` times `n` independent uniform laws on `[0,1]`. -/
noncomputable def psSampleMeasure {n : ℕ} (μ : Fin n → Measure ℝ) :
    Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (Measure.pi μ).prod (Measure.pi fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))

/-- The set of variables that pass their threshold at their own arrival time:
`{ j : m · θ(t_j) < x_j }` (strict acceptance). -/
noncomputable def psPassing (θ : ℝ → ℝ) (m : ℝ) {n : ℕ} (x t : Fin n → ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j => m * θ (t j) < x j

/-- The passing variables with the earliest arrival time among the passing ones. -/
noncomputable def psFirst (θ : ℝ → ℝ) (m : ℝ) {n : ℕ} (x t : Fin n → ℝ) : Finset (Fin n) := by
  classical
  exact (psPassing θ m x t).filter fun j => ∀ k ∈ psPassing θ m x t, t j ≤ t k

/-- **Reward `ALG` of the prophet-secretary threshold rule at a sample point.** Feng, Jin, Wu, Xiang,
arXiv:2610.24711 (held version), §2, p.5 (PDF p.6): "A non-adaptive deterministic threshold algorithm
chooses a decreasing function θ before seeing any variables and accepts the first value satisfying
Xi > θ(ti ). … Its reward is ALG, with reward zero if it accepts nothing."

Values are inspected in increasing order of arrival time; the rule accepts the first one with
`x_j > m · θ(t_j)` and receives `x_j`, or `0` if no value passes.

**Formalization Note.** Ties in arrival times (probability zero) are broken by the least index. There
is no forced acceptance. The scale `m` is the known mean `E[X*]` (`= 1` under the paper's
normalization). -/
noncomputable def psReward (θ : ℝ → ℝ) (m : ℝ) {n : ℕ} (x t : Fin n → ℝ) : ℝ :=
  if h : (psFirst θ m x t).Nonempty then x ((psFirst θ m x t).min' h) else 0

/-- **Expected reward `E[ALG]` of the prophet-secretary threshold rule with thresholds
`E[X*] · θ(t_i)`.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711 (held
version, sha256 c68bfec4…), §2, p.5 (PDF p.6) and §4.1, p.12 (PDF p.13).

`psExpectedReward θ μ = E[ALG]` for independent values `X_i ∼ μ_i`, independent uniform arrival times
`t_i ∈ [0,1]`, and the rule "accept the first arrival with `X_i > E[X*] · θ(t_i)`, else receive 0".

**Formalization Note.** The expectation is the Bochner integral over `psSampleMeasure μ`; the scale is
`psProphetMean μ`, so the rule reads the laws only through `E[X*]`. For nonnegative values with finite
means the reward lies between `0` and `max_i x_i`. -/
noncomputable def psExpectedReward (θ : ℝ → ℝ) {n : ℕ} [NeZero n] (μ : Fin n → Measure ℝ) : ℝ :=
  ∫ p, psReward θ (psProphetMean μ) p.1 p.2 ∂(psSampleMeasure μ)

end MeanOnlyProphet.Supplement


