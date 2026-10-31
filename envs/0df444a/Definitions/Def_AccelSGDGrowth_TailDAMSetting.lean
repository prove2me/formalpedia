-- Prove2me | Definitions.Def_AccelSGDGrowth_TailDAMSetting
-- name    : AccelSGDGrowth_TailDAMSetting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:32:34.985301+00:00
-- url     : https://prove2.me/theorems/aeaad9d8-face-45d3-b5b5-8c71e5a66155
-- title:
--   The setting of Theorem 5.1: DAM+ under the growth condition with the schedule (5.4)
-- statement:
--   On a measure space $(\Omega,\mathbb P)$ with filtration $(\mathcal G_k)$, the setting of Theorem 5.1 consists of:
--
--   1. $f\in\mathcal F(m,\mathcal L)$;
--   2. $\delta\ge0$, $\sigma^2\ge0$ and a tuning parameter $\alpha>0$;
--   3. positive weights $a_k>0$, $k\ge1$;
--   4. for every outcome $\omega$, the sequences $x_k(\omega),y_k(\omega),z_k(\omega),g_k(\omega)$ form a run of DAM+ (4.6) with weights $a_k$ and step sizes $\eta_k$;
--   5. the growth condition (2.5) with constants $\delta,\sigma^2$;
--   6. $x_1$ is $\mathcal G_1$-measurable with $\mathbb E\|x_1\|^2<\infty$;
--   7. $\eta_k=r_k$ from (5.4) with $\gamma_1=\sqrt{m\mathcal L}$, $\gamma_4=2\mathcal L(1+\delta)$, for every $k\ge1$;
--   8. $a_k/A_k=\sqrt{m\mathcal L}\,\eta_k$ for every $k\ge2$.
--
--   **Formalization Note** Item 8 is imposed for $k\ge2$ only: $a_1/A_1=1$ for every weight sequence, while $\sqrt{m\mathcal L}\,\eta_1\le1/2$ whenever $\alpha<\gamma_4$, so the printed condition "for all $k$" admits no positive weights (a correction). $\gamma_4/\alpha$ need not be an integer. The initial point may be random; $y_1$ is free (its coefficient $A_0/A_1$ is $0$) and $z_1=0$ is not assumed (it is forced).
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, Theorem 5.1, p.24, with (4.6), p.16, Definition 1.1, p.3, (2.5), p.6, and (5.4), p.22

import Definitions.Def_AccelSGDGrowth_ClassF
import Definitions.Def_AccelSGDGrowth_GrowthCondition
import Definitions.Def_AccelSGDGrowth_IsDAMPlusRun
import Definitions.Def_AccelSGDGrowth_scheduleR

open MeasureTheory

namespace AccelSGDGrowth

/-- The setting of Chen, Na, Kolar, arXiv:2006.06782v4, Theorem 5.1, p.24: DAM+ (4.6) under the
growth condition (Definition 1.1, (2.5)) with the schedule (5.4), `γ₁ = √(mL)`, `γ₄ = 2L(1+δ)`.

It bundles:
1. `f ∈ F(m, L)` (1.2);
2. `δ ≥ 0`, `σ² ≥ 0` (`sig2`), `α > 0`;
3. positive weights `a_k > 0` for `k ≥ 1`;
4. for every outcome `ω`, the sequences `x, y, z, g` at `ω` form a DAM+ run (4.6) with weights `a`
   and step sizes `η`;
5. the growth condition (2.5) with constants `δ, σ²` for `x, g` and the filtration `𝒢`;
6. `x_1` is `𝒢_1`-strongly measurable with `‖x_1‖²` integrable;
7. `η_k = r_k` of (5.4) for every `k ≥ 1`;
8. `a_k / A_k = √(mL) η_k` for every `k ≥ 2`.

**Formalization Note.** Item 8 is imposed for `k ≥ 2` only: at `k = 1`, `a_1/A_1 = 1`, while
`√(mL) η_1 ≤ 1/2` whenever `α < γ₄`, so the printed condition "for all k" admits no positive weight
sequence (a correction; `a_1 > 0` is free and only ratios enter the scheme). `γ₄/α` need not be an
integer. The initial point `x_1` may be random; `y_1` is free (its coefficient `A_0/A_1` is `0`) and
`z_1 = 0` is not assumed (it is forced by (4.6a) at `k = 1`). -/
def TailDAMSetting {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    (𝒢 : Filtration ℕ mΩ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (m L δ sig2 α : ℝ)
    (a η : ℕ → ℝ) (x y z g : ℕ → Ω → EuclideanSpace ℝ (Fin d)) : Prop :=
  ClassF m L f ∧ 0 ≤ δ ∧ 0 ≤ sig2 ∧ 0 < α ∧
  (∀ k : ℕ, 1 ≤ k → 0 < a k) ∧
  (∀ ω : Ω, IsDAMPlusRun m a η (fun k => x k ω) (fun k => y k ω) (fun k => z k ω)
    (fun k => g k ω)) ∧
  GrowthCondition μ 𝒢 f x g δ sig2 ∧
  StronglyMeasurable[𝒢 1] (x 1) ∧
  Integrable (fun ω => ‖x 1 ω‖ ^ 2) μ ∧
  (∀ k : ℕ, 1 ≤ k → η k = scheduleR (Real.sqrt (m * L)) (2 * L * (1 + δ)) α k) ∧
  (∀ k : ℕ, 2 ≤ k → a k / cumWeight a k = Real.sqrt (m * L) * η k)

end AccelSGDGrowth


