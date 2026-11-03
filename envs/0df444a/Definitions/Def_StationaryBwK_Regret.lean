-- Prove2me | Definitions.Def_StationaryBwK_Regret
-- name    : StationaryBwK_Regret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:51:13.960258+00:00
-- url     : https://prove2.me/theorems/ebf2933a-32a0-49b5-b08d-c2cc2c4da5bc
-- title:
--   No-regret guarantees (4), (5) of the subroutines and the explicit error of Lemma 5.1
-- statement:
--   Let $\rho=B/T$ and let $\mathcal L_t(a,i)$ be the Lagrangian of Algorithm 1. For functions $\mathrm{Reg}_{\max},\mathrm{Reg}_{\min}$ of the confidence $\delta$:
--
--   1. **Guarantee (4)** of the maximizing subroutine: for all $\delta>0$, with probability at least $1-\delta$, for all $T'\le T$,
--   $$\max_{a\in[K]}\sum_{t=1}^{T'}\mathcal L_t(a,I_t)-\sum_{t=1}^{T'}\mathcal L_t(A_t,I_t)\le\mathrm{Reg}_{\max}(\delta).$$
--   2. **Guarantee (5)** of the minimizing subroutine: for all $\delta>0$, with probability at least $1-\delta$, for all $T'\le T$,
--   $$\sum_{t=1}^{T'}\mathcal L_t(A_t,I_t)-\min_{i\in[d]\cup\{0\}}\sum_{t=1}^{T'}\mathcal L_t(A_t,i)\le\mathrm{Reg}_{\min}(\delta).$$
--   3. The Azuma–Hoeffding deviation $(1+1/\rho)\sqrt{2T\log(TK/\delta_3)}$ of the proof of Lemma 5.1.
--   4. The additive error
--   $$\mathrm{Err}(\delta)=\mathrm{Reg}_{\max}(\delta/3)+\mathrm{Reg}_{\min}(\delta/3)+\Big(1+\frac1\rho\Big)\sqrt{2T\log(3TK/\delta)}+\frac1\rho .$$
--
--   In the paper (4) is provided by EXP3.P and (5) by Hedge, with $\mathrm{Reg}$ defined only up to $O(\cdot)$; $\mathrm{Err}(\delta)$ is the error the proof of Lemma 5.1 actually produces with $\delta_1=\delta_2=\delta_3=\delta/3$.
--
--   **Formalization Note** "With probability at least $1-\delta$" is a measurable event of probability at least $1-\delta$ on which the inequality holds for every $T'\in\{0,\dots,T\}$. $T$ is fixed, so $\mathrm{Reg}$ is a function of $\delta$ only. `Real.log` and `Real.sqrt` are used; for $\delta_3>TK$ the logarithm is negative and the square root is $0$, a case in which $1-\delta_3<0$.
-- source:
--   G. Fikioris and É. Tardos, Approximately Stationary Bandits with Knapsacks, arXiv:2302.14686v2 [cs.LG] (preprint, 8 Jul 2023), https://arxiv.org/abs/2302.14686v2, §4, (4), p.8 and (5), p.9; proof of Lemma 5.1, p.16 (Azuma term, error 2Reg_max(T, δ/3) + Reg_min(T, δ/3)) and (9), p.15 (the 1/ρ)

import Mathlib
import Definitions.Def_StationaryBwK_Play

open MeasureTheory

namespace StationaryBwK

/-! # The no-regret guarantees (4), (5) of the subroutines and the explicit error term

Fikioris & Tardos, *Approximately Stationary Bandits with Knapsacks*, arXiv:2302.14686v2,
(4), p.8 and (5), p.9; the error is the one produced by the proof of Lemma 5.1, p.16.

**Formalization Note.** `Regmax, Regmin : ℝ → ℝ` are arbitrary functions of the confidence `δ`
(the horizon `T` is fixed). "With probability at least `1 − δ` it holds for all `T′`" is: there is
a measurable event `E` with `μ(E) ≥ 1 − δ` on which the inequality holds for every
`T′ ∈ {0, …, T}` (`T′ = 0` gives empty sums). -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Guarantee (4), p.8, of `Alg_max`: for all `δ > 0`, with probability at least `1 − δ`, for all
`T′ ≤ T`, `max_{a∈[K]} Σ_{t=1}^{T′} L_t(a, I_t) − Σ_{t=1}^{T′} L_t(A_t, I_t) ≤ Reg_max(T, δ)`. -/
def MaxRegretBound {d K : ℕ} (μ : Measure Ω) (T : ℕ) (B : ℝ) (R : ℕ → Ω → Fin K → ℝ)
    (C : ℕ → Ω → Fin d → Fin K → ℝ) (A : ℕ → Ω → Fin K) (I : ℕ → Ω → Option (Fin d))
    (Regmax : ℝ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ E : Set Ω, MeasurableSet E ∧ 1 - δ ≤ μ.real E ∧
    ∀ ω ∈ E, ∀ T' ≤ T,
      (⨆ a : Fin K, ∑ t ∈ Finset.Icc 1 T', lagr (rho T B) R C t ω a (I t ω)) -
        ∑ t ∈ Finset.Icc 1 T', lagr (rho T B) R C t ω (A t ω) (I t ω) ≤ Regmax δ

/-- Guarantee (5), p.9, of `Alg_min`: for all `δ > 0`, with probability at least `1 − δ`, for all
`T′ ≤ T`, `Σ_{t=1}^{T′} L_t(A_t, I_t) − min_{i∈[d]∪{0}} Σ_{t=1}^{T′} L_t(A_t, i) ≤ Reg_min(T, δ)`. -/
def MinRegretBound {d K : ℕ} (μ : Measure Ω) (T : ℕ) (B : ℝ) (R : ℕ → Ω → Fin K → ℝ)
    (C : ℕ → Ω → Fin d → Fin K → ℝ) (A : ℕ → Ω → Fin K) (I : ℕ → Ω → Option (Fin d))
    (Regmin : ℝ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ E : Set Ω, MeasurableSet E ∧ 1 - δ ≤ μ.real E ∧
    ∀ ω ∈ E, ∀ T' ≤ T,
      ∑ t ∈ Finset.Icc 1 T', lagr (rho T B) R C t ω (A t ω) (I t ω) -
        (⨅ j : Option (Fin d), ∑ t ∈ Finset.Icc 1 T', lagr (rho T B) R C t ω (A t ω) j) ≤
          Regmin δ

/-- The Azuma–Hoeffding deviation of p.16: `(1 + 1/ρ) √(2T log(TK/δ₃))`. -/
noncomputable def azumaTerm (T K : ℕ) (ρ δ₃ : ℝ) : ℝ :=
  (1 + 1 / ρ) * Real.sqrt (2 * T * Real.log (T * K / δ₃))

/-- The additive error that the proof of Lemma 5.1 (pp.15–16) yields with
`δ₁ = δ₂ = δ₃ = δ/3`: `Reg_max(T, δ/3) + Reg_min(T, δ/3) + (1 + 1/ρ)√(2T log(3TK/δ)) + 1/ρ`.
The paper absorbs the last two terms into `Reg_max(T, δ)`, which it defines only up to `O(·)`. -/
noncomputable def lagrErr (T K : ℕ) (ρ : ℝ) (Regmax Regmin : ℝ → ℝ) (δ : ℝ) : ℝ :=
  Regmax (δ / 3) + Regmin (δ / 3) + azumaTerm T K ρ (δ / 3) + 1 / ρ

end StationaryBwK


