-- Prove2me | Definitions.Def_ActiveSaddleSGD_Noise
-- name    : ActiveSaddleSGD_Noise
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:11.11702+00:00
-- url     : https://prove2.me/theorems/42e33f29-5621-4ed9-8447-38512adc2888
-- title:
--   The noise conditions: Assumptions 3 and 4, in the generalized conditional expectation
-- statement:
--   Let $E^-$ be a subspace of $\mathbb R^d$ and $\eta^-$ the orthogonal projection of $\eta$ on it.
--
--   **Assumption 3** requires, almost surely on the event $[x_n\to x^*]$:
--
--   1. $\mathbb E[\eta_{n+1}\mid\mathcal F_n]=0$ for all $n$;
--   2. $\limsup\mathbb E[\|\eta_{n+1}\|^4\mid\mathcal F_n]<+\infty$;
--   3. $\liminf\mathbb E[\|\eta^-_{n+1}\|\mid\mathcal F_n]>0$.
--
--   **Assumption 4** is the global form: there are deterministic $A,B>0$ such that almost surely, for all $n$,
--   $$
--   \mathbb E_n[\eta_{n+1}]=0,\qquad\mathbb E_n\|\eta_{n+1}\|^4\le B,\qquad\mathbb E_n\|\eta^-_{n+1}\|\ge A.
--   $$
--
--   The first condition makes the noise a martingale difference, the second bounds it, and the third says that it excites the directions of negative curvature, so that the iterates can leave the saddle.
--
--   **Formalization Note** Assumption 3 holds only on an event and no integrability of $\eta$ is assumed, while Mathlib's conditional expectation is $0$ on non-integrable functions. So moments are `condLExp`, the $[0,\infty]$-valued conditional expectation of extended norms. The mean is the generalized one (`CondMeanZeroAt`): with $G_K=\{\mathbb E[\|\eta_{n+1}\|\mid\mathcal F_n]\le K\}$, the variable $\mathbb 1_{G_K}\eta_{n+1}$ is integrable, and its conditional expectation must vanish on $G_K$, for every integer $K$. For an integrable $\eta_{n+1}$ this says exactly that $\mathbb E[\eta_{n+1}\mid\mathcal F_n]=0$ almost surely. In Assumption 4 the moment bound gives integrability, so Mathlib's conditional expectation is used directly.
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, Assumption 3, p.12, and Assumption 4, p.18

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ActiveSaddleSGD

variable {d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Assumption 3 i), p.12: the generalized
conditional mean of `ξ` given `m` vanishes at `ω`.

**Formalization Note** Assumption 3 holds only on an event and no integrability of the noise is
assumed, so Mathlib's `μ[ξ|m]`, which is `0` for a non-integrable `ξ`, would make the condition
vacuous. The mean is read through the `[0,∞]`-valued conditional expectation `condLExp`: with
`G_K = {E[‖ξ‖ | m] ≤ K}`, which is `m`-measurable, `1_{G_K} ξ` is integrable, and at each `ω ∈ G_K`
its conditional expectation must vanish. When `ξ` is integrable this is `μ[ξ|m] ω = 0` a.e.
Integer levels `K` suffice, because `G_K` increases with `K`. -/
def CondMeanZeroAt (μ : Measure Ω) (m : MeasurableSpace Ω)
    (ξ : Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) : Prop :=
  ∀ K : ℕ, ω ∈ {a | condLExp m μ (fun b => ‖ξ b‖ₑ) a ≤ K} →
    (μ[{a | condLExp m μ (fun b => ‖ξ b‖ₑ) a ≤ K}.indicator ξ | m]) ω = 0

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Assumption 3, p.12: almost surely on the event
`[x_n → x*]`, i) `E[η_{n+1}|𝓕_n] = 0` for all `n`, ii) `limsup E[‖η_{n+1}‖⁴|𝓕_n] < +∞`,
iii) `liminf E[‖η⁻_{n+1}‖|𝓕_n] > 0`, where `η⁻` is the orthogonal projection on `Eneg = E⁻`.

**Formalization Note** The moments are `condLExp` of extended norms, so they are `[0,∞]`-valued and
need no integrability; `limsup`, `liminf` are taken in `ℝ≥0∞`. Clause i) is `CondMeanZeroAt`. -/
def Assumption3 (μ : Measure Ω) (ℱ : Filtration ℕ mΩ)
    (x η : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (xs : EuclideanSpace ℝ (Fin d))
    (Eneg : Submodule ℝ (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n => x n ω) atTop (𝓝 xs) →
    (∀ n, CondMeanZeroAt μ (ℱ n) (η (n + 1)) ω) ∧
    limsup (fun n => condLExp (ℱ n) μ (fun a => ‖η (n + 1) a‖ₑ ^ 4) ω) atTop < ⊤ ∧
    0 < liminf (fun n => condLExp (ℱ n) μ (fun a => ‖Eneg.starProjection (η (n + 1) a)‖ₑ) ω) atTop

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Assumption 4, p.18: there are deterministic
`A, B > 0` such that almost surely, for all `n`, `E_n[η_{n+1}] = 0`, `E_n‖η_{n+1}‖⁴ ≤ B` and
`E_n‖η⁻_{n+1}‖ ≥ A`.

**Formalization Note** The bound on `condLExp` puts `η_{n+1}` in `L⁴`, so Mathlib's `μ[η (n+1)|ℱ n]`
is a genuine conditional expectation here. -/
def Assumption4 (μ : Measure Ω) (ℱ : Filtration ℕ mΩ)
    (η : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (Eneg : Submodule ℝ (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ A B : ℝ≥0, 0 < A ∧ 0 < B ∧ ∀ᵐ ω ∂μ, ∀ n,
    (μ[η (n + 1) | ℱ n]) ω = 0 ∧
    condLExp (ℱ n) μ (fun a => ‖η (n + 1) a‖ₑ ^ 4) ω ≤ B ∧
    (A : ℝ≥0∞) ≤ condLExp (ℱ n) μ (fun a => ‖Eneg.starProjection (η (n + 1) a)‖ₑ) ω

end ActiveSaddleSGD


