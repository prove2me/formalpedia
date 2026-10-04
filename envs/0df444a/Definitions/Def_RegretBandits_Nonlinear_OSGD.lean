-- Prove2me | Definitions.Def_RegretBandits_Nonlinear_OSGD
-- name    : RegretBandits_Nonlinear_OSGD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T10:21:53.352219+00:00
-- url     : https://prove2.me/theorems/479f8d03-21a5-4865-864d-3beb7a9d9ccb
-- title:
--   OSGD (Online Stochastic Gradient Descent), two-point and one-point gradient estimates, pseudo-regret (Ch. 6)
-- statement:
--   This file fixes the algorithm and the performance measure of Sections 6.1–6.2. Points live in $\mathbb R^d$ with the Euclidean norm.
--
--   1. **Euclidean projection.** $y$ is a nearest point of $z$ in $\mathcal K$ if $y\in\mathcal K$ and $\|y-z\|\le\|w-z\|$ for all $w\in\mathcal K$, i.e. $y=\operatorname{argmin}_{w\in\mathcal K}\|w-z\|$.
--   2. **OSGD.** Given a set $\mathcal K$, a learning rate $\eta$ and gradient estimates $\widetilde g_t$, a run is a sequence $x_1,x_2,\dots$ with $x_1=(0,\dots,0)$ and, for every round $t\ge 1$,
--   $$x'_{t+1}=x_t-\eta\,\widetilde g_t(x_t),\qquad x_{t+1}=\operatorname*{argmin}_{y\in\mathcal K}\|y-x'_{t+1}\| .$$
--   3. **Two-point estimate (6.1).** For a loss $\ell_t$, a direction $S$ and $\delta>0$,
--   $$\widetilde g_t(x)=\frac{d}{2\delta}\big(\ell_t(x+\delta S)-\ell_t(x-\delta S)\big)S .$$
--   4. **One-point estimate (6.3).**
--   $$\widetilde g_t(x)=\frac{d}{\delta}\,\ell_t(x+\delta S)\,S .$$
--   5. **Pseudo-regret.** For a fixed loss sequence $\ell_1,\ell_2,\dots$ and random played points $X_t$,
--   $$\overline R_n=\mathbb E\sum_{t=1}^n\ell_t(X_t)-\min_{x\in\mathcal K}\sum_{t=1}^n\ell_t(x).$$
--   6. **Fair sign.** The law putting mass $1/2$ on $+1$ and on $-1$.
--
--   **Formalization Note** Rounds are numbered $t=1,2,\dots$; the value $x_0$ is never used. The projection is a predicate rather than a function; for a nonempty closed convex set it determines $x_{t+1}$ uniquely, so a run is determined by $\mathcal K$, $\eta$ and the estimates. The losses are oblivious (deterministic), so the book's $\min_x\mathbb E\sum_t\ell_t(x)$ is $\min_x\sum_t\ell_t(x)$; the minimum is written as the infimum over the subtype $\mathcal K$, which is the minimum when $\mathcal K$ is nonempty and compact and the losses are continuous, as in every theorem of the mission. The fair sign is used to pick the played point between $X_t^+$ and $X_t^-$ in Theorem 6.1.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 88 (pseudo-regret), p. 90 (OSGD box, Eq. (6.1)), p. 93 (Theorem 6.1: X~_t drawn at random between X+_t and X-_t), p. 94 (Eq. (6.3))

import Mathlib

open MeasureTheory

namespace RegretBandits.Nonlinear

/-- `y` is a Euclidean projection of `z` onto `K`: `y ∈ K` and `y` minimizes `‖w - z‖` over
`w ∈ K`, i.e. `y = argmin_{w ∈ K} ‖w - z‖` (step (3) of OSGD, p. 90). For a nonempty closed convex
`K ⊆ ℝ^d` the minimizer exists and is unique. -/
def IsNearestPoint {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d)))
    (z y : EuclideanSpace ℝ (Fin d)) : Prop :=
  y ∈ K ∧ ∀ w ∈ K, ‖y - z‖ ≤ ‖w - z‖

/-- `x` is a run of OSGD, Online Stochastic Gradient Descent (Bubeck, Cesa-Bianchi,
arXiv:1204.5721v2, p. 90, box), on the set `K` with learning rate `η`, driven by the gradient
estimates `g`: rounds are `t = 1, 2, …`; `x 1 = 0`; and for every round `t ≥ 1`, with
`g̃_t(x_t) = g t (x t)` the estimate observed at round `t`,
`x'_{t+1} = x_t - η g̃_t(x_t)` and `x_{t+1} = argmin_{y ∈ K} ‖y - x'_{t+1}‖`.
The value `x 0` is never used. -/
def IsOSGDRun {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (η : ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  x 1 = 0 ∧ ∀ t : ℕ, 1 ≤ t → IsNearestPoint K (x t - η • g t (x t)) (x (t + 1))

/-- The two-point gradient estimate (6.1), p. 90: for the loss `ℓ`, the direction `S` and the
point `x`, `g̃(x) = (d / (2δ)) (ℓ(x + δS) - ℓ(x - δS)) S`. -/
noncomputable def twoPointEstimate (d : ℕ) (δ : ℝ) (ℓ : EuclideanSpace ℝ (Fin d) → ℝ)
    (S x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ((d : ℝ) / (2 * δ) * (ℓ (x + δ • S) - ℓ (x - δ • S))) • S

/-- The one-point gradient estimate (6.3), p. 94: `g̃(x) = (d / δ) ℓ(x + δS) S`. -/
noncomputable def onePointEstimate (d : ℕ) (δ : ℝ) (ℓ : EuclideanSpace ℝ (Fin d) → ℝ)
    (S x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ((d : ℝ) / δ * ℓ (x + δ • S)) • S

/-- The pseudo-regret of Chapter 6 (p. 88) against a fixed (oblivious) loss sequence `ℓ`:
`R̄_n = E ∑_{t=1}^n ℓ_t(X_t) - min_{x ∈ K} ∑_{t=1}^n ℓ_t(x)`, where `X_t` is the point played at
round `t` (a random variable on `(Ω, P)`). Because the losses are deterministic,
`E ∑ ℓ_t(x) = ∑ ℓ_t(x)`. The minimum is written as the infimum over the subtype `K`; it is the
book's minimum whenever that minimum is attained (e.g. `K` nonempty and compact, `ℓ_t` continuous).
-/
noncomputable def pseudoRegret {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (K : Set (EuclideanSpace ℝ (Fin d))) (ℓ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (P : Measure Ω) (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (n : ℕ) : ℝ :=
  (∫ ω, ∑ t ∈ Finset.Icc 1 n, ℓ t (X t ω) ∂P) - ⨅ x : K, ∑ t ∈ Finset.Icc 1 n, ℓ t x

/-- The law of a fair random sign: `1/2` at `+1` and `1/2` at `-1`. Used for the choice of
the played point `X̃_t` "at random between `X⁺_t` and `X⁻_t`" in Theorem 6.1 (p. 93). -/
noncomputable def fairSign : Measure ℝ :=
  (1 / 2 : ENNReal) • (Measure.dirac (1 : ℝ) + Measure.dirac (-1 : ℝ))

end RegretBandits.Nonlinear


