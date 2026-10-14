-- Prove2me | Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem
-- name    : SmoothAmbEq_Gaussian_InsideSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:19.693971+00:00
-- url     : https://prove2.me/theorems/68915d4b-73e1-4810-9d28-08bc1fff872f
-- title:
--   (5.2)–(5.3), (C.1), Definition 5.1, (5.7) — the inside system started at (t, x, β), admissible strategies Π, the generator
-- statement:
--   This file builds the inside system of §5.1 (p. 15), the admissible class of Definition 5.1 (p. 15) and the generator (5.7) (p. 16).
--
--   Fix a probability space $(\Omega,\mathcal F,\mathbb P)$ carrying a standard Brownian motion $W$. For a hypothetical drift value $z\in\mathbb R$ and a start $(t,x,\beta)$ with $t\ge0$:
--
--   1. **Posterior mean.** $\beta^z$ is given explicitly by (C.1), p. 25:
--   $$\beta^z_s=\zeta(s)\Big[\zeta(t)^{-1}\beta+z\sigma^{-2}(s-t)+\sigma^{-1}(W_s-W_t)\Big],\qquad s\ge t,$$
--   the unique solution of $d\beta^z_s=\frac{\zeta(s)}{\sigma^2}\big[(z-\beta^z_s)ds+\sigma dW_s\big]$ (5.3) with $\beta^z_t=\beta$.
--   2. **Strategies.** A strategy is a feedback function $\pi:(t,x,\beta)\mapsto\pi(t,x,\beta)$ ((4.1), p. 12).
--   3. **Wealth.** $X$ is a strong solution of (5.2) on $[t,T]$ started at $X_t=x$ if it is adapted to the natural filtration of the increments $W_{t+\cdot}-W_t$ (up to null sets), has a.s. continuous paths, $u\mapsto\pi(u,X_u,\beta^z_u)$ is a.s. square integrable on $[t,T]$, and for every $s\in[t,T]$, almost surely,
--   $$X_s=x+\int_t^s\big[rX_u+\pi(u,X_u,\beta^z_u)(z-r)\big]du+\int_t^s\pi(u,X_u,\beta^z_u)\,\sigma\,dW_u .$$
--   4. **Admissibility (Definition 5.1).** $\pi\in\Pi$ if (i) for every $z\in\mathbb R$ and every start $(t,x,\beta)\in[0,T]\times\mathbb R^2$ the equation above has a strong solution, unique up to indistinguishability; and (ii) for every $(t,x,\beta)\in[0,T)\times\mathbb R^2$, $\epsilon>0$ and $\rho>2$ there are $\delta>2$, $\tilde t\in(t,T)$ and $C>0$ such that for every $z$ and $s\in[t,\tilde t]$
--   $$\mathbb E\big[e^{-\delta k e^{r(T-s)}X^{z,\pi}_s}\big]\le Ce^{\epsilon z^2},\qquad \mathbb E\big[|\pi(s,X^{z,\pi}_s,\beta^z_s)|^\rho\big]\le Ce^{\epsilon z^2}\qquad(5.4)\text{–}(5.5),$$
--   for the wealth started at $(t,x,\beta)$.
--   5. **Generator (5.7).** For $f(t,x,\beta)$ and an action value $p$,
--   $$\mathcal A^{z,p}f=f_t+[rx+p(z-r)]f_x+\frac{\zeta}{\sigma^2}(z-\beta)f_\beta+\tfrac12\sigma^2p^2f_{xx}+\tfrac12\frac{\zeta^2}{\sigma^2}f_{\beta\beta}+p\zeta f_{x\beta};$$
--   $\mathcal A^{z,\pi}f(t,x,\beta)$ is this with $p=\pi(t,x,\beta)$.
--   6. **Martingales on an interval.** A process $(Y_s)_{s\in[t_0,T_1]}$ is a martingale for the filtration of the increments after $t_0$ if each $Y_s$ is integrable and adapted and $\int_AY_{s'}d\mathbb P=\int_AY_sd\mathbb P$ for $t_0\le s\le s'\le T_1$ and every event $A$ of the filtration at time $s$.
--
--   These are the stochastic objects in which the equilibrium notion and Appendix G are stated.
--
--   **Formalization Note** The paper's conditional expectations $\mathbb E[\,\cdot\mid X^{z,\pi}_t=x,\beta^z_t=\beta]$ are encoded, as in Appendices B–G (Markov property), by starting the inside system at $(t,x,\beta)$ and driving it with the increments $W_s-W_t$. Mathlib's Brownian motion is indexed by $\mathbb R_{\ge0}$, so $W_s$ means $W$ at `s.toNNReal`; the stochastic integral is the published `EthierKurtz.HasBrownianItoIntegral` against $v\mapsto W_{t+v}-W_t$ and its natural filtration, with the integrand set to $0$ after $T$ and on the null set of paths where it is not square integrable (that definition requires square integrability for every path). Definition 5.1(i) says "SDE (5.1) has a unique strong solution"; every quantity the paper uses is computed on the inside system (5.2)–(5.3), so (i) is stated there, for every $z$ and every start (disclosed reformulation, paper.md slip 8; at $t=T$ it holds trivially). Condition (ii) is required for every solution, which under (i) is the same as for the solution. Expectations of nonnegative quantities are lower Lebesgue integrals. $f_t$ in (5.7) is the derivative within $[0,T]$ (one-sided at the endpoints); $f_x,f_\beta$ and the second derivatives are ordinary derivatives of the partial maps.
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, pp. 12, 15–16, 25, (4.1), (5.2)–(5.3), Definition 5.1, (5.7), (C.1)

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_SmoothAmbEq_Gaussian_Model

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SmoothAmbEq.Gaussian

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Brownian increments after time `t ≥ 0`: `v ↦ W_{t+v} - W_t`, indexed by the elapsed
time `v ∈ ℝ≥0`. -/
noncomputable def shiftBM (W : ℝ≥0 → Ω → ℝ) (t : ℝ) : ℝ≥0 → Ω → ℝ :=
  fun v ω => W (t.toNNReal + v) ω - W t.toNNReal ω

/-- The natural filtration of the increments after `t`: at elapsed time `v` it is generated by
`W_{t+u} - W_t`, `u ≤ v`. -/
noncomputable def shiftFiltration (W : ℝ≥0 → Ω → ℝ) (t : ℝ) : ℝ≥0 → MeasurableSpace Ω :=
  fun v => ⨆ (u : ℝ≥0) (_ : u ≤ v), MeasurableSpace.comap (shiftBM W t u) (by infer_instance)

/-- The posterior-mean process `β^z` of the inside system started at `β^z_t = β`, given
explicitly by (C.1), p. 25:
`β^z_s = ζ(s)[ζ(t)⁻¹β + zσ⁻²(s - t) + σ⁻¹(W_s - W_t)]`, `s ≥ t ≥ 0`.
It is the unique solution of the linear SDE (5.3). -/
noncomputable def betaZ (M : Model) (W : ℝ≥0 → Ω → ℝ) (z t β s : ℝ) (ω : Ω) : ℝ :=
  M.ζ s * (β / M.ζ t + z * (s - t) / M.σ ^ 2 + (W s.toNNReal ω - W t.toNNReal ω) / M.σ)

/-- A feedback trading strategy `π : (t, x, β) ↦ π(t, x, β)` ((4.1), p. 12): the amount of
wealth held in the stock at time `t`, wealth `x`, posterior mean `β`. -/
abbrev Strategy := ℝ → ℝ → ℝ → ℝ

open Classical in
/-- The diffusion integrand `π(t+v, X_{t+v}, β^z_{t+v}) σ` of (5.2), in elapsed time `v`, cut
off to `0` after the horizon (`t + v > T`) and on the null set of paths where
`u ↦ π(u, X_u, β^z_u)` is not square integrable on `[t, T]`. -/
noncomputable def wealthIntegrand (M : Model) (W : ℝ≥0 → Ω → ℝ) (π : Strategy)
    (z t β : ℝ) (X : ℝ → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun v ω =>
    if t + (v : ℝ) ≤ M.T ∧
        IntervalIntegrable (fun u => (π u (X u ω) (betaZ M W z t β u ω)) ^ 2) volume t M.T then
      π (t + v) (X (t + v) ω) (betaZ M W z t β (t + v) ω) * M.σ
    else 0

/-- `X` is a strong solution on `[t, T]` of the inside wealth equation (5.2) under the
hypothetical drift `z`, started at `X_t = x`, `β^z_t = β` (with `β^z` given by (C.1)):
`X` is adapted to the (augmented) natural filtration of `W_{t+·} - W_t`, has a.s. continuous
paths on `[t, T]`, `u ↦ π(u, X_u, β^z_u)` is a.s. square integrable on `[t, T]`, and for every
`s ∈ [t, T]`, almost surely,
`X_s = x + ∫_t^s [r X_u + π(u, X_u, β^z_u)(z - r)] du + ∫_t^s π(u, X_u, β^z_u) σ dW_u`,
the stochastic integral being an Itô integral (`EthierKurtz.HasBrownianItoIntegral`) against
the shifted Brownian motion. -/
def IsInsideWealth (M : Model) (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (π : Strategy)
    (z t x β : ℝ) (X : ℝ → Ω → ℝ) : Prop :=
  (∀ s ∈ Icc t M.T, AEStronglyMeasurable[shiftFiltration W t (s - t).toNNReal] (X s) P) ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun s => X s ω) (Icc t M.T)) ∧
  (∀ᵐ ω ∂P, IntervalIntegrable
    (fun u => (π u (X u ω) (betaZ M W z t β u ω)) ^ 2) volume t M.T) ∧
  ∃ I : ℝ≥0 → Ω → ℝ,
    EthierKurtz.HasBrownianItoIntegral P (shiftFiltration W t) (shiftBM W t)
      (wealthIntegrand M W π z t β X) I ∧
    ∀ s ∈ Icc t M.T, ∀ᵐ ω ∂P,
      X s ω = x + (∫ u in t..s, (M.r * X u ω + π u (X u ω) (betaZ M W z t β u ω) * (z - M.r)))
        + I (s - t).toNNReal ω

/-- Condition (i) of Definition 5.1, read on the inside system (paper.md, slip 8): for every
drift `z ∈ ℝ` and every start `(t, x, β) ∈ [0, T] × ℝ²` the wealth equation (5.2) has a strong
solution on `[t, T]`, unique up to indistinguishability. -/
def AdmissibleI (M : Model) (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (π : Strategy) : Prop :=
  ∀ z : ℝ, ∀ t ∈ Icc 0 M.T, ∀ x β : ℝ,
    (∃ X, IsInsideWealth M P W π z t x β X) ∧
    ∀ X Y, IsInsideWealth M P W π z t x β X → IsInsideWealth M P W π z t x β Y →
      ∀ᵐ ω ∂P, ∀ s ∈ Icc t M.T, X s ω = Y s ω

/-- Condition (ii) of Definition 5.1 (p. 15): for every `(t, x, β) ∈ [0, T) × ℝ²`, `ε > 0`,
`ρ > 2` there are `δ > 2`, `t̃ ∈ (t, T)`, `C > 0` such that for every `z ∈ ℝ` and every
`s ∈ [t, t̃]` the moment bounds (5.4) and (5.5) hold for the wealth started at `(t, x, β)`. -/
def AdmissibleII (M : Model) (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (π : Strategy) : Prop :=
  ∀ t ∈ Ico 0 M.T, ∀ x β : ℝ, ∀ ε > (0 : ℝ), ∀ ρ > (2 : ℝ),
    ∃ δ > (2 : ℝ), ∃ tt ∈ Ioo t M.T, ∃ C > (0 : ℝ), ∀ z : ℝ, ∀ X,
      IsInsideWealth M P W π z t x β X → ∀ s ∈ Icc t tt,
        (∫⁻ ω, ENNReal.ofReal (Real.exp (-δ * M.k * Real.exp (M.r * (M.T - s)) * X s ω)) ∂P)
            ≤ ENNReal.ofReal (C * Real.exp (ε * z ^ 2)) ∧
        (∫⁻ ω, ENNReal.ofReal (|π s (X s ω) (betaZ M W z t β s ω)| ^ ρ) ∂P)
            ≤ ENNReal.ofReal (C * Real.exp (ε * z ^ 2))

/-- Admissible strategies, Definition 5.1 (p. 15): the class `Π`. -/
def Admissible (M : Model) (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (π : Strategy) : Prop :=
  AdmissibleI M P W π ∧ AdmissibleII M P W π

/-- The infinitesimal generator (5.7), p. 16, of the inside system with drift `z`, applied to
`f(t, x, β)` at the action value `p = π(t, x, β)`:
`f_t + [rx + p(z - r)] f_x + (ζ/σ²)(z - β) f_β + ½σ²p² f_xx + ½(ζ²/σ²) f_ββ + pζ f_xβ`.
The time derivative is taken within `[0, T]` (one-sided at the endpoints). -/
noncomputable def gen (M : Model) (z p : ℝ) (f : ℝ → ℝ → ℝ → ℝ) (t x β : ℝ) : ℝ :=
  derivWithin (fun s => f s x β) (Icc 0 M.T) t
    + (M.r * x + p * (z - M.r)) * deriv (fun y => f t y β) x
    + M.ζ t / M.σ ^ 2 * (z - β) * deriv (fun b => f t x b) β
    + 1 / 2 * M.σ ^ 2 * p ^ 2 * deriv (fun y => deriv (fun y' => f t y' β) y) x
    + 1 / 2 * (M.ζ t ^ 2 / M.σ ^ 2) * deriv (fun b => deriv (fun b' => f t x b') b) β
    + p * M.ζ t * deriv (fun b => deriv (fun y => f t y b) x) β

/-- `Y` is a martingale on `[t₀, T₁]` with respect to `ℱ` indexed by elapsed time `s - t₀`:
each `Y_s` is integrable and `ℱ_{s-t₀}`-measurable up to a null set, and
`∫_A Y_{s'} dP = ∫_A Y_s dP` for all `t₀ ≤ s ≤ s' ≤ T₁` and `A ∈ ℱ_{s-t₀}`. -/
def IsMartingaleOn (P : Measure Ω) (ℱ : ℝ≥0 → MeasurableSpace Ω) (Y : ℝ → Ω → ℝ)
    (t₀ T₁ : ℝ) : Prop :=
  (∀ s ∈ Icc t₀ T₁, Integrable (Y s) P ∧ AEStronglyMeasurable[ℱ (s - t₀).toNNReal] (Y s) P) ∧
  ∀ s s', t₀ ≤ s → s ≤ s' → s' ≤ T₁ → ∀ A : Set Ω, MeasurableSet[ℱ (s - t₀).toNNReal] A →
    ∫ ω in A, Y s' ω ∂P = ∫ ω in A, Y s ω ∂P

end SmoothAmbEq.Gaussian


