-- Prove2me | Definitions.Def_DiffusionErrorAcc_Stability_AdditiveSDE
-- name    : DiffusionErrorAcc_Stability_AdditiveSDE
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:58:23.948788+00:00
-- url     : https://prove2.me/theorems/5feeab58-96b0-419c-bf30-ed9f8bfdc6b4
-- title:
--   Additive-noise SDEs dX = b(X, t)dt + √2 dW (pathwise solutions), their Feynman–Kac posteriors, and the drift of the learned reverse SDE (2.2)
-- statement:
--   A drift $b:\mathbb R^d\times[0,T]\to\mathbb R^d$, written `b x t`, is **regular** (`IsLipContDrift b T`) when it is Lipschitz in space uniformly in time on $[0,T]$ and jointly continuous on $\mathbb R^d\times[0,T]$.
--
--   Let $W$ be a standard $d$-dimensional Brownian motion on a probability space $(\Omega,P)$ (the platform predicate `EthierKurtz.IsStandardBrownian`). Because the noise of $dX_u=b(X_u,u)\,du+\sqrt2\,dW_u$ is additive, a **solution on $[0,T]$** (`IsSDESolution P b W T X`) is a process with measurable $X_u$ such that almost surely $u\mapsto X_u$ is continuous on $[0,T]$ and
--   $$X_u=X_0+\int_0^u b(X_s,s)\,ds+\sqrt2\,W_u\qquad\text{for all } u\in[0,T].$$
--   A **solution started at $x$ at time $t_0$** (`IsSDESolutionFrom`) satisfies $X_u=x+\int_{t_0}^u b(X_s,s)\,ds+\sqrt2\,(W_u-W_{t_0})$ for $u\in[t_0,T]$.
--
--   The **Feynman–Kac posterior** $f_t(x)=\mathbb E[f(X_T)\mid X_t=x]$ of a statistic $f$ is pinned down by `IsFeynmanKacPosterior b f T F`: for every $t\in[0,T]$, $x\in\mathbb R^d$, every probability space, every standard Brownian motion $W$ on it and every solution $X$ started at $x$ at time $t$, $F(t,x)=\mathbb E[f(X_T)]$.
--
--   The **learned reverse SDE** (2.2) is $dY_u=(Y_u+2\hat s_{T-u}(Y_u))\,du+\sqrt2\,dB_u$, $0\le u\le T$; its drift $(y,u)\mapsto y+2\hat s(y,T-u)$ is `learnedReverseDrift ŝ T`.
--
--   **Formalization Note.** Brownian time is `ℝ≥0`; `W u.toNNReal` evaluates it at $u\ge0$. The integral is an interval integral of a path-continuous integrand.
-- source:
--   Giapitzakis, Moitra, Risteski, Rohatgi, Error accumulation in reverse diffusion with an imperfect score: beyond path-space analyses, STOC 2027 submission (manuscript sha256 c0118fd2…), p. 9, (2.2); p. 21, Appendix A setting (SDEs, drifts, f_t); p. 39, Lemma G.11 (f_t(x) := E[f(X_T) | X_t = x])

import Mathlib
import Definitions.Def_DiffusionErrorAcc_Stability_Densities
import Definitions.Def_EthierKurtz_IsStandardBrownian

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DiffusionErrorAcc.Stability

/-! # Additive-noise SDEs `dX_t = b(X_t, t) dt + √2 dW_t`, their Feynman–Kac posteriors, and the
learned reverse SDE (2.2) (Giapitzakis–Moitra–Risteski–Rohatgi, (2.2) p. 9, Appendix A p. 21,
Lemma G.11 p. 39)

`W` is a standard `d`-dimensional Brownian motion in the sense of the platform definition
`EthierKurtz.IsStandardBrownian` (time `ℝ≥0`). Because the noise is additive, a solution is
defined pathwise by the integral equation; no Itô integral is needed. -/

/-- A drift `b : ℝ^d × [0, T] → ℝ^d`, written `b x t`, that is Lipschitz in space uniformly in
time on `[0, T]` and jointly continuous on `ℝ^d × [0, T]` (Appendix A, Lemma G.11, §2.3). -/
def IsLipContDrift {d : ℕ} (b : Rd d → ℝ → Rd d) (T : ℝ) : Prop :=
  (∃ L : ℝ≥0, ∀ t ∈ Icc (0 : ℝ) T, LipschitzWith L (fun x => b x t)) ∧
    ContinuousOn (fun q : Rd d × ℝ => b q.1 q.2) (univ ×ˢ Icc (0 : ℝ) T)

/-- `X` solves `dX_u = b(X_u, u) du + √2 dW_u` on `[0, T]`: every `X u` is measurable and,
almost surely, `u ↦ X_u` is continuous on `[0, T]` and
`X_u = X_0 + ∫_0^u b(X_s, s) ds + √2 W_u` for all `u ∈ [0, T]`. -/
def IsSDESolution {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (b : Rd d → ℝ → Rd d) (W : ℝ≥0 → Ω → Rd d) (T : ℝ) (X : ℝ → Ω → Rd d) : Prop :=
  (∀ u, Measurable (X u)) ∧
    ∀ᵐ ω ∂P, ContinuousOn (fun u => X u ω) (Icc 0 T) ∧
      ∀ u ∈ Icc (0 : ℝ) T,
        X u ω = X 0 ω + (∫ s in (0 : ℝ)..u, b (X s ω) s) + Real.sqrt 2 • W u.toNNReal ω

/-- `X` solves the same SDE on `[t₀, T]` started at the point `x` at time `t₀`: almost surely
`u ↦ X_u` is continuous on `[t₀, T]` and
`X_u = x + ∫_{t₀}^u b(X_s, s) ds + √2 (W_u − W_{t₀})` for all `u ∈ [t₀, T]`. -/
def IsSDESolutionFrom {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (b : Rd d → ℝ → Rd d) (W : ℝ≥0 → Ω → Rd d) (t₀ : ℝ) (x : Rd d) (T : ℝ)
    (X : ℝ → Ω → Rd d) : Prop :=
  (∀ u, Measurable (X u)) ∧
    ∀ᵐ ω ∂P, ContinuousOn (fun u => X u ω) (Icc t₀ T) ∧
      ∀ u ∈ Icc t₀ T,
        X u ω = x + (∫ s in t₀..u, b (X s ω) s) +
          Real.sqrt 2 • (W u.toNNReal ω - W t₀.toNNReal ω)

/-- `F t x` is the Feynman–Kac posterior `f_t(x) = E[f(X_T) | X_t = x]` of the SDE
`dX = b(X, t) dt + √2 dW` (Appendix A, Lemma G.11): for every `t ∈ [0, T]` and `x ∈ ℝ^d`,
every probability space, every standard Brownian motion `W` on it and every solution `X` started
at `x` at time `t`, `F t x = E[f(X_T)]`. -/
def IsFeynmanKacPosterior {d : ℕ} (b : Rd d → ℝ → Rd d) (f : Rd d → ℝ) (T : ℝ)
    (F : ℝ → Rd d → ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → Rd d) (X : ℝ → Ω → Rd d) (t : ℝ) (x : Rd d),
    t ∈ Icc (0 : ℝ) T → EthierKurtz.IsStandardBrownian P W →
      IsSDESolutionFrom P b W t x T X → F t x = ∫ ω, f (X T ω) ∂P

/-- The drift of the learned reverse SDE (2.2), `dY_u = (Y_u + 2 ŝ_{T−u}(Y_u)) du + √2 dB_u`:
`(y, u) ↦ y + 2 ŝ(y, T − u)`. -/
def learnedReverseDrift {d : ℕ} (sHat : Rd d → ℝ → Rd d) (T : ℝ) : Rd d → ℝ → Rd d :=
  fun y u => y + (2 : ℝ) • sHat y (T - u)

end DiffusionErrorAcc.Stability


