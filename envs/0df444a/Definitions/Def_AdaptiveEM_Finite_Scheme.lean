-- Prove2me | Definitions.Def_AdaptiveEM_Finite_Scheme
-- name    : AdaptiveEM_Finite_Scheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:05:59.028793+00:00
-- url     : https://prove2.me/theorems/47209a6a-4e77-46d1-8d10-7f788abc8f2c
-- title:
--   (5), p. 528 — the adaptive Euler–Maruyama scheme on random times, the index n_t and the interpolants X̄_t, X̂_t
-- statement:
--   This file defines the adaptive Euler–Maruyama scheme (5) of Fang and Giles (2020) and its two interpolants.
--
--   Let $f:\mathbb R^m\to\mathbb R^m$, $g:\mathbb R^m\to\mathbb R^{m\times d}$, a timestep function $h:\mathbb R^m\to\mathbb R$, an initial value $x_0\in\mathbb R^m$ and a $d$-dimensional path $W_t$, $t\ge0$, be given. Starting from $t_0=0$, $\widehat X_0=x_0$, the scheme sets $h_n=h(\widehat X_{t_n})$ and
--   $$t_{n+1}=t_n+h_n,\qquad \widehat X_{t_{n+1}}=\widehat X_{t_n}+f(\widehat X_{t_n})\,h_n+g(\widehat X_{t_n})\,(W_{t_{n+1}}-W_{t_n}).$$
--   The grid $t_0<t_1<\dots$ is random: it depends on the path through the states. For a time $t$, the index $n_t$ is the $n$ with $t_n\le t<t_{n+1}$ and $\underline t=t_{n_t}$ is the last grid time not after $t$. The piecewise constant interpolant is $\overline X_t=\widehat X_{\underline t}$, and the continuous interpolant is
--   $$\widehat X_t=\widehat X_{\underline t}+f(\widehat X_{\underline t})(t-\underline t)+g(\widehat X_{\underline t})(W_t-W_{\underline t}).$$
--   The file also names the matrix–vector product $Aw$, $A\in\mathbb R^{m\times d}$, $w\in\mathbb R^d$.
--
--   The scheme is the explicit Euler–Maruyama method with a state-dependent step: small steps where the drift is large keep the method stable for drifts that are only one-sided Lipschitz.
--
--   **Formalization Note** Times are nonnegative reals and indices start at $0$. The scheme is defined pathwise for each $\omega$; the time advances by the positive part of $h(\widehat X_{t_n})$, which is $h_n$ whenever $h>0$, as all theorems assume. The index $n_t$ is the least $n$ with $t<t_{n+1}$; if the grid never passes $t$ it is set to $0$, a junk value on an event that has probability zero under the paper's assumptions (Theorem 1). The last step is not capped at $T$, as in (5).
-- source:
--   Fang, Giles, Adaptive Euler–Maruyama method for SDEs with nonglobally Lipschitz drift, Ann. Appl. Probab. 30 (2020), p. 528, (5) and the interpolants

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace AdaptiveEM.Finite

open EthierKurtz

/-- The matrix–vector product `A w` of an `m × d` matrix `A` (an element of `Diffusion m d`,
carrying the Frobenius norm) with a vector `w ∈ ℝ^d`. -/
noncomputable def mulVec {m d : ℕ} (A : SabanisEuler.Shared.Diffusion m d) (w : SDEState d) :
    SDEState m :=
  WithLp.toLp 2 (fun i => ∑ j, A (i, j) * w j)

/-- Fang–Giles (2020), (5), p. 528: the adaptive Euler–Maruyama scheme on the random grid.
`grid f g h x0 W n ω = (t_n, X̂_{t_n})` with `t_0 = 0`, `X̂_0 = x0`,
`t_{n+1} = t_n + h(X̂_{t_n})`,
`X̂_{t_{n+1}} = X̂_{t_n} + f(X̂_{t_n}) h(X̂_{t_n}) + g(X̂_{t_n}) (W_{t_{n+1}} - W_{t_n})`.
The step uses the real number `h x`; the time is advanced by `(h x).toNNReal`, which equals
`h x` whenever `h > 0`. -/
noncomputable def grid {m d : ℕ} {Ω : Type*} (f : SDEState m → SDEState m)
    (g : SDEState m → SabanisEuler.Shared.Diffusion m d) (h : SDEState m → ℝ)
    (x0 : SDEState m) (W : ℝ≥0 → Ω → SDEState d) : ℕ → Ω → ℝ≥0 × SDEState m
  | 0, _ => (0, x0)
  | n + 1, ω =>
    let p := grid f g h x0 W n ω
    let t' := p.1 + (h p.2).toNNReal
    (t', p.2 + h p.2 • f p.2 + mulVec (g p.2) (W t' ω - W p.1 ω))

/-- `n_t`, the index of the last grid time not after `t`: the first `n` with `t < t_{n+1}`.
If the grid never passes `t` the value is the junk `0` (an event of probability zero under the
paper's assumptions, Theorem 1). -/
noncomputable def idx {m d : ℕ} {Ω : Type*} (f : SDEState m → SDEState m)
    (g : SDEState m → SabanisEuler.Shared.Diffusion m d) (h : SDEState m → ℝ)
    (x0 : SDEState m) (W : ℝ≥0 → Ω → SDEState d) (t : ℝ≥0) (ω : Ω) : ℕ := by
  classical
  exact if H : ∃ n, t < (grid f g h x0 W (n + 1) ω).1 then Nat.find H else 0

/-- `t̲ = t_{n_t}`, the last grid time not after `t`. -/
noncomputable def tlow {m d : ℕ} {Ω : Type*} (f : SDEState m → SDEState m)
    (g : SDEState m → SabanisEuler.Shared.Diffusion m d) (h : SDEState m → ℝ)
    (x0 : SDEState m) (W : ℝ≥0 → Ω → SDEState d) (t : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (grid f g h x0 W (idx f g h x0 W t ω) ω).1

/-- The piecewise constant interpolant `X̄_t = X̂_{t̲}`. -/
noncomputable def Xbar {m d : ℕ} {Ω : Type*} (f : SDEState m → SDEState m)
    (g : SDEState m → SabanisEuler.Shared.Diffusion m d) (h : SDEState m → ℝ)
    (x0 : SDEState m) (W : ℝ≥0 → Ω → SDEState d) (t : ℝ≥0) (ω : Ω) : SDEState m :=
  (grid f g h x0 W (idx f g h x0 W t ω) ω).2

/-- The continuous interpolant
`X̂_t = X̂_{t̲} + f(X̂_{t̲}) (t - t̲) + g(X̂_{t̲}) (W_t - W_{t̲})`. -/
noncomputable def Xhat {m d : ℕ} {Ω : Type*} (f : SDEState m → SDEState m)
    (g : SDEState m → SabanisEuler.Shared.Diffusion m d) (h : SDEState m → ℝ)
    (x0 : SDEState m) (W : ℝ≥0 → Ω → SDEState d) (t : ℝ≥0) (ω : Ω) : SDEState m :=
  Xbar f g h x0 W t ω + ((t : ℝ) - (tlow f g h x0 W t ω : ℝ)) • f (Xbar f g h x0 W t ω) +
    mulVec (g (Xbar f g h x0 W t ω)) (W t ω - W (tlow f g h x0 W t ω) ω)

end AdaptiveEM.Finite


