-- Prove2me | Definitions.Def_StochAutoreg_gRule
-- name    : StochAutoreg_gRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:14:43.671561+00:00
-- url     : https://prove2.me/theorems/bd3be95d-8c7d-4542-bef5-84029e5ffe32
-- title:
--   Transition rules of the family $G_N$
-- statement:
--   For $\omega\in\{-1,1\}^N$ and $\tau\in\{-1,1\}$, the prescriptions of $g_{\omega,\tau}$ on the $N$ roots $r_j$ and the base-only root $v$ are, for $|z|<M$,
--
--   $$p_g(r_jz)=\begin{cases}\tfrac12+t_G\omega_j,&|z|<J,\\ \mathbf 1\{\sum_{t=1}^Jz_t>J/2\},&|z|=M-1,\\ \tfrac12,&\text{otherwise,}\end{cases}\qquad p_g(vz)=\begin{cases}\tfrac12+4\tau\sqrt\varepsilon,&z\text{ empty},\\ \tfrac12,&\text{otherwise.}\end{cases}$$
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §7, "The first family G_N", p.15

import Mathlib
import Definitions.Def_StochAutoreg_clampI

namespace StochAutoreg

/-- The prescriptions of the family `G_N`, on `N` roots `r_j` and one base-only root `v`, for `ω ∈ {-1,1}^N` and
`τ ∈ {-1,1}`. At `r_j`: `1/2 + t_G ω_j` for `|z| < J`; `1{∑_{t≤J} z_t > J/2}` for `|z| = M-1`; `1/2` otherwise. At `v`:
`1/2 + 4τ√ε` for `z` empty, `1/2` at strict descendants. Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §7 "The first family `G_N`", p.15.

**Formalization Note.** `z` is oldest token first, so `z.take J` is `z₁, …, z_J`, generated at depths `0, …, J-1`.
Signs are units of `ℤ`. The index `Sum.inl j` is `r_j` and `Sum.inr ()` is `v`. -/
noncomputable def gRule (J M : ℕ) (ε tG : ℝ) {N : ℕ} (ω : Fin N → ℤˣ) (τ : ℤˣ) :
    Fin N ⊕ Unit → List Bool → unitInterval
  | Sum.inl j, z =>
    clampI (if z.length < J then 1 / 2 + tG * ((ω j : ℤ) : ℝ)
      else if z.length = M - 1 then (if J < 2 * (z.take J).count true then 1 else 0)
      else 1 / 2)
  | Sum.inr _, z =>
    clampI (if z = [] then 1 / 2 + 4 * ((τ : ℤ) : ℝ) * Real.sqrt ε else 1 / 2)

end StochAutoreg


