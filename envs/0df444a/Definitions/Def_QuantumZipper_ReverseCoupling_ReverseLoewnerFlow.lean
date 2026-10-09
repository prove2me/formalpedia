-- Prove2me | Definitions.Def_QuantumZipper_ReverseCoupling_ReverseLoewnerFlow
-- name    : QuantumZipper_ReverseCoupling_ReverseLoewnerFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:37.248753+00:00
-- url     : https://prove2.me/theorems/4859101b-a368-4505-9ed9-a2f09712f049
-- title:
--   (1.7), p. 13 — the reverse Loewner flow f_t = g_t − W_t, ∂_t g_t(z) = −2/(g_t(z) − W_t), and the spatial derivative f′_t
-- statement:
--   Let $W:[0,\infty)\to\mathbb R$ be a driving function. A family of maps $g_t:\mathbb H\to\mathbb C$, $t\ge0$, is a **reverse Loewner flow** driven by $W$ if for every $z\in\mathbb H$,
--   $$g_0(z)=z,\qquad \partial_t g_t(z)=\frac{-2}{g_t(z)-W_t}\quad(t\ge0),$$
--   with $g_t(z)-W_t\in\mathbb H$ for all $t$ (at $t=0$ the derivative is one-sided). Writing
--   $$f_t(z)=g_t(z)-W_t ,$$
--   this is the pathwise meaning of the stochastic equation (1.7), $df_t(z)=\frac{-2}{f_t(z)}\,dt-\sqrt\kappa\,dB_t$, $f_0(z)=z$, when $W_t=\sqrt\kappa B_t$. The spatial derivative is $f'_t(z)=\partial_z f_t(z)=\partial_z g_t(z)$, a complex derivative.
--
--   For continuous $W$ the solution exists for all $t\ge0$ and is unique on $\mathbb H$, because $\operatorname{Im} f_t(z)$ is increasing and the right-hand side is locally Lipschitz away from the real line. The maps $f_t$ are the reverse SLE$_\kappa$ maps of Theorem 1.2: $f_T$ maps $\mathbb H$ onto $\mathbb H\setminus K_T$.
--
--   **Formalization Note** Time is $\mathbb R_{\ge0}$ (as for Mathlib's Brownian motion); the time derivative is that of $s\mapsto g_{\max(s,0)}(z)$ within $[0,\infty)$. No stochastic integral is used. Values of $g_t$ off $\mathbb H$ are unconstrained and never used; $f'_t(z)$ is `deriv (f t) z`, which at $z\in\mathbb H$ depends only on values in $\mathbb H$. Existence and uniqueness (Picard–Lindelöf) are cited, not posed; the sanity file checks the explicit flow $g_t(z)=\sqrt{z^2-4t}$ (branch in $\mathbb H$) for $W\equiv0$.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, Theorem 1.2, (1.7), p. 13; §4.1, p. 43 (f′_t is the spatial derivative); footnote 7, p. 14

import Mathlib

set_option autoImplicit false

open scoped NNReal

namespace QuantumZipper.ReverseCoupling

/-- **Reverse Loewner flow** driven by `W : ℝ≥0 → ℝ` (arXiv:1012.4797v2, Theorem 1.2, (1.7), p. 13).

The paper writes the flow as the SDE `df_t(z) = −2/f_t(z) dt − √κ dB_t`, `f₀(z) = z`, with driving
function `W_t = √κ B_t`. Pathwise this says `f_t(z) = g_t(z) − W_t`, where for each `z ∈ ℍ` the path
`t ↦ g_t(z)` solves the ordinary differential equation
`∂_t g_t(z) = −2 / (g_t(z) − W_t)`, `g₀(z) = z`.
`IsReverseLoewnerFlow W g` states exactly this, for every `z` in the upper half-plane and every
`t ≥ 0`, together with `g_t(z) − W_t ∈ ℍ`.

**Formalization Note** Time is `ℝ≥0`, as in Mathlib's Brownian motion. The time derivative is taken
for `s ↦ g_{s⁺}(z)` (`s⁺ = Real.toNNReal s`) within `[0, ∞)`: a two-sided derivative at `t > 0` and
a right derivative at `t = 0`. No stochastic integral is needed: `W` enters only through the
right-hand side. For continuous `W` the solution exists and is unique on `ℍ` (Picard–Lindelöf, using
that `Im (g_t(z) − W_t)` is increasing, so the solution never leaves `ℍ`); this is cited, not posed.
Values of `g t z` for `z ∉ ℍ` are unconstrained and never used. -/
def IsReverseLoewnerFlow (W : ℝ≥0 → ℝ) (g : ℝ≥0 → ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im →
    g 0 z = z ∧
    ∀ t : ℝ≥0, 0 < (g t z - (W t : ℂ)).im ∧
      HasDerivWithinAt (fun s : ℝ => g (Real.toNNReal s) z) (-2 / (g t z - (W t : ℂ)))
        (Set.Ici 0) (t : ℝ)

/-- The reverse Loewner map `f_t(z) = g_t(z) − W_t` of (1.7) (p. 13). -/
def revF (W : ℝ≥0 → ℝ) (g : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (z : ℂ) : ℂ :=
  g t z - (W t : ℂ)

/-- The spatial derivative `f′_t(z) = ∂/∂z f_t(z)` (p. 43: "Here `f′_t(z)` denotes the spatial
derivative `∂/∂z f_t`"), a complex derivative in `z`. -/
noncomputable def revFDeriv (W : ℝ≥0 → ℝ) (g : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (z : ℂ) : ℂ :=
  deriv (revF W g t) z

end QuantumZipper.ReverseCoupling


