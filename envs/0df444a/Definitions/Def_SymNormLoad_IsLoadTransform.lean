-- Prove2me | Definitions.Def_SymNormLoad_IsLoadTransform
-- name    : SymNormLoad_IsLoadTransform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:05.045147+00:00
-- url     : https://prove2.me/theorems/1e447168-b875-4ec1-9035-a37bc343b662
-- title:
--   Load transform $h$: solution of the ODE (2.2)
-- statement:
--   Let $c=\ln(3/2)$ and let $\varphi$ be the piecewise-linear extension above. The **load transform** $h:[0,\infty)\to[0,\infty)$ is defined by the differential equation
--   $$
--   h(0)=0,\qquad h'(t)=c\,\varphi(r(t)),\qquad r(t)=M\exp(-h(t)).\tag{2.2}
--   $$
--   A function $h$ is a load transform when it satisfies (2.2) on $[0,\infty)$.
--
--   The transform depends only on $\Psi$ and $M$; the penalty $g=e^{h}$ and the potential $\Phi$ are built from it.
--
--   **Formalization Note** $h$ is a function $\mathbb R\to\mathbb R$; the derivative is taken within $[0,\infty)$ (the right derivative at $0$), and values for $t<0$ are unconstrained. That (2.2) has exactly one solution is the milestone `SymNormLoad.eq_2_2`.
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Section 2.1.2, Eq. (2.2), p.10

import Mathlib
import Definitions.Def_SymNormLoad_phiBar

namespace SymNormLoad

/-- **The load transform `h` (the ODE (2.2)).** Chen–Im–Sirri, *Online Load Balancing under
Symmetric Norms*, manuscript (STOC 2027 submission), §2.1.2, Eq. (2.2), p.10: the load transform
`h : [0, ∞) → [0, ∞)` is defined by
`h(0) = 0`, `h′(t) = c φ(r(t))`, `r(t) = M exp(−h(t))`, `c = ln(3/2)`, where `φ(r(t))` is
evaluated with the piecewise-linear extension of `φ`.

**Formalization Note** `IsLoadTransform Ψ h` says that `h : ℝ → ℝ` solves (2.2) on `[0, ∞)`:
`h 0 = 0`, and for every `t ≥ 0`, `h` has derivative `ln(3/2) · φ̄(M e^{−h(t)})` within `[0, ∞)`
at `t` (the two-sided derivative for `t > 0`, the right derivative at `0`). The values of `h` on
`t < 0` are unconstrained and never used. Existence and uniqueness of such `h` is the separate
milestone `SymNormLoad.eq_2_2`. -/
def IsLoadTransform {M : ℕ} (Ψ : (Fin M → ℝ) → ℝ) (h : ℝ → ℝ) : Prop :=
  h 0 = 0 ∧ ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt h (Real.log (3 / 2) * phiBar Ψ ((M : ℝ) * Real.exp (-h t))) (Set.Ici 0) t

end SymNormLoad


