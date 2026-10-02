-- Prove2me | Definitions.Def_TeschlODE_Frobenius_slitDisc
-- name    : TeschlODE_Frobenius_slitDisc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:03:19.151832+00:00
-- url     : https://prove2.me/theorems/93776f85-59fb-4142-8af5-679094a389a2
-- title:
--   Slit punctured disc {0 < |z| < R} ∖ (−∞, 0] (domain of the standard branch, §4.2)
-- statement:
--   For $R \in (0, \infty]$ the **slit punctured disc** of radius $R$ is
--   $$\mathrm{slitDisc}(R) = \{ z \in \mathbb{C} : |z| < R \} \setminus (-\infty, 0],$$
--   the open disc of radius $R$ about $0$ with the closed negative real half-axis (including $0$) removed. It is simply connected, and on it the powers $z^\alpha = e^{\alpha \log z}$ and the logarithm $\log z = \log|z| + i \arg z$, $-\pi < \arg z < \pi$, are single-valued and holomorphic. This is the "standard branch (with branch cut along the negative real axis)" the book uses in §4.2 (pp. 116–118) for the Euler equation and the Frobenius method.
--
--   **Formalization Note.** `Metric.eball 0 R ∩ Complex.slitPlane` with `R : ENNReal`, so $R = \infty$ (the slit plane $\mathbb{C} \setminus (-\infty,0]$) is allowed. Mathlib's `Complex.slitPlane` is $\{z : \operatorname{Re} z > 0 \text{ or } \operatorname{Im} z \neq 0\}$, which excludes $0$. On this set Mathlib's `z ^ α` (`Complex.cpow`) and `Complex.log` are the principal branches.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 116, §4.2, Eq. (4.23)

import Mathlib

namespace TeschlODE.Frobenius

/-- The slit punctured disc `{z : 0 < |z| < R} ∖ (-∞, 0]` of radius `R` (`R = ⊤` allowed, giving
`ℂ ∖ (-∞, 0]`). It is the domain on which Teschl (§4.2, pp. 116–118) evaluates `z ^ α` and
`log z` with "the standard branch" (branch cut along the negative real axis); `Complex.slitPlane`
already excludes `0`. -/
def slitDisc (R : ENNReal) : Set ℂ :=
  Metric.eball (0 : ℂ) R ∩ Complex.slitPlane

end TeschlODE.Frobenius


