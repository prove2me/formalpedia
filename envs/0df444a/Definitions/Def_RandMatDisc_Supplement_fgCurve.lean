-- Prove2me | Definitions.Def_RandMatDisc_Supplement_fgCurve
-- name    : RandMatDisc_Supplement_fgCurve
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:10:00.694121+00:00
-- url     : https://prove2.me/theorems/17f59ae4-36f4-4cf9-8150-5995d5865cb0
-- title:
--   The Frobenius-greedy curve: $r(t)$ of (10)–(11), $\Phi(\tau)=\sqrt{2/\tau}\,r(2\tau)$, $a_\kappa$ and $\tau_{\mathrm{FG}}(\kappa)$
-- statement:
--   For $0\le r<\sqrt{\pi/8}$ put
--
--   $$h(r)=-\sqrt{\tfrac{\pi}{2}}\,r-\tfrac{\pi}{4}\log\Big(1-\sqrt{\tfrac{8}{\pi}}\,r\Big).$$
--
--   This is a continuous, strictly increasing bijection from $[0,\sqrt{\pi/8})$ onto $[0,\infty)$. The **Frobenius-greedy radius** $r:[0,\infty)\to[0,\sqrt{\pi/8})$ is its inverse, i.e. the solution of (11), $t=h(r(t))$. The **limiting discrepancy** is
--
--   $$\Phi(\tau)=\sqrt{\tfrac{2}{\tau}}\;r(2\tau),\qquad\tau>0.$$
--
--   With $L(a)=-a-\log(1-a)$, for $0<\kappa<2$ let $a_\kappa\in(0,1)$ be the solution of $\kappa^2=2a_\kappa^2/L(a_\kappa)$, and set
--
--   $$\tau_{\mathrm{FG}}(\kappa)=\tfrac{\pi}{8}\,L(a_\kappa).$$
--
--   These are the objects of Theorems 2.6 and 2.7: $\Phi$ is the exact limit of the Frobenius-greedy discrepancy, and $\tau_{\mathrm{FG}}(\kappa)$ is the density above which the algorithm succeeds at margin $\kappa$.
--
--   **Formalization Note** $r(t)$ is written as $\sup\{x\in[0,\sqrt{\pi/8}):h(x)\le t\}$, which equals $h^{-1}(t)$ for $t\ge0$; Theorem 2.7 states that it satisfies (11). $a_\kappa$ is written as the infimum of the solution set in $(0,1)$; that this set is a singleton is part of Theorem 2.7, not an assumption. The values at $t<0$ and at $\kappa\notin(0,2)$ are never used.
-- source:
--   Kızıldağ, Li, Stable and Online Algorithms for Random Matrix Discrepancy, arXiv:2610.01591 (preprint; held file sha256 889af7fc2595be5c653c6b477e70fa5898c7b743d8720cda44ca99761d629a13), §2.2, p.12 (PDF p.14), eqs. (10)–(11); p.13 (PDF p.15), Theorems 2.6 (Φ) and 2.7 (a_κ, τ_FG); §4.2, p.33 (PDF p.35), L(a)

import Mathlib

namespace RandMatDisc.Supplement

/-- The right-hand side of (11), p.12 (PDF p.14) of Kızıldağ, Li, arXiv:2610.01591 (held file
sha256 889af7fc…), as a function of `r ∈ [0, √(π/8))`:
`h(r) = −√(π/2) r − (π/4) log(1 − √(8/π) r)`. -/
noncomputable def fgTime (r : ℝ) : ℝ :=
  -Real.sqrt (Real.pi / 2) * r - Real.pi / 4 * Real.log (1 - Real.sqrt (8 / Real.pi) * r)

/-- The **Frobenius-greedy radius** `r : [0, ∞) → [0, √(π/8))`, eqs. (10)–(11), p.12 (PDF p.14)
of arXiv:2610.01591 (sha256 889af7fc…): `r(t)` is defined through (11),
`t = −√(π/2) r(t) − (π/4) log(1 − √(8/π) r(t))`, i.e. `r = h⁻¹` for the continuous strictly
increasing bijection `h = fgTime : [0, √(π/8)) → [0, ∞)` (p.33).

**Formalization Note.** Written as `r(t) = sup {x ∈ [0, √(π/8)) : h(x) ≤ t}`. For `t ≥ 0` the
set contains `0` and is bounded by `√(π/8)`, and since `h` is a continuous increasing bijection
the supremum is the unique `x` with `h(x) = t`. For `t < 0` the value (`0`) is never used. -/
noncomputable def fgRadius (t : ℝ) : ℝ :=
  sSup {x : ℝ | 0 ≤ x ∧ x < Real.sqrt (Real.pi / 8) ∧ fgTime x ≤ t}

/-- The limiting Frobenius-greedy discrepancy `Φ(τ) = √(2/τ) · r(2τ)`, Theorem 2.6, p.13 (PDF
p.15) of arXiv:2610.01591 (sha256 889af7fc…). -/
noncomputable def fgPhi (τ : ℝ) : ℝ := Real.sqrt (2 / τ) * fgRadius (2 * τ)

/-- `L(a) = −a − log(1 − a)`, p.33 (PDF p.35). -/
noncomputable def fgL (a : ℝ) : ℝ := -a - Real.log (1 - a)

/-- `a_κ`, Theorem 2.7, p.13 (PDF p.15) of arXiv:2610.01591 (sha256 889af7fc…): for `0 < κ < 2`,
the unique `a ∈ (0, 1)` with `κ² = 2a² / (−a − log(1 − a))`.

**Formalization Note.** Written as the infimum of the solution set in `(0, 1)`; that this set is
a singleton for `0 < κ < 2` (existence and uniqueness) is part of Theorem 2.7, not assumed. -/
noncomputable def fgA (κ : ℝ) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ a < 1 ∧ κ ^ 2 = 2 * a ^ 2 / fgL a}

/-- The Frobenius-greedy density threshold `τ_FG(κ) = (π/8)[−a_κ − log(1 − a_κ)]`,
Theorem 2.7, p.13 (PDF p.15) of arXiv:2610.01591 (sha256 889af7fc…). -/
noncomputable def tauFG (κ : ℝ) : ℝ := Real.pi / 8 * fgL (fgA κ)

end RandMatDisc.Supplement


