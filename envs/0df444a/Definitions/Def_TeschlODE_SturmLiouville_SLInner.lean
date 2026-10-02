-- Prove2me | Definitions.Def_TeschlODE_SturmLiouville_SLInner
-- name    : TeschlODE_SturmLiouville_SLInner
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:22:53.206813+00:00
-- url     : https://prove2.me/theorems/5269aa58-3b0c-4e76-ae6e-1f749bab21e5
-- title:
--   Weighted scalar product on C([a,b], ℂ) (5.52)
-- statement:
--   With the weight $r > 0$ of (5.45), the space $H_0 = C([a,b],\mathbb{C})$ carries the scalar product
--   $$\langle f, g\rangle = \int_a^b f(x)^* g(x)\, r(x)\, dx, \qquad (5.52)$$
--   conjugate linear in $f$, and the norm $\|f\| = \sqrt{\langle f, f\rangle}$ (5.20). $H_0$ with this scalar product is an inner product space but not complete.
--
--   **Formalization Note.** Elements of $H_0$ are functions $\mathbb{R} \to \mathbb{C}$ continuous on `Set.Icc a b`; only their values on $[a,b]$ matter. The scalar product is the interval integral `∫ x in a..b`. Every statement applies it only to functions continuous on $[a,b]$, so the integrand is integrable and no junk value of the Bochner integral arises. Norm convergence $\|f_n - f\| \to 0$ is written as $\operatorname{Re}\langle f_n - f, f_n - f\rangle \to 0$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 155, §5.4, Eq. (5.52)

import Mathlib

namespace TeschlODE.SturmLiouville

/-- Teschl §5.4, p. 155, (5.52): the weighted scalar product `⟨f, g⟩ = ∫_a^b f(x)* g(x) r(x) dx`
on `H₀ = C([a, b], ℂ)`, conjugate linear in the first argument. The norm of `H₀` is
`‖f‖ = √(Re ⟨f, f⟩)` (5.20). Every use applies it to functions continuous on `[a, b]`. -/
noncomputable def SLInner (r : ℝ → ℝ) (a b : ℝ) (f g : ℝ → ℂ) : ℂ :=
  ∫ x in a..b, starRingEnd ℂ (f x) * g x * (r x : ℂ)

end TeschlODE.SturmLiouville


