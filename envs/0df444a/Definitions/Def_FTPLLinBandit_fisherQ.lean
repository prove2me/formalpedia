-- Prove2me | Definitions.Def_FTPLLinBandit_fisherQ
-- name    : FTPLLinBandit_fisherQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:59.219525+00:00
-- url     : https://prove2.me/theorems/30d4beef-0ec9-4b34-baf8-72c3b5adb6ee
-- title:
--   Shifted Fisher-information matrix $\mathcal I^v(\rho)$ (Definition 1), as a quadratic form
-- statement:
--   Let $\rho$ be a probability density on $\mathbb R^d$ that is positive almost everywhere, and $v\in\mathbb R^d$. The **shifted Fisher-information matrix** is
--   $$\mathcal I^v(\rho)=\int_{\mathbb R^d}\frac{\nabla\rho(z)\nabla\rho(z)^\top}{\rho(z+v)}\,dz ,$$
--   and for $u\in\mathbb R^d$ its quadratic form is
--   $$u^\top\mathcal I^v(\rho)u=\int_{\mathbb R^d}\frac{\langle\nabla\rho(z),u\rangle^2}{\rho(z+v)}\,dz\in[0,\infty].$$
--   At $v=0$ it is the Fisher information matrix $\mathcal I(\rho)$. At round $t$ the paper writes $\mathcal I^v_t=\mathcal I^v(\rho_t)$; Theorems 4 and 7 bound the stability terms through it.
--
--   **Formalization Note** The value lies in $[0,\infty]$ (a lower Lebesgue integral), so an infinite information is $\infty$, never a junk $0$. Where $\rho(z+v)=0$ the Lean quotient is $0$; for $\rho$ positive almost everywhere this is a null set of $z$.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Definition 1, Eq. (11), p.11

import Mathlib

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace FTPLLinBandit

/-- **The shifted Fisher-information matrix `I^v(ρ)` (Definition 1), as a quadratic form.** Wei,
arXiv:2610.17818, Definition 1, Eq. (11), p.11: "Let ρ be a probability density on ℝ^d that is
positive almost everywhere. Define the shifted Fisher-information matrix by
I^v(ρ) = ∫_{ℝ^d} ∇ρ(z)∇ρ(z)ᵀ / ρ(z + v) dz".

`fisherQ ρ v u = ∫ ⟨∇ρ(z), u⟩² / ρ(z + v) dz = uᵀ I^v(ρ) u ∈ [0, ∞]`.

**Formalization Note.** The value is an extended nonnegative real (a lower Lebesgue integral), so
an infinite information is `∞` (e.g. Table 4 notes that an information of Student-t₂ is
infinite) and never a junk `0`. `gradient ρ` is Mathlib's gradient (`0` off the differentiability
set, a null set for locally Lipschitz `ρ`). Where `ρ(z + v) = 0` Lean's quotient is `0`; for `ρ`
positive almost everywhere (Definition 1's hypothesis, stated in every theorem using `fisherQ`)
this is a null set of `z`. -/
noncomputable def fisherQ {d : ℕ} (ρ : EuclideanSpace ℝ (Fin d) → ℝ)
    (v u : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (⟪gradient ρ z, u⟫_ℝ ^ 2 / ρ (z + v))

end FTPLLinBandit


