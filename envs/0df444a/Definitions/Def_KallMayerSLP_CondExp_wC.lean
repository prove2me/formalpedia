-- Prove2me | Definitions.Def_KallMayerSLP_CondExp_wC
-- name    : KallMayerSLP_CondExp_wC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:11:02.408464+00:00
-- url     : https://prove2.me/theorems/0258bce0-6586-4369-909c-fb6be05d3975
-- title:
--   Joint CVaR function $w_c^\alpha(x,z)$
-- statement:
--   Let $\zeta(x,\xi)=t(\xi)^{\mathrm T}x-h(\xi)$, where $t(\xi)$ is an $n$-dimensional random vector and $h(\xi)$ a random variable. For $x\in\mathbb R^n$, $z\in\mathbb R$ and $0<\alpha<1$,
--   $$
--   w_c^\alpha(x,z)=z+\frac{1}{1-\alpha}\,\mathbb E[(\zeta(x,\xi)-z)^+].
--   $$
--   Minimizing over $z$ gives the evaluation function $v_c(x,\alpha)$; minimizing over $(x,z)$ jointly gives the CVaR model (4.35).
--
--   **Formalization Note** $t(\xi)$ and $h(\xi)$ are maps on the underlying probability space.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §4.3, p.162

import Mathlib
import Definitions.Def_KallMayerSLP_CondExp_cvarObjective

open MeasureTheory

namespace KallMayerSLP.CondExp

/-- The function `w_c^α(x, z) := z + (1 / (1 - α)) 𝔼[(ζ(x, ξ) - z)⁺]`, where
`ζ(x, ξ) := t(ξ)ᵀx - h(ξ)`.
Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §4.3, p.162 (PDF 172).

**Formalization Note** The random vector `t(ξ)` and the random variable `h(ξ)` are the maps
`t : Ω → (Fin n → ℝ)` and `h : Ω → ℝ` on the underlying probability space. -/
noncomputable def wC {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω)
    (t : Ω → Fin n → ℝ) (h : Ω → ℝ) (α : ℝ) (x : Fin n → ℝ) (z : ℝ) : ℝ :=
  cvarObjective μ (fun ω => t ω ⬝ᵥ x - h ω) α z

end KallMayerSLP.CondExp


