-- Prove2me | Definitions.Def_FracMPGA_liftedRatio
-- name    : FracMPGA_liftedRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:24.516857+00:00
-- url     : https://prove2.me/theorems/af1f67bc-93ec-4c10-80ba-a539d7f87d06
-- title:
--   The lifted ratio $\rho(x,y)=\varphi_1(x)/(\langle x,y\rangle-\varphi_2^*(y))$
-- statement:
--   Let $\varphi_1:\mathbb R^n\to(-\infty,+\infty]$ and $\varphi_2:\mathbb R^n\to\mathbb R$, with Fenchel conjugate $\varphi_2^*(y)=\sup_x\{\langle x,y\rangle-\varphi_2(x)\}$. The **lifted ratio** is
--   $$
--   \rho(x,y)=\begin{cases}\dfrac{\varphi_1(x)}{\langle x,y\rangle-\varphi_2^*(y)}, & (x,y)\in\operatorname{dom}\varphi_1\times\operatorname{dom}\varphi_2^*\text{ and }\langle x,y\rangle-\varphi_2^*(y)>0,\\[1ex] +\infty, & \text{otherwise.}\end{cases}
--   $$
--   The module also fixes $\mathbb R^n$ as the Euclidean space `Vec n`, the Euclidean product $\mathbb R^n\times\mathbb R^n$ as `Pair n`, the point $(x,y)$, and the denominator $\langle x,y\rangle-\varphi_2^*(y)\in[-\infty,+\infty)$.
--
--   With $\varphi_1=f+h$ and $\varphi_2=g$ it is the objective $Q$ of the reformulated problem.
--
--   **Formalization Note** On the domain branch the quotient is the real quotient of two finite values. The page prints $\varphi_2(y)$ inside the supremum defining $\varphi_2^*$, a typo for $\varphi_2(x)$.
-- source:
--   Zhou, Zhang, Li, An equivalent reformulation and multi-proximity gradient algorithms for a class of nonsmooth fractional programming, arXiv:2311.00957v2, §2.1, p.6 (the functions τ and ρ)

import Mathlib
import Definitions.Def_fenchelConjugate

open scoped InnerProductSpace

namespace FracMPGA

/-- `ℝⁿ` with the Euclidean norm and inner product. -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- `ℝⁿ × ℝⁿ` with the Euclidean norm `‖(x, y)‖₂ = (‖x‖₂² + ‖y‖₂²)^{1/2}` and inner product
`⟨x, x'⟩ + ⟨y, y'⟩` used throughout Zhou, Zhang, Li, arXiv:2311.00957v2. -/
abbrev Pair (n : ℕ) := WithLp 2 (Vec n × Vec n)

/-- The point `(x, y)` of `Pair n`. -/
def pair {n : ℕ} (x y : Vec n) : Pair n := WithLp.toLp 2 (x, y)

/-- The denominator `⟨x, y⟩ − φ₂*(y)` of the lifted ratio, valued in `[−∞, +∞)`
(Zhou, Zhang, Li, arXiv:2311.00957v2, p.6; for `φ₂ = g` it is `η(x, y)` of p.9). Here `φ₂*` is
the Fenchel conjugate `φ₂*(y) = sup_x (⟨x, y⟩ − φ₂(x))` (`ConvexOptimization.fenchelConjugate`;
the page prints `φ₂(y)` inside the supremum, a typo for `φ₂(x)`). If `φ₂*(y) = +∞` the value is
`−∞`. -/
noncomputable def liftDen {n : ℕ} (φ₂ : Vec n → ℝ) (x y : Vec n) : EReal :=
  ((⟪x, y⟫_ℝ : ℝ) : EReal) - ConvexOptimization.fenchelConjugate φ₂ y

/-- The **lifted ratio** `ρ` of Zhou, Zhang, Li, arXiv:2311.00957v2, §2.1, p.6: for
`φ₁ : ℝⁿ → (−∞, +∞]` and `φ₂ : ℝⁿ → ℝ` (the page assumes `dom(φ₂) = ℝⁿ`),
`ρ(x, y) := φ₁(x) / (⟨x, y⟩ − φ₂*(y))` if `(x, y) ∈ dom(φ₁) × dom(φ₂*)` and
`⟨x, y⟩ − φ₂*(y) > 0`, and `ρ(x, y) := +∞` otherwise.

**Formalization Note** On the domain branch both `φ₁ x` and the denominator are finite, and the
quotient is the real quotient of their real values. A function `φ₁` with values in
`(−∞, +∞]` never takes the value `⊥`; statements using `liftedRatio` assume this. -/
noncomputable def liftedRatio {n : ℕ} (φ₁ : Vec n → EReal) (φ₂ : Vec n → ℝ) (x y : Vec n) :
    EReal :=
  if φ₁ x ≠ ⊤ ∧ ConvexOptimization.fenchelConjugate φ₂ y ≠ ⊤ ∧ 0 < liftDen φ₂ x y then
    (((φ₁ x).toReal / (liftDen φ₂ x y).toReal : ℝ) : EReal)
  else ⊤

/-- The lifted ratio `ρ` as a function on the Euclidean product `Pair n`. -/
noncomputable def liftedRatioPair {n : ℕ} (φ₁ : Vec n → EReal) (φ₂ : Vec n → ℝ) (p : Pair n) :
    EReal :=
  liftedRatio φ₁ φ₂ p.ofLp.1 p.ofLp.2

end FracMPGA


