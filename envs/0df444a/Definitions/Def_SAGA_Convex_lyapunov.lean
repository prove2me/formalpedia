-- Prove2me | Definitions.Def_SAGA_Convex_lyapunov
-- name    : SAGA_Convex_lyapunov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:24:56.943243+00:00
-- url     : https://prove2.me/theorems/9879db20-ce4b-47c2-8e57-d2a35cad2399
-- title:
--   The SAGA Lyapunov function $T(x,\phi)$
-- statement:
--   Fix a reference point $x^*$ and a coefficient $a\in\mathbb R$. For a SAGA state $(x,\phi)$ with table $\phi_1,\dots,\phi_n$, the **Lyapunov function** is
--
--   $$
--   T(x,\phi)=\frac1n\sum_{i=1}^n f_i(\phi_i)-f(x^*)-\frac1n\sum_{i=1}^n\big\langle f_i'(x^*),\phi_i-x^*\big\rangle+a\,\|x-x^*\|^2 .
--   $$
--
--   This is the function $T$ of Theorem 1 (p. 7) with the coefficient $c$ of $\|x-x^*\|^2$ replaced by a free $a$. In the proof of Theorem 2 (pp. 11–12) the coefficient is $a=c+\alpha$, with $c=\frac{3L}{2n}$ and $\alpha=\frac{3L}{8n}$.
--
--   **Formalization Note** `lyapunov f f' xs a s` is $T$ at the state `s = (x, φ)`.
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, p. 7, Theorem 1 (definition of T); p. 11, proof of Theorem 2 (added alpha term)

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum

open scoped RealInnerProductSpace

namespace SAGA.Convex

/-- The Lyapunov function of Theorem 1 (p. 7) with the coefficient `a` of `‖x - x*‖²`:
`T(x, φ) = (1/n) ∑ᵢ fᵢ(φᵢ) - f(x*) - (1/n) ∑ᵢ ⟨f′ᵢ(x*), φᵢ - x*⟩ + a ‖x - x*‖²`.
In the proof of Theorem 2 (Appendix C, pp. 11–12) `a = c + α`. -/
noncomputable def lyapunov {d n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (xs : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, f i (s.2 i) - fAvg f xs
    - (1 / (n : ℝ)) * ∑ i, ⟪f' i xs, s.2 i - xs⟫ + a * ‖s.1 - xs‖ ^ 2

end SAGA.Convex


