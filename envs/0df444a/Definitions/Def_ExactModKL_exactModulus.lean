-- Prove2me | Definitions.Def_ExactModKL_exactModulus
-- name    : ExactModKL_exactModulus
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:56:53.348746+00:00
-- url     : https://prove2.me/theorems/7f7d3cc5-b45b-48e3-a154-707e0ae0c9a7
-- title:
--   The exact modulus $\tilde\varphi$ of the generalized concave KL property
-- statement:
--   Let $f:\mathbb R^n\to(-\infty,\infty]$, $\bar x\in\mathbb R^n$, $U\subseteq\mathbb R^n$ and $\eta\in(0,\infty]$, and let $h$ be as in Definition 3.6. The exact modulus of the generalized concave KL property of $f$ at $\bar x$ with respect to $U$ and $\eta$ is
--   $$
--   \tilde\varphi(t)=\int_0^t h(s)\,ds\quad(t\in(0,\eta)),\qquad\tilde\varphi(0)=0 .
--   $$
--   If $U\cap[0<f-f(\bar x)<\eta]=\emptyset$, then $\tilde\varphi\equiv0$. Proposition 3.9 shows that it is the smallest concave desingularizing function.
--
--   **Formalization Note** The integral is the Lebesgue integral of the $[0,\infty]$-valued $h$ over $(0,t]$, converted to a real number. For $h\ge0$ it equals the paper's possibly improper integral. Proposition 3.9 proves it finite on $[0,\eta)$, so the conversion loses nothing there. On an empty band $h\equiv0$, so $\tilde\varphi\equiv0$ as the paper prescribes.
-- source:
--   Wang–Wang, arXiv:2008.13257v5, Definition 3.6, p.11

import Mathlib
import Definitions.Def_ExactModKL_hfun

open scoped ENNReal

namespace ExactModKL

/-- The exact modulus of the generalized concave KL property of `f` at `x̄` with respect to `U`
and `η` (Wang–Wang, arXiv:2008.13257v5 (preprint), Definition 3.6, p.11):
`ϕ̃(t) = ∫₀ᵗ h(s) ds` for `t ∈ (0, η)` and `ϕ̃(0) = 0`; if `U ∩ [0 < f − f(x̄) < η] = ∅`, then
`ϕ̃ ≡ 0`.

**Formalization Note.** The integral is the Lebesgue integral of the `ℝ≥0∞`-valued `h` over
`(0, t]`, which for `h ≥ 0` equals the paper's (possibly improper) integral (Remark 3.7(ii)).
It is converted to a real number with `ENNReal.toReal`; Proposition 3.9 proves the integral
finite on `[0, η)`, so nothing is lost there. At `t = 0` (and `t ≤ 0`) the domain is empty and
`ϕ̃ = 0`. On an empty band `h ≡ 0` (`sup ∅ = 0`), so `ϕ̃ ≡ 0`, the paper's convention. -/
noncomputable def exactModulus {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar : EuclideanSpace ℝ (Fin n)) (U : Set (EuclideanSpace ℝ (Fin n))) (η : ℝ≥0∞)
    (t : ℝ) : ℝ :=
  (∫⁻ s in Set.Ioc 0 t, hfun f xbar U η s).toReal

end ExactModKL


