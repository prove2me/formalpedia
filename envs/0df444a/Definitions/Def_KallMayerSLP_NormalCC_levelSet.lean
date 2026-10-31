-- Prove2me | Definitions.Def_KallMayerSLP_NormalCC_levelSet
-- name    : KallMayerSLP_NormalCC_levelSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:56.183108+00:00
-- url     : https://prove2.me/theorems/378b4bc6-814e-4d0c-9c37-84575aebfce1
-- title:
--   Feasible set $\mathcal B(\alpha)=\{x\mid G(x)\ge\alpha\}$ of a separate chance constraint
-- statement:
--   For a probability level $\alpha\in\mathbb R$, the feasible set of the separate chance constraint is
--   $$\mathcal B(\alpha)=\{x\in\mathbb R^n\mid G(x)\ge\alpha\},\qquad G(x)=\mathbb P(\eta^{\mathsf T}x\ge\xi).$$
--
--   Theorems 2.5, 2.6 and 2.7 are statements about the convexity of $\mathcal B(\alpha)$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Theorem 2.5, p.107 (PDF p.117)

import Mathlib
import Definitions.Def_KallMayerSLP_NormalCC_probFun

open MeasureTheory

namespace KallMayerSLP.NormalCC

/-- **The feasible set of a separate chance constraint** (Kall & Mayer 2005, Chapter 2,
Theorem 2.5, p.107, PDF p.117): `B(α) = { x | G(x) ≥ α }`, with `G(x) = ℙ(ηᵀx ≥ ξ)` the
probability function `probFun` of (2.31).

**Formalization Note.** `α` is any real number; no range restriction is built in. -/
def levelSet {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (η : Ω → Fin n → ℝ) (ξ : Ω → ℝ) (α : ℝ) : Set (Fin n → ℝ) :=
  {x | α ≤ probFun P η ξ x}

end KallMayerSLP.NormalCC


