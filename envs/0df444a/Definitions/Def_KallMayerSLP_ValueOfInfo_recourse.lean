-- Prove2me | Definitions.Def_KallMayerSLP_ValueOfInfo_recourse
-- name    : KallMayerSLP_ValueOfInfo_recourse
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:10.774854+00:00
-- url     : https://prove2.me/theorems/9a7138a7-010b-4eb6-9158-3cd95da066f4
-- title:
--   Recourse function $Q(x;T(\xi),h(\xi),W(\xi),q(\xi))$
-- statement:
--   For a first-stage decision $x$ and a realization $\xi$, the optimal value of the second-stage linear program
--
--   $$
--   Q(x;T(\xi),h(\xi),W(\xi),q(\xi))=\inf_y\{q(\xi)^{\mathsf T}y : W(\xi)y=h(\xi)-T(\xi)x,\ y\ge 0\}\in[-\infty,+\infty],
--   $$
--
--   which is $+\infty$ if the second stage is infeasible and $-\infty$ if it is unbounded below.
--
--   **Formalization Note** It is the platform definition `StochasticProg.RecourseKKT.secondStageValue` (the extended-real infimum of $q^{\mathsf T}y$ over $\{y\ge0: Wy=h-Tx\}$) evaluated at the realized data. The book's infimum over $y(\cdot)\in Y=L^2(\Omega,\mathbb R^{n_2})$ with almost-sure constraints is taken realization by realization, as the book uses it ("$\forall\xi\in\Xi$", p.245).
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, eq. (2.66), p.243 (PDF 252) and (2.4), p.200 (PDF 209)

import Mathlib
import Definitions.Def_KallMayerSLP_ValueOfInfo_TwoStageSLP
import Definitions.Def_StochasticProg_RecourseKKT_secondStageValue

namespace KallMayerSLP.ValueOfInfo

/-- **The recourse function `Q(x; T(ξ), h(ξ), W(ξ), q(ξ))`, (2.66)/(2.4).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, p.243 (PDF 252):
`Q(x; T(ξ), h(ξ), W(ξ), q(ξ)) := inf q(ξ)ᵀy(ξ)` s.t. `W(ξ)y(ξ) = h(ξ) − T(ξ)x`, `y(ξ) ≥ 0`.

It is the platform's second-stage linear-program value
`StochasticProg.RecourseKKT.secondStageValue W q h T x = inf {qᵀy | Wy = h − Tx, y ≥ 0}` evaluated at
the realized data `(W(ξ), q(ξ), h(ξ), T(ξ))`.

**Formalization Note.** The value lies in `EReal`: `+∞` if the second stage is infeasible (infimum
of the empty set), `−∞` if it is unbounded, the book's "usual convention" of p.200. The book's
infimum over `y(·) ∈ Y = L²` with almost-sure constraints is taken realization by realization,
which is how the book uses it (`∀ ξ ∈ Ξ` in the proof of Prop. 2.2, p.245). -/
noncomputable def recourse {r n₁ m₁ n₂ m₂ : ℕ} (P : TwoStageSLP r n₁ m₁ n₂ m₂)
    (x : Fin n₁ → ℝ) (ξ : Fin r → ℝ) : EReal :=
  StochasticProg.RecourseKKT.secondStageValue (P.W ξ) (P.q ξ) (P.h ξ) (P.T ξ) x

end KallMayerSLP.ValueOfInfo


