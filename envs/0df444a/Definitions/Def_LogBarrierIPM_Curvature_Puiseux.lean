-- Prove2me | Definitions.Def_LogBarrierIPM_Curvature_Puiseux
-- name    : LogBarrierIPM_Curvature_Puiseux
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:12:10.609981+00:00
-- url     : https://prove2.me/theorems/b38aac1f-f9e1-4f53-b3a5-2e36efaade19
-- title:
--   Absolutely convergent generalized real Puiseux series $\mathbb K$: evaluation $f(t)$ and valuation $\mathrm{val}\,f$
-- statement:
--   The field $\mathbb K$ of **absolutely convergent generalized real Puiseux series** consists of the formal series
--   $$f=\sum_{\alpha\in\mathbb R}a_\alpha t^\alpha,\qquad a_\alpha\in\mathbb R,$$
--   such that (i) the support $\{\alpha: a_\alpha\ne0\}$ is either finite or has $-\infty$ as its only accumulation point, and (ii) there is $\rho>0$ such that the series converges absolutely for every real $t>\rho$.
--
--   1. The **evaluation** of $f$ at a real $t>\rho$ is the real number $f(t)=\sum_\alpha a_\alpha t^\alpha$; for a vector $x\in\mathbb K^d$, $x(t)\in\mathbb R^d$ is evaluated coordinatewise.
--   2. The **valuation** $\mathrm{val}\,f\in\mathbb T=\mathbb R\cup\{-\infty\}$ is the greatest element of the support when $f\ne0$, and $-\infty$ for the null series; for $x\in\mathbb K^d$, $\mathrm{val}(x)\in\mathbb T^d$ is taken coordinatewise.
--   3. A vector $x\in\mathbb K^d$ is **non-null** when some coordinate is not the null series.
--
--   The paper reads its parametric family of linear programs as a single linear program over $\mathbb K$, and the valuation turns the central path over $\mathbb K$ into the tropical central path.
--
--   **Formalization Note** An element is encoded by its coefficient function $\alpha\mapsto a_\alpha$ together with (i), stated as: for every $c$ only finitely many $\alpha\ge c$ have $a_\alpha\ne0$, and (ii), the summability of $\alpha\mapsto|a_\alpha|t^\alpha$ for $t>\rho$. Only evaluation and valuation are defined; no field operations are needed by the statements that use this module (equalities, products and order in $\mathbb K$ are expressed through evaluations at large $t$, which is how the paper characterizes them on p. 7). The valuation is the real supremum of the support, which is bounded above and attained by (i). Vectors evaluated at $t$ are `EuclideanSpace` points; valuations are `WithBot ℝ`, with $\bot=-\infty$.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 7, §3.1, eq. (7) and the valuation map

import Mathlib

namespace LogBarrierIPM.Curvature

/-- An element `f = ∑_{α ∈ ℝ} a_α t^α` of the field `𝕂` of absolutely convergent generalized real
Puiseux series (§3.1, (7), p. 7), given by its coefficient function `α ↦ a_α`:
(i) the support is finite or has `−∞` as its only accumulation point, i.e. it meets every
half-line `[c, ∞)` in a finite set; (ii) there is `ρ > 0` such that the series converges
absolutely for all `t > ρ`. -/
structure Puiseux where
  /-- the coefficient `a_α` of `t^α` -/
  coeff : ℝ → ℝ
  /-- (i): finitely many exponents `α ≥ c` carry a non-zero coefficient, for every `c` -/
  support_finite_above : ∀ c : ℝ, {α : ℝ | c ≤ α ∧ coeff α ≠ 0}.Finite
  /-- (ii): absolute convergence for all sufficiently large `t` -/
  abs_summable : ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, ρ < t → Summable (fun α : ℝ => |coeff α| * t ^ α)

namespace Puiseux

/-- The evaluation `f(t) = ∑_α a_α t^α ∈ ℝ` of a Puiseux series at a real `t` (meaningful for
`t > ρ`). -/
noncomputable def eval (f : Puiseux) (t : ℝ) : ℝ :=
  ∑' α : ℝ, f.coeff α * t ^ α

/-- The valuation `val f ∈ 𝕋 = ℝ ∪ {−∞}` (p. 7): the greatest element of the support of `f` when
`f ≠ 0`, and `−∞` (`⊥`) for the null series. By (i) a non-empty support is bounded above and
attains its supremum. -/
noncomputable def val (f : Puiseux) : WithBot ℝ :=
  open Classical in
  if (Function.support f.coeff).Nonempty then ((sSup (Function.support f.coeff) : ℝ) : WithBot ℝ)
  else ⊥

end Puiseux

/-- A vector `x ∈ 𝕂^d` is non-null: some coordinate is not the null series. -/
def IsNonNull {d : ℕ} (x : Fin d → Puiseux) : Prop :=
  ∃ i : Fin d, ∃ α : ℝ, (x i).coeff α ≠ 0

/-- The real vector `x(t) ∈ ℝ^d` obtained by evaluating every coordinate of `x ∈ 𝕂^d` at `t`,
as a point of Euclidean space. -/
noncomputable def evalVec {d : ℕ} (x : Fin d → Puiseux) (t : ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (x i).eval t)

/-- The coordinate-wise valuation `val(x) ∈ 𝕋^d` of `x ∈ 𝕂^d`. -/
noncomputable def valVec {d : ℕ} (x : Fin d → Puiseux) : Fin d → WithBot ℝ :=
  fun i => (x i).val

end LogBarrierIPM.Curvature


