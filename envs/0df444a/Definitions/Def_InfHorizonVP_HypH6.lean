-- Prove2me | Definitions.Def_InfHorizonVP_HypH6
-- name    : InfHorizonVP_HypH6
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:25.685824+00:00
-- url     : https://prove2.me/theorems/1bf561bd-6fe5-488a-9da9-c0d0cb6256a7
-- title:
--   Hypothesis (H6): Lipschitz multifunction with modulus $\gamma$
-- statement:
--   **(H6)** with modulus $\gamma$: $\gamma:\mathbb R_+\to\mathbb R_+$ is locally integrable and, with $B$ the open unit ball of $E$, for every $t\ge0$ and $x,x'\in E$,
--   $$
--   \Gamma(t,0)\subset\gamma(t)B,\qquad \Gamma(t,x)\subset\Gamma(t,x')+\gamma(t)\|x-x'\|B .
--   $$
--
--   **Formalization Note** $rB$ is the pointwise scalar multiple of the open unit ball (it is $\{0\}$ for $r=0$); the sum is a Minkowski sum.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §3.2, p.9, (H6)

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Hypothesis (H6), with the modulus `γ`.**
Frankowska, Sagara, arXiv:1801.00400v3, §3.2, p.9: "(H6) There exist a locally integrable
function γ : R+ → R+ such that Γ(t, 0) ⊂ γ(t)B and Γ(t, x) ⊂ Γ(t, x′) + γ(t)‖x − x′‖B for every
t ∈ R+ and x, x′ ∈ E." Here "B [is] the open unit ball in E" (p.5).

**Formalization Note.** `γ(t)B` is the pointwise scalar multiple `γ t • ball 0 1` (which is `{0}`
when `γ(t) = 0`); the second inclusion is a Minkowski sum. "Locally integrable" is integrability
on every `[0, T]`; `R+`-valued is nonnegativity on `[0, ∞)`. The modulus is an argument; the same
`γ` enters (H7). -/
def HypH6 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Γ : ℝ → E → Set E) (γ : ℝ → ℝ) : Prop :=
  (∀ T, IntegrableOn γ (Icc 0 T)) ∧ (∀ t, 0 ≤ t → 0 ≤ γ t) ∧
  (∀ t, 0 ≤ t → Γ t 0 ⊆ γ t • Metric.ball (0 : E) 1) ∧
  ∀ t, 0 ≤ t → ∀ x x' : E, Γ t x ⊆ Γ t x' + (γ t * ‖x - x'‖) • Metric.ball (0 : E) 1

end InfHorizonVP


