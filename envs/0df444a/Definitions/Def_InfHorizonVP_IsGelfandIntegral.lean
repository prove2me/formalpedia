-- Prove2me | Definitions.Def_InfHorizonVP_IsGelfandIntegral
-- name    : InfHorizonVP_IsGelfandIntegral
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:17:14.226798+00:00
-- url     : https://prove2.me/theorems/2687cd40-1e03-4329-adb1-709de52de1c4
-- title:
--   Gelfand integral $\int_A f\,dt$
-- statement:
--   Let $f:A\to E^*$. An element $x^*_A\in E^*$ is the **Gelfand (weak$^*$) integral** of $f$ over $A$ if for every $x\in E$ the function $t\mapsto\langle f(t),x\rangle$ is Lebesgue integrable on $A$ and
--   $$
--   \langle x^*_A,x\rangle=\int_A\langle f(t),x\rangle\,dt .
--   $$
--   The adjoint arc of Theorem 4.1 is $p(t)=\int_0^tf(s)\,ds-x^*$ in this sense.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §A.2, p.21

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Gelfand (weak\*) integral.**
Frankowska, Sagara, arXiv:1801.00400v3, §A.2, p.21: "a weakly* scalarly measurable function f is
said to be Gelfand integrable (or weakly* integrable) over a given set A ∈ 𝓛 if there exists
x*_A ∈ E* such that ⟨x*_A, x⟩ = ∫_A ⟨f(t), x⟩dt for every x ∈ E. The element x*_A is called the
Gelfand (or weak*) integral of f over A and is denoted by ∫_A f dt."

`IsGelfandIntegral f A z` says that `z` is the Gelfand integral of `f` over `A`.

**Formalization Note.** Each scalar function `⟨f(·), x⟩` is required to be Lebesgue integrable on
`A`, so that `∫_A ⟨f(t), x⟩ dt` is a genuine real integral (Lean's Bochner integral is `0` for a
non-integrable function). Integrability includes a.e. measurability on `A`. -/
def IsGelfandIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E →L[ℝ] ℝ) (A : Set ℝ) (z : E →L[ℝ] ℝ) : Prop :=
  ∀ x : E, IntegrableOn (fun t => f t x) A ∧ z x = ∫ t in A, f t x

end InfHorizonVP


