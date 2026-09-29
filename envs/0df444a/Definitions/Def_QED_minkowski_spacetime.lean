-- Prove2me | Definitions.Def_QED_minkowski_spacetime
-- name    : QED_minkowski_spacetime
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-21T03:41:37.439821+00:00
-- url     : https://prove2.me/theorems/729d17db-139e-4ac3-b6b9-eaef628308b8
-- title:
--   Minkowski spacetime: the metric $\eta$, the derivatives $\partial_\mu$ and the wave operator $\Box$
-- statement:
--   The coordinate layer of classical field theory on flat spacetime. A point of **Minkowski spacetime** is a quadruple of real coordinates $x=(x^0,x^1,x^2,x^3)$. The **Minkowski metric** $\eta$ has signature $(+,-,-,-)$, so $\eta_{00}=1$, $\eta_{11}=\eta_{22}=\eta_{33}=-1$ and $\eta_{\mu\nu}=0$ off the diagonal; because $\eta$ is its own inverse, the same array is used for the contravariant metric $\eta^{\mu\nu}$ that raises indices.
--
--   For a field $f$ on spacetime with values in a real normed space, the **partial derivative** $\partial_\mu f(x)$ is the Fréchet derivative of $f$ at $x$ evaluated on the $\mu$-th coordinate direction; where $f$ is not differentiable it takes the value $0$, so the operator is total and every statement using it carries its own smoothness hypotheses. The **d'Alembert wave operator** is the contraction
--   $$\Box f=\eta^{\mu\nu}\partial_\mu\partial_\nu f=\partial_0^2f-\partial_1^2f-\partial_2^2f-\partial_3^2f.$$
--   These are the conventions shared by every statement of the mission.
-- source:
--   Wikipedia, "Quantum electrodynamics", section "Mathematical formulation", subsections "QED action" and "Equations of motion" (QED Lagrangian, Dirac matrices, covariant derivative, field tensor, conserved current, Euler-Lagrange equations for psi and A, Lorenz-gauge wave equation). https://en.wikipedia.org/wiki/Quantum_electrodynamics

import Mathlib

namespace QED

/-- Minkowski spacetime in coordinates: a point `x` is the quadruple of its
contravariant coordinates `x⁰, x¹, x², x³`. -/
abbrev Spacetime : Type := Fin 4 → ℝ

/-- The Minkowski metric `η` with signature `(+, -, -, -)`:
`η 0 0 = 1`, `η i i = -1` for `i = 1, 2, 3`, and `η μ ν = 0` for `μ ≠ ν`.
Since `η` is its own inverse, the same function is used for the contravariant
metric `η^{μν}` used to raise indices. -/
def minkowski (μ ν : Fin 4) : ℝ :=
  if μ = ν then (if μ = 0 then 1 else -1) else 0

/-- The partial derivative `∂_μ f` of a field `f` on Minkowski spacetime with
values in a real normed space, i.e. the Fréchet derivative of `f` evaluated on
the `μ`-th coordinate direction. If `f` is not differentiable at `x`, this is
`0` by the junk-value convention for `fderiv`. -/
noncomputable def partialD {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Fin 4) (f : Spacetime → E) (x : Spacetime) : E :=
  fderiv ℝ f x (Pi.single μ 1)

/-- The d'Alembert wave operator `□ f = η^{μν} ∂_μ ∂_ν f`. -/
noncomputable def dAlembert {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Spacetime → E) (x : Spacetime) : E :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, minkowski μ ν • partialD μ (partialD ν f) x

end QED


