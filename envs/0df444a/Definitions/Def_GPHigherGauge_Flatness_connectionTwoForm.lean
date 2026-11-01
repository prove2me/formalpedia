-- Prove2me | Definitions.Def_GPHigherGauge_Flatness_connectionTwoForm
-- name    : GPHigherGauge_Flatness_connectionTwoForm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:55:40.945181+00:00
-- url     : https://prove2.me/theorems/7eb695f5-9c91-40e9-ae94-949bb12fe53b
-- title:
--   The connection 2-form $B_{\mu\nu}(x)$ of a family of square labels
-- statement:
--   Let $H$ be a real Lie group with Lie algebra $\mathfrak h=T_1H$. A family of **square labels** assigns to each pair of directions $\mu,\nu$, base point $x\in\mathbb R^n$ and side $a\in\mathbb R$ the element $h_{\mu\nu}(x,a)\in H$ labelling the square at $x$ spanned by $a\,e_\mu$ and $a\,e_\nu$.
--
--   The **connection 2-form** is the coefficient of $a^2$ of the square label at $a=0$, read in the chart $\varphi_1$ of $H$ at the unit:
--   $$B_{\mu\nu}(x)=\frac12\,\frac{d^2}{da^2}\Big|_{a=0}\varphi_1\big(h_{\mu\nu}(x,a)\big)\in\mathfrak h .$$
--
--   This is the field $B$ of the paper's ansatz $h_{\mu\nu}\sim e^{a^2B_{\mu\nu}}$; the factor $\tfrac12$ makes $a^2B_{\mu\nu}$ the second-order Taylor term.
--
--   **Formalization Note** The ansatz is read as $h_{\mu\nu}(x,0)=1$, first $a$-derivative $0$ at $a=0$, and this second derivative. Under those conditions (assumed wherever the definition is used) the value transforms as a tangent vector at $1$. The chart is `extChartAt` at $1$, the same in which derivatives at $1$ are computed.
-- source:
--   Girelli, Pfeiffer, Higher gauge theory — differential versus integral formulation, arXiv:hep-th/0309173v2, §3.3, Eq. (3.16) and the sentence after it, p. 15

import Mathlib

open scoped Manifold ContDiff

namespace GPHigherGauge.Flatness

/-- The connection 2-form `B_μν(x)` of a family of square labels.

Girelli, Pfeiffer, *Higher gauge theory — differential versus integral formulation*,
arXiv:hep-th/0309173v2, §3.3, Eq. (3.16), p. 15:
"h_µν(0) = e^{∫_S B} ∼ e^{a²B_µν}. [...] S a square of area a² in the (µν)-plane", and
"the 𝔥-valued connection 2-form B = ½B_µν dx^µ ∧ dx^ν".

The square labels are `h : Fin n → Fin n → ℝⁿ → ℝ → H`, with `h μ ν x a` the label in `H` of the
square at `x` spanned by `a • e_μ` and `a • e_ν` (Figure 1(c), p. 15). `B_μν(x)` is the
coefficient of `a²` of the curve `a ↦ h μ ν x a`, read in the chart of `H` at `1`:
`B_μν(x) = ½ · d²/da² (φ₁ (h μ ν x a))|_{a=0}`, an element of `𝔥 = T₁H`.

**Formalization Note** Reading 2: "h_μν ∼ e^{a²B_μν}" is read as `h μ ν x 0 = 1`, first
`a`-derivative `0` at `a = 0`, and this second-derivative definition. The factor `½` is the one
that makes `a²B` the second-order Taylor term. Under the zero-velocity hypothesis (imposed in
`IsSmoothSquareLabels`) the value transforms as a tangent vector at `1`, so it does not depend on
the chart beyond its linearization; the chart used is `extChartAt 𝓘(ℝ, F) 1`, the same in which
`mfderiv` at `1` is computed. Off those hypotheses the value is not meaningful. -/
noncomputable def connectionTwoForm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] [ChartedSpace F H] [Group H] {n : ℕ}
    (h : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ → H) (μ ν : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : GroupLieAlgebra 𝓘(ℝ, F) H :=
  (1 / 2 : ℝ) • deriv (deriv (fun a => extChartAt 𝓘(ℝ, F) (1 : H) (h μ ν x a))) 0

end GPHigherGauge.Flatness


