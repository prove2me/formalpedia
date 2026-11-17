-- Prove2me | Definitions.Def_ABPOnline_Supplement_Vrelax
-- name    : ABPOnline_Supplement_Vrelax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:34:39.435805+00:00
-- url     : https://prove2.me/theorems/88f687d0-c376-438c-ad71-29c685a5e613
-- title:
--   The weighted $L^2$ relaxation $V_\kappa(\eta)$ of the Brownian control value
-- statement:
--   Let $B=(B_t)_{0\le t\le1}$ be a standard Brownian motion with its completed natural filtration, and let $\eta:(0,1)\to(0,\infty)$ be a weight. For a control $u$ write $Y^u_1=B_1+\int_0^1u_t\,dt$. The **weighted $L^2$ relaxation** of the Brownian control value at margin $\kappa\in\mathbb R$ is
--   $$
--   V_\kappa(\eta):=\inf_{Y^u_1\ge\kappa\ \text{a.s.}}\ \mathbb E\int_0^1\eta(t)\,u_t^2\,dt ,
--   $$
--   where the infimum is over controls that are progressively measurable with respect to the Brownian filtration and have finite integrated second moment $\mathbb E\int_0^1u_t^2\,dt<\infty$.
--
--   Replacing the uniform-in-time second-moment constraint of $E_\star(\kappa)$ by a weighted time average gives, for normalized weights, lower bounds on $E_\star(\kappa)$; for piecewise-constant weights $V_\kappa(\eta)$ is computed exactly by a one-dimensional recursion (Theorem 5.3).
--
--   **Formalization Note** The value lies in $[0,\infty]$, so an empty feasible set gives $+\infty$. The cost is $\int_0^1\eta(t)\,\mathbb E u_t^2\,dt$ written with the published second moment $t\mapsto\mathbb Eu_t^2$ (equal to $\mathbb E\int_0^1\eta u^2$ by Tonelli for progressive controls); the terminal value is the published $Y^u_1$ of `ABPOnline.Estar`. The weight is a real function of which only the values on $(0,1)$ enter.
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), §5.1, (35), p.19 (PDF p.20)

import Mathlib
import Definitions.Def_ABPOnline_Estar

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ABPOnline.Supplement

/-- The **weighted `L²` relaxation** of the Brownian control value (Jo–Lee, arXiv:2609.02124,
§5.1, (35), printed p.19, PDF p.20):
`V_κ(η) := inf { E ∫₀¹ η(t) u_t² dt : Y^u_1 = B_1 + ∫₀¹ u_t dt ≥ κ a.s. }`,
the infimum over controls `u` progressively measurable for the (completed natural) Brownian
filtration and with finite integrated second moment `E ∫₀¹ u_t² dt < ∞`.

**Formalization Note** Time is `ℝ≥0` as in the published `ABPOnline.Estar`; the weight `η` is a
real function of which only the values on `(0,1)` are used (negative values would be read as `0`,
but the paper's weights are positive). Both time integrals are lower Lebesgue integrals over
`(0,1)` of the published second moment `t ↦ E u_t²` (Tonelli: for a progressive, hence jointly
measurable, control this is `E ∫₀¹ η u²`). The value is in `ℝ≥0∞`: an empty feasible set gives
`⊤`, never a junk `0`. The constraint set is the paper's: finite integrated second moment, not the
finite `‖u‖_{∞,2}` of `E⋆`. The terminal value is the published `ABPOnline.ctrlTerminal`. -/
noncomputable def Vrelax {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (κ : ℝ) (η : ℝ → ℝ) : ℝ≥0∞ :=
  ⨅ (u : ℝ≥0 → Ω → ℝ) (_ : IsStronglyProgressive (brownFiltration P B) u ∧
      (∫⁻ t in Set.Ioo (0 : ℝ) 1, secondMoment P u t) < ⊤ ∧
      ∀ᵐ ω ∂P, κ ≤ ctrlTerminal B u 1 ω),
    ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (η t) * secondMoment P u t

end ABPOnline.Supplement


