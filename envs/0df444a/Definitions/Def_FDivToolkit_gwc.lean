-- Prove2me | Definitions.Def_FDivToolkit_gwc
-- name    : FDivToolkit_gwc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:23:59.728158+00:00
-- url     : https://prove2.me/theorems/d6102fec-ab10-4535-9f47-919722a50213
-- title:
--   The worst-case density $g^{wc}$ and its defining conditions
-- statement:
--   For parameters $(\alpha_1,\alpha_2)\in\mathbb R^2$, the **worst-case density** is
--   $$
--   g^{wc}(x)=\mathbf 1_{\{\alpha_1+\alpha_2x>L\}}\exp\!\big(H^{-1}(\alpha_1+\alpha_2x)\big)f(x),\qquad x\in\mathcal S. \tag{6}
--   $$
--   The parameters belonging to a radius $\kappa$ are the $(\alpha_1,\alpha_2)\in\mathbb R\times(0,\infty)$ with $\int g^{wc}=1$ and $D_F(\eta^{wc}\,|\,\nu)=\kappa$ (`IsWcParam`).
--
--   This is the explicit form of the worst-case model in Proposition 1.
--
--   **Formalization Note** The indicator is the test $\alpha_1+\alpha_2x\in\operatorname{range}H$, since the range of $H$ is $(L,\infty)$.
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), display (6), Proposition 1, p.8

import Definitions.Def_FDivToolkit_ball
import Definitions.Def_FDivToolkit_IsAdmissibleH

namespace FDivToolkit

open Classical in
/-- The worst-case density of display (6), Kruse, Schneider & Schweizer, SSRN 3680475
(Aug 25, 2020), Proposition 1, p.8:
`g^wc(x) = 1_{α₁ + α₂x > L} exp(H⁻¹(α₁ + α₂x)) f(x)`, with `L = lim_{y→−∞} H(y)`.

**Formalization Note.** For an admissible `H`, `s > L` is equivalent to `s ∈ Set.range H`, because
that range is the open ray `(L, ∞)`. The range test therefore is the paper's indicator, and `Hinv`
is applied on the range only. -/
noncomputable def gwc (H f : ℝ → ℝ) (α : ℝ × ℝ) (x : ℝ) : ℝ :=
  if α.1 + α.2 * x ∈ Set.range H then Real.exp (Hinv H (α.1 + α.2 * x)) * f x else 0

/-- The two conditions that characterize the worst-case parameters `(α₁, α₂) ∈ ℝ × (0, ∞)` for the
radius `κ` (Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), Proposition 1, p.8):
`g^wc` integrates to `1`, and `D_F(η^wc|ν) = κ`. -/
def IsWcParam (H f : ℝ → ℝ) (κ : ℝ) (α : ℝ × ℝ) : Prop :=
  0 < α.2 ∧ ∫ x, gwc H f α x = 1 ∧ fDiv (Fbar H) f (gwc H f α) = ENNReal.ofReal κ

end FDivToolkit


