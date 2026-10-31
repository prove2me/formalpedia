-- Prove2me | Definitions.Def_FDivToolkit_Cond5
-- name    : FDivToolkit_Cond5
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:21:58.996434+00:00
-- url     : https://prove2.me/theorems/c44a0b98-28a6-4b0b-b77d-dcb17d399385
-- title:
--   Condition (5)
-- statement:
--   Condition (5) says that for all $\alpha\in[0,\infty)$,
--   $$
--   \int_{\mathcal S}|x|\exp\!\big(H^{-1}(\alpha|x|)\big)f(x)\,dx<\infty.
--   $$
--
--   It is the integrability hypothesis of Proposition 1, relating the tail of $\nu$ to the growth of $H^{-1}$.
--
--   **Formalization Note** $\alpha|x|\ge0$ lies in the range of $H$, and finiteness of the nonnegative integral is `Integrable`.
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), display (5), Proposition 1, p.8

import Definitions.Def_FDivToolkit_IsAdmissibleH

open MeasureTheory

namespace FDivToolkit

/-- Condition (5), Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), Proposition 1, p.8:
for all `α ∈ [0, ∞)`, `∫_𝓢 |x| exp(H⁻¹(α|x|)) f(x) dx < ∞`.

**Formalization Note.** `α|x| ≥ 0` lies in the range of an admissible `H`, so `Hinv` is evaluated on
its range. The integrand vanishes off `𝓢`; finiteness of a nonnegative integral is `Integrable`. -/
def Cond5 (H f : ℝ → ℝ) : Prop :=
  ∀ α : ℝ, 0 ≤ α → Integrable fun x => |x| * Real.exp (Hinv H (α * |x|)) * f x

end FDivToolkit


