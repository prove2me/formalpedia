-- Prove2me | Definitions.Def_PushInfoShare_payoff
-- name    : PushInfoShare_payoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:10.106258+00:00
-- url     : https://prove2.me/theorems/aa79698e-9383-4e73-b2d7-40c2adff635f
-- title:
--   Manufacturer's expected profit under a pricing deviation
-- statement:
--   If manufacturer $i$ prices by $f(Y_i)$ while the rival follows its rule, its expected profit is
--   $$E\bigl[f(Y_i)\,q_i\bigl(w^f,Y\bigr)\bigr],\qquad w^f_i=f(Y_i),\quad w^f_{3-i}=\alpha_{3-i}+B_{3-i}Y_{3-i}.$$
--   The deviation moves the retailer's order directly and, when $i$ does not share, through the retailer's inference.
--
--   **Formalization Note** The expectation is ex ante. On an equilibrium the order rule is affine, so the integrand is integrable whenever $f\circ Y_i\in L^2$.
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), eq. (3), p.10

import Mathlib
import Definitions.Def_PushInfoShare_Profile

open MeasureTheory

namespace PushInfoShare

/-- Manufacturer `i`'s expected profit `E[wᵢ qᵢ]` under the profile `str` when it prices by
`f(Yᵢ)` instead of its linear rule, the rival pricing by its rule, Jain, SSRN:3388957 (PDF of
2021-04-25), problem (3), p.10.

**Formalization Note.** The expectation is ex ante. A deviation `f` changes the price seen by the
retailer's order rule `str.q`, hence its inference of an unshared signal. On an equilibrium `str.q`
is affine in its arguments, so the integrand is integrable for `f ∘ Yᵢ` in `L²`. -/
noncomputable def payoff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Fin 2 → Ω → ℝ)
    (str : Profile) (i : Fin 2) (f : ℝ → ℝ) : ℝ :=
  ∫ ω, f (Y i ω) *
    str.q i (Function.update (fun j => str.α j + str.B j * Y j ω) i (f (Y i ω)))
      (fun j => Y j ω) ∂μ

end PushInfoShare


