-- Prove2me | Definitions.Def_ChenFarias_SimplePolicy_Supplement_Feedback
-- name    : ChenFarias_SimplePolicy_Supplement_Feedback
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:59:39.070806+00:00
-- url     : https://prove2.me/theorems/fbd96d55-a725-41e0-8452-be6fadd02c5a
-- title:
--   (12)–(13) — pricing policies realized from a maximizing HJB control
-- statement:
--   Given a candidate $J$, a maximizing Markov control $a$, and initial inventory $x_0$, a feedback realization starts at a nonnegative maximizer $p_0$ of $p\mapsto J(0,p,x_0)$ over all $p\ge0$. With $y_s=(s,\pi_s,X_{s-})$, it satisfies, while stock remains,
--   $$
--   \pi_t=p_0+\int_0^t a_0(y_s)\,ds+\sum_{S_k<t}a_1(y_{S_k}).
--   $$
--   The derivative control is ordinarily integrable along almost every realized trajectory, making the displayed integral meaningful. No uniqueness of the realization, continuity of the maximizing set, or robustness of the resulting policy is assumed. The theorem separately requires that it is a pricing policy with the stated sales intensity.
--
--   This predicate describes all realizations of the paper's construction; it does not replace the process by its expected value.
--
--   **Formalization Note** In (12), the printed $\pi^{*,M}(s)$ is evaluated at $y_s$, and its jump term is evaluated at the actual sale time and pre-sale state. The printed sum index $t_n<s$ is read as $t_n<t$. The initial argmax in (13) is stated as a maximizing property, without claiming it always exists.
-- source:
--   Chen and Farias, Robust Dynamic Pricing with Strategic Customers, Mathematics of Operations Research 43(4) (2018), p. 1134, (12)–(13)

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Supplement_HJB

namespace ChenFarias.SimplePolicy.Supplement

open MeasureTheory Set

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {x0 : ℕ}

/-- The pre-sale state used by the feedback rule. -/
def Pricing.state (P : Pricing Ω x0) (s : ℝ) (ω : Ω) : State :=
  ((s, P.core s ω), P.sales.stock s ω)

/-- A solution of (12)–(13). Integrability states that the displayed ordinary
integral exists; the integral is not assigned a default value on bad input.
There is no assumption that the resulting price policy is robust or regular. -/
def IsHJBPolicy (P : Pricing Ω x0) (μ : Measure Ω) (T : ℝ)
    (J : ValueFunction) (a : MarkovControl) (p0 : ℝ) : Prop :=
  0 ≤ p0 ∧ (∀ p : ℝ, 0 ≤ p → J 0 p x0 ≤ J 0 p0 x0) ∧
  (∀ᵐ ω ∂μ, IntegrableOn (fun s => (a (P.state s ω)).1) (Icc 0 T) ∧
    ∀ t ∈ Icc (0 : ℝ) T, 0 < P.sales.stock t ω →
      P.core t ω = p0 + (∫ s in Ioc (0 : ℝ) t, (a (P.state s ω)).1) +
        P.sales.sumBefore (fun s ω' => (a (P.state s ω')).2) t ω)

end
end ChenFarias.SimplePolicy.Supplement


