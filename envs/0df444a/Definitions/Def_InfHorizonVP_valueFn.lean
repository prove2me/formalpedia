-- Prove2me | Definitions.Def_InfHorizonVP_valueFn
-- name    : InfHorizonVP_valueFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:18:13.23666+00:00
-- url     : https://prove2.me/theorems/09b96b06-bfd5-4a3a-92fc-632a0c22172f
-- title:
--   The value function $V(t,\xi)$
-- statement:
--   The **value function** of the problem $(P_t)$ is
--   $$
--   V(t,\xi)=\inf_{x\in\mathcal A_{(t,\xi)}}\int_t^\infty L(s,x(s),\dot x(s))\,ds\in\mathbb R\cup\{\pm\infty\},
--   $$
--   the infimum ranging over admissible trajectories whose improper integral exists, with the convention $\inf\emptyset=+\infty$ (if $\mathcal A_{(t,\xi)}$ is empty or no integral is well defined).
--
--   All the results of the paper are statements about $V$: its Lipschitz continuity (Theorem 3.1), its subdifferentials along optimal trajectories (Theorem 3.2), and the adjoint inclusion $-p(t)\in\partial^-_xV(t,x_0(t))$ (Theorem 4.1).
--
--   **Formalization Note** $V$ is `EReal`-valued; the infimum of the empty family is $+\infty$.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §3.1, p.8

import Mathlib
import Definitions.Def_InfHorizonVP_Admissible
import Definitions.Def_InfHorizonVP_HasImproperIntegral
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **The value function `V(t, ξ)`.**
Frankowska, Sagara, arXiv:1801.00400v3, §3.1, p.8: "Then the value function V : R+ × E → R ∪ {±∞}
is defined by V(t, ξ) := inf_{x(·)∈𝒜_(t,ξ)} ∫_t^∞ L(s, x(s), ẋ(s))ds. Here, we set inf ∅ = +∞ if
𝒜_(t,ξ) is empty or if for every x(·) ∈ 𝒜_(t,ξ) the integral ∫_t^∞ L(s, x(s), ẋ(s))ds is not
well-defined."

`valueFn L Γ t ξ` is the infimum, over admissible trajectories `x ∈ 𝒜_(t,ξ)` whose improper
integral exists, of that integral.

**Formalization Note.** `V` takes values in `EReal = [-∞, +∞]`; the infimum of the empty family is
`⊤ = +∞`, which is the page's convention `inf ∅ = +∞`. Admissible arcs whose improper integral does
not exist do not contribute. -/
noncomputable def valueFn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ → E → E → ℝ) (Γ : ℝ → E → Set E) (t : ℝ) (ξ : E) : EReal :=
  ⨅ (x : ℝ → E) (_ : x ∈ Admissible Γ t ξ) (c : EReal) (_ : HasImproperIntegral L x t c), c

end InfHorizonVP


