-- Prove2me | Definitions.Def_InfHorizonVP_IsOptimal
-- name    : InfHorizonVP_IsOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:15.574028+00:00
-- url     : https://prove2.me/theorems/bdb0de3d-efe9-4b59-b9af-11892f42c7d6
-- title:
--   Optimal trajectory for $(P_t)$
-- statement:
--   For $(t,\xi)$ in the effective domain $\operatorname{dom}V=\{V<+\infty\}$, an admissible trajectory $x\in\mathcal A_{(t,\xi)}$ is **optimal** for $(P_t)$ if
--   $$
--   \int_t^\infty L(s,x(s),\dot x(s))\,ds=V(t,\xi)>-\infty .
--   $$
--   The definition bundles $V(t,\xi)<+\infty$, $V(t,\xi)>-\infty$, admissibility, and existence of the improper integral with value $V(t,\xi)$.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §3.1, p.8

import Mathlib
import Definitions.Def_InfHorizonVP_Admissible
import Definitions.Def_InfHorizonVP_HasImproperIntegral
import Definitions.Def_InfHorizonVP_valueFn
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Optimal trajectory for `(P_t)`.**
Frankowska, Sagara, arXiv:1801.00400v3, §3.1, p.8: "The effective domain of V is given by
dom V = {(t, x) ∈ R+ × E | V(t, x) < +∞} … For every (t, ξ) ∈ dom V, an admissible trajectory
x(·) ∈ 𝒜_(t,ξ) is said to be optimal for (P_t) if it satisfies ∫_t^∞ L(s, x(s), ẋ(s))ds =
V(t, ξ) > −∞."

`IsOptimal L Γ t ξ x` says: `(t, ξ) ∈ dom V`, `x ∈ 𝒜_(t,ξ)`, and the improper integral of `x`
exists and equals `V(t, ξ)`, which is `> -∞`.

**Formalization Note.** `V(t, ξ) < +∞` (membership in `dom V`) and `V(t, ξ) > -∞` are written
`≠ ⊤` and `≠ ⊥` in `EReal`. -/
def IsOptimal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ → E → E → ℝ) (Γ : ℝ → E → Set E) (t : ℝ) (ξ : E) (x : ℝ → E) : Prop :=
  valueFn L Γ t ξ ≠ ⊤ ∧ valueFn L Γ t ξ ≠ ⊥ ∧ x ∈ Admissible Γ t ξ ∧
    HasImproperIntegral L x t (valueFn L Γ t ξ)

end InfHorizonVP


