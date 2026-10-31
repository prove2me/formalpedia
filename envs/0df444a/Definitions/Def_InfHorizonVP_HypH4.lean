-- Prove2me | Definitions.Def_InfHorizonVP_HypH4
-- name    : InfHorizonVP_HypH4
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:22.792994+00:00
-- url     : https://prove2.me/theorems/9b576963-5084-423c-b225-d366ad020a24
-- title:
--   Hypothesis (H4): nonempty closed values
-- statement:
--   **(H4)** $\Gamma(t,x)$ is nonempty and closed for every $t\ge0$ and $x\in E$.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §3.1, p.8, (H4)

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Hypothesis (H4).**
Frankowska, Sagara, arXiv:1801.00400v3, §3.1, p.8: "(H4) Γ has nonempty closed values." -/
def HypH4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Γ : ℝ → E → Set E) : Prop :=
  ∀ t, 0 ≤ t → ∀ x : E, (Γ t x).Nonempty ∧ IsClosed (Γ t x)

end InfHorizonVP


