-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_ArcCostMCFP0
-- name    : DiscreteConvex_NetworkFlowsB_ArcCostMCFP0
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:27.162892+00:00
-- url     : https://prove2.me/theorems/59dd92d1-556d-4682-8de1-304cfdcf812a
-- title:
--   ArcCostMCFP0
-- statement:
--   The linear-cost arc function of Eq. (9.11): $f_a(t)=\gamma(a)t$ on $[\underline c(a),\overline c(a)]$, $+\infty$ elsewhere.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247, Eq. (9.11).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247, Eq. (9.11)

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The linear-cost arc function of Eq. (9.11): `fa(t) = γ(a)t` on `[c(a),c̄(a)]`, `+∞`
elsewhere. -/
noncomputable def ArcCostMCFP0 (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ) (gamma : A → ℝ) (a : A)
    (t : ℝ) : WithTop ℝ :=
  if cLower a ≤ (t : WithBot ℝ) ∧ (t : WithTop ℝ) ≤ cUpper a then ((gamma a * t : ℝ) : WithTop ℝ)
  else ⊤

end DiscreteConvex.NetworkFlowsB


