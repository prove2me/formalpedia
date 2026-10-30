-- Prove2me | Definitions.Def_EPRPharma_IsMaxWelfare
-- name    : EPRPharma_IsMaxWelfare
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:15:05.618056+00:00
-- url     : https://prove2.me/theorems/365b54d4-74f5-4a8e-ba24-79c7a02f2a42
-- title:
--   Maximal total welfare $W_P^*$ of a model
-- statement:
--   A real number $v$ is the maximal total welfare of model $P$ if
--
--   1. some equilibrium of $P$ has welfare $v$, and
--   2. every equilibrium of $P$ has welfare at most $v$.
--
--   This is the value of the planner's problem under $P$, as an attained maximum.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3.3, p. 13 (unnumbered)

import Mathlib
import Definitions.Def_EPRPharma_IsEquilibrium
import Definitions.Def_EPRPharma_welfare

namespace EPRPharma

/-- **The maximal total welfare of model m.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3.3, p. 13: "the social planner maximizes
the total expected welfare W under each model by setting the associated model parameter(s) y_P".
`IsMaxWelfare P m v` says that v is the maximum of W over the equilibria of model m: some
equilibrium attains v and no equilibrium exceeds it.

**Formalization Note.** An attained maximum, not a supremum, so no junk value arises when the set
of equilibria is empty or unbounded. -/
def IsMaxWelfare (P : Params) (m : Model) (v : ℝ) : Prop :=
  (∃ y d, IsEquilibrium P m y d ∧ welfare P m y d = v) ∧
    ∀ y d, IsEquilibrium P m y d → welfare P m y d ≤ v

end EPRPharma


