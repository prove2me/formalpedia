-- Prove2me | Definitions.Def_TreeMultiflow_RatInstance_lpval
-- name    : TreeMultiflow_RatInstance_lpval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:54.784213+00:00
-- url     : https://prove2.me/theorems/fa23f109-31cf-4ca2-90ab-40fdf7fa1b5c
-- title:
--   Fractional solution of a rational instance
-- statement:
--   The fractional value $x_f$ of the request in position $f$ of the request list, as a real number.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Theorem 1.2, p.3 (a feasible solution x of (1), rationally encoded)

import Mathlib
import Definitions.Def_TreeMultiflow_RatInstance

namespace TreeMultiflow

/-- **The fractional solution carried by a rational instance.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Theorem 1.2,
p.3 ("For every feasible solution x of (1) … for rationally encoded inputs").

`I.lpval f` is the value `x_f` of the `f`-th entry of `I.reqs`, as a real number. -/
def RatInstance.lpval (I : RatInstance) (f : Fin I.reqs.length) : ℝ :=
  ((I.reqs.get f).2.2.2 : ℝ)

end TreeMultiflow


