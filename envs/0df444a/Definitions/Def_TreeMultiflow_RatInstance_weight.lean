-- Prove2me | Definitions.Def_TreeMultiflow_RatInstance_weight
-- name    : TreeMultiflow_RatInstance_weight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:57.989205+00:00
-- url     : https://prove2.me/theorems/0a8a56ab-3dee-4161-be68-cd4444efdc64
-- title:
--   Request weights of a rational instance
-- statement:
--   The weight $w_f$ of the request in position $f$ of the request list, as a real number.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Section 1, p.2 (nonnegative weight w_f)

import Mathlib
import Definitions.Def_TreeMultiflow_RatInstance

namespace TreeMultiflow

/-- **Request weights of a rational instance.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Section 1,
p.2 ("Each request f ∈ F has a nonnegative weight w_f").

`I.weight f` is the weight of the `f`-th entry of `I.reqs`, as a real number. -/
def RatInstance.weight (I : RatInstance) (f : Fin I.reqs.length) : ℝ :=
  ((I.reqs.get f).2.2.1 : ℝ)

end TreeMultiflow


