-- Prove2me | Definitions.Def_BinaryQueryLB_answer
-- name    : BinaryQueryLB_answer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:43:50.969186+00:00
-- url     : https://prove2.me/theorems/36e1cc52-491e-4fdd-8d61-67d806ad95d9
-- title:
--   Answer of a local binary query
-- statement:
--   Under a chart $G$, the answer of the local binary query $(y,h)$ on a function $f$ is the bit
--   $$
--   h\big(f(y),\,G(f,y)\big).
--   $$
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.3, p.11

import Mathlib
import Definitions.Def_BinaryQueryLB_Chart
import Definitions.Def_BinaryQueryLB_LocalQuery

namespace BinaryQueryLB

/-- **Answer of a local binary query (Definition 2.3).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.3, p.11: "Under a
chart `G`, its answer on `f` is the bit `h(f(y), G(f, y))`." -/
def answer {d : ℕ} (G : Chart d) (f : EuclideanSpace ℝ (Fin d) → ℝ) (qr : LocalQuery d) : Bool :=
  qr.2 (f qr.1, G f qr.1)

end BinaryQueryLB


