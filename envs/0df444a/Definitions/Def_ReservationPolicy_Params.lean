-- Prove2me | Definitions.Def_ReservationPolicy_Params
-- name    : ReservationPolicy_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:18.962532+00:00
-- url     : https://prove2.me/theorems/ad68fed5-38bb-4f3d-9b67-922a28d3ba7f
-- title:
--   Parameters $(k,\phi,\alpha,z,\kappa)$ of the admission model
-- statement:
--   The model has five real parameters: the effort-cost parameter $k$ (a student exerting effort $e$ pays $ke^2$), the productivity $\phi$ of effort without proprietary educational resources, the size $\alpha$ of type $x$ (type $y$ has size $1-\alpha$, and the total mass of students is one), the college capacity $z$, and the cost $\kappa$ of the proprietary resources.
--
--   These five numbers index every object of the mission.
--
--   **Formalization Note** The structure records only the numbers. The assumptions on them are the predicate `Params.Valid`.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), §2, pp.8–9

import Mathlib

namespace ReservationPolicy

/-- The parameters of the college-admission model. Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), §2,
pp.8–9 (PDF 8–9).

* `k` is the effort-cost parameter, `c(e) = k e²`;
* `ϕ` is the productivity of effort without proprietary resources;
* `α` is the size of type `x`, and `1 − α` the size of type `y`;
* `z` is the college capacity;
* `κ` is the cost of proprietary educational resources.

**Formalization Note** The fields are bare reals. The paper's assumptions are `Params.Valid`. -/
structure Params where
  k : ℝ
  ϕ : ℝ
  α : ℝ
  z : ℝ
  κ : ℝ

end ReservationPolicy


