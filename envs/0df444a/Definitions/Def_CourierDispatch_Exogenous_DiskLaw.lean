-- Prove2me | Definitions.Def_CourierDispatch_Exogenous_DiskLaw
-- name    : CourierDispatch_Exogenous_DiskLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T23:11:42.090056+00:00
-- url     : https://prove2.me/theorems/5a40ab8f-94d2-4763-b66c-71c60695eec7
-- title:
--   §3, p. 7 — the uniform law of a customer's location on the disk of radius r
-- statement:
--   Let $D_r=\{x\in\mathbb R^2:\|x\|\le r\}$ be the closed disk of radius $r$ centred at the vendor's facility, with the Euclidean norm. The **uniform law on the disk** is Lebesgue measure conditioned on $D_r$:
--   $$\mathcal U_r(A)=\frac{\operatorname{Leb}(A\cap D_r)}{\operatorname{Leb}(D_r)}=\frac{\operatorname{Leb}(A\cap D_r)}{\pi r^2}.$$
--   For $r>0$ it is a probability measure. It models the location of a customer, which in the paper is independent and uniformly distributed on the disk; the trip lengths $X_D$ and $X_B$ are functions of one or two such locations.
--
--   **Formalization Note** The plane is `EuclideanSpace ℝ (Fin 2)` with its Lebesgue measure `volume`, and the law is `ProbabilityTheory.cond volume (closedBall 0 r)`. For $r\le 0$ it is not a probability measure; every theorem using it assumes $r>0$.
-- source:
--   Chen, Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063 (version of 2022-09-21), p. 7, §3 (customer locations uniform on the disk)

import Mathlib

namespace CourierDispatch.Exogenous

/-- The uniform distribution on the closed disk of radius `r` centred at the origin of the
Euclidean plane: Lebesgue measure conditioned on the disk (Chen, Hu, SSRN 3675063, p. 7: each
customer's location is uniformly distributed on the disk). It is a probability measure for `0 < r`. -/
noncomputable def diskLaw (r : ℝ) : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2)) :=
  ProbabilityTheory.cond MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r)

end CourierDispatch.Exogenous


