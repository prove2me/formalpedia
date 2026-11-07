-- Prove2me | Definitions.Def_EuclidSPAgg_IsPosHomogeneous
-- name    : EuclidSPAgg_IsPosHomogeneous
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:36.954239+00:00
-- url     : https://prove2.me/theorems/0ffa1d84-ad69-4036-9eca-3e2f61640ae5
-- title:
--   Positive homogeneity
-- statement:
--   A mechanism $f$ is **positively homogeneous** if
--   $$
--   f(tx_1,\dots,tx_n)=t\,f(x_1,\dots,x_n)\qquad\text{for every profile }x\text{ and every }t\ge0 .
--   $$
--   The case $t=0$ is included, so $f(0,\dots,0)=0$.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.9 (PDF p.11); p.3 (PDF p.5)

import Mathlib
import Definitions.Def_EuclidSPAgg_Mech
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- Positive homogeneity (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.9 (PDF p.11)): `f(t x) = t f(x)` for every
profile `x` and every `t ≥ 0`, where `t x = (t x₁, …, t xₙ)`.

**Formalization Note** `t = 0` is included, as printed ("for every `t ≥ 0`", p.3), so
`f(0, …, 0) = 0`. -/
def IsPosHomogeneous {n d : ℕ} (f : Mech n d) : Prop :=
  ∀ (x : Fin n → E d) (t : ℝ), 0 ≤ t → f (fun i => t • x i) = t • f x

end EuclidSPAgg


