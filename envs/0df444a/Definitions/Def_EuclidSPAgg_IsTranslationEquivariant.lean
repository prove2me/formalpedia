-- Prove2me | Definitions.Def_EuclidSPAgg_IsTranslationEquivariant
-- name    : EuclidSPAgg_IsTranslationEquivariant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:35.718901+00:00
-- url     : https://prove2.me/theorems/66e1a907-b259-4601-b6e3-223bb84ab113
-- title:
--   Translation equivariance (Definition 1.4)
-- statement:
--   A mechanism $f$ is **translation-equivariant** if
--   $$
--   f(x_1+v,\dots,x_n+v)=f(x_1,\dots,x_n)+v\qquad\text{for every profile }x\text{ and every }v\in E .
--   $$
--   Moving all reports by the same vector moves the outcome by that vector.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Definition 1.4, p.3 (PDF p.5); Section 2.1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_EuclidSPAgg_Mech
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- Translation equivariance, Definition 1.4 (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.3 (PDF p.5); Section 2.1, p.9 (PDF p.11)):
`f(x + v) = f(x) + v` for every profile `x` and every `v ∈ E`, where `x + v = (x₁ + v, …, xₙ + v)`. -/
def IsTranslationEquivariant {n d : ℕ} (f : Mech n d) : Prop :=
  ∀ (x : Fin n → E d) (v : E d), f (fun i => x i + v) = f x + v

end EuclidSPAgg


