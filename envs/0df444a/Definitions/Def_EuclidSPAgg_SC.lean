-- Prove2me | Definitions.Def_EuclidSPAgg_SC
-- name    : EuclidSPAgg_SC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:26.379266+00:00
-- url     : https://prove2.me/theorems/db8fabdd-9b4f-4787-808e-89f98fc6cf0d
-- title:
--   Social cost $\mathrm{SC}(x,y)$
-- statement:
--   The **social cost** of locating the facility at $y\in E$ when the reports are $x\in E^n$ is
--   $$
--   \mathrm{SC}(x,y)=\sum_{i=1}^n\|x_i-y\| .
--   $$
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_RBMSensitivity_E
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- The social cost `SC(x, y) = ∑ᵢ ‖xᵢ − y‖` of the location `y` at the profile `x` (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…),
Section 2.1, p.8 (PDF p.10)). -/
noncomputable def SC {n d : ℕ} (x : Fin n → E d) (y : E d) : ℝ :=
  ∑ i, ‖x i - y‖

end EuclidSPAgg


