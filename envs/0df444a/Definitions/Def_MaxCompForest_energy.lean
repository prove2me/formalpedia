-- Prove2me | Definitions.Def_MaxCompForest_energy
-- name    : MaxCompForest_energy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:53.652368+00:00
-- url     : https://prove2.me/theorems/a37941d7-98cb-442a-b9fe-6a7d21b8060d
-- title:
--   Graph energy $\mathcal E(\Phi)=\sum_e c_e\|\Phi_u-\Phi_v\|^2$
-- statement:
--   For a map $\Phi:V\to\mathbb R^d$,
--   $$
--   \mathcal E(\Phi)=\sum_{e=uv}c_e\|\Phi_u-\Phi_v\|^2 ,
--   $$
--   every labelled edge contributing once. It measures the variation of $\Phi$ between adjacent vertices.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), §2.1 p.7

import Mathlib
import Definitions.Def_MaxCompForest_distEnergy
import Definitions.Def_MaxCompForest_rowDist
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype E] [DecidableEq E]

/-- **The graph energy** `E(Φ) = ∑_{e=uv} c_e ‖Φ_u − Φ_v‖²` of a map into `ℝ^d`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), §2.1 p.7. Every labelled edge contributes once. -/
noncomputable def energy {d : ℕ} (G : WGraph V E) (x : V → EuclideanSpace ℝ (Fin d)) : ℝ :=
  distEnergy G (rowDist x)

end MaxCompForest


