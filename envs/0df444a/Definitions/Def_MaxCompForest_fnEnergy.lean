-- Prove2me | Definitions.Def_MaxCompForest_fnEnergy
-- name    : MaxCompForest_fnEnergy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:23.5057+00:00
-- url     : https://prove2.me/theorems/76e5ddd1-49a0-455e-8540-fd85dc086147
-- title:
--   Energy of a scalar potential
-- statement:
--   For $f:V\to\mathbb R$,
--   $$
--   \mathcal E(f)=\sum_{e=uv}c_e\,(f_u-f_v)^2 ,
--   $$
--   where every labelled edge contributes once.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), §2.1, p.7

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype E] [DecidableEq E]

/-- **The energy of a scalar function** `E(f) = ∑_{e=uv} c_e (f_u − f_v)²`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), §2.1, p.7. Every labelled edge contributes once. -/
noncomputable def fnEnergy (G : WGraph V E) (f : V → ℝ) : ℝ :=
  ∑ e, G.w e * (f (G.head e) - f (G.tail e)) ^ 2

end MaxCompForest


