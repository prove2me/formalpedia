-- Prove2me | Definitions.Def_MaxCompForest_compP
-- name    : MaxCompForest_compP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:34.897032+00:00
-- url     : https://prove2.me/theorems/bb509e08-b7f1-4a8f-9683-1d0e6ba31763
-- title:
--   Component factor $p_C$
-- statement:
--   $$
--   p_C=\frac{\prod_{e\in E(C)}c_e}{\prod_{v\in V(C)}d_v},
--   $$
--   which records the edge and vertex weights of the component $C$. Every use has positive masses.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (3.5), p.16

import Mathlib
import Definitions.Def_MaxCompForest_compVerts
import Definitions.Def_MaxCompForest_compEdges
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V]

/-- **The component factor** `p_C = (∏_{e ∈ E(C)} c_e) / (∏_{v ∈ V(C)} d_v)`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (3.5), p.16. Every use has positive masses `d`. -/
noncomputable def compP (G : WGraph V E) (F : Finset E) (d : V → ℝ) (C : ContractV G F) : ℝ :=
  (∏ e ∈ compEdges G F C, G.w e) / ∏ v ∈ compVerts G F C, d v

end MaxCompForest


