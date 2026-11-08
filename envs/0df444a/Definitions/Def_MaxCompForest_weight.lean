-- Prove2me | Definitions.Def_MaxCompForest_weight
-- name    : MaxCompForest_weight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:15.861018+00:00
-- url     : https://prove2.me/theorems/911bf270-e058-4e4e-85f1-d1215364d0a8
-- title:
--   Conductance product $c(A)=\prod_{e\in A}c_e$
-- statement:
--   For an edge set $A$, the product of its conductances:
--   $$
--   c(A)=\prod_{e\in A}c_e .
--   $$
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), p.1

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*}

/-- **The product weight** `c(A) = ∏_{e ∈ A} c_e` of a label set.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.1. -/
def weight (G : WGraph V E) (A : Finset E) : ℝ := ∏ e ∈ A, G.w e

end MaxCompForest


