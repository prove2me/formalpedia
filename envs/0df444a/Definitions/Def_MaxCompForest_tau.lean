-- Prove2me | Definitions.Def_MaxCompForest_tau
-- name    : MaxCompForest_tau
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:35:35.712436+00:00
-- url     : https://prove2.me/theorems/d490442f-6697-4dd8-8bbb-9b21241b4d88
-- title:
--   Weighted spanning-tree count $\tau_c(G)$
-- statement:
--   The total weight of all spanning trees,
--   $$
--   \tau_c(G)=\sum_{T}c(T),
--   $$
--   the normalizer of the weighted spanning-tree law, which samples $T$ with probability $c(T)/\tau_c(G)$. It is positive exactly on connected graphs.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), p.1, p.14

import Mathlib
import Definitions.Def_MaxCompForest_IsSpanningTree
import Definitions.Def_MaxCompForest_weight
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]

open Classical in
/-- **The weighted spanning-tree count** `τ_c(G) = ∑_T c(T)`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.1, p.14.

**Formalization Note.** Sum over label sets. The empty sum `0` occurs only for a disconnected graph. -/
noncomputable def tau (G : WGraph V E) : ℝ :=
  ∑ T ∈ Finset.univ.filter (IsSpanningTree G), weight G T

end MaxCompForest


