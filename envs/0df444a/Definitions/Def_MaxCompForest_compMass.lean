-- Prove2me | Definitions.Def_MaxCompForest_compMass
-- name    : MaxCompForest_compMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:36:55.909537+00:00
-- url     : https://prove2.me/theorems/e5a7ac7c-2844-4e86-af81-12dbf74bed6f
-- title:
--   Component mass $m_C$
-- statement:
--   $m_C=\sum_{v\in V(C)}d_v$, the total vertex mass of the component $C$, for vertex masses $d$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (3.5), p.16

import Mathlib
import Definitions.Def_MaxCompForest_compVerts
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V]

/-- **The component mass** `m_C = ∑_{v ∈ V(C)} d_v`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (3.5), p.16. -/
noncomputable def compMass (G : WGraph V E) (F : Finset E) (d : V → ℝ) (C : ContractV G F) : ℝ :=
  ∑ v ∈ compVerts G F C, d v

end MaxCompForest


