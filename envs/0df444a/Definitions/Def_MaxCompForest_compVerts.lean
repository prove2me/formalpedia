-- Prove2me | Definitions.Def_MaxCompForest_compVerts
-- name    : MaxCompForest_compVerts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:35:55.795198+00:00
-- url     : https://prove2.me/theorems/d2c8a18a-b7ce-4947-8303-d61fceaa3367
-- title:
--   Vertices $V(C)$ of a forest component
-- statement:
--   For a label set $F$ and a connected component $C$ of $(V,F)$, the set $V(C)$ of its vertices.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (3.5), p.16

import Mathlib
import Definitions.Def_MaxCompForest_contract
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V]

open Classical in
/-- **The vertices `V(C)`** of a component `C` of `(V, F)`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (3.5), p.16. -/
noncomputable def compVerts (G : WGraph V E) (F : Finset E) (C : ContractV G F) : Finset V :=
  Finset.univ.filter fun v => (spanSub G F).connectedComponentMk v = C

end MaxCompForest


