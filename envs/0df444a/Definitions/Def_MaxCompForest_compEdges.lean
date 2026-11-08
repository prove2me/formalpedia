-- Prove2me | Definitions.Def_MaxCompForest_compEdges
-- name    : MaxCompForest_compEdges
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:35:46.421829+00:00
-- url     : https://prove2.me/theorems/74586167-4b5f-4ac9-ac30-200ec9b91f45
-- title:
--   Edges $E(C)$ of a forest component
-- statement:
--   For a label set $F$ and a connected component $C$ of $(V,F)$, the set $E(C)$ of labels of $F$ with endpoints in $C$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (3.5), p.16

import Mathlib
import Definitions.Def_MaxCompForest_contract
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*}

open Classical in
/-- **The edges `E(C)`** of a component `C` of `(V, F)`: the labels of `F` inside `C`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (3.5), p.16. -/
noncomputable def compEdges (G : WGraph V E) (F : Finset E) (C : ContractV G F) : Finset E :=
  F.filter fun e => (spanSub G F).connectedComponentMk (G.head e) = C

end MaxCompForest


