-- Prove2me | Definitions.Def_MaxCompForest_nontrivialComps
-- name    : MaxCompForest_nontrivialComps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:20.853204+00:00
-- url     : https://prove2.me/theorems/9257e9c4-57b6-4423-b04b-80a3c1d28d67
-- title:
--   Nontrivial components $\mathcal C(F)$ of a forest
-- statement:
--   For a forest $F$, the set $\mathcal C(F)$ of connected components of $(V,F)$ with at least two vertices. These are the components that carry edges of $F$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), p.16

import Mathlib
import Definitions.Def_MaxCompForest_compVerts
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V]

/-- **The nontrivial components `C(F)`** of a forest: those with at least two vertices.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.16: "let `C(F)` consist of its nontrivial components". -/
noncomputable def nontrivialComps (G : WGraph V E) (F : Finset E) : Finset (ContractV G F) :=
  Finset.univ.filter fun C => 2 ≤ (compVerts G F C).card

end MaxCompForest


