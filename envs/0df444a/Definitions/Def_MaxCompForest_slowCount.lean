-- Prove2me | Definitions.Def_MaxCompForest_slowCount
-- name    : MaxCompForest_slowCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:35:08.05872+00:00
-- url     : https://prove2.me/theorems/d252c034-016d-48e4-b3f1-e1eb9406e012
-- title:
--   Number $r$ of positive eigenvalues below the cutoff
-- statement:
--   The number $r$ of positive eigenvalues of the normalized Laplacian below the cutoff $c$, counted with multiplicity.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem F.1, p.42

import Mathlib
import Definitions.Def_MaxCompForest_normLap
import Definitions.Def_MaxCompForest_deg
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **The retained rank** `r`: the number of positive eigenvalues of `N` below the cutoff `c`, with
multiplicity.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Theorem F.1, p.42. -/
noncomputable def slowCount (G : WGraph V E) (c : ℝ) : ℕ :=
  (Finset.univ.filter fun a => 0 < (normLap_isHermitian G (deg G)).eigenvalues a ∧
    (normLap_isHermitian G (deg G)).eigenvalues a < c).card

end MaxCompForest


