-- Prove2me | Definitions.Def_MaxCompForest_dmax
-- name    : MaxCompForest_dmax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:35:55.029344+00:00
-- url     : https://prove2.me/theorems/8971ddd6-6ab0-4209-8cd5-b56ae6b56d57
-- title:
--   Largest weighted degree $d_{\max}$
-- statement:
--   $d_{\max}=\max_v d_v$, the largest weighted degree.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (F.2), p.42

import Mathlib
import Definitions.Def_MaxCompForest_deg
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **The largest weighted degree** `d_max = max_v d_v`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (F.2), p.42.

**Formalization Note.** `⨆` over a finite type; every use has a nonempty `V`. -/
noncomputable def dmax (G : WGraph V E) : ℝ := ⨆ v, deg G v

end MaxCompForest


