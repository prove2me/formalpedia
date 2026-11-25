-- Prove2me | Definitions.Def_SourceProof_99772f69b5e3310f6b195fa2
-- name    : SourceProof_99772f69b5e3310f6b195fa2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:00.740047+00:00
-- url     : https://prove2.me/theorems/e57a4b74-2b03-4feb-a175-db7bdc6d6ac9
-- title:
--   StochLean source theorem: StochLean.TimePartition.eq_of_nonempty_cell_endpoints

import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F000
import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F002
import Definitions.Def_StochLean_Analysis_PathVariation_Reflection_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Endpoint-set invariance of deterministic sums

An ordered list may repeat its endpoints. Nonempty cells, however, are determined uniquely by
the endpoint set. Thus sums of cell contributions that vanish on empty cells depend only on
the endpoint set, rather than its enumeration.
-/

@[expose] public section

open Finset Set
open scoped NNReal

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_99772f69b5e3310f6b195fa2 (π : TimePartition T) {i j : Fin π.size}
    (hi : π.left i < π.right i) (hl : π.left i = π.left j)
    (hr : π.right i = π.right j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hji
  · have h : π.right i ≤ π.left j := π.monotone_point (show i.succ ≤ j.castSucc from hij)
    exact False.elim ((not_le_of_gt hi) (hl ▸ h))
  · exact hij
  · have h : π.right j ≤ π.left i := π.monotone_point (show j.succ ≤ i.castSucc from hji)
    exact False.elim ((not_le_of_gt hi) (hr ▸ h))
end StochLean.TimePartition

namespace StochLean

end StochLean


