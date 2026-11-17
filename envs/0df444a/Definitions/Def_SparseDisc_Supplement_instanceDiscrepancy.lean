-- Prove2me | Definitions.Def_SparseDisc_Supplement_instanceDiscrepancy
-- name    : SparseDisc_Supplement_instanceDiscrepancy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:02:51.770046+00:00
-- url     : https://prove2.me/theorems/4fe1a4ff-88b9-4ac5-9238-2d36ad4bbcc6
-- title:
--   Discrepancy of a finite instance
-- statement:
--   The **discrepancy** of a finite instance is the infimum of the real thresholds attained by one common sign colouring. Since the cube is finite, this is the minimum appearing in Definition 2.2.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Definition 2.2, p.12

import Mathlib
import Definitions.Def_SparseDisc_InstDiscLE

namespace SparseDisc.Supplement

/-- The discrepancy of a finite instance, expressed as the infimum of its attainable real
thresholds (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027
submission manuscript (sha256 0f09ec60…25b81), Definition 2.2, p.12). -/
noncomputable def instanceDiscrepancy {V ι : Type} [Fintype V] [Fintype ι]
    (g : V → SparseDisc.Cube ι → ℝ) : ℝ :=
  sInf {c : ℝ | SparseDisc.InstDiscLE g c}

end SparseDisc.Supplement


