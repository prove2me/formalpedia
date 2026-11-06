-- Prove2me | Definitions.Def_ConstrSOSP_InColumns
-- name    : ConstrSOSP_InColumns
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:02:01.586755+00:00
-- url     : https://prove2.me/theorems/e94962f6-9099-46a6-ba72-2960564cc622
-- title:
--   The set Columns
-- statement:
--   $\mathrm{Columns}=\{k\in\{1,\dots,2^n\}: C(k)\ne k\}$: the Iter nodes that receive a blue column.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §5.3, p.29

import Mathlib
import Definitions.Def_ConstrSOSP_Circuit_app

namespace ConstrSOSP

/-- **The set Columns** (arXiv:2604.02285, 2 Nov 2026, §5.3, p.29: "Columns = {k ∈ {1, 2, …, 2ⁿ} :
C(k) ≠ k}"), the Iter nodes that get a blue column. -/
def InColumns (C : Circuit) (k : ℕ) : Prop :=
  1 ≤ k ∧ k ≤ 2 ^ C.n ∧ C.app k ≠ k

end ConstrSOSP


