-- Prove2me | Definitions.Def_TractableComposite_rsub
-- name    : TractableComposite_rsub
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:51:06.43005+00:00
-- url     : https://prove2.me/theorems/f555fd65-7259-4fe2-91dd-ce2d86c6c054
-- title:
--   Ticked real difference
-- statement:
--   One step of the real-RAM cost model: charges one tick and returns $x-y$.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Corollary 1's proof, p.13 ("operations")

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick

namespace TractableComposite

/-- **Ticked real difference.** `rsub x y` charges one tick and returns `x − y` (cost model of
`LNTopology.Hermetization.tick`, reading R3). He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), Corollary 1's proof, p.13 ("operations"). -/
noncomputable def rsub (x y : ℝ) : StateM ℕ ℝ := do
  LNTopology.Hermetization.tick 1
  pure (x - y)

end TractableComposite


