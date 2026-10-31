-- Prove2me | Definitions.Def_TractableComposite_radd
-- name    : TractableComposite_radd
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:49.725286+00:00
-- url     : https://prove2.me/theorems/586542ea-5536-4849-a736-ffc1b198a4ca
-- title:
--   Ticked real sum
-- statement:
--   One step of the real-RAM cost model: charges one tick and returns $x+y$. The cost model is the published tick counter `LNTopology.Hermetization.tick`.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Corollary 1's proof, p.13 ("operations")

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick

namespace TractableComposite

/-- **Ticked real sum.** `radd x y` charges one tick and returns `x + y` (cost model of
`LNTopology.Hermetization.tick`, reading R3). He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), Corollary 1's proof, p.13 ("operations"). -/
noncomputable def radd (x y : ℝ) : StateM ℕ ℝ := do
  LNTopology.Hermetization.tick 1
  pure (x + y)

end TractableComposite


