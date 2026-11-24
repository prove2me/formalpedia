-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_SiuaNum
-- name    : Development_WeilBound_CoreStatements_HodgeTatePoints_SiuaNum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:08.688507+00:00
-- url     : https://prove2.me/theorems/95bc3ee3-7b40-41fd-b88c-851340e8994f
-- title:
--   Siua Num
-- statement:
--   Definitions and structural lemmas for Siua Num, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/SiuaNum.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PositivityTheory.HtPt.Siua
open Filter Topology
noncomputable def form {M : Type} [AddCommGroup M] {n : ℕ} (f : MultilinearMap ℤ (fun _ : Fin n => M) ℤ)
    (μ e : M) (x y : Fin n → ℚ) : ℚ :=
  ∑ s : Finset (Fin n), (∏ i, if i ∈ s then x i else y i) * (f (fun i => if i ∈ s then μ else e) : ℚ)
end PositivityTheory.HtPt.Siua


