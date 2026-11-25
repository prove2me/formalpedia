-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndIrr
-- name    : Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndIrr
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T18:06:53.496803+00:00
-- url     : https://prove2.me/theorems/8cc621ed-f0de-41dd-bdf2-a19f531b32d9
-- title:
--   Ind Irr
-- statement:
--   Definitions and structural lemmas for Ind Irr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/RegularisedThetaMirabolic/CuspidalMirabolic/IndIrr.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling
namespace PositivityTheory.Mirab.Irr
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
open Classical in

def deltaU (ψ₀ : AddChar k ℂ) (x : mirabSub k n) : ℂ :=
  if h : x ∈ uniSub k n then genericChar n ψ₀ ⟨x, h⟩ else 0
end PositivityTheory.Mirab.Irr


