-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndIrr
-- name    : CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndIrr
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T18:03:43.973827+00:00
-- url     : https://prove2.me/theorems/36256d5a-acd0-5f5c-be8a-0f15719c29ee
-- title:
--   Ind Irr
-- statement:
--   Definitions and structural lemmas for Ind Irr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndIrr.lean

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
namespace CompanionTheory.Mirab.Irr
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
open Classical in

def deltaU (ψ₀ : AddChar k ℂ) (x : mirabSub k n) : ℂ :=
  if h : x ∈ uniSub k n then genericChar n ψ₀ ⟨x, h⟩ else 0
end CompanionTheory.Mirab.Irr


