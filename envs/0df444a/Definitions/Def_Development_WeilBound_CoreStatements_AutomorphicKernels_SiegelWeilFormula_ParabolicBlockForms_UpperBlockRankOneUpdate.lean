-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ParabolicBlockForms_UpperBlockRankOneUpdate
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ParabolicBlockForms_UpperBlockRankOneUpdate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:06.30312+00:00
-- url     : https://prove2.me/theorems/114d1c9e-8155-46d1-8498-427f6cc2ea77
-- title:
--   Upper Block Rank One Update
-- statement:
--   Definitions and structural lemmas for Upper Block Rank One Update, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ParabolicBlockForms/UpperBlockRankOneUpdate.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PositivityTheory.SiegelWeilFormula.Act.C4.Bq
open Matrix
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
def NQ (x y : ι) (M : Matrix ι ι R) : Prop :=
  (∀ k, (M - 1) k x = 0) ∧ ∀ k l, l ≠ x → l ≠ y → k ≠ x → (M - 1) k l = 0
def Pad (x y : ι) (J : Matrix ι ι R) : Prop :=
  ∀ r c, (r = x ∨ r = y ∨ c = x ∨ c = y) → J r c = (1 : Matrix ι ι R) r c
variable {n : ℕ}
end PositivityTheory.SiegelWeilFormula.Act.C4.Bq


