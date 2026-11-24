-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GoodWordCount
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GoodWordCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:46.436048+00:00
-- url     : https://prove2.me/theorems/91e6d34b-bbb0-450b-8094-90f71e46eef7
-- title:
--   Good Word Count
-- statement:
--   Definitions and structural lemmas for Good Word Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GoodWordCount.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
namespace GlobalTheory.CompanionTheory.GoodWords
variable {N s : ℕ}
open Classical in

noncomputable def leftSet (b β : Fin N → Fin s) (k : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun x => ∃ i : Fin N, (i : ℕ) < k ∧ β i = b x
def rank (S : Finset (Fin N)) (b : Fin N → Fin s) (x : Fin N) : ℕ :=
  (open Classical in if x ∈ S then 0 else s) + (s - 1 - (b x : ℕ))
end GlobalTheory.CompanionTheory.GoodWords


