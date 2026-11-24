-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchange
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:22.939891+00:00
-- url     : https://prove2.me/theorems/500c8643-2dee-4ab7-a3b5-eab87aa1da17
-- title:
--   Root Exchange
-- statement:
--   Definitions and structural lemmas for Root Exchange, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
namespace GlobalTheory.CompanionTheory.RootExch
section Abstract
variable {G : Type*} [Group G] [Fintype G]
end Abstract
end GlobalTheory.CompanionTheory.RootExch
namespace GlobalTheory.CompanionTheory.RootExch
section Mat
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
def tv (r t : ι) (h : r ≠ t) (s : K) : GL ι K :=
  ⟨Matrix.transvection r t s, Matrix.transvection r t (-s),
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp,
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp⟩
end Mat
end GlobalTheory.CompanionTheory.RootExch
namespace GlobalTheory.CompanionTheory.RootExch
end GlobalTheory.CompanionTheory.RootExch


