-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsChainsOfRange
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsChainsOfRange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:15.396061+00:00
-- url     : https://prove2.me/theorems/057e1647-5338-43d0-a6ff-196e8804a1c4
-- title:
--   Exists Chains Of Range
-- statement:
--   Definitions and structural lemmas for Exists Chains Of Range, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsChainsOfRange.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.JordanChain
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
def chainVec (f : V →ₗ[K] V) {ι : Type} (e : ι → ℕ) (v : ι → V) : (Σ a, Fin (e a)) → V :=
  fun p => (f ^ (p.2 : ℕ)) (v p.1)
end GlobalTheory.CompanionTheory.JordanChain


