-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCongruenceSubset
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCongruenceSubset
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:21.657884+00:00
-- url     : https://prove2.me/theorems/e7a7cdd5-4ca6-4e31-94d1-c8c010ace903
-- title:
--   Exists Congruence Subset
-- statement:
--   Definitions and structural lemmas for Exists Congruence Subset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCongruenceSubset.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Filter Topology Matrix
namespace GlobalTheory.CompanionTheory.CongruenceBasis
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.CompanionTheory.CongruenceBasis


