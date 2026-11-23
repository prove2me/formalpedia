-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenIsCompactPrincipal
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenIsCompactPrincipal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:24.170853+00:00
-- url     : https://prove2.me/theorems/020e45f4-c9ab-4864-9a88-39b28e67425e
-- title:
--   Is Open Is Compact Principal
-- statement:
--   Definitions and structural lemmas for Is Open Is Compact Principal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsOpenIsCompactPrincipal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
open scoped Topology
namespace GlobalTheory.CompanionTheory.PrincipalCongruence
variable {k : Type*} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def congSet (n : Type*) [DecidableEq n] (t : k) : Set (Matrix n n k) :=
  {A | ∀ i j, valuation k (A i j - (1 : Matrix n n k) i j) ≤ valuation k t}
def congGL (n : Type*) [Fintype n] [DecidableEq n] (t : k) : Set (GL n k) :=
  {g | (g : Matrix n n k) ∈ congSet n t}
end GlobalTheory.CompanionTheory.PrincipalCongruence


