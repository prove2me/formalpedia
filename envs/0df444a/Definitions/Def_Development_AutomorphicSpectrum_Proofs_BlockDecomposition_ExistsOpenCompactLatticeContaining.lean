-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOpenCompactLatticeContaining
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOpenCompactLatticeContaining
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:25.102986+00:00
-- url     : https://prove2.me/theorems/26c9a086-9024-483d-be80-3155b638e95c
-- title:
--   Exists Open Compact Lattice Containing
-- statement:
--   Definitions and structural lemmas for Exists Open Compact Lattice Containing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOpenCompactLatticeContaining.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
noncomputable section
namespace GlobalTheory.CompanionTheory.LocalLattice
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def ballSubgroup (k : Type) [Field k] [ValuativeRel k] (n : ℕ) (γ : ValueGroupWithZero k) :
    AddSubgroup (Fin n → k) where
  carrier := {x | ∀ i, valuation k (x i) ≤ γ}
  zero_mem' := fun i => by simp
  add_mem' := fun {a b} ha hb i =>
    (Valuation.map_add _ _ _).trans (max_le (ha i) (hb i))
  neg_mem' := fun {a} ha i => by simpa using ha i
end GlobalTheory.CompanionTheory.LocalLattice


