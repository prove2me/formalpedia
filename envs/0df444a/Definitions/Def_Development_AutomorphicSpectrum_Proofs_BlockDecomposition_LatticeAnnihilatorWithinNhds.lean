-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeAnnihilatorWithinNhds
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeAnnihilatorWithinNhds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:32.640061+00:00
-- url     : https://prove2.me/theorems/97188eb9-a83d-4b10-a66d-03e7a7520aa8
-- title:
--   Lattice Annihilator Within Nhds
-- statement:
--   Definitions and structural lemmas for Lattice Annihilator Within Nhds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeAnnihilatorWithinNhds.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel
open scoped Topology
noncomputable section
namespace GlobalTheory.CompanionTheory.AnnihShrink
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def box (n : ℕ) (b : k) : AddSubgroup (Fin n → k) where
  carrier := {a | ∀ j, valuation k (a j) ≤ valuation k b}
  zero_mem' := fun j => by simp
  add_mem' := fun {x y} hx hy j =>
    ((valuation k).map_add _ _).trans (max_le (hx j) (hy j))
  neg_mem' := fun {x} hx j => by simpa using hx j
end GlobalTheory.CompanionTheory.AnnihShrink


