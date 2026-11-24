-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsStd
-- name    : Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsStd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:27.32285+00:00
-- url     : https://prove2.me/theorems/7558043c-23fa-427d-bde0-d62a2d8f8b05
-- title:
--   Exists Std
-- statement:
--   Definitions and structural lemmas for Exists Std, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsStd.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SchrodingerModelSelfDualLatticeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix Topology
namespace GlobalTheory.CompanionTheory.StdLattice
variable {R : Type} [CommRing R] {κ : Type} [Fintype κ]
def box (O : Subring R) (v : Rˣ) (κ : Type) : AddSubgroup (κ → R) where
  carrier := {x | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O}
  zero_mem' := fun i => by simp
  add_mem' := fun hx hy i => by simpa [mul_add] using O.add_mem (hx i) (hy i)
  neg_mem' := fun hx i => by simpa using O.neg_mem (hx i)
def ind (O : Subring R) (κ : Type) : (κ → R) → ℂ := Set.indicator {x : κ → R | ∀ i, x i ∈ O} fun _ => (1 : ℂ)
variable [TopologicalSpace R]
variable [IsTopologicalRing R] [Invertible (2 : R)]
end GlobalTheory.CompanionTheory.StdLattice


