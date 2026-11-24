-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsLatticeOfCompactOpen
-- name    : Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsLatticeOfCompactOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:50.353802+00:00
-- url     : https://prove2.me/theorems/3ee0aafb-4861-4e6e-ae1e-672412e14a15
-- title:
--   Is Lattice Of Compact Open
-- statement:
--   Definitions and structural lemmas for Is Lattice Of Compact Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/IsLatticeOfCompactOpen.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_OrderOKOneInert
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsArtinianRingKummerAdjoinRootQuotientRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CompanionTheory.SplitIdx
section Lattice
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
end Lattice
def invT {k : Type} [CommRing k] {β : Type} [Fintype β] [DecidableEq β] (u : GL β k) : GL β k :=
  ⟨((u⁻¹ : GL β k) : Matrix β β k)ᵀ, (u : Matrix β β k)ᵀ,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
def swapAlg (k : Type) [CommRing k] : (k × k) ≃ₐ[k] k × k :=
  { (RingEquiv.prodComm : k × k ≃+* k × k) with commutes' := fun _ => rfl }
section Split
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {E : Type} [CommRing E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E]
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
end Split
end GlobalTheory.CompanionTheory.SplitIdx


