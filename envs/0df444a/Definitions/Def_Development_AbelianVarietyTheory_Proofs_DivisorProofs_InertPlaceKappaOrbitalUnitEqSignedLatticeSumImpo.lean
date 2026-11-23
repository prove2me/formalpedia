-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:47.220202+00:00
-- url     : https://prove2.me/theorems/55da3550-3660-44a0-b8ac-27c210d1e2d6
-- title:
--   Inert Place Kappa Orbital Unit Eq Signed Lattice Sum Impo
-- statement:
--   Definitions and structural lemmas for Inert Place Kappa Orbital Unit Eq Signed Lattice Sum Impo, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.InertUnitOrb
open GlobalTheory.UnitLemma Matrix
def stdH (K : UQ) (n : ℕ) (y z : Fin n → K.E) : K.E := ∑ k, y k * K.c (z k)
def IsModel {K : UQ} (B : InvAlg K) {n : ℕ} (γ : Matrix (Fin n) (Fin n) K.E) (x : B.Aˣ)
    (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) : Prop :=
  B.σ (x : B.A) = x ∧ (∀ y, ψ (B.g * y) = γ *ᵥ ψ y) ∧ ∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z
end GlobalTheory.InertUnitOrb


