-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFlagDualMatrix
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFlagDualMatrix
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:45.869648+00:00
-- url     : https://prove2.me/theorems/bfacdd41-3ec3-4890-9597-f75247b18c14
-- title:
--   Exists Flag Dual Matrix
-- statement:
--   Definitions and structural lemmas for Exists Flag Dual Matrix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFlagDualMatrix.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.IwaFlag
variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {ρ : ℕ} {c : R →+* R} {ε : R} {O : AddSubgroup R}
  {h : V →ₗ[R] V →ₛₗ[c] R} {M : AddSubgroup V}
def Princ (ε : R) (O : AddSubgroup R) : Prop :=
  ∀ J : AddSubgroup R, (∀ a ∈ J, ε * a = a) → (∀ o ∈ O, ∀ a ∈ J, o * a ∈ J) → (∃ m : ℕ, 0 < m ∧ (m : R) * ε ∈ J) →
    (∃ N : ℕ, 0 < N ∧ ∀ a ∈ J, (N : R) * a ∈ O) → ∃ α ∈ J, ∃ α', ε * α' = α' ∧ α * α' = ε ∧ ∀ a ∈ J, α' * a ∈ O
open Matrix in

def sesq (c : R →+* R) {n : ℕ} (G : Matrix (Fin n) (Fin n) R) : (Fin n → R) →ₗ[R] (Fin n → R) →ₛₗ[c] R :=
  LinearMap.mk₂'ₛₗ (RingHom.id R) c (fun x y => ∑ i, ∑ j, c (y i) * G i j * x j)
    (fun x x' y => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun a x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    (fun x y y' => by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
    (fun a x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
end GlobalTheory.IwaFlag


