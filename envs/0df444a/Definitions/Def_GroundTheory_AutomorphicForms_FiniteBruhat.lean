-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
-- name    : GroundTheory_AutomorphicForms_FiniteBruhat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:51.848041+00:00
-- url     : https://prove2.me/theorems/c4a7f3e3-e4df-40b9-8150-eacbc65410d8
-- title:
--   Finite Bruhat
-- statement:
--   Definitions and structural lemmas for Finite Bruhat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open Matrix DoubleCoset
variable {n : ℕ} {k : Type*} [Field k]
variable (n k) in

def borel : Subgroup (GL (Fin n) k) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) k).IsUpperTriangular}
  mul_mem' {a b} ha hb := by
    show ((a * b : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).IsUpperTriangular
    rw [Units.val_mul]
    exact BlockTriangular.mul ha hb
  one_mem' := by
    show ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).IsUpperTriangular
    rw [Units.val_one]
    exact blockTriangular_one
  inv_mem' {a} ha := by
    show ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).IsUpperTriangular
    rw [Matrix.coe_units_inv]
    let _ := (Units.isUnit a).invertible
    exact blockTriangular_inv_of_blockTriangular ha
variable (k) in

noncomputable def permGL : Equiv.Perm (Fin n) →* GL (Fin n) k :=
  (Matrix.permMatrixHom (n := Fin n) (R := k)).toHomUnits
def RowsReduced (M : Matrix (Fin n) (Fin n) k) (t : ℕ) : Prop :=
  ∃ p : Fin n → Fin n, ∀ i : Fin n, t ≤ i.val →
    M i (p i) ≠ 0 ∧ (∀ c, c ≠ p i → M i c = 0) ∧ (∀ r, r ≠ i → M r (p i) = 0)
end GroundTheory.Automorphic


