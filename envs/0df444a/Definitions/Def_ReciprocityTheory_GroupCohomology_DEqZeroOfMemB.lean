-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
-- name    : ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:23.466207+00:00
-- url     : https://prove2.me/theorems/52e7e10b-6cda-440d-9a3e-cef2f1c4e7f5
-- title:
--   DEq Zero Of Mem B
-- statement:
--   Definitions and structural lemmas for DEq Zero Of Mem B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/DEqZeroOfMemB.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
universe u
namespace Cx
variable {R : Type u} [CommRing R] {A B C : Cx R}
theorem Hom.d_f_eq_zero (φ : Hom A B) {n : ℕ} {x : A.X n} (hx : A.d n x = 0) :
    B.d n (φ.f n x) = 0 := by
  rw [← φ.comm, hx, map_zero]
theorem d_add_eq_zero {n : ℕ} {x y : A.X n} (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.d n (x + y) = 0 := by
  rw [map_add, hx, hy, add_zero]
theorem d_sub_eq_zero {n : ℕ} {x y : A.X n} (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.d n (x - y) = 0 := by
  rw [map_sub, hx, hy, sub_zero]
theorem d_neg_eq_zero {n : ℕ} {x : A.X n} (hx : A.d n x = 0) : A.d n (-x) = 0 := by
  rw [map_neg, hx, neg_zero]
theorem d_smul_eq_zero {n : ℕ} (r : R) {x : A.X n} (hx : A.d n x = 0) : A.d n (r • x) = 0 := by
  rw [map_smul, hx, smul_zero]
end Cx
end ReciprocityTheory.Coh


