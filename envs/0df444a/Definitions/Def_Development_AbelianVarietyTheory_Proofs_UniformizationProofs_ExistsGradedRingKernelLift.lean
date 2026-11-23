-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGradedRingKernelLift
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGradedRingKernelLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:26:06.926799+00:00
-- url     : https://prove2.me/theorems/59422bc3-d421-49c7-8cdf-05da39bbcfbd
-- title:
--   Exists Graded Ring Kernel Lift
-- statement:
--   Definitions and structural lemmas for Exists Graded Ring Kernel Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGradedRingKernelLift.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace GlobalTheory
def reesShiftIdeal {R : Type} [CommRing R] (I : Ideal R) : Ideal (reesAlgebra I) where
  carrier := {p | ∀ n, (p : R[X]).coeff n ∈ I ^ (n + 1)}
  zero_mem' := fun n => by simp
  add_mem' := fun {p q} hp hq n => by
    rw [Subalgebra.coe_add, coeff_add]
    exact Ideal.add_mem _ (hp n) (hq n)
  smul_mem' := fun p q hq n => by
    rw [smul_eq_mul, Subalgebra.coe_mul, coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨j, k⟩ e
    have e' : j + k = n := by simpa using e
    rw [← e', add_assoc, pow_add]
    exact Ideal.mul_mem_mul (p.2 j) (hq k)
end GlobalTheory


