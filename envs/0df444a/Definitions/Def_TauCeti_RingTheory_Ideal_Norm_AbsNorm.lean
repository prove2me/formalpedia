-- Prove2me | Definitions.Def_TauCeti_RingTheory_Ideal_Norm_AbsNorm
-- name    : TauCeti_RingTheory_Ideal_Norm_AbsNorm
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:42:02.391306+00:00
-- url     : https://prove2.me/theorems/0a791e09-000a-4ff4-8dd8-c518bc0d176f
-- title:
--   The absolute ideal norm under a ring isomorphism, and congruences of norms
-- statement:
--   In a ring free of finite rank over $\mathbb Z$, congruence modulo $(m)$ is compatible with algebraic norms. In the Dedekind-domain setting, when the signed norms have nonnegative product, the corresponding principal ideals have congruent absolute norms. These norm-transport facts support the rational-prime and congruence interfaces.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/Ideal/Norm/AbsNorm.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/Ideal/Norm/AbsNorm.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Data_ZMod_Divisibility
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The absolute ideal norm under a ring isomorphism, and congruences of norms

Identifying two rings along an isomorphism identifies their ideals, and the absolute norm is
insensitive to that identification.

In a ring that is free of finite rank over `ℤ`, elements congruent modulo `(m)` have norms
congruent modulo `m`; for principal ideals whose generators have norms with nonnegative product,
the congruence passes to the absolute norms.

## Main results

* `Ideal.absNorm_comap_of_ringEquiv`, `Ideal.absNorm_map_of_ringEquiv`: the absolute norm of an
  ideal is unchanged by transporting it along a ring isomorphism, in either direction.
* `Algebra.intCast_norm_eq_of_sub_mem_span_natCast`: elements congruent modulo `(m)` have norms
  congruent modulo `m`.
* `Ideal.span_singleton_natCast_eq_top_iff`: the ideal `(m)` is the unit ideal only for `m = 1`.
* `Ideal.natCast_absNorm_span_singleton_eq_of_sub_mem`: congruent elements whose norms have
  nonnegative product generate ideals with absolute norms congruent modulo `m`.
-/

 section

namespace Ideal

variable {R R' : Type*} [CommRing R] [CommRing R'] [IsDedekindDomain R] [IsDedekindDomain R']
  [Module.Free ℤ R] [Module.Free ℤ R']





end Ideal

section Congruence

variable {S : Type*} [CommRing S] [Module.Free ℤ S] [Module.Finite ℤ S]

/-- **Congruent elements have congruent norms.** If `a ≡ b` modulo the ideal `(m)` of a ring `S`
that is free of finite rank over `ℤ`, then `N(a) ≡ N(b)` modulo `m`. -/
theorem Algebra.intCast_norm_eq_of_sub_mem_span_natCast {m : ℕ} {a b : S}
    (h : a - b ∈ Ideal.span {(m : S)}) :
    ((Algebra.norm ℤ a : ℤ) : ZMod m) = ((Algebra.norm ℤ b : ℤ) : ZMod m) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  let B := Module.Free.chooseBasis ℤ S
  rw [Algebra.norm_eq_matrix_det B, Algebra.norm_eq_matrix_det B,
    ← eq_intCast (Int.castRingHom (ZMod m)) (Algebra.leftMulMatrix B a).det,
    ← eq_intCast (Int.castRingHom (ZMod m)) (Algebra.leftMulMatrix B b).det, RingHom.map_det,
    RingHom.map_det, sub_eq_iff_eq_add.mp hc.symm, map_add, map_mul, map_natCast, map_add,
    map_mul, map_natCast, ← Matrix.diagonal_natCast, ZMod.natCast_self, Matrix.diagonal_zero,
    mul_zero, zero_add]

/-- **The ideal `(m)` is the unit ideal only for `m = 1`**, in a nontrivial ring that is free of
finite rank over `ℤ`. -/
theorem Ideal.span_singleton_natCast_eq_top_iff [Nontrivial S] {m : ℕ} :
    Ideal.span {(m : S)} = ⊤ ↔ m = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  -- the norm `m ^ [S : ℤ]` of the unit `m` is a unit of `ℤ`
  have hu := Int.isUnit_iff_natAbs_eq.mp
    ((Ideal.span_singleton_eq_top.mp h).map (Algebra.norm ℤ (S := S)))
  rw [Algebra.norm_natCast, Int.natAbs_pow, Int.natAbs_natCast] at hu
  exact (Nat.pow_eq_one.mp hu).resolve_right Module.finrank_pos.ne'

/-- **Congruent elements with norms of nonnegative product generate ideals of congruent norms.**
If `a ≡ b` modulo the ideal `(m)` of a Dedekind domain `S` that is free of finite rank over `ℤ`,
and `N(a) N(b) ≥ 0`, then the absolute norms of `(a)` and `(b)` are congruent modulo `m`. -/
theorem Ideal.natCast_absNorm_span_singleton_eq_of_sub_mem [IsDedekindDomain S] [Infinite S]
    {m : ℕ}
    {a b : S} (hab : 0 ≤ Algebra.norm ℤ a * Algebra.norm ℤ b)
    (h : a - b ∈ Ideal.span {(m : S)}) :
    (Ideal.absNorm (Ideal.span {a}) : ZMod m) = Ideal.absNorm (Ideal.span {b}) := by
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton]
  exact ZMod.natCast_natAbs_eq_of_mul_nonneg hab (Algebra.intCast_norm_eq_of_sub_mem_span_natCast h)

end Congruence


end
end


