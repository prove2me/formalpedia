-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
-- name    : QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:43:45.635713+00:00
-- url     : https://prove2.me/theorems/aebf61ec-2d8f-453b-b228-80b8d2b40c52
-- title:
--   Fixed Field Artin Schreier
-- statement:
--   Definitions and structural lemmas for Fixed Field Artin Schreier, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/FixedFieldArtinSchreier.lean

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Field
import Mathlib.FieldTheory.Finite.Trace
import Theorems.Thm_QEC_Coding_f256_card
import Theorems.Thm_QEC_Coding_f256_finrank

set_option autoImplicit false
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
abbrev F16 : Type := GaloisField 2 4
noncomputable instance f16Fintype : Fintype F16 := Fintype.ofFinite F16
theorem f16_card : Fintype.card F16 = 16 := by
  rw [Fintype.card_eq_nat_card]
  simpa using (GaloisField.card 2 4 (by norm_num : (4 : ℕ) ≠ 0))
theorem f16_finrank : Module.finrank (ZMod 2) F16 = 4 := by
  exact GaloisField.finrank 2 (by norm_num : (4 : ℕ) ≠ 0)
noncomputable def f16Embedding : F16 →ₐ[ZMod 2] F256 :=
  Classical.choice
    (FiniteField.nonempty_algHom_of_finrank_dvd
      (F := ZMod 2) (K := F16) (L := F256) (by
        rw [f16_finrank, f256_finrank]
        norm_num))
noncomputable instance f256F16Algebra : Algebra F16 F256 :=
  f16Embedding.toRingHom.toAlgebra
noncomputable instance f256F16ScalarTower : IsScalarTower (ZMod 2) F16 F256 :=
  IsScalarTower.of_algebraMap_eq fun c => (f16Embedding.commutes c).symm
theorem f256_finrank_over_f16 : Module.finrank F16 F256 = 2 := by
  have h := Module.finrank_mul_finrank (ZMod 2) F16 F256
  rw [f16_finrank, f256_finrank] at h
  omega
noncomputable def f256ArtinSchreier : F256 →ₗ[F16] F256 :=
  (FiniteField.frobeniusAlgHom F16 F256).toLinearMap + LinearMap.id
@[simp] theorem f256ArtinSchreier_apply (x : F256) :
    f256ArtinSchreier x = x ^ 16 + x := by
  change x ^ Fintype.card F16 + x = x ^ 16 + x
  rw [f16_card]
theorem algebraMap_trace_eq_f256ArtinSchreier (x : F256) :
    algebraMap F16 F256 (Algebra.trace F16 F256 x) = f256ArtinSchreier x := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow]
  simp only [f256_finrank_over_f16, Nat.card_eq_fintype_card, f16_card]
  norm_num [Finset.sum_range_succ, f256ArtinSchreier_apply, add_comm]
noncomputable instance f256ArtinSchreierKernelFintype :
    Fintype (LinearMap.ker f256ArtinSchreier) := Fintype.ofFinite _
noncomputable def f256ArtinSchreierRoot (x : F256) : F256 :=
  Classical.choose
    (Algebra.trace_surjective F16 F256 (Algebra.norm F16 x))
theorem f256ArtinSchreierRoot_trace (x : F256) :
    Algebra.trace F16 F256 (f256ArtinSchreierRoot x) = Algebra.norm F16 x :=
  Classical.choose_spec
    (Algebra.trace_surjective F16 F256 (Algebra.norm F16 x))
theorem f256ArtinSchreierRoot_spec (x : F256) :
    f256ArtinSchreier (f256ArtinSchreierRoot x) = x ^ 17 := by
  calc
    f256ArtinSchreier (f256ArtinSchreierRoot x) =
        algebraMap F16 F256 (Algebra.trace F16 F256 (f256ArtinSchreierRoot x)) :=
      (algebraMap_trace_eq_f256ArtinSchreier _).symm
    _ = algebraMap F16 F256 (Algebra.norm F16 x) := by
      rw [f256ArtinSchreierRoot_trace]
    _ = x ^ 17 := by
      rw [FiniteField.algebraMap_norm_eq_pow]
      norm_num [Nat.card_eq_fintype_card, f16_card, f256_card]
noncomputable def f256ArtinSchreierRoots (x : F256) : Finset F256 :=
  Finset.univ.filter fun y => f256ArtinSchreier y = x ^ 17
noncomputable def f256ArtinSchreierKernelEquivRoots (x : F256) :
    LinearMap.ker f256ArtinSchreier ≃ ↥(f256ArtinSchreierRoots x) where
  toFun y := ⟨f256ArtinSchreierRoot x + y, by
    simp only [f256ArtinSchreierRoots, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [map_add, f256ArtinSchreierRoot_spec, y.property, add_zero]⟩
  invFun y := ⟨y - f256ArtinSchreierRoot x, by
    change f256ArtinSchreier (y - f256ArtinSchreierRoot x) = 0
    rw [map_sub, f256ArtinSchreierRoot_spec]
    have hy : f256ArtinSchreier (y : F256) = x ^ 17 := by
      simpa only [f256ArtinSchreierRoots, Finset.mem_filter, Finset.mem_univ, true_and]
        using y.property
    rw [hy, sub_self]⟩
  left_inv y := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


