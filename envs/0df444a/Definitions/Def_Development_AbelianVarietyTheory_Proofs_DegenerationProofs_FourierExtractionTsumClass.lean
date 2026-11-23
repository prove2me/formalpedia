-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:47.863283+00:00
-- url     : https://prove2.me/theorems/3bba1204-6401-45dc-b8fa-71bd2d3c9b6e
-- title:
--   Fourier Extraction Tsum Class
-- statement:
--   Definitions and structural lemmas for Fourier Extraction Tsum Class, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FourierExtractionTsumClass.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
namespace GlobalTheory
namespace TorsionFourier
section Algebra
variable {K X : Type} [Field K] [AddCommGroup X]
def torsionChars (K X : Type) [Field K] [AddCommGroup X] (N : ℕ) :
    Subgroup (Multiplicative X →* Kˣ) where
  carrier := {t | t ^ N = 1}
  one_mem' := one_pow N
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [mul_pow, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [inv_pow, ha, inv_one]
open Module in
variable {K X : Type} [Field K] [AddCommGroup X] in

theorem _root_.GlobalTheory.TorsionFourier.char_apply_eq_prod {ι : Type} [Fintype ι] (b : Basis ι ℤ X)
    (t : Multiplicative X →* Kˣ) (x : X) :
    t (Multiplicative.ofAdd x) = ∏ i, t (Multiplicative.ofAdd (b i)) ^ (b.repr x i) := by
  conv_lhs => rw [← b.sum_repr x]
  rw [ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofAdd_zsmul, map_zpow]
noncomputable def charOfValues {ι : Type} [Fintype ι] (b : Basis ι ℤ X) (u : ι → Kˣ) :
    Multiplicative X →* Kˣ where
  toFun x := ∏ i, u i ^ (b.repr x.toAdd i)
  map_one' := by simp
  map_mul' x y := by simp [zpow_add, Finset.prod_mul_distrib]
open Module in
variable {K X : Type} [Field K] [AddCommGroup X] in
theorem _root_.GlobalTheory.TorsionFourier.charOfValues_basis {ι : Type} [Fintype ι] (b : Basis ι ℤ X) (u : ι → Kˣ)
    (j : ι) : _root_.GlobalTheory.TorsionFourier.charOfValues b u (Multiplicative.ofAdd (b j)) = u j := by
  simp only [_root_.GlobalTheory.TorsionFourier.charOfValues, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
    Basis.repr_self]
  rw [Finset.prod_eq_single j
    (fun i _ hi => by simp [Finsupp.single_apply, Ne.symm hi]) (by simp)]
  simp
open Module in
variable {K X : Type} [Field K] [AddCommGroup X] in
theorem _root_.GlobalTheory.TorsionFourier.charOfValues_pow {ι : Type} [Fintype ι] (b : Basis ι ℤ X)
    (u : ι → Kˣ) (N : ℕ) (hu : ∀ i, u i ^ N = 1) : _root_.GlobalTheory.TorsionFourier.charOfValues b u ^ N = 1 := by
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply]
  simp only [_root_.GlobalTheory.TorsionFourier.charOfValues, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
open Module in
variable {K X : Type} [Field K] [AddCommGroup X] in
theorem _root_.GlobalTheory.TorsionFourier.apply_pow_eq_one {N : ℕ} {t : Multiplicative X →* Kˣ}
    (ht : t ^ N = 1) (x : Multiplicative X) : t x ^ N = 1 := by
  rw [← MonoidHom.pow_apply, ht, MonoidHom.one_apply]
noncomputable def torsionCharsEquiv {ι : Type} [Fintype ι] (b : Basis ι ℤ X) (N : ℕ) :
    torsionChars K X N ≃ (ι → rootsOfUnity N K) where
  toFun t i := ⟨t.1 (Multiplicative.ofAdd (b i)),
    (mem_rootsOfUnity _ _).2 (apply_pow_eq_one t.2 _)⟩
  invFun u := ⟨charOfValues b fun i => (u i).1,
    charOfValues_pow b _ N fun i => (mem_rootsOfUnity _ _).1 (u i).2⟩
  left_inv t := by
    refine Subtype.ext (MonoidHom.ext fun x => ?_)
    exact (char_apply_eq_prod b t.1 x.toAdd).symm
  right_inv u := by
    funext i
    exact Subtype.ext (charOfValues_basis b _ i)
variable [Module.Free ℤ X] [Module.Finite ℤ X]
end Algebra
end TorsionFourier
end GlobalTheory


