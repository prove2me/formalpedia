-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0008
-- name    : PNT_ZeroFree_433_0008
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T11:59:25.539138+00:00
-- url     : https://prove2.me/theorems/1c699f02-926f-4043-876c-a1f967ad04fb
-- title:
--   Zero-free region foundations: GaussSum.ChineseRemainder [0008]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.ChineseRemainder
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L19-L680

import Definitions.Def_PNT_ZeroFree_433_0001

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean#L19-L680
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.GaussSum.ChineseRemainder
section
namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open Finset Complex

open scoped Classical

namespace GaussCRT

theorem gauss_sum_chinese_product (m n : ℕ)
    [NeZero m] [NeZero n] [NeZero (m * n)] (h : m.Coprime n)
    (χm : MulChar (ZMod m) ℂ) (χn : MulChar (ZMod n) ℂ)
    (ψm : AddChar (ZMod m) ℂ) (ψn : AddChar (ZMod n) ℂ) :
    (∑ x : ZMod (m * n),
      χm ((ZMod.chineseRemainder h x).1) *
      χn ((ZMod.chineseRemainder h x).2) *
      ψm ((ZMod.chineseRemainder h x).1) *
      ψn ((ZMod.chineseRemainder h x).2)) =
      gaussSum χm ψm * gaussSum χn ψn := by
  let e := (ZMod.chineseRemainder h).toEquiv
  let F : ZMod m × ZMod n → ℂ :=
    fun z => χm z.1 * χn z.2 * ψm z.1 * ψn z.2
  calc
    (∑ x : ZMod (m * n),
      χm ((ZMod.chineseRemainder h x).1) *
      χn ((ZMod.chineseRemainder h x).2) *
      ψm ((ZMod.chineseRemainder h x).1) *
      ψn ((ZMod.chineseRemainder h x).2)) =
        ∑ x : ZMod (m * n), F (e x) := rfl
    _ = ∑ z : ZMod m × ZMod n, F z := Equiv.sum_comp e F
    _ = ∑ z : ZMod m, ∑ w : ZMod n, F (z, w) := Fintype.sum_prod_type F
    _ = gaussSum χm ψm * gaussSum χn ψn := by
      simp only [F, gaussSum]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro w hw
      ring

def leftAddChar (m n : ℕ) (h : m.Coprime n)
    (ψ : AddChar (ZMod (m * n)) ℂ) : AddChar (ZMod m) ℂ where
  toFun z := ψ ((ZMod.chineseRemainder h).symm (z, 0))
  map_zero_eq_one' := by
    change ψ ((ZMod.chineseRemainder h).symm (0 : ZMod m × ZMod n)) = 1
    rw [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' z w := by
    change ψ ((ZMod.chineseRemainder h).symm (z + w, 0)) =
      ψ ((ZMod.chineseRemainder h).symm (z, 0)) *
        ψ ((ZMod.chineseRemainder h).symm (w, 0))
    rw [show (z + w, (0 : ZMod n)) = (z, 0) + (w, 0) by ext <;> simp,
      map_add, AddChar.map_add_eq_mul]

def rightAddChar (m n : ℕ) (h : m.Coprime n)
    (ψ : AddChar (ZMod (m * n)) ℂ) : AddChar (ZMod n) ℂ where
  toFun z := ψ ((ZMod.chineseRemainder h).symm (0, z))
  map_zero_eq_one' := by
    change ψ ((ZMod.chineseRemainder h).symm (0 : ZMod m × ZMod n)) = 1
    rw [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' z w := by
    change ψ ((ZMod.chineseRemainder h).symm (0, z + w)) =
      ψ ((ZMod.chineseRemainder h).symm (0, z)) *
        ψ ((ZMod.chineseRemainder h).symm (0, w))
    rw [show ((0 : ZMod m), z + w) = (0, z) + (0, w) by ext <;> simp,
      map_add, AddChar.map_add_eq_mul]

theorem addChar_crt_factor (m n : ℕ) (h : m.Coprime n)
    (ψ : AddChar (ZMod (m * n)) ℂ) (x : ZMod (m * n)) :
    ψ x =
      leftAddChar m n h ψ ((ZMod.chineseRemainder h x).1) *
      rightAddChar m n h ψ ((ZMod.chineseRemainder h x).2) := by
  let z := ZMod.chineseRemainder h x
  have hz : (z.1, (0 : ZMod n)) + ((0 : ZMod m), z.2) = z := by
    ext <;> simp
  calc
    ψ x = ψ ((ZMod.chineseRemainder h).symm z) := by simp [z]
    _ = ψ ((ZMod.chineseRemainder h).symm (z.1, 0) +
          (ZMod.chineseRemainder h).symm (0, z.2)) := by
          rw [← map_add, hz]
    _ = _ := by rw [AddChar.map_add_eq_mul]; rfl

theorem gauss_sum_crt (m n : ℕ)
    [NeZero m] [NeZero n] [NeZero (m * n)] (h : m.Coprime n)
    (χm : MulChar (ZMod m) ℂ) (χn : MulChar (ZMod n) ℂ)
    (ψ : AddChar (ZMod (m * n)) ℂ) :
    (∑ x : ZMod (m * n),
      χm ((ZMod.chineseRemainder h x).1) *
      χn ((ZMod.chineseRemainder h x).2) * ψ x) =
      gaussSum χm (leftAddChar m n h ψ) *
      gaussSum χn (rightAddChar m n h ψ) := by
  simp_rw [addChar_crt_factor m n h ψ]
  convert! gauss_sum_chinese_product m n h χm χn
    (leftAddChar m n h ψ) (rightAddChar m n h ψ) using 1 ;
      congr 1 ; ext x ; ring

theorem crt_left_axis (m n r : ℕ) (h : m.Coprime n)
    [NeZero m] [NeZero n]
    (hr : ((n * r : ℕ) : ZMod m) = 1) (z : ZMod m) :
    (ZMod.chineseRemainder h).symm (z, 0) =
      ((n * r * z.val : ℕ) : ZMod (m * n)) := by
  apply (ZMod.chineseRemainder h).injective
  rw [(ZMod.chineseRemainder h).apply_symm_apply]
  have hfst (x : ZMod (m * n)) : ((ZMod.chineseRemainder h) x).1 =
      (x.cast : ZMod m) := by
        simp [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.fst_zmod_cast]
  have hsnd (x : ZMod (m * n)) : ((ZMod.chineseRemainder h) x).2 =
      (x.cast : ZMod n) := by
        simp [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.snd_zmod_cast]
  apply Prod.ext
  · rw [hfst, ZMod.cast_natCast (by simp : m ∣ m * n) (n * r * z.val)]
    simp only [ Nat.cast_mul]
    rw [← Nat.cast_mul (α := ZMod m) n r, hr, one_mul,
      ZMod.natCast_zmod_val]
  · rw [hsnd, ZMod.cast_natCast (by simp : n ∣ m * n) (n * r * z.val)]
    simp [Nat.cast_mul]

theorem leftAddChar_std_apply (m n r : ℕ) (h : m.Coprime n)
    [NeZero m] [NeZero n] [NeZero (m * n)]
    (hr : ((n * r : ℕ) : ZMod m) = 1) (z : ZMod m) :
    leftAddChar m n h (ZMod.stdAddChar (N := m * n)) z =
      (ZMod.stdAddChar (N := m)) ((r : ZMod m) * z) := by
  have hleft :
      leftAddChar m n h (ZMod.stdAddChar (N := m * n)) z =
      ZMod.stdAddChar ((n * r * z.val : ℕ) : ZMod (m * n)) := by
    change ZMod.stdAddChar ((ZMod.chineseRemainder h).symm (z, 0)) = _
    rw [crt_left_axis m n r h hr z]
  have hz : ((r : ZMod m) * z) = ((r * z.val : ℕ) : ZMod m) := by
    rw [← ZMod.natCast_zmod_val z]
    simp [Nat.cast_mul]
  rw [hleft, hz]
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have h1 := ZMod.stdAddChar_coe (N := m * n) (j := (n * r * z.val : ℤ))
  have h2 := ZMod.stdAddChar_coe (N := m) (j := (r * z.val : ℤ))
  norm_cast at h1 h2 ⊢
  rw [h1, h2]
  congr 1
  field_simp
  simp only [Nat.cast_mul]
  ring

theorem crt_right_axis (m n r : ℕ) (h : m.Coprime n)
    [NeZero m] [NeZero n]
    (hr : ((m * r : ℕ) : ZMod n) = 1) (z : ZMod n) :
    (ZMod.chineseRemainder h).symm (0, z) =
      ((m * r * z.val : ℕ) : ZMod (m * n)) := by
  apply (ZMod.chineseRemainder h).injective
  rw [(ZMod.chineseRemainder h).apply_symm_apply]
  have hfst (x : ZMod (m * n)) : ((ZMod.chineseRemainder h) x).1 =
      (x.cast : ZMod m) := by
        simp [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.fst_zmod_cast]
  have hsnd (x : ZMod (m * n)) : ((ZMod.chineseRemainder h) x).2 =
      (x.cast : ZMod n) := by
        simp [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.snd_zmod_cast]
  apply Prod.ext
  · rw [hfst, ZMod.cast_natCast (by simp : m ∣ m * n) (m * r * z.val)]
    simp [Nat.cast_mul]
  · rw [hsnd, ZMod.cast_natCast (by simp : n ∣ m * n) (m * r * z.val)]
    simp only [Nat.cast_mul]
    rw [← Nat.cast_mul (α := ZMod n) m r, hr, one_mul,
      ZMod.natCast_zmod_val]

theorem rightAddChar_std_apply (m n r : ℕ) (h : m.Coprime n)
    [NeZero m] [NeZero n] [NeZero (m * n)]
    (hr : ((m * r : ℕ) : ZMod n) = 1) (z : ZMod n) :
    rightAddChar m n h (ZMod.stdAddChar (N := m * n)) z =
      (ZMod.stdAddChar (N := n)) ((r : ZMod n) * z) := by
  have hright :
      rightAddChar m n h (ZMod.stdAddChar (N := m * n)) z =
      ZMod.stdAddChar ((m * r * z.val : ℕ) : ZMod (m * n)) := by
    change ZMod.stdAddChar ((ZMod.chineseRemainder h).symm (0, z)) = _
    rw [crt_right_axis m n r h hr z]
  have hz : ((r : ZMod n) * z) = ((r * z.val : ℕ) : ZMod n) := by
    rw [← ZMod.natCast_zmod_val z]
    simp [Nat.cast_mul]
  rw [hright, hz]
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have h1 := ZMod.stdAddChar_coe (N := m * n) (j := (m * r * z.val : ℤ))
  have h2 := ZMod.stdAddChar_coe (N := n) (j := (r * z.val : ℤ))
  norm_cast at h1 h2 ⊢
  rw [h1, h2]
  congr 1
  field_simp
  simp only [Nat.cast_mul]
  ring

theorem gauss_shift_cross (m n r : ℕ) [NeZero m]
    (χ : MulChar (ZMod m) ℂ)
    (hr : ((n * r : ℕ) : ZMod m) = 1) :
    gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m)) =
      χ (n : ZMod m) * gaussSum χ (ZMod.stdAddChar (N := m)) := by
  have hrprod : (n : ZMod m) * (r : ZMod m) = 1 := by
    simpa only [Nat.cast_mul] using hr
  have hur : IsUnit (r : ZMod m) :=
    IsUnit.of_mul_eq_one_right (n : ZMod m) hrprod
  have hcharprod : χ (n : ZMod m) * χ (r : ZMod m) = 1 := by
    rw [← map_mul, hrprod, map_one]
  have hshift := gaussSum_mulShift χ (ZMod.stdAddChar (N := m)) hur.unit
  have hshift' : χ (r : ZMod m) *
      gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m)) =
      gaussSum χ (ZMod.stdAddChar (N := m)) := by
    simpa only [hur.unit_spec] using hshift
  calc
    gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m)) =
        (χ (n : ZMod m) * χ (r : ZMod m)) *
          gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m)) := by
            rw [hcharprod, one_mul]
    _ = χ (n : ZMod m) *
          (χ (r : ZMod m) *
            gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m))) := by ring
    _ = χ (n : ZMod m) * gaussSum χ (ZMod.stdAddChar (N := m)) := by rw [hshift']

theorem gauss_sum_crt_standard (m n r s : ℕ)
    [NeZero m] [NeZero n] [NeZero (m * n)]
    (h : m.Coprime n)
    (hr : ((n * r : ℕ) : ZMod m) = 1)
    (hs : ((m * s : ℕ) : ZMod n) = 1)
    (χm : MulChar (ZMod m) ℂ) (χn : MulChar (ZMod n) ℂ) :
    (∑ x : ZMod (m * n),
      χm ((ZMod.chineseRemainder h x).1) *
      χn ((ZMod.chineseRemainder h x).2) *
      (ZMod.stdAddChar (N := m * n)) x) =
      χm (n : ZMod m) * χn (m : ZMod n) *
        gaussSum χm (ZMod.stdAddChar (N := m)) *
        gaussSum χn (ZMod.stdAddChar (N := n)) := by
  have hleft : leftAddChar m n h (ZMod.stdAddChar (N := m * n)) =
      (ZMod.stdAddChar (N := m)).mulShift (r : ZMod m) := by
    ext z
    exact leftAddChar_std_apply m n r h hr z
  have hright : rightAddChar m n h (ZMod.stdAddChar (N := m * n)) =
      (ZMod.stdAddChar (N := n)).mulShift (s : ZMod n) := by
    ext z
    exact rightAddChar_std_apply m n s h hs z
  rw [gauss_sum_crt m n h χm χn (ZMod.stdAddChar (N := m * n)),
      hleft, hright,
      gauss_shift_cross m n r χm hr,
      gauss_shift_cross n m s χn hs]
  ring

end GaussCRT

open scoped Classical

namespace IdealGaussCRT

variable {T R S : Type*} [CommRing T] [CommRing R] [CommRing S]

def leftAddChar (e : T ≃+* R × S) (ψ : AddChar T ℂ) : AddChar R ℂ where
  toFun z := ψ (e.symm (z, 0))
  map_zero_eq_one' := by
    change ψ (e.symm (0 : R × S)) = 1
    rw [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' z w := by
    change ψ (e.symm (z + w, 0)) = ψ (e.symm (z, 0)) * ψ (e.symm (w, 0))
    rw [show (z + w, (0 : S)) = (z, 0) + (w, 0) by ext <;> simp,
      map_add, AddChar.map_add_eq_mul]

def rightAddChar (e : T ≃+* R × S) (ψ : AddChar T ℂ) : AddChar S ℂ where
  toFun z := ψ (e.symm (0, z))
  map_zero_eq_one' := by
    change ψ (e.symm (0 : R × S)) = 1
    rw [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' z w := by
    change ψ (e.symm (0, z + w)) = ψ (e.symm (0, z)) * ψ (e.symm (0, w))
    rw [show ((0 : R), z + w) = (0, z) + (0, w) by ext <;> simp,
      map_add, AddChar.map_add_eq_mul]

theorem addChar_crt_factor (e : T ≃+* R × S) (ψ : AddChar T ℂ) (x : T) :
    ψ x = leftAddChar e ψ (e x).1 * rightAddChar e ψ (e x).2 := by
  let z := e x
  have hz : (z.1, (0 : S)) + ((0 : R), z.2) = z := by ext <;> simp
  calc
    ψ x = ψ (e.symm z) := by simp [z]
    _ = ψ (e.symm (z.1, 0) + e.symm (0, z.2)) := by rw [← map_add, hz]
    _ = _ := by rw [AddChar.map_add_eq_mul]; rfl

theorem gauss_sum_crt [Fintype T] [Fintype R] [Fintype S]
    (e : T ≃+* R × S) (χR : MulChar R ℂ) (χS : MulChar S ℂ)
    (ψ : AddChar T ℂ) :
    (∑ x : T, χR (e x).1 * χS (e x).2 * ψ x) =
      gaussSum χR (leftAddChar e ψ) * gaussSum χS (rightAddChar e ψ) := by
  simp_rw [addChar_crt_factor e ψ]
  let F : R × S → ℂ := fun z =>
    χR z.1 * χS z.2 * leftAddChar e ψ z.1 * rightAddChar e ψ z.2
  calc
    (∑ x : T,
      χR (e x).1 * χS (e x).2 *
        (leftAddChar e ψ (e x).1 * rightAddChar e ψ (e x).2)) =
        ∑ x : T, F (e x) := by congr 1; ext x; simp [F]; ring
    _ = ∑ z : R × S, F z := Equiv.sum_comp e.toEquiv F
    _ = ∑ z : R, ∑ w : S, F (z, w) := Fintype.sum_prod_type F
    _ = gaussSum χR (leftAddChar e ψ) * gaussSum χS (rightAddChar e ψ) := by
      simp only [F, gaussSum]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro w hw
      ring

theorem gauss_sum_ideal_crt {A : Type*} [CommRing A]
    (I J : Ideal A) (h : IsCoprime I J)
    [Fintype (A ⧸ I * J)] [Fintype (A ⧸ I)] [Fintype (A ⧸ J)]
    (χI : MulChar (A ⧸ I) ℂ) (χJ : MulChar (A ⧸ J) ℂ)
    (ψ : AddChar (A ⧸ I * J) ℂ) :
    (∑ x : A ⧸ I * J,
      χI (Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) x) *
      χJ (Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) x) * ψ x) =
      gaussSum χI (leftAddChar (Ideal.quotientMulEquivQuotientProd I J h) ψ) *
      gaussSum χJ (rightAddChar (Ideal.quotientMulEquivQuotientProd I J h) ψ) := by
  let e := Ideal.quotientMulEquivQuotientProd I J h
  convert! gauss_sum_crt e χI χJ ψ using 1
  congr 1
  ext x
  simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
    Ideal.quotientMulEquivQuotientProd_snd]

noncomputable def quotientAddChar {A : Type*} [CommRing A]
    (I : Ideal A) (ψ : AddChar A ℂ)
    (hper : ∀ a : A, a ∈ I → ψ a = 1) : AddChar (A ⧸ I) ℂ where
  toFun := fun x => Quotient.liftOn' x ψ (by
    intro a b hab
    have hsub : a - b ∈ I := I.quotientRel_def.mp hab
    have h := ψ.map_add_eq_mul (a - b) b
    rw [sub_add_cancel] at h
    rw [hper _ hsub, one_mul] at h
    exact h)
  map_zero_eq_one' := by
    change ψ 0 = 1
    exact AddChar.map_zero_eq_one ψ
  map_add_eq_mul' := by
    intro x y
    refine Quotient.inductionOn₂' x y ?_
    intro a b
    exact AddChar.map_add_eq_mul ψ a b

@[simp] theorem quotientAddChar_mk {A : Type*} [CommRing A]
    (I : Ideal A) (ψ : AddChar A ℂ)
    (hper : ∀ a : A, a ∈ I → ψ a = 1) (a : A) :
    quotientAddChar I ψ hper (Ideal.Quotient.mk I a) = ψ a := rfl

theorem principal_coprime_of_bezout {A : Type*} [CommRing A]
    {a b u v : A} (h : u * a + v * b = 1) :
    IsCoprime (Ideal.span {a}) (Ideal.span {b}) := by
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨u * a, ?_, v * b, ?_, h⟩
  · exact Ideal.mem_span_singleton.mpr ⟨u, by ring⟩
  · exact Ideal.mem_span_singleton.mpr ⟨v, by ring⟩

theorem bezout_of_principal_coprime {A : Type*} [CommRing A]
    {a b : A} (h : IsCoprime (Ideal.span {a}) (Ideal.span {b})) :
    ∃ u v : A, u * a + v * b = 1 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hy
  refine ⟨u, v, ?_⟩
  rw [hu, hv] at hxy
  convert! hxy using 1; ring

theorem crt_left_inverse_coordinate {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) (x : A) :
    (Ideal.quotientMulEquivQuotientProd
      (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm
        (Ideal.Quotient.mk (Ideal.span {a}) x, 0) =
      Ideal.Quotient.mk ((Ideal.span {a}) * (Ideal.span {b})) (x * v * b) := by
  let I : Ideal A := Ideal.span {a}
  let J : Ideal A := Ideal.span {b}
  let e := Ideal.quotientMulEquivQuotientProd I J
    (principal_coprime_of_bezout hbez)
  apply e.injective
  apply Prod.ext
  · change (e (e.symm (Ideal.Quotient.mk I x, 0))).1 =
      (e (Ideal.Quotient.mk (I * J) (x * v * b))).1
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq.mpr
    change x - x * v * b ∈ I
    rw [Ideal.mem_span_singleton]
    refine ⟨x * u, ?_⟩
    calc
      x - x * v * b = x * (u * a + v * b) - x * v * b := by rw [hbez]; ring
      _ = a * (x * u) := by ring
  · change (e (e.symm (Ideal.Quotient.mk I x, 0))).2 =
      (e (Ideal.Quotient.mk (I * J) (x * v * b))).2
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_snd,
      Ideal.Quotient.factor_mk]
    symm
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    exact Ideal.mem_span_singleton.mpr ⟨x * v, by ring⟩

theorem crt_right_inverse_coordinate {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) (y : A) :
    (Ideal.quotientMulEquivQuotientProd
      (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm
        (0, Ideal.Quotient.mk (Ideal.span {b}) y) =
      Ideal.Quotient.mk ((Ideal.span {a}) * (Ideal.span {b})) (y * u * a) := by
  let I : Ideal A := Ideal.span {a}
  let J : Ideal A := Ideal.span {b}
  let e := Ideal.quotientMulEquivQuotientProd I J
    (principal_coprime_of_bezout hbez)
  apply e.injective
  apply Prod.ext
  · change (e (e.symm (0, Ideal.Quotient.mk J y))).1 =
      (e (Ideal.Quotient.mk (I * J) (y * u * a))).1
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.Quotient.factor_mk]
    symm
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    exact Ideal.mem_span_singleton.mpr ⟨y * u, by ring⟩
  · change (e (e.symm (0, Ideal.Quotient.mk J y))).2 =
      (e (Ideal.Quotient.mk (I * J) (y * u * a))).2
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_snd,
      Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq.mpr
    change y - y * u * a ∈ J
    rw [Ideal.mem_span_singleton]
    refine ⟨y * v, ?_⟩
    calc
      y - y * u * a = y * (u * a + v * b) - y * u * a := by rw [hbez]; ring
      _ = b * (y * v) := by ring

noncomputable def rawTraceChar {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (c : A) : AddChar A ℂ where
  toFun x := ψ (ι x / (ι c * lam))
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    rw [map_add, add_div, AddChar.map_add_eq_mul]

theorem rawTraceChar_period {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (c : A)
    (hc : ι c ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1)
    (x : A) (hx : x ∈ Ideal.span {c}) :
    rawTraceChar ι ψ lam c x = 1 := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
  rw [hy]
  change ψ (ι (c * y) / (ι c * lam)) = 1
  rw [map_mul]
  have hfrac : ι c * ι y / (ι c * lam) = ι y / lam := by
    field_simp
  rw [hfrac]
  exact hbase y

noncomputable def traceModChar {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (c : A)
    (hc : ι c ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) :
    AddChar (A ⧸ Ideal.span {c}) ℂ :=
  quotientAddChar (Ideal.span {c}) (rawTraceChar ι ψ lam c)
    (rawTraceChar_period ι ψ lam c hc hlam hbase)

@[simp] theorem traceModChar_mk {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (c : A)
    (hc : ι c ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) (x : A) :
    traceModChar ι ψ lam c hc hlam hbase
      (Ideal.Quotient.mk (Ideal.span {c}) x) =
      ψ (ι x / (ι c * lam)) := rfl

noncomputable def traceProdChar {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (a b : A)
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) :
    AddChar (A ⧸ (Ideal.span {a}) * (Ideal.span {b})) ℂ :=
  quotientAddChar ((Ideal.span {a}) * (Ideal.span {b}))
    (rawTraceChar ι ψ lam (a * b)) (by
      intro x hx
      have hx' : x ∈ Ideal.span {a * b} := by
        simpa only [Ideal.span_singleton_mul_span_singleton] using hx
      exact rawTraceChar_period ι ψ lam (a * b)
        (by simpa only [map_mul] using mul_ne_zero ha hb)
        hlam hbase x hx')

@[simp] theorem traceProdChar_mk {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (a b : A)
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) (x : A) :
    traceProdChar ι ψ lam a b ha hb hlam hbase
      (Ideal.Quotient.mk ((Ideal.span {a}) * (Ideal.span {b})) x) =
      ψ (ι x / (ι (a * b) * lam)) := rfl

theorem leftAddChar_traceProd {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ)
    {a b u v : A} (hbez : u * a + v * b = 1)
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) :
    leftAddChar
      (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez))
      (traceProdChar ι ψ lam a b ha hb hlam hbase) =
      (traceModChar ι ψ lam a ha hlam hbase).mulShift
        (Ideal.Quotient.mk (Ideal.span {a}) v) := by
  ext z
  refine Quotient.inductionOn' z ?_
  intro x
  change traceProdChar ι ψ lam a b ha hb hlam hbase
      ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez)).symm
        (Ideal.Quotient.mk (Ideal.span {a}) x, 0)) =
    (traceModChar ι ψ lam a ha hlam hbase).mulShift
      (Ideal.Quotient.mk (Ideal.span {a}) v)
      (Ideal.Quotient.mk (Ideal.span {a}) x)
  rw [crt_left_inverse_coordinate hbez x]
  simp only [traceProdChar_mk, AddChar.mulShift_apply, ← map_mul,
    traceModChar_mk]
  congr 1
  simp only [map_mul]
  field_simp

theorem rightAddChar_traceProd {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ)
    {a b u v : A} (hbez : u * a + v * b = 1)
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) :
    rightAddChar
      (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez))
      (traceProdChar ι ψ lam a b ha hb hlam hbase) =
      (traceModChar ι ψ lam b hb hlam hbase).mulShift
        (Ideal.Quotient.mk (Ideal.span {b}) u) := by
  ext z
  refine Quotient.inductionOn' z ?_
  intro y
  change traceProdChar ι ψ lam a b ha hb hlam hbase
      ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez)).symm
        (0, Ideal.Quotient.mk (Ideal.span {b}) y)) =
    (traceModChar ι ψ lam b hb hlam hbase).mulShift
      (Ideal.Quotient.mk (Ideal.span {b}) u)
      (Ideal.Quotient.mk (Ideal.span {b}) y)
  rw [crt_right_inverse_coordinate hbez y]
  simp only [traceProdChar_mk, AddChar.mulShift_apply, ← map_mul,
    traceModChar_mk]
  congr 1
  simp only [map_mul]
  field_simp

theorem bezout_inverse_left {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) :
    (Ideal.Quotient.mk (Ideal.span {a}) b) *
      (Ideal.Quotient.mk (Ideal.span {a}) v) = 1 := by
  rw [← map_mul]
  apply Ideal.Quotient.eq.mpr
  change b * v - 1 ∈ Ideal.span {a}
  rw [Ideal.mem_span_singleton]
  refine ⟨-u, ?_⟩
  calc
    b * v - 1 = b * v - (u * a + v * b) := by rw [hbez]
    _ = a * -u := by ring

theorem bezout_inverse_right {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) :
    (Ideal.Quotient.mk (Ideal.span {b}) a) *
      (Ideal.Quotient.mk (Ideal.span {b}) u) = 1 := by
  rw [← map_mul]
  apply Ideal.Quotient.eq.mpr
  change a * u - 1 ∈ Ideal.span {b}
  rw [Ideal.mem_span_singleton]
  refine ⟨-v, ?_⟩
  calc
    a * u - 1 = a * u - (u * a + v * b) := by rw [hbez]
    _ = b * -v := by ring

theorem gauss_shift_bezout_left {A : Type*} [CommRing A]
    {a b u v : A} [Fintype (A ⧸ Ideal.span {a})]
    (hbez : u * a + v * b = 1)
    (χ : MulChar (A ⧸ Ideal.span {a}) ℂ)
    (ψ : AddChar (A ⧸ Ideal.span {a}) ℂ) :
    gaussSum χ (ψ.mulShift (Ideal.Quotient.mk (Ideal.span {a}) v)) =
      χ (Ideal.Quotient.mk (Ideal.span {a}) b) * gaussSum χ ψ := by
  let mb := Ideal.Quotient.mk (Ideal.span {a}) b
  let mv := Ideal.Quotient.mk (Ideal.span {a}) v
  have hprod : mb * mv = 1 := bezout_inverse_left hbez
  have hu : IsUnit mv := IsUnit.of_mul_eq_one_right mb hprod
  have hχ : χ mb * χ mv = 1 := by rw [← map_mul, hprod, map_one]
  have hshift := gaussSum_mulShift χ ψ hu.unit
  have hshift' : χ mv * gaussSum χ (ψ.mulShift mv) = gaussSum χ ψ := by
    simpa only [hu.unit_spec] using hshift
  calc
    gaussSum χ (ψ.mulShift mv) =
        (χ mb * χ mv) * gaussSum χ (ψ.mulShift mv) := by rw [hχ, one_mul]
    _ = χ mb * (χ mv * gaussSum χ (ψ.mulShift mv)) := by ring
    _ = χ mb * gaussSum χ ψ := by rw [hshift']

theorem gauss_shift_bezout_right {A : Type*} [CommRing A]
    {a b u v : A} [Fintype (A ⧸ Ideal.span {b})]
    (hbez : u * a + v * b = 1)
    (χ : MulChar (A ⧸ Ideal.span {b}) ℂ)
    (ψ : AddChar (A ⧸ Ideal.span {b}) ℂ) :
    gaussSum χ (ψ.mulShift (Ideal.Quotient.mk (Ideal.span {b}) u)) =
      χ (Ideal.Quotient.mk (Ideal.span {b}) a) * gaussSum χ ψ := by
  let ma := Ideal.Quotient.mk (Ideal.span {b}) a
  let mu := Ideal.Quotient.mk (Ideal.span {b}) u
  have hprod : ma * mu = 1 := bezout_inverse_right hbez
  have hu : IsUnit mu := IsUnit.of_mul_eq_one_right ma hprod
  have hχ : χ ma * χ mu = 1 := by rw [← map_mul, hprod, map_one]
  have hshift := gaussSum_mulShift χ ψ hu.unit
  have hshift' : χ mu * gaussSum χ (ψ.mulShift mu) = gaussSum χ ψ := by
    simpa only [hu.unit_spec] using hshift
  calc
    gaussSum χ (ψ.mulShift mu) =
        (χ ma * χ mu) * gaussSum χ (ψ.mulShift mu) := by rw [hχ, one_mul]
    _ = χ ma * (χ mu * gaussSum χ (ψ.mulShift mu)) := by ring
    _ = χ ma * gaussSum χ ψ := by rw [hshift']

theorem gauss_sum_trace_crt {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ)
    {a b u v : A} (hbez : u * a + v * b = 1)
    [Fintype (A ⧸ (Ideal.span {a}) * (Ideal.span {b}))]
    [Fintype (A ⧸ Ideal.span {a})]
    [Fintype (A ⧸ Ideal.span {b})]
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1)
    (χa : MulChar (A ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (A ⧸ Ideal.span {b}) ℂ) :
    (∑ x : A ⧸ (Ideal.span {a}) * (Ideal.span {b}),
      χa (Ideal.Quotient.factor
        (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
      χb (Ideal.Quotient.factor
        (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
      traceProdChar ι ψ lam a b ha hb hlam hbase x) =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      gaussSum χa (traceModChar ι ψ lam a ha hlam hbase) *
      gaussSum χb (traceModChar ι ψ lam b hb hlam hbase) := by
  let e := Ideal.quotientMulEquivQuotientProd (Ideal.span {a})
    (Ideal.span {b}) (principal_coprime_of_bezout hbez)
  have h := gauss_sum_ideal_crt (Ideal.span {a}) (Ideal.span {b})
    (principal_coprime_of_bezout hbez) χa χb
    (traceProdChar ι ψ lam a b ha hb hlam hbase)
  rw [leftAddChar_traceProd ι ψ lam hbez ha hb hlam hbase,
      rightAddChar_traceProd ι ψ lam hbez ha hb hlam hbase,
      gauss_shift_bezout_left hbez χa (traceModChar ι ψ lam a ha hlam hbase),
      gauss_shift_bezout_right hbez χb (traceModChar ι ψ lam b hb hlam hbase)] at h
  calc
    _ = (χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
          gaussSum χa (traceModChar ι ψ lam a ha hlam hbase)) *
        (χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
          gaussSum χb (traceModChar ι ψ lam b hb hlam hbase)) := h
    _ = _ := by ring

theorem gauss_sum_trace_crt_of_coprime {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ)
    (a b : A)
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    [Fintype (A ⧸ (Ideal.span {a}) * (Ideal.span {b}))]
    [Fintype (A ⧸ Ideal.span {a})]
    [Fintype (A ⧸ Ideal.span {b})]
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1)
    (χa : MulChar (A ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (A ⧸ Ideal.span {b}) ℂ) :
    (∑ x : A ⧸ (Ideal.span {a}) * (Ideal.span {b}),
      χa (Ideal.Quotient.factor
        (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
      χb (Ideal.Quotient.factor
        (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
      traceProdChar ι ψ lam a b ha hb hlam hbase x) =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      gaussSum χa (traceModChar ι ψ lam a ha hlam hbase) *
      gaussSum χb (traceModChar ι ψ lam b hb hlam hbase) := by
  obtain ⟨u, v, hbez⟩ := bezout_of_principal_coprime hcop
  exact gauss_sum_trace_crt ι ψ lam hbez ha hb hlam hbase χa χb

end IdealGaussCRT

end

end OAI

end


