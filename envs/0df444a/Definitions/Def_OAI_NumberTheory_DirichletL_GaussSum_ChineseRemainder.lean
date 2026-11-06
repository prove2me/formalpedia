-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
-- name    : OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:35.417732+00:00
-- url     : https://prove2.me/theorems/782dc1b4-30d9-4d27-8d99-4de32f36b942
-- title:
--   Chinese Remainder
-- statement:
--   Definitions and structural lemmas for Chinese Remainder, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ChineseRemainder.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
set_option autoImplicit false
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
end IdealGaussCRT
end
end OAI


