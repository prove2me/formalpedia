-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_SmKerSurj
-- name    : ReciprocityTheory_DualLattices_SmKerSurj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:58.971025+00:00
-- url     : https://prove2.me/theorems/aba59693-b496-424c-9d1b-93c6a98863cd
-- title:
--   Sm Ker Surj
-- statement:
--   Definitions and structural lemmas for Sm Ker Surj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SmKerSurj.lean

import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
namespace ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
section
variable {R' R : LAlg R₀} (π : LHom R' R) (ξ : (R' : Type u)) (hsurj : Function.Surjective π.1)
def ell (r : (R : Type u)) : (R' : Type u) := Function.surjInv hsurj r * ξ
end
section
variable {R' R : LAlg R₀} {π : LHom R' R} {ξ : (R' : Type u)}
  (hsurj : Function.Surjective π.1) (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0)
include hker in
lemma π_ξ : π.1 ξ = 0 := by
  have h : ξ ∈ RingHom.ker π.1 := by
    rw [hker]
    exact Ideal.mem_span_singleton_self ξ
  exact (RingHom.mem_ker).1 h
include hker hsq in
lemma ell_spec (a : (R' : Type u)) : ell π ξ hsurj (π.1 a) = a * ξ := by
  have h1 : π.1 (Function.surjInv hsurj (π.1 a)) = π.1 a := Function.surjInv_eq hsurj _
  have h2 : Function.surjInv hsurj (π.1 a) - a ∈ Ideal.span {ξ} := by
    rw [← hker, RingHom.mem_ker, map_sub, h1, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h2
  show Function.surjInv hsurj (π.1 a) * ξ = a * ξ
  have e : Function.surjInv hsurj (π.1 a) = a + c * ξ := by
    rw [hc]
    ring
  rw [e, add_mul, mul_assoc, hsq, mul_zero, add_zero]
include hker in
lemma ell_π (r : (R : Type u)) : π.1 (ell π ξ hsurj r) = 0 := by
  show π.1 (Function.surjInv hsurj r * ξ) = 0
  rw [map_mul, π_ξ hker, mul_zero]
include hker hsq in
lemma ell_add (r r' : (R : Type u)) :
    ell π ξ hsurj (r + r') = ell π ξ hsurj r + ell π ξ hsurj r' := by
  obtain ⟨a, rfl⟩ := hsurj r
  obtain ⟨a', rfl⟩ := hsurj r'
  rw [← map_add, ell_spec hsurj hker hsq, ell_spec hsurj hker hsq, ell_spec hsurj hker hsq, add_mul]
include hker hsq in
lemma ell_mul (a : (R' : Type u)) (r : (R : Type u)) :
    ell π ξ hsurj (π.1 a * r) = a * ell π ξ hsurj r := by
  obtain ⟨b, rfl⟩ := hsurj r
  rw [← map_mul, ell_spec hsurj hker hsq, ell_spec hsurj hker hsq, mul_assoc]
include hker hsq in
lemma ell_zero : ell π ξ hsurj 0 = 0 := by
  have h := ell_spec hsurj hker hsq 0
  rw [map_zero, zero_mul] at h
  exact h
include hker hsq in
lemma ell_mul_ell (r r' : (R : Type u)) : ell π ξ hsurj r * ell π ξ hsurj r' = 0 := by
  obtain ⟨a, rfl⟩ := hsurj r
  obtain ⟨b, rfl⟩ := hsurj r'
  rw [ell_spec hsurj hker hsq, ell_spec hsurj hker hsq]
  calc a * ξ * (b * ξ) = a * b * (ξ * ξ) := by ring
    _ = 0 := by rw [hsq, mul_zero]
end
section
variable {R' R : LAlg R₀} (π : LHom R' R) (Dp : DualPair R) (ξ : (R' : Type u))
  (hsurj : Function.Surjective π.1) (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0)
def smAlg : (FP π Dp.π : Type u) →ₐ[R₀] (R' : Type u) where
  toFun x := x.1.1 + ell π ξ hsurj (Dp.κ x.1.2)
  map_one' := by
    show (1 : (R' : Type u)) + ell π ξ hsurj (Dp.κ 1) = 1
    rw [Dp.κ_one, ell_zero hsurj hker hsq, add_zero]
  map_mul' x y := by
    show x.1.1 * y.1.1 + ell π ξ hsurj (Dp.κ (x.1.2 * y.1.2)) =
      (x.1.1 + ell π ξ hsurj (Dp.κ x.1.2)) * (y.1.1 + ell π ξ hsurj (Dp.κ y.1.2))
    rw [Dp.κ_mul, ← FP.mem π Dp.π x, ← FP.mem π Dp.π y, ell_add hsurj hker hsq,
      ell_mul hsurj hker hsq, ell_mul hsurj hker hsq]
    linear_combination (-1 : (R' : Type u)) *
      ell_mul_ell hsurj hker hsq (Dp.κ x.1.2) (Dp.κ y.1.2)
  map_zero' := by
    show (0 : (R' : Type u)) + ell π ξ hsurj (Dp.κ 0) = 0
    rw [Dp.κ_zero, ell_zero hsurj hker hsq, add_zero]
  map_add' x y := by
    show (x.1.1 + y.1.1) + ell π ξ hsurj (Dp.κ (x.1.2 + y.1.2)) =
      (x.1.1 + ell π ξ hsurj (Dp.κ x.1.2)) + (y.1.1 + ell π ξ hsurj (Dp.κ y.1.2))
    rw [Dp.κ_add, ell_add hsurj hker hsq]; ring
  commutes' c := by
    show algebraMap R₀ (R' : Type u) c + ell π ξ hsurj (Dp.κ (algebraMap R₀ (Dp.D : Type u) c)) =
      algebraMap R₀ (R' : Type u) c
    rw [Dp.κ_algebraMap, ell_zero hsurj hker hsq, add_zero]
def sm : LHom (FP π Dp.π) R' :=
  ⟨smAlg π Dp ξ hsurj hker hsq, ⟨fun x hx => fp_isUnit π Dp.π x (π.2.map_nonunit _ (by
    convert hx.map π.1 using 1
    show _ = π.1 (x.1.1 + ell π ξ hsurj (Dp.κ x.1.2))
    rw [map_add, ell_π hsurj hker, add_zero]; rfl))⟩⟩
end
section
variable {R' R : LAlg R₀} (π : LHom R' R) (Dp : DualPair R)
def ι₁ : LHom R' (FP π Dp.π) :=
  FP.lift π Dp.π (LHom.id R') (Dp.σ.comp π) (fun t => (Dp.sect (π.1 t)).symm)
variable {ξ : (R' : Type u)} (hsurj : Function.Surjective π.1)
  (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0)
lemma sm_ker : ∀ a ∈ (FP.p₁ π Dp.π).ker, (sm π Dp ξ hsurj hker hsq).1.toLinearMap a ∈ π.ker := by
  intro a ha
  have ha0 : a.1.1 = 0 := ha
  show π.1 (a.1.1 + ell π ξ hsurj (Dp.κ a.1.2)) = 0
  rw [map_add, ell_π hsurj hker, ha0, map_zero, add_zero]
end
end ReciprocityTheory.PGsh


