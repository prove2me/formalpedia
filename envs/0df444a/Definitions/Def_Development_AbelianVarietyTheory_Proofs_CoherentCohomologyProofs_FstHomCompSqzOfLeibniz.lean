-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FstHomCompSqzOfLeibniz
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FstHomCompSqzOfLeibniz
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:41.471961+00:00
-- url     : https://prove2.me/theorems/066aac08-c3ef-493a-afd4-2564654269ea
-- title:
--   Fst Hom Comp Sqz Of Leibniz
-- statement:
--   Definitions and structural lemmas for Fst Hom Comp Sqz Of Leibniz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FstHomCompSqzOfLeibniz.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.SquareZeroLeibnizPoint
open TrivSqZeroExt
section PointsOfDual
variable {O C : Type*} [CommRing O] [CommRing C] {ι : Type*} [Fintype ι]
def sqzPoint (φ : O →+* C) (n : ι → C) (hn : ∀ a b, n a * n b = 0) :
    TrivSqZeroExt O (ι → O) →+* C where
  toFun x := φ x.fst + ∑ i, φ (x.snd i) * n i
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by
    simp only [fst_add, snd_add, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
    ring
  map_mul' x y := by
    have hcross : (∑ i, φ (x.snd i) * n i) * (∑ j, φ (y.snd j) * n j) = 0 := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      calc φ (x.snd i) * n i * (φ (y.snd j) * n j)
          = φ (x.snd i) * φ (y.snd j) * (n i * n j) := by ring
        _ = 0 := by rw [hn, mul_zero]
    have hs : ∀ i, (x * y).snd i = x.fst * y.snd i + x.snd i * y.fst := fun i => by
      rw [snd_mul]; rfl
    have h1 : ∑ i, φ ((x * y).snd i) * n i
        = φ x.fst * ∑ i, φ (y.snd i) * n i + φ y.fst * ∑ i, φ (x.snd i) * n i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hs, map_add, map_mul, map_mul]; ring
    rw [h1, fst_mul, map_mul]
    linear_combination (-1 : C) * hcross
theorem sqzPoint_apply (φ : O →+* C) (n : ι → C) (hn : ∀ a b, n a * n b = 0)
    (x : TrivSqZeroExt O (ι → O)) :
    sqzPoint φ n hn x = φ x.fst + ∑ i, φ (x.snd i) * n i := rfl
@[simp] theorem sqzPoint_inl (φ : O →+* C) (n : ι → C) (hn : ∀ a b, n a * n b = 0) (a : O) :
    sqzPoint φ n hn (inl a) = φ a := by
  rw [sqzPoint_apply]
  simp
@[simp] theorem sqzPoint_inr (φ : O →+* C) (n : ι → C) (hn : ∀ a b, n a * n b = 0) (v : ι → O) :
    sqzPoint φ n hn (inr v) = ∑ i, φ (v i) * n i := by
  rw [sqzPoint_apply]
  simp
end PointsOfDual
section Leibniz
variable {A O M : Type*} [CommRing A] [CommRing O] [AddCommGroup M] [Module O M]
theorem leibniz_map_one (ε : A →+* O) (d : A →+ M)
    (hd : ∀ f f', d (f * f') = ε f • d f' + ε f' • d f) : d 1 = 0 := by
  have h := hd 1 1
  simpa using h
variable [Module Oᵐᵒᵖ M] [IsCentralScalar O M]
def sqzOfLeibniz (ε : A →+* O) (d : A →+ M)
    (hd : ∀ f f', d (f * f') = ε f • d f' + ε f' • d f) : A →+* TrivSqZeroExt O M where
  toFun f := (ε f, d f)
  map_one' := TrivSqZeroExt.ext (map_one ε) (leibniz_map_one ε d hd)
  map_zero' := TrivSqZeroExt.ext (map_zero ε) (map_zero d)
  map_add' f f' := TrivSqZeroExt.ext (map_add ε f f') (map_add d f f')
  map_mul' f f' := TrivSqZeroExt.ext (map_mul ε f f') (by
    change d (f * f') = ε f • d f' + MulOpposite.op (ε f') • d f
    rw [op_smul_eq_smul]
    exact hd f f')
end Leibniz
end GlobalTheory.SquareZeroLeibnizPoint


