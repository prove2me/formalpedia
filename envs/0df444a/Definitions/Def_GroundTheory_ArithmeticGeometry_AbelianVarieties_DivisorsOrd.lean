-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
-- name    : GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T11:28:49.396361+00:00
-- url     : https://prove2.me/theorems/b5826075-af3b-43ba-b9bc-7e23cc48dd87
-- title:
--   Divisors Ord
-- statement:
--   Definitions and structural lemmas for Divisors Ord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some


set_option autoImplicit false
namespace GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
section Infinity
omit [Field F] in
theorem two_nsmul_add_le {u v w : WithBot ℕ} (h : u ≤ max v w) (c : WithBot ℕ) :
    2 • u + c ≤ max (2 • v + c) (2 • w + c) := by
  rcases le_total v w with hvw | hvw
  · rw [max_eq_right hvw] at h
    exact le_max_of_le_right (add_le_add (nsmul_le_nsmul_right h 2) le_rfl)
  · rw [max_eq_left hvw] at h
    exact le_max_of_le_left (add_le_add (nsmul_le_nsmul_right h 2) le_rfl)
theorem degree_norm_add_le (a b : W.toAffine.CoordinateRing) :
    (Algebra.norm F[X] (a + b)).degree ≤
      max (Algebra.norm F[X] a).degree (Algebra.norm F[X] b).degree := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq a
  obtain ⟨p', q', rfl⟩ := exists_smul_basis_eq b
  have hs : p • (1 : W.toAffine.CoordinateRing) + q • AdjoinRoot.mk W.toAffine.polynomial X +
      (p' • 1 + q' • AdjoinRoot.mk W.toAffine.polynomial X) =
        (p + p') • 1 + (q + q') • AdjoinRoot.mk W.toAffine.polynomial X := by
    rw [add_smul, add_smul]; abel
  rw [hs, degree_norm_smul_basis, degree_norm_smul_basis, degree_norm_smul_basis]
  have h1 := two_nsmul_add_le (degree_add_le p p') 0
  have h2 := two_nsmul_add_le (degree_add_le q q') 3
  simp only [add_zero] at h1
  exact max_le (h1.trans (max_le_max (le_max_left _ _) (le_max_left _ _)))
    (h2.trans (max_le_max (le_max_right _ _) (le_max_right _ _)))
theorem norm_coordinateRing_ne_zero {a : W.toAffine.CoordinateRing} (ha : a ≠ 0) :
    Algebra.norm F[X] a ≠ 0 :=
  Algebra.norm_ne_zero_iff.mpr ha
noncomputable def valuationInftyCoord : Valuation W.toAffine.CoordinateRing ℤᵐ⁰ where
  toFun a := if a = 0 then 0 else exp ((Algebra.norm F[X] a).natDegree : ℤ)
  map_zero' := if_pos rfl
  map_one' := by simp
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    simp only [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb, map_mul,
      natDegree_mul (norm_coordinateRing_ne_zero W ha) (norm_coordinateRing_ne_zero W hb),
      Nat.cast_add, exp_add]
  map_add_le_max' a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    by_cases hab : a + b = 0
    · simp [hab]
    simp only [if_neg ha, if_neg hb, if_neg hab]
    have hd := degree_norm_add_le W a b
    rw [degree_eq_natDegree (norm_coordinateRing_ne_zero W hab),
      degree_eq_natDegree (norm_coordinateRing_ne_zero W ha),
      degree_eq_natDegree (norm_coordinateRing_ne_zero W hb)] at hd
    rcases le_max_iff.mp hd with h | h
    · exact le_max_of_le_left (exp_le_exp.mpr (by exact_mod_cast WithBot.coe_le_coe.mp h))
    · exact le_max_of_le_right (exp_le_exp.mpr (by exact_mod_cast WithBot.coe_le_coe.mp h))
theorem valuationInftyCoord_apply {a : W.toAffine.CoordinateRing} (ha : a ≠ 0) :
    valuationInftyCoord W a = exp ((Algebra.norm F[X] a).natDegree : ℤ) := if_neg ha
theorem valuationInftyCoord_ne_zero {a : W.toAffine.CoordinateRing} (ha : a ≠ 0) :
    valuationInftyCoord W a ≠ 0 := by
  rw [valuationInftyCoord_apply W ha]; exact exp_ne_zero
noncomputable def valuationInfty : Valuation W.toAffine.FunctionField ℤᵐ⁰ :=
  (valuationInftyCoord W).extendToLocalization (S := W.toAffine.CoordinateRing⁰)
    (fun _ hr => Set.mem_compl (valuationInftyCoord_ne_zero W (nonZeroDivisors.ne_zero hr)))
    W.toAffine.FunctionField
noncomputable def ordInfty (f : W.toAffine.FunctionField) : ℤ :=
  -log (valuationInfty W f)
end Infinity
section Affine
variable [IsAlgClosed F] [W.IsElliptic]
noncomputable def ordAtIdeal (v : HeightOneSpectrum W.toAffine.CoordinateRing)
    (f : W.toAffine.FunctionField) : ℤ :=
  FractionalIdeal.count W.toAffine.FunctionField v
    (FractionalIdeal.spanSingleton W.toAffine.CoordinateRing⁰ f)
noncomputable def valuationPoint : W.toAffine.Point → Valuation W.toAffine.FunctionField ℤᵐ⁰
  | .zero => valuationInfty W
  | .some _ _ h => (heightOneOfNonsingular h).valuation W.toAffine.FunctionField
noncomputable def ordPoint : W.toAffine.Point → W.toAffine.FunctionField → ℤ
  | .zero => ordInfty W
  | .some _ _ h => ordAtIdeal W (heightOneOfNonsingular h)
end Affine
end GroundTheory.Arith.Abelian


