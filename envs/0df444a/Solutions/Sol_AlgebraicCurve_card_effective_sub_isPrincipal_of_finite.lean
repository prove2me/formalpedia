-- Prove2me | solution 1 for AlgebraicCurve.card_effective_sub_isPrincipal_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/815931ab-3551-5d03-af81-ee51364ed0d0

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_card_effective_sub_isPrincipal_of_finite

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_card_effective_sub_isPrincipal_of_finite.AlgebraicCurve"

open scoped LinearAlgebra.Projectivization

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.ord_inv Divisor Divisor.IsPrincipal HasPrincipalDivisors HasPrincipalDivisors.exists_divisor LSpace ell mem_lSpace_iff_ord ConstantsAreBase finiteDimensional_lSpace"
namespace CardLinearSystemSol
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section DivOf

variable [HasPrincipalDivisors K F]

variable (K) in
open Classical in

noncomputable def divOf (f : F) : Divisor K F :=
  if h : f = 0 then 0 else Classical.choose (HasPrincipalDivisors.exists_divisor (K := K) f h)

theorem divOf_apply {f : F} (hf : f ≠ 0) (v : Place K F) : divOf K f v = v.ord f := by
  rw [divOf, dif_neg hf]
  exact (Classical.choose_spec (HasPrincipalDivisors.exists_divisor (K := K) f hf)).1 v

omit [HasPrincipalDivisors K F] in

theorem ord_algebraMap (v : Place K F) {a : K} (ha : a ≠ 0) : v.ord (algebraMap K F a) = 0 := by
  have hu : IsUnit (algebraMap K v.toValuationSubring a) := (IsUnit.mk0 a ha).map _
  have := v.ord_coe_unit hu.unit
  rwa [IsUnit.unit_spec] at this

theorem divOf_smul {f : F} (hf : f ≠ 0) {a : K} (ha : a ≠ 0) :
    divOf K (a • f) = divOf K f := by
  ext v
  have haf : a • f ≠ 0 := smul_ne_zero ha hf
  rw [divOf_apply haf, divOf_apply hf, Algebra.smul_def,
    v.ord_mul ((map_ne_zero _).mpr ha) hf, ord_algebraMap v ha, zero_add]

theorem divOf_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    divOf K (f * g) = divOf K f + divOf K g := by
  ext v
  simp [divOf_apply hf, divOf_apply hg, divOf_apply (mul_ne_zero hf hg), v.ord_mul hf hg]

theorem divOf_inv (f : F) : divOf K f⁻¹ = -divOf K f := by
  rcases eq_or_ne f 0 with rfl | hf
  · have h0 : divOf K (0 : F) = 0 := by rw [divOf, dif_pos rfl]
    rw [inv_zero, h0, neg_zero]
  · ext v
    simp [divOf_apply hf, divOf_apply (inv_ne_zero hf), Place.ord_inv]

theorem nonneg_divOf_add_iff {f : F} (hf : f ≠ 0) (C : Divisor K F) :
    0 ≤ divOf K f + C ↔ f ∈ LSpace C := by
  rw [mem_lSpace_iff_ord, Finsupp.le_def]
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply, divOf_apply hf]
  constructor
  · intro h
    exact Or.inr fun v => by linarith [h v]
  · intro h v
    have := (h.resolve_left hf) v
    linarith

end DivOf

section LinSys

variable [IsCurveOver K F]

abbrev LinSys (C : Divisor K F) : Type _ :=
  {D : Divisor K F // 0 ≤ D ∧ Divisor.IsPrincipal (D - C)}

noncomputable def toLinSys' (C : Divisor K F) (f : {f : LSpace C // f ≠ 0}) : LinSys C :=
  ⟨divOf K (f.1 : F) + C, by
    have hf : (f.1 : F) ≠ 0 := fun h => f.2 (Subtype.ext h)
    refine ⟨(nonneg_divOf_add_iff hf C).mpr f.1.2, f.1, hf, fun v => ?_⟩
    simp [divOf_apply hf]⟩

theorem toLinSys'_wd (C : Divisor K F) (a b : {f : LSpace C // f ≠ 0}) (t : K)
    (h : (a : LSpace C) = t • (b : LSpace C)) : toLinSys' C a = toLinSys' C b := by
  have hb : ((b : LSpace C) : F) ≠ 0 := fun h0 => b.2 (Subtype.ext h0)
  have ht : t ≠ 0 := by
    rintro rfl
    exact a.2 (by rw [h, zero_smul])
  apply Subtype.ext
  simp only [toLinSys']
  have : ((a : LSpace C) : F) = t • ((b : LSpace C) : F) := by rw [h]; rfl
  rw [this, divOf_smul hb ht]

noncomputable def toLinSys (C : Divisor K F) : ℙ K (LSpace C) → LinSys C :=
  Projectivization.lift (toLinSys' C) (toLinSys'_wd C)

theorem toLinSys_mk (C : Divisor K F) (f : LSpace C) (hf : f ≠ 0) :
    (toLinSys C (Projectivization.mk K f hf) : Divisor K F) = divOf K (f : F) + C := by
  simp [toLinSys, toLinSys']

theorem toLinSys_injective (hC : ConstantsAreBase K F) (C : Divisor K F) :
    Function.Injective (toLinSys C) := by
  intro x y hxy
  induction x using Projectivization.ind with
  | h f hf =>
  induction y using Projectivization.ind with
  | h g hg =>
  have hf' : (f : F) ≠ 0 := fun h0 => hf (Subtype.ext h0)
  have hg' : (g : F) ≠ 0 := fun h0 => hg (Subtype.ext h0)
  have h := congrArg (fun D : LinSys C => (D : Divisor K F)) hxy
  simp only [toLinSys_mk, add_left_inj] at h

  have hquot : divOf K ((f : F) * (g : F)⁻¹) = 0 := by
    rw [divOf_mul hf' (inv_ne_zero hg'), divOf_inv, h, add_neg_cancel]
  have hmem : (f : F) * (g : F)⁻¹ ∈ LSpace (0 : Divisor K F) := by
    rw [← nonneg_divOf_add_iff (mul_ne_zero hf' (inv_ne_zero hg')), hquot, add_zero]
  have hmem' : (f : F) * (g : F)⁻¹ ∈ LinearMap.range (Algebra.linearMap K F) := by
    have hC' : LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) := hC
    rw [← hC']
    exact hmem
  obtain ⟨a, ha⟩ := hmem'
  simp only [Algebra.linearMap_apply] at ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact mul_ne_zero hf' (inv_ne_zero hg') ha.symm
  rw [Projectivization.mk_eq_mk_iff]
  refine ⟨Units.mk0 a ha0, Subtype.ext ?_⟩
  show ((Units.mk0 a ha0 • g : LSpace C) : F) = f
  rw [Units.smul_def, Units.val_mk0, Submodule.coe_smul, Algebra.smul_def, ha,
    inv_mul_cancel_right₀ hg']

theorem toLinSys_surjective (C : Divisor K F) : Function.Surjective (toLinSys C) := by
  rintro ⟨D, hD0, f, hf, hfD⟩
  have hdiv : divOf K f = D - C := Finsupp.ext fun v => by rw [divOf_apply hf, hfD v]
  have hmem : f ∈ LSpace C := by
    rw [← nonneg_divOf_add_iff hf C, hdiv, sub_add_cancel]
    exact hD0
  have hne : (⟨f, hmem⟩ : LSpace C) ≠ 0 := fun h0 => hf (congrArg Subtype.val h0)
  refine ⟨Projectivization.mk K ⟨f, hmem⟩ hne, Subtype.ext ?_⟩
  rw [toLinSys_mk]
  simp [hdiv]

theorem main [Finite K] (hC : ConstantsAreBase K F) (C : Divisor K F) :
    (Nat.card K - 1) * Nat.card (LinSys C) + 1 = Nat.card K ^ ell C := by

  haveI : FiniteDimensional K (LSpace (0 : Divisor K F)) := by
    have hC' : LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) := hC
    rw [hC']
    infer_instance
  haveI : FiniteDimensional K (LSpace C) := finiteDimensional_lSpace C
  haveI : Finite (LSpace C) := Module.finite_of_finite K
  have hcard : Nat.card (ℙ K (LSpace C)) = Nat.card (LinSys C) :=
    Nat.card_eq_of_bijective _ ⟨toLinSys_injective hC C, toLinSys_surjective C⟩
  have h1 := Projectivization.card' K (LSpace C)
  have h2 : Nat.card (LSpace C) = Nat.card K ^ ell C := Module.natCard_eq_pow_finrank
  rw [← h2, h1, hcard, mul_comm]

end LinSys

end AlgebraicCurve.CardLinearSystemSol

theorem solution
    (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [AlgebraicCurve.IsCurveOver k F]
    (hC : AlgebraicCurve.ConstantsAreBase k F) (C : AlgebraicCurve.Divisor k F) :
    (Nat.card k - 1) *
        Nat.card {D : AlgebraicCurve.Divisor k F //
          0 ≤ D ∧ AlgebraicCurve.Divisor.IsPrincipal (D - C)} + 1 =
      Nat.card k ^ AlgebraicCurve.ell C :=
  AlgebraicCurve.CardLinearSystemSol.main hC C

end S_AlgebraicCurve_card_effective_sub_isPrincipal_of_finite
end P2MW
export P2MW.S_AlgebraicCurve_card_effective_sub_isPrincipal_of_finite (solution)
