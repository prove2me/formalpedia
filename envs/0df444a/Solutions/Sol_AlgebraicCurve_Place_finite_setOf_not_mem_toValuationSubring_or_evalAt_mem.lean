-- Prove2me | solution 1 for AlgebraicCurve.Place.finite_setOf_not_mem_toValuationSubring_or_evalAt_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/dba3f181-842a-5834-9d59-038cad96bffa

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_finite_setOf_not_mem_toValuationSubring_or_evalAt_mem

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_finite_setOf_not_mem_toValuationSubring_or_evalAt_mem.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord HasPrincipalDivisors HasPrincipalDivisors.exists_divisor"
namespace Place
p2m_export "AlgebraicCurve.Place" "IsRational evalAt algebraMap_evalAt ResidueField adicValuation adicValuation_ne_zero adicValuation_coe_eq_one_iff ord ord_inv algebraMap_mem' toValuationSubring"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem _root_.AlgebraicCurve.Place.fov_ord_coe_eq_zero_iff (v : Place K F) (a : v.toValuationSubring) (ha : (a : F) ≠ 0) :
    v.ord (a : F) = 0 ↔ IsUnit a := by
  rw [← v.adicValuation_coe_eq_one_iff]
  have hne : v.adicValuation (a : F) ≠ 0 := v.adicValuation_ne_zero ha
  constructor
  · intro h
    have h' : WithZero.log (v.adicValuation (a : F)) = 0 := by
      have := h; simp only [Place.ord, neg_eq_zero] at this; exact this
    rw [← WithZero.exp_log hne, h', WithZero.exp_zero]
  · intro h
    simp only [Place.ord, h, WithZero.log_one, neg_zero]

p2m_export "AlgebraicCurve.Place" "fov_ord_coe_eq_zero_iff"

private theorem _root_.AlgebraicCurve.Place.fov_ord_ne_zero_of_not_mem (v : Place K F) {x : F} (hx : x ∉ v.toValuationSubring) : v.ord x ≠ 0 := by
  have hx0 : x ≠ 0 := fun h => hx (h ▸ zero_mem _)
  have hinv : x⁻¹ ∈ v.toValuationSubring := by
    rcases v.toValuationSubring.mem_or_inv_mem x with h | h
    · exact absurd h hx
    · exact h
  have hnu : ¬ IsUnit (⟨x⁻¹, hinv⟩ : v.toValuationSubring) := by
    rintro ⟨u, hu⟩
    apply hx
    have h1 : ((u : v.toValuationSubring) : F) * (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = 1 := by
      rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
    rw [hu] at h1
    have hval : (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = x := by
      calc (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F)
          = x * (x⁻¹ * (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F)) := by
            rw [← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
        _ = x := by rw [show (x⁻¹ : F) * _ = 1 from h1, mul_one]
    rw [← hval]; exact SetLike.coe_mem _
  intro h0
  have h1 : v.ord x⁻¹ = 0 := by rw [v.ord_inv, h0, neg_zero]
  exact hnu ((v.fov_ord_coe_eq_zero_iff ⟨x⁻¹, hinv⟩ (inv_ne_zero hx0)).mp h1)

p2m_export "AlgebraicCurve.Place" "fov_ord_ne_zero_of_not_mem"

private theorem _root_.AlgebraicCurve.Place.fov_ord_sub_ne_zero_of_evalAt_eq (v : Place K F) (hv : v.IsRational) {x : F}
    (hx : x ∉ Set.range (algebraMap K F)) (hmem : x ∈ v.toValuationSubring) {t : K} (ht : v.evalAt x = t) :
    v.ord (x - algebraMap K F t) ≠ 0 := by
  have htmem : algebraMap K F t ∈ v.toValuationSubring := v.algebraMap_mem' t
  have hsub : x - algebraMap K F t ∈ v.toValuationSubring := sub_mem hmem htmem
  have hne : x - algebraMap K F t ≠ 0 := fun h => hx ⟨t, (sub_eq_zero.mp h).symm⟩
  intro h0
  have hunit := (v.fov_ord_coe_eq_zero_iff ⟨_, hsub⟩ hne).mp h0

  have hres : IsLocalRing.residue v.toValuationSubring (⟨_, hsub⟩ : v.toValuationSubring) = 0 := by
    have e1 : (⟨_, hsub⟩ : v.toValuationSubring) = ⟨x, hmem⟩ - ⟨algebraMap K F t, htmem⟩ := rfl
    have e2 : (⟨algebraMap K F t, htmem⟩ : v.toValuationSubring) = algebraMap K v.toValuationSubring t := rfl
    rw [e1, map_sub, ← v.algebraMap_evalAt hv hmem, ht, e2]
    show algebraMap K v.ResidueField t - algebraMap v.toValuationSubring v.ResidueField (algebraMap K v.toValuationSubring t) = 0
    rw [← IsScalarTower.algebraMap_apply, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff] at hres
  exact (IsLocalRing.mem_maximalIdeal _).mp hres hunit

p2m_export "AlgebraicCurve.Place" "fov_ord_sub_ne_zero_of_evalAt_eq"
end AlgebraicCurve.Place

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (hrat : ∀ v : Place K F, v.IsRational)
    (x : F) (hx : x ∉ Set.range (algebraMap K F)) (T : Finset K) :
    {v : Place K F | x ∉ v.toValuationSubring ∨ v.evalAt x ∈ (T : Set K)}.Finite := by
  classical
  have hx0 : x ≠ 0 := fun h => hx ⟨0, by rw [map_zero, h]⟩

  have hfin : ∀ f : F, f ≠ 0 → {v : Place K F | v.ord f ≠ 0}.Finite := by
    intro f hf
    obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
    refine D.finite_support.subset ?_
    intro v hv
    rw [Function.mem_support, hD]
    exact hv
  refine ((hfin x hx0).union (T.finite_toSet.biUnion fun t _ => hfin (x - algebraMap K F t)
    (fun h => hx ⟨t, (sub_eq_zero.mp h).symm⟩))).subset ?_
  rintro v (hv | hv)
  · exact Or.inl (v.fov_ord_ne_zero_of_not_mem hv)
  · by_cases hmem : x ∈ v.toValuationSubring
    · refine Or.inr (Set.mem_biUnion (Finset.mem_coe.mpr hv) ?_)
      exact v.fov_ord_sub_ne_zero_of_evalAt_eq (hrat v) hx hmem rfl
    · exact Or.inl (v.fov_ord_ne_zero_of_not_mem hmem)

end S_AlgebraicCurve_Place_finite_setOf_not_mem_toValuationSubring_or_evalAt_mem
end P2MW
export P2MW.S_AlgebraicCurve_Place_finite_setOf_not_mem_toValuationSubring_or_evalAt_mem (solution)
