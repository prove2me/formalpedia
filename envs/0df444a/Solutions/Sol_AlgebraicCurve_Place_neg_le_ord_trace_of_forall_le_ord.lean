-- Prove2me | solution 1 for AlgebraicCurve.Place.neg_le_ord_trace_of_forall_le_ord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/aff71108-13f1-569e-beb2-89dd79e61dd2

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_traceIntegralAlong_of_separableAlong
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_neg_le_ord_trace_of_forall_le_ord
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_neg_le_ord_trace_of_forall_le_ord.AlgebraicCurve ModularCurve KaehlerDifferential"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.mem_iff_ord_nonneg IsCurveOver Place Place.ord_zero algebraAlong isScalarTower_along FiniteAlong Place.ramificationIndexAlong Place.ord_restrictAlong SeparableAlong traceFunAlong traceFunAlong_apply TraceIntegralAlong traceIntegralAlong_of_separableAlong"
namespace TraceFloor
p2m_open "AlgebraicCurve"

variable {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']

theorem exists_ord_eq_one (x : Place k F) : ∃ π : F, x.ord π = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible x.toValuationSubring
  exact ⟨(π : F), x.ord_coe_irreducible hπ⟩

theorem ord_nonneg_of_mem' (v : Place k F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  by_cases h0 : f = 0
  · rw [h0, Place.ord_zero]
  · exact (Place.mem_iff_ord_nonneg v h0).mp hf

theorem ord_pow' (v : Place k F) (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  have := v.ord_zpow f (n : ℤ)
  rwa [zpow_natCast] at this

theorem main (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong k φ)
    (hsep : SeparableAlong k φ)
    (x : Place k F) (S : Finset (Place k F')) (hS : ∀ y : Place k F', y ∈ S ↔ y.restrictAlong φ hφ = x)
    (a : ℤ) (ha : 0 ≤ a) (g : F')
    (hg : ∀ y ∈ S, -((Place.ramificationIndexAlong φ y : ℤ) * a) ≤ y.ord g) :
    letI := AlgebraicCurve.algebraAlong φ;
    -a ≤ x.ord (Algebra.trace F F' g) := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI := isScalarTower_along φ
  show -a ≤ x.ord (Algebra.trace F F' g)

  by_cases hT0 : Algebra.trace F F' g = 0
  · rw [hT0, Place.ord_zero]; linarith
  have hg0 : g ≠ 0 := by
    intro h; apply hT0; rw [h, map_zero]

  obtain ⟨π, hπ⟩ := exists_ord_eq_one x
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hπ; exact zero_ne_one hπ
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha

  set u : F' := φ (π ^ n) * g with hu
  have hφπ : φ (π ^ n) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero _ ((map_ne_zero φ).mpr hπ0)
  have hu0 : u ≠ 0 := mul_ne_zero hφπ hg0
  have hint : ∀ y : Place k F', y.restrictAlong φ hφ = x → u ∈ y.toValuationSubring := by
    intro y hy
    have hyS : y ∈ S := (hS y).mpr hy
    apply (Place.mem_iff_ord_nonneg y hu0).mpr
    rw [hu, y.ord_mul hφπ hg0, Place.ord_restrictAlong φ hφ y (π ^ n), hy, ord_pow', hπ, mul_one]
    have := hg y hyS
    push_cast at this ⊢
    linarith

  have htr : traceFunAlong φ u ∈ x.toValuationSubring :=
    AlgebraicCurve.traceIntegralAlong_of_separableAlong φ hφ hfin hsep x u hint
  rw [traceFunAlong_apply] at htr

  have hTu : Algebra.trace F F' u = π ^ n * Algebra.trace F F' g := by
    have e1 : u = (π ^ n) • g := by rw [hu, Algebra.smul_def]; rfl
    rw [e1, map_smul, smul_eq_mul]
  rw [hTu] at htr
  have h0 := ord_nonneg_of_mem' x htr
  rw [x.ord_mul (pow_ne_zero _ hπ0) hT0, ord_pow', hπ, mul_one] at h0
  linarith

end AlgebraicCurve.TraceFloor

theorem solution
    {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F'] [IsAlgClosed k]
    [IsCurveOver k F] [IsCurveOver k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong k φ) (hsep : SeparableAlong k φ)
    (x : Place k F) (S : Finset (Place k F')) (hS : ∀ y : Place k F', y ∈ S ↔ y.restrictAlong φ hφ = x)
    (a : ℤ) (ha : 0 ≤ a) (g : F') (hg : ∀ y ∈ S, -((Place.ramificationIndexAlong φ y : ℤ) * a) ≤ y.ord g) :
    letI := AlgebraicCurve.algebraAlong φ;
    -a ≤ x.ord (Algebra.trace F F' g) :=
  AlgebraicCurve.TraceFloor.main φ hφ hfin hsep x S hS a ha g hg

end S_AlgebraicCurve_Place_neg_le_ord_trace_of_forall_le_ord
end P2MW
export P2MW.S_AlgebraicCurve_Place_neg_le_ord_trace_of_forall_le_ord (solution)
