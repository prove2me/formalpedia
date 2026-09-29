-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_sub_algebraMap_evalAt_eq_mul_of_derivative_evalEval_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/bf79a06d-f867-5c3c-9657-f0fae35d9515

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_sub_algebraMap_evalAt_eq_mul_of_derivative_evalEval_ne_zero

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_sub_algebraMap_evalAt_eq_mul_of_derivative_evalEval_ne_zero.AlgebraicCurve Polynomial IsLocalRing"
open scoped Polynomial.Bivariate

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
namespace Place
p2m_export "AlgebraicCurve.Place" "IsRational algebraMap_residueField_injective evalAt algebraMap_evalAt ext coe_algebraMap ResidueField toValuationSubring evalAt_algebraMap_eq"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem g2p_algebraMap_comp :
    (algebraMap v.toValuationSubring F).comp (algebraMap K v.toValuationSubring) = algebraMap K F :=
  (IsScalarTower.algebraMap_eq K v.toValuationSubring F).symm

private theorem _root_.AlgebraicCurve.Place.g2p_hom_evalEval {S : Type*} [CommRing S] (φ : v.toValuationSubring →+* S)
    (P : K[X][Y]) (a b : v.toValuationSubring) :
    φ ((P.map (mapRingHom (algebraMap K v.toValuationSubring))).evalEval a b)
      = (P.map (mapRingHom (φ.comp (algebraMap K v.toValuationSubring)))).evalEval (φ a) (φ b) := by
  rw [← map_mapRingHom_evalEval φ, Polynomial.map_map, mapRingHom_comp]

p2m_export "AlgebraicCurve.Place" "g2p_hom_evalEval"
private theorem _root_.AlgebraicCurve.Place.g2p_hom_eval {S : Type*} [CommRing S] (φ : v.toValuationSubring →+* S)
    (p : K[X]) (a : v.toValuationSubring) :
    φ ((p.map (algebraMap K v.toValuationSubring)).eval a)
      = (p.map (φ.comp (algebraMap K v.toValuationSubring))).eval (φ a) := by
  rw [eval_map, eval_map, hom_eval₂]

p2m_export "AlgebraicCurve.Place" "g2p_hom_eval"
private theorem _root_.AlgebraicCurve.Place.g2p_coe_evalEval (P : K[X][Y]) (a b : v.toValuationSubring) :
    (((P.map (mapRingHom (algebraMap K v.toValuationSubring))).evalEval a b : v.toValuationSubring) : F)
      = (P.map (mapRingHom (algebraMap K F))).evalEval (a : F) (b : F) := by
  have h := v.g2p_hom_evalEval (algebraMap v.toValuationSubring F) P a b
  rw [g2p_algebraMap_comp] at h
  exact h

p2m_export "AlgebraicCurve.Place" "g2p_coe_evalEval"
private theorem _root_.AlgebraicCurve.Place.g2p_coe_eval (p : K[X]) (a : v.toValuationSubring) :
    (((p.map (algebraMap K v.toValuationSubring)).eval a : v.toValuationSubring) : F)
      = (p.map (algebraMap K F)).eval (a : F) := by
  have h := v.g2p_hom_eval (algebraMap v.toValuationSubring F) p a
  rw [g2p_algebraMap_comp] at h
  exact h

p2m_export "AlgebraicCurve.Place" "g2p_coe_eval"
private theorem _root_.AlgebraicCurve.Place.g2p_evalEval_mem (P : K[X][Y]) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring) :
    (P.map (mapRingHom (algebraMap K F))).evalEval z y ∈ v.toValuationSubring := by
  rw [← v.g2p_coe_evalEval P ⟨z, hz⟩ ⟨y, hy⟩]
  exact SetLike.coe_mem _

p2m_export "AlgebraicCurve.Place" "g2p_evalEval_mem"
theorem g2p_eval_mem (p : K[X]) {z : F} (hz : z ∈ v.toValuationSubring) :
    (p.map (algebraMap K F)).eval z ∈ v.toValuationSubring := by
  rw [← v.g2p_coe_eval p ⟨z, hz⟩]
  exact SetLike.coe_mem _

theorem g2p_algebraMap_residueField (c : K) :
    algebraMap K v.ResidueField c
      = residue v.toValuationSubring (algebraMap K v.toValuationSubring c) := by
  rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField c,
    ResidueField.algebraMap_eq]

private theorem _root_.AlgebraicCurve.Place.g2p_residue_mk (hv : v.IsRational) (a : v.toValuationSubring) :
    residue v.toValuationSubring a = algebraMap K v.ResidueField (v.evalAt (a : F)) := by
  rw [v.algebraMap_evalAt hv a.2]

p2m_export "AlgebraicCurve.Place" "g2p_residue_mk"

private theorem _root_.AlgebraicCurve.Place.g2p_evalAt_evalEval (hv : v.IsRational) (P : K[X][Y]) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring) :
    v.evalAt ((P.map (mapRingHom (algebraMap K F))).evalEval z y)
      = P.evalEval (v.evalAt z) (v.evalAt y) := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (v.g2p_evalEval_mem P hz hy)]
  have hmk : (⟨(P.map (mapRingHom (algebraMap K F))).evalEval z y, v.g2p_evalEval_mem P hz hy⟩
        : v.toValuationSubring)
      = (P.map (mapRingHom (algebraMap K v.toValuationSubring))).evalEval ⟨z, hz⟩ ⟨y, hy⟩ :=
    Subtype.ext (by rw [g2p_coe_evalEval])
  rw [hmk, ← ResidueField.algebraMap_eq, g2p_hom_evalEval,
    ← IsScalarTower.algebraMap_eq K v.toValuationSubring v.ResidueField,
    ResidueField.algebraMap_eq, v.g2p_residue_mk hv, v.g2p_residue_mk hv,
    map_mapRingHom_evalEval]

p2m_export "AlgebraicCurve.Place" "g2p_evalAt_evalEval"
theorem g2p_evalAt_eval (hv : v.IsRational) (p : K[X]) {z : F} (hz : z ∈ v.toValuationSubring) :
    v.evalAt ((p.map (algebraMap K F)).eval z) = p.eval (v.evalAt z) := by
  have h := v.g2p_evalAt_evalEval hv (C p) hz hz
  rwa [Polynomial.map_C, evalEval_C, evalEval_C] at h

private theorem _root_.AlgebraicCurve.Place.g2p_sub_mem_maximalIdeal (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    (⟨f, hf⟩ - algebraMap K v.toValuationSubring (v.evalAt f) : v.toValuationSubring)
      ∈ maximalIdeal v.toValuationSubring := by
  rw [← residue_eq_zero_iff, map_sub, ← g2p_algebraMap_residueField, v.g2p_residue_mk hv, sub_self]

p2m_export "AlgebraicCurve.Place" "g2p_sub_mem_maximalIdeal"

theorem g2p_isUnit_add_of_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (ha : IsUnit a) (hb : b ∈ maximalIdeal R) : IsUnit (a + b) := by
  by_contra h
  have hab : a + b ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
  have ha' : a ∈ maximalIdeal R := by simpa using sub_mem hab hb
  exact (IsLocalRing.mem_maximalIdeal _).mp ha' ha

end AlgebraicCurve.Place

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_sub_algebraMap_evalAt_eq_mul_of_derivative_evalEval_ne_zero.AlgebraicCurve AlgebraicCurve.Place P2MW.S_AlgebraicCurve_Place_exists_sub_algebraMap_evalAt_eq_mul_of_derivative_evalEval_ne_zero.AlgebraicCurve.Place Polynomial Polynomial.Bivariate.Polynomial IsLocalRing"

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring)
    (G : Polynomial (Polynomial K))
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0)
    (hsep : (Polynomial.derivative G).evalEval (v.evalAt z) (v.evalAt y) ≠ 0) :
    ∃ h ∈ v.toValuationSubring,
      y - algebraMap K F (v.evalAt y) = h * (z - algebraMap K F (v.evalAt z)) := by

  set zO : v.toValuationSubring := ⟨z, hz⟩ with hzO
  set yO : v.toValuationSubring := ⟨y, hy⟩ with hyO
  set z0 : v.toValuationSubring := algebraMap K v.toValuationSubring (v.evalAt z) with hz0
  set y0 : v.toValuationSubring := algebraMap K v.toValuationSubring (v.evalAt y) with hy0
  set GO : (v.toValuationSubring)[X][Y] := G.map (mapRingHom (algebraMap K v.toValuationSubring))
    with hGO

  have h1 : GO.evalEval zO yO = 0 := by
    rw [← ZeroMemClass.coe_eq_zero, hGO, g2p_coe_evalEval]
    exact hG

  have h2 : zO - z0 ∣ GO.evalEval zO yO - GO.evalEval z0 yO := by
    unfold Polynomial.evalEval
    exact sub_dvd_eval_sub _ _ _
  obtain ⟨a, ha⟩ := h2
  rw [h1, zero_sub] at ha

  set p : (v.toValuationSubring)[X] := GO.map (evalRingHom z0) with hp
  have hpev : ∀ t, p.eval t = GO.evalEval z0 t := fun t => map_evalRingHom_eval z0 t GO

  have hG0 : G.evalEval (v.evalAt z) (v.evalAt y) = 0 := by
    rw [← v.g2p_evalAt_evalEval hv G hz hy, hG]
    simpa using v.evalAt_algebraMap_eq (0 : K)
  have hp0 : p.eval y0 = 0 := by
    rw [hpev, hz0, hy0, hGO, map_mapRingHom_evalEval, hG0, map_zero]
  have hp1 : p.derivative.eval y0
      = algebraMap K v.toValuationSubring
          ((Polynomial.derivative G).evalEval (v.evalAt z) (v.evalAt y)) := by
    rw [hp, derivative_map, map_evalRingHom_eval, hGO, derivative_map, hz0, hy0,
      map_mapRingHom_evalEval]

  obtain ⟨k, hk⟩ := binomExpansion p y0 (yO - y0)
  rw [add_sub_cancel, hp0, zero_add, hp1, hpev] at hk

  have hu : IsUnit (algebraMap K v.toValuationSubring
      ((Polynomial.derivative G).evalEval (v.evalAt z) (v.evalAt y)) + k * (yO - y0)) :=
    g2p_isUnit_add_of_mem_maximalIdeal ((isUnit_iff_ne_zero.mpr hsep).map _)
      (Ideal.mul_mem_left _ _ (by simpa [hyO, hy0] using v.g2p_sub_mem_maximalIdeal hv hy))
  have hmain : (yO - y0) * (algebraMap K v.toValuationSubring
      ((Polynomial.derivative G).evalEval (v.evalAt z) (v.evalAt y)) + k * (yO - y0))
      = (zO - z0) * (-a) := by
    rw [mul_neg, ← ha, hk]
    ring
  have hsol : yO - y0 = ((-a) * ↑(hu.unit⁻¹)) * (zO - z0) := by
    calc yO - y0 = (yO - y0) * (algebraMap K v.toValuationSubring
          ((Polynomial.derivative G).evalEval (v.evalAt z) (v.evalAt y)) + k * (yO - y0))
          * ↑(hu.unit⁻¹) := by rw [mul_assoc, hu.mul_val_inv, mul_one]
      _ = ((-a) * ↑(hu.unit⁻¹)) * (zO - z0) := by rw [hmain]; ring
  refine ⟨(((-a) * ↑(hu.unit⁻¹) : v.toValuationSubring) : F), SetLike.coe_mem _, ?_⟩
  have hF := congrArg (fun t : v.toValuationSubring => (t : F)) hsol
  simpa [hyO, hzO, hy0, hz0, v.coe_algebraMap] using hF

#print axioms solution

end S_AlgebraicCurve_Place_exists_sub_algebraMap_evalAt_eq_mul_of_derivative_evalEval_ne_zero
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_sub_algebraMap_evalAt_eq_mul_of_derivative_evalEval_ne_zero (solution)
