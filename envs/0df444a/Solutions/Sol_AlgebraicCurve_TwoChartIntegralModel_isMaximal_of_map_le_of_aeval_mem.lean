-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.isMaximal_of_map_le_of_aeval_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/038d1de6-61d0-5916-993a-47a4574ae05f

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isMaximal_of_map_le_of_aeval_mem

set_option autoImplicit false

universe u

p2m_open "AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isMaximal_of_map_le_of_aeval_mem.AlgebraicCurve.TwoChartIntegralModel"
open Polynomial

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "mem_chartAlg_iff adjoin_le_chartAlg chartAlgFin jChartFin XFin"
namespace SSClosedProof
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]

theorem aeval_mem_map_of_forall_coeff_mem (𝔪 : Ideal R) (x : A) (P : R[X]) (hP : ∀ i, P.coeff i ∈ 𝔪) :
    aeval x P ∈ 𝔪.map (algebraMap R A) := by
  rw [aeval_eq_sum_range]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hP i))

theorem isIntegral_mk_of_aeval_mem (𝔪 : Ideal R) [𝔪.IsMaximal] (I : Ideal A)
    (hI : 𝔪.map (algebraMap R A) ≤ I) (x : A) (P : R[X]) (hP0 : P.map (Ideal.Quotient.mk 𝔪) ≠ 0)
    (hPx : aeval x P ∈ I) : IsIntegral R (Ideal.Quotient.mk I x) := by
  classical
  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  set Pb : (R ⧸ 𝔪)[X] := P.map (Ideal.Quotient.mk 𝔪) with hPb
  set c : R ⧸ 𝔪 := Pb.leadingCoeff with hc
  have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr hP0

  set q : (R ⧸ 𝔪)[X] := Pb * C c⁻¹ with hq
  have hqm : q.Monic := monic_mul_leadingCoeff_inv hP0
  have hql : q ∈ Polynomial.lifts (Ideal.Quotient.mk 𝔪) := by
    obtain ⟨q', hq'⟩ := Polynomial.map_surjective (Ideal.Quotient.mk 𝔪) Ideal.Quotient.mk_surjective q
    exact (Polynomial.mem_lifts q).mpr ⟨q', hq'⟩
  obtain ⟨Q, hQq, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hql hqm
  obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (I := 𝔪) c⁻¹

  have hcoeff : ∀ i, (Q - C d * P).coeff i ∈ 𝔪 := by
    intro i
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_C, hQq, hd, hq, mul_comm (C c⁻¹) Pb, sub_self, coeff_zero]
  have hQx : aeval x Q ∈ I := by
    have h1 : aeval x (Q - C d * P) ∈ I := hI (aeval_mem_map_of_forall_coeff_mem 𝔪 x _ hcoeff)
    have h2 : aeval x (C d * P) ∈ I := by
      rw [map_mul, aeval_C]
      exact Ideal.mul_mem_left _ _ hPx
    have h3 : aeval x Q = aeval x (Q - C d * P) + aeval x (C d * P) := by rw [map_sub, sub_add_cancel]
    rw [h3]
    exact I.add_mem h1 h2
  refine ⟨Q, hQm, ?_⟩
  rw [← aeval_def, ← Ideal.Quotient.mkₐ_eq_mk R, aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem]
  exact hQx

end AlgebraicCurve.TwoChartIntegralModel.SSClosedProof

open AlgebraicCurve.TwoChartIntegralModel.SSClosedProof in
theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (𝔪 : Ideal R) [𝔪.IsMaximal]
    (y : ↥(XFin R F j))
    (hy : Ideal.map (algebraMap R ↥(chartAlgFin R F j)) 𝔪 ≤ y.asIdeal)
    (halg : ∃ P : Polynomial R, P.map (Ideal.Quotient.mk 𝔪) ≠ 0 ∧
      (Polynomial.aeval (jChartFin R F j) P : ↥(chartAlgFin R F j)) ∈ y.asIdeal) :
    y.asIdeal.IsMaximal ∧
      (Algebra.FiniteType R ↥(chartAlgFin R F j) → Module.Finite R (↥(chartAlgFin R F j) ⧸ y.asIdeal)) := by
  classical

  set A : Subalgebra R F := chartAlgFin R F j with hA
  set S : Subalgebra R F := Algebra.adjoin R ({j} : Set F) with hS
  have hSA : S ≤ A := adjoin_le_chartAlg R F {j}
  let I : Ideal A := y.asIdeal
  haveI hIp : I.IsPrime := y.isPrime
  obtain ⟨P, hP0, hPj⟩ := halg

  have hj : IsIntegral R (Ideal.Quotient.mk I (jChartFin R F j)) :=
    isIntegral_mk_of_aeval_mem 𝔪 I hy (jChartFin R F j) P hP0 hPj

  let θ : S →ₐ[R] A ⧸ I := (Ideal.Quotient.mkₐ R I).comp (Subalgebra.inclusion hSA)
  have hθ : ∀ s : S, θ s = Ideal.Quotient.mk I (Subalgebra.inclusion hSA s) := fun s => rfl

  have hθint : ∀ s : S, IsIntegral R (θ s) := by
    rintro ⟨s, hs⟩
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      have hxj : x = j := Set.mem_singleton_iff.mp hx
      have hxS : (⟨x, Algebra.subset_adjoin hx⟩ : S) = ⟨j, Algebra.subset_adjoin rfl⟩ := Subtype.ext hxj
      rw [hxS, hθ]
      exact hj
    | algebraMap r =>
      have : (⟨algebraMap R F r, Subalgebra.algebraMap_mem S r⟩ : S) = algebraMap R S r := rfl
      rw [this, AlgHom.commutes]
      exact isIntegral_algebraMap
    | add x z hx hz ihx ihz =>
      have : (⟨x + z, Subalgebra.add_mem S hx hz⟩ : S) = ⟨x, hx⟩ + ⟨z, hz⟩ := rfl
      rw [this, map_add]
      exact ihx.add ihz
    | mul x z hx hz ihx ihz =>
      have : (⟨x * z, Subalgebra.mul_mem S hx hz⟩ : S) = ⟨x, hx⟩ * ⟨z, hz⟩ := rfl
      rw [this, map_mul]
      exact ihx.mul ihz
  haveI hS'int : Algebra.IsIntegral R ↥θ.range := by
    refine ⟨?_⟩
    rintro ⟨b, s, rfl⟩
    exact (isIntegral_algHom_iff θ.range.val Subtype.val_injective).mp (hθint s)

  have hBint : ∀ b : A ⧸ I, IsIntegral R b := by
    intro b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b

    obtain ⟨p, hpm, hpa⟩ := (mem_chartAlg_iff R F).mp a.2
    have hpa' : Polynomial.eval₂ (Subalgebra.inclusion hSA).toRingHom a p = 0 := by
      apply Subtype.val_injective
      have h := Polynomial.hom_eval₂ p (Subalgebra.inclusion hSA).toRingHom A.val.toRingHom a
      have hcomp : A.val.toRingHom.comp (Subalgebra.inclusion hSA).toRingHom = algebraMap S F := by
        ext s; rfl
      rw [hcomp] at h
      show A.val.toRingHom (eval₂ (Subalgebra.inclusion hSA).toRingHom a p) = ((0 : A) : F)
      rw [h]
      exact hpa
    have hrel : Polynomial.eval₂ θ.toRingHom (Ideal.Quotient.mk I a) p = 0 := by
      have h := Polynomial.hom_eval₂ p (Subalgebra.inclusion hSA).toRingHom (Ideal.Quotient.mk I) a
      rw [hpa', map_zero] at h
      have hcomp : (Ideal.Quotient.mk I).comp (Subalgebra.inclusion hSA).toRingHom = θ.toRingHom := by
        ext s; rfl
      rw [hcomp] at h
      exact h.symm

    have hS' : IsIntegral (↥θ.range) (Ideal.Quotient.mk I a) := by
      refine ⟨p.map θ.rangeRestrict.toRingHom, hpm.map _, ?_⟩
      rw [eval₂_map]
      have hcomp : (algebraMap (↥θ.range) (A ⧸ I)).comp θ.rangeRestrict.toRingHom = θ.toRingHom := by
        ext s; rfl
      rw [hcomp]
      exact hrel
    exact isIntegral_trans (Ideal.Quotient.mk I a) hS'

  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hle : 𝔪 ≤ I.comap (algebraMap R A) := Ideal.map_le_iff_le_comap.mp hy
  let φ : R ⧸ 𝔪 →+* A ⧸ I := Ideal.quotientMap I (algebraMap R A) hle
  letI : Algebra (R ⧸ 𝔪) (A ⧸ I) := φ.toAlgebra
  haveI : IsScalarTower R (R ⧸ 𝔪) (A ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI : Algebra.IsIntegral (R ⧸ 𝔪) (A ⧸ I) := ⟨fun b => (hBint b).tower_top⟩
  have hfield : IsField (A ⧸ I) :=
    isField_of_isIntegral_of_isField' (Field.toIsField (R ⧸ 𝔪))
  refine ⟨Ideal.Quotient.maximal_of_isField I hfield, fun hFT => ?_⟩
  haveI : Algebra.IsIntegral R (A ⧸ I) := ⟨hBint⟩
  haveI : Algebra.FiniteType R (A ⧸ I) :=
    hFT.of_surjective (Ideal.Quotient.mkₐ R I) Ideal.Quotient.mk_surjective
  exact Algebra.IsIntegral.finite

end S_AlgebraicCurve_TwoChartIntegralModel_isMaximal_of_map_le_of_aeval_mem
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isMaximal_of_map_le_of_aeval_mem (solution)
