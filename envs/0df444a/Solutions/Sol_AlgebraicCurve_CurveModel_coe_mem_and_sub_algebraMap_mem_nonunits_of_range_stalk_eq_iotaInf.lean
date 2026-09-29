-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iotaInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/22d07c88-16b7-5fe7-b5a9-24f57430a0d4

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iotaInf

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

p2m_open "CategoryTheory AlgebraicGeometry IntermediateField AlgebraicCurve P2MW.S_AlgebraicCurve_CurveModel_coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iotaInf.AlgebraicCurve AlgebraicCurve.CurveModel P2MW.S_AlgebraicCurve_CurveModel_coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iotaInf.AlgebraicCurve.CurveModel"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "CurveModel Place"
namespace CurveModel
p2m_export "AlgebraicCurve.CurveModel" "inclInf glued ιInf ιU ιU_eq' gluedFunctionFieldEquiv range_ffEquiv_symm_comp_algebraMap_stalk chartRing"
namespace CentreSP
p2m_open "AlgebraicCurve.CurveModel AlgebraicCurve"

universe u

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]
  [FiniteDimensional ↥K⟮t⟯ L]

theorem spec_map_base_closedPoint_asIdeal {A : Type u} [CommRing A] (χ : A →+* K) :
    ((Spec.map (CommRingCat.ofHom χ)).base (IsLocalRing.closedPoint K)).asIdeal = RingHom.ker χ := by
  rw [Spec.map_base]
  show (PrimeSpectrum.comap (CommRingCat.ofHom χ).hom (IsLocalRing.closedPoint K)).asIdeal = _
  rw [PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom, RingHom.ker_eq_comap_bot]
  congr 1
  exact (IsLocalRing.closedPoint K).asIdeal.eq_bot_of_prime

theorem chart
    (A : Subalgebra K L) (i : ↥A →ₐ[K] ↥(chartRing K ({t, t⁻¹} : Set L)))
    (hi : ∀ a : A, (i a : L) = a)
    (ιA : Spec (CommRingCat.of ↥A) ⟶ glued K t) [IsOpenImmersion ιA]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom i.toRingHom))]
    (comm : Spec.map (CommRingCat.ofHom i.toRingHom) ≫ ιA = ιU K t)
    (P : closedPoints (glued K t) → Place K L)
    (hPst : ∀ x : closedPoints (glued K t),
      (((gluedFunctionFieldEquiv K t).symm : (glued K t).functionField ≃+* L).toRingHom.comp
          (algebraMap ((glued K t).presheaf.stalk x.1) (glued K t).functionField)).range =
        (P x).toValuationSubring.toSubring)
    (χ : ↥A →ₐ[K] K) (z : closedPoints (glued K t))
    (hz : z.1 = ιA.base ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base
      (IsLocalRing.closedPoint K))) (c : ↥A) :
    (c : L) ∈ (P z).toValuationSubring ∧
      (c : L) - algebraMap K L (χ c) ∈ (P z).toValuationSubring.nonunits := by
  obtain ⟨z₁, hzc⟩ := z
  subst hz

  have hset : ∀ y : L, y ∈ (P ⟨_, hzc⟩).toValuationSubring ↔
      ∃ a b : A, b ∉ RingHom.ker χ.toRingHom ∧ y = (a : L) * ((b : A) : L)⁻¹ := by
    intro y
    have h1 := range_ffEquiv_symm_comp_algebraMap_stalk K t A i hi ιA comm
      ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base (IsLocalRing.closedPoint K))
    rw [spec_map_base_closedPoint_asIdeal] at h1
    have h2 := hPst ⟨_, hzc⟩
    rw [← ValuationSubring.mem_toSubring, ← h2, ← SetLike.mem_coe]
    show y ∈ ((((gluedFunctionFieldEquiv K t).symm : (glued K t).functionField ≃+* L).toRingHom.comp
        (algebraMap ((glued K t).presheaf.stalk
          (ιA.base ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base (IsLocalRing.closedPoint K))))
          (glued K t).functionField)).range : Set L) ↔ _
    rw [h1]
    rfl
  have hker : ∀ a : A, a ∈ RingHom.ker χ.toRingHom ↔ χ a = 0 := fun a => RingHom.mem_ker
  have hone : (1 : A) ∉ RingHom.ker χ.toRingHom := by
    rw [hker, map_one]; exact one_ne_zero

  have hmem : ∀ a : A, (a : L) ∈ (P ⟨_, hzc⟩).toValuationSubring := fun a =>
    (hset _).mpr ⟨a, 1, hone, by simp⟩
  refine ⟨hmem c, ?_⟩

  set e : A := c - algebraMap K A (χ c) with he
  have heker : e ∈ RingHom.ker χ.toRingHom := by
    rw [hker, he, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hecoe : (e : L) = (c : L) - algebraMap K L (χ c) := by
    rw [he, Subalgebra.coe_sub, IsScalarTower.algebraMap_apply K A L]
    rfl
  rw [← hecoe, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  refine ⟨hmem e, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  obtain ⟨u, hu⟩ := hunit.exists_right_inv
  obtain ⟨a, b, hb, hab⟩ := (hset (u : L)).mp u.2
  have hb0 : ((b : A) : L) ≠ 0 := by
    intro h0
    apply hb
    rw [hker, show b = 0 from Subtype.ext h0, map_zero]

  have h1 : (e : L) * (u : L) = 1 := by
    have := congrArg (fun w : (P ⟨_, hzc⟩).toValuationSubring => (w : L)) hu
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
    exact this
  rw [hab] at h1
  have h2 : ((e * a : A) : L) = ((b : A) : L) := by
    rw [Subalgebra.coe_mul]
    field_simp at h1
    linear_combination h1
  have h3 : e * a = b := Subtype.ext h2
  apply hb
  rw [← h3]
  exact Ideal.mul_mem_right _ _ heker

end AlgebraicCurve.CurveModel.CentreSP

end

universe u

open _root_.AlgebraicCurve.CurveModel _root_.P2MW.S_AlgebraicCurve_CurveModel_coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iotaInf.AlgebraicCurve.CurveModel in

theorem solution
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]
    [FiniteDimensional ↥K⟮t⟯ L]
    (P : closedPoints (glued K t) → Place K L)
    (hPst : ∀ x : closedPoints (glued K t),
      (((gluedFunctionFieldEquiv K t).symm : (glued K t).functionField ≃+* L).toRingHom.comp
          (algebraMap ((glued K t).presheaf.stalk x.1) (glued K t).functionField)).range =
        (P x).toValuationSubring.toSubring)
    (χ : ↥(chartRing K ({t⁻¹} : Set L)) →ₐ[K] K)
    (z : closedPoints (glued K t))
    (hz : z.1 = (ιInf K t).base ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base
      (IsLocalRing.closedPoint K))) :
    ∀ c : ↥(chartRing K ({t⁻¹} : Set L)),
      (c : L) ∈ (P z).toValuationSubring ∧
        (c : L) - algebraMap K L (χ c) ∈ (P z).toValuationSubring.nonunits := fun c =>
  AlgebraicCurve.CurveModel.CentreSP.chart K t (chartRing K ({t⁻¹} : Set L)) (inclInf K t)
    (fun _ => rfl) (ιInf K t) (ιU_eq' K t).symm P hPst χ z hz c

end S_AlgebraicCurve_CurveModel_coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iotaInf
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iotaInf (solution)
