-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_algEquiv_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a24d3ba0-7023-52e7-b301-5f107a72b774

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_algEquiv_apply_eq

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "chartAlg mem_chartAlg_iff coe_chartIncl chartAlgFin chartAlgInf chartAlgMid inclFin inclInf fFin fInf ιFin ιInf toBase ιFin_toBase ιInf_toBase"
namespace Transport
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

variable {R : Type u} [CommRing R] {F F' : Type u} [Field F] [Field F'] [Algebra R F] [Algebra R F']

theorem mem_chartAlg_map (e : F ≃ₐ[R] F') (S : Set F) {x : F} (hx : x ∈ chartAlg R F S) :
    e x ∈ chartAlg R F' (e '' S) := by
  rw [mem_chartAlg_iff] at hx ⊢
  set A := Algebra.adjoin R S with hA
  set A' := Algebra.adjoin R (e '' S) with hA'

  have hAA' : ∀ a : F, a ∈ A → e a ∈ A' := by
    intro a ha
    have : e a ∈ A.map (e : F →ₐ[R] F') := Subalgebra.mem_map.mpr ⟨a, ha, rfl⟩
    rwa [AlgHom.map_adjoin] at this
  let eA : A →+* A' :=
    { toFun := fun a => ⟨e a, hAA' a a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hcomp : (e : F →+* F').comp (algebraMap A F) = (algebraMap A' F').comp eA := RingHom.ext fun a => rfl
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map eA, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map, ← hcomp]
  have h2 : eval₂ ((e : F →+* F').comp (algebraMap A F)) ((e : F →+* F') x) p =
      (e : F →+* F') (eval₂ (algebraMap A F) x p) := (Polynomial.hom_eval₂ p (algebraMap A F) (e : F →+* F') x).symm
  exact h2.trans (by rw [hpx, map_zero])

theorem exists_restr (e : F ≃ₐ[R] F') (S : Set F) (S' : Set F') (hS : e '' S = S') :
    ∃ τ : chartAlg R F S →ₐ[R] chartAlg R F' S', ∀ x, (τ x : F') = e x := by
  subst hS
  exact ⟨((e : F →ₐ[R] F').comp (chartAlg R F S).val).codRestrict (chartAlg R F' (e '' S))
    (fun x => mem_chartAlg_map e S x.2), fun _ => rfl⟩

theorem spec_map_comp_eq_id {A B : Type u} [CommRing A] [CommRing B] (a : A →+* B) (b : B →+* A)
    (hab : ∀ x, a (b x) = x) :
    Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom b) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show a.comp b = RingHom.id B from RingHom.ext hab, CommRingCat.ofHom_id]
  exact Spec.map_id _

end AlgebraicCurve.TwoChartIntegralModel.Transport

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "chartAlg mem_chartAlg_iff coe_chartIncl chartAlgFin chartAlgInf chartAlgMid inclFin inclInf fFin fInf ιFin ιInf toBase ιFin_toBase ιInf_toBase"
namespace TransportMain
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"
p2m_open "AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_algEquiv_apply_eq.AlgebraicCurve.TwoChartIntegralModel"
open AlgebraicCurve.TwoChartIntegralModel.Transport

variable (R : Type u) [CommRing R] (F F' : Type u) [Field F] [Field F'] [Algebra R F] [Algebra R F']
  (j : F) (j' : F') [Fact (j ≠ 0)] [Fact (j' ≠ 0)]

theorem exists_hom_of_chartAlgHom₂
    (aF : chartAlgFin R F j →ₐ[R] chartAlgFin R F' j') (aI : chartAlgInf R F j →ₐ[R] chartAlgInf R F' j')
    (aM : chartAlgMid R F j →ₐ[R] chartAlgMid R F' j')
    (hcF : ∀ x, (aM (inclFin R F j x) : F') = aF x) (hcI : ∀ x, (aM (inclInf R F j x) : F') = aI x) :
    ∃ φ : AlgebraicCurve.TwoChartIntegralModel R F' j' ⟶ AlgebraicCurve.TwoChartIntegralModel R F j,
      ιFin R F' j' ≫ φ = Spec.map (CommRingCat.ofHom aF.toRingHom) ≫ ιFin R F j ∧
      ιInf R F' j' ≫ φ = Spec.map (CommRingCat.ofHom aI.toRingHom) ≫ ιInf R F j := by
  have eF : (inclFin R F' j').toRingHom.comp aF.toRingHom = aM.toRingHom.comp (inclFin R F j).toRingHom :=
    RingHom.ext fun x => Subtype.ext
      (show ((inclFin R F' j' (aF x) : chartAlgMid R F' j') : F') = (aM (inclFin R F j x) : F') by
          rw [hcF, coe_chartIncl])
  have eI : (inclInf R F' j').toRingHom.comp aI.toRingHom = aM.toRingHom.comp (inclInf R F j).toRingHom :=
    RingHom.ext fun x => Subtype.ext
      (show ((inclInf R F' j' (aI x) : chartAlgMid R F' j') : F') = (aM (inclInf R F j x) : F') by
          rw [hcI, coe_chartIncl])
  have cF : fFin R F' j' ≫ Spec.map (CommRingCat.ofHom aF.toRingHom) =
      Spec.map (CommRingCat.ofHom aM.toRingHom) ≫ fFin R F j := by
    simp only [fFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp, eF]
  have cI : fInf R F' j' ≫ Spec.map (CommRingCat.ofHom aI.toRingHom) =
      Spec.map (CommRingCat.ofHom aM.toRingHom) ≫ fInf R F j := by
    simp only [fInf, ← Spec.map_comp, ← CommRingCat.ofHom_comp, eI]
  refine ⟨pushout.map _ _ _ _ (Spec.map (CommRingCat.ofHom aF.toRingHom))
    (Spec.map (CommRingCat.ofHom aI.toRingHom)) (Spec.map (CommRingCat.ofHom aM.toRingHom)) cF cI, ?_, ?_⟩
  · exact pushout.inl_desc _ _ _
  · exact pushout.inr_desc _ _ _

variable {F F' j j'} in

theorem comp_eq_id_of_charts
    (α : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F' j')
    (β : AlgebraicCurve.TwoChartIntegralModel R F' j' ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
    (aF : chartAlgFin R F' j' →+* chartAlgFin R F j) (bF : chartAlgFin R F j →+* chartAlgFin R F' j')
    (aI : chartAlgInf R F' j' →+* chartAlgInf R F j) (bI : chartAlgInf R F j →+* chartAlgInf R F' j')
    (hαF : ιFin R F j ≫ α = Spec.map (CommRingCat.ofHom aF) ≫ ιFin R F' j')
    (hβF : ιFin R F' j' ≫ β = Spec.map (CommRingCat.ofHom bF) ≫ ιFin R F j)
    (hαI : ιInf R F j ≫ α = Spec.map (CommRingCat.ofHom aI) ≫ ιInf R F' j')
    (hβI : ιInf R F' j' ≫ β = Spec.map (CommRingCat.ofHom bI) ≫ ιInf R F j)
    (habF : ∀ x, aF (bF x) = x) (habI : ∀ x, aI (bI x) = x) : α ≫ β = 𝟙 _ := by
  apply pushout.hom_ext
  · change ιFin R F j ≫ α ≫ β = ιFin R F j ≫ 𝟙 _
    rw [← Category.assoc, hαF, Category.assoc, hβF, ← Category.assoc,
      spec_map_comp_eq_id aF bF habF, Category.id_comp, Category.comp_id]
  · change ιInf R F j ≫ α ≫ β = ιInf R F j ≫ 𝟙 _
    rw [← Category.assoc, hαI, Category.assoc, hβI, ← Category.assoc,
      spec_map_comp_eq_id aI bI habI, Category.id_comp, Category.comp_id]

theorem exists_iso_of_algEquiv_apply_eq (e : F ≃ₐ[R] F') (he : e j = j') :
    ∃ (w : AlgebraicCurve.TwoChartIntegralModel R F j ≅ AlgebraicCurve.TwoChartIntegralModel R F' j')
      (eFin : chartAlgFin R F j →ₐ[R] chartAlgFin R F' j') (eInf : chartAlgInf R F j →ₐ[R] chartAlgInf R F' j'),
      (∀ x, (eFin x : F') = e x) ∧ (∀ x, (eInf x : F') = e x) ∧
      w.hom ≫ toBase R F' j' = toBase R F j ∧
      Spec.map (CommRingCat.ofHom eFin.toRingHom) ≫ ιFin R F j = ιFin R F' j' ≫ w.inv ∧
      Spec.map (CommRingCat.ofHom eInf.toRingHom) ≫ ιInf R F j = ιInf R F' j' ≫ w.inv := by
  have hS1 : e '' ({j} : Set F) = {j'} := by rw [Set.image_singleton, he]
  have hS2 : e '' ({j⁻¹} : Set F) = {j'⁻¹} := by rw [Set.image_singleton, map_inv₀, he]
  have hS3 : e '' ({j, j⁻¹} : Set F) = {j', j'⁻¹} := by
    rw [Set.image_insert_eq, Set.image_singleton, map_inv₀, he]
  have hS1' : e.symm '' ({j'} : Set F') = {j} := by rw [Set.image_singleton, ← he, e.symm_apply_apply]
  have hS2' : e.symm '' ({j'⁻¹} : Set F') = {j⁻¹} := by
    rw [Set.image_singleton, map_inv₀, ← he, e.symm_apply_apply]
  have hS3' : e.symm '' ({j', j'⁻¹} : Set F') = {j, j⁻¹} := by
    rw [Set.image_insert_eq, Set.image_singleton, map_inv₀, ← he, e.symm_apply_apply]
  obtain ⟨τF, eτF⟩ := exists_restr e {j} {j'} hS1
  obtain ⟨τI, eτI⟩ := exists_restr e {j⁻¹} {j'⁻¹} hS2
  obtain ⟨τM, eτM⟩ := exists_restr e {j, j⁻¹} {j', j'⁻¹} hS3
  obtain ⟨τF', eτF'⟩ := exists_restr e.symm {j'} {j} hS1'
  obtain ⟨τI', eτI'⟩ := exists_restr e.symm {j'⁻¹} {j⁻¹} hS2'
  obtain ⟨τM', eτM'⟩ := exists_restr e.symm {j', j'⁻¹} {j, j⁻¹} hS3'

  obtain ⟨ψ, hψF, hψI⟩ := exists_hom_of_chartAlgHom₂ R F F' j j' τF τI τM
    (fun x => by rw [eτM, eτF, coe_chartIncl]) (fun x => by rw [eτM, eτI, coe_chartIncl])
  obtain ⟨φ, hφF, hφI⟩ := exists_hom_of_chartAlgHom₂ R F' F j' j τF' τI' τM'
    (fun x => by rw [eτM', eτF', coe_chartIncl]) (fun x => by rw [eτM', eτI', coe_chartIncl])
  have iF : ∀ x, τF.toRingHom (τF'.toRingHom x) = x := fun x => Subtype.ext (by
    change (τF (τF' x) : F') = x; rw [eτF, eτF']; exact e.apply_symm_apply _)
  have iF' : ∀ x, τF'.toRingHom (τF.toRingHom x) = x := fun x => Subtype.ext (by
    change (τF' (τF x) : F) = x; rw [eτF', eτF]; exact e.symm_apply_apply _)
  have iI : ∀ x, τI.toRingHom (τI'.toRingHom x) = x := fun x => Subtype.ext (by
    change (τI (τI' x) : F') = x; rw [eτI, eτI']; exact e.apply_symm_apply _)
  have iI' : ∀ x, τI'.toRingHom (τI.toRingHom x) = x := fun x => Subtype.ext (by
    change (τI' (τI x) : F) = x; rw [eτI', eτI]; exact e.symm_apply_apply _)
  have hφψ : φ ≫ ψ = 𝟙 _ :=
    comp_eq_id_of_charts R φ ψ _ _ _ _ hφF hψF hφI hψI iF' iI'
  have hψφ : ψ ≫ φ = 𝟙 _ :=
    comp_eq_id_of_charts R ψ φ _ _ _ _ hψF hφF hψI hφI iF iI
  refine ⟨⟨φ, ψ, hφψ, hψφ⟩, τF, τI, eτF, eτI, ?_, hψF.symm, hψI.symm⟩

  apply pushout.hom_ext
  · change ιFin R F j ≫ φ ≫ toBase R F' j' = ιFin R F j ≫ toBase R F j
    rw [← Category.assoc, hφF, Category.assoc, ιFin_toBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ιFin_toBase]
    congr 2
    exact RingHom.ext fun r => τF'.commutes r
  · change ιInf R F j ≫ φ ≫ toBase R F' j' = ιInf R F j ≫ toBase R F j
    rw [← Category.assoc, hφI, Category.assoc, ιInf_toBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ιInf_toBase]
    congr 2
    exact RingHom.ext fun r => τI'.commutes r

end AlgebraicCurve.TwoChartIntegralModel.TransportMain

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_algEquiv_apply_eq.AlgebraicCurve _root_.AlgebraicCurve.TwoChartIntegralModel _root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_algEquiv_apply_eq.AlgebraicCurve.TwoChartIntegralModel in
theorem solution
    (R : Type u) [CommRing R] (F F' : Type u) [Field F] [Field F'] [Algebra R F] [Algebra R F']
    (j : F) (j' : F') [Fact (j ≠ 0)] [Fact (j' ≠ 0)] (e : F ≃ₐ[R] F') (he : e j = j') :
    ∃ (w : AlgebraicCurve.TwoChartIntegralModel R F j ≅ AlgebraicCurve.TwoChartIntegralModel R F' j')
      (eFin : chartAlgFin R F j →ₐ[R] chartAlgFin R F' j') (eInf : chartAlgInf R F j →ₐ[R] chartAlgInf R F' j'),
      (∀ x, (eFin x : F') = e x) ∧ (∀ x, (eInf x : F') = e x) ∧
      w.hom ≫ toBase R F' j' = toBase R F j ∧
      Spec.map (CommRingCat.ofHom eFin.toRingHom) ≫ ιFin R F j = ιFin R F' j' ≫ w.inv ∧
      Spec.map (CommRingCat.ofHom eInf.toRingHom) ≫ ιInf R F j = ιInf R F' j' ≫ w.inv :=
  AlgebraicCurve.TwoChartIntegralModel.TransportMain.exists_iso_of_algEquiv_apply_eq R F F' j j' e he

end S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_algEquiv_apply_eq
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_algEquiv_apply_eq (solution)
