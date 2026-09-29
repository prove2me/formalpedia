-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_ringEquiv_of_ringEquiv_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ec2b6722-08e8-5a1b-8620-0ea4cdb4c19f

import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_ringEquiv_of_ringEquiv_apply_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

namespace E153F

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

section Alg

variable {R R' : Type u} [CommRing R] [CommRing R'] {F F' : Type u} [Field F] [Field F'] [Algebra R F] [Algebra R' F']

theorem map_mem_adjoin (e₀ : R ≃+* R') (e : F ≃+* F')
    (he₀ : ∀ r : R, e (algebraMap R F r) = algebraMap R' F' (e₀ r))
    (S : Set F) {z : F} (hz : z ∈ Algebra.adjoin R S) : e z ∈ Algebra.adjoin R' (e '' S) := by
  induction hz using Algebra.adjoin_induction with
  | mem z hz => exact Algebra.subset_adjoin ⟨z, hz, rfl⟩
  | algebraMap r => rw [he₀]; exact Subalgebra.algebraMap_mem _ _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem map_mem_chartAlg (e₀ : R ≃+* R') (e : F ≃+* F')
    (he₀ : ∀ r : R, e (algebraMap R F r) = algebraMap R' F' (e₀ r))
    (S : Set F) {x : F} (hx : x ∈ chartAlg R F S) : e x ∈ chartAlg R' F' (e '' S) := by
  let φ : ↥(Algebra.adjoin R S) →+* ↥(Algebra.adjoin R' (e '' S)) :=
    { toFun := fun z => ⟨e z, map_mem_adjoin e₀ e he₀ S z.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  exact ((mem_chartAlg_iff R F).mp hx).map_of_comp_eq φ e.toRingHom (by ext z; rfl)

theorem symm_algebraMap (e₀ : R ≃+* R') (e : F ≃+* F')
    (he₀ : ∀ r : R, e (algebraMap R F r) = algebraMap R' F' (e₀ r)) :
    ∀ r' : R', e.symm (algebraMap R' F' r') = algebraMap R F (e₀.symm r') := by
  intro r'
  apply e.injective
  rw [e.apply_symm_apply, he₀, e₀.apply_symm_apply]

theorem mem_chartAlg_iff_map (e₀ : R ≃+* R') (e : F ≃+* F')
    (he₀ : ∀ r : R, e (algebraMap R F r) = algebraMap R' F' (e₀ r))
    (S : Set F) (S' : Set F') (hS : e '' S = S') (x : F) :
    x ∈ chartAlg R F S ↔ e x ∈ chartAlg R' F' S' := by
  constructor
  · intro hx
    rw [← hS]
    exact map_mem_chartAlg e₀ e he₀ S hx
  · intro hx
    have h := map_mem_chartAlg e₀.symm e.symm (symm_algebraMap e₀ e he₀) S' hx
    rw [RingEquiv.symm_apply_apply] at h
    have hS' : e.symm '' S' = S := by
      rw [← hS, ← Set.image_comp,
        show (⇑e.symm ∘ ⇑e) = id from funext fun y => e.symm_apply_apply y, Set.image_id]
    rwa [hS'] at h

def chartEquiv (e₀ : R ≃+* R') (e : F ≃+* F')
    (he₀ : ∀ r : R, e (algebraMap R F r) = algebraMap R' F' (e₀ r))
    (S : Set F) (S' : Set F') (hS : e '' S = S') : ↥(chartAlg R F S) ≃+* ↥(chartAlg R' F' S') where
  toFun x := ⟨e x, (mem_chartAlg_iff_map e₀ e he₀ S S' hS x).mp x.2⟩
  invFun y := ⟨e.symm y, by
    have h := mem_chartAlg_iff_map e₀ e he₀ S S' hS (e.symm y)
    rw [RingEquiv.apply_symm_apply] at h
    exact h.mpr y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply _)
  right_inv y := Subtype.ext (e.apply_symm_apply _)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

theorem coe_chartEquiv (e₀ : R ≃+* R') (e : F ≃+* F')
    (he₀ : ∀ r : R, e (algebraMap R F r) = algebraMap R' F' (e₀ r))
    (S : Set F) (S' : Set F') (hS : e '' S = S') (x : ↥(chartAlg R F S)) :
    ((chartEquiv e₀ e he₀ S S' hS x : ↥(chartAlg R' F' S')) : F') = e x := rfl

theorem coe_chartEquiv_symm (e₀ : R ≃+* R') (e : F ≃+* F')
    (he₀ : ∀ r : R, e (algebraMap R F r) = algebraMap R' F' (e₀ r))
    (S : Set F) (S' : Set F') (hS : e '' S = S') (y : ↥(chartAlg R' F' S')) :
    (((chartEquiv e₀ e he₀ S S' hS).symm y : ↥(chartAlg R F S)) : F) = e.symm y := rfl

end Alg

noncomputable def specCongr {A B : Type u} [CommRing A] [CommRing B] (ε : A ≃+* B) :
    Spec (CommRingCat.of A) ≅ Spec (CommRingCat.of B) where
  hom := Spec.map (CommRingCat.ofHom ε.symm.toRingHom)
  inv := Spec.map (CommRingCat.ofHom ε.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingEquiv.symm_toRingHom_comp_toRingHom,
      CommRingCat.ofHom_id, Spec.map_id]
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingEquiv.toRingHom_comp_symm_toRingHom,
      CommRingCat.ofHom_id, Spec.map_id]

end E153F

set_option maxHeartbeats 16000000 in

theorem solution
    (R R' : Type u) [CommRing R] [CommRing R'] (F F' : Type u) [Field F] [Field F'] [Algebra R F] [Algebra R' F']
    (j : F) (j' : F') [Fact (j ≠ 0)] [Fact (j' ≠ 0)]
    (e₀ : R ≃+* R') (e : F ≃+* F')
    (he₀ : ∀ r : R, e (algebraMap R F r) = algebraMap R' F' (e₀ r)) (he : e j = j') :
    ∃ (w : AlgebraicCurve.TwoChartIntegralModel R F j ≅ AlgebraicCurve.TwoChartIntegralModel R' F' j')
      (eFin : chartAlgFin R F j ≃+* chartAlgFin R' F' j') (eInf : chartAlgInf R F j ≃+* chartAlgInf R' F' j'),
      (∀ x, (eFin x : F') = e x) ∧ (∀ x, (eInf x : F') = e x) ∧
      w.hom ≫ toBase R' F' j' = toBase R F j ≫ Spec.map (CommRingCat.ofHom e₀.symm.toRingHom) ∧
      Spec.map (CommRingCat.ofHom eFin.toRingHom) ≫ ιFin R F j = ιFin R' F' j' ≫ w.inv ∧
      Spec.map (CommRingCat.ofHom eInf.toRingHom) ≫ ιInf R F j = ιInf R' F' j' ≫ w.inv := by
  classical
  have hSfin : e '' ({j} : Set F) = {j'} := by rw [Set.image_singleton, he]
  have hSinf : e '' ({j⁻¹} : Set F) = {j'⁻¹} := by rw [Set.image_singleton, map_inv₀, he]
  have hSmid : e '' ({j, j⁻¹} : Set F) = {j', j'⁻¹} := by rw [Set.image_pair, map_inv₀, he]
  let εFin : ↥(chartAlgFin R F j) ≃+* ↥(chartAlgFin R' F' j') := E153F.chartEquiv e₀ e he₀ {j} {j'} hSfin
  let εInf : ↥(chartAlgInf R F j) ≃+* ↥(chartAlgInf R' F' j') := E153F.chartEquiv e₀ e he₀ {j⁻¹} {j'⁻¹} hSinf
  let εMid : ↥(chartAlgMid R F j) ≃+* ↥(chartAlgMid R' F' j') := E153F.chartEquiv e₀ e he₀ {j, j⁻¹} {j', j'⁻¹} hSmid
  let iFin : XFin R F j ≅ XFin R' F' j' := E153F.specCongr εFin
  let iInf : XInf R F j ≅ XInf R' F' j' := E153F.specCongr εInf
  let iMid : XMid R F j ≅ XMid R' F' j' := E153F.specCongr εMid

  have hcompFin : (εMid.symm.toRingHom).comp (inclFin R' F' j').toRingHom =
      (inclFin R F j).toRingHom.comp εFin.symm.toRingHom := by
    ext y
    rfl
  have hcompInf : (εMid.symm.toRingHom).comp (inclInf R' F' j').toRingHom =
      (inclInf R F j).toRingHom.comp εInf.symm.toRingHom := by
    ext y
    rfl
  have wf : iMid.hom ≫ fFin R' F' j' = fFin R F j ≫ iFin.hom := by
    show Spec.map (CommRingCat.ofHom εMid.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom (inclFin R' F' j').toRingHom) =
      Spec.map (CommRingCat.ofHom (inclFin R F j).toRingHom) ≫ Spec.map (CommRingCat.ofHom εFin.symm.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcompFin]
  have wg : iMid.hom ≫ fInf R' F' j' = fInf R F j ≫ iInf.hom := by
    show Spec.map (CommRingCat.ofHom εMid.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom (inclInf R' F' j').toRingHom) =
      Spec.map (CommRingCat.ofHom (inclInf R F j).toRingHom) ≫ Spec.map (CommRingCat.ofHom εInf.symm.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcompInf]
  let w : AlgebraicCurve.TwoChartIntegralModel R F j ≅ AlgebraicCurve.TwoChartIntegralModel R' F' j' :=
    HasColimit.isoOfNatIso (spanExt iMid iFin iInf wf wg)

  have hFin : ιFin R F j ≫ w.hom = iFin.hom ≫ ιFin R' F' j' := by
    have h := HasColimit.isoOfNatIso_ι_hom (spanExt iMid iFin iInf wf wg) WalkingSpan.left
    rw [spanExt_hom_app_left] at h
    exact h
  have hInf : ιInf R F j ≫ w.hom = iInf.hom ≫ ιInf R' F' j' := by
    have h := HasColimit.isoOfNatIso_ι_hom (spanExt iMid iFin iInf wf wg) WalkingSpan.right
    rw [spanExt_hom_app_right] at h
    exact h
  refine ⟨w, εFin, εInf, fun x => rfl, fun x => rfl, ?_, ?_, ?_⟩
  ·
    apply pushout.hom_ext
    · have h1 : pushout.inl (fFin R F j) (fInf R F j) ≫ w.hom ≫ toBase R' F' j' =
          Spec.map (CommRingCat.ofHom (εFin.symm.toRingHom.comp (algebraMap R' ↥(chartAlgFin R' F' j')))) := by
        rw [← Category.assoc]
        change (ιFin R F j ≫ w.hom) ≫ toBase R' F' j' = _
        rw [hFin, Category.assoc, ιFin_toBase]
        show Spec.map (CommRingCat.ofHom εFin.symm.toRingHom) ≫ _ = _
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have h2 : pushout.inl (fFin R F j) (fInf R F j) ≫ toBase R F j ≫ Spec.map (CommRingCat.ofHom e₀.symm.toRingHom) =
          Spec.map (CommRingCat.ofHom ((algebraMap R ↥(chartAlgFin R F j)).comp e₀.symm.toRingHom)) := by
        rw [← Category.assoc]
        change (ιFin R F j ≫ toBase R F j) ≫ _ = _
        rw [ιFin_toBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have h3 : εFin.symm.toRingHom.comp (algebraMap R' ↥(chartAlgFin R' F' j')) =
          (algebraMap R ↥(chartAlgFin R F j)).comp e₀.symm.toRingHom := by
        ext r'
        exact E153F.symm_algebraMap e₀ e he₀ r'
      exact h1.trans ((congrArg (fun f => Spec.map (CommRingCat.ofHom f)) h3).trans h2.symm)
    · have h1 : pushout.inr (fFin R F j) (fInf R F j) ≫ w.hom ≫ toBase R' F' j' =
          Spec.map (CommRingCat.ofHom (εInf.symm.toRingHom.comp (algebraMap R' ↥(chartAlgInf R' F' j')))) := by
        rw [← Category.assoc]
        change (ιInf R F j ≫ w.hom) ≫ toBase R' F' j' = _
        rw [hInf, Category.assoc, ιInf_toBase]
        show Spec.map (CommRingCat.ofHom εInf.symm.toRingHom) ≫ _ = _
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have h2 : pushout.inr (fFin R F j) (fInf R F j) ≫ toBase R F j ≫ Spec.map (CommRingCat.ofHom e₀.symm.toRingHom) =
          Spec.map (CommRingCat.ofHom ((algebraMap R ↥(chartAlgInf R F j)).comp e₀.symm.toRingHom)) := by
        rw [← Category.assoc]
        change (ιInf R F j ≫ toBase R F j) ≫ _ = _
        rw [ιInf_toBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have h3 : εInf.symm.toRingHom.comp (algebraMap R' ↥(chartAlgInf R' F' j')) =
          (algebraMap R ↥(chartAlgInf R F j)).comp e₀.symm.toRingHom := by
        ext r'
        exact E153F.symm_algebraMap e₀ e he₀ r'
      exact h1.trans ((congrArg (fun f => Spec.map (CommRingCat.ofHom f)) h3).trans h2.symm)
  · show iFin.inv ≫ ιFin R F j = ιFin R' F' j' ≫ w.inv
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact hFin
  · show iInf.inv ≫ ιInf R F j = ιInf R' F' j' ≫ w.inv
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact hInf

end S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_ringEquiv_of_ringEquiv_apply_eq
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_ringEquiv_of_ringEquiv_apply_eq (solution)
