-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_algEquiv_globalSections_chartAlgFin_inf_chartAlgInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ab66acc6-c95c-5bc7-a46b-cff12e5caaa4

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_globalSections_chartAlgFin_inf_chartAlgInf

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_globalSections_chartAlgFin_inf_chartAlgInf.AlgebraicCurve.TwoChartIntegralModel"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "coe_chartIncl chartAlgFin chartAlgInf chartAlgMid inclFin inclInf XFin XInf fFin fInf ιFin ιInf glue_condition toBase ιFin_toBase"
namespace H0GammaAux
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

abbrev eFin := Scheme.ΓSpecIso (CommRingCat.of (chartAlgFin R F j))
abbrev eInf := Scheme.ΓSpecIso (CommRingCat.of (chartAlgInf R F j))
abbrev eMid := Scheme.ΓSpecIso (CommRingCat.of (chartAlgMid R F j))

theorem appTop_glue :
    (ιFin R F j).appTop ≫ (fFin R F j).appTop = (ιInf R F j).appTop ≫ (fInf R F j).appTop := by
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, glue_condition]

theorem appTop_glue_apply (s : Γ(AlgebraicCurve.TwoChartIntegralModel R F j, ⊤)) :
    (fFin R F j).appTop ((ιFin R F j).appTop s) = (fInf R F j).appTop ((ιInf R F j).appTop s) := by
  have h := congrArg (fun φ => φ.hom s) (appTop_glue R F j)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h

theorem eMid_fFin (a : Γ(XFin R F j, ⊤)) :
    (eMid R F j).hom ((fFin R F j).appTop a) = inclFin R F j ((eFin R F j).hom a) := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (inclFin R F j).toRingHom)
  have h2 := congrArg (fun φ => φ.hom a) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2

theorem eMid_fInf (a : Γ(XInf R F j, ⊤)) :
    (eMid R F j).hom ((fInf R F j).appTop a) = inclInf R F j ((eInf R F j).hom a) := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (inclInf R F j).toRingHom)
  have h2 := congrArg (fun φ => φ.hom a) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2

theorem coe_res_eq (s : Γ(AlgebraicCurve.TwoChartIntegralModel R F j, ⊤)) :
    (((eFin R F j).hom ((ιFin R F j).appTop s) : chartAlgFin R F j) : F) =
      (((eInf R F j).hom ((ιInf R F j).appTop s) : chartAlgInf R F j) : F) := by
  have h1 := congrArg (fun a => (eMid R F j).hom a) (appTop_glue_apply R F j s)
  simp only at h1
  rw [eMid_fFin, eMid_fInf] at h1
  have h2 := congrArg (fun x : chartAlgMid R F j => (x : F)) h1
  simpa only [coe_chartIncl] using h2

def toInf : Γ(AlgebraicCurve.TwoChartIntegralModel R F j, ⊤) →+* ↥(chartAlgFin R F j ⊓ chartAlgInf R F j) :=
  RingHom.codRestrict
    ((chartAlgFin R F j).val.toRingHom.comp ((ιFin R F j).appTop ≫ (eFin R F j).hom).hom)
    (chartAlgFin R F j ⊓ chartAlgInf R F j)
    (fun s => by
      have hs : ((chartAlgFin R F j).val.toRingHom.comp ((ιFin R F j).appTop ≫ (eFin R F j).hom).hom) s
          = (((eFin R F j).hom ((ιFin R F j).appTop s) : chartAlgFin R F j) : F) := by
        simp only [RingHom.comp_apply, CommRingCat.hom_comp, AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom, Subalgebra.coe_val]
      rw [hs]
      refine Algebra.mem_inf.mpr ⟨((eFin R F j).hom ((ιFin R F j).appTop s)).2, ?_⟩
      rw [coe_res_eq]
      exact ((eInf R F j).hom ((ιInf R F j).appTop s)).2)

theorem coe_toInf (s : Γ(AlgebraicCurve.TwoChartIntegralModel R F j, ⊤)) :
    ((toInf R F j s : ↥(chartAlgFin R F j ⊓ chartAlgInf R F j)) : F) =
      (((eFin R F j).hom ((ιFin R F j).appTop s) : chartAlgFin R F j) : F) := by
  simp only [toInf, RingHom.codRestrict_apply, RingHom.comp_apply, CommRingCat.hom_comp,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Subalgebra.coe_val]

theorem coe_toInf' (s : Γ(AlgebraicCurve.TwoChartIntegralModel R F j, ⊤)) :
    ((toInf R F j s : ↥(chartAlgFin R F j ⊓ chartAlgInf R F j)) : F) =
      (((eInf R F j).hom ((ιInf R F j).appTop s) : chartAlgInf R F j) : F) := by
  rw [coe_toInf, coe_res_eq]

theorem isPullback_appTop :
    IsPullback (ιInf R F j).appTop (ιFin R F j).appTop (fInf R F j).appTop (fFin R F j).appTop := by
  have h := (IsPushout.of_hasPushout (fFin R F j) (fInf R F j)).op.map Scheme.Γ
  simp only [Scheme.Γ_map_op] at h
  exact h

abbrev PB := CommRingCat.pullbackCone (fInf R F j).appTop (fFin R F j).appTop

def isoPB : Γ(AlgebraicCurve.TwoChartIntegralModel R F j, ⊤) ≅ (PB R F j).pt :=
  (isPullback_appTop R F j).isLimit.conePointUniqueUpToIso (CommRingCat.pullbackConeIsLimit _ _)

theorem isoPB_fst (s : Γ(AlgebraicCurve.TwoChartIntegralModel R F j, ⊤)) :
    ((isoPB R F j).hom s).1.1 = (ιInf R F j).appTop s := by
  have h := (isPullback_appTop R F j).isLimit.conePointUniqueUpToIso_hom_comp
    (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.left
  have h2 := congrArg (fun φ => φ.hom s) h
  exact h2

theorem isoPB_snd (s : Γ(AlgebraicCurve.TwoChartIntegralModel R F j, ⊤)) :
    ((isoPB R F j).hom s).1.2 = (ιFin R F j).appTop s := by
  have h := (isPullback_appTop R F j).isLimit.conePointUniqueUpToIso_hom_comp
    (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.right
  have h2 := congrArg (fun φ => φ.hom s) h
  exact h2

theorem toInf_injective : Function.Injective (toInf R F j) := by
  intro s t hst
  have hF : (((eFin R F j).hom ((ιFin R F j).appTop s) : chartAlgFin R F j) : F) =
      (((eFin R F j).hom ((ιFin R F j).appTop t) : chartAlgFin R F j) : F) := by
    rw [← coe_toInf, ← coe_toInf, hst]
  have hI : (((eInf R F j).hom ((ιInf R F j).appTop s) : chartAlgInf R F j) : F) =
      (((eInf R F j).hom ((ιInf R F j).appTop t) : chartAlgInf R F j) : F) := by
    rw [← coe_toInf', ← coe_toInf', hst]
  have hF' : (ιFin R F j).appTop s = (ιFin R F j).appTop t :=
    (eFin R F j).commRingCatIsoToRingEquiv.injective (Subtype.ext hF)
  have hI' : (ιInf R F j).appTop s = (ιInf R F j).appTop t :=
    (eInf R F j).commRingCatIsoToRingEquiv.injective (Subtype.ext hI)
  apply (isoPB R F j).commRingCatIsoToRingEquiv.injective
  refine Subtype.ext (Prod.ext ?_ ?_)
  · change ((isoPB R F j).hom s).1.1 = ((isoPB R F j).hom t).1.1
    rw [isoPB_fst, isoPB_fst, hI']
  · change ((isoPB R F j).hom s).1.2 = ((isoPB R F j).hom t).1.2
    rw [isoPB_snd, isoPB_snd, hF']

theorem toInf_surjective : Function.Surjective (toInf R F j) := by
  intro x
  obtain ⟨hxF, hxI⟩ := Algebra.mem_inf.mp x.2

  let a : Γ(XInf R F j, ⊤) := (eInf R F j).inv ⟨x, hxI⟩
  let b : Γ(XFin R F j, ⊤) := (eFin R F j).inv ⟨x, hxF⟩
  have hab : (fInf R F j).appTop a = (fFin R F j).appTop b := by
    apply (eMid R F j).commRingCatIsoToRingEquiv.injective
    change (eMid R F j).hom ((fInf R F j).appTop a) = (eMid R F j).hom ((fFin R F j).appTop b)
    rw [eMid_fInf, eMid_fFin]
    apply Subtype.ext
    rw [coe_chartIncl, coe_chartIncl]
    change (((eInf R F j).hom ((eInf R F j).inv ⟨x, hxI⟩) : chartAlgInf R F j) : F) =
      (((eFin R F j).hom ((eFin R F j).inv ⟨x, hxF⟩) : chartAlgFin R F j) : F)
    rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  let p : (PB R F j).pt := ⟨(a, b), hab⟩
  refine ⟨(isoPB R F j).inv p, Subtype.ext ?_⟩
  rw [coe_toInf]
  have h2 : (ιFin R F j).appTop ((isoPB R F j).inv p) = b := by
    have := isoPB_snd R F j ((isoPB R F j).inv p)
    rw [Iso.inv_hom_id_apply] at this
    exact this.symm
  rw [h2]
  change (((eFin R F j).hom ((eFin R F j).inv ⟨x, hxF⟩) : chartAlgFin R F j) : F) = x
  rw [Iso.inv_hom_id_apply]

def ringEquiv : Γ(AlgebraicCurve.TwoChartIntegralModel R F j, ⊤) ≃+* ↥(chartAlgFin R F j ⊓ chartAlgInf R F j) :=
  RingEquiv.ofBijective (toInf R F j) ⟨toInf_injective R F j, toInf_surjective R F j⟩

theorem appLE_top_eq_appTop {Y : Scheme.{u}} (c : Y ⟶ Spec (.of R)) : c.appLE ⊤ ⊤ le_top = c.appTop := by
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop]

theorem toInf_algebraMap (r : R) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase R F j) ⊤
    toInf R F j (algebraMap R _ r) = algebraMap R _ r := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase R F j) ⊤
  apply Subtype.ext
  rw [coe_toInf, Subalgebra.coe_algebraMap]
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, appLE_top_eq_appTop]
  have h1 : (ιFin R F j).appTop ((toBase R F j).appTop ((Scheme.ΓSpecIso (.of R)).inv r)) =
      (Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgFin R F j)))).appTop
        ((Scheme.ΓSpecIso (.of R)).inv r) := by
    have := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of R)).inv r))
      (show (toBase R F j).appTop ≫ (ιFin R F j).appTop =
        (Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgFin R F j)))).appTop by
        rw [← Scheme.Hom.comp_appTop, ιFin_toBase])
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  rw [h1]
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (chartAlgFin R F j)))
  have h3 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of R)).inv r)) h2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
  rw [h3, Iso.inv_hom_id_apply, Subalgebra.coe_algebraMap]

end AlgebraicCurve.TwoChartIntegralModel.H0GammaAux

end

open AlgebraicCurve.TwoChartIntegralModel.H0GammaAux in

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase R F j) ⊤
    ∃ e : Γ(AlgebraicCurve.TwoChartIntegralModel R F j, ⊤) ≃ₐ[R]
        ↥(chartAlgFin R F j ⊓ chartAlgInf R F j),
      (∀ s, ((e s : ↥(chartAlgFin R F j ⊓ chartAlgInf R F j)) : F) =
        ((Scheme.ΓSpecIso (CommRingCat.of (chartAlgFin R F j))).hom ((ιFin R F j).appTop s) :
          chartAlgFin R F j)) ∧
      (∀ s, ((e s : ↥(chartAlgFin R F j ⊓ chartAlgInf R F j)) : F) =
        ((Scheme.ΓSpecIso (CommRingCat.of (chartAlgInf R F j))).hom ((ιInf R F j).appTop s) :
          chartAlgInf R F j)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase R F j) ⊤
  refine ⟨AlgEquiv.ofRingEquiv (f := ringEquiv R F j) (toInf_algebraMap R F j), fun s => ?_, fun s => ?_⟩
  · exact coe_toInf R F j s
  · exact coe_toInf' R F j s

end S_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_globalSections_chartAlgFin_inf_chartAlgInf
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_globalSections_chartAlgFin_inf_chartAlgInf (solution)
