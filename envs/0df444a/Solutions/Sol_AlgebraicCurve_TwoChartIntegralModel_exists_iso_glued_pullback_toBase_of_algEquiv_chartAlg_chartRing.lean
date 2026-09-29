-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_iso_glued_pullback_toBase_of_algEquiv_chartAlg_chartRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/8d49226c-1300-520c-96ff-7838847a5bfe

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_glued_pullback_toBase_of_algEquiv_chartAlg_chartRing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.CurveModel

open scoped TensorProduct

universe u

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace SPISO

theorem coe_jChartFin' (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    ((TwoChartIntegralModel.jChartFin R F j : ↥(TwoChartIntegralModel.chartAlgFin R F j)) : F) = j := rfl

theorem coe_jInvChartInf' (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    ((TwoChartIntegralModel.jInvChartInf R F j : ↥(TwoChartIntegralModel.chartAlgInf R F j)) : F) = j⁻¹ := rfl

structure GlueDatum (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] (K : Type u) [Field K]
    [Algebra R K] {L : Type u} [Field L] [Algebra K L] (t : L) where
  θFin : ↥(TwoChartIntegralModel.chartAlgFin R F j) ⊗[R] K →+* ↥(chartRing K ({t} : Set L))
  θInf : ↥(TwoChartIntegralModel.chartAlgInf R F j) ⊗[R] K →+* ↥(chartRing K ({t⁻¹} : Set L))
  ρMid : ↥(TwoChartIntegralModel.chartAlgMid R F j) →+* ↥(chartRing K ({t, t⁻¹} : Set L))
  θFin_right : θFin.comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
      K →ₐ[R] ↥(TwoChartIntegralModel.chartAlgFin R F j) ⊗[R] K)) =
    algebraMap K ↥(chartRing K ({t} : Set L))
  θInf_right : θInf.comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
      K →ₐ[R] ↥(TwoChartIntegralModel.chartAlgInf R F j) ⊗[R] K)) =
    algebraMap K ↥(chartRing K ({t⁻¹} : Set L))
  sq_fin : (incl₀ K t).toRingHom.comp (θFin.comp Algebra.TensorProduct.includeLeftRingHom) =
    ρMid.comp (TwoChartIntegralModel.inclFin R F j).toRingHom
  sq_inf : (inclInf K t).toRingHom.comp (θInf.comp Algebra.TensorProduct.includeLeftRingHom) =
    ρMid.comp (TwoChartIntegralModel.inclInf R F j).toRingHom
  ρInf_jInv : (θInf.comp Algebra.TensorProduct.includeLeftRingHom) (TwoChartIntegralModel.jInvChartInf R F j) = tInvChart K t
  bijFin : Function.Bijective θFin
  bijInf : Function.Bijective θInf

abbrev baseMap (R : Type u) [CommRing R] (K : Type u) [Field K] [Algebra R K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

section Igusa

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

private theorem ig_ιFin_eq_ιInf_iff (x₀ : TwoChartIntegralModel.XFin R F j) (xi : TwoChartIntegralModel.XInf R F j) :
    (TwoChartIntegralModel.ιFin R F j).base x₀ = (TwoChartIntegralModel.ιInf R F j).base xi ↔
      ∃ w : TwoChartIntegralModel.XMid R F j,
        (TwoChartIntegralModel.fFin R F j).base w = x₀ ∧ (TwoChartIntegralModel.fInf R F j).base w = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (F := span (TwoChartIntegralModel.fFin R F j) (TwoChartIntegralModel.fInf R F j))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · exact match fi, fj, h₁, h₂ with
        | .init _, .init _, h₁, h₂ => ⟨w, h₁, h₂⟩
    · exact nomatch fj
    · exact nomatch fi
  · rintro ⟨w, rfl, rfl⟩
    change (TwoChartIntegralModel.fFin R F j ≫ TwoChartIntegralModel.ιFin R F j).base w =
      (TwoChartIntegralModel.fInf R F j ≫ TwoChartIntegralModel.ιInf R F j).base w
    rw [TwoChartIntegralModel.glue_condition]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem ig_range_fInf : Set.range (TwoChartIntegralModel.fInf R F j).base =
    ((PrimeSpectrum.basicOpen (TwoChartIntegralModel.jInvChartInf R F j) :
        TopologicalSpace.Opens (PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgInf R F j))) : Set (PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgInf R F j))) := by
  letI := (TwoChartIntegralModel.inclInf R F j).toRingHom.toAlgebra
  haveI := TwoChartIntegralModel.isLocalization_away_inclInf R F j
  exact PrimeSpectrum.localization_away_comap_range ↥(TwoChartIntegralModel.chartAlgMid R F j) (TwoChartIntegralModel.jInvChartInf R F j)

private theorem ig_ιInf_mem_range_ιFin_iff (xi : TwoChartIntegralModel.XInf R F j) :
    (TwoChartIntegralModel.ιInf R F j).base xi ∈ Set.range (TwoChartIntegralModel.ιFin R F j).base ↔
      TwoChartIntegralModel.jInvChartInf R F j ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← ig_range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨w, -, hw⟩ := (ig_ιFin_eq_ιInf_iff R F j x₀ xi).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(TwoChartIntegralModel.fFin R F j).base w, (ig_ιFin_eq_ιInf_iff R F j _ _).mpr ⟨w, rfl, rfl⟩⟩

end Igusa

section Schemes

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)] {K : Type u} [Field K]
  [Algebra R K] {L : Type u} [Field L] [Algebra K L] {t : L} [Fact (t ≠ 0)]
  (D : GlueDatum R F j K t)

abbrev GlueDatum.ρFin : ↥(TwoChartIntegralModel.chartAlgFin R F j) →+* ↥(chartRing K ({t} : Set L)) :=
  D.θFin.comp Algebra.TensorProduct.includeLeftRingHom

abbrev GlueDatum.ρInf : ↥(TwoChartIntegralModel.chartAlgInf R F j) →+* ↥(chartRing K ({t⁻¹} : Set L)) :=
  D.θInf.comp Algebra.TensorProduct.includeLeftRingHom

private theorem ρFin_comp_algebraMap :
    D.ρFin.comp (algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j)) =
      (algebraMap K ↥(chartRing K ({t} : Set L))).comp (algebraMap R K) := by
  refine RingHom.ext fun q => ?_
  have h1 : (Algebra.TensorProduct.includeLeftRingHom (algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) q) :
      ↥(TwoChartIntegralModel.chartAlgFin R F j) ⊗[R] K) =
      (1 : ↥(TwoChartIntegralModel.chartAlgFin R F j)) ⊗ₜ[R] (algebraMap R K q) := by
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  have h2 := RingHom.congr_fun D.θFin_right (algebraMap R K q)
  show D.θFin (Algebra.TensorProduct.includeLeftRingHom (algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j) q)) =
    algebraMap K ↥(chartRing K ({t} : Set L)) (algebraMap R K q)
  rw [h1, ← h2]
  rfl

private theorem ρInf_comp_algebraMap :
    D.ρInf.comp (algebraMap R ↥(TwoChartIntegralModel.chartAlgInf R F j)) =
      (algebraMap K ↥(chartRing K ({t⁻¹} : Set L))).comp (algebraMap R K) := by
  refine RingHom.ext fun q => ?_
  have h1 : (Algebra.TensorProduct.includeLeftRingHom (algebraMap R ↥(TwoChartIntegralModel.chartAlgInf R F j) q) :
      ↥(TwoChartIntegralModel.chartAlgInf R F j) ⊗[R] K) =
      (1 : ↥(TwoChartIntegralModel.chartAlgInf R F j)) ⊗ₜ[R] (algebraMap R K q) := by
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  have h2 := RingHom.congr_fun D.θInf_right (algebraMap R K q)
  show D.θInf (Algebra.TensorProduct.includeLeftRingHom (algebraMap R ↥(TwoChartIntegralModel.chartAlgInf R F j) q)) =
    algebraMap K ↥(chartRing K ({t⁻¹} : Set L)) (algebraMap R K q)
  rw [h1, ← h2]
  rfl

private abbrev uFin : X₀ K t ⟶ TwoChartIntegralModel.XFin R F j := Spec.map (CommRingCat.ofHom D.ρFin)

private abbrev uInf : CurveModel.XInf K t ⟶ TwoChartIntegralModel.XInf R F j :=
  Spec.map (CommRingCat.ofHom D.ρInf)

private abbrev uMid : XOverlap K t ⟶ TwoChartIntegralModel.XMid R F j := Spec.map (CommRingCat.ofHom D.ρMid)

private theorem f₀_uFin : f₀ K t ≫ uFin D = uMid D ≫ TwoChartIntegralModel.fFin R F j := by
  simp only [f₀, uFin, uMid, TwoChartIntegralModel.fFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) D.sq_fin

private theorem fInf_uInf : CurveModel.fInf K t ≫ uInf D = uMid D ≫ TwoChartIntegralModel.fInf R F j := by
  simp only [CurveModel.fInf, uInf, uMid, TwoChartIntegralModel.fInf, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) D.sq_inf

private theorem glue_compat :
    f₀ K t ≫ (uFin D ≫ TwoChartIntegralModel.ιFin R F j) =
      CurveModel.fInf K t ≫ (uInf D ≫ TwoChartIntegralModel.ιInf R F j) := by
  rw [← Category.assoc, f₀_uFin, ← Category.assoc, fInf_uInf, Category.assoc, Category.assoc,
    TwoChartIntegralModel.glue_condition]

private def u : glued K t ⟶ TwoChartIntegralModel R F j :=
  pushout.desc (uFin D ≫ TwoChartIntegralModel.ιFin R F j) (uInf D ≫ TwoChartIntegralModel.ιInf R F j)
    (glue_compat D)

@[reassoc]
private theorem ι₀_u : ι₀ K t ≫ u D = uFin D ≫ TwoChartIntegralModel.ιFin R F j :=
  pushout.inl_desc _ _ _

@[reassoc]
private theorem ιInf_u : CurveModel.ιInf K t ≫ u D = uInf D ≫ TwoChartIntegralModel.ιInf R F j :=
  pushout.inr_desc _ _ _

private theorem uFin_base :
    uFin D ≫ Spec.map (CommRingCat.ofHom (algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j))) =
      Spec.map (CommRingCat.ofHom (algebraMap K ↥(chartRing K ({t} : Set L)))) ≫ baseMap R K := by
  simp only [uFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (ρFin_comp_algebraMap D)

private theorem uInf_base :
    uInf D ≫ Spec.map (CommRingCat.ofHom (algebraMap R ↥(TwoChartIntegralModel.chartAlgInf R F j))) =
      Spec.map (CommRingCat.ofHom (algebraMap K ↥(chartRing K ({t⁻¹} : Set L)))) ≫ baseMap R K := by
  simp only [uInf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (ρInf_comp_algebraMap D)

private theorem u_igusaTo : u D ≫ TwoChartIntegralModel.toBase R F j = gluedToBase K t ≫ baseMap R K := by
  refine pushout.hom_ext (f := f₀ K t) (g := CurveModel.fInf K t) ?_ ?_
  · change ι₀ K t ≫ u D ≫ TwoChartIntegralModel.toBase R F j = ι₀ K t ≫ gluedToBase K t ≫ baseMap R K
    rw [ι₀_u_assoc, TwoChartIntegralModel.ιFin_toBase, uFin_base, ι₀_gluedToBase_assoc]
  · change CurveModel.ιInf K t ≫ u D ≫ TwoChartIntegralModel.toBase R F j =
      CurveModel.ιInf K t ≫ gluedToBase K t ≫ baseMap R K
    rw [ιInf_u_assoc, TwoChartIntegralModel.ιInf_toBase, uInf_base, ιInf_gluedToBase_assoc]

def es : glued K t ⟶ pullback (TwoChartIntegralModel.toBase R F j) (baseMap R K) :=
  pullback.lift (u D) (gluedToBase K t) (u_igusaTo D)

@[reassoc (attr := simp)]
private theorem es_fst : es D ≫ pullback.fst (TwoChartIntegralModel.toBase R F j) (baseMap R K) = u D := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem es_snd : es D ≫ pullback.snd (TwoChartIntegralModel.toBase R F j) (baseMap R K) = gluedToBase K t :=
  pullback.lift_snd _ _ _

theorem ι₀_es_fst :
    ι₀ K t ≫ es D ≫ pullback.fst (TwoChartIntegralModel.toBase R F j) (baseMap R K) =
      uFin D ≫ TwoChartIntegralModel.ιFin R F j := by
  rw [es_fst, ι₀_u]

theorem ιInf_es_fst :
    CurveModel.ιInf K t ≫ es D ≫ pullback.fst (TwoChartIntegralModel.toBase R F j) (baseMap R K) =
      uInf D ≫ TwoChartIntegralModel.ιInf R F j := by
  rw [es_fst, ιInf_u]

private theorem uInf_asIdeal (z : CurveModel.XInf K t) :
    ((uInf D).base z).asIdeal = z.asIdeal.comap D.ρInf := rfl

private theorem u_mem_range_ιFin_iff (y : glued K t) :
    (u D).base y ∈ Set.range (TwoChartIntegralModel.ιFin R F j).base ↔ y ∈ Set.range (ι₀ K t).base := by
  rcases mem_range_ι₀_or_mem_range_ιInf K t y with ⟨x₀, rfl⟩ | ⟨z, rfl⟩
  · refine ⟨fun _ => ⟨x₀, rfl⟩, fun _ => ⟨(uFin D).base x₀, ?_⟩⟩
    change (uFin D ≫ TwoChartIntegralModel.ιFin R F j).base x₀ = (ι₀ K t ≫ u D).base x₀
    rw [ι₀_u]
  · have hz : (u D).base ((CurveModel.ιInf K t).base z) =
        (TwoChartIntegralModel.ιInf R F j).base ((uInf D).base z) := by
      change (CurveModel.ιInf K t ≫ u D).base z = (uInf D ≫ TwoChartIntegralModel.ιInf R F j).base z
      rw [ιInf_u]
    rw [hz, ig_ιInf_mem_range_ιFin_iff, ιInf_mem_range_ι₀_iff, uInf_asIdeal, Ideal.mem_comap]
    exact not_congr (iff_of_eq (congrArg (· ∈ z.asIdeal) D.ρInf_jInv))

theorem es_fst_mem_range_ιFin_iff (y : glued K t) :
    (es D ≫ pullback.fst (TwoChartIntegralModel.toBase R F j) (baseMap R K)).base y ∈
        Set.range (TwoChartIntegralModel.ιFin R F j).base ↔ y ∈ Set.range (ι₀ K t).base := by
  rw [es_fst]; exact u_mem_range_ιFin_iff D y

private abbrev PFin (_D : GlueDatum R F j K t) := pullback (TwoChartIntegralModel.ιFin R F j) (pullback.fst (TwoChartIntegralModel.toBase R F j) (baseMap R K))

private abbrev PInf (_D : GlueDatum R F j K t) := pullback (TwoChartIntegralModel.ιInf R F j) (pullback.fst (TwoChartIntegralModel.toBase R F j) (baseMap R K))

private def φFin : X₀ K t ⟶ PFin D :=
  pullback.lift (uFin D) (ι₀ K t ≫ es D) (by rw [Category.assoc, ι₀_es_fst])

private def φInf : CurveModel.XInf K t ⟶ PInf D :=
  pullback.lift (uInf D) (CurveModel.ιInf K t ≫ es D) (by rw [Category.assoc, ιInf_es_fst])

@[reassoc (attr := simp)]
private theorem φFin_fst : φFin D ≫ pullback.fst _ _ = uFin D := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem φFin_snd : φFin D ≫ pullback.snd _ _ = ι₀ K t ≫ es D := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
private theorem φInf_fst : φInf D ≫ pullback.fst _ _ = uInf D := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem φInf_snd : φInf D ≫ pullback.snd _ _ = CurveModel.ιInf K t ≫ es D := pullback.lift_snd _ _ _

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem SpecMap_θFin_eq :
    Spec.map (CommRingCat.ofHom D.θFin) ≫
        (pullbackSpecIso R ↥(TwoChartIntegralModel.chartAlgFin R F j) K).inv =
      φFin D ≫ (pullbackRightPullbackFstIso (TwoChartIntegralModel.toBase R F j) (baseMap R K) (TwoChartIntegralModel.ιFin R F j)).hom ≫
        (pullback.congrHom (TwoChartIntegralModel.ιFin_toBase R F j) rfl).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, φFin_fst]
    try rfl
  · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [D.θFin_right]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd, φFin_snd_assoc, es_snd, ι₀_gluedToBase]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem SpecMap_θInf_eq :
    Spec.map (CommRingCat.ofHom D.θInf) ≫
        (pullbackSpecIso R ↥(TwoChartIntegralModel.chartAlgInf R F j) K).inv =
      φInf D ≫ (pullbackRightPullbackFstIso (TwoChartIntegralModel.toBase R F j) (baseMap R K) (TwoChartIntegralModel.ιInf R F j)).hom ≫
        (pullback.congrHom (TwoChartIntegralModel.ιInf_toBase R F j) rfl).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, φInf_fst]
    try rfl
  · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [D.θInf_right]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd, φInf_snd_assoc, es_snd, ιInf_gluedToBase]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isIso_φFin : IsIso (φFin D) := by
  haveI : IsIso (Spec.map (CommRingCat.ofHom D.θFin)) := isIso_SpecMap_iff.mpr D.bijFin
  haveI : IsIso (φFin D ≫
      (pullbackRightPullbackFstIso (TwoChartIntegralModel.toBase R F j) (baseMap R K) (TwoChartIntegralModel.ιFin R F j)).hom ≫
        (pullback.congrHom (TwoChartIntegralModel.ιFin_toBase R F j) rfl).hom) := by
    rw [← SpecMap_θFin_eq]
    infer_instance
  exact IsIso.of_isIso_comp_right (φFin D)
    ((pullbackRightPullbackFstIso (TwoChartIntegralModel.toBase R F j) (baseMap R K) (TwoChartIntegralModel.ιFin R F j)).hom ≫
      (pullback.congrHom (TwoChartIntegralModel.ιFin_toBase R F j) rfl).hom)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isIso_φInf : IsIso (φInf D) := by
  haveI : IsIso (Spec.map (CommRingCat.ofHom D.θInf)) := isIso_SpecMap_iff.mpr D.bijInf
  haveI : IsIso (φInf D ≫
      (pullbackRightPullbackFstIso (TwoChartIntegralModel.toBase R F j) (baseMap R K) (TwoChartIntegralModel.ιInf R F j)).hom ≫
        (pullback.congrHom (TwoChartIntegralModel.ιInf_toBase R F j) rfl).hom) := by
    rw [← SpecMap_θInf_eq]
    infer_instance
  exact IsIso.of_isIso_comp_right (φInf D)
    ((pullbackRightPullbackFstIso (TwoChartIntegralModel.toBase R F j) (baseMap R K) (TwoChartIntegralModel.ιInf R F j)).hom ≫
      (pullback.congrHom (TwoChartIntegralModel.ιInf_toBase R F j) rfl).hom)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isOpenImmersion_ι₀_es : IsOpenImmersion (ι₀ K t ≫ es D) := by
  haveI := isIso_φFin D
  rw [← φFin_snd]
  infer_instance

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isOpenImmersion_ιInf_es : IsOpenImmersion (CurveModel.ιInf K t ≫ es D) := by
  haveI := isIso_φInf D
  rw [← φInf_snd]
  infer_instance

set_option synthInstance.maxHeartbeats 1600000 in

private theorem u_eq_of_es_eq {y y' : glued K t} (h : es D y = es D y') : u D y = u D y' := by
  have h1 := congrArg (pullback.fst (TwoChartIntegralModel.toBase R F j) (baseMap R K)) h
  rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, es_fst] at h1

set_option synthInstance.maxHeartbeats 1600000 in
private theorem injective_es : Function.Injective (es D) := by
  intro y y' h
  have hu := u_eq_of_es_eq D h
  have hu' : (u D).base y = (u D).base y' := hu
  have hsame : y ∈ Set.range (ι₀ K t).base ↔ y' ∈ Set.range (ι₀ K t).base := by
    rw [← u_mem_range_ιFin_iff D y, ← u_mem_range_ιFin_iff D y', hu']
  by_cases hy : y ∈ Set.range (ι₀ K t).base
  · obtain ⟨a, rfl⟩ := hy
    obtain ⟨a', rfl⟩ := hsame.mp ⟨a, rfl⟩
    haveI := isOpenImmersion_ι₀_es D
    have : (ι₀ K t ≫ es D) a = (ι₀ K t ≫ es D) a' := h
    rw [(ι₀ K t ≫ es D).isOpenEmbedding.injective this]
  · have hy' : y' ∉ Set.range (ι₀ K t).base := fun h' => hy (hsame.mpr h')
    obtain ⟨a, rfl⟩ := (mem_range_ι₀_or_mem_range_ιInf K t y).resolve_left hy
    obtain ⟨a', rfl⟩ := (mem_range_ι₀_or_mem_range_ιInf K t y').resolve_left hy'
    haveI := isOpenImmersion_ιInf_es D
    have : (CurveModel.ιInf K t ≫ es D) a = (CurveModel.ιInf K t ≫ es D) a' := h
    rw [(CurveModel.ιInf K t ≫ es D).isOpenEmbedding.injective this]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem surjective_es : Function.Surjective (es D) := by
  intro p
  rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf R F j (pullback.fst (TwoChartIntegralModel.toBase R F j) (baseMap R K) p) with hp | hp
  · have hp' : p ∈ Set.range (pullback.snd (TwoChartIntegralModel.ιFin R F j)
        (pullback.fst (TwoChartIntegralModel.toBase R F j) (baseMap R K))) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact hp
    obtain ⟨r, rfl⟩ := hp'
    haveI := isIso_φFin D
    obtain ⟨a, rfl⟩ := (φFin D).homeomorph.surjective r
    exact ⟨ι₀ K t a, by
      show (ι₀ K t ≫ es D) a = (φFin D ≫ pullback.snd _ _) a
      rw [φFin_snd]⟩
  · have hp' : p ∈ Set.range (pullback.snd (TwoChartIntegralModel.ιInf R F j)
        (pullback.fst (TwoChartIntegralModel.toBase R F j) (baseMap R K))) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact hp
    obtain ⟨r, rfl⟩ := hp'
    haveI := isIso_φInf D
    obtain ⟨a, rfl⟩ := (φInf D).homeomorph.surjective r
    exact ⟨CurveModel.ιInf K t a, by
      show (CurveModel.ιInf K t ≫ es D) a = (φInf D ≫ pullback.snd _ _) a
      rw [φInf_snd]⟩

set_option synthInstance.maxHeartbeats 1600000 in

theorem isIso_es : IsIso (es D) := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨?_, ⟨surjective_es D⟩⟩
  refine IsOpenImmersion.of_forall_source_exists _ (injective_es D) fun y => ?_
  rcases mem_range_ι₀_or_mem_range_ιInf K t y with hy | hy
  · exact ⟨_, ι₀ K t, inferInstance, hy, isOpenImmersion_ι₀_es D⟩
  · exact ⟨_, CurveModel.ιInf K t, inferInstance, hy, isOpenImmersion_ιInf_es D⟩

end Schemes

section Datum

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)] {K : Type u} [Field K]
  [Algebra R K] {L : Type u} [Field L] [Algebra K L] {t : L}

variable
  (eFin : K ⊗[R] ↥(TwoChartIntegralModel.chartAlgFin R F j) ≃ₐ[K] ↥(chartRing K ({t} : Set L)))
  (eInf : K ⊗[R] ↥(TwoChartIntegralModel.chartAlgInf R F j) ≃ₐ[K] ↥(chartRing K ({t⁻¹} : Set L)))

private def θF : ↥(TwoChartIntegralModel.chartAlgFin R F j) ⊗[R] K →+* ↥(chartRing K ({t} : Set L)) :=
  (eFin : K ⊗[R] ↥(TwoChartIntegralModel.chartAlgFin R F j) →+* ↥(chartRing K ({t} : Set L))).comp
    (RingHomClass.toRingHom
      (Algebra.TensorProduct.comm R ↥(TwoChartIntegralModel.chartAlgFin R F j) K))

private def θI : ↥(TwoChartIntegralModel.chartAlgInf R F j) ⊗[R] K →+* ↥(chartRing K ({t⁻¹} : Set L)) :=
  (eInf : K ⊗[R] ↥(TwoChartIntegralModel.chartAlgInf R F j) →+* ↥(chartRing K ({t⁻¹} : Set L))).comp
    (RingHomClass.toRingHom
      (Algebra.TensorProduct.comm R ↥(TwoChartIntegralModel.chartAlgInf R F j) K))

private theorem θF_tmul (b : ↥(TwoChartIntegralModel.chartAlgFin R F j)) (x : K) :
    θF eFin (b ⊗ₜ[R] x) = eFin (x ⊗ₜ[R] b) := by
  show eFin (Algebra.TensorProduct.comm R ↥(TwoChartIntegralModel.chartAlgFin R F j) K (b ⊗ₜ x)) = _
  rw [Algebra.TensorProduct.comm_tmul]

private theorem θI_tmul (b : ↥(TwoChartIntegralModel.chartAlgInf R F j)) (x : K) :
    θI eInf (b ⊗ₜ[R] x) = eInf (x ⊗ₜ[R] b) := by
  show eInf (Algebra.TensorProduct.comm R ↥(TwoChartIntegralModel.chartAlgInf R F j) K (b ⊗ₜ x)) = _
  rw [Algebra.TensorProduct.comm_tmul]

private theorem θF_right :
    (θF eFin).comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
      K →ₐ[R] ↥(TwoChartIntegralModel.chartAlgFin R F j) ⊗[R] K)) =
    algebraMap K ↥(chartRing K ({t} : Set L)) := by
  refine RingHom.ext fun x => ?_
  show θF eFin ((1 : ↥(TwoChartIntegralModel.chartAlgFin R F j)) ⊗ₜ[R] x) = _
  rw [θF_tmul]
  have hx : (x ⊗ₜ[R] (1 : ↥(TwoChartIntegralModel.chartAlgFin R F j)) :
      K ⊗[R] ↥(TwoChartIntegralModel.chartAlgFin R F j)) = algebraMap K _ x := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  rw [hx, AlgEquiv.commutes]

private theorem θI_right :
    (θI eInf).comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
      K →ₐ[R] ↥(TwoChartIntegralModel.chartAlgInf R F j) ⊗[R] K)) =
    algebraMap K ↥(chartRing K ({t⁻¹} : Set L)) := by
  refine RingHom.ext fun x => ?_
  show θI eInf ((1 : ↥(TwoChartIntegralModel.chartAlgInf R F j)) ⊗ₜ[R] x) = _
  rw [θI_tmul]
  have hx : (x ⊗ₜ[R] (1 : ↥(TwoChartIntegralModel.chartAlgInf R F j)) :
      K ⊗[R] ↥(TwoChartIntegralModel.chartAlgInf R F j)) = algebraMap K _ x := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  rw [hx, AlgEquiv.commutes]

private theorem θF_includeLeft (b : ↥(TwoChartIntegralModel.chartAlgFin R F j)) :
    (θF eFin).comp Algebra.TensorProduct.includeLeftRingHom b = eFin ((1 : K) ⊗ₜ[R] b) := by
  rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, θF_tmul]

private theorem θI_includeLeft (b : ↥(TwoChartIntegralModel.chartAlgInf R F j)) :
    (θI eInf).comp Algebra.TensorProduct.includeLeftRingHom b = eInf ((1 : K) ⊗ₜ[R] b) := by
  rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, θI_tmul]

private def gMid : ↥(TwoChartIntegralModel.chartAlgFin R F j) →+* ↥(chartRing K ({t, t⁻¹} : Set L)) :=
  (incl₀ K t).toRingHom.comp ((θF eFin).comp Algebra.TensorProduct.includeLeftRingHom)

private theorem coe_gMid (b : ↥(TwoChartIntegralModel.chartAlgFin R F j)) :
    (gMid (t := t) eFin b : L) = (eFin ((1 : K) ⊗ₜ[R] b) : L) := by
  show ((incl₀ K t) ((θF eFin).comp Algebra.TensorProduct.includeLeftRingHom b) : L) = _
  rw [CurveModel.coe_chartIncl, θF_includeLeft]

private theorem isUnit_gMid_j [Fact (t ≠ 0)] (hj : ((eFin ((1 : K) ⊗ₜ[R] TwoChartIntegralModel.jChartFin R F j)) : L) = t) : IsUnit (gMid (t := t) eFin (TwoChartIntegralModel.jChartFin R F j)) := by
  have h : gMid (t := t) eFin (TwoChartIntegralModel.jChartFin R F j) = incl₀ K t (tChart K t) := by
    apply Subtype.ext
    rw [coe_gMid, hj, CurveModel.coe_chartIncl, coe_tChart]
  rw [h]
  exact isUnit_incl₀_tChart K t Fact.out

private def ρM [Fact (t ≠ 0)] (hj : ((eFin ((1 : K) ⊗ₜ[R] TwoChartIntegralModel.jChartFin R F j)) : L) = t) : ↥(TwoChartIntegralModel.chartAlgMid R F j) →+* ↥(chartRing K ({t, t⁻¹} : Set L)) :=
  letI := (TwoChartIntegralModel.inclFin R F j).toRingHom.toAlgebra
  haveI := TwoChartIntegralModel.isLocalization_away_inclFin R F j
  IsLocalization.Away.lift (TwoChartIntegralModel.jChartFin R F j) (g := gMid (t := t) eFin) (isUnit_gMid_j eFin hj)

private theorem ρM_inclFin [Fact (t ≠ 0)] (hj : ((eFin ((1 : K) ⊗ₜ[R] TwoChartIntegralModel.jChartFin R F j)) : L) = t) (b : ↥(TwoChartIntegralModel.chartAlgFin R F j)) :
    ρM eFin hj (TwoChartIntegralModel.inclFin R F j b) = gMid (t := t) eFin b := by
  letI := (TwoChartIntegralModel.inclFin R F j).toRingHom.toAlgebra
  haveI := TwoChartIntegralModel.isLocalization_away_inclFin R F j
  exact IsLocalization.Away.lift_eq (TwoChartIntegralModel.jChartFin R F j) (isUnit_gMid_j eFin hj) b

private theorem _root_.SPISO.sq_fin [Fact (t ≠ 0)] (hj : ((eFin ((1 : K) ⊗ₜ[R] TwoChartIntegralModel.jChartFin R F j)) : L) = t) :
    (incl₀ K t).toRingHom.comp ((θF eFin).comp Algebra.TensorProduct.includeLeftRingHom) =
      (ρM eFin hj).comp (TwoChartIntegralModel.inclFin R F j).toRingHom :=
  RingHom.ext fun b => (ρM_inclFin eFin hj b).symm

p2m_export "SPISO" "sq_fin"

private theorem _root_.SPISO.sq_inf [Fact (t ≠ 0)] (hj : ((eFin ((1 : K) ⊗ₜ[R] TwoChartIntegralModel.jChartFin R F j)) : L) = t)
    (hcompat : ∀ (b : ↥(TwoChartIntegralModel.chartAlgFin R F j)) (b' : ↥(TwoChartIntegralModel.chartAlgInf R F j)) (n : ℕ),
      ((b : F) = (b' : F) * j ^ n) →
      ((eFin ((1 : K) ⊗ₜ[R] b) : L) =
        (eInf ((1 : K) ⊗ₜ[R] b') : L) * t ^ n)) :
    (inclInf K t).toRingHom.comp ((θI eInf).comp Algebra.TensorProduct.includeLeftRingHom) =
      (ρM eFin hj).comp (TwoChartIntegralModel.inclInf R F j).toRingHom := by
  letI := (TwoChartIntegralModel.inclFin R F j).toRingHom.toAlgebra
  haveI := TwoChartIntegralModel.isLocalization_away_inclFin R F j
  refine RingHom.ext fun b' => Subtype.ext ?_

  obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, h⟩ :=
    IsLocalization.surj (Submonoid.powers (TwoChartIntegralModel.jChartFin R F j)) (TwoChartIntegralModel.inclInf R F j b')
  have h' : (TwoChartIntegralModel.inclInf R F j b') * (TwoChartIntegralModel.inclFin R F j (TwoChartIntegralModel.jChartFin R F j)) ^ n =
      TwoChartIntegralModel.inclFin R F j b := by
    simp only [RingHom.algebraMap_toAlgebra, map_pow] at h
    exact h
  have hF : (b : F) = (b' : F) * j ^ n := by
    have := congrArg (fun z : ↥(TwoChartIntegralModel.chartAlgMid R F j) => (z : F)) h'
    simpa only [Subalgebra.coe_mul, Subalgebra.coe_pow, TwoChartIntegralModel.coe_chartIncl, SPISO.coe_jChartFin']
      using this.symm
  have hc := hcompat b b' n hF

  have hρ := congrArg (fun z : ↥(TwoChartIntegralModel.chartAlgMid R F j) => ((ρM eFin hj z : ↥(chartRing K ({t, t⁻¹} : Set L))) : L)) h'
  simp only [map_mul, map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow] at hρ
  rw [ρM_inclFin, ρM_inclFin, coe_gMid, coe_gMid, hj, hc] at hρ
  have htn : t ^ n ≠ 0 := pow_ne_zero n Fact.out
  have hmain : ((ρM eFin hj (TwoChartIntegralModel.inclInf R F j b') : ↥(chartRing K ({t, t⁻¹} : Set L))) : L) =
      (eInf ((1 : K) ⊗ₜ[R] b') : L) :=
    mul_right_cancel₀ htn hρ
  show ((inclInf K t) ((θI eInf).comp Algebra.TensorProduct.includeLeftRingHom b') : L) =
    ((ρM eFin hj (TwoChartIntegralModel.inclInf R F j b') : ↥(chartRing K ({t, t⁻¹} : Set L))) : L)
  rw [CurveModel.coe_chartIncl, θI_includeLeft, hmain]

p2m_export "SPISO" "sq_inf"

private def datum [Fact (t ≠ 0)] (hj : ((eFin ((1 : K) ⊗ₜ[R] TwoChartIntegralModel.jChartFin R F j)) : L) = t)
    (hcompat : ∀ (b : ↥(TwoChartIntegralModel.chartAlgFin R F j)) (b' : ↥(TwoChartIntegralModel.chartAlgInf R F j)) (n : ℕ),
      ((b : F) = (b' : F) * j ^ n) →
      ((eFin ((1 : K) ⊗ₜ[R] b) : L) =
        (eInf ((1 : K) ⊗ₜ[R] b') : L) * t ^ n))
    (hjInv : ((eInf ((1 : K) ⊗ₜ[R] TwoChartIntegralModel.jInvChartInf R F j)) : L) = t⁻¹) : GlueDatum R F j K t where
  θFin := θF eFin
  θInf := θI eInf
  ρMid := ρM eFin hj
  θFin_right := θF_right eFin
  θInf_right := θI_right eInf
  sq_fin := sq_fin eFin hj
  sq_inf := sq_inf eFin eInf hj hcompat
  ρInf_jInv := Subtype.ext (by rw [θI_includeLeft, hjInv, coe_tInvChart])
  bijFin := eFin.bijective.comp
    (Algebra.TensorProduct.comm R ↥(TwoChartIntegralModel.chartAlgFin R F j) K).bijective
  bijInf := eInf.bijective.comp
    (Algebra.TensorProduct.comm R ↥(TwoChartIntegralModel.chartAlgInf R F j) K).bijective

private theorem ρFin_eq :
    (θF eFin).comp Algebra.TensorProduct.includeLeftRingHom =
      eFin.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := R) (A := K) (B := ↥(TwoChartIntegralModel.chartAlgFin R F j))).toRingHom :=
  RingHom.ext fun b => θF_includeLeft eFin b

private theorem ρInf_eq :
    (θI eInf).comp Algebra.TensorProduct.includeLeftRingHom =
      eInf.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := R) (A := K) (B := ↥(TwoChartIntegralModel.chartAlgInf R F j))).toRingHom :=
  RingHom.ext fun b => θI_includeLeft eInf b

theorem main [Fact (t ≠ 0)] (hj : ((eFin ((1 : K) ⊗ₜ[R] TwoChartIntegralModel.jChartFin R F j)) : L) = t)
    (hcompat : ∀ (b : ↥(TwoChartIntegralModel.chartAlgFin R F j)) (b' : ↥(TwoChartIntegralModel.chartAlgInf R F j)) (n : ℕ),
      ((b : F) = (b' : F) * j ^ n) →
      ((eFin ((1 : K) ⊗ₜ[R] b) : L) =
        (eInf ((1 : K) ⊗ₜ[R] b') : L) * t ^ n))
    (hjInv : ((eInf ((1 : K) ⊗ₜ[R] TwoChartIntegralModel.jInvChartInf R F j)) : L) = t⁻¹) :
    ∃ (es : glued K t ⟶ pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom
        (algebraMap R K)))) (_ : IsIso es),
      es ≫ pullback.snd (TwoChartIntegralModel.toBase R F j) _ = gluedToBase K t ∧
      (AlgebraicCurve.CurveModel.ι₀ K t ≫ es ≫ pullback.fst (TwoChartIntegralModel.toBase R F j) _ =
        Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := R) (A := K) (B := ↥(TwoChartIntegralModel.chartAlgFin R F j))).toRingHom)) ≫
          TwoChartIntegralModel.ιFin R F j) ∧
      (AlgebraicCurve.CurveModel.ιInf K t ≫ es ≫ pullback.fst (TwoChartIntegralModel.toBase R F j) _ =
        Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := R) (A := K) (B := ↥(TwoChartIntegralModel.chartAlgInf R F j))).toRingHom)) ≫
          TwoChartIntegralModel.ιInf R F j) := by
  let D := datum eFin eInf hj hcompat hjInv
  refine ⟨es D, isIso_es D, es_snd D, ?_, ?_⟩
  · rw [ι₀_es_fst]
    show Spec.map (CommRingCat.ofHom ((θF eFin).comp Algebra.TensorProduct.includeLeftRingHom)) ≫ _ = _
    rw [ρFin_eq]
  · rw [ιInf_es_fst]
    show Spec.map (CommRingCat.ofHom ((θI eInf).comp Algebra.TensorProduct.includeLeftRingHom)) ≫ _ = _
    rw [ρInf_eq]

end Datum

end SPISO

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve in
open scoped TensorProduct in

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (K : Type u) [Field K] [Algebra R K]
    {L : Type u} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]
    (eFin : K ⊗[R] ↥(TwoChartIntegralModel.chartAlgFin R F j) ≃ₐ[K] ↥(CurveModel.chartRing K ({t} : Set L)))
    (eInf : K ⊗[R] ↥(TwoChartIntegralModel.chartAlgInf R F j) ≃ₐ[K] ↥(CurveModel.chartRing K ({t⁻¹} : Set L)))
    (hj : ((eFin ((1 : K) ⊗ₜ[R] TwoChartIntegralModel.jChartFin R F j)) : L) = t)
    (hjInv : ((eInf ((1 : K) ⊗ₜ[R] TwoChartIntegralModel.jInvChartInf R F j)) : L) = t⁻¹)
    (hcompat : ∀ (b : ↥(TwoChartIntegralModel.chartAlgFin R F j)) (b' : ↥(TwoChartIntegralModel.chartAlgInf R F j)) (n : ℕ),
      (b : F) = (b' : F) * j ^ n →
      ((eFin ((1 : K) ⊗ₜ[R] b)) : L) = ((eInf ((1 : K) ⊗ₜ[R] b')) : L) * t ^ n) :
    ∃ (es : CurveModel.glued K t ⟶ pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (_ : IsIso es),
      es ≫ pullback.snd (TwoChartIntegralModel.toBase R F j) _ = CurveModel.gluedToBase K t ∧
      (CurveModel.ι₀ K t ≫ es ≫ pullback.fst (TwoChartIntegralModel.toBase R F j) _ =
        Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := ↥(TwoChartIntegralModel.chartAlgFin R F j))).toRingHom)) ≫
          TwoChartIntegralModel.ιFin R F j) ∧
      (CurveModel.ιInf K t ≫ es ≫ pullback.fst (TwoChartIntegralModel.toBase R F j) _ =
        Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := ↥(TwoChartIntegralModel.chartAlgInf R F j))).toRingHom)) ≫
          TwoChartIntegralModel.ιInf R F j) :=
  SPISO.main eFin eInf hj hcompat hjInv

end S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_glued_pullback_toBase_of_algEquiv_chartAlg_chartRing
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_glued_pullback_toBase_of_algEquiv_chartAlg_chartRing (solution)
