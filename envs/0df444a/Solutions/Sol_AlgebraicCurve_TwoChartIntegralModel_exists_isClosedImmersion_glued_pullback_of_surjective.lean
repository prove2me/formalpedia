-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_isClosedImmersion_glued_pullback_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/035e4ff0-5835-5078-90bb-789b66594c4c

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_isClosedImmersion_glued_pullback_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.CurveModel

open scoped TensorProduct

noncomputable section

namespace GLUECI

open AlgebraicCurve.TwoChartIntegralModel

structure GlueDatum (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (κ : Type u) [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] (t : L) where
  θFin : ↥(chartAlgFin R F j) ⊗[R] κ →+* ↥(chartRing κ ({t} : Set L))
  θInf : ↥(chartAlgInf R F j) ⊗[R] κ →+* ↥(chartRing κ ({t⁻¹} : Set L))
  ρMid : ↥(chartAlgMid R F j) →+* ↥(chartRing κ ({t, t⁻¹} : Set L))
  θFin_right : θFin.comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
      κ →ₐ[R] ↥(chartAlgFin R F j) ⊗[R] κ)) = algebraMap κ ↥(chartRing κ ({t} : Set L))
  θInf_right : θInf.comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
      κ →ₐ[R] ↥(chartAlgInf R F j) ⊗[R] κ)) = algebraMap κ ↥(chartRing κ ({t⁻¹} : Set L))
  sq_fin : (incl₀ κ t).toRingHom.comp (θFin.comp Algebra.TensorProduct.includeLeftRingHom) =
    ρMid.comp (TwoChartIntegralModel.inclFin R F j).toRingHom
  sq_inf : (CurveModel.inclInf κ t).toRingHom.comp (θInf.comp Algebra.TensorProduct.includeLeftRingHom) =
    ρMid.comp (TwoChartIntegralModel.inclInf R F j).toRingHom
  m : ℕ
  m_pos : 0 < m
  ρFin_j : (θFin.comp Algebra.TensorProduct.includeLeftRingHom) (jChartFin R F j) = tChart κ t ^ m
  ρInf_jInv : (θInf.comp Algebra.TensorProduct.includeLeftRingHom) (jInvChartInf R F j) = tInvChart κ t ^ m
  surjFin : Function.Surjective θFin
  surjInf : Function.Surjective θInf

abbrev baseMap (R : Type u) [CommRing R] (κ : Type u) [Field κ] [Algebra R κ] :
    Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R κ))

section Model

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem tc_ιFin_eq_ιInf_iff (x₀ : XFin R F j) (xi : TwoChartIntegralModel.XInf R F j) :
    (ιFin R F j).base x₀ = (TwoChartIntegralModel.ιInf R F j).base xi ↔
      ∃ w : XMid R F j, (fFin R F j).base w = x₀ ∧ (TwoChartIntegralModel.fInf R F j).base w = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (F := span (fFin R F j) (TwoChartIntegralModel.fInf R F j))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · exact match fi, fj, h₁, h₂ with
        | .init _, .init _, h₁, h₂ => ⟨w, h₁, h₂⟩
    · exact nomatch fj
    · exact nomatch fi
  · rintro ⟨w, rfl, rfl⟩
    change (fFin R F j ≫ ιFin R F j).base w =
      (TwoChartIntegralModel.fInf R F j ≫ TwoChartIntegralModel.ιInf R F j).base w
    rw [TwoChartIntegralModel.glue_condition]

theorem tc_range_fInf : Set.range (TwoChartIntegralModel.fInf R F j).base =
    ((PrimeSpectrum.basicOpen (jInvChartInf R F j) :
        TopologicalSpace.Opens (PrimeSpectrum ↥(chartAlgInf R F j))) : Set (PrimeSpectrum ↥(chartAlgInf R F j))) := by
  letI := (TwoChartIntegralModel.inclInf R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf R F j
  exact PrimeSpectrum.localization_away_comap_range ↥(chartAlgMid R F j) (jInvChartInf R F j)

theorem tc_ιInf_mem_range_ιFin_iff (xi : TwoChartIntegralModel.XInf R F j) :
    (TwoChartIntegralModel.ιInf R F j).base xi ∈ Set.range (ιFin R F j).base ↔
      jInvChartInf R F j ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← tc_range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨w, -, hw⟩ := (tc_ιFin_eq_ιInf_iff R F j x₀ xi).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(fFin R F j).base w, (tc_ιFin_eq_ιInf_iff R F j _ _).mpr ⟨w, rfl, rfl⟩⟩

theorem tc_range_fFin : Set.range (fFin R F j).base =
    ((PrimeSpectrum.basicOpen (jChartFin R F j) :
        TopologicalSpace.Opens (PrimeSpectrum ↥(chartAlgFin R F j))) : Set (PrimeSpectrum ↥(chartAlgFin R F j))) := by
  letI := (TwoChartIntegralModel.inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  exact PrimeSpectrum.localization_away_comap_range ↥(chartAlgMid R F j) (jChartFin R F j)

theorem tc_ιFin_mem_range_ιInf_iff (x₀ : XFin R F j) :
    (ιFin R F j).base x₀ ∈ Set.range (TwoChartIntegralModel.ιInf R F j).base ↔
      jChartFin R F j ∉ x₀.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← tc_range_fFin, Set.mem_range]
  constructor
  · rintro ⟨xi, h⟩
    obtain ⟨w, hw, -⟩ := (tc_ιFin_eq_ιInf_iff R F j x₀ xi).mp h.symm
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(TwoChartIntegralModel.fInf R F j).base w, ((tc_ιFin_eq_ιInf_iff R F j _ _).mpr ⟨w, rfl, rfl⟩).symm⟩

end Model

section Schemes

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
  {κ : Type u} [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] {t : L} [Fact (t ≠ 0)]
  (D : GlueDatum R F j κ t)

abbrev GlueDatum.ρFin : ↥(chartAlgFin R F j) →+* ↥(chartRing κ ({t} : Set L)) :=
  D.θFin.comp Algebra.TensorProduct.includeLeftRingHom

abbrev GlueDatum.ρInf : ↥(chartAlgInf R F j) →+* ↥(chartRing κ ({t⁻¹} : Set L)) :=
  D.θInf.comp Algebra.TensorProduct.includeLeftRingHom

theorem ρFin_comp_algebraMap :
    D.ρFin.comp (algebraMap R ↥(chartAlgFin R F j)) =
      (algebraMap κ ↥(chartRing κ ({t} : Set L))).comp (algebraMap R κ) := by
  refine RingHom.ext fun q => ?_
  have h1 : (Algebra.TensorProduct.includeLeftRingHom (algebraMap R ↥(chartAlgFin R F j) q) :
      ↥(chartAlgFin R F j) ⊗[R] κ) = (1 : ↥(chartAlgFin R F j)) ⊗ₜ[R] (algebraMap R κ q) := by
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  have h2 := RingHom.congr_fun D.θFin_right (algebraMap R κ q)
  show D.θFin (Algebra.TensorProduct.includeLeftRingHom (algebraMap R ↥(chartAlgFin R F j) q)) =
    algebraMap κ ↥(chartRing κ ({t} : Set L)) (algebraMap R κ q)
  rw [h1, ← h2]
  rfl

theorem ρInf_comp_algebraMap :
    D.ρInf.comp (algebraMap R ↥(chartAlgInf R F j)) =
      (algebraMap κ ↥(chartRing κ ({t⁻¹} : Set L))).comp (algebraMap R κ) := by
  refine RingHom.ext fun q => ?_
  have h1 : (Algebra.TensorProduct.includeLeftRingHom (algebraMap R ↥(chartAlgInf R F j) q) :
      ↥(chartAlgInf R F j) ⊗[R] κ) = (1 : ↥(chartAlgInf R F j)) ⊗ₜ[R] (algebraMap R κ q) := by
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  have h2 := RingHom.congr_fun D.θInf_right (algebraMap R κ q)
  show D.θInf (Algebra.TensorProduct.includeLeftRingHom (algebraMap R ↥(chartAlgInf R F j) q)) =
    algebraMap κ ↥(chartRing κ ({t⁻¹} : Set L)) (algebraMap R κ q)
  rw [h1, ← h2]
  rfl

abbrev uFin : X₀ κ t ⟶ XFin R F j := Spec.map (CommRingCat.ofHom D.ρFin)

abbrev uInf : CurveModel.XInf κ t ⟶ TwoChartIntegralModel.XInf R F j := Spec.map (CommRingCat.ofHom D.ρInf)

abbrev uMid : XOverlap κ t ⟶ XMid R F j := Spec.map (CommRingCat.ofHom D.ρMid)

theorem f₀_uFin : f₀ κ t ≫ uFin D = uMid D ≫ fFin R F j := by
  simp only [f₀, uFin, uMid, fFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) D.sq_fin

theorem fInf_uInf : CurveModel.fInf κ t ≫ uInf D = uMid D ≫ TwoChartIntegralModel.fInf R F j := by
  simp only [CurveModel.fInf, uInf, uMid, TwoChartIntegralModel.fInf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) D.sq_inf

theorem glue_compat :
    f₀ κ t ≫ (uFin D ≫ ιFin R F j) = CurveModel.fInf κ t ≫ (uInf D ≫ TwoChartIntegralModel.ιInf R F j) := by
  rw [← Category.assoc, f₀_uFin, ← Category.assoc, fInf_uInf, Category.assoc, Category.assoc,
    TwoChartIntegralModel.glue_condition]

def u : glued κ t ⟶ AlgebraicCurve.TwoChartIntegralModel R F j :=
  pushout.desc (uFin D ≫ ιFin R F j) (uInf D ≫ TwoChartIntegralModel.ιInf R F j) (glue_compat D)

@[reassoc]
theorem ι₀_u : ι₀ κ t ≫ u D = uFin D ≫ ιFin R F j := pushout.inl_desc _ _ _

@[reassoc]
theorem ιInf_u : CurveModel.ιInf κ t ≫ u D = uInf D ≫ TwoChartIntegralModel.ιInf R F j := pushout.inr_desc _ _ _

theorem uFin_base :
    uFin D ≫ Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgFin R F j))) =
      Spec.map (CommRingCat.ofHom (algebraMap κ ↥(chartRing κ ({t} : Set L)))) ≫ baseMap R κ := by
  simp only [uFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (ρFin_comp_algebraMap D)

theorem uInf_base :
    uInf D ≫ Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgInf R F j))) =
      Spec.map (CommRingCat.ofHom (algebraMap κ ↥(chartRing κ ({t⁻¹} : Set L)))) ≫ baseMap R κ := by
  simp only [uInf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (ρInf_comp_algebraMap D)

theorem u_toBase : u D ≫ toBase R F j = gluedToBase κ t ≫ baseMap R κ := by
  refine pushout.hom_ext (f := f₀ κ t) (g := CurveModel.fInf κ t) ?_ ?_
  · change ι₀ κ t ≫ u D ≫ toBase R F j = ι₀ κ t ≫ gluedToBase κ t ≫ baseMap R κ
    rw [ι₀_u_assoc, ιFin_toBase, uFin_base, ι₀_gluedToBase_assoc]
  · change CurveModel.ιInf κ t ≫ u D ≫ toBase R F j = CurveModel.ιInf κ t ≫ gluedToBase κ t ≫ baseMap R κ
    rw [ιInf_u_assoc, ιInf_toBase, uInf_base, ιInf_gluedToBase_assoc]

def es : glued κ t ⟶ pullback (toBase R F j) (baseMap R κ) :=
  pullback.lift (u D) (gluedToBase κ t) (u_toBase D)

@[reassoc (attr := simp)]
theorem es_fst : es D ≫ pullback.fst (toBase R F j) (baseMap R κ) = u D := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem es_snd : es D ≫ pullback.snd (toBase R F j) (baseMap R κ) = gluedToBase κ t := pullback.lift_snd _ _ _

theorem ι₀_es_fst : ι₀ κ t ≫ es D ≫ pullback.fst (toBase R F j) (baseMap R κ) = uFin D ≫ ιFin R F j := by
  rw [es_fst, ι₀_u]

theorem ιInf_es_fst :
    CurveModel.ιInf κ t ≫ es D ≫ pullback.fst (toBase R F j) (baseMap R κ) =
      uInf D ≫ TwoChartIntegralModel.ιInf R F j := by
  rw [es_fst, ιInf_u]

theorem uInf_asIdeal (z : CurveModel.XInf κ t) : ((uInf D).base z).asIdeal = z.asIdeal.comap D.ρInf := rfl

theorem u_mem_range_ιFin_iff (y : glued κ t) :
    (u D).base y ∈ Set.range (ιFin R F j).base ↔ y ∈ Set.range (ι₀ κ t).base := by
  rcases mem_range_ι₀_or_mem_range_ιInf κ t y with ⟨x₀, rfl⟩ | ⟨z, rfl⟩
  · refine ⟨fun _ => ⟨x₀, rfl⟩, fun _ => ⟨(uFin D).base x₀, ?_⟩⟩
    change (uFin D ≫ ιFin R F j).base x₀ = (ι₀ κ t ≫ u D).base x₀
    rw [ι₀_u]
  · have hz : (u D).base ((CurveModel.ιInf κ t).base z) =
        (TwoChartIntegralModel.ιInf R F j).base ((uInf D).base z) := by
      change (CurveModel.ιInf κ t ≫ u D).base z = (uInf D ≫ TwoChartIntegralModel.ιInf R F j).base z
      rw [ιInf_u]
    rw [hz, tc_ιInf_mem_range_ιFin_iff, ιInf_mem_range_ι₀_iff, uInf_asIdeal, Ideal.mem_comap]
    have hpin : D.ρInf (jInvChartInf R F j) = tInvChart κ t ^ D.m := D.ρInf_jInv
    rw [hpin]
    exact not_congr (Ideal.IsPrime.pow_mem_iff_mem inferInstance D.m D.m_pos)

theorem uFin_asIdeal (x₀ : X₀ κ t) : ((uFin D).base x₀).asIdeal = x₀.asIdeal.comap D.ρFin := rfl

theorem u_mem_range_ιInf_iff (y : glued κ t) :
    (u D).base y ∈ Set.range (TwoChartIntegralModel.ιInf R F j).base ↔ y ∈ Set.range (CurveModel.ιInf κ t).base := by
  rcases mem_range_ι₀_or_mem_range_ιInf κ t y with ⟨x₀, rfl⟩ | ⟨z, rfl⟩
  · have hx : (u D).base ((ι₀ κ t).base x₀) = (ιFin R F j).base ((uFin D).base x₀) := by
      change (ι₀ κ t ≫ u D).base x₀ = (uFin D ≫ ιFin R F j).base x₀
      rw [ι₀_u]
    rw [hx, tc_ιFin_mem_range_ιInf_iff, ι₀_mem_range_ιInf_iff, uFin_asIdeal, Ideal.mem_comap]
    have hpin : D.ρFin (jChartFin R F j) = tChart κ t ^ D.m := D.ρFin_j
    rw [hpin]
    exact not_congr (Ideal.IsPrime.pow_mem_iff_mem inferInstance D.m D.m_pos)
  · refine ⟨fun _ => ⟨z, rfl⟩, fun _ => ⟨(uInf D).base z, ?_⟩⟩
    change (uInf D ≫ TwoChartIntegralModel.ιInf R F j).base z = (CurveModel.ιInf κ t ≫ u D).base z
    rw [ιInf_u]

theorem es_fst_mem_range_ιInf_iff (y : glued κ t) :
    (es D ≫ pullback.fst (toBase R F j) (baseMap R κ)).base y ∈ Set.range (TwoChartIntegralModel.ιInf R F j).base ↔
      y ∈ Set.range (CurveModel.ιInf κ t).base := by
  rw [es_fst]; exact u_mem_range_ιInf_iff D y

theorem es_fst_mem_range_ιFin_iff (y : glued κ t) :
    (es D ≫ pullback.fst (toBase R F j) (baseMap R κ)).base y ∈ Set.range (ιFin R F j).base ↔
      y ∈ Set.range (ι₀ κ t).base := by
  rw [es_fst]; exact u_mem_range_ιFin_iff D y

abbrev PFin (_D : GlueDatum R F j κ t) := pullback (ιFin R F j) (pullback.fst (toBase R F j) (baseMap R κ))

abbrev PInf (_D : GlueDatum R F j κ t) :=
  pullback (TwoChartIntegralModel.ιInf R F j) (pullback.fst (toBase R F j) (baseMap R κ))

def φFin : X₀ κ t ⟶ PFin D :=
  pullback.lift (uFin D) (ι₀ κ t ≫ es D) (by rw [Category.assoc, ι₀_es_fst])

def φInf : CurveModel.XInf κ t ⟶ PInf D :=
  pullback.lift (uInf D) (CurveModel.ιInf κ t ≫ es D) (by rw [Category.assoc, ιInf_es_fst])

@[reassoc (attr := simp)]
theorem φFin_fst : φFin D ≫ pullback.fst _ _ = uFin D := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem φFin_snd : φFin D ≫ pullback.snd _ _ = ι₀ κ t ≫ es D := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem φInf_fst : φInf D ≫ pullback.fst _ _ = uInf D := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem φInf_snd : φInf D ≫ pullback.snd _ _ = CurveModel.ιInf κ t ≫ es D := pullback.lift_snd _ _ _

def isoFin : PFin D ≅ Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] κ)) :=
  pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (ιFin R F j) ≪≫
    pullback.congrHom (ιFin_toBase R F j) rfl ≪≫ pullbackSpecIso R ↥(chartAlgFin R F j) κ

def isoInf : PInf D ≅ Spec (CommRingCat.of (↥(chartAlgInf R F j) ⊗[R] κ)) :=
  pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (TwoChartIntegralModel.ιInf R F j) ≪≫
    pullback.congrHom (ιInf_toBase R F j) rfl ≪≫ pullbackSpecIso R ↥(chartAlgInf R F j) κ

set_option maxHeartbeats 1600000 in

theorem SpecMap_θFin_eq :
    Spec.map (CommRingCat.ofHom D.θFin) ≫ (pullbackSpecIso R ↥(chartAlgFin R F j) κ).inv =
      φFin D ≫ (pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (ιFin R F j)).hom ≫
        (pullback.congrHom (ιFin_toBase R F j) rfl).hom := by
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
theorem SpecMap_θInf_eq :
    Spec.map (CommRingCat.ofHom D.θInf) ≫ (pullbackSpecIso R ↥(chartAlgInf R F j) κ).inv =
      φInf D ≫ (pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (TwoChartIntegralModel.ιInf R F j)).hom ≫
        (pullback.congrHom (ιInf_toBase R F j) rfl).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, φInf_fst]
    try rfl
  · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [D.θInf_right]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd, φInf_snd_assoc, es_snd, ιInf_gluedToBase]

theorem φFin_isoFin : φFin D ≫ (isoFin D).hom = Spec.map (CommRingCat.ofHom D.θFin) := by
  calc φFin D ≫ (isoFin D).hom
      = (φFin D ≫ (pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (ιFin R F j)).hom ≫
          (pullback.congrHom (ιFin_toBase R F j) rfl).hom) ≫ (pullbackSpecIso R ↥(chartAlgFin R F j) κ).hom := by
        simp only [isoFin, Iso.trans_hom, Category.assoc]
    _ = (Spec.map (CommRingCat.ofHom D.θFin) ≫ (pullbackSpecIso R ↥(chartAlgFin R F j) κ).inv) ≫
          (pullbackSpecIso R ↥(chartAlgFin R F j) κ).hom := by rw [SpecMap_θFin_eq]
    _ = Spec.map (CommRingCat.ofHom D.θFin) := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem φInf_isoInf : φInf D ≫ (isoInf D).hom = Spec.map (CommRingCat.ofHom D.θInf) := by
  calc φInf D ≫ (isoInf D).hom
      = (φInf D ≫ (pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (TwoChartIntegralModel.ιInf R F j)).hom ≫
          (pullback.congrHom (ιInf_toBase R F j) rfl).hom) ≫ (pullbackSpecIso R ↥(chartAlgInf R F j) κ).hom := by
        simp only [isoInf, Iso.trans_hom, Category.assoc]
    _ = (Spec.map (CommRingCat.ofHom D.θInf) ≫ (pullbackSpecIso R ↥(chartAlgInf R F j) κ).inv) ≫
          (pullbackSpecIso R ↥(chartAlgInf R F j) κ).hom := by rw [SpecMap_θInf_eq]
    _ = Spec.map (CommRingCat.ofHom D.θInf) := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

scoped instance isClosedImmersion_φFin : IsClosedImmersion (φFin D) := by
  have h : φFin D = Spec.map (CommRingCat.ofHom D.θFin) ≫ (isoFin D).inv := by
    rw [← φFin_isoFin, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom D.θFin)) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom D.θFin) (by simpa using D.surjFin)
  rw [h]
  infer_instance

scoped instance isClosedImmersion_φInf : IsClosedImmersion (φInf D) := by
  have h : φInf D = Spec.map (CommRingCat.ofHom D.θInf) ≫ (isoInf D).inv := by
    rw [← φInf_isoInf, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom D.θInf)) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom D.θInf) (by simpa using D.surjInf)
  rw [h]
  infer_instance

abbrev gFin : PFin D ⟶ pullback (toBase R F j) (baseMap R κ) := pullback.snd _ _

abbrev gInf : PInf D ⟶ pullback (toBase R F j) (baseMap R κ) := pullback.snd _ _

theorem range_gFin : Set.range (gFin D).base =
    (pullback.fst (toBase R F j) (baseMap R κ)).base ⁻¹' Set.range (ιFin R F j).base := by
  rw [gFin, IsOpenImmersion.range_pullbackSnd]; rfl

theorem range_gInf : Set.range (gInf D).base =
    (pullback.fst (toBase R F j) (baseMap R κ)).base ⁻¹' Set.range (TwoChartIntegralModel.ιInf R F j).base := by
  rw [gInf, IsOpenImmersion.range_pullbackSnd]; rfl

theorem range_pullback_fst_gFin :
    Set.range (pullback.fst (es D) (gFin D)).base = Set.range (ι₀ κ t).base := by
  rw [IsOpenImmersion.range_pullbackFst]
  ext y
  change (es D).base y ∈ Set.range (gFin D).base ↔ _
  rw [range_gFin, Set.mem_preimage]
  exact es_fst_mem_range_ιFin_iff D y

theorem range_pullback_fst_gInf :
    Set.range (pullback.fst (es D) (gInf D)).base = Set.range (CurveModel.ιInf κ t).base := by
  rw [IsOpenImmersion.range_pullbackFst]
  ext y
  change (es D).base y ∈ Set.range (gInf D).base ↔ _
  rw [range_gInf, Set.mem_preimage]
  exact es_fst_mem_range_ιInf_iff D y

theorem isClosedImmersion_pullback_snd_gFin : IsClosedImmersion (pullback.snd (es D) (gFin D)) := by
  let e := IsOpenImmersion.isoOfRangeEq (ι₀ κ t) (pullback.fst (es D) (gFin D)) (range_pullback_fst_gFin D).symm
  have he : e.hom ≫ pullback.fst (es D) (gFin D) = ι₀ κ t := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have h : e.hom ≫ pullback.snd (es D) (gFin D) = φFin D := by
    rw [← cancel_mono (gFin D)]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, he, φFin_snd]
  have h' : pullback.snd (es D) (gFin D) = e.inv ≫ φFin D := by rw [← h, Iso.inv_hom_id_assoc]
  rw [h']
  infer_instance

theorem isClosedImmersion_pullback_snd_gInf : IsClosedImmersion (pullback.snd (es D) (gInf D)) := by
  let e := IsOpenImmersion.isoOfRangeEq (CurveModel.ιInf κ t) (pullback.fst (es D) (gInf D)) (range_pullback_fst_gInf D).symm
  have he : e.hom ≫ pullback.fst (es D) (gInf D) = CurveModel.ιInf κ t := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have h : e.hom ≫ pullback.snd (es D) (gInf D) = φInf D := by
    rw [← cancel_mono (gInf D)]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, he, φInf_snd]
  have h' : pullback.snd (es D) (gInf D) = e.inv ≫ φInf D := by rw [← h, Iso.inv_hom_id_assoc]
  rw [h']
  infer_instance

def fibreCover : (pullback (toBase R F j) (baseMap R κ)).OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun b => cond b (PFin D) (PInf D))
    (fun b => match b with
      | true => gFin D
      | false => gInf D)
    (by
      intro x
      rcases mem_range_ιFin_or_mem_range_ιInf R F j ((pullback.fst (toBase R F j) (baseMap R κ)).base x) with hx | hx
      · have hx' : x ∈ Set.range (gFin D).base := by rw [range_gFin]; exact hx
        obtain ⟨y, hy⟩ := hx'
        exact ⟨true, y, hy⟩
      · have hx' : x ∈ Set.range (gInf D).base := by rw [range_gInf]; exact hx
        obtain ⟨y, hy⟩ := hx'
        exact ⟨false, y, hy⟩)
    (fun b => match b with
      | true => (inferInstance : IsOpenImmersion (gFin D))
      | false => (inferInstance : IsOpenImmersion (gInf D)))

theorem isClosedImmersion_es : IsClosedImmersion (es D) := by
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (fibreCover D) ?_
  intro b
  match b with
  | true => exact isClosedImmersion_pullback_snd_gFin D
  | false => exact isClosedImmersion_pullback_snd_gInf D

theorem gFin_mem_range_es_iff (z : PFin D) :
    (gFin D).base z ∈ Set.range (es D).base ↔ z ∈ Set.range (φFin D).base := by
  constructor
  · rintro ⟨y, hy⟩
    have hy' : (es D ≫ pullback.fst (toBase R F j) (baseMap R κ)).base y ∈ Set.range (ιFin R F j).base := by
      refine ⟨(pullback.fst (ιFin R F j) _).base z, ?_⟩
      change _ = ((es D).base ≫ (pullback.fst (toBase R F j) (baseMap R κ)).base) y
      rw [TopCat.comp_app, hy]
      change (pullback.fst (ιFin R F j) _ ≫ ιFin R F j).base z = (gFin D ≫ pullback.fst (toBase R F j) (baseMap R κ)).base z
      rw [pullback.condition]
    obtain ⟨x₀, rfl⟩ := (es_fst_mem_range_ιFin_iff D y).mp hy'
    refine ⟨x₀, (gFin D).isOpenEmbedding.injective ?_⟩
    change ((φFin D) ≫ gFin D).base x₀ = _
    rw [φFin_snd]
    exact hy
  · rintro ⟨x₀, rfl⟩
    refine ⟨(ι₀ κ t).base x₀, ?_⟩
    change (ι₀ κ t ≫ es D).base x₀ = (φFin D ≫ gFin D).base x₀
    rw [φFin_snd]

theorem gInf_mem_range_es_iff (z : PInf D) :
    (gInf D).base z ∈ Set.range (es D).base ↔ z ∈ Set.range (φInf D).base := by
  constructor
  · rintro ⟨y, hy⟩
    have hy' : (es D ≫ pullback.fst (toBase R F j) (baseMap R κ)).base y ∈
        Set.range (TwoChartIntegralModel.ιInf R F j).base := by
      refine ⟨(pullback.fst (TwoChartIntegralModel.ιInf R F j) _).base z, ?_⟩
      change _ = ((es D).base ≫ (pullback.fst (toBase R F j) (baseMap R κ)).base) y
      rw [TopCat.comp_app, hy]
      change (pullback.fst (TwoChartIntegralModel.ιInf R F j) _ ≫ TwoChartIntegralModel.ιInf R F j).base z =
        (gInf D ≫ pullback.fst (toBase R F j) (baseMap R κ)).base z
      rw [pullback.condition]
    obtain ⟨xi, rfl⟩ := (es_fst_mem_range_ιInf_iff D y).mp hy'
    refine ⟨xi, (gInf D).isOpenEmbedding.injective ?_⟩
    change ((φInf D) ≫ gInf D).base xi = _
    rw [φInf_snd]
    exact hy
  · rintro ⟨xi, rfl⟩
    refine ⟨(CurveModel.ιInf κ t).base xi, ?_⟩
    change (CurveModel.ιInf κ t ≫ es D).base xi = (φInf D ≫ gInf D).base xi
    rw [φInf_snd]

theorem mem_range_φFin_iff (z : PFin D) :
    z ∈ Set.range (φFin D).base ↔ RingHom.ker D.θFin ≤ ((isoFin D).hom.base z).asIdeal := by
  have hbij := (isoFin D).hom.homeomorph.injective
  constructor
  · rintro ⟨x₀, rfl⟩
    have : (isoFin D).hom.base ((φFin D).base x₀) = (Spec.map (CommRingCat.ofHom D.θFin)).base x₀ := by
      change (φFin D ≫ (isoFin D).hom).base x₀ = _
      rw [φFin_isoFin]
    rw [this]
    change RingHom.ker D.θFin ≤ (x₀.asIdeal.comap D.θFin)
    exact fun a ha => by simp [Ideal.mem_comap, RingHom.mem_ker.mp ha]
  · intro h
    have hz : (isoFin D).hom.base z ∈ Set.range (Spec.map (CommRingCat.ofHom D.θFin)).base := by
      change (isoFin D).hom.base z ∈ Set.range (PrimeSpectrum.comap D.θFin)
      rw [range_comap_of_surjective _ D.θFin D.surjFin]
      exact h
    obtain ⟨x₀, hx₀⟩ := hz
    refine ⟨x₀, hbij ?_⟩
    change ((φFin D) ≫ (isoFin D).hom).base x₀ = _
    rw [φFin_isoFin]
    exact hx₀

theorem mem_range_φInf_iff (z : PInf D) :
    z ∈ Set.range (φInf D).base ↔ RingHom.ker D.θInf ≤ ((isoInf D).hom.base z).asIdeal := by
  have hbij := (isoInf D).hom.homeomorph.injective
  constructor
  · rintro ⟨xi, rfl⟩
    have : (isoInf D).hom.base ((φInf D).base xi) = (Spec.map (CommRingCat.ofHom D.θInf)).base xi := by
      change (φInf D ≫ (isoInf D).hom).base xi = _
      rw [φInf_isoInf]
    rw [this]
    change RingHom.ker D.θInf ≤ (xi.asIdeal.comap D.θInf)
    exact fun a ha => by simp [Ideal.mem_comap, RingHom.mem_ker.mp ha]
  · intro h
    have hz : (isoInf D).hom.base z ∈ Set.range (Spec.map (CommRingCat.ofHom D.θInf)).base := by
      change (isoInf D).hom.base z ∈ Set.range (PrimeSpectrum.comap D.θInf)
      rw [range_comap_of_surjective _ D.θInf D.surjInf]
      exact h
    obtain ⟨xi, hxi⟩ := hz
    refine ⟨xi, hbij ?_⟩
    change ((φInf D) ≫ (isoInf D).hom).base xi = _
    rw [φInf_isoInf]
    exact hxi

end Schemes

section Datum

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
  {κ : Type u} [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] {t : L}

variable
  (eFin : κ ⊗[R] ↥(chartAlgFin R F j) →ₐ[κ] ↥(chartRing κ ({t} : Set L)))
  (eInf : κ ⊗[R] ↥(chartAlgInf R F j) →ₐ[κ] ↥(chartRing κ ({t⁻¹} : Set L)))

def θF : ↥(chartAlgFin R F j) ⊗[R] κ →+* ↥(chartRing κ ({t} : Set L)) :=
  (eFin : κ ⊗[R] ↥(chartAlgFin R F j) →+* ↥(chartRing κ ({t} : Set L))).comp
    (RingHomClass.toRingHom (Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ))

def θI : ↥(chartAlgInf R F j) ⊗[R] κ →+* ↥(chartRing κ ({t⁻¹} : Set L)) :=
  (eInf : κ ⊗[R] ↥(chartAlgInf R F j) →+* ↥(chartRing κ ({t⁻¹} : Set L))).comp
    (RingHomClass.toRingHom (Algebra.TensorProduct.comm R ↥(chartAlgInf R F j) κ))

theorem θF_tmul (b : ↥(chartAlgFin R F j)) (x : κ) : θF eFin (b ⊗ₜ[R] x) = eFin (x ⊗ₜ[R] b) := by
  show eFin (Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ (b ⊗ₜ x)) = _
  rw [Algebra.TensorProduct.comm_tmul]

theorem θI_tmul (b : ↥(chartAlgInf R F j)) (x : κ) : θI eInf (b ⊗ₜ[R] x) = eInf (x ⊗ₜ[R] b) := by
  show eInf (Algebra.TensorProduct.comm R ↥(chartAlgInf R F j) κ (b ⊗ₜ x)) = _
  rw [Algebra.TensorProduct.comm_tmul]

theorem θF_right :
    (θF eFin).comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
      κ →ₐ[R] ↥(chartAlgFin R F j) ⊗[R] κ)) = algebraMap κ ↥(chartRing κ ({t} : Set L)) := by
  refine RingHom.ext fun x => ?_
  show θF eFin ((1 : ↥(chartAlgFin R F j)) ⊗ₜ[R] x) = _
  rw [θF_tmul]
  have hx : (x ⊗ₜ[R] (1 : ↥(chartAlgFin R F j)) : κ ⊗[R] ↥(chartAlgFin R F j)) = algebraMap κ _ x := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  rw [hx, AlgHom.commutes]

theorem θI_right :
    (θI eInf).comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
      κ →ₐ[R] ↥(chartAlgInf R F j) ⊗[R] κ)) = algebraMap κ ↥(chartRing κ ({t⁻¹} : Set L)) := by
  refine RingHom.ext fun x => ?_
  show θI eInf ((1 : ↥(chartAlgInf R F j)) ⊗ₜ[R] x) = _
  rw [θI_tmul]
  have hx : (x ⊗ₜ[R] (1 : ↥(chartAlgInf R F j)) : κ ⊗[R] ↥(chartAlgInf R F j)) = algebraMap κ _ x := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  rw [hx, AlgHom.commutes]

theorem θF_includeLeft (b : ↥(chartAlgFin R F j)) :
    (θF eFin).comp Algebra.TensorProduct.includeLeftRingHom b = eFin ((1 : κ) ⊗ₜ[R] b) := by
  rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, θF_tmul]

theorem θI_includeLeft (b : ↥(chartAlgInf R F j)) :
    (θI eInf).comp Algebra.TensorProduct.includeLeftRingHom b = eInf ((1 : κ) ⊗ₜ[R] b) := by
  rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, θI_tmul]

def gMid : ↥(chartAlgFin R F j) →+* ↥(chartRing κ ({t, t⁻¹} : Set L)) :=
  (incl₀ κ t).toRingHom.comp ((θF eFin).comp Algebra.TensorProduct.includeLeftRingHom)

theorem coe_gMid (b : ↥(chartAlgFin R F j)) : (gMid (t := t) eFin b : L) = (eFin ((1 : κ) ⊗ₜ[R] b) : L) := by
  show ((incl₀ κ t) ((θF eFin).comp Algebra.TensorProduct.includeLeftRingHom b) : L) = _
  rw [CurveModel.coe_chartIncl, θF_includeLeft]

variable {m : ℕ}

theorem isUnit_gMid_j [Fact (t ≠ 0)] (hj : ((eFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m) :
    IsUnit (gMid (t := t) eFin (jChartFin R F j)) := by
  have h : gMid (t := t) eFin (jChartFin R F j) = incl₀ κ t (tChart κ t) ^ m := by
    apply Subtype.ext
    rw [coe_gMid, hj, Subalgebra.coe_pow, CurveModel.coe_chartIncl, coe_tChart]
  rw [h]
  exact (isUnit_incl₀_tChart κ t Fact.out).pow m

def ρM [Fact (t ≠ 0)] (hj : ((eFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m) :
    ↥(chartAlgMid R F j) →+* ↥(chartRing κ ({t, t⁻¹} : Set L)) :=
  letI := (TwoChartIntegralModel.inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  IsLocalization.Away.lift (jChartFin R F j) (g := gMid (t := t) eFin) (isUnit_gMid_j eFin hj)

theorem ρM_inclFin [Fact (t ≠ 0)] (hj : ((eFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m) (b : ↥(chartAlgFin R F j)) :
    ρM eFin hj (TwoChartIntegralModel.inclFin R F j b) = gMid (t := t) eFin b := by
  letI := (TwoChartIntegralModel.inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  exact IsLocalization.Away.lift_eq (jChartFin R F j) (isUnit_gMid_j eFin hj) b

private theorem _root_.GLUECI.sq_fin [Fact (t ≠ 0)] (hj : ((eFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m) :
    (incl₀ κ t).toRingHom.comp ((θF eFin).comp Algebra.TensorProduct.includeLeftRingHom) =
      (ρM eFin hj).comp (TwoChartIntegralModel.inclFin R F j).toRingHom :=
  RingHom.ext fun b => (ρM_inclFin eFin hj b).symm

p2m_export "GLUECI" "sq_fin"

private theorem _root_.GLUECI.sq_inf [Fact (t ≠ 0)] (hj : ((eFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m)
    (hcompat : ∀ (b : ↥(chartAlgFin R F j)) (b' : ↥(chartAlgInf R F j)) (n : ℕ),
      (b : F) = (b' : F) * j ^ n → ((eFin ((1 : κ) ⊗ₜ[R] b)) : L) = ((eInf ((1 : κ) ⊗ₜ[R] b')) : L) * t ^ (m * n)) :
    (CurveModel.inclInf κ t).toRingHom.comp ((θI eInf).comp Algebra.TensorProduct.includeLeftRingHom) =
      (ρM eFin hj).comp (TwoChartIntegralModel.inclInf R F j).toRingHom := by
  letI := (TwoChartIntegralModel.inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  refine RingHom.ext fun b' => Subtype.ext ?_
  obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, h⟩ :=
    IsLocalization.surj (Submonoid.powers (jChartFin R F j)) (TwoChartIntegralModel.inclInf R F j b')
  have h' : (TwoChartIntegralModel.inclInf R F j b') * (TwoChartIntegralModel.inclFin R F j (jChartFin R F j)) ^ n =
      TwoChartIntegralModel.inclFin R F j b := by
    simp only [RingHom.algebraMap_toAlgebra, map_pow] at h
    exact h
  have hF : (b : F) = (b' : F) * j ^ n := by
    have := congrArg (fun z : ↥(chartAlgMid R F j) => (z : F)) h'
    simpa only [Subalgebra.coe_mul, Subalgebra.coe_pow, TwoChartIntegralModel.coe_chartIncl, coe_jChartFin]
      using this.symm
  have hc := hcompat b b' n hF
  have hρ := congrArg (fun z : ↥(chartAlgMid R F j) => ((ρM eFin hj z : ↥(chartRing κ ({t, t⁻¹} : Set L))) : L)) h'
  simp only [map_mul, map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow] at hρ
  rw [ρM_inclFin, ρM_inclFin, coe_gMid, coe_gMid, hj, hc, ← pow_mul] at hρ
  have htn : t ^ (m * n) ≠ 0 := pow_ne_zero _ Fact.out
  have hmain : ((ρM eFin hj (TwoChartIntegralModel.inclInf R F j b') : ↥(chartRing κ ({t, t⁻¹} : Set L))) : L) =
      (eInf ((1 : κ) ⊗ₜ[R] b') : L) :=
    mul_right_cancel₀ htn hρ
  show ((CurveModel.inclInf κ t) ((θI eInf).comp Algebra.TensorProduct.includeLeftRingHom b') : L) =
    ((ρM eFin hj (TwoChartIntegralModel.inclInf R F j b') : ↥(chartRing κ ({t, t⁻¹} : Set L))) : L)
  rw [CurveModel.coe_chartIncl, θI_includeLeft, hmain]

p2m_export "GLUECI" "sq_inf"

def datum [Fact (t ≠ 0)] (hm : 0 < m) (hj : ((eFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m)
    (hcompat : ∀ (b : ↥(chartAlgFin R F j)) (b' : ↥(chartAlgInf R F j)) (n : ℕ),
      (b : F) = (b' : F) * j ^ n → ((eFin ((1 : κ) ⊗ₜ[R] b)) : L) = ((eInf ((1 : κ) ⊗ₜ[R] b')) : L) * t ^ (m * n))
    (hjInv : ((eInf ((1 : κ) ⊗ₜ[R] jInvChartInf R F j)) : L) = t⁻¹ ^ m)
    (hFin : Function.Surjective eFin) (hInf : Function.Surjective eInf) : GlueDatum R F j κ t where
  θFin := θF eFin
  θInf := θI eInf
  ρMid := ρM eFin hj
  θFin_right := θF_right eFin
  θInf_right := θI_right eInf
  sq_fin := sq_fin eFin hj
  sq_inf := sq_inf eFin eInf hj hcompat
  m := m
  m_pos := hm
  ρFin_j := Subtype.ext (by rw [θF_includeLeft, hj, Subalgebra.coe_pow, coe_tChart])
  ρInf_jInv := Subtype.ext (by rw [θI_includeLeft, hjInv, Subalgebra.coe_pow, coe_tInvChart])
  surjFin := hFin.comp (Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ).surjective
  surjInf := hInf.comp (Algebra.TensorProduct.comm R ↥(chartAlgInf R F j) κ).surjective

theorem ρFin_eq :
    (θF eFin).comp Algebra.TensorProduct.includeLeftRingHom =
      eFin.toRingHom.comp (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom :=
  RingHom.ext fun b => θF_includeLeft eFin b

theorem ρInf_eq :
    (θI eInf).comp Algebra.TensorProduct.includeLeftRingHom =
      eInf.toRingHom.comp (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom :=
  RingHom.ext fun b => θI_includeLeft eInf b

theorem ker_θF : RingHom.ker (θF eFin) =
    RingHom.ker (eFin.toRingHom.comp (Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ).toRingHom) := rfl

theorem ker_θI : RingHom.ker (θI eInf) =
    RingHom.ker (eInf.toRingHom.comp (Algebra.TensorProduct.comm R ↥(chartAlgInf R F j) κ).toRingHom) := rfl

end Datum

end GLUECI
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_isClosedImmersion_glued_pullback_of_surjective.GLUECI"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_isClosedImmersion_glued_pullback_of_surjective.GLUECI"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel in
open scoped TensorProduct in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (κ : Type u) [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] (t : L) [Fact (t ≠ 0)]
    (m : ℕ) (hm : 0 < m)
    (θFin : κ ⊗[R] ↥(chartAlgFin R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t} : Set L)))
    (θInf : κ ⊗[R] ↥(chartAlgInf R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t⁻¹} : Set L)))
    (hFin : Function.Surjective θFin) (hInf : Function.Surjective θInf)
    (hj : ((θFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m)
    (hjInv : ((θInf ((1 : κ) ⊗ₜ[R] jInvChartInf R F j)) : L) = t⁻¹ ^ m)
    (hcompat : ∀ (b : ↥(chartAlgFin R F j)) (b' : ↥(chartAlgInf R F j)) (n : ℕ),
      (b : F) = (b' : F) * j ^ n →
      ((θFin ((1 : κ) ⊗ₜ[R] b)) : L) = ((θInf ((1 : κ) ⊗ₜ[R] b')) : L) * t ^ (m * n)) :
    ∃ c : CurveModel.glued κ t ⟶
        pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))),
      IsClosedImmersion c ∧
      c ≫ pullback.snd (toBase R F j) _ = CurveModel.gluedToBase κ t ∧
      (CurveModel.ι₀ κ t ≫ c ≫ pullback.fst (toBase R F j) _ =
        Spec.map (CommRingCat.ofHom (θFin.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom)) ≫
          ιFin R F j) ∧
      (CurveModel.ιInf κ t ≫ c ≫ pullback.fst (toBase R F j) _ =
        Spec.map (CommRingCat.ofHom (θInf.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom)) ≫
          ιInf R F j) ∧

      (∀ y : ↥(CurveModel.glued κ t),
        (c ≫ pullback.fst (toBase R F j) _).base y ∈ Set.range (ιFin R F j).base ↔
          y ∈ Set.range (CurveModel.ι₀ κ t).base) ∧

      (∀ z : ↥(pullback (ιFin R F j) (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))),
        (pullback.snd (ιFin R F j) _).base z ∈ Set.range c.base ↔
          RingHom.ker (θFin.toRingHom.comp
              (Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ).toRingHom) ≤
            ((pullbackRightPullbackFstIso (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) (ιFin R F j) ≪≫
                pullback.congrHom (ιFin_toBase R F j) rfl ≪≫
                pullbackSpecIso R ↥(chartAlgFin R F j) κ).hom.base z).asIdeal) ∧
      (∀ z : ↥(pullback (ιInf R F j) (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))),
        (pullback.snd (ιInf R F j) _).base z ∈ Set.range c.base ↔
          RingHom.ker (θInf.toRingHom.comp
              (Algebra.TensorProduct.comm R ↥(chartAlgInf R F j) κ).toRingHom) ≤
            ((pullbackRightPullbackFstIso (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) (ιInf R F j) ≪≫
                pullback.congrHom (ιInf_toBase R F j) rfl ≪≫
                pullbackSpecIso R ↥(chartAlgInf R F j) κ).hom.base z).asIdeal) := by
  let D := GLUECI.datum (m := m) θFin θInf hm hj hcompat hjInv hFin hInf
  refine ⟨GLUECI.es D, GLUECI.isClosedImmersion_es D, GLUECI.es_snd D, ?_, ?_,
    GLUECI.es_fst_mem_range_ιFin_iff D, ?_, ?_⟩
  · rw [GLUECI.ι₀_es_fst]
    show Spec.map (CommRingCat.ofHom ((GLUECI.θF θFin).comp Algebra.TensorProduct.includeLeftRingHom)) ≫ _ = _
    rw [GLUECI.ρFin_eq]
  · rw [GLUECI.ιInf_es_fst]
    show Spec.map (CommRingCat.ofHom ((GLUECI.θI θInf).comp Algebra.TensorProduct.includeLeftRingHom)) ≫ _ = _
    rw [GLUECI.ρInf_eq]
  · intro z
    rw [GLUECI.gFin_mem_range_es_iff, GLUECI.mem_range_φFin_iff]
    rfl
  · intro z
    rw [GLUECI.gInf_mem_range_es_iff, GLUECI.mem_range_φInf_iff]
    rfl

end S_AlgebraicCurve_TwoChartIntegralModel_exists_isClosedImmersion_glued_pullback_of_surjective
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_isClosedImmersion_glued_pullback_of_surjective (solution)
