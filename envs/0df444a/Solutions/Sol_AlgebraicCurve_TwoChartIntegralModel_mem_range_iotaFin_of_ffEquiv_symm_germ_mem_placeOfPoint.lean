-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e273d27f-0265-5096-a8e7-6bf45fa788bd

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint.AlgebraicCurve"
p2m_open "AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint.AlgebraicCurve.TwoChartIntegralModel"

universe u v

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel.chartAlgFin TwoChartIntegralModel.jChartFin TwoChartIntegralModel TwoChartIntegralModel.ιFin CurveModel"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "coe_chartIncl chartAlgFin chartAlgInf chartAlgMid jChartFin jInvChartInf coe_jChartFin coe_jInvChartInf inclFin inclInf isLocalization_away_inclFin isLocalization_away_inclInf XFin XInf XMid fFin fInf ιFin ιInf glue_condition mem_range_ιFin_or_mem_range_ιInf chartFinOpen chartInfOpen fibre"
namespace ChartsGen
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

set_option quotPrecheck false in
local notation "X₀" => AlgebraicCurve.TwoChartIntegralModel R F j

theorem ιFin_eq_ιInf_iff (x₀ : XFin R F j) (xi : XInf R F j) :
    (ιFin R F j).base x₀ = (ιInf R F j).base xi ↔
      ∃ u : XMid R F j, (fFin R F j).base u = x₀ ∧ (fInf R F j).base u = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, u, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span (fFin R F j) (fInf R F j))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · obtain rfl : fi = WalkingSpan.Hom.fst := Subsingleton.elim _ _
      obtain rfl : fj = WalkingSpan.Hom.snd := Subsingleton.elim _ _
      exact ⟨u, by simp at h₁; exact h₁, by simp at h₂; exact h₂⟩
    · rcases fj with ⟨⟩
    · rcases fi with ⟨⟩
  · rintro ⟨u, rfl, rfl⟩
    change (fFin R F j ≫ ιFin R F j).base u = (fInf R F j ≫ ιInf R F j).base u
    rw [glue_condition]

theorem range_fFin : Set.range (fFin R F j).base =
    ((PrimeSpectrum.basicOpen (jChartFin R F j) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgFin R F j))) :
      Set (PrimeSpectrum (chartAlgFin R F j))) := by
  letI := (inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid R F j) (jChartFin R F j)

theorem range_fInf : Set.range (fInf R F j).base =
    ((PrimeSpectrum.basicOpen (jInvChartInf R F j) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgInf R F j))) :
      Set (PrimeSpectrum (chartAlgInf R F j))) := by
  letI := (inclInf R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf R F j
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid R F j) (jInvChartInf R F j)

abbrev ιMid : XMid R F j ⟶ X₀ := fFin R F j ≫ ιFin R F j

scoped instance isOpenImmersion_ιMid : IsOpenImmersion (ιMid R F j) := IsOpenImmersion.comp _ _

theorem ιMid_eq' : ιMid R F j = fInf R F j ≫ ιInf R F j := glue_condition R F j

theorem inclFin_j_mul_inclInf_jInv :
    inclFin R F j (jChartFin R F j) * inclInf R F j (jInvChartInf R F j) = 1 :=
  Subtype.ext (by
    rw [Subalgebra.coe_mul, coe_chartIncl, coe_chartIncl, coe_jChartFin, coe_jInvChartInf,
      Subalgebra.coe_one, mul_inv_cancel₀ (Fact.out : j ≠ 0)])

abbrev U : (X₀).Opens := (ιFin R F j) ''ᵁ ⊤

abbrev V : (X₀).Opens := (ιInf R F j) ''ᵁ ⊤

theorem U_eq : U R F j = chartFinOpen R F j := (ιFin R F j).image_top_eq_opensRange
theorem V_eq : V R F j = chartInfOpen R F j := (ιInf R F j).image_top_eq_opensRange

def sF : Γ(XFin R F j, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of (chartAlgFin R F j))).inv (jChartFin R F j)

def sI : Γ(XInf R F j, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of (chartAlgInf R F j))).inv (jInvChartInf R F j)

def f : Γ(X₀, U R F j) := ((ιFin R F j).appIso ⊤).inv (sF R F j)

def g : Γ(X₀, V R F j) := ((ιInf R F j).appIso ⊤).inv (sI R F j)

theorem basicOpen_sF : (XFin R F j).basicOpen (sF R F j) = (fFin R F j).opensRange := by
  apply TopologicalSpace.Opens.ext
  rw [sF, basicOpen_eq_of_affine]
  exact (range_fFin R F j).symm

theorem basicOpen_sI : (XInf R F j).basicOpen (sI R F j) = (fInf R F j).opensRange := by
  apply TopologicalSpace.Opens.ext
  rw [sI, basicOpen_eq_of_affine]
  exact (range_fInf R F j).symm

theorem image_opensRange {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) [IsOpenImmersion a]
    [IsOpenImmersion b] :
    b ''ᵁ a.opensRange = (a ≫ b).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext x
  constructor
  · rintro ⟨y, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, (Scheme.Hom.comp_apply a b u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨a.base u, ⟨u, rfl⟩, (Scheme.Hom.comp_apply a b u).symm⟩

theorem basicOpen_f : (X₀).basicOpen (f R F j) = (ιMid R F j).opensRange := by
  rw [f, ← Scheme.image_basicOpen, basicOpen_sF, image_opensRange]

theorem opensRange_ιMid' : (fInf R F j ≫ ιInf R F j).opensRange = (ιMid R F j).opensRange := by
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_opensRange]
  rw [← ιMid_eq']

theorem basicOpen_g : (X₀).basicOpen (g R F j) = (ιMid R F j).opensRange := by
  rw [g, ← Scheme.image_basicOpen, basicOpen_sI, image_opensRange, opensRange_ιMid']

theorem U_inf_V : U R F j ⊓ V R F j = (ιMid R F j).opensRange := by
  apply le_antisymm
  · intro x hx
    obtain ⟨⟨x₀, -, hx₀⟩, ⟨xi, -, hxi⟩⟩ := hx
    obtain ⟨u, rfl, rfl⟩ := (ιFin_eq_ιInf_iff R F j x₀ xi).mp (hx₀.trans hxi.symm)
    exact ⟨u, hx₀⟩
  · rintro x ⟨u, rfl⟩
    refine ⟨⟨(fFin R F j).base u, trivial, rfl⟩, ⟨(fInf R F j).base u, trivial, ?_⟩⟩
    change (fInf R F j ≫ ιInf R F j).base u = (fFin R F j ≫ ιFin R F j).base u
    rw [glue_condition]

theorem presheaf_map_map_apply {Y : Scheme.{u}} {A B C : Y.Opens} (i : op A ⟶ op B) (i' : op B ⟶ op C)
    (i'' : op A ⟶ op C) (t : Γ(Y, A)) :
    Y.presheaf.map i' (Y.presheaf.map i t) = Y.presheaf.map i'' t := by
  rw [Subsingleton.elim i'' (i ≫ i'), Functor.map_comp, CommRingCat.comp_apply]

theorem presheaf_map_map_map_apply {Y : Scheme.{u}} {A B C D : Y.Opens} (i : op A ⟶ op B) (i' : op B ⟶ op C)
    (i'' : op C ⟶ op D) (k : op A ⟶ op D) (t : Γ(Y, A)) :
    Y.presheaf.map i'' (Y.presheaf.map i' (Y.presheaf.map i t)) = Y.presheaf.map k t := by
  rw [presheaf_map_map_apply i i' (i ≫ i'), presheaf_map_map_apply (i ≫ i') i'' k]

theorem app_res_f (W : (X₀).Opens) (hWU : W ≤ U R F j) :
    (ιMid R F j).app W ((X₀).presheaf.map (homOfLE hWU).op (f R F j)) =
      (XMid R F j).presheaf.map (homOfLE le_top).op ((fFin R F j).appTop (sF R F j)) := by
  have step1 : (ιMid R F j).app W ((X₀).presheaf.map (homOfLE hWU).op (f R F j)) =
      (XMid R F j).presheaf.map ((TopologicalSpace.Opens.map (ιMid R F j).base).map (homOfLE hWU)).op
        ((ιMid R F j).app (U R F j) (f R F j)) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  have step2 : (ιMid R F j).app (U R F j) (f R F j) =
      (fFin R F j).app _ ((ιFin R F j).app (U R F j) (f R F j)) := rfl
  have step4 : ∀ {V' : (XFin R F j).Opens} (k : op ⊤ ⟶ op V'),
      (fFin R F j).app V' ((XFin R F j).presheaf.map k (sF R F j)) =
        (XMid R F j).presheaf.map ((TopologicalSpace.Opens.map (fFin R F j).base).map k.unop).op
          ((fFin R F j).appTop (sF R F j)) := fun k => by
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  rw [step1, step2, f, Scheme.Hom.appIso_inv_app_apply, step4]
  exact presheaf_map_map_apply _ _ _ _

theorem app_res_g (W : (X₀).Opens) (hWV : W ≤ V R F j) :
    (ιMid R F j).app W ((X₀).presheaf.map (homOfLE hWV).op (g R F j)) =
      (XMid R F j).presheaf.map (homOfLE le_top).op ((fInf R F j).appTop (sI R F j)) := by
  rw [Scheme.Hom.congr_app (ιMid_eq' R F j) W, CommRingCat.comp_apply]
  have step1 : (fInf R F j ≫ ιInf R F j).app W ((X₀).presheaf.map (homOfLE hWV).op (g R F j)) =
      (XMid R F j).presheaf.map ((TopologicalSpace.Opens.map (fInf R F j ≫ ιInf R F j).base).map (homOfLE hWV)).op
        ((fInf R F j ≫ ιInf R F j).app (V R F j) (g R F j)) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  have step2 : (fInf R F j ≫ ιInf R F j).app (V R F j) (g R F j) =
      (fInf R F j).app _ ((ιInf R F j).app (V R F j) (g R F j)) := rfl
  have step4 : ∀ {V' : (XInf R F j).Opens} (k : op ⊤ ⟶ op V'),
      (fInf R F j).app V' ((XInf R F j).presheaf.map k (sI R F j)) =
        (XMid R F j).presheaf.map ((TopologicalSpace.Opens.map (fInf R F j).base).map k.unop).op
          ((fInf R F j).appTop (sI R F j)) := fun k => by
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  rw [step1, step2, g, Scheme.Hom.appIso_inv_app_apply, step4]
  exact presheaf_map_map_map_apply _ _ _ _ _

theorem appTop_sF : (fFin R F j).appTop (sF R F j) =
    (Scheme.ΓSpecIso (CommRingCat.of (chartAlgMid R F j))).inv (inclFin R F j (jChartFin R F j)) := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (inclFin R F j).toRingHom)
  have h' := congrArg (fun φ => φ.hom (jChartFin R F j)) h
  simp only [CommRingCat.comp_apply] at h'
  exact h'.symm

theorem appTop_sI : (fInf R F j).appTop (sI R F j) =
    (Scheme.ΓSpecIso (CommRingCat.of (chartAlgMid R F j))).inv (inclInf R F j (jInvChartInf R F j)) := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (inclInf R F j).toRingHom)
  have h' := congrArg (fun φ => φ.hom (jInvChartInf R F j)) h
  simp only [CommRingCat.comp_apply] at h'
  exact h'.symm

theorem res_f_mul_res_g :
    ((X₀).presheaf.map (homOfLE (inf_le_left : U R F j ⊓ V R F j ≤ U R F j)).op).hom (f R F j) *
      ((X₀).presheaf.map (homOfLE (inf_le_right : U R F j ⊓ V R F j ≤ V R F j)).op).hom (g R F j) = 1 := by
  have hWle : U R F j ⊓ V R F j ≤ (ιMid R F j).opensRange := (U_inf_V R F j).le

  haveI : IsIso ((ιMid R F j).app (U R F j ⊓ V R F j)) := Scheme.Hom.isIso_app _ _ hWle
  have hinj : Function.Injective ((ιMid R F j).app (U R F j ⊓ V R F j)) :=
    (ConcreteCategory.bijective_of_isIso ((ιMid R F j).app (U R F j ⊓ V R F j))).1
  apply hinj
  rw [map_mul, map_one, app_res_f, app_res_g, appTop_sF, appTop_sI, ← map_mul, ← map_mul,
    inclFin_j_mul_inclInf_jInv, map_one, map_one]

theorem charts_aux :
    ∃ (f' : Γ(X₀, U R F j)) (g' : Γ(X₀, V R F j)),
      U R F j ⊓ V R F j = (X₀).basicOpen f' ∧ U R F j ⊓ V R F j = (X₀).basicOpen g' ∧
      ((X₀).presheaf.map (homOfLE (inf_le_left : U R F j ⊓ V R F j ≤ U R F j)).op).hom f' *
        ((X₀).presheaf.map (homOfLE (inf_le_right : U R F j ⊓ V R F j ≤ V R F j)).op).hom g' = 1 :=
  ⟨f R F j, g R F j, (U_inf_V R F j).trans (basicOpen_f R F j).symm, (U_inf_V R F j).trans (basicOpen_g R F j).symm,
    res_f_mul_res_g R F j⟩

end AlgebraicCurve.TwoChartIntegralModel.ChartsGen
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint.AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint.AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint.AlgebraicCurve.TwoChartIntegralModel.ChartsGen"
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint.AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint.AlgebraicCurve.TwoChartIntegralModel"
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint.AlgebraicCurve"

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "TwoChartIntegralModel.chartAlgFin TwoChartIntegralModel.jChartFin TwoChartIntegralModel TwoChartIntegralModel.ιFin CurveModel" namespace TwoChartIntegralModel p2m_export "AlgebraicCurve.TwoChartIntegralModel" "coe_chartIncl chartAlgFin chartAlgInf chartAlgMid jChartFin jInvChartInf coe_jChartFin coe_jInvChartInf inclFin inclInf isLocalization_away_inclFin isLocalization_away_inclInf XFin XInf XMid fFin fInf ιFin ιInf glue_condition mem_range_ιFin_or_mem_range_ιInf chartFinOpen chartInfOpen fibre" end AlgebraicCurve.TwoChartIntegralModel
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel" in

theorem AlgebraicCurve.TwoChartIntegralModel.mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] (M : CurveModel K L)
    (Φ : M.C ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
    [hMne : Nonempty (Scheme.Opens.toScheme (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)))]
    (x : closedPoints M.C)
    (hj : M.ffEquiv.symm (M.C.germToFunctionField (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤))
        ((Φ.app ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin R F j).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin R F j))).inv (TwoChartIntegralModel.jChartFin R F j)))))
        ∈ (M.placeOfPoint x).toValuationSubring) :
    Φ.base x.1 ∈ Set.range (TwoChartIntegralModel.ιFin R F j).base := by
  set xj := M.ffEquiv.symm (M.C.germToFunctionField (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤))
        ((Φ.app ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin R F j).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin R F j))).inv (TwoChartIntegralModel.jChartFin R F j))))) with hxj
  classical
  by_contra hxU

  have hUV := ChartsGen.U_inf_V R F j
  have hbg := ChartsGen.basicOpen_g R F j

  have hxV : Φ.base x.1 ∈ ChartsGen.V R F j := by
    rcases mem_range_ιFin_or_mem_range_ιInf R F j (Φ.base x.1) with h | h
    · exact absurd h hxU
    · rw [ChartsGen.V_eq]; exact h

  set t : Γ(M.C, Φ ⁻¹ᵁ ChartsGen.V R F j) :=
    (Φ.app (ChartsGen.V R F j)).hom (ChartsGen.g R F j) with ht
  have hnot : ¬ IsUnit ((M.C.presheaf.germ (Φ ⁻¹ᵁ ChartsGen.V R F j) x.1 hxV).hom t) := by
    intro hunit
    have hmem : x.1 ∈ M.C.basicOpen t := (Scheme.mem_basicOpen M.C t x.1 hxV).mpr hunit
    rw [ht, ← Scheme.preimage_basicOpen, hbg] at hmem

    apply hxU
    have h2 : Φ.base x.1 ∈ ChartsGen.U R F j ⊓ ChartsGen.V R F j := by
      rw [hUV]; exact hmem
    have h3 : Φ.base x.1 ∈ ChartsGen.U R F j := h2.1
    rw [ChartsGen.U_eq] at h3
    exact h3

  have hηU : genericPoint M.C ∈ Φ ⁻¹ᵁ ChartsGen.U R F j := by
    obtain ⟨⟨y, hy⟩⟩ := hMne
    exact (genericPoint_specializes y).mem_open (Φ ⁻¹ᵁ ChartsGen.U R F j).2 hy
  have hηV : genericPoint M.C ∈ Φ ⁻¹ᵁ ChartsGen.V R F j :=
    (genericPoint_specializes x.1).mem_open (Φ ⁻¹ᵁ ChartsGen.V R F j).2 hxV

  set s : Γ(M.C, Φ ⁻¹ᵁ ChartsGen.U R F j) :=
    (Φ.app (ChartsGen.U R F j)).hom (ChartsGen.f R F j) with hs

  have hηW : genericPoint M.C ∈ Φ ⁻¹ᵁ (ChartsGen.U R F j ⊓ ChartsGen.V R F j) := ⟨hηU, hηV⟩
  have hprod : (M.C.presheaf.germ _ (genericPoint M.C) hηU).hom s *
      (M.C.presheaf.germ _ (genericPoint M.C) hηV).hom t = 1 := by
    have key := ChartsGen.res_f_mul_res_g R F j

    have e1 : (M.C.presheaf.germ _ (genericPoint M.C) hηU).hom s =
        (M.C.presheaf.germ _ (genericPoint M.C) hηW).hom
          ((Φ.app (ChartsGen.U R F j ⊓ ChartsGen.V R F j)).hom
            (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.map (homOfLE (inf_le_left : ChartsGen.U R F j ⊓ ChartsGen.V R F j ≤ ChartsGen.U R F j)).op).hom
              (ChartsGen.f R F j))) := by
      have nat := congrArg (fun φ => φ.hom (ChartsGen.f R F j))
        (Φ.naturality (homOfLE (inf_le_left : ChartsGen.U R F j ⊓ ChartsGen.V R F j ≤ ChartsGen.U R F j)).op)
      simp only [CommRingCat.comp_apply] at nat
      rw [nat, TopCat.Presheaf.germ_res_apply, hs]
    have e2 : (M.C.presheaf.germ _ (genericPoint M.C) hηV).hom t =
        (M.C.presheaf.germ _ (genericPoint M.C) hηW).hom
          ((Φ.app (ChartsGen.U R F j ⊓ ChartsGen.V R F j)).hom
            (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.map (homOfLE (inf_le_right : ChartsGen.U R F j ⊓ ChartsGen.V R F j ≤ ChartsGen.V R F j)).op).hom
              (ChartsGen.g R F j))) := by
      have nat := congrArg (fun φ => φ.hom (ChartsGen.g R F j))
        (Φ.naturality (homOfLE (inf_le_right : ChartsGen.U R F j ⊓ ChartsGen.V R F j ≤ ChartsGen.V R F j)).op)
      simp only [CommRingCat.comp_apply] at nat
      rw [nat, TopCat.Presheaf.germ_res_apply, ht]
    rw [e1, e2, ← map_mul, ← map_mul, key, map_one, map_one]

  have hpin : (M.C.presheaf.germ _ (genericPoint M.C) hηU).hom s = M.ffEquiv xj := by
    rw [hxj, RingEquiv.apply_symm_apply]
    rfl

  obtain ⟨r, hr⟩ : ∃ r : M.C.presheaf.stalk x.1,
      algebraMap (M.C.presheaf.stalk x.1) M.C.functionField r = M.ffEquiv (xj) := by
    have hj' : xj ∈ (M.placeOfPoint x).toValuationSubring.toSubring := hj
    rw [← M.range_stalk_eq x] at hj'
    obtain ⟨r, hr⟩ := RingHom.mem_range.mp hj'
    refine ⟨r, ?_⟩
    rw [← RingEquiv.symm_apply_eq]
    exact hr

  have htη : algebraMap (M.C.presheaf.stalk x.1) M.C.functionField
      ((M.C.presheaf.germ (Φ ⁻¹ᵁ ChartsGen.V R F j) x.1 hxV).hom t) =
      (M.C.presheaf.germ _ (genericPoint M.C) hηV).hom t := by
    show (M.C.presheaf.stalkSpecializes (genericPoint_specializes x.1)).hom _ = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]

  have hinj : Function.Injective (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField) :=
    IsFractionRing.injective (M.C.presheaf.stalk x.1) M.C.functionField
  apply hnot
  refine isUnit_iff_exists_inv.mpr ⟨r, ?_⟩
  apply hinj
  rw [map_mul, map_one, htη, hr, ← hpin, mul_comm]
  exact hprod

end
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint.AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint.AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint.AlgebraicCurve.TwoChartIntegralModel.ChartsGen"

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] (M : CurveModel K L)
    (Φ : M.C ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
    [hMne : Nonempty (Scheme.Opens.toScheme (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)))]
    (x : closedPoints M.C)
    (hj : M.ffEquiv.symm (M.C.germToFunctionField (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤))
        ((Φ.app ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin R F j).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin R F j))).inv (TwoChartIntegralModel.jChartFin R F j)))))
        ∈ (M.placeOfPoint x).toValuationSubring) :
    Φ.base x.1 ∈ Set.range (TwoChartIntegralModel.ιFin R F j).base :=
  AlgebraicCurve.TwoChartIntegralModel.mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint R F j M Φ x hj

end S_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint (solution)
