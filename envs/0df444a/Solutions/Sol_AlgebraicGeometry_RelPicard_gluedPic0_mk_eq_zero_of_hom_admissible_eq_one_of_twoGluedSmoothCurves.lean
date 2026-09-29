-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.gluedPic0_mk_eq_zero_of_hom_admissible_eq_one_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/87b7db5c-2d60-54cb-815f-03ff84a9e1ad

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_GluedPic0_ker_toPic0Pair_eq_range_nodeUnit
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_isNodeUnitModule_one_unit
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_exists_eq_mul_of_iso
import Theorems.Thm_AlgebraicGeometry_exists_rationalPoint_enumeration_of_natCard_pullback_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_gluedPic0_mk_eq_zero_of_hom_admissible_eq_one_of_twoGluedSmoothCurves
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"
set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.TwoGluedCurves AlgebraicCurve"

namespace PhiInjAux

theorem eq_one_of_mul_self {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (y : SchemeHomOver t f)
    (h : G.mul t y y = y) : y = G.one t := by
  calc y = G.mul t (G.one t) y := (G.one_mul t y).symm
    _ = G.mul t (G.mul t (G.inv t y) y) y := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t y) (G.mul t y y) := by rw [G.mul_assoc]
    _ = G.mul t (G.inv t y) y := by rw [h]
    _ = G.one t := G.inv_mul_cancel t y

theorem surjective_algebraMap_residueField {K : Type u} [Field K] [IsAlgClosed K] {L : Type u} [Field L] [Algebra K L]
    (M : CurveModel K L) (v : Place K L) : Function.Surjective (algebraMap K v.ResidueField) := by
  classical
  obtain ⟨x, rfl⟩ := M.placeOfPoint_bijective.2 v
  let A : ValuationSubring L := (M.placeOfPoint x).toValuationSubring
  let S : CommRingCat := M.C.presheaf.stalk x.1

  let ρ : CommRingCat.of K ⟶ M.C.residueField x.1 :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ M.toBase.appTop ≫ M.C.Γevaluation x.1
  have hA : M.C.fromSpecResidueField x.1 ≫ M.toBase = Spec.map ρ := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    simp only [← Spec.map_comp]
    congr 1
    rw [Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of K) (M.toBase.base x.1)]
    simp only [ρ, Category.assoc, Scheme.residue_residueFieldMap, Scheme.Hom.germ_stalkMap_assoc]
    rfl

  have hρ : ρ = (residueFieldIsoBase M.toBase x.1 x.2).inv :=
    Spec.map_injective (by rw [← hA, SpecMap_residueFieldIsoBase_inv])
  have hρsurj : Function.Surjective ρ.hom := by
    rw [hρ]
    exact (ConcreteCategory.bijective_of_isIso ((residueFieldIsoBase M.toBase x.1 x.2).inv)).2

  let φ : S →+* L :=
    (M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp (algebraMap S M.C.functionField)
  have hφrange : φ.range = A.toSubring := M.range_stalk_eq x
  have hφmem : ∀ s : S, φ s ∈ A := fun s => by
    have h : φ s ∈ φ.range := ⟨s, rfl⟩
    rw [hφrange] at h
    exact h
  let ψ : S →+* A := φ.codRestrict A hφmem
  have hψ : ∀ s : S, (ψ s : L) = φ s := fun _ => rfl
  have hψinj : Function.Injective ψ := by
    intro a b h
    have h' : φ a = φ b := by rw [← hψ, ← hψ, h]
    exact IsFractionRing.injective S M.C.functionField (M.ffEquiv.symm.injective h')
  have hψsurj : Function.Surjective ψ := by
    intro a
    have ha : (a : L) ∈ φ.range := by rw [hφrange]; exact a.2
    obtain ⟨s, hs⟩ := ha
    exact ⟨s, Subtype.ext hs⟩
  let e : S ≃+* A := RingEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩

  let c : K → S := fun a =>
    M.C.presheaf.germ ⊤ x.1 trivial (M.toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))
  have hρc : ∀ a : K, ρ.hom a = IsLocalRing.residue S (c a) := fun _ => rfl
  have hgerm : ∀ t : Γ(M.C, ⊤), algebraMap S M.C.functionField (M.C.presheaf.germ ⊤ x.1 trivial t)
      = M.C.presheaf.germ ⊤ (genericPoint M.C) trivial t := by
    intro t
    change (M.C.presheaf.germ ⊤ x.1 trivial ≫ M.C.presheaf.stalkSpecializes
      ((genericPoint_spec M.C).specializes trivial)) t = _
    rw [TopCat.Presheaf.germ_stalkSpecializes]
  have hφc : ∀ a : K, φ (c a) = algebraMap K L a := by
    intro a
    have h1 : algebraMap S M.C.functionField (c a) = baseToFunctionField M.toBase a := hgerm _
    simp only [φ, RingHom.coe_comp, Function.comp_apply, h1, ← M.ffEquiv_algebraMap]
    exact M.ffEquiv.symm_apply_apply _
  have hψc : ∀ a : K, ψ (c a) = algebraMap K A a := fun a =>
    Subtype.ext (by rw [hψ, hφc]; rfl)

  intro r
  obtain ⟨g, rfl⟩ := IsLocalRing.residue_surjective (R := A) r
  obtain ⟨s, rfl⟩ := hψsurj g
  obtain ⟨a, ha⟩ := hρsurj (IsLocalRing.residue S s)
  refine ⟨a, ?_⟩
  rw [hρc] at ha
  have hm : c a - s ∈ IsLocalRing.maximalIdeal S := by
    rw [← Ideal.Quotient.eq]
    exact ha
  have hm' : ψ (c a - s) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' : IsUnit (c a - s) := by simpa using (show IsUnit (e (c a - s)) from hu).map e.symm
    exact ((IsLocalRing.mem_maximalIdeal _).mp hm) hu'
  have hres : IsLocalRing.residue A (ψ (c a)) = IsLocalRing.residue A (ψ s) := by
    rw [← sub_eq_zero, ← map_sub, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hm'
  change algebraMap K (IsLocalRing.ResidueField A) a = IsLocalRing.residue A (ψ s)
  rw [← hres, hψc]
  rfl

end PhiInjAux

open PhiInjAux in

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)

    (hc : pullback.snd i₁.1 i₂.1 ≫ c₂ = pullback.fst i₁.1 i₂.1 ≫ c₁)
    (ε : SchemeHomOver (𝟙 _) x) (ε₁ : SchemeHomOver (𝟙 _) c₁) (hε : ε₁.1 ≫ i₁.1 = ε.1)
    (ε₂ : SchemeHomOver (𝟙 _) c₂)
    (D : RelativePic0Designation k x) (hD : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (D₁ : RelativePic0Designation k c₁) (hD₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)
    (D₂ : RelativePic0Designation k c₂) (hD₂ : RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂)
    (ν₁ : SchemeHomOver D.toBase D₁.toBase) (ν₂ : SchemeHomOver D.toBase D₂.toBase)
    (hν₁ : ν₁ = RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁)
    (hν₂ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        Nonempty ((hD₂.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L)))

    (F : Type u) [Field F] [Algebra k F] [HasPrincipalDivisors k F] (hCB : ConstantsAreBase k F)
    (Mdl₁ : CurveModel k F) (e₁ : Mdl₁.C ≅ C₁) (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    (Mdl₂ : CurveModel k F) (e₂ : Mdl₂.C ≅ C₂) (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

    (Φ₁ : Pic0 k F ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₁.toBase)
    (hΦ₁_add : ∀ a b, Φ₁ (a + b) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).mul _ (Φ₁ a) (Φ₁ b))
    (hΦ₁ : ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (Dv : Divisor.degZero (K := k) (F := F)),
      (Dv : Divisor k F) =
        Finsupp.single (Mdl₁.pointEquivPlace ⟨P.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact P.2⟩) 1 -
          Finsupp.single (Mdl₁.pointEquivPlace ⟨ε₁.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact ε₁.2⟩) 1 →
      Nonempty ((hD₁.poincare.pullbackAlong (Φ₁ (Pic0.mk Dv))).L ≅
        (RelEffCartierDiv.ofPoint c₁ P.1 P.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₁ ε₁.1 ε₁.2).idealModule))
    (Φ₂ : Pic0 k F ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase)
    (hΦ₂_add : ∀ a b, Φ₂ (a + b) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).mul _ (Φ₂ a) (Φ₂ b))
    (hΦ₂ : ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂) (Dv : Divisor.degZero (K := k) (F := F)),
      (Dv : Divisor k F) =
        Finsupp.single (Mdl₂.pointEquivPlace ⟨P.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact P.2⟩) 1 -
          Finsupp.single (Mdl₂.pointEquivPlace ⟨ε₂.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact ε₂.2⟩) 1 →
      Nonempty ((hD₂.poincare.pullbackAlong (Φ₂ (Pic0.mk Dv))).L ≅
        (RelEffCartierDiv.ofPoint c₂ P.1 P.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₂ ε₂.1 ε₂.2).idealModule))

    (S : Finset (Place k F × Place k F))
    (nd : ↥S ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (pullback.fst i₁.1 i₂.1 ≫ c₁))
    (hS : ∀ σ : ↥S,
        (σ : Place k F × Place k F).1 = Mdl₁.pointEquivPlace ⟨((nd σ).1 ≫ pullback.fst i₁.1 i₂.1) ≫ e₁.inv,
            by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc, Category.assoc]; exact (nd σ).2⟩ ∧
        (σ : Place k F × Place k F).2 = Mdl₂.pointEquivPlace ⟨((nd σ).1 ≫ pullback.snd i₁.1 i₂.1) ≫ e₂.inv,
            by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc, Category.assoc, hc]; exact (nd σ).2⟩)

    (φ : ↥(GluingData.admissible S) → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase)
    (hφ_mul : ∀ a b, φ (a + b) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _ (φ a) (φ b))
    (hφ_princ : ∀ a : ↥(GluingData.admissible S), GluingData.IsGluedPrincipal S (a : GluingData k F S) →
        φ a = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).one _)
    (hφ_res : ∀ a : ↥(GluingData.admissible S), postComp ν₁ (φ a) = Φ₁ (Pic0.mk ⟨(a : GluingData k F S).1, a.2.1⟩) ∧
        postComp ν₂ (φ a) = Φ₂ (Pic0.mk ⟨(a : GluingData k F S).2.1, a.2.2.1⟩))
    (hφ_node : ∀ w : ↥S → Additive kˣ,
        IsNodeUnitModule x i₁ i₂
          (fun σ => ⟨(nd σ).1 ≫ pullback.fst i₁.1 i₂.1, by rw [Category.assoc]; exact (nd σ).2⟩)
          (fun σ => ⟨(nd σ).1 ≫ pullback.snd i₁.1 i₂.1, by rw [Category.assoc, hc]; exact (nd σ).2⟩)
          (𝟙 (Spec (CommRingCat.of k)))
          (fun σ => Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom (Additive.toMul (w σ))⁻¹)
          (hD.poincare.pullbackAlong (φ ⟨(0, 0, w), GluingData.zero_zero_mem_admissible S w⟩)).L)

    (hν₁_mul : ∀ a b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase,
        postComp ν₁ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _ a b) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).mul _ (postComp ν₁ a) (postComp ν₁ b))
    (hν₂_mul : ∀ a b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase,
        postComp ν₂ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _ a b) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).mul _ (postComp ν₂ a) (postComp ν₂ b))
    (a : ↥(GluingData.admissible S))
    (ha : φ a = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).one _) :
    GluedPic0.mk S a = 0 := by
  classical
  haveI : IsReduced X := hXred

  set law := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD with hlaw
  set law₁ := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁ with hlaw₁
  set law₂ := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂ with hlaw₂

  have hone₁ : postComp ν₁ (law.one (𝟙 (Spec (CommRingCat.of k)))) = law₁.one (𝟙 (Spec (CommRingCat.of k))) := by
    apply eq_one_of_mul_self
    have h := hν₁_mul (law.one _) (law.one _)
    rw [law.one_mul] at h
    exact h.symm
  have hone₂ : postComp ν₂ (law.one (𝟙 (Spec (CommRingCat.of k)))) = law₂.one (𝟙 (Spec (CommRingCat.of k))) := by
    apply eq_one_of_mul_self
    have h := hν₂_mul (law.one _) (law.one _)
    rw [law.one_mul] at h
    exact h.symm

  have hΦ₁0 : Φ₁ 0 = law₁.one (𝟙 (Spec (CommRingCat.of k))) := by
    apply eq_one_of_mul_self
    have h := hΦ₁_add 0 0
    rw [add_zero] at h
    exact h.symm
  have hΦ₂0 : Φ₂ 0 = law₂.one (𝟙 (Spec (CommRingCat.of k))) := by
    apply eq_one_of_mul_self
    have h := hΦ₂_add 0 0
    rw [add_zero] at h
    exact h.symm

  have hcls : GluedPic0.toPic0Pair S (GluedPic0.mk S a) = 0 := by
    have h := hφ_res a
    rw [ha, hone₁, hone₂, ← hΦ₁0, ← hΦ₂0] at h
    rw [GluedPic0.toPic0Pair_mk]
    exact Prod.ext (Φ₁.injective h.1).symm (Φ₂.injective h.2).symm

  have hrat : ∀ s : ↥S,
      Function.Surjective (algebraMap k ((s : Place k F × Place k F).1.ResidueField)) ∧
        Function.Surjective (algebraMap k ((s : Place k F × Place k F).2.ResidueField)) := fun s =>
    ⟨surjective_algebraMap_residueField Mdl₁ _, surjective_algebraMap_residueField Mdl₁ _⟩

  obtain ⟨w, hw⟩ : ∃ w, GluedPic0.nodeUnit S w = GluedPic0.mk S a := by
    have hmem : GluedPic0.mk S a ∈ (GluedPic0.toPic0Pair S).ker := hcls
    rw [AlgebraicCurve.GluedPic0.ker_toPic0Pair_eq_range_nodeUnit S hrat] at hmem
    exact hmem

  have hφw : φ ⟨(0, 0, w), GluingData.zero_zero_mem_admissible S w⟩ = law.one (𝟙 (Spec (CommRingCat.of k))) := by
    set b : ↥(GluingData.admissible S) := ⟨(0, 0, w), GluingData.zero_zero_mem_admissible S w⟩ with hb
    have hab : GluedPic0.mk S a = GluedPic0.mk S b := by rw [← hw, GluedPic0.nodeUnit_apply]
    rw [GluedPic0.mk_eq_mk_iff] at hab
    have hp : φ (-a + b) = law.one _ := hφ_princ (-a + b) (by simpa using hab)
    have h1 : φ b = law.mul _ (φ a) (φ (-a + b)) := by rw [← hφ_mul, add_neg_cancel_left]
    rw [h1, hp, ha, law.one_mul]

  have hnu := hφ_node w
  rw [hφw] at hnu

  have htriv : Nonempty ((hD.poincare.pullbackAlong (law.one (𝟙 (Spec (CommRingCat.of k))))).L ≅
      SheafOfModules.unit (pullback x (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf) := by
    have h1 : law.one (𝟙 (Spec (CommRingCat.of k))) = ⟨D.zeroSection, D.zeroSection_toBase⟩ :=
      Subtype.ext (RepresentsRelSubPic.relativeGroupLaw_one (P := algEquivZeroGroupCut x ε) hD)
    rw [h1]
    exact hD.zero

  have hnode : ∀ σ : ↥S, ((nd σ).1 ≫ pullback.fst i₁.1 i₂.1) ≫ i₁.1 = ((nd σ).1 ≫ pullback.snd i₁.1 i₂.1) ≫ i₂.1 :=
    fun σ => by simp only [Category.assoc, pullback.condition]
  have hinj : Function.Injective fun σ : ↥S => ((nd σ).1 ≫ pullback.fst i₁.1 i₂.1).base (IsLocalRing.closedPoint k) := by
    intro σ τ h
    apply nd.injective
    apply Subtype.ext
    have h' : (nd σ).1.base (IsLocalRing.closedPoint k) = (nd τ).1.base (IsLocalRing.closedPoint k) := by
      apply (pullback.fst i₁.1 i₂.1).isClosedEmbedding.injective
      simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using h
    exact ext_of_apply_closedPoint_eq (pullback.fst i₁.1 i₂.1 ≫ c₁) (nd σ).2 (nd τ).2 h'
  have hinter : ∀ (q₁ : C₁) (q₂ : C₂), i₁.1.base q₁ = i₂.1.base q₂ →
      ∃ σ : ↥S, q₁ = ((nd σ).1 ≫ pullback.fst i₁.1 i₂.1).base (IsLocalRing.closedPoint k) ∧
        q₂ = ((nd σ).1 ≫ pullback.snd i₁.1 i₂.1).base (IsLocalRing.closedPoint k) := by
    obtain ⟨p₁, p₂, -, hnode', hinter'⟩ :=
      AlgebraicGeometry.exists_rationalPoint_enumeration_of_natCard_pullback_eq k x i₁ i₂ s hs hs0
    intro q₁ q₂ hq
    obtain ⟨j, hq₁, hq₂⟩ := hinter' q₁ q₂ hq
    let z : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (pullback.fst i₁.1 i₂.1 ≫ c₁) :=
      ⟨pullback.lift (p₁ j).1 (p₂ j).1 (hnode' j), by rw [pullback.lift_fst_assoc]; exact (p₁ j).2⟩
    refine ⟨nd.symm z, ?_, ?_⟩
    · rw [Equiv.apply_symm_apply, hq₁]
      simp only [z, pullback.lift_fst]
    · rw [Equiv.apply_symm_apply, hq₂]
      simp only [z, pullback.lift_snd]
  have h1 : IsNodeUnitModule x i₁ i₂
      (fun σ => ⟨(nd σ).1 ≫ pullback.fst i₁.1 i₂.1, by rw [Category.assoc]; exact (nd σ).2⟩)
      (fun σ => ⟨(nd σ).1 ≫ pullback.snd i₁.1 i₂.1, by rw [Category.assoc, hc]; exact (nd σ).2⟩)
      (𝟙 (Spec (CommRingCat.of k))) 1 (SheafOfModules.unit (pullback x (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf) :=
    AlgebraicGeometry.TwoGluedCurves.isNodeUnitModule_one_unit k x i₁ i₂ hjs _ _ hinj hnode hinter hcr (𝟙 _)

  haveI : IsIntegral C₁ := GeometricallyIntegral.isIntegral_of_subsingleton c₁
  haveI : IsIntegral C₂ := GeometricallyIntegral.isIntegral_of_subsingleton c₂
  obtain ⟨cst, hcst⟩ : ∃ cst : kˣ, ∀ σ, Additive.toMul (w σ) = cst := by
    obtain ⟨c0, hc0⟩ := AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.exists_eq_mul_of_iso k x i₁ i₂ hjs _ _ hinj hnode
      hinter hcr (hD.poincare.pullbackAlong (law.one (𝟙 (Spec (CommRingCat.of k))))).isInvertible
      (Scheme.Modules.isInvertible_unit _) hnu h1 htriv
    refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom c0, fun σ => ?_⟩

    have h := hc0 σ
    rw [map_inv, eq_mul_inv_iff_mul_eq, Pi.one_apply, one_mul] at h

    rw [← h, ← MonoidHom.comp_apply, ← Units.map_comp]
    ext
    simp only [Units.coe_map, MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    exact (CategoryTheory.Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of k)) _).symm

  rw [← hw]
  have : w = fun _ => Additive.ofMul cst := funext fun σ => by rw [← hcst σ]; rfl
  rw [this]
  exact GluedPic0.nodeUnit_const S cst

end S_AlgebraicGeometry_RelPicard_gluedPic0_mk_eq_zero_of_hom_admissible_eq_one_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_gluedPic0_mk_eq_zero_of_hom_admissible_eq_one_of_twoGluedSmoothCurves (solution)
