-- Prove2me | solution 1 for AlgebraicCurve.Pic0.exists_semilinear_hom_of_pushforwardAlong_frobenius_of_representsRelSubPic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/7ce51635-dc17-57dd-9bf1-441a96d181d1

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_semilinear_iso_pointEquivPlace_eq_restrictAlong_frobenius
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_exists_semilinear_hom_of_pushforwardAlong_frobenius_of_representsRelSubPic
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero AlgebraicCurve.Divisor.congr_single AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve"

universe u v w

noncomputable section

namespace P2mSemilin

variable {K : Type u} [Field K]

section FAE

variable {C : Scheme.{u}} (c : C ⟶ (Spec (.of K)))

theorem fae_pullback_of_comp_snd {T : Scheme.{u}} {t₁ t₂ : T ⟶ (Spec (.of K))}
    (Θ : pullback c t₁ ⟶ pullback c t₂) (hΘ : Θ ≫ pullback.snd c t₂ = pullback.snd c t₁)
    {L : (pullback c t₂).Modules}
    (hL : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      IsAlgEquivZero (fibreAt c t₂ s) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t₂) s)).obj L))
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T) :
    IsAlgEquivZero (fibreAt c t₁ s)
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t₁) s)).obj
        ((Scheme.Modules.pullback Θ).obj L)) := by
  let e : Limits.pullback (pullback.snd c t₁) s ⟶ Limits.pullback (pullback.snd c t₂) s :=
    pullback.map _ _ _ _ Θ (𝟙 _) (𝟙 T) (by rw [Category.comp_id, hΘ]) (by simp)
  have he : e ≫ fibreAt c t₂ s = fibreAt c t₁ s := by
    simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e ≫ pullback.fst (pullback.snd c t₂) s = pullback.fst (pullback.snd c t₁) s ≫ Θ := by
    simp only [e, pullback.lift_fst]
  refine IsAlgEquivZero.of_iso ?_ ((hL k s).pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app L ≪≫
    (Scheme.Modules.pullbackCongr hfst).app L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app L).symm

theorem fae_tensor_pullbackSnd {T : Scheme.{u}} {t : T ⟶ (Spec (.of K))} {L : (pullback c t).Modules}
    (hL : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      IsAlgEquivZero (fibreAt c t s) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj L))
    {N : T.Modules} (hN : Scheme.Modules.IsInvertible N)
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T) :
    IsAlgEquivZero (fibreAt c t s)
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj
        (L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj N)) := by
  have hsq : pullback.fst (pullback.snd c t) s ≫ pullback.snd c t = fibreAt c t s ≫ s := pullback.condition
  obtain ⟨u⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k
    ((Scheme.Modules.pullback s).obj N) (hN.pullback s)

  have triv : (Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj
      ((Scheme.Modules.pullback (pullback.snd c t)).obj N) ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackComp _ _).app N ≪≫
      (Scheme.Modules.pullbackCongr hsq).app N ≪≫
      ((Scheme.Modules.pullbackComp _ _).app N).symm ≪≫
      (Scheme.Modules.pullback _).mapIso u ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso _
  refine IsAlgEquivZero.of_iso ?_ (hL k s)
  exact (ρ_ _).symm ≪≫ (Iso.refl _ ⊗ᵢ triv.symm) ≪≫ (Scheme.Modules.pullbackTensorObjIso _ _ _).symm

end FAE

section Twist

variable {C : Scheme.{u}} {c : C ⟶ (Spec (.of K))} {ε : SchemeHomOver (𝟙 (Spec (.of K))) c}
  {D : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
  (e : (Spec (.of K)) ⟶ (Spec (.of K))) [IsIso e] (B : C ≅ C) (hB : B.hom ≫ c ≫ e = c)

include hB in
omit [IsIso e] in
theorem inv_comp_base : B.inv ≫ c = c ≫ e :=
  B.inv_comp_eq.mpr (by simpa only [Category.assoc] using hB.symm)

include hB in
theorem hom_comp_base : B.hom ≫ c = c ≫ inv e :=
  (IsIso.eq_comp_inv e).mpr (by simpa only [Category.assoc] using hB)

def tw (D : RelativePic0Designation K c) (e : (Spec (.of K)) ⟶ (Spec (.of K))) [IsIso e] : D.P ⟶ (Spec (.of K)) := D.toBase ≫ inv e

def Theta : pullback c (tw D e) ⟶ pullback c D.toBase :=
  pullback.lift (pullback.fst _ _ ≫ B.inv) (pullback.snd _ _) (by
    rw [Category.assoc, inv_comp_base e B hB, ← Category.assoc, pullback.condition, Category.assoc, tw,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id])

@[reassoc (attr := simp)]
theorem Theta_snd : Theta e B hB ≫ pullback.snd c D.toBase = pullback.snd c (tw D e) :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem Theta_fst : Theta (D := D) e B hB ≫ pullback.fst c D.toBase = pullback.fst c (tw D e) ≫ B.inv :=
  pullback.lift_fst _ _ _

def twistL : (pullback c (tw D e)).Modules := (Scheme.Modules.pullback (Theta e B hB)).obj h.poincare.L

theorem isInvertible_twistL : Scheme.Modules.IsInvertible (twistL h e B hB) :=
  h.poincare.isInvertible.pullback _

def twistBundle : RigidifiedLineBundle c ε (tw D e) :=
  RigidifiedLineBundle.ofInvertible (ε := ε) (twistL h e B hB) (isInvertible_twistL h e B hB)

theorem twistBundle_mem : FibrewiseAlgEquivZero (twistBundle h e B hB) := by
  intro k _ _ s
  have h1 := fae_pullback_of_comp_snd c (Theta e B hB) (Theta_snd e B hB) (L := h.poincare.L)
    (fun k _ _ s => h.poincare_mem k s)
  have hN := (((isInvertible_twistL h e B hB).pullback (rigSection c (tw D e) ε)).dual).1
  exact fae_tensor_pullbackSnd c h1 hN k s

def NB : SchemeHomOver (tw D e) D.toBase :=
  h.classify (tw D e) (twistBundle h e B hB) (twistBundle_mem h e B hB)

theorem NB_spec : Nonempty ((h.poincare.pullbackAlong (NB h e B hB)).L ≅ (twistBundle h e B hB).L) :=
  h.classify_spec _ _ _

theorem NB_comp : (NB h e B hB).1 ≫ D.toBase ≫ e = D.toBase := by
  rw [← Category.assoc, (NB h e B hB).2, tw, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

def Xi : pullback c (𝟙 (Spec (.of K))) ⟶ pullback c (𝟙 (Spec (.of K))) :=
  pullback.lift (pullback.fst _ _ ≫ B.inv) (pullback.snd _ _ ≫ e) (by
    rw [Category.assoc, inv_comp_base e B hB, ← Category.assoc, pullback.condition, Category.assoc,
      Category.assoc, Category.id_comp, Category.comp_id])

def XiInv : pullback c (𝟙 (Spec (.of K))) ⟶ pullback c (𝟙 (Spec (.of K))) :=
  pullback.lift (pullback.fst _ _ ≫ B.hom) (pullback.snd _ _ ≫ inv e) (by
    rw [Category.assoc, hom_comp_base e B hB, ← Category.assoc, pullback.condition, Category.assoc,
      Category.assoc, Category.id_comp, Category.comp_id])

omit [IsIso e] in
@[reassoc (attr := simp)]
theorem Xi_fst : Xi e B hB ≫ pullback.fst c (𝟙 (Spec (.of K))) = pullback.fst c (𝟙 (Spec (.of K))) ≫ B.inv := pullback.lift_fst _ _ _

omit [IsIso e] in
@[reassoc (attr := simp)]
theorem Xi_snd : Xi e B hB ≫ pullback.snd c (𝟙 (Spec (.of K))) = pullback.snd c (𝟙 (Spec (.of K))) ≫ e := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem XiInv_fst : XiInv e B hB ≫ pullback.fst c (𝟙 (Spec (.of K))) = pullback.fst c (𝟙 (Spec (.of K))) ≫ B.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem XiInv_snd : XiInv e B hB ≫ pullback.snd c (𝟙 (Spec (.of K))) = pullback.snd c (𝟙 (Spec (.of K))) ≫ inv e :=
  pullback.lift_snd _ _ _

scoped instance isIso_Xi : IsIso (Xi e B hB) :=
  ⟨XiInv e B hB, by apply pullback.hom_ext <;> simp, by apply pullback.hom_ext <;> simp⟩

def twistPt (p : SchemeHomOver (𝟙 (Spec (.of K))) D.toBase) : SchemeHomOver (𝟙 (Spec (.of K))) (tw D e) :=
  ⟨e ≫ p.1, by rw [tw, Category.assoc, ← Category.assoc p.1, p.2, Category.id_comp, IsIso.hom_inv_id]⟩

def Psi (p : SchemeHomOver (𝟙 (Spec (.of K))) D.toBase) : SchemeHomOver (𝟙 (Spec (.of K))) D.toBase :=
  postComp (NB h e B hB) (twistPt e p)

theorem Psi_coe (p : SchemeHomOver (𝟙 (Spec (.of K))) D.toBase) : (Psi h e B hB p).1 = e ≫ p.1 ≫ (NB h e B hB).1 := by
  simp [Psi, postComp, twistPt]

theorem baseChangeSnd_twistPt_Theta (p : SchemeHomOver (𝟙 (Spec (.of K))) D.toBase) :
    baseChangeSnd c (twistPt e p) ≫ Theta e B hB = Xi e B hB ≫ baseChangeSnd c p := by
  apply pullback.hom_ext
  · simp only [baseChangeSnd, twistPt, Category.assoc, Theta_fst, Xi_fst, pullback.lift_fst,
      pullback.lift_fst_assoc, Category.comp_id]
  · simp only [baseChangeSnd, twistPt, Category.assoc, Theta_snd, Xi_snd_assoc, pullback.lift_snd]

theorem poincare_Psi (p : SchemeHomOver (𝟙 (Spec (.of K))) D.toBase) :
    Nonempty ((h.poincare.pullbackAlong (Psi h e B hB p)).L ≅
      (RigidifiedLineBundle.ofInvertible (ε := ε)
        ((Scheme.Modules.pullback (Xi e B hB)).obj (h.poincare.pullbackAlong p).L)
        ((h.poincare.pullbackAlong p).isInvertible.pullback _)).L) := by
  obtain ⟨e1⟩ := NB_spec h e B hB
  obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := ε) (twistPt e p)
    (isInvertible_twistL h e B hB)

  have e3 : (Scheme.Modules.pullback (baseChangeSnd c (twistPt e p))).obj (twistL h e B hB) ≅
      (Scheme.Modules.pullback (Xi e B hB)).obj (h.poincare.pullbackAlong p).L :=
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr (baseChangeSnd_twistPt_Theta e B hB p)).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm
  obtain ⟨e4⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    ((isInvertible_twistL h e B hB).pullback (baseChangeSnd c (twistPt e p)))
    ((h.poincare.pullbackAlong p).isInvertible.pullback (Xi e B hB)) e3
  exact ⟨(h.poincare.pullbackAlongPullbackAlongIso' (NB h e B hB) (twistPt e p)).symm ≪≫
    (Scheme.Modules.pullback _).mapIso e1 ≪≫ e2 ≪≫ e4⟩

theorem poincare_mul {T : Scheme.{u}} (t : T ⟶ (Spec (.of K))) (x y : SchemeHomOver t D.toBase) :
    Nonempty ((h.poincare.pullbackAlong
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t x y)).L ≅
      (h.poincare.pullbackAlong x).L ⊗ (h.poincare.pullbackAlong y).L) :=
  RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := algEquivZeroGroupCut c ε) h (T := Over.mk t)
    (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)

theorem Psi_mul (p p' : SchemeHomOver (𝟙 (Spec (.of K))) D.toBase) :
    Psi h e B hB ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (𝟙 (Spec (.of K))) p p') =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (𝟙 (Spec (.of K)))
        (Psi h e B hB p) (Psi h e B hB p') := by
  obtain ⟨m⟩ := poincare_mul h (𝟙 (Spec (.of K))) p p'
  obtain ⟨m'⟩ := poincare_mul h (𝟙 (Spec (.of K))) (Psi h e B hB p) (Psi h e B hB p')
  obtain ⟨a⟩ := poincare_Psi h e B hB
    ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (𝟙 (Spec (.of K))) p p')
  obtain ⟨b⟩ := poincare_Psi h e B hB p
  obtain ⟨b'⟩ := poincare_Psi h e B hB p'
  have hp := (h.poincare.pullbackAlong p).isInvertible.pullback (Xi e B hB)
  have hp' := (h.poincare.pullbackAlong p').isInvertible.pullback (Xi e B hB)

  have t1 : (Scheme.Modules.pullback (Xi e B hB)).obj (h.poincare.pullbackAlong
      ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (𝟙 (Spec (.of K))) p p')).L ≅
      (Scheme.Modules.pullback (Xi e B hB)).obj (h.poincare.pullbackAlong p).L ⊗
        (Scheme.Modules.pullback (Xi e B hB)).obj (h.poincare.pullbackAlong p').L :=
    (Scheme.Modules.pullback _).mapIso m ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _
  obtain ⟨t2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    ((h.poincare.pullbackAlong _).isInvertible.pullback (Xi e B hB)) (hp.tensor hp') t1
  obtain ⟨t3⟩ := RigidifiedLineBundle.nonempty_ofInvertible_tensor_iso (ε := ε) hp hp'
  refine h.ext_of_iso (𝟙 (Spec (.of K))) _ _ ⟨a ≪≫ t2 ≪≫ t3 ≪≫ (b.symm ⊗ᵢ b'.symm) ≪≫ m'.symm⟩

section PointModules

def Bpt (y : SchemeHomOver (𝟙 (Spec (.of K))) c) : SchemeHomOver (𝟙 (Spec (.of K))) c :=
  ⟨e ≫ y.1 ≫ B.hom, by
    rw [Category.assoc, Category.assoc, hom_comp_base e B hB, ← Category.assoc y.1, y.2, Category.id_comp,
      IsIso.hom_inv_id]⟩

@[scoped simp] theorem Bpt_coe (y : SchemeHomOver (𝟙 (Spec (.of K))) c) : (Bpt e B hB y).1 = e ≫ y.1 ≫ B.hom := rfl

omit [IsIso e] in
theorem graphOver_comp_Xi (y : Spec (.of K) ⟶ C) (hy : y ≫ c = 𝟙 _) (y' : Spec (.of K) ⟶ C)
    (hy' : y' ≫ c = 𝟙 _) (hyy' : y' = e ≫ y ≫ B.hom) :
    graphOver c y' hy' ≫ Xi e B hB = e ≫ graphOver c y hy := by
  subst hyy'
  apply pullback.hom_ext
  · simp only [graphOver, Category.assoc, Xi_fst, pullback.lift_fst_assoc, Iso.hom_inv_id, Category.comp_id,
      pullback.lift_fst]
  · simp only [graphOver, Category.assoc, Xi_snd, pullback.lift_snd_assoc, Category.id_comp, pullback.lift_snd,
      Category.comp_id]

variable (aj : SchemeHomOver c D.toBase)

def ajPt (x : SchemeHomOver (𝟙 (Spec (.of K))) c) : SchemeHomOver (𝟙 (Spec (.of K))) D.toBase :=
  ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩

@[scoped simp] theorem ajPt_coe (x : SchemeHomOver (𝟙 (Spec (.of K))) c) : (ajPt aj x).1 = x.1 ≫ aj.1 := rfl

variable [IsSeparated c] [SmoothOfRelativeDimension 1 c]

theorem Xi_pointModules (y : Spec (.of K) ⟶ C) (hy : y ≫ c = 𝟙 _) (y' : Spec (.of K) ⟶ C)
    (hy' : y' ≫ c = 𝟙 _) (hyy' : y' = e ≫ y ≫ B.hom) :
    Nonempty ((Scheme.Modules.pullback (Xi e B hB)).obj (RelEffCartierDiv.ofPoint c y hy).lineBundle ≅
        (RelEffCartierDiv.ofPoint c y' hy').lineBundle) ∧
      Nonempty ((Scheme.Modules.pullback (Xi e B hB)).obj (RelEffCartierDiv.ofPoint c y hy).idealModule ≅
        (RelEffCartierDiv.ofPoint c y' hy').idealModule) := by
  have hg := graphOver_comp_Xi e B hB y hy y' hy' hyy'
  have hker : (e ≫ graphOver c y hy).ker = (graphOver c y hy).ker := Scheme.Hom.ker_comp_of_isIso _ _
  have hI : (e ≫ graphOver c y hy).ker.IsInvertible := by
    rw [hker]; exact RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c y hy)
  have hI' : (graphOver c y' hy').ker.IsInvertible := RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c y' hy')
  obtain ⟨⟨i1⟩, ⟨i2⟩⟩ := Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso (Xi e B hB)
    (e ≫ graphOver c y hy) (graphOver c y' hy') hg hI hI' 1
  rw [pow_one, pow_one, hker] at i1 i2
  exact ⟨⟨i1⟩, ⟨i2⟩⟩

set_option maxHeartbeats 6400000 in

theorem Psi_ajPt_mul
    (haj : ∀ x : SchemeHomOver (𝟙 (Spec (.of K))) c,
      Nonempty ((h.poincare.pullbackAlong (ajPt aj x)).L ≅
        (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c (𝟙 (Spec (.of K)) ≫ ε.1)
            ((Category.assoc _ _ _).trans ((congrArg (𝟙 (Spec (.of K)) ≫ ·) ε.2).trans
              (Category.comp_id _)))).idealModule))
    (x : SchemeHomOver (𝟙 (Spec (.of K))) c) :
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (𝟙 (Spec (.of K)))
        (Psi h e B hB (ajPt aj x)) (ajPt aj (Bpt e B hB ε)) = ajPt aj (Bpt e B hB x) := by
  have pε : (𝟙 (Spec (.of K)) ≫ ε.1) ≫ c = 𝟙 _ :=
    (Category.assoc _ _ _).trans ((congrArg (𝟙 (Spec (.of K)) ≫ ·) ε.2).trans (Category.comp_id _))

  obtain ⟨ePsi⟩ := poincare_Psi h e B hB (ajPt aj x)
  obtain ⟨ia⟩ := haj x
  obtain ⟨ib⟩ := haj (Bpt e B hB ε)
  obtain ⟨ig⟩ := haj (Bpt e B hB x)

  obtain ⟨⟨lx⟩, -⟩ := Xi_pointModules e B hB x.1 x.2 (Bpt e B hB x).1 (Bpt e B hB x).2 rfl
  obtain ⟨-, ⟨mε⟩⟩ := Xi_pointModules e B hB (𝟙 (Spec (.of K)) ≫ ε.1) pε (Bpt e B hB ε).1 (Bpt e B hB ε).2
    (by simp only [Bpt_coe, Category.id_comp])

  have hIb : Scheme.Modules.IsInvertible (RelEffCartierDiv.ofPoint c (Bpt e B hB ε).1 (Bpt e B hB ε).2).idealModule :=
    (RelEffCartierDiv.isInvertible_I _).isInvertible_module
  obtain ⟨dd⟩ := hIb.dual.2

  have raw : (Scheme.Modules.pullback (Xi e B hB)).obj (h.poincare.pullbackAlong (ajPt aj x)).L ⊗
      (h.poincare.pullbackAlong (ajPt aj (Bpt e B hB ε))).L ≅ (h.poincare.pullbackAlong (ajPt aj (Bpt e B hB x))).L :=
    (((Scheme.Modules.pullback (Xi e B hB)).mapIso ia ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (lx ⊗ᵢ mε)) ⊗ᵢ ib) ≪≫
    α_ _ _ _ ≪≫
    (Iso.refl _ ⊗ᵢ ((α_ _ _ _).symm ≪≫ (dd ⊗ᵢ Iso.refl _) ≪≫ λ_ _)) ≪≫
    ig.symm

  have hXa := (h.poincare.pullbackAlong (ajPt aj x)).isInvertible.pullback (Xi e B hB)
  obtain ⟨r1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
    (h.poincare.pullbackAlong (ajPt aj (Bpt e B hB ε)))
  obtain ⟨r2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_tensor_iso (ε := ε) hXa
    (h.poincare.pullbackAlong (ajPt aj (Bpt e B hB ε))).isInvertible
  obtain ⟨r3⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    (hXa.tensor (h.poincare.pullbackAlong (ajPt aj (Bpt e B hB ε))).isInvertible)
    (h.poincare.pullbackAlong (ajPt aj (Bpt e B hB x))).isInvertible raw
  obtain ⟨r4⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
    (h.poincare.pullbackAlong (ajPt aj (Bpt e B hB x)))
  have key : (RigidifiedLineBundle.ofInvertible (ε := ε)
        ((Scheme.Modules.pullback (Xi e B hB)).obj (h.poincare.pullbackAlong (ajPt aj x)).L) hXa).L ⊗
      (h.poincare.pullbackAlong (ajPt aj (Bpt e B hB ε))).L ≅
      (h.poincare.pullbackAlong (ajPt aj (Bpt e B hB x))).L :=
    (Iso.refl _ ⊗ᵢ r1.symm) ≪≫ r2.symm ≪≫ r3 ≪≫ r4
  obtain ⟨emul⟩ := poincare_mul h (𝟙 (Spec (.of K))) (Psi h e B hB (ajPt aj x)) (ajPt aj (Bpt e B hB ε))
  exact h.ext_of_iso (𝟙 (Spec (.of K))) _ _ ⟨emul ≪≫ (ePsi ⊗ᵢ Iso.refl _) ≪≫ key⟩

end PointModules

end Twist

section Places

variable {K : Type u} [Field K] [IsAlgClosed K] {F : Type v} [Field F] [Algebra K F]

theorem inertiaDegAlong_eq_one [IsCurveOver K F] (φ : F →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral) (w : Place K F) :
    w.inertiaDegAlong φ hφ = 1 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  have h := w.deg_restrict_mul_inertiaDeg (F := F)
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed, one_mul] at h
  exact h

theorem pushforwardAlong_single_one [IsCurveOver K F] (φ : F →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral) (w : Place K F) :
    Divisor.pushforwardAlong φ hφ (Finsupp.single w 1) = Finsupp.single (w.restrictAlong φ hφ) 1 := by
  rw [Divisor.pushforwardAlong_single, inertiaDegAlong_eq_one, Nat.cast_one, one_mul]

noncomputable def retract [IsCurveOver K F] (v₀ : Place K F) :
    Divisor K F →+ Divisor.degZero (K := K) (F := F) :=
  AddMonoidHom.mk'
    (fun D => ⟨D - Divisor.degree D • Finsupp.single v₀ 1, by
      rw [Divisor.mem_degZero, map_sub, map_zsmul, Divisor.degree_single,
        IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one, smul_eq_mul, mul_one, sub_self]⟩)
    (fun a b => by
      apply Subtype.ext
      simp only [map_add, AddSubgroup.coe_add, add_smul]
      abel)

theorem retract_coe [IsCurveOver K F] (v₀ : Place K F) (D : Divisor K F) :
    (retract v₀ D : Divisor K F) = D - Divisor.degree D • Finsupp.single v₀ 1 := rfl

theorem retract_single_one_coe [IsCurveOver K F] (v₀ w : Place K F) :
    (retract v₀ (Finsupp.single w 1) : Divisor K F) = Finsupp.single w 1 - Finsupp.single v₀ 1 := by
  rw [retract_coe, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one,
    one_smul]

theorem retract_of_mem [IsCurveOver K F] (v₀ : Place K F) {D : Divisor K F}
    (hD : D ∈ Divisor.degZero (K := K) (F := F)) : retract v₀ D = ⟨D, hD⟩ := by
  apply Subtype.ext
  rw [retract_coe, Divisor.mem_degZero.mp hD, zero_smul, sub_zero]

theorem degZero_addMonoidHom_ext [IsCurveOver K F] {A : Type*} [AddGroup A] (v₀ : Place K F)
    {f g : Divisor.degZero (K := K) (F := F) →+ A}
    (hfg : ∀ w : Place K F, f (retract v₀ (Finsupp.single w 1)) = g (retract v₀ (Finsupp.single w 1))) :
    f = g := by
  have key : f.comp (retract v₀) = g.comp (retract v₀) := by
    apply Finsupp.addHom_ext'
    intro w
    apply AddMonoidHom.ext_int
    simpa using hfg w
  ext ⟨D, hD⟩
  have h := DFunLike.congr_fun key D
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, retract_of_mem v₀ hD] at h
  exact h

end Places

theorem isIso_SpecMap_of_pow_card (k : Type*) [Finite k] [Nonempty k] {K : Type u} [Field K] [IsAlgClosed K]
    (σ : K →+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k) : IsIso (Spec.map (CommRingCat.ofHom σ)) := by
  have hq : 0 < Nat.card k := Nat.card_pos
  have hbij : Function.Bijective σ := ⟨σ.injective, fun c => by
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq c hq
    exact ⟨a, by rw [hσ, ha]⟩⟩
  haveI : IsIso (CommRingCat.ofHom σ) :=
    ⟨⟨CommRingCat.ofHom (RingEquiv.ofBijective σ hbij).symm.toRingHom,
      by ext x; exact (RingEquiv.ofBijective σ hbij).symm_apply_apply x,
      by ext x; exact (RingEquiv.ofBijective σ hbij).apply_symm_apply x⟩⟩
  infer_instance

end P2mSemilin
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_semilinear_hom_of_pushforwardAlong_frobenius_of_representsRelSubPic.P2mSemilin"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_semilinear_hom_of_pushforwardAlong_frobenius_of_representsRelSubPic.P2mSemilin"

open P2mSemilin in
set_option maxHeartbeats 3200000 in
theorem solution
    (k : Type*) (K : Type u) (F₀ : Type*) (F : Type v) [Field k] [Finite k] [Field K] [IsAlgClosed K]
    [Field F₀] [Field F] [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (M : CurveModel K F)
    (s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (D : RelativePic0Designation K M.toBase)
    (h : RepresentsRelSubPic M.toBase s (algEquivZeroCut M.toBase s) D)
    (aj : SchemeHomOver M.toBase D.toBase) (hajs : s.1 ≫ aj.1 = D.zeroSection)
    (haj : ∀ (K' : Type u) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K))
        (x : SchemeHomOver t M.toBase),
      Nonempty ((h.poincare.pullbackAlong
          ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M.toBase (t ≫ s.1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) s.2).trans (Category.comp_id t)))).idealModule))
    (pts : Pic0 K F ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase)
    (hadd : ∀ x y : Pic0 K F, pts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase s) h).mul _ (pts x) (pts y))
    (hnorm : ∀ x : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      ∃ Dv : Divisor.degZero (K := K) (F := F),
        (Dv : Divisor K F) =
          Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ aj.1) :
    ∃ σ : K →+* K, (∀ c : K, σ c = c ^ Nat.card k) ∧
      ∃ NB : D.P ⟶ D.P, NB ≫ D.toBase ≫ Spec.map (CommRingCat.ofHom σ) = D.toBase ∧
        ∀ Dv : Divisor.degZero (K := K) (F := F),
          (pts (Pic0.mk ⟨Divisor.pushforwardAlong φ hφi Dv,
              Divisor.pushforwardAlong_mem_degZero φ hφi Dv.2⟩)).1 =
            Spec.map (CommRingCat.ofHom σ) ≫ (pts (Pic0.mk Dv)).1 ≫ NB := by
  classical

  obtain ⟨σ, hσ, B, hB, hBpt⟩ :=
    AlgebraicCurve.CurveModel.exists_semilinear_iso_pointEquivPlace_eq_restrictAlong_frobenius
      k K F₀ F hgen φ hφi hφ M
  haveI : Nonempty k := ⟨0⟩
  haveI : IsIso (Spec.map (CommRingCat.ofHom σ)) := isIso_SpecMap_of_pow_card k σ hσ
  set e : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) := Spec.map (CommRingCat.ofHom σ) with he

  refine ⟨σ, hσ, (NB h e B hB).1, NB_comp h e B hB, ?_⟩
  intro Dv

  letI G := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase s) h).pointGroup
    (𝟙 (Spec (CommRingCat.of K)))
  let ptsA : Pic0 K F →+ Additive (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (pts x)) (fun x y => congrArg Additive.ofMul (hadd x y))
  let PsiA : Additive (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) →+
      Additive (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :=
    AddMonoidHom.mk' (fun z => Additive.ofMul (Psi h e B hB (Additive.toMul z)))
      (fun z z' => congrArg Additive.ofMul (Psi_mul h e B hB (Additive.toMul z) (Additive.toMul z')))
  let pf : Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F) :=
    AddMonoidHom.mk'
      (fun E => ⟨Divisor.pushforwardAlong φ hφi E, Divisor.pushforwardAlong_mem_degZero φ hφi E.2⟩)
      (fun a b => Subtype.ext (map_add _ _ _))
  let mkF : Divisor.degZero (K := K) (F := F) →+ Pic0 K F := QuotientAddGroup.mk' _
  let Ψ₁ : Divisor.degZero (K := K) (F := F) →+ Additive (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :=
    ptsA.comp (mkF.comp pf)
  let Ψ₂ : Divisor.degZero (K := K) (F := F) →+ Additive (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :=
    PsiA.comp (ptsA.comp mkF)
  suffices hΨ : Ψ₁ = Ψ₂ by
    have hD := congrArg (fun z => (Additive.toMul z).1) (DFunLike.congr_fun hΨ Dv)
    exact hD.trans (Psi_coe h e B hB (pts (Pic0.mk Dv)))

  have hFr : ∀ y : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      (e ≫ y.1 ≫ B.hom) ≫ M.toBase = 𝟙 _ := fun y => (Bpt e B hB y).2
  let Fr : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _} →
      {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _} := fun y => ⟨e ≫ y.1 ≫ B.hom, hFr y⟩
  have hFrPlace : ∀ y : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      M.pointEquivPlace (Fr y) = AlgebraicCurve.Place.restrictAlong φ hφi (M.pointEquivPlace y) := by
    intro y
    obtain ⟨hy, hplace⟩ := hBpt y
    exact hplace
  have hA : ∀ x : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      pts (Pic0.mk (retract (M.pointEquivPlace s) (Finsupp.single (M.pointEquivPlace x) 1))) = ajPt aj x := by
    intro x
    obtain ⟨Dx, hDx, hpt⟩ := hnorm x
    have hre : retract (M.pointEquivPlace s) (Finsupp.single (M.pointEquivPlace x) 1) = Dx :=
      Subtype.ext ((retract_single_one_coe _ _).trans hDx.symm)
    rw [hre]
    exact Subtype.ext hpt

  apply degZero_addMonoidHom_ext (M.pointEquivPlace s)
  intro w
  obtain ⟨y, rfl⟩ := M.pointEquivPlace.surjective w

  have hpf : pf (retract (M.pointEquivPlace s) (Finsupp.single (M.pointEquivPlace y) 1)) =
      retract (M.pointEquivPlace s) (Finsupp.single (M.pointEquivPlace (Fr y)) 1) -
        retract (M.pointEquivPlace s) (Finsupp.single (M.pointEquivPlace (Fr s)) 1) := by
    apply Subtype.ext
    change Divisor.pushforwardAlong φ hφi
        (retract (M.pointEquivPlace s) (Finsupp.single (M.pointEquivPlace y) 1) : Divisor K F) = _
    rw [AddSubgroup.coe_sub, retract_single_one_coe, retract_single_one_coe, retract_single_one_coe,
      map_sub, pushforwardAlong_single_one, pushforwardAlong_single_one, ← hFrPlace y, ← hFrPlace s]
    abel

  have h1 : Additive.toMul (Ψ₁ (retract (M.pointEquivPlace s) (Finsupp.single (M.pointEquivPlace y) 1))) =
      ajPt aj (Fr y) * (ajPt aj (Fr s))⁻¹ := by
    change Additive.toMul (ptsA (mkF (pf _))) = _
    rw [hpf, map_sub, map_sub, toMul_sub]
    change pts (Pic0.mk _) * (pts (Pic0.mk _))⁻¹ = _
    rw [hA, hA]

  have h2 : Additive.toMul (Ψ₂ (retract (M.pointEquivPlace s) (Finsupp.single (M.pointEquivPlace y) 1))) =
      Psi h e B hB (ajPt aj y) := by
    change Psi h e B hB (pts (Pic0.mk _)) = _
    rw [hA]

  have h3 : Psi h e B hB (ajPt aj y) * ajPt aj (Fr s) = ajPt aj (Fr y) :=
    Psi_ajPt_mul h e B hB aj (fun x => haj K (𝟙 _) x) y
  apply Additive.toMul.injective
  rw [h1, h2]
  exact (eq_mul_inv_of_mul_eq h3).symm

end S_AlgebraicCurve_Pic0_exists_semilinear_hom_of_pushforwardAlong_frobenius_of_representsRelSubPic
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_exists_semilinear_hom_of_pushforwardAlong_frobenius_of_representsRelSubPic (solution)
