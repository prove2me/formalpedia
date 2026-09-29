-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_isInvertible_transition_eq_of_inf_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/de49efd8-171c-5a6f-a674-4466fe00be40

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_of_forall_pullback_iso_of_isOpenImmersion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_isInvertible_transition_eq_of_inf_cocycle

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

noncomputable section

namespace B26

open AlgebraicGeometry.Scheme.Modules

variable {Y : Scheme.{u}} {M : Y.Modules} (V : Y.Opens) (f : Γ(M, V))

def fr (W' : (V : Scheme.{u}).Opens) : Γ(M.restrict V.ι, W') :=
  M.presheaf.map (homOfLE (V.ι_image_le W')).op f

theorem fr_def (W' : (V : Scheme.{u}).Opens) :
    fr V f W' = (M.presheaf.map (homOfLE (V.ι_image_le W')).op f : Γ(M, V.ι ''ᵁ W')) := rfl

theorem map_map (M : Y.Modules) {A B C : Y.Opens} (i : B ⟶ A) (j : C ⟶ B) (x : Γ(M, A)) :
    M.presheaf.map j.op (M.presheaf.map i.op x) = M.presheaf.map (j ≫ i).op x := by
  rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]; rfl

theorem map_irrel (M : Y.Modules) {A B : Y.Opens} (i j : B ⟶ A) (x : Γ(M, A)) :
    M.presheaf.map i.op x = M.presheaf.map j.op x := by rw [Subsingleton.elim i j]

theorem map_fr {W' W'' : (V : Scheme.{u}).Opens} (i : W'' ⟶ W') :
    (M.restrict V.ι).presheaf.map i.op (fr V f W') = fr V f W'' := by
  show (M.presheaf.map ((Scheme.Hom.opensFunctor V.ι).map i).op (M.presheaf.map (homOfLE (V.ι_image_le W')).op f)
    : Γ(M, V.ι ''ᵁ W'')) = M.presheaf.map (homOfLE (V.ι_image_le W'')).op f
  rw [map_map]
  rfl

theorem smul_restrict (W' : (V : Scheme.{u}).Opens) (g : Γ((V : Scheme.{u}), W')) (m : Γ(M.restrict V.ι, W')) :
    g • m = (((V.ι.appIso W').inv.hom g : Γ(Y, V.ι ''ᵁ W')) • (show Γ(M, V.ι ''ᵁ W') from m) : Γ(M, V.ι ''ᵁ W')) := by
  rfl

theorem smul_restrict' (W' : (V : Scheme.{u}).Opens) (g : Γ((V : Scheme.{u}), W')) (m : Γ(M.restrict V.ι, W')) :
    g • m = ((show Γ(Y, V.ι ''ᵁ W') from g) • (show Γ(M, V.ι ''ᵁ W') from m) : Γ(M, V.ι ''ᵁ W')) := by
  rw [smul_restrict, Scheme.Opens.ι_appIso]; rfl

def frSec : (M.restrict V.ι).sections :=
  PresheafOfModules.sectionsMk (fun W' => fr V f W'.unop) (by
    intro A B i
    exact map_fr V f i.unop)

def σ : @Quiver.Hom ((V : Scheme.{u}).Modules) _
    (SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf) (M.restrict V.ι) :=
  (M.restrict V.ι).unitHomEquiv.symm (frSec V f)

theorem σ_app (W' : (V : Scheme.{u}).Opens) (g : Γ((V : Scheme.{u}), W')) :
    (σ V f).app W' g = g • fr V f W' := rfl

variable (hf : IsFrameOn f V)

include hf in
theorem bijective_σ_app (W' : (V : Scheme.{u}).Opens) : Function.Bijective ((σ V f).app W') := by
  have hb := hf (V.ι_image_le W') (V.ι_image_le W')
  have e : ((σ V f).app W' : Γ((SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf : (V : Scheme.{u}).Modules), W') →
      Γ(M.restrict V.ι, W')) =
      fun g : Γ(Y, V.ι ''ᵁ W') => g • (M.presheaf.map (homOfLE (V.ι_image_le W')).op f : Γ(M, V.ι ''ᵁ W')) := by
    funext g
    rw [σ_app, smul_restrict']
    rfl
  rw [e]; exact hb

include hf in
theorem isIso_σ : IsIso (σ V f) :=
  Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun W' =>
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_σ_app V f hf W')

def ρ : M.restrict V.ι ≅ (SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf : (V : Scheme.{u}).Modules) :=
  haveI := isIso_σ V f hf
  (asIso (σ V f)).symm

theorem ρ_inv : (ρ V f hf).inv = σ V f := rfl

theorem ρ_hom_app_smul_fr (W' : (V : Scheme.{u}).Opens) (g : Γ((V : Scheme.{u}), W')) :
    (ρ V f hf).hom.app W' (g • fr V f W') = g := by
  rw [← σ_app, ← ρ_inv V f hf, ← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id,
    Scheme.Modules.Hom.id_app]
  rfl

def τf : (Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf :=
  ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app M).symm ≪≫ ρ V f hf

def Q (U : Y.Opens) (m : Γ(M, U)) : Γ(M.restrict V.ι, V.ι ⁻¹ᵁ U) :=
  M.presheaf.map (homOfLE (V.ι.image_preimage_le U)).op m

theorem rFIP_hom_app_Q (U : Y.Opens) (m : Γ(M, U)) :
    ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app M).app (V.ι ⁻¹ᵁ U) (Q V U m) =
      pullbackLocalSection V.ι m := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction V.ι)
    (Scheme.Modules.pullbackPushforwardAdjunction V.ι) M
  have h' := congrArg (fun k => Scheme.Modules.Hom.app k U m) h
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply] at h'
  exact h'

theorem rFIP_inv_app_P (U : Y.Opens) (m : Γ(M, U)) :
    ((Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app M).app (V.ι ⁻¹ᵁ U) (pullbackLocalSection V.ι m) =
      Q V U m := by
  rw [← rFIP_hom_app_Q, ← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id_app,
    Scheme.Modules.Hom.id_app]
  rfl

theorem τf_hom_app_P (U : Y.Opens) (m : Γ(M, U)) :
    (τf V f hf).hom.app (V.ι ⁻¹ᵁ U) (pullbackLocalSection V.ι m) = (ρ V f hf).hom.app (V.ι ⁻¹ᵁ U) (Q V U m) := by
  show ((((Scheme.Modules.restrictFunctorIsoPullback V.ι).app M).inv ≫ (ρ V f hf).hom).app (V.ι ⁻¹ᵁ U)
    (pullbackLocalSection V.ι m)) = _
  rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, Iso.app_inv, rFIP_inv_app_P]

theorem Q_smul_map (U : Y.Opens) (hUV : U ≤ V) (g : Γ(Y, U)) :
    Q V U (g • M.presheaf.map (homOfLE hUV).op f) = V.ι.app U g • fr V f (V.ι ⁻¹ᵁ U) := by
  rw [smul_restrict', Q, Scheme.Modules.map_smul, map_map, Scheme.Opens.ι_app]
  rfl

theorem τf_hom_app_P_smul (U : Y.Opens) (hUV : U ≤ V) (g : Γ(Y, U)) :
    (τf V f hf).hom.app (V.ι ⁻¹ᵁ U) (pullbackLocalSection V.ι (g • M.presheaf.map (homOfLE hUV).op f)) =
      V.ι.app U g := by
  rw [τf_hom_app_P, Q_smul_map, ρ_hom_app_smul_fr]

end B26
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_isInvertible_transition_eq_of_inf_cocycle.B26"
end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_isInvertible_transition_eq_of_inf_cocycle.B26"

noncomputable section

namespace B26

open AlgebraicGeometry.Scheme.Modules

section conj
variable {X Z : Scheme.{u}} (φ : X ⟶ Z)

def toU (U : Z.Opens) (g : Z.presheaf.obj (op U)) :
    Γ((SheafOfModules.unit Z.ringCatSheaf : Z.Modules), U) := g

theorem pullbackUnitIso_hom_app_pls (U : Z.Opens) (g : Z.presheaf.obj (op U)) :
    (pullbackUnitIso φ).hom.app (φ ⁻¹ᵁ U) (pullbackLocalSection φ (toU U g)) =
      toU (φ ⁻¹ᵁ U) ((φ.app U).hom g) := by
  have h1 : (pullbackUnitIso φ).hom =
      ((pullbackPushforwardAdjunction φ).homEquiv _ _).symm
        (SheafOfModules.unitToPushforwardObjUnit φ.toRingCatSheafHom) := rfl
  rw [h1, Scheme.Modules.homEquiv_symm_app_pullbackLocalSection]
  rfl

end conj
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_isInvertible_transition_eq_of_inf_cocycle.B26"

section gen
variable {Y V B : Scheme.{u}} (M : Y.Modules)

def genRestrict (ι : V ⟶ Y) (j : B ⟶ Y) (k : B ⟶ V) (e : k ≫ ι = j)
    (τ : (Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit V.ringCatSheaf) :
    (Scheme.Modules.pullback j).obj M ≅ SheafOfModules.unit B.ringCatSheaf :=
  ((pullbackCongr e).app M).symm ≪≫ ((pullbackComp k ι).app M).symm ≪≫
    (Scheme.Modules.pullback k).mapIso τ ≪≫ pullbackUnitIso k

theorem genRestrict_hom_app_P (ι : V ⟶ Y) (j : B ⟶ Y) (k : B ⟶ V) (e : k ≫ ι = j)
    (τ : (Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit V.ringCatSheaf)
    (U : Y.Opens) (m : Γ(M, U)) (g : Y.presheaf.obj (op U))
    (hx : τ.hom.app (ι ⁻¹ᵁ U) (pullbackLocalSection ι m) = toU (ι ⁻¹ᵁ U) ((ι.app U).hom g)) :
    (genRestrict M ι j k e τ).hom.app (j ⁻¹ᵁ U) (pullbackLocalSection j m) =
      toU (j ⁻¹ᵁ U) ((j.app U).hom g) := by
  subst e
  have hC : ((pullbackCongr (rfl : k ≫ ι = k ≫ ι)).app M).inv = 𝟙 _ := by
    simp [pullbackCongr]
  have hD0 : ∀ y : Γ((Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback ι).obj M), k ⁻¹ᵁ ι ⁻¹ᵁ U),
      ((pullbackComp k ι).app M).inv.app (k ⁻¹ᵁ ι ⁻¹ᵁ U) (((pullbackComp k ι).hom.app M).app (k ⁻¹ᵁ ι ⁻¹ᵁ U) y) = y := by
    intro y
    rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.app_inv, Iso.hom_inv_id_app,
      Scheme.Modules.Hom.id_app]
    rfl
  have hD : ((pullbackComp k ι).app M).inv.app (k ⁻¹ᵁ ι ⁻¹ᵁ U)
      (pullbackLocalSection (k ≫ ι) m : Γ((Scheme.Modules.pullback (k ≫ ι)).obj M, k ⁻¹ᵁ ι ⁻¹ᵁ U)) =
      pullbackLocalSection k (pullbackLocalSection ι m) := by
    have := hD0 (pullbackLocalSection k (pullbackLocalSection ι m))
    rwa [Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection k ι M U m] at this
  have hF : ((Scheme.Modules.pullback k).map τ.hom).app (k ⁻¹ᵁ ι ⁻¹ᵁ U)
      (pullbackLocalSection k (pullbackLocalSection ι m)) = pullbackLocalSection k (toU (ι ⁻¹ᵁ U) ((ι.app U).hom g)) := by
    rw [← pullbackLocalSection_app, hx]
  have hG := pullbackUnitIso_hom_app_pls k (ι ⁻¹ᵁ U) ((ι.app U).hom g)
  have hcomp : (k.app (ι ⁻¹ᵁ U)).hom ((ι.app U).hom g) = ((k ≫ ι).app U).hom g := by
    rfl
  simp only [genRestrict, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [hC]
  change (pullbackUnitIso k).hom.app (k ⁻¹ᵁ ι ⁻¹ᵁ U) (((Scheme.Modules.pullback k).map τ.hom).app (k ⁻¹ᵁ ι ⁻¹ᵁ U)
    (((pullbackComp k ι).app M).inv.app (k ⁻¹ᵁ ι ⁻¹ᵁ U) ((𝟙 ((Scheme.Modules.pullback (k ≫ ι)).obj M) :
      (Scheme.Modules.pullback (k ≫ ι)).obj M ⟶ _).app (k ⁻¹ᵁ ι ⁻¹ᵁ U)
      (pullbackLocalSection (k ≫ ι) m : Γ((Scheme.Modules.pullback (k ≫ ι)).obj M, k ⁻¹ᵁ ι ⁻¹ᵁ U))))) =
    toU (k ⁻¹ᵁ ι ⁻¹ᵁ U) (((k ≫ ι).app U).hom g)
  rw [Scheme.Modules.Hom.id_app, CategoryTheory.id_apply, hD, hF, hG, hcomp]

end gen
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_isInvertible_transition_eq_of_inf_cocycle.B26"

section util
variable {Y : Scheme.{u}}

theorem presheaf_map_eq_rO {A B : Y.Opens} (f : op A ⟶ op B) (h : B ≤ A) (x : Γ(Y, A)) :
    (Y.presheaf.map f).hom x = GlueOfCocycle.rO h x := by
  have : f = (homOfLE h).op := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [this]

theorem app_map {N₁ N₂ : Y.Modules} (φ : N₁ ⟶ N₂) {A B : Y.Opens} (i : B ⟶ A) (x : Γ(N₁, A)) :
    φ.app B (N₁.presheaf.map i.op x) = N₂.presheaf.map i.op (φ.app A x) := by
  have := (φ.mapPresheaf).naturality i.op
  exact congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(N₁, A) → Γ(N₂, B))) this) x

theorem unit_presheaf_map {A B : Y.Opens} (i : B ⟶ A) (x : Γ(Y, A)) :
    (Scheme.Modules.presheaf (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)).map i.op (toU A x) = toU B ((Y.presheaf.map i.op).hom x) :=
  rfl

theorem unit_presheaf_map_one {A B : Y.Opens} (i : B ⟶ A) :
    (Scheme.Modules.presheaf (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)).map i.op (toU A 1) = toU B 1 := by
  rw [unit_presheaf_map, map_one]

theorem uas_eq (W : Y.Opens)
    (e : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf) :
    unitAutSection W e =
      W.topIso.hom.hom ((show @Iso ((W : Scheme.{u}).Modules) _ _ _ from e).hom.app ⊤ (toU ⊤ 1)) := rfl

theorem topIso_hom_eq_rO (W : Y.Opens) (x : Γ((W : Scheme.{u}), ⊤)) :
    W.topIso.hom.hom x = GlueOfCocycle.rO (Scheme.Opens.ι_image_top W).ge x :=
  presheaf_map_eq_rO _ _ _

end util
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_isInvertible_transition_eq_of_inf_cocycle.B26"

section trans
variable {Y : Scheme.{u}} {M : Y.Modules} (𝒱 : Y.OrderedAffineCover)
  (fa : ∀ a, Γ(M, 𝒱.U a)) (hfa : ∀ a, IsFrameOn (fa a) (𝒱.U a))

def τF : CechTrivialisation 𝒱 M := fun a => τf (𝒱.U a) (fa a) (hfa a)

theorem restrict_eq_genRestrict (τ : CechTrivialisation 𝒱 M) {a : 𝒱.ι} {W : Y.Opens} (h : W ≤ 𝒱.U a) :
    τ.restrict h = genRestrict M (𝒱.U a).ι W.ι (Y.homOfLE h) (Y.homOfLE_ι h) (τ a) := rfl

theorem restrict_τF_hom_app_P {a : 𝒱.ι} {W : Y.Opens} (h : W ≤ 𝒱.U a) (U : Y.Opens) (hUW : U ≤ W)
    (g : Γ(Y, U)) :
    ((τF 𝒱 fa hfa).restrict h).hom.app (W.ι ⁻¹ᵁ U)
        (pullbackLocalSection W.ι (g • M.presheaf.map (homOfLE (hUW.trans h)).op (fa a))) =
      toU (W.ι ⁻¹ᵁ U) ((W.ι.app U).hom g) := by
  rw [restrict_eq_genRestrict]
  exact genRestrict_hom_app_P M _ _ _ _ _ U _ g (τf_hom_app_P_smul (𝒱.U a) (fa a) (hfa a) U (hUW.trans h) g)

theorem transition_τF (s : 𝒱.Idx 1) (gW : Γ(Y, 𝒱.inter s))
    (hrel : M.presheaf.map (homOfLE (𝒱.inter_le s 0)).op (fa (s.1 0)) =
      gW • M.presheaf.map (homOfLE (𝒱.inter_le s 1)).op (fa (s.1 1))) :
    (τF 𝒱 fa hfa).transition s = gW := by
  have h0 : 𝒱.inter s ≤ 𝒱.U (s.1 0) := 𝒱.inter_le s 0
  have h1 : 𝒱.inter s ≤ 𝒱.U (s.1 1) := 𝒱.inter_le s 1

  have hA : ((τF 𝒱 fa hfa).restrict h0).hom.app ((𝒱.inter s).ι ⁻¹ᵁ 𝒱.inter s)
      (pullbackLocalSection (𝒱.inter s).ι (M.presheaf.map (homOfLE h0).op (fa (s.1 0)))) =
      toU ((𝒱.inter s).ι ⁻¹ᵁ 𝒱.inter s) 1 := by
    have h := restrict_τF_hom_app_P 𝒱 fa hfa h0 (𝒱.inter s) le_rfl 1
    rw [one_smul, map_one] at h
    exact h
  have hB : ((τF 𝒱 fa hfa).restrict h1).hom.app ((𝒱.inter s).ι ⁻¹ᵁ 𝒱.inter s)
      (pullbackLocalSection (𝒱.inter s).ι (M.presheaf.map (homOfLE h0).op (fa (s.1 0)))) =
      toU ((𝒱.inter s).ι ⁻¹ᵁ 𝒱.inter s) (((𝒱.inter s).ι.app (𝒱.inter s)).hom gW) := by
    have h := restrict_τF_hom_app_P 𝒱 fa hfa h1 (𝒱.inter s) le_rfl gW
    rw [← hrel] at h
    exact h

  have hAinv : ((τF 𝒱 fa hfa).restrict h0).inv.app ((𝒱.inter s).ι ⁻¹ᵁ 𝒱.inter s)
      (toU ((𝒱.inter s).ι ⁻¹ᵁ 𝒱.inter s) 1) =
      pullbackLocalSection (𝒱.inter s).ι (M.presheaf.map (homOfLE h0).op (fa (s.1 0))) := by
    rw [← hA, ← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app]
    rfl
  have hE : (((τF 𝒱 fa hfa).restrict h0).symm ≪≫ (τF 𝒱 fa hfa).restrict h1).hom.app ((𝒱.inter s).ι ⁻¹ᵁ 𝒱.inter s)
      (toU ((𝒱.inter s).ι ⁻¹ᵁ 𝒱.inter s) 1) =
      toU ((𝒱.inter s).ι ⁻¹ᵁ 𝒱.inter s) (((𝒱.inter s).ι.app (𝒱.inter s)).hom gW) := by
    rw [Iso.trans_hom, Iso.symm_hom, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, hAinv, hB]

  have le1 : (𝒱.inter s).ι ''ᵁ ((𝒱.inter s).ι ⁻¹ᵁ 𝒱.inter s) ≤ 𝒱.inter s := (𝒱.inter s).ι.image_preimage_le _
  have le2 : 𝒱.inter s ≤ (𝒱.inter s).ι ''ᵁ ((𝒱.inter s).ι ⁻¹ᵁ 𝒱.inter s) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_idem]
  have le3 : (𝒱.inter s).ι ''ᵁ ((𝒱.inter s).ι ⁻¹ᵁ 𝒱.inter s) ≤ (𝒱.inter s).ι ''ᵁ ⊤ :=
    ((𝒱.inter s).ι.opensFunctor.map (homOfLE le_top)).le
  have hz := app_map (((τF 𝒱 fa hfa).restrict h0).symm ≪≫ (τF 𝒱 fa hfa).restrict h1).hom
    (homOfLE (le_top : (𝒱.inter s).ι ⁻¹ᵁ 𝒱.inter s ≤ ⊤)) (toU ⊤ 1)
  rw [unit_presheaf_map_one, hE] at hz

  change GlueOfCocycle.rO le1 gW =
    (Y.presheaf.map ((𝒱.inter s).ι.opensFunctor.map (homOfLE (le_top : (𝒱.inter s).ι ⁻¹ᵁ 𝒱.inter s ≤ ⊤))).op).hom
      ((show @Iso ((𝒱.inter s : Scheme.{u}).Modules) _ _ _ from
        (((τF 𝒱 fa hfa).restrict h0).symm ≪≫ (τF 𝒱 fa hfa).restrict h1)).hom.app ⊤ (toU ⊤ 1)) at hz
  rw [presheaf_map_eq_rO _ le3] at hz
  show unitAutSection (𝒱.inter s) (((τF 𝒱 fa hfa).restrict h0).symm ≪≫ (τF 𝒱 fa hfa).restrict h1) = gW
  rw [uas_eq, topIso_hom_eq_rO]
  apply (GlueOfCocycle.rO_bijective_of_le_le le1 le2).1
  rw [GlueOfCocycle.rO_rO, hz]
  rfl

end trans
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_isInvertible_transition_eq_of_inf_cocycle.B26"

end B26
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_isInvertible_transition_eq_of_inf_cocycle.B26"
end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_isInvertible_transition_eq_of_inf_cocycle.B26"

noncomputable section

namespace B26

open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueOfCocycle

section assemble
variable {Y : Scheme.{u}} (𝒱 : Y.OrderedAffineCover)
  (W : ∀ a b : 𝒱.ι, Γ(Y, 𝒱.U a ⊓ 𝒱.U b))
  (hW1 : ∀ a : 𝒱.ι, W a a = 1)
  (hWc : ∀ a b c : 𝒱.ι,
    (Y.presheaf.map (homOfLE (inf_le_left : 𝒱.U a ⊓ 𝒱.U b ⊓ 𝒱.U c ≤ 𝒱.U a ⊓ 𝒱.U b)).op).hom (W a b) *
        (Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          𝒱.U a ⊓ 𝒱.U b ⊓ 𝒱.U c ≤ 𝒱.U b ⊓ 𝒱.U c)).op).hom (W b c) =
      (Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          𝒱.U a ⊓ 𝒱.U b ⊓ 𝒱.U c ≤ 𝒱.U a ⊓ 𝒱.U c)).op).hom (W a c))

def cW : UnitCocycle 𝒱.U where
  u i j := rO (le_of_eq (inf_comm (𝒱.U i) (𝒱.U j))) (W j i)
  refl i := by rw [hW1, map_one]
  cocycle i j k := by
    rw [rO_rO, rO_rO, rO_rO]
    have h := congrArg (rO (le_inf (le_inf (inf_le_right) (inf_le_left.trans inf_le_right)) (inf_le_left.trans inf_le_left) :
      𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k ≤ 𝒱.U k ⊓ 𝒱.U j ⊓ 𝒱.U i)) (hWc k j i)
    rw [map_mul] at h
    change rO _ (rO _ (W k j)) * rO _ (rO _ (W j i)) = rO _ (rO _ (W k i)) at h
    rw [rO_rO, rO_rO, rO_rO, mul_comm] at h
    exact h

theorem cW_u (i j : 𝒱.ι) : (cW 𝒱 W hW1 hWc).u i j = rO (le_of_eq (inf_comm (𝒱.U i) (𝒱.U j))) (W j i) := rfl

abbrev L : Y.Modules := glueOfCocycle (cW 𝒱 W hW1 hWc)

def τL : CechTrivialisation 𝒱 (L 𝒱 W hW1 hWc) :=
  τF 𝒱 (fun a => glueFrame (cW 𝒱 W hW1 hWc) a) (fun a => isFrameOn_glueFrame (cW 𝒱 W hW1 hWc) a)

theorem isInvertible_L : Scheme.Modules.IsInvertible (L 𝒱 W hW1 hWc) :=
  Scheme.Modules.IsInvertible.of_forall_pullback_iso_of_isOpenImmersion (fun a : 𝒱.ι => (𝒱.U a).ι)
    (fun y => by
      have hy : y ∈ (⨆ a, 𝒱.U a) := by rw [𝒱.iSup_eq_top]; trivial
      obtain ⟨a, ha⟩ := Opens.mem_iSup.1 hy
      exact ⟨a, ⟨y, ha⟩, rfl⟩)
    (fun a => SheafOfModules.unit (𝒱.U a : Scheme.{u}).ringCatSheaf) (fun a => Scheme.Modules.isInvertible_unit _)
    (L 𝒱 W hW1 hWc) (τL 𝒱 W hW1 hWc)

theorem transition_τL (s : 𝒱.Idx 1) :
    (τL 𝒱 W hW1 hWc).transition s =
      (Y.presheaf.map (homOfLE (le_inf (𝒱.inter_le s 0) (𝒱.inter_le s 1) :
        𝒱.inter s ≤ 𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 1))).op).hom (W (s.1 0) (s.1 1)) := by
  apply transition_τF
  have h := map_glueFrame_eq_smul (cW 𝒱 W hW1 hWc) (s.1 1) (s.1 0)
  have h' := congrArg ((L 𝒱 W hW1 hWc).presheaf.map (homOfLE (le_inf (𝒱.inter_le s 1) (𝒱.inter_le s 0) :
    𝒱.inter s ≤ 𝒱.U (s.1 1) ⊓ 𝒱.U (s.1 0))).op) h
  rw [Scheme.Modules.map_smul] at h'
  change (L 𝒱 W hW1 hWc).presheaf.map _ ((L 𝒱 W hW1 hWc).presheaf.map _ _) =
    _ • (L 𝒱 W hW1 hWc).presheaf.map _ ((L 𝒱 W hW1 hWc).presheaf.map _ _) at h'
  rw [map_map, map_map, cW_u] at h'
  change _ = (rO _ (rO _ (W (s.1 0) (s.1 1)))) • _ at h'
  rw [rO_rO] at h'
  exact h'

end assemble
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_isInvertible_transition_eq_of_inf_cocycle.B26"

end B26
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_isInvertible_transition_eq_of_inf_cocycle.B26"
end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_isInvertible_transition_eq_of_inf_cocycle.B26"

theorem solution
    {Y : Scheme.{u}} (𝒱 : Y.OrderedAffineCover)
    (W : ∀ a b : 𝒱.ι, Γ(Y, 𝒱.U a ⊓ 𝒱.U b))
    (hW1 : ∀ a : 𝒱.ι, W a a = 1) (hWu : ∀ a b : 𝒱.ι, IsUnit (W a b))
    (hWc : ∀ a b c : 𝒱.ι,
      (Y.presheaf.map (homOfLE (inf_le_left : 𝒱.U a ⊓ 𝒱.U b ⊓ 𝒱.U c ≤ 𝒱.U a ⊓ 𝒱.U b)).op).hom (W a b) *
          (Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            𝒱.U a ⊓ 𝒱.U b ⊓ 𝒱.U c ≤ 𝒱.U b ⊓ 𝒱.U c)).op).hom (W b c) =
        (Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            𝒱.U a ⊓ 𝒱.U b ⊓ 𝒱.U c ≤ 𝒱.U a ⊓ 𝒱.U c)).op).hom (W a c)) :
    ∃ 𝓛 : Y.Modules, Scheme.Modules.IsInvertible 𝓛 ∧
      ∃ τ : Scheme.Modules.CechTrivialisation 𝒱 𝓛, ∀ s : 𝒱.Idx 1,
        τ.transition s =
          (Y.presheaf.map (homOfLE (le_inf (𝒱.inter_le s 0) (𝒱.inter_le s 1) :
            𝒱.inter s ≤ 𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 1))).op).hom (W (s.1 0) (s.1 1)) :=
  ⟨B26.L 𝒱 W hW1 hWc, B26.isInvertible_L 𝒱 W hW1 hWc, B26.τL 𝒱 W hW1 hWc, B26.transition_τL 𝒱 W hW1 hWc⟩

end S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_isInvertible_transition_eq_of_inf_cocycle
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_isInvertible_transition_eq_of_inf_cocycle (solution)
