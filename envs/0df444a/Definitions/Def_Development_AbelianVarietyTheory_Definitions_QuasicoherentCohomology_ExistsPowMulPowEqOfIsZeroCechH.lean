-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH
-- name    : Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T23:11:00.794854+00:00
-- url     : https://prove2.me/theorems/3c7ad690-a0ef-4e38-9030-f3f642989573
-- title:
--   Exists Pow Mul Pow Eq Of Is Zero Cech H
-- statement:
--   Definitions and structural lemmas for Exists Pow Mul Pow Eq Of Is Zero Cech H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsPowMulPowEqOfIsZeroCechH.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Theorems.Thm_GlobalTheory_Cube_SemiHom_homology_bijective
import Theorems.Thm_GlobalTheory_Cube_SemiHom_homology_cechClass
import Theorems.Thm_GlobalTheory_cechAbCubeMap_app_apply
import Theorems.Thm_GlobalTheory_cechAbHMap_id
import Theorems.Thm_GlobalTheory_cechAbHZeroEquiv_symm_apply
import Theorems.Thm_GlobalTheory_cechComplex_exactAt_succ_iff
import Theorems.Thm_GlobalTheory_cechComplex_exactAt_succ_iff_cube
import Theorems.Thm_GlobalTheory_cechOpen_inf_family
import Theorems.Thm_GlobalTheory_cechOpen_pair
import Theorems.Thm_GlobalTheory_cohOn_res_map
import Theorems.Thm_GlobalTheory_cubeComplex_exactAt_of_isLocalizedModule
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
import Theorems.Thm_GlobalTheory_presheafCechHZeroEquiv_symm_apply
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
import Theorems.Thm_GlobalTheory_sectionsOn_res_map
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Cube.SemiHom.homology_cechClass
attribute [local simp] GlobalTheory.cechAbCubeMap_app_apply
attribute [local simp] GlobalTheory.cechAbHMap_id
attribute [local simp] GlobalTheory.cechAbHZeroEquiv_symm_apply
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id
attribute [local simp] GlobalTheory.presheafCechHZeroEquiv_symm_apply
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply


set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe t v u
noncomputable section
namespace GlobalTheory
variable {X Y : Scheme.{u}} {ι : Type}
section Basic
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
@[simps]
def sectionsPresheafMap {F G : X.Modules} (φ : F ⟶ G) :
    sectionsPresheaf R F ⟶ sectionsPresheaf R G where
  app W := ModuleCat.ofHom (sectionsOn.map R φ W.unop)
  naturality _ _ i := ModuleCat.hom_ext (LinearMap.ext fun x =>
    (sectionsOn.res_map R φ i.unop.le x).symm)
theorem isSheaf_sectionsPresheaf (F : X.Modules) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (sectionsPresheaf R F) :=
  (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (C := ModuleCat.{u} R)
    (X := X.toPresheafedSpace.carrier) (sectionsPresheaf R F)).2
    ((TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (C := AddCommGrpCat.{u}) F.presheaf).1
      F.isSheaf)
@[simp]
theorem sectionsOn.res_res (F : X.Modules) {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W')
    (x : sectionsOn F W) :
    sectionsOn.res R F h' (sectionsOn.res R F h x) = sectionsOn.res R F (h'.trans h) x :=
  LinearMap.congr_fun (sectionsOn.res_comp_res R F h h') x
def sectionsOn.congrOpens (F : X.Modules) {W W' : X.Opens} (h : W = W') :
    sectionsOn F W ≃ₗ[R] sectionsOn F W' :=
  presheafCongr (sectionsPresheaf R F) h
@[simp]
theorem sectionsOn.congrOpens_apply (F : X.Modules) {W W' : X.Opens} (h : W = W')
    (x : sectionsOn F W) : sectionsOn.congrOpens R F h x = sectionsOn.res R F h.ge x := rfl
@[simp]
theorem sectionsOn.congrOpens_symm_apply (F : X.Modules) {W W' : X.Opens} (h : W = W')
    (x : sectionsOn F W') :
    (sectionsOn.congrOpens R F h).symm x = sectionsOn.res R F h.le x := rfl
variable (F : X.Modules) {G H : X.Modules} (V : X.Opens) (U : ι → X.Opens)
def cechCube : Cube.{u} ι R := presheafCube (sectionsPresheaf R F) V U
variable {F} in

def cechCubeMap (φ : F ⟶ G) : cechCube R F V U ⟶ cechCube R G V U :=
  presheafCubeMap V U (sectionsPresheafMap R φ)
variable {F} in

@[simp]
theorem cechCubeMap_app (φ : F ⟶ G) (s : Finset ι) :
    ((cechCubeMap R V U φ).app s).hom = sectionsOn.map R φ (cechOpen V U s) := rfl
@[simps]
def cechCubeFunctor : X.Modules ⥤ Cube.{u} ι R where
  obj F := cechCube R F V U
  map := cechCubeMap R V U
  map_id _ := rfl
  map_comp _ _ := rfl
instance cechCubeFunctor_additive : (cechCubeFunctor R V U).Additive where
  map_add := rfl
def cechCubeEmptyEquiv : sectionsOn F V ≃ₗ[R] (cechCube R F V U).obj ∅ :=
  presheafCubeEmptyEquiv (sectionsPresheaf R F) V U
variable {V U} in

def cechCubeRes {V' : X.Opens} {U' : ι → X.Opens} (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s) :
    cechCube R F V U ⟶ cechCube R F V' U' :=
  presheafCubeRes (sectionsPresheaf R F) h
variable {V U} in

@[simp]
theorem cechCubeRes_app {V' : X.Opens} {U' : ι → X.Opens}
    (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s) (s : Finset ι) :
    ((cechCubeRes R F h).app s).hom = sectionsOn.res R F (h s) := rfl
def cechRestrictions : sectionsOn F V →ₗ[R] Cube.Term (cechCube R F V U) 1 :=
  presheafCechAug (sectionsPresheaf R F) V U
@[simp]
theorem cechRestrictions_apply (x : sectionsOn F V) (s : {s : Finset ι // s.card = 1}) :
    cechRestrictions R F V U x s = sectionsOn.res R F (cechOpen_le V U s.1) x := rfl
variable [LinearOrder ι]
def cech : CochainComplex (ModuleCat.{u} R) ℕ := cechComplex (cechCube R F V U)
def cechH (n : ℕ) : ModuleCat.{u} R := (cech R F V U).homology n
theorem cech_d (p : ℕ) :
    (cech R F V U).d p (p + 1) = ModuleCat.ofHom (Cube.d (cechCube R F V U) (p + 1)) :=
  cechComplex_d _ p
variable {F} in

def cechMap (φ : F ⟶ G) : cech R F V U ⟶ cech R G V U := cechComplexMap (cechCubeMap R V U φ)
variable {F} in

def cechHMap (φ : F ⟶ G) (n : ℕ) : cechH R F V U n ⟶ cechH R G V U n :=
  HomologicalComplex.homologyMap (cechMap R V U φ) n
@[simps]
def cechModulesFunctor : X.Modules ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj F := cech R F V U
  map := cechMap R V U
  map_id _ := rfl
  map_comp _ _ := rfl
instance cechModulesFunctor_additive : (cechModulesFunctor R V U).Additive where
  map_add := rfl
@[simps]
def cechHFunctor (n : ℕ) : X.Modules ⥤ ModuleCat.{u} R where
  obj F := cechH R F V U n
  map φ := cechHMap R V U φ n
  map_id F := (cechModulesFunctor R V U ⋙ HomologicalComplex.homologyFunctor _ _ n).map_id F
  map_comp := (cechModulesFunctor R V U ⋙ HomologicalComplex.homologyFunctor _ _ n).map_comp
instance cechHFunctor_additive (n : ℕ) : (cechHFunctor R V U n).Additive where
  map_add := (cechModulesFunctor R V U ⋙ HomologicalComplex.homologyFunctor _ _ n).map_add
@[simp]
theorem cechMap_id : cechMap R V U (𝟙 F) = 𝟙 _ := rfl
variable {F} in

@[reassoc]
theorem cechMap_comp (φ : F ⟶ G) (ψ : G ⟶ H) :
    cechMap R V U (φ ≫ ψ) = cechMap R V U φ ≫ cechMap R V U ψ := rfl
@[simp]
theorem cechHMap_id (n : ℕ) : cechHMap R V U (𝟙 F) n = 𝟙 _ := (cechHFunctor R V U n).map_id F
variable {F} in

@[reassoc]
theorem cechHMap_comp (φ : F ⟶ G) (ψ : G ⟶ H) (n : ℕ) :
    cechHMap R V U (φ ≫ ψ) n = cechHMap R V U φ n ≫ cechHMap R V U ψ n :=
  (cechHFunctor R V U n).map_comp φ ψ
variable {F} in

def cechMapIso (e : F ≅ G) : cech R F V U ≅ cech R G V U := (cechModulesFunctor R V U).mapIso e
variable {F} in

def cechHMapIso (e : F ≅ G) (n : ℕ) : cechH R F V U n ≅ cechH R G V U n :=
  (cechHFunctor R V U n).mapIso e
variable {V U} in

def cechTopIso (h : ∀ i, U i ≤ V) : cech R F ⊤ U ≅ cech R F V U :=
  presheafCechTopIso (sectionsPresheaf R F) h
variable {F V U} in

@[reassoc]
theorem cechTopIso_naturality (h : ∀ i, U i ≤ V) (φ : F ⟶ G) :
    cechMap R ⊤ U φ ≫ (cechTopIso R G h).hom = (cechTopIso R F h).hom ≫ cechMap R V U φ :=
  congrArg cechComplexMap (presheafCubeRes_naturality (sectionsPresheafMap R φ)
    (cechOpen_mono (le_top (a := V)) fun _ => le_rfl))
def cechInfIso : cech R F V U ≅ cech R F V fun i => V ⊓ U i :=
  (cechFunctor ι R).mapIso
    (presheafCubeCongr (sectionsPresheaf R F) fun s => (cechOpen_inf_family V U s).symm)
@[simp]
theorem d_cechRestrictions (x : sectionsOn F V) :
    Cube.d (cechCube R F V U) 1 (cechRestrictions R F V U x) = 0 :=
  d_presheafCechAug (sectionsPresheaf R F) V U x
def toCechH : sectionsOn F V →ₗ[R] cechH R F V U 0 := presheafToCechH (sectionsPresheaf R F) V U
variable {V U} (hc : V ≤ ⨆ i, U i)
include hc in

theorem toCechH_bijective : Function.Bijective (toCechH R F V U) :=
  presheafToCechH_bijective (T := X.toPresheafedSpace.carrier) (isSheaf_sectionsPresheaf R F) hc
def cechHZeroEquiv : cechH R F V U 0 ≃ₗ[R] sectionsOn F V :=
  (LinearEquiv.ofBijective _ (toCechH_bijective R F hc)).symm
@[simp]
theorem cechHZeroEquiv_symm_apply (x : sectionsOn F V) :
    (cechHZeroEquiv R F hc).symm x = toCechH R F V U x := rfl
@[simp]
theorem cechHZeroEquiv_toCechH (x : sectionsOn F V) :
    cechHZeroEquiv R F hc (toCechH R F V U x) = x := (cechHZeroEquiv R F hc).apply_symm_apply x
def cechHZeroEquivCohOn : cechH R F V U 0 ≃ₗ[R] cohOn F V 0 :=
  (cechHZeroEquiv R F hc).trans (cohOn.zeroEquiv R F V).symm
end Basic
def cechHZeroTopEquiv [LinearOrder ι] (F : X.Modules) {U : ι → X.Opens} (hc : ⨆ i, U i = ⊤) :
    cechH Γ(X, ⊤) F ⊤ U 0 ≃ₗ[Γ(X, ⊤)] Γ(F, ⊤) :=
  (cechHZeroEquiv Γ(X, ⊤) F hc.ge).trans (sectionsOn.topEquiv F)
section Scalars
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
  (F : X.Modules) {G : X.Modules} (V : X.Opens) (U : ι → X.Opens)
def cechAbCubeToCube :
    Cube.SemiHom (Int.castRingHom R) (cechAbCube F.presheaf V U) (cechCube R F V U) where
  app s :=
    { toFun := (sectionsOn.toΓ F (cechOpen V U s)).symm
      map_add' := map_add _
      map_smul' := fun n x => (map_zsmul (sectionsOn.toΓ F (cechOpen V U s)).symm n x).trans
        (Int.cast_smul_eq_zsmul R n _).symm }
  app_res _ _ := rfl
def cechCubeIntIso : cechCube ℤ F V U ≅ cechAbCube F.presheaf V U :=
  Cube.isoMk (fun s => (sectionsOn.toΓ F (cechOpen V U s)).toIntLinearEquiv) fun _ _ => rfl
variable (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)] [Algebra R S] [IsScalarTower R S Γ(X, ⊤)]
def cechCubeScalars : Cube.SemiHom (algebraMap R S) (cechCube R F V U) (cechCube S F V U) where
  app s :=
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun r (x : sectionsOn F (cechOpen V U s)) => (algebraMap_smul S r x).symm }
  app_res _ _ := rfl
def cechCubeRestrictScalarsIso :
    cechCube R F V U ≅ cechCube S F V U ⋙ ModuleCat.restrictScalars (algebraMap R S) :=
  Cube.isoMk (fun s =>
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r (x : sectionsOn F (cechOpen V U s)) => (algebraMap_smul S r x).symm })
    fun _ _ => rfl
variable [LinearOrder ι]
def cechRestrictIso : cech R F V U ≅
    ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj (cech S F V U) :=
  (cechFunctor ι R).mapIso (cechCubeRestrictScalarsIso R F V U S) ≪≫
    (cechRestrictScalarsIso (algebraMap R S) (cechCube S F V U)).symm
def cechHScalarsEquiv (n : ℕ) : cechH R F V U n ≃+ cechH S F V U n :=
  AddEquiv.ofBijective ((cechCubeScalars R F V U S).homology n).toAddMonoidHom
    ((cechCubeScalars R F V U S).homology_bijective (fun _ _ => Function.bijective_id) n)
def cechAbHEquiv (n : ℕ) : cechAbH F.presheaf V U n ≃+ cechH R F V U n :=
  AddEquiv.ofBijective ((cechAbCubeToCube R F V U).homology n).toAddMonoidHom
    ((cechAbCubeToCube R F V U).homology_bijective (fun _ _ => Function.bijective_id) n)
end Scalars
section Morphism
variable (g : Y ⟶ X) (V : X.Opens) (U : ι → X.Opens)
theorem preimage_cechOpen (s : Finset ι) :
    g ⁻¹ᵁ cechOpen V U s = cechOpen (g ⁻¹ᵁ V) (fun i => g ⁻¹ᵁ U i) s := by
  ext x
  exact mem_cechOpen.trans (mem_cechOpen (V := g ⁻¹ᵁ V) (U := fun i => g ⁻¹ᵁ U i)).symm
variable {R : Type v} [CommRing R] [Algebra R Γ(X, ⊤)] {S : Type t} [CommRing S]
  [Algebra S Γ(Y, ⊤)] {σ : R →+* S}
  {g} (hσ : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))
  {F : X.Modules} {G : Y.Modules} (φ : F ⟶ (Scheme.Modules.pushforward g).obj G)
def sectionsOn.mapOver (W : X.Opens) : sectionsOn F W →ₛₗ[σ] sectionsOn G (g ⁻¹ᵁ W) where
  toFun x := (sectionsOn.toΓ G (g ⁻¹ᵁ W)).symm (φ.app W (sectionsOn.toΓ F W x))
  map_add' x y := map_add (φ.app W).hom x y
  map_smul' r x := by
    have h : g.app W (restrictGlobal X W (algebraMap R Γ(X, ⊤) r)) =
        restrictGlobal Y (g ⁻¹ᵁ W) (algebraMap S Γ(Y, ⊤) (σ r)) := by
      rw [← hσ]
      exact ConcreteCategory.congr_hom (g.naturality (homOfLE le_top : W ⟶ ⊤).op) _
    refine (φ.app_smul (restrictGlobal X W (algebraMap R Γ(X, ⊤) r)) x).trans ?_
    exact congrArg (fun a : Γ(Y, g ⁻¹ᵁ W) =>
      (a • (show Γ(G, g ⁻¹ᵁ W) from φ.app W (sectionsOn.toΓ F W x)) : Γ(G, g ⁻¹ᵁ W))) h
theorem sectionsOn.mapOver_res {W W' : X.Opens} (h : W' ≤ W) (x : sectionsOn F W) :
    sectionsOn.mapOver hσ φ W' (sectionsOn.res R F h x) =
      sectionsOn.res S G (g.preimage_mono h) (sectionsOn.mapOver hσ φ W x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x
def cechCubeMapOver :
    Cube.SemiHom σ (cechCube R F V U) (cechCube S G (g ⁻¹ᵁ V) fun i => g ⁻¹ᵁ U i) where
  app s := (sectionsOn.res S G (preimage_cechOpen g V U s).ge).comp
    (sectionsOn.mapOver hσ φ (cechOpen V U s))
  app_res {s t} h x :=
    (congrArg (sectionsOn.res S G (preimage_cechOpen g V U t).ge)
      (sectionsOn.mapOver_res hσ φ (cechOpen_anti V U h) x)).trans
      ((sectionsOn.res_res S G _ _ _).trans
        (sectionsOn.res_res S G _ (cechOpen_anti _ _ h) _).symm)
theorem cechCubeMapOver_id_bijective (s : Finset ι) : Function.Bijective
    ((cechCubeMapOver V U hσ (𝟙 ((Scheme.Modules.pushforward g).obj G))).app s) :=
  (sectionsOn.congrOpens S G (preimage_cechOpen g V U s)).bijective
variable [Algebra R Γ(Y, ⊤)]
  (hg : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) r)
variable (G) in

def cechCubePushforwardIso : cechCube R ((Scheme.Modules.pushforward g).obj G) V U ≅
    cechCube R G (g ⁻¹ᵁ V) fun i => g ⁻¹ᵁ U i :=
  Cube.isoMk (fun s => LinearEquiv.ofBijective _
    (cechCubeMapOver_id_bijective (σ := RingHom.id R) V U hg s))
    (cechCubeMapOver (σ := RingHom.id R) V U hg (𝟙 _)).app_res
@[reassoc]
theorem cechCubePushforwardIso_naturality {G' : Y.Modules} (ψ : G ⟶ G') :
    cechCubeMap R V U ((Scheme.Modules.pushforward g).map ψ) ≫
        (cechCubePushforwardIso V U G' hg).hom =
      (cechCubePushforwardIso V U G hg).hom ≫ cechCubeMap R _ _ ψ :=
  NatTrans.ext (funext fun s => ModuleCat.hom_ext (LinearMap.ext fun x =>
    sectionsOn.res_map R ψ (preimage_cechOpen g V U s).ge x))
variable (G) in

def cechPushforwardIso [LinearOrder ι] : cech R ((Scheme.Modules.pushforward g).obj G) V U ≅
    cech R G (g ⁻¹ᵁ V) fun i => g ⁻¹ᵁ U i :=
  (cechFunctor ι R).mapIso (cechCubePushforwardIso V U G hg)
end Morphism
section Two
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] (F : X.Modules) (V : X.Opens)
  (U : Fin 2 → X.Opens)
def cechTwoXZero :
    (cech R F V U).X 0 ≃ₗ[R] sectionsOn F (V ⊓ U 0) × sectionsOn F (V ⊓ U 1) :=
  Cube.termOneFinTwo (cechCube R F V U) ≪≫ₗ
    (sectionsOn.congrOpens R F (cechOpen_singleton V U 0)).prodCongr
      (sectionsOn.congrOpens R F (cechOpen_singleton V U 1))
def cechTwoXOne : (cech R F V U).X 1 ≃ₗ[R] sectionsOn F (V ⊓ (U 0 ⊓ U 1)) :=
  Cube.termTwoFinTwo (cechCube R F V U) ≪≫ₗ sectionsOn.congrOpens R F (cechOpen_pair V U 0 1)
theorem cechTwo_d (x : (cech R F V U).X 0) :
    cechTwoXOne R F V U (((cech R F V U).d 0 1).hom x) =
      sectionsOn.res R F (inf_le_inf_left V inf_le_right) (cechTwoXZero R F V U x).2 -
        sectionsOn.res R F (inf_le_inf_left V inf_le_left) (cechTwoXZero R F V U x).1 := by
  rw [cech_d R F V U 0]
  refine (congrArg (sectionsOn.congrOpens R F (cechOpen_pair V U 0 1))
    (Cube.d_one_finTwo (cechCube R F V U) x)).trans ((map_sub _ _ _).trans ?_)
  exact congrArg₂ (· - ·)
    ((sectionsOn.res_res R F _ _ _).trans
      (sectionsOn.res_res R F (cechOpen_singleton V U 1).ge _ _).symm)
    ((sectionsOn.res_res R F _ _ _).trans
      (sectionsOn.res_res R F (cechOpen_singleton V U 0).ge _ _).symm)
theorem isZero_cechH_one_iff_surjective :
    IsZero (cechH R F V U 1) ↔ Function.Surjective ((cech R F V U).d 0 1).hom := by
  haveI := Cube.subsingleton_term (cechCube R F V U) (p := 0 + 2 + 1) (by simp)
  rw [cech_d R F V U 0]
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ _).symm.trans
    ((cechComplex_exactAt_succ_iff (cechCube R F V U) 0).trans (forall_congr' fun x => ?_))
  exact ⟨fun h => h.1 (Subsingleton.elim _ _), fun h => ⟨fun _ => h, fun _ => Subsingleton.elim _ _⟩⟩
end Two
section Affine
variable {A : CommRingCat.{u}} (M : ModuleCat.{u} A)
def tildeToSections (W : (Spec A).Opens) : M →ₗ[A] sectionsOn (tilde M) W :=
  (sectionsOn.specEquiv (tilde M) W).symm.toLinearMap ∘ₗ (tilde.toOpen M W).hom
@[simp]
theorem res_tildeToSections {W W' : (Spec A).Opens} (h : W' ≤ W) (m : M) :
    sectionsOn.res A (tilde M) h (tildeToSections M W m) = tildeToSections M W' m := rfl
def basicOpenFamily (f : ι → A) : ι → (Spec A).Opens := fun i => PrimeSpectrum.basicOpen (f i)
theorem isLocalizedModule_tildeToSections (f : A) {W : (Spec A).Opens}
    (h : W = PrimeSpectrum.basicOpen f) : IsLocalizedModule.Away f (tildeToSections M W) := by
  have h₀ : IsLocalizedModule.Away f (tilde.toOpen M W).hom := by
    subst h
    infer_instance
  exact IsLocalizedModule.of_linearEquiv (.powers f)
    (tilde.toOpen M W).hom (sectionsOn.specEquiv (tilde M) W).symm
theorem cechOpen_basicOpenFamily (f : ι → A) (s : Finset ι) :
    cechOpen ⊤ (basicOpenFamily f) s = PrimeSpectrum.basicOpen (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [cechOpen_empty, Finset.prod_empty]
    exact PrimeSpectrum.basicOpen_one.symm
  | insert a s ha ih =>
    rw [cechOpen_insert, ih, Finset.prod_insert ha]
    exact (PrimeSpectrum.basicOpen_mul _ _).symm
theorem iSup_basicOpenFamily_eq_top_iff (f : ι → A) :
    ⨆ i, basicOpenFamily f i = ⊤ ↔ Ideal.span (Set.range f) = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff
def locCubeIsoCechCube (f : ι → A) : locCube f M ≅ cechCube A (tilde M) ⊤ (basicOpenFamily f) :=
  locCubeIso f M _ (fun s => tildeToSections M (cechOpen ⊤ (basicOpenFamily f) s))
    (hg := fun s => isLocalizedModule_tildeToSections M _ (cechOpen_basicOpenFamily f s))
    fun h m => res_tildeToSections M (cechOpen_anti _ _ h) m
theorem cechCube_tilde_exactAt [LinearOrder ι] [Finite ι] {f : ι → A}
    (hf : Ideal.span (Set.range f) = ⊤) (p : ℕ) :
    (cubeComplex (cechCube A (tilde M) ⊤ (basicOpenFamily f))).ExactAt p :=
  cubeComplex_exactAt_of_isLocalizedModule _ f
    (fun s => tildeToSections M (cechOpen ⊤ (basicOpenFamily f) s))
    (fun s => isLocalizedModule_tildeToSections M _ (cechOpen_basicOpenFamily f s))
    (fun h m => res_tildeToSections M (cechOpen_anti _ _ h) m) hf p
theorem isZero_cechH_tilde_succ [LinearOrder ι] [Finite ι] {f : ι → A}
    (hf : Ideal.span (Set.range f) = ⊤) (p : ℕ) :
    IsZero (cechH A (tilde M) ⊤ (basicOpenFamily f) (p + 1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    ((cechComplex_exactAt_succ_iff_cube _ p).2 (cechCube_tilde_exactAt M hf (p + 2)))
def cechHZeroTildeEquiv [LinearOrder ι] {f : ι → A} (hf : Ideal.span (Set.range f) = ⊤) :
    cechH A (tilde M) ⊤ (basicOpenFamily f) 0 ≃ₗ[A] M :=
  cechHZeroEquiv A (tilde M) ((iSup_basicOpenFamily_eq_top_iff f).2 hf).ge ≪≫ₗ
    sectionsOn.specEquiv (tilde M) ⊤ ≪≫ₗ (tilde.isoTop M).toLinearEquiv.symm
def awayTransition {a b : A} (h : a ∣ b) :
    LocalizedModule (.powers a) M →ₗ[A] LocalizedModule (.powers b) M :=
  LocalizedModule.lift _ (LocalizedModule.mkLinearMap _ M)
    (isUnit_powers_of_dvd h (LocalizedModule.mkLinearMap _ M))
@[simp]
theorem awayTransition_mk_one {a b : A} (h : a ∣ b) (m : M) :
    awayTransition M h (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 :=
  LocalizedModule.lift_mk_one _ _ _ m
def sectionsAwayEquiv (f : A) {W : (Spec A).Opens} (h : W = PrimeSpectrum.basicOpen f) :
    sectionsOn (tilde M) W ≃ₗ[A] LocalizedModule (.powers f) M :=
  haveI := isLocalizedModule_tildeToSections M f h
  IsLocalizedModule.linearEquiv (.powers f) (tildeToSections M W) (LocalizedModule.mkLinearMap _ M)
@[simp]
theorem sectionsAwayEquiv_tildeToSections (f : A) {W : (Spec A).Opens}
    (h : W = PrimeSpectrum.basicOpen f) (m : M) :
    sectionsAwayEquiv M f h (tildeToSections M W m) = LocalizedModule.mk m 1 :=
  haveI := isLocalizedModule_tildeToSections M f h
  IsLocalizedModule.linearEquiv_apply (.powers f) _ _ m
theorem sectionsAwayEquiv_res {a b : A} (hab : a ∣ b) {W W' : (Spec A).Opens}
    (h : W = PrimeSpectrum.basicOpen a) (h' : W' = PrimeSpectrum.basicOpen b) (hW : W' ≤ W)
    (x : sectionsOn (tilde M) W) :
    sectionsAwayEquiv M b h' (sectionsOn.res A (tilde M) hW x) =
      awayTransition M hab (sectionsAwayEquiv M a h x) := by
  haveI := isLocalizedModule_tildeToSections M a h
  have := IsLocalizedModule.ext (.powers a) (tildeToSections M W)
    (isUnit_powers_of_dvd hab (LocalizedModule.mkLinearMap _ M))
    (j := (sectionsAwayEquiv M b h').toLinearMap ∘ₗ sectionsOn.res A (tilde M) hW)
    (k := awayTransition M hab ∘ₗ (sectionsAwayEquiv M a h).toLinearMap) (by ext m; simp)
  exact congr($this x)
variable (f g : A)
abbrev twoCharts : Fin 2 → (Spec A).Opens := basicOpenFamily ![f, g]
theorem twoCharts_inf : ⊤ ⊓ (twoCharts f g 0 ⊓ twoCharts f g 1) = PrimeSpectrum.basicOpen (f * g) :=
  (top_inf_eq _).trans (PrimeSpectrum.basicOpen_mul f g).symm
def twoChartsXZero : (cech A (tilde M) ⊤ (twoCharts f g)).X 0 ≃ₗ[A]
    LocalizedModule (.powers f) M × LocalizedModule (.powers g) M :=
  cechTwoXZero A (tilde M) ⊤ (twoCharts f g) ≪≫ₗ
    (sectionsAwayEquiv M f (top_inf_eq _)).prodCongr (sectionsAwayEquiv M g (top_inf_eq _))
def twoChartsXOne :
    (cech A (tilde M) ⊤ (twoCharts f g)).X 1 ≃ₗ[A] LocalizedModule (.powers (f * g)) M :=
  cechTwoXOne A (tilde M) ⊤ (twoCharts f g) ≪≫ₗ sectionsAwayEquiv M (f * g) (twoCharts_inf f g)
theorem twoCharts_d (x : (cech A (tilde M) ⊤ (twoCharts f g)).X 0) :
    twoChartsXOne M f g (((cech A (tilde M) ⊤ (twoCharts f g)).d 0 1).hom x) =
      awayTransition M (dvd_mul_left g f) (twoChartsXZero M f g x).2 -
        awayTransition M (dvd_mul_right f g) (twoChartsXZero M f g x).1 :=
  (congrArg (sectionsAwayEquiv M (f * g) (twoCharts_inf f g))
    (cechTwo_d A (tilde M) ⊤ (twoCharts f g) x)).trans ((map_sub _ _ _).trans (congrArg₂ (· - ·)
      (sectionsAwayEquiv_res M _ (top_inf_eq _) _ _ _)
      (sectionsAwayEquiv_res M _ (top_inf_eq _) _ _ _)))
theorem isZero_cechH_twoCharts_one_iff : IsZero (cechH A (tilde M) ⊤ (twoCharts f g) 1) ↔
    ∀ z, ∃ a b, awayTransition M (dvd_mul_left g f) b - awayTransition M (dvd_mul_right f g) a =
      z := by
  rw [isZero_cechH_one_iff_surjective]
  constructor
  · intro h z
    obtain ⟨x, hx⟩ := h ((twoChartsXOne M f g).symm z)
    exact ⟨_, _, by rw [← twoCharts_d, hx, LinearEquiv.apply_symm_apply]⟩
  · intro h z
    obtain ⟨a, b, hab⟩ := h (twoChartsXOne M f g z)
    refine ⟨(twoChartsXZero M f g).symm (a, b), (twoChartsXOne M f g).injective ?_⟩
    rw [twoCharts_d, LinearEquiv.apply_symm_apply, hab]
theorem span_range_pair_one_sub : Ideal.span (Set.range ![f, 1 - f]) = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (by
    simpa using Ideal.add_mem _ (Ideal.subset_span (s := Set.range ![f, 1 - f]) ⟨0, rfl⟩)
      (Ideal.subset_span ⟨1, rfl⟩))
def cechHZeroTwoChartsEquiv : cechH A (tilde M) ⊤ (twoCharts f (1 - f)) 0 ≃ₗ[A] M :=
  cechHZeroTildeEquiv M (span_range_pair_one_sub f)
theorem isZero_cechH_twoCharts_succ (p : ℕ) :
    IsZero (cechH A (tilde M) ⊤ (twoCharts f (1 - f)) (p + 1)) :=
  isZero_cechH_tilde_succ M (span_range_pair_one_sub f) p
def cechStructureIso [LinearOrder ι] (V : (Spec A).Opens) (U : ι → (Spec A).Opens) :
    cech A (tilde (ModuleCat.of A A)) V U ≅ cech A (structureModule (Spec A)) V U :=
  cechMapIso A V U tildeSelf
def cechHZeroStructureTwoChartsEquiv :
    cechH A (structureModule (Spec A)) ⊤ (twoCharts f (1 - f)) 0 ≃ₗ[A] A :=
  (cechHMapIso A ⊤ (twoCharts f (1 - f)) tildeSelf 0).toLinearEquiv.symm ≪≫ₗ
    cechHZeroTwoChartsEquiv (ModuleCat.of A A) f
theorem isZero_cechH_structure_twoCharts_succ (p : ℕ) :
    IsZero (cechH A (structureModule (Spec A)) ⊤ (twoCharts f (1 - f)) (p + 1)) :=
  (isZero_cechH_twoCharts_succ (ModuleCat.of A A) f p).of_iso
    (cechHMapIso A ⊤ (twoCharts f (1 - f)) tildeSelf (p + 1)).symm
theorem exists_pow_mul_pow_eq_of_isZero_cechH
    (h : IsZero (cechH A (structureModule (Spec A)) ⊤ (twoCharts f g) 1)) :
    ∃ (n k : ℕ) (a b : A), f ^ n * g ^ k = f ^ (n + 1) * b + g ^ (k + 1) * a := by
  obtain ⟨a, b, hab⟩ := (isZero_cechH_twoCharts_one_iff (ModuleCat.of A A) f g).1
    (h.of_iso (cechHMapIso A ⊤ (twoCharts f g) tildeSelf 1))
    (LocalizedModule.mk (1 : A) ⟨f * g, 1, pow_one _⟩)
  obtain ⟨n, a', ha⟩ := IsLocalizedModule.Away.surj (LocalizedModule.mkLinearMap _ _) f a
  obtain ⟨k, b', hb⟩ := IsLocalizedModule.Away.surj (LocalizedModule.mkLinearMap _ _) g b
  let l : A →ₗ[A] LocalizedModule (.powers (f * g)) A := LocalizedModule.mkLinearMap _ _
  have h₁ : f ^ n • awayTransition (ModuleCat.of A A) (dvd_mul_right f g) a = l a' := by
    rw [← map_smul, ha]; exact awayTransition_mk_one (ModuleCat.of A A) _ a'
  have h₂ : g ^ k • awayTransition (ModuleCat.of A A) (dvd_mul_left g f) b = l b' := by
    rw [← map_smul, hb]; exact awayTransition_mk_one (ModuleCat.of A A) _ b'
  have h₃ : (f * g) • LocalizedModule.mk (1 : A) (⟨f * g, 1, pow_one _⟩ : Submonoid.powers (f * g)) =
      l 1 := by
    rw [LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_cancel (⟨f * g, 1, pow_one _⟩ : Submonoid.powers (f * g)) (1 : A)
  have h₄ : l ((f ^ n * g ^ k) • (1 : A)) =
      l ((f ^ n * (f * g)) • b' - (g ^ k * (f * g)) • a') := by
    rw [map_sub, map_smul, map_smul, map_smul, ← h₁, ← h₂, ← h₃, ← hab]
    simp only [smul_sub, smul_smul]
    congr 2 <;> ring
  obtain ⟨m, hm⟩ := IsLocalizedModule.Away.exists_of_eq (f * g) h₄
  refine ⟨n + m, k + m, -(f ^ (m + 1) * a'), g ^ (m + 1) * b', ?_⟩
  simp only [smul_eq_mul, mul_pow] at hm
  linear_combination hm
end Affine
example :
    letI := algebraΓSpec (.of ℤ)
    Nontrivial (cechH (CommRingCat.of ℤ) (structureModule (Spec (.of ℤ))) ⊤
      (twoCharts (A := .of ℤ) 3 (1 - 3)) 0) ∧
    IsZero (cechH (CommRingCat.of ℤ) (structureModule (Spec (.of ℤ))) ⊤
      (twoCharts (A := .of ℤ) 3 (1 - 3)) 1) :=
  ⟨(cechHZeroStructureTwoChartsEquiv (A := .of ℤ) 3).toEquiv.nontrivial,
    isZero_cechH_structure_twoCharts_succ (A := .of ℤ) 3 0⟩
example : Nontrivial (cechAbH (structureModule (Spec (.of ℤ))).presheaf ⊤
    (twoCharts (A := .of ℤ) 3 (1 - 3)) 0) :=
  letI := algebraΓSpec (.of ℤ)
  haveI := (cechHZeroStructureTwoChartsEquiv (A := .of ℤ) 3).toEquiv.nontrivial
  (cechAbHEquiv (CommRingCat.of ℤ) (structureModule (Spec (.of ℤ))) ⊤
    (twoCharts (A := .of ℤ) 3 (1 - 3)) 0).toEquiv.nontrivial
example {A : CommRingCat.{u}} (M : ModuleCat.{u} A) (f g : A) (m : M) :
    twoChartsXOne M f g (((cech A (tilde M) ⊤ (twoCharts f g)).d 0 1).hom
      ((twoChartsXZero M f g).symm (LocalizedModule.mk m 1, 0))) = -LocalizedModule.mk m 1 := by
  rw [twoCharts_d, LinearEquiv.apply_symm_apply, map_zero, awayTransition_mk_one, zero_sub]
example :
    letI := algebraΓSpec (.of (Polynomial ℤ))
    ¬ IsZero (cechH (CommRingCat.of (Polynomial ℤ)) (structureModule (Spec (.of (Polynomial ℤ)))) ⊤
      (twoCharts (A := .of (Polynomial ℤ)) (Polynomial.C 2) Polynomial.X) 1) := by
  intro h
  obtain ⟨n, k, a, b, hab⟩ := exists_pow_mul_pow_eq_of_isZero_cechH (A := .of (Polynomial ℤ))
    (Polynomial.C 2) Polynomial.X h
  have h₁ : (Polynomial.C (2 : ℤ) ^ n * Polynomial.X ^ k).coeff k =
      (Polynomial.C (2 : ℤ) ^ (n + 1) * b + Polynomial.X ^ (k + 1) * a).coeff k :=
    congrArg (fun p : Polynomial ℤ => p.coeff k) hab
  rw [← map_pow, ← map_pow, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_self, Polynomial.coeff_X_pow_mul', if_neg (by omega), add_zero,
    pow_succ, mul_assoc] at h₁
  have h₂ := mul_left_cancel₀ (by positivity : (2 : ℤ) ^ n ≠ 0) h₁
  omega
end GlobalTheory


