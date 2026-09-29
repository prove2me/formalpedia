-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.nonempty_pullback_iso_free_of_forall_exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/8bc34a8b-07e6-5ad6-bbe6-b7a2e366b03c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.AlgebraicGeometry Opposite TopologicalSpace"

namespace PresheafOfModules
p2m_export "PresheafOfModules" "presheaf sections map_id pullback pushforward evaluation map ofPresheaf hom_ext evaluationJointlyReflectsLimits Hom toPresheaf unit free restriction map_comp isSheaf_of_isLimit homMk obj"
p2m_open "PresheafOfModules"

variable {C : Type*} [Category C] (R : Cᵒᵖ ⥤ CommRingCat.{u}) (n : ℕ)

noncomputable def piPowAb : Cᵒᵖ ⥤ Ab.{u} where
  obj X := AddCommGrpCat.of (Fin n → R.obj X)
  map {X Y} f := AddCommGrpCat.ofHom (AddMonoidHom.compLeft (R.map f).hom.toAddMonoidHom (Fin n))
  map_id X := by ext v i; simp
  map_comp f g := by ext v i; simp

noncomputable scoped instance instModulePiPowAb (X : Cᵒᵖ) :
    Module ((R ⋙ forget₂ CommRingCat RingCat).obj X) ((piPowAb R n).obj X) :=
  inferInstanceAs (Module (R.obj X) (Fin n → R.obj X))

noncomputable def piPow : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) :=
  @ofPresheaf C _ (R ⋙ forget₂ CommRingCat RingCat) (piPowAb R n) (fun X => instModulePiPowAb R n X)
    (fun X Y f r v => by
      funext i
      exact map_mul (R.map f).hom (show R.obj X from r) (v i))

lemma piPow_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (v : Fin n → R.obj X) (i : Fin n) :
    ((piPow R n).map f (show (piPow R n).obj X from v) : Fin n → R.obj Y) i = R.map f (v i) := rfl

lemma piPow_map_basisFun {X Y : Cᵒᵖ} (f : X ⟶ Y) (j : Fin n) :
    ((piPow R n).map f (show (piPow R n).obj X from Pi.basisFun (R.obj X) (Fin n) j) :
      Fin n → R.obj Y) = Pi.basisFun (R.obj Y) (Fin n) j := by
  funext i
  rw [piPow_map_apply, Pi.basisFun_apply, Pi.basisFun_apply, Pi.single_apply, Pi.single_apply]
  split_ifs <;> simp

end PresheafOfModules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.PresheafOfModules"

namespace PresheafOfModules
p2m_export "PresheafOfModules" "presheaf sections map_id pullback pushforward evaluation map ofPresheaf hom_ext evaluationJointlyReflectsLimits Hom toPresheaf unit free restriction map_comp isSheaf_of_isLimit homMk obj"
p2m_open "PresheafOfModules"

lemma sum_app {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}} {M N : PresheafOfModules.{u} R}
    {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N)) (X : Cᵒᵖ) :
    (∑ i ∈ s, f i).app X = ∑ i ∈ s, (f i).app X :=
  Functor.map_sum (evaluation R X) f s

end PresheafOfModules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.PresheafOfModules"

namespace SheafOfModules
p2m_export "SheafOfModules" "isColimitFreeCofan over pushforward forget val hom_ext evaluation isSheaf unit fullyFaithfulForget Hom pullback sections free"
p2m_open "SheafOfModules"

lemma sum_val {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R} {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N)) :
    (∑ i ∈ s, f i).val = ∑ i ∈ s, (f i).val :=
  Functor.map_sum (SheafOfModules.forget R) f s

end SheafOfModules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.PresheafOfModules"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme.Hom Scheme.Opens.ι_appIso Scheme.Hom.image_preimage_eq_opensRange_inf Scheme Scheme.Modules Scheme.Opens Scheme.Modules.map_smul Scheme.Opens.opensRange_ι"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "forget ringCatSheaf Modules.pullback Hom Γ Opens.ι_appIso Hom.image_preimage_eq_opensRange_inf Modules.restrictFunctor Modules.restrictFunctorIsoPullback restrictFunctor Modules Opens grothendieckTopology Modules.map_smul Opens.opensRange_ι restrict PresheafOfModules evaluation"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext toPresheaf pushforward pullback presheaf Hom restrictFunctor restrictFunctorIsoPullback isSheaf restrict map_smul"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

open TopologicalSpace

variable (X : Scheme.{u}) (n : ℕ)

noncomputable abbrev piPowPresheaf : X.PresheafOfModules := PresheafOfModules.piPow X.sheaf.obj n

noncomputable abbrev ringCatSheafAb : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ RingCat.{u} AddCommGrpCat.{u})).obj X.ringCatSheaf

noncomputable def piPowCone :
    Cone (Discrete.functor (fun _ : Fin n => ringCatSheafAb X) ⋙ sheafToPresheaf _ _) where
  pt := (piPowPresheaf X n).presheaf
  π := Discrete.natTrans (fun i =>
    { app := fun V => AddCommGrpCat.ofHom (X := Fin n → (X.presheaf.obj V : Type u))
        (Y := (X.presheaf.obj V : Type u))
        (Pi.evalAddMonoidHom (fun _ : Fin n => (X.presheaf.obj V : Type u)) i.as)
      naturality := fun V W g => by ext v; rfl })

noncomputable def isLimitPiPowCone : IsLimit (piPowCone X n) :=
  evaluationJointlyReflectsLimits _ (fun V =>
    { lift := fun s => AddCommGrpCat.ofHom (X := (s.pt : Type u)) (Y := Fin n → (X.presheaf.obj V : Type u))
        (AddMonoidHom.pi (fun i : Fin n =>
          (show (s.pt : Type u) →+ (X.presheaf.obj V : Type u) from (s.π.app ⟨i⟩).hom)))
      fac := fun s j => by
        obtain ⟨i⟩ := j
        ext x
        rfl
      uniq := fun s m h => by
        ext x
        funext i
        exact ConcreteCategory.congr_hom (h ⟨i⟩) x })

lemma isSheaf_piPowPresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (piPowPresheaf X n).presheaf :=
  Sheaf.isSheaf_of_isLimit _ (piPowCone X n) (isLimitPiPowCone X n)

private noncomputable def _root_.AlgebraicGeometry.Scheme.Modules.piPow : X.Modules where
  val := piPowPresheaf X n
  isSheaf := isSheaf_piPowPresheaf X n

p2m_export "AlgebraicGeometry.Scheme.Modules" "piPow"

noncomputable def piPowπ (i : Fin n) : piPow X n ⟶ SheafOfModules.unit X.ringCatSheaf :=
  ⟨PresheafOfModules.homMk (M₂ := PresheafOfModules.unit _)
    { app := fun V => AddCommGrpCat.ofHom (X := Fin n → (X.presheaf.obj V : Type u))
        (Y := (X.presheaf.obj V : Type u))
        (Pi.evalAddMonoidHom (fun _ : Fin n => (X.presheaf.obj V : Type u)) i)
      naturality := fun V W g => by ext v; rfl }
    (fun V r v => rfl)⟩

lemma piPowπ_apply (i : Fin n) (V : X.Opensᵒᵖ) (v : Fin n → (X.presheaf.obj V : Type u)) :
    ((piPowπ X n i).val.app V (show (piPow X n).val.obj V from v) : X.presheaf.obj V) = v i := rfl

noncomputable def piPowι (i : Fin n) : SheafOfModules.unit X.ringCatSheaf ⟶ piPow X n :=
  ⟨PresheafOfModules.homMk (M₁ := PresheafOfModules.unit _)
    { app := fun V => AddCommGrpCat.ofHom (X := (X.presheaf.obj V : Type u))
        (Y := Fin n → (X.presheaf.obj V : Type u))
        (AddMonoidHom.single (fun _ : Fin n => (X.presheaf.obj V : Type u)) i)
      naturality := fun V W g => by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun (a : X.presheaf.obj V) => ?_)
        funext k
        change (Pi.single i (X.presheaf.map g a) : Fin n → X.presheaf.obj W) k =
          X.presheaf.map g ((Pi.single i a : Fin n → X.presheaf.obj V) k)
        simp only [Pi.single_apply]
        split_ifs <;> simp }
    (fun V (r : X.presheaf.obj V) (a : X.presheaf.obj V) => by
      funext k
      change (Pi.single i (r * a) : Fin n → X.presheaf.obj V) k =
        r * (Pi.single i a : Fin n → X.presheaf.obj V) k
      simp only [Pi.single_apply]
      split_ifs <;> simp)⟩

lemma piPowι_apply (i : Fin n) (V : X.Opensᵒᵖ) (a : (X.presheaf.obj V : Type u)) :
    ((piPowι X n i).val.app V (show (SheafOfModules.unit X.ringCatSheaf).val.obj V from a) :
      Fin n → X.presheaf.obj V) = Pi.single i a := rfl

noncomputable def piPowBicone :
    Bicone (fun _ : ULift.{u} (Fin n) => SheafOfModules.unit X.ringCatSheaf) where
  pt := piPow X n
  π j := piPowπ X n j.down
  ι j := piPowι X n j.down
  ι_π j j' := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext
      (LinearMap.ext fun (a : X.presheaf.obj V) => ?_))
    by_cases h : j = j'
    · subst h
      rw [dif_pos rfl]
      change (Pi.single j.down a : Fin n → X.presheaf.obj V) j.down = a
      simp
    · rw [dif_neg h]
      have h' : j'.down ≠ j.down := fun e => h (ULift.ext _ _ e.symm)
      change (Pi.single j.down a : Fin n → X.presheaf.obj V) j'.down = (0 : X.presheaf.obj V)
      simp [h']

lemma piPowBicone_total :
    ∑ j : ULift.{u} (Fin n), (piPowBicone X n).π j ≫ (piPowBicone X n).ι j = 𝟙 (piPow X n) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext
    (LinearMap.ext fun (v : Fin n → X.presheaf.obj V) => ?_))
  rw [SheafOfModules.sum_val, PresheafOfModules.sum_app, ModuleCat.hom_sum, LinearMap.sum_apply]
  change (∑ j : ULift.{u} (Fin n), (Pi.single j.down (v j.down) : Fin n → X.presheaf.obj V)) = v
  rw [Fintype.sum_equiv Equiv.ulift
    (fun j : ULift.{u} (Fin n) => (Pi.single j.down (v j.down) : Fin n → X.presheaf.obj V))
    (fun i : Fin n => Pi.single i (v i)) (fun _ => rfl)]
  exact Finset.univ_sum_single _

noncomputable def isBilimitPiPowBicone : (piPowBicone X n).IsBilimit :=
  isBilimitOfTotal _ (piPowBicone_total X n)

noncomputable def freeIsoPiPow : SheafOfModules.free.{u} (ULift.{u} (Fin n)) ≅ piPow X n :=
  IsColimit.coconePointUniqueUpToIso
    (SheafOfModules.isColimitFreeCofan.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin n)))
    (isBilimitPiPowBicone X n).isColimit

end AlgebraicGeometry.Scheme.Modules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.PresheafOfModules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.PresheafOfModules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.PresheafOfModules"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme.Hom Scheme.Opens.ι_appIso Scheme.Hom.image_preimage_eq_opensRange_inf Scheme Scheme.Modules Scheme.Opens Scheme.Modules.map_smul Scheme.Opens.opensRange_ι"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "forget ringCatSheaf Modules.pullback Hom Γ Opens.ι_appIso Hom.image_preimage_eq_opensRange_inf Modules.restrictFunctor Modules.restrictFunctorIsoPullback restrictFunctor Modules Opens grothendieckTopology Modules.map_smul Opens.opensRange_ι restrict PresheafOfModules evaluation"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext toPresheaf pushforward pullback presheaf Hom restrictFunctor restrictFunctorIsoPullback isSheaf restrict map_smul"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace FrameBridge

open Opposite TopologicalSpace

variable {X : Scheme.{u}}

section restrict

variable (W : X.Opens)

def restrictRingCatSheafHom : (W : Scheme.{u}).ringCatSheaf ⟶
    (W.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (W : Scheme.{u})) (Opens.grothendieckTopology X)).obj
        X.ringCatSheaf :=
  ⟨𝟙 _⟩

def restrictFunctor' : X.Modules ⥤ (W : Scheme.{u}).Modules :=
  SheafOfModules.pushforward (restrictRingCatSheafHom W)

lemma restrictFunctor'_eq : restrictFunctor' W = Modules.restrictFunctor W.ι := by
  dsimp only [restrictFunctor', Modules.restrictFunctor, restrictRingCatSheafHom]
  congr 2
  ext V : 2
  change 𝟙 _ = (forget₂ CommRingCat RingCat).map (W.ι.appIso V.unop).inv
  rw [Scheme.Opens.ι_appIso]
  rfl

def restrictFunctor'IsoPullback : restrictFunctor' W ≅ Modules.pullback W.ι :=
  eqToIso (restrictFunctor'_eq W) ≪≫ Modules.restrictFunctorIsoPullback W.ι

lemma image_le (W' : (W : Scheme.{u}).Opens) : W.ι ''ᵁ W' ≤ W :=
  (W.ι.image_le_opensRange W').trans_eq W.opensRange_ι

variable {W} in
lemma image_preimage_of_le {W₂ : X.Opens} (h : W₂ ≤ W) : W.ι ''ᵁ (W.ι ⁻¹ᵁ W₂) = W₂ := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr h

abbrev secX (W' : (W : Scheme.{u}).Opens) (a : Γ(W, W')) : Γ(X, W.ι ''ᵁ W') := a

end restrict
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.PresheafOfModules"

end FrameBridge
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.PresheafOfModules"

variable {X : Scheme.{u}}

lemma isIso_of_bijective_app (W : X.Opens) {P Q : ((W : X.Opens) : Scheme.{u}).Modules} (ψ : P ⟶ Q)
    (hb : ∀ W' : (((W : X.Opens) : Scheme.{u}).Opens)ᵒᵖ, Function.Bijective (ψ.val.app W')) :
    IsIso ψ := by
  have h₂ : IsIso ((PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map ψ)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro W'
    have : IsIso ((CategoryTheory.forget Ab).map
        (((PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map ψ)).app W')) :=
      (isIso_iff_bijective _).2 (hb W')
    exact isIso_of_reflects_iso _ (CategoryTheory.forget Ab)
  have := (SheafOfModules.fullyFaithfulForget (((W : X.Opens) : Scheme.{u}).ringCatSheaf)).reflectsIsomorphisms
  have h₃ := isIso_of_reflects_iso ((SheafOfModules.forget _).map ψ) (PresheafOfModules.toPresheaf _)
  exact isIso_of_reflects_iso ψ (SheafOfModules.forget _)

section sumSmul

variable (N : X.Modules) (W : X.Opens) {n : ℕ} (τ : Fin n → Γ(N, W))

def sumSmulHom : piPow ((W : X.Opens) : Scheme.{u}) n ⟶ (FrameBridge.restrictFunctor' W).obj N :=
  ⟨{ app := fun W' => ModuleCat.ofHom
      { toFun := fun g : (Fin n → Γ((W : X.Opens), W'.unop)) =>
          (∑ i, FrameBridge.secX W W'.unop (g i) • N.presheaf.map (homOfLE (FrameBridge.image_le W W'.unop)).op (τ i) :
            Γ(N, W.ι ''ᵁ W'.unop))
        map_add' := fun g g' => by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => add_smul (FrameBridge.secX W W'.unop (g i))
            (FrameBridge.secX W W'.unop (g' i)) _
        map_smul' := fun r g => by
          rw [RingHom.id_apply, Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => mul_smul (FrameBridge.secX W W'.unop r)
            (FrameBridge.secX W W'.unop (g i)) _ }
     naturality := fun {W' W''} i => by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro g
       show (∑ k, FrameBridge.secX W W''.unop (X.presheaf.map (W.ι.opensFunctor.map i.unop).op
              (FrameBridge.secX W W'.unop (g k))) •
           N.presheaf.map (homOfLE (FrameBridge.image_le W W''.unop)).op (τ k)) =
         N.presheaf.map (W.ι.opensFunctor.map i.unop).op
           (∑ k, FrameBridge.secX W W'.unop (g k) • N.presheaf.map (homOfLE (FrameBridge.image_le W W'.unop)).op (τ k))
       rw [map_sum]
       refine Finset.sum_congr rfl fun k _ => ?_
       rw [Scheme.Modules.map_smul]
       congr 1
       change _ = (N.presheaf.map _ ≫ N.presheaf.map _) (τ k)
       rw [← N.presheaf.map_comp]
       rfl }⟩

lemma sumSmulHom_app_apply (W' : (((W : X.Opens) : Scheme.{u}).Opens)ᵒᵖ) (g : Fin n → Γ((W : X.Opens), W'.unop)) :
    (sumSmulHom N W τ).val.app W' (show (piPow ((W : X.Opens) : Scheme.{u}) n).val.obj W' from g) =
      ∑ i, FrameBridge.secX W W'.unop (g i) • N.presheaf.map (homOfLE (FrameBridge.image_le W W'.unop)).op (τ i) := rfl

end sumSmul
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.PresheafOfModules"

theorem nonempty_pullback_iso_free_of_forall_exists_basis'
    {n : ℕ} (M : X.Modules) (U : X.Opens) (e : Fin n → Γ(M, U))
    (he : ∀ (W : X.Opens) (hW : W ≤ U),
      ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i)) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n))) := by
  haveI : IsIso (sumSmulHom M U e) := by
    apply isIso_of_bijective_app
    intro W'
    obtain ⟨b, hb⟩ := he (U.ι ''ᵁ W'.unop) (FrameBridge.image_le U W'.unop)
    have hfun : (fun g : (Fin n → Γ((U : X.Opens), W'.unop)) =>
        ((sumSmulHom M U e).val.app W' (show (piPow ((U : X.Opens) : Scheme.{u}) n).val.obj W' from g) :
          Γ(M, U.ι ''ᵁ W'.unop))) = fun g => b.equivFun.symm g := by
      funext g
      rw [sumSmulHom_app_apply, Module.Basis.equivFun_symm_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [hb i]
    exact (show Function.Bijective (fun g : (Fin n → Γ((U : X.Opens), W'.unop)) =>
        ((sumSmulHom M U e).val.app W' (show (piPow ((U : X.Opens) : Scheme.{u}) n).val.obj W' from g) :
          Γ(M, U.ι ''ᵁ W'.unop))) from hfun ▸ b.equivFun.symm.bijective)
  exact ⟨((FrameBridge.restrictFunctor'IsoPullback U).symm.app M) ≪≫ (asIso (sumSmulHom M U e)).symm ≪≫
    (freeIsoPiPow ((U : X.Opens) : Scheme.{u}) n).symm⟩

end AlgebraicGeometry.Scheme.Modules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.PresheafOfModules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.PresheafOfModules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.PresheafOfModules"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.PresheafOfModules"

theorem solution
    {X : Scheme.{u}} {n : ℕ} (M : X.Modules) (U : X.Opens) (e : Fin n → Γ(M, U))
    (he : ∀ (W : X.Opens) (hW : W ≤ U),
      ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i)) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n))) :=
  AlgebraicGeometry.Scheme.Modules.nonempty_pullback_iso_free_of_forall_exists_basis' M U e he

end S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis (solution)
