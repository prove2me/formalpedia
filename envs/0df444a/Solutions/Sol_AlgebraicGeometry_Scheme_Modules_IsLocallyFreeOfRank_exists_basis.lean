-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/acd01061-de6a-5e70-a355-9a8124e94cd5

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis.AlgebraicGeometry Opposite TopologicalSpace"

namespace PresheafOfModules
p2m_export "PresheafOfModules" "presheaf sections map_id evaluation map ofPresheaf hom_ext evaluationJointlyReflectsLimits Hom id_app unit comp_app free restriction map_comp mk isSheaf_of_isLimit homMk obj"
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
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis.PresheafOfModules"

namespace PresheafOfModules
p2m_export "PresheafOfModules" "presheaf sections map_id evaluation map ofPresheaf hom_ext evaluationJointlyReflectsLimits Hom id_app unit comp_app free restriction map_comp mk isSheaf_of_isLimit homMk obj"
p2m_open "PresheafOfModules"

lemma sum_app {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}} {M N : PresheafOfModules.{u} R}
    {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N)) (X : Cᵒᵖ) :
    (∑ i ∈ s, f i).app X = ∑ i ∈ s, (f i).app X :=
  Functor.map_sum (evaluation R X) f s

end PresheafOfModules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis.PresheafOfModules"

namespace SheafOfModules
p2m_export "SheafOfModules" "isColimitFreeCofan over mk forget val hom_ext evaluation isSheaf unit Hom sections free"
p2m_open "SheafOfModules"

lemma sum_val {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R} {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N)) :
    (∑ i ∈ s, f i).val = ∑ i ∈ s, (f i).val :=
  Functor.map_sum (SheafOfModules.forget R) f s

end SheafOfModules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis.PresheafOfModules"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Opens.ι_appIso Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme Scheme.Modules.Hom.id_app Scheme.Modules.restrict_map Scheme.Modules Scheme.Opens Scheme.Opens.opensRange_ι Scheme.Modules.IsLocallyFreeOfRank"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "forget ringCatSheaf Hom.id_app Hom mk Γ Modules.Hom.comp_app Opens.ι_appIso Modules.Hom Hom.image_preimage_eq_opensRange_inf Modules.Hom.id_app Modules.restrict_map restrictFunctor Hom.comp_app Modules Opens grothendieckTopology Modules.map_smul Opens.opensRange_ι PresheafOfModules evaluation Modules.IsLocallyFreeOfRank"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext Hom.app_smul presheaf Hom.comp_app Hom mapPresheaf_app restrictFunctor Hom.id_app restrictFunctorIsoPullback restrict_map isSheaf map_smul IsLocallyFreeOfRank"
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
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis.PresheafOfModules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis.PresheafOfModules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis.PresheafOfModules"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Opens.ι_appIso Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme Scheme.Modules.Hom.id_app Scheme.Modules.restrict_map Scheme.Modules Scheme.Opens Scheme.Opens.opensRange_ι Scheme.Modules.IsLocallyFreeOfRank"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "forget ringCatSheaf Hom.id_app Hom mk Γ Modules.Hom.comp_app Opens.ι_appIso Modules.Hom Hom.image_preimage_eq_opensRange_inf Modules.Hom.id_app Modules.restrict_map restrictFunctor Hom.comp_app Modules Opens grothendieckTopology Modules.map_smul Opens.opensRange_ι PresheafOfModules evaluation Modules.IsLocallyFreeOfRank"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext Hom.app_smul presheaf Hom.comp_app Hom mapPresheaf_app restrictFunctor Hom.id_app restrictFunctorIsoPullback restrict_map isSheaf map_smul IsLocallyFreeOfRank"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

section helpers

lemma map_eq_map' {M : X.Modules} {W₁ W₂ : X.Opens} (i j : W₁ ⟶ W₂) (m : Γ(M, W₂)) :
    M.presheaf.map i.op m = M.presheaf.map j.op m := by
  rw [Subsingleton.elim i j]

lemma map_map_of_eq {M : X.Modules} {W₁ W₂ : X.Opens} (h : W₁ = W₂) (m : Γ(M, W₂)) :
    M.presheaf.map (homOfLE h.ge).op (M.presheaf.map (homOfLE h.le).op m) = m := by
  subst h
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  have : ((homOfLE (le_refl W₁)).op ≫ (homOfLE (le_refl W₁)).op) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

lemma ringMap_ringMap_of_eq {W₁ W₂ : X.Opens} (h : W₁ = W₂) (a : Γ(X, W₂)) :
    X.presheaf.map (homOfLE h.ge).op (X.presheaf.map (homOfLE h.le).op a) = a := by
  subst h
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  have : ((homOfLE (le_refl W₁)).op ≫ (homOfLE (le_refl W₁)).op) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

lemma image_preimage_eq_of_le {V W : X.Opens} (hW : W ≤ V) : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 hW]

lemma restrictFunctor_obj_presheaf_map (M : X.Modules) (V : X.Opens) {W₁ W₂ : (V : Scheme.{u}).Opens}
    (i : W₁ ⟶ W₂) (m : Γ((restrictFunctor V.ι).obj M, W₂)) :
    ((restrictFunctor V.ι).obj M).presheaf.map i.op m =
      M.presheaf.map (homOfLE (V.ι.image_mono i.le)).op (m : Γ(M, V.ι ''ᵁ W₂)) := by
  rw [Scheme.Modules.restrict_map]
  exact map_eq_map' _ _ _

end helpers
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis.PresheafOfModules"

namespace IsLocallyFreeOfRank p2m_export "AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank" "mk exists_trivialization" end IsLocallyFreeOfRank
namespace IsLocallyFreeOfRank
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank" in

private theorem _root_.AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.exists_basis {n : ℕ} {M : X.Modules} (hM : IsLocallyFreeOfRank n M) (x : X) :
    ∃ (V : X.Opens), x ∈ V ∧ ∃ e : Fin n → Γ(M, V), ∀ (W : X.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i) := by
  obtain ⟨V, hxV, ⟨e⟩⟩ := hM.exists_trivialization x

  let t : (restrictFunctor V.ι).obj M ≅ piPow (V : Scheme.{u}) n :=
    (restrictFunctorIsoPullback V.ι).app M ≪≫ e ≪≫ freeIsoPiPow (V : Scheme.{u}) n
  have hV : V.ι ''ᵁ ⊤ = V := V.ι_image_top

  let std : ∀ (W' : (V : Scheme.{u}).Opens), Fin n → Γ(piPow (V : Scheme.{u}) n, W') :=
    fun W' i => (Pi.single i 1 : Fin n → ((V : Scheme.{u}).presheaf.obj (op W')))

  let e₀ : Fin n → Γ(M, V.ι ''ᵁ ⊤) := fun i => (t.inv.app ⊤ (std ⊤ i) : Γ(M, V.ι ''ᵁ ⊤))
  refine ⟨V, hxV, fun i => M.presheaf.map (homOfLE hV.ge).op (e₀ i), fun W hW => ?_⟩

  let W' : (V : Scheme.{u}).Opens := V.ι ⁻¹ᵁ W
  have hW' : V.ι ''ᵁ W' = W := image_preimage_eq_of_le hW

  let ρ : Γ(M, W) → Γ(M, V.ι ''ᵁ W') := fun m => M.presheaf.map (homOfLE hW'.le).op m
  let σ : Γ(M, V.ι ''ᵁ W') → Γ(M, W) := fun m => M.presheaf.map (homOfLE hW'.ge).op m
  let ρR : Γ(X, W) → Γ(X, V.ι ''ᵁ W') := fun a => X.presheaf.map (homOfLE hW'.le).op a
  let σR : Γ(X, V.ι ''ᵁ W') → Γ(X, W) := fun a => X.presheaf.map (homOfLE hW'.ge).op a
  have hσρ : ∀ m, σ (ρ m) = m := fun m => map_map_of_eq hW' m
  have hσρR : ∀ a, σR (ρR a) = a := fun a => ringMap_ringMap_of_eq hW' a
  have hρ_smul : ∀ (a : Γ(X, W)) (m : Γ(M, W)), ρ (a • m) = ρR a • ρ m :=
    fun a m => Modules.map_smul M _ a m
  have hσ_smul : ∀ (a : Γ(X, V.ι ''ᵁ W')) (m : Γ(M, V.ι ''ᵁ W')), σ (a • m) = σR a • σ m :=
    fun a m => Modules.map_smul M _ a m
  have hρ0 : ρ 0 = 0 := map_zero (ConcreteCategory.hom (M.presheaf.map (homOfLE hW'.le).op))
  have hσR0 : σR 0 = 0 := map_zero (ConcreteCategory.hom (X.presheaf.map (homOfLE hW'.ge).op))
  have hρsum : ∀ (f : Fin n → Γ(M, W)), ρ (∑ j, f j) = ∑ j, ρ (f j) :=
    fun f => map_sum (ConcreteCategory.hom (M.presheaf.map (homOfLE hW'.le).op)) _ _
  have hσsum : ∀ (f : Fin n → Γ(M, V.ι ''ᵁ W')), σ (∑ j, f j) = ∑ j, σ (f j) :=
    fun f => map_sum (ConcreteCategory.hom (M.presheaf.map (homOfLE hW'.ge).op)) _ _

  have key : ∀ i, ρ (M.presheaf.map (homOfLE hW).op (M.presheaf.map (homOfLE hV.ge).op (e₀ i))) =
      (t.inv.app W' (std W' i) : Γ(M, V.ι ''ᵁ W')) := by
    intro i
    have h1 : ρ (M.presheaf.map (homOfLE hW).op (M.presheaf.map (homOfLE hV.ge).op (e₀ i))) =
        M.presheaf.map (homOfLE (V.ι.image_mono (le_top : W' ≤ ⊤))).op (e₀ i) := by
      change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ (e₀ i))) = _
      rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
      exact map_eq_map' _ _ _
    rw [h1]
    have h2 := congr($(t.inv.mapPresheaf.naturality (homOfLE (le_top : W' ≤ ⊤)).op) (std ⊤ i))
    simp only [CategoryTheory.comp_apply, mapPresheaf_app] at h2

    have h3 : (piPow (V : Scheme.{u}) n).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op (std ⊤ i) = std W' i := by
      funext j
      change (V : Scheme.{u}).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op ((Pi.single i 1 : Fin n → _) j) =
        (Pi.single i 1 : Fin n → _) j
      by_cases h : j = i
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    rw [h3] at h2

    rw [h2]
    exact (restrictFunctor_obj_presheaf_map M V (homOfLE (le_top : W' ≤ ⊤)) _).symm

  let A : Type u := Γ((V : Scheme.{u}), W')
  let N : Type u := Γ((restrictFunctor V.ι).obj M, W')
  have ht₁ : ∀ m : N, (t.inv.app W') (t.hom.app W' m) = m := fun m => by
    rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, t.hom_inv_id, Scheme.Modules.Hom.id_app]
    rfl
  have ht₂ : ∀ v : Γ(piPow (V : Scheme.{u}) n, W'), (t.hom.app W') (t.inv.app W' v) = v := fun v => by
    rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, t.inv_hom_id, Scheme.Modules.Hom.id_app]
    rfl
  let tW : N ≃ₗ[A] (Fin n → A) :=
    { toFun := fun m => (t.hom.app W' m : (Fin n → A))
      invFun := fun v => (t.inv.app W' v : N)
      map_add' := fun m m' => (t.hom.app W').hom.map_add m m'
      map_smul' := fun a m => by
        rw [RingHom.id_apply]
        exact Hom.app_smul t.hom a m
      left_inv := ht₁
      right_inv := ht₂ }
  let b' : Module.Basis (Fin n) A N := (Pi.basisFun A (Fin n)).map tW.symm
  have hb' : ∀ i, b' i = (t.inv.app W' (std W' i) : N) := fun i => by
    simp only [b', Module.Basis.map_apply, Pi.basisFun_apply]
    rfl

  have hXN : ∀ (a : Γ(X, V.ι ''ᵁ W')) (m : Γ(M, V.ι ''ᵁ W')), a • m = @HSMul.hSMul A N N _ a m := by
    intro a m
    change _ = (((V.ι.appIso W').inv a : Γ(X, V.ι ''ᵁ W')) • m : Γ(M, V.ι ''ᵁ W'))
    simp [Scheme.Opens.ι_appIso] <;> rfl

  let v : Fin n → Γ(M, W) := fun i => M.presheaf.map (homOfLE hW).op (M.presheaf.map (homOfLE hV.ge).op (e₀ i))
  have hρv : ∀ i, ρ (v i) = (b' i : Γ(M, V.ι ''ᵁ W')) := fun i => (key i).trans (hb' i).symm
  have hli : LinearIndependent Γ(X, W) v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h0 : ∑ j, @HSMul.hSMul A N N _ (ρR (c j)) (b' j) = (0 : N) := by
      have h := congrArg ρ hc
      rw [hρ0, hρsum] at h
      rw [← h]
      exact Finset.sum_congr rfl (fun j _ => by rw [hρ_smul, hXN, hρv])
    have h1 : ρR (c i) = 0 :=
      (Fintype.linearIndependent_iff.mp b'.linearIndependent) (fun j => ρR (c j)) h0 i
    rw [← hσρR (c i)]
    change σR (ρR (c i)) = 0
    rw [h1, hσR0]
  have hsp : ⊤ ≤ Submodule.span (X.presheaf.obj (op W)) (Set.range v) := by
    rintro m -
    set r := b'.repr (ρ m) with hr
    have hm : ρ m = ∑ j, @HSMul.hSMul A N N _ (r j) (b' j) := (b'.sum_repr (ρ m)).symm
    have hm' : m = ∑ j, σR (r j) • v j := by
      conv_lhs => rw [← hσρ m]
      change σ (ρ m) = _
      rw [hm, hσsum]
      exact Finset.sum_congr rfl (fun j _ => by rw [← hXN, hσ_smul, ← hρv, hσρ])
    rw [hm']
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  exact ⟨Module.Basis.mk hli hsp, fun i => by rw [Module.Basis.mk_apply]⟩

end IsLocallyFreeOfRank
p2m_export "AlgebraicGeometry.Scheme.Modules" "IsLocallyFreeOfRank.exists_basis"
end AlgebraicGeometry.Scheme.Modules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis.PresheafOfModules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis.PresheafOfModules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis.PresheafOfModules"

theorem solution {X : AlgebraicGeometry.Scheme.{u}} {n : ℕ} {M : X.Modules}
    (hM : AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank n M) (x : X) :
    ∃ (V : X.Opens), x ∈ V ∧ ∃ e : Fin n → Γ(M, V), ∀ (W : X.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i) :=
  hM.exists_basis x

end S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis (solution)
