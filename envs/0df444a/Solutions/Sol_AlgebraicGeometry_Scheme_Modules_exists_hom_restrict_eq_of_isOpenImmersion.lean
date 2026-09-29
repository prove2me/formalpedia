-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_hom_restrict_eq_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/f51fed8a-a7df-5dac-b542-0cf05325d45a

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_restrict_eq_of_isOpenImmersion

set_option autoImplicit false

universe u v

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Scheme.Modules.Hom.app_smul Surjective Scheme.Hom.opensRange_comp Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Modules.restrictFunctorCongr Scheme Scheme.Modules.restrictFunctor Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app IsOpenImmersion Scheme.Modules.restrictFunctorComp Scheme.Modules Scheme.Modules.map_smul Scheme.Hom.image_le_opensRange Scheme.Modules.exists_fibreProduct_sections_bijective Scheme.Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.hom_ext Modules.Hom.app_smul Hom.opensRange_comp Hom.id_app Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom Hom.image_preimage_eq_opensRange_inf Modules.restrictFunctorCongr Modules.restrictFunctor Modules.Hom.id_app Modules.Hom.app restrictFunctor Hom.comp_app Modules.restrictFunctorComp Modules Opens Modules.map_smul restrict Hom.image_le_opensRange PresheafOfModules Modules.exists_fibreProduct_sections_bijective Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext Hom.app_smul pushforward presheaf Hom.comp_app Hom restrictFunctorCongr restrictFunctor Hom.id_app Hom.app restrictAdjunction restrictFunctorComp restrict map_smul exists_fibreProduct_sections_bijective Hom.isIso_of_isIso_app_of_iSup_eq_top"
namespace GlueHom
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_restrict_eq_of_isOpenImmersion.AlgebraicGeometry Opposite TopologicalSpace AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_restrict_eq_of_isOpenImmersion.AlgebraicGeometry.Scheme.Modules"

section Generic

variable {Y : Scheme.{u}}

theorem op_hom_eq {U V : Y.Opens} (i j : op U ⟶ op V) : i = j :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem map_endo (M : Y.Modules) {U : Y.Opens} (i : op U ⟶ op U) (x : Γ(M, U)) :
    M.presheaf.map i x = x := by
  rw [op_hom_eq i (𝟙 _), CategoryTheory.Functor.map_id]; rfl

theorem map_map (M : Y.Modules) {U V W : Y.Opens} (i : op U ⟶ op V) (j : op V ⟶ op W) (x : Γ(M, U)) :
    M.presheaf.map j (M.presheaf.map i x) = M.presheaf.map (i ≫ j) x := by
  rw [Functor.map_comp]; rfl

theorem map_irrel (M : Y.Modules) {U V : Y.Opens} (i j : op U ⟶ op V) (x : Γ(M, U)) :
    M.presheaf.map i x = M.presheaf.map j x := by rw [op_hom_eq i j]

theorem ring_map_endo {U : Y.Opens} (i : op U ⟶ op U) (x : Y.presheaf.obj (op U)) :
    Y.presheaf.map i x = x := by
  rw [op_hom_eq i (𝟙 _), CategoryTheory.Functor.map_id]; rfl

theorem ring_map_map {U V W : Y.Opens} (i : op U ⟶ op V) (j : op V ⟶ op W) (x : Y.presheaf.obj (op U)) :
    Y.presheaf.map j (Y.presheaf.map i x) = Y.presheaf.map (i ≫ j) x := by
  rw [Functor.map_comp]; rfl

theorem map_comp_eq (M : Y.Modules) {U V W : Y.Opens} (i : op U ⟶ op V) (j : op V ⟶ op W) (k : op U ⟶ op W) :
    M.presheaf.map i ≫ M.presheaf.map j = M.presheaf.map k := by
  rw [← Functor.map_comp, op_hom_eq (i ≫ j) k]

theorem app_naturality {M N : Y.Modules} (φ : M ⟶ N) {U V : Y.Opens} (i : op U ⟶ op V) (x : Γ(M, U)) :
    φ.app V (M.presheaf.map i x) = N.presheaf.map i (φ.app U x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i) x

theorem bijective_app_of_iso {M N : Y.Modules} (e : M ≅ N) (U : Y.Opens) :
    Function.Bijective (e.hom.app U) := by
  rw [← ConcreteCategory.isIso_iff_bijective]
  exact ⟨⟨e.inv.app U, by rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app],
    by rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]⟩⟩

theorem bijective_app_comp {M N K : Y.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (U : Y.Opens)
    (hφ : Function.Bijective (φ.app U)) (hψ : Function.Bijective (ψ.app U)) :
    Function.Bijective ((φ ≫ ψ).app U) := by
  rw [Scheme.Modules.Hom.comp_app]; exact hψ.comp hφ

theorem bijective_map_of_eq (M : Y.Modules) {U V : Y.Opens} (h : U = V) (i : op U ⟶ op V) :
    Function.Bijective (M.presheaf.map i) := by
  subst h
  have : (M.presheaf.map i : Γ(M, U) → Γ(M, U)) = id := funext fun x => map_endo M i x
  rw [this]; exact Function.bijective_id

theorem pushforward_map_apply {Z : Scheme.{u}} (f : Y ⟶ Z) (M : Y.Modules) {U V : Z.Opens} (i : op U ⟶ op V)
    (x : Γ((pushforward f).obj M, U)) :
    ((pushforward f).obj M).presheaf.map i x = M.presheaf.map ((Opens.map f.base).map i.unop).op x := rfl

end Generic

section Lift

variable {X : Scheme.{u}} {N₀ N₁ N₀₁ G M : X.Modules} (a : N₀ ⟶ N₀₁) (b : N₁ ⟶ N₀₁)
  (π₀ : G ⟶ N₀) (π₁ : G ⟶ N₁)
  (hinj : ∀ U : X.Opens, Function.Injective fun s : Γ(G, U) => (π₀.app U s, π₁.app U s))
  (hlift : ∀ (U : X.Opens) (s₀ : Γ(N₀, U)) (s₁ : Γ(N₁, U)), a.app U s₀ = b.app U s₁ →
    ∃ s : Γ(G, U), π₀.app U s = s₀ ∧ π₁.app U s = s₁)
  (u₀ : M ⟶ N₀) (u₁ : M ⟶ N₁) (hu : u₀ ≫ a = u₁ ≫ b)

include hu in
theorem hu_app (U : X.Opens) (s : Γ(M, U)) : a.app U (u₀.app U s) = b.app U (u₁.app U s) := by
  have h := congrArg (fun φ => Scheme.Modules.Hom.app φ U s) hu
  simp only [Scheme.Modules.Hom.comp_app] at h
  exact h

def liftFun (U : X.Opens) (s : Γ(M, U)) : Γ(G, U) :=
  (hlift U (u₀.app U s) (u₁.app U s) (hu_app a b u₀ u₁ hu U s)).choose

theorem π₀_liftFun (U : X.Opens) (s : Γ(M, U)) : π₀.app U (liftFun a b π₀ π₁ hlift u₀ u₁ hu U s) = u₀.app U s :=
  (hlift U (u₀.app U s) (u₁.app U s) (hu_app a b u₀ u₁ hu U s)).choose_spec.1

theorem π₁_liftFun (U : X.Opens) (s : Γ(M, U)) : π₁.app U (liftFun a b π₀ π₁ hlift u₀ u₁ hu U s) = u₁.app U s :=
  (hlift U (u₀.app U s) (u₁.app U s) (hu_app a b u₀ u₁ hu U s)).choose_spec.2

include hinj in
theorem liftFun_eq_of (U : X.Opens) (s : Γ(M, U)) (t : Γ(G, U)) (h₀ : π₀.app U t = u₀.app U s)
    (h₁ : π₁.app U t = u₁.app U s) : liftFun a b π₀ π₁ hlift u₀ u₁ hu U s = t := by
  apply hinj U
  refine Prod.ext ?_ ?_
  · exact (π₀_liftFun a b π₀ π₁ hlift u₀ u₁ hu U s).trans h₀.symm
  · exact (π₁_liftFun a b π₀ π₁ hlift u₀ u₁ hu U s).trans h₁.symm

include hinj in
theorem liftFun_add (U : X.Opens) (s t : Γ(M, U)) :
    liftFun a b π₀ π₁ hlift u₀ u₁ hu U (s + t) =
      liftFun a b π₀ π₁ hlift u₀ u₁ hu U s + liftFun a b π₀ π₁ hlift u₀ u₁ hu U t := by
  apply liftFun_eq_of a b π₀ π₁ hinj hlift u₀ u₁ hu
  · rw [map_add, map_add, π₀_liftFun, π₀_liftFun]
  · rw [map_add, map_add, π₁_liftFun, π₁_liftFun]

include hinj in
theorem liftFun_smul (U : X.Opens) (r : X.presheaf.obj (op U)) (s : Γ(M, U)) :
    liftFun a b π₀ π₁ hlift u₀ u₁ hu U (r • s) = r • liftFun a b π₀ π₁ hlift u₀ u₁ hu U s := by
  apply liftFun_eq_of a b π₀ π₁ hinj hlift u₀ u₁ hu
  · rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, π₀_liftFun]
  · rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, π₁_liftFun]

include hinj in
theorem liftFun_map {U V : X.Opens} (i : op U ⟶ op V) (s : Γ(M, U)) :
    liftFun a b π₀ π₁ hlift u₀ u₁ hu V (M.presheaf.map i s) =
      G.presheaf.map i (liftFun a b π₀ π₁ hlift u₀ u₁ hu U s) := by
  apply liftFun_eq_of a b π₀ π₁ hinj hlift u₀ u₁ hu
  · rw [app_naturality, π₀_liftFun, app_naturality]
  · rw [app_naturality, π₁_liftFun, app_naturality]

def liftPresheafHom : M.presheaf ⟶ G.presheaf where
  app U := AddCommGrpCat.ofHom
    { toFun := fun s => liftFun a b π₀ π₁ hlift u₀ u₁ hu U.unop s
      map_zero' := by
        have h := liftFun_add a b π₀ π₁ hinj hlift u₀ u₁ hu U.unop 0 0
        rw [add_zero] at h
        exact left_eq_add.mp h
      map_add' := fun s t => liftFun_add a b π₀ π₁ hinj hlift u₀ u₁ hu U.unop s t }
  naturality U V i := by
    ext s
    exact liftFun_map a b π₀ π₁ hinj hlift u₀ u₁ hu i s

def lift : M ⟶ G :=
  ⟨PresheafOfModules.homMk (liftPresheafHom a b π₀ π₁ hinj hlift u₀ u₁ hu)
    (fun U r s => liftFun_smul a b π₀ π₁ hinj hlift u₀ u₁ hu U.unop r s)⟩

theorem lift_app (U : X.Opens) (s : Γ(M, U)) :
    (lift a b π₀ π₁ hinj hlift u₀ u₁ hu).app U s = liftFun a b π₀ π₁ hlift u₀ u₁ hu U s := rfl

theorem lift_π₀ : lift a b π₀ π₁ hinj hlift u₀ u₁ hu ≫ π₀ = u₀ := by
  apply Scheme.Modules.hom_ext; intro U; ext s
  rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, lift_app, π₀_liftFun]

theorem lift_π₁ : lift a b π₀ π₁ hinj hlift u₀ u₁ hu ≫ π₁ = u₁ := by
  apply Scheme.Modules.hom_ext; intro U; ext s
  rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, lift_app, π₁_liftFun]

theorem lift_app_π₀ (U : X.Opens) (s : Γ(M, U)) :
    π₀.app U ((lift a b π₀ π₁ hinj hlift u₀ u₁ hu).app U s) = u₀.app U s := by
  rw [lift_app, π₀_liftFun]

theorem lift_app_π₁ (U : X.Opens) (s : Γ(M, U)) :
    π₁.app U ((lift a b π₀ π₁ hinj hlift u₀ u₁ hu).app U s) = u₁.app U s := by
  rw [lift_app, π₁_liftFun]

end Lift

section ResHom

variable {X A B : Scheme.{u}} (p : A ⟶ X) (q : B ⟶ X) [IsOpenImmersion p] [IsOpenImmersion q]

theorem comp_app_apply {M N K : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (U : X.Opens) (x : Γ(M, U)) :
    (φ ≫ ψ).app U x = ψ.app U (φ.app U x) := rfl

def resHom (hle : ∀ W : X.Opens, q ''ᵁ (q ⁻¹ᵁ W) ≤ p ''ᵁ (p ⁻¹ᵁ W)) (N : X.Modules) :
    (pushforward p).obj (N.restrict p) ⟶ (pushforward q).obj (N.restrict q) :=
  ⟨PresheafOfModules.homMk
    { app := fun W => N.presheaf.map (homOfLE (hle W.unop)).op
      naturality := fun W W' i => by
        change N.presheaf.map _ ≫ N.presheaf.map _ = N.presheaf.map _ ≫ N.presheaf.map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        rfl }
    (fun W r m => by
      obtain ⟨W⟩ := W
      show N.presheaf.map (homOfLE (hle W)).op
          (((p.appIso (p ⁻¹ᵁ W)).inv (p.app W r)) • (show Γ(N, p ''ᵁ (p ⁻¹ᵁ W)) from m)) =
        ((q.appIso (q ⁻¹ᵁ W)).inv (q.app W r)) •
          N.presheaf.map (homOfLE (hle W)).op (show Γ(N, p ''ᵁ (p ⁻¹ᵁ W)) from m)
      rw [Scheme.Modules.map_smul]
      congr 1
      have hp : (p.appIso (p ⁻¹ᵁ W)).inv (p.app W r) =
          X.presheaf.map (homOfLE (Set.image_preimage_subset p W.1)).op r :=
        congrArg (fun t => (CommRingCat.Hom.hom t) r) (p.app_appIso_inv W)
      have hq : (q.appIso (q ⁻¹ᵁ W)).inv (q.app W r) =
          X.presheaf.map (homOfLE (Set.image_preimage_subset q W.1)).op r :=
        congrArg (fun t => (CommRingCat.Hom.hom t) r) (q.app_appIso_inv W)
      rw [hp, hq, ring_map_map]
      rfl)⟩

theorem resHom_apply (hle : ∀ W : X.Opens, q ''ᵁ (q ⁻¹ᵁ W) ≤ p ''ᵁ (p ⁻¹ᵁ W)) (N : X.Modules) (W : X.Opens)
    (s : Γ((pushforward p).obj (N.restrict p), W)) :
    (resHom p q hle N).app W s = N.presheaf.map (homOfLE (hle W)).op s := rfl

theorem bijective_resHom_app (hle : ∀ W : X.Opens, q ''ᵁ (q ⁻¹ᵁ W) ≤ p ''ᵁ (p ⁻¹ᵁ W)) (N : X.Modules)
    {W : X.Opens} (h : q ''ᵁ (q ⁻¹ᵁ W) = p ''ᵁ (p ⁻¹ᵁ W)) :
    Function.Bijective ((resHom p q hle N).app W) :=
  bijective_map_of_eq N h.symm _

omit [IsOpenImmersion q] in

theorem unit_apply (N : X.Modules) (W : X.Opens) (s : Γ(N, W)) :
    ((restrictAdjunction p).unit.app N).app W s = N.presheaf.map (homOfLE (p.image_preimage_le W)).op s := rfl

omit [IsOpenImmersion q] in
theorem bijective_unit_app (N : X.Modules) {W : X.Opens} (hW : W ≤ p.opensRange) :
    Function.Bijective (((restrictAdjunction p).unit.app N).app W) := by
  rw [show ((restrictAdjunction p).unit.app N).app W = N.presheaf.map (homOfLE (p.image_preimage_le W)).op from rfl]
  refine bijective_map_of_eq N ?_ _
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
  exact (inf_eq_right.mpr hW).symm

omit [IsOpenImmersion p] [IsOpenImmersion q] in
theorem pushforward_app_apply {M N : A.Modules} (φ : M ⟶ N) (W : X.Opens) (x : Γ((pushforward p).obj M, W)) :
    ((pushforward p).map φ).app W x = φ.app (p ⁻¹ᵁ W) x := rfl

omit [IsOpenImmersion q] in
theorem restrict_map_apply (M : X.Modules) {U V : A.Opens} (i : op U ⟶ op V) (x : Γ(M.restrict p, U)) :
    (M.restrict p).presheaf.map i x = M.presheaf.map (p.opensFunctor.map i.unop).op x := rfl

omit [IsOpenImmersion p] [IsOpenImmersion q] in
theorem image_comp_eq {C : Scheme.{u}} (g : C ⟶ A) (f : A ⟶ X) [IsOpenImmersion g] [IsOpenImmersion f]
    (U : C.Opens) : (g ≫ f) ''ᵁ U = f ''ᵁ (g ''ᵁ U) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨g.base x, ⟨x, hx, rfl⟩, by simp⟩
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp⟩

omit [IsOpenImmersion p] [IsOpenImmersion q] in
theorem image_eq_of_eq {p' q' : A ⟶ X} [IsOpenImmersion p'] [IsOpenImmersion q'] (h : p' = q') (V : A.Opens) :
    p' ''ᵁ V = q' ''ᵁ V := by subst h; rfl

omit [IsOpenImmersion p] [IsOpenImmersion q] in
theorem opensRange_eq_of_eq {p' q' : A ⟶ X} [IsOpenImmersion p'] [IsOpenImmersion q'] (h : p' = q') :
    p'.opensRange = q'.opensRange := by subst h; rfl

omit [IsOpenImmersion p] [IsOpenImmersion q] in
theorem preimage_eq_of_eq {p' q' : A ⟶ X} (h : p' = q') (W : X.Opens) : p' ⁻¹ᵁ W = q' ⁻¹ᵁ W := by subst h; rfl

omit [IsOpenImmersion q] in
theorem restrictComp_hom_apply {C : Scheme.{u}} (g : C ⟶ A) [IsOpenImmersion g] (M : X.Modules) (V : C.Opens)
    (t : Γ(M.restrict (g ≫ p), V)) :
    (((restrictFunctorComp g p).hom.app M).app V t : Γ(M, p ''ᵁ (g ''ᵁ V))) =
      M.presheaf.map (eqToHom (image_comp_eq g p V).symm).op (show Γ(M, (g ≫ p) ''ᵁ V) from t) := rfl

omit [IsOpenImmersion q] in
theorem restrictComp_inv_apply {C : Scheme.{u}} (g : C ⟶ A) [IsOpenImmersion g] (M : X.Modules) (V : C.Opens)
    (t : Γ((M.restrict p).restrict g, V)) :
    (((restrictFunctorComp g p).inv.app M).app V t : Γ(M, (g ≫ p) ''ᵁ V)) =
      M.presheaf.map (eqToHom (image_comp_eq g p V)).op (show Γ(M, p ''ᵁ (g ''ᵁ V)) from t) := rfl

omit [IsOpenImmersion p] [IsOpenImmersion q] in
theorem restrictCongr_hom_apply {p' q' : A ⟶ X} [IsOpenImmersion p'] [IsOpenImmersion q'] (h : p' = q')
    (M : X.Modules) (V : A.Opens) (t : Γ(M.restrict p', V)) :
    (((restrictFunctorCongr h).hom.app M).app V t : Γ(M, q' ''ᵁ V)) =
      M.presheaf.map (eqToHom (image_eq_of_eq h V).symm).op (show Γ(M, p' ''ᵁ V) from t) := rfl

omit [IsOpenImmersion p] [IsOpenImmersion q] in
theorem restrictCongr_inv_apply {p' q' : A ⟶ X} [IsOpenImmersion p'] [IsOpenImmersion q'] (h : p' = q')
    (M : X.Modules) (V : A.Opens) (t : Γ(M.restrict q', V)) :
    (((restrictFunctorCongr h).inv.app M).app V t : Γ(M, p' ''ᵁ V)) =
      M.presheaf.map (eqToHom (image_eq_of_eq h V)).op (show Γ(M, q' ''ᵁ V) from t) := rfl

omit [IsOpenImmersion p] in
theorem restrict_app_apply {M N : X.Modules} (φ : M ⟶ N) (V : B.Opens) (x : Γ(M.restrict q, V)) :
    ((restrictFunctor q).map φ).app V x = φ.app (q ''ᵁ V) x := rfl

end ResHom

section Glue

variable {X Y₀ Y₁ Y₀₁ : Scheme.{u}} (f₀ : Y₀ ⟶ X) (f₁ : Y₁ ⟶ X) [IsOpenImmersion f₀] [IsOpenImmersion f₁]
  (g₀ : Y₀₁ ⟶ Y₀) (g₁ : Y₀₁ ⟶ Y₁) [IsOpenImmersion g₀] [IsOpenImmersion g₁]
  (hg : g₀ ≫ f₀ = g₁ ≫ f₁)

abbrev N0 (N : X.Modules) : X.Modules := (pushforward f₀).obj (N.restrict f₀)
abbrev N1 (N : X.Modules) : X.Modules := (pushforward f₁).obj (N.restrict f₁)
abbrev N01 (N : X.Modules) : X.Modules := (pushforward (g₀ ≫ f₀)).obj (N.restrict (g₀ ≫ f₀))

theorem le_a (W : X.Opens) : (g₀ ≫ f₀) ''ᵁ ((g₀ ≫ f₀) ⁻¹ᵁ W) ≤ f₀ ''ᵁ (f₀ ⁻¹ᵁ W) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.image_preimage_eq_opensRange_inf]
  refine inf_le_inf_right W ?_
  rw [Scheme.Hom.opensRange_comp]
  exact Scheme.Hom.image_le_opensRange f₀ _

include hg in
theorem le_b (W : X.Opens) : (g₀ ≫ f₀) ''ᵁ ((g₀ ≫ f₀) ⁻¹ᵁ W) ≤ f₁ ''ᵁ (f₁ ⁻¹ᵁ W) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.image_preimage_eq_opensRange_inf,
    opensRange_eq_of_eq hg]
  refine inf_le_inf_right W ?_
  rw [Scheme.Hom.opensRange_comp]
  exact Scheme.Hom.image_le_opensRange f₁ _

def a (N : X.Modules) : N0 f₀ N ⟶ N01 f₀ g₀ N := resHom f₀ (g₀ ≫ f₀) (le_a f₀ g₀) N

def b (N : X.Modules) : N1 f₁ N ⟶ N01 f₀ g₀ N := resHom f₁ (g₀ ≫ f₀) (le_b f₀ f₁ g₀ g₁ hg) N

theorem a_apply (N : X.Modules) (W : X.Opens) (s : Γ(N0 f₀ N, W)) :
    (a f₀ g₀ N).app W s = N.presheaf.map (homOfLE (le_a f₀ g₀ W)).op s := rfl
theorem b_apply (N : X.Modules) (W : X.Opens) (s : Γ(N1 f₁ N, W)) :
    (b f₀ f₁ g₀ g₁ hg N).app W s =
      N.presheaf.map (homOfLE (le_b f₀ f₁ g₀ g₁ hg W)).op s := rfl

variable (hov : f₀.opensRange ⊓ f₁.opensRange ≤ (g₀ ≫ f₀).opensRange)

include hg hov in
theorem opensRange_g₀f₀ : (g₀ ≫ f₀).opensRange = f₀.opensRange ⊓ f₁.opensRange := by
  refine le_antisymm (le_inf ?_ ?_) hov
  · rw [Scheme.Hom.opensRange_comp]; exact Scheme.Hom.image_le_opensRange f₀ _
  · rw [opensRange_eq_of_eq hg, Scheme.Hom.opensRange_comp]; exact Scheme.Hom.image_le_opensRange f₁ _

include g₁ hg hov in
theorem eq_a {W : X.Opens} (hW : W ≤ f₁.opensRange) : (g₀ ≫ f₀) ''ᵁ ((g₀ ≫ f₀) ⁻¹ᵁ W) = f₀ ''ᵁ (f₀ ⁻¹ᵁ W) := by
  have h := opensRange_g₀f₀ f₀ f₁ g₀ g₁ hg hov
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.image_preimage_eq_opensRange_inf, h, inf_assoc,
    inf_eq_right.mpr hW]

include g₁ hg hov in
theorem eq_b {W : X.Opens} (hW : W ≤ f₀.opensRange) : (g₀ ≫ f₀) ''ᵁ ((g₀ ≫ f₀) ⁻¹ᵁ W) = f₁ ''ᵁ (f₁ ⁻¹ᵁ W) := by
  have h := opensRange_g₀f₀ f₀ f₁ g₀ g₁ hg hov
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.image_preimage_eq_opensRange_inf, h,
    inf_right_comm, inf_eq_right.mpr hW, inf_comm]

include g₁ hg hov in
theorem bijective_a_app (N : X.Modules) {W : X.Opens} (hW : W ≤ f₁.opensRange) :
    Function.Bijective ((a f₀ g₀ N).app W) :=
  bijective_resHom_app _ _ _ N (eq_a f₀ f₁ g₀ g₁ hg hov hW)

include hov in
theorem bijective_b_app (N : X.Modules) {W : X.Opens} (hW : W ≤ f₀.opensRange) :
    Function.Bijective ((b f₀ f₁ g₀ g₁ hg N).app W) :=
  bijective_resHom_app _ _ _ N (eq_b f₀ f₁ g₀ g₁ hg hov hW)

variable (N : X.Modules)

theorem glue_exists : ∃ (G : X.Modules) (π₀ : G ⟶ N0 f₀ N) (π₁ : G ⟶ N1 f₁ N),
    π₀ ≫ a f₀ g₀ N = π₁ ≫ b f₀ f₁ g₀ g₁ hg N ∧
      (∀ U : X.Opens, Function.Injective fun s : Γ(G, U) => (π₀.app U s, π₁.app U s)) ∧
      (∀ (U : X.Opens) (s₀ : Γ(N0 f₀ N, U)) (s₁ : Γ(N1 f₁ N, U)),
        (a f₀ g₀ N).app U s₀ = (b f₀ f₁ g₀ g₁ hg N).app U s₁ →
        ∃ s : Γ(G, U), π₀.app U s = s₀ ∧ π₁.app U s = s₁) :=
  Scheme.Modules.exists_fibreProduct_sections_bijective _ _

def G : X.Modules := (glue_exists f₀ f₁ g₀ g₁ hg N).choose
def π₀ : G f₀ f₁ g₀ g₁ hg N ⟶ N0 f₀ N := (glue_exists f₀ f₁ g₀ g₁ hg N).choose_spec.choose
def π₁ : G f₀ f₁ g₀ g₁ hg N ⟶ N1 f₁ N := (glue_exists f₀ f₁ g₀ g₁ hg N).choose_spec.choose_spec.choose
theorem π_comm : π₀ f₀ f₁ g₀ g₁ hg N ≫ a f₀ g₀ N = π₁ f₀ f₁ g₀ g₁ hg N ≫ b f₀ f₁ g₀ g₁ hg N :=
  (glue_exists f₀ f₁ g₀ g₁ hg N).choose_spec.choose_spec.choose_spec.1
theorem π_inj (U : X.Opens) : Function.Injective fun s : Γ(G f₀ f₁ g₀ g₁ hg N, U) =>
    ((π₀ f₀ f₁ g₀ g₁ hg N).app U s, (π₁ f₀ f₁ g₀ g₁ hg N).app U s) :=
  (glue_exists f₀ f₁ g₀ g₁ hg N).choose_spec.choose_spec.choose_spec.2.1 U
theorem π_lift (U : X.Opens) (s₀ : Γ(N0 f₀ N, U)) (s₁ : Γ(N1 f₁ N, U))
    (h : (a f₀ g₀ N).app U s₀ = (b f₀ f₁ g₀ g₁ hg N).app U s₁) :
    ∃ s : Γ(G f₀ f₁ g₀ g₁ hg N, U), (π₀ f₀ f₁ g₀ g₁ hg N).app U s = s₀ ∧ (π₁ f₀ f₁ g₀ g₁ hg N).app U s = s₁ :=
  (glue_exists f₀ f₁ g₀ g₁ hg N).choose_spec.choose_spec.choose_spec.2.2 U s₀ s₁ h

theorem π_comm_app (W : X.Opens) (s : Γ(G f₀ f₁ g₀ g₁ hg N, W)) :
    (a f₀ g₀ N).app W ((π₀ f₀ f₁ g₀ g₁ hg N).app W s) =
      (b f₀ f₁ g₀ g₁ hg N).app W ((π₁ f₀ f₁ g₀ g₁ hg N).app W s) := by
  have h := congrArg (fun φ => Scheme.Modules.Hom.app φ W s) (π_comm f₀ f₁ g₀ g₁ hg N)
  simp only [Scheme.Modules.Hom.comp_app] at h
  exact h

include hov in
theorem bijective_π₀_app {W : X.Opens} (hW : W ≤ f₀.opensRange) :
    Function.Bijective ((π₀ f₀ f₁ g₀ g₁ hg N).app W) := by
  obtain ⟨binj, bsurj⟩ := bijective_b_app f₀ f₁ g₀ g₁ hg hov N hW
  constructor
  · intro s t hst
    apply π_inj f₀ f₁ g₀ g₁ hg N W
    refine Prod.ext hst (binj ?_)
    rw [← π_comm_app, ← π_comm_app, hst]
  · intro s₀
    obtain ⟨s₁, hs₁⟩ := bsurj ((a f₀ g₀ N).app W s₀)
    obtain ⟨s, hs, -⟩ := π_lift f₀ f₁ g₀ g₁ hg N W s₀ s₁ hs₁.symm
    exact ⟨s, hs⟩

include hov in
theorem bijective_π₁_app {W : X.Opens} (hW : W ≤ f₁.opensRange) :
    Function.Bijective ((π₁ f₀ f₁ g₀ g₁ hg N).app W) := by
  obtain ⟨ainj, asurj⟩ := bijective_a_app f₀ f₁ g₀ g₁ hg hov N hW
  constructor
  · intro s t hst
    apply π_inj f₀ f₁ g₀ g₁ hg N W
    refine Prod.ext (ainj ?_) hst
    rw [π_comm_app, π_comm_app, hst]
  · intro s₁
    obtain ⟨s₀, hs₀⟩ := asurj ((b f₀ f₁ g₀ g₁ hg N).app W s₁)
    obtain ⟨s, -, hs⟩ := π_lift f₀ f₁ g₀ g₁ hg N W s₀ s₁ hs₀
    exact ⟨s, hs⟩

def η₀ : N ⟶ N0 f₀ N := (restrictAdjunction f₀).unit.app N

def η₁ : N ⟶ N1 f₁ N := (restrictAdjunction f₁).unit.app N

theorem η₀_apply (W : X.Opens) (s : Γ(N, W)) :
    (η₀ f₀ N).app W s = N.presheaf.map (homOfLE (f₀.image_preimage_le W)).op s := rfl
theorem η₁_apply (W : X.Opens) (s : Γ(N, W)) :
    (η₁ f₁ N).app W s = N.presheaf.map (homOfLE (f₁.image_preimage_le W)).op s := rfl

theorem η_comm : η₀ f₀ N ≫ a f₀ g₀ N = η₁ f₁ N ≫ b f₀ f₁ g₀ g₁ hg N := by
  apply Scheme.Modules.hom_ext; intro W; ext s
  rw [comp_app_apply, comp_app_apply, a_apply, b_apply, η₀_apply, η₁_apply, map_map, map_map]
  rfl

def can : N ⟶ G f₀ f₁ g₀ g₁ hg N :=
  lift (a f₀ g₀ N) (b f₀ f₁ g₀ g₁ hg N) (π₀ f₀ f₁ g₀ g₁ hg N) (π₁ f₀ f₁ g₀ g₁ hg N)
    (π_inj f₀ f₁ g₀ g₁ hg N) (π_lift f₀ f₁ g₀ g₁ hg N) (η₀ f₀ N) (η₁ f₁ N) (η_comm f₀ f₁ g₀ g₁ hg N)

theorem can_π₀ : can f₀ f₁ g₀ g₁ hg N ≫ π₀ f₀ f₁ g₀ g₁ hg N = η₀ f₀ N := lift_π₀ ..
theorem can_π₁ : can f₀ f₁ g₀ g₁ hg N ≫ π₁ f₀ f₁ g₀ g₁ hg N = η₁ f₁ N := lift_π₁ ..

theorem bijective_of_comp {A B C : X.Modules} (v : A ⟶ B) (p : B ⟶ C) (w : A ⟶ C) (h : v ≫ p = w) (W : X.Opens)
    (hp : Function.Bijective (p.app W)) (hw : Function.Bijective (w.app W)) : Function.Bijective (v.app W) := by
  have hc : Function.Bijective ((v ≫ p).app W) := by rw [h]; exact hw
  rw [Scheme.Modules.Hom.comp_app] at hc
  change Function.Bijective ((p.app W) ∘ (v.app W)) at hc
  exact ⟨hc.1.of_comp, (Function.Surjective.of_comp_iff' hp _).mp hc.2⟩

variable (hcov : f₀.opensRange ⊔ f₁.opensRange = ⊤)

include hov hcov in
theorem isIso_can : IsIso (can f₀ f₁ g₀ g₁ hg N) := by
  refine Scheme.Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top (can f₀ f₁ g₀ g₁ hg N)
    (fun i : Bool => cond i f₀.opensRange f₁.opensRange) ?_ ?_
  · rw [iSup_bool_eq]; exact hcov
  · intro i V hV
    rw [ConcreteCategory.isIso_iff_bijective]
    cases i with
    | true =>
      exact bijective_of_comp _ _ _ (can_π₀ f₀ f₁ g₀ g₁ hg N) V (bijective_π₀_app f₀ f₁ g₀ g₁ hg hov N hV)
        (bijective_unit_app f₀ N hV)
    | false =>
      exact bijective_of_comp _ _ _ (can_π₁ f₀ f₁ g₀ g₁ hg N) V (bijective_π₁_app f₀ f₁ g₀ g₁ hg hov N hV)
        (bijective_unit_app f₁ N hV)

variable {M : X.Modules} (ψ₀ : M.restrict f₀ ⟶ N.restrict f₀) (ψ₁ : M.restrict f₁ ⟶ N.restrict f₁)
  (hψ : (restrictFunctorComp g₀ f₀).hom.app M ≫ (restrictFunctor g₀).map ψ₀ ≫ (restrictFunctorComp g₀ f₀).inv.app N =
    (restrictFunctorCongr hg).hom.app M ≫ (restrictFunctorComp g₁ f₁).hom.app M ≫ (restrictFunctor g₁).map ψ₁ ≫
      (restrictFunctorComp g₁ f₁).inv.app N ≫ (restrictFunctorCongr hg).inv.app N)

def u₀ : M ⟶ N0 f₀ N := η₀ f₀ M ≫ (pushforward f₀).map ψ₀
def u₁ : M ⟶ N1 f₁ N := η₁ f₁ M ≫ (pushforward f₁).map ψ₁

theorem u₀_apply (W : X.Opens) (s : Γ(M, W)) :
    (u₀ f₀ N ψ₀).app W s = ψ₀.app (f₀ ⁻¹ᵁ W) (M.presheaf.map (homOfLE (f₀.image_preimage_le W)).op s) := rfl
theorem u₁_apply (W : X.Opens) (s : Γ(M, W)) :
    (u₁ f₁ N ψ₁).app W s = ψ₁.app (f₁ ⁻¹ᵁ W) (M.presheaf.map (homOfLE (f₁.image_preimage_le W)).op s) := rfl

omit [IsOpenImmersion f₀] in
theorem g₀_image_le (W : X.Opens) : g₀ ''ᵁ ((g₀ ≫ f₀) ⁻¹ᵁ W) ≤ f₀ ⁻¹ᵁ W := by
  rintro y ⟨z, hz, rfl⟩
  simpa using hz

omit [IsOpenImmersion f₀] [IsOpenImmersion f₁] [IsOpenImmersion g₀] in
include hg in
theorem g₁_image_le (W : X.Opens) : g₁ ''ᵁ ((g₀ ≫ f₀) ⁻¹ᵁ W) ≤ f₁ ⁻¹ᵁ W := by
  rintro y ⟨z, hz, rfl⟩
  rw [preimage_eq_of_eq hg] at hz
  simpa using hz

theorem u₀_a_apply (W : X.Opens) (s : Γ(M, W))
    (k₁ : op W ⟶ op (f₀ ''ᵁ (g₀ ''ᵁ ((g₀ ≫ f₀) ⁻¹ᵁ W))))
    (k₂ : op (f₀ ''ᵁ (g₀ ''ᵁ ((g₀ ≫ f₀) ⁻¹ᵁ W))) ⟶ op ((g₀ ≫ f₀) ''ᵁ ((g₀ ≫ f₀) ⁻¹ᵁ W))) :
    (u₀ f₀ N ψ₀ ≫ a f₀ g₀ N).app W s =
      N.presheaf.map k₂ (ψ₀.app (g₀ ''ᵁ ((g₀ ≫ f₀) ⁻¹ᵁ W)) (M.presheaf.map k₁ s)) := by
  rw [comp_app_apply, a_apply, u₀_apply]
  have nat := app_naturality ψ₀ (homOfLE (g₀_image_le f₀ g₀ W)).op
    (M.presheaf.map (homOfLE (f₀.image_preimage_le W)).op s)
  have lhs : N.presheaf.map (homOfLE (le_a f₀ g₀ W)).op
      (ψ₀.app (f₀ ⁻¹ᵁ W) (M.presheaf.map (homOfLE (f₀.image_preimage_le W)).op s)) =
      N.presheaf.map k₂ ((N.restrict f₀).presheaf.map (homOfLE (g₀_image_le f₀ g₀ W)).op
        (ψ₀.app (f₀ ⁻¹ᵁ W) (M.presheaf.map (homOfLE (f₀.image_preimage_le W)).op s))) := by
    rw [restrict_map_apply, map_map]; rfl
  have hx : (M.restrict f₀).presheaf.map (homOfLE (g₀_image_le f₀ g₀ W)).op
      (M.presheaf.map (homOfLE (f₀.image_preimage_le W)).op s) = M.presheaf.map k₁ s := by
    rw [restrict_map_apply, map_map]; rfl
  refine lhs.trans ?_
  rw [← nat, hx]

theorem u₁_b_apply (W : X.Opens) (s : Γ(M, W))
    (k₁ : op W ⟶ op (f₁ ''ᵁ (g₁ ''ᵁ ((g₀ ≫ f₀) ⁻¹ᵁ W))))
    (k₂ : op (f₁ ''ᵁ (g₁ ''ᵁ ((g₀ ≫ f₀) ⁻¹ᵁ W))) ⟶ op ((g₀ ≫ f₀) ''ᵁ ((g₀ ≫ f₀) ⁻¹ᵁ W))) :
    (u₁ f₁ N ψ₁ ≫ b f₀ f₁ g₀ g₁ hg N).app W s =
      N.presheaf.map k₂ (ψ₁.app (g₁ ''ᵁ ((g₀ ≫ f₀) ⁻¹ᵁ W)) (M.presheaf.map k₁ s)) := by
  rw [comp_app_apply, b_apply, u₁_apply]
  have nat := app_naturality ψ₁ (homOfLE (g₁_image_le f₀ f₁ g₀ g₁ hg W)).op
    (M.presheaf.map (homOfLE (f₁.image_preimage_le W)).op s)
  have lhs : N.presheaf.map (homOfLE (le_b f₀ f₁ g₀ g₁ hg W)).op
      (ψ₁.app (f₁ ⁻¹ᵁ W) (M.presheaf.map (homOfLE (f₁.image_preimage_le W)).op s)) =
      N.presheaf.map k₂ ((N.restrict f₁).presheaf.map (homOfLE (g₁_image_le f₀ f₁ g₀ g₁ hg W)).op
        (ψ₁.app (f₁ ⁻¹ᵁ W) (M.presheaf.map (homOfLE (f₁.image_preimage_le W)).op s))) := by
    rw [restrict_map_apply, map_map]; rfl
  have hx : (M.restrict f₁).presheaf.map (homOfLE (g₁_image_le f₀ f₁ g₀ g₁ hg W)).op
      (M.presheaf.map (homOfLE (f₁.image_preimage_le W)).op s) = M.presheaf.map k₁ s := by
    rw [restrict_map_apply, map_map]; rfl
  refine lhs.trans ?_
  rw [← nat, hx]

include hψ in

theorem hψ_app (V : Y₀₁.Opens) (t : Γ(M, (g₀ ≫ f₀) ''ᵁ V))
    (e₁ : op ((g₀ ≫ f₀) ''ᵁ V) ⟶ op (f₀ ''ᵁ (g₀ ''ᵁ V)))
    (e₂ : op (f₀ ''ᵁ (g₀ ''ᵁ V)) ⟶ op ((g₀ ≫ f₀) ''ᵁ V))
    (e₃ : op ((g₀ ≫ f₀) ''ᵁ V) ⟶ op (f₁ ''ᵁ (g₁ ''ᵁ V)))
    (e₄ : op (f₁ ''ᵁ (g₁ ''ᵁ V)) ⟶ op ((g₀ ≫ f₀) ''ᵁ V)) :
    N.presheaf.map e₂ (ψ₀.app (g₀ ''ᵁ V) (M.presheaf.map e₁ t)) =
      N.presheaf.map e₄ (ψ₁.app (g₁ ''ᵁ V) (M.presheaf.map e₃ t)) := by
  have key := congrArg (fun T => Scheme.Modules.Hom.app T V (show Γ(M.restrict (g₀ ≫ f₀), V) from t)) hψ
  simp only [comp_app_apply] at key
  have key' : N.presheaf.map (eqToHom (image_comp_eq g₀ f₀ V)).op
      (ψ₀.app (g₀ ''ᵁ V) (M.presheaf.map (eqToHom (image_comp_eq g₀ f₀ V).symm).op t)) =
      N.presheaf.map (eqToHom (image_eq_of_eq hg V)).op (N.presheaf.map (eqToHom (image_comp_eq g₁ f₁ V)).op
        (ψ₁.app (g₁ ''ᵁ V) (M.presheaf.map (eqToHom (image_comp_eq g₁ f₁ V).symm).op
          (M.presheaf.map (eqToHom (image_eq_of_eq hg V).symm).op t)))) := key
  rw [map_map, map_map] at key'
  obtain rfl : e₁ = (eqToHom (image_comp_eq g₀ f₀ V).symm).op := op_hom_eq _ _
  obtain rfl : e₂ = (eqToHom (image_comp_eq g₀ f₀ V)).op := op_hom_eq _ _
  obtain rfl : e₃ = (eqToHom (image_eq_of_eq hg V).symm).op ≫ (eqToHom (image_comp_eq g₁ f₁ V).symm).op :=
    op_hom_eq _ _
  obtain rfl : e₄ = (eqToHom (image_comp_eq g₁ f₁ V)).op ≫ (eqToHom (image_eq_of_eq hg V)).op := op_hom_eq _ _
  exact key'

include hψ in
theorem u_comm : u₀ f₀ N ψ₀ ≫ a f₀ g₀ N = u₁ f₁ N ψ₁ ≫ b f₀ f₁ g₀ g₁ hg N := by
  apply Scheme.Modules.hom_ext; intro W; ext s
  have E0 : f₀ ''ᵁ (g₀ ''ᵁ ((g₀ ≫ f₀) ⁻¹ᵁ W)) = (g₀ ≫ f₀) ''ᵁ ((g₀ ≫ f₀) ⁻¹ᵁ W) :=
    (image_comp_eq g₀ f₀ _).symm
  have E1 : f₁ ''ᵁ (g₁ ''ᵁ ((g₀ ≫ f₀) ⁻¹ᵁ W)) = (g₀ ≫ f₀) ''ᵁ ((g₀ ≫ f₀) ⁻¹ᵁ W) := by
    rw [← image_comp_eq g₁ f₁, image_eq_of_eq hg]
  have h0 := u₀_a_apply f₀ g₀ N ψ₀ W s
    ((eqToHom E0 ≫ homOfLE ((g₀ ≫ f₀).image_preimage_le W)).op) (eqToHom E0.symm).op
  have h1 := u₁_b_apply f₀ f₁ g₀ g₁ hg N ψ₁ W s
    ((eqToHom E1 ≫ homOfLE ((g₀ ≫ f₀).image_preimage_le W)).op) (eqToHom E1.symm).op
  change (u₀ f₀ N ψ₀ ≫ a f₀ g₀ N).app W s = (u₁ f₁ N ψ₁ ≫ b f₀ f₁ g₀ g₁ hg N).app W s
  rw [h0, h1, op_comp, op_comp, ← map_map, ← map_map]
  exact hψ_app f₀ f₁ g₀ g₁ hg N ψ₀ ψ₁ hψ _ _ _ _ _ _

def v : M ⟶ G f₀ f₁ g₀ g₁ hg N :=
  lift (a f₀ g₀ N) (b f₀ f₁ g₀ g₁ hg N) (π₀ f₀ f₁ g₀ g₁ hg N) (π₁ f₀ f₁ g₀ g₁ hg N)
    (π_inj f₀ f₁ g₀ g₁ hg N) (π_lift f₀ f₁ g₀ g₁ hg N) (u₀ f₀ N ψ₀) (u₁ f₁ N ψ₁)
    (u_comm f₀ f₁ g₀ g₁ hg N ψ₀ ψ₁ hψ)

theorem v_π₀ : v f₀ f₁ g₀ g₁ hg N ψ₀ ψ₁ hψ ≫ π₀ f₀ f₁ g₀ g₁ hg N = u₀ f₀ N ψ₀ := lift_π₀ ..
theorem v_π₁ : v f₀ f₁ g₀ g₁ hg N ψ₀ ψ₁ hψ ≫ π₁ f₀ f₁ g₀ g₁ hg N = u₁ f₁ N ψ₁ := lift_π₁ ..

def φ : M ⟶ N :=
  haveI := isIso_can f₀ f₁ g₀ g₁ hg hov N hcov
  v f₀ f₁ g₀ g₁ hg N ψ₀ ψ₁ hψ ≫ inv (can f₀ f₁ g₀ g₁ hg N)

theorem φ_can : φ f₀ f₁ g₀ g₁ hg hov N hcov ψ₀ ψ₁ hψ ≫ can f₀ f₁ g₀ g₁ hg N = v f₀ f₁ g₀ g₁ hg N ψ₀ ψ₁ hψ := by
  haveI := isIso_can f₀ f₁ g₀ g₁ hg hov N hcov
  simp [φ]

theorem φ_η₀ : φ f₀ f₁ g₀ g₁ hg hov N hcov ψ₀ ψ₁ hψ ≫ η₀ f₀ N = u₀ f₀ N ψ₀ := by
  rw [← can_π₀ f₀ f₁ g₀ g₁ hg N, ← Category.assoc, φ_can, v_π₀]

theorem φ_η₁ : φ f₀ f₁ g₀ g₁ hg hov N hcov ψ₀ ψ₁ hψ ≫ η₁ f₁ N = u₁ f₁ N ψ₁ := by
  rw [← can_π₁ f₀ f₁ g₀ g₁ hg N, ← Category.assoc, φ_can, v_π₁]

theorem restrict_φ₀ : (restrictFunctor f₀).map (φ f₀ f₁ g₀ g₁ hg hov N hcov ψ₀ ψ₁ hψ) = ψ₀ := by
  apply Scheme.Modules.hom_ext; intro V; ext x
  rw [restrict_app_apply]
  have key := congrArg (fun T => Scheme.Modules.Hom.app T (f₀ ''ᵁ V) (show Γ(M, f₀ ''ᵁ V) from x))
    (φ_η₀ f₀ f₁ g₀ g₁ hg hov N hcov ψ₀ ψ₁ hψ)
  have key' : N.presheaf.map (homOfLE (f₀.image_preimage_le (f₀ ''ᵁ V))).op
      ((φ f₀ f₁ g₀ g₁ hg hov N hcov ψ₀ ψ₁ hψ).app (f₀ ''ᵁ V) x) =
      ψ₀.app (f₀ ⁻¹ᵁ (f₀ ''ᵁ V)) (M.presheaf.map (homOfLE (f₀.image_preimage_le (f₀ ''ᵁ V))).op x) := key
  have hV : f₀ ⁻¹ᵁ (f₀ ''ᵁ V) = V := f₀.preimage_image_eq V
  have nat := app_naturality ψ₀ (homOfLE hV.ge).op
    (M.presheaf.map (homOfLE (f₀.image_preimage_le (f₀ ''ᵁ V))).op x)
  have hx : (M.restrict f₀).presheaf.map (homOfLE hV.ge).op
      (M.presheaf.map (homOfLE (f₀.image_preimage_le (f₀ ''ᵁ V))).op x) = x := by
    rw [restrict_map_apply, map_map]; exact map_endo M _ x
  have hy : ∀ y : Γ(N, f₀ ''ᵁ V), (N.restrict f₀).presheaf.map (homOfLE hV.ge).op
      (N.presheaf.map (homOfLE (f₀.image_preimage_le (f₀ ''ᵁ V))).op y) = y := fun y => by
    rw [restrict_map_apply, map_map]; exact map_endo N _ y
  rw [hx, ← key', hy] at nat
  exact nat.symm

theorem restrict_φ₁ : (restrictFunctor f₁).map (φ f₀ f₁ g₀ g₁ hg hov N hcov ψ₀ ψ₁ hψ) = ψ₁ := by
  apply Scheme.Modules.hom_ext; intro V; ext x
  rw [restrict_app_apply]
  have key := congrArg (fun T => Scheme.Modules.Hom.app T (f₁ ''ᵁ V) (show Γ(M, f₁ ''ᵁ V) from x))
    (φ_η₁ f₀ f₁ g₀ g₁ hg hov N hcov ψ₀ ψ₁ hψ)
  have key' : N.presheaf.map (homOfLE (f₁.image_preimage_le (f₁ ''ᵁ V))).op
      ((φ f₀ f₁ g₀ g₁ hg hov N hcov ψ₀ ψ₁ hψ).app (f₁ ''ᵁ V) x) =
      ψ₁.app (f₁ ⁻¹ᵁ (f₁ ''ᵁ V)) (M.presheaf.map (homOfLE (f₁.image_preimage_le (f₁ ''ᵁ V))).op x) := key
  have hV : f₁ ⁻¹ᵁ (f₁ ''ᵁ V) = V := f₁.preimage_image_eq V
  have nat := app_naturality ψ₁ (homOfLE hV.ge).op
    (M.presheaf.map (homOfLE (f₁.image_preimage_le (f₁ ''ᵁ V))).op x)
  have hx : (M.restrict f₁).presheaf.map (homOfLE hV.ge).op
      (M.presheaf.map (homOfLE (f₁.image_preimage_le (f₁ ''ᵁ V))).op x) = x := by
    rw [restrict_map_apply, map_map]; exact map_endo M _ x
  have hy : ∀ y : Γ(N, f₁ ''ᵁ V), (N.restrict f₁).presheaf.map (homOfLE hV.ge).op
      (N.presheaf.map (homOfLE (f₁.image_preimage_le (f₁ ''ᵁ V))).op y) = y := fun y => by
    rw [restrict_map_apply, map_map]; exact map_endo N _ y
  rw [hx, ← key', hy] at nat
  exact nat.symm

end Glue

end AlgebraicGeometry.Scheme.Modules.GlueHom

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_restrict_eq_of_isOpenImmersion.AlgebraicGeometry Opposite TopologicalSpace"

open AlgebraicGeometry.Scheme.Modules.GlueHom in
theorem solution
    {X Y₀ Y₁ Y₀₁ : Scheme.{u}} (f₀ : Y₀ ⟶ X) (f₁ : Y₁ ⟶ X) [IsOpenImmersion f₀] [IsOpenImmersion f₁]
    (g₀ : Y₀₁ ⟶ Y₀) (g₁ : Y₀₁ ⟶ Y₁) [IsOpenImmersion g₀] [IsOpenImmersion g₁]
    (hg : g₀ ≫ f₀ = g₁ ≫ f₁) (hcov : f₀.opensRange ⊔ f₁.opensRange = ⊤)
    (hov : f₀.opensRange ⊓ f₁.opensRange ≤ (g₀ ≫ f₀).opensRange)
    {M N : X.Modules} (ψ₀ : M.restrict f₀ ⟶ N.restrict f₀) (ψ₁ : M.restrict f₁ ⟶ N.restrict f₁)
    (hψ : (Scheme.Modules.restrictFunctorComp g₀ f₀).hom.app M ≫ (Scheme.Modules.restrictFunctor g₀).map ψ₀ ≫
            (Scheme.Modules.restrictFunctorComp g₀ f₀).inv.app N =
          (Scheme.Modules.restrictFunctorCongr hg).hom.app M ≫
            (Scheme.Modules.restrictFunctorComp g₁ f₁).hom.app M ≫ (Scheme.Modules.restrictFunctor g₁).map ψ₁ ≫
            (Scheme.Modules.restrictFunctorComp g₁ f₁).inv.app N ≫ (Scheme.Modules.restrictFunctorCongr hg).inv.app N) :
    ∃ φ : M ⟶ N, (Scheme.Modules.restrictFunctor f₀).map φ = ψ₀ ∧ (Scheme.Modules.restrictFunctor f₁).map φ = ψ₁ :=
  ⟨φ f₀ f₁ g₀ g₁ hg hov N hcov ψ₀ ψ₁ hψ, restrict_φ₀ .., restrict_φ₁ ..⟩

end
end S_AlgebraicGeometry_Scheme_Modules_exists_hom_restrict_eq_of_isOpenImmersion
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_restrict_eq_of_isOpenImmersion (solution)
