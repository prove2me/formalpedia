-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a33ef7d5-fdee-5f60-9fd8-50c5bf0b35a6

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit.AlgebraicGeometry TopologicalSpace Opposite"

universe u

namespace DirLimSpread

section Ring

variable {κ : Type u} [Preorder κ]
  {G : κ → Type u} [∀ j, CommRing (G j)] (φ : ∀ j k : κ, j ≤ k → G j →+* G k)
  [DirectedSystem G fun j k h => ⇑(φ j k h)]
  {R : Type u} [CommRing R] (g : ∀ j, G j →+* R)

theorem φ_self (j : κ) : φ j j le_rfl = RingHom.id (G j) :=
  RingHom.ext fun x => DirectedSystem.map_self (f := fun j k h => ⇑(φ j k h)) x

theorem φ_comp {j k l : κ} (hjk : j ≤ k) (hkl : k ≤ l) : (φ k l hkl).comp (φ j k hjk) = φ j l (hjk.trans hkl) :=
  RingHom.ext fun x => DirectedSystem.map_map (f := fun j k h => ⇑(φ j k h)) hjk hkl x

@[simps]
def ringDiag : κ ⥤ CommRingCat.{u} where
  obj j := CommRingCat.of (G j)
  map {j k} h := CommRingCat.ofHom (φ j k (leOfHom h))
  map_id j := by rw [← CommRingCat.ofHom_id]; congr 1; exact φ_self φ j
  map_comp {j k l} h h' := by rw [← CommRingCat.ofHom_comp]; congr 1; exact (φ_comp φ _ _).symm

@[simps]
def ringCocone (hRc : ∀ i j hij x, g j (φ i j hij x) = g i x) : Cocone (ringDiag φ) where
  pt := CommRingCat.of R
  ι := { app := fun j => CommRingCat.ofHom (g j)
         naturality := fun {j k} h => by
           apply CommRingCat.hom_ext; ext x
           have h__af := hRc j k (leOfHom h) x
           simp at h__af ⊢
           exact h__af }

noncomputable def specDiag : κᵒᵖ ⥤ Scheme.{u} := (ringDiag φ).op ⋙ Scheme.Spec

theorem specDiag_obj (j : κᵒᵖ) : (specDiag φ).obj j = Spec (CommRingCat.of (G j.unop)) := rfl

theorem specDiag_map {j k : κᵒᵖ} (h : j ⟶ k) :
    (specDiag φ).map h = Spec.map (CommRingCat.ofHom (φ k.unop j.unop (leOfHom h.unop))) := rfl

scoped instance isAffine_specDiag_obj (j : κᵒᵖ) : IsAffine ((specDiag φ).obj j) := (inferInstance : IsAffine (Spec _))

scoped instance isAffineHom_specDiag_map {j k : κᵒᵖ} (h : j ⟶ k) : IsAffineHom ((specDiag φ).map h) :=
  (inferInstance : IsAffineHom (Spec.map _))

variable [Nonempty κ] [IsDirectedOrder κ] (hR : IsDirectLimit (fun j k h => ⇑(φ j k h)) fun j => ⇑(g j))

noncomputable def isColimitRingCocone : IsColimit (ringCocone φ g hR.compatibility) := by
  have hT : IsColimit ((forget CommRingCat.{u}).mapCocone (ringCocone φ g hR.compatibility)) := by
    refine Types.FilteredColimit.isColimitOf _ _ (fun x => ?_) (fun j k xj xk h => ?_)
    · obtain ⟨j, xj, hx⟩ := hR.surj x
      exact ⟨j, xj, by have h__af := hx.symm; simp at h__af ⊢; exact h__af⟩
    · have h' : g j xj = g k xk := by simp at h; exact h
      obtain ⟨l, hjl, hkl, e⟩ := hR.inj j k xj xk h'
      exact ⟨l, homOfLE hjl, homOfLE hkl, by simp at e ⊢; exact e⟩
  haveI : ReflectsColimit (ringDiag φ) (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  exact isColimitOfReflects (forget CommRingCat.{u}) hT

noncomputable def specCone : Cone (specDiag φ) := Scheme.Spec.mapCone (ringCocone φ g hR.compatibility).op

theorem specCone_pt : (specCone φ g hR).pt = Spec (CommRingCat.of R) := rfl

theorem specCone_π (j : κᵒᵖ) : (specCone φ g hR).π.app j = Spec.map (CommRingCat.ofHom (g j.unop)) := rfl

noncomputable def isLimitSpecCone : IsLimit (specCone φ g hR) :=
  haveI : PreservesLimitsOfSize.{u, u} Scheme.Spec.{u} := ΓSpec.adjunction.rightAdjoint_preservesLimits
  isLimitOfPreserves Scheme.Spec (isColimitRingCocone φ g hR).op

end Ring

section BaseChange

variable {κ : Type u} [Preorder κ]
  {G : κ → Type u} [∀ j, CommRing (G j)] (φ : ∀ j k : κ, j ≤ k → G j →+* G k)
  {R : Type u} [CommRing R] (g : ∀ j, G j →+* R)

noncomputable abbrev sφ {j k : κ} (h : j ≤ k) : Spec (CommRingCat.of (G k)) ⟶ Spec (CommRingCat.of (G j)) :=
  Spec.map (CommRingCat.ofHom (φ j k h))

noncomputable abbrev sg (j : κ) : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (G j)) :=
  Spec.map (CommRingCat.ofHom (g j))

theorem sφ_irrel {j k : κ} (h h' : j ≤ k) : sφ φ h = sφ φ h' := rfl

theorem sg_comp (hRc : ∀ i j hij x, g j (φ i j hij x) = g i x) {j k : κ} (hjk : j ≤ k) :
    sg g k ≫ sφ φ hjk = sg g j := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun x => hRc j k hjk x

variable [DirectedSystem G fun j k h => ⇑(φ j k h)]

theorem sφ_comp {j k l : κ} (hjk : j ≤ k) (hkl : k ≤ l) : sφ φ hkl ≫ sφ φ hjk = sφ φ (hjk.trans hkl) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, φ_comp φ hjk hkl]

theorem sφ_self (j : κ) : sφ φ (le_refl j) = 𝟙 _ := by
  rw [← Spec.map_id]
  change Spec.map (CommRingCat.ofHom (φ _ _ le_rfl)) = _
  rw [φ_self φ]
  rfl

variable (b : κ) (hb : ∀ j, b ≤ j) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G b)))

noncomputable def D : κᵒᵖ ⥤ Scheme.{u} where
  obj j := pullback fX (sφ φ (hb j.unop))
  map {j k} f := pullback.map fX (sφ φ (hb j.unop)) fX (sφ φ (hb k.unop)) (𝟙 X) (sφ φ (leOfHom f.unop)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, sφ_comp])
  map_id j := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.id_comp, Category.comp_id]
    · rw [pullback.lift_snd, Category.id_comp]
      convert Category.comp_id _
      exact sφ_self φ _
  map_comp {j k l} f f' := by
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, Category.assoc, Category.comp_id]
    · simp only [pullback.lift_snd, Category.assoc, pullback.lift_snd_assoc]
      rw [sφ_comp]

noncomputable def t : D φ b hb fX ⟶ (Functor.const _).obj (Spec (CommRingCat.of (G b))) where
  app j := pullback.fst fX (sφ φ (hb j.unop)) ≫ fX
  naturality {j k} f := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, D]
    rw [← Category.assoc, pullback.lift_fst, Category.comp_id]

theorem D_obj (j : κᵒᵖ) : (D φ b hb fX).obj j = pullback fX (sφ φ (hb j.unop)) := rfl

theorem D_map_fst {j k : κᵒᵖ} (f : j ⟶ k) :
    (D φ b hb fX).map f ≫ pullback.fst fX (sφ φ (hb k.unop)) = pullback.fst fX (sφ φ (hb j.unop)) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem D_map_snd {j k : κᵒᵖ} (f : j ⟶ k) :
    (D φ b hb fX).map f ≫ pullback.snd fX (sφ φ (hb k.unop)) =
      pullback.snd fX (sφ φ (hb j.unop)) ≫ sφ φ (leOfHom f.unop) :=
  pullback.lift_snd _ _ _

theorem t_app (j : κᵒᵖ) : (t φ b hb fX).app j = pullback.fst fX (sφ φ (hb j.unop)) ≫ fX := rfl

theorem isPullback_D_map {j k : κᵒᵖ} (f : j ⟶ k) :
    IsPullback ((D φ b hb fX).map f) (pullback.snd fX (sφ φ (hb j.unop))) (pullback.snd fX (sφ φ (hb k.unop)))
      (sφ φ (leOfHom f.unop)) :=
  IsPullback.of_right (by have h__af := (IsPullback.of_hasPullback fX (sφ φ (hb j.unop))); simp only [D_map_fst, sφ_comp] at h__af ⊢; exact h__af)
    (D_map_snd φ b hb fX f) (IsPullback.of_hasPullback _ _)

scoped instance isAffineHom_D_map {j k : κᵒᵖ} (f : j ⟶ k) : IsAffineHom ((D φ b hb fX).map f) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_D_map φ b hb fX f).flip inferInstance

scoped instance compactSpace_pullback_sφ [CompactSpace X] (j : κ) : CompactSpace ↥(pullback fX (sφ φ (hb j))) := by
  haveI : IsAffineHom (sφ φ (hb j)) := inferInstance
  haveI : QuasiCompact (sφ φ (hb j)) := inferInstance
  infer_instance

scoped instance compactSpace_D_obj [CompactSpace X] (j : κᵒᵖ) : CompactSpace ((D φ b hb fX).obj j) :=
  compactSpace_pullback_sφ φ b hb fX j.unop

scoped instance quasiSeparatedSpace_pullback_sφ [QuasiSeparatedSpace X] (j : κ) :
    QuasiSeparatedSpace ↥(pullback fX (sφ φ (hb j))) := by
  haveI : QuasiSeparated (pullback.fst fX (sφ φ (hb j))) := inferInstance
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst fX (sφ φ (hb j)))

scoped instance quasiSeparatedSpace_D_obj [QuasiSeparatedSpace X] (j : κᵒᵖ) : QuasiSeparatedSpace ((D φ b hb fX).obj j) :=
  quasiSeparatedSpace_pullback_sφ φ b hb fX j.unop

noncomputable def α : D φ b hb fX ⟶ specDiag φ where
  app j := pullback.snd fX (sφ φ (hb j.unop))
  naturality {j k} f := D_map_snd φ b hb fX f

section Cone

variable (hRc : ∀ i j hij x, g j (φ i j hij x) = g i x)

noncomputable def c : Cone (D φ b hb fX) where
  pt := pullback fX (sg g b)
  π :=
    { app := fun j => pullback.map fX (sg g b) fX (sφ φ (hb j.unop)) (𝟙 X) (sg g j.unop) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, sg_comp φ g hRc])
      naturality := by
        intro j k f
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, D]
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
        · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
          rw [sg_comp φ g hRc] }

theorem c_pt : (c φ g b hb fX hRc).pt = pullback fX (sg g b) := rfl

theorem c_π_fst (j : κᵒᵖ) :
    (c φ g b hb fX hRc).π.app j ≫ pullback.fst fX (sφ φ (hb j.unop)) = pullback.fst fX (sg g b) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem c_π_snd (j : κᵒᵖ) :
    (c φ g b hb fX hRc).π.app j ≫ pullback.snd fX (sφ φ (hb j.unop)) = pullback.snd fX (sg g b) ≫ sg g j.unop :=
  pullback.lift_snd _ _ _

theorem isPullback_c_π (j : κᵒᵖ) :
    IsPullback ((c φ g b hb fX hRc).π.app j) (pullback.snd fX (sg g b)) (pullback.snd fX (sφ φ (hb j.unop)))
      (sg g j.unop) :=
  IsPullback.of_right (by have h__af := (IsPullback.of_hasPullback fX (sg g b)); simp only [c_π_fst, sg_comp φ g hRc] at h__af ⊢; exact h__af)
    (c_π_snd φ g b hb fX hRc j) (IsPullback.of_hasPullback _ _)

end Cone

variable [Nonempty κ] [IsDirectedOrder κ] (hR : IsDirectLimit (fun j k h => ⇑(φ j k h)) fun j => ⇑(g j))

noncomputable def isLimitCone : IsLimit (c φ g b hb fX hR.compatibility) :=
  haveI : IsConnected κᵒᵖ := by
    haveI : IsConnected κ := IsFiltered.isConnected κ
    infer_instance
  isLimitOfIsPullbackOfIsConnected (α φ b hb fX) _ (specCone φ g hR)
    { hom := pullback.snd fX (sg g b)
      w := fun j => (c_π_snd φ g b hb fX hR.compatibility j).symm }
    (fun j => isPullback_c_π φ g b hb fX hR.compatibility j) (isLimitSpecCone φ g hR)

end BaseChange

section API

variable {κ : Type u} [Preorder κ]
  {G : κ → Type u} [∀ j, CommRing (G j)] {φ : ∀ j k : κ, j ≤ k → G j →+* G k}
  [DirectedSystem G fun j k h => ⇑(φ j k h)]
  {R : Type u} [CommRing R] {g : ∀ j, G j →+* R}
  {b : κ} {hb : ∀ j, b ≤ j} {X : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of (G b))}
  {hRc : ∀ i j hij x, g j (φ i j hij x) = g i x}

noncomputable def proj (φ : ∀ j k : κ, j ≤ k → G j →+* G k) [DirectedSystem G fun j k h => ⇑(φ j k h)]
    (g : ∀ j, G j →+* R) (hb : ∀ j, b ≤ j)
    (fX : X ⟶ Spec (CommRingCat.of (G b))) (hRc : ∀ i j hij x, g j (φ i j hij x) = g i x) (j : κ) :
    pullback fX (sg g b) ⟶ (D φ b hb fX).obj (op j) :=
  (c φ g b hb fX hRc).π.app (op j)

noncomputable def fstL (φ : ∀ j k : κ, j ≤ k → G j →+* G k) [DirectedSystem G fun j k h => ⇑(φ j k h)]
    (hb : ∀ j, b ≤ j) (fX : X ⟶ Spec (CommRingCat.of (G b))) (j : κ) : (D φ b hb fX).obj (op j) ⟶ X :=
  pullback.fst fX (sφ φ (hb j))

noncomputable def sndL (φ : ∀ j k : κ, j ≤ k → G j →+* G k) [DirectedSystem G fun j k h => ⇑(φ j k h)]
    (hb : ∀ j, b ≤ j) (fX : X ⟶ Spec (CommRingCat.of (G b))) (j : κ) :
    (D φ b hb fX).obj (op j) ⟶ Spec (CommRingCat.of (G j)) :=
  pullback.snd fX (sφ φ (hb j))

theorem proj_def (j : κ) : (c φ g b hb fX hRc).π.app (op j) = proj φ g hb fX hRc j := rfl
theorem fstL_def (j : κ) : pullback.fst fX (sφ φ (hb j)) = fstL φ hb fX j := rfl
theorem sndL_def (j : κ) : pullback.snd fX (sφ φ (hb j)) = sndL φ hb fX j := rfl
theorem t_appL (j : κ) : (t φ b hb fX).app (op j) = fstL φ hb fX j ≫ fX := rfl

theorem hom_extL {j : κ} {W : Scheme.{u}} {a a' : W ⟶ (D φ b hb fX).obj (op j)}
    (h₁ : a ≫ fstL φ hb fX j = a' ≫ fstL φ hb fX j) (h₂ : a ≫ sndL φ hb fX j = a' ≫ sndL φ hb fX j) : a = a' :=
  pullback.hom_ext h₁ h₂

theorem conditionL (j : κ) : fstL φ hb fX j ≫ fX = sndL φ hb fX j ≫ sφ φ (hb j) := pullback.condition

noncomputable def liftL (φ : ∀ j k : κ, j ≤ k → G j →+* G k) [DirectedSystem G fun j k h => ⇑(φ j k h)]
    (hb : ∀ j, b ≤ j) (fX : X ⟶ Spec (CommRingCat.of (G b))) (j : κ) {W : Scheme.{u}} (a : W ⟶ X)
    (a' : W ⟶ Spec (CommRingCat.of (G j))) (w : a ≫ fX = a' ≫ sφ φ (hb j)) : W ⟶ (D φ b hb fX).obj (op j) :=
  pullback.lift a a' w

theorem liftL_fstL (j : κ) {W : Scheme.{u}} (a : W ⟶ X) (a' : W ⟶ Spec (CommRingCat.of (G j)))
    (w : a ≫ fX = a' ≫ sφ φ (hb j)) : liftL φ hb fX j a a' w ≫ fstL φ hb fX j = a :=
  pullback.lift_fst _ _ _

theorem liftL_sndL (j : κ) {W : Scheme.{u}} (a : W ⟶ X) (a' : W ⟶ Spec (CommRingCat.of (G j)))
    (w : a ≫ fX = a' ≫ sφ φ (hb j)) : liftL φ hb fX j a a' w ≫ sndL φ hb fX j = a' :=
  pullback.lift_snd _ _ _

theorem D_map_eq {j j' : κ} (f f' : (op j' : κᵒᵖ) ⟶ op j) : (D φ b hb fX).map f = (D φ b hb fX).map f' := by
  rw [Subsingleton.elim f f']

theorem D_map_fstL {j j' : κ} (f : (op j' : κᵒᵖ) ⟶ op j) : (D φ b hb fX).map f ≫ fstL φ hb fX j = fstL φ hb fX j' :=
  D_map_fst φ b hb fX f

theorem D_map_sndL {j j' : κ} (f : (op j' : κᵒᵖ) ⟶ op j) :
    (D φ b hb fX).map f ≫ sndL φ hb fX j = sndL φ hb fX j' ≫ sφ φ (leOfHom f.unop) :=
  D_map_snd φ b hb fX f

theorem D_map_map {j j' j'' : κ} (f : (op j' : κᵒᵖ) ⟶ op j) (f' : (op j'' : κᵒᵖ) ⟶ op j') (f'' : (op j'' : κᵒᵖ) ⟶ op j) :
    (D φ b hb fX).map f' ≫ (D φ b hb fX).map f = (D φ b hb fX).map f'' := by
  rw [← Functor.map_comp, Subsingleton.elim (f' ≫ f) f'']

theorem proj_map {j j' : κ} (f : (op j' : κᵒᵖ) ⟶ op j) : proj φ g hb fX hRc j' ≫ (D φ b hb fX).map f = proj φ g hb fX hRc j :=
  (c φ g b hb fX hRc).w f

theorem proj_fstL (j : κ) : proj φ g hb fX hRc j ≫ fstL φ hb fX j = pullback.fst fX (sg g b) := c_π_fst φ g b hb fX hRc _

theorem proj_sndL (j : κ) : proj φ g hb fX hRc j ≫ sndL φ hb fX j = pullback.snd fX (sg g b) ≫ sg g j :=
  c_π_snd φ g b hb fX hRc _

def homOp {j j' : κ} (h : j ≤ j') : (op j' : κᵒᵖ) ⟶ op j := (homOfLE h).op

end API

section Core

variable {κ : Type u} [Preorder κ] [Nonempty κ] [IsDirectedOrder κ]
  {G : κ → Type u} [∀ j, CommRing (G j)] (φ : ∀ j k : κ, j ≤ k → G j →+* G k)
  [DirectedSystem G fun j k h => ⇑(φ j k h)]
  {R : Type u} [CommRing R] (g : ∀ j, G j →+* R)
  (hR : IsDirectLimit (fun j k h => ⇑(φ j k h)) fun j => ⇑(g j))
  (b : κ) (hb : ∀ j, b ≤ j)

include hR in

theorem exists_open_core {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G b)))
    (U : (pullback fX (sg g b)).Opens) (hU : IsCompact (U : Set ↥(pullback fX (sg g b)))) :
    ∃ (j : κ) (V : ((D φ b hb fX).obj (op j)).Opens),
      IsCompact (V : Set ↥((D φ b hb fX).obj (op j))) ∧ proj φ g hb fX hR.compatibility j ⁻¹ᵁ V = U := by
  obtain ⟨j, V, hV, e⟩ := exists_preimage_eq (D φ b hb fX) (c φ g b hb fX hR.compatibility) (isLimitCone φ g b hb fX hR) U hU
  obtain ⟨j⟩ := j
  exact ⟨j, V, hV, e⟩

end Core

section Reindex

variable {ι : Type u} [Preorder ι]
  {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
  {R : Type u} [CommRing R] (g : ∀ i, G i →+* R) (i : ι)

abbrev J (i : ι) : Type u := {j : ι // i ≤ j}

abbrev φ' (j k : J i) (h : j ≤ k) : G j.1 →+* G k.1 := φ j.1 k.1 h

abbrev g' (j : J i) : G j.1 →+* R := g j.1

abbrev bot : J i := ⟨i, le_rfl⟩

theorem bot_le (j : J i) : bot i ≤ j := j.2

scoped instance directedSystem' [DirectedSystem G fun i j h => ⇑(φ i j h)] :
    DirectedSystem (fun j : J i => G j.1) fun j k h => ⇑(φ' φ i j k h) where
  map_self := fun j x => DirectedSystem.map_self (f := fun i j h => ⇑(φ i j h)) x
  map_map := fun _ _ _ hjk hkl x => DirectedSystem.map_map (f := fun i j h => ⇑(φ i j h)) hjk hkl x

scoped instance nonempty' : Nonempty (J i) := ⟨bot i⟩

scoped instance isDirectedOrder' [IsDirectedOrder ι] : IsDirectedOrder (J i) :=
  ⟨fun j k => by
    obtain ⟨m, hjm, hkm⟩ := exists_ge_ge j.1 k.1
    exact ⟨⟨m, j.2.trans hjm⟩, hjm, hkm⟩⟩

theorem isDirectLimit' [DirectedSystem G fun i j h => ⇑(φ i j h)] [IsDirectedOrder ι]
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i)) :
    IsDirectLimit (fun j k h => ⇑(φ' φ i j k h)) fun j => ⇑(g' g i j) where
  surj x := by
    obtain ⟨l, xl, hx⟩ := hR.surj x
    obtain ⟨m, him, hlm⟩ := exists_ge_ge i l
    exact ⟨⟨m, him⟩, φ l m hlm xl, (hR.compatibility l m hlm xl).trans hx⟩
  inj j k xj xk h := by
    obtain ⟨m, hjm, hkm, e⟩ := hR.inj j.1 k.1 xj xk h
    exact ⟨⟨m, j.2.trans hjm⟩, hjm, hkm, e⟩
  compatibility j k h x := hR.compatibility j.1 k.1 h x

end Reindex

end DirLimSpread
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit.DirLimSpread"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective quasiSeparatedSpace_of_quasiSeparated Scheme.exists_isOpenCover_and_isAffine QuasiCompact IsAffine Spec Spec.map Scheme QuasiCompact.compactSpace_of_compactSpace ΓSpec.adjunction Spec.map_id Scheme.Spec IsAffineOpen Scheme.Modules QuasiSeparated exists_preimage_eq IsAffineHom Scheme.Modules.IsFrameOn Scheme.Modules.IsInvertible" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "forget exists_isOpenCover_and_isAffine mk Γ isBasis_affineOpens Modules Opens Modules.IsFrameOn Modules.IsInvertible" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext pullback presheaf IsFrameOn IsInvertible IsInvertible.exists_isFrameOn" end AlgebraicGeometry.Scheme.Modules
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in
theorem AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_congr {Y : Scheme.{u}} {M : Y.Modules}
    {U U' : Y.Opens} (h : U = U') (hU : ∃ s : Γ(M, U), Scheme.Modules.IsFrameOn s U) :
    ∃ s : Γ(M, U'), Scheme.Modules.IsFrameOn s U' := by
  subst h
  exact hU

open DirLimSpread in

theorem solution
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    (𝓛 : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))).Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    ∃ (j : ι) (hij : i ≤ j) (n : ℕ) (W : ULift.{u} (Fin n) → (Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))).Opens),
      (∀ k, IsAffineOpen (W k)) ∧
      ∀ (c : Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i))) ⟶ Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))),
        c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i))) →
        c ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (g i))) ≫ Spec.map (CommRingCat.ofHom (g j)) →
        (⨆ k, c ⁻¹ᵁ W k) = ⊤ ∧
        ∃ s : ∀ k, Γ(𝓛, c ⁻¹ᵁ W k), ∀ k, Scheme.Modules.IsFrameOn (s k) (c ⁻¹ᵁ W k) := by
  classical
  haveI : IsDirectedOrder ι := ‹IsDirected ι (· ≤ ·)›
  have hR' := isDirectLimit' φ g i hR
  haveI : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace fX
  haveI : QuasiSeparatedSpace ↥X := quasiSeparatedSpace_of_quasiSeparated fX

  have hc := isLimitCone (φ' φ i) (g' g i) (bot i) (bot_le i) fX hR'

  let XR : Scheme.{u} := Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))
  let Jt : Type u := {A : XR.Opens // IsAffineOpen A ∧ ∃ s : Γ(𝓛, A), Scheme.Modules.IsFrameOn s A}
  have hcov : IsOpenCover (fun A : Jt => (A.1 : XR.Opens)) := by
    refine IsOpenCover.mk (top_le_iff.mp fun x _ => ?_)
    obtain ⟨U, s, hxU, hs⟩ := h𝓛.exists_isFrameOn x
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAU⟩ := XR.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
    have hsA : Scheme.Modules.IsFrameOn (𝓛.presheaf.map (homOfLE hAU).op s) A := (hs.map (homOfLE hAU)).mono hAU
    exact Opens.mem_iSup.mpr ⟨⟨A, hA, _, hsA⟩, hxA⟩
  obtain ⟨jo, S, V, hV, hVU⟩ :=
    Scheme.exists_isOpenCover_and_isAffine (D (φ' φ i) (bot i) (bot_le i) fX)
      (DirLimSpread.c (φ' φ i) (g' g i) (bot i) (bot_le i) fX hR'.compatibility) hc
      (fun A : Jt => (A.1 : XR.Opens)) hcov (fun A => A.2.1)
  obtain ⟨j⟩ := jo

  let e : ULift.{u} (Fin S.card) → ↥S := fun k => S.equivFin.symm k.down
  have he : Function.Surjective e := fun A => ⟨ULift.up (S.equivFin A), by simp [e]⟩
  refine ⟨j.1, j.2, S.card, fun k => V (e k), fun k => (hVU (e k)).1, fun cX hX₁ hX₂ => ?_⟩
  have ecX : cX = proj (φ' φ i) (g' g i) (bot_le i) fX hR'.compatibility j := by
    apply pullback.hom_ext
    · rw [hX₁]
      exact (proj_fstL (φ := φ' φ i) (g := g' g i) (hb := bot_le i) (fX := fX) (hRc := hR'.compatibility) j).symm
    · rw [hX₂]
      exact (proj_sndL (φ := φ' φ i) (g := g' g i) (hb := bot_le i) (fX := fX) (hRc := hR'.compatibility) j).symm

  have hpre : ∀ k, cX ⁻¹ᵁ V (e k) = (e k).1.1 := fun k => by
    rw [ecX]
    exact ((hVU (e k)).2).symm
  refine ⟨?_, ?_⟩
  ·
    refine top_le_iff.mp fun x _ => ?_
    have hx : cX.base x ∈ (⨆ A : ↥S, V A) := by
      rw [hV.iSup_eq_top]
      exact trivial
    obtain ⟨A, hA⟩ := Opens.mem_iSup.mp hx
    obtain ⟨k, rfl⟩ := he A
    exact Opens.mem_iSup.mpr ⟨k, show x ∈ cX ⁻¹ᵁ V (e k) from hA⟩
  ·
    have hex : ∀ k, ∃ s : Γ(𝓛, cX ⁻¹ᵁ V (e k)), Scheme.Modules.IsFrameOn s (cX ⁻¹ᵁ V (e k)) := fun k =>
      Scheme.Modules.exists_isFrameOn_congr (hpre k).symm (e k).1.2.2
    exact ⟨fun k => (hex k).choose, fun k => (hex k).choose_spec⟩

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit (solution)
