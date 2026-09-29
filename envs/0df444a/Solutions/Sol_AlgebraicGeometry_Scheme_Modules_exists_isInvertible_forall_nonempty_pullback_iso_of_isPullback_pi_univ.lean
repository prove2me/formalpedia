-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_isInvertible_forall_nonempty_pullback_iso_of_isPullback_pi_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/31cdc4e3-2473-558f-ab0b-846a917e9bda

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_of_forall_pullback_iso_of_isOpenImmersion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_forall_nonempty_pullback_iso_of_isPullback_pi_univ

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u

open TopologicalSpace Opposite

namespace PiSpecCover

variable {k : ℕ} (C : Fin k → Type u) [∀ i, CommRing (C i)]

noncomputable def θ : (∀ i, C i) ≃+* (∀ j : ULift.{u} (Fin k), C j.down) :=
  RingEquiv.piCongrLeft' C Equiv.ulift.symm

theorem eval_comp_θ (i : Fin k) :
    (Pi.evalRingHom (fun j : ULift.{u} (Fin k) => C j.down) (ULift.up i)).comp (θ C).toRingHom = Pi.evalRingHom C i := by
  ext f; rfl

theorem specMap_eval (i : Fin k) :
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)) =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun j : ULift.{u} (Fin k) => C j.down) (ULift.up i))) ≫
        Spec.map (CommRingCat.ofHom (θ C).toRingHom) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, eval_comp_θ]

scoped instance : IsIso (Spec.map (CommRingCat.ofHom (θ C).toRingHom)) := by
  change IsIso (Scheme.Spec.map (Quiver.Hom.op (θ C).toCommRingCatIso.hom))
  infer_instance

theorem exists_eval_eq (s : ↥(Spec (CommRingCat.of (∀ i, C i)))) :
    ∃ (i : Fin k) (y : ↥(Spec (CommRingCat.of (C i)))), Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)) y = s := by
  let Rf : ULift.{u} (Fin k) → CommRingCat.{u} := fun j => CommRingCat.of (C j.down)
  let Θ := Spec.map (CommRingCat.ofHom (θ C).toRingHom)
  obtain ⟨⟨j, y⟩, hy⟩ := (sigmaMk (fun j => Spec (Rf j))).surjective (inv (sigmaSpec Rf) (inv Θ s))
  refine ⟨j.down, y, ?_⟩
  rw [sigmaMk_mk] at hy
  have e := congrArg (fun φ => φ y) (ι_sigmaSpec Rf j)
  simp only [Scheme.Hom.comp_apply] at e
  rw [specMap_eval, Scheme.Hom.comp_apply]
  change Θ ((Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun j => ↑(Rf j)) j))) y) = s
  have h1 : ∀ x, (sigmaSpec Rf) ((inv (sigmaSpec Rf)) x) = x := fun x => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  have h2 : ∀ x, Θ ((inv Θ) x) = x := fun x => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  rw [← e, hy]
  change Θ ((sigmaSpec Rf) ((inv (sigmaSpec Rf)) ((inv Θ) s))) = s
  rw [h1, h2]

theorem isEmpty_of_comp_eval_eq {i₁ i₂ : Fin k} (h : i₁ ≠ i₂) {Z : Scheme.{u}}
    (a : Z ⟶ Spec (CommRingCat.of (C i₁))) (b : Z ⟶ Spec (CommRingCat.of (C i₂)))
    (hab : a ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i₁)) = b ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i₂))) :
    IsEmpty ↥Z := by
  let Rf : ULift.{u} (Fin k) → CommRingCat.{u} := fun j => CommRingCat.of (C j.down)
  rw [specMap_eval C i₁, specMap_eval C i₂, ← Category.assoc, ← Category.assoc, cancel_mono] at hab
  have hab' : (a ≫ Sigma.ι (fun j => Spec (Rf j)) (ULift.up i₁)) ≫ sigmaSpec Rf =
      (b ≫ Sigma.ι (fun j => Spec (Rf j)) (ULift.up i₂)) ≫ sigmaSpec Rf := by
    rw [Category.assoc, Category.assoc, ι_sigmaSpec, ι_sigmaSpec]; exact hab
  rw [cancel_mono] at hab'
  exact isEmpty_of_commSq_sigmaι_of_ne ⟨hab'⟩ (fun e => h (congrArg ULift.down e))

end PiSpecCover
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_forall_nonempty_pullback_iso_of_isPullback_pi_univ.PiSpecCover"

namespace GlueClopen

theorem subsingleton_obj {Y : Scheme.{u}} (hY : IsEmpty ↥Y) (B : Y.Modules) (U : (Opens ↥Y)ᵒᵖ) :
    Subsingleton (B.val.obj U) := by
  have hbot : (⊥ : Sieve U.unop) ∈ (Opens.grothendieckTopology ↥Y) U.unop :=
    fun x _ => (hY.false x).elim
  have hT : Limits.IsTerminal (B.val.presheaf.obj U) :=
    Sheaf.isTerminalOfBotCover ⟨B.val.presheaf, B.isSheaf⟩ U.unop hbot
  have h0 : (𝟙 (B.val.presheaf.obj U) : _ ⟶ _) = 0 := hT.hom_ext _ _
  refine ⟨fun a b => ?_⟩
  have ha : a = 0 := by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) a) h0
    simp at this
    exact this
  have hb : b = 0 := by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) b) h0
    simp at this
    exact this
  rw [ha, hb]

theorem hom_subsingleton {Y : Scheme.{u}} (hY : IsEmpty ↥Y) (A B : Y.Modules) : Subsingleton (A ⟶ B) := by
  refine ⟨fun φ ψ => ?_⟩
  ext U : 2
  ext a
  exact @Subsingleton.elim _ (subsingleton_obj hY B (op U)) _ _

variable {k : ℕ} (C : Fin k → Type u) [∀ i, CommRing (C i)]
  {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of (∀ i, C i)))
  {Xi : Fin k → Scheme.{u}} (gi : ∀ i, Xi i ⟶ Spec (CommRingCat.of (C i))) (v : ∀ i, Xi i ⟶ X)
  (hv : ∀ i, IsPullback (v i) (gi i) g (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))))

include hv in
theorem isEmpty_of_ne {i₁ i₂ : Fin k} (h : i₁ ≠ i₂) {Y : Scheme.{u}} (f₁ : Y ⟶ Xi i₁) (f₂ : Y ⟶ Xi i₂)
    (hq : f₁ ≫ v i₁ = f₂ ≫ v i₂) : IsEmpty ↥Y := by
  refine PiSpecCover.isEmpty_of_comp_eval_eq C h (f₁ ≫ gi i₁) (f₂ ≫ gi i₂) ?_
  rw [Category.assoc, Category.assoc, ← (hv i₁).w, ← (hv i₂).w, ← Category.assoc, ← Category.assoc, hq]

noncomputable abbrev FF := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁

variable (M : ∀ i, (Xi i).Modules) [hmono : ∀ i, Mono (v i)]

theorem obj_eq {i₁ i₂ : Fin k} (h : i₁ = i₂) {Y : Scheme.{u}} (q : Y ⟶ X) (f₁ : Y ⟶ Xi i₁) (f₂ : Y ⟶ Xi i₂)
    (hf₁ : f₁ ≫ v i₁ = q) (hf₂ : f₂ ≫ v i₂ = q) :
    (Scheme.Modules.pullback f₁).obj (M i₁) = (Scheme.Modules.pullback f₂).obj (M i₂) := by
  subst h
  obtain rfl : f₁ = f₂ := (cancel_mono (v i₁)).1 (hf₁.trans hf₂.symm)
  rfl

noncomputable def homAux {Y : Scheme.{u}} (q : Y ⟶ X) {i₁ i₂ : Fin k} (f₁ : Y ⟶ Xi i₁) (f₂ : Y ⟶ Xi i₂)
    (hf₁ : f₁ ≫ v i₁ = q) (hf₂ : f₂ ≫ v i₂ = q) :
    (Scheme.Modules.pullback f₁).obj (M i₁) ⟶ (Scheme.Modules.pullback f₂).obj (M i₂) := by
  classical
  exact if h : i₁ = i₂ then eqToHom (obj_eq v M h q f₁ f₂ hf₁ hf₂) else 0

theorem homAux_self {Y : Scheme.{u}} (q : Y ⟶ X) {i : Fin k} (f : Y ⟶ Xi i) (hf : f ≫ v i = q) :
    homAux v M q f f hf hf = 𝟙 _ := by
  simp [homAux]

theorem pullHom_homAux_self {Y' Y : Scheme.{u}} (g' : Y' ⟶ Y) (q : Y ⟶ X) (q' : Y' ⟶ X) {i : Fin k}
    (f : Y ⟶ Xi i) (hf : f ≫ v i = q) (gf : Y' ⟶ Xi i) (hgf : g' ≫ f = gf) (hgf' : gf ≫ v i = q') :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := FF) (M₁ := M i) (M₂ := M i) (f₁ := f) (f₂ := f)
      (homAux v M q f f hf hf) g' gf gf hgf hgf = homAux v M q' gf gf hgf' hgf' := by
  rw [homAux_self, homAux_self]
  simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Cat.Hom.hom_inv_id_toNatTrans_app]
  rfl

include hv in
theorem pullHom_homAux {Y' Y : Scheme.{u}} (g' : Y' ⟶ Y) (q : Y ⟶ X) (q' : Y' ⟶ X) (hq : g' ≫ q = q')
    {i₁ i₂ : Fin k} (f₁ : Y ⟶ Xi i₁) (f₂ : Y ⟶ Xi i₂) (hf₁ : f₁ ≫ v i₁ = q) (hf₂ : f₂ ≫ v i₂ = q)
    (gf₁ : Y' ⟶ Xi i₁) (gf₂ : Y' ⟶ Xi i₂) (hgf₁ : g' ≫ f₁ = gf₁) (hgf₂ : g' ≫ f₂ = gf₂)
    (hgf₁' : gf₁ ≫ v i₁ = q') (hgf₂' : gf₂ ≫ v i₂ = q') :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := FF) (M₁ := M i₁) (M₂ := M i₂) (f₁ := f₁) (f₂ := f₂)
      (homAux v M q f₁ f₂ hf₁ hf₂) g' gf₁ gf₂ hgf₁ hgf₂ = homAux v M q' gf₁ gf₂ hgf₁' hgf₂' := by
  classical
  by_cases h : i₁ = i₂
  · subst h
    obtain rfl : f₁ = f₂ := (cancel_mono (v i₁)).1 (hf₁.trans hf₂.symm)
    obtain rfl : gf₁ = gf₂ := hgf₁.symm.trans hgf₂
    exact pullHom_homAux_self v M g' q q' f₁ hf₁ gf₁ hgf₁ hgf₁'
  · exact @Subsingleton.elim _ (hom_subsingleton (isEmpty_of_ne C g gi v hv h gf₁ gf₂ (hgf₁'.trans hgf₂'.symm))
      ((Scheme.Modules.pullback gf₁).obj (M i₁)) ((Scheme.Modules.pullback gf₂).obj (M i₂))) _ _

include hv in
noncomputable def descentData : (FF).DescentData v where
  obj i := M i
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := homAux v M q f₁ f₂ hf₁ hf₂
  pullHom_hom Y' Y g' q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    pullHom_homAux C g gi v hv M g' q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
      (by rw [← hgf₁, Category.assoc, hf₁, hq]) (by rw [← hgf₂, Category.assoc, hf₂, hq])
  hom_self Y q i f hf := homAux_self v M q f hf
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    classical
    by_cases h₁₂ : i₁ = i₂
    · by_cases h₂₃ : i₂ = i₃
      · subst h₁₂; subst h₂₃
        obtain rfl : f₁ = f₂ := (cancel_mono (v i₁)).1 (hf₁.trans hf₂.symm)
        obtain rfl : f₁ = f₃ := (cancel_mono (v i₁)).1 (hf₁.trans hf₃.symm)
        change homAux v M q f₁ f₁ _ _ ≫ homAux v M q f₁ f₁ _ _ = homAux v M q f₁ f₁ _ _
        simp only [homAux_self, Category.id_comp]
      · exact @Subsingleton.elim _ (hom_subsingleton (isEmpty_of_ne C g gi v hv h₂₃ f₂ f₃ (hf₂.trans hf₃.symm))
          ((Scheme.Modules.pullback f₁).obj (M i₁)) ((Scheme.Modules.pullback f₃).obj (M i₃))) _ _
    · exact @Subsingleton.elim _ (hom_subsingleton (isEmpty_of_ne C g gi v hv h₁₂ f₁ f₂ (hf₁.trans hf₂.symm))
        ((Scheme.Modules.pullback f₁).obj (M i₁)) ((Scheme.Modules.pullback f₃).obj (M i₃))) _ _

end GlueClopen
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_forall_nonempty_pullback_iso_of_isPullback_pi_univ.PiSpecCover"

open GlueClopen in
theorem solution
    {k : ℕ} (C : Fin k → Type u) [∀ i, CommRing (C i)]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of (∀ i, C i)))
    {Xi : Fin k → Scheme.{u}} (gi : ∀ i, Xi i ⟶ Spec (CommRingCat.of (C i))) (v : ∀ i, Xi i ⟶ X)
    (hv : ∀ i, IsPullback (v i) (gi i) g (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))))
    (M : ∀ i, (Xi i).Modules) (hM : ∀ i, Scheme.Modules.IsInvertible (M i)) :
    ∃ N : X.Modules, Scheme.Modules.IsInvertible N ∧ ∀ i, Nonempty ((Scheme.Modules.pullback (v i)).obj N ≅ M i) := by
  classical

  let σ : ∀ i, Spec (CommRingCat.of (C i)) ⟶ Spec (CommRingCat.of (∀ i, C i)) := fun i =>
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))
  haveI hσ : ∀ i, IsOpenImmersion (σ i) := fun i =>
    (inferInstance : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (C ·) i))))
  haveI hvo : ∀ i, IsOpenImmersion (v i) := fun i => by
    rw [← (hv i).isoPullback_hom_fst]; infer_instance
  have hcov : ∀ y : ↥X, ∃ (i : Fin k) (x : ↥(Xi i)), (v i).base x = y := by
    intro y
    obtain ⟨j, z, hy⟩ := PiSpecCover.exists_eval_eq C (g y)
    have hr : y ∈ Set.range (pullback.fst g (σ j)) := by
      rw [Scheme.Pullback.range_fst]; exact ⟨z, hy⟩
    obtain ⟨p, hp⟩ := hr
    refine ⟨j, (hv j).isoPullback.inv p, ?_⟩
    change ((hv j).isoPullback.inv ≫ v j) p = y
    rw [(hv j).isoPullback_inv_fst]
    exact hp

  haveI : ∀ i, Mono (v i) := fun i => inferInstance
  let D := descentData C g gi v hv M
  obtain ⟨N, ⟨e⟩⟩ := (AlgebraicGeometry.Scheme.Modules.toDescentData_essSurj_of_openCover v hcov).mem_essImage D
  let ψ : ∀ i, (Scheme.Modules.pullback (v i)).obj N ≅ M i := fun i =>
    { hom := e.hom.hom i
      inv := e.inv.hom i
      hom_inv_id := by
        have := congrArg (fun φ => Pseudofunctor.DescentData.Hom.hom φ i) e.hom_inv_id
        simp only [Pseudofunctor.DescentData.comp_hom, Pseudofunctor.DescentData.id_hom] at this
        exact this
      inv_hom_id := by
        have := congrArg (fun φ => Pseudofunctor.DescentData.Hom.hom φ i) e.inv_hom_id
        simp only [Pseudofunctor.DescentData.comp_hom, Pseudofunctor.DescentData.id_hom] at this
        exact this }
  exact ⟨N, AlgebraicGeometry.Scheme.Modules.IsInvertible.of_forall_pullback_iso_of_isOpenImmersion v hcov M hM N ψ,
    fun i => ⟨ψ i⟩⟩

end S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_forall_nonempty_pullback_iso_of_isPullback_pi_univ
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_forall_nonempty_pullback_iso_of_isPullback_pi_univ (solution)
