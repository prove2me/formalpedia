-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_etale_units_frame_torsors
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-19T13:53:52.570784+00:00
-- url     : https://prove2.me/submissions/ace222fc-3777-455e-8a89-3f57477b1821

import Definitions.Def_AlgebraicGeometry_EtaleFrameTorsorCompletion
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_etaleFrame_presentation_of_torsor
import Theorems.Thm_AlgebraicGeometry_Scheme_etaleFrame_tensor_restrict

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory Opposite
open PhilipponTorsorPresheafDifference PhilipponTorsorInvariantDescent
open PhilipponTorsorSectionFibers PhilipponTorsorFiberComparison PhilipponPresheafTorsorCompletion

namespace PhilipponTorsorMorphismExtension
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

theorem isLocallyInjective {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q)
    (h : ∀ U, Nonempty (P.obj U) → Function.Bijective (f.app U)) :
    Presheaf.IsLocallyInjective J f := by
  apply Presheaf.isLocallyInjective_of_injective J f
  intro U p q he
  exact (h U ⟨p⟩).injective he

theorem isLocallySurjective {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q)
    (hlocal : ∀ U, presence P U ∈ J U)
    (h : ∀ U, Nonempty (P.obj U) → Function.Bijective (f.app U)) :
    Presheaf.IsLocallySurjective J f where
  imageSieve_mem {U} s := by
    refine J.superset_covering ?_ (hlocal U)
    intro V g hv
    exact (h (op V) hv).surjective (Q.map g.op s)

theorem equivalent_of_map {G : Sheaf J AddCommGrpCat.{w}} {A B : Torsor G}
    (f : A.D.P ⟶ B.D.P)
    (hf : ∀ (U : Cᵒᵖ) (p q : A.D.P.obj U), B.D.diff U (f.app U p) (f.app U q) = A.D.diff U p q) :
    Equivalent A B := by
  have hb (U : Cᵒᵖ) : Nonempty (A.D.P.obj U) → Function.Bijective (f.app U) := by
    rintro ⟨p⟩
    exact bijective_of_section (D := A.D) (E := B.D) f U p (A.diff_bijective U p)
      (B.diff_bijective U (f.app U p)) (fun q => hf U q p)
  let A' : Sheaf J (Type w) := ⟨A.D.P, A.isSheaf⟩
  let B' : Sheaf J (Type w) := ⟨B.D.P, B.isSheaf⟩
  let φ : A' ⟶ B' := ⟨f⟩
  let : IsIso φ := (Sheaf.isLocallyBijective_iff_isIso (A := Type w) φ).mp
    ⟨isLocallyInjective f hb, isLocallySurjective f A.locally_nonempty hb⟩
  exact ⟨(sheafToPresheaf J (Type w)).mapIso (asIso φ), hf⟩

variable [J.WEqualsLocallyBijective (Type w)]

/-- A map preserving differences extends along a locally bijective
comparison of section presheaves. -/
theorem exists_extension {G : Sheaf J AddCommGrpCat.{w}} {D E : Difference G.obj}
    {B : Torsor G} (η : D.P ⟶ E.P)
    (hlocal : ∀ U, presence D.P U ∈ J U)
    (hb : ∀ U, Nonempty (D.P.obj U) → Function.Bijective (η.app U))
    (hη : ∀ (U : Cᵒᵖ) (p q : D.P.obj U), E.diff U (η.app U p) (η.app U q) = D.diff U p q)
    (k : D.P ⟶ B.D.P)
    (hk : ∀ (U : Cᵒᵖ) (p q : D.P.obj U), B.D.diff U (k.app U p) (k.app U q) = D.diff U p q) :
    ∃ f : E.P ⟶ B.D.P,
      ∀ (U : Cᵒᵖ) (p q : E.P.obj U), B.D.diff U (f.app U p) (f.app U q) = E.diff U p q := by
  have hw : J.W η := (J.W_iff_isLocallyBijective η).mpr
    ⟨isLocallyInjective η hb, isLocallySurjective η hlocal hb⟩
  obtain ⟨f, hf⟩ := (hw B.D.P B.isSheaf).surjective k
  refine ⟨f, fun U x y => ?_⟩
  let G' : Sheaf J (Type w) := (sheafCompose J (forget AddCommGrpCat.{w})).obj G
  apply (G'.property.isSheafFor _ (hlocal U.unop)).isSeparatedFor.ext
  intro V g hv
  obtain ⟨p, hp⟩ := (hb (op V) hv).surjective (E.P.map g.op x)
  obtain ⟨q, hq⟩ := (hb (op V) hv).surjective (E.P.map g.op y)
  change G.obj.map g.op (B.D.diff U (f.app U x) (f.app U y)) =
    G.obj.map g.op (E.diff U x y)
  have he (t : D.P.obj (op V)) : f.app (op V) (η.app (op V) t) = k.app (op V) t :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hf (op V)) t
  rw [B.D.map_diff, E.map_diff, ← NatTrans.naturality_apply f g.op x,
    ← NatTrans.naturality_apply f g.op y, ← hp, ← hq, he p, he q, hk, hη]

/-- An equivariant map on locally available sections extends to the
associated torsor and determines an equivariant isomorphism. -/
theorem equivalent_of_local_map {G : Sheaf J AddCommGrpCat.{w}} {A B : Torsor G}
    {D : Difference G.obj} (η : D.P ⟶ A.D.P)
    (hlocal : ∀ U, presence D.P U ∈ J U)
    (hb : ∀ U, Nonempty (D.P.obj U) → Function.Bijective (η.app U))
    (hη : ∀ (U : Cᵒᵖ) (p q : D.P.obj U), A.D.diff U (η.app U p) (η.app U q) = D.diff U p q)
    (k : D.P ⟶ B.D.P)
    (hk : ∀ (U : Cᵒᵖ) (p q : D.P.obj U), B.D.diff U (k.app U p) (k.app U q) = D.diff U p q) :
    Equivalent A B := by
  obtain ⟨f, hf⟩ := exists_extension η hlocal hb hη k hk
  exact equivalent_of_map f hf

end PhilipponTorsorMorphismExtension
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open PhilipponTorsorInvariantDescent PhilipponTorsorPresheafDifference
open PhilipponTorsorCohomologyRepresentative PhilipponTorsorSectionFibers
open PhilipponTorsorFiberComparison PhilipponTorsorSectionExactness

namespace PhilipponTorsorClassification
universe u v w w'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
theorem pair_presence {G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (D E : Difference G) (U : C)
    (hD : presence D.P U ∈ J U) (hE : presence E.P U ∈ J U) :
    presence (pair D E).P U ∈ J U := by
  apply J.superset_covering _ (J.intersection_covering hD hE)
  rintro V f ⟨⟨x⟩, ⟨y⟩⟩
  exact ⟨(x, y)⟩

end PhilipponTorsorClassification
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponFramePullback PhilipponEtaleFramePresheaf PhilipponEtaleFrameSections
open PhilipponTorsorSectionFibers PhilipponTorsorFiberComparison

namespace PhilipponEtaleFrameIsomorphism
universe u
variable {X : Scheme.{u}} {M N : X.Modules}

/-- A module isomorphism gives a natural map on actual frames. -/
def postcompose (e : M ≅ N) : presheaf M ⟶ presheaf N where
  app U := ↾fun p => p ≪≫ (Scheme.Modules.pullback U.unop.hom).mapIso e
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro p
    let γ := Scheme.Modules.pullbackComp f.unop.left U.unop.hom ≪≫
      Scheme.Modules.pullbackCongr (MorphismProperty.Over.w f.unop)
    change (pullFrame f.unop.left p ≪≫ γ.app M) ≪≫ (Scheme.Modules.pullback V.unop.hom).mapIso e =
      pullFrame f.unop.left (p ≪≫ (Scheme.Modules.pullback U.unop.hom).mapIso e) ≪≫ γ.app N
    apply Iso.ext
    have h := γ.hom.naturality e.hom
    change (Scheme.Modules.pullback f.unop.left).map ((Scheme.Modules.pullback U.unop.hom).map e.hom) ≫
        (γ.app N).hom = (γ.app M).hom ≫ (Scheme.Modules.pullback V.unop.hom).map e.hom at h
    simp only [pullFrame, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    rw [h]

theorem difference_postcompose (e : M ≅ N) (U : X.Etaleᵒᵖ) (p q : (presheaf M).obj U) :
    diff N U.unop ((postcompose e).app U p) ((postcompose e).app U q) = diff M U.unop p q := by
  exact congrArg Additive.ofMul (PhilipponFramePullback.difference_postcompose (X := U.unop.left) p q
    ((Scheme.Modules.pullback U.unop.hom).mapIso e))

/-- Isomorphic invertible modules give equivariantly isomorphic torsors
for every choice of the comparison from frames. -/
theorem equivalent_of_iso (e : M ≅ N) (hM : Scheme.Modules.IsInvertible M)
    {A B : Torsor (PhilipponKummerSequence.units X)}
    (f : presheaf M ⟶ A.D.P) (g : presheaf N ⟶ B.D.P)
    (hf : ∀ (U : X.Etaleᵒᵖ) (p q : Frame M U.unop),
      A.D.diff U (f.app U p) (f.app U q) = diff M U.unop p q)
    (hfb : ∀ U : X.Etaleᵒᵖ, Nonempty (Frame M U.unop) → Function.Bijective (f.app U))
    (hg : ∀ (U : X.Etaleᵒᵖ) (p q : Frame N U.unop),
      B.D.diff U (g.app U p) (g.app U q) = diff N U.unop p q) : Equivalent A B := by
  refine PhilipponTorsorMorphismExtension.equivalent_of_local_map (D := difference M)
    f (locally_nonempty M hM) hfb hf (postcompose e ≫ g) (fun U p q => ?_)
  change B.D.diff U (g.app U ((postcompose e).app U p)) (g.app U ((postcompose e).app U q)) =
    diff M U.unop p q
  rw [hg, difference_postcompose]

end PhilipponEtaleFrameIsomorphism
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponEtaleFrameTorsor PhilipponEtaleFramePresheaf PhilipponEtaleFrameSections
open PhilipponFrameUnits PhilipponFramePullback

namespace PhilipponEtaleFrameRecovery
universe u
variable {X : Scheme.{u}} {M N : X.Modules} (P : Presentation M) (Q : Presentation N)
variable (e : P.torsor.D.P ≅ Q.torsor.D.P)

/-- Over an object with a frame of the target, recover the image of a
source frame under an isomorphism of frame torsors. -/
def frameImage {U : X.Etale} (hU : Nonempty (Frame N U)) (p : Frame M U) : Frame N U :=
  (Equiv.ofBijective (Q.frames.app (op U)) (Q.bijective (op U) hU)).symm
    (e.hom.app (op U) (P.frames.app (op U) p))

theorem frameImage_apply {U : X.Etale} (hU : Nonempty (Frame N U)) (p : Frame M U) :
    Q.frames.app (op U) (frameImage P Q e hU p) = e.hom.app (op U) (P.frames.app (op U) p) :=
  (Equiv.ofBijective (Q.frames.app (op U)) (Q.bijective (op U) hU)).apply_symm_apply _

theorem frameImage_restrict {U V : X.Etale} (f : V ⟶ U)
    (hU : Nonempty (Frame N U)) (hV : Nonempty (Frame N V)) (p : Frame M U) :
    frameImage P Q e hV (restrict M f p) = restrict N f (frameImage P Q e hU p) := by
  apply (Q.bijective (op V) hV).injective
  change Q.frames.app (op V) (frameImage P Q e hV (restrict M f p)) =
    Q.frames.app (op V) ((presheaf N).map f.op (frameImage P Q e hU p))
  rw [frameImage_apply, NatTrans.naturality_apply Q.frames f.op, frameImage_apply,
    ← NatTrans.naturality_apply e.hom f.op, ← NatTrans.naturality_apply P.frames f.op]
  rfl

def moduleIso {U : X.Etale} (hU : Nonempty (Frame N U)) (p : Frame M U) :
    (Scheme.Modules.pullback U.hom).obj M ≅ (Scheme.Modules.pullback U.hom).obj N :=
  p.symm ≪≫ frameImage P Q e hU p

/-- The isomorphism recovered from a difference-preserving map of torsors
over a trivializing object is independent of the frame. -/
theorem moduleIso_independent
    (he : ∀ (U : X.Etaleᵒᵖ) (p q : P.torsor.D.P.obj U),
      Q.torsor.D.diff U (e.hom.app U p) (e.hom.app U q) = P.torsor.D.diff U p q)
    {U : X.Etale} (hU : Nonempty (Frame N U)) (p q : Frame M U) :
    moduleIso P Q e hU p = moduleIso P Q e hU q := by
  have hd := (Q.diff_eq (op U) (frameImage P Q e hU p) (frameImage P Q e hU q)).symm
  rw [frameImage_apply, frameImage_apply, he, P.diff_eq] at hd
  change Additive.ofMul (differenceEquiv U.left (frameImage P Q e hU q) (frameImage P Q e hU p)) =
    Additive.ofMul (differenceEquiv U.left q p) at hd
  have h := (unitAut U.left).injective (Additive.ofMul.injective hd)
  change frameImage P Q e hU p ≪≫ (frameImage P Q e hU q).symm = p ≪≫ q.symm at h
  calc
    moduleIso P Q e hU p = p.symm ≪≫ (frameImage P Q e hU p ≪≫ (frameImage P Q e hU q).symm) ≪≫
        frameImage P Q e hU q := by simp [moduleIso, Iso.trans_assoc]
    _ = moduleIso P Q e hU q := by rw [h]; simp [moduleIso, Iso.trans_assoc]

/-- The recovered isomorphisms commute with restriction between objects
that admit frames of both modules. -/
theorem moduleIso_restrict {U V : X.Etale} (f : V ⟶ U)
    (hU : Nonempty (Frame N U)) (hV : Nonempty (Frame N V)) (p : Frame M U) :
    let c := Scheme.Modules.pullbackComp f.left U.hom ≪≫
      Scheme.Modules.pullbackCongr (MorphismProperty.Over.w f)
    (c.app M).symm ≪≫ (Scheme.Modules.pullback f.left).mapIso (moduleIso P Q e hU p) ≪≫
      c.app N = moduleIso P Q e hV (restrict M f p) := by
  dsimp only
  simp only [moduleIso, frameImage_restrict P Q e f hU hV p]
  apply Iso.ext
  simp [restrict, pullFrame, Category.assoc]

variable (M N) in
/-- Invertible modules have simultaneous frames on a Zariski neighborhood
of each point. -/
theorem exists_common_open_frames (hM : Scheme.Modules.IsInvertible M)
    (hN : Scheme.Modules.IsInvertible N) (x : X) :
    ∃ (V : X.Opens), x ∈ V ∧ Nonempty (Frame M (Scheme.Etale.mk V.ι)) ∧
      Nonempty (Frame N (Scheme.Etale.mk V.ι)) := by
  obtain ⟨U, hxU, ⟨p⟩⟩ := hM.exists_trivialization x
  obtain ⟨W, hxW, ⟨q⟩⟩ := hN.exists_trivialization x
  let V := U ⊓ W
  let f : Scheme.Etale.mk V.ι ⟶ Scheme.Etale.mk U.ι :=
    MorphismProperty.Over.homMk (X.homOfLE inf_le_left) (X.homOfLE_ι inf_le_left) trivial
  let g : Scheme.Etale.mk V.ι ⟶ Scheme.Etale.mk W.ι :=
    MorphismProperty.Over.homMk (X.homOfLE inf_le_right) (X.homOfLE_ι inf_le_right) trivial
  exact ⟨V, ⟨hxU, hxW⟩, ⟨restrict M f p.symm⟩, ⟨restrict N g q.symm⟩⟩

end PhilipponEtaleFrameRecovery
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace PhilipponPullbackSectionMaps
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The map on sections given by the unit of inverse and direct image. -/
abbrev onSections (M : Y.Modules) (U : Y.Opens) :
    Γ(M, U) ⟶ Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U

theorem onSections_smul (M : Y.Modules) (U : Y.Opens) (r : Γ(Y, U)) (a : Γ(M, U)) :
    onSections f M U (r • a) = f.app U r • onSections f M U a :=
  Scheme.Modules.Hom.app_smul ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) r a

/-- The section map of an open immersion is an isomorphism over an open
contained in its image. -/
theorem onSections_isIso [IsOpenImmersion f] (M : Y.Modules) (U : Y.Opens) (hU : U ≤ f.opensRange) :
    IsIso (onSections f M U) := by
  let e := Scheme.Modules.restrictFunctorIsoPullback f
  have h := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) M
  have h' := congrArg (fun a => Scheme.Modules.Hom.app a U) h
  change ((Scheme.Modules.restrictAdjunction f).unit.app M).app U ≫ (e.hom.app M).app (f ⁻¹ᵁ U) =
    onSections f M U at h'
  have hEq : f ''ᵁ (f ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_eq_right.mpr hU
  have heq : (homOfLE (f.image_preimage_le U)) = eqToHom hEq := Subsingleton.elim _ _
  have hi : IsIso (((Scheme.Modules.restrictAdjunction f).unit.app M).app U) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app, heq]
    infer_instance
  rw [← h']
  infer_instance

theorem onSections_naturality {M N : Y.Modules} (a : M ⟶ N) (U : Y.Opens) :
    a.app U ≫ onSections f N U =
      onSections f M U ≫ ((Scheme.Modules.pullback f).map a).app (f ⁻¹ᵁ U) := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a
  exact congrArg (fun k => Scheme.Modules.Hom.app k U) h

theorem onSections_restrict (M : Y.Modules) {U V : Y.Opens} (i : V ⟶ U) :
    M.presheaf.map i.op ≫ onSections f M V = onSections f M U ≫
      ((Scheme.Modules.pullback f).obj M).presheaf.map
        ((TopologicalSpace.Opens.map f.base).map i).op :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).mapPresheaf.naturality i.op

/-- The section maps for successive pullbacks agree with the composite
via the canonical comparison of pullback functors. -/
theorem onSections_comp {Z : Scheme.{u}} (g : Z ⟶ X) (M : Y.Modules) (U : Y.Opens) :
    onSections (g ≫ f) M U = onSections f M U ≫
      onSections g ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) ≫
      ((Scheme.Modules.pullbackComp g f).hom.app M).app ((g ≫ f) ⁻¹ᵁ U) := by
  let F := Scheme.Modules.pullback f
  let adjF := Scheme.Modules.pullbackPushforwardAdjunction f
  let adjG := Scheme.Modules.pullbackPushforwardAdjunction g
  let adjC := Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)
  let P := Scheme.Modules.pushforward (g ≫ f)
  let e := (Scheme.Modules.pullbackComp g f).app M
  have h := unit_conjugateEquiv (adjF.comp adjG) adjC (Scheme.Modules.pullbackComp g f).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  change (adjF.comp adjG).unit.app M ≫ (Scheme.Modules.pushforwardComp g f).hom.app
      ((F ⋙ Scheme.Modules.pullback g).obj M) = adjC.unit.app M ≫ P.map e.inv at h
  have h' := congrArg (fun k => k ≫ P.map e.hom) h
  simp only [Category.assoc] at h'
  rw [← P.map_comp, Iso.inv_hom_id, P.map_id] at h'
  have hh := congrArg (fun k => Scheme.Modules.Hom.app k U)
    (h'.trans (Category.comp_id (adjC.unit.app M)))
  rw [Adjunction.comp_unit_app] at hh
  let c := (e.hom).app ((g ≫ f) ⁻¹ᵁ U)
  let a := onSections f M U
  let b := onSections g ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U)
  simp only [adjC, adjF, adjG, F, P, e, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforward_map_app,
    Category.assoc] at hh
  change a ≫ b ≫ 𝟙 _ ≫ c = onSections (g ≫ f) M U at hh
  exact hh.symm.trans (congrArg (fun k => a ≫ b ≫ k) (Category.id_comp c))

end PhilipponPullbackSectionMaps
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponPullbackSectionMaps

namespace PhilipponOpenModuleComparison
universe u
variable {S X : Scheme.{u}} (f : X ⟶ S) {M N : S.Modules}

/-- Transport a map of pulled-back modules to sections of the original
modules on an open where the section map for the target is invertible. -/
abbrev sectionMap (a : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (U : S.Opens) [IsIso (onSections f N U)] : Γ(M, U) ⟶ Γ(N, U) :=
  onSections f M U ≫ a.app (f ⁻¹ᵁ U) ≫ inv (onSections f N U)

@[reassoc]
theorem sectionMap_spec (a : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (U : S.Opens) [IsIso (onSections f N U)] : sectionMap f a U ≫ onSections f N U =
      onSections f M U ≫ a.app (f ⁻¹ᵁ U) := by
  simp only [sectionMap, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem sectionMap_smul (a : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (U : S.Opens) [IsIso (onSections f N U)] (r : Γ(S, U)) (x : Γ(M, U)) :
    sectionMap f a U (r • x) = r • sectionMap f a U x := by
  have h (z : Γ(M, U)) : onSections f N U (sectionMap f a U z) =
      a.app (f ⁻¹ᵁ U) (onSections f M U z) :=
    ConcreteCategory.congr_hom (sectionMap_spec f a U) z
  apply (ConcreteCategory.bijective_of_isIso (onSections f N U)).injective
  rw [h, onSections_smul f N U, h, onSections_smul f M U, Scheme.Modules.Hom.app_smul]

theorem sectionMap_restrict (a : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    {U V : S.Opens} (i : V ⟶ U) [IsIso (onSections f N U)] [IsIso (onSections f N V)] :
    sectionMap f a U ≫ N.presheaf.map i.op = M.presheaf.map i.op ≫ sectionMap f a V := by
  let j := ((TopologicalSpace.Opens.map f.base).map i).op
  have ha : ((Scheme.Modules.pullback f).obj M).presheaf.map j ≫ a.app (f ⁻¹ᵁ V) =
      a.app (f ⁻¹ᵁ U) ≫ ((Scheme.Modules.pullback f).obj N).presheaf.map j :=
    a.mapPresheaf.naturality j
  apply (cancel_mono (onSections f N V)).mp
  simp only [Category.assoc]
  rw [onSections_restrict f N i]
  simp only [sectionMap, Category.assoc, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]
  calc
    _ = onSections f M U ≫ ((Scheme.Modules.pullback f).obj M).presheaf.map j ≫
          a.app (f ⁻¹ᵁ V) := congrArg (onSections f M U ≫ ·) ha.symm
    _ = (onSections f M U ≫ ((Scheme.Modules.pullback f).obj M).presheaf.map j) ≫
          a.app (f ⁻¹ᵁ V) := (Category.assoc _ _ _).symm
    _ = (M.presheaf.map i.op ≫ onSections f M V) ≫ a.app (f ⁻¹ᵁ V) :=
      congrArg (· ≫ a.app (f ⁻¹ᵁ V)) (onSections_restrict f M i).symm
    _ = _ := Category.assoc _ _ _

variable {Z : Scheme.{u}}

/-- Compatible module maps on two pullbacks give the same map on
sections whenever their comparison maps on sections are invertible. -/
theorem sectionMap_compare (g : Z ⟶ X) {h : Z ⟶ S} (w : g ≫ f = h)
    (a : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N)
    (b : (Scheme.Modules.pullback h).obj M ≅ (Scheme.Modules.pullback h).obj N)
    (hb : let c := Scheme.Modules.pullbackComp g f ≪≫ Scheme.Modules.pullbackCongr w
      (c.app M).symm ≪≫ (Scheme.Modules.pullback g).mapIso a ≪≫ c.app N = b)
    (U : S.Opens) [IsIso (onSections f N U)] [IsIso (onSections h N U)] :
    sectionMap f a.hom U = sectionMap h b.hom U := by
  subst h
  let c := Scheme.Modules.pullbackComp g f
  change (((c.app M) ≪≫ Iso.refl _).symm ≪≫
    (Scheme.Modules.pullback g).mapIso a ≪≫ ((c.app N) ≪≫ Iso.refl _)) = b at hb
  simp only [Iso.trans_refl] at hb
  have hc : (c.app M).hom ≫ b.hom = (Scheme.Modules.pullback g).map a.hom ≫ (c.app N).hom := by
    rw [← hb]
    simp
  have hc' : (c.app M).hom.app ((g ≫ f) ⁻¹ᵁ U) ≫ b.hom.app ((g ≫ f) ⁻¹ᵁ U) =
      ((Scheme.Modules.pullback g).map a.hom).app ((g ≫ f) ⁻¹ᵁ U) ≫
        (c.app N).hom.app ((g ≫ f) ⁻¹ᵁ U) :=
    congrArg (fun k => Scheme.Modules.Hom.app k ((g ≫ f) ⁻¹ᵁ U)) hc
  apply (cancel_mono (onSections (g ≫ f) N U)).mp
  rw [sectionMap_spec, onSections_comp f g N U, onSections_comp f g M U]
  simp only [Category.assoc]
  change _ = onSections f M U ≫
    onSections g ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) ≫
      (c.app M).hom.app ((g ≫ f) ⁻¹ᵁ U) ≫ b.hom.app ((g ≫ f) ⁻¹ᵁ U)
  rw [hc']
  simp only [sectionMap, Category.assoc, IsIso.inv_hom_id_assoc]
  let d := (c.app N).hom.app ((g ≫ f) ⁻¹ᵁ U)
  have hh := congrArg (fun k => onSections f M U ≫ k ≫ d)
    (onSections_naturality g a.hom (f ⁻¹ᵁ U))
  simp only [Category.assoc] at hh
  exact hh

end PhilipponOpenModuleComparison
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PhilipponZariskiModuleBasis
universe u v
variable {X : Scheme.{u}} {ι : Type v} (B : ι → X.Opens)
variable {M N : X.Modules} (hB : Opens.IsBasis (Set.range B))
include hB

/-- A map defined on a basis of opens extends uniquely as a map of
module sheaves when its components on that basis are linear. -/
theorem exists_moduleHom
    (α : (inducedFunctor B).op ⋙ M.presheaf ⟶ (inducedFunctor B).op ⋙ N.presheaf)
    (hα : ∀ (i : ι) (r : Γ(X, B i)) (a : Γ(M, B i)),
      α.app (op i) (r • a) = @SMul.smul (Γ(X, B i)) (Γ(N, B i)) inferInstance r (α.app (op i) a)) :
    ∃ φ : M ⟶ N, ∀ i, φ.app (B i) = α.app (op i) := by
  let N' : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨N.presheaf, N.isSheaf⟩
  let β := TopCat.Sheaf.restrictHomEquivHom M.presheaf N' hB α
  have hβ (i : ι) : β.app (op (B i)) = α.app (op i) :=
    TopCat.Sheaf.extend_hom_app M.presheaf N' hB α i
  let H := inducedFunctor B
  let J := Opens.grothendieckTopology X
  let : H.IsCoverDense J := TopCat.Opens.coverDense_inducedFunctor hB
  have hlin (U : X.Opens) (r : Γ(X, U)) (a : Γ(M, U)) :
      β.app (op U) (r • a) = r • β.app (op U) a := by
    let N₀ : Sheaf J (Type u) := (sheafCompose J (forget AddCommGrpCat.{u})).obj N'
    let R := Sieve.coverByImage H U
    have hR : R ∈ J U := H.is_cover_of_isCoverDense J U
    apply (N₀.property.isSheafFor R hR).isSeparatedFor.ext
    intro V f hf
    obtain ⟨i, k, l, hk⟩ := hf
    change B i ⟶ U at l
    have hloc : N.presheaf.map l.op (β.app (op U) (r • a)) =
        N.presheaf.map l.op (r • β.app (op U) a) := by
      rw [← NatTrans.naturality_apply β l.op, M.map_smul, N.map_smul,
        ← NatTrans.naturality_apply β l.op, hβ]
      exact hα i (X.presheaf.map l.op r) (M.presheaf.map l.op a)
    change N.presheaf.map f.op (β.app (op U) (r • a)) =
      N.presheaf.map f.op (r • β.app (op U) a)
    rw [← hk, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    exact congrArg (fun x : Γ(N, B i) => N.presheaf.map k.op x) hloc
  let φ : M ⟶ N := ⟨PresheafOfModules.homMk (M₁ := M.val) (M₂ := N.val) β (fun U => hlin U.unop)⟩
  refine ⟨φ, fun i => ?_⟩
  apply AddCommGrpCat.ext
  intro a
  exact ConcreteCategory.congr_hom (hβ i) a

/-- Linear isomorphisms on a basis that are compatible with restriction
give an isomorphism of the actual modules. -/
theorem nonempty_moduleIso
    (α : (inducedFunctor B).op ⋙ M.presheaf ⟶ (inducedFunctor B).op ⋙ N.presheaf)
    (hα : ∀ (i : ι) (r : Γ(X, B i)) (a : Γ(M, B i)),
      α.app (op i) (r • a) = @SMul.smul (Γ(X, B i)) (Γ(N, B i)) inferInstance r (α.app (op i) a))
    (hi : ∀ i : ι, IsIso (α.app (op i))) : Nonempty (M ≅ N) := by
  obtain ⟨φ, hφ⟩ := exists_moduleHom B hB α hα
  let M' : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
  let N' : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨N.presheaf, N.isSheaf⟩
  let f : M' ⟶ N' := ⟨(Scheme.Modules.toPresheaf X).map φ⟩
  let : IsIso f := TopCat.Sheaf.isIso_iff_isIso_basis hB (φ := f) (by
    intro i
    change IsIso (φ.app (B i))
    rw [hφ]
    exact hi i)
  let : IsIso ((Scheme.Modules.toPresheaf X).map φ) :=
    inferInstanceAs (IsIso ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).map f))
  let : IsIso φ := isIso_of_reflects_iso φ (Scheme.Modules.toPresheaf X)
  exact ⟨asIso φ⟩

end PhilipponZariskiModuleBasis
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PhilipponEtaleFrameSections PhilipponEtaleFrameTorsor PhilipponEtaleFrameRecovery
open PhilipponPullbackSectionMaps PhilipponOpenModuleComparison
open PhilipponTorsorFiberComparison

namespace PhilipponEtaleFrameGlobalRecovery
universe u
variable {X : Scheme.{u}} {M N : X.Modules}

abbrev openObject (U : X.Opens) : X.Etale := Scheme.Etale.mk U.ι

abbrev openInclusion {V U : X.Opens} (h : V ≤ U) : openObject V ⟶ openObject U :=
  MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι h) trivial

/-- The opens on which both modules admit frames. -/
def CommonOpens (M N : X.Modules) :=
  {U : X.Opens // Nonempty (Frame M (openObject U)) ∧ Nonempty (Frame N (openObject U))}

abbrev basisOpen (M N : X.Modules) (U : CommonOpens M N) : X.Opens := U.val

theorem isBasis (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N) :
    Opens.IsBasis (Set.range (basisOpen M N)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro W x hx
  obtain ⟨U, hxU, ⟨p⟩, ⟨q⟩⟩ := exists_common_open_frames M N hM hN x
  let V := U ⊓ W
  let f : openObject V ⟶ openObject U := openInclusion inf_le_left
  let i : CommonOpens M N := ⟨V, ⟨restrict M f p⟩, ⟨restrict N f q⟩⟩
  exact ⟨V, ⟨i, rfl⟩, ⟨hxU, hx⟩, inf_le_right⟩

variable (P : Presentation M) (Q : Presentation N) (e : P.torsor.D.P ≅ Q.torsor.D.P)

def localIso (U : CommonOpens M N) :
    (Scheme.Modules.pullback U.val.ι).obj M ≅ (Scheme.Modules.pullback U.val.ι).obj N :=
  moduleIso P Q e U.property.2 U.property.1.some

private theorem isIso_onOpen {L : X.Modules} (U W : X.Opens) (h : W ≤ U) :
    IsIso (onSections U.ι L W) :=
  onSections_isIso U.ι L W (by rw [U.opensRange_ι]; exact h)

def homOnOpen (U : CommonOpens M N) {W : X.Opens} (h : W ≤ U.val) : Γ(M, W) ⟶ Γ(N, W) :=
  letI := isIso_onOpen (L := N) U.val W h
  sectionMap U.val.ι (localIso P Q e U).hom W

theorem isIso_homOnOpen (U : CommonOpens M N) {W : X.Opens} (h : W ≤ U.val) :
    IsIso (homOnOpen P Q e U h) := by
  let : IsIso (onSections U.val.ι M W) := isIso_onOpen U.val W h
  let : IsIso (onSections U.val.ι N W) := isIso_onOpen U.val W h
  change IsIso (sectionMap U.val.ι (localIso P Q e U).hom W)
  infer_instance

theorem homOnOpen_smul (U : CommonOpens M N) {W : X.Opens} (h : W ≤ U.val)
    (r : Γ(X, W)) (a : Γ(M, W)) : homOnOpen P Q e U h (r • a) = r • homOnOpen P Q e U h a := by
  let : IsIso (onSections U.val.ι N W) := isIso_onOpen U.val W h
  exact sectionMap_smul U.val.ι (localIso P Q e U).hom W r a

theorem homOnOpen_restrict (U : CommonOpens M N) {V W : X.Opens} (i : V ⟶ W) (h : W ≤ U.val) :
    homOnOpen P Q e U h ≫ N.presheaf.map i.op =
      M.presheaf.map i.op ≫ homOnOpen P Q e U ((leOfHom i).trans h) := by
  let : IsIso (onSections U.val.ι N W) := isIso_onOpen U.val W h
  let : IsIso (onSections U.val.ι N V) := isIso_onOpen U.val V ((leOfHom i).trans h)
  exact sectionMap_restrict U.val.ι (localIso P Q e U).hom i

variable (he : ∀ (U : X.Etaleᵒᵖ) (p q : P.torsor.D.P.obj U),
  Q.torsor.D.diff U (e.hom.app U p) (e.hom.app U q) = P.torsor.D.diff U p q)

include he in
theorem homOnOpen_compare (U V : CommonOpens M N) (h : V.val ≤ U.val) :
    homOnOpen P Q e U h = homOnOpen P Q e V le_rfl := by
  let f : openObject V.val ⟶ openObject U.val := openInclusion h
  let : IsIso (onSections U.val.ι N V.val) := isIso_onOpen U.val V.val h
  let : IsIso (onSections V.val.ι N V.val) := isIso_onOpen V.val V.val le_rfl
  have hb := moduleIso_restrict P Q e f U.property.2 V.property.2 U.property.1.some
  have hind := moduleIso_independent P Q e he V.property.2
    (restrict M f U.property.1.some) V.property.1.some
  have hc : let c := Scheme.Modules.pullbackComp (X.homOfLE h) U.val.ι ≪≫
      Scheme.Modules.pullbackCongr (X.homOfLE_ι h)
      (c.app M).symm ≪≫ (Scheme.Modules.pullback (X.homOfLE h)).mapIso (localIso P Q e U) ≪≫
        c.app N = localIso P Q e V := hb.trans hind
  exact sectionMap_compare U.val.ι (X.homOfLE h) (X.homOfLE_ι h) (localIso P Q e U)
    (localIso P Q e V) hc V.val

def mapOnBasis : (inducedFunctor (basisOpen M N)).op ⋙ M.presheaf ⟶
    (inducedFunctor (basisOpen M N)).op ⋙ N.presheaf where
  app U := homOnOpen P Q e U.unop le_rfl
  naturality U V f := by
    let i : V.unop.val ⟶ U.unop.val := (inducedFunctor (basisOpen M N)).map f.unop
    change M.presheaf.map i.op ≫ homOnOpen P Q e V.unop le_rfl =
      homOnOpen P Q e U.unop le_rfl ≫ N.presheaf.map i.op
    exact ((homOnOpen_restrict P Q e U.unop i le_rfl).trans
      (congrArg (M.presheaf.map i.op ≫ ·) (homOnOpen_compare P Q e he U.unop V.unop (leOfHom i)))).symm

/-- Equivariantly isomorphic frame torsors of invertible modules recover
an isomorphism of the original modules by gluing on the Zariski basis. -/
theorem nonempty_iso (P : Presentation M) (Q : Presentation N)
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (h : Equivalent P.torsor Q.torsor) : Nonempty (M ≅ N) := by
  obtain ⟨e, he⟩ := h
  exact PhilipponZariskiModuleBasis.nonempty_moduleIso (basisOpen M N) (isBasis hM hN)
    (mapOnBasis P Q e he) (fun U => homOnOpen_smul P Q e U le_rfl)
      (fun U => isIso_homOnOpen P Q e U le_rfl)

end PhilipponEtaleFrameGlobalRecovery
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PhilipponFrameUnits

namespace PhilipponTensorFrames
universe u v

/-- The tensor of two endomorphisms of the monoidal unit, transported
back to the unit, is their composite. -/
theorem unit_tensor_end {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (a b : (𝟙_ C) ⟶ (𝟙_ C)) :
    (λ_ (𝟙_ C)).inv ≫ (a ⊗ₘ b) ≫ (λ_ (𝟙_ C)).hom = a ≫ b := by
  have h : (a ▷ (𝟙_ C)) ≫ (λ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom ≫ a := by
    rw [unitors_equal]
    exact rightUnitor_naturality a
  rw [MonoidalCategory.tensorHom_def, Category.assoc, leftUnitor_naturality, reassoc_of% h]
  simp

/-- Tensoring two local frames multiplies the units measuring their
respective changes of frame. -/
theorem tensor_difference (X : Scheme.{u}) {M N : X.Modules} (p p' : trivial X ≅ M)
    (q q' : trivial X ≅ N) :
    differenceEquiv X (tensorFrame X p' q') (tensorFrame X p q) =
      differenceEquiv X p' p * differenceEquiv X q' q := by
  let a : Aut (trivial X) := p ≪≫ p'.symm
  let b : Aut (trivial X) := q ≪≫ q'.symm
  have h : (tensorFrame X p q ≪≫ (tensorFrame X p' q').symm : Aut (trivial X)) = b * a := by
    apply Aut.ext
    change ((λ_ (𝟙_ X.Modules)).inv ≫ (p.hom ⊗ₘ q.hom)) ≫
      (p'.inv ⊗ₘ q'.inv) ≫ (λ_ (𝟙_ X.Modules)).hom = (p.hom ≫ p'.inv) ≫ (q.hom ≫ q'.inv)
    rw [Category.assoc, tensorHom_comp_tensorHom_assoc, unit_tensor_end]
  change unitAut X (tensorFrame X p q ≪≫ (tensorFrame X p' q').symm) = unitAut X a * unitAut X b
  rw [h, map_mul, mul_comm]

end PhilipponTensorFrames
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory
open PhilipponEtaleFrameSections PhilipponEtaleFramePresheaf PhilipponEtaleFrameTorsor
open PhilipponTorsorSectionFibers PhilipponTorsorClassification
open PhilipponTorsorPresheafDifference
open PhilipponTensorFrames

namespace PhilipponEtaleFrameTensorExtension
universe u v w

private def pairMap {C : Type u} [Category.{v} C] {G : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    {D₁ D₂ E₁ E₂ : Difference G} (f₁ : D₁.P ⟶ E₁.P) (f₂ : D₂.P ⟶ E₂.P) :
    (pair D₁ D₂).P ⟶ (pair E₁ E₂).P where
  app U := ↾fun p => (f₁.app U p.1, f₂.app U p.2)
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro p
    change (f₁.app V (D₁.P.map f p.1), f₂.app V (D₂.P.map f p.2)) =
      (E₁.P.map f (f₁.app U p.1), E₂.P.map f (f₂.app U p.2))
    exact Prod.ext (NatTrans.naturality_apply f₁ f p.1) (NatTrans.naturality_apply f₂ f p.2)

variable {X : Scheme.{u}} {M N L : X.Modules}

theorem tensorOn_diff (e : M ⊗ N ≅ L) (U : X.Etale)
    (p p' : Frame M U) (q q' : Frame N U) :
    diff L U (tensorOn e U p q) (tensorOn e U p' q') = diff M U p p' + diff N U q q' := by
  let c := (Functor.Monoidal.μIso (Scheme.Modules.pullback U.hom) M N) ≪≫
    (Scheme.Modules.pullback U.hom).mapIso e
  change Additive.ofMul (PhilipponFrameUnits.differenceEquiv U.left
    (tensorFrame U.left p' q' ≪≫ c) (tensorFrame U.left p q ≪≫ c)) =
    Additive.ofMul (PhilipponFrameUnits.differenceEquiv U.left p' p *
      PhilipponFrameUnits.differenceEquiv U.left q' q)
  apply congrArg Additive.ofMul
  rw [PhilipponFramePullback.difference_postcompose, tensor_difference]

def mapOnFrames (e : M ⊗ N ≅ L) :
    (pair (difference M) (difference N)).P ⟶ presheaf L where
  app U := ↾fun p => tensorOn e U.unop p.1 p.2
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro p
    exact (Scheme.etaleFrame_tensor_restrict e f.unop p.1 p.2).symm

theorem combines (P : Presentation M) (Q : Presentation N) (R : Presentation L)
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (e : M ⊗ N ≅ L) : Combines P.torsor Q.torsor R.torsor := by
  let η : (pair (difference M) (difference N)).P ⟶ (pair P.torsor.D Q.torsor.D).P :=
    pairMap (D₁ := difference M) (D₂ := difference N) (E₁ := P.torsor.D) (E₂ := Q.torsor.D)
      P.frames Q.frames
  refine PhilipponTorsorMorphismExtension.exists_extension
    (D := pair (difference M) (difference N)) (E := pair P.torsor.D Q.torsor.D) (B := R.torsor)
    η (fun U => pair_presence _ _ U (locally_nonempty M hM U) (locally_nonempty N hN U))
    (fun U ⟨p⟩ => ?_) (fun U p q => ?_) (mapOnFrames e ≫ R.frames) (fun U p q => ?_)
  · exact (P.bijective U ⟨p.1⟩).prodMap (Q.bijective U ⟨p.2⟩)
  · change P.torsor.D.diff U (P.frames.app U p.1) (P.frames.app U q.1) +
      Q.torsor.D.diff U (Q.frames.app U p.2) (Q.frames.app U q.2) =
      diff M U.unop p.1 q.1 + diff N U.unop p.2 q.2
    rw [P.diff_eq, Q.diff_eq]
  · change R.torsor.D.diff U (R.frames.app U (tensorOn e U.unop p.1 p.2))
        (R.frames.app U (tensorOn e U.unop q.1 q.2)) =
      diff M U.unop p.1 q.1 + diff N U.unop p.2 q.2
    rw [R.diff_eq]
    exact tensorOn_diff e U.unop p.1 q.1 p.2 q.2

end PhilipponEtaleFrameTensorExtension
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
open PhilipponTorsorSectionFibers PhilipponTorsorFiberComparison PhilipponTorsorClassification
open PhilipponEtaleFrameTorsor
universe u

theorem solution (X : Scheme.{u}) :
    ∃ F : {M : X.Modules // Scheme.Modules.IsInvertible M} → Torsor (PhilipponKummerSequence.units X),
      (∀ A : Torsor (PhilipponKummerSequence.units X), ∃ M, Equivalent (F M) A) ∧
      (∀ M N, Equivalent (F M) (F N) ↔ toSkeleton M.val = toSkeleton N.val) ∧
      ∀ M N P, toSkeleton P.val = toSkeleton M.val * toSkeleton N.val →
        Combines (F M) (F N) (F P) := by
  let P (M : {M : X.Modules // Scheme.Modules.IsInvertible M}) : Presentation M.val :=
    chosenPresentation M.val M.property
  refine ⟨fun M => (P M).torsor, ?_, ?_, ?_⟩
  · intro A
    obtain ⟨M, hM, Q, rfl⟩ := Scheme.exists_etaleFrame_presentation_of_torsor X A
    let L : {M : X.Modules // Scheme.Modules.IsInvertible M} := ⟨M, hM⟩
    exact ⟨L, PhilipponEtaleFrameIsomorphism.equivalent_of_iso (Iso.refl M) hM
      (P L).frames Q.frames (P L).diff_eq (P L).bijective Q.diff_eq⟩
  · intro M N
    rw [toSkeleton_eq_toSkeleton_iff]
    constructor
    · exact PhilipponEtaleFrameGlobalRecovery.nonempty_iso (P M) (P N) M.property N.property
    · rintro ⟨e⟩
      exact PhilipponEtaleFrameIsomorphism.equivalent_of_iso e M.property
        (P M).frames (P N).frames (P M).diff_eq (P M).bijective (P N).diff_eq
  · intro M N L h
    rw [← Skeleton.toSkeleton_tensorObj] at h
    let e : M.val ⊗ N.val ≅ L.val := (toSkeleton_eq_toSkeleton_iff.mp h.symm).some
    exact PhilipponEtaleFrameTensorExtension.combines (P M) (P N) (P L) M.property N.property e

#print axioms PhilipponEtaleFrameGlobalRecovery.nonempty_iso
#print axioms PhilipponEtaleFrameIsomorphism.equivalent_of_iso
#print axioms solution

end
end
