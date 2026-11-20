-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_etaleFrame_presentation_of_torsor
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-19T15:32:21.278176+00:00
-- url     : https://prove2.me/submissions/2cbe9ae9-6754-4f0f-b570-5cc144703cb8

import Definitions.Def_AlgebraicGeometry_EtaleFrameTorsorCompletion
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_etaleFrame_presentation_spec
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_etaleFrame_presentation_of_zariski_sections

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory

namespace PhilipponSmallEtaleOpenImmersion
universe u
variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

/-- View an étale scheme over the open subscheme as one over the ambient scheme. -/
def along : Y.Etale ⥤ X.Etale where
  obj U := Scheme.Etale.mk (U.hom ≫ f)
  map {U V} a := MorphismProperty.Over.homMk a.left
    ((Category.assoc a.left V.hom f).symm.trans
      (congrArg (· ≫ f) (MorphismProperty.Over.w a)))
  map_id _ := MorphismProperty.Over.Hom.ext rfl
  map_comp _ _ := MorphismProperty.Over.Hom.ext rfl

instance : (along f).Faithful where
  map_injective h := MorphismProperty.Over.Hom.ext (congrArg (fun a => a.left) h)

instance : (along f).Full where
  map_surjective {U V} a := by
    have h : a.left ≫ (V.hom ≫ f) = U.hom ≫ f := MorphismProperty.Over.w a
    rw [← Category.assoc] at h
    exact ⟨MorphismProperty.Over.homMk a.left ((cancel_mono f).mp h),
      MorphismProperty.Over.Hom.ext rfl⟩

/-- The source of an arrow into an object over the open subscheme is itself
an étale scheme over that open subscheme. -/
def liftObj {V : X.Etale} {U : Y.Etale} (a : V ⟶ (along f).obj U) : Y.Etale :=
  Scheme.Etale.mk (a.left ≫ U.hom)

def liftIso {V : X.Etale} {U : Y.Etale} (a : V ⟶ (along f).obj U) :
    (along f).obj (liftObj f a) ≅ V :=
  MorphismProperty.Over.isoMk (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.id_comp]; exact
      (MorphismProperty.Over.w a).symm.trans (Category.assoc a.left U.hom f).symm)

def liftArrow {V : X.Etale} {U : Y.Etale} (a : V ⟶ (along f).obj U) :
    liftObj f a ⟶ U := MorphismProperty.Over.homMk a.left rfl

theorem along_liftArrow {V : X.Etale} {U : Y.Etale} (a : V ⟶ (along f).obj U) :
    (along f).map (liftArrow f a) = (liftIso f a).hom ≫ a :=
  MorphismProperty.Over.Hom.ext (Category.id_comp a.left).symm

theorem coverPreserving : CoverPreserving Y.smallEtaleTopology X.smallEtaleTopology (along f) := by
  constructor
  intro W S hS
  obtain ⟨U, hOver, hEtale, hle⟩ := (Scheme.mem_smallGrothendieckTopology W S).mp hS
  let : U.Over Y := hOver
  let V (i : U.I₀) := (U.X i).asOverProp Y (hEtale i)
  let r (i : U.I₀) : V i ⟶ W := (U.f i).asOverProp Y
  have hc : Sieve.ofArrows (fun i => (along f).obj (V i)) (fun i => (along f).map (r i))
      ∈ X.smallEtaleTopology ((along f).obj W) := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun i => (along f).map (r i))).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨z, hz⟩ := U.covers x
    exact ⟨U.idx x, z, hz⟩
  apply X.smallEtaleTopology.superset_covering _ hc
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨i⟩
  exact S.image_mem_functorPushforward (along f) (hle _ _ ⟨i⟩)

instance : (along f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfDownwardsClosed X.smallEtaleTopology (along f)
      (fun a => ⟨liftObj f a, liftIso f a⟩))
    (coverPreserving f)

theorem pullback_cover {W : Y.Etale} (S : Sieve ((along f).obj W))
    (hS : S ∈ X.smallEtaleTopology ((along f).obj W)) :
    S.functorPullback (along f) ∈ Y.smallEtaleTopology W := by
  obtain ⟨U, hOver, hEtale, hle⟩ :=
    (Scheme.mem_smallGrothendieckTopology ((along f).obj W) S).mp hS
  let : U.Over X := hOver
  let V (i : U.I₀) := (U.X i).asOverProp X (hEtale i)
  let a (i : U.I₀) : V i ⟶ (along f).obj W := (U.f i).asOverProp X
  let V' (i : U.I₀) := liftObj f (a i)
  let r (i : U.I₀) : V' i ⟶ W := liftArrow f (a i)
  have hc : Sieve.ofArrows V' r ∈ Y.smallEtaleTopology W := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff r).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨z, hz⟩ := U.covers x
    exact ⟨U.idx x, z, hz⟩
  apply Y.smallEtaleTopology.superset_covering _ hc
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨i⟩
  change S ((along f).map (r i))
  rw [along_liftArrow f (a i)]
  exact S.downward_closed (hle _ _ ⟨i⟩) _

end PhilipponSmallEtaleOpenImmersion
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponSmallEtaleOpenImmersion PhilipponTorsorPresheafDifference
open PhilipponTorsorSectionFibers PhilipponTorsorInvariantDescent

namespace PhilipponEtaleTorsorOpenRestriction
universe u
variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable (A : Torsor (PhilipponKummerSequence.units X))

/-- The units torsor restricted to an open subscheme uses the same sections
on the same underlying étale schemes. -/
def restrict : Torsor (PhilipponKummerSequence.units Y) where
  D :=
    { P := (along f).op ⋙ A.D.P
      diff U := A.D.diff ((along f).op.obj U)
      diff_add_diff U := A.D.diff_add_diff ((along f).op.obj U)
      map_diff i := A.D.map_diff ((along f).op.map i) }
  isSheaf := (isSheaf_iff_isSheaf_of_type _ _).2
    ((along f).op_comp_isSheaf_of_types Y.smallEtaleTopology X.smallEtaleTopology ⟨A.D.P, A.isSheaf⟩)
  locally_nonempty U := pullback_cover f (presence A.D.P ((along f).obj U))
    (A.locally_nonempty ((along f).obj U))
  diff_bijective U := A.diff_bijective ((along f).op.obj U)

end PhilipponEtaleTorsorOpenRestriction
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponTorsorSectionFibers PhilipponEtaleFrameTorsor

namespace PhilipponEtaleTorsorZariskiLocal
universe u

abbrev openObject {X : Scheme.{u}} (U : X.Opens) : X.Etale := Scheme.Etale.mk U.ι

/-- Effectivity on affine spectra yields Zariski-local sections of every
units torsor on the small étale site. -/
theorem exists_open_section
    (ha : ∀ (R : CommRingCat.{u}) (B : Torsor (PhilipponKummerSequence.units (Spec R))),
      ∃ (M : (Spec R).Modules) (_ : Scheme.Modules.IsInvertible M)
        (P : Presentation M), P.torsor = B)
    {X : Scheme.{u}} (A : Torsor (PhilipponKummerSequence.units X)) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty (A.D.P.obj (op (openObject U))) := by
  let C := X.affineOpenCover
  let i := C.idx x
  let R := C.X i
  let f : Spec R ⟶ X := C.f i
  let : IsOpenImmersion f := C.openCover.map_prop i
  obtain ⟨y, hy⟩ := C.covers x
  let B := PhilipponEtaleTorsorOpenRestriction.restrict f A
  obtain ⟨M, hM, P, hP⟩ := ha R B
  obtain ⟨W, hW, ⟨t⟩⟩ := hM.exists_trivialization y
  have hsec : Nonempty (B.D.P.obj (op (openObject W))) := by
    rw [← hP]
    exact ⟨P.frames.app (op (openObject W)) t.symm⟩
  let g := W.ι ≫ f
  let U := g.opensRange
  let b : openObject U ⟶ Scheme.Etale.mk g :=
    MorphismProperty.Over.homMk g.isoOpensRange.inv g.isoOpensRange_inv_comp
  obtain ⟨s⟩ := hsec
  have s' : A.D.P.obj (op (Scheme.Etale.mk g)) := s
  exact ⟨U, ⟨⟨y, hW⟩, hy⟩, ⟨A.D.P.map b.op s'⟩⟩

end PhilipponEtaleTorsorZariskiLocal
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MonoidalCategory
open PhilipponTorsorSectionFibers PhilipponEtaleFrameTorsor PhilipponEtaleFrameSections
open PhilipponTensorFrames
universe u

theorem solution (X : Scheme.{u}) (A : Torsor (PhilipponKummerSequence.units X)) :
    ∃ (M : X.Modules) (_ : Scheme.Modules.IsInvertible M) (P : Presentation M), P.torsor = A := by
  refine Scheme.exists_etaleFrame_presentation_of_zariski_sections X A ?_
  exact PhilipponEtaleTorsorZariskiLocal.exists_open_section
    Scheme.exists_etaleFrame_presentation_spec A

#print axioms PhilipponEtaleTorsorZariskiLocal.exists_open_section
#print axioms solution
