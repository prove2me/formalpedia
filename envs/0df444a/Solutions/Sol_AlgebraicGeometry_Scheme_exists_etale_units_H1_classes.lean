-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_etale_units_H1_classes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-18T21:52:31.535909+00:00
-- url     : https://prove2.me/submissions/79f19a17-ef7d-4f18-8db9-9e17ae1e114b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_SmallEtaleUnits
import Definitions.Def_AlgebraicGeometry_AbelianSheafTorsors
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_etale_units_frame_torsors

section
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open CategoryTheory Opposite

namespace PhilipponTorsorPresheafDifference
universe u v w
variable {C : Type u} [Category.{v} C]

private def augmentation (T : Type w) : FreeAbelianGroup T →+ ℤ :=
  FreeAbelianGroup.lift (fun _ => 1)

private theorem augmentation_map {A B : Type w} (f : A → B) (z : FreeAbelianGroup A) :
    augmentation B (FreeAbelianGroup.map f z) = augmentation A z :=
  (FreeAbelianGroup.lift_comp f (fun _ => (1 : ℤ)) z).symm

/-- The subgroup of degree-zero formal sums on each section set. -/
def degreeZero (P : Cᵒᵖ ⥤ Type w) : Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj U := AddCommGrpCat.of (augmentation (P.obj U)).ker
  map f := AddCommGrpCat.ofHom
    { toFun := fun z => ⟨FreeAbelianGroup.map (P.map f) z.val,
        (augmentation_map (P.map f) z.val).trans z.property⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ a.val b.val) }
  map_id U := by
    apply AddCommGrpCat.ext
    intro z
    apply Subtype.ext
    change FreeAbelianGroup.map (P.map (𝟙 U)) z.val = z.val
    rw [P.map_id]
    exact FreeAbelianGroup.map_id_apply z.val
  map_comp f g := by
    apply AddCommGrpCat.ext
    intro z
    apply Subtype.ext
    change FreeAbelianGroup.map (P.map (f ≫ g)) z.val =
      FreeAbelianGroup.map (P.map g) (FreeAbelianGroup.map (P.map f) z.val)
    rw [P.map_comp]
    exact FreeAbelianGroup.map_comp_apply (f := P.map f) (g := P.map g) z.val

def inclusion (P : Cᵒᵖ ⥤ Type w) : degreeZero P ⟶ P ⋙ AddCommGrpCat.free where
  app U := AddCommGrpCat.ofHom (AddSubgroup.subtype (augmentation (P.obj U)).ker)
  naturality _ _ _ := rfl

instance (P : Cᵒᵖ ⥤ Type w) : Mono (inclusion P) := by
  letI (U : Cᵒᵖ) : Mono ((inclusion P).app U) :=
    (AddCommGrpCat.mono_iff_injective _).mpr Subtype.val_injective
  exact NatTrans.mono_of_mono_app _

namespace Difference
variable {G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (D : Difference G)

private def atAnchor (U : Cᵒᵖ) (p : D.P.obj U) : FreeAbelianGroup (D.P.obj U) →+ G.obj U :=
  FreeAbelianGroup.lift (fun q => D.diff U q p)

private theorem atAnchor_eq (U : Cᵒᵖ) (p q : D.P.obj U) (z : (degreeZero D.P).obj U) :
    D.atAnchor U p z.val = D.atAnchor U q z.val := by
  let c : ℤ →+ G.obj U := AddMonoidHom.mk' (fun a : ℤ => a • D.diff U q p)
    (fun a b => add_zsmul _ a b)
  have h : D.atAnchor U p = D.atAnchor U q + c.comp (augmentation (D.P.obj U)) := by
    apply FreeAbelianGroup.lift_ext
    intro x
    simp only [atAnchor, FreeAbelianGroup.lift_apply_of, AddMonoidHom.add_apply,
      AddMonoidHom.comp_apply, augmentation]
    change D.diff U x p = D.diff U x q + (1 : ℤ) • D.diff U q p
    rw [one_zsmul, D.diff_add_diff]
  have e := DFunLike.congr_fun h z.val
  change D.atAnchor U p z.val = D.atAnchor U q z.val + c (augmentation (D.P.obj U) z.val) at e
  have hz : augmentation (D.P.obj U) z.val = 0 := z.property
  rwa [hz, map_zero, add_zero] at e

private def component (U : Cᵒᵖ) : (degreeZero D.P).obj U →+ G.obj U := by
  classical
  exact if h : Nonempty (D.P.obj U) then
    (D.atAnchor U h.some).comp (AddSubgroup.subtype (augmentation (D.P.obj U)).ker)
  else 0

private theorem component_eq (U : Cᵒᵖ) (p : D.P.obj U) (z : (degreeZero D.P).obj U) :
    D.component U z = D.atAnchor U p z.val := by
  have hp : Nonempty (D.P.obj U) := ⟨p⟩
  simp only [component, dif_pos hp, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype]
  exact D.atAnchor_eq U _ _ z

private theorem free_eq_zero_of_empty {T : Type w} [IsEmpty T] (z : FreeAbelianGroup T) : z = 0 := by
  induction z using FreeAbelianGroup.induction_on with
  | zero => rfl
  | of p => exact isEmptyElim p
  | neg p => exact isEmptyElim p
  | add a b ha hb => rw [ha, hb, add_zero]

/-- The formal sum of differences on degree-zero sums is independent of
the anchor, so it commutes with restriction. -/
def differenceMap : degreeZero D.P ⟶ G where
  app U := AddCommGrpCat.ofHom (D.component U)
  naturality U V f := by
    classical
    apply AddCommGrpCat.ext
    intro z
    change D.component V ((degreeZero D.P).map f z) = G.map f (D.component U z)
    by_cases h : Nonempty (D.P.obj U)
    · let p := h.some
      rw [D.component_eq U p, D.component_eq V (D.P.map f p)]
      have e : (D.atAnchor V (D.P.map f p)).comp (FreeAbelianGroup.map (D.P.map f)) =
          (G.map f).hom.comp (D.atAnchor U p) := by
        apply FreeAbelianGroup.lift_ext
        intro x
        simp only [AddMonoidHom.comp_apply, FreeAbelianGroup.map_of_apply,
          atAnchor, FreeAbelianGroup.lift_apply_of]
        exact (D.map_diff f x p).symm
      exact DFunLike.congr_fun e z.val
    · letI : IsEmpty (D.P.obj U) := not_nonempty_iff.mp h
      have hz : z = 0 := Subtype.ext (free_eq_zero_of_empty z.val)
      simp [hz]

private def formalDifference (P : Cᵒᵖ ⥤ Type w) (U : Cᵒᵖ) (p q : P.obj U) :
    (degreeZero P).obj U :=
  ⟨FreeAbelianGroup.of p - FreeAbelianGroup.of q, by
    change augmentation _ (FreeAbelianGroup.of p - FreeAbelianGroup.of q) = 0
    simp [augmentation]⟩

theorem differenceMap_formalDifference (U : Cᵒᵖ) (p q : D.P.obj U) :
    D.differenceMap.app U (formalDifference D.P U p q) = D.diff U p q := by
  change D.component U (formalDifference D.P U p q) = _
  rw [D.component_eq U q]
  have h : D.diff U q q = 0 := by
    have h' := D.diff_add_diff U q q q
    exact add_left_cancel (h'.trans (add_zero _).symm)
  simp [formalDifference, atAnchor, h]

private def generator (P : Cᵒᵖ ⥤ Type w) : P ⟶ (P ⋙ AddCommGrpCat.free) ⋙ forget AddCommGrpCat where
  app U := ↾(FreeAbelianGroup.of : P.obj U → _)
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- Into an injective abelian presheaf, a map out of the group of
differences extends to coordinates on the original section sets. -/
theorem exists_coordinates {I : Cᵒᵖ ⥤ AddCommGrpCat.{w}} [Injective I] (j : G ⟶ I) :
    ∃ e : D.P ⟶ I ⋙ forget AddCommGrpCat,
      ∀ U (p q : D.P.obj U), e.app U p - e.app U q = j.app U (D.diff U p q) := by
  let g := Injective.factorThru (D.differenceMap ≫ j) (inclusion D.P)
  let e := generator D.P ≫ Functor.whiskerRight g (forget AddCommGrpCat)
  refine ⟨e, fun U p q => ?_⟩
  have hf := Injective.comp_factorThru (D.differenceMap ≫ j) (inclusion D.P)
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app hf U) (formalDifference D.P U p q)
  change g.app U (FreeAbelianGroup.of p - FreeAbelianGroup.of q) =
    j.app U (D.differenceMap.app U (formalDifference D.P U p q)) at h
  change g.app U (FreeAbelianGroup.of p) - g.app U (FreeAbelianGroup.of q) = _
  rwa [map_sub, D.differenceMap_formalDifference] at h

end Difference
end PhilipponTorsorPresheafDifference
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory Opposite

namespace PhilipponTorsorInvariantDescent
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A natural quantity independent of the local section descends through
the covering sieve where the presheaf has sections. -/
theorem existsUnique_of_invariant {P : Cᵒᵖ ⥤ Type w} (Q : Sheaf J (Type w))
    (c : P ⟶ Q.obj) (hinv : ∀ U (x y : P.obj U), c.app U x = c.app U y)
    {T : C} (hT : presence P T ∈ J T) :
    ∃! q : Q.obj.obj (op T), ∀ (V : C) (f : V ⟶ T) (x : P.obj (op V)),
      Q.obj.map f.op q = c.app (op V) x := by
  classical
  let R := presence P T
  let a : R.arrows.FamilyOfElements Q.obj := fun V _ hf => c.app (op V) hf.some
  have ha : a.Compatible := (Presieve.compatible_iff_sieveCompatible a).mpr (by
    intro V W f g hf
    change c.app (op W) (R.downward_closed hf g).some = Q.obj.map g.op (c.app (op V) hf.some)
    rw [hinv (op W) _ (P.map g.op hf.some)]
    exact NatTrans.naturality_apply c g.op hf.some)
  obtain ⟨q, hq, hun⟩ := Q.property.isSheafFor R hT a ha
  refine ⟨q, ?_, ?_⟩
  · intro V f x
    let hf : R f := ⟨x⟩
    exact (hq f hf).trans (hinv _ _ x)
  · intro r hr
    exact hun r fun V f hf => hr V f hf.some

end PhilipponTorsorInvariantDescent
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace PhilipponTorsorSectionExactness
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}]

def evaluation (U : Cᵒᵖ) : Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
  sheafToPresheaf J AddCommGrpCat ⋙ (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj U

/-- Taking sections of a short exact sequence preserves the kernel
condition even when the last section map need not be surjective. -/
theorem exact_on_sections (S : ShortComplex (Sheaf J AddCommGrpCat.{w}))
    (hS : S.ShortExact) (U : Cᵒᵖ) :
    Function.Exact (S.f.hom.app U) (S.g.hom.app U) := by
  let E := evaluation (J := J) U
  letI : PreservesLimits E := inferInstanceAs (PreservesLimits
    (sheafToPresheaf J AddCommGrpCat ⋙ (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj U))
  letI : E.PreservesZeroMorphisms := inferInstanceAs
    ((sheafToPresheaf J AddCommGrpCat ⋙ (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj U).PreservesZeroMorphisms)
  exact (ShortComplex.ab_exact_iff_function_exact _).mp
    (hS.exact.map_of_mono_of_preservesKernel E hS.mono_f (by infer_instance))

theorem injective_on_sections (S : ShortComplex (Sheaf J AddCommGrpCat.{w}))
    (hS : S.ShortExact) (U : Cᵒᵖ) : Function.Injective (S.f.hom.app U) := by
  letI := hS.mono_f
  letI : Mono S.f.hom := inferInstanceAs (Mono ((sheafToPresheaf J AddCommGrpCat).map S.f))
  exact (AddCommGrpCat.mono_iff_injective _).mp (inferInstance : Mono (S.f.hom.app U))

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]

/-- Choose an actual injective presentation and its cokernel in the
abelian category of sheaves. -/
def injectiveSequence (G : Sheaf J AddCommGrpCat.{w}) : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
  ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G)) (cokernel.condition _)

instance (G : Sheaf J AddCommGrpCat.{w}) : Injective (injectiveSequence G).X₂ :=
  inferInstanceAs (Injective (Injective.under G))

theorem injectiveSequence_shortExact (G : Sheaf J AddCommGrpCat.{w}) :
    (injectiveSequence G).ShortExact := by
  letI : Mono (injectiveSequence G).f := inferInstanceAs (Mono (Injective.ι G))
  letI : Epi (injectiveSequence G).g := inferInstanceAs (Epi (cokernel.π (Injective.ι G)))
  exact { exact := ShortComplex.exact_cokernel (Injective.ι G) }

end PhilipponTorsorSectionExactness
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace PhilipponEtaleH1Boundary
universe u v w w'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- For a short exact sequence with injective middle sheaf, first
cohomology of the kernel is the cokernel on actual global sections. -/
theorem exists_section_boundary {T : C} (hT : IsTerminal T)
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact) [Injective S.X₂] :
    ∃ δ : S.X₃.obj.obj (op T) →+ S.X₁.H 1,
      Function.Surjective δ ∧ Function.Exact (S.g.hom.app (op T)).hom δ := by
  let A := (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))
  let d : S.X₃.H 0 →+ S.X₁.H 1 := hS.extClass.postcomp A (show 0 + 1 = 1 by decide)
  let e₃ := Sheaf.H.equiv₀ S.X₃ hT
  let e₂ := Sheaf.H.equiv₀ S.X₂ hT
  have hsurj : Function.Surjective d := by
    intro z
    exact Ext.covariant_sequence_exact₁ A hS z (Ext.eq_zero_of_injective _) (show 0 + 1 = 1 by decide)
  have hexact : Function.Exact (Sheaf.H.map S.g 0) d :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.covariant_sequence_exact₃' A hS 0 1 (by decide))
  let δ := d.comp e₃.symm.toAddMonoidHom
  refine ⟨δ, hsurj.comp e₃.symm.surjective, fun x => ?_⟩
  change d (e₃.symm x) = 0 ↔ x ∈ Set.range (S.g.hom.app (op T)).hom
  rw [hexact]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e₂ y, ?_⟩
    rw [Sheaf.H.equiv₀_naturality, hy, AddEquiv.apply_symm_apply]
  · rintro ⟨y, rfl⟩
    exact ⟨e₂.symm y, Sheaf.H.equiv₀_symm_naturality hT S.g y⟩

end PhilipponEtaleH1Boundary
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open CategoryTheory Opposite
open PhilipponTorsorInvariantDescent PhilipponTorsorPresheafDifference PhilipponTorsorSectionExactness

namespace PhilipponTorsorCohomologyRepresentative
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} {T : C}

/-- A system of local coordinates in the middle sheaf and its descended
value in the quotient sheaf. -/
structure Coordinates (D : Difference S.X₁.obj) (T : C) where
  lift : D.P ⟶ S.X₂.obj ⋙ forget AddCommGrpCat
  value : S.X₃.obj.obj (op T)
  diff (U : Cᵒᵖ) (x y : D.P.obj U) :
    lift.app U x - lift.app U y = S.f.hom.app U (D.diff U x y)
  desc (U : C) (f : U ⟶ T) (x : D.P.obj (op U)) :
    S.X₃.obj.map f.op value = S.g.hom.app (op U) (lift.app (op U) x)

variable [HasSheafify J AddCommGrpCat.{w}]

/-- The local coordinates in an injective sheaf give a global section of
the quotient because their images there agree on each object. -/
theorem exists_coordinates (hS : S.ShortExact) [Injective S.X₂]
    (D : Difference S.X₁.obj) (hT : presence D.P T ∈ J T) : Nonempty (Coordinates D T) := by
  letI : Injective S.X₂.obj :=
    (sheafificationAdjunction J AddCommGrpCat).map_injective S.X₂ inferInstance
  obtain ⟨e, he⟩ := D.exists_coordinates S.f.hom
  let Q : Sheaf J (Type w) := (sheafCompose J (forget AddCommGrpCat.{w})).obj S.X₃
  let c : D.P ⟶ Q.obj := e ≫ Functor.whiskerRight S.g.hom (forget AddCommGrpCat)
  have hinv (U : Cᵒᵖ) (x y : D.P.obj U) : c.app U x = c.app U y := by
    change S.g.hom.app U (e.app U x) = S.g.hom.app U (e.app U y)
    apply sub_eq_zero.mp
    rw [← map_sub, he U x y]
    exact (exact_on_sections S hS U _).mpr ⟨D.diff U x y, rfl⟩
  obtain ⟨q, hq, _⟩ := existsUnique_of_invariant Q c hinv hT
  exact ⟨⟨e, q, he, hq⟩⟩

/-- Two coordinate systems differ by a global section of the middle
sheaf. Thus their quotient sections define the same class under any
boundary map exact at global sections. -/
theorem Coordinates.same_class {D : Difference S.X₁.obj} (a b : Coordinates D T)
    (hT : presence D.P T ∈ J T) {H : Type*} [AddCommGroup H]
    (δ : S.X₃.obj.obj (op T) →+ H) (hexact : Function.Exact (S.g.hom.app (op T)) δ) :
    δ a.value = δ b.value := by
  let I : Sheaf J (Type w) := (sheafCompose J (forget AddCommGrpCat.{w})).obj S.X₂
  let c : D.P ⟶ I.obj :=
    { app U := ↾fun z => a.lift.app U z - b.lift.app U z
      naturality U V f := by
        apply ConcreteCategory.hom_ext
        intro z
        change a.lift.app V (D.P.map f z) - b.lift.app V (D.P.map f z) =
          S.X₂.obj.map f (a.lift.app U z - b.lift.app U z)
        rw [map_sub]
        exact congrArg₂ (· - ·) (NatTrans.naturality_apply a.lift f z)
          (NatTrans.naturality_apply b.lift f z) }
  have hinv (U : Cᵒᵖ) (x y : D.P.obj U) : c.app U x = c.app U y := by
    change a.lift.app U x - b.lift.app U x = a.lift.app U y - b.lift.app U y
    apply sub_eq_zero.mp
    have he : (a.lift.app U x - b.lift.app U x) - (a.lift.app U y - b.lift.app U y) =
      (a.lift.app U x - a.lift.app U y) - (b.lift.app U x - b.lift.app U y) := by abel
    rw [he, a.diff, b.diff, sub_self]
  obtain ⟨r, hr, _⟩ := existsUnique_of_invariant I c hinv hT
  change ↥(S.X₂.obj.obj (op T)) at r
  let Q : Sheaf J (Type w) := (sheafCompose J (forget AddCommGrpCat.{w})).obj S.X₃
  have hq : S.g.hom.app (op T) r = a.value - b.value := by
    apply (Q.property.isSheafFor _ hT).isSeparatedFor.ext
    intro U f hf
    let z : D.P.obj (op U) := hf.some
    change S.X₃.obj.map f.op (S.g.hom.app (op T) r) =
      S.X₃.obj.map f.op (a.value - b.value)
    have hnat := ConcreteCategory.congr_hom (S.g.hom.naturality f.op) r
    change S.g.hom.app (op U) (S.X₂.obj.map f.op r) =
      S.X₃.obj.map f.op (S.g.hom.app (op T) r) at hnat
    rw [← hnat, map_sub, a.desc U f z, b.desc U f z]
    have h := hr U f z
    change S.X₂.obj.map f.op r = a.lift.app (op U) z - b.lift.app (op U) z at h
    rw [h, map_sub]
  have hz := (hexact (a.value - b.value)).mpr ⟨r, hq⟩
  rwa [map_sub, sub_eq_zero] at hz

end PhilipponTorsorCohomologyRepresentative
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open PhilipponTorsorInvariantDescent PhilipponTorsorPresheafDifference PhilipponTorsorSectionExactness

namespace PhilipponTorsorSectionFibers
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
variable {T : C} (hT : IsTerminal T) (q : S.X₃.obj.obj (op T))

/-- The fibre of the section map over a global section of the last sheaf. -/
def fiber : Cᵒᵖ ⥤ Type w where
  obj U := {a : S.X₂.obj.obj U // S.g.hom.app U a = S.X₃.obj.map (hT.from U.unop).op q}
  map {U V} f := ↾fun a => ⟨S.X₂.obj.map f a.val, by
    have h := ConcreteCategory.congr_hom (S.g.hom.naturality f) a.val
    change S.g.hom.app V (S.X₂.obj.map f a.val) = S.X₃.obj.map f (S.g.hom.app U a.val) at h
    rw [h, a.property, ← comp_apply, ← Functor.map_comp]
    rw [show (hT.from U.unop).op ≫ f = (hT.from V.unop).op from
      Quiver.Hom.unop_inj (hT.hom_ext _ _)]⟩
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    change S.X₂.obj.map (𝟙 U) a.val = a.val
    rw [S.X₂.obj.map_id]
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    change S.X₂.obj.map (f ≫ g) a.val = S.X₂.obj.map g (S.X₂.obj.map f a.val)
    rw [S.X₂.obj.map_comp]
    rfl

def inclusion : fiber hT q ⟶ S.X₂.obj ⋙ forget AddCommGrpCat where
  app _ := ↾fun a => a.val
  naturality _ _ _ := rfl

theorem isSheaf_fiber : Presheaf.IsSheaf J (fiber hT q) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro U R hR a ha
  let I : Sheaf J (Type w) := (sheafCompose J (forget AddCommGrpCat.{w})).obj S.X₂
  let Q : Sheaf J (Type w) := (sheafCompose J (forget AddCommGrpCat.{w})).obj S.X₃
  let a' : R.arrows.FamilyOfElements I.obj := a.map (inclusion hT q)
  obtain ⟨b, hb, hun⟩ := I.property.isSheafFor R hR a' (ha.map (inclusion hT q))
  change ↥(S.X₂.obj.obj (op U)) at b
  have hb' : S.g.hom.app (op U) b = S.X₃.obj.map (hT.from U).op q := by
    apply (Q.property.isSheafFor R hR).isSeparatedFor.ext
    intro V f hf
    have h := ConcreteCategory.congr_hom (S.g.hom.naturality f.op) b
    have ha' : S.X₂.obj.map f.op b = (a f hf).val := hb f hf
    change S.g.hom.app (op V) (S.X₂.obj.map f.op b) =
      S.X₃.obj.map f.op (S.g.hom.app (op U) b) at h
    change S.X₃.obj.map f.op (S.g.hom.app (op U) b) =
      S.X₃.obj.map f.op (S.X₃.obj.map (hT.from U).op q)
    rw [← h, ha', (a f hf).property, ← comp_apply, ← Functor.map_comp, ← op_comp,
      hT.hom_ext (f ≫ _) _]
  refine ⟨⟨b, hb'⟩, ?_, ?_⟩
  · intro V f hf
    exact Subtype.ext (hb f hf)
  · intro t ht
    exact Subtype.ext (hun t.val fun V f hf => congrArg Subtype.val (ht f hf))

variable [HasSheafify J AddCommGrpCat.{w}] (hS : S.ShortExact)
include hS

private theorem has_difference (U : Cᵒᵖ) (x y : (fiber hT q).obj U) :
    ∃ z : S.X₁.obj.obj U, S.f.hom.app U z = x.val - y.val := by
  apply (exact_on_sections S hS U _).mp
  rw [map_sub, x.property, y.property, sub_self]

def differenceAt (U : Cᵒᵖ) (x y : (fiber hT q).obj U) : S.X₁.obj.obj U :=
  (has_difference hT q hS U x y).choose

@[simp] theorem differenceAt_image (U : Cᵒᵖ) (x y : (fiber hT q).obj U) :
    S.f.hom.app U (differenceAt hT q hS U x y) = x.val - y.val :=
  (has_difference hT q hS U x y).choose_spec

def difference : Difference S.X₁.obj where
  P := fiber hT q
  diff := differenceAt hT q hS
  diff_add_diff U x y z := by
    apply injective_on_sections S hS U
    simp only [map_add, differenceAt_image]
    abel
  map_diff {U V} f x y := by
    apply injective_on_sections S hS V
    have h := ConcreteCategory.congr_hom (S.f.hom.naturality f) (differenceAt hT q hS U x y)
    change S.f.hom.app V (S.X₁.obj.map f _) =
      S.X₂.obj.map f (S.f.hom.app U (differenceAt hT q hS U x y)) at h
    rw [h, differenceAt_image, differenceAt_image, map_sub]
    rfl

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

theorem fiber_locally_nonempty (U : C) : presence (fiber hT q) U ∈ J U := by
  letI : Epi S.g := hS.epi_g
  letI : Sheaf.IsLocallySurjective S.g :=
    (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{w}) S.g).mpr inferInstance
  have h := Presheaf.imageSieve_mem J S.g.hom (S.X₃.obj.map (hT.from U).op q)
  refine J.superset_covering ?_ h
  intro V f hf
  obtain ⟨a, ha⟩ := hf
  refine ⟨⟨a, ?_⟩⟩
  rw [ha, ← comp_apply, ← Functor.map_comp, ← op_comp, hT.hom_ext (f ≫ _) _]

theorem differenceAt_bijective (U : Cᵒᵖ) (p : (fiber hT q).obj U) :
    Function.Bijective (fun r => differenceAt hT q hS U r p) := by
  constructor
  · intro x y h
    apply Subtype.ext
    have h' : x.val - p.val = y.val - p.val :=
      (differenceAt_image hT q hS U x p).symm.trans
        ((congrArg (S.f.hom.app U).hom h).trans (differenceAt_image hT q hS U y p))
    simpa only [sub_add_cancel] using congrArg (· + p.val) h'
  · intro a
    have hz := (exact_on_sections S hS U (S.f.hom.app U a)).mpr ⟨a, rfl⟩
    let r : (fiber hT q).obj U := ⟨S.f.hom.app U a + p.val, by
      rw [map_add, hz, zero_add, p.property]⟩
    refine ⟨r, injective_on_sections S hS U ?_⟩
    rw [differenceAt_image]
    exact add_sub_cancel_right _ _

/-- Fibres of the epimorphism in a short exact sequence form actual
torsors under the first sheaf. -/
def torsor : Torsor S.X₁ where
  D := difference hT q hS
  isSheaf := isSheaf_fiber hT q
  locally_nonempty := fiber_locally_nonempty hT q hS
  diff_bijective := differenceAt_bijective hT q hS

end PhilipponTorsorSectionFibers
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open PhilipponTorsorInvariantDescent PhilipponTorsorCohomologyRepresentative
open PhilipponTorsorSectionFibers PhilipponTorsorSectionExactness

namespace PhilipponTorsorFiberComparison
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

theorem Equivalent.symm {G : Sheaf J AddCommGrpCat.{w}} {P Q : Torsor G}
    (h : Equivalent P Q) : Equivalent Q P := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun U p q => ?_⟩
  have hp : e.hom.app U (e.inv.app U p) = p :=
    ConcreteCategory.congr_hom (e.app U).inv_hom_id p
  have hq : e.hom.app U (e.inv.app U q) = q :=
    ConcreteCategory.congr_hom (e.app U).inv_hom_id q
  have hh := he U (e.inv.app U p) (e.inv.app U q)
  rw [hp, hq] at hh
  exact hh.symm

theorem Equivalent.trans {G : Sheaf J AddCommGrpCat.{w}} {P Q R : Torsor G}
    (h : Equivalent P Q) (k : Equivalent Q R) : Equivalent P R := by
  obtain ⟨e, he⟩ := h
  obtain ⟨f, hf⟩ := k
  exact ⟨e ≪≫ f, fun U p q => (hf U _ _).trans (he U p q)⟩

variable {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} {T : C}

def toFiber (hT : IsTerminal T) {P : Torsor S.X₁} (a : Coordinates P.D T) :
    P.D.P ⟶ fiber hT a.value where
  app U := ↾fun x => ⟨a.lift.app U x, (a.desc U.unop (hT.from U.unop) x).symm⟩
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    change a.lift.app V (P.D.P.map f x) = S.X₂.obj.map f (a.lift.app U x)
    exact NatTrans.naturality_apply a.lift f x

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The chosen local coordinates identify a torsor with the fibre over its
descended global section. Pointwise injectivity and local surjectivity
provide the isomorphism of sheaves. -/
theorem equivalent_fiber (hS : S.ShortExact) (hT : IsTerminal T) {P : Torsor S.X₁}
    (a : Coordinates P.D T) : Equivalent P (torsor hT a.value hS) := by
  let P' : Sheaf J (Type w) := ⟨P.D.P, P.isSheaf⟩
  let Q' : Sheaf J (Type w) := ⟨fiber hT a.value, isSheaf_fiber hT a.value⟩
  let f : P' ⟶ Q' := ⟨toFiber hT a⟩
  have hinj (U : Cᵒᵖ) : Function.Injective ((toFiber hT a).app U) := by
    intro p q h
    have h' : a.lift.app U p = a.lift.app U q := congrArg Subtype.val h
    apply (P.diff_bijective U q).injective
    apply injective_on_sections S hS U
    rw [← a.diff U p q, ← a.diff U q q, h']
  letI : Sheaf.IsLocallyInjective f :=
    Presheaf.isLocallyInjective_of_injective J (toFiber hT a) hinj
  letI hsur : Sheaf.IsLocallySurjective f := by
    constructor
    intro U z
    refine J.superset_covering ?_ (P.locally_nonempty U)
    intro V g hv
    obtain ⟨p⟩ := hv
    let z' : (fiber hT a.value).obj (op V) := (fiber hT a.value).map g.op z
    let w : (fiber hT a.value).obj (op V) := (toFiber hT a).app (op V) p
    obtain ⟨p', hp'⟩ := (P.diff_bijective (op V) p).surjective
      (differenceAt hT a.value hS (op V) z' w)
    have h := a.diff (op V) p' p
    change P.D.diff (op V) p' p = differenceAt hT a.value hS (op V) z' w at hp'
    rw [hp', differenceAt_image] at h
    have h' : a.lift.app (op V) p' - w.val = z'.val - w.val := h
    refine ⟨p', Subtype.ext ?_⟩
    change a.lift.app (op V) p' = z'.val
    simpa only [sub_add_cancel] using congrArg (· + w.val) h'
  letI : IsIso f := (Sheaf.isLocallyBijective_iff_isIso (A := Type w) f).mp ⟨inferInstance, hsur⟩
  let e := (sheafToPresheaf J (Type w)).mapIso (asIso f)
  refine ⟨e, fun U p q => ?_⟩
  apply injective_on_sections S hS U
  change S.f.hom.app U (differenceAt hT a.value hS U
    ((toFiber hT a).app U p) ((toFiber hT a).app U q)) = _
  rw [differenceAt_image]
  exact a.diff U p q

end PhilipponTorsorFiberComparison
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
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} {T : C}
variable [HasSheafify J AddCommGrpCat.{w}]

/-- Translating the coordinates by a global section changes the descended
quotient section by the image of that section. -/
def translate {D : Difference S.X₁.obj} (a : Coordinates D T) (hT : IsTerminal T)
    (q : S.X₃.obj.obj (op T)) (r : S.X₂.obj.obj (op T))
    (hr : S.g.hom.app (op T) r = a.value - q) : Coordinates D T where
  lift :=
    { app U := ↾fun x => a.lift.app U x - S.X₂.obj.map (hT.from U.unop).op r
      naturality U V f := by
        apply ConcreteCategory.hom_ext
        intro x
        change a.lift.app V (D.P.map f x) - S.X₂.obj.map (hT.from V.unop).op r =
          S.X₂.obj.map f (a.lift.app U x - S.X₂.obj.map (hT.from U.unop).op r)
        have hn : a.lift.app V (D.P.map f x) = S.X₂.obj.map f (a.lift.app U x) :=
          NatTrans.naturality_apply a.lift f x
        have hc : (hT.from U.unop).op ≫ f = (hT.from V.unop).op :=
          Quiver.Hom.unop_inj (hT.hom_ext _ _)
        rw [map_sub, hn, ← Functor.map_comp_apply, hc] }
  value := q
  diff U x y := by
    change (a.lift.app U x - S.X₂.obj.map (hT.from U.unop).op r) -
      (a.lift.app U y - S.X₂.obj.map (hT.from U.unop).op r) = _
    rw [← a.diff U x y]
    abel
  desc U f x := by
    change S.X₃.obj.map f.op q = S.g.hom.app (op U)
      (a.lift.app (op U) x - S.X₂.obj.map (hT.from U).op r)
    rw [hT.hom_ext (hT.from U) f, map_sub]
    have h := ConcreteCategory.congr_hom (S.g.hom.naturality f.op) r
    change S.g.hom.app (op U) (S.X₂.obj.map f.op r) =
      S.X₃.obj.map f.op (S.g.hom.app (op T) r) at h
    rw [h, hr, ← a.desc U f x, ← map_sub, sub_sub_cancel]

/-- Any difference-preserving map pulls a coordinate system back. -/
def pull {D E : Difference S.X₁.obj} (b : Coordinates E T) (f : D.P ⟶ E.P)
    (hf : ∀ (U : Cᵒᵖ) (p q : D.P.obj U),
      E.diff U (f.app U p) (f.app U q) = D.diff U p q) : Coordinates D T where
  lift := f ≫ b.lift
  value := b.value
  diff U p q := by
    change b.lift.app U (f.app U p) - b.lift.app U (f.app U q) = _
    rw [b.diff, hf]
  desc U g p := b.desc U g (f.app (op U) p)

def fiberCoordinates (hS : S.ShortExact) (hT : IsTerminal T)
    (q : S.X₃.obj.obj (op T)) : Coordinates (difference hT q hS) T where
  lift := inclusion hT q
  value := q
  diff U p r := (differenceAt_image hT q hS U p r).symm
  desc U f p := by
    change S.X₃.obj.map f.op q = S.g.hom.app (op U) p.val
    rw [p.property, hT.hom_ext f (hT.from U)]

theorem pair_presence {G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (D E : Difference G) (U : C)
    (hD : presence D.P U ∈ J U) (hE : presence E.P U ∈ J U) :
    presence (pair D E).P U ∈ J U := by
  apply J.superset_covering _ (J.intersection_covering hD hE)
  rintro V f ⟨⟨x⟩, ⟨y⟩⟩
  exact ⟨(x, y)⟩

def pairCoordinates {D E : Difference S.X₁.obj} (a : Coordinates D T)
    (b : Coordinates E T) : Coordinates (pair D E) T where
  lift :=
    { app U := ↾fun x => a.lift.app U x.1 + b.lift.app U x.2
      naturality U V f := by
        apply ConcreteCategory.hom_ext
        intro x
        change a.lift.app V (D.P.map f x.1) + b.lift.app V (E.P.map f x.2) =
          S.X₂.obj.map f (a.lift.app U x.1 + b.lift.app U x.2)
        rw [map_add]
        exact congrArg₂ (· + ·) (NatTrans.naturality_apply a.lift f x.1)
          (NatTrans.naturality_apply b.lift f x.2) }
  value := a.value + b.value
  diff U x y := by
    change (a.lift.app U x.1 + b.lift.app U x.2) -
      (a.lift.app U y.1 + b.lift.app U y.2) =
      S.f.hom.app U (D.diff U x.1 y.1 + E.diff U x.2 y.2)
    rw [add_sub_add_comm, a.diff, b.diff, map_add]
  desc U f x := by
    change S.X₃.obj.map f.op (a.value + b.value) =
      S.g.hom.app (op U) (a.lift.app (op U) x.1 + b.lift.app (op U) x.2)
    rw [map_add, map_add, a.desc U f x.1, b.desc U f x.2]

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The boundary for an injective presentation classifies actual torsors.
The assignment is surjective, and its fibres are precisely equivariant
isomorphism classes. -/
theorem exists_classification (hS : S.ShortExact) [Injective S.X₂] (hT : IsTerminal T)
    {H : Type w'} [AddCommGroup H] (δ : S.X₃.obj.obj (op T) →+ H)
    (hsur : Function.Surjective δ) (hex : Function.Exact (S.g.hom.app (op T)) δ) :
    ∃ c : Torsor S.X₁ → H, Function.Surjective c ∧
      (∀ P Q, c P = c Q ↔ Equivalent P Q) ∧
      (∀ P Q R, Combines P Q R → c R = c P + c Q) := by
  let a (P : Torsor S.X₁) : Coordinates P.D T :=
    (exists_coordinates hS P.D (P.locally_nonempty T)).some
  let c (P : Torsor S.X₁) := δ (a P).value
  refine ⟨c, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨q, rfl⟩ := hsur h
    let P := torsor hT q hS
    exact ⟨P, (a P).same_class (fiberCoordinates hS hT q) (P.locally_nonempty T) δ hex⟩
  · intro P Q
    constructor
    · intro h
      change δ (a P).value = δ (a Q).value at h
      have hz : δ ((a P).value - (a Q).value) = 0 := by rw [map_sub, h, sub_self]
      obtain ⟨r, hr⟩ := (hex _).mp hz
      let a' := translate (a P) hT (a Q).value r hr
      exact (equivalent_fiber hS hT a').trans (equivalent_fiber hS hT (a Q)).symm
    · rintro ⟨f, hf⟩
      exact (a P).same_class (pull (a Q) f.hom hf) (P.locally_nonempty T) δ hex
  · rintro P Q R ⟨m, hm⟩
    have h := (pull (a R) m hm).same_class (pairCoordinates (a P) (a Q))
      (pair_presence P.D Q.D T (P.locally_nonempty T) (Q.locally_nonempty T)) δ hex
    change δ (a R).value = δ ((a P).value + (a Q).value) at h
    exact h.trans (map_add δ _ _)

/-- First derived sheaf cohomology classifies torsors and adds the classes
of torsors related by a difference-additive map. -/
theorem exists_H1_classification [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] (G : Sheaf J AddCommGrpCat.{w})
    (hT : IsTerminal T) :
    ∃ c : Torsor G → G.H 1, Function.Surjective c ∧
      (∀ P Q, c P = c Q ↔ Equivalent P Q) ∧
      (∀ P Q R, Combines P Q R → c R = c P + c Q) := by
  let S := injectiveSequence G
  have hS := injectiveSequence_shortExact G
  obtain ⟨δ, hsur, hex⟩ := PhilipponEtaleH1Boundary.exists_section_boundary hT S hS
  exact exists_classification hS hT δ hsur hex

end PhilipponTorsorClassification
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponTorsorSectionFibers PhilipponTorsorFiberComparison PhilipponTorsorClassification
universe u

private def smallEtaleTerminal (X : Scheme.{u}) : IsTerminal (Scheme.Etale.mk (𝟙 X)) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal

theorem solution (X : Scheme.{u}) :
    ∃ c : {M : X.Modules // Scheme.Modules.IsInvertible M} →
        (PhilipponKummerSequence.units X).H 1,
      Function.Surjective c ∧
      (∀ M N, c M = c N ↔ toSkeleton M.val = toSkeleton N.val) ∧
      ∀ M N P, toSkeleton P.val = toSkeleton M.val * toSkeleton N.val → c P = c M + c N := by
  obtain ⟨F, hsur, hinj, hmul⟩ := AlgebraicGeometry.Scheme.exists_etale_units_frame_torsors X
  obtain ⟨c, hc, heq, hadd⟩ := exists_H1_classification (PhilipponKummerSequence.units X)
    (smallEtaleTerminal X)
  refine ⟨fun M => c (F M), ?_, fun M N => (heq (F M) (F N)).trans (hinj M N), ?_⟩
  · intro h
    obtain ⟨A, rfl⟩ := hc h
    obtain ⟨M, hM⟩ := hsur A
    exact ⟨M, (heq (F M) A).mpr hM⟩
  · intro M N P h
    exact hadd (F M) (F N) (F P) (hmul M N P h)

end
end
