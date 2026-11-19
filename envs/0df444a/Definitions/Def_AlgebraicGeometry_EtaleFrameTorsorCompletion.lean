-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleFrameTorsorCompletion
-- name    : AlgebraicGeometry_EtaleFrameTorsorCompletion
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-19T00:49:18.371686+00:00
-- url     : https://prove2.me/theorems/2ac36c24-4cb0-43c8-9989-1af515f4bb4c
-- title:
--   Chosen torsor of frames of an invertible module
-- statement:
--   For an invertible module on a scheme, this construction chooses a torsor under the small étale sheaf of units and a map from the local frames to its sections. The map preserves the change-of-frame unit and is bijective on every étale object on which the module has a frame.
-- source:
--   Stacks Project, Section 59.24, https://stacks.math.columbia.edu/tag/03P8.

import Definitions.Def_AlgebraicGeometry_EtaleFramePresentations

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
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open PhilipponTorsorInvariantDescent PhilipponTorsorPresheafDifference
open PhilipponTorsorCohomologyRepresentative PhilipponTorsorSectionFibers
open PhilipponTorsorSectionExactness

namespace PhilipponPresheafTorsorCompletion
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- If both presheaves have simply transitive differences, a
difference-preserving map is a bijection wherever the domain has a section. -/
theorem bijective_of_section {G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} {D E : Difference G}
    (f : D.P ⟶ E.P) (U : Cᵒᵖ) (p : D.P.obj U)
    (hD : Function.Bijective (fun q => D.diff U q p))
    (hE : Function.Bijective (fun q => E.diff U q (f.app U p)))
    (hf : ∀ q : D.P.obj U, E.diff U (f.app U q) (f.app U p) = D.diff U q p) :
    Function.Bijective (f.app U) := by
  constructor
  · intro x y h
    exact hD.injective ((hf x).symm.trans ((congrArg (fun t => E.diff U t (f.app U p)) h).trans (hf y)))
  · intro y
    obtain ⟨x, hx⟩ := hD.surjective (E.diff U y (f.app U p))
    exact ⟨x, hE.injective ((hf x).trans hx)⟩

variable [HasSheafify J AddCommGrpCat.{w}] [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A presheaf with local sections and simply transitive differences
maps equivariantly into a torsor sheaf. The map is bijective on every
object where the presheaf admits a section. -/
theorem exists_torsor (G : Sheaf J AddCommGrpCat.{w}) {T : C} (hT : IsTerminal T)
    (D : Difference G.obj) (hlocal : ∀ U, presence D.P U ∈ J U)
    (hbij : ∀ (U : Cᵒᵖ) (p : D.P.obj U), Function.Bijective (fun q => D.diff U q p)) :
    ∃ (A : Torsor G) (f : D.P ⟶ A.D.P),
      (∀ (U : Cᵒᵖ) (p q : D.P.obj U), A.D.diff U (f.app U p) (f.app U q) = D.diff U p q) ∧
      (∀ U, Nonempty (D.P.obj U) → Function.Bijective (f.app U)) := by
  let S := injectiveSequence G
  have hS := injectiveSequence_shortExact G
  obtain ⟨a⟩ := exists_coordinates hS D (hlocal T)
  let A : Torsor G := torsor hT a.value hS
  let f : D.P ⟶ fiber hT a.value :=
    { app U := ↾fun x => ⟨a.lift.app U x, (a.desc U.unop (hT.from U.unop) x).symm⟩
      naturality U V g := by
        apply ConcreteCategory.hom_ext
        intro x
        apply Subtype.ext
        change a.lift.app V (D.P.map g x) = S.X₂.obj.map g (a.lift.app U x)
        exact NatTrans.naturality_apply a.lift g x }
  have hf (U : Cᵒᵖ) (p q : D.P.obj U) :
      A.D.diff U (f.app U p) (f.app U q) = D.diff U p q := by
    apply injective_on_sections S hS U
    change S.f.hom.app U (differenceAt hT a.value hS U (f.app U p) (f.app U q)) = _
    rw [differenceAt_image]
    exact a.diff U p q
  refine ⟨A, f, hf, fun U ⟨p⟩ => ?_⟩
  exact bijective_of_section (D := D) (E := A.D) f U p
    (hbij U p) (A.diff_bijective U (f.app U p)) (fun q => hf U q p)

end PhilipponPresheafTorsorCompletion
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponFrameUnits PhilipponFramePullback

namespace PhilipponEtaleFrameSections
universe u
variable {X : Scheme.{u}} (M : X.Modules)

/-- The Zariski trivializations of an invertible module after pullback
give a small étale cover equipped with local frames. -/
theorem exists_frame_cover (hM : Scheme.Modules.IsInvertible M) (U : X.Etale) :
    ∃ (V : U.left → X.Etale) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ X.smallEtaleTopology U ∧ ∀ i, Nonempty (Frame M (V i)) := by
  have hU := hM.pullback U.hom
  choose W hw e using hU.exists_trivialization
  let V (i : U.left) : X.Etale := Scheme.Etale.mk ((W i).ι ≫ U.hom)
  let f (i : U.left) : V i ⟶ U := MorphismProperty.Over.homMk (W i).ι rfl trivial
  refine ⟨V, f, ?_, ?_⟩
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨x, ⟨x, hw x⟩, rfl⟩
  · intro i
    obtain ⟨p⟩ := e i
    exact ⟨p.symm ≪≫ (Scheme.Modules.pullbackComp (W i).ι U.hom).app M⟩

end PhilipponEtaleFrameSections
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponFrameUnits PhilipponEtaleFrameSections PhilipponFrameRestrictionCoherence
open PhilipponTorsorPresheafDifference PhilipponTorsorInvariantDescent

namespace PhilipponEtaleFramePresheaf
universe u
variable {X : Scheme.{u}} (M : X.Modules)

theorem locally_nonempty (hM : Scheme.Modules.IsInvertible M) (U : X.Etale) :
    presence (presheaf M) U ∈ X.smallEtaleTopology U := by
  obtain ⟨V, f, h, hp⟩ := exists_frame_cover M hM U
  apply X.smallEtaleTopology.superset_covering _ h
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨i⟩
  exact hp i

end PhilipponEtaleFramePresheaf
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponTorsorSectionFibers PhilipponEtaleFramePresheaf PhilipponEtaleFrameSections

namespace PhilipponEtaleFrameTorsor
universe u
variable {X : Scheme.{u}}

private def terminal (X : Scheme.{u}) : IsTerminal (Scheme.Etale.mk (𝟙 X)) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal

/-- An invertible module gives a torsor under the published units sheaf.
Its actual frames map into the torsor, with bijection on sections over
any object admitting a frame. -/
theorem exists_torsor (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ (A : Torsor (PhilipponKummerSequence.units X)) (f : presheaf M ⟶ A.D.P),
      (∀ (U : X.Etaleᵒᵖ) (p q : Frame M U.unop),
        A.D.diff U (f.app U p) (f.app U q) = diff M U.unop p q) ∧
      (∀ U : X.Etaleᵒᵖ, Nonempty (Frame M U.unop) → Function.Bijective (f.app U)) :=
  PhilipponPresheafTorsorCompletion.exists_torsor (PhilipponKummerSequence.units X) (terminal X)
    (difference M) (locally_nonempty M hM) (fun U => diff_bijective M U.unop)

theorem nonempty_presentation (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Nonempty (Presentation M) := by
  obtain ⟨A, f, hdiff, hb⟩ := exists_torsor M hM
  exact ⟨⟨A, f, hdiff, hb⟩⟩

end PhilipponEtaleFrameTorsor
end
end

section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry
namespace PhilipponEtaleFrameTorsor
universe u

/-- A choice of completion of the frame presheaf of an invertible module. -/
def chosenPresentation {X : Scheme.{u}} (M : X.Modules)
    (h : Scheme.Modules.IsInvertible M) : Presentation M :=
  (nonempty_presentation M h).some

end PhilipponEtaleFrameTorsor
end
end


