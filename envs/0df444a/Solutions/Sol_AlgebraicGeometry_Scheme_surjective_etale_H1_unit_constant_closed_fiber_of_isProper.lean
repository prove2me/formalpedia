-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.surjective_etale_H1_unit_constant_closed_fiber_of_isProper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T06:12:01.722904+00:00
-- url     : https://prove2.me/submissions/c7f9af9a-33a6-4af6-b171-ac0a1e4134bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_AbelianSheafTorsors
import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Mathlib.Algebra.Module.ZMod
import Theorems.Thm_AlgebraicGeometry_Scheme_etale_pushforward_preservesFiniteColimits_of_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_equivariant_lift_constant_etale_torsor_closed_fiber_of_isProper

set_option maxHeartbeats 1600000

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) etaleHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) etaleHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) etaleEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

section

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

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

section

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

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

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

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

section

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

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

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

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

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace PhilipponEtaleH1Boundary
universe u v w w'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- The first connecting homomorphism, with the source in global sections. -/
def sectionBoundary {T : C} (hT : IsTerminal T)
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact) :
    S.X₃.obj.obj (op T) →+ S.X₁.H 1 :=
  let A := (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))
  (hS.extClass.postcomp A (zero_add 1)).comp (Sheaf.H.equiv₀ S.X₃ hT).symm.toAddMonoidHom

/-- An injective middle term makes the boundary a cokernel on sections. -/
theorem sectionBoundary_spec {T : C} (hT : IsTerminal T)
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact) [Injective S.X₂] :
    Function.Surjective (sectionBoundary hT S hS) ∧
      Function.Exact (S.g.hom.app (op T)).hom (sectionBoundary hT S hS) := by
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
  refine ⟨hsurj.comp e₃.symm.surjective, fun x => ?_⟩
  change d (e₃.symm x) = 0 ↔ x ∈ Set.range (S.g.hom.app (op T)).hom
  rw [hexact]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e₂ y, ?_⟩
    rw [Sheaf.H.equiv₀_naturality, hy, AddEquiv.apply_symm_apply]
  · rintro ⟨y, rfl⟩
    exact ⟨e₂.symm y, Sheaf.H.equiv₀_symm_naturality hT S.g y⟩

/-- For a short exact sequence with injective middle sheaf, first
cohomology of the kernel is the cokernel on actual global sections. -/
theorem exists_section_boundary {T : C} (hT : IsTerminal T)
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact) [Injective S.X₂] :
    ∃ δ : S.X₃.obj.obj (op T) →+ S.X₁.H 1,
      Function.Surjective δ ∧ Function.Exact (S.g.hom.app (op T)).hom δ :=
  ⟨sectionBoundary hT S hS, sectionBoundary_spec hT S hS⟩

/-- The connecting homomorphism commutes with maps of short exact sequences. -/
theorem sectionBoundary_naturality {T : C} (hT : IsTerminal T)
    {S S' : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact) (hS' : S'.ShortExact)
    (m : S ⟶ S') (q : S.X₃.obj.obj (op T)) :
    Sheaf.H.map m.τ₁ 1 (sectionBoundary hT S hS q) =
      sectionBoundary hT S' hS' (m.τ₃.hom.app (op T) q) := by
  let e := (Sheaf.H.equiv₀ S.X₃ hT).symm q
  have he : (Sheaf.H.equiv₀ S'.X₃ hT).symm (m.τ₃.hom.app (op T) q) =
      e.comp (Ext.mk₀ m.τ₃) (add_zero 0) :=
    (Sheaf.H.equiv₀_symm_naturality hT m.τ₃ q).symm
  change (e.comp hS.extClass (zero_add 1)).comp (Ext.mk₀ m.τ₁) (add_zero 1) =
    ((Sheaf.H.equiv₀ S'.X₃ hT).symm (m.τ₃.hom.app (op T) q)).comp hS'.extClass (zero_add 1)
  rw [he, Ext.comp_assoc e hS.extClass (Ext.mk₀ m.τ₁) (zero_add 1) (add_zero 1) (zero_add 1),
    hS.extClass_naturality hS' m,
    Ext.comp_assoc e (Ext.mk₀ m.τ₃) hS'.extClass (add_zero 0) (zero_add 1) (zero_add 1)]

end PhilipponEtaleH1Boundary

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open PhilipponTorsorInvariantDescent PhilipponTorsorPresheafDifference
open PhilipponTorsorCohomologyRepresentative PhilipponTorsorSectionFibers
open PhilipponTorsorFiberComparison PhilipponTorsorSectionExactness

namespace PhilipponTorsorClassification
universe u v w w'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} {T : C}
variable [HasSheafify J AddCommGrpCat.{w}]

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

end PhilipponTorsorClassification

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleH1Boundary (sectionBoundary sectionBoundary_spec sectionBoundary_naturality)
open PhilipponTorsorPresheafDifference (Difference)
open PhilipponTorsorSectionFibers (Torsor torsor)
open PhilipponTorsorSectionExactness (injectiveSequence injectiveSequence_shortExact)
open PhilipponTorsorCohomologyRepresentative (Coordinates exists_coordinates)
open PhilipponTorsorClassification (fiberCoordinates pull)


namespace PhilipponTorsorH1Naturality

universe u v w w'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

private abbrev Ab := Sheaf J AddCommGrpCat.{w}

/-- Apply a coefficient map to the differences of a presheaf of local sections. -/
def mapDifference {G H : Ab (J := J)} (f : G ⟶ H) (D : Difference G.obj) : Difference H.obj where
  P := D.P
  diff := fun U x y => f.hom.app U (D.diff U x y)
  diff_add_diff := by
    intro U x y z
    rw [← map_add, D.diff_add_diff]
  map_diff := by
    intro U V g x y
    rw [← NatTrans.naturality_apply f.hom g, D.map_diff]

/-- A map between short exact presentations sends coordinates to coordinates
for the transported differences. -/
private def mapCoordinates {T : C} {S S' : ShortComplex (Ab (J := J))}
    (m : S ⟶ S') {D : Difference S.X₁.obj} (a : Coordinates D T) :
    Coordinates (mapDifference m.τ₁ D) T where
  lift := a.lift ≫ Functor.whiskerRight m.τ₂.hom (forget AddCommGrpCat)
  value := m.τ₃.hom.app (op T) a.value
  diff := by
    intro U x y
    change m.τ₂.hom.app U (a.lift.app U x) - m.τ₂.hom.app U (a.lift.app U y) =
      S'.f.hom.app U (m.τ₁.hom.app U (D.diff U x y))
    rw [← map_sub, a.diff]
    have h := congrArg (fun k : S.X₁ ⟶ S'.X₂ => k.hom.app U) m.comm₁₂
    exact (ConcreteCategory.congr_hom h (D.diff U x y)).symm
  desc := by
    intro U g x
    change S'.X₃.obj.map g.op (m.τ₃.hom.app (op T) a.value) =
      S'.g.hom.app (op U) (m.τ₂.hom.app (op U) (a.lift.app (op U) x))
    rw [← NatTrans.naturality_apply m.τ₃.hom g.op, a.desc]
    have h := congrArg (fun k : S.X₂ ⟶ S'.X₃ => k.hom.app (op U)) m.comm₂₃
    exact (ConcreteCategory.congr_hom h (a.lift.app (op U) x)).symm

variable [HasSheafify J AddCommGrpCat.{w}]
variable [EnoughInjectives (Ab (J := J))] [HasExt.{w'} (Ab (J := J))]

private def presentationMap {S : ShortComplex (Ab (J := J))} (hS : S.ShortExact)
    {H : Ab (J := J)} (f : S.X₁ ⟶ H) : S ⟶ injectiveSequence H := by
  let I := injectiveSequence H
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  let b : S.X₂ ⟶ I.X₂ := Injective.factorThru (f ≫ I.f) S.f
  have hb : S.f ≫ b = f ≫ I.f := Injective.comp_factorThru _ _
  have hz : S.f ≫ (b ≫ I.g) = 0 := by
    rw [← Category.assoc, hb, Category.assoc, I.zero, comp_zero]
  exact ShortComplex.homMk f b (hS.exact.desc (b ≫ I.g) hz) hb.symm (hS.exact.g_desc _ _).symm

private def chosenCoordinates (T : C) {G : Ab (J := J)} (A : Torsor G) :
    Coordinates (S := injectiveSequence G) A.D T :=
  Classical.choice (exists_coordinates (injectiveSequence_shortExact G) A.D (A.locally_nonempty T))

/-- The cohomology class of an abelian torsor, computed in an injective presentation. -/
def classOf {T : C} (hT : IsTerminal T) {G : Ab (J := J)} (A : Torsor G) : G.H 1 :=
  sectionBoundary hT (injectiveSequence G) (injectiveSequence_shortExact G) (chosenCoordinates T A).value

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Every first cohomology class has a torsor representative. -/
theorem classOf_surjective {T : C} (hT : IsTerminal T) (G : Ab (J := J)) :
    Function.Surjective (classOf hT (G := G)) := by
  let S := injectiveSequence G
  let hS := injectiveSequence_shortExact G
  let spec := sectionBoundary_spec hT S hS
  intro x
  obtain ⟨q, hq⟩ := spec.1 x
  let A := torsor hT q hS
  refine ⟨A, (Coordinates.same_class (chosenCoordinates T A) (fiberCoordinates hS hT q)
    (A.locally_nonempty T) (sectionBoundary hT S hS) spec.2).trans hq⟩

/-- Coordinates in any short exact sequence compute the same torsor class. -/
theorem classOf_eq_sectionBoundary {T : C} (hT : IsTerminal T)
    {S : ShortComplex (Ab (J := J))} (hS : S.ShortExact) {A : Torsor S.X₁}
    (a : Coordinates A.D T) : classOf hT A = sectionBoundary hT S hS a.value := by
  let S' := injectiveSequence S.X₁
  let hS' := injectiveSequence_shortExact S.X₁
  let m := presentationMap hS (𝟙 S.X₁)
  let D := mapDifference (𝟙 S.X₁) A.D
  let a' : Coordinates (S := S') D T := mapCoordinates m a
  let c' : Coordinates (S := S') D T := pull (chosenCoordinates T A) (𝟙 A.D.P) (by
    intro U x y
    change A.D.diff U x y = A.D.diff U x y
    rfl)
  let δ := sectionBoundary hT S' hS'
  calc
    _ = δ c'.value := rfl
    _ = δ a'.value := Coordinates.same_class c' a' (A.locally_nonempty T) δ
      (sectionBoundary_spec hT S' hS').2
    _ = Sheaf.H.map (𝟙 S.X₁) 1 (sectionBoundary hT S hS a.value) :=
      (sectionBoundary_naturality hT hS hS' m a.value).symm
    _ = _ := Sheaf.H.map_id_apply _

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The torsor of lifts of a global section represents its boundary. -/
theorem classOf_fiber {T : C} (hT : IsTerminal T) {S : ShortComplex (Ab (J := J))}
    (hS : S.ShortExact) (q : S.X₃.obj.obj (op T)) :
    classOf hT (torsor hT q hS) = sectionBoundary hT S hS q :=
  classOf_eq_sectionBoundary hT (S := S) hS (A := torsor hT q hS)
    (fiberCoordinates (S := S) hS hT q)

/-- An equivariant torsor map over a homomorphism of coefficients takes the
source class to the target class under the induced map on first cohomology. -/
theorem classOf_naturality {T : C} (hT : IsTerminal T) {G H : Ab (J := J)} {f : G ⟶ H}
    {A : Torsor G} {B : Torsor H} (b : A.D.P ⟶ B.D.P)
    (hb : ∀ (U : Cᵒᵖ) (x y : A.D.P.obj U),
      B.D.diff U (b.app U x) (b.app U y) = f.hom.app U (A.D.diff U x y)) :
    Sheaf.H.map f 1 (classOf hT A) = classOf hT B := by
  let S := injectiveSequence G
  let S' := injectiveSequence H
  let hS := injectiveSequence_shortExact G
  let hS' := injectiveSequence_shortExact H
  let m := presentationMap hS f
  let a := chosenCoordinates T A
  let c := chosenCoordinates T B
  let D := mapDifference f A.D
  let a' : Coordinates (S := S') D T := mapCoordinates m a
  let c' : Coordinates (S := S') D T := pull c b hb
  let δ := sectionBoundary hT S' hS'
  have hδ := (sectionBoundary_spec hT S' hS').2
  calc
    _ = δ a'.value := sectionBoundary_naturality hT hS hS' m a.value
    _ = δ c'.value := Coordinates.same_class a' c' (A.locally_nonempty T) δ hδ
    _ = _ := rfl

end PhilipponTorsorH1Naturality

end

section

open AlgebraicGeometry CategoryTheory
open PhilipponEtaleSmallSite (pullbackAdjunction)
namespace PhilipponEtaleCohomologyUnits
universe u
abbrev unitMap {X Y : Scheme.{u}} (p : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) :=
  (Sheaf.functorH X.smallEtaleTopology q).map ((pullbackAdjunction p).unit.app F)
end PhilipponEtaleCohomologyUnits

end

section

set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleCohomologyUnits (unitMap)
open PhilipponEtaleH1Boundary (sectionBoundary sectionBoundary_spec)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponTorsorSectionExactness (injectiveSequence injectiveSequence_shortExact injective_on_sections)
open PhilipponTorsorSectionFibers (Torsor fiber torsor differenceAt differenceAt_image)
open PhilipponTorsorH1Naturality (classOf classOf_fiber classOf_naturality)


namespace PhilipponEtaleH1TorsorSpecialization

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev terminal (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)
private def terminalIsTerminal (X : Scheme.{u}) : IsTerminal (terminal X) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal

variable {X Z : Scheme.{u}} (i : Z ⟶ X)

private def terminalIso : (baseChange i).obj (terminal X) ≅ terminal Z := by
  let : PreservesFiniteLimits (baseChange i) :=
    inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback (@Etale) ⊤ i))
  exact (IsTerminal.isTerminalObj (baseChange i) _ (terminalIsTerminal X)).uniqueUpToIso
    (terminalIsTerminal Z)

private abbrev precompose (P : Z.Etaleᵒᵖ ⥤ Type u) := (baseChange i).op ⋙ P

/-- Lifting torsors for the restriction unit means lifting to the ambient
scheme with an equivariant map to the restricted sections on each chart. -/
def TorsorsLiftForUnit (F : Ab X) : Prop :=
  ∀ B : Torsor ((pullbackSheaves i).obj F), ∃ (A : Torsor F) (b : A.D.P ⟶ precompose i B.D.P),
    ∀ (U : X.Etaleᵒᵖ) (x y : A.D.P.obj U),
      B.D.diff ((baseChange i).op.obj U) (b.app U x) (b.app U y) =
        ((pullbackAdjunction i).unit.app F).hom.app U (A.D.diff U x y)

private abbrev sourcePoint {S : ShortComplex (Ab Z)} (q : S.X₃.obj.obj (op (terminal Z))) :
    (S.map (pushforward i)).X₃.obj.obj (op (terminal X)) := S.X₃.obj.map (terminalIso i).hom.op q

/-- A local lift of a quotient section over the base-changed chart is a
local lift in the direct-image sequence on the original chart. -/
private def transportFiber {S : ShortComplex (Ab Z)} (q : S.X₃.obj.obj (op (terminal Z))) :
    precompose i (fiber (terminalIsTerminal Z) q) ⟶
      fiber (S := S.map (pushforward i)) (terminalIsTerminal X) (sourcePoint i q) where
  app U := ↾fun x => ⟨x.val, by
    let g := (baseChange i).map ((terminalIsTerminal X).from U.unop) ≫ (terminalIso i).hom
    have hg : g = (terminalIsTerminal Z).from ((baseChange i).obj U.unop) :=
      (terminalIsTerminal Z).hom_ext _ _
    change S.g.hom.app (op ((baseChange i).obj U.unop)) x.val =
      S.X₃.obj.map ((baseChange i).map ((terminalIsTerminal X).from U.unop)).op
        (S.X₃.obj.map (terminalIso i).hom.op q)
    rw [← Functor.map_comp_apply, ← op_comp]
    exact x.property.trans (congrArg (fun a : (baseChange i).obj U.unop ⟶ terminal Z => S.X₃.obj.map a.op q) hg.symm)⟩
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact Subtype.ext rfl

private theorem transportFiber_difference {S : ShortComplex (Ab Z)} (hS : S.ShortExact)
    (hX : (S.map (pushforward i)).ShortExact) (q : S.X₃.obj.obj (op (terminal Z)))
    (U : X.Etaleᵒᵖ) (x y : (precompose i (fiber (terminalIsTerminal Z) q)).obj U) :
    differenceAt (terminalIsTerminal X) (sourcePoint i q) hX U
        ((transportFiber i q).app U x) ((transportFiber i q).app U y) =
      differenceAt (terminalIsTerminal Z) q hS ((baseChange i).op.obj U) x y := by
  apply injective_on_sections S hS ((baseChange i).op.obj U)
  exact (differenceAt_image (terminalIsTerminal X) (sourcePoint i q) hX U
    ((transportFiber i q).app U x) ((transportFiber i q).app U y)).trans
      (differenceAt_image (terminalIsTerminal Z) q hS ((baseChange i).op.obj U) x y).symm

/-- Equivariant specialization of torsors implies surjectivity on first
cohomology for the unit of restriction, when direct image is exact. -/
theorem surjective_unitMap_of_torsorsLift [PreservesFiniteColimits (pushforward i)]
    (F : Ab X) (hLift : TorsorsLiftForUnit i F) : Function.Surjective (unitMap i F 1) := by
  let G := (pullbackSheaves i).obj F
  let R := pushforward i
  let S := injectiveSequence G
  let hS := injectiveSequence_shortExact G
  let SX := S.map R
  let hX : SX.ShortExact := hS.map_of_exact R
  let : Injective SX.X₂ := R.injective_obj_of_injective (inferInstance : Injective S.X₂)
  intro c
  obtain ⟨qX, hqX⟩ := (sectionBoundary_spec (terminalIsTerminal X) SX hX).1 c
  obtain ⟨q, hq⟩ := (ConcreteCategory.bijective_of_isIso (S.X₃.obj.map (terminalIso i).hom.op)).surjective qX
  have hq' : sourcePoint i q = qX := hq
  subst qX
  let B₀ := torsor (terminalIsTerminal Z) q hS
  let B := torsor (terminalIsTerminal X) (sourcePoint i q) hX
  obtain ⟨A, f, hf⟩ := hLift B₀
  let g : A.D.P ⟶ B.D.P := f ≫ transportFiber i q
  have hg (U : X.Etaleᵒᵖ) (x y : A.D.P.obj U) :
      B.D.diff U (g.app U x) (g.app U y) =
        ((pullbackAdjunction i).unit.app F).hom.app U (A.D.diff U x y) :=
    (transportFiber_difference i hS hX q U (f.app U x) (f.app U y)).trans (hf U x y)
  refine ⟨classOf (terminalIsTerminal X) A, ?_⟩
  exact (classOf_naturality (terminalIsTerminal X) g hg).trans
    ((classOf_fiber (terminalIsTerminal X) hX (sourcePoint i q)).trans hqX)

end PhilipponEtaleH1TorsorSpecialization

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (A : Type u) [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] {Y T : Scheme.{u}}
    (g : Y ⟶ Spec (.of A)) [IsProper g]
    (s : T ⟶ Spec (.of (IsLocalRing.ResidueField A))) (j : T ⟶ Y)
    (h : IsPullback s j (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g) (N : ℕ) (hN : N.Prime) :
    Function.Surjective ((Sheaf.functorH Y.smallEtaleTopology 1).map
      ((PhilipponEtaleSmallSite.pullbackAdjunction j).unit.app ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} (ZMod N)))))) := by
  let ρ := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let : IsClosedImmersion ρ := IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  let : IsClosedImmersion j := MorphismProperty.of_isPullback h (inferInstance : IsClosedImmersion ρ)
  let : PreservesFiniteColimits (PhilipponEtaleClosedPushforward.pushforward j) := AlgebraicGeometry.Scheme.etale_pushforward_preservesFiniteColimits_of_isFinite j
  exact PhilipponEtaleH1TorsorSpecialization.surjective_unitMap_of_torsorsLift j _
    (AlgebraicGeometry.Scheme.exists_equivariant_lift_constant_etale_torsor_closed_fiber_of_isProper A g s j h N hN)

end

end
