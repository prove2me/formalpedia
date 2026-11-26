-- Prove2me | Definitions.Def_AlgebraicGeometry_FiniteModulePresheafPresentations
-- name    : AlgebraicGeometry_FiniteModulePresheafPresentations
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T00:01:49.873608+00:00
-- url     : https://prove2.me/theorems/342455fc-6d81-5ea0-b906-d4667ab87a94
-- title:
--   Finite presentations of module presheaves
-- statement:
--   Module presheaves are filtered colimits of cokernels with finitely many generators and relations.
-- source:
--   Stacks Project, 59.73.2 (https://stacks.math.columbia.edu/tag/03SA) and 59.74.4 (https://stacks.math.columbia.edu/tag/09Z7).

import Definitions.Def_AlgebraicGeometry_EtaleFinitePresentationFieldModels
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Module.ZMod
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Presentable.Adjunction
import Mathlib.CategoryTheory.Presentable.Presheaf
import Mathlib.CategoryTheory.Presentable.Type
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Sum

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponEtaleRelativeCoefficients

universe u

private def liftPresheaf {C : Type*} [Category* C] (N : ℕ)
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (h : ∀ U (a : ↥(P.obj U)), N • a = 0) :
    Cᵒᵖ ⥤ ModuleCat.{u} (ZMod N) := by
  letI instModule (U : Cᵒᵖ) : Module (ZMod N) (P.obj U) := AddCommGroup.zmodModule (h U)
  refine {
    obj := fun U => ModuleCat.of (ZMod N) (P.obj U)
    map := fun f => ModuleCat.ofHom ((P.map f).hom.toZModLinearMap N)
    map_id := ?_
    map_comp := ?_ }
  · intro U
    apply ConcreteCategory.hom_ext
    intro a
    change P.map (𝟙 U) a = a
    rw [P.map_id]
    rfl
  · intro U V W f g
    apply ConcreteCategory.hom_ext
    intro a
    change P.map (f ≫ g) a = P.map g (P.map f a)
    rw [P.map_comp]
    rfl

/-- An abelian étale sheaf annihilated by an integer has a model as a
sheaf of modules over the corresponding quotient of the integers. -/
def boundedTorsionModule {X : Scheme.{u}} (N : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (h : N • 𝟙 F = 0) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod N)) := by
  have hSection (W : X.Etaleᵒᵖ) (a : ↥(F.obj.obj W)) : N • a = 0 :=
    congrArg (fun t : F ⟶ F => t.hom.app W a) h
  let P := liftPresheaf N F.obj hSection
  refine ⟨P, ?_⟩
  apply Presheaf.isSheaf_of_isSheaf_comp _ P (forget₂ (ModuleCat.{u} (ZMod N)) AddCommGrpCat.{u})
  exact F.property

/-- The underlying abelian presheaf of the module model is the original
presheaf. -/
theorem boundedTorsionModule_forget {X : Scheme.{u}} (N : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (h : N • 𝟙 F = 0) :
    (boundedTorsionModule N F h).obj ⋙ (forget₂ (ModuleCat.{u} (ZMod N)) AddCommGrpCat.{u}) =
      F.obj := rfl

end PhilipponEtaleRelativeCoefficients

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits


namespace PhilipponFiniteCokernelPresentation

universe u v w

variable {C : Type w} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]
  {K : Type u} (G : K → C)

/-- A finite list of generators and a finite list of relations, expressed
as a cokernel of a map of finite coproducts from the given family. -/
structure Presentation (X : C) where
  generators : Type u
  relations : Type u
  [finiteGenerators : Finite generators]
  [finiteRelations : Finite relations]
  generator : generators → K
  relation : relations → K
  differential : (∐ fun i => G (relation i)) ⟶ (∐ fun i => G (generator i))
  quotientIso : cokernel differential ≅ X

attribute [instance] Presentation.finiteGenerators Presentation.finiteRelations

namespace Presentation

variable {G} {X : C} (p : Presentation G X)

abbrev source := ∐ fun i => G (p.relation i)
abbrev target := ∐ fun i => G (p.generator i)

def quotient : p.target ⟶ X := cokernel.π p.differential ≫ p.quotientIso.hom

instance : Epi p.quotient := inferInstanceAs (Epi (cokernel.π p.differential ≫ p.quotientIso.hom))

@[reassoc (attr := simp)]
theorem condition : p.differential ≫ p.quotient = 0 := by
  rw [quotient, cokernel.condition_assoc, zero_comp]

def desc {Y : C} (f : p.target ⟶ Y) (hf : p.differential ≫ f = 0) : X ⟶ Y :=
  p.quotientIso.inv ≫ cokernel.desc p.differential f hf

@[reassoc (attr := simp)]
theorem quotient_desc {Y : C} (f : p.target ⟶ Y) (hf : p.differential ≫ f = 0) :
    p.quotient ≫ p.desc f hf = f := by
  simp only [quotient, desc, Category.assoc, Iso.hom_inv_id_assoc, cokernel.π_desc]

end Presentation

set_option maxHeartbeats 1200000 in
/-- Colimits of finite diagrams of these presentations have finite
presentations using the same family of projectives. Add one relation for
each arrow and each generator of its source. -/
theorem presentation_of_finite_colimit [∀ k, Projective (G k)]
    {J : Type u} [SmallCategory J] [Finite J] [Finite (Arrow J)]
    (F : J ⥤ C) (c : Cocone F) (hc : IsColimit c)
    (p : ∀ j, Presentation G (F.obj j)) :
    Nonempty (Presentation G c.pt) := by
  let B := Σ j : J, (p j).generators
  let D := (Σ j : J, (p j).relations) ⊕ (Σ a : Arrow J, (p a.left).generators)
  let : ∀ j : J, Finite (p j).generators := fun j => (p j).finiteGenerators
  let : ∀ j : J, Finite (p j).relations := fun j => (p j).finiteRelations
  let : ∀ a : Arrow J, Finite (p a.left).generators := fun a => (p a.left).finiteGenerators
  let : Finite B := inferInstanceAs (Finite (Σ j : J, (p j).generators))
  let : Finite D := inferInstanceAs
    (Finite ((Σ j : J, (p j).relations) ⊕ (Σ a : Arrow J, (p a.left).generators)))
  let BLabel (j : B) : K := (p j.1).generator j.2
  let DLabel : D → K := Sum.elim (fun j => (p j.1).relation j.2)
    (fun j => (p j.1.left).generator j.2)
  let i (j : J) : (p j).target ⟶ ∐ (G ∘ BLabel) :=
    Sigma.desc fun a => Sigma.ι (G ∘ BLabel) ⟨j, a⟩
  have hi (j : J) (a : (p j).generators) :
      Sigma.ι (fun i => G ((p j).generator i)) a ≫ i j = Sigma.ι (G ∘ BLabel) ⟨j, a⟩ :=
    Sigma.ι_desc _ _
  let l (a : Arrow J) (z : (p a.left).generators) :
      G ((p a.left).generator z) ⟶ (p a.right).target :=
    Projective.factorThru
      (Sigma.ι (fun i => G ((p a.left).generator i)) z ≫ (p a.left).quotient ≫ F.map a.hom)
      (p a.right).quotient
  have hl (a : Arrow J) (z : (p a.left).generators) :
      l a z ≫ (p a.right).quotient =
        Sigma.ι (fun i => G ((p a.left).generator i)) z ≫ (p a.left).quotient ≫ F.map a.hom :=
    Projective.factorThru_comp _ _
  let rel : ∀ z : D, G (DLabel z) ⟶ ∐ (G ∘ BLabel) :=
    fun z => match z with
    | .inl ⟨j, a⟩ =>
      Sigma.ι (fun i => G ((p j).relation i)) a ≫ (p j).differential ≫ i j
    | .inr ⟨a, z⟩ => l a z ≫ i a.right -
      (show G ((p a.left).generator z) ⟶ ∐ (G ∘ BLabel) from
        Sigma.ι (G ∘ BLabel) ⟨a.left, z⟩)
  let d := Sigma.desc rel
  let π := cokernel.π d
  have hrel (z : D) : rel z ≫ π = 0 := by
    rw [← Sigma.ι_desc rel z, Category.assoc, cokernel.condition, comp_zero]
  have hSource (j : J) : (p j).differential ≫ i j ≫ π = 0 := by
    apply Sigma.hom_ext
    intro z
    simpa only [rel, Category.assoc, comp_zero] using hrel (.inl ⟨j, z⟩)
  have hArrow (a : Arrow J) (z : (p a.left).generators) :
      l a z ≫ i a.right ≫ π =
        Sigma.ι (G ∘ BLabel) ⟨a.left, z⟩ ≫ π := by
    apply sub_eq_zero.mp
    simpa only [rel, Preadditive.sub_comp, Category.assoc] using hrel (.inr ⟨a, z⟩)
  let ι (j : J) : F.obj j ⟶ cokernel d := (p j).desc (i j ≫ π) (hSource j)
  have hι (j : J) : (p j).quotient ≫ ι j = i j ≫ π :=
    (p j).quotient_desc _ _
  let c₀ : Cocone F :=
    { pt := cokernel d
      ι :=
        { app := ι
          naturality := by
            intro j k a
            change F.map a ≫ ι k = ι j ≫ 𝟙 _
            rw [Category.comp_id]
            apply (cancel_epi (p j).quotient).mp
            apply Sigma.hom_ext
            intro z
            have hLift : l (Arrow.mk a) z ≫ (p k).quotient =
                Sigma.ι (fun i => G ((p j).generator i)) z ≫ (p j).quotient ≫ F.map a :=
              hl (Arrow.mk a) z
            simp only [← reassoc_of% hLift, hι k, hι j,
              reassoc_of% (hi j z)]
            exact hArrow (Arrow.mk a) z } }
  let toCoconeComponent (c' : Cocone F) (z : B) : (G ∘ BLabel) z ⟶ c'.pt :=
    Sigma.ι (fun i => G ((p z.1).generator i)) z.2 ≫ (p z.1).quotient ≫ c'.ι.app z.1
  let toCocone (c' : Cocone F) : (∐ (G ∘ BLabel)) ⟶ c'.pt :=
    Sigma.desc (toCoconeComponent c')
  have hiTo (c' : Cocone F) (j : J) : i j ≫ toCocone c' = (p j).quotient ≫ c'.ι.app j := by
    apply Sigma.hom_ext
    intro z
    rw [← Category.assoc, hi, Sigma.ι_desc]
  have hTo (c' : Cocone F) : d ≫ toCocone c' = 0 := by
    apply Sigma.hom_ext
    intro z
    rw [← Category.assoc, Sigma.ι_desc, comp_zero]
    rcases z with ⟨j, a⟩ | ⟨a, z⟩
    · simp only [rel, Category.assoc, hiTo, Presentation.condition_assoc, zero_comp, comp_zero]
    · let b : G ((p a.left).generator z) ⟶ ∐ (G ∘ BLabel) :=
        Sigma.ι (G ∘ BLabel) ⟨a.left, z⟩
      change (l a z ≫ i a.right - b) ≫ toCocone c' = 0
      dsimp only [b]
      rw [Preadditive.sub_comp, Category.assoc, hiTo, reassoc_of% (hl a z), Sigma.ι_desc]
      simp only [toCoconeComponent, c'.w, sub_self]
  let h₀ : IsColimit c₀ :=
    { desc := fun c' => cokernel.desc d (toCocone c') (hTo c')
      fac := by
        intro c' j
        change ι j ≫ cokernel.desc d (toCocone c') (hTo c') = c'.ι.app j
        apply (cancel_epi (p j).quotient).mp
        rw [← Category.assoc, hι, Category.assoc, cokernel.π_desc, hiTo]
      uniq := by
        intro c' m hm
        apply (cancel_epi π).mp
        rw [cokernel.π_desc]
        apply Sigma.hom_ext
        rintro ⟨j, z⟩
        let a := Sigma.ι (fun i => G ((p j).generator i)) z
        have h := congrArg (fun k => a ≫ (p j).quotient ≫ k) (hm j)
        change Sigma.ι (fun i => G ((p j).generator i)) z ≫ (p j).quotient ≫ ι j ≫ m =
          Sigma.ι (fun i => G ((p j).generator i)) z ≫ (p j).quotient ≫ c'.ι.app j at h
        simp only [reassoc_of% (hι j), reassoc_of% (hi j z)] at h
        exact h.trans (Sigma.ι_desc (toCoconeComponent c') ⟨j, z⟩).symm }
  exact ⟨{
    generators := B
    relations := D
    generator := BLabel
    relation := DLabel
    differential := d
    quotientIso := h₀.coconePointUniqueUpToIso hc }⟩

/-- A generator by itself has a presentation with one generator and no relations. -/
def generatorPresentation (k : K) : Presentation G (G k) := by
  let B (_ : PUnit.{u + 1}) := G k
  let E (e : PEmpty.{u + 1}) := G (PEmpty.elim e)
  let e : (∐ B) ≅ G k :=
    { hom := Sigma.desc fun _ => 𝟙 (G k)
      inv := Sigma.ι B PUnit.unit
      hom_inv_id := by
        apply Sigma.hom_ext
        rintro ⟨⟩
        simp only [Sigma.ι_desc_assoc, Category.comp_id]
        exact Category.id_comp _
      inv_hom_id := Sigma.ι_desc _ _ }
  let d : (∐ E) ⟶ (∐ B) := 0
  exact {
    generators := PUnit.{u + 1}
    relations := PEmpty.{u + 1}
    generator := fun _ => k
    relation := PEmpty.elim
    differential := d
    quotientIso := (asIso (cokernel.π d)).symm ≪≫ e }

/-- The finite-colimit closure of a family of projectives consists of
objects with finite generators and relations from that family. -/
theorem presentation_of_colimitsCardinalClosure [∀ k, Projective (G k)] {X : C}
    (h : (ObjectProperty.ofObj G).colimitsCardinalClosure (Cardinal.aleph0 : Cardinal.{u}) X) :
    Nonempty (Presentation G X) := by
  let Q : ObjectProperty C := fun Y => Nonempty (Presentation G Y)
  let : Q.IsClosedUnderIsomorphisms :=
    ⟨fun e ⟨p⟩ => ⟨{ p with quotientIso := p.quotientIso ≪≫ e }⟩⟩
  have hQ : (ObjectProperty.ofObj G).colimitsCardinalClosure (Cardinal.aleph0 : Cardinal.{u}) ≤ Q := by
    apply ObjectProperty.colimitsCardinalClosure_le
    · intro J _ hj
      let : Finite (Arrow J) := (hasCardinalLT_aleph0_iff _).mp hj
      let : Finite J := Finite.of_injective (fun j : J => Arrow.mk (𝟙 j))
        (fun _ _ hEq => congrArg Arrow.left hEq)
      apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
      rintro _ ⟨F, hF⟩
      exact presentation_of_finite_colimit G F (colimit.cocone F) (colimit.isColimit F)
        fun j => Classical.choice (hF j)
    · rintro _ ⟨k⟩
      exact ⟨generatorPresentation G k⟩
  exact hQ _ h

/-- A finite presentation is in the finite-colimit closure of its generators. -/
theorem colimitsCardinalClosure_of_presentation {X : C} (p : Presentation G X) :
    (ObjectProperty.ofObj G).colimitsCardinalClosure (Cardinal.aleph0 : Cardinal.{u}) X := by
  let P := ObjectProperty.ofObj G
  let κ : Cardinal.{u} := Cardinal.aleph0
  let Q := P.colimitsCardinalClosure κ
  have hSum {L : Type u} [Finite L] (label : L → K) : Q (∐ fun i => G (label i)) := by
    let : Q.IsClosedUnderColimitsOfShape (Discrete L) :=
      P.isClosedUnderColimitsOfShape_colimitsCardinalClosure κ _
        (hasCardinalLT_of_finite _ _ le_rfl)
    exact Q.prop_colimit _ (fun j => P.le_colimitsCardinalClosure κ _ ⟨label j.as⟩)
  let : Q.IsClosedUnderColimitsOfShape WalkingParallelPair :=
    P.isClosedUnderColimitsOfShape_colimitsCardinalClosure κ _
      (hasCardinalLT_of_finite _ _ le_rfl)
  apply Q.prop_of_iso p.quotientIso
  exact Q.prop_colimit _ (fun j => by
    cases j
    · exact hSum p.relation
    · exact hSum p.generator)

end PhilipponFiniteCokernelPresentation

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponFiniteModulePresheafPresentation

universe u

attribute [local instance] Cardinal.fact_isRegular_aleph0

variable (R : Type u) [Ring R]

abbrev unitModule := (ModuleCat.free.{u} R).obj PUnit.{u + 1}

private theorem strongGenerator_unitModule :
    (ObjectProperty.singleton (unitModule.{u} R)).IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff]
  constructor
  · intro A B f g h
    apply ConcreteCategory.hom_ext
    intro a
    let q : unitModule.{u} R ⟶ A := ModuleCat.freeDesc (↾fun _ => a)
    have he := ConcreteCategory.congr_hom (h _ ((ObjectProperty.singleton_iff _ _).2 rfl) q)
      (ModuleCat.freeMk (R := R) (X := PUnit.{u + 1}) PUnit.unit)
    simpa [q] using he
  · intro A B f _ h
    have : Epi f := by
      apply (ModuleCat.epi_iff_surjective f).mpr
      intro b
      let q : unitModule.{u} R ⟶ B := ModuleCat.freeDesc (↾fun _ => b)
      obtain ⟨p, hp⟩ := h _ ((ObjectProperty.singleton_iff _ _).2 rfl) q
      let t := ModuleCat.freeMk (R := R) (X := PUnit.{u + 1}) PUnit.unit
      exact ⟨p t, by simpa [q, t] using ConcreteCategory.congr_hom hp t⟩
    exact isIso_of_mono_of_epi f

private theorem presentable_unitModule :
    IsCardinalPresentable (unitModule.{u} R) (Cardinal.aleph0 : Cardinal.{u}) := by
  let : IsCardinalPresentable PUnit.{u + 1} (Cardinal.aleph0 : Cardinal.{u}) :=
    (hasCardinalLT_of_finite _ _ le_rfl).isCardinalPresentable
  let : (forget (ModuleCat.{u} R)).IsCardinalAccessible (Cardinal.aleph0 : Cardinal.{u}) := {
    preservesColimitOfShape := fun K _ _ => by
      let : IsFiltered K := isFiltered_of_isCardinalFiltered K Cardinal.aleph0
      infer_instance }
  exact (ModuleCat.adj.{u} R).isCardinalPresentable_leftAdjoint_obj Cardinal.aleph0 _

variable (C : Type u) [SmallCategory C]

/-- The free module presheaf on a representable. -/
abbrev freeChart (U : C) := Presheaf.freeYoneda U (unitModule.{u} R)

/-- A free rank-one representable is projective in module presheaves.
Lifting a map amounts to lifting the image of its generator at the representing object. -/
theorem projective_freeYoneda_unitModule (U : C) :
    Projective (Presheaf.freeYoneda U (unitModule.{u} R)) where
  factors {F G} f e _ := by
    let a := Presheaf.freeYonedaHomEquiv f
    let t := ModuleCat.freeMk (R := R) (X := PUnit.{u + 1}) PUnit.unit
    let : Epi (e.app (op U)) := (NatTrans.epi_iff_epi_app e).mp inferInstance _
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (e.app (op U))).mp inferInstance (a t)
    let b : unitModule R ⟶ F.obj (op U) := ModuleCat.freeDesc (↾fun _ => z)
    refine ⟨Presheaf.freeYonedaHomEquiv.symm b, ?_⟩
    apply Presheaf.freeYonedaHomEquiv.injective
    rw [Presheaf.freeYonedaHomEquiv_comp, Equiv.apply_symm_apply]
    apply (ModuleCat.freeHomEquiv (R := R)).injective
    apply ConcreteCategory.hom_ext
    intro i
    cases i
    change e.app (op U) (b t) = a t
    simpa [b, t] using hz

/-- Presheaves obtained from the free representable module presheaves by
colimits of diagrams with finitely many morphisms. -/
def finitePresentations : ObjectProperty (Cᵒᵖ ⥤ ModuleCat.{u} R) :=
  ObjectProperty.colimitsCardinalClosure
    (ObjectProperty.ofObj (fun U : C => Presheaf.freeYoneda U (unitModule.{u} R)))
    (Cardinal.aleph0 : Cardinal.{u})

/-- Finite presentations on a small site can be represented by a single
map between two finite sums of free module presheaves on representables. -/
theorem finitePresentations_iff_cokernelPresentation (F : Cᵒᵖ ⥤ ModuleCat.{u} R) :
    finitePresentations R C F ↔
      Nonempty (PhilipponFiniteCokernelPresentation.Presentation (freeChart R C) F) := by
  let : ∀ U : C, Projective (freeChart R C U) := projective_freeYoneda_unitModule R C
  exact ⟨PhilipponFiniteCokernelPresentation.presentation_of_colimitsCardinalClosure _,
    fun ⟨p⟩ => PhilipponFiniteCokernelPresentation.colimitsCardinalClosure_of_presentation _ p⟩

private theorem strongGenerator_freeYoneda :
    (ObjectProperty.ofObj (fun U : C =>
      Presheaf.freeYoneda U (unitModule.{u} R))).IsStrongGenerator := by
  have h := Presheaf.isStrongGenerator (strongGenerator_unitModule.{u} R) C
  convert h using 1
  ext P
  constructor
  · rintro ⟨U⟩
    let j : C × Subtype (ObjectProperty.singleton (unitModule R)) :=
      ⟨U, unitModule R, (ObjectProperty.singleton_iff _ _).2 rfl⟩
    exact ObjectProperty.ofObj_apply _ j
  · rintro ⟨⟨U, M, hM⟩⟩
    obtain rfl := (ObjectProperty.singleton_iff _ _).mp hM
    exact ⟨U⟩

/-- A module presheaf on a small site is a filtered colimit of terms
built from finite colimits of free representable module presheaves. -/
theorem ind_finitePresentations (F : Cᵒᵖ ⥤ ModuleCat.{u} R) :
    ObjectProperty.ind.{u} (finitePresentations R C) F := by
  let P := ObjectProperty.ofObj (fun U : C => Presheaf.freeYoneda U (unitModule.{u} R))
  let κ : Cardinal.{u} := Cardinal.aleph0
  let : Fact κ.IsRegular := Cardinal.fact_isRegular_aleph0
  have hP : P ≤ isCardinalPresentable _ κ := by
    rintro _ ⟨U⟩
    let := presentable_unitModule.{u} R
    rw [isCardinalPresentable_iff]
    infer_instance
  have := (strongGenerator_freeYoneda R C).isDense_colimitsCardinalClosure_ι hP
  let Q := P.colimitsCardinalClosure κ
  let hQ := IsCardinalFilteredGenerator.of_isDense_ι Q κ
    (P.colimitsCardinalClosure_le_isCardinalPresentable hP)
  obtain ⟨J, _, _, ⟨p⟩⟩ := hQ.exists_colimitsOfShape F
  let : IsFiltered J := isFiltered_of_isCardinalFiltered J κ
  exact ⟨J, inferInstance, inferInstance, p.toColimitPresentation, p.prop_diag_obj⟩

/-- Sheafification gives a filtered presentation by the sheafifications
of finite presentations on the small site. -/
theorem ind_sheafify_finitePresentations (J : GrothendieckTopology C)
    [HasWeakSheafify J (ModuleCat.{u} R)] (F : Sheaf J (ModuleCat.{u} R)) :
    ObjectProperty.ind.{u}
      ((finitePresentations R C).map (presheafToSheaf J (ModuleCat.{u} R))) F := by
  obtain ⟨K, _, _, p, hp⟩ := ind_finitePresentations R C F.obj
  let L := presheafToSheaf J (ModuleCat.{u} R)
  exact ⟨K, inferInstance, inferInstance, (p.map L).ofIso (sheafificationIso F).symm,
    fun i => (finitePresentations R C).prop_map_obj L (hp i)⟩

end PhilipponFiniteModulePresheafPresentation

end

end


