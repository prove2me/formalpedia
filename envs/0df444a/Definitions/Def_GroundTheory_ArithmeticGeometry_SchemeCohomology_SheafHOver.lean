-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafHOver
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafHOver
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:03:58.081867+00:00
-- url     : https://prove2.me/theorems/2ce668e5-02e2-43d4-99a2-64d49eed00ee
-- title:
--   Sheaf HOver
-- statement:
--   Definitions and structural lemmas for Sheaf HOver, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafHOver.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_OverShriek
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_freeSheafHomAddEquiv_naturality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open CategoryTheory Limits Opposite Abelian
universe w' v u
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] (U : C)
section Exact
instance overPullback_additive : (J.overPullback AddCommGrpCat.{v} U).Additive where
  map_add := rfl
instance overPullback_isRightAdjoint : (J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint :=
  ⟨_, ⟨sheafShriekAdjunction J U⟩⟩
instance overPullback_preservesFiniteLimits :
    PreservesFiniteLimits (J.overPullback AddCommGrpCat.{v} U) := inferInstance
variable [HasSheafify (J.over U) AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{v})] [(J.over U).HasSheafCompose (forget AddCommGrpCat.{v})]
instance overPullback_preservesEpimorphisms :
    (J.overPullback AddCommGrpCat.{v} U).PreservesEpimorphisms where
  preserves {F G} φ _ := by
    have : Sheaf.IsLocallySurjective φ := (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{v}) φ).2 inferInstance
    have : Sheaf.IsLocallySurjective ((J.overPullback AddCommGrpCat.{v} U).map φ) :=
      Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) φ.hom
    exact (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{v}) _).1 this
instance overPullback_preservesFiniteColimits :
    PreservesFiniteColimits (J.overPullback AddCommGrpCat.{v} U) := by
  have h := (Functor.preservesFiniteLimits_tfae (J.overPullback AddCommGrpCat.{v} U)).out 3 0
  refine ((Functor.preservesFiniteColimits_tfae (J.overPullback AddCommGrpCat.{v} U)).out 0 3).1 ?_
  intro S hS
  have := hS.epi_g
  exact ⟨(h.1 inferInstance S hS).1, (J.overPullback AddCommGrpCat.{v} U).map_epi S.g⟩
end Exact
section Const
variable [HasSheafify (J.over U) AddCommGrpCat.{v}]
omit [HasSheafify J AddCommGrpCat.{v}] in

noncomputable def overConstHomAddEquiv (G : Sheaf (J.over U) AddCommGrpCat.{v}) :
    ((constantSheaf (J.over U) AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)) ⟶ G) ≃+
      G.obj.obj (op (Over.mk (𝟙 U))) :=
  ((constantSheafAdj (J.over U) AddCommGrpCat.{v} (Over.mkIdTerminal (X := U))).homAddEquiv _ G).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _)
omit [HasSheafify J AddCommGrpCat.{v}] in
lemma overConstHomAddEquiv_naturality {G G' : Sheaf (J.over U) AddCommGrpCat.{v}}
    (a : (constantSheaf (J.over U) AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)) ⟶ G)
    (φ : G ⟶ G') :
    overConstHomAddEquiv J U G' (a ≫ φ) = φ.hom.app _ (overConstHomAddEquiv J U G a) := by
  simp only [overConstHomAddEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply,
    Adjunction.homEquiv_naturality_right]
  rfl
noncomputable def overUnitMap :
    (constantSheaf (J.over U) AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)) ⟶
      (freeSheaf J U).over U :=
  (overConstHomAddEquiv J U _).symm (freeSheafHomAddEquiv U (freeSheaf J U) (𝟙 _))
end Const
section Main
variable [HasSheafify (J.over U) AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{v})] [(J.over U).HasSheafCompose (forget AddCommGrpCat.{v})]
  [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})] [HasExt.{w'} (Sheaf (J.over U) AddCommGrpCat.{v})]
noncomputable def overCohomologyMap (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    Ext (freeSheaf J U) F n →+ Sheaf.H (F.over U) n :=
  ((Ext.mk₀ (overUnitMap J U)).precomp _ (zero_add n)).comp
    ((J.overPullback AddCommGrpCat.{v} U).mapExtAddHom (freeSheaf J U) F n)
lemma overCohomologyMap_apply (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ)
    (x : Ext (freeSheaf J U) F n) :
    overCohomologyMap J U F n x = (Ext.mk₀ (overUnitMap J U)).comp
      (x.mapExactFunctor (J.overPullback AddCommGrpCat.{v} U)) (zero_add n) := rfl
lemma overCohomologyMap_comp_mk₀ {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n : ℕ)
    (x : Ext (freeSheaf J U) F n) :
    overCohomologyMap J U G n (x.comp (Ext.mk₀ f) (add_zero n)) =
      (overCohomologyMap J U F n x).comp (Ext.mk₀ ((J.overPullback AddCommGrpCat.{v} U).map f))
        (add_zero n) := by
  rw [overCohomologyMap_apply, overCohomologyMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]
lemma overCohomologyMap_comp_extClass {S : ShortComplex (Sheaf J AddCommGrpCat.{v})}
    (hS : S.ShortExact) (n : ℕ) (x : Ext (freeSheaf J U) S.X₃ n) :
    overCohomologyMap J U S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (overCohomologyMap J U S.X₃ n x).comp
        (hS.map_of_exact (J.overPullback AddCommGrpCat.{v} U)).extClass rfl := by
  rw [overCohomologyMap_apply, overCohomologyMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm
lemma overCohomologyMap_zero_bijective (F : Sheaf J AddCommGrpCat.{v}) :
    Function.Bijective (overCohomologyMap J U F 0) := by
  let Θ : (freeSheaf J U ⟶ F) → _ := fun g =>
    overUnitMap J U ≫ (J.overPullback AddCommGrpCat.{v} U).map g
  have key : ∀ g, overConstHomAddEquiv J U (F.over U) (Θ g) = freeSheafHomAddEquiv U F g := by
    intro g
    simp only [Θ]
    rw [overConstHomAddEquiv_naturality, overUnitMap]
    refine (congrArg (((J.overPullback AddCommGrpCat.{v} U).map g).hom.app (op (Over.mk (𝟙 U))))
      (AddEquiv.apply_symm_apply _ _)).trans ?_
    have := freeSheafHomAddEquiv_naturality U (𝟙 (freeSheaf J U)) g
    rw [Category.id_comp] at this
    exact this.symm
  have hΘ : Function.Bijective Θ := by
    have : Θ = (overConstHomAddEquiv J U (F.over U)).symm ∘ freeSheafHomAddEquiv U F :=
      funext fun g => ((AddEquiv.symm_apply_eq _).2 (key g).symm).symm
    rw [this]
    exact (AddEquiv.bijective _).comp (AddEquiv.bijective _)
  have : ⇑(overCohomologyMap J U F 0) = Ext.addEquiv₀.symm ∘ Θ ∘ Ext.addEquiv₀ := by
    funext x
    obtain ⟨g, rfl⟩ := Ext.addEquiv₀.symm.surjective x
    simp only [Function.comp_apply, AddEquiv.apply_symm_apply, Θ]
    rw [Ext.addEquiv₀_symm_apply, Ext.addEquiv₀_symm_apply, overCohomologyMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  rw [this]
  exact (AddEquiv.bijective _).comp (hΘ.comp (AddEquiv.bijective _))
attribute [local instance] Ext.subsingleton_of_injective in

theorem overCohomologyMap_bijective [EnoughInjectives (Sheaf J AddCommGrpCat.{v})] (n : ℕ) :
    ∀ F : Sheaf J AddCommGrpCat.{v}, Function.Bijective (overCohomologyMap J U F n) := by
  induction n with
  | zero => exact overCohomologyMap_zero_bijective J U
  | succ n hn =>
    intro F
    let I : InjectivePresentation F := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have : Injective S.X₂ := I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have hS' := hS.map_of_exact (J.overPullback AddCommGrpCat.{v} U)
    have : Injective (S.map (J.overPullback AddCommGrpCat.{v} U)).X₂ :=
      (J.overPullback AddCommGrpCat.{v} U).injective_obj_of_injective I.injective
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (overCohomologyMap J U S.X₂ n) (overCohomologyMap J U S.X₃ n)
      (overCohomologyMap J U S.X₁ (n + 1))
      (by ext x; exact (overCohomologyMap_comp_mk₀ J U S.g n x).symm)
      (by ext x; exact (overCohomologyMap_comp_extClass J U hS n x).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (freeSheaf J U) hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' _ hS' n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ hS' y₁ (by subsingleton) rfl)
noncomputable def cohomologyPresheafOverAddEquiv [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    (F.cohomologyPresheaf n).obj (op U) ≃+ Sheaf.H (F.over U) n :=
  AddEquiv.ofBijective (overCohomologyMap J U F n) (overCohomologyMap_bijective J U n F)
end Main
section Small
variable {C : Type v} [SmallCategory C] (J : GrothendieckTopology C) (U : C)
  [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})] [HasExt.{w'} (Sheaf (J.over U) AddCommGrpCat.{v})]
noncomputable def cohomologyPresheafOverAddEquivOfSmall (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    (F.cohomologyPresheaf n).obj (op U) ≃+ Sheaf.H (F.over U) n :=
  cohomologyPresheafOverAddEquiv J U F n
end Small
end GroundTheory.Arith.SchemeCoh


