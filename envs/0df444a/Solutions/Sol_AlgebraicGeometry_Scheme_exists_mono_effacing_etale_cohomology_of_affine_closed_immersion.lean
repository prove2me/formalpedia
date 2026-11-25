-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_mono_effacing_etale_cohomology_of_affine_closed_immersion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-25T00:01:22.509849+00:00
-- url     : https://prove2.me/submissions/6f221199-f647-4da1-83b8-98ee95510986
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.RingTheory.Henselian
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_bounded_finite_constant_model_closed_fiber
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_surjective_effacing_unit_on_closed_fiber

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtaleBaseChangeMap (pushforwardCompIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleCohomologyEffacement

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private theorem pushout_killed {C : Type*} [Category* C] [Abelian C]
    {F F₁ T : C} (u : T ⟶ F₁) (v : T ⟶ F) (N : ℕ)
    (hF : N • 𝟙 F = 0) (hF₁ : N • 𝟙 F₁ = 0) : N • 𝟙 (pushout u v) = 0 := by
  apply pushout.hom_ext
  · calc
      pushout.inl u v ≫ (N • 𝟙 (pushout u v)) = (N • 𝟙 F₁) ≫ pushout.inl u v := by
        rw [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id, Category.id_comp]
      _ = _ := by rw [hF₁, zero_comp, comp_zero]
  · calc
      pushout.inr u v ≫ (N • 𝟙 (pushout u v)) = (N • 𝟙 F) ≫ pushout.inr u v := by
        rw [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id, Category.id_comp]
      _ = _ := by rw [hF, zero_comp, comp_zero]

/-- Push out an effacing monomorphism along the map from a model of the
cohomology class. The pushout preserves the fixed torsion bound. -/
theorem exists_mono_effacing_of_model {X Z : Scheme.{u}} (i : Z ⟶ X)
    {F₀ F F₁ : Ab X} (v : F₀ ⟶ F) (u : F₀ ⟶ F₁) [Mono u]
    (N : ℕ) (hF : N • 𝟙 F = 0) (hF₁ : N • 𝟙 F₁ = 0) (q : ℕ)
    (x₀ : ((pullbackSheaves i).obj F₀).H q)
    (hu : Sheaf.H.map ((pullbackSheaves i).map u) q x₀ = 0) :
    ∃ (G : Ab X) (k : F ⟶ G), Mono k ∧ N • 𝟙 G = 0 ∧
      Sheaf.H.map ((pullbackSheaves i).map k) q (Sheaf.H.map ((pullbackSheaves i).map v) q x₀) = 0 := by
  let H := pullbackSheaves i ⋙ Sheaf.functorH Z.smallEtaleTopology q
  refine ⟨pushout u v, pushout.inr u v, inferInstance, pushout_killed u v N hF hF₁, ?_⟩
  have h : H.map v ≫ H.map (pushout.inr u v) = H.map u ≫ H.map (pushout.inl u v) := by
    rw [← H.map_comp, ← H.map_comp, pushout.condition]
  change H.map (pushout.inr u v) (H.map v x₀) = 0
  rw [← ConcreteCategory.comp_apply, h, ConcreteCategory.comp_apply]
  change H.map (pushout.inl u v) (Sheaf.H.map ((pullbackSheaves i).map u) q x₀) = 0
  rw [hu, map_zero]

private abbrev constant (X : Scheme.{u}) := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- Direct image of the constant sheaf with coefficient group `M`. -/
abbrev constantDirectImage {X Y : Scheme.{u}} (p : Y ⟶ X) (M : AddCommGrpCat.{u}) : Ab X :=
  (pushforward p).obj ((constant Y).obj M)

/-- The map from a constant direct image to the direct image obtained after
pulling its constant sheaf along a further morphism. -/
def extendConstantDirectImage {X Y Y' : Scheme.{u}} (p : Y ⟶ X) (a : Y' ⟶ Y)
    (M : AddCommGrpCat.{u}) : constantDirectImage p M ⟶ constantDirectImage (a ≫ p) M :=
  (pushforward p).map ((pullbackAdjunction a).unit.app ((constant Y).obj M) ≫
    (pushforward a).map ((pullbackConstantIso a).hom.app M)) ≫
      (pushforwardCompIso p a).hom.app ((constant Y').obj M)

/-- A surjective further morphism gives a monomorphism of constant direct images. -/
theorem mono_extendConstantDirectImage {X Y Y' : Scheme.{u}} (p : Y ⟶ X) (a : Y' ⟶ Y)
    [Surjective a] (M : AddCommGrpCat.{u}) : Mono (extendConstantDirectImage p a M) := by
  let : Mono ((pullbackAdjunction a).unit.app ((constant Y).obj M)) :=
    PhilipponEtaleStalkPullback.unit_mono_of_surjective a _
  unfold extendConstantDirectImage
  infer_instance

/-- The comparison with the constant sheaf on the covering scheme preserves
vanishing after the inverse-image unit. -/
theorem extendConstantDirectImage_kills_of_unit {X Z Y Y' : Scheme.{u}}
    (i : Z ⟶ X) (p : Y ⟶ X) (a : Y' ⟶ Y) (M : AddCommGrpCat.{u}) (q : ℕ)
    (x : ((pullbackSheaves i).obj (constantDirectImage p M)).H q)
    (hx : Sheaf.H.map ((pullbackSheaves i).map ((pushforward p).map
      ((pullbackAdjunction a).unit.app ((constant Y).obj M)))) q x = 0) :
    Sheaf.H.map ((pullbackSheaves i).map (extendConstantDirectImage p a M)) q x = 0 := by
  let H := pullbackSheaves i ⋙ Sheaf.functorH Z.smallEtaleTopology q
  let f := (pushforward p).map ((pullbackAdjunction a).unit.app ((constant Y).obj M))
  let g := (pushforward p).map ((pushforward a).map ((pullbackConstantIso a).hom.app M)) ≫
    (pushforwardCompIso p a).hom.app ((constant Y').obj M)
  have h : extendConstantDirectImage p a M = f ≫ g := by
    unfold extendConstantDirectImage f g
    rw [Functor.map_comp, Category.assoc]
  change H.map (extendConstantDirectImage p a M) x = 0
  have hx' : H.map f x = 0 := hx
  rw [h, H.map_comp, ConcreteCategory.comp_apply]
  exact (congrArg (fun y => H.map g y) hx').trans (H.map g).hom.map_zero

/-- The coefficient group's exponent kills its constant direct image. -/
theorem constantDirectImage_killed {X Y : Scheme.{u}} (p : Y ⟶ X) (M : AddCommGrpCat.{u})
    (N : ℕ) (hM : N • 𝟙 M = 0) : N • 𝟙 (constantDirectImage p M) = 0 := by
  let t := Scheme.Etale.mk (𝟙 Y)
  let hT : IsTerminal t := IsTerminal.isTerminalOfObj (Scheme.Etale.forget Y) _ Over.mkIdTerminal
  let L := constant Y
  let : L.Additive := (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u} hT).left_adjoint_additive
  let P := L ⋙ pushforward p
  change N • 𝟙 (P.obj M) = 0
  rw [← P.map_id, ← P.map_nsmul, hM, P.map_zero]

/-- Effacement follows from representing a class by a sheaf embedded in a
finite constant direct image and killing its image by a finite cover. -/
theorem exists_mono_effacing_of_finite_constant_models {X Z : Scheme.{u}} (i : Z ⟶ X)
    (N : ℕ) (F : Ab X) (hF : N • 𝟙 F = 0) (q : ℕ)
    (x : ((pullbackSheaves i).obj F).H (q + 1))
    (hModel : ∃ (F₀ : Ab X) (v : F₀ ⟶ F) (x₀ : ((pullbackSheaves i).obj F₀).H (q + 1)),
      Sheaf.H.map ((pullbackSheaves i).map v) (q + 1) x₀ = x ∧
        ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (_ : IsFinite p) (_ : LocallyOfFinitePresentation p)
          (M : AddCommGrpCat.{u}) (_ : Finite M), N • 𝟙 M = 0 ∧
            ∃ m : F₀ ⟶ constantDirectImage p M, Mono m)
    (hKill : ∀ {Y : Scheme.{u}} (p : Y ⟶ X) (_ : IsFinite p) (M : AddCommGrpCat.{u}) (_ : Finite M)
      (y : ((pullbackSheaves i).obj (constantDirectImage p M)).H (q + 1)),
      ∃ (Y' : Scheme.{u}) (a : Y' ⟶ Y) (_ : IsFinite a) (_ : Surjective a),
        Sheaf.H.map ((pullbackSheaves i).map (extendConstantDirectImage p a M)) (q + 1) y = 0) :
    ∃ (G : Ab X) (k : F ⟶ G), Mono k ∧ N • 𝟙 G = 0 ∧
      Sheaf.H.map ((pullbackSheaves i).map k) (q + 1) x = 0 := by
  obtain ⟨F₀, v, x₀, hx, Y, p, hp, _, M, hMF, hM, m, hm⟩ := hModel
  obtain ⟨Y', a, _, ha, hk⟩ := hKill p hp M hMF
    (Sheaf.H.map ((pullbackSheaves i).map m) (q + 1) x₀)
  let : Surjective a := ha
  let : Mono m := hm
  let e := extendConstantDirectImage p a M
  let : Mono e := mono_extendConstantDirectImage p a M
  have he : Sheaf.H.map ((pullbackSheaves i).map (m ≫ e)) (q + 1) x₀ = 0 := by
    rw [Functor.map_comp, Sheaf.H.map_comp_apply]
    exact hk
  rw [← hx]
  exact exists_mono_effacing_of_model i v (m ≫ e) N hF
    (constantDirectImage_killed (a ≫ p) M N hM) (q + 1) x₀ he

end PhilipponEtaleCohomologyEffacement

end

open PhilipponEtaleCohomologyEffacement
open PhilipponEtaleSmallSite (pullbackSheaves)
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i]
    (N : ℕ) (hN : N ≠ 0) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (hF : N • 𝟙 F = 0)
    (q : ℕ) (x : ((pullbackSheaves i).obj F).H (q + 1)) :
    ∃ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (a : F ⟶ G),
      Mono a ∧ N • 𝟙 G = 0 ∧ Sheaf.H.map ((pullbackSheaves i).map a) (q + 1) x = 0 := by
  refine exists_mono_effacing_of_finite_constant_models i N F hF q x
    (AlgebraicGeometry.Scheme.exists_bounded_finite_constant_model_closed_fiber i N hN F hF q x) ?_
  intro Y p hp M hM y
  obtain ⟨Y', a, ha, hs, hy⟩ := AlgebraicGeometry.Scheme.exists_finite_surjective_effacing_unit_on_closed_fiber i p hp M hM q y
  exact ⟨Y', a, ha, hs, extendConstantDirectImage_kills_of_unit i p a M (q + 1) y hy⟩

end
