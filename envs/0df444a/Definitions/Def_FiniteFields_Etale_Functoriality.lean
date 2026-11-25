-- Prove2me | Definitions.Def_FiniteFields_Etale_Functoriality
-- name    : FiniteFields_Etale_Functoriality
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-25T11:35:02.905001+00:00
-- url     : https://prove2.me/theorems/6fe5523b-d49e-592d-88a0-18b407454951
-- title:
--   Base change of étale sites, direct image $f_*$ and inverse image $f^{-1}$ of étale sheaves
-- statement:
--   Let $f\colon X\to Y$ be a morphism of schemes.
--
--   * **Base change** sends a scheme $U$ étale over $Y$ to $U\times_Y X$, étale over $X$ (and similarly for weakly étale schemes). It preserves finite limits and is continuous for the étale (resp. pro-étale) topologies.
--   * The **direct image** $f_*$ of abelian sheaves on the small étale sites is $(f_*F)(U)=F(U\times_Y X)$.
--   * The **inverse image** $f^{-1}$ is the left adjoint of $f_*$, obtained as the sheaf pullback along base change; the adjunction $f^{-1}\dashv f_*$ is part of the file.
--   * Direct images are compatible with composition, $g_*\circ f_*\cong (g\circ f)_*$, and inverse images contravariantly, $(g\circ f)^{-1}\cong f^{-1}\circ g^{-1}$.
-- source:
--   The Stacks Project, Chapter 59 (Étale Cohomology), Sections 59.34 (Functoriality of small étale topos), 59.35 (Direct images), 59.36 (Inverse image).

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Definitions.Def_FiniteFields_Etale_Cohomology
import Definitions.Def_FiniteFields_Etale_Sites

noncomputable section

open CategoryTheory

namespace FiniteFields.Etale

open AlgebraicGeometry CategoryTheory.Limits CategoryTheory.MorphismProperty

universe u

-- Portage v4.33 : option nécessaire avec Mathlib `0df444a` (comme dans `Sites/Etale.lean`).
set_option backward.isDefEq.respectTransparency.types false

/-- Actual scheme base change on the native small etale site. -/
def smallEtaleBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SmallEtaleSite Y ⥤ SmallEtaleSite X := by
  change MorphismProperty.Over @AlgebraicGeometry.Etale ⊤ Y ⥤
    MorphismProperty.Over @AlgebraicGeometry.Etale ⊤ X
  exact MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f

/-- Actual scheme base change on the native small pro-etale site. -/
def proEtaleBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ProEtaleSite Y ⥤ ProEtaleSite X := by
  change MorphismProperty.Over @AlgebraicGeometry.WeaklyEtale ⊤ Y ⥤
    MorphismProperty.Over @AlgebraicGeometry.WeaklyEtale ⊤ X
  exact MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ f

/-- The structural morphism of a base-changed small-etale object is the second pullback map. -/
@[simp]
theorem smallEtaleBaseChange_obj_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : SmallEtaleSite Y) :
    ((smallEtaleBaseChange f).obj U).hom = pullback.snd U.hom f :=
  rfl

/-- The structural morphism of a base-changed small-pro-etale object is the second pullback map. -/
@[simp]
theorem proEtaleBaseChange_obj_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : ProEtaleSite Y) :
    ((proEtaleBaseChange f).obj U).hom = pullback.snd U.hom f :=
  rfl

/-- Restricted small-etale base change preserves finite limits. -/
instance smallEtaleBaseChange_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (smallEtaleBaseChange f) := by
  change PreservesFiniteLimits
    (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f)
  infer_instance

/-- Restricted small-pro-etale base change preserves finite limits. -/
instance proEtaleBaseChange_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (proEtaleBaseChange f) := by
  change PreservesFiniteLimits
    (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ f)
  infer_instance





private def smallEtaleBaseChangeCompIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleBaseChange (f ≫ g) ≅
      smallEtaleBaseChange g ⋙ smallEtaleBaseChange f := by
  change MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ (f ≫ g) ≅
    MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g ⋙
      MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f
  exact MorphismProperty.Over.pullbackComp f g



/-- Actual restricted base change is continuous for the native small etale topologies. -/
instance smallEtaleBaseChange_isContinuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtaleBaseChange f).IsContinuous
      (smallEtaleSiteTopology Y) (smallEtaleSiteTopology X) := by
  letI : HasFiniteLimits (SmallEtaleSite Y) := by
    change HasFiniteLimits
      (MorphismProperty.Over @AlgebraicGeometry.Etale ⊤ Y)
    infer_instance
  letI : RepresentablyFlat (smallEtaleBaseChange f) :=
    flat_of_preservesFiniteLimits _
  rw [Functor.isContinuous_iff_coverPreserving]
  constructor
  intro U S hS
  change S.functorPushforward
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f) ∈
    X.smallGrothendieckTopology @AlgebraicGeometry.Etale _
  rw [Functor.mem_restrictedTopology_iff]
  rw [← Sieve.functorPushforward_comp]
  change S.functorPushforward
      (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ Y ⋙
        CategoryTheory.Over.pullback f) ∈
    (Scheme.etaleTopology.over X) _
  rw [Sieve.functorPushforward_comp]
  apply (GrothendieckTopology.coverPreserving_overPullback
    (J := Scheme.etaleTopology) f).cover_preserve
  exact Functor.mem_restrictedTopology_iff.mp hS

/-- Actual restricted base change is continuous for the native small pro-etale topologies. -/
instance proEtaleBaseChange_isContinuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (proEtaleBaseChange f).IsContinuous
      (proEtaleSiteTopology Y) (proEtaleSiteTopology X) := by
  letI : HasFiniteLimits (ProEtaleSite Y) := by
    change HasFiniteLimits
      (MorphismProperty.Over @AlgebraicGeometry.WeaklyEtale ⊤ Y)
    infer_instance
  letI : RepresentablyFlat (proEtaleBaseChange f) :=
    flat_of_preservesFiniteLimits _
  rw [Functor.isContinuous_iff_coverPreserving]
  constructor
  intro U S hS
  change S.functorPushforward
      (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ f) ∈
    Scheme.ProEt.topology X _
  change S ∈
    (Scheme.proetalePrecoverage.comap
      (MorphismProperty.Over.forget @AlgebraicGeometry.WeaklyEtale ⊤ Y ⋙
        CategoryTheory.Over.forget Y)).toGrothendieck U at hS
  have htopY :
      (Scheme.proetalePrecoverage.comap
        (MorphismProperty.Over.forget @AlgebraicGeometry.WeaklyEtale ⊤ Y ⋙
          CategoryTheory.Over.forget Y)).toGrothendieck =
        (MorphismProperty.Over.forget @AlgebraicGeometry.WeaklyEtale ⊤ Y).restrictedTopology
          (Scheme.proetaleTopology.over Y) :=
    MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology
      Scheme.proetalePrecoverage
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale
  rw [htopY] at hS
  change S ∈
    (Scheme.ProEt.forget Y).restrictedTopology (Scheme.proetaleTopology.over Y) U at hS
  have htopX : Scheme.ProEt.topology X =
      (MorphismProperty.Over.forget @AlgebraicGeometry.WeaklyEtale ⊤ X).restrictedTopology
        (Scheme.proetaleTopology.over X) :=
    MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology
      Scheme.proetalePrecoverage
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale
  rw [htopX]
  change S.functorPushforward (proEtaleBaseChange f) ∈
    (Scheme.ProEt.forget X).restrictedTopology (Scheme.proetaleTopology.over X) _
  apply Functor.mem_restrictedTopology_iff.mpr
  rw [← Sieve.functorPushforward_comp]
  change S.functorPushforward
      (Scheme.ProEt.forget Y ⋙ CategoryTheory.Over.pullback f) ∈
    (Scheme.proetaleTopology.over X) _
  rw [Sieve.functorPushforward_comp]
  apply (GrothendieckTopology.coverPreserving_overPullback
    (J := Scheme.proetaleTopology) f).cover_preserve
  exact Functor.mem_restrictedTopology_iff.mp hS

/-- Direct image of abelian sheaves along a scheme map on the native small etale sites. -/
def smallEtalePushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SmallEtaleAbelianSheaf X ⥤ SmallEtaleAbelianSheaf Y :=
  (smallEtaleBaseChange f).sheafPushforwardContinuous
    Ab.{u + 1} (smallEtaleSiteTopology Y) (smallEtaleSiteTopology X)

/-- Inverse image of abelian sheaves along a scheme map on the native small etale sites. -/
def smallEtalePullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SmallEtaleAbelianSheaf Y ⥤ SmallEtaleAbelianSheaf X :=
  (smallEtaleBaseChange f).sheafPullback
    Ab.{u + 1} (smallEtaleSiteTopology Y) (smallEtaleSiteTopology X)

/-- The native inverse-image/direct-image adjunction on small etale abelian sheaves. -/
def smallEtalePullbackPushforwardAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtalePullback f ⊣ smallEtalePushforward f :=
  (smallEtaleBaseChange f).sheafAdjunctionContinuous
    Ab.{u + 1} (smallEtaleSiteTopology Y) (smallEtaleSiteTopology X)









/-- Direct image respects composition on small-etale sheaves. -/
def smallEtalePushforwardComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtalePushforward f ⋙ smallEtalePushforward g ≅
      smallEtalePushforward (f ≫ g) :=
  Functor.sheafPushforwardContinuousComp'
    (smallEtaleBaseChangeCompIso f g).symm Ab.{u + 1}
      (smallEtaleSiteTopology Z) (smallEtaleSiteTopology Y) (smallEtaleSiteTopology X)



/-- Inverse image is contravariantly compatible with composition on small-etale sheaves. -/
def smallEtalePullbackComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtalePullback (f ≫ g) ≅
      smallEtalePullback g ⋙ smallEtalePullback f :=
  (Adjunction.leftAdjointCompIso
    (smallEtalePullbackPushforwardAdjunction g)
    (smallEtalePullbackPushforwardAdjunction f)
    (smallEtalePullbackPushforwardAdjunction (f ≫ g))
    (smallEtalePushforwardComp f g)).symm











end FiniteFields.Etale


