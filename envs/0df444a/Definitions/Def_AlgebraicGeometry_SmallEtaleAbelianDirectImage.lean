-- Prove2me | Definitions.Def_AlgebraicGeometry_SmallEtaleAbelianDirectImage
-- name    : AlgebraicGeometry_SmallEtaleAbelianDirectImage
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-20T18:49:28.051448+00:00
-- url     : https://prove2.me/theorems/048123a3-962d-4ddd-8c2a-7967011c1bb6
-- title:
--   Direct image of abelian sheaves on small étale sites
-- statement:
--   A morphism $i\colon Z\to X$ induces a direct-image
--   functor on small étale abelian sheaves. It assigns to a sheaf $F$ on $Z$ the sheaf whose
--   sections on an étale $X$-scheme $U$ are $F(U\times_X Z)$.
-- source:
--   Stacks Project, Section 59.34, https://stacks.math.columbia.edu/tag/04I0, and Section 59.46, https://stacks.math.columbia.edu/tag/04E1.

import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.MorphismProperty.CommaSites
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.ObjectProperty.LimitsClosure
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.PreservesLimits
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Tactic.Ring

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite


namespace PhilipponEtaleBaseChangeComparison

universe u
variable {X Y : Scheme.{u}}

/-- Base change on the categories underlying the small étale sites. -/
abbrev baseChange (f : Y ⟶ X) : X.Etale ⥤ Y.Etale :=
  MorphismProperty.Over.pullback (@Etale) ⊤ f

/-- Pullback along an étale arrow commutes with base change. -/
theorem map_isPullback (f : Y ⟶ X) {U V : X.Etale} (g : U ⟶ V) :
    IsPullback (pullback.fst U.hom f) ((baseChange f).map g).left g.left
      (pullback.fst V.hom f) := by
  have h₁ : g.left ≫ V.hom = U.hom := MorphismProperty.Over.w g
  have h₂ : ((baseChange f).map g).left ≫ pullback.snd V.hom f = pullback.snd U.hom f := by
    change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    rw [pullback.lift_snd]
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback V.hom f)
  · simpa only [h₁, h₂] using IsPullback.of_hasPullback U.hom f
  · symm
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    rw [pullback.lift_fst]

/-- Pullback along an arbitrary morphism preserves small étale covering sieves. -/
theorem coverPreserving (f : Y ⟶ X) :
    CoverPreserving X.smallEtaleTopology Y.smallEtaleTopology (baseChange f) where
  cover_preserve {V S} h := by
    rw [← Sieve.ofArrows_category S, Scheme.ofArrows_mem_smallEtaleTopology_iff] at h
    rw [← Sieve.ofArrows_category S, Sieve.functorPushforward_ofArrows,
      Scheme.ofArrows_mem_smallEtaleTopology_iff]
    simp only [Set.eq_univ_iff_forall, Set.mem_iUnion, Set.mem_range] at h ⊢
    intro w
    obtain ⟨g, z, hz⟩ := h (pullback.fst V.hom f w)
    obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback
      (map_isPullback f g.obj.hom) z w hz
    exact ⟨g, t, ht⟩

/-- Base change along a surjection preserves and reflects covering sieves.
This part does not need an equivalence of the underlying categories. -/
theorem covering_iff (f : Y ⟶ X) [Surjective f] {V : X.Etale} (S : Sieve V) :
    S.functorPushforward (baseChange f) ∈ Y.smallEtaleTopology _ ↔
      S ∈ X.smallEtaleTopology _ := by
  refine ⟨?_, (coverPreserving f).cover_preserve⟩
  rw [← Sieve.ofArrows_category S, Sieve.functorPushforward_ofArrows,
    Scheme.ofArrows_mem_smallEtaleTopology_iff, Scheme.ofArrows_mem_smallEtaleTopology_iff]
  simp only [Set.eq_univ_iff_forall, Set.mem_iUnion, Set.mem_range]
  intro h v
  obtain ⟨w, hw⟩ := (show Function.Surjective (pullback.fst V.hom f) from
    (inferInstance : Surjective (pullback.fst V.hom f)).surj) v
  obtain ⟨g, z, hz⟩ := h w
  refine ⟨g, pullback.fst g.obj.left.hom f z, ?_⟩
  have hcomm := congrArg (fun a : (_ : Scheme) ⟶ (_ : Scheme) => a z)
    (map_isPullback f g.obj.hom).w
  exact hcomm.trans ((congrArg (pullback.fst V.hom f) hz).trans hw)

instance baseChange_isContinuous (f : Y ⟶ X) :
    (baseChange f).IsContinuous X.smallEtaleTopology Y.smallEtaleTopology := by
  letI : PreservesFiniteLimits (baseChange f) := inferInstanceAs
    (PreservesFiniteLimits (MorphismProperty.Over.pullback (@Etale) ⊤ f))
  have : RepresentablyFlat (baseChange f) := flat_of_preservesFiniteLimits _
  exact Functor.isContinuous_iff_coverPreserving.mpr (coverPreserving f)

end PhilipponEtaleBaseChangeComparison

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison


namespace PhilipponEtaleClosedPushforward

universe u
variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-- Direct image of an étale abelian sheaf by a morphism of schemes. -/
def pushforward : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} ⥤
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (baseChange i).sheafPushforwardContinuous _ _ _

instance : (pushforward i).Additive where
  map_add := rfl

instance : PreservesFiniteLimits (pushforward i) := by
  let e := (baseChange i).sheafPushforwardContinuousCompSheafToPresheafIso
    AddCommGrpCat.{u} X.smallEtaleTopology Z.smallEtaleTopology
  have : PreservesFiniteLimits
      (pushforward i ⋙ sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

end PhilipponEtaleClosedPushforward

end

end


