-- Prove2me | Definitions.Def_AlgebraicGeometry_SmallEtaleRelativeConstant
-- name    : AlgebraicGeometry_SmallEtaleRelativeConstant
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-20T19:48:20.969254+00:00
-- url     : https://prove2.me/theorems/ce7b7cde-e113-4ebe-ac36-569e9c811316
-- title:
--   Relative constant sheaf on the small étale site
-- statement:
--   For a closed immersion $i\colon Z\hookrightarrow X$ and an abelian group $A$, the relative constant sheaf is the kernel of the restriction morphism $\underline A_X\to i_*\underline A_Z$. On an étale $X$-scheme $V$, its sections are locally constant functions from $V$ to $A$ that vanish on the inverse image $V\times_X Z$. This realizes extension by zero of the constant sheaf on the complement.
-- source:
--   Stacks Project, Lemma 59.70.8, https://stacks.math.columbia.edu/tag/095L.

import Definitions.Def_AlgebraicGeometry_SmallEtaleAbelianDirectImage
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PhilipponKummerSequence
universe u
def underlying (X : Scheme.{u}) : X.Etale ⥤ Scheme.{u} :=
  Scheme.Etale.forget X ⋙ Over.forget X

instance continuous_underlying (X : Scheme.{u}) :
    (underlying X).IsContinuous X.smallEtaleTopology Scheme.etaleTopology := by
  have hle : Scheme.precoverage (@Etale.{u}) ≤ (MorphismProperty.precoverage (@Etale.{u})) :=
    inf_le_right
  have hc := MorphismProperty.isContinuous_comap_forget (S := X) (P := @Etale)
    (Scheme.precoverage @Etale) hle
  rw [MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology _ hle] at hc
  letI : (Scheme.Etale.forget X).IsContinuous X.smallEtaleTopology (Scheme.etaleTopology.over X) := hc
  exact Functor.isContinuous_comp _ _ _ (Scheme.etaleTopology.over X) _


end PhilipponKummerSequence

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


namespace PhilipponEtaleConstantDegreeZero

universe u
variable (X : Scheme.{u}) (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]

/-- Continuous functions with values in the discrete coefficient group form
an étale sheaf by restriction of the fpqc sheaf of continuous functions. -/
def continuousSheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  ((PhilipponKummerSequence.underlying X).sheafPushforwardContinuous AddCommGrpCat
    X.smallEtaleTopology Scheme.etaleTopology).obj
    ⟨continuousMapPresheafAb A, (isSheaf_fpqcTopology_continuousMapPresheafAb A).of_le
      (Scheme.etaleTopology_le_proetaleTopology.trans Scheme.proetaleTopology_le_fpqcTopology)⟩

end PhilipponEtaleConstantDegreeZero

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 850000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleConstantDegreeZero (continuousSheaf)


namespace PhilipponEtaleClosedCover

universe u
variable {X Y Z : Scheme.{u}}
variable (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]

private def precompose (f : Y ⟶ Z) : C(Z, A) →+ C(Y, A) where
  toFun h := h.comp ⟨f, f.continuous⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem projection_naturality (f : Y ⟶ X) {U V : X.Etale} (g : U ⟶ V) :
    ((baseChange f).map g).left ≫ pullback.fst V.hom f =
      pullback.fst U.hom f ≫ g.left :=
  pullback.lift_fst _ _ _

/-- Restriction of continuous coefficient functions to the pullback of a
scheme morphism. -/
def restriction (i : Y ⟶ X) :
    continuousSheaf X A ⟶ (pushforward i).obj (continuousSheaf Y A) :=
  ⟨{
    app W := AddCommGrpCat.ofHom (precompose A (pullback.fst W.unop.hom i))
    naturality {U V} f := by
      apply ConcreteCategory.hom_ext
      intro s
      change C(U.unop.left, A) at s
      apply ContinuousMap.ext
      intro x
      change s (f.unop.left (pullback.fst V.unop.hom i x)) =
        s (pullback.fst U.unop.hom i (((baseChange i).map f.unop).left x))
      exact congrArg s (congrArg (fun k : (_ : Scheme) ⟶ (_ : Scheme) => k x)
        (projection_naturality i f.unop).symm)
  }⟩

end PhilipponEtaleClosedCover

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedCover (restriction)

namespace PhilipponEtaleRelativeCohomology
universe u
private abbrev AbelianSheaves (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

section Restriction
variable {X Z : Scheme.{u}} (i : Z ⟶ X)
variable (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
/-- Relative constant sheaf for a closed subscheme, defined as the kernel
of the restriction map to its direct image. -/
def relativeSheaf : AbelianSheaves X := kernel (restriction A i)

end Restriction

/-- The canonical relative constant sheaf, using the discrete topology on
the underlying abelian group of coefficients. -/
def relativeConstant {X Z : Scheme.{u}} (i : Z ⟶ X) (A : Type u) [AddCommGroup A] :
    AbelianSheaves X :=
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  relativeSheaf i A

end PhilipponEtaleRelativeCohomology

end

end


