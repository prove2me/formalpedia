-- Prove2me | Definitions.Def_ProEtale_Topology_Coherent_Affine
-- name    : ProEtale_Topology_Coherent_Affine
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:42:01.676235+00:00
-- url     : https://prove2.me/theorems/b098e8f7-053c-57a1-92e5-022058ea3dc5
-- title:
--   Finite coproducts, extensivity, pullbacks and effective epimorphisms in categories of affine schemes over a base, such as the affine étale site
-- statement:
--   Let $S$ be a scheme and $P$ a class of morphisms of schemes that is local at the source for the Zariski topology, stable under base change, multiplicative (contains identities and is closed under composition) and satisfies right cancellation ($g\circ f \in P$ and $g \in P$ imply $f \in P$). Consider the category of affine schemes $\operatorname{Spec} R$ over $S$ whose structure morphism lies in $P$ (for $P$ = étale, this is the small affine étale site $S_{\text{affét}}$).
--
--   Principal results:
--   1. General preservation facts for the comparison functor from costructured arrows $F(c) \to X$ to the over category of $X$: it preserves connected limits and colimits that $F$ preserves; and for the $P$-restricted versions it preserves pullbacks (when $P$ is stable under base change) and colimits of a given shape that exist in the source categories.
--   2. For Zariski-local-at-source $P$, the subcategory of objects whose structure map lies in $P$ is closed under small coproducts (in costructured-arrow and comma categories), provided the relevant functor preserves them.
--   3. The category of affine $S$-schemes with structure map in $P$ has finite coproducts and is finitary extensive.
--   4. For the affine étale site: the functor to étale $S$-schemes reflects effective epimorphisms; every morphism $X \to Y$ of affine étale $S$-schemes whose underlying morphism of schemes is surjective is an effective epimorphism; and the affine étale site has pullbacks.
--
--   These facts make the affine étale site a finitary extensive category with pullbacks, so that its topology can be treated as a coherent (finitary) topology; they are used for the comparison between étale and pro-étale sites.
--
--   **Formalization Note** The category is `P.CostructuredArrow ⊤ Scheme.Spec S` (objects are commutative rings `R` with a `P`-morphism `Spec R ⟶ S`; morphisms are ring maps), and `S.AffineEtale` with functor `AffineEtale.Spec S`. Named declarations: `AlgebraicGeometry.Scheme.IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete`, `IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete_commaObj`, `AffineEtale.effectiveEpi_of_surjective`; the remaining results are unnamed instances (`HasFiniteCoproducts`, `FinitaryExtensive`, `ReflectsEffectiveEpis`, `HasPullbacks S.AffineEtale`, and preservation instances for `CostructuredArrow.toOver`). Surjectivity in `effectiveEpi_of_surjective` is the Mathlib class `Surjective` on `Spec.map f.left.unop`. Index types of coproducts are required to be `Small.{u}`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Coherent/Affine.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
import Mathlib.CategoryTheory.Sites.CoproductSheafCondition
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Preserves
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.Topology.Sets.CompactOpenCovered
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.Hom
import Definitions.Def_ProEtale_FromPi1_Etale
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Cover_MorphismProperty
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Extensive
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Morphisms_UnderlyingMap
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_MorphismProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_Sieves
import Definitions.Def_ProEtale_Topology_Coherent_Etale
import Definitions.Def_ProEtale_Topology_Flat_QuasiCompactCover

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Affine étale site
-/

universe u

open CategoryTheory Opposite Limits

namespace CategoryTheory

section

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (X : D)

instance inst_TopologyCoherentAffine_L29 (J : Type*) [Category J] [IsConnected J] [HasLimitsOfShape J C]
    [PreservesLimitsOfShape J F]
    [HasLimitsOfShape J D] :
    PreservesLimitsOfShape J (CostructuredArrow.toOver F X) where
  preservesLimit {K} := by
    have : PreservesLimit K (CostructuredArrow.toOver F X ⋙ Over.forget X) := by
      change PreservesLimit K (CostructuredArrow.proj F X ⋙ F)
      infer_instance
    apply Limits.preservesLimit_of_reflects_of_preserves _ (Over.forget X)

instance inst_TopologyCoherentAffine_L39 (J : Type*) [Category J] [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    [HasColimitsOfShape J (Over X)] [PreservesColimitsOfShape J F] :
    PreservesColimitsOfShape J (CostructuredArrow.toOver F X) where
  preservesColimit {K} := by
    have : PreservesColimit K (CostructuredArrow.toOver F X ⋙ Over.forget X) := by
      change PreservesColimit K (CostructuredArrow.proj F X ⋙ F)
      infer_instance
    apply Limits.preservesColimit_of_reflects_of_preserves _ (Over.forget X)

end

namespace MorphismProperty

variable {C D : Type*} [Category C] [Category D]
variable (P : MorphismProperty D) (Q : MorphismProperty C) [Q.IsMultiplicative] (F : C ⥤ D) (X : D)

namespace CostructuredArrow

section Limits

variable [P.IsStableUnderBaseChange]
  [P.IsStableUnderComposition] [P.HasOfPostcompProperty P]
  [PreservesLimitsOfShape WalkingCospan F] [HasPullbacks C] [HasPullbacks D]

instance inst_TopologyCoherentAffine_L63 : PreservesLimitsOfShape WalkingCospan (CostructuredArrow.toOver P F X) := by
  have : PreservesLimitsOfShape WalkingCospan
      (CostructuredArrow.toOver P F X ⋙ Over.forget P ⊤ X) := by
    change PreservesLimitsOfShape WalkingCospan <|
      CostructuredArrow.forget P ⊤ F X ⋙ CategoryTheory.CostructuredArrow.toOver F X
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget _ _ X)

end Limits

section Colimits

variable (J : Type*) [Category J] [HasColimitsOfShape J C] [HasColimitsOfShape J D]
  [HasColimitsOfShape J (P.Over ⊤ X)] [PreservesColimitsOfShape J F]
  [(MorphismProperty.commaObj F (Functor.fromPUnit X) P).IsClosedUnderColimitsOfShape J]

instance inst_TopologyCoherentAffine_L79 : PreservesColimitsOfShape J (CostructuredArrow.toOver P F X) := by
  have : CreatesColimitsOfShape J (CostructuredArrow.forget P ⊤ F X) :=
    MorphismProperty.Comma.forgetCreatesColimitsOfShapeOfClosed
      (L := F) (R := .fromPUnit X) (P := P) (J := J)
  have : PreservesColimitsOfShape J
      (CostructuredArrow.toOver P F X ⋙ Over.forget P ⊤ X) := by
    change PreservesColimitsOfShape J <|
      CostructuredArrow.forget P ⊤ F X ⋙ CategoryTheory.CostructuredArrow.toOver F X
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves _ (Over.forget _ _ X)

end Colimits

end CostructuredArrow

end MorphismProperty

end CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

variable {S : Scheme.{u}}

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P]

instance IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete
    {ι : Type*} [Small.{u} ι] {C : Type*} [Category C] [HasColimitsOfShape (Discrete ι) C]
    (L : C ⥤ Scheme.{u}) [PreservesColimitsOfShape (Discrete ι) L] (X : Scheme.{u}) :
    (P.costructuredArrowObj L (X := X)).IsClosedUnderColimitsOfShape (Discrete ι) := by
  refine CostructuredArrow.isClosedUnderColimitsOfShape ?_ ?_ ?_ _
  · intro D _
    exact Sigma.cocone _
  · intro D
    exact coproductIsCoproduct' _
  · intro D _ X s h
    exact IsZariskiLocalAtSource.sigmaDesc (h ⟨·⟩)

instance IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete_commaObj
    {ι : Type*} [Small.{u} ι] {C : Type*} [Category C] [HasColimitsOfShape (Discrete ι) C]
    (L : C ⥤ Scheme.{u}) [PreservesColimitsOfShape (Discrete ι) L] (X : Scheme.{u}) :
    (MorphismProperty.commaObj L (Functor.fromPUnit.{0} X) P).IsClosedUnderColimitsOfShape
      (Discrete ι) :=
  IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete L X

variable [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] [P.IsMultiplicative]

instance inst_TopologyCoherentAffine_L127 : HasFiniteCoproducts (P.CostructuredArrow ⊤ Scheme.Spec S) where
  out _ := inferInstance

instance inst_TopologyCoherentAffine_L130 : FinitaryExtensive (P.CostructuredArrow ⊤ Scheme.Spec S) :=
  CategoryTheory.finitaryExtensive_of_preserves_and_reflects_isomorphism
    (MorphismProperty.CostructuredArrow.toOver P Scheme.Spec S)


namespace AffineEtale

instance inst_TopologyCoherentAffine_L153 : (AffineEtale.Spec S).ReflectsEffectiveEpis :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).ReflectsEffectiveEpis

instance effectiveEpi_of_surjective {S : Scheme} {X Y : S.AffineEtale} (f : X ⟶ Y)
    [Surjective (Spec.map f.left.unop)] : EffectiveEpi f := by
  apply (AffineEtale.Spec S).effectiveEpi_of_map
  have : Surjective ((AffineEtale.Spec S).map f).left := ‹_›
  infer_instance

instance inst_TopologyCoherentAffine_L162 : HasPullbacks S.AffineEtale :=
  inferInstanceAs <| HasPullbacks (MorphismProperty.CostructuredArrow _ _ _ _)

-- Question: What are the effective epimorphisms of `AffineEtale S`?


end AffineEtale

end Scheme

end AlgebraicGeometry


