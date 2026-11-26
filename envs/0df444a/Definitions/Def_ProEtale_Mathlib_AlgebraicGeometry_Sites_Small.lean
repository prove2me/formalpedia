-- Prove2me | Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_Small
-- name    : ProEtale_Mathlib_AlgebraicGeometry_Sites_Small
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:39:42.617725+00:00
-- url     : https://prove2.me/theorems/6ed2a538-c3c9-464e-bda2-ac7bc55d73df
-- title:
--   Continuity of change-of-property, base change and postcomposition functors between small sites of schemes
-- statement:
--   For a scheme $S$ and a class $P$ of morphisms of schemes that is multiplicative, stable under base change and preserves joint surjectivity, the small $P$-site of $S$ is the category of $S$-schemes $X \to S$ in $P$ with the topology induced by jointly surjective families of $P$-morphisms.
--
--   Principal results:
--   1. If $P \le Q$ (both as above) and $P$ satisfies right cancellation, the inclusion of the small $P$-site into the small $Q$-site is continuous.
--   2. For a morphism $f : S \to T$, the base change functor $X \mapsto X \times_T S$ from the small $P$-site of $T$ to that of $S$ is continuous; if $\mathcal A$ is a category such that sheaves on the small $P$-site of $S$ admit weak sheafification, the induced pushforward on $\mathcal A$-valued sheaves is a right adjoint.
--   3. If $f : S \to T$ lies in $P$, postcomposition with $f$ (viewing an $S$-scheme as a $T$-scheme) is continuous from the small $P$-site of $S$ to that of $T$.
--
--   These continuity statements allow pulling back and pushing forward sheaves between small étale and pro-étale sites, and comparing the small sites for different classes of morphisms (e.g. étale inside weakly étale).
--
--   **Formalization Note** For `S : Scheme.{u}`, the sites are `smallGrothendieckTopology (Q := P) P`. The results are unnamed instances of `Functor.IsContinuous` for `Over.changeProp S hPQ le_rfl`, `Over.pullback P ⊤ f` and `Over.map ⊤ hf`, and an `IsRightAdjoint` instance for `(Over.pullback P ⊤ f).sheafPushforwardContinuous A …`. Standing assumptions are `[P.IsMultiplicative] [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]` (and similarly for `Q`); item 1 also uses `[P.HasOfPostcompProperty P]`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/AlgebraicGeometry/Sites/Small.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.AlgebraicGeometry.Sites.Small
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.Grothendieck
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_Grothendieck

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
universe u

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry
namespace Scheme

variable (S : Scheme.{u}) {P Q : MorphismProperty Scheme.{u}}
  [P.IsMultiplicative] [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange] [IsJointlySurjectivePreserving Q]

instance inst_MathlibAlgebraicGeometrySitesSmall_L16 (hPQ : P ≤ Q) [P.HasOfPostcompProperty P] :
    (Over.changeProp S hPQ le_rfl).IsContinuous
    (smallGrothendieckTopology (Q := P) P _) (smallGrothendieckTopology (Q := Q) Q _) := by
  have : PreservesFiniteLimits
      (Over.changeProp S hPQ le_rfl : P.Over ⊤ S ⥤ Q.Over ⊤ S) := by
    refine ⟨fun J _ _ ↦ ?_⟩
    have : PreservesLimitsOfShape J (Over.changeProp S hPQ le_rfl ⋙
        MorphismProperty.Over.forget Q ⊤ S) :=
      inferInstanceAs <| PreservesLimitsOfShape J (MorphismProperty.Over.forget P ⊤ S)
    exact preservesLimitsOfShape_of_reflects_of_preserves _
      (MorphismProperty.Over.forget Q ⊤ S)
  have : RepresentablyFlat (Over.changeProp S hPQ le_rfl : P.Over ⊤ S ⥤ Q.Over ⊤ S) :=
    flat_of_preservesFiniteLimits _
  refine Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ _) ⟨fun {U R} hR ↦ ?_⟩
  rw [Functor.mem_restrictedTopology_iff, ← Sieve.functorPushforward_comp]
  -- `Over.changeProp S hPQ le_rfl ⋙ forget Q = forget P` definitionally
  have hmono : S.overGrothendieckTopology P ≤ S.overGrothendieckTopology Q := by
    intro Z T hT
    rw [GrothendieckTopology.mem_over_iff] at hT ⊢
    exact grothendieckTopology_monotone hPQ _ hT
  exact hmono _ (Functor.mem_restrictedTopology_iff.mp hR)

section

variable {S T : Scheme.{u}} (f : S ⟶ T)
  (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] [P.RespectsIso]
  [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
variable (A : Type*) [Category* A]

/-- The base change functor along `f : S ⟶ T` is continuous for the small
Grothendieck topologies. -/
instance inst_MathlibAlgebraicGeometrySitesSmall_L46 :
    (Over.pullback P ⊤ f).IsContinuous
      (T.smallGrothendieckTopology (Q := P) P)
      (S.smallGrothendieckTopology (Q := P) P) := by
  have : RepresentablyFlat (Over.pullback P ⊤ f) := flat_of_preservesFiniteLimits _
  refine Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ (Over.pullback P ⊤ f)) ⟨fun {U R} hR ↦ ?_⟩
  rw [Functor.mem_restrictedTopology_iff, ← Sieve.functorPushforward_comp]
  refine GrothendieckTopology.functorPushforward_mem_of_iso _
    (Over.pullbackCompForgetIso (P := P) (Q := ⊤) f).symm R ?_
  rw [Sieve.functorPushforward_comp]
  exact (GrothendieckTopology.coverPreserving_overPullback
    (J := Scheme.grothendieckTopology P) f).cover_preserve
    (by rwa [Functor.mem_restrictedTopology_iff] at hR)


variable [HasWeakSheafify (S.smallGrothendieckTopology (Q := P) P) A]
  [∀ F : (P.Over ⊤ T)ᵒᵖ ⥤ A, (Over.pullback P ⊤ f).op.HasLeftKanExtension F]

instance inst_MathlibAlgebraicGeometrySitesSmall_L71 :
    ((Over.pullback P ⊤ f).sheafPushforwardContinuous A (smallGrothendieckTopology (Q := P) P _)
      (smallGrothendieckTopology (Q := P) P _)).IsRightAdjoint :=
  inferInstance


/-- The functor `X/S ⥤ X/T` induced by postcomposition with `f : S ⟶ T` satisfying `P`
is continuous for the small Grothendieck topologies. -/
instance inst_MathlibAlgebraicGeometrySitesSmall_L86 (hf : P f) :
    (Over.map ⊤ hf).IsContinuous (smallGrothendieckTopology (Q := P) P _) (smallGrothendieckTopology (Q := P) P _) := by
  refine Functor.isContinuous_of_coverPreserving ⟨?_⟩ ⟨fun {U R} hR ↦ ?_⟩
  · -- compatible preservation, mirroring `over_map_compatiblePreserving`: a cone over
    -- `(Over.map ⊤ hf).obj Y₁` and `(Over.map ⊤ hf).obj Y₂` lifts to `P.Over ⊤ S`,
    -- the property of the lifted structure morphism coming from `of_postcomp`.
    intro ℱ Z 𝒯 x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h
    have hW' : P (f₁.left ≫ Y₁.hom) := by
      refine P.of_postcomp (W' := P) _ f hf ?_
      have : f₁.left ≫ Y₁.hom ≫ f = W.hom := MorphismProperty.Over.w f₁
      rw [Category.assoc, this]
      exact W.prop
    let W' : P.Over ⊤ S := MorphismProperty.Over.mk ⊤ (f₁.left ≫ Y₁.hom) hW'
    have hleft : f₁.left ≫ g₁.left = f₂.left ≫ g₂.left := by
      simpa using congrArg (fun q ↦ q.left) h
    let g₁' : W' ⟶ Y₁ := MorphismProperty.Over.homMk f₁.left rfl trivial
    let g₂' : W' ⟶ Y₂ := MorphismProperty.Over.homMk f₂.left
      (by rw [← MorphismProperty.Over.w g₂, ← Category.assoc, ← hleft, Category.assoc,
        MorphismProperty.Over.w g₁]; simp [W']) trivial
    let e : (Over.map ⊤ hf).obj W' ≅ W := MorphismProperty.Over.isoMk (Iso.refl _)
      (by simpa [W'] using (MorphismProperty.Over.w f₁).symm)
    have compat : ℱ.obj.map ((Over.map ⊤ hf).map g₁').op (x g₁ hg₁) =
        ℱ.obj.map ((Over.map ⊤ hf).map g₂').op (x g₂ hg₂) :=
      hx g₁' g₂' hg₁ hg₂ (by ext; simpa [g₁', g₂'] using hleft)
    have h1 : e.inv ≫ (Over.map ⊤ hf).map g₁' = f₁ := by
      ext
      simp [e, g₁', W']
    have h2 : e.inv ≫ (Over.map ⊤ hf).map g₂' = f₂ := by
      ext
      simp [e, g₂', W']
    calc ℱ.obj.map f₁.op (x g₁ hg₁)
        = ℱ.obj.map (e.inv ≫ (Over.map ⊤ hf).map g₁').op (x g₁ hg₁) := by rw [h1]
      _ = ℱ.obj.map e.inv.op (ℱ.obj.map ((Over.map ⊤ hf).map g₁').op (x g₁ hg₁)) := by
          rw [op_comp, ℱ.obj.map_comp]; rfl
      _ = ℱ.obj.map e.inv.op (ℱ.obj.map ((Over.map ⊤ hf).map g₂').op (x g₂ hg₂)) := by
          rw [compat]
      _ = ℱ.obj.map f₂.op (x g₂ hg₂) := by rw [← h2, op_comp, ℱ.obj.map_comp]; rfl
  · -- cover preservation, by transport to `over_map_coverPreserving` for the big sites
    rw [Functor.mem_restrictedTopology_iff, ← Sieve.functorPushforward_comp]
    have e : MorphismProperty.Over.forget P ⊤ S ⋙ CategoryTheory.Over.map f ≅
        Over.map ⊤ hf ⋙ MorphismProperty.Over.forget P ⊤ T := Iso.refl _
    refine GrothendieckTopology.functorPushforward_mem_of_iso _ e R ?_
    rw [Sieve.functorPushforward_comp]
    exact (GrothendieckTopology.over_map_coverPreserving
      (J := Scheme.grothendieckTopology P) f).cover_preserve
      (Functor.mem_restrictedTopology_iff.mp hR)


end

end Scheme
end AlgebraicGeometry


