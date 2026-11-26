-- Prove2me | Definitions.Def_ProEtale_Topology_Comparison_FreeSheaf
-- name    : ProEtale_Topology_Comparison_FreeSheaf
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:37:47.384798+00:00
-- url     : https://prove2.me/theorems/5d35912a-9dce-4f0e-bc4c-f083bb1a7fc1
-- title:
--   Pulling back free abelian sheaves and constant sheaves from the étale to the pro-étale site
-- statement:
--   Let $G : \mathcal C \to \mathcal D$ be a continuous functor between sites $(\mathcal C, J)$ and $(\mathcal D, K)$ whose sheaf pushforward $G_*$ has a left adjoint, the sheaf pullback $G^*$. The file constructs, via uniqueness of left adjoints:
--
--   1. an isomorphism $G^* \circ a_J \cong a_K \circ \operatorname{Lan}_{G^{\mathrm{op}}}$ (sheafify then pull back, versus left Kan extend then sheafify), where $a$ denotes sheafification;
--   2. an isomorphism showing that forming free abelian presheaves commutes with left Kan extension along $G^{\mathrm{op}}$;
--   3. a natural isomorphism $G^*\big(\mathbb Z[U]^{\#}\big) \cong \mathbb Z[G(U)]^{\#}$ for $U \in \mathcal C$, where $\mathbb Z[U]^{\#}$ is the free abelian sheaf on (the sheafification of) the representable presheaf of $U$;
--   4. if $T$ is terminal in $\mathcal C$ and $G(T)$ is terminal in $\mathcal D$, a natural isomorphism $G^*(\underline M) \cong \underline M$ between pullbacks of constant sheaves and constant sheaves.
--
--   Specializing to the inclusion $\nu : S_{\text{ét}} \to S_{\text{proét}}$ of the small étale site of a scheme $S$ into its pro-étale site, one obtains
--   $$\nu^*\,\mathbb Z[U]^{\#} \cong \mathbb Z[\nu U]^{\#} \quad (U \in S_{\text{ét}}), \qquad \nu^*\,\underline M \cong \underline M \quad (M \text{ an abelian group}),$$
--   both natural, using that $S \xrightarrow{\mathrm{id}} S$ is terminal in both sites.
--
--   These isomorphisms are used to compare étale and pro-étale cohomology, which are computed via morphisms out of free and constant abelian sheaves.
--
--   **Formalization Note** The sites are `C D : Type (u+1)` with `Category.{u}`, and abelian groups are `AddCommGrpCat.{u+1}`. Main declarations: `CategoryTheory.sheafPushforwardContinuousCompSheafToPresheafIso`, `CategoryTheory.presheafToSheafCompSheafPullbackIso`, `CategoryTheory.whiskeringFreeCompLanIso`, `CategoryTheory.freeAbelianSheafFunctorCompSheafPullbackIso`, `CategoryTheory.constantSheafCompSheafPullbackIso`, and for schemes `AlgebraicGeometry.Scheme.ProEt.sheafPullbackCompFreeIso`, `sheafPullbackFreeIso`, `isTerminalMkId`, `isTerminalMkIdProEt`, `sheafPullbackCompConstantIso`, `sheafPullbackConstantIso`. The pullback functors are Mathlib's `Functor.sheafPullback`/`ProEt.sheafPullback`, and the isomorphisms are produced by `conjugateIsoEquiv`, so they are canonical but not given by explicit formulas.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/FreeSheaf.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Definitions.Def_ProEtale_Comparator_Definitions
import Definitions.Def_ProEtale_Comparator_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_SheafCohomology_FreeAbelianSheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Pullback of free abelian sheaves along the inclusion of the étale site

We show that the sheaf pullback along `toProEtale S : S.Etale ⥤ S.ProEt` is compatible
with forming free abelian sheaves on representable presheaves, and that it sends
constant sheaves to constant sheaves.

The main results are:

- `AlgebraicGeometry.Scheme.ProEt.sheafPullbackCompFreeIso`: pulling back the free abelian
  sheaf on `U : S.Etale` yields the free abelian sheaf on `(toProEtale S).obj U`,
  functorially in `U`.
- `AlgebraicGeometry.Scheme.ProEt.sheafPullbackConstantIso`: pulling back the constant
  sheaf with values `M` yields the constant sheaf with values `M`.

All isomorphisms are obtained from uniqueness of left adjoints, via
`CategoryTheory.conjugateIsoEquiv`.
-/

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type (u + 1)} [Category.{u} C] {D : Type (u + 1)} [Category.{u} D]

variable (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K]

section Presheaf

variable (A : Type*) [Category A] [HasWeakSheafify J A] [HasWeakSheafify K A]
  [∀ F : Cᵒᵖ ⥤ A, G.op.HasLeftKanExtension F]
  [(G.sheafPushforwardContinuous A J K).IsRightAdjoint]

/-- The underlying presheaf of the pushforward of a sheaf is the restriction of its
underlying presheaf, functorially. -/
def sheafPushforwardContinuousCompSheafToPresheafIso :
    G.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A ≅
      sheafToPresheaf K A ⋙ (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op :=
  NatIso.ofComponents fun _ ↦ Iso.refl _

/-- Sheafification commutes with pullback of (pre)sheaves: sheafifying and then pulling
back is the same as left Kan extending and then sheafifying. -/
noncomputable def presheafToSheafCompSheafPullbackIso :
    presheafToSheaf J A ⋙ G.sheafPullback A J K ≅ G.op.lan ⋙ presheafToSheaf K A :=
  ((conjugateIsoEquiv
      ((sheafificationAdjunction J A).comp (G.sheafAdjunctionContinuous A J K))
      ((G.op.lanAdjunction A).comp (sheafificationAdjunction K A))).symm
    (sheafPushforwardContinuousCompSheafToPresheafIso G J K A)).symm

end Presheaf

section Free

variable [∀ F : Cᵒᵖ ⥤ Type (u + 1), G.op.HasLeftKanExtension F]
  [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}, G.op.HasLeftKanExtension F]

/-- Forming free abelian group presheaves commutes with left Kan extension. -/
noncomputable def whiskeringFreeCompLanIso :
    (Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.free.{u + 1} ⋙ G.op.lan ≅
      G.op.lan ⋙ (Functor.whiskeringRight Dᵒᵖ _ _).obj AddCommGrpCat.free.{u + 1} :=
  ((conjugateIsoEquiv
      ((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj).comp (G.op.lanAdjunction _))
      ((G.op.lanAdjunction _).comp (Adjunction.whiskerRight Dᵒᵖ AddCommGrpCat.adj))).symm
    (NatIso.ofComponents fun _ ↦ Iso.refl _)).symm

variable [HasWeakSheafify J AddCommGrpCat.{u + 1}] [HasWeakSheafify K AddCommGrpCat.{u + 1}]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K).IsRightAdjoint]

/-- The free abelian sheaf functor commutes with sheaf pullback. -/
noncomputable def freeAbelianSheafFunctorCompSheafPullbackIso :
    freeAbelianSheafFunctor J ⋙ G.sheafPullback AddCommGrpCat.{u + 1} J K ≅
      G ⋙ freeAbelianSheafFunctor K :=
  Functor.isoWhiskerLeft
      (uliftYoneda.{u + 1} ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free)
      (presheafToSheafCompSheafPullbackIso G J K _) ≪≫
    Functor.isoWhiskerLeft uliftYoneda.{u + 1}
      (Functor.isoWhiskerRight (whiskeringFreeCompLanIso G) (presheafToSheaf K _)) ≪≫
    Functor.isoWhiskerRight (Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{u + 1} G).symm
      ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙ presheafToSheaf K _)

end Free

section Constant

variable (A : Type*) [Category A] [HasWeakSheafify J A] [HasWeakSheafify K A]
  [(G.sheafPushforwardContinuous A J K).IsRightAdjoint]
  {T : C} (hT : IsTerminal T) (hT' : IsTerminal (G.obj T))

/-- If `G` preserves the terminal object, the constant sheaf functor commutes with
sheaf pullback along `G`. -/
noncomputable def constantSheafCompSheafPullbackIso :
    constantSheaf J A ⋙ G.sheafPullback A J K ≅ constantSheaf K A :=
  ((conjugateIsoEquiv
      ((constantSheafAdj J A hT).comp (G.sheafAdjunctionContinuous A J K))
      (constantSheafAdj K A hT')).symm
    (NatIso.ofComponents fun _ ↦ Iso.refl _)).symm

end Constant

end CategoryTheory

namespace AlgebraicGeometry
namespace Scheme

variable (S : Scheme.{u})

namespace ProEt

/-- Pulling back free abelian sheaves on the small étale site of `S` to the pro-étale
site of `S` yields free abelian sheaves, functorially. -/
noncomputable def sheafPullbackCompFreeIso :
    freeAbelianSheafFunctor (smallEtaleTopology S) ⋙
        ProEt.sheafPullback S AddCommGrpCat.{u + 1} ≅
      toProEtale S ⋙ freeAbelianSheafFunctor (ProEt.topology S) :=
  freeAbelianSheafFunctorCompSheafPullbackIso (toProEtale S) _ _

/-- The pullback of the free abelian sheaf on `U : S.Etale` to the pro-étale site of `S`
is the free abelian sheaf on `(toProEtale S).obj U`. -/
noncomputable def sheafPullbackFreeIso (U : S.Etale) :
    (ProEt.sheafPullback S AddCommGrpCat.{u + 1}).obj
        ((freeAbelianSheafFunctor (smallEtaleTopology S)).obj U) ≅
      (freeAbelianSheafFunctor (ProEt.topology S)).obj ((toProEtale S).obj U) :=
  (sheafPullbackCompFreeIso S).app U

/-- `S` with the identity is a terminal object of the small étale site of `S`. -/
noncomputable def isTerminalMkId :
    IsTerminal (MorphismProperty.Over.mk ⊤ (𝟙 S) (MorphismProperty.id_mem _ S) : S.Etale) :=
  MorphismProperty.Over.mkIdTerminal _ _

/-- The image of the terminal object of the small étale site of `S` in the pro-étale
site of `S` is terminal. -/
noncomputable def isTerminalMkIdProEt :
    IsTerminal ((toProEtale S).obj
      (MorphismProperty.Over.mk ⊤ (𝟙 S) (MorphismProperty.id_mem _ S))) :=
  MorphismProperty.Over.mkIdTerminal @WeaklyEtale S

/-- Pulling back constant sheaves on the small étale site of `S` to the pro-étale site
of `S` yields constant sheaves, functorially. -/
noncomputable def sheafPullbackCompConstantIso :
    constantSheaf (smallEtaleTopology S) AddCommGrpCat.{u + 1} ⋙
        ProEt.sheafPullback S AddCommGrpCat.{u + 1} ≅
      constantSheaf (ProEt.topology S) AddCommGrpCat.{u + 1} :=
  constantSheafCompSheafPullbackIso (toProEtale S) _ _ _
    (isTerminalMkId S) (isTerminalMkIdProEt S)

/-- The pullback of the constant sheaf with values `M` on the small étale site of `S`
to the pro-étale site of `S` is the constant sheaf with values `M`. -/
noncomputable def sheafPullbackConstantIso (M : AddCommGrpCat.{u + 1}) :
    (ProEt.sheafPullback S AddCommGrpCat.{u + 1}).obj
        ((constantSheaf (smallEtaleTopology S) _).obj M) ≅
      (constantSheaf (ProEt.topology S) _).obj M :=
  (sheafPullbackCompConstantIso S).app M

end ProEt

end Scheme
end AlgebraicGeometry


