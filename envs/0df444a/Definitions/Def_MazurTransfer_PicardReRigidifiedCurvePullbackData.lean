-- Prove2me | Definitions.Def_MazurTransfer_PicardReRigidifiedCurvePullbackData
-- name    : MazurTransfer_PicardReRigidifiedCurvePullbackData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T09:41:09.212597+00:00
-- url     : https://prove2.me/theorems/416a70d4-560d-4ff3-b3e9-4e532962d265
-- title:
--   Re-rigidified curve pullback data on a represented Picard scheme
-- statement:
--   Let $R$ be a commutative ring, let $c:C\to\operatorname{Spec}R$ have a chosen section, and let $D$ represent its algebraically trivial rigidified relative line bundles through a representation $h$. For a curve morphism $f:C\to C$ over $R$, a pullback datum consists of a relative endomorphism $N:D\to D$ together with its specified classification and group compatibility. On every test scheme, the Poincaré line bundle classified by $N(a)$ is isomorphic to the pullback of that classified by $a$, rigidified again along the chosen section; moreover $$N(xy)=N(x)N(y),\qquad N(1)=1.$$ This is the interface for the diamond-induced scheme endomorphism even when $f$ does not preserve the section.
-- source:
--   Original complete PullbackData structure and its four fields from MazurTheorem PicardReRigidifiedCurvePullback.lean, Apache-2.0, Vas and contributors. Original structure body unchanged. The nonempty construction is a separate theorem node. Six original closed types (the structure, constructor and four accessors) and the single data projection value are kernel-compared; the three proof accessors are compared at their complete types. Native, strict and complete frontend checks pass. Reuses the official Anthropic FLT re-rigidified pullback API at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Named downstream consumer: actual rational Picard diamond scheme endomorphism.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Reuses the complete checked original Anthropic FLT re-rigidified pullback
construction at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: a curve morphism over the base acts on represented Picard
schemes after rigidification; preservation of the chosen section is unnecessary.
Named downstream consumer: the actual diamond automorphism of the order-13
curve and its Picard scheme endomorphism, including all base changes.
-/
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_rigidify_pullback_map_of_comp_eq_comp

noncomputable section
universe u
namespace MazurTransfer.PicardReRigidifiedCurvePullback
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {D : RelativePic0Designation R c}

structure PullbackData (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (f : C ⟶ C) (hf : f ≫ c = c) where
  hom : SchemeHomOver D.toBase D.toBase
  classifies : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (a : SchemeHomOver t D.toBase),
    Nonempty ((h.poincare.pullbackAlong (postComp hom a)).L ≅
      Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
        ((Scheme.Modules.pullback (curveChange f hf t)).obj (h.poincare.pullbackAlong a).L))
  mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t D.toBase),
    postComp hom ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t x y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t
        (postComp hom x) (postComp hom y)
  one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
    postComp hom ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one t) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one t



end MazurTransfer.PicardReRigidifiedCurvePullback
#print axioms AlgebraicGeometry.RelPicard.RepresentsRelSubPic.relativeGroupLaw


