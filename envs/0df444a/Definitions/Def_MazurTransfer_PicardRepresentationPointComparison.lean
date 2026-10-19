-- Prove2me | Definitions.Def_MazurTransfer_PicardRepresentationPointComparison
-- name    : MazurTransfer_PicardRepresentationPointComparison
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T08:06:19.11999+00:00
-- url     : https://prove2.me/theorems/f193bb64-aa6f-42af-807f-fcaef8ea836c
-- title:
--   Relative point comparison for two representations of the same Picard subfunctor
-- statement:
--   Let $P$ be a rigidified relative Picard subfunctor for a pointed scheme $C$ over a commutative ring $R$. Suppose $D$ and $D^{\prime}$ both represent this same subfunctor. For every test scheme $T$ over $R$, classification of the pulled-back universal bundle gives an equivalence $$D(T)\simeq D^{\prime}(T).$$ The construction includes the classified bundle isomorphism, the inverse-composite identity and the corresponding equivalence of morphisms in the slice category over $\operatorname{Spec}R$. It is used to compare the actual integral family’s field fibre with the representative in the published arithmetic Picard theorem.
-- source:
--   New checked comparison interface in MazurTheorem scratch integration, Apache-2.0, Vas and contributors. Uses only the original official Anthropic FLT SubPicCondition and RepresentsRelSubPic classify, classify_spec and ext_of_iso APIs, exact upstream pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Five closed declarations comprise the classification map, its structural bundle and inverse identities, and the two point equivalences; all three data values are closed. Native, strict and complete frontend checks pass with standard axioms only. Explicit design boundary: relative points of two representations of the same specified subfunctor. Named downstream consumer: the unchanged actual integral Picard relative arithmetic group-equivalence contract. No equality between the two chosen representing schemes is asserted.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: two representations of the same rigidified Picard
subfunctor classify the same bundles and give equivalent relative points.
Named downstream consumer: the arithmetic group of the actual integral
Picard family's literal field fibre, using the published field representative.
Uses the original official Anthropic FLT representing-equivalence API,
exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Mathlib
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

noncomputable section
universe u
namespace MazurTransfer.PicardRepresentationPointComparison
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
variable {R : Type u} [CommRing R] {C : Scheme.{u}}
variable {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
variable {P : SubPicCondition c ε} {D D' : RelativePic0Designation R c}
variable (h : RepresentsRelSubPic c ε P D) (h' : RepresentsRelSubPic c ε P D')

def pointMap {T : Scheme.{u}} (t : T ⟶ Spec (.of R))
    (p : SchemeHomOver t D.toBase) : SchemeHomOver t D'.toBase :=
  h'.classify t (h.poincare.pullbackAlong p)
    (P.pullback_mem _ _ p _ h.poincare_mem)

theorem pointMap_spec {T : Scheme.{u}} (t : T ⟶ Spec (.of R))
    (p : SchemeHomOver t D.toBase) :
    Nonempty ((h'.poincare.pullbackAlong (pointMap h h' t p)).L ≅
      (h.poincare.pullbackAlong p).L) :=
  h'.classify_spec t _ _

theorem pointMap_roundtrip {T : Scheme.{u}} (t : T ⟶ Spec (.of R))
    (p : SchemeHomOver t D.toBase) : pointMap h' h t (pointMap h h' t p) = p := by
  apply h.ext_of_iso t
  exact ⟨(pointMap_spec h' h t (pointMap h h' t p)).some ≪≫
    (pointMap_spec h h' t p).some⟩

def pointEquiv {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) :
    SchemeHomOver t D.toBase ≃ SchemeHomOver t D'.toBase where
  toFun := pointMap h h' t
  invFun := pointMap h' h t
  left_inv := pointMap_roundtrip h h' t
  right_inv := pointMap_roundtrip h' h t

def overPointEquiv {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) :
    (Over.mk t ⟶ Over.mk D.toBase) ≃ (Over.mk t ⟶ Over.mk D'.toBase) :=
  (schemeHomOverEquivOverHom t D.toBase).symm.trans
    ((pointEquiv h h' t).trans (schemeHomOverEquivOverHom t D'.toBase))

end MazurTransfer.PicardRepresentationPointComparison
#print axioms MazurTransfer.PicardRepresentationPointComparison.overPointEquiv


