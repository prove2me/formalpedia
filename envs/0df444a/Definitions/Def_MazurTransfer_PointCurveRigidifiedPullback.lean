-- Prove2me | Definitions.Def_MazurTransfer_PointCurveRigidifiedPullback
-- name    : MazurTransfer_PointCurveRigidifiedPullback
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-10T11:39:43.33548+00:00
-- url     : https://prove2.me/theorems/639477e4-9eec-40f6-a93a-7685dff2599b
-- title:
--   Rigidified line-bundle pullback along a pointed curve morphism
-- statement:
--   Let $C$ and $C′$ be curves over a common affine base, with chosen sections. A morphism $C′\to C$ over the base that carries one section to the other induces pullback of rigidified line bundles on every scheme base change. The constructor retains the induced map of the fibre product, the invertible sheaf, and its trivialization along the section. Only the constructor and its necessary projection and section identities are included. The downstream theorem proves preservation of fibrewise algebraic equivalence to zero, and the integral order-13 Picard family uses the construction to identify its rational and finite-field fibres.
-- source:
--   Owned CurveHomRigidifiedLineBundlePullback.lean for the MazurTheorem campaign; base rigidified line-bundle interface from official Anthropic FLT, Apache-2.0, exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Constructor proof and attribution retained; no original-source count increment.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: pullback of rigidified line bundles along a morphism of
pointed curves over the same base preserves fibrewise algebraic equivalence
to zero. Named downstream consumer: CurveIsoPicardRepresentationTransport
and the rational/finite-field fibres of the actual integral Picard family.
Original line-bundle and algebraic-equivalence APIs: official Anthropic FLT,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut

namespace PointCurveRigidifiedPullbackLibrary
noncomputable section
universe u
namespace MazurTransfer.CurveHomRigidifiedLineBundlePullback
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
variable {c : C ⟶ Spec (.of R)} {c' : C' ⟶ Spec (.of R)}
variable {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
variable {ε' : SchemeHomOver (𝟙 (Spec (.of R))) c'}
variable (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.val ≫ f = ε.val)

def curvePullback {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) : pullback c' t ⟶ pullback c t :=
  pullback.map c' t c t f (𝟙 T) (𝟙 _) (by rw [Category.comp_id,hf]) (by simp)

theorem curvePullback_fst {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) :
    curvePullback f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f :=
  pullback.lift_fst _ _ _

theorem curvePullback_snd {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) :
    curvePullback f hf t ≫ pullback.snd c t = pullback.snd c' t := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

include hε in
theorem rigSection_curvePullback {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) :
    rigSection c' t ε' ≫ curvePullback f hf t = rigSection c t ε := by
  apply pullback.hom_ext
  · rw [Category.assoc,curvePullback_fst,← Category.assoc]
    simp only [rigSection,pullback.lift_fst,Category.assoc,hε]
  · rw [Category.assoc,curvePullback_snd]
    simp only [rigSection,pullback.lift_snd]

def pullbackRigidified {T : Scheme.{u}} {t : T ⟶ Spec (.of R)}
    (M : RigidifiedLineBundle c ε t) : RigidifiedLineBundle c' ε' t where
  L := (Scheme.Modules.pullback (curvePullback f hf t)).obj M.L
  isInvertible := M.isInvertible.pullback _
  rigidified := ⟨(Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (rigSection_curvePullback f hf hε t)).app M.L ≪≫
    M.rigidified.some⟩

end MazurTransfer.CurveHomRigidifiedLineBundlePullback
end
end PointCurveRigidifiedPullbackLibrary
#print axioms PointCurveRigidifiedPullbackLibrary.MazurTransfer.CurveHomRigidifiedLineBundlePullback.pullbackRigidified


