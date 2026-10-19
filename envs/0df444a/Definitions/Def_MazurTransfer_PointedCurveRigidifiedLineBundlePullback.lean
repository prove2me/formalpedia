-- Prove2me | Definitions.Def_MazurTransfer_PointedCurveRigidifiedLineBundlePullback
-- name    : MazurTransfer_PointedCurveRigidifiedLineBundlePullback
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T07:36:19.223235+00:00
-- url     : https://prove2.me/theorems/353895af-7119-4c52-a5bb-d8e1fe807a51
-- title:
--   Rigidified line-bundle pullback along a pointed curve morphism
-- statement:
--   Let $C$ and $C^{\prime}$ be curves over a commutative ring $R$, each with a specified section. A morphism $f:C^{\prime}\to C$ over $R$ carrying the specified section to the specified section induces pullback on rigidified line bundles after every base change $T\to\operatorname{Spec}R$. The constructed bundle satisfies $$f_T^*M\in\operatorname{RigidPic}(C_T^{\prime}/T).$$ The bundle, its invertibility and its rigidification are specified together with the module isomorphisms for further base change, isomorphic input bundles and the unit bundle. These constructors support transport of relative Picard representations along actual pointed curve isomorphisms.
-- source:
--   MazurTheorem CurveHomRigidifiedLineBundlePullback.lean, Apache-2.0, Vas and contributors. Original official Anthropic FLT line-bundle and relative Picard APIs at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. All nine constructor and structural theorem bodies are retained unchanged; the separate thirteen-line fibrewise algebraic-equivalence preservation theorem is excluded as a distinct public theorem node. All nine original closed types and all five data values are kernel-compared; native, strict and full frontend checks pass. Design boundary: structural rigidified line-bundle pullback. Named downstream consumer: CurveIsoPicardRepresentationTransport and actual literal rational/mod-3/mod-5 fibres.

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

theorem curvePullback_baseChangeSnd {T T' : Scheme.{u}}
    {t : T ⟶ Spec (.of R)} {t' : T' ⟶ Spec (.of R)} (ψ : SchemeHomOver t' t) :
    curvePullback f hf t' ≫ baseChangeSnd c ψ =
      baseChangeSnd c' ψ ≫ curvePullback f hf t := by
  apply pullback.hom_ext
  · simp only [Category.assoc,baseChangeSnd,pullback.lift_fst,pullback.lift_fst_assoc,
      Category.comp_id,curvePullback_fst]
  · simp only [Category.assoc,baseChangeSnd,pullback.lift_snd,curvePullback_snd]
    rw [← Category.assoc,curvePullback_snd]

def pullbackAlong_iso {T T' : Scheme.{u}} {t : T ⟶ Spec (.of R)}
    {t' : T' ⟶ Spec (.of R)} (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε t) :
    (pullbackRigidified f hf hε (M.pullbackAlong ψ)).L ≅
      ((pullbackRigidified f hf hε M).pullbackAlong ψ).L :=
  (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (curvePullback_baseChangeSnd f hf ψ)).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm

def pullbackRigidified_congr {T : Scheme.{u}} {t : T ⟶ Spec (.of R)}
    {M N : RigidifiedLineBundle c ε t} (e : M.L ≅ N.L) :
    (pullbackRigidified f hf hε M).L ≅ (pullbackRigidified f hf hε N).L :=
  (Scheme.Modules.pullback (curvePullback f hf t)).mapIso e

def pullbackRigidified_unit_iso {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) :
    (pullbackRigidified f hf hε (RigidifiedLineBundle.unit t)).L ≅
      (RigidifiedLineBundle.unit (c := c') (ε := ε') t).L :=
  Scheme.Modules.pullbackUnitIso (curvePullback f hf t)



end MazurTransfer.CurveHomRigidifiedLineBundlePullback


#print axioms MazurTransfer.CurveHomRigidifiedLineBundlePullback.pullbackRigidified
#print axioms MazurTransfer.CurveHomRigidifiedLineBundlePullback.pullbackAlong_iso


