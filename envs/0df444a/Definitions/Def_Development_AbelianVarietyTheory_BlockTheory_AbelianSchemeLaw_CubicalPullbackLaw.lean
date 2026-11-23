-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_CubicalPullbackLaw
-- name    : Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_CubicalPullbackLaw
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:16.966313+00:00
-- url     : https://prove2.me/theorems/347de17c-1ec2-4df1-8506-f059400d777f
-- title:
--   Cubical Pullback Law
-- statement:
--   Definitions and structural lemmas for Cubical Pullback Law, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/CubicalPullbackLaw.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.IndefiniteRowSideFullHecke.CubicalPullbackLaw
def IsRigPull {S S' : Scheme.{0}} {B' : Over S'} {B : Over S} [GrpObj B'] [IsCommMonObj B']
    [GrpObj B] [IsCommMonObj B] (p : S' ⟶ S) (F : B'.left ⟶ B.left) (L' : RigLB B') (L : RigLB B) : Prop :=
  ∃ he : eSec B' ≫ F = (show (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left from p) ≫ eSec B,
  ∃ w : LB.Iso L'.L (L.L.pull F), w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec B') (fun _ => 1)) L'.rig
      (rigPullOf F p he L.L L.rig)
def Identifies {S S' : Scheme.{0}} (p : S' ⟶ S) (E : SplitExt S) (E' : SplitExt S')
    (φ : E'.B ≅ (Over.pullback p).obj E.B) (ψ : E'.X ≃+ E.X) : Prop :=
  haveI := E.isAbelian.comm
  haveI := E'.isAbelian.comm
  IsMonHom φ.hom ∧
    ∀ χ : E'.X, IsRigPull p (φ.hom.left ≫ pullback.fst E.B.hom p) (E'.O χ) (E.O (ψ χ))
def IsBaseChange {S S' : Scheme.{0}} (p : S' ⟶ S) (E : SplitExt S) (E' : SplitExt S') : Prop :=
  ∃ (φ : E'.B ≅ (Over.pullback p).obj E.B) (ψ : E'.X ≃+ E.X), Identifies p E E' φ ψ
def GtBaseChangeLaw : Prop :=
  ∀ {S S' : Scheme.{0}} (p : S' ⟶ S) (E : SplitExt S) (G : Over S) [GrpObj G],
    E.IsGt G → ∃ E' : SplitExt S', IsBaseChange p E E' ∧ E'.IsGt ((Over.pullback p).obj G)
def CubicalPullLaw : Prop :=
  ∀ {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) (L : RigLB G) (c : CubicalStr G L),
    ∃ (hL : (L.L.pull m.F).IsLB) (hr : (m.rigPull L.L L.rig).IsGen)
      (c' : CubicalStr G' (m.rigLB L hL hr)),
      c'.t = m.thetaPull L.L c.t ∧ m.IsPullCubical c' c ∧
        (L.IsSymmetric → (m.rigLB L hL hr).IsSymmetric)
def Laws : Prop := GtBaseChangeLaw ∧ CubicalPullLaw
def GtPresentationBaseChangeLaw : Prop :=
  ∀ {S S' : Scheme.{0}} (p : S' ⟶ S) (E : SplitExt S) (G : Over S) [GrpObj G] (D : E.GtDatum G),
    ∃ (E' : SplitExt S') (φ : E'.B ≅ (Over.pullback p).obj E.B) (ψ : E'.X ≃+ E.X)
      (D' : E'.GtDatum ((Over.pullback p).obj G))
      (τ : (splitTorus S' E'.X).left ⟶ (splitTorus S E.X).left),
      Identifies p E E' φ ψ ∧
      D'.q ≫ φ.hom = (Over.pullback p).map D.q ∧
      τ ≫ (splitTorus S E.X).hom = (splitTorus S' E'.X).hom ≫ p ∧
      (∀ χ : E'.X, Units.map τ.appTop.hom.toMonoidHom (charUnit S E.X (ψ χ)) =
        charUnit S' E'.X χ) ∧
      D'.i.left ≫ pullback.fst G.hom p = τ ≫ D.i.left
end GlobalTheory.IndefiniteRowSideFullHecke.CubicalPullbackLaw
end


