-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianSchemes
-- name    : Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianSchemes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:09.348278+00:00
-- url     : https://prove2.me/theorems/876b31e4-e041-437a-84aa-26bfdabb19cf
-- title:
--   Semi Abelian Schemes
-- statement:
--   Definitions and structural lemmas for Semi Abelian Schemes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/SemiAbelianSchemes.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusAff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes
open ReciprocityTheory.ChartRestriction.G.Semi
structure IsAbelianScheme {S : Scheme.{u}} (A : Over S) [GrpObj A] : Prop where
  smooth : Smooth A.hom
  proper : IsProper A.hom
  geometricallyConnected : GeometricallyConnected A.hom
  comm : IsCommMonObj A
structure IsShortExact {S : Scheme.{u}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]
    (i : T ⟶ G) (q : G ⟶ B) : Prop where
  isMonHom_i : IsMonHom i
  isMonHom_q : IsMonHom q
  isKernel : IsPullback i (toUnit T) q (η : 𝟙_ (Over S) ⟶ B)
  flat : Flat q.left
  surjective : Surjective q.left
  finitePresentation : LocallyOfFinitePresentation q.left
def IsTorusExtension {k : Type u} [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] :
    Prop :=
  IsCommMonObj G ∧
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X)
      (B : Over (Spec (CommRingCat.of k))) (_ : GrpObj B)
      (i : splitTorus (Spec (CommRingCat.of k)) X ⟶ G) (q : G ⟶ B),
      IsAbelianScheme B ∧ IsShortExact i q
structure IsSemiAbelianScheme {S : Scheme.{u}} (G : Over S) [GrpObj G] : Prop where
  smooth : Smooth G.hom
  separated : IsSeparated G.hom
  locallyOfFiniteType : LocallyOfFiniteType G.hom
  quasiCompact : QuasiCompact G.hom
  comm : IsCommMonObj G
  geometricFibre : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S),
    IsTorusExtension ((Over.pullback s).obj G)
section SplitTorus
variable (X : Type u) [AddCommGroup X]
end SplitTorus
end GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes


