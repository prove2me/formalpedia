-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_AbelianOpenPart_AbelianAt
-- name    : Formalism_SharpRestriction_Divisibility_AbelianOpenPart_AbelianAt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:58:08.002808+00:00
-- url     : https://prove2.me/theorems/d5cf5a8c-558e-44b3-9f48-82dc83b80e2e
-- title:
--   Abelian At
-- statement:
--   Definitions and structural lemmas for Abelian At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/AbelianOpenPart/AbelianAt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
namespace Formalism.MainNotions.DIV.Cons
universe u
attribute [local instance] CategoryTheory.Hom.group
abbrev GrpSch (S : Scheme.{u}) : Type (u + 1) := Grp (Over S)
def IsAbSch {S : Scheme.{u}} (A : GrpSch S) : Prop :=
  IsCommMonObj A.X ∧ IsProper A.X.hom ∧ Smooth A.X.hom ∧ GeometricallyConnected A.X.hom
def AbSch (S : Scheme.{u}) : Type (u + 1) := {A : GrpSch S // IsAbSch A}
def bchG {S T : Scheme.{u}} (f : T ⟶ S) (A : GrpSch S) : GrpSch T :=
  (Over.pullback f).mapGrp.obj A
def nMul {S : Scheme.{u}} (A : GrpSch S) (N : ℕ) : A.X ⟶ A.X := (𝟙 A.X) ^ N
def tors {S : Scheme.{u}} (A : GrpSch S) (N : ℕ) : Over S :=
  pullback (nMul A N) (MonObj.one : 𝟙_ (Over S) ⟶ A.X)
structure RAct (R : Type) [Ring R] {S : Scheme.{u}} (A : GrpSch S) where
  act : R → (A.X ⟶ A.X)
  hom : ∀ a, IsMonHom (act a)
  map_one : act 1 = 𝟙 A.X
  map_mul : ∀ a b, act (a * b) = act b ≫ act a
  map_add : ∀ a b, act (a + b) = act a * act b
def fibreAt {Z : Scheme.{u}} (A : GrpSch Z) (x : Z) : GrpSch (Spec (Z.residueField x)) :=
  bchG (Z.fromSpecResidueField x) A
def AbelianAt {Z : Scheme.{u}} (A : GrpSch Z) (x : Z) : Prop := IsAbSch (fibreAt A x)
structure ModelG (O : Type u) [CommRing O] [IsLocalRing O] where
  Z : Scheme.{u}
  str : Z ⟶ Spec (CommRingCat.of O)
  G : GrpSch Z
def ModelG.spf {O : Type u} [CommRing O] [IsLocalRing O] (M : ModelG O) : Scheme.{u} :=
  M.str.fiber (IsLocalRing.closedPoint O)
def ModelG.Gen {O : Type u} [CommRing O] [IsLocalRing O] (M : ModelG O) : Type u :=
  ↥(irreducibleComponents M.spf)
def ModelG.gpt {O : Type u} [CommRing O] [IsLocalRing O] (M : ModelG O) (η : M.Gen) : M.Z :=
  M.str.fiberι _ (η.2.1.genericPoint)
def ModelG.abAt {O : Type u} [CommRing O] [IsLocalRing O] (M : ModelG O) (η : M.Gen) : Prop :=
  AbelianAt M.G (M.gpt η)
end Formalism.MainNotions.DIV.Cons


