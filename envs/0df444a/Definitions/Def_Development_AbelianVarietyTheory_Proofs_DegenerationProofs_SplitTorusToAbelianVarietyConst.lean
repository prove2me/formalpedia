-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:12.356735+00:00
-- url     : https://prove2.me/theorems/3459d065-a12c-4268-a7ce-03171a206acd
-- title:
--   Split Torus To Abelian Variety Const
-- statement:
--   Definitions and structural lemmas for Split Torus To Abelian Variety Const, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
namespace TorusConst
open Polynomial TorusToProper
variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))}
noncomputable def val {R A : Type} [CommRing R] [Algebra K R] [CommRing A] [Algebra K A]
    (F : sp K R[X] ⟶ B) (c : R →ₐ[K] A) (x : A) : sp K A ⟶ B :=
  spm (aevalTower c x) ≫ F
def Glue {R : Type} [CommRing R] [Algebra K R] (F G : sp K R[X] ⟶ B) : Prop :=
  ∀ (A : Type) [Field A] [Algebra K A] (c : R →ₐ[K] A) (x : A), x ≠ 0 → val F c x = val G c x⁻¹
section group
variable [GrpObj B] {L R : Type} [Field L] [Algebra K L] [CommRing R] [Algebra K R]
noncomputable def twist (b : sp K L[X] ⟶ B) (i : L →ₐ[K] R) (s : R) : sp K R[X] ⟶ B :=
  val b (CAlgHom.comp i) (C s * X) * (val b (CAlgHom.comp i) X)⁻¹
end group
section laurent
open LaurentPolynomial
variable {L : Type} [Field L] [Algebra K L]
noncomputable def ev {A : Type} [CommRing A] [Algebra K A] (c : L →ₐ[K] A) (x : Aˣ) :
    L[T;T⁻¹] →ₐ[K] A where
  toRingHom := LaurentPolynomial.eval₂ (c : L →+* A) x
  commutes' r := by
    change LaurentPolynomial.eval₂ (c : L →+* A) x (LaurentPolynomial.C (algebraMap K L r)) = _
    rw [LaurentPolynomial.eval₂_C]
    exact c.commutes r
variable (K L) in

noncomputable def inc : L[X] →ₐ[K] L[T;T⁻¹] := (toLaurentAlg : L[X] →ₐ[L] L[T;T⁻¹]).restrictScalars K
variable (K L) in

noncomputable def cst : L →ₐ[K] L[T;T⁻¹] := (inc K L).comp CAlgHom
variable (L) in

noncomputable def tU : (L[T;T⁻¹])ˣ := (isUnit_T (R := L) 1).unit
end laurent
end TorusConst
end GlobalTheory


