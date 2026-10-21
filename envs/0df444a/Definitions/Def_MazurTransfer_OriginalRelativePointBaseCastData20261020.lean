-- Prove2me | Definitions.Def_MazurTransfer_OriginalRelativePointBaseCastData20261020
-- name    : MazurTransfer_OriginalRelativePointBaseCastData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T02:47:54.224887+00:00
-- url     : https://prove2.me/theorems/ba59fe1a-9d6d-4272-91d7-05de9e35b62b
-- title:
--   Original relative point equivalence over the same proved-equal base arrow
-- statement:
--   Retain the original relative point equivalence induced by the same given base-arrow equality, with its underlying scheme map unchanged. Its complete original type and whole value, the complete original relative-point type and whole alias value, and all generated structural certificates are independently checked. Naturality and group compatibility are separate theorem interfaces. Named downstream consumer: coefficient-map comparison between the same integral nineteen Hopf points and fixed arithmetic norm-kernel points.
-- source:
--   MazurTheorem RelativePointBaseCast by Vas and contributors; complete original type and whole equivalence value, preserving Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: change only the PROVED-EQUAL base arrow of a relative
point, retaining its underlying scheme map and relative group operations.
Named downstream consumer: canonical coefficient-map comparison between
integral nineteen Hopf points and fixed arithmetic norm-kernel points.
-/
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

noncomputable section
namespace MazurTransfer.RelativePointBaseCast
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
universe u
variable {B A T : Scheme.{u}} {f : A ⟶ B} {t t' : T ⟶ B}

def pointEquiv (h : t = t') : SchemeHomOver t f ≃ SchemeHomOver t' f where
  toFun x := ⟨x.val, x.property.trans h⟩
  invFun x := ⟨x.val, x.property.trans h.symm⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl







variable {R : Type u} [CommRing R] {A T : Scheme.{u}}
variable {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
variable {t t' : T ⟶ Spec (CommRingCat.of R)}





end MazurTransfer.RelativePointBaseCast
#print axioms MazurTransfer.RelativePointBaseCast.pointEquiv


