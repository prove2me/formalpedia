-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsBasisMemOfSpanEqTopOfSemilocal
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsBasisMemOfSpanEqTopOfSemilocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:31:23.720797+00:00
-- url     : https://prove2.me/theorems/776fe35f-f56d-4890-bf62-0ee476f9976b
-- title:
--   Exists Basis Mem Of Span Eq Top Of Semilocal
-- statement:
--   Definitions and structural lemmas for Exists Basis Mem Of Span Eq Top Of Semilocal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsBasisMemOfSpanEqTopOfSemilocal.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace SemilocalBasis
open scoped Pointwise
noncomputable def red {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M] {n : ℕ}
    (e : Module.Basis (Fin n) B M) (I : Ideal B) : M →ₗ[B] (Fin n → B ⧸ I) :=
  LinearMap.pi fun j => (Submodule.mkQ I).comp (e.coord j)
end SemilocalBasis
end GlobalTheory


