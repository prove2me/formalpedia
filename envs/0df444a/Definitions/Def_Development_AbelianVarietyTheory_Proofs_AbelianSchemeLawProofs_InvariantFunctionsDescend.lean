-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:49.585836+00:00
-- url     : https://prove2.me/theorems/05a063ff-4a8b-4822-9a05-b474e8850c60
-- title:
--   Invariant Functions Descend
-- statement:
--   Definitions and structural lemmas for Invariant Functions Descend, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InvariantFunctionsDescend.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FunDescent
noncomputable def coord : Γ(Spec (CommRingCat.of (Polynomial ℤ)), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv.hom Polynomial.X
noncomputable def res {X : Scheme.{0}} (U : X.Opens) : Γ(X, U) ⟶ Γ(U.toScheme, ⊤) :=
  U.ι.appLE U ⊤ (by simp)
end GlobalTheory.FunDescent
namespace GlobalTheory
end GlobalTheory


