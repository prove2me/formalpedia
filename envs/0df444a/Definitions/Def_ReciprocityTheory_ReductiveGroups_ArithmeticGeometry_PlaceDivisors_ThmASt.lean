-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:32:23.225942+00:00
-- url     : https://prove2.me/theorems/2f155d1d-adb0-4c95-87bc-c9d4f4ef3702
-- title:
--   Thm ASt
-- statement:
--   Definitions and structural lemmas for Thm ASt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/ThmASt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace ReciprocityTheory.ChartRestriction.G.Pdiv
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
def ThmAGtStC (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
      (E : SplitExt (Spec (CommRingCat.of O))) (B : Out.PolAV (Spec (CommRingCat.of O)))
      (_ : B.A = E.B) (_ : HEq B.grp E.grpB) (G : Over (Spec (CommRingCat.of O))) [GrpObj G]
      [IsCommMonObj G],
      E.IsGt G → HTChar p v G
end ReciprocityTheory.ChartRestriction.G.Pdiv


