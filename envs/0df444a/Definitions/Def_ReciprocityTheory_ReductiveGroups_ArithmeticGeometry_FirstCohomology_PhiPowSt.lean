-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:28.432524+00:00
-- url     : https://prove2.me/theorems/9c2a776b-6fff-47ca-a9cf-3a529d33e751
-- title:
--   Phi Pow St
-- statement:
--   Definitions and structural lemmas for Phi Pow St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/PhiPowSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt
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
open CategoryTheory AlgebraicGeometry
namespace ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
def PhiPowStatement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I)
    (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
    ∀ (p : QkPt D.toPre F k)
      (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))),
      w.IsGen →
      ∃ c : F, c ≠ 0 ∧ ∀ ss : Fin (k + 1) → Fam D.toPre F k,
        (∀ i : Fin k, PhiRel D.toPre F k p w (ss i.castSucc) (ss i.succ)) →
        Fam.IsSmul D.toPre F c (ss 0) (ss (Fin.last k))
end ReciprocityTheory.ChartRestriction.G.H1


