-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:50:19.626076+00:00
-- url     : https://prove2.me/theorems/2020a03e-61fb-4613-a8b1-1f9acf45fd38
-- title:
--   Phi Gen
-- statement:
--   Definitions and structural lemmas for Phi Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PhiGen.lean

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
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
def PhiFunStatement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I)
    (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
    ∀ (p : QkPt D.toPre F k)
      (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))),
      w.IsGen →
      ∃ Φ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k,
        ∀ s t : Fam D.toPre F k, PhiRel D.toPre F k p w s t ↔ t = Φ s
end ReciprocityTheory.ChartRestriction.G.DVR


