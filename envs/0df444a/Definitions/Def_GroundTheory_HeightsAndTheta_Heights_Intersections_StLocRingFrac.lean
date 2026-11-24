-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingFrac
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingFrac
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:02.58781+00:00
-- url     : https://prove2.me/theorems/aca04416-add5-4723-a0a5-a43c87db8d7b
-- title:
--   St Loc Ring Frac
-- statement:
--   Definitions and structural lemmas for St Loc Ring Frac, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StLocRingFrac.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def LocRingFrac.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)),
    P.IsPrime → W.IsPrime → P ≤ W →
    ∀ y ∈ locRing P W, ∃ (u v : MRing ι) (a : K → ℕ),
      IsMultiHomog u a ∧ IsMultiHomog v a ∧ v ∉ W ∧ y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)
end
end GroundTheory.Heights₂.Heights.Inter


