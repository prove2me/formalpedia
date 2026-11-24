-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TwoMemFunFieldSpecZ
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_TwoMemFunFieldSpecZ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:48.438686+00:00
-- url     : https://prove2.me/theorems/9e87ea23-466d-424d-bcb0-b7ff151c645c
-- title:
--   Two Mem Fun Field Spec Z
-- statement:
--   Definitions and structural lemmas for Two Mem Fun Field Spec Z, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/TwoMemFunFieldSpecZ.lean

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
def RegularityFormula.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (b : funField P),
    IsArithVar P 1 → b ≠ 0 → (∀ W, IsClosedPt W → P ≤ W → (b : FractionRing (MRing ι ⧸ P)) ∈ locRing P W) →
    {W | IsClosedPt W ∧ P ≤ W ∧ Nat.card (locRing P W ⧸ locIdeal P W b) ≠ 1}.Finite ∧
      ∑ᶠ W ∈ {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W},
          Real.log (Nat.card (locRing P W ⧸ locIdeal P W b)) =
        ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ b‖
end
end GroundTheory.Heights₂.Heights.Inter


