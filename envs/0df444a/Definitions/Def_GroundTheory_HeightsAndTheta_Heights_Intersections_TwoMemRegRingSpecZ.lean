-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TwoMemRegRingSpecZ
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_TwoMemRegRingSpecZ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:33.191496+00:00
-- url     : https://prove2.me/theorems/27ed75bf-fcda-4d68-98ce-6fa82a50beff
-- title:
--   Two Mem Reg Ring Spec Z
-- statement:
--   Definitions and structural lemmas for Two Mem Reg Ring Spec Z, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/TwoMemRegRingSpecZ.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TwoMemFunFieldSpecZ
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
def regRing {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) :
    Subring (funField P) where
  carrier := {x | ∀ W, IsClosedPt W → P ≤ W → (x : FractionRing (MRing ι ⧸ P)) ∈ locRing P W}
  mul_mem' ha hb W h1 h2 := mul_mem (ha W h1 h2) (hb W h1 h2)
  one_mem' _ _ _ := one_mem _
  add_mem' ha hb W h1 h2 := add_mem (ha W h1 h2) (hb W h1 h2)
  zero_mem' _ _ _ := zero_mem _
  neg_mem' ha W h1 h2 := neg_mem (ha W h1 h2)
def RegularityOrder.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → Module.Free ℤ (regRing P) ∧ Module.Finite ℤ (regRing P) ∧
      ∀ hF : IsField (funField P), letI := hF.toField; ∀ [NumberField (funField P)],
        Module.finrank ℤ (regRing P) = Module.finrank ℚ (funField P)
end
end GroundTheory.Heights₂.Heights.Inter


