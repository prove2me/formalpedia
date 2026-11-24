-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartPrimElt
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StChartPrimElt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:22.873339+00:00
-- url     : https://prove2.me/theorems/8329f325-9b30-4a2b-ab0d-14782d6b2967
-- title:
--   St Chart Prim Elt
-- statement:
--   Definitions and structural lemmas for St Chart Prim Elt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StChartPrimElt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
open Polynomial
def ChartPrimElt.Statement : Prop :=
  ∀ (Φ : Type) [Field Φ] [CharZero Φ] (Φ' : Type) [Field Φ'] [Algebra Φ Φ'] (Q : Type) [Fintype Q]
    (r : Q → Φ'),
    FiniteDimensional Φ (IntermediateField.adjoin Φ (Set.range r)) →
    ∃ (τ : MvPolynomial Q Φ) (g : Q → Φ[X]) (u : Φ[X]),
      (minpoly Φ (MvPolynomial.aeval r τ)).natDegree =
        Module.finrank Φ (IntermediateField.adjoin Φ (Set.range r)) ∧
      (∀ q, aeval (MvPolynomial.aeval r τ) (g q) = r q) ∧
      minpoly Φ (MvPolynomial.aeval r τ) ∣ u * derivative (minpoly Φ (MvPolynomial.aeval r τ)) - 1 ∧
      minpoly Φ (MvPolynomial.aeval r τ) ∣ MvPolynomial.aeval g τ - X ∧
      ∀ q, r q ≠ 0 → ∃ h : Φ[X], minpoly Φ (MvPolynomial.aeval r τ) ∣ h * g q - 1
section Inhabitants
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


