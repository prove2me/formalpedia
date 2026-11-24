-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartSpecCount
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StChartSpecCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:13.483093+00:00
-- url     : https://prove2.me/theorems/e3d81227-5540-4223-a2fd-8e4a756ac23a
-- title:
--   St Chart Spec Count
-- statement:
--   Definitions and structural lemmas for St Chart Spec Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StChartSpecCount.lean

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
def ChartSpecCount.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (Φ : Type) [Field Φ] [CharZero Φ] (Φ' : Type) [Field Φ'] [Algebra Φ Φ']
    (φ : R →+* Φ) (Q : Type) [Fintype Q] (r : Q → Φ'),
    (∀ c : Φ, ∃ f g : R, φ g ≠ 0 ∧ c = φ f / φ g) →
    FiniteDimensional Φ (IntermediateField.adjoin Φ (Set.range r)) →
    ∃ E : R, φ E ≠ 0 ∧ ∀ ψ : R →+* ℂ, RingHom.ker φ ≤ RingHom.ker ψ → ψ E ≠ 0 →
      {y : Q → ℂ | ∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
          MvPolynomial.eval₂ ψ y F = 0}.Finite ∧
      {y : Q → ℂ | ∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
          MvPolynomial.eval₂ ψ y F = 0}.ncard =
        Module.finrank Φ (IntermediateField.adjoin Φ (Set.range r)) ∧
      ∀ y : Q → ℂ, (∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
          MvPolynomial.eval₂ ψ y F = 0) → ∀ q, r q ≠ 0 → y q ≠ 0
section Inhabitants
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


