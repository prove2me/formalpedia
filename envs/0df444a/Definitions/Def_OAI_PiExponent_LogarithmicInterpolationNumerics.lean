-- Prove2me | Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
-- name    : OAI_PiExponent_LogarithmicInterpolationNumerics
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-20T08:25:44.938657+00:00
-- url     : https://prove2.me/theorems/d4017370-68f5-40de-bd61-4e4323e50b7c
-- title:
--   Numerical hypotheses for logarithmic weighted interpolation
-- statement:
--   A proposition bundling positive dimension, center count, sigma, and rational weights together with the full strict volume, fibre-volume, separated-product, and coordinate-ratio hypotheses of the logarithmic curve-contact inequality.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily

open scoped BigOperators

namespace OAI.PiExponent.FormalInterpolation

/-- Rational degree and jet weights satisfying the numerical hypotheses of
 the logarithmic curve-contact inequality. -/
structure LogarithmicInterpolationNumerics
    (m K : Nat) (w v : Fin (m + 1) → Rat) (sigma : Rat) : Prop where
  m_pos : 1 ≤ m
  K_pos : 1 ≤ K
  sigma_pos : 0 < (sigma : Real)
  degree_pos : ∀ i, 0 < (w i : Real)
  jet_pos : ∀ i, 0 < (v i : Real)
  volume :
    (K : Real) * (1 + 3 * (sigma : Real)) ^ (m + 1) *
      (∏ i, (w i : Real)) / (∏ i, (v i : Real)) < 1
  fibre_volume :
    (K : Real) * (1 + 3 * (sigma : Real)) ^ m *
      (∏ i : Fin m, (w i.succ : Real)) /
        (∏ i : Fin m, (v i.succ : Real)) < 1
  separated :
    ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
        (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
        interpolationSeparationConstant m sigma *
          (∏ j ∈ B, (v j : Real)) < ∏ j ∈ A, (w j : Real)
  coordinate_ratio :
    ∀ i : Fin m, (1 + (sigma : Real)) * (w i.succ : Real) <
      (v i.succ : Real)

end OAI.PiExponent.FormalInterpolation


