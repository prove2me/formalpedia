-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveRegularOffCentre
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveRegularOffCentre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:09.379294+00:00
-- url     : https://prove2.me/theorems/1f6a3a45-c942-404c-941e-469dd4981f44
-- title:
--   St Curve Regular Off Centre
-- statement:
--   Definitions and structural lemmas for St Curve Regular Off Centre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCurveRegularOffCentre.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchNormalisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets Filter Topology
noncomputable section
def CurveRegularOffCentre.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    ringKrullDim (curveLocalRing I q) = 1 →
      ∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet I ∩ N, x ≠ q →
        ∃ (A : (Fin n → ℂ) →L[ℂ] ℂ) (O : Set ℂ) (V : Set (Fin n → ℂ)) (g : ℂ → Fin n → ℂ),
          IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧
            zeroSet I ∩ V = g '' O
end
end GroundTheory.Heights₂.Heights


