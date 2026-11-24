-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedPointsCount
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedPointsCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:39.11996+00:00
-- url     : https://prove2.me/theorems/deba2554-3e6d-4e4e-aee9-ef10b2ff5fed
-- title:
--   St Isolated Points Count
-- statement:
--   Definitions and structural lemmas for St Isolated Points Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StIsolatedPointsCount.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
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
open MvPolynomial Topology ComplexSets
noncomputable section
def isolatedFibrePts {n m : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (Q : Fin m → MvPolynomial (Fin n) ℂ)
    (z : Fin m → ℂ) : Set (Fin n → ℂ) :=
  {x | x ∈ zeroSet J ∧ (∀ i, eval x (Q i) = z i) ∧
    ∃ V ∈ 𝓝 x, ∀ x' ∈ zeroSet J ∩ V, (∀ i, eval x' (Q i) = z i) → x' = x}
def IsolatedPointsCount.Statement : Prop :=
  ∀ (n m : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (Q : Fin m → MvPolynomial (Fin n) ℂ),
    ∃ N : ℕ, ∀ z : Fin m → ℂ, (isolatedFibrePts J Q z).encard ≤ N
end
end GroundTheory.Heights₂.Heights


