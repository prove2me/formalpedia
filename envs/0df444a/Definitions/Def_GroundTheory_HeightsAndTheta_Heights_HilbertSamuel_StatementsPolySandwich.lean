-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPolySandwich
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPolySandwich
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:34.513639+00:00
-- url     : https://prove2.me/theorems/bd8c1008-cda2-42af-83f4-6d17191d4b32
-- title:
--   Statements Poly Sandwich
-- statement:
--   Definitions and structural lemmas for Statements Poly Sandwich, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsPolySandwich.lean

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
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
def PolySandwich.Statement : Prop :=
  ∀ (D c : ℕ) (p q : Polynomial ℚ), q.natDegree ≤ D →
    (∀ᶠ n : ℕ in Filter.atTop, p.eval (n : ℚ) ≤ q.eval (n : ℚ) ∧ q.eval (n : ℚ) ≤ p.eval ((n : ℚ) + c)) →
    p.natDegree ≤ D ∧ p.coeff D = q.coeff D
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


