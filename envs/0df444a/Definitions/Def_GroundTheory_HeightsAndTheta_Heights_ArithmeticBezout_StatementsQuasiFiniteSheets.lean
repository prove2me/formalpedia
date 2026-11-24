-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:16.55744+00:00
-- url     : https://prove2.me/theorems/e49f38a8-1691-4ad4-8bfa-c2cd5516b7b9
-- title:
--   Statements Quasi Finite Sheets
-- statement:
--   Definitions and structural lemmas for Statements Quasi Finite Sheets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsQuasiFiniteSheets.lean

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
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
def QuasiFiniteSheets.Statement : Prop :=
  ∀ (n d : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ),
    (∀ y : Fin d → ℂ, (ComplexSets.fibre I A y).Finite) →
      ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ ∀ y : Fin d → ℂ, eval y c ≠ 0 →
        ∃ (U : Set (Fin d → ℂ)) (N : ℕ) (s : Fin N → (Fin d → ℂ) → Fin n → ℂ),
          IsOpen U ∧ y ∈ U ∧ (∀ j, DifferentiableOn ℂ (s j) U) ∧
          ∀ y' ∈ U, (∀ j, s j y' ∈ ComplexSets.fibre I A y') ∧
            Function.Injective (fun j => s j y') ∧
            ComplexSets.fibre I A y' ⊆ Set.range (fun j => s j y')
end GroundTheory.Heights₂.Heights


