-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalSheets
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalSheets
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:52.370638+00:00
-- url     : https://prove2.me/theorems/fbef21fe-9bbb-4bf9-adf8-dd63b8edd18f
-- title:
--   Statements Cone Local Sheets
-- statement:
--   Definitions and structural lemmas for Statements Cone Local Sheets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeLocalSheets.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetCover
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj mcPts fibre segre)
def ConeLocalSheets.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      ∃ (c : MvPolynomial (Fin (e + 1)) ℂ) (m : ℕ), c ≠ 0 ∧ c.IsHomogeneous m ∧
        ∀ x : Fin e → ℂ, eval (Fin.cons 1 x : Fin (e + 1) → ℂ) c ≠ 0 →
          ∃ (U : Set (Fin e → ℂ)) (N : ℕ) (s : Fin N → (Fin e → ℂ) → (Σ k, PBlk n k) → ℂ),
            IsOpen U ∧ x ∈ U ∧ (∀ j, DifferentiableOn ℂ (s j) U) ∧
            ∀ y ∈ U, (∀ j, s j y ∈ mcPts P ∧ Ψ (segre (s j y)) = Fin.cons 1 y) ∧
              Function.Injective (fun j => s j y) ∧
              fibre P Ψ y ⊆ Set.range (fun j => segre (s j y))
end GroundTheory.Heights₂.Heights


