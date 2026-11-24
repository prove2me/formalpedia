-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarWirtinger
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarWirtinger
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:40.06382+00:00
-- url     : https://prove2.me/theorems/f08751c0-226b-4157-b793-4f0b8f8586f0
-- title:
--   St Var Wirtinger
-- statement:
--   Definitions and structural lemmas for St Var Wirtinger, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StVarWirtinger.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
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
open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal
noncomputable section
def VarWirtinger.Statement : Prop :=
  ∀ d : ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ),
      J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
      ∀ B : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet B → Bornology.IsBounded B →
        Integrable (chartDens J A (((fun x => WithLp.toLp 2 x) ⁻¹' B).indicator fun _ => 1)
            (fun _ => euclPot)) ∧
          μH[((2 * (d + 1) : ℕ) : ℝ)] (zeroSetEuc J ∩ B) =
            ENNReal.ofReal (c * ∫ y, chartDens J A (((fun x => WithLp.toLp 2 x) ⁻¹' B).indicator fun _ => 1)
              (fun _ => euclPot) y)
end
end GroundTheory.Heights₂.Heights


