-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ComplexFibreIdealBot
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ComplexFibreIdealBot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:45.595337+00:00
-- url     : https://prove2.me/theorems/5c03400f-8d49-4fc7-93c4-98400077a282
-- title:
--   Complex Fibre Ideal Bot
-- statement:
--   Definitions and structural lemmas for Complex Fibre Ideal Bot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ComplexFibreIdealBot.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)
def complexFibreIdeal {n : ℕ} (P : Ideal (MRing (PBlk n))) : Ideal (MvPolynomial (Fin n) ℂ) :=
  (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).map (MvPolynomial.map (Int.castRingHom ℂ))
def ComplexFibreCycle.Statement : Prop :=
  ∀ (n e δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsArithVar P (e + 1) →
    ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ f →
      (∀ W ∈ (fundCycle (complexFibreIdeal P)).support, IsProjPrime W) ∧
      IsChowFormCycle (fundCycle (complexFibreIdeal P)) (e + 1) f ∧
      ∀ u : Fin n → ℂ, IndefiniteRowSideFullHecke.ArithBezout.specFirst u f ≠ 0 ↔
        ∀ W ∈ (fundCycle (complexFibreIdeal P)).support, linForm u ∉ W
end GroundTheory.Heights₂.Heights


