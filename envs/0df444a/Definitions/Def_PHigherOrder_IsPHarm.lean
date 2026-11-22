-- Prove2me | Definitions.Def_PHigherOrder_IsPHarm
-- name    : PHigherOrder_IsPHarm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:09:41.648239+00:00
-- url     : https://prove2.me/theorems/42b807fb-6701-4c69-932a-926171a70bd8
-- title:
--   Is PHarm
-- statement:
--   Definitions and structural lemmas for Is PHarm, from na0b and contributors's pinned Higher-order estimates for planar p-harmonic functions under the stated hypotheses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/IsPHarm.lean

import Definitions.Def_PHigherOrder_PFlux
set_option autoImplicit false
structure IsPHarm (p : ℝ) (Ω : Set Plane) (u : Plane → ℝ) (g : Plane → Plane) : Prop where
  openOmega : IsOpen Ω
  contU : ContinuousOn u Ω
  measG : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict Ω)
  locIntG : ∀ K : Set Plane, K ⊆ Ω → IsCompact K →
      MeasureTheory.IntegrableOn (fun x => ‖g x‖ ^ p) K
  weakGrad : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∫ x in Ω, u x • gradient φ x = - ∫ x in Ω, φ x • g x
  eqn : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∫ x in Ω, inner ℝ (PFlux p (g x)) (gradient φ x) = (0 : ℝ)


