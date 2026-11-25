-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameThresholdBoundHolds
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameThresholdBoundHolds
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T04:31:35.492695+00:00
-- url     : https://prove2.me/theorems/332383cd-1806-4fd5-b466-7b3dd5e56432
-- title:
--   Frame Threshold Bound Holds
-- statement:
--   Definitions and structural lemmas for Frame Threshold Bound Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameThresholdBoundHolds.lean

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt
def FrameThresholdBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : Sz.Glob ι) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ) (w : ι),
    0 < G.g → 0 < G.lenI → 28 * Real.exp 1 ≤ C →
    (∀ one, 0 ≤ J.supA G de de' T T' l one w) →
    (∀ (b s : ℕ) (Q cg : ℝ), 1 ≤ b → 0 ≤ Q → Q ≤ Real.exp 1 → 0 ≤ cg →
      cg ≤ (28 * G.N / G.lenI) ^ (2 * (b - 1) + s) →
      (2 * Real.pi / G.g) ^ (-(S6.nuBlock G.r b s)) * Q * cg *
          J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w ≤
        J.thrS G C de de' T T' l b (s + 1) w) ∧
    (∀ (b : ℕ) (Q cg : ℝ), 1 ≤ b → 0 ≤ Q → Q ≤ Real.exp 1 → 0 ≤ cg →
      cg ≤ (28 * G.N / G.lenI) ^ (2 * (b - 1)) →
      √((2 * Real.pi / G.g) ^ (-(2 * S6.nuBlock G.r b ((G.r : ℤ) + 2 - b))) * Q * cg *
          J.supA G de de' T T' l false w * (√(T * T'))⁻¹) ≤
        J.thrP G C de de' T T' l b w)
end Formalism.FourierDecayAlt.P.PBD


