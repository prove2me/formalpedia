-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_ParamsWindow
-- name    : Formalism_PieriBlockIdeals_ParamsWindow
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:16:22.261997+00:00
-- url     : https://prove2.me/theorems/339f87ee-392d-40af-867b-358f3f0cd60b
-- title:
--   Params Window
-- statement:
--   Definitions and structural lemmas for Params Window, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/ParamsWindow.lean

import Mathlib
import Definitions.Def_Formalism_RankGapBounds_CloudMinFalse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.CohomologicalDescent
def lamOf (N : ℕ) (U : ℕ → ℤ) (i : ℕ) : ℤ := U i - ((N : ℤ) - 1 - (i : ℤ))
def CrossTerm : Prop :=
  ∀ (l N h a : ℕ) (U : ℕ → ℤ), l.Prime → (∀ i j, i < j → j < N → U j < U i) →
    (∀ i < N, 0 ≤ U i ∧ U i ≤ (h : ℤ)) → a ≤ N →
    ∑ i ∈ Finset.range a, ∑ j ∈ Finset.Ico a N,
      (Nat.log l (((j : ℤ) - (i : ℤ) + lamOf N U 0 - lamOf N U (N - 1)).toNat) -
        padicValInt l (lamOf N U i - lamOf N U j + (j : ℤ) - (i : ℤ))) ≤
      a * (N - a) * Nat.log l (2 * h + N)
def ExpStopH : Prop :=
  ∀ (l N h : ℕ) (U : Fin N → ℤ), l.Prime → StrictAnti U → (∀ i, 0 ≤ U i ∧ U i ≤ (h : ℤ)) →
    h < l → Formalism.RankGapBounds.JumpSetsAlt.eExp U l = 0
def ParamsWindow : Prop :=
  ∀ (b h l t : ℕ) (lstar h0 η : ℝ), 1 ≤ lstar → (h : ℝ) ≤ 2 * b → lstar < (l : ℝ) →
    12 * b / lstar + 2 * t + 8 ≤ h0 → 2 * η + t + 8 * b / lstar + 7 < lstar → 0 ≤ η →
    ((h / (l - 1) : ℕ) : ℝ) ≤ h0 / 4 - t / 2 - 2 ∧ η + t + ((h / (l - 1) : ℕ) : ℝ) < l ∧
      0 < h0 / 2 - 1 - t / 2 - ((h / (l - 1) : ℕ) : ℝ)
end Formalism.CohomologicalDescent


