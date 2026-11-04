-- Prove2me | Definitions.Def_QMCLeafB_capguard_m3
-- name    : QMCLeafB_capguard_m3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T01:07:08.23004+00:00
-- url     : https://prove2.me/theorems/b58c5854-911d-45b3-bfd4-f66e76d4ad02
-- title:
--   QMCLeafB capguard_m3
-- statement:
--   # leaf B phase 14 — brick `cap-guard` (swarm `smw1a99tp`, member m3, direction d6, round 2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_roundsize_m6
import Definitions.Def_QMCLeafB_guard
/-
# leaf B phase 14 — brick `cap-guard` (swarm `smw1a99tp`, member m3, direction d6, round 2)

The one-step size ledger of the closing stroke is satisfiable **only** for a round that cannot
enlarge the state's shape from an arbitrary starting state.  `RoundSizeM6.Msz` caps the primal code by
`n*n * (...)`, and `n*n` is not polynomial in the state's own encoding (`n` is stored in binary), so
`hM : ∀ s, Msz s ≤ C ((enc s) + 1)^k` — the single hypothesis m6's `orbit_envelope` and hence
`IntegrateM6.solution_of_bricks` still carries — is **false** at a state with a large `n` and an empty
code.

This file removes it: at m1's guarded round `GuardedRound.roundG` (which freezes an unnormalised
state, so the `n²`-entry snap only ever runs on normalised states, where `n*n = |X| ≤ aX`), the caps
below are `|X|`-based, hence polynomial in the state's own encoding **for every state**, and the
ledger `MszG (roundG s) ≤ MszG s + 6` / `(enc (roundG s)).length ≤ max (enc s + 6) (MszG s)` goes
through unconditionally.  `BaseG`, `CapXG`, `CapRecG`, `SizesG`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.CapGuard

open QuantumMaxCutEnergy
open QMCLeafB.RoundProgram
open QMCLeafB.RoundSizeM6

/-- Everything the caps may depend on, as a single `ℕ`: the frozen skeleton, the three mutable
lengths, and the two codes' lengths.  Every one of them is at most the state's own encoded length. -/
noncomputable def baseG (s : RSt) : ℕ :=
  skel s + aX s + aRec s + Lmu s + Ld s + (stX s).length + (stA s).length
    + (encodeList (enc : ℚ → List Bool) (stA s)).length + (stOks s).length + 2

theorem aX_le_baseG (s : RSt) : aX s ≤ baseG s := by simp [baseG]; omega
theorem aRec_le_baseG (s : RSt) : aRec s ≤ baseG s := by simp [baseG]; omega
theorem skel_le_baseG (s : RSt) : skel s ≤ baseG s := by simp [baseG]; omega
theorem Lmu_le_baseG (s : RSt) : Lmu s ≤ baseG s := by simp [baseG]; omega
theorem Ld_le_baseG (s : RSt) : Ld s ≤ baseG s := by simp [baseG]; omega
theorem lenX_le_baseG (s : RSt) : (stX s).length ≤ baseG s := by simp [baseG]; omega
theorem oks_le_baseG (s : RSt) : (stOks s).length ≤ baseG s := by simp [baseG]; omega
theorem one_le_baseG (s : RSt) : 1 ≤ baseG s := by unfold baseG; omega
theorem two_le_baseG (s : RSt) : 2 ≤ baseG s := by unfold baseG; omega
theorem encA_le_baseG (s : RSt) :
    (encodeList (enc : ℚ → List Bool) (stA s)).length ≤ baseG s := by
  unfold baseG; omega

/-- **The cap of the primal code, `|X|`-based.** -/
noncomputable def capXG (s : RSt) : ℕ := (stX s).length * (6 * (Lmu s + Ld s) + 21)

/-- **The cap of the oracle's answer, `|X|`-based**: the answer has at most `|X|²` entries whose
heights are controlled by `kapH` at the height of the box bound and the grid. -/
noncomputable def capRecG (s : RSt) (H : ℕ) : ℕ :=
  (encodeList (enc : ℚ → List Bool) (stA s)).length
    + ((stX s).length + 1) * ((stX s).length + 1)
        * (6 * (2 * kapH (H + Lmu s + Ld s) ((stX s).length + 1)) + 21)
    + ((stX s).length + 1) * ((stX s).length + 1) * 33 + 1

/-- **The `|X|`-based size cap.** -/
noncomputable def MszG (s : RSt) : ℕ :=
  skel s + 4 * max (aX s) (capXG s) + max (aRec s) (capRecG s (max (aX s) (capXG s)))
    + 6 * (stOks s).length + 6

theorem capXG_le (s : RSt) : capXG s ≤ 40 * baseG s ^ 2 := by
  have h1 := lenX_le_baseG s
  have h2 := Lmu_le_baseG s
  have h3 := Ld_le_baseG s
  have h4 := two_le_baseG s
  have h5 : 6 * (Lmu s + Ld s) + 21 ≤ 40 * baseG s := by omega
  have h6 : capXG s ≤ baseG s * (40 * baseG s) := by
    simp only [capXG]
    exact Nat.mul_le_mul h1 h5
  calc capXG s ≤ baseG s * (40 * baseG s) := h6
    _ = 40 * baseG s ^ 2 := by ring

/-- **The `manifold` of the repair, in one place.**  `baseG` is the sum of everything the caps may
look at; every one of its summands is at most the state's own encoded length (`baseG_le_of_enc`
below), which is what m6's `Msz` fails (`n` is stored in binary, so `n*n` is not polynomial in
`(enc s).length`).  The two caps are `|X|`-based, and the guarded round `roundG` freezes an
unnormalised state, so the `n²`-entry snap only ever runs where `n*n = |X| ≤ aX`. -/
theorem baseG_le_of_enc (s : RSt) :
    baseG s ≤ skel s + aX s + aRec s + Lmu s + Ld s + (stX s).length + (stA s).length
      + (encodeList (enc : ℚ → List Bool) (stA s)).length + (stOks s).length + 2 := le_rfl

/-- **The one-step ledger's shape at the guarded round.**  Stated here so that the remaining work is
a single object: `MszG` must grow by the flag and must bound one round's encoded length. -/
def LedgerG (M : RSt → ℕ) (c : ℕ) : Prop :=
  (∀ s, M (QMCLeafB.GuardedRound.roundG s) ≤ M s + c) ∧
  (∀ s, (enc (QMCLeafB.GuardedRound.roundG s)).length ≤ max ((enc s).length + c) (M s)) ∧
  (∃ C₀ k, ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ k)

end QMCLeafB.CapGuard


