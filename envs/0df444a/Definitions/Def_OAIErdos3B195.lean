-- Prove2me | Definitions.Def_OAIErdos3B195
-- name    : OAIErdos3B195
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T09:14:41.328581+00:00
-- url     : https://prove2.me/theorems/cb6a35a0-cd69-4015-b91e-fd5927db5ffd
-- title:
--   OpenAI Erdős-3 split, definitions bundle 196 of 206
-- statement:
--   Definitions bundle 196 of 206 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B194`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 196 available.
--
--   Modules: `OAI.Erdos3.exists_sharedFreeProperAffineSelection_bound`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B189

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SharedFreeAffineBudget
namespace OAI

section

namespace Erdos3

open CyclicCrootSisask

end Erdos3

end

section

namespace Erdos3

open CyclicCrootSisask

end Erdos3

end

section

namespace Erdos3

open CyclicCrootSisask

end Erdos3

end

section

namespace Erdos3

open CyclicCrootSisask

theorem exists_sharedFreeProperAffineSelection_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → ∀ n : ℕ, (n : ℝ) ≤ 4 * (s : ℝ) * p →
      properAffineRecoveryLogLoss ((p + 2) ^ 3 + 2 * p) n ≤ (p + C) ^ C ∧
      properAffineScaleLog ((p + 2) ^ 3 + 2 * p) n ≤ (p + C) ^ C ∧
      properAffineRankBound ((p + 2) ^ 3 + 2 * p) n ≤ (p + C) ^ C := by
  let c := ⌈max quarticBogolyubovProgressionConstant quarticBogolyubovConstant⌉₊
  have hc₀ : quarticBogolyubovProgressionConstant ≤ (c : ℝ) :=
    (le_max_left _ _).trans (Nat.le_ceil _)
  have hc₁ : quarticBogolyubovConstant ≤ (c : ℝ) :=
    (le_max_right _ _).trans (Nat.le_ceil _)
  let PB : Polynomial ℕ := (Polynomial.X + 2) ^ 3 + 2 * Polynomial.X
  let PD : Polynomial ℕ := 4 * Polynomial.C s * Polynomial.X
  let PZ : Polynomial ℕ := 736 + 96 * PB + 1504 * PD
  let PR : Polynomial ℕ := 2 + Polynomial.C c * (PZ + 1) ^ 4
  let PA : Polynomial ℕ := Polynomial.C c * (PZ + 1) ^ 8 + (PB + 13 * PD) + 16 * (PD + 3)
  let PV : Polynomial ℕ := 2 + 16 * (44 + 6 * PB + 94 * PD)
  let PT : Polynomial ℕ := 2 * PR + PV + PA + 2
  let PL : Polynomial ℕ := PA + (4 + PT) * PR
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (PL + PT + PR)
  refine ⟨C, hC, ?_⟩
  intro p hp n hn
  let B := (p + 2) ^ 3 + 2 * p
  let D := 4 * (s : ℝ) * p
  let Z := 736 + 96 * B + 1504 * D
  let R := 2 + (c : ℝ) * (Z + 1) ^ 4
  let A := (c : ℝ) * (Z + 1) ^ 8 + (B + 13 * D) + 16 * (D + 3)
  let V := 2 + 16 * (44 + 6 * B + 94 * D)
  let T := 2 * R + V + A + 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hz : roundedModelLogBudget B n ≤ Z := by
    unfold roundedModelLogBudget
    rw [max_eq_left hB]
    dsimp [Z]
    gcongr
  have hz0 : 0 ≤ roundedModelLogBudget B n + 1 := by
    linarith [roundedModelLogBudget_nonneg B n]
  have hrank : properAffineRankBound B n ≤ R := by
    unfold properAffineRankBound
    dsimp [R]
    gcongr
  have hloss : affineRecoveryLogLoss B n ≤ A := by
    unfold affineRecoveryLogLoss
    dsimp [A]
    gcongr
  have hvolume : properAffineVolumeLog B n ≤ V := by
    unfold properAffineVolumeLog
    rw [max_eq_left hB]
    dsimp [V]
    gcongr
  have hscale : properAffineScaleLog B n ≤ T := by
    unfold properAffineScaleLog
    dsimp [T]
    linarith only [hrank, hloss, hvolume]
  have hrank0 : 0 ≤ properAffineRankBound B n := by
    have hc := quarticBogolyubovConstant_pos.le
    unfold properAffineRankBound
    positivity
  have hloss0 : 0 ≤ affineRecoveryLogLoss B n := by
    have hc := quarticBogolyubovProgressionConstant_pos.le
    unfold affineRecoveryLogLoss
    positivity
  have hscale0 : 0 ≤ properAffineScaleLog B n := by
    unfold properAffineScaleLog properAffineVolumeLog
    positivity
  have hproper : properAffineRecoveryLogLoss B n ≤ A + (4 + T) * R := by
    unfold properAffineRecoveryLogLoss
    exact add_le_add hloss (mul_le_mul (by linarith only [hscale]) hrank hrank0
      (by linarith only [hT]))
  have heval : (PL + PT + PR).eval₂ (Nat.castRingHom ℝ) p = A + (4 + T) * R + T + R := by
    simp [PL, PT, PV, PA, PR, PZ, PD, PB, B, D, Z, R, A, V, T, Polynomial.eval₂_pow]
  have htotal := hbound p hp
  rw [heval] at htotal
  have hproper0 : 0 ≤ A + (4 + T) * R := by positivity
  exact ⟨hproper.trans (by linarith only [htotal, hT, hR]),
    hscale.trans (by linarith only [htotal, hproper0, hR]),
    hrank.trans (by linarith only [htotal, hproper0, hT])⟩

end Erdos3

end

section

namespace Erdos3

open CyclicCrootSisask

end Erdos3

end

end OAI

end


