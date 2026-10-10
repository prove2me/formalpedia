-- Prove2me | Definitions.Def_OAIErdos3B205
-- name    : OAIErdos3B205
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T09:37:50.707216+00:00
-- url     : https://prove2.me/theorems/8767c282-bfc5-43e4-81a0-eaed1dcd3dd4
-- title:
--   OpenAI Erdős-3 split, definitions bundle 206 of 206
-- statement:
--   Definitions bundle 206 of 206 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B204`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 206 available.
--
--   Modules: `OAI.Erdos3.sharedFreeAffineConstant`, `OAI.Erdos3.sharedFreeAffineConstant_proper_spec`, `OAI.Erdos3.sharedFreeAffineConstant_shift_bound`, `OAI.Erdos3.sharedFreeAffineConstant_spec`, `OAI.Erdos3.sharedFreeAffineConstant_two_le`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B195

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

end Erdos3

end

section

namespace Erdos3

open CyclicCrootSisask

noncomputable def sharedFreeAffineConstant (s : ℕ) : ℕ :=
  (exists_sharedFreeAffineUniform_bound s).choose +
    (exists_sharedFreeProperAffineSelection_bound s).choose

theorem sharedFreeAffineConstant_two_le (s : ℕ) : 2 ≤ sharedFreeAffineConstant s := by
  have h := (exists_sharedFreeAffineUniform_bound s).choose_spec.1
  unfold sharedFreeAffineConstant
  omega

theorem sharedFreeAffineConstant_shift_bound (s : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (c : ℕ) (hc : c ≤ sharedFreeAffineConstant s) :
    (p + c) ^ c ≤ (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s := by
  have hcR : (c : ℝ) ≤ sharedFreeAffineConstant s := by exact_mod_cast hc
  have hCR : (2 : ℝ) ≤ sharedFreeAffineConstant s := by
    exact_mod_cast sharedFreeAffineConstant_two_le s
  exact (pow_le_pow_left₀ (by positivity)
    (by linarith : p + c ≤ p + sharedFreeAffineConstant s) c).trans
    (pow_le_pow_right₀ (by linarith : 1 ≤ p + sharedFreeAffineConstant s) hc)

theorem sharedFreeAffineConstant_spec (s : ℕ) :
    2 ≤ sharedFreeAffineConstant s ∧
      ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
        ∀ n : ℕ, (n : ℝ) ≤ 4 * (s : ℝ) * p →
          sharedFreeRecoveryThreshold s q p ≤ (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s ∧
          affineRecoveryLogLoss ((p + 2) ^ 3 + 2 * p) n ≤
            (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s ∧
          2 + quarticBogolyubovConstant *
            (roundedModelLogBudget ((p + 2) ^ 3 + 2 * p) n + 1) ^ 4 ≤
              (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s := by
  refine ⟨sharedFreeAffineConstant_two_le s, ?_⟩
  intro q p hq hqp hp n hn
  have h := (exists_sharedFreeAffineUniform_bound s).choose_spec.2 q p hq hqp hp n hn
  have hb := sharedFreeAffineConstant_shift_bound s hp
    (exists_sharedFreeAffineUniform_bound s).choose (by unfold sharedFreeAffineConstant; omega)
  exact ⟨h.1.trans hb, h.2.1.trans hb, h.2.2.trans hb⟩

theorem sharedFreeAffineConstant_proper_spec (s : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (n : ℕ) (hn : (n : ℝ) ≤ 4 * (s : ℝ) * p) :
    properAffineRecoveryLogLoss ((p + 2) ^ 3 + 2 * p) n ≤
      (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s ∧
    properAffineScaleLog ((p + 2) ^ 3 + 2 * p) n ≤
      (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s ∧
    properAffineRankBound ((p + 2) ^ 3 + 2 * p) n ≤
      (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s := by
  have h := (exists_sharedFreeProperAffineSelection_bound s).choose_spec.2 p hp n hn
  have hb := sharedFreeAffineConstant_shift_bound s hp
    (exists_sharedFreeProperAffineSelection_bound s).choose (by unfold sharedFreeAffineConstant; omega)
  exact ⟨h.1.trans hb, h.2.1.trans hb, h.2.2.trans hb⟩

end Erdos3

end

end OAI

end


