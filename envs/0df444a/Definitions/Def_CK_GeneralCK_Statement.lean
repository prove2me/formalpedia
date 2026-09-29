-- Prove2me | Definitions.Def_CK_GeneralCK_Statement
-- name    : CK_GeneralCK_Statement
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:16:09.120492+00:00
-- url     : https://prove2.me/theorems/e6146a41-956e-4ccf-bf20-a6aa5902bc4c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Statement` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Statement` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Statement` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Statement (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Statement.lean)

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_statement

/-! Precise target, not a proof of the Courtade--Kumar conjecture. -/
namespace GeneralCK
open scoped BigOperators
































theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

@[simp] theorem H_zero : H 0 = 0 := by simp [H]
@[simp] theorem H_one : H 1 = 0 := by simp [H]
@[simp] theorem H_half : H (1 / 2) = 1 := by
  have h : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  simpa [H, one_div] using div_self h

theorem H_complement (p : ℝ) : H (1 - p) = H p := by simp [H]

theorem H_nonneg {p : ℝ} (h₀ : 0 ≤ p) (h₁ : p ≤ 1) : 0 ≤ H p :=
  div_nonneg (Real.binEntropy_nonneg h₀ h₁) log_two_pos.le

theorem H_le_one (p : ℝ) : H p ≤ 1 := by
  rw [H, div_le_one log_two_pos]
  exact Real.binEntropy_le_log_two

theorem H_continuous : Continuous H :=
  Real.binEntropy_continuous.div_const _

end GeneralCK


