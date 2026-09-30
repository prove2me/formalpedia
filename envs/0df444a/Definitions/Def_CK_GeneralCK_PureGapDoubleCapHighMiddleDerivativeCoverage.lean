-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeCoverage
-- name    : CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeCoverage
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:54:50.507344+00:00
-- url     : https://prove2.me/theorems/0aaea7be-61c5-48c3-a998-4d6077a1c695
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapHighMiddleDerivativeCoverage` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapHighMiddleDerivativeCoverage` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapHighMiddleDerivativeCoverage` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapHighMiddleDerivativeCoverage (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapHighMiddleDerivativeCoverage.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailSevenSixteenthsActualSign

-- ===== source module GeneralCK.PureGapDoubleCapHighMiddleDerivativeCoverage =====
section

/-! Exact 256-cell dyadic coverage and a sound per-cell derivative-sign
interface for the remaining `x∈[1/8,1/5]` high-cap slope bridge.
The individual derivative cells and derivative formula are separate obligations. -/

namespace GeneralCK

noncomputable def doubleCapBridgeStep : ℝ := 3 / 10240

noncomputable def doubleCapBridgeLo (i : Fin 256) : ℝ :=
  1 / 8 + (i.val : ℝ) * doubleCapBridgeStep

noncomputable def doubleCapBridgeHi (i : Fin 256) : ℝ :=
  1 / 8 + ((i.val + 1 : ℕ) : ℝ) * doubleCapBridgeStep

theorem doubleCapBridge_complete_256_cover {x : ℝ}
    (hx : x ∈ Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ)) :
    ∃ i : Fin 256, x ∈ Set.Icc (doubleCapBridgeLo i)
      (doubleCapBridgeHi i) := by
  have hδ : 0 < doubleCapBridgeStep := by norm_num [doubleCapBridgeStep]
  let t : ℝ := (x - 1 / 8) / doubleCapBridgeStep
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hx.1]) hδ.le
  have ht256 : t ≤ 256 := by
    change (x - 1 / 8) / doubleCapBridgeStep ≤ 256
    apply (div_le_iff₀ hδ).2
    norm_num [doubleCapBridgeStep]
    linarith [hx.2]
  have hxEq : x = 1 / 8 + t * doubleCapBridgeStep := by
    dsimp [t]
    field_simp [hδ.ne'] <;> ring
  by_cases ht : t < 256
  · let n : ℕ := Nat.floor t
    have hn : n < 256 := (Nat.floor_lt ht0).2 ht
    have hlo : (n : ℝ) ≤ t := Nat.floor_le ht0
    have hhi : t < (n : ℝ) + 1 := Nat.lt_floor_add_one t
    refine ⟨⟨n, hn⟩, ?_⟩
    constructor
    · dsimp [doubleCapBridgeLo]
      rw [hxEq]
      have hm := mul_le_mul_of_nonneg_right hlo hδ.le
      linarith
    · dsimp [doubleCapBridgeHi]
      rw [hxEq]
      have hm := mul_lt_mul_of_pos_right hhi hδ
      simpa only [Nat.cast_add, Nat.cast_one, add_comm] using
        (add_le_add_left hm.le (1 / 8 : ℝ))
  · have htEq : t = 256 := by linarith [ht256]
    refine ⟨⟨255, by decide⟩, ?_⟩
    constructor
    · dsimp [doubleCapBridgeLo]
      rw [hxEq, htEq]
      norm_num [doubleCapBridgeStep]
    · dsimp [doubleCapBridgeHi]
      rw [hxEq, htEq] <;> norm_num [doubleCapBridgeStep]

structure DoubleCapBridgeDerivativeCellCertificate (i : Fin 256)
    (derivativeExpression : ℝ → ℝ) : Prop where
  positive : ∀ x : ℝ, x ∈ Set.Icc (doubleCapBridgeLo i)
    (doubleCapBridgeHi i) → 0 < derivativeExpression x

theorem doubleCapBridge_derivative_pos_of_256_cells
    {derivativeExpression : ℝ → ℝ}
    (hCells : ∀ i : Fin 256,
      DoubleCapBridgeDerivativeCellCertificate i derivativeExpression)
    {x : ℝ} (hx : x ∈ Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ)) :
    0 < derivativeExpression x := by
  obtain ⟨i, hCell⟩ := doubleCapBridge_complete_256_cover hx
  exact (hCells i).positive x hCell

#print axioms doubleCapBridge_complete_256_cover
#print axioms doubleCapBridge_derivative_pos_of_256_cells

end GeneralCK

end


