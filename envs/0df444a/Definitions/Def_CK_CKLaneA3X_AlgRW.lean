-- Prove2me | Definitions.Def_CK_CKLaneA3X_AlgRW
-- name    : CK_CKLaneA3X_AlgRW
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:16:00.129994+00:00
-- url     : https://prove2.me/theorems/22148fe0-aad8-4e0d-b5f1-7463781ad6ba
-- title:
--   Courtade–Kumar proof module `CKLaneA3X.AlgRW` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA3X.AlgRW` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA3X.AlgRW` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA3X.AlgRW (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/AlgRW.lean)

import Mathlib

/-! Lane A3: algebraic identities for the R and W congr steps (atomic variables). -/

namespace CKLaneA3X

theorem R_alg (c d E B A : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) (_h1 : 1 - c * c ≠ 0) (hB : B ≠ 0) :
    c / d * (((2 : ℚ) : ℝ) * (A / c) + ((2 : ℚ) : ℝ) * (E * (1 / (((1 : ℚ) : ℝ) + ((-1 : ℚ) : ℝ) * (c * c))) * (1 / B))) =
      (2 * A + E * c / ((1 - c ^ 2) / 4 * (2 * B))) / d := by
  have e1 : ((1 : ℚ) : ℝ) + ((-1 : ℚ) : ℝ) * (c * c) = 1 - c * c := by push_cast; ring
  have e2 : (1 : ℝ) - c ^ 2 = 1 - c * c := by ring
  rw [e1, e2]
  push_cast
  field_simp
  ring

theorem W_alg (c E B S : ℝ) (_h1 : 1 - c * c ≠ 0) (hB : B ≠ 0) (hS : S ≠ 0) :
    ((8 : ℚ) : ℝ) * (E * E * E * (((2 : ℚ) : ℝ) * B + ((-1 : ℚ) : ℝ) * (c * c)) * (1 / S) *
      (1 / (((1 : ℚ) : ℝ) + ((-1 : ℚ) : ℝ) * (c * c)) * (1 / (((1 : ℚ) : ℝ) + ((-1 : ℚ) : ℝ) * (c * c)))) *
      (1 / B * (1 / B) * (1 / B))) =
    2 * (2 * E ^ 3 * (2 * B - c ^ 2) / (S * ((1 - c ^ 2) / 4) ^ 2 * (2 * B) ^ 3)) := by
  have e1 : ((1 : ℚ) : ℝ) + ((-1 : ℚ) : ℝ) * (c * c) = 1 - c * c := by push_cast; ring
  have e2 : (1 : ℝ) - c ^ 2 = 1 - c * c := by ring
  have e3 : (2 : ℝ) * B - c ^ 2 = 2 * B - c * c := by ring
  rw [e1, e2, e3]
  push_cast
  field_simp
  ring

end CKLaneA3X


