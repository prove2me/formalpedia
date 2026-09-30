-- Prove2me | Definitions.Def_CK_CKLaneN23_CSemT
-- name    : CK_CKLaneN23_CSemT
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:00:22.643985+00:00
-- url     : https://prove2.me/theorems/5517e41e-af43-4df4-b5be-878f39dd74a8
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CSemT` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CSemT` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CSemT` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CSemT (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CSemT.lean)

import Definitions.Def_CK_CKLaneN23_CStep2

-- ===== source module CKLaneN23.CSemT =====
section

/-!
# CKLaneN23.CSemT — small semantic facts used inside the trivariate corner chain (Lane N23b)
-/

namespace CKLaneN23.CT

open GeneralCK

theorem hent_le_one (z : ℝ) : hent z ≤ 1 := H_le_one _

/-- `ε = 1 - (a+b)/2 ≥ 0` (scaled by 5) when `a, b ≤ 1` — the argument of the eta series. -/
theorem eps_nonneg_chain (a b : ℝ) (ha : a ≤ 1) (hb : b ≤ 1) :
    0 ≤ (((5 : ℚ) : ℚ) : ℝ) * (LPoly.eval (Real.log 2) [(0, (1 : ℚ))] +
      (((-1 : ℚ) : ℚ) : ℝ) * (((((1 : ℚ) / 2) : ℚ) : ℝ) * (a + b))) := by
  rw [LPoly.eval_c]
  push_cast
  nlinarith

end CKLaneN23.CT

end


