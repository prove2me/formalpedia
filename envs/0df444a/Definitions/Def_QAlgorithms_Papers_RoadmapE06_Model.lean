-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapE06_Model
-- name    : QAlgorithms_Papers_RoadmapE06_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:25:39.288994+00:00
-- url     : https://prove2.me/theorems/2397703d-bcef-4411-bf61-73a8e6784566
-- title:
--   Single-shot decoding of good quantum LDPC codes: supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Single-shot decoding of good quantum LDPC codes, arXiv:2306.12470v2, https://arxiv.org/abs/2306.12470v2. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_NoisyTannerDecoding
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.RoadmapE06

open QAlgorithms.NoisyTanner

/-- The actual CSS distance of the Tanner code, as defined on PDF p.5 of
arXiv:2306.12470v2. Here `qtCode0 = C_X` and `qtCode1 = C_Z`.
The infima are in `ℕ∞`: an empty logical-error set has distance infinity. -/
def tannerQuantumDistance {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (C : CodeData G) : ℕ∞ :=
  min (⨅ x ∈ qtCode1 C.CA C.CB, ⨅ (_ : x ∉ codeDual (qtCode0 C.CA C.CB)),
      (hammingNorm x : ℕ∞))
    (⨅ x ∈ qtCode0 C.CA C.CB, ⨅ (_ : x ∉ codeDual (qtCode1 C.CA C.CB)),
      (hammingNorm x : ℕ∞))


end QAlgorithms.Papers.RoadmapE06


