-- Prove2me | Definitions.Def_HardTilingSimple_DecisionCounting_Problems
-- name    : HardTilingSimple_DecisionCounting_Problems
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-31T00:33:08.437728+00:00
-- url     : https://prove2.me/theorems/bc9434ef-1edc-4193-99f4-bec6d0939a10
-- title:
--   Existence language and exact counting function on bit strings
-- statement:
--   For a bit string b encoding a finite region R, the existence language accepts b exactly when R admits a tiling by the fixed right tromino and square tetromino, and the counting function returns the number of its unordered geometric tilings. Invalid region encodings are rejected and have count zero.
--
--   Both objects are computed solely from the decoded geometric region. They have no SAT data, assumed reduction, correctness certificate or hardness hypothesis. In particular the valid empty-region encoding is accepted with count one, while the empty bit string is invalid and has count zero.
-- source:
--   Moore and Robson, Hard Tiling Problems with Simple Tiles, Discrete & Computational Geometry 26, 573–590 (2001), published DOI https://doi.org/10.1007/s00454-001-0047-6, §2, pp. 574 and 577 (PDF 2 and 5), existence/counting problems and unnumbered completeness conclusion.

import Definitions.Def_HardTilingSimple_DecisionCounting_Tiles
import Definitions.Def_HardTilingSimple_DecisionCounting_RegionCodec

namespace HardTilingSimple.DecisionCounting

/-- Invalid strings are rejected; valid strings ask for a geometric tiling. -/
def tilingLanguage (bs : List Bool) : Prop :=
  ∃ R : Region, decodeRegion bs = some R ∧ (tilings R).Nonempty

/-- Invalid strings have count zero, independently of all SAT encodings. -/
def tilingCountFunction (bs : List Bool) : ℕ :=
  match decodeRegion bs with
  | none => 0
  | some R => tilingCount R

end HardTilingSimple.DecisionCounting


