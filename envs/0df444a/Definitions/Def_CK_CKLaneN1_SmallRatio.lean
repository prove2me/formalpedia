-- Prove2me | Definitions.Def_CK_CKLaneN1_SmallRatio
-- name    : CK_CKLaneN1_SmallRatio
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T04:13:34.026582+00:00
-- url     : https://prove2.me/theorems/0e0de544-3bc1-4753-b685-0f7b6e4c9e5a
-- title:
--   Courtade–Kumar proof module `CKLaneN1.SmallRatio` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.SmallRatio` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.SmallRatio` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.SmallRatio (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/SmallRatio.lean)

import Definitions.Def_CK_CKLaneN1_SRShard_C00
import Definitions.Def_CK_CKLaneN1_SRShard_C01
import Definitions.Def_CK_CKLaneN1_SRShard_C02
import Definitions.Def_CK_CKLaneN1_SRShard_C03
import Definitions.Def_CK_CKLaneN1_SRShard_C04
import Definitions.Def_CK_CKLaneN1_SRShard_C05
import Definitions.Def_CK_CKLaneN1_SRShard_T00
import Definitions.Def_CK_CKLaneN1_SRShard_T01
import Definitions.Def_CK_CKLaneN1_SRShard_T02
import Definitions.Def_CK_CKLaneN1_SRShard_T03
import Definitions.Def_CK_CKLaneN1_SRShard_T04
import Definitions.Def_CK_CKLaneN1_SRShard_T05
import Definitions.Def_CK_CKLaneN1_SRShard_T06
import Definitions.Def_CK_CKLaneN1_SRShard_T07
import Definitions.Def_CK_CKLaneN1_SRShard_T08
import Definitions.Def_CK_CKLaneN1_SRShard_T09
import Definitions.Def_CK_CKLaneN1_SRShard_T10
import Definitions.Def_CK_CKLaneN1_SRShard_T11
import Definitions.Def_CK_CKLaneN1_SRShard_T12
import Definitions.Def_CK_CKLaneN1_SRShard_T13
import Definitions.Def_CK_CKLaneN1_SRShard_T14
import Definitions.Def_CK_CKLaneN1_SRShard_T15
import Definitions.Def_CK_CKLaneN1_Chunks

-- ===== source module CKLaneN1.SmallRatio =====
section

/-!
# Lane N1: SMALL_RATIO Thm 1 cover, Thm 4 cover, and the rows they close

* `row_smallRatioT1Cover : SmallRatioT1Cover` — NORMALIZED_COLLAR, all 205 archived leaves.
* `thm4_cover` — CENTRAL_SMALL_RATIO, all 611 archived leaves (572 `normalized` by the kernel check,
  39 `small_ratio` delegated to Thm 1 exactly as archived).
* `row_smallRatioT4Rest : SmallRatioT4Rest`, `row_SR_SmallRatio : SR_SmallRatio`.

`SmallRatioT1Cover` / `SmallRatioT4Rest` are verbatim copies of lane N23's rows
(`N23/src/CKLaneN23/SameSideHalf.lean`); `SR_SmallRatio` is `N1/SUBROWS.lean`.
-/

namespace CKLaneN1

open GeneralCK

/-- Theorem 1 cover root `[10^-6, 11/200] × [0,4]` (NORMALIZED_COLLAR, 205 leaves).
(Verbatim copy of `CKLaneN23.SmallRatioT1Cover`.) -/
def SmallRatioT1Cover : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 1000000 ≤ μ.meanEntropy → μ.meanEntropy ≤ 11 / 200 →
    1 - μ.a - μ.b ≤ μ.meanEntropy → μ.b - μ.a ≤ 4 * μ.meanEntropy →
    PsiActive μ → μ.gap ≤ μ.cost

/-- Thm 4 cover (root `E ∈ [10^-6, 11/200]`) outside the Thm 1 boxes: the 572 `normalized`
leaves (they satisfy `E < q` wherever Thm 1 is not used).
(Verbatim copy of `CKLaneN23.SmallRatioT4Rest`.) -/
def SmallRatioT4Rest : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → 1 / 1000000 ≤ μ.meanEntropy →
    μ.meanEntropy ≤ 11 / 200 → μ.b - μ.a ≤ 4 * μ.meanEntropy →
    μ.meanEntropy < 1 - μ.a - μ.b → PsiActive μ → μ.gap ≤ μ.cost

theorem collarTree_length : collarTree.leaves.length = 205 := by decide +kernel
theorem centralTree_length : centralTree.leaves.length = 611 := by decide +kernel

/-- Every archived NORMALIZED_COLLAR leaf passes the kernel check. -/
theorem collarTree_ok : collarTree.allLeaves leafOKC = true := by
  unfold PT.allLeaves
  apply all_of_chunks (fun q => leafOKC q.1 q.2) 40 6 collarTree.leaves
    (by rw [collarTree_length]; decide)
  intro k hk
  interval_cases k
  · exact SRShard.C00
  · exact SRShard.C01
  · exact SRShard.C02
  · exact SRShard.C03
  · exact SRShard.C04
  · exact SRShard.C05

/-- Every archived CENTRAL_SMALL_RATIO leaf passes the kernel check. -/
theorem centralTree_ok : centralTree.allLeaves leafOK4 = true := by
  unfold PT.allLeaves
  apply all_of_chunks (fun q => leafOK4 q.1 q.2) 40 16 centralTree.leaves
    (by rw [centralTree_length]; decide)
  intro k hk
  interval_cases k
  · exact SRShard.T00
  · exact SRShard.T01
  · exact SRShard.T02
  · exact SRShard.T03
  · exact SRShard.T04
  · exact SRShard.T05
  · exact SRShard.T06
  · exact SRShard.T07
  · exact SRShard.T08
  · exact SRShard.T09
  · exact SRShard.T10
  · exact SRShard.T11
  · exact SRShard.T12
  · exact SRShard.T13
  · exact SRShard.T14
  · exact SRShard.T15

/-- Row 1 (N23): SMALL_RATIO Theorem 1 on its archived cover root. -/
theorem row_smallRatioT1Cover : SmallRatioT1Cover :=
  collar_of_tree collarTree_ok

/-- SMALL_RATIO Theorem 4 on its archived cover root (`E ≥ 10^-6`), all 611 leaves. -/
theorem thm4_cover : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → 1 / 1000000 ≤ μ.meanEntropy → μ.meanEntropy ≤ 11 / 200 →
    μ.b - μ.a ≤ 4 * μ.meanEntropy → PsiActive μ → μ.gap ≤ μ.cost :=
  central_of_tree centralTree_ok row_smallRatioT1Cover

/-- Row 2 (N23): the Thm 4 cover outside the Thm 1 boxes. -/
theorem row_smallRatioT4Rest : SmallRatioT4Rest := by
  intro k μ hab hsum ha _hb hE0 hE1 hd4 _hq hact
  exact thm4_cover k μ hab hsum ha hE0 hE1 hd4 hact

/-- §4 row `d ≥ 1/50, E ≤ 11/200, d ≤ 4E` of the central square (`N1/SUBROWS.lean`). -/
theorem row_SR_SmallRatio : SR_SmallRatio := by
  intro k μ hab hsum ha _hb2 _hb hd hE1 hd4 hact
  have hE0 : 1 / 1000000 ≤ μ.meanEntropy := by linarith
  exact thm4_cover k μ hab hsum ha hE0 hE1 hd4 hact

end CKLaneN1

end


