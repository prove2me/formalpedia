-- Prove2me | Definitions.Def_CK_CKLaneN23_SameSideHalf
-- name    : CK_CKLaneN23_SameSideHalf
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:40:11.194437+00:00
-- url     : https://prove2.me/theorems/6ddfbf71-84ab-4b17-b3f4-b062aefe4579
-- title:
--   Courtade–Kumar proof module `CKLaneN23.SameSideHalf` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.SameSideHalf` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.SameSideHalf` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.SameSideHalf (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/SameSideHalf.lean)

import Definitions.Def_CK_CKLaneN23_OpCorner
import Definitions.Def_CK_GeneralCK_EqualMean
import Definitions.Def_CK_GeneralCK_PsiGeneralLowEntropy
import Definitions.Def_CK_GeneralCK_PsiParentDominance
import Definitions.Def_CK_GeneralCK_PsiLowEntropyBias
import Definitions.Def_CK_GeneralCK_PsiOuterEntropy200

-- ===== source module CKLaneN23.SameSideHalf =====
section

/-!
# Lane N23 — the same-side half-square `SR_SameSideHalf` (CentralSquare sub-row)

`SR_SameSideHalf` and `SR_DiagonalBand` are verbatim copies of the sub-rows in
`~/ck_lanes_20260923/N1/SUBROWS.lean` (`CKLaneN1`); `PsiActive` is the verbatim route copy in
`CKLaneN23.OpCorner`.

Archived proof (`CK_NO_SEPARATION_EXTENSION` §7, last paragraph): for means in
`[1/10,1/2]^2`, Theorem A covers `d ≤ 1/50` and `CK_SMALL_RATIO_EXTENSION` Theorem 3 covers
`d ≥ 1/100`.

* Theorem A (`a,b ∈ [1/10,9/10]`, `d ≤ 1/50`), exhaustive §7 table:
  `E ≥ 11/200` (§6: 325 leaves = 153 endpoint + 140 log-sum + 32 prior-cap) |
  `E ≤ 11/200, d ≤ 4E` (SMALL_RATIO Thm 4: 611 leaves = 572 normalized + 39 owned by Thm 1,
  plus 11 tail comparisons) | `E ≤ 11/200, d ≥ 4E, q ≥ 1/10` (§5, seven fixed comparisons) |
  `… q ≤ 1/10, q ≥ 8E` (Theorem C) | `… q ≤ 8E` (§4).
* Theorem 3 (`a,b ∈ [1/10,1/2]`, `d ≥ 1/100`): 76,547-leaf cover of the root
  `E = 10^-6 + t(C0-10^-6)`; leaves `prior_same_side` (1,599, `d ≥ 1/20` throughout) invoke the
  33,572-leaf FULL_ENTROPY cover; `central_small_ratio` (68) invoke Thm 4; `cap` (962) invoke
  the central cap theorem (`s ≤ 3/40`, CAP_REGION covers); `E ≤ 10^-6` is `SAME_SIDE_TAIL.py`.
* FULL_ENTROPY (`d ≥ 1/20`): 33,572 leaves (423 `cap`) and a four-comparison `E ≤ 10^-6` tail.

Canonical notation: `d = b - a`, `q = 1 - a - b`, `E = meanEntropy`, `s = (H a + H b)/2 - E`.

Discharged here by reuse of compiled F-C theorems (no numerical or regional hypotheses):
Theorem C row, every `E ≤ 10^-6` tail, the reuse-owned parts of §4 and §5. The remaining
obligations are exactly the eight certificate rows of `sameSideHalf_of_certificate_rows`.
-/

namespace CKLaneN23

open GeneralCK

/-! ## Verbatim sub-row statements (`CKLaneN1`, `N1/SUBROWS.lean`) -/

/-- Same-side half-square `[1/10,1/2]^2`, canonical
(CK_NO_SEPARATION_EXTENSION Theorem B, lower half-square). -/
def SR_SameSideHalf : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 1 / 2 → PsiActive μ → μ.gap ≤ μ.cost

/-- §4 row `d ≤ 1/50`: the full-entropy central diagonal band
(CK_NO_SEPARATION_EXTENSION Theorem A), on the opposite central part. -/
def SR_DiagonalBand : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
    μ.b - μ.a ≤ 1 / 50 → PsiActive μ → μ.gap ≤ μ.cost

/-! ## Shared archived components -/

/-- CAP_REGION central cap theorem (`a,b ∈ [1/10,9/10]`, `s ≤ 3/40`), hybrid form.
Covers: same-side cap square (2,108 leaves) and expanded cap rectangle (14,525 leaves, which
reuses the quantitative cap subrectangle, 29,996 leaves). -/
def CentralCap : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → (H μ.a + H μ.b) / 2 - μ.meanEntropy ≤ 3 / 40 →
    PsiActive μ → μ.gap ≤ μ.cost

/-- SMALL_RATIO Theorem 1 (hybrid form): `E ≤ 11/200`, `q ≤ E`, `d ≤ 4E`, any means. -/
def SmallRatioT1 : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    μ.meanEntropy ≤ 11 / 200 → 1 - μ.a - μ.b ≤ μ.meanEntropy →
    μ.b - μ.a ≤ 4 * μ.meanEntropy → PsiActive μ → μ.gap ≤ μ.cost

/-- Theorem 1 cover root `[10^-6, 11/200] × [0,4]` (NORMALIZED_COLLAR, 205 leaves). -/
def SmallRatioT1Cover : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 1000000 ≤ μ.meanEntropy → μ.meanEntropy ≤ 11 / 200 →
    1 - μ.a - μ.b ≤ μ.meanEntropy → μ.b - μ.a ≤ 4 * μ.meanEntropy →
    PsiActive μ → μ.gap ≤ μ.cost

/-- Theorem 1 analytic tail `E ≤ 10^-6` (SMALL_RATIO_TAIL.py). -/
def SmallRatioT1Tail : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    μ.meanEntropy ≤ 1 / 1000000 → 1 - μ.a - μ.b ≤ μ.meanEntropy →
    μ.b - μ.a ≤ 4 * μ.meanEntropy → PsiActive μ → μ.gap ≤ μ.cost

/-- SMALL_RATIO Theorem 4 (central small ratio), hybrid form, canonical. -/
def SmallRatioT4 : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → μ.meanEntropy ≤ 11 / 200 →
    μ.b - μ.a ≤ 4 * μ.meanEntropy → PsiActive μ → μ.gap ≤ μ.cost

/-- Thm 4 cover (root `E ∈ [10^-6, 11/200]`) outside the Thm 1 boxes: the 572 `normalized`
leaves (they satisfy `E < q` wherever Thm 1 is not used). -/
def SmallRatioT4Rest : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → 1 / 1000000 ≤ μ.meanEntropy →
    μ.meanEntropy ≤ 11 / 200 → μ.b - μ.a ≤ 4 * μ.meanEntropy →
    μ.meanEntropy < 1 - μ.a - μ.b → PsiActive μ → μ.gap ≤ μ.cost

/-- Thm 4 analytic small-entropy tail `E ≤ 10^-6` (CENTRAL_SMALL_RATIO_TAIL, 11 comparisons). -/
def SmallRatioT4Tail : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → μ.meanEntropy ≤ 1 / 1000000 →
    μ.b - μ.a ≤ 4 * μ.meanEntropy → PsiActive μ → μ.gap ≤ μ.cost

/-! ## Theorem A (NO_SEPARATION) -/

/-- NO_SEPARATION Theorem A (full-entropy central diagonal band), canonical. -/
def NoSepA : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → μ.b - μ.a ≤ 1 / 50 → PsiActive μ → μ.gap ≤ μ.cost

/-- Thm A, §7 row `E ≥ 11/200`: NO_SEPARATION §6 normalized cover. -/
def NoSepA_Moderate : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → μ.b - μ.a ≤ 1 / 50 →
    11 / 200 ≤ μ.meanEntropy → PsiActive μ → μ.gap ≤ μ.cost

/-- §6 leaves other than prior-cap (153 normalized-endpoint + 140 normalized-log-sum); the 32
prior-cap leaves have `I_+ ≤ 3/40`, hence `s ≤ 3/40`. -/
def NoSepA_ModerateRest : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → μ.b - μ.a ≤ 1 / 50 →
    11 / 200 ≤ μ.meanEntropy → 3 / 40 < (H μ.a + H μ.b) / 2 - μ.meanEntropy →
    PsiActive μ → μ.gap ≤ μ.cost

/-- Thm A, §7 row `E ≤ 11/200, d ≤ 4E`: SMALL_RATIO Theorem 4 (restricted to `d ≤ 1/50`). -/
def NoSepA_SmallRatio : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → μ.b - μ.a ≤ 1 / 50 →
    μ.meanEntropy ≤ 11 / 200 → μ.b - μ.a ≤ 4 * μ.meanEntropy →
    PsiActive μ → μ.gap ≤ μ.cost

/-- Thm A, §7 row `E ≤ 11/200, d ≥ 4E, q ≥ 1/10`: NO_SEPARATION §5 (seven comparisons). -/
def NoSepA_HighBias : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → μ.b - μ.a ≤ 1 / 50 →
    μ.meanEntropy ≤ 11 / 200 → 4 * μ.meanEntropy ≤ μ.b - μ.a →
    1 / 10 ≤ 1 - μ.a - μ.b → PsiActive μ → μ.gap ≤ μ.cost

/-- §5 remainder after reuse: `q > 1/2` (comparisons `k = 5,6,7`) and `E > 10^-6`. -/
def NoSepA_HighBiasRem : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → μ.b - μ.a ≤ 1 / 50 →
    μ.meanEntropy ≤ 11 / 200 → 4 * μ.meanEntropy ≤ μ.b - μ.a →
    1 / 2 < 1 - μ.a - μ.b → 1 / 1000000 < μ.meanEntropy →
    PsiActive μ → μ.gap ≤ μ.cost

/-- Thm A, §7 row `E ≤ 11/200, d ≥ 4E, 0 < q ≤ 1/10, q ≥ 8E`: Theorem C. -/
def NoSepA_ThmC : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → μ.b - μ.a ≤ 1 / 50 →
    μ.meanEntropy ≤ 11 / 200 → 4 * μ.meanEntropy ≤ μ.b - μ.a →
    0 < 1 - μ.a - μ.b → 1 - μ.a - μ.b ≤ 1 / 10 → 8 * μ.meanEntropy ≤ 1 - μ.a - μ.b →
    PsiActive μ → μ.gap ≤ μ.cost

/-- Thm A, §7 row `E ≤ 11/200, d ≥ 4E, q ≤ 8E`: NO_SEPARATION §4 low-entropy strip. -/
def NoSepA_Strip : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → μ.b - μ.a ≤ 1 / 50 →
    μ.meanEntropy ≤ 11 / 200 → 4 * μ.meanEntropy ≤ μ.b - μ.a →
    1 - μ.a - μ.b ≤ 8 * μ.meanEntropy → PsiActive μ → μ.gap ≤ μ.cost

/-- §4 remainder after reuse: `E > 10^-6` and `d < 8E`. -/
def NoSepA_StripRem : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → μ.b - μ.a ≤ 1 / 50 →
    μ.meanEntropy ≤ 11 / 200 → 4 * μ.meanEntropy ≤ μ.b - μ.a →
    1 - μ.a - μ.b ≤ 8 * μ.meanEntropy →
    1 / 1000000 < μ.meanEntropy → μ.b - μ.a < 8 * μ.meanEntropy →
    PsiActive μ → μ.gap ≤ μ.cost

/-! ## Theorem 3 (SMALL_RATIO §6) and FULL_ENTROPY -/

/-- SMALL_RATIO Theorem 3 (completed smaller-separation same-side cover), canonical. -/
def SmallRatioT3 : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 1 / 2 → 1 / 100 ≤ μ.b - μ.a → PsiActive μ → μ.gap ≤ μ.cost

/-- Theorem 3 cover leaves other than `prior_same_side` (`d < 1/20`), root `E ≥ 10^-6`. -/
def SmallRatioT3Near : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 1 / 2 → 1 / 100 ≤ μ.b - μ.a → μ.b - μ.a < 1 / 20 →
    1 / 1000000 ≤ μ.meanEntropy → PsiActive μ → μ.gap ≤ μ.cost

/-- Theorem 3 `d < 1/20` leaves other than `central_small_ratio` (inside `E ≤ 11/200, d ≤ 4E`)
and `cap` (inside `s ≤ 3/40`). -/
def SmallRatioT3NearRest : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 1 / 2 → 1 / 100 ≤ μ.b - μ.a → μ.b - μ.a < 1 / 20 →
    1 / 1000000 ≤ μ.meanEntropy →
    (11 / 200 < μ.meanEntropy ∨ 4 * μ.meanEntropy < μ.b - μ.a) →
    3 / 40 < (H μ.a + H μ.b) / 2 - μ.meanEntropy →
    PsiActive μ → μ.gap ≤ μ.cost

/-- Theorem 3 analytic tail `E ≤ 10^-6` (SAME_SIDE_TAIL.py, 79 comparisons). -/
def SmallRatioT3Tail : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 1 / 2 → 1 / 100 ≤ μ.b - μ.a →
    μ.meanEntropy ≤ 1 / 1000000 → PsiActive μ → μ.gap ≤ μ.cost

/-- FULL_ENTROPY larger same-side theorem: `a,b ∈ [1/10,1/2]`, `d ≥ 1/20`. -/
def FullEntropySS : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 1 / 2 → 1 / 20 ≤ μ.b - μ.a → PsiActive μ → μ.gap ≤ μ.cost

/-- FULL_ENTROPY cover, `E ≥ 10^-6` (33,572 leaves). -/
def FullEntropySSCover : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 1 / 2 → 1 / 20 ≤ μ.b - μ.a →
    1 / 1000000 ≤ μ.meanEntropy → PsiActive μ → μ.gap ≤ μ.cost

/-- FULL_ENTROPY cover leaves other than `cap` (`s_+ ≤ 3/40`) and `outside`. -/
def FullEntropySSCoverRest : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 1 / 2 → 1 / 20 ≤ μ.b - μ.a →
    1 / 1000000 ≤ μ.meanEntropy → 3 / 40 < (H μ.a + H μ.b) / 2 - μ.meanEntropy →
    PsiActive μ → μ.gap ≤ μ.cost

/-- FULL_ENTROPY analytic tail `E ≤ 10^-6` (LOW_ENTROPY_CHECK.py, four comparisons). -/
def FullEntropySSTail : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 1 / 2 → 1 / 20 ≤ μ.b - μ.a →
    μ.meanEntropy ≤ 1 / 1000000 → PsiActive μ → μ.gap ≤ μ.cost

/-! ## Elementary facts -/

theorem meanEntropy_pos' {k : ℕ} (μ : InteriorLaw (Fin k)) : 0 < μ.meanEntropy := by
  unfold InteriorLaw.meanEntropy
  linarith [μ.e_pos, μ.f_pos]

theorem midpoint_eq_bias {k : ℕ} (μ : InteriorLaw (Fin k)) :
    (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
  unfold InteriorLaw.midpoint
  ring

/-- Global low-entropy tail (compiled `PsiGeneralLowEntropy.law_gap_le_cost`), with the
equal-mean case by `equal_mean_hybrid`. -/
theorem lowEntropy_tail {k : ℕ} (μ : InteriorLaw (Fin k)) (hab : μ.a ≤ μ.b)
    (hsum : μ.a + μ.b ≤ 1) (hmean : 1 / 16 < μ.a + μ.b)
    (hE : μ.meanEntropy ≤ 1 / 1000000) (hact : PsiActive μ) : μ.gap ≤ μ.cost := by
  rcases hab.eq_or_lt with heq | hlt
  · exact μ.equal_mean_hybrid heq
  · have hact' : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy := hact
    exact PsiGeneralLowEntropy.law_gap_le_cost μ hlt hsum hmean hE hact'.le

/-! ## Rows discharged by reuse (unconditional) -/

/-- Theorem C row: vacuous for strictly psi-active parents
(`PsiParentDominance.activePsi_entropy_gt_eighth`). -/
theorem row_noSepA_thmC : NoSepA_ThmC := by
  intro k μ _hab _hsum _ha _hb _hd _hEu _hd4 hq0 hq hq8 hact
  have hact' : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy := hact
  have hq2 : 1 - 2 * μ.midpoint = 1 - μ.a - μ.b := by
    unfold InteriorLaw.midpoint
    ring
  have h := PsiParentDominance.activePsi_entropy_gt_eighth (meanEntropy_pos' μ)
    (by rw [hq2]; exact hq0) (by rw [hq2]; exact hq) hact'
  rw [hq2] at h
  exfalso
  linarith

theorem row_smallRatioT1Tail : SmallRatioT1Tail := by
  intro k μ hab hsum hE hq _hd4 hact
  exact lowEntropy_tail μ hab hsum (by linarith) hE hact

theorem row_smallRatioT4Tail : SmallRatioT4Tail := by
  intro k μ hab hsum ha _hb hE _hd4 hact
  exact lowEntropy_tail μ hab hsum (by linarith) hE hact

theorem row_smallRatioT3Tail : SmallRatioT3Tail := by
  intro k μ hab hsum ha _hb _hd hE hact
  exact lowEntropy_tail μ hab hsum (by linarith) hE hact

theorem row_fullEntropySSTail : FullEntropySSTail := by
  intro k μ hab hsum ha _hb _hd hE hact
  exact lowEntropy_tail μ hab hsum (by linarith) hE hact

/-! ## Reuse reductions to the certificate remainders -/

/-- §5 is vacuous for `q ≤ 1/2` (`PsiOuterEntropy200.active_bias_lt_eight_entropy`, since
`E ≤ d/4 ≤ 1/200`) and for `E ≤ 10^-6` (`PsiLowEntropyBias.active_bias_lt_tenth`). -/
theorem noSepA_highBias_of_rem (h : NoSepA_HighBiasRem) : NoSepA_HighBias := by
  intro k μ hab hsum ha hb hd hEu hd4 hq hact
  have hE := meanEntropy_pos' μ
  have hact' : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy := hact
  have hmid := midpoint_eq_bias μ
  by_cases hq2 : 1 - μ.a - μ.b ≤ 1 / 2
  · have h8 := PsiOuterEntropy200.active_bias_lt_eight_entropy (q := 1 - μ.a - μ.b)
      (E := μ.meanEntropy) hq2 hE (by linarith) (by rw [hmid]; exact hact'.le)
    exfalso
    linarith
  · by_cases hEs : μ.meanEntropy ≤ 1 / 1000000
    · have h10 := PsiLowEntropyBias.active_bias_lt_tenth (q := 1 - μ.a - μ.b)
        (E := μ.meanEntropy) (by linarith) hE hEs (by rw [hmid]; exact hact'.le)
      exfalso
      linarith
    · exact h k μ hab hsum ha hb hd hEu hd4 (lt_of_not_ge hq2) (lt_of_not_ge hEs) hact

/-- §4 on `E ≤ 10^-6` (`PsiGeneralLowEntropy`) and on `d ≥ 8E`
(`PsiEndpointBellman.law_gap_le_cost`, since `E ≤ 1/400` and `q ≤ 8E ≤ 1/50`). -/
theorem noSepA_strip_of_rem (h : NoSepA_StripRem) : NoSepA_Strip := by
  intro k μ hab hsum ha hb hd hEu hd4 hq8 hact
  by_cases hEs : μ.meanEntropy ≤ 1 / 1000000
  · exact lowEntropy_tail μ hab hsum (by linarith) hEs hact
  · by_cases h8 : 8 * μ.meanEntropy ≤ μ.b - μ.a
    · have hact' : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy := hact
      exact PsiEndpointBellman.law_gap_le_cost μ hsum (by linarith) h8 (by linarith) hact'.le
    · exact h k μ hab hsum ha hb hd hEu hd4 hq8 (lt_of_not_ge hEs) (lt_of_not_ge h8) hact

/-! ## Assembly adapters (archived exhaustive tables) -/

theorem smallRatioT1_of_parts (hc : SmallRatioT1Cover) (ht : SmallRatioT1Tail) :
    SmallRatioT1 := by
  intro k μ hab hsum hEu hq hd4 hact
  by_cases hEs : μ.meanEntropy ≤ 1 / 1000000
  · exact ht k μ hab hsum hEs hq hd4 hact
  · exact hc k μ hab hsum (lt_of_not_ge hEs).le hEu hq hd4 hact

/-- Thm 4: Thm 1 owns the boxes with `q ≤ E`; the normalized leaves own `E < q`; the
tail owns `E ≤ 10^-6`. -/
theorem smallRatioT4_of_parts (h1 : SmallRatioT1) (hr : SmallRatioT4Rest)
    (ht : SmallRatioT4Tail) : SmallRatioT4 := by
  intro k μ hab hsum ha hb hEu hd4 hact
  by_cases hEs : μ.meanEntropy ≤ 1 / 1000000
  · exact ht k μ hab hsum ha hb hEs hd4 hact
  · by_cases hq : 1 - μ.a - μ.b ≤ μ.meanEntropy
    · exact h1 k μ hab hsum hEu hq hd4 hact
    · exact hr k μ hab hsum ha hb (lt_of_not_ge hEs).le hEu hd4 (lt_of_not_ge hq) hact

theorem noSepA_moderate_of_parts (hcap : CentralCap) (hr : NoSepA_ModerateRest) :
    NoSepA_Moderate := by
  intro k μ hab hsum ha hb hd hE hact
  by_cases hs : (H μ.a + H μ.b) / 2 - μ.meanEntropy ≤ 3 / 40
  · exact hcap k μ hab hsum ha hb hs hact
  · exact hr k μ hab hsum ha hb hd hE (lt_of_not_ge hs) hact

theorem noSepA_smallRatio_of_T4 (h4 : SmallRatioT4) : NoSepA_SmallRatio := by
  intro k μ hab hsum ha hb _hd hEu hd4 hact
  exact h4 k μ hab hsum ha hb hEu hd4 hact

/-- NO_SEPARATION §7: the five rows are exhaustive (closed faces overlap). -/
theorem noSepA_of_rows (h1 : NoSepA_Moderate) (h2 : NoSepA_SmallRatio)
    (h3 : NoSepA_HighBias) (h4 : NoSepA_ThmC) (h5 : NoSepA_Strip) : NoSepA := by
  intro k μ hab hsum ha hb hd hact
  have hE := meanEntropy_pos' μ
  by_cases hE1 : 11 / 200 ≤ μ.meanEntropy
  · exact h1 k μ hab hsum ha hb hd hE1 hact
  have hEu : μ.meanEntropy ≤ 11 / 200 := (lt_of_not_ge hE1).le
  by_cases hsr : μ.b - μ.a ≤ 4 * μ.meanEntropy
  · exact h2 k μ hab hsum ha hb hd hEu hsr hact
  have hd4 : 4 * μ.meanEntropy ≤ μ.b - μ.a := (lt_of_not_ge hsr).le
  by_cases hq1 : 1 / 10 ≤ 1 - μ.a - μ.b
  · exact h3 k μ hab hsum ha hb hd hEu hd4 hq1 hact
  have hq10 : 1 - μ.a - μ.b ≤ 1 / 10 := (lt_of_not_ge hq1).le
  by_cases hq8 : 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy
  · exact h5 k μ hab hsum ha hb hd hEu hd4 hq8 hact
  have h8q : 8 * μ.meanEntropy < 1 - μ.a - μ.b := lt_of_not_ge hq8
  exact h4 k μ hab hsum ha hb hd hEu hd4 (by linarith) hq10 h8q.le hact

theorem fullEntropySSCover_of_parts (hcap : CentralCap) (hr : FullEntropySSCoverRest) :
    FullEntropySSCover := by
  intro k μ hab hsum ha hb hd hEl hact
  by_cases hs : (H μ.a + H μ.b) / 2 - μ.meanEntropy ≤ 3 / 40
  · exact hcap k μ hab hsum ha (by linarith) hs hact
  · exact hr k μ hab hsum ha hb hd hEl (lt_of_not_ge hs) hact

theorem fullEntropySS_of_parts (hc : FullEntropySSCover) (ht : FullEntropySSTail) :
    FullEntropySS := by
  intro k μ hab hsum ha hb hd hact
  by_cases hEs : μ.meanEntropy ≤ 1 / 1000000
  · exact ht k μ hab hsum ha hb hd hEs hact
  · exact hc k μ hab hsum ha hb hd (lt_of_not_ge hEs).le hact

/-- Theorem 3 `d < 1/20` leaves: `central_small_ratio` (Thm 4), `cap` (central cap), rest. -/
theorem smallRatioT3Near_of_parts (h4 : SmallRatioT4) (hcap : CentralCap)
    (hr : SmallRatioT3NearRest) : SmallRatioT3Near := by
  intro k μ hab hsum ha hb hd hd20 hEl hact
  by_cases hsr : μ.meanEntropy ≤ 11 / 200 ∧ μ.b - μ.a ≤ 4 * μ.meanEntropy
  · exact h4 k μ hab hsum ha (by linarith) hsr.1 hsr.2 hact
  · by_cases hs : (H μ.a + H μ.b) / 2 - μ.meanEntropy ≤ 3 / 40
    · exact hcap k μ hab hsum ha (by linarith) hs hact
    · have hor : 11 / 200 < μ.meanEntropy ∨ 4 * μ.meanEntropy < μ.b - μ.a := by
        by_cases hE : μ.meanEntropy ≤ 11 / 200
        · exact Or.inr (lt_of_not_ge fun h => hsr ⟨hE, h⟩)
        · exact Or.inl (lt_of_not_ge hE)
      exact hr k μ hab hsum ha hb hd hd20 hEl hor (lt_of_not_ge hs) hact

/-- SMALL_RATIO §6: `prior_same_side` leaves (`d ≥ 1/20`) invoke FULL_ENTROPY; the other
leaves cover `d < 1/20`; `SAME_SIDE_TAIL` covers `E ≤ 10^-6`. -/
theorem smallRatioT3_of_parts (hn : SmallRatioT3Near) (hf : FullEntropySS)
    (ht : SmallRatioT3Tail) : SmallRatioT3 := by
  intro k μ hab hsum ha hb hd hact
  by_cases hEs : μ.meanEntropy ≤ 1 / 1000000
  · exact ht k μ hab hsum ha hb hd hEs hact
  · by_cases h20 : μ.b - μ.a < 1 / 20
    · exact hn k μ hab hsum ha hb hd h20 (lt_of_not_ge hEs).le hact
    · exact hf k μ hab hsum ha hb (le_of_not_gt h20) hact

/-- NO_SEPARATION §7, last paragraph: Theorem A (`d ≤ 1/50`) and Theorem 3 (`d ≥ 1/100`)
cover the lower half-square. -/
theorem sameSideHalf_of_noSepA_smallRatioT3 (hA : NoSepA) (h3 : SmallRatioT3) :
    SR_SameSideHalf := by
  intro k μ hab hsum ha hb hact
  by_cases hd : μ.b - μ.a ≤ 1 / 50
  · exact hA k μ hab hsum ha (by linarith) hd hact
  · exact h3 k μ hab hsum ha hb (by linarith [lt_of_not_ge hd]) hact

/-- Theorem A also owns the opposite central band `SR_DiagonalBand`. -/
theorem diagonalBand_of_noSepA (hA : NoSepA) : SR_DiagonalBand := by
  intro k μ hab hsum ha _hb hb9 hd hact
  exact hA k μ hab hsum ha hb9 hd hact

/-- Theorem A from its certificate rows (all reuse-closable pieces discharged). -/
theorem noSepA_of_certificate_rows (hT1 : SmallRatioT1Cover) (hT4 : SmallRatioT4Rest)
    (hcap : CentralCap) (hMod : NoSepA_ModerateRest) (hHB : NoSepA_HighBiasRem)
    (hStrip : NoSepA_StripRem) : NoSepA :=
  noSepA_of_rows (noSepA_moderate_of_parts hcap hMod)
    (noSepA_smallRatio_of_T4
      (smallRatioT4_of_parts (smallRatioT1_of_parts hT1 row_smallRatioT1Tail) hT4
        row_smallRatioT4Tail))
    (noSepA_highBias_of_rem hHB) row_noSepA_thmC (noSepA_strip_of_rem hStrip)

/-- Conditional (NOT a closure): `SR_SameSideHalf` from exactly the eight archived
certificate rows that reuse does not discharge. -/
theorem sameSideHalf_of_certificate_rows (hT1 : SmallRatioT1Cover)
    (hT4 : SmallRatioT4Rest) (hcap : CentralCap) (hMod : NoSepA_ModerateRest)
    (hHB : NoSepA_HighBiasRem) (hStrip : NoSepA_StripRem)
    (hNear : SmallRatioT3NearRest) (hFE : FullEntropySSCoverRest) : SR_SameSideHalf :=
  sameSideHalf_of_noSepA_smallRatioT3
    (noSepA_of_certificate_rows hT1 hT4 hcap hMod hHB hStrip)
    (smallRatioT3_of_parts
      (smallRatioT3Near_of_parts
        (smallRatioT4_of_parts (smallRatioT1_of_parts hT1 row_smallRatioT1Tail) hT4
          row_smallRatioT4Tail)
        hcap hNear)
      (fullEntropySS_of_parts (fullEntropySSCover_of_parts hcap hFE) row_fullEntropySSTail)
      row_smallRatioT3Tail)

/-- Conditional (NOT a closure): `SR_DiagonalBand` from the Theorem A certificate rows. -/
theorem diagonalBand_of_certificate_rows (hT1 : SmallRatioT1Cover)
    (hT4 : SmallRatioT4Rest) (hcap : CentralCap) (hMod : NoSepA_ModerateRest)
    (hHB : NoSepA_HighBiasRem) (hStrip : NoSepA_StripRem) : SR_DiagonalBand :=
  diagonalBand_of_noSepA (noSepA_of_certificate_rows hT1 hT4 hcap hMod hHB hStrip)

end CKLaneN23

end


