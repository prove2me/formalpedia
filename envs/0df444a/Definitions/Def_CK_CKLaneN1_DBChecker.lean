-- Prove2me | Definitions.Def_CK_CKLaneN1_DBChecker
-- name    : CK_CKLaneN1_DBChecker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:43:13.155989+00:00
-- url     : https://prove2.me/theorems/072f95a0-8c02-4317-b3d9-8f57f1038df1
-- title:
--   Courtade–Kumar proof module `CKLaneN1.DBChecker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.DBChecker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.DBChecker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.DBChecker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/DBChecker.lean)

import Definitions.Def_CK_CKLaneN1_SRChecker
import Definitions.Def_CK_CKLaneN1_SecondDiff
import Definitions.Def_CK_CKLaneE_SlopeBounds
import Definitions.Def_CK_CKLaneM07_KappaLogSum
import Definitions.Def_CK_GeneralCK_PureGapCapZeroReduction

-- ===== source module CKLaneN1.DBChecker =====
section

/-!
# Lane N1: Boolean kernel for NO_SEP §6 (DIAGONAL_BAND, `E ≥ 11/200`, `d ≤ 1/50`)

Archive: `CK_NO_SEPARATION_EXTENSION.zip` (sha256 e9cd4c2e…23cc), `DIAGONAL_BAND.py` `bound`,
root `(q, t) ∈ [0,4/5] × [0,1]`, `E = 11/200 + t (H((1−q)/2) − 11/200)`, `I = (1−t)(H((1−q)/2) − 11/200)`.
Owners:
* `endpoint_normalized`: `F(D,E⁺)/D² − K p⁺ ≥ 0`;
* `logsum_normalized`: `β* s* − K (p⁺ − 4) ≥ 0`;
* `prior_cap`: `I⁺ ≤ 3/40`, which is vacuous in the row `NoSepA_ModerateRest` (`s > 3/40`).

Here `K = min(K₁, K₂)`, with `K₁ = 1/(2L(1−r*²))` and `K₂` the second-difference bound (15)
(`CKLaneN1.SecondDiff`). `p⁺` bounds `P'(I⁺)` via a slope anchor (`CKLaneE.FP.anchorOk`).
The log-sum floor uses the `κ`-enhanced bound `CKLaneM07.kappa_cost_lower_bound`.
-/

namespace CKLaneN1

open GeneralCK GeneralCK.Scalar CKLaneE.FP Set

/-- Maximum mean difference of the band, `D = 1/50`. -/
def DD : ℚ := 1 / 50
/-- Entropy floor of §6, `E₀ = 11/200`. -/
def EM : ℚ := 11 / 200

/-- §6 root `(q, t) ∈ [0, 4/5] × [0, 1]` (degenerate third axis). -/
def dbRoot : B3 := ⟨0, 4 / 5, 0, 1, 0, 0⟩

/-- Law membership in a §6 box (`q = 1−a−b ∈ [a0,a1]`, `E` between the `t`-levels `b0`, `b1`). -/
def InDB (B : B3) {k : ℕ} (μ : InteriorLaw (Fin k)) : Prop :=
  (B.a0 : ℝ) ≤ 1 - μ.a - μ.b ∧ 1 - μ.a - μ.b ≤ (B.a1 : ℝ) ∧
    (EM : ℝ) + (B.b0 : ℝ) * (H ((μ.a + μ.b) / 2) - EM) ≤ μ.meanEntropy ∧
    μ.meanEntropy ≤ (EM : ℝ) + (B.b1 : ℝ) * (H ((μ.a + μ.b) / 2) - EM)

/-- Leaf payload of the §6 tree. -/
inductive DBLeaf where
  | endpoint (vp vc : ℚ)
  | logsum (vp kap : ℚ)
  | cap
  deriving Repr, DecidableEq

/-- Box quantities. -/
def dbHpU (B : B3) : ℚ := Hhi ((1 - B.a0) / 2)
def dbHpL (B : B3) : ℚ := Hlo ((1 - B.a1) / 2)
def dbEup (B : B3) : ℚ := EM + B.b1 * (dbHpU B - EM)
def dbIup (B : B3) : ℚ := (1 - B.b0) * (dbHpU B - EM)
def dbIlo (B : B3) : ℚ := (1 - B.b1) * (dbHpL B - EM)
def dbRmax (B : B3) : ℚ := min (B.a1 + DD) (4 / 5)
def dbK2 (B : B3) : ℚ :=
  (Cup (B.a1 + DD) + Cup (|B.a1 - DD|) - 2 * Clo B.a1) / (2 * DD ^ 2)
def dbK (B : B3) : ℚ := min (AupOf (dbRmax B)) (dbK2 B)

/-- Common box sanity and enclosure validity. -/
def dbBase (B : B3) : Bool :=
  decide (0 ≤ B.a0 ∧ B.a0 ≤ B.a1 ∧ B.a1 + DD < 1 ∧ 0 ≤ B.b0 ∧ B.b0 ≤ B.b1 ∧ B.b1 ≤ 1) &&
  ptOk ((1 - B.a0) / 2) && ptOk ((1 - B.a1) / 2) &&
  ptOk ((1 - (B.a1 + DD)) / 2) && ptOk ((1 - |B.a1 - DD|) / 2) &&
  decide (0 ≤ dbHpU B - EM)

/-- Kernel check of one §6 leaf. -/
def dbLeafOK (p : List ℕ) : DBLeaf → Bool
  | .cap =>
      let B := dbRoot.ofPath p
      dbBase B && decide (dbIup B ≤ 3 / 40)
  | .endpoint vp vc =>
      let B := dbRoot.ofPath p
      dbBase B && anchorOk vp (dbIup B) && decide (0 ≤ dbIup B) &&
      ptOk vc && decide (vc ≤ 1 / 2 ∧ dbEup B * (1 - 2 * vc) ≤ DD * Hlo vc ∧ 0 ≤ lamLo vc ∧
        0 ≤ P1up vp ∧ dbK B * P1up vp ≤ JloOf vc / DD)
  | .logsum vp kap =>
      let B := dbRoot.ofPath p
      let us := (1 - dbRmax B) / 2
      dbBase B && anchorOk vp (dbIup B) && decide (0 ≤ dbIup B) && ptOk us &&
      decide (0 ≤ kap ∧ kap ≤ 2 ∧ kap * (-(l1Lo us)) ≤ us / (1 - us) ∧ 4 ≤ P1up vp ∧
        kap / (2 * (((1 + DD) ^ 2 - B.a0 ^ 2) / 4)) * max 0 (dbIlo B - dbK B * DD ^ 2) -
          dbK B * (P1up vp - 4) ≥ 0)

/-! ## Analytic helpers -/

/-- `κ` transfer: if `κ(−log(1−u)) ≤ u/(1−u)` and `u ≤ a < 1`, the same holds at `a`
(convexity of `exp`: `(eˣ−1)/x` is increasing). -/
theorem kappa_transfer {κ u a : ℝ} (hu : 0 < u) (hua : u ≤ a) (ha : a < 1)
    (h : κ * (-Real.log (1 - u)) ≤ u / (1 - u)) : κ * (-Real.log (1 - a)) ≤ a / (1 - a) := by
  set x := -Real.log (1 - u) with hx
  set y := -Real.log (1 - a) with hy
  have hu1 : 0 < 1 - u := by linarith
  have ha1 : 0 < 1 - a := by linarith
  have hx0 : 0 < x := by
    rw [hx, neg_pos]
    exact Real.log_neg hu1 (by linarith)
  have hxy : x ≤ y := by
    rw [hx, hy, neg_le_neg_iff]
    exact Real.log_le_log ha1 (by linarith)
  have hex : Real.exp x = 1 / (1 - u) := by
    rw [hx, Real.exp_neg, Real.exp_log hu1, one_div]
  have hey : Real.exp y = 1 / (1 - a) := by
    rw [hy, Real.exp_neg, Real.exp_log ha1, one_div]
  have hyx : u / (1 - u) = Real.exp x - 1 := by rw [hex]; field_simp; ring
  have hya : a / (1 - a) = Real.exp y - 1 := by rw [hey]; field_simp; ring
  rw [hyx] at h
  rw [hya]
  have hy0 : 0 < y := hx0.trans_le hxy
  -- convexity: exp x ≤ (1 - x/y) * exp 0 + (x/y) * exp y
  have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ y)
    (show (0 : ℝ) ≤ 1 - x / y by rw [sub_nonneg, div_le_one hy0]; exact hxy)
    (show (0 : ℝ) ≤ x / y by positivity) (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
  have e : x / y * y = x := by field_simp
  rw [e] at hc
  -- κ x ≤ exp x - 1 ≤ (x/y)(exp y - 1)
  have h2 : κ * x ≤ x / y * (Real.exp y - 1) := by nlinarith
  have h3 : κ * x * y ≤ x * (Real.exp y - 1) := by
    have := mul_le_mul_of_nonneg_right h2 hy0.le
    rw [show x / y * (Real.exp y - 1) * y = x * (Real.exp y - 1) by field_simp] at this
    linarith
  have h4 : x * (κ * y) ≤ x * (Real.exp y - 1) := by linarith
  exact le_of_mul_le_mul_left h4 hx0

/-- `Δ ≤ K₂ d²` from the second-difference monotonicity. -/
theorem drop_le_K2 {q d q₁ D : ℝ} (hq : 0 ≤ q) (hqq : q ≤ q₁) (hq₁ : q₁ + D < 1)
    (hd : 0 < d) (hdD : d ≤ D) :
    secondDiff q d / 2 ≤ secondDiff q₁ D / (2 * D ^ 2) * d ^ 2 := by
  have hD : 0 < D := hd.trans_le hdD
  have h1 := secondDiff_div_sq_le (q := q) (D := D) (d := d) (by linarith) (by linarith) hd hdD
  have h2 := secondDiff_mono_q hq hqq hq₁ hD.le
  have hD2 : 0 < D ^ 2 := by positivity
  have h3 : secondDiff q d ≤ d ^ 2 * secondDiff q D / D ^ 2 := by
    rw [le_div_iff₀ hD2]; linarith
  have h4 : d ^ 2 * secondDiff q D / D ^ 2 ≤ d ^ 2 * secondDiff q₁ D / D ^ 2 := by
    apply div_le_div_of_nonneg_right _ hD2.le
    exact mul_le_mul_of_nonneg_left h2 (sq_nonneg d)
  have : secondDiff q₁ D / (2 * D ^ 2) * d ^ 2 = d ^ 2 * secondDiff q₁ D / D ^ 2 / 2 := by
    field_simp
  rw [this]
  linarith

/-- `C(|r|) = C(r)`. -/
theorem Cf_abs (r : ℝ) : Cf |r| = Cf r := by
  rcases le_total 0 r with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, Cf_neg]

end CKLaneN1

end


