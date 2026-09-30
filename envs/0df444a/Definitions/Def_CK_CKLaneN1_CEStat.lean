-- Prove2me | Definitions.Def_CK_CKLaneN1_CEStat
-- name    : CK_CKLaneN1_CEStat
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:38:53.299986+00:00
-- url     : https://prove2.me/theorems/29bb2cbc-404c-48bb-83ad-85bf6675bcbd
-- title:
--   Courtade–Kumar proof module `CKLaneN1.CEStat` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.CEStat` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.CEStat` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.CEStat (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/CEStat.lean)

import Definitions.Def_CK_GeneralCK_PureGapCapAnalytic
import Definitions.Def_CK_GeneralCK_SmallMeanPhiRetainedCutoff

-- ===== source module CKLaneN1.CEStat =====
section

set_option autoImplicit false

/-!
# Lane N1: CE-stat owner partition for `capFibers.leftStationary`

Manuscript (integrated review, `/tmp/ckgc/txt/ms.txt`): Lemma 6.2 routes every interior stationary
point of the Case-E cap fiber (`0 < a < b < c < 1/2`, left mean on its entropy cap `e = H(a)`,
`b = ι(f)`) to CE-stat (Theorem 3.18(h)); App. S.3 gives CE-stat's exact owner partition in the
verifier coordinates `t_C` and `A`:

| exact domain                                  | owner                                          |
|-----------------------------------------------|------------------------------------------------|
| `0 < t_C ≤ 1/80000`, `A ≤ 21/200`             | retained-domain exclusion (SB-1 outside)       |
| `0 < t_C ≤ 1/100`, `A > 21/200`               | capital exclusion theorem                      |
| `1/80000 ≤ t_C ≤ 1/100`, `0 ≤ A ≤ 1/20`       | transverse-curvature pure-gap owner            |
| `1/80000 ≤ t_C ≤ 1/100`, `1/20 ≤ A ≤ 21/200`  | corrected A3 exact leaf union                  |
| `1/100 ≤ t_C < 1/2`, `1/2 < λ < 1`            | high-`t_C` condition-E exclusion               |

Chart coordinates of a Case-E stationary point, in the Lean corpus normalization
(`e8Theta x = Θ(x)`, contact `v` of `(z, h)` solving `z H(v) = h (1 - 2v)`):
* `A = (c - a)/(e + f)` (the verifier's `A = 1/L(t_A)`, `t_A = radialContact (c - a) ((e+f)/2)`);
* `t_C = radialContact (1 - 2c) f` (the verifier's `t_C = L⁻¹(2H(b)/(1-2c))`);
* `λ = f/(e + f)` (the verifier's `λ = (B - A)/(2C)`); `1/2 < λ < 1` is automatic from `0 < e < f`.

This module states the five owners as Lean propositions over the physical stationary point and
proves the reduction `leftStationary ← owners`. It is CONDITIONAL on the five owners.
-/

namespace CKLaneN1.CEStat

open GeneralCK GeneralCK.SmallMeanPhiCutoff

/-- The exact field type `leftStationary` of
`GeneralCK.CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff`. -/
def LeftStationaryField : Prop :=
  ∀ e f c : ℝ, 0 < e → e < f → f ≤ 1 →
    capFiberLower retainedCutoff f (entropyInverse e) < c → c < 1 / 2 →
    deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
    0 ≤ canonicalPureGap (entropyInverse e) c e f

/-- `LeftStationaryField` is definitionally the structure field. -/
theorem field_of_structure (o : CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff) :
    LeftStationaryField := o.leftStationary

/-- Interior stationary point of the Case-E `c`-fiber, cutoff-free:
`a = ι(e) < b = ι(f) < c < 1/2` and `∂_c G(a, c, e, f) = 0`. -/
def PointFree (e f c : ℝ) : Prop :=
  0 < e ∧ e < f ∧ f ≤ 1 ∧ entropyInverse f < c ∧ c < 1 / 2 ∧
    deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0

/-- Retained interior stationary Case-E point (`a + c > S`). -/
def Point (e f c : ℝ) : Prop :=
  PointFree e f c ∧ retainedCutoff < entropyInverse e + c

/-- Verifier coordinate `A = (c - a)/E`, `E = e + f`. -/
noncomputable def chartA (e f c : ℝ) : ℝ := (c - entropyInverse e) / (e + f)

/-- Verifier coordinate `t_C`: the contact point of the right radial term `F(1 - 2c, f)`. -/
noncomputable def chartTC (f c : ℝ) : ℝ := radialContact (1 - 2 * c) f

/-- Verifier coordinate `λ = H(b)/E`. -/
noncomputable def chartLambda (e f : ℝ) : ℝ := f / (e + f)

/-! ## The five S.3 owners -/

/-- S.3 row 1 (`0 < t_C ≤ 1/80000`, `A ≤ 21/200`): the stationary point lies outside the retained
domain (`a + c < S`), where SB-1 owns the target. -/
def RetainedDomainExclusion : Prop :=
  ∀ e f c : ℝ, PointFree e f c → chartTC f c ≤ 1 / 80000 → chartA e f c ≤ 21 / 200 →
    entropyInverse e + c < retainedCutoff

/-- S.3 row 2 (`0 < t_C ≤ 1/100`, `A > 21/200`): capital exclusion (no retained stationary point). -/
def CapitalExclusion : Prop :=
  ∀ e f c : ℝ, Point e f c → chartTC f c ≤ 1 / 100 → 21 / 200 < chartA e f c → False

/-- S.3 row 3 (`1/80000 ≤ t_C ≤ 1/100`, `0 ≤ A ≤ 1/20`): transverse-curvature pure-gap owner. -/
def TransverseCurvatureOwner : Prop :=
  ∀ e f c : ℝ, Point e f c → 1 / 80000 ≤ chartTC f c → chartTC f c ≤ 1 / 100 →
    chartA e f c ≤ 1 / 20 → 0 ≤ canonicalPureGap (entropyInverse e) c e f

/-- S.3 row 4 (`1/80000 ≤ t_C ≤ 1/100`, `1/20 ≤ A ≤ 21/200`): corrected A3 exact leaf union. -/
def A3LeafUnion : Prop :=
  ∀ e f c : ℝ, Point e f c → 1 / 80000 ≤ chartTC f c → chartTC f c ≤ 1 / 100 →
    1 / 20 ≤ chartA e f c → chartA e f c ≤ 21 / 200 →
    0 ≤ canonicalPureGap (entropyInverse e) c e f

/-- S.3 row 5 (`1/100 ≤ t_C < 1/2`, `1/2 < λ < 1`): high-`t_C` condition-E exclusion. -/
def HighTCExclusion : Prop :=
  ∀ e f c : ℝ, Point e f c → 1 / 100 ≤ chartTC f c → False

/-- The five CE-stat owners of App. S.3. -/
structure Owners : Prop where
  retained : RetainedDomainExclusion
  capital : CapitalExclusion
  transverse : TransverseCurvatureOwner
  a3 : A3LeafUnion
  highTC : HighTCExclusion

/-! ## Chart facts -/

/-- The hypotheses of the field give a retained stationary Case-E point. -/
theorem point_of_field {e f c : ℝ} (he : 0 < e) (hef : e < f) (hf : f ≤ 1)
    (hlow : capFiberLower retainedCutoff f (entropyInverse e) < c) (hc : c < 1 / 2)
    (hs : deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0) : Point e f c := by
  unfold capFiberLower at hlow
  have hb : entropyInverse f < c := lt_of_le_of_lt (le_max_left _ _) hlow
  have hS : retainedCutoff - entropyInverse e < c := lt_of_le_of_lt (le_max_right _ _) hlow
  exact ⟨⟨he, hef, hf, hb, hc, hs⟩, by linarith⟩

/-- `b < t_C < c` at every Case-E point (so `t_C ∈ (0, 1/2)` is the verifier's chart value). -/
theorem chart_order {e f c : ℝ} (hp : PointFree e f c) :
    entropyInverse f < chartTC f c ∧ chartTC f c < c := by
  obtain ⟨he, hef, hf, hbc, hc, -⟩ := hp
  have hf0 : 0 < f := he.trans hef
  obtain ⟨hb0, hb2, hHb⟩ := entropyInverse_spec hf0.le hf
  have hz : 0 < 1 - 2 * c := by linarith
  have hc0 : 0 ≤ c := hb0.trans hbc.le
  constructor
  · by_contra hn
    have hle : chartTC f c ≤ entropyInverse f := le_of_not_gt hn
    have h := (radialContact_le_iff hz hf0 hb0 hb2).mp hle
    rw [hHb] at h
    have : f * (1 - 2 * entropyInverse f) ≤ f * (1 - 2 * c) := by linarith
    have h2 := le_of_mul_le_mul_left this hf0
    linarith
  · by_contra hn
    have hle : c ≤ chartTC f c := le_of_not_gt hn
    have h := (le_radialContact_iff hz hf0 hc0 hc.le).mp hle
    have hH : f < H c := by
      rw [← hHb]
      exact H_strictMonoOn ⟨hb0, hb2⟩ ⟨hc0, hc.le⟩ hbc
    have : (1 - 2 * c) * H c ≤ (1 - 2 * c) * f := by linarith
    have h3 := le_of_mul_le_mul_left this hz
    linarith

/-- `1/2 < λ < 1` holds automatically (the S.3 row-5 side condition). -/
theorem chart_lambda_mem {e f : ℝ} (he : 0 < e) (hef : e < f) :
    1 / 2 < chartLambda e f ∧ chartLambda e f < 1 := by
  have hE : 0 < e + f := by linarith
  unfold chartLambda
  constructor
  · rw [lt_div_iff₀ hE]; linarith
  · rw [div_lt_one hE]; linarith

/-- `A > 0` at every Case-E point. -/
theorem chartA_pos {e f c : ℝ} (hp : PointFree e f c) : 0 < chartA e f c := by
  obtain ⟨he, hef, hf, hbc, -, -⟩ := hp
  have hf0 : 0 < f := he.trans hef
  have hab : entropyInverse e < entropyInverse f := by
    have h1 := entropyInverse_spec he.le (hef.le.trans hf)
    have h2 := entropyInverse_spec hf0.le hf
    by_contra hn
    have hle : entropyInverse f ≤ entropyInverse e := le_of_not_gt hn
    have := H_strictMonoOn.monotoneOn ⟨h2.1, h2.2.1⟩ ⟨h1.1, h1.2.1⟩ hle
    rw [h1.2.2, h2.2.2] at this
    linarith
  unfold chartA
  exact div_pos (by linarith) (by linarith)

/-! ## Reduction (CONDITIONAL on the five owners) -/

/-- Manuscript Lemma 6.2 + App. S.3: the field `leftStationary` from the five CE-stat owners. -/
theorem leftStationary_of_owners (o : Owners) : LeftStationaryField := by
  intro e f c he hef hf hlow hc hs
  have hp := point_of_field he hef hf hlow hc hs
  by_cases h1 : chartTC f c ≤ 1 / 80000
  · by_cases hA : chartA e f c ≤ 21 / 200
    · have h := o.retained e f c hp.1 h1 hA
      exact absurd hp.2 (not_lt.mpr h.le)
    · exact (o.capital e f c hp (h1.trans (by norm_num)) (lt_of_not_ge hA)).elim
  · have h1' : 1 / 80000 ≤ chartTC f c := (lt_of_not_ge h1).le
    by_cases h2 : chartTC f c ≤ 1 / 100
    · by_cases hA1 : chartA e f c ≤ 1 / 20
      · exact o.transverse e f c hp h1' h2 hA1
      · by_cases hA2 : chartA e f c ≤ 21 / 200
        · exact o.a3 e f c hp h1' h2 (lt_of_not_ge hA1).le hA2
        · exact (o.capital e f c hp h2 (lt_of_not_ge hA2)).elim
    · exact (o.highTC e f c hp (lt_of_not_ge h2).le).elim

end CKLaneN1.CEStat

end


