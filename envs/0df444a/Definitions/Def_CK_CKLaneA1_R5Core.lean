-- Prove2me | Definitions.Def_CK_CKLaneA1_R5Core
-- name    : CK_CKLaneA1_R5Core
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:40:52.768537+00:00
-- url     : https://prove2.me/theorems/8779c990-8c77-4644-96bb-7f68a8ee9782
-- title:
--   Courtade–Kumar proof module `CKLaneA1.R5Core` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.R5Core` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.R5Core` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.R5Core (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/R5Core.lean)

import Definitions.Def_CK_CKLaneN1_CEStat
import Definitions.Def_CK_CKLaneP_LeftFiber
import Definitions.Def_CK_CKLaneP_ThetaPrime
import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryLogIncrementTail

-- ===== source module CKLaneA1.R5Core =====
section

/-!
# CKLaneA1.R5Core — chart glue, the Case-E exclusion lemma and the large-`A` tail for CE-stat row 5

Lane A1, CE-stat S.3 row 5 (`CKLaneN1.CEStat.HighTCExclusion`): no retained stationary Case-E
point has `t_C ≥ 1/100`.

For a Case-E stationary point write `a = ι(e) < b = ι(f) < c < 1/2`, `t = t_C = radialContact (1-2c) f`,
`E = e + f`, `A = (c-a)/E`, `W = (1-2c)/(2f) = X(t)`, `λ = f/E`.  Stationarity is
`D(A,W,λ) := Θ(A) + Θ(W) − Θ(A + 2λW) = 0`.  `D` is strictly decreasing in `λ` at fixed `(A, W)`.
The Case-E condition `b < c` (equivalently `t < c`) reads `λ(t − a) < A·H(t)`, and together with the
exact relation `L(a) = (1−λ)/(A + λW)` (`L(a) = 2H(a)/(1−2a)`) it bounds `λ` from above
(`exclusion`): if `κ > 0`, `u = 2A·H(t)/(1+κA) < t` and `H(t) − H(t−u) ≤ uκ`, then `λ < (1+κA)/2`.
-/

set_option autoImplicit false

namespace CKLaneA1.R5

open GeneralCK GeneralCK.Certificates.Mixed CKLaneN1.CEStat

/-- `W` as a function of the contact `t`: `X(t) = (1-2t)/(2H(t))`. -/
noncomputable def Xf (t : ℝ) : ℝ := (1 - 2 * t) / (2 * H t)

/-- `L(a) = 2H(a)/(1-2a)`. -/
noncomputable def Lf (a : ℝ) : ℝ := 2 * H a / (1 - 2 * a)

/-- The stationarity residual `D(A,W,λ) = Θ(A) + Θ(W) − Θ(A + 2λW)`. -/
noncomputable def Dst (A W lam : ℝ) : ℝ := e8Theta A + e8Theta W - e8Theta (A + 2 * lam * W)

theorem H_zero' : H 0 = 0 := by
  have h := hn_eq_H_mul_log 0
  have h0 : hn 0 = 0 := by simp [hn]
  rw [h0] at h
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rcases mul_eq_zero.mp h.symm with h1 | h1
  · exact h1
  · exact absurd h1 hl

theorem H_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1 / 2) : H u ≤ H v :=
  H_strictMonoOn.monotoneOn ⟨hu, huv.trans hv⟩ ⟨hu.trans huv, hv⟩ huv

theorem H_lt {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1 / 2) : H u < H v :=
  H_strictMonoOn ⟨hu, huv.le.trans hv⟩ ⟨hu.trans huv.le, hv⟩ huv

/-- `L` is strictly increasing on `(0, 1/2)`. -/
theorem Lf_lt {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 1 / 2) : Lf u < Lf v := by
  unfold Lf
  have h1 : 0 < 1 - 2 * v := by linarith
  have h2 : 0 < 1 - 2 * u := by linarith
  have hHu : 0 < H u := H_pos hu (by linarith)
  have hH := H_lt hu.le huv hv.le
  rw [div_lt_div_iff₀ h2 h1]
  nlinarith

theorem le_of_Lf_le {u v : ℝ} (hu : 0 < u) (hu2 : u < 1 / 2) (hv : 0 < v) (hv2 : v < 1 / 2)
    (h : Lf u ≤ Lf v) : u ≤ v := by
  by_contra hn
  have := Lf_lt hv (lt_of_not_ge hn) hu2
  linarith

/-! ## The chart of a row-5 point -/

/-- All chart facts of a retained stationary Case-E point with `t_C ≥ 1/100`. -/
theorem chart_point {e f c : ℝ} (hp : Point e f c) (ht : 1 / 100 ≤ chartTC f c) :
    let a := entropyInverse e
    let t := chartTC f c
    0 < a ∧ a < t ∧ t < c ∧ c < 1 / 2 ∧ H a = e ∧ 0 < e ∧ 0 < f ∧
      (1 - 2 * c) * H t = f * (1 - 2 * t) ∧ 1 / 100 ≤ t ∧
      Dst ((c - a) / (e + f)) ((1 - 2 * c) / (2 * f)) (f / (e + f)) = 0 := by
  intro a t
  have hord := chart_order hp.1
  obtain ⟨⟨he, hef, hf, hbc, hc, hs⟩, -⟩ := hp
  have hf0 : 0 < f := he.trans hef
  obtain ⟨ha0, ha2, hHa⟩ := entropyInverse_spec he.le (hef.le.trans hf)
  have hab : entropyInverse e < entropyInverse f := inv_lt_inv' he hef hf
  have ha : 0 < a := by
    rcases ha0.lt_or_eq with h | h
    · exact h
    · exfalso
      have : H (entropyInverse e) = 0 := by rw [← h]; exact H_zero'
      rw [hHa] at this; linarith
  have hat : a < t := hab.trans hord.1
  have htc : t < c := hord.2
  have hac : a < c := hat.trans htc
  have hz : 0 < 1 - 2 * c := by linarith
  have hcont : (1 - 2 * c) * H t = f * (1 - 2 * t) := radialContact_equation hz hf0
  refine ⟨ha, hat, htc, hc, hHa, he, hf0, hcont, ht, ?_⟩
  have hd := CKLaneP.leftFiber_deriv_eq hac (by linarith) hc he hf0
  rw [hs] at hd
  unfold CKLaneP.leftFiberDeriv at hd
  unfold Dst
  have hE : 0 < e + f := by linarith
  have e1 : (c - a) / (e + f) + 2 * (f / (e + f)) * ((1 - 2 * c) / (2 * f)) =
      (1 - a - c) / (e + f) := by
    field_simp
    ring
  rw [e1]
  linarith
where
  inv_lt_inv' {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f ≤ 1) :
      entropyInverse e < entropyInverse f := by
    have hf0 : 0 < f := he.trans hef
    have h1 := entropyInverse_spec he.le (hef.le.trans hf)
    have h2 := entropyInverse_spec hf0.le hf
    by_contra hn
    have hle : entropyInverse f ≤ entropyInverse e := le_of_not_gt hn
    have := H_strictMonoOn.monotoneOn ⟨h2.1, h2.2.1⟩ ⟨h1.1, h1.2.1⟩ hle
    rw [h1.2.2, h2.2.2] at this
    linarith

/-- Chart identities: `W = X(t)`, `L(a) = (1−λ)/(A+λW)`, and the Case-E inequality
`λ(t−a) < A·H(t)`. -/
theorem chart_ids {a t c e f : ℝ} (ha : 0 < a) (hat : a < t) (htc : t < c) (hc : c < 1 / 2)
    (hHa : H a = e) (he : 0 < e) (hf : 0 < f) (hcont : (1 - 2 * c) * H t = f * (1 - 2 * t)) :
    (1 - 2 * c) / (2 * f) = Xf t ∧
      Lf a = (1 - f / (e + f)) / ((c - a) / (e + f) + f / (e + f) * ((1 - 2 * c) / (2 * f))) ∧
      f / (e + f) * (t - a) < (c - a) / (e + f) * H t := by
  have hE : 0 < e + f := by linarith
  have hHt : 0 < H t := H_pos (ha.trans hat) (by linarith)
  have hz : 0 < 1 - 2 * c := by linarith
  have hzt : 0 < 1 - 2 * t := by linarith
  have hza : 0 < 1 - 2 * a := by linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold Xf
    rw [div_eq_div_iff (by positivity) (by positivity)]
    nlinarith [hcont]
  · unfold Lf
    rw [hHa]
    have e1 : 1 - f / (e + f) = e / (e + f) := by field_simp; ring
    have e2 : (c - a) / (e + f) + f / (e + f) * ((1 - 2 * c) / (2 * f)) =
        (1 - 2 * a) / (2 * (e + f)) := by field_simp; ring
    rw [e1, e2]
    field_simp
  · have hHt' : H t = f * (1 - 2 * t) / (1 - 2 * c) := by
      field_simp; linarith [hcont]
    rw [hHt']
    rw [div_mul_eq_mul_div, div_mul_div_comm, div_lt_div_iff₀ hE (by positivity)]
    have key : f * (t - a) * ((e + f) * (1 - 2 * c)) - (c - a) * (f * (1 - 2 * t)) * (e + f) =
        f * (e + f) * ((t - c) * (1 - 2 * a)) := by ring
    have hneg : f * (e + f) * ((t - c) * (1 - 2 * a)) < 0 := by
      have : (t - c) * (1 - 2 * a) < 0 := mul_neg_of_neg_of_pos (by linarith) hza
      have hp : 0 < f * (e + f) := mul_pos hf hE
      exact mul_neg_of_pos_of_neg hp this
    nlinarith [key, hneg]

/-! ## Entropy tangent inequality -/

/-- Tangent-line (concavity) inequality for the binary entropy: `H(x) ≤ H(y) + J(y)(x − y)`. -/
theorem H_le_tangent {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    H x ≤ H y + J y * (x - y) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx := hn_eq_H_mul_log x
  have hy := hn_eq_H_mul_log y
  have hHx : H x = hn x / Real.log 2 := by field_simp; linarith
  have hHy : H y = hn y / Real.log 2 := by field_simp; linarith
  rw [hHx, hHy]
  unfold J
  rw [div_mul_eq_mul_div, ← add_div, div_le_div_iff_of_pos_right hl2]
  -- KL(x‖y) ≥ 0 via log z ≤ z − 1
  have h1 : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
  have h2 : Real.log ((1 - y) / (1 - x)) ≤ (1 - y) / (1 - x) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
  rw [Real.log_div hy0.ne' hx0.ne'] at h1
  rw [Real.log_div (by linarith) (by linarith)] at h2
  rw [Real.log_div (by linarith) hy0.ne']
  unfold hn
  have hx1' : 0 < 1 - x := by linarith
  have k1 : x * (Real.log y - Real.log x) ≤ y - x := by
    have := mul_le_mul_of_nonneg_left h1 hx0.le
    have e : x * (y / x - 1) = y - x := by field_simp
    linarith
  have k2 : (1 - x) * (Real.log (1 - y) - Real.log (1 - x)) ≤ x - y := by
    have := mul_le_mul_of_nonneg_left h2 hx1'.le
    have e : (1 - x) * ((1 - y) / (1 - x) - 1) = x - y := by field_simp; ring
    linarith
  nlinarith [k1, k2]

theorem J_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) : J y ≤ J x := by
  unfold J
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply div_le_div_of_nonneg_right _ hl2.le
  apply Real.log_le_log (div_pos (by linarith) (by linarith))
  rw [div_le_div_iff₀ (by linarith) hx]
  nlinarith

/-! ## The exclusion lemma -/

/-- **Case-E exclusion.**  At a Case-E chart point (`λ(t−a) < A·H(t)`, `L(a) = (1−λ)/(A+λW)`,
`H(t)·W = (1−2t)/2`), if `κ > 0`, `u = 2A·H(t)/(1+κA)`, `0 < t − u` and `H(t) − H(t−u) ≤ uκ`,
then `λ < (1+κA)/2`. -/
theorem exclusion {a t A W lam kap' : ℝ} (ha : 0 < a) (hat : a < t) (ht2 : t < 1 / 2)
    (hA : 0 < A) (hW : 0 < W) (hHW : H t * W = (1 - 2 * t) / 2) (hlam0 : 0 < lam)
    (hL : Lf a = (1 - lam) / (A + lam * W)) (hcase : lam * (t - a) < A * H t)
    (hk : 0 < kap') (hu : 0 < t - 2 * A * H t / (1 + kap' * A))
    (hH : H t - H (t - 2 * A * H t / (1 + kap' * A)) ≤ 2 * A * H t / (1 + kap' * A) * kap') :
    lam < (1 + kap' * A) / 2 := by
  set u := 2 * A * H t / (1 + kap' * A) with hu_def
  have ht0 : 0 < t := ha.trans hat
  have hHt : 0 < H t := H_pos ht0 (by linarith)
  have h1k : 0 < 1 + kap' * A := by positivity
  set s := 2 * H t / (1 + kap' * A) with hs_def
  have hs : 0 < s := by positivity
  have hus : u = A * s := by rw [hu_def, hs_def]; ring
  set a2 := t - u with ha2_def
  have ha2 : 0 < a2 := hu
  have ha2t : a2 < t := by rw [ha2_def]; have : 0 < u := by rw [hus]; positivity
                           linarith
  set e2 := H a2 with he2_def
  have he2 : 0 < e2 := H_pos ha2 (by linarith)
  set E2 := e2 + H t with hE2_def
  have hE2 : 0 < E2 := by positivity
  have hE2s : s ≤ E2 := by
    have : 2 * H t - u * kap' = s := by
      rw [hu_def, hs_def]; field_simp; ring
    have hH' : H t - e2 ≤ u * kap' := hH
    linarith
  by_contra hn
  push Not at hn
  -- λ ≥ (1+κA)/2 = H t / s
  have hlb : (1 + kap' * A) / 2 = H t / s := by rw [hs_def]; field_simp
  set lam2 := H t / E2 with hlam2_def
  have hlam2_le : lam2 ≤ lam := by
    have : H t / E2 ≤ H t / s := div_le_div_of_nonneg_left hHt.le hs hE2s
    linarith
  have hlam2_lt1 : lam2 < 1 := by rw [hlam2_def, div_lt_one hE2]; linarith
  have hlam2_pos : 0 < lam2 := by positivity
  set A2 := u / E2 with hA2_def
  have hA2_le : A2 ≤ A := by
    rw [hA2_def, div_le_iff₀ hE2, hus]
    nlinarith
  have hA2_pos : 0 < A2 := by
    rw [hA2_def]; have : 0 < u := by rw [hus]; positivity
    positivity
  -- L(a2) = (1-λ2)/(A2+λ2 W)
  have hLa2 : Lf a2 = (1 - lam2) / (A2 + lam2 * W) := by
    unfold Lf
    rw [← he2_def]
    have e1 : 1 - lam2 = e2 / E2 := by rw [hlam2_def]; field_simp; rw [hE2_def]; ring
    have e2' : A2 + lam2 * W = (1 - 2 * a2) / (2 * E2) := by
      rw [hA2_def, hlam2_def, div_mul_eq_mul_div, ← add_div, hHW, ha2_def]
      field_simp; ring
    rw [e1, e2']
    have : 0 < 1 - 2 * a2 := by linarith
    field_simp
  -- monotonicity chain
  have hden1 : 0 < A + lam * W := by positivity
  have hden2 : 0 < A + lam2 * W := by positivity
  have hden3 : 0 < A2 + lam2 * W := by positivity
  have c1 : (1 - lam) / (A + lam * W) ≤ (1 - lam2) / (A + lam2 * W) := by
    rw [div_le_div_iff₀ hden1 hden2]
    nlinarith
  have c2 : (1 - lam2) / (A + lam2 * W) ≤ (1 - lam2) / (A2 + lam2 * W) :=
    div_le_div_of_nonneg_left (by linarith) hden3 (by nlinarith)
  have hLL : Lf a ≤ Lf a2 := by rw [hL, hLa2]; exact c1.trans c2
  have haa2 : a ≤ a2 := le_of_Lf_le ha (by linarith) ha2 (by linarith) hLL
  -- λ(t-a) ≥ (H t/s)·u = A·H t
  have hta : u ≤ t - a := by rw [ha2_def] at haa2; linarith
  have hkey : H t / s * u = A * H t := by rw [hus]; field_simp
  have : H t / s * u ≤ lam * (t - a) := by
    have hlb' : H t / s ≤ lam := by rw [← hlb]; exact hn
    have hu0 : 0 ≤ u := by rw [hus]; positivity
    calc H t / s * u ≤ lam * u := mul_le_mul_of_nonneg_right hlb' hu0
      _ ≤ lam * (t - a) := mul_le_mul_of_nonneg_left hta hlam0.le
  linarith

#print axioms chart_point
#print axioms chart_ids
#print axioms H_le_tangent
#print axioms exclusion

end CKLaneA1.R5

end


