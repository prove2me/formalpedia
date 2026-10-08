-- Prove2me | Definitions.Def_CK_CKLaneN1_CapKey
-- name    : CK_CKLaneN1_CapKey
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T20:21:57.463217+00:00
-- url     : https://prove2.me/theorems/1833cd1a-0aca-4774-837e-9b9a44e107f7
-- title:
--   Courtade–Kumar proof module `CKLaneN1.CapKey` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.CapKey` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.CapKey` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.CapKey (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/CapKey.lean)

import Definitions.Def_CK_CKLaneN1_CapTree
import Definitions.Def_CK_CKLaneN1_CapTail
import Definitions.Def_CK_CKLaneN1_CEStatRetained

-- ===== source module CKLaneN1.CapKey =====
section

set_option autoImplicit false

/-!
# Lane N1: CE-stat S.3 row 2 — capital exclusion from the capital tree check (conditional on `capTree_ok`)

At a retained stationary Case-E point, `L'(c) = Θ(U) - Θ(V) + Θ(W) = 0` with `U = A`,
`V = (1-a-c)/E`, `W = (1-2c)/(2f)` and `V = U + 2λW < U + 2W` (`λ = f/E < 1`). The condition
`t_C ≤ 1/100` gives `W ≥ 303/50`. The concavity-free pure-`Θ` inequality
`Θ(U + 2W) ≤ Θ(U) + Θ(W)` on `[21/200, ∞) × [303/50, ∞)` (`theta_capital`) then contradicts
`Θ(U) + Θ(W) = Θ(V) < Θ(U + 2W)` whenever `A > 21/200`.

`theta_capital` = 531-leaf kernel box certificate on `[21/200,128] × [303/50,128]`
(`capTree_ok`, fleet shards `CapShard.K00..K08`) + analytic tails:
`W ≤ U` via `Θ(v)-Θ(u) ≤ (13/6) log(v/u)` (corpus); `W ≥ 128` via `Θ(v)-Θ(u) ≤ (81/50) log(v/u)`
(`theta_increment_tail`); anchors `Θ(21/200)`, `Θ(1/5)`, `Θ(303/50)`.
-/

namespace CKLaneN1.Capital

open GeneralCK CKLaneE.FP GeneralCK.SmallMeanPhiCutoff CKLaneN1.CEStat

theorem ratcast_le {x y : ℚ} (h : x ≤ y) : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast h

/-- **Pure-Θ capital inequality** (concavity-free). -/
theorem theta_capital_of_tree
    (hT : capTree.allLeaves (fun p w => capLeafOK (capRoot.ofPath p) w) = true)
    {U W : ℝ} (hU : 21 / 200 ≤ U) (hW : 303 / 50 ≤ W) :
    e8Theta (U + 2 * W) ≤ e8Theta U + e8Theta W := by
  have hUpos : 0 < U := by linarith
  have hWpos : 0 < W := by linarith
  have hl3 := log_three_le
  have hl1281 := log_1281_le
  have hL := logs_ok
  have hcB := ratcast_le hL.2.2.2.2.1
  have hcW := ratcast_le hL.2.2.2.2.2.1
  have hcA := ratcast_le hL.2.2.2.1
  push_cast at hcA hcB hcW hl3 hl1281
  by_cases hWU : W ≤ U
  · have h1 := ZeroCapLeftStationaryLogIncrementTail.theta_increment_log_bound hUpos
      (show U ≤ U + 2 * W by linarith)
    have h2 : Real.log ((U + 2 * W) / U) ≤ Real.log 3 :=
      Real.log_le_log (by positivity) (by rw [div_le_iff₀ hUpos]; linarith)
    have h5 := theta_anchorW
    have h6 := theta_mono (by norm_num : (0 : ℝ) < 303 / 50) hW
    nlinarith
  · have hUW : U < W := lt_of_not_ge hWU
    by_cases hWT : 128 ≤ W
    · have h1 := theta_increment_tail hWT (show W ≤ U + 2 * W by linarith)
      by_cases hU5 : U ≤ 1 / 5
      · have h2 : Real.log ((U + 2 * W) / W) ≤ Real.log (1281 / 640) :=
          Real.log_le_log (by positivity) (by rw [div_le_iff₀ hWpos]; nlinarith)
        have h5 := theta_anchorA
        have h6 := theta_mono (by norm_num : (0 : ℝ) < 21 / 200) hU
        nlinarith
      · have h2 : Real.log ((U + 2 * W) / W) ≤ Real.log 3 :=
          Real.log_le_log (by positivity) (by rw [div_le_iff₀ hWpos]; linarith)
        have h5 := theta_anchorB
        have h6 := theta_mono (by norm_num : (0 : ℝ) < 1 / 5) (le_of_not_ge hU5)
        nlinarith
    · exact cap_cover hT hU (by linarith) hW (le_of_not_ge hWT)

/-- The left-fiber derivative in `Θ` form (corpus `deriv_canonicalPureGap_right`). -/
theorem deriv_leftFiber_theta {a c e f : ℝ} (hac : a < c) (hsum : a + c < 1) (hc : c < 1 / 2)
    (he : 0 < e) (hf : 0 < f) :
    deriv (fun y => canonicalPureGap a y e f) c =
      e8Theta ((c - a) / (e + f)) - e8Theta ((1 - a - c) / (e + f)) +
        e8Theta ((1 - 2 * c) / (2 * f)) := by
  have hE : 0 < (e + f) / 2 := by linarith
  rw [deriv_canonicalPureGap_right hac hsum hc he hf,
    deriv_F_radius_eq_e8Theta (sub_pos.mpr hac) hE,
    deriv_F_radius_eq_e8Theta (by linarith) hE,
    deriv_F_radius_eq_e8Theta (by linarith) hf]
  have e2 : 2 * ((e + f) / 2) = e + f := by ring
  rw [e2]

/-- **S.3 row 2 (CE-stat capital exclusion).** -/
theorem capitalExclusion_of_tree
    (hT : capTree.allLeaves (fun p w => capLeafOK (capRoot.ofPath p) w) = true) :
    CapitalExclusion := by
  intro e f c hp htc hA
  obtain ⟨⟨he, hef, hf, hbc, hc, hs⟩, -⟩ := hp
  have hf0 : 0 < f := he.trans hef
  have hab := inv_lt_inv he hef hf
  have hac : entropyInverse e < c := hab.trans hbc
  have ha0 : 0 ≤ entropyInverse e := (entropyInverse_spec he.le (hef.le.trans hf)).1
  have hsum : entropyInverse e + c < 1 := by linarith
  have hE : 0 < e + f := by linarith
  have hz : 0 < 1 - 2 * c := by linarith
  have hderiv := deriv_leftFiber_theta hac hsum hc he hf0
  rw [hs] at hderiv
  set U := (c - entropyInverse e) / (e + f) with hUdef
  set V := (1 - entropyInverse e - c) / (e + f) with hVdef
  set W := (1 - 2 * c) / (2 * f) with hWdef
  have hU : 21 / 200 < U := by
    have : chartA e f c = U := rfl
    linarith
  -- `t_C ≤ 1/100` gives `W ≥ 303/50`
  have hW : 303 / 50 ≤ W := by
    have htc' : radialContact (1 - 2 * c) f ≤ 1 / 100 := htc
    have h := (radialContact_le_iff hz hf0 (by norm_num) (by norm_num)).mp htc'
    have hH := (H_bounds logs_ok.2.2.2.2.2.2.2.2.2).2
    have hHq := ratcast_le logs_ok.2.2.2.2.2.2.2.2.1
    push_cast at hH hHq
    have hH' : H (1 / 100 : ℝ) ≤ 49 / 606 := by linarith
    have h2 : f * (49 / 50) ≤ (1 - 2 * c) * (49 / 606) := by
      have := mul_le_mul_of_nonneg_left hH' hz.le
      nlinarith
    rw [hWdef, le_div_iff₀ (by positivity)]
    nlinarith
  have hVpos : 0 < V := by rw [hVdef]; exact div_pos (by linarith) hE
  have hVlt : V < U + 2 * W := by
    have h1 : V - U = (1 - 2 * c) / (e + f) := by
      rw [hVdef, hUdef]; field_simp; ring
    have h2 : (1 - 2 * c) / (e + f) < (1 - 2 * c) / f :=
      div_lt_div_of_pos_left hz hf0 (by linarith)
    have h3 : 2 * W = (1 - 2 * c) / f := by
      rw [hWdef]; field_simp
    linarith
  have hlt : e8Theta V < e8Theta (U + 2 * W) :=
    strictMonoOn_e8Theta_pos (Set.mem_Ioi.mpr hVpos) (Set.mem_Ioi.mpr (by linarith)) hVlt
  have hkey := theta_capital_of_tree hT hU.le hW
  linarith

end CKLaneN1.Capital

end


