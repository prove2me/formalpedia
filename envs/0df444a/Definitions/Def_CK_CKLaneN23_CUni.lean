-- Prove2me | Definitions.Def_CK_CKLaneN23_CUni
-- name    : CK_CKLaneN23_CUni
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:50:17.289102+00:00
-- url     : https://prove2.me/theorems/e591b8db-137d-41f2-8ca9-0527768a240c
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CUni` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CUni` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CUni` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CUni (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CUni.lean)

import Definitions.Def_CK_CKLaneN23_CStep
import Definitions.Def_CK_CKLaneN23_RSDefs
import Definitions.Def_CK_GeneralCK_RadialDerivatives
import Definitions.Def_CK_GeneralCK_RadialContact
import Definitions.Def_CK_GeneralCK_EtaMonotone
import Definitions.Def_CK_GeneralCK_ProfileConvexity
import Definitions.Def_CK_GeneralCK_ProfileDerivatives

-- ===== source module CKLaneN23.CUni =====
section

/-!
# CKLaneN23.CUni — univariate implicit functions of the RA-stat corner certificate (Lane N23b)

**Contact.**  For `ζ > 0` let `v = radialContact ζ 1`, `δ = 1 - 2v`.  With `w = ζ²` put
`gC w = δ/ζ` (`gC w = 1` for `w ≤ 0`), `YC w = w·gC(w)² = δ²`, `kapC Y = log 2 - log(1-Y)/2`.  Then
(`contact_values`)
  `F ζ 1 = Phi0 (ζ²)`, `deriv (F · 1) ζ = ζ · Phi1 (ζ²)`, `deriv² (F · 1) ζ = Phi2 (ζ²)`.
`gC_bracket` turns two residual signs of `hent(√(w G²)) - G` into `G₋ ≤ gC w ≤ G₊`.

**Entropy inverse.**  `Rst ε = (1 - 2·entropyInverse (1-ε))²`; for `0 < ε < 1`
(`eta_values`) `etaSlope (1-ε) = Sfun ε`, `etaCurvature (1-ε) = Kfun ε`; `Rst_bracket` turns two
residual signs of `hent(√R) + (ε - 1)` into `R₋ ≤ Rst ε ≤ R₊`.

**Packaging.**  `uni_ser`: a σ,τ-free TM of `x ↦ Φ x` on `(0, Eps]` plus `Φ 0 = hornerL cs 0` gives
the series bound consumed by `step_ser_nonneg` in the trivariate chain.
-/

namespace CKLaneN23.CT

open GeneralCK GeneralCK.Certificates.Mixed

/-! ## packaging -/

/-- σ,τ-free `TPoly` from a coefficient list (`[]` stays `[]`). -/
def toT (cs : List LPoly) : TPoly := cs.map (fun l => if l = [] then [] else [((0, 0), l)])

theorem eval_toT (x σ τ : ℝ) (cs : List LPoly) :
    TPoly.eval x σ τ (Real.log 2) (toT cs) = hornerL cs x := by
  induction cs with
  | nil => rfl
  | cons l cs ih =>
    have e : toT (l :: cs) = (if l = [] then [] else [((0, 0), l)]) :: toT cs := rfl
    rw [e, TPoly.eval_cons, hornerL_cons, ih]
    split_ifs with h
    · subst h; simp [QPoly.eval_nil, LPoly.eval_nil]
    · simp [QPoly.eval_cons, QPoly.eval_nil]

theorem uni_ser {Φ : ℝ → ℝ} {cs : List LPoly} {r : ℚ} {n : ℕ}
    (h : Good (fun x _ _ => Φ x) ⟨toT cs, r, n⟩) (h0 : Φ 0 = hornerL cs 0) :
    ∀ z : ℝ, 0 ≤ z → z ≤ (Eps : ℝ) → |Φ z - hornerL cs z| ≤ (r : ℝ) * |z| ^ n := by
  intro z hz0 hz1
  have hr : (0 : ℝ) ≤ r := by exact_mod_cast h.2
  rcases hz0.lt_or_eq with hpos | hzero
  · have hd : Dom z 0 0 := ⟨hpos, hz1, by norm_num, by norm_num⟩
    have h1 := h.1 z 0 0 hd
    unfold ev at h1
    rw [eval_toT] at h1
    rw [abs_of_pos hpos]
    exact h1
  · subst hzero
    rw [h0, sub_self, abs_zero]
    positivity

/-! ## contact: residual brackets -/

theorem contact_le {ζ δ : ℝ} (hζ : 0 < ζ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hres : 0 ≤ ζ * hent δ - δ) : δ ≤ 1 - 2 * radialContact ζ 1 := by
  have hv0 : 0 ≤ (1 - δ) / 2 := by linarith
  have hv1 : (1 - δ) / 2 ≤ 1 / 2 := by linarith
  have h := (radialContact_le_iff hζ (by norm_num : (0 : ℝ) < 1) hv0 hv1).2 (by
    unfold hent at hres
    have e : 1 - 2 * ((1 - δ) / 2) = δ := by ring
    rw [e]
    linarith)
  linarith

theorem contact_ge {ζ δ : ℝ} (hζ : 0 < ζ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hres : ζ * hent δ - δ ≤ 0) : 1 - 2 * radialContact ζ 1 ≤ δ := by
  have hv0 : 0 ≤ (1 - δ) / 2 := by linarith
  have hv1 : (1 - δ) / 2 ≤ 1 / 2 := by linarith
  have h := (le_radialContact_iff hζ (by norm_num : (0 : ℝ) < 1) hv0 hv1).2 (by
    unfold hent at hres
    have e : 1 - 2 * ((1 - δ) / 2) = δ := by ring
    rw [e]
    linarith)
  linarith

/-- contact ratio `g(w) = δ(√w)/√w`, `g(w) = 1` for `w ≤ 0` -/
noncomputable def gC (w : ℝ) : ℝ :=
  if w ≤ 0 then 1 else (1 - 2 * radialContact (Real.sqrt w) 1) / Real.sqrt w

theorem sqrt_mul_sq {w G : ℝ} (hw : 0 ≤ w) (hG : 0 ≤ G) : Real.sqrt (w * (G * G)) = Real.sqrt w * G := by
  rw [Real.sqrt_mul hw, Real.sqrt_mul_self hG]

theorem gC_bracket {w Gm Gp : ℝ} (hw : 0 < w) (hm0 : 0 ≤ Gm) (hmp : Gm ≤ Gp)
    (hp1 : Real.sqrt w * Gp ≤ 1)
    (hlo : 0 ≤ hent (Real.sqrt (w * (Gm * Gm))) + ((-1 : ℚ) : ℝ) * Gm)
    (hhi : hent (Real.sqrt (w * (Gp * Gp))) + ((-1 : ℚ) : ℝ) * Gp ≤ 0) :
    Gm ≤ gC w ∧ gC w ≤ Gp := by
  set ζ := Real.sqrt w with hζdef
  have hζ : 0 < ζ := Real.sqrt_pos.mpr hw
  have hp0 : 0 ≤ Gp := hm0.trans hmp
  rw [sqrt_mul_sq hw.le hm0] at hlo
  rw [sqrt_mul_sq hw.le hp0] at hhi
  push_cast at hlo hhi
  have hg : gC w = (1 - 2 * radialContact ζ 1) / ζ := by
    unfold gC; rw [if_neg (not_le.mpr hw)]
  have hlo' : 0 ≤ ζ * hent (ζ * Gm) - ζ * Gm := by nlinarith
  have hhi' : ζ * hent (ζ * Gp) - ζ * Gp ≤ 0 := by nlinarith
  have hmζ : ζ * Gm ≤ ζ * Gp := mul_le_mul_of_nonneg_left hmp hζ.le
  have h1 := contact_le hζ (by positivity) (hmζ.trans hp1) hlo'
  have h2 := contact_ge hζ (by positivity) hp1 hhi'
  rw [hg]
  constructor
  · rw [le_div_iff₀ hζ]; linarith
  · rw [div_le_iff₀ hζ]; linarith

/-! ## contact: the functions `Phi0, Phi1, Phi2` and their identification -/

noncomputable def YC (w : ℝ) : ℝ := w * (gC w * gC w)

noncomputable def kapC (Y : ℝ) : ℝ := Real.log 2 - Real.log (1 - Y) / 2

noncomputable def Phi0 (w : ℝ) : ℝ := 2 / Real.log 2 * (w * (gC w * Adiv (YC w)))

noncomputable def Phi1 (w : ℝ) : ℝ :=
  2 / Real.log 2 * (gC w * Adiv (YC w)) + 2 * (gC w * gC w * (1 / (1 - YC w)) * (1 / kapC (YC w)))

noncomputable def Phi2 (w : ℝ) : ℝ :=
  4 * ((gC w * gC w * (2 * kapC (YC w) - YC w)) *
    ((1 / (1 - YC w)) * (1 / (1 - YC w)) * ((1 / kapC (YC w)) * (1 / kapC (YC w))) * (1 / (2 + Phi0 w))))

theorem gC_zero : gC 0 = 1 := by simp [gC]

theorem YC_zero : YC 0 = 0 := by simp [YC]

theorem kapC_zero : kapC 0 = Real.log 2 := by simp [kapC]

theorem Phi0_zero : Phi0 0 = 0 := by simp [Phi0]

theorem Phi1_zero : Phi1 0 = 4 / Real.log 2 := by
  have hL : Real.log 2 ≠ 0 := by positivity
  simp only [Phi1, gC_zero, YC_zero, Adiv_zero, kapC_zero]
  field_simp
  ring

theorem Phi2_zero : Phi2 0 = 4 / Real.log 2 := by
  have hL : Real.log 2 ≠ 0 := by positivity
  simp only [Phi2, gC_zero, YC_zero, kapC_zero, Phi0_zero]
  field_simp
  ring

theorem atanhR_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : 0 < atanhR x := by
  unfold atanhR
  apply div_pos _ (by norm_num)
  apply Real.log_pos
  rw [one_lt_div (by linarith)]
  linarith

theorem contact_values {ζ : ℝ} (hζ : 0 < ζ) :
    Phi0 (ζ ^ 2) = F ζ 1 ∧ ζ * Phi1 (ζ ^ 2) = deriv (fun r => F r 1) ζ ∧
      Phi2 (ζ ^ 2) = deriv (deriv (fun r => F r 1)) ζ := by
  have h1 : (0 : ℝ) < 1 := one_pos
  have hv0 : 0 < radialContact ζ 1 := radialContact_pos hζ h1
  have hv1 : radialContact ζ 1 < 1 / 2 := radialContact_lt_half hζ h1
  have heq : ζ * H (radialContact ζ 1) = 1 * (1 - 2 * radialContact ζ 1) := radialContact_equation hζ h1
  set v := radialContact ζ 1 with hv
  have hvc : 0 < 1 - v := by linarith
  have hδ0 : 0 < 1 - 2 * v := by linarith
  have hδ1 : 1 - 2 * v < 1 := by linarith
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hg : gC (ζ ^ 2) = (1 - 2 * v) / ζ := by
    unfold gC; rw [if_neg (not_le.mpr (by positivity)), Real.sqrt_sq hζ.le]
  have hY : YC (ζ ^ 2) = (1 - 2 * v) ^ 2 := by unfold YC; rw [hg]; field_simp
  have hA : Adiv ((1 - 2 * v) ^ 2) = atanhR (1 - 2 * v) / (1 - 2 * v) := Adiv_of_pos hδ0
  have hat : 0 < atanhR (1 - 2 * v) := atanhR_pos hδ0 hδ1
  have hJ : J v = 2 * atanhR (1 - 2 * v) / Real.log 2 := by
    unfold J atanhR
    have e : (1 - v) / v = (1 + (1 - 2 * v)) / (1 - (1 - 2 * v)) := by field_simp; ring
    rw [e]; ring
  have hH : H v = (1 - 2 * v) / ζ := by field_simp; linarith [heq]
  have hkap : kap v = kapC ((1 - 2 * v) ^ 2) := by
    unfold kap kapC
    have e : 1 - (1 - 2 * v) ^ 2 = 2 ^ 2 * (v * (1 - v)) := by ring
    rw [e, Real.log_mul (by norm_num : (2 : ℝ) ^ 2 ≠ 0) (mul_pos hv0 hvc).ne', Real.log_pow]
    push_cast; ring
  have hkp : 0 < kapC ((1 - 2 * v) ^ 2) := hkap ▸ kap_pos hv0 hv1
  have hd1 : 0 < 1 - (1 - 2 * v) ^ 2 := by nlinarith
  have hF : F ζ 1 = ζ * J v := by unfold F; rw [if_neg hζ.ne']
  have hP0 : Phi0 (ζ ^ 2) = F ζ 1 := by
    unfold Phi0; rw [hY, hg, hA, hF, hJ]; field_simp
  have hJp : 0 < J v := J_pos hv0 hv1
  refine ⟨hP0, ?_, ?_⟩
  · rw [deriv_F_radius_slope hζ h1, ← hv]
    unfold Phi1 radialSlope
    rw [hY, hg, hA, hJ, hn_eq_H_mul_log, hH, hkap]
    have hkp' := hkp.ne'
    have hd1' := hd1.ne'
    have hat' := hat.ne'
    have hv0' := hv0.ne'
    have hvc' := hvc.ne'
    field_simp
    ring
  · rw [(hasDerivAt_deriv_F_radius hζ h1).deriv, ← hv]
    unfold Phi2
    rw [hP0, hF, hY, hg, hn_eq_H_mul_log, hH, hkap, hJ]
    have hden : 0 < ζ * (2 * atanhR (1 - 2 * v) / Real.log 2) + 2 * 1 := by positivity
    have hden2 : 0 < 2 + ζ * (2 * atanhR (1 - 2 * v) / Real.log 2) := by positivity
    have hkp' := hkp.ne'
    have hd1' := hd1.ne'
    have hv0' := hv0.ne'
    have hvc' := hvc.ne'
    have hden' := hden.ne'
    have hden2' := hden2.ne'
    field_simp
    ring

/-! ## entropy inverse -/

theorem entropy_le {E δ : ℝ} (hE0 : 0 ≤ E) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hres : 0 ≤ hent δ - E) : δ ≤ 1 - 2 * entropyInverse E := by
  have hv0 : 0 ≤ (1 - δ) / 2 := by linarith
  have hv1 : (1 - δ) / 2 ≤ 1 / 2 := by linarith
  unfold hent at hres
  have hmono := entropyInverse_mono hE0 (H_le_one _) (show E ≤ H ((1 - δ) / 2) by linarith)
  rw [entropyInverse_H_lower hv0 hv1] at hmono
  linarith

theorem entropy_ge {E δ : ℝ} (hE1 : E ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hres : hent δ - E ≤ 0) : 1 - 2 * entropyInverse E ≤ δ := by
  have hv0 : 0 ≤ (1 - δ) / 2 := by linarith
  have hv1 : (1 - δ) / 2 ≤ 1 / 2 := by linarith
  unfold hent at hres
  have hHnn := H_nonneg hv0 (by linarith)
  have hmono := entropyInverse_mono hHnn hE1 (show H ((1 - δ) / 2) ≤ E by linarith)
  rw [entropyInverse_H_lower hv0 hv1] at hmono
  linarith

/-- `R(ε) = (1 - 2 entropyInverse (1-ε))²` -/
noncomputable def Rst (ε : ℝ) : ℝ := (1 - 2 * entropyInverse (1 - ε)) ^ 2

theorem Rst_bracket {ε Rm Rp : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hm0 : 0 ≤ Rm) (hmp : Rm ≤ Rp)
    (hp1 : Rp ≤ 1)
    (hlo : 0 ≤ hent (Real.sqrt Rm) + (ε + ((-1 : ℚ) : ℝ)))
    (hhi : hent (Real.sqrt Rp) + (ε + ((-1 : ℚ) : ℝ)) ≤ 0) :
    Rm ≤ Rst ε ∧ Rst ε ≤ Rp := by
  push_cast at hlo hhi
  have hE0 : 0 ≤ 1 - ε := by linarith
  have hE1 : 1 - ε ≤ 1 := by linarith
  obtain ⟨hm0', hm1', _⟩ := entropyInverse_spec hE0 hE1
  have hρ0 : 0 ≤ 1 - 2 * entropyInverse (1 - ε) := by linarith
  have hsm0 := Real.sqrt_nonneg Rm
  have hsp0 := Real.sqrt_nonneg Rp
  have hsm1 : Real.sqrt Rm ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (hmp.trans hp1)
  have hsp1 : Real.sqrt Rp ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hp1
  have h1 := entropy_le hE0 hsm0 hsm1 (by linarith)
  have h2 := entropy_ge hE1 hsp0 hsp1 (by linarith)
  unfold Rst
  constructor
  · have := mul_le_mul h1 h1 hsm0 hρ0
    rw [Real.mul_self_sqrt hm0] at this
    nlinarith
  · have := mul_le_mul h2 h2 hρ0 hsp0
    rw [Real.mul_self_sqrt (hm0.trans hmp)] at this
    nlinarith

noncomputable def Sfun (ε : ℝ) : ℝ :=
  -2 + -2 * ((1 / (1 - Rst ε)) * (1 / (1 - (1 - Adiv (Rst ε)))))

noncomputable def Kfun (ε : ℝ) : ℝ :=
  2 * Real.log 2 * ((Bfun (Rst ε) * ((1 / (1 - Rst ε)) * (1 / (1 - Rst ε)))) *
    ((1 / (1 - (1 - Adiv (Rst ε)))) * (1 / (1 - (1 - Adiv (Rst ε)))) * (1 / (1 - (1 - Adiv (Rst ε))))))

theorem Rst_zero : Rst 0 = 0 := by
  unfold Rst
  have h := entropyInverse_H_lower (v := 1 / 2) (by norm_num) le_rfl
  rw [H_half] at h
  rw [sub_zero, h]
  norm_num

theorem Sfun_zero : Sfun 0 = -4 := by
  simp only [Sfun, Rst_zero, Adiv_zero]; norm_num

theorem Kfun_zero : Kfun 0 = 8 / 3 * Real.log 2 := by
  have hb : Bfun 0 = 4 / 3 := by simp [Bfun]
  simp only [Kfun, Rst_zero, Adiv_zero, hb]; ring

theorem eta_alg {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1 / 2) :
    (-2 - (1 - 2 * m) / (Real.log 2 * m * (1 - m) * J m)) =
      -2 + -2 * ((1 / (1 - (1 - 2 * m) ^ 2)) * (1 / (1 - (1 - Adiv ((1 - 2 * m) ^ 2))))) ∧
    Scalar.curvatureNumerator m / ((Real.log 2 * m * (1 - m) * J m) ^ 2 * J m) =
      2 * Real.log 2 * ((Bfun ((1 - 2 * m) ^ 2) *
        ((1 / (1 - (1 - 2 * m) ^ 2)) * (1 / (1 - (1 - 2 * m) ^ 2)))) *
        ((1 / (1 - (1 - Adiv ((1 - 2 * m) ^ 2)))) * (1 / (1 - (1 - Adiv ((1 - 2 * m) ^ 2)))) *
          (1 / (1 - (1 - Adiv ((1 - 2 * m) ^ 2)))))) := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = 1 - 2 * m := ⟨_, rfl⟩
  have hm : m = (1 - ρ) / 2 := by linarith
  subst hm
  have hρ0 : 0 < ρ := by linarith
  have hρ1 : ρ < 1 := by linarith
  have e1 : 1 - 2 * ((1 - ρ) / 2) = ρ := by ring
  rw [e1]
  simp only [sub_sub_cancel]
  have hA : Adiv (ρ ^ 2) = atanhR ρ / ρ := Adiv_of_pos hρ0
  have hB : Bfun (ρ ^ 2) = ((1 + ρ ^ 2) * Adiv (ρ ^ 2) - 1) / ρ ^ 2 := by
    unfold Bfun; rw [if_neg (not_le.mpr (by positivity))]
  have hJ : J ((1 - ρ) / 2) = 2 * atanhR ρ / Real.log 2 := by
    unfold J atanhR
    have e : (1 - (1 - ρ) / 2) / ((1 - ρ) / 2) = (1 + ρ) / (1 - ρ) := by
      have : (1 - ρ) ≠ 0 := by linarith
      field_simp; ring
    rw [e]; ring
  have hat := atanhR_pos hρ0 hρ1
  unfold Scalar.curvatureNumerator
  rw [hB, hA, hJ]
  set a := atanhR ρ with ha
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (1 - ρ) ≠ 0 := by linarith
  have h2 : (1 + ρ) ≠ 0 := by linarith
  have h3 : (1 - ρ ^ 2) ≠ 0 := by nlinarith
  have ha' : a ≠ 0 := hat.ne'
  have hρ' : ρ ≠ 0 := hρ0.ne'
  have e2 : 1 - (1 - ρ) / 2 = (1 + ρ) / 2 := by ring
  rw [e2]
  have h2' : ρ + 1 ≠ 0 := by linarith
  have h3' : 1 - ρ ^ 2 = (1 - ρ) * (1 + ρ) := by ring
  rw [h3']
  constructor
  · field_simp
    ring
  · field_simp
    ring

theorem eta_values {E : ℝ} (h0 : 0 < E) (h1 : E < 1) :
    Scalar.etaSlope E = Sfun (1 - E) ∧ Scalar.etaCurvature E = Kfun (1 - E) := by
  have hm0 : 0 < entropyInverse E := entropyInverse_pos h0 h1.le
  have hm1 : entropyInverse E < 1 / 2 := entropyInverse_lt_half h0.le h1
  have hR : Rst (1 - E) = (1 - 2 * entropyInverse E) ^ 2 := by
    unfold Rst; rw [show 1 - (1 - E) = E by ring]
  unfold Scalar.etaSlope Scalar.etaCurvature Sfun Kfun
  rw [hR]
  exact eta_alg hm0 hm1

end CKLaneN23.CT

end


