-- Prove2me | Definitions.Def_CK_CKLaneC2_Points
-- name    : CK_CKLaneC2_Points
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T15:50:35.371986+00:00
-- url     : https://prove2.me/theorems/be764b5b-1ebf-4ed3-b446-0792d55ba839
-- title:
--   Courtade–Kumar proof module `CKLaneC2.Points` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2.Points` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2.Points` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2.Points (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2/Points.lean)

import Definitions.Def_CK_CKLaneC2_Cells
import Definitions.Def_CK_CKLaneC2_Bridge

-- ===== source module CKLaneC2.Points =====
section
/-
Lane C2 — the four point conditions, as reflective checks with soundness.

All are evaluated on the point environment `envW p p = [c, E, K, A, L]` of a certified `Pt`:
  * `chkThetaLt p s` ⟹ `thetaParamReal p.c < s`       (used with c₁ = 69/5000, s = 2/25)
  * `chkThetaGt p s` ⟹ `s < thetaParamReal p.c`       (used with c_T = 23/25, s = 63/10)
  * `chkTau p U`     ⟹ `gfun x·x²/r0 ≤ U`, `x = xParamReal p.c`
  * `chkS2 p U`      ⟹ `e8Theta x < θ0 · x · p(U)`
  * `chkNpos p`      ⟹ `0 < gfun (xParamReal p.c)`
-/

set_option autoImplicit false

namespace CKLaneC2

open GeneralCK Set

def ppolyQ (U : ℚ) : ℚ := 1 - U / 3 + U ^ 2 / 5 - U ^ 3 / 7

/-- `A(1-c²)K + 2cE` over `[c, E, K, A, L]`. -/
def TnumEx : Ex :=
  .add (.mul (.mul (.var 3) (.sub (.cst 1) (.pow (.var 0) 2))) (.var 2))
    (.mul (.mul (.cst 2) (.var 0)) (.var 1))
/-- `L(1-c²)K`. -/
def denEx : Ex := .mul (.mul (.var 4) (.sub (.cst 1) (.pow (.var 0) 2))) (.var 2)
/-- `N = 2L(1-c²)²K³ - E³(2K-c²)`. -/
def NEx : Ex :=
  .sub (.mul (.mul (.mul (.cst 2) (.var 4)) (.pow (.sub (.cst 1) (.pow (.var 0) 2)) 2)) (.pow (.var 2) 3))
    (.mul (.pow (.var 1) 3) (.sub (.mul (.cst 2) (.var 2)) (.pow (.var 0) 2)))
/-- `E³(2K-c²)`. -/
def tauDenEx : Ex := .mul (.pow (.var 1) 3) (.sub (.mul (.cst 2) (.var 2)) (.pow (.var 0) 2))

def chkThetaLt (p : Pt) (s : ℚ) : Bool :=
  decide ((Ex.evalI (envW p p) (.sub TnumEx (.mul (.cst s) denEx))).hi < 0)
def chkThetaGt (p : Pt) (s : ℚ) : Bool :=
  decide ((Ex.evalI (envW p p) (.sub (.mul (.cst s) denEx) TnumEx)).hi < 0)
def chkTau (p : Pt) (U : ℚ) : Bool :=
  decide ((Ex.evalI (envW p p) (.sub NEx (.mul (.cst U) tauDenEx))).hi < 0)
def chkS2 (p : Pt) (U : ℚ) : Bool :=
  decide ((Ex.evalI (envW p p)
    (.sub (.mul TnumEx (.var 1)) (.mul (.mul (.mul (.cst 4) (.var 0)) (.cst (ppolyQ U))) denEx))).hi < 0)
def chkNpos (p : Pt) : Bool :=
  decide ((Ex.evalI (envW p p) (.sub (.cst 0) NEx)).hi < 0)

/-- Real value of a point check expression is below the certified upper end. -/
theorem point_eval_lt {p : Pt} (hp : PtFacts p) {e : Ex}
    (h : decide ((Ex.evalI (envW p p) e).hi < 0) = true) :
    Ex.evalR [(p.c : ℝ), Ef p.c, Kf p.c, Af p.c, Real.log 2] e < 0 := by
  have hmem := Ex.evalI_sound (envW_mem hp hp (le_refl _) (le_refl _)) e
  have h' : ((Ex.evalI (envW p p) e).hi : ℝ) < 0 := by exact_mod_cast (of_decide_eq_true h)
  exact lt_of_le_of_lt hmem.2 h'

theorem den_pos {c : ℝ} (h0 : 0 < c) (h1 : c < 1) : 0 < Real.log 2 * (1 - c ^ 2) * Kf c := by
  have hL := log_two_pos'
  have hK := Kf_pos h0.le h1
  have hc : (0 : ℝ) < 1 - c ^ 2 := by nlinarith
  positivity

theorem thetaParam_lt_of_chk {p : Pt} (hp : PtFacts p) {s : ℚ} (h : chkThetaLt p s = true) :
    E8AnalyticGerm.thetaParamReal p.c < s := by
  have he := point_eval_lt hp h
  simp only [TnumEx, denEx, Ex.evalR, List.getD_cons_zero, List.getD_cons_succ] at he
  push_cast at he
  have hd := den_pos hp.c_pos hp.c_lt
  rw [thetaParam_eq hp.c_pos hp.c_lt]
  have e : Af p.c / Real.log 2 + 2 * p.c * Ef p.c / (Real.log 2 * (1 - (p.c : ℝ) ^ 2) * Kf p.c)
      = (Af p.c * (1 - (p.c : ℝ) ^ 2) * Kf p.c + 2 * p.c * Ef p.c) / (Real.log 2 * (1 - (p.c : ℝ) ^ 2) * Kf p.c) := by
    have hL := log_two_pos'
    have hK := Kf_pos hp.c_pos.le hp.c_lt
    have hc : (1 : ℝ) - (p.c : ℝ) ^ 2 ≠ 0 := by nlinarith [hp.c_pos, hp.c_lt]
    field_simp
  rw [e, div_lt_iff₀ hd]
  linarith

theorem thetaParam_gt_of_chk {p : Pt} (hp : PtFacts p) {s : ℚ} (h : chkThetaGt p s = true) :
    (s : ℝ) < E8AnalyticGerm.thetaParamReal p.c := by
  have he := point_eval_lt hp h
  simp only [TnumEx, denEx, Ex.evalR, List.getD_cons_zero, List.getD_cons_succ] at he
  push_cast at he
  have hd := den_pos hp.c_pos hp.c_lt
  rw [thetaParam_eq hp.c_pos hp.c_lt]
  have e : Af p.c / Real.log 2 + 2 * p.c * Ef p.c / (Real.log 2 * (1 - (p.c : ℝ) ^ 2) * Kf p.c)
      = (Af p.c * (1 - (p.c : ℝ) ^ 2) * Kf p.c + 2 * p.c * Ef p.c) / (Real.log 2 * (1 - (p.c : ℝ) ^ 2) * Kf p.c) := by
    have hL := log_two_pos'
    have hK := Kf_pos hp.c_pos.le hp.c_lt
    have hc : (1 : ℝ) - (p.c : ℝ) ^ 2 ≠ 0 := by nlinarith [hp.c_pos, hp.c_lt]
    field_simp
  rw [e, lt_div_iff₀ hd]
  linarith

theorem tau_le_of_chk {p : Pt} (hp : PtFacts p) {U : ℚ} (h : chkTau p U = true) :
    gfun (E8AnalyticGerm.xParamReal p.c) * (E8AnalyticGerm.xParamReal p.c) ^ 2 / r0 ≤ U := by
  have he := point_eval_lt hp h
  simp only [NEx, tauDenEx, Ex.evalR, List.getD_cons_zero, List.getD_cons_succ] at he
  push_cast at he
  rw [tau_identity hp.c_pos hp.c_lt]
  have hE := Ef_pos hp.c_pos.le hp.c_lt
  have h2K := two_Kf_sub_pos hp.c_pos.le hp.c_lt
  have hd : 0 < Ef p.c ^ 3 * (2 * Kf p.c - (p.c : ℝ) ^ 2) := by positivity
  rw [div_le_iff₀ hd]
  unfold Nf
  linarith

theorem S2_of_chk {p : Pt} (hp : PtFacts p) {U : ℚ} (h : chkS2 p U = true) :
    e8Theta (E8AnalyticGerm.xParamReal p.c)
      < pureGapTheta0 * E8AnalyticGerm.xParamReal p.c * ppoly (U : ℝ) := by
  have he := point_eval_lt hp h
  simp only [TnumEx, denEx, Ex.evalR, List.getD_cons_zero, List.getD_cons_succ, ppolyQ] at he
  push_cast at he
  rw [E8AnalyticGerm.e8Theta_xParamReal hp.c_pos hp.c_lt, theta0_mul_xParam hp.c_pos hp.c_lt,
    thetaParam_eq hp.c_pos hp.c_lt]
  have hd := den_pos hp.c_pos hp.c_lt
  have hE := Ef_pos hp.c_pos.le hp.c_lt
  have hL := log_two_pos'
  have hK := Kf_pos hp.c_pos.le hp.c_lt
  have hc : (1 : ℝ) - (p.c : ℝ) ^ 2 ≠ 0 := by nlinarith [hp.c_pos, hp.c_lt]
  have e1 : Af p.c / Real.log 2 + 2 * p.c * Ef p.c / (Real.log 2 * (1 - (p.c : ℝ) ^ 2) * Kf p.c)
      = (Af p.c * (1 - (p.c : ℝ) ^ 2) * Kf p.c + 2 * p.c * Ef p.c) / (Real.log 2 * (1 - (p.c : ℝ) ^ 2) * Kf p.c) := by
    field_simp
  have e2 : 4 * (p.c : ℝ) / Ef p.c * ppoly (U : ℝ)
      = (4 * p.c * ppoly (U : ℝ) * (Real.log 2 * (1 - (p.c : ℝ) ^ 2) * Kf p.c)) /
          (Ef p.c * (Real.log 2 * (1 - (p.c : ℝ) ^ 2) * Kf p.c)) := by
    field_simp
  rw [e1, e2, div_lt_div_iff₀ hd (by positivity)]
  unfold ppoly
  nlinarith [he, hE, hd]

theorem gfun_pos_of_chk {p : Pt} (hp : PtFacts p) (h : chkNpos p = true) :
    0 < gfun (E8AnalyticGerm.xParamReal p.c) := by
  have he := point_eval_lt hp h
  simp only [NEx, Ex.evalR, List.getD_cons_zero, List.getD_cons_succ] at he
  push_cast at he
  rw [gfun_xParam hp.c_pos hp.c_lt]
  unfold Gf
  have hN : 0 < Nf p.c := by unfold Nf; linarith
  exact div_pos hN (Dnf_pos hp.c_pos hp.c_lt)

end CKLaneC2

end


