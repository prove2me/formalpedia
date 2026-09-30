-- Prove2me | Definitions.Def_CK_CKLaneM05_Checker
-- name    : CK_CKLaneM05_Checker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:43:48.110135+00:00
-- url     : https://prove2.me/theorems/6f2b5799-703f-44f5-adce-a1c27b0a8d71
-- title:
--   Courtade–Kumar proof module `CKLaneM05.Checker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM05.Checker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM05.Checker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM05.Checker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM05/Checker.lean)

import Definitions.Def_CK_CKLaneE_FastPoint
import Definitions.Def_CK_CKLaneD_FleetBase
import Definitions.Def_CK_GeneralCK_PureGapCapZeroReduction
import Definitions.Def_CK_GeneralCK_RadialContact
import Mathlib.Analysis.SpecialFunctions.Log.Base

-- ===== source module CKLaneM05.Checker =====
section

/-!
# Lane M05: archived same-side method `parent` (parent dominance) — semantic kernel

Archive (`CK_GENERAL_COMPLETION/same_side/COVER.py`, owner `'parent'`; `PROOF.md` §4 item 5):
on a leaf box of the same-side cover, with `q = 1 - 2m`,
`eta(E_up) - F(q_up, E_up) - P(I_up) ≥ 0` certifies `psi(m,E) ≤ phi(m,E)` at the parent.

Archive coordinates (root `[[0,32],[1/32,1/2],[0,1]]`):
`x = -log₂(a/b)`, `b`, `t = E / ((H a + H b)/2)`; the leaf box of a path is obtained by exact
halving (digit `d`: axis `d / 2`, side `d % 2`), exactly as `COVER.reconstruct`. Law-level
membership `InSSBox` is the canonical same-side `InS` of BRIEF §7 (image of `a = b·2^-x`, `E = t·C0`).

`check w = true` binds, for the box `ssBox w.path`:
* box sanity and the ratio enclosure `rLo ≤ 2^-x1`, `2^-x0 ≤ rHi ≤ 1` (exact `Nat` powers,
  `CKLaneD.pow2LowerOK/pow2UpperOK`);
* rational enclosures of `H` at `a_hi = rHi b1`, `a_lo = rLo b0`, `b0`, `b1`, `m_lo`, `m_hi` and of
  `log((1-v)/v)` at the witness points `u0, v2, u1` (`CKLaneE.FP.ptOk`, fixed-point atanh series);
* `E_up = t1 (Hhi(a_hi) + Hhi(b1))/2 < Hlo(m_lo)` (the common endpoint is feasible),
  `E_up ≤ Hlo(u0)`, `q_hi Hhi(v2) ≤ E_up (1 - 2 v2)` (so `v2 ≤ radialContact(q_hi, E_up)`),
  `Hhi(u1) ≤ E_lo + 1 - Hhi(m_hi)`, and
  `(1-2u1) Jh(u1) ≤ (1-2u0) Jl(u0) - q_hi Jh(v2)`.

Soundness (`check_sound`), for every interior law in the exact box:
`psi(m,E) ≤ (1-2u1)J(u1) ≤ (1-2u0)J(u0) - q_hi J(v2) ≤ eta(E_up) - F(q, E_up) = phi(m, E_up) ≤ phi(m, E)`.
The last step ("Phi decreases in E") is derived, not assumed: `phi(m,·)` is convex on `(0, H m]`
(`GeneralCK.phi_entropy_convexOn`), vanishes at the cap (`GeneralCK.phi_at_entropy_cap`), and
`phi(m, E_up) ≥ 0`, so `phi(m,E) ≥ phi(m,E_up)` for `0 < E ≤ E_up < H m`.
No real-variable enclosure, no stored margin and no `e = C t` parametrization is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM05

open GeneralCK CKLaneE.FP

/-! ## Archived same-side boxes and their law-level semantics -/

/-- A box of the archived same-side cover in archive coordinates `(x, b, t)`. -/
structure SSBox where
  x0 : ℚ
  x1 : ℚ
  b0 : ℚ
  b1 : ℚ
  t0 : ℚ
  t1 : ℚ
  deriving Repr, DecidableEq

/-- Archive root `[[0,32],[1/32,1/2],[0,1]]` (`ADAPT_RESULT.json`, key `root`). -/
def ssRoot : SSBox := ⟨0, 32, 1 / 32, 1 / 2, 0, 1⟩

/-- One exact halving step of `COVER.reconstruct` (digit `d`: axis `d / 2`, side `d % 2`). -/
def ssStep (B : SSBox) (d : ℕ) : SSBox :=
  match d with
  | 0 => { B with x1 := (B.x0 + B.x1) / 2 }
  | 1 => { B with x0 := (B.x0 + B.x1) / 2 }
  | 2 => { B with b1 := (B.b0 + B.b1) / 2 }
  | 3 => { B with b0 := (B.b0 + B.b1) / 2 }
  | 4 => { B with t1 := (B.t0 + B.t1) / 2 }
  | 5 => { B with t0 := (B.t0 + B.t1) / 2 }
  | _ => B

/-- The exact leaf box of an archived path (list of digits). -/
def ssBox (p : List ℕ) : SSBox := p.foldl ssStep ssRoot

/-- Law-level membership in the exact (closed) archived box: the canonical same-side `InS` of
BRIEF §7, field for field: `2^(-x1) ≤ a/b ≤ 2^(-x0) ∧ b0 ≤ b ≤ b1 ∧ t0*C0 ≤ E ≤ t1*C0`
(real `rpow`, `C0 = (H a + H b)/2`), i.e. the image of the archive map `a = b·2^-x`, `E = t·C0`. -/
def InSSBox (B : SSBox) (a b E : ℝ) : Prop :=
  (2 : ℝ) ^ (-(B.x1 : ℝ)) ≤ a / b ∧ a / b ≤ (2 : ℝ) ^ (-(B.x0 : ℝ)) ∧
    (B.b0 : ℝ) ≤ b ∧ b ≤ (B.b1 : ℝ) ∧
    (B.t0 : ℝ) * ((H a + H b) / 2) ≤ E ∧ E ≤ (B.t1 : ℝ) * ((H a + H b) / 2)

/-- Parent dominance on a box: `psi ≤ phi` at the parent for every interior law in the box. -/
def ParentSem (B : SSBox) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), InSSBox B μ.a μ.b μ.meanEntropy →
    psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy

/-! ## Witness and Boolean checker -/

/-- Rational literal `n / d` used to encode witness data. -/
def qq (n : ℤ) (d : ℕ) : ℚ := (n : ℚ) / (d : ℚ)

/-- Per-leaf witness: the archived path, the ratio enclosure and three rational points. -/
structure ParentWitness where
  path : List ℕ
  rLo : ℚ
  rHi : ℚ
  u0 : ℚ
  v2 : ℚ
  u1 : ℚ
  deriving Repr

def aHi (B : SSBox) (rHi : ℚ) : ℚ := rHi * B.b1
def aLo (B : SSBox) (rLo : ℚ) : ℚ := rLo * B.b0
def mLo (B : SSBox) (rLo : ℚ) : ℚ := B.b0 * (1 + rLo) / 2
def mHi (B : SSBox) (rHi : ℚ) : ℚ := B.b1 * (1 + rHi) / 2
def CHi (B : SSBox) (rHi : ℚ) : ℚ := (Hhi (aHi B rHi) + Hhi B.b1) / 2
def CLo (B : SSBox) (rLo : ℚ) : ℚ := (Hlo (aLo B rLo) + Hlo B.b0) / 2
def Eup (B : SSBox) (rHi : ℚ) : ℚ := B.t1 * CHi B rHi
def Elo (B : SSBox) (rLo : ℚ) : ℚ := B.t0 * CLo B rLo
def qHi (B : SSBox) (rLo : ℚ) : ℚ := 1 - 2 * mLo B rLo
/-- Lower bound for `J v = log((1-v)/v)/log 2` (valid when `lamLo v ≥ 0`). -/
def Jl (v : ℚ) : ℚ := lamLo v / LqHi
/-- Upper bound for `J v` (valid when `v ≤ 1/2`). -/
def Jh (v : ℚ) : ℚ := lamHi v / LqLo
def phiLo (B : SSBox) (w : ParentWitness) : ℚ :=
  (1 - 2 * w.u0) * Jl w.u0 - qHi B w.rLo * Jh w.v2
def psiHi (w : ParentWitness) : ℚ := (1 - 2 * w.u1) * Jh w.u1

/-- Box sanity and ratio enclosure. -/
def boxOk (B : SSBox) (w : ParentWitness) : Bool :=
  decide (0 ≤ B.x0 ∧ B.x0 ≤ B.x1 ∧ 0 < B.b0 ∧ B.b0 ≤ B.b1 ∧ B.b1 ≤ 1 / 2 ∧ 0 ≤ B.t0 ∧
      B.t0 ≤ B.t1 ∧ 0 < w.rLo ∧ w.rHi ≤ 1) &&
    CKLaneD.pow2LowerOK w.rLo B.x1 && CKLaneD.pow2UpperOK w.rHi B.x0

/-- Certified log/entropy enclosures exist at every point used. -/
def ptsOk (B : SSBox) (w : ParentWitness) : Bool :=
  ptOk (aHi B w.rHi) && ptOk (aLo B w.rLo) && ptOk (mLo B w.rLo) && ptOk (mHi B w.rHi) &&
    ptOk B.b0 && ptOk B.b1 && ptOk w.u0 && ptOk w.v2 && ptOk w.u1

/-- The parent-dominance inequalities, all in exact `ℚ`. -/
def ineqOk (B : SSBox) (w : ParentWitness) : Bool :=
  decide (mHi B w.rHi ≤ 1 / 2 ∧ Eup B w.rHi < Hlo (mLo B w.rLo) ∧ 0 < qHi B w.rLo ∧
    w.u0 < 1 / 2 ∧ w.v2 < 1 / 2 ∧ w.u1 < 1 / 2 ∧
    Eup B w.rHi ≤ Hlo w.u0 ∧ 0 ≤ lamLo w.u0 ∧
    qHi B w.rLo * Hhi w.v2 ≤ Eup B w.rHi * (1 - 2 * w.v2) ∧ 0 ≤ lamHi w.v2 ∧
    Hhi w.u1 ≤ Elo B w.rLo + 1 - Hhi (mHi B w.rHi) ∧
    psiHi w ≤ phiLo B w)

def checkBox (B : SSBox) (w : ParentWitness) : Bool :=
  boxOk B w && ptsOk B w && ineqOk B w

/-- The per-leaf checker: the box is recomputed from the archived path. -/
def check (w : ParentWitness) : Bool := checkBox (ssBox w.path) w

/-! ## Analytic helper lemmas -/

theorem H_le_H {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1 / 2) : H x ≤ H y :=
  H_strictMonoOn.monotoneOn ⟨hx, hxy.trans hy⟩ ⟨hx.trans hxy, hy⟩ hxy

theorem eta_H_eq {u : ℝ} (hu : 0 < u) (hu' : u ≤ 1 / 2) : eta (H u) = (1 - 2 * u) * J u := by
  rw [eta_eq_profile (H_nonneg hu.le (by linarith)) (H_le_one u), entropyInverse_H_lower hu.le hu']

theorem Jl_le {v : ℚ} (hpt : ptOk v = true) (hlam : 0 ≤ lamLo v) :
    ((Jl v : ℚ) : ℝ) ≤ J (v : ℝ) := by
  obtain ⟨hl, _⟩ := lam_bounds hpt
  obtain ⟨_, hL2⟩ := log_two_mem
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlam' : (0 : ℝ) ≤ ((lamLo v : ℚ) : ℝ) := by exact_mod_cast hlam
  unfold J
  have e : ((Jl v : ℚ) : ℝ) = ((lamLo v : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) := by
    simp only [Jl]; push_cast; ring
  rw [e]
  calc ((lamLo v : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) ≤ ((lamLo v : ℚ) : ℝ) / Real.log 2 :=
        div_le_div_of_nonneg_left hlam' hL hL2
    _ ≤ Real.log ((1 - (v : ℝ)) / v) / Real.log 2 := div_le_div_of_nonneg_right hl hL.le

theorem le_Jh {v : ℚ} (hpt : ptOk v = true) (hv12 : (v : ℝ) ≤ 1 / 2) :
    J (v : ℝ) ≤ ((Jh v : ℚ) : ℝ) := by
  obtain ⟨_, hu⟩ := lam_bounds hpt
  obtain ⟨hL1, _⟩ := log_two_mem
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (ptOk_pos hpt).1
  have hJ0 : 0 ≤ J (v : ℝ) := J_nonneg hv0 hv12
  have hlog0 : 0 ≤ Real.log ((1 - (v : ℝ)) / v) := by
    have := hJ0; unfold J at this
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hL))
  unfold J
  have e : ((Jh v : ℚ) : ℝ) = ((lamHi v : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) := by
    simp only [Jh]; push_cast; ring
  rw [e]
  calc Real.log ((1 - (v : ℝ)) / v) / Real.log 2 ≤ ((lamHi v : ℚ) : ℝ) / Real.log 2 :=
        div_le_div_of_nonneg_right hu hL.le
    _ ≤ ((lamHi v : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) :=
        div_le_div_of_nonneg_left (hlog0.trans hu) LqLo_pos hL1

/-- A convex function on `(0, c]` vanishing at `c` and nonnegative at `y < c` is
`≥ f y` on `(0, y]`. -/
theorem convex_step {f : ℝ → ℝ} {c x y : ℝ} (hconv : ConvexOn ℝ (Set.Ioc 0 c) f)
    (hx : 0 < x) (hxy : x ≤ y) (hyc : y < c) (hfc : f c = 0) (hfy : 0 ≤ f y) : f y ≤ f x := by
  rcases hxy.eq_or_lt with rfl | hlt
  · exact le_rfl
  have hcx : 0 < c - x := by linarith
  set l : ℝ := (c - y) / (c - x) with hl
  have hl0 : 0 < l := div_pos (by linarith) hcx
  have hl1 : l ≤ 1 := (div_le_one hcx).mpr (by linarith)
  have hxmem : x ∈ Set.Ioc (0 : ℝ) c := ⟨hx, by linarith⟩
  have hcmem : c ∈ Set.Ioc (0 : ℝ) c := ⟨by linarith, le_rfl⟩
  have hlcx : l * (c - x) = c - y := by rw [hl, div_mul_cancel₀ _ hcx.ne']
  have hy : l • x + (1 - l) • c = y := by
    simp only [smul_eq_mul]; linear_combination -hlcx
  have h := hconv.2 hxmem hcmem hl0.le (by linarith : (0 : ℝ) ≤ 1 - l) (by ring)
  rw [hy, smul_eq_mul, smul_eq_mul, hfc, mul_zero, add_zero] at h
  have hlfx : 0 ≤ l * f x := hfy.trans h
  have hfx : 0 ≤ f x := by
    by_contra hneg
    have : l * f x < 0 := mul_neg_of_pos_of_neg hl0 (not_le.mp hneg)
    linarith
  have : l * f x ≤ f x := by
    have := mul_le_mul_of_nonneg_right hl1 hfx
    linarith
  linarith

/-- `F` is dominated at a larger radius through a certified contact lower bound. -/
theorem F_le_of_contact {q qH E : ℝ} {v2 : ℚ} (hq0 : 0 ≤ q) (hqq : q ≤ qH) (hqH : 0 < qH)
    (hE : 0 < E) (hpt : ptOk v2 = true) (hv2 : (v2 : ℝ) < 1 / 2)
    (hcont : qH * H (v2 : ℝ) ≤ E * (1 - 2 * (v2 : ℝ))) (hlam : 0 ≤ lamHi v2) :
    F q E ≤ qH * ((Jh v2 : ℚ) : ℝ) := by
  have hv2p : (0 : ℝ) < v2 := by exact_mod_cast (ptOk_pos hpt).1
  have hJh0 : (0 : ℝ) ≤ ((Jh v2 : ℚ) : ℝ) := by
    have : (0 : ℝ) ≤ ((lamHi v2 : ℚ) : ℝ) := by exact_mod_cast hlam
    simp only [Jh]; push_cast
    exact div_nonneg this LqLo_pos.le
  have hrc : (v2 : ℝ) ≤ radialContact qH E :=
    (le_radialContact_iff hqH hE hv2p.le hv2.le).mpr hcont
  by_cases hq : q = 0
  · rw [hq]; unfold F; rw [if_pos rfl]; positivity
  · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
    unfold F; rw [if_neg hq]
    have h1 : radialContact qH E ≤ radialContact q E := radialContact_anti_radius hqpos hqq hE
    have hJ : J (radialContact q E) ≤ J (v2 : ℝ) :=
      J_antitone hv2p (radialContact_lt_half hqpos hE).le (hrc.trans h1)
    have hJ' := hJ.trans (le_Jh hpt hv2.le)
    have hJ0 : 0 ≤ J (radialContact q E) :=
      J_nonneg (radialContact_pos hqpos hE) (radialContact_lt_half hqpos hE).le
    calc q * J (radialContact q E) ≤ qH * J (radialContact q E) :=
          mul_le_mul_of_nonneg_right hqq hJ0
      _ ≤ qH * ((Jh v2 : ℚ) : ℝ) := mul_le_mul_of_nonneg_left hJ' hqH.le

/-- `eta` at a point below a certified entropy value. -/
theorem eta_ge_of_pt {h : ℝ} {u : ℚ} (hh : 0 < h) (hpt : ptOk u = true) (hu : (u : ℝ) < 1 / 2)
    (hhu : h ≤ H (u : ℝ)) (hlam : 0 ≤ lamLo u) :
    (1 - 2 * (u : ℝ)) * ((Jl u : ℚ) : ℝ) ≤ eta h := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (ptOk_pos hpt).1
  have h1 : eta (H (u : ℝ)) ≤ eta h :=
    eta_antitoneOn ⟨hh, hhu.trans (H_le_one _)⟩ ⟨hh.trans_le hhu, H_le_one _⟩ hhu
  rw [eta_H_eq hu0 hu.le] at h1
  have := mul_le_mul_of_nonneg_left (Jl_le hpt hlam) (by linarith : (0 : ℝ) ≤ 1 - 2 * (u : ℝ))
  linarith

/-- `eta` at a point above a certified entropy value. -/
theorem eta_le_of_pt {h : ℝ} {u : ℚ} (hh1 : h ≤ 1) (hpt : ptOk u = true) (hu : (u : ℝ) < 1 / 2)
    (hhu : H (u : ℝ) ≤ h) : eta h ≤ (1 - 2 * (u : ℝ)) * ((Jh u : ℚ) : ℝ) := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (ptOk_pos hpt).1
  have hu1 : (u : ℝ) < 1 := by linarith
  have hHu : 0 < H (u : ℝ) := H_pos hu0 hu1
  have h1 : eta h ≤ eta (H (u : ℝ)) :=
    eta_antitoneOn ⟨hHu, H_le_one _⟩ ⟨hHu.trans_le hhu, hh1⟩ hhu
  rw [eta_H_eq hu0 hu.le] at h1
  have := mul_le_mul_of_nonneg_left (le_Jh hpt hu.le) (by linarith : (0 : ℝ) ≤ 1 - 2 * (u : ℝ))
  linarith

/-! ## Soundness -/

theorem boxOk_spec {B : SSBox} {w : ParentWitness} (h : boxOk B w = true) :
    (0 : ℚ) ≤ B.x0 ∧ B.x0 ≤ B.x1 ∧ 0 < B.b0 ∧ B.b0 ≤ B.b1 ∧ B.b1 ≤ 1 / 2 ∧ 0 ≤ B.t0 ∧
      B.t0 ≤ B.t1 ∧ 0 < w.rLo ∧ w.rHi ≤ 1 ∧
      ((w.rLo : ℝ) ≤ (2 : ℝ) ^ (-(B.x1 : ℝ))) ∧ ((2 : ℝ) ^ (-(B.x0 : ℝ)) ≤ (w.rHi : ℝ)) := by
  simp only [boxOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hd, hl⟩, hu⟩ := h
  exact ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2.1,
    hd.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2, CKLaneD.pow2LowerOK_sound hl,
    CKLaneD.pow2UpperOK_sound hu⟩

theorem ptsOk_spec {B : SSBox} {w : ParentWitness} (h : ptsOk B w = true) :
    ptOk (aHi B w.rHi) = true ∧ ptOk (aLo B w.rLo) = true ∧ ptOk (mLo B w.rLo) = true ∧
      ptOk (mHi B w.rHi) = true ∧ ptOk B.b0 = true ∧ ptOk B.b1 = true ∧ ptOk w.u0 = true ∧
      ptOk w.v2 = true ∧ ptOk w.u1 = true := by
  simp only [ptsOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

set_option maxHeartbeats 4000000 in
theorem checkBox_sound (B : SSBox) (w : ParentWitness) (hw : checkBox B w = true) :
    ParentSem B := by
  intro k μ hin
  simp only [checkBox, Bool.and_eq_true] at hw
  obtain ⟨⟨hbox, hpts⟩, hineq⟩ := hw
  obtain ⟨_, _, hb0, _, hb1h, ht0, ht01, hrLo0, hrHi1, hrL, hrH⟩ := boxOk_spec hbox
  obtain ⟨paHi, paLo, pmLo, pmHi, pb0, pb1, pu0, pv2, pu1⟩ := ptsOk_spec hpts
  simp only [ineqOk, decide_eq_true_eq] at hineq
  obtain ⟨cmHi, cfeas, cqHi, cu0, cv2, cu1, ceta, clam0, ccont, clam2, cpsi, cfin⟩ := hineq
  -- law facts
  have ha0 : 0 < μ.a := μ.a_interior.1
  have ha1 : μ.a < 1 := μ.a_interior.2
  have hb0' : 0 < μ.b := μ.b_interior.1
  have hb1' : μ.b < 1 := μ.b_interior.2
  have hE0 : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy; linarith [μ.e_pos, μ.f_pos]
  have hEC : μ.meanEntropy ≤ (H μ.a + H μ.b) / 2 := by
    unfold InteriorLaw.meanEntropy; linarith [μ.e_le_cap, μ.f_le_cap]
  have hm_def : μ.midpoint = (μ.a + μ.b) / 2 := rfl
  have hCm : (H μ.a + H μ.b) / 2 ≤ H μ.midpoint := by
    have := μ.entropyDrop_nonneg
    unfold InteriorLaw.entropyDrop at this
    linarith
  -- box membership (canonical InS conjuncts)
  obtain ⟨hr_ge, hr_le, hB0, hB1, hEt0, hEt1⟩ := hin
  have hrHpos : (0 : ℝ) < (w.rHi : ℝ) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hrH
  have hrLpos : (0 : ℝ) < (w.rLo : ℝ) := by exact_mod_cast hrLo0
  have haH : μ.a ≤ (w.rHi : ℝ) * μ.b := by
    have := hr_le.trans hrH
    rwa [div_le_iff₀ hb0'] at this
  have haL : (w.rLo : ℝ) * μ.b ≤ μ.a := by
    have := hrL.trans hr_ge
    rwa [le_div_iff₀ hb0'] at this
  -- rational facts in ℝ
  have hb0pos : (0 : ℝ) < (B.b0 : ℝ) := by exact_mod_cast hb0
  have hb1half : (B.b1 : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hb1h; push_cast at h; exact h
  have ht0nn : (0 : ℝ) ≤ (B.t0 : ℝ) := by exact_mod_cast ht0
  have ht1nn : (0 : ℝ) ≤ (B.t1 : ℝ) := by exact_mod_cast ht0.trans ht01
  have hrHle1 : (w.rHi : ℝ) ≤ 1 := by exact_mod_cast hrHi1
  have hb1nn : (0 : ℝ) ≤ (B.b1 : ℝ) := hb0'.le.trans hB1
  have ha_half : μ.a ≤ 1 / 2 := by nlinarith
  have hb_half : μ.b ≤ 1 / 2 := hB1.trans hb1half
  -- casts of derived rationals
  have c_aHi : ((aHi B w.rHi : ℚ) : ℝ) = (w.rHi : ℝ) * (B.b1 : ℝ) := by
    unfold aHi; push_cast; ring
  have c_aLo : ((aLo B w.rLo : ℚ) : ℝ) = (w.rLo : ℝ) * (B.b0 : ℝ) := by
    unfold aLo; push_cast; ring
  have c_mLo : ((mLo B w.rLo : ℚ) : ℝ) = (B.b0 : ℝ) * (1 + (w.rLo : ℝ)) / 2 := by
    unfold mLo; push_cast; ring
  have c_mHi : ((mHi B w.rHi : ℚ) : ℝ) = (B.b1 : ℝ) * (1 + (w.rHi : ℝ)) / 2 := by
    unfold mHi; push_cast; ring
  have c_CHi : ((CHi B w.rHi : ℚ) : ℝ) =
      (((Hhi (aHi B w.rHi) : ℚ) : ℝ) + ((Hhi B.b1 : ℚ) : ℝ)) / 2 := by
    unfold CHi; push_cast; ring
  have c_CLo : ((CLo B w.rLo : ℚ) : ℝ) =
      (((Hlo (aLo B w.rLo) : ℚ) : ℝ) + ((Hlo B.b0 : ℚ) : ℝ)) / 2 := by
    unfold CLo; push_cast; ring
  have c_Eup : ((Eup B w.rHi : ℚ) : ℝ) = (B.t1 : ℝ) * ((CHi B w.rHi : ℚ) : ℝ) := by
    unfold Eup; push_cast; ring
  have c_Elo : ((Elo B w.rLo : ℚ) : ℝ) = (B.t0 : ℝ) * ((CLo B w.rLo : ℚ) : ℝ) := by
    unfold Elo; push_cast; ring
  have c_qHi : ((qHi B w.rLo : ℚ) : ℝ) = 1 - 2 * ((mLo B w.rLo : ℚ) : ℝ) := by
    unfold qHi; push_cast; ring
  -- a, b, m enclosures
  have ha_le_aHi : μ.a ≤ ((aHi B w.rHi : ℚ) : ℝ) := by
    rw [c_aHi]
    calc μ.a ≤ (w.rHi : ℝ) * μ.b := haH
      _ ≤ (w.rHi : ℝ) * (B.b1 : ℝ) := mul_le_mul_of_nonneg_left hB1 hrHpos.le
  have haHi_half : ((aHi B w.rHi : ℚ) : ℝ) ≤ 1 / 2 := by
    rw [c_aHi]
    calc (w.rHi : ℝ) * (B.b1 : ℝ) ≤ 1 * (B.b1 : ℝ) := mul_le_mul_of_nonneg_right hrHle1 hb1nn
      _ ≤ 1 / 2 := by linarith
  have haLo_le : ((aLo B w.rLo : ℚ) : ℝ) ≤ μ.a := by
    rw [c_aLo]
    calc (w.rLo : ℝ) * (B.b0 : ℝ) ≤ (w.rLo : ℝ) * μ.b := mul_le_mul_of_nonneg_left hB0 hrLpos.le
      _ ≤ μ.a := haL
  have haLo_nn : (0 : ℝ) ≤ ((aLo B w.rLo : ℚ) : ℝ) := by rw [c_aLo]; positivity
  have hmLo_le : ((mLo B w.rLo : ℚ) : ℝ) ≤ μ.midpoint := by
    rw [c_mLo, hm_def]
    have := mul_le_mul_of_nonneg_left hB0 hrLpos.le
    linarith
  have hmHi_ge : μ.midpoint ≤ ((mHi B w.rHi : ℚ) : ℝ) := by
    rw [c_mHi, hm_def]
    have := mul_le_mul_of_nonneg_left hB1 hrHpos.le
    linarith
  have hmHi_half : ((mHi B w.rHi : ℚ) : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr cmHi; push_cast at h; exact h
  have hm_pos : 0 < μ.midpoint := by rw [hm_def]; linarith
  have hm_half : μ.midpoint ≤ 1 / 2 := hmHi_ge.trans hmHi_half
  have hmLo_nn : (0 : ℝ) ≤ ((mLo B w.rLo : ℚ) : ℝ) := by rw [c_mLo]; positivity
  -- entropy enclosures
  obtain ⟨_, HaHi⟩ := H_bounds paHi
  obtain ⟨HaLo, _⟩ := H_bounds paLo
  obtain ⟨HmLo, _⟩ := H_bounds pmLo
  obtain ⟨_, HmHi⟩ := H_bounds pmHi
  obtain ⟨Hb0, _⟩ := H_bounds pb0
  obtain ⟨_, Hb1⟩ := H_bounds pb1
  have hHa_up : H μ.a ≤ ((Hhi (aHi B w.rHi) : ℚ) : ℝ) :=
    (H_le_H ha0.le ha_le_aHi haHi_half).trans HaHi
  have hHb_up : H μ.b ≤ ((Hhi B.b1 : ℚ) : ℝ) := (H_le_H hb0'.le hB1 hb1half).trans Hb1
  have hHa_lo : ((Hlo (aLo B w.rLo) : ℚ) : ℝ) ≤ H μ.a :=
    HaLo.trans (H_le_H haLo_nn haLo_le ha_half)
  have hHb_lo : ((Hlo B.b0 : ℚ) : ℝ) ≤ H μ.b := Hb0.trans (H_le_H hb0pos.le hB0 hb_half)
  have hHm_up : H μ.midpoint ≤ ((Hhi (mHi B w.rHi) : ℚ) : ℝ) :=
    (H_le_H hm_pos.le hmHi_ge hmHi_half).trans HmHi
  have hHm_lo : ((Hlo (mLo B w.rLo) : ℚ) : ℝ) ≤ H μ.midpoint :=
    HmLo.trans (H_le_H hmLo_nn hmLo_le hm_half)
  -- entropy range of the box
  have hE_le_Eup : μ.meanEntropy ≤ ((Eup B w.rHi : ℚ) : ℝ) := by
    have hC : (H μ.a + H μ.b) / 2 ≤ ((CHi B w.rHi : ℚ) : ℝ) := by rw [c_CHi]; linarith
    rw [c_Eup]
    exact hEt1.trans (mul_le_mul_of_nonneg_left hC ht1nn)
  have hElo_le : ((Elo B w.rLo : ℚ) : ℝ) ≤ μ.meanEntropy := by
    have hC : ((CLo B w.rLo : ℚ) : ℝ) ≤ (H μ.a + H μ.b) / 2 := by rw [c_CLo]; linarith
    rw [c_Elo]
    exact (mul_le_mul_of_nonneg_left hC ht0nn).trans hEt0
  have hEup_pos : (0 : ℝ) < ((Eup B w.rHi : ℚ) : ℝ) := hE0.trans_le hE_le_Eup
  have hEup_lt : ((Eup B w.rHi : ℚ) : ℝ) < H μ.midpoint := by
    have h := (Rat.cast_lt (K := ℝ)).mpr cfeas
    exact h.trans_le hHm_lo
  have hEm : μ.meanEntropy ≤ H μ.midpoint := hEC.trans hCm
  -- radius
  have hq_eq : |1 - 2 * μ.midpoint| = 1 - 2 * μ.midpoint := abs_of_nonneg (by linarith)
  have hqHi_pos : (0 : ℝ) < ((qHi B w.rLo : ℚ) : ℝ) := by exact_mod_cast cqHi
  have hq_le : |1 - 2 * μ.midpoint| ≤ ((qHi B w.rLo : ℚ) : ℝ) := by
    rw [hq_eq, c_qHi]; linarith
  -- rational witness-point facts in ℝ
  have cast_lt_half : ∀ {x : ℚ}, x < 1 / 2 → (x : ℝ) < 1 / 2 := by
    intro x hx
    have h := (Rat.cast_lt (K := ℝ)).mpr hx
    push_cast at h; linarith
  have hu0R := cast_lt_half cu0
  have hv2R := cast_lt_half cv2
  have hu1R := cast_lt_half cu1
  -- (i) eta(E_up) ≥ (1-2u0) Jl(u0)
  have i1 : (1 - 2 * (w.u0 : ℝ)) * ((Jl w.u0 : ℚ) : ℝ) ≤ eta ((Eup B w.rHi : ℚ) : ℝ) := by
    obtain ⟨Hu0, _⟩ := H_bounds pu0
    have h := (Rat.cast_le (K := ℝ)).mpr ceta
    exact eta_ge_of_pt hEup_pos pu0 hu0R (h.trans Hu0) clam0
  -- (ii) F(q, E_up) ≤ qHi Jh(v2)
  have i2 : F |1 - 2 * μ.midpoint| ((Eup B w.rHi : ℚ) : ℝ) ≤
      ((qHi B w.rLo : ℚ) : ℝ) * ((Jh w.v2 : ℚ) : ℝ) := by
    obtain ⟨_, Hv2⟩ := H_bounds pv2
    have h := (Rat.cast_le (K := ℝ)).mpr ccont
    push_cast at h
    have hcont : ((qHi B w.rLo : ℚ) : ℝ) * H (w.v2 : ℝ) ≤
        ((Eup B w.rHi : ℚ) : ℝ) * (1 - 2 * (w.v2 : ℝ)) :=
      (mul_le_mul_of_nonneg_left Hv2 hqHi_pos.le).trans h
    exact F_le_of_contact (abs_nonneg _) hq_le hqHi_pos hEup_pos pv2 hv2R hcont clam2
  -- (iii) psi(m,E) ≤ (1-2u1) Jh(u1)
  have i3 : psi μ.midpoint μ.meanEntropy ≤ (1 - 2 * (w.u1 : ℝ)) * ((Jh w.u1 : ℚ) : ℝ) := by
    obtain ⟨_, Hu1⟩ := H_bounds pu1
    have h := (Rat.cast_le (K := ℝ)).mpr cpsi
    push_cast at h
    unfold psi
    apply eta_le_of_pt (by linarith) pu1 hu1R
    linarith
  -- final rational comparison
  have hfin : (1 - 2 * (w.u1 : ℝ)) * ((Jh w.u1 : ℚ) : ℝ) ≤
      (1 - 2 * (w.u0 : ℝ)) * ((Jl w.u0 : ℚ) : ℝ) -
        ((qHi B w.rLo : ℚ) : ℝ) * ((Jh w.v2 : ℚ) : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr cfin
    simp only [psiHi, phiLo] at h
    push_cast at h
    exact h
  have hpsi0 : 0 ≤ (1 - 2 * (w.u1 : ℝ)) * ((Jh w.u1 : ℚ) : ℝ) := by
    have hu1p : (0 : ℝ) < w.u1 := by exact_mod_cast (ptOk_pos pu1).1
    have hJ0 := J_nonneg hu1p hu1R.le
    have hJh := le_Jh pu1 hu1R.le
    have : (0 : ℝ) ≤ 1 - 2 * (w.u1 : ℝ) := by linarith
    exact mul_nonneg this (hJ0.trans hJh)
  -- phi at the upper entropy endpoint
  have hphiUp : (1 - 2 * (w.u0 : ℝ)) * ((Jl w.u0 : ℚ) : ℝ) -
      ((qHi B w.rLo : ℚ) : ℝ) * ((Jh w.v2 : ℚ) : ℝ) ≤
      phi μ.midpoint ((Eup B w.rHi : ℚ) : ℝ) := by
    unfold phi; linarith
  have hphiUp0 : 0 ≤ phi μ.midpoint ((Eup B w.rHi : ℚ) : ℝ) := by linarith
  -- Phi decreases in E below the cap (convexity + zero at the cap)
  have hconv := phi_entropy_convexOn hm_pos (by linarith : μ.midpoint < 1)
  have hcap := phi_at_entropy_cap hm_pos hm_half
  have hmono : phi μ.midpoint ((Eup B w.rHi : ℚ) : ℝ) ≤ phi μ.midpoint μ.meanEntropy :=
    convex_step hconv hE0 hE_le_Eup hEup_lt hcap hphiUp0
  linarith

/-- **Soundness.** `check w = true` alone gives parent dominance on the exact archived box. -/
theorem check_sound (w : ParentWitness) (h : check w = true) : ParentSem (ssBox w.path) :=
  checkBox_sound (ssBox w.path) w h

/-- Owner form for the consumers' psi-active premise: on a parent-dominance box the premise
`phi < psi` is contradictory, so any conclusion holds (here `μ.gap ≤ μ.cost`). -/
theorem gap_le_cost_of_parentSem {B : SSBox} (hB : ParentSem B) (k : ℕ) (μ : InteriorLaw (Fin k))
    (hin : InSSBox B μ.a μ.b μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy) : μ.gap ≤ μ.cost :=
  absurd hactive (not_lt.mpr (hB k μ hin))

end CKLaneM05

#check @CKLaneM05.check_sound
#check @CKLaneM05.checkBox_sound
#check @CKLaneM05.convex_step
#print axioms CKLaneM05.check_sound
#print axioms CKLaneM05.gap_le_cost_of_parentSem

end


