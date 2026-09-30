-- Prove2me | Definitions.Def_CK_CKLaneR2_Tail_Chart
-- name    : CK_CKLaneR2_Tail_Chart
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:19:32.783339+00:00
-- url     : https://prove2.me/theorems/c36fec14-40fc-4e27-8b94-40619b963663
-- title:
--   Courtade–Kumar proof module `CKLaneR2.Tail.Chart` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneR2.Tail.Chart` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneR2.Tail.Chart` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneR2.Tail.Chart (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneR2/Tail/Chart.lean)

import Definitions.Def_CK_CKLaneR2_Tail_SoundCellThm

-- ===== source module CKLaneR2.Tail.Chart =====
section

/-!
# Lane R2b — u-tail: chart semantics, Boolean domain checks, front soundness (`FOK`) and coordinate inversion

* b-chart (`BChart`): exponential `b = (bc/one) exp(-(bN/bD) x)` or linear `b = (bc + bh x)/one`.
* S-front (`frontS`): `σ = (sc/one) exp(-(shN/shD) z)`, `u = b σ`; the semantics `semS` uses the true functions of `u`.
* L-front (`frontL`): `λ = (lh + lh z)/one ∈ [0, 2 lh/one]`, `u = exp(-1/λ)` (`u = 0` at `λ = 0`); `u`, `u ln(1/u)`,
  `-ln(1-u)`, `g1 u` are noise constants whose ranges are certified by scalar-log checks.
* `domS` / `domL`: Boolean chart/box checks (decided by the kernel together with `tailCheck`).
* `fokS` / `fokL`: the checks imply `FOK (frontS c) (semS c)` / `FOK (frontL c) (semL c)`.
* `b_coord`, `lin_coord`, `exp_coord`, `lamL_coord`: every point of the integer box has chart coordinates in `[-1,1]`.
-/

namespace CKLaneR2.Tail

open CKLaneR2.TM3 CKLaneR2.Cell GeneralCK

/-! ## Boolean domain checks -/

/-- `2 d² + 2 n d + n² = 2 d² (1 + r + r²/2)` for `r = n/d`. -/
def quadN (n d : ℕ) : Int := 2 * (d : Int) ^ 2 + 2 * (n : Int) * d + (n : Int) ^ 2

/-- Precondition of `logScalar_sound`. -/
noncomputable def lsOK (k : ℕ) : Bool := decide (0 < k) && decide (2 * (logScalarEY P k).2.natAbs ≤ one)

/-- The exp chart `c/one · exp(-(n/d) w)`, `w ∈ [-1,1]`, covers `[lo/one, hi/one]` (`1 + r + r²/2 ≤ exp r`). -/
noncomputable def expBoxOK (c : Int) (n d : ℕ) (lo hi : Int) : Bool :=
  decide (0 < c) && decide (0 < n) && decide (n ≤ d) && decide (n * one % d = 0)
    && decide (c * (2 * (d : Int) ^ 2) ≤ lo * quadN n d) && decide (hi * (2 * (d : Int) ^ 2) ≤ c * quadN n d)
    && lsOK c.toNat

/-- The linear chart `(c + h w)/one`, `w ∈ [-1,1]`, has the endpoints `lo`, `hi`. -/
def linBoxOK (c h lo hi : Int) : Bool := decide (c - h = lo) && decide (c + h = hi) && decide (0 ≤ h)

/-- b-chart check against the box `[b0, b1]`, plus `0 < b ≤ 1/2` on the whole chart (TM bounds). -/
noncomputable def bDomOK (c : BChart) (b0 b1 : Int) : Bool :=
  (if c.bexp then expBoxOK c.bc c.bN c.bD b0 b1 else linBoxOK c.bc c.bh b0 b1)
    && (frontB c).1.ok && decide (0 < (frontB c).1.lower) && decide (2 * (frontB c).1.upper ≤ ONEi)

noncomputable def tDomOK (tc th t0 t1 : Int) : Bool :=
  linBoxOK tc th t0 t1 && decide (0 ≤ t0) && decide (t1 ≤ ONEi)

/-- S-cell chart/box check. -/
noncomputable def domS (c : SCell) (b0 b1 t0 t1 s0 s1 : Int) : Bool :=
  bDomOK c.bch b0 b1 && tDomOK c.tc c.th t0 t1 && expBoxOK c.sc c.shN c.shD s0 s1 && decide (2 * c.sc ≤ ONEi)

/-- `⌈b1 s1 / one⌉`: `u = bσ ≤ b1 s1/one² ≤ kBox/one` on the box. -/
noncomputable def kBox (b1 s1 : Int) : ℕ := cdiv (b1 * s1).toNat one

noncomputable def lhI (c : LCell) : Int := (((c.lam1 + 1) / 2 : ℕ) : Int)

/-- L-cell chart/box check (`s0` is irrelevant: the L chart covers every `σ ∈ (0, s1]`). -/
noncomputable def domL (c : LCell) (b0 b1 t0 t1 s1 : Int) : Bool :=
  bDomOK c.bch b0 b1 && tDomOK c.tc c.th t0 t1 && decide (0 < s1) && decide (0 < lhI c)
    && lsOK c.u1 && lsOK (kBox b1 s1)
    && decide ((((logScalar P c.u1).2 : Int) - (logScalar P c.u1).1) * (2 * lhI c) ≤ ONEi * ONEi)
    && decide (ONEi * ONEi ≤ -((logScalar P (kBox b1 s1)).1 + ((logScalar P (kBox b1 s1)).2 : Int)) * (2 * lhI c))
    && decide (3 * c.u1 ≤ one) && decide (c.u1 ≤ 2 * ((c.u1 + 1) / 2))
    && decide ((c.u1 : Int) * (((logScalar P c.u1).2 : Int) - (logScalar P c.u1).1)
        ≤ 2 * (((c.w1 + 1) / 2 : ℕ) : Int) * ONEi)

/-! ## Chart functions -/

noncomputable def expF (c : Int) (n d : ℕ) (w : ℝ) : ℝ := (c : ℝ) / one * Real.exp (-((n : ℝ) / d) * w)

noncomputable def linF (c h : Int) (w : ℝ) : ℝ := ((c : ℝ) + h * w) / one

noncomputable def bF (c : BChart) (x : ℝ) : ℝ := if c.bexp then expF c.bc c.bN c.bD x else linF c.bc c.bh x

/-! ## Scalar facts -/

theorem one_cast_pow : ((one : ℕ) : ℝ) = (2 : ℝ) ^ P := by
  unfold one; push_cast; rfl

theorem logScalar_enc {k : ℕ} (h : lsOK k = true) :
    |Real.log ((k : ℝ) / one) - ((logScalar P k).1 : ℝ) / one| ≤ ((logScalar P k).2 : ℝ) / one := by
  simp only [lsOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have hy : 2 * (logScalarEY P k).2.natAbs ≤ 2 ^ P := by have := h.2; unfold one at this; exact this
  have hs := logScalar_sound P hP k h.1 hy
  rw [one_cast_pow]
  have hP0 : (0 : ℝ) < 2 ^ P := by positivity
  rw [abs_sub_comm]
  rw [show ((logScalar P k).1 : ℝ) / 2 ^ P - Real.log ((k : ℝ) / 2 ^ P)
      = (((logScalar P k).1 : ℝ) - 2 ^ P * Real.log ((k : ℝ) / 2 ^ P)) / 2 ^ P by field_simp]
  rw [abs_div, abs_of_pos hP0]
  exact div_le_div_of_nonneg_right hs hP0.le

theorem logScalar_encI {c : Int} (hc : 0 < c) (h : lsOK c.toNat = true) :
    |Real.log ((c : ℝ) / one) - ((logScalar P c.toNat).1 : ℝ) / one| ≤ ((logScalar P c.toNat).2 : ℝ) / one := by
  have e : ((c.toNat : ℕ) : ℝ) = (c : ℝ) := by
    have : ((c.toNat : ℤ)) = c := Int.toNat_of_nonneg hc.le
    exact_mod_cast this
  have := logScalar_enc h
  rwa [e] at this

theorem rate_eq {n d : ℕ} (hd : 0 < d) (h : n * one % d = 0) :
    ((rateI n d : ℤ) : ℝ) / one = (n : ℝ) / d := by
  unfold rateI
  have hdvd : d ∣ n * one := Nat.dvd_of_mod_eq_zero h
  have e : ((n * one / d : ℕ) : ℝ) = (n : ℝ) * one / d := by
    rw [Nat.cast_div hdvd (by exact_mod_cast hd.ne')]; push_cast; ring
  rw [Int.cast_natCast, e]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hne1 : (one : ℝ) ≠ 0 := hne
  field_simp

theorem ONEi_real' : ((ONEi : ℤ) : ℝ) = (one : ℝ) := by unfold ONEi; rw [Int.cast_natCast]

theorem C_constF (c : Int) (r : ℕ) (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → |f x y z - (c : ℝ) / one| ≤ (r : ℝ) / one) :
    Contains one (TM.const c r) f := by
  intro _ x y z hx hy hz
  have : evalP 0 (TM.const c r).p x y z = c := by simp [TM.const, evalP, evalC, evalR]
  rw [this]; exact hf x y z hx hy hz

theorem abs_sub_le_of_mem {v a r : ℝ} (h0 : a - r ≤ v) (h1 : v ≤ a + r) : |v - a| ≤ r := by
  rw [abs_le]; constructor <;> linarith

theorem w_nonneg {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : 0 ≤ u * (-Real.log u) :=
  mul_nonneg h0 (by have := Real.log_nonpos h0 h1; linarith)

theorem cq_nonneg {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) : 0 ≤ -Real.log (1 - u) := by
  have := Real.log_nonpos (by linarith : (0 : ℝ) ≤ 1 - u) (by linarith); linarith

theorem hu_le_of {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    (u * (-Real.log u) + (1 - u) * (-Real.log (1 - u))) * (1 / Real.log 2) ≤ 1 := by
  rcases h0.eq_or_lt with h | h
  · subst h; simp
  · have := H_le_one u
    rw [H_logs h h1] at this
    rw [mul_one_div]; exact this

/-! ## b-chart -/

theorem expF_pos {c : Int} (hc : 0 < c) (n d : ℕ) (w : ℝ) : 0 < expF c n d w := by
  unfold expF
  exact mul_pos (div_pos (by exact_mod_cast hc) hone') (Real.exp_pos _)

theorem log_expF {c : Int} (hc : 0 < c) (n d : ℕ) (w : ℝ) :
    Real.log (expF c n d w) = Real.log ((c : ℝ) / one) - (n : ℝ) / d * w := by
  unfold expF
  rw [Real.log_mul (div_pos (by exact_mod_cast hc) hone').ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

theorem expBoxOK_parts {c : Int} {n d : ℕ} {lo hi : Int} (h : expBoxOK c n d lo hi = true) :
    0 < c ∧ 0 < n ∧ n ≤ d ∧ n * one % d = 0 ∧ c * (2 * (d : Int) ^ 2) ≤ lo * quadN n d ∧
      hi * (2 * (d : Int) ^ 2) ≤ c * quadN n d ∧ lsOK c.toNat = true := by
  simp only [expBoxOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem linBoxOK_parts {c h lo hi : Int} (hb : linBoxOK c h lo hi = true) : c - h = lo ∧ c + h = hi ∧ 0 ≤ h := by
  simp only [linBoxOK, Bool.and_eq_true, decide_eq_true_eq] at hb
  exact ⟨hb.1.1, hb.1.2, hb.2⟩

theorem expPolyx_contains' {c : Int} {n d : ℕ} {lo hi : Int} (h : expBoxOK c n d lo hi = true) :
    Contains one (expPolyTMx c n d) (fun x _ _ => expF c n d x) := by
  obtain ⟨hc, hn, hnd, _, _, _, _⟩ := expBoxOK_parts h
  exact expPolyx_contains c n d hc (by omega) hnd

theorem expPoly_contains' {c : Int} {n d : ℕ} {lo hi : Int} (h : expBoxOK c n d lo hi = true) :
    Contains one (expPolyTM c n d) (fun _ _ z => expF c n d z) := by
  obtain ⟨hc, hn, hnd, _, _, _, _⟩ := expBoxOK_parts h
  exact expPoly_contains c n d hc (by omega) hnd

theorem lin_contains_x (c h : Int) : Contains one (TM.lin c h 0 0) (fun x _ _ => linF c h x) :=
  Contains.congr (Contains.lin c h 0 0) (fun x y z _ _ _ => by unfold linF; push_cast; ring)

theorem lin_contains_y (c h : Int) : Contains one (TM.lin c 0 h 0) (fun _ y _ => linF c h y) :=
  Contains.congr (Contains.lin c 0 h 0) (fun x y z _ _ _ => by unfold linF; push_cast; ring)

theorem frontB_contains (c : BChart) {b0 b1 : Int} (h : bDomOK c b0 b1 = true) :
    Contains one (frontB c).1 (fun x _ _ => bF c x) ∧
      Contains one (frontB c).2 (fun x _ _ => Real.log (bF c x)) := by
  simp only [bDomOK, Bool.and_eq_true] at h
  have hch := h.1.1.1
  rcases c with ⟨bexp, bc, bh, bN, bD⟩
  cases bexp with
  | true =>
    simp only [↓reduceIte] at hch
    obtain ⟨hc, hn, hnd, hmod, _, _, hls⟩ := expBoxOK_parts hch
    have hd : 0 < bD := by omega
    refine ⟨?_, ?_⟩
    · simp only [frontB, bF, ↓reduceIte]
      exact expPolyx_contains' hch
    · simp only [frontB, bF, ↓reduceIte]
      have hk := Contains.const (logScalar P bc.toNat).1 (logScalar P bc.toNat).2 (Real.log ((bc : ℝ) / one))
        (logScalar_encI hc hls)
      have hl := Contains.add hk (Contains.lin 0 (-(rateI bN bD)) 0 0)
      refine Contains.congr hl (fun x y z _ _ _ => ?_)
      rw [log_expF hc]
      have hr := rate_eq hd hmod
      have e : ((rateI bN bD : ℤ) : ℝ) * x / one = (bN : ℝ) / bD * x := by
        rw [mul_div_right_comm, hr]
      push_cast
      linear_combination (-1 : ℝ) * e
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hch
    refine ⟨?_, ?_⟩
    · simp only [frontB, bF, Bool.false_eq_true, ↓reduceIte]
      exact lin_contains_x bc bh
    · simp only [frontB, bF, Bool.false_eq_true, ↓reduceIte]
      exact C_log (lin_contains_x bc bh)

theorem bF_bounds (c : BChart) {b0 b1 : Int} (h : bDomOK c b0 b1 = true) (x : ℝ) (hx : |x| ≤ 1) :
    0 < bF c x ∧ bF c x ≤ 1 / 2 := by
  have hB := (frontB_contains c h).1
  simp only [bDomOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, hok⟩, hlo⟩, hup⟩ := h
  have h0 : |(0 : ℝ)| ≤ 1 := by simp
  have l1 := Contains.lower_le hone hB hok x 0 0 hx h0 h0
  have l2 := Contains.le_upper hone hB hok x 0 0 hx h0 h0
  constructor
  · have : (0 : ℝ) < ((frontB c).1.lower : ℝ) / one := div_pos (by exact_mod_cast hlo) hone'
    linarith
  · have hu : (2 * ((frontB c).1.upper : ℝ)) ≤ (one : ℝ) := by
      have := (show ((2 * (frontB c).1.upper : ℤ) : ℝ) ≤ ((ONEi : ℤ) : ℝ) by exact_mod_cast hup)
      push_cast at this; rwa [ONEi_real'] at this
    have : ((frontB c).1.upper : ℝ) / one ≤ 1 / 2 := by
      rw [div_le_iff₀ hone']; linarith
    linarith

theorem tDom_parts {tc th t0 t1 : Int} (h : tDomOK tc th t0 t1 = true) :
    tc - th = t0 ∧ tc + th = t1 ∧ 0 ≤ th ∧ 0 ≤ t0 ∧ t1 ≤ ONEi := by
  simp only [tDomOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hl, h0⟩, h1⟩ := h
  obtain ⟨e1, e2, e3⟩ := linBoxOK_parts hl
  exact ⟨e1, e2, e3, h0, h1⟩

theorem tF_bounds {tc th t0 t1 : Int} (h : tDomOK tc th t0 t1 = true) (y : ℝ) (hy : |y| ≤ 1) :
    0 ≤ linF tc th y ∧ linF tc th y ≤ 1 := by
  obtain ⟨e1, e2, e3, h0, h1⟩ := tDom_parts h
  have hth : (0 : ℝ) ≤ th := by exact_mod_cast e3
  have hyl := (abs_le.mp hy)
  have hlo : (0 : ℝ) ≤ (tc : ℝ) - th := by
    have : (0 : ℤ) ≤ tc - th := by omega
    exact_mod_cast this
  have hhi : (tc : ℝ) + th ≤ (one : ℝ) := by
    have : ((tc + th : ℤ) : ℝ) ≤ ((ONEi : ℤ) : ℝ) := by exact_mod_cast (show tc + th ≤ ONEi by omega)
    push_cast at this; rwa [ONEi_real'] at this
  unfold linF
  constructor
  · apply div_nonneg _ hone'.le
    nlinarith [mul_le_mul_of_nonneg_left hyl.1 hth]
  · rw [div_le_one hone']
    nlinarith [mul_le_mul_of_nonneg_left hyl.2 hth]

/-! ## Coordinate inversion -/

theorem lin_coord {c h lo hi : Int} (hb : linBoxOK c h lo hi = true) {v : ℝ} (hlo : (lo : ℝ) / one ≤ v)
    (hhi : v ≤ (hi : ℝ) / one) : ∃ w : ℝ, |w| ≤ 1 ∧ linF c h w = v := by
  obtain ⟨e1, e2, e3⟩ := linBoxOK_parts hb
  have hlo' : (lo : ℝ) ≤ v * one := by rwa [div_le_iff₀ hone'] at hlo
  have hhi' : v * one ≤ (hi : ℝ) := by rwa [le_div_iff₀ hone'] at hhi
  have el : (lo : ℝ) = (c : ℝ) - h := by rw [← e1]; push_cast; ring
  have eh : (hi : ℝ) = (c : ℝ) + h := by rw [← e2]; push_cast; ring
  rcases e3.eq_or_lt with h0 | hpos
  · refine ⟨0, by simp, ?_⟩
    have h0' : (h : ℝ) = 0 := by exact_mod_cast h0.symm
    rw [el, h0'] at hlo'; rw [eh, h0'] at hhi'
    unfold linF; rw [h0', mul_zero, add_zero, div_eq_iff hne]
    linarith
  · have hp : (0 : ℝ) < h := by exact_mod_cast hpos
    have hne1 : (one : ℝ) ≠ 0 := hne
    have hh0 : (h : ℝ) ≠ 0 := hp.ne'
    refine ⟨(v * one - c) / h, ?_, ?_⟩
    · rw [abs_div, abs_of_pos hp, div_le_one hp, abs_le]
      constructor <;> linarith
    · unfold linF
      field_simp
      try ring

theorem quad_le_exp_rat {n d : ℕ} (hd : 0 < d) :
    ((quadN n d : ℤ) : ℝ) / (2 * (d : ℝ) ^ 2) ≤ Real.exp ((n : ℝ) / d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hq := Real.quadratic_le_exp_of_nonneg (div_nonneg (Nat.cast_nonneg n) hd'.le)
  have e : ((quadN n d : ℤ) : ℝ) / (2 * (d : ℝ) ^ 2) = 1 + (n : ℝ) / d + ((n : ℝ) / d) ^ 2 / 2 := by
    unfold quadN; push_cast; field_simp
  rw [e]; exact hq

theorem exp_coord {c : Int} {n d : ℕ} {lo hi : Int} (hb : expBoxOK c n d lo hi = true) {v : ℝ}
    (hlo : (lo : ℝ) / one ≤ v) (hhi : v ≤ (hi : ℝ) / one) : ∃ w : ℝ, |w| ≤ 1 ∧ expF c n d w = v := by
  obtain ⟨hc, hn, hnd, _, hL, hH, _⟩ := expBoxOK_parts hb
  have hd : 0 < d := by omega
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  set r : ℝ := (n : ℝ) / d with hr
  have hr0 : 0 < r := div_pos hn' hd'
  set Q : ℝ := ((quadN n d : ℤ) : ℝ) with hQ
  have hD : (0 : ℝ) < 2 * (d : ℝ) ^ 2 := by positivity
  have hQpos : 0 < Q := by
    rw [hQ]; unfold quadN; push_cast; positivity
  have hqe : Q / (2 * (d : ℝ) ^ 2) ≤ Real.exp r := quad_le_exp_rat hd
  have hL' : (c : ℝ) * (2 * (d : ℝ) ^ 2) ≤ (lo : ℝ) * Q := by
    have := (show ((c * (2 * (d : Int) ^ 2) : ℤ) : ℝ) ≤ ((lo * quadN n d : ℤ) : ℝ) by exact_mod_cast hL)
    push_cast at this; rw [hQ]; exact this
  have hH' : (hi : ℝ) * (2 * (d : ℝ) ^ 2) ≤ (c : ℝ) * Q := by
    have := (show ((hi * (2 * (d : Int) ^ 2) : ℤ) : ℝ) ≤ ((c * quadN n d : ℤ) : ℝ) by exact_mod_cast hH)
    push_cast at this; rw [hQ]; exact this
  -- v ∈ [(c/one) e^{-r}, (c/one) e^{r}]
  set k : ℝ := (c : ℝ) / one with hk
  have hk0 : 0 < k := div_pos hc' hone'
  have hlo2 : k * (2 * (d : ℝ) ^ 2) / Q ≤ v := by
    calc k * (2 * (d : ℝ) ^ 2) / Q = ((c : ℝ) * (2 * (d : ℝ) ^ 2)) / Q / one := by rw [hk]; ring
      _ ≤ ((lo : ℝ) * Q) / Q / one := by gcongr
      _ = (lo : ℝ) / one := by field_simp
      _ ≤ v := hlo
  have hhi2 : v ≤ k * Q / (2 * (d : ℝ) ^ 2) := by
    calc v ≤ (hi : ℝ) / one := hhi
      _ = ((hi : ℝ) * (2 * (d : ℝ) ^ 2)) / (2 * (d : ℝ) ^ 2) / one := by field_simp
      _ ≤ ((c : ℝ) * Q) / (2 * (d : ℝ) ^ 2) / one := by gcongr
      _ = k * Q / (2 * (d : ℝ) ^ 2) := by rw [hk]; ring
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hlo2
  have hup : v / k ≤ Real.exp r := by
    rw [div_le_iff₀ hk0]
    calc v ≤ k * Q / (2 * (d : ℝ) ^ 2) := hhi2
      _ = k * (Q / (2 * (d : ℝ) ^ 2)) := by ring
      _ ≤ k * Real.exp r := mul_le_mul_of_nonneg_left hqe hk0.le
      _ = Real.exp r * k := by ring
  have hlow : Real.exp (-r) ≤ v / k := by
    rw [Real.exp_neg, le_div_iff₀ hk0]
    have h1 : (2 * (d : ℝ) ^ 2) / Q ≥ (Real.exp r)⁻¹ := by
      rw [ge_iff_le, inv_le_comm₀ (Real.exp_pos r) (div_pos hD hQpos), inv_div]; exact hqe
    calc (Real.exp r)⁻¹ * k ≤ (2 * (d : ℝ) ^ 2) / Q * k := mul_le_mul_of_nonneg_right h1 hk0.le
      _ = k * (2 * (d : ℝ) ^ 2) / Q := by ring
      _ ≤ v := hlo2
  have hvk : 0 < v / k := div_pos hv0 hk0
  refine ⟨-Real.log (v / k) / r, ?_, ?_⟩
  · rw [abs_div, abs_of_pos hr0, div_le_one hr0, abs_neg, abs_le]
    constructor
    · have := Real.log_le_log (Real.exp_pos _) hlow
      rw [Real.log_exp] at this; linarith
    · have := Real.log_le_log hvk hup
      rw [Real.log_exp] at this; linarith
  · unfold expF
    rw [← hk, ← hr]
    have e : -r * (-Real.log (v / k) / r) = Real.log (v / k) := by field_simp
    rw [e, Real.exp_log hvk]
    field_simp

theorem b_coord (c : BChart) {b0 b1 : Int} (h : bDomOK c b0 b1 = true) {v : ℝ} (hlo : (b0 : ℝ) / one ≤ v)
    (hhi : v ≤ (b1 : ℝ) / one) : ∃ x : ℝ, |x| ≤ 1 ∧ bF c x = v := by
  simp only [bDomOK, Bool.and_eq_true] at h
  have hch := h.1.1.1
  rcases c with ⟨bexp, bc, bh, bN, bD⟩
  cases bexp with
  | true =>
    simp only [↓reduceIte] at hch
    obtain ⟨x, hx, e⟩ := exp_coord hch hlo hhi
    exact ⟨x, hx, by simp only [bF, ↓reduceIte]; exact e⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hch
    obtain ⟨x, hx, e⟩ := lin_coord hch hlo hhi
    exact ⟨x, hx, by simp only [bF, Bool.false_eq_true, ↓reduceIte]; exact e⟩

/-! ## S-front -/

noncomputable def sgF (c : SCell) (z : ℝ) : ℝ := expF c.sc c.shN c.shD z

noncomputable def semS (c : SCell) : FSem where
  b := fun x _ _ => bF c.bch x
  t := fun _ y _ => linF c.tc c.th y
  u := fun x _ z => bF c.bch x * sgF c z
  lam := fun x _ z => (-Real.log (bF c.bch x * sgF c z))⁻¹
  w := fun x _ z => bF c.bch x * sgF c z * (-Real.log (bF c.bch x * sgF c z))
  cq := fun x _ z => -Real.log (1 - bF c.bch x * sgF c z)
  gg := fun x _ z => g1 (bF c.bch x * sgF c z)

theorem domS_parts {c : SCell} {b0 b1 t0 t1 s0 s1 : Int} (h : domS c b0 b1 t0 t1 s0 s1 = true) :
    bDomOK c.bch b0 b1 = true ∧ tDomOK c.tc c.th t0 t1 = true ∧ expBoxOK c.sc c.shN c.shD s0 s1 = true ∧
      2 * c.sc ≤ ONEi := by
  simp only [domS, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem sgF_bounds {c : SCell} {s0 s1 : Int} (h : expBoxOK c.sc c.shN c.shD s0 s1 = true) (h2 : 2 * c.sc ≤ ONEi)
    (z : ℝ) (hz : |z| ≤ 1) : 0 < sgF c z ∧ sgF c z ≤ 3 / 2 := by
  obtain ⟨hc, hn, hnd, _, _, _, _⟩ := expBoxOK_parts h
  refine ⟨expF_pos hc _ _ _, ?_⟩
  unfold sgF expF
  have hd' : (0 : ℝ) < c.shD := by exact_mod_cast (show 0 < c.shD by omega)
  have hr1 : (c.shN : ℝ) / c.shD ≤ 1 := by rw [div_le_one hd']; exact_mod_cast hnd
  have hr0 : (0 : ℝ) ≤ (c.shN : ℝ) / c.shD := div_nonneg (Nat.cast_nonneg _) hd'.le
  have harg : -((c.shN : ℝ) / c.shD) * z ≤ 1 := by
    have := neg_abs_le z
    have hzl := (abs_le.mp hz).1
    nlinarith
  have he : Real.exp (-((c.shN : ℝ) / c.shD) * z) ≤ 3 := by
    calc Real.exp (-((c.shN : ℝ) / c.shD) * z) ≤ Real.exp 1 := Real.exp_le_exp.mpr harg
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hsc : (c.sc : ℝ) / one ≤ 1 / 2 := by
    have : ((2 * c.sc : ℤ) : ℝ) ≤ ((ONEi : ℤ) : ℝ) := by exact_mod_cast h2
    push_cast at this; rw [ONEi_real'] at this
    rw [div_le_iff₀ hone']; linarith
  have hsc0 : (0 : ℝ) ≤ (c.sc : ℝ) / one := div_nonneg (by exact_mod_cast hc.le) hone'.le
  calc (c.sc : ℝ) / one * Real.exp (-((c.shN : ℝ) / c.shD) * z) ≤ 1 / 2 * 3 :=
        mul_le_mul hsc he (Real.exp_pos _).le (by norm_num)
    _ = 3 / 2 := by norm_num

theorem fokS (c : SCell) {b0 b1 t0 t1 s0 s1 : Int} (h : domS c b0 b1 t0 t1 s0 s1 = true) :
    FOK (frontS c) (semS c) := by
  obtain ⟨hb, ht, hs, h2⟩ := domS_parts h
  obtain ⟨hB, hlogB⟩ := frontB_contains c.bch hb
  obtain ⟨hc, hn, hnd, hmod, _, _, hls⟩ := expBoxOK_parts hs
  have hd : 0 < c.shD := by omega
  have hSg : Contains one (expPolyTM c.sc c.shN c.shD) (fun _ _ z => sgF c z) := expPoly_contains' hs
  have hU : Contains one (mul (frontB c.bch).1 (expPolyTM c.sc c.shN c.shD))
      (fun x _ z => bF c.bch x * sgF c z) := C_mul hB hSg
  -- positivity / range at chart points
  have hbF := fun x hx => bF_bounds c.bch hb x hx
  have hsF := fun z hz => sgF_bounds hs h2 z hz
  have hu_pos : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 0 < bF c.bch x * sgF c z :=
    fun x _ z hx _ hz => mul_pos (hbF x hx).1 (hsF z hz).1
  have hu_lt : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → bF c.bch x * sgF c z < 1 := by
    intro x _ z hx _ hz
    have h1 := hbF x hx; have h2 := hsF z hz
    calc bF c.bch x * sgF c z ≤ 1 / 2 * (3 / 2) := mul_le_mul h1.2 h2.2 h2.1.le (by norm_num)
      _ < 1 := by norm_num
  -- ell
  have hk := Contains.const (-(logScalar P c.sc.toNat).1) (logScalar P c.sc.toNat).2
    (-Real.log ((c.sc : ℝ) / one)) (by
      have := logScalar_encI hc hls
      rw [show -Real.log ((c.sc : ℝ) / one) - (((-(logScalar P c.sc.toNat).1 : ℤ)) : ℝ) / one
        = -(Real.log ((c.sc : ℝ) / one) - ((logScalar P c.sc.toNat).1 : ℝ) / one) by push_cast; ring, abs_neg]
      exact this)
  have hell0 := Contains.add (Contains.add (Contains.neg hlogB) hk) (Contains.lin 0 0 0 (rateI c.shN c.shD))
  have hell : Contains one (TM.add (TM.add (TM.neg (frontB c.bch).2) (TM.const (-(logScalar P c.sc.toNat).1)
      (logScalar P c.sc.toNat).2)) (TM.lin 0 0 0 (rateI c.shN c.shD)))
      (fun x _ z => -Real.log (bF c.bch x * sgF c z)) := by
    refine Contains.congr hell0 (fun x y z hx hy hz => ?_)
    have hb0 := (hbF x hx).1
    rw [Real.log_mul hb0.ne' (hsF z hz).1.ne']
    unfold sgF
    rw [log_expF hc]
    have hr := rate_eq hd hmod
    push_cast
    rw [add_div, add_div, add_div, zero_div, zero_mul, zero_div, zero_mul, zero_div, zero_add, zero_add,
      mul_div_right_comm, hr]
    ring
  refine
    { hB := hB
      hT := lin_contains_y c.tc c.th
      hlogB := hlogB
      hU := hU
      hLam := C_recip hell
      hW := Contains.congr (C_mul hU hell) (fun _ _ _ _ _ _ => rfl)
      homU := C_oneSub hU
      hCq := Contains.neg (C_log (C_oneSub hU))
      hG1 := g1Series_contains hU (C_oneSub hU) (fun x y z hx hy hz => (hu_pos x y z hx hy hz).le)
      b_pos := fun x _ _ hx _ _ => (hbF x hx).1
      b_le := fun x _ _ hx _ _ => (hbF x hx).2
      t_nn := fun _ y _ _ hy _ => (tF_bounds ht y hy).1
      t_le := fun _ y _ _ hy _ => (tF_bounds ht y hy).2
      u_nn := fun x y z hx hy hz => (hu_pos x y z hx hy hz).le
      w_nn := fun x y z hx hy hz => w_nonneg (hu_pos x y z hx hy hz).le (hu_lt x y z hx hy hz).le
      cq_nn := fun x y z hx hy hz => cq_nonneg (hu_pos x y z hx hy hz).le (hu_lt x y z hx hy hz)
      hu_le := fun x y z hx hy hz => hu_le_of (hu_pos x y z hx hy hz).le (hu_lt x y z hx hy hz) }

/-! ## L-front -/

noncomputable def lamF (c : LCell) (z : ℝ) : ℝ := ((lhI c : ℝ) + lhI c * z) / one

noncomputable def uLF (c : LCell) (z : ℝ) : ℝ := if 0 < lamF c z then Real.exp (-1 / lamF c z) else 0

noncomputable def semL (c : LCell) : FSem where
  b := fun x _ _ => bF c.bch x
  t := fun _ y _ => linF c.tc c.th y
  u := fun _ _ z => uLF c z
  lam := fun _ _ z => lamF c z
  w := fun _ _ z => uLF c z * (-Real.log (uLF c z))
  cq := fun _ _ z => -Real.log (1 - uLF c z)
  gg := fun _ _ z => g1 (uLF c z)

theorem domL_parts {c : LCell} {b0 b1 t0 t1 s1 : Int} (h : domL c b0 b1 t0 t1 s1 = true) :
    bDomOK c.bch b0 b1 = true ∧ tDomOK c.tc c.th t0 t1 = true ∧ 0 < s1 ∧ 0 < lhI c ∧ lsOK c.u1 = true ∧
      lsOK (kBox b1 s1) = true ∧
      (((logScalar P c.u1).2 : Int) - (logScalar P c.u1).1) * (2 * lhI c) ≤ ONEi * ONEi ∧
      ONEi * ONEi ≤ -((logScalar P (kBox b1 s1)).1 + ((logScalar P (kBox b1 s1)).2 : Int)) * (2 * lhI c) ∧
      3 * c.u1 ≤ one ∧ c.u1 ≤ 2 * ((c.u1 + 1) / 2) ∧
      (c.u1 : Int) * (((logScalar P c.u1).2 : Int) - (logScalar P c.u1).1) ≤ 2 * (((c.w1 + 1) / 2 : ℕ) : Int) * ONEi := by
  simp only [domL, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-! ### Real-valued consequences of `domL` (kept in small lemmas: clean contexts for the analytic steps) -/

theorem cast_le_ONEi_mul {a b : Int} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h

/-- `U1 := u1/one ≤ 1/3`, `0 < U1`, `U1 ≤ 2 uh/one`. -/
theorem domL_U1 {c : LCell} {b0 b1 t0 t1 s1 : Int} (h : domL c b0 b1 t0 t1 s1 = true) :
    0 < (c.u1 : ℝ) / one ∧ (c.u1 : ℝ) / one ≤ 1 / 3 ∧
      (c.u1 : ℝ) / one ≤ 2 * (((c.u1 + 1) / 2 : ℕ) : ℝ) / one := by
  obtain ⟨_, _, _, _, hls1, _, _, _, h3u, huh, _⟩ := domL_parts h
  have hu1pos : 0 < c.u1 := by simp only [lsOK, Bool.and_eq_true, decide_eq_true_eq] at hls1; exact hls1.1
  refine ⟨div_pos (by exact_mod_cast hu1pos) hone', ?_, ?_⟩
  · rw [div_le_iff₀ hone']
    have : ((3 * c.u1 : ℕ) : ℝ) ≤ (one : ℝ) := by exact_mod_cast h3u
    push_cast at this; linarith
  · apply div_le_div_of_nonneg_right _ hone'.le
    exact_mod_cast huh

/-- `-log U1 ≤ A1 := (E1 - L1)/one`, `A1 · 2lh ≤ one`, `u1 · A1 ≤ 2 wh` (all real). -/
theorem domL_A1 {c : LCell} {b0 b1 t0 t1 s1 : Int} (h : domL c b0 b1 t0 t1 s1 = true) :
    -Real.log ((c.u1 : ℝ) / one) ≤ (((logScalar P c.u1).2 : ℝ) - (logScalar P c.u1).1) / one ∧
      (((logScalar P c.u1).2 : ℝ) - (logScalar P c.u1).1) * (2 * (lhI c : ℝ)) ≤ (one : ℝ) * one ∧
      (c.u1 : ℝ) * (((logScalar P c.u1).2 : ℝ) - (logScalar P c.u1).1) ≤ 2 * (((c.w1 + 1) / 2 : ℕ) : ℝ) * one := by
  obtain ⟨_, _, _, _, hls1, _, hU1, _, _, _, hw⟩ := domL_parts h
  have henc := logScalar_enc hls1
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_div]; linarith [(abs_le.mp henc).1]
  · have := cast_le_ONEi_mul hU1
    push_cast at this; rw [ONEi_real'] at this; exact this
  · have h1 := cast_le_ONEi_mul hw
    have e1 : (((c.u1 : Int) * (((logScalar P c.u1).2 : Int) - (logScalar P c.u1).1) : ℤ) : ℝ)
        = (c.u1 : ℝ) * (((logScalar P c.u1).2 : ℝ) - (logScalar P c.u1).1) := by
      rw [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
    have e2 : ((2 * (((c.w1 + 1) / 2 : ℕ) : Int) * ONEi : ℤ) : ℝ) = 2 * (((c.w1 + 1) / 2 : ℕ) : ℝ) * one := by
      rw [Int.cast_mul, Int.cast_mul, ONEi_real', Int.cast_natCast, Int.cast_ofNat]
    rw [e1, e2] at h1; exact h1

/-- The box bound: `ln(1/u) ≥ one/(2 lh)` for `0 < u ≤ b1 s1/one²`. -/
theorem domL_K {c : LCell} {b0 b1 t0 t1 s1 : Int} (h : domL c b0 b1 t0 t1 s1 = true) {u : ℝ} (hu0 : 0 < u)
    (hu : u ≤ (b1 : ℝ) / one * ((s1 : ℝ) / one)) (hb1 : 0 < b1) :
    (one : ℝ) / (2 * (lhI c : ℝ)) ≤ -Real.log u := by
  obtain ⟨_, _, hs1, hlh, _, hlsk, _, hK, _, _, _⟩ := domL_parts h
  have hlh' : (0 : ℝ) < lhI c := by exact_mod_cast hlh
  have hk_ge : (b1 : ℝ) * s1 / one ≤ (kBox b1 s1 : ℝ) := by
    unfold kBox
    have hcd := le_cdiv (b1 * s1).toNat one hone
    have e : (((b1 * s1).toNat : ℕ) : ℝ) = (b1 : ℝ) * s1 := by
      have : (((b1 * s1).toNat : ℤ)) = b1 * s1 := Int.toNat_of_nonneg (mul_pos hb1 hs1).le
      exact_mod_cast this
    rw [e] at hcd; exact hcd
  have hu_le : u ≤ (kBox b1 s1 : ℝ) / one := by
    calc u ≤ (b1 : ℝ) / one * ((s1 : ℝ) / one) := hu
      _ = (b1 : ℝ) * s1 / one / one := by ring
      _ ≤ (kBox b1 s1 : ℝ) / one := div_le_div_of_nonneg_right hk_ge hone'.le
  have henc := logScalar_enc hlsk
  have hlogu : Real.log u ≤ ((logScalar P (kBox b1 s1)).1 : ℝ) / one + ((logScalar P (kBox b1 s1)).2 : ℝ) / one := by
    have := Real.log_le_log hu0 hu_le
    linarith [(abs_le.mp henc).2]
  have hK' : (one : ℝ) * one ≤ -(((logScalar P (kBox b1 s1)).1 : ℝ) + ((logScalar P (kBox b1 s1)).2 : ℝ))
      * (2 * lhI c) := by
    have := cast_le_ONEi_mul hK
    push_cast at this; rw [ONEi_real'] at this; exact this
  have h2l : (0 : ℝ) < 2 * (lhI c : ℝ) := by linarith
  have h1 : (one : ℝ) / (2 * lhI c) ≤ -(((logScalar P (kBox b1 s1)).1 : ℝ) + ((logScalar P (kBox b1 s1)).2 : ℝ)) / one := by
    rw [div_le_div_iff₀ h2l hone']; linarith
  have h2 : -(((logScalar P (kBox b1 s1)).1 : ℝ) + ((logScalar P (kBox b1 s1)).2 : ℝ)) / one ≤ -Real.log u := by
    rw [neg_div, add_div]; linarith
  linarith

/-! ### Pure analytic helpers -/

theorem lam_le_aux {L z : ℝ} (hL : 0 < L) (hz : |z| ≤ 1) : (L + L * z) / one ≤ 2 * L / one := by
  apply div_le_div_of_nonneg_right _ hone'.le
  have := mul_le_mul_of_nonneg_left (abs_le.mp hz).2 hL.le
  linarith

theorem lam_nonneg_aux {L z : ℝ} (hL : 0 < L) (hz : |z| ≤ 1) : 0 ≤ (L + L * z) / one := by
  apply div_nonneg _ hone'.le
  have := mul_le_mul_of_nonneg_left (abs_le.mp hz).1 hL.le
  linarith

theorem exp_neg_inv_le {lam L U R : ℝ} (hl : 0 < lam) (hL : 0 < L) (hlam : lam ≤ 2 * L / one) (hU : 0 < U)
    (hA : -Real.log U ≤ R / one) (hAL : R * (2 * L) ≤ (one : ℝ) * one) : Real.exp (-1 / lam) ≤ U := by
  have h2L : 0 < 2 * L := by linarith
  have h1 : -1 / lam ≤ -((one : ℝ) / (2 * L)) := by
    rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ h2L hl]
    have := mul_le_mul_of_nonneg_right hlam hone'.le
    rw [div_mul_cancel₀ _ hone'.ne'] at this; linarith
  have hA' : R / one ≤ (one : ℝ) / (2 * L) := by
    rw [div_le_div_iff₀ hone' h2L]; exact hAL
  have h2 : -((one : ℝ) / (2 * L)) ≤ Real.log U := by linarith
  calc Real.exp (-1 / lam) ≤ Real.exp (Real.log U) := Real.exp_le_exp.mpr (h1.trans h2)
    _ = U := Real.exp_log hU

theorem log_third_lt : Real.log (1 / 3 : ℝ) < -1 := by
  rw [one_div, Real.log_inv, neg_lt_neg_iff, Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9; linarith

theorem cq_le_two {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) : -Real.log (1 - u) ≤ 2 * u := by
  have h1u : 0 < 1 - u := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos h1u
  have e : 1 - (1 - u)⁻¹ = -(u / (1 - u)) := by field_simp; ring
  rw [e] at hl
  have hq : u / (1 - u) ≤ 2 * u := by
    rw [div_le_iff₀ h1u]
    have e2 : 2 * u * (1 - u) - u = u * (1 - 2 * u) := by ring
    have : 0 ≤ u * (1 - 2 * u) := mul_nonneg h0 (by linarith)
    linarith
  linarith

theorem C_constN (a : ℕ) (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 0 ≤ f x y z ∧ f x y z ≤ 2 * (a : ℝ) / one) :
    Contains one (TM.const (a : Int) a) f := by
  apply C_constF
  intro x y z hx hy hz
  obtain ⟨h0, h1⟩ := hf x y z hx hy hz
  rw [Int.cast_natCast]
  have ha : (0 : ℝ) ≤ (a : ℝ) / one := div_nonneg (Nat.cast_nonneg a) hone'.le
  apply abs_sub_le_of_mem
  · linarith
  · have e : 2 * (a : ℝ) / one = (a : ℝ) / one + (a : ℝ) / one := by ring
    linarith

theorem C_constG (a : ℕ) (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 1 - 2 * (a : ℝ) / one ≤ f x y z ∧ f x y z ≤ 1) :
    Contains one (TM.const (ONEi - (a : Int)) a) f := by
  apply C_constF
  intro x y z hx hy hz
  obtain ⟨h0, h1⟩ := hf x y z hx hy hz
  have e : (((ONEi - (a : Int) : ℤ)) : ℝ) / one = 1 - (a : ℝ) / one := by
    push_cast; rw [sub_div, ONEi_real', div_self hone'.ne']
  rw [e]
  apply abs_sub_le_of_mem
  · have e2 : 2 * (a : ℝ) / one = (a : ℝ) / one + (a : ℝ) / one := by ring
    linarith
  · linarith

/-! ### L chart -/

/-- `0 ≤ u ≤ u1/one` on the whole L chart. -/
theorem uLF_le {c : LCell} {b0 b1 t0 t1 s1 : Int} (h : domL c b0 b1 t0 t1 s1 = true) (z : ℝ) (hz : |z| ≤ 1) :
    0 ≤ uLF c z ∧ uLF c z ≤ (c.u1 : ℝ) / one := by
  obtain ⟨hU1pos, _, _⟩ := domL_U1 h
  obtain ⟨hA, hAL, _⟩ := domL_A1 h
  have hlh' : (0 : ℝ) < lhI c := by exact_mod_cast (domL_parts h).2.2.2.1
  unfold uLF
  split_ifs with hl
  · refine ⟨(Real.exp_pos _).le, ?_⟩
    exact exp_neg_inv_le hl hlh' (lam_le_aux hlh' hz) hU1pos hA hAL
  · exact ⟨le_refl 0, hU1pos.le⟩

theorem fokL (c : LCell) {b0 b1 t0 t1 s1 : Int} (h : domL c b0 b1 t0 t1 s1 = true) :
    FOK (frontL c) (semL c) := by
  have hb := (domL_parts h).1
  have ht := (domL_parts h).2.1
  obtain ⟨hB, hlogB⟩ := frontB_contains c.bch hb
  have hbF := fun x hx => bF_bounds c.bch hb x hx
  obtain ⟨hU1pos, hU13, hU1uh⟩ := domL_U1 h
  obtain ⟨hA, _, hwA⟩ := domL_A1 h
  have huB := fun z hz => uLF_le h z hz
  have hu3 : ∀ z : ℝ, |z| ≤ 1 → uLF c z ≤ 1 / 3 := fun z hz => (huB z hz).2.trans hU13
  have hU : Contains one (TM.const (((c.u1 + 1) / 2 : ℕ) : Int) ((c.u1 + 1) / 2)) (fun _ _ z => uLF c z) :=
    C_constN _ _ (fun x y z _ _ hz => ⟨(huB z hz).1, (huB z hz).2.trans hU1uh⟩)
  -- W
  have hlogU1 : Real.log ((c.u1 : ℝ) / one) ≤ -1 :=
    (Real.log_le_log hU1pos hU13).trans log_third_lt.le
  have hW : Contains one (TM.const (((c.w1 + 1) / 2 : ℕ) : Int) ((c.w1 + 1) / 2))
      (fun _ _ z => uLF c z * (-Real.log (uLF c z))) := by
    apply C_constN
    intro x y z _ _ hz
    obtain ⟨h0, h1⟩ := huB z hz
    refine ⟨w_nonneg h0 (by linarith [hu3 z hz]), ?_⟩
    have hwle : uLF c z * (-Real.log (uLF c z)) ≤ (c.u1 : ℝ) / one * (-Real.log ((c.u1 : ℝ) / one)) := by
      rcases h0.eq_or_lt with he | hpos
      · rw [← he, zero_mul]; exact mul_nonneg hU1pos.le (by linarith)
      · exact xlog_mono hpos h1 hlogU1
    have hmid : (c.u1 : ℝ) / one * (-Real.log ((c.u1 : ℝ) / one))
        ≤ (c.u1 : ℝ) / one * ((((logScalar P c.u1).2 : ℝ) - (logScalar P c.u1).1) / one) :=
      mul_le_mul_of_nonneg_left hA hU1pos.le
    have hlast : (c.u1 : ℝ) / one * ((((logScalar P c.u1).2 : ℝ) - (logScalar P c.u1).1) / one)
        ≤ 2 * (((c.w1 + 1) / 2 : ℕ) : ℝ) / one := by
      rw [show (c.u1 : ℝ) / one * ((((logScalar P c.u1).2 : ℝ) - (logScalar P c.u1).1) / one)
          = ((c.u1 : ℝ) * (((logScalar P c.u1).2 : ℝ) - (logScalar P c.u1).1)) / one / one by ring]
      calc ((c.u1 : ℝ) * (((logScalar P c.u1).2 : ℝ) - (logScalar P c.u1).1)) / one / one
          ≤ (2 * (((c.w1 + 1) / 2 : ℕ) : ℝ) * one) / one / one := by gcongr
        _ = 2 * (((c.w1 + 1) / 2 : ℕ) : ℝ) / one := by rw [mul_div_cancel_right₀ _ hone'.ne']
    linarith
  -- Cq
  have hCq : Contains one (TM.const (c.u1 : Int) c.u1) (fun _ _ z => -Real.log (1 - uLF c z)) := by
    apply C_constN
    intro x y z _ _ hz
    obtain ⟨h0, h1⟩ := huB z hz
    refine ⟨cq_nonneg h0 (by linarith [hu3 z hz]), ?_⟩
    have := cq_le_two h0 (by linarith [hu3 z hz])
    have h2 : 2 * uLF c z ≤ 2 * ((c.u1 : ℝ) / one) := by linarith
    rw [mul_div_assoc]; linarith
  -- G1
  have hG1 : Contains one (TM.const (ONEi - (((c.u1 + 1) / 2 : ℕ) : Int)) ((c.u1 + 1) / 2))
      (fun _ _ z => g1 (uLF c z)) := by
    apply C_constG
    intro x y z _ _ hz
    obtain ⟨h0, h1⟩ := huB z hz
    obtain ⟨gl, gu⟩ := g1_bounds h0 (by linarith [hu3 z hz])
    have hu2 : uLF c z ≤ 2 * (((c.u1 + 1) / 2 : ℕ) : ℝ) / one := h1.trans hU1uh
    exact ⟨by linarith, gu⟩
  exact
    { hB := hB
      hT := lin_contains_y c.tc c.th
      hlogB := hlogB
      hU := hU
      hLam := Contains.congr (Contains.lin (lhI c) 0 0 (lhI c)) (fun x y z _ _ _ => by
        show _ = lamF c z
        unfold lamF; push_cast; ring)
      hW := hW
      homU := C_oneSub hU
      hCq := hCq
      hG1 := hG1
      b_pos := fun x _ _ hx _ _ => (hbF x hx).1
      b_le := fun x _ _ hx _ _ => (hbF x hx).2
      t_nn := fun _ y _ _ hy _ => (tF_bounds ht y hy).1
      t_le := fun _ y _ _ hy _ => (tF_bounds ht y hy).2
      u_nn := fun _ _ z _ _ hz => (huB z hz).1
      w_nn := fun _ _ z _ _ hz => w_nonneg (huB z hz).1 (by linarith [hu3 z hz])
      cq_nn := fun _ _ z _ _ hz => cq_nonneg (huB z hz).1 (by linarith [hu3 z hz])
      hu_le := fun _ _ z _ _ hz => hu_le_of (huB z hz).1 (by linarith [hu3 z hz]) }

/-- Every `u = bσ` of the L box has `λ = 1/ln(1/u) ∈ (0, 2 lh/one]`, i.e. chart coordinate `z ∈ [-1,1]`. -/
theorem lamL_coord {c : LCell} {b0 b1 t0 t1 s1 : Int} (h : domL c b0 b1 t0 t1 s1 = true) {b σ : ℝ} (hb0 : 0 < b)
    (hb1 : b ≤ (b1 : ℝ) / one) (hσ0 : 0 < σ) (hσ1 : σ ≤ (s1 : ℝ) / one) :
    ∃ z : ℝ, |z| ≤ 1 ∧ 0 < lamF c z ∧ uLF c z = b * σ := by
  have hlh' : (0 : ℝ) < lhI c := by exact_mod_cast (domL_parts h).2.2.2.1
  have hne1 : (one : ℝ) ≠ 0 := hne
  have hlhne : (lhI c : ℝ) ≠ 0 := hlh'.ne'
  have hu0 : 0 < b * σ := mul_pos hb0 hσ0
  have hb1' : (0 : ℝ) < (b1 : ℝ) / one := lt_of_lt_of_le hb0 hb1
  have hb1i : 0 < b1 := by
    have : (0 : ℝ) < (b1 : ℝ) := by
      have := mul_pos hb1' hone'; rwa [div_mul_cancel₀ _ hne1] at this
    exact_mod_cast this
  have hu_le : b * σ ≤ (b1 : ℝ) / one * ((s1 : ℝ) / one) := mul_le_mul hb1 hσ1 hσ0.le hb1'.le
  have hell := domL_K h hu0 hu_le hb1i
  have h2l : (0 : ℝ) < 2 * (lhI c : ℝ) := by linarith
  have hellpos : 0 < -Real.log (b * σ) := lt_of_lt_of_le (div_pos hone' h2l) hell
  set lam := (-Real.log (b * σ))⁻¹ with hlamdef
  have hlam0 : 0 < lam := inv_pos.mpr hellpos
  have hlam1 : lam ≤ 2 * (lhI c : ℝ) / one := by
    rw [hlamdef, inv_le_comm₀ hellpos (div_pos h2l hone'), inv_div]; exact hell
  have e : lamF c (lam * one / lhI c - 1) = lam := by
    unfold lamF
    field_simp
    try ring
  refine ⟨lam * one / lhI c - 1, ?_, ?_, ?_⟩
  · rw [abs_le]; constructor
    · have : 0 ≤ lam * one / lhI c := div_nonneg (mul_nonneg hlam0.le hone'.le) hlh'.le
      linarith
    · have : lam * one / lhI c ≤ 2 := by
        rw [div_le_iff₀ hlh']
        have := mul_le_mul_of_nonneg_right hlam1 hone'.le
        rw [div_mul_cancel₀ _ hne1] at this; linarith
      linarith
  · rw [e]; exact hlam0
  · unfold uLF
    rw [e, if_pos hlam0, hlamdef]
    rw [show -1 / (-Real.log (b * σ))⁻¹ = Real.log (b * σ) by rw [div_inv_eq_mul]; ring]
    exact Real.exp_log hu0

end CKLaneR2.Tail

end


