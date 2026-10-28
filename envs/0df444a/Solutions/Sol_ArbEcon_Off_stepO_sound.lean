-- Prove2me | solution 1 for ArbEcon.Off.stepO_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:55:18.57887+00:00
-- url     : https://prove2.me/submissions/01310224-6ba8-4540-b9cf-7395f679f2aa

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRS_Arithmetic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_ArbEcon_Off_ampl_sound
import Theorems.Thm_ArbEcon_logInc_bound
import Theorems.Thm_ArbEcon_theta_bracket
import Theorems.Thm_ArbEcon_trig_sound
/-  Probes/ArbEconomics_Sound.lean -- soundness of the Nat-only zeta evaluator (ArbEconomics_Eval).

    Every function of `ArbEconomics_Eval` is shown to produce a TRUE enclosure:
      * `logInc`   : `S <= (log m - log (m-1)) 2^P <= S + K + T`
                     (Mathlib `Real.hasSum_pow_div_log_of_abs_lt_one`, `abs_log_sub_add_sum_range_le`);
      * `termOf`   : `Rlo <= 2^P / sqrt m <= Rhi` for ANY Newton iterate (two-sided validation);
      * `trig`     : cos/sin balls of `theta` from the (pi/2)-reduction, the Horner scheme
                     (Mathlib `Complex.exp_bound`) and the quadrant rotation;
      * `step`/`run` : the loop invariant `Inv` (log bracket + Re/Im balls of the partial zeta sum).

    The main theorem `run_sound` turns a kernel-checked chunk equation
    `St.beq (run cfg L s) s' = true` into `Inv n s -> Inv (n + L) s'`.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/










open Real Finset

namespace ArbEcon

/-! ## A. floor division / shifts, cast to ℝ -/

theorem natdiv_le (a b : ℕ) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b := Nat.cast_div_le

theorem lt_natdiv_add_one (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b < ((a / b : ℕ) : ℝ) + 1 := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_lt_iff₀ hbR]
  have h1 : a < (a / b + 1) * b := by
    have := Nat.lt_div_mul_add (a := a) hb
    nlinarith [this]
  have h2 : ((a : ℕ) : ℝ) < (((a / b + 1) * b : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h2
  linarith

theorem shr_eq (a d : ℕ) : Nat.shiftRight a d = a / 2 ^ d := Nat.shiftRight_eq_div_pow a d



theorem two_pow_pos' (P : ℕ) : (0 : ℝ) < (2 : ℝ) ^ P := by positivity

/-! The evaluator calls the kernel primitives directly; these `rfl` lemmas translate them back to
    notation for the proofs. -/
@[simp] theorem p_add (a b : ℕ) : Nat.add a b = a + b := rfl
@[simp] theorem p_mul (a b : ℕ) : Nat.mul a b = a * b := rfl
@[simp] theorem p_sub (a b : ℕ) : Nat.sub a b = a - b := rfl
@[simp] theorem p_div (a b : ℕ) : Nat.div a b = a / b := rfl

@[simp] theorem p_shr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl


/-- `⌊a / 2^d⌋ ≤ a / 2^d < ⌊a / 2^d⌋ + 1` over ℝ. -/
theorem shr_bounds (a d : ℕ) :
    ((Nat.shiftRight a d : ℕ) : ℝ) ≤ (a : ℝ) / 2 ^ d ∧ (a : ℝ) / 2 ^ d < (Nat.shiftRight a d : ℝ) + 1 := by
  rw [shr_eq]
  have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
  have e : ((2 ^ d : ℕ) : ℝ) = (2 : ℝ) ^ d := by push_cast; ring
  constructor
  · have := natdiv_le a (2 ^ d); rw [e] at this; exact this
  · have := lt_natdiv_add_one a (2 ^ d) hpos; rw [e] at this; exact this

/-! ## B. the log increment -/



theorem logLoop_spec (one m : ℕ) :
    ∀ (fuel i pw S : ℕ), pw = m ^ (i + 1) → S = ∑ j ∈ range i, one / (m ^ (j + 1) * (j + 1)) →
      LogSpec one m (logLoop one m fuel i pw S) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i pw S hpw hS
    exact ⟨hS, hpw⟩
  | succ fuel ih =>
    intro i pw S hpw hS
    show LogSpec one m (Bool.rec (logLoop one m fuel (Nat.succ i) (Nat.mul pw m)
      (Nat.add S (Nat.div one (Nat.mul pw (Nat.succ i))))) (S, i, pw)
      (Nat.beq (Nat.div one (Nat.mul pw (Nat.succ i))) 0))
    cases Nat.beq (Nat.div one (Nat.mul pw (Nat.succ i))) 0 with
    | true => exact ⟨hS, hpw⟩
    | false =>
      apply ih
      · show pw * m = m ^ (i + 1 + 1)
        rw [hpw]; ring
      · show S + one / (pw * (i + 1)) = ∑ j ∈ range (i + 1), one / (m ^ (j + 1) * (j + 1))
        rw [sum_range_succ, ← hS, hpw]

theorem logFix_spec (one m : ℕ) :
    ∀ (K i pw S : ℕ), pw = m ^ (i + 1) → S = ∑ j ∈ range i, one / (m ^ (j + 1) * (j + 1)) →
      LogSpec one m (logFix one m K i pw S) := by
  intro K
  induction K with
  | zero =>
    intro i pw S hpw hS
    exact ⟨hS, hpw⟩
  | succ K ih =>
    intro i pw S hpw hS
    show LogSpec one m (logFix one m K (Nat.succ i) (Nat.mul pw m)
      (Nat.add S (Nat.div one (Nat.mul pw (Nat.succ i)))))
    apply ih
    · show pw * m = m ^ (i + 1 + 1)
      rw [hpw]; ring
    · show S + one / (pw * (i + 1)) = ∑ j ∈ range (i + 1), one / (m ^ (j + 1) * (j + 1))
      rw [sum_range_succ, ← hS, hpw]





/-! ## C. the square-root bracket -/



/-! ## D. the theta interval -/



/-! ## E. Horner: real recursion, closed form, fixed-point error -/


















/-! ## F. Taylor remainders for cos / sin through `Complex.exp_bound` -/





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/





theorem sgn_not (b : Bool) : sgn (!b) = -sgn b := by cases b <;> simp [sgn]
theorem abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp [sgn]



















/-! ## H. the zeta term, the term product, one step, the run -/













theorem logInc_spec (c : Cfg) (t : ℝ) (K : ℕ) (hv : Valid c t K) (m : ℕ) :
    LogSpec (2 ^ c.P) m (logInc c m) := by
  rw [← hv.one_eq]
  show LogSpec c.one m (Bool.rec (logLoop c.one m c.lnfuel 0 m 0) (c.lnf m) (Nat.ble c.lnbig m))
  cases Nat.ble c.lnbig m with
  | false => exact logLoop_spec c.one m c.lnfuel 0 m 0 (by ring) (by simp)
  | true =>
    show LogSpec c.one m (c.lnf m)
    rw [hv.lnf_eq]; exact logFix_spec c.one m c.lnK 0 m 0 (by ring) (by simp)









end ArbEcon


/-  EMZetaOfflineSound.lean -- soundness of the off-line Nat-only evaluator (EMZetaOfflineEval).

    Every function of `EMZetaOfflineEval` produces a TRUE enclosure:
      * `imul_sound`     : the product `x · v` of a nonnegative bracket and a term ball;
      * `ampl_sound`     : the validated Newton root brackets `2^P m^(-σ)`, `σ = (a - b)/q`
                           (for ANY Newton output: the two kernel comparisons decide the bracket);
      * `termTB_sound`   : the term ball of `m^(-s) = m^(-σ)(cos θ - i sin θ)`, `θ = t log m`;
      * `addChain_sound` : accumulator `k` receives `(log m)^k m^(-s)`;
      * `stepO_sound`, `runO_sound`, `chunkO_sound` : the loop invariant `InvO` (log bracket and
                           the `p + 1` complex balls of `Σ_{m ≤ n} (log m)^k m^(-s)`).
    The log increment and the cos/sin kernels are `ArbEcon.logInc`/`ArbEcon.trig`, whose soundness
    (`ArbEcon.logInc_bound`, `ArbEcon.trig_sound`) is reused unchanged.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/



open Real Finset

namespace ArbEcon

namespace Off



/-! ## A. Specifications. -/















/-! ## B. The bracket-times-ball product. -/

theorem imul_sound (P lo hi vm vr : ℕ) (vs : Bool) (x v : ℝ) (hx0 : 0 ≤ x)
    (hlo : (lo : ℝ) ≤ x * 2 ^ P) (hhi : x * 2 ^ P ≤ hi) (hv : |v * 2 ^ P - sgn vs * vm| ≤ vr) :
    |x * v * 2 ^ P - sgn vs * (imC P hi vm : ℝ)| ≤ (imR P lo hi vm vr : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ P := two_pow_pos' P
  have hle : lo ≤ hi := by exact_mod_cast le_trans hlo hhi
  obtain ⟨a1, a2⟩ := shr_bounds (hi * vm) P
  obtain ⟨_, b2⟩ := shr_bounds (hi * vr) P
  obtain ⟨_, c2⟩ := shr_bounds ((hi - lo) * vm) P
  have hsub : (((hi - lo : ℕ)) : ℝ) = (hi : ℝ) - lo := by rw [Nat.cast_sub hle]
  simp only [imC, imR, p_add, p_mul, p_sub, p_shr] at a1 a2 b2 c2 ⊢
  push_cast [hsub] at a1 a2 b2 c2 ⊢
  set T := (((hi * vm) >>> P : ℕ) : ℝ) with hT
  set U := (((hi * vr) >>> P : ℕ) : ℝ) with hU
  set V := ((((hi - lo) * vm) >>> P : ℕ) : ℝ) with hV
  have hvm0 : (0 : ℝ) ≤ vm := Nat.cast_nonneg vm
  have hvr0 : (0 : ℝ) ≤ vr := Nat.cast_nonneg vr
  have e : x * v * 2 ^ P - sgn vs * T
      = x * (v * 2 ^ P - sgn vs * vm) + sgn vs * (vm * (x * 2 ^ P - hi) / 2 ^ P)
        + sgn vs * ((hi : ℝ) * vm / 2 ^ P - T) := by
    field_simp; ring
  rw [e]
  have t1 : |x * (v * 2 ^ P - sgn vs * vm)| ≤ (hi : ℝ) * vr / 2 ^ P := by
    rw [abs_mul, abs_of_nonneg hx0]
    have h1 : x * |v * 2 ^ P - sgn vs * vm| ≤ x * vr := mul_le_mul_of_nonneg_left hv hx0
    have h2 : x * (vr : ℝ) ≤ (hi : ℝ) * vr / 2 ^ P := by
      rw [le_div_iff₀ hP]; nlinarith
    linarith
  have t2 : |sgn vs * (vm * (x * 2 ^ P - hi) / 2 ^ P)| ≤ ((hi : ℝ) - lo) * vm / 2 ^ P := by
    rw [abs_mul, abs_sgn, one_mul, abs_div, abs_of_pos hP, abs_mul, abs_of_nonneg hvm0]
    apply div_le_div_of_nonneg_right _ hP.le
    have : |x * 2 ^ P - hi| ≤ (hi : ℝ) - lo := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg (x * 2 ^ P - hi)]
  have t3 : |sgn vs * ((hi : ℝ) * vm / 2 ^ P - T)| ≤ 1 := by
    rw [abs_mul, abs_sgn, one_mul, abs_le]
    constructor <;> linarith
  have q1 := abs_add_le (x * (v * 2 ^ P - sgn vs * vm) + sgn vs * (vm * (x * 2 ^ P - hi) / 2 ^ P))
    (sgn vs * ((hi : ℝ) * vm / 2 ^ P - T))
  have q2 := abs_add_le (x * (v * 2 ^ P - sgn vs * vm)) (sgn vs * (vm * (x * 2 ^ P - hi) / 2 ^ P))
  have e2 : ((hi : ℝ) - lo) * vm / 2 ^ P = ((hi : ℝ) - lo) * vm / 2 ^ P := rfl
  linarith

/-! ## C. Term balls, accumulation, the log chain. -/

theorem tbMul_sound (P lo hi : ℕ) (x : ℝ) (w : ℂ) (t : TB) (hx0 : 0 ≤ x)
    (hlo : (lo : ℝ) ≤ x * 2 ^ P) (hhi : x * 2 ^ P ≤ hi) (ht : TBOK P w t) :
    TBOK P ((x : ℂ) * w) (tbMul P lo hi t) := by
  obtain ⟨h1, h2⟩ := ht
  have hre : ((x : ℂ) * w).re = x * w.re := by simp [Complex.mul_re]
  have him : ((x : ℂ) * w).im = x * w.im := by simp [Complex.mul_im]
  refine ⟨?_, ?_⟩
  · rw [hre]; exact imul_sound P lo hi t.rm t.rr t.rs x w.re hx0 hlo hhi h1
  · rw [him]; exact imul_sound P lo hi t.im t.ir t.is x w.im hx0 hlo hhi h2

theorem accAdd_sound (P : ℕ) (z w : ℂ) (x : Acc) (t : TB) (hx : AccOK P z x) (ht : TBOK P w t) :
    AccOK P (z + w) (accAdd x t) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨ht1, ht2⟩ := ht
  constructor
  · have hc : ((accAdd x t).reP : ℝ) - (accAdd x t).reN = ((x.reP : ℝ) - x.reN) + sgn t.rs * t.rm := by
      show ((Bool.rec x.reP (Nat.add x.reP t.rm) t.rs : ℕ) : ℝ)
        - ((Bool.rec (Nat.add x.reN t.rm) x.reN t.rs : ℕ) : ℝ) = _
      cases t.rs <;> simp [sgn] <;> ring
    have hr : ((accAdd x t).reR : ℝ) = x.reR + t.rr := by
      show ((Nat.add x.reR t.rr : ℕ) : ℝ) = _; simp
    rw [hc, hr, Complex.add_re]
    have e : (z.re + w.re) * 2 ^ P - (((x.reP : ℝ) - x.reN) + sgn t.rs * t.rm)
        = (z.re * 2 ^ P - ((x.reP : ℝ) - x.reN)) + (w.re * 2 ^ P - sgn t.rs * t.rm) := by ring
    rw [e]; exact le_trans (abs_add_le _ _) (add_le_add hx1 ht1)
  · have hc : ((accAdd x t).imP : ℝ) - (accAdd x t).imN = ((x.imP : ℝ) - x.imN) + sgn t.is * t.im := by
      show ((Bool.rec x.imP (Nat.add x.imP t.im) t.is : ℕ) : ℝ)
        - ((Bool.rec (Nat.add x.imN t.im) x.imN t.is : ℕ) : ℝ) = _
      cases t.is <;> simp [sgn] <;> ring
    have hr : ((accAdd x t).imR : ℝ) = x.imR + t.ir := by
      show ((Nat.add x.imR t.ir : ℕ) : ℝ) = _; simp
    rw [hc, hr, Complex.add_im]
    have e : (z.im + w.im) * 2 ^ P - (((x.imP : ℝ) - x.imN) + sgn t.is * t.im)
        = (z.im * 2 ^ P - ((x.imP : ℝ) - x.imN)) + (w.im * 2 ^ P - sgn t.is * t.im) := by ring
    rw [e]; exact le_trans (abs_add_le _ _) (add_le_add hx2 ht2)

theorem addChain_sound (P lo hi : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hlo : (lo : ℝ) ≤ x * 2 ^ P)
    (hhi : x * 2 ^ P ≤ hi) (f : ℕ → ℂ) (w : ℂ) :
    ∀ (xs : List Acc) (k : ℕ) (t : TB), TBOK P ((x : ℂ) ^ k * w) t → AccsOK P f k xs →
      AccsOK P (fun j => f j + (x : ℂ) ^ j * w) k (addChain P lo hi xs t) := by
  intro xs
  induction xs with
  | nil => intro k t _ _; trivial
  | cons a as ih =>
    intro k t ht hA
    obtain ⟨hA1, hA2⟩ := hA
    have hstep : addChain P lo hi (a :: as) t = accAdd a t :: addChain P lo hi as (tbMul P lo hi t) :=
      rfl
    rw [hstep]
    refine ⟨accAdd_sound P (f k) ((x : ℂ) ^ k * w) a t hA1 ht, ?_⟩
    apply ih (k + 1) (tbMul P lo hi t) _ hA2
    have := tbMul_sound P lo hi x ((x : ℂ) ^ k * w) t hx0 hlo hhi ht
    have e : (x : ℂ) * ((x : ℂ) ^ k * w) = (x : ℂ) ^ (k + 1) * w := by ring
    rw [e] at this
    exact this

/-! ## D. The validated amplitude bracket. -/





/-! ## E. The term `m^(-s)`. -/

theorem cpow_termG (m : ℕ) (hm : 0 < m) (σ t : ℝ) :
    ((m : ℂ) ^ (-sOfG σ t)).re = (m : ℝ) ^ (-σ) * Real.cos (t * Real.log m) ∧
    ((m : ℂ) ^ (-sOfG σ t)).im = -((m : ℝ) ^ (-σ) * Real.sin (t * Real.log m)) := by
  have hnpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hne : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hlog : Complex.log (m : ℂ) = (Real.log m : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hnpos.le]
  have hre : (((Real.log m : ℝ) : ℂ) * -sOfG σ t).re = -σ * Real.log m := by
    simp only [sOfG, Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.neg_im,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    ring
  have him : (((Real.log m : ℝ) : ℂ) * -sOfG σ t).im = -(t * Real.log m) := by
    simp only [sOfG, Complex.mul_im, Complex.neg_re, Complex.add_re, Complex.neg_im,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re,
      Complex.I_im]
    ring
  have hrp : Real.exp (-σ * Real.log m) = (m : ℝ) ^ (-σ) := by
    rw [Real.rpow_def_of_pos hnpos]; ring_nf
  rw [Complex.cpow_def_of_ne_zero hne, hlog]
  constructor
  · rw [Complex.exp_re, hre, him, Real.cos_neg, hrp]
  · rw [Complex.exp_im, hre, him, Real.sin_neg, hrp]; ring

theorem termTB_sound (P Xlo Xhi : ℕ) (tr : Trig) (m : ℕ) (hm : 0 < m) (σ t : ℝ)
    (hXlo : (Xlo : ℝ) ≤ (m : ℝ) ^ (-σ) * 2 ^ P) (hXhi : (m : ℝ) ^ (-σ) * 2 ^ P ≤ Xhi)
    (htr : TrigOK P (t * Real.log m) tr) :
    TBOK P ((m : ℂ) ^ (-sOfG σ t)) (termTB P Xlo Xhi tr) := by
  obtain ⟨hc, hs, _, _⟩ := htr
  obtain ⟨ere, eim⟩ := cpow_termG m hm σ t
  have hX0 : (0 : ℝ) ≤ (m : ℝ) ^ (-σ) := by positivity
  constructor
  · rw [ere]
    exact imul_sound P Xlo Xhi tr.cm tr.cr tr.cs _ _ hX0 hXlo hXhi hc
  · rw [eim]
    have h := imul_sound P Xlo Xhi tr.sm tr.sr tr.ss _ _ hX0 hXlo hXhi hs
    show |-((m : ℝ) ^ (-σ) * Real.sin (t * Real.log m)) * 2 ^ P - sgn (!tr.ss) * (imC P Xhi tr.sm : ℝ)|
      ≤ (imR P Xlo Xhi tr.sm tr.sr : ℝ)
    rw [sgn_not]
    have e : -((m : ℝ) ^ (-σ) * Real.sin (t * Real.log m)) * 2 ^ P - -sgn tr.ss * (imC P Xhi tr.sm : ℝ)
        = -((m : ℝ) ^ (-σ) * Real.sin (t * Real.log m) * 2 ^ P - sgn tr.ss * (imC P Xhi tr.sm : ℝ)) := by
      ring
    rw [e, abs_neg]; exact h

/-! ## F. The partial sums. -/

theorem psumK_succ (σ t : ℝ) (k n : ℕ) :
    psumK σ t k (n + 1) = psumK σ t k n
      + ((Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) ^ k * (((n + 1 : ℕ) : ℕ) : ℂ) ^ (-sOfG σ t) := by
  simp only [psumK]
  rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]





/-! ## G. One step, the run, the chunks. -/

















end Off

end ArbEcon


/-  EMZetaOfflineSound.lean -- soundness of the off-line Nat-only evaluator (EMZetaOfflineEval).

    Every function of `EMZetaOfflineEval` produces a TRUE enclosure:
      * `imul_sound`     : the product `x · v` of a nonnegative bracket and a term ball;
      * `ampl_sound`     : the validated Newton root brackets `2^P m^(-σ)`, `σ = (a - b)/q`
                           (for ANY Newton output: the two kernel comparisons decide the bracket);
      * `termTB_sound`   : the term ball of `m^(-s) = m^(-σ)(cos θ - i sin θ)`, `θ = t log m`;
      * `addChain_sound` : accumulator `k` receives `(log m)^k m^(-s)`;
      * `stepO_sound`, `runO_sound`, `chunkO_sound` : the loop invariant `InvO` (log bracket and
                           the `p + 1` complex balls of `Σ_{m ≤ n} (log m)^k m^(-s)`).
    The log increment and the cos/sin kernels are `ArbEcon.logInc`/`ArbEcon.trig`, whose soundness
    (`ArbEcon.logInc_bound`, `ArbEcon.trig_sound`) is reused unchanged.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/



open Real Finset

section
namespace ArbEcon
end ArbEcon
open ArbEcon

section
namespace ArbEcon.Off
end ArbEcon.Off
open ArbEcon.Off



/-! ## A. Specifications. -/















/-! ## B. The bracket-times-ball product. -/



/-! ## C. Term balls, accumulation, the log chain. -/







/-! ## D. The validated amplitude bracket. -/





/-! ## E. The term `m^(-s)`. -/





/-! ## F. The partial sums. -/







/-! ## G. One step, the run, the chunks. -/

theorem solution (c : Cfg) (o : OCfg) (σ t : ℝ) (K : ℕ) (hv : Valid c t K)
    (ho : OValid c o σ) (n : ℕ) (s : StO) (hI : InvO c σ t n s) :
    InvO c σ t (n + 1) (stepO c o s) := by
  obtain ⟨hn, h1, hllo, hlhi, hacc⟩ := hI
  subst hn
  have hP : (0 : ℝ) < 2 ^ c.P := two_pow_pos' c.P
  have hm2 : 2 ≤ s.n + 1 := by omega
  have hmpos : 0 < s.n + 1 := by omega
  -- the log bracket (same computation as `ArbEcon.step`)
  have hls := logInc_spec c t K hv (s.n + 1)
  obtain ⟨lb1, lb2⟩ := logInc_bound c.P (s.n + 1) hm2 (logInc c (s.n + 1)) hls
  have hmn : ((s.n + 1 : ℕ) : ℝ) - 1 = (s.n : ℝ) := by push_cast; ring
  rw [hmn] at lb1 lb2
  have hllo' : ((stepO c o s).llo : ℝ) = s.llo + (logInc c (s.n + 1)).1 := by
    show ((Nat.add s.llo (logInc c (Nat.succ s.n)).1 : ℕ) : ℝ) = _
    simp only [p_add]; push_cast; rfl
  have hlhi' : ((stepO c o s).lhi : ℝ) = s.lhi + (logInc c (s.n + 1)).1 + (logInc c (s.n + 1)).2.1
      + ((2 ^ (c.P + 1) / (logInc c (s.n + 1)).2.2 : ℕ) + 1) := by
    show ((Nat.add (Nat.add (Nat.add s.lhi (logInc c (Nat.succ s.n)).1) (logInc c (Nat.succ s.n)).2.1)
      (Nat.add (Nat.div c.two1 (logInc c (Nat.succ s.n)).2.2) 1) : ℕ) : ℝ) = _
    rw [hv.two1_eq]; simp only [p_add, p_div]; push_cast; rfl
  have hLlo : ((stepO c o s).llo : ℝ) ≤ Real.log ((s.n + 1 : ℕ) : ℝ) * 2 ^ c.P := by
    rw [hllo']; nlinarith [lb1, hllo]
  have hLhi : Real.log ((s.n + 1 : ℕ) : ℝ) * 2 ^ c.P ≤ (stepO c o s).lhi := by
    rw [hlhi']; nlinarith [lb2, hlhi]
  -- the amplitude
  have ham := ampl_sound c o hv.one_eq ho.oneQ_eq ho.q_pos (s.n + 1) s.g (by omega)
  rw [← ho.sigma_eq] at ham
  -- theta and trig
  have htb := theta_bracket c.P c.tn c.tq (Real.log ((s.n + 1 : ℕ) : ℝ)) (stepO c o s).llo
    (stepO c o s).lhi hLlo hLhi
  rw [← hv.t_eq] at htb
  have htr := trig_sound c t K hv (t * Real.log ((s.n + 1 : ℕ) : ℝ)) _ _ htb.1 htb.2
  have hterm := termTB_sound c.P (ampl c o (s.n + 1) s.g).2.1 (ampl c o (s.n + 1) s.g).2.2 _
    (s.n + 1) hmpos σ t ham.1 ham.2 htr
  -- the chain
  have hlog0 : (0 : ℝ) ≤ Real.log ((s.n + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ s.n + 1 by omega))
  have hterm0 : TBOK c.P (((Real.log ((s.n + 1 : ℕ) : ℝ) : ℝ) : ℂ) ^ 0 * (((s.n + 1 : ℕ) : ℂ)) ^ (-sOfG σ t))
      (termTB c.P (ampl c o (s.n + 1) s.g).2.1 (ampl c o (s.n + 1) s.g).2.2
        (trig c (Nat.shiftRight (Nat.mul c.tn (stepO c o s).llo) c.tq)
          (Nat.add (Nat.shiftRight (Nat.mul c.tn (stepO c o s).lhi) c.tq) 1))) := by
    rw [pow_zero, one_mul]; exact hterm
  have hchain := addChain_sound c.P (stepO c o s).llo (stepO c o s).lhi
    (Real.log ((s.n + 1 : ℕ) : ℝ)) hlog0 hLlo hLhi
    (fun k => psumK σ t k s.n) ((((s.n + 1 : ℕ) : ℂ)) ^ (-sOfG σ t)) s.acc 0 _ hterm0 hacc
  refine ⟨rfl, by omega, hLlo, hLhi, ?_⟩
  have hf : (fun k => psumK σ t k (s.n + 1))
      = (fun k => psumK σ t k s.n
          + ((Real.log ((s.n + 1 : ℕ) : ℝ) : ℝ) : ℂ) ^ k * (((s.n + 1 : ℕ) : ℂ)) ^ (-sOfG σ t)) := by
    funext k; rw [psumK_succ]
  rw [hf]
  exact hchain
