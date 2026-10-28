-- Prove2me | solution 1 for ArbEcon.step_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:43:33.164774+00:00
-- url     : https://prove2.me/submissions/7757dda1-e682-4ebf-92e3-a503ef6647a9

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRS_Arithmetic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_ArbEcon_cpow_term
import Theorems.Thm_ArbEcon_logInc_bound
import Theorems.Thm_ArbEcon_sqrt_bracket
import Theorems.Thm_ArbEcon_tmul_sound
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

theorem theta_bracket (P tn tq : ℕ) (L : ℝ) (lloN lhiN : ℕ)
    (hlo : (lloN : ℝ) ≤ L * 2 ^ P) (hhi : L * 2 ^ P ≤ lhiN) :
    ((Nat.shiftRight (Nat.mul tn lloN) tq : ℕ) : ℝ) ≤ ((tn : ℝ) / 2 ^ tq * L) * 2 ^ P ∧
    ((tn : ℝ) / 2 ^ tq * L) * 2 ^ P ≤ ((Nat.add (Nat.shiftRight (Nat.mul tn lhiN) tq) 1 : ℕ) : ℝ) := by
  have hq : (0 : ℝ) < 2 ^ tq := two_pow_pos' tq
  have htn : (0 : ℝ) ≤ tn := by positivity
  obtain ⟨b1, _⟩ := shr_bounds (tn * lloN) tq
  obtain ⟨_, b2⟩ := shr_bounds (tn * lhiN) tq
  simp only [p_mul, p_add, p_shr] at b1 b2 ⊢
  have e : ((tn : ℝ) / 2 ^ tq * L) * 2 ^ P = (tn : ℝ) * (L * 2 ^ P) / 2 ^ tq := by ring
  rw [e]
  constructor
  · refine le_trans b1 ?_
    push_cast
    apply div_le_div_of_nonneg_right _ (le_of_lt hq)
    exact mul_le_mul_of_nonneg_left hlo htn
  · push_cast
    refine le_trans ?_ (le_of_lt b2)
    push_cast
    apply div_le_div_of_nonneg_right _ (le_of_lt hq)
    exact mul_le_mul_of_nonneg_left hhi htn

/-! ## E. Horner: real recursion, closed form, fixed-point error -/


















/-! ## F. Taylor remainders for cos / sin through `Complex.exp_bound` -/





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/


























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

section
namespace ArbEcon
end ArbEcon
open ArbEcon

/-! ## A. floor division / shifts, cast to ℝ -/











/-! The evaluator calls the kernel primitives directly; these `rfl` lemmas translate them back to
    notation for the proofs. -/










/-! ## B. the log increment -/











/-! ## C. the square-root bracket -/



/-! ## D. the theta interval -/



/-! ## E. Horner: real recursion, closed form, fixed-point error -/


















/-! ## F. Taylor remainders for cos / sin through `Complex.exp_bound` -/





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/


























/-! ## H. the zeta term, the term product, one step, the run -/















theorem solution (c : Cfg) (t : ℝ) (K : ℕ) (hv : Valid c t K) (n : ℕ) (s : St)
    (hI : Inv c t n s) : Inv c t (n + 1) (step c s) := by
  obtain ⟨hn, h1, hllo, hlhi, hre, him⟩ := hI
  have hP : (0 : ℝ) < 2 ^ c.P := two_pow_pos' c.P
  set m := n + 1 with hm
  have hm2 : 2 ≤ m := by omega
  have hmpos : 0 < m := by omega
  -- log
  have hls := logInc_spec c t K hv m
  obtain ⟨lb1, lb2⟩ := logInc_bound c.P m hm2 (logInc c m) hls
  have hmn : (m : ℝ) - 1 = (n : ℝ) := by rw [hm]; push_cast; ring
  rw [hmn] at lb1 lb2
  set lg := logInc c m with hlg
  have hstep_n : (step c s).n = m := by show Nat.succ s.n = m; rw [hn]
  have hllo' : ((step c s).llo : ℝ) = s.llo + lg.1 := by
    show ((Nat.add s.llo (logInc c (Nat.succ s.n)).1 : ℕ) : ℝ) = _
    rw [hn]; simp only [p_add]; push_cast; rfl
  have hlhi' : ((step c s).lhi : ℝ) = s.lhi + lg.1 + lg.2.1 + ((2 ^ (c.P + 1) / lg.2.2 : ℕ) + 1) := by
    show ((Nat.add (Nat.add (Nat.add s.lhi (logInc c (Nat.succ s.n)).1) (logInc c (Nat.succ s.n)).2.1)
      (Nat.add (Nat.div c.two1 (logInc c (Nat.succ s.n)).2.2) 1) : ℕ) : ℝ) = _
    rw [hn, hv.two1_eq]; simp only [p_add, p_div]; push_cast; rfl
  have hLlo : ((step c s).llo : ℝ) ≤ Real.log m * 2 ^ c.P := by
    rw [hllo']; nlinarith [lb1, hllo]
  have hLhi : Real.log m * 2 ^ c.P ≤ (step c s).lhi := by
    rw [hlhi']; nlinarith [lb2, hlhi]
  -- the term data
  set o := termOf c s with ho
  have hoLlo : o.llo = (step c s).llo := rfl
  have hoLhi : o.lhi = (step c s).lhi := rfl
  -- sqrt
  have hsq : (o.Rlo : ℝ) ≤ 2 ^ c.P / Real.sqrt m ∧ 2 ^ c.P / Real.sqrt m ≤ o.Rhi := by
    have := sqrt_bracket c.P m (isqrt c m (Nat.div c.oneSq m) s.g) (by omega)
    rw [← hv.oneSq_eq, ← hv.one_eq] at this
    have e1 : o.Rlo = Bool.rec 0 (Bool.rec (Nat.div c.oneSq (Nat.mul m (isqrt c m (Nat.div c.oneSq m) s.g)))
        (isqrt c m (Nat.div c.oneSq m) s.g)
        (Nat.ble (Nat.mul (Nat.mul (isqrt c m (Nat.div c.oneSq m) s.g) (isqrt c m (Nat.div c.oneSq m) s.g)) m)
          c.oneSq)) (Nat.ble 1 (isqrt c m (Nat.div c.oneSq m) s.g)) := by
      show (termOf c s).Rlo = _; simp only [termOf, hn]; rfl
    have e2 : o.Rhi = Bool.rec c.one (Bool.rec (isqrt c m (Nat.div c.oneSq m) s.g)
        (Nat.add (Nat.div c.oneSq (Nat.mul m (isqrt c m (Nat.div c.oneSq m) s.g))) 1)
        (Nat.ble (Nat.mul (Nat.mul (isqrt c m (Nat.div c.oneSq m) s.g) (isqrt c m (Nat.div c.oneSq m) s.g)) m)
          c.oneSq)) (Nat.ble 1 (isqrt c m (Nat.div c.oneSq m) s.g)) := by
      show (termOf c s).Rhi = _; simp only [termOf, hn]; rfl
    rw [e1, e2]; exact this
  set x := 1 / Real.sqrt m with hx
  have hsqrt1 : 1 ≤ Real.sqrt m := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ m))
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one (by linarith)]; exact hsqrt1
  have hxlo : (o.Rlo : ℝ) ≤ x * 2 ^ c.P := by rw [hx, one_div_mul_eq_div]; exact hsq.1
  have hxhi : x * 2 ^ c.P ≤ o.Rhi := by rw [hx, one_div_mul_eq_div]; exact hsq.2
  -- theta and trig
  have htb := theta_bracket c.P c.tn c.tq (Real.log m) o.llo o.lhi
    (by rw [hoLlo]; exact hLlo) (by rw [hoLhi]; exact hLhi)
  rw [← hv.t_eq] at htb
  have htr : o.tr = trig c (Nat.shiftRight (Nat.mul c.tn o.llo) c.tq)
      (Nat.add (Nat.shiftRight (Nat.mul c.tn o.lhi) c.tq) 1) := by
    show (termOf c s).tr = _; simp only [termOf]; rfl
  have hT := trig_sound c t K hv (t * Real.log m) _ _ htb.1 htb.2
  rw [← htr] at hT
  obtain ⟨hcos, hsin, hcm, hsm⟩ := hT
  -- the two term balls
  have hRe := tmul_sound c.P o.Rlo o.Rhi o.tr.cm o.tr.cr o.tr.cs x (Real.cos (t * Real.log m))
    hx0 hx1 hxlo hxhi hcos hcm
  have hIm := tmul_sound c.P o.Rlo o.Rhi o.tr.sm o.tr.sr o.tr.ss x (Real.sin (t * Real.log m))
    hx0 hx1 hxlo hxhi hsin hsm
  obtain ⟨ere, eim⟩ := cpow_term m hmpos t
  have hps : psum t m = psum t n + (m : ℂ) ^ (-((1 : ℂ) / 2 + (t : ℂ) * Complex.I)) := by
    simp only [psum, hm]
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
  refine ⟨hstep_n, by omega, hLlo, hLhi, ?_, ?_⟩
  · -- real part
    rw [hps, Complex.add_re, ere]
    set T := ((Nat.shiftRight (Nat.mul o.Rhi o.tr.cm) c.P : ℕ) : ℝ)
    set R := ((Nat.add (Nat.add (Nat.shiftRight (Nat.mul o.Rhi o.tr.cr) c.P) (Nat.sub o.Rhi o.Rlo)) 2 : ℕ) : ℝ) with hR
    have hcenter : ((step c s).reP : ℝ) - (step c s).reN = ((s.reP : ℝ) - s.reN) + sgn o.tr.cs * T := by
      show ((Bool.rec s.reP (Nat.add s.reP (Nat.shiftRight (Nat.mul o.Rhi o.tr.cm) c.P)) o.tr.cs : ℕ) : ℝ)
        - ((Bool.rec (Nat.add s.reN (Nat.shiftRight (Nat.mul o.Rhi o.tr.cm) c.P)) s.reN o.tr.cs : ℕ) : ℝ) = _
      cases o.tr.cs <;> simp [sgn, T] <;> ring
    have hrad : ((step c s).reR : ℝ) = s.reR + R := by
      show ((Nat.add s.reR (Nat.add (Nat.add (Nat.shiftRight (Nat.mul o.Rhi o.tr.cr) c.P) (Nat.sub o.Rhi o.Rlo)) 2) : ℕ) : ℝ) = _
      rw [hR]; simp only [p_add]; push_cast; ring
    rw [hcenter, hrad]
    have e : ((psum t n).re + x * Real.cos (t * Real.log m)) * 2 ^ c.P
        - (((s.reP : ℝ) - s.reN) + sgn o.tr.cs * T)
        = ((psum t n).re * 2 ^ c.P - ((s.reP : ℝ) - s.reN))
          + (x * Real.cos (t * Real.log m) * 2 ^ c.P - sgn o.tr.cs * T) := by ring
    rw [e]
    exact le_trans (abs_add_le _ _) (add_le_add hre hRe)
  · -- imaginary part:  Im term = -(x sin)
    rw [hps, Complex.add_im, eim]
    set T := ((Nat.shiftRight (Nat.mul o.Rhi o.tr.sm) c.P : ℕ) : ℝ)
    set R := ((Nat.add (Nat.add (Nat.shiftRight (Nat.mul o.Rhi o.tr.sr) c.P) (Nat.sub o.Rhi o.Rlo)) 2 : ℕ) : ℝ) with hR
    have hcenter : ((step c s).imP : ℝ) - (step c s).imN = ((s.imP : ℝ) - s.imN) - sgn o.tr.ss * T := by
      show ((Bool.rec (Nat.add s.imP (Nat.shiftRight (Nat.mul o.Rhi o.tr.sm) c.P)) s.imP o.tr.ss : ℕ) : ℝ)
        - ((Bool.rec s.imN (Nat.add s.imN (Nat.shiftRight (Nat.mul o.Rhi o.tr.sm) c.P)) o.tr.ss : ℕ) : ℝ) = _
      cases o.tr.ss <;> simp [sgn, T] <;> ring
    have hrad : ((step c s).imR : ℝ) = s.imR + R := by
      show ((Nat.add s.imR (Nat.add (Nat.add (Nat.shiftRight (Nat.mul o.Rhi o.tr.sr) c.P) (Nat.sub o.Rhi o.Rlo)) 2) : ℕ) : ℝ) = _
      rw [hR]; simp only [p_add]; push_cast; ring
    rw [hcenter, hrad]
    have e : ((psum t n).im + -(x * Real.sin (t * Real.log m))) * 2 ^ c.P
        - (((s.imP : ℝ) - s.imN) - sgn o.tr.ss * T)
        = ((psum t n).im * 2 ^ c.P - ((s.imP : ℝ) - s.imN))
          - (x * Real.sin (t * Real.log m) * 2 ^ c.P - sgn o.tr.ss * T) := by ring
    rw [e]
    exact le_trans (abs_sub _ _) (add_le_add him hIm)
