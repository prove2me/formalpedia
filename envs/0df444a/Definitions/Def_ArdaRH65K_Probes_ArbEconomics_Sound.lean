-- Prove2me | Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
-- name    : ArdaRH65K_Probes_ArbEconomics_Sound
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:28:36.312706+00:00
-- url     : https://prove2.me/theorems/6ea74877-bc4b-4fa7-931b-73f14b50f8be
-- title:
--   Real specifications for the fixed-point zeta evaluator
-- statement:
--   This bundle defines the real specifications used by the fixed-point evaluator:
--   the logarithm-series certificate, real Horner recurrence, sine and cosine
--   divisor lists, signed error balls, configuration validity, trigonometric output
--   condition, partial zeta sum, and loop invariant. For example, for scale $S$,
--   integer $m$, and a certificate triple $(A,K,W)$, the logarithm specification is
--
--   $$A=\sum_{j=0}^{K-1}\left\lfloor\frac{S}{m^{j+1}(j+1)}\right\rfloor,
--   \qquad W=m^{K+1}.$$
--
--   The formal integer division convention gives zero when the divisor is zero.
--   The invariant relates the stored logarithm interval and signed real and imaginary
--   balls to $\sum_{j=1}^{n}j^{-1/2-it}$ at the configured scale.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Probes/ArbEconomics_Sound.lean

import Definitions.Def_ArdaRS_Arithmetic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.IntervalCases
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











/-! The evaluator calls the kernel primitives directly; these `rfl` lemmas translate them back to
    notation for the proofs. -/










/-! ## B. the log increment -/

/-- The (S, K, pw) triple is the floor-truncated log(1-x) series with `pw = m^(K+1)`. -/
def LogSpec (one m : ℕ) (r : ℕ × ℕ × ℕ) : Prop :=
  r.1 = ∑ i ∈ range r.2.1, one / (m ^ (i + 1) * (i + 1)) ∧ r.2.2 = m ^ (r.2.1 + 1)









/-! ## C. the square-root bracket -/



/-! ## D. the theta interval -/



/-! ## E. Horner: real recursion, closed form, fixed-point error -/

/-- Real Horner over real divisors, same shape as `horner` (head processed first). -/
noncomputable def hornerR (w : ℝ) : List ℝ → ℝ → ℝ
  | [], h => h
  | d :: ds, h => hornerR w ds (1 - w * h / d)

/-- cos divisors `(2k-1)(2k)` and sin divisors `(2k)(2k+1)`. -/
def fcos (k : ℕ) : ℕ := (2 * k - 1) * (2 * k)
def fsin (k : ℕ) : ℕ := (2 * k) * (2 * k + 1)













/-! ## F. Taylor remainders for cos / sin through `Complex.exp_bound` -/





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/

/-- sign of a Bool (`true` = `+1`). -/
def sgn (b : Bool) : ℝ := Bool.rec (-1) 1 b






/-- signed ball: `|x 2^P - sgn s * m| ≤ r`. -/
def SBall (P : ℕ) (x : ℝ) (m : ℕ) (s : Bool) (r : ℕ) : Prop :=
  |x * 2 ^ P - sgn s * m| ≤ r



/-- The Taylor-core bound constant for `u ≤ 13/16` with `K+1` terms. -/
noncomputable def taylorBnd (K : ℕ) : ℝ :=
  (13 / 16 : ℝ) ^ (2 * K + 2) * (((2 * K + 2).succ : ℝ) * (((2 * K + 2).factorial : ℝ) * (2 * K + 2 : ℕ))⁻¹)







/-- Validity of an evaluator configuration for the height `t` (Horner length `K`).  Every field
    is a closed numeric fact, discharged per instance by `decide`/`rfl`/`norm_num`. -/
structure Valid (c : Cfg) (t : ℝ) (K : ℕ) : Prop where
  one_eq : c.one = 2 ^ c.P
  two1_eq : c.two1 = 2 ^ (c.P + 1)
  oneSq_eq : c.oneSq = 2 ^ (2 * c.P)
  t_eq : t = (c.tn : ℝ) / 2 ^ c.tq
  pi_ball : |Real.pi / 2 * 2 ^ c.P - c.hp| ≤ c.rp
  umax_le : c.umax * 16 ≤ 13 * 2 ^ c.P
  dcos_eq : c.dcos = (divList fcos K).map (fun d : ℕ => c.one * d)
  dsin_eq : c.dsin = (divList fsin K).map (fun d : ℕ => c.one * d)
  tau_ok : (2 : ℝ) ^ c.P * taylorBnd K ≤ c.tau
  hc_eq : ∀ w, c.hc w = horner c.one w c.dcos c.one
  hs_eq : ∀ w, c.hs w = horner c.one w c.dsin c.one
  lnf_eq : ∀ m, c.lnf m = logFix c.one m c.lnK 0 m 0

/-- cos/sin balls of `theta` (plus magnitude caps) -- what `trig` guarantees. -/
def TrigOK (P : ℕ) (θ : ℝ) (tr : Trig) : Prop :=
  SBall P (Real.cos θ) tr.cm tr.cs tr.cr ∧ SBall P (Real.sin θ) tr.sm tr.ss tr.sr ∧
  tr.cm ≤ 2 ^ P ∧ tr.sm ≤ 2 ^ P



/-! ## H. the zeta term, the term product, one step, the run -/







/-- The partial zeta sum `Sum_{k=1}^{n} k^(-(1/2 + i t))`. -/
noncomputable def psum (t : ℝ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.Ico 1 (n + 1), (k : ℂ) ^ (-((1 : ℂ) / 2 + (t : ℂ) * Complex.I))

/-- The loop invariant after `n` terms. -/
def Inv (c : Cfg) (t : ℝ) (n : ℕ) (s : St) : Prop :=
  s.n = n ∧ 1 ≤ n ∧ (s.llo : ℝ) ≤ Real.log n * 2 ^ c.P ∧ Real.log n * 2 ^ c.P ≤ s.lhi ∧
  |(psum t n).re * 2 ^ c.P - ((s.reP : ℝ) - s.reN)| ≤ s.reR ∧
  |(psum t n).im * 2 ^ c.P - ((s.imP : ℝ) - s.imN)| ≤ s.imR













end ArbEcon


def ArdaRH65K_Probes_ArbEconomics_Sound : Nat := 0


