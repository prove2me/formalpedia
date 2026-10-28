-- Prove2me | solution 1 for ArbEcon.Off.ampl_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:46:07.715355+00:00
-- url     : https://prove2.me/submissions/fc7c0683-64e8-4f59-8915-c5c9f5720a75

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









theorem two_pow_pos' (P : ℕ) : (0 : ℝ) < (2 : ℝ) ^ P := by positivity

/-! The evaluator calls the kernel primitives directly; these `rfl` lemmas translate them back to
    notation for the proofs. -/

@[simp] theorem p_mul (a b : ℕ) : Nat.mul a b = a * b := rfl








/-! ## B. the log increment -/











/-! ## C. the square-root bracket -/



/-! ## D. the theta interval -/



/-! ## E. Horner: real recursion, closed form, fixed-point error -/


















/-! ## F. Taylor remainders for cos / sin through `Complex.exp_bound` -/





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/


























/-! ## H. the zeta term, the term product, one step, the run -/























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

@[simp] theorem p_pow (a b : ℕ) : Nat.pow a b = a ^ b := rfl

/-! ## A. Specifications. -/















/-! ## B. The bracket-times-ball product. -/



/-! ## C. Term balls, accumulation, the log chain. -/







/-! ## D. The validated amplitude bracket. -/

theorem rpow_neg_sigma_pow (m : ℕ) (hm : 1 ≤ m) (a b q : ℕ) (hq : 1 ≤ q) :
    ((m : ℝ) ^ (-(((a : ℝ) - b) / q))) ^ q * (m : ℝ) ^ a = (m : ℝ) ^ b := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  rw [← Real.rpow_natCast ((m : ℝ) ^ _), ← Real.rpow_mul hmpos.le]
  have e : -(((a : ℝ) - b) / q) * (q : ℝ) = (b : ℝ) - a := by field_simp; ring
  rw [e, Real.rpow_sub hmpos, Real.rpow_natCast, Real.rpow_natCast]
  have : (0 : ℝ) < (m : ℝ) ^ a := by positivity
  field_simp



/-! ## E. The term `m^(-s)`. -/





/-! ## F. The partial sums. -/







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



theorem solution (c : Cfg) (o : OCfg) (hone : c.one = 2 ^ c.P) (hQ : o.oneQ = 2 ^ (o.q * c.P))
    (hq : 1 ≤ o.q) (m gprev : ℕ) (hm : 1 ≤ m) :
    ((ampl c o m gprev).2.1 : ℝ) ≤ (m : ℝ) ^ (-(((o.a : ℝ) - o.b) / o.q)) * 2 ^ c.P ∧
    (m : ℝ) ^ (-(((o.a : ℝ) - o.b) / o.q)) * 2 ^ c.P ≤ ((ampl c o m gprev).2.2 : ℝ) := by
  set X : ℝ := (m : ℝ) ^ (-(((o.a : ℝ) - o.b) / o.q)) with hX
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hX0 : 0 < X := Real.rpow_pos_of_pos hmpos _
  have hP : (0 : ℝ) < 2 ^ c.P := two_pow_pos' c.P
  set Y : ℝ := X * 2 ^ c.P with hY
  have hY0 : 0 ≤ Y := by positivity
  have hma : (0 : ℝ) < (m : ℝ) ^ o.a := by positivity
  have hq0 : o.q ≠ 0 := by omega
  -- the key identity  Y^q m^a = 2^(qP) m^b
  have hkey : Y ^ o.q * (m : ℝ) ^ o.a = (2 : ℝ) ^ (o.q * c.P) * (m : ℝ) ^ o.b := by
    have h1 := rpow_neg_sigma_pow m hm o.a o.b o.q hq
    rw [← hX] at h1
    calc Y ^ o.q * (m : ℝ) ^ o.a = (X ^ o.q * (m : ℝ) ^ o.a) * ((2 : ℝ) ^ c.P) ^ o.q := by
          rw [hY, mul_pow]; ring
      _ = (m : ℝ) ^ o.b * (2 : ℝ) ^ (o.q * c.P) := by rw [h1, ← pow_mul, mul_comm c.P o.q]
      _ = (2 : ℝ) ^ (o.q * c.P) * (m : ℝ) ^ o.b := by ring
  set g := rootLoop o.q (Nat.mul o.oneQ (Nat.pow m o.b)) (Nat.pow m o.a) o.nfuel
    (Nat.add (Nat.add gprev (Nat.div gprev (Nat.sub m 1))) 2) with hg
  have hlo_eq : (ampl c o m gprev).2.1 = Bool.rec 0 g
      (Nat.ble (Nat.mul (Nat.pow g o.q) (Nat.pow m o.a)) (Nat.mul o.oneQ (Nat.pow m o.b))) := rfl
  have hhi_eq : (ampl c o m gprev).2.2 = Bool.rec (Nat.mul c.one (Nat.pow m o.b)) (Nat.succ g)
      (Nat.ble (Nat.mul o.oneQ (Nat.pow m o.b)) (Nat.mul (Nat.pow (Nat.succ g) o.q) (Nat.pow m o.a))) :=
    rfl
  constructor
  · rw [hlo_eq]
    cases hb : Nat.ble (Nat.mul (Nat.pow g o.q) (Nat.pow m o.a)) (Nat.mul o.oneQ (Nat.pow m o.b)) with
    | false => simp only; push_cast; exact hY0
    | true =>
      simp only
      have hle := Nat.le_of_ble_eq_true hb
      simp only [p_mul, p_pow] at hle
      have hleR : (g : ℝ) ^ o.q * (m : ℝ) ^ o.a ≤ (2 : ℝ) ^ (o.q * c.P) * (m : ℝ) ^ o.b := by
        have := (Nat.cast_le (α := ℝ)).mpr hle
        rw [hQ] at this; push_cast at this; exact this
      rw [← hkey] at hleR
      have hgq : (g : ℝ) ^ o.q ≤ Y ^ o.q := le_of_mul_le_mul_right hleR hma
      exact le_of_pow_le_pow_left₀ hq0 hY0 hgq
  · rw [hhi_eq]
    cases hb : Nat.ble (Nat.mul o.oneQ (Nat.pow m o.b)) (Nat.mul (Nat.pow (Nat.succ g) o.q) (Nat.pow m o.a)) with
    | false =>
      simp only
      -- fallback: m^(-σ) ≤ m^b
      have hexp : -(((o.a : ℝ) - o.b) / o.q) ≤ (o.b : ℝ) := by
        have hqR : (1 : ℝ) ≤ o.q := by exact_mod_cast hq
        have ha0 : (0 : ℝ) ≤ o.a := Nat.cast_nonneg _
        have hb0 : (0 : ℝ) ≤ o.b := Nat.cast_nonneg _
        rw [neg_div', div_le_iff₀ (by linarith)]
        nlinarith
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hXle : X ≤ (m : ℝ) ^ o.b := by
        rw [hX, ← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hm1 hexp
      rw [hone]; simp only [p_mul, p_pow]; push_cast
      rw [hY]; nlinarith
    | true =>
      simp only
      have hle := Nat.le_of_ble_eq_true hb
      simp only [p_mul, p_pow] at hle
      have hleR : (2 : ℝ) ^ (o.q * c.P) * (m : ℝ) ^ o.b ≤ ((g : ℝ) + 1) ^ o.q * (m : ℝ) ^ o.a := by
        have := (Nat.cast_le (α := ℝ)).mpr hle
        rw [hQ] at this; push_cast at this; exact this
      rw [← hkey] at hleR
      have hgq : Y ^ o.q ≤ ((g : ℝ) + 1) ^ o.q := le_of_mul_le_mul_right hleR hma
      have := le_of_pow_le_pow_left₀ hq0 (by positivity) hgq
      push_cast
      exact this
