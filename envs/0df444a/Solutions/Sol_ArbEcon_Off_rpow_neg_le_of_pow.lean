-- Prove2me | solution 1 for ArbEcon.Off.rpow_neg_le_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:48:13.953511+00:00
-- url     : https://prove2.me/submissions/b56dd291-59b7-4121-941e-c0ee59aad809

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.IntervalCases
namespace ArbEcon
end ArbEcon
namespace ArbEcon.OrderK
end ArbEcon.OrderK
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
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


/-  EMZetaOfflineCheck.lean -- lane offline: the KERNEL-ONLY assembly of an order-(2K+1)
    Euler-Maclaurin enclosure of ζ(σ + i t) at a rational `σ = (a - b)/q` (any sign, `σ > -2K`) and a
    dyadic `t = tn / 2^tq > 0`.

      * `gpochG`, `pochRI_eq_gpochG`  -- the Gaussian-integer rising factorial
                                         `(q u)^k (σ + i t)_k` (`u = 2^tq`);
      * `corrDataG`, `corr_eqG`       -- the exact correction factor `emCorr K (σ + i t) N` as
                                         `(BreN + i BimN) / BD` in integers;
      * `pnG`, `pochNormSq_eq_pnG`    -- the remainder numerator `Π_{j<k} ((sN + j q)² u² + tn² q²)`;
      * `rpow_neg_le_of_pow`          -- `N^(-σ) ≤ Rn/Rd` from `Rd^q N^b ≤ Rn^q N^a`;
      * `remOddG`, `remOddG_sound`    -- the odd-saw remainder of `EMOff.em_zeta_orderK_enclosure_odd_ext`
                                         (valid off the line, `σ > -2K`) as `EN/ED`;
      * `zeta_ballG`                  -- the evaluator balls after `N-1` and `N` terms plus any remainder
                                         bound give balls for `Re ζ(s)`, `Im ζ(s)`;
      * `checkG`, `checkG_sound`      -- ONE Boolean checker (run by `decide +kernel`) and its
                                         soundness: `lo/D ≤ Re ζ(σ + i t) ≤ hi/D`, same for `Im`.

    conjecture1_proved = False.  Finite interval arithmetic at one point; nothing about RH.
-/




open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

section
namespace ArbEcon
end ArbEcon
open ArbEcon

section
namespace ArbEcon.Off
end ArbEcon.Off
open ArbEcon.Off

open ArbEcon.OrderK (betaN Lbeta  )

/-! ## A. The Gaussian-integer rising factorial at `σ = sN/q`, `t = tn/u`. -/















/-! ## B. The remainder numerator and `N^(-σ)`. -/






theorem solution (N : ℕ) (hN : 1 ≤ N) (a b q : ℕ) (hq : 1 ≤ q) (Rn Rd : ℕ)
    (hRd : 0 < Rd) (h : Rd ^ q * N ^ b ≤ Rn ^ q * N ^ a) :
    (N : ℝ) ^ (-(((a : ℝ) - b) / q)) ≤ (Rn : ℝ) / Rd := by
  set X := (N : ℝ) ^ (-(((a : ℝ) - b) / q)) with hX
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hX0 : 0 ≤ X := by positivity
  have hRdR : (0 : ℝ) < Rd := by exact_mod_cast hRd
  have hNa : (0 : ℝ) < (N : ℝ) ^ a := by positivity
  have hid := rpow_neg_sigma_pow N hN a b q hq
  rw [← hX] at hid
  have hR : (Rd : ℝ) ^ q * (N : ℝ) ^ b ≤ (Rn : ℝ) ^ q * (N : ℝ) ^ a := by exact_mod_cast h
  have hXq : X ^ q ≤ ((Rn : ℝ) / Rd) ^ q := by
    rw [div_pow]
    have hRdq : (0 : ℝ) < (Rd : ℝ) ^ q := by positivity
    rw [le_div_iff₀ hRdq]
    have : X ^ q * (N : ℝ) ^ a * (Rd : ℝ) ^ q ≤ (Rn : ℝ) ^ q * (N : ℝ) ^ a := by
      rw [hid]; linarith
    nlinarith
  exact le_of_pow_le_pow_left₀ (by omega) (by positivity) hXq
