-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlab
-- name    : ArdaRH65K_Turing121_EMZetaOfflineSlab
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:07:10.714999+00:00
-- url     : https://prove2.me/theorems/d7f2f67b-1dcf-45cb-82a2-3cd1b01327a7
-- title:
--   EMZetaOfflineSlab certificate definitions
-- statement:
--   This bundle defines error bounds controlling zeta variation over rectangular cells. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{ArbEcon.Off.Cp},\;\mathtt{ArbEcon.Off.corrVar},\;\mathtt{ArbEcon.Off.Wk},\;\mathtt{ArbEcon.Off.taylorErr}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaOfflineSlab.lean

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
import Mathlib.Analysis.Complex.ExponentialBounds
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
/-  EMZetaOfflineSlab.lean -- lane offline: zero-free cells OFF the critical line by a Taylor model
    of the Euler-Maclaurin finite part (the analysis behind a `SlabClear` certificate).

    For a center `c = σc + i tc` (`σc ≥ 0`) and a point `s = c + h`, `‖h‖ ≤ r`:

      T1.  `exp_taylor_le`        -- `‖e^w - Σ_{k≤p} w^k/k!‖ ≤ ‖w‖^(p+1) (p+2)/((p+1)!(p+1))`, `‖w‖ ≤ 1`;
      T2.  `natCpow_neg_add`      -- `n^(-(c+h)) = n^(-c) e^(-h log n)`;
      T3.  `norm_poch_sub_le`     -- `‖(c+h)_k - (c)_k‖ ≤ (U+r)^k - U^k` when every `‖c + j‖ ≤ U`;
      T4.  `emCorr_sub_le`        -- the correction factor moves by at most
                                     `δ = N r / a² + Σ_{i<2K-1} |B_{i+2}|/(i+2)! ((U+r)^(i+1) - U^(i+1)) / N^(i+1)`
                                     (`a ≤ Im c`, `a ≤ Im s`);
      T5.  `emFinite_taylor_le`   -- THE TAYLOR MODEL:
                                     `‖emFinite K (c+h) N - Σ_{k≤p} h^k (-1)^k/k! · W_k‖ ≤ Err`, where
                                     `W_k = Σ_{n<N} (log n)^k n^(-c) + (log N)^k N^(-c) emCorr(c)` and
                                     `Err = C_p (r L)^(p+1) ((N-1) + ‖emCorr(c)‖) + 3 δ`, `L ≥ log N`;
      T6.  `em_remainder_region`  -- the order-(2K+1) remainder uniformly on `1/2 ≤ Re s ≤ 1`,
                                     `0 ≤ Im s ≤ B`;
      T7.  `zeta_ne_zero_of_cell` -- a zero at `s` would force `‖Σ_k h^k …‖ ≤ Err + E`; so
                                     `‖W_0‖ > Σ_{k=1}^p ‖W_k‖ r^k / k! + Err + E` rules it out.

    conjecture1_proved = False.  A finite, local nonvanishing argument; nothing about RH.
-/



open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace ArbEcon

namespace Off

/-! ## T1. The complex exponential Taylor remainder. -/

/-- The Taylor constant `C_p = (p+2) / ((p+1)! (p+1))`. -/
noncomputable def Cp (p : ℕ) : ℝ := ((p + 2 : ℕ) : ℝ) / (((p + 1)! : ℕ) * ((p + 1 : ℕ) : ℝ))





/-! ## T2. Shifting the exponent. -/





/-! ## T3. The Pochhammer symbol moves slowly. -/



/-! ## T4. The correction factor moves slowly. -/

/-- The variation budget `δ` of the correction factor. -/
noncomputable def corrVar (K N : ℕ) (r a U : ℝ) : ℝ :=
  (N : ℝ) * r / a ^ 2
    + ∑ i ∈ Finset.range (2 * K - 1),
        |(bernoulli (i + 2) : ℝ)| / ((i + 2)! : ℝ) * ((U + r) ^ (i + 1) - U ^ (i + 1)) / (N : ℝ) ^ (i + 1)



/-! ## T5. The Taylor model of the finite part. -/

/-- The `k`-th Taylor weight at the center `c`:
    `W_k = Σ_{n<N} (log n)^k n^(-c) + (log N)^k N^(-c) emCorr(c)`. -/
noncomputable def Wk (K N : ℕ) (c : ℂ) (k : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, ((Real.log n : ℝ) : ℂ) ^ k * (n : ℂ) ^ (-c))
    + ((Real.log N : ℝ) : ℂ) ^ k * (N : ℂ) ^ (-c) * emCorr K c N

/-- The error budget of the Taylor model. -/
noncomputable def taylorErr (K N p : ℕ) (c : ℂ) (r L a U : ℝ) : ℝ :=
  Cp p * (r * L) ^ (p + 1) * (((N : ℝ) - 1) + ‖emCorr K c N‖) + 3 * corrVar K N r a U





/-! ## T6. The order-(2K+1) remainder uniformly on a region. -/

/-- The odd-saw remainder constant `C_K = 2 (1 + (π²/6 - 1)/2^(2K-1)) / (2π)^(2K+1)`. -/
noncomputable def CK (K : ℕ) : ℝ := 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1)









/-! ## T7. A zero-free cell. -/





end Off

end ArbEcon


def ArdaRH65K_Turing121_EMZetaOfflineSlab : Nat := 0


