-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
-- name    : ArdaRH65K_Turing121_EMZetaHigh
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:05:26.011168+00:00
-- url     : https://prove2.me/theorems/bf7f2237-7870-438b-9f04-5080801864a9
-- title:
--   EMZetaHigh certificate definitions
-- statement:
--   This bundle defines higher-order Euler–Maclaurin sums, correction terms, and remainders. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{ZetaReflection.EMHigh.poch},\;\mathtt{ZetaReflection.EMHigh.emC},\;\mathtt{ZetaReflection.EMHigh.emTail},\;\mathtt{ZetaReflection.EMHigh.emFiniteM}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaHigh.lean

import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
/-  EMZetaHigh.lean -- the GENERAL-ORDER Euler-Maclaurin representation of ζ with an explicit,
    PROVED remainder bound (lane emhigh, memo ANDURIL_ARB_DISCHARGE_2026-09-23 section 3 / step 2
    node `AND_em_zeta_orderK`).

    The island's order-3 chain (`EMZetaTail.em_zeta_strip3`) stops at the saw-3 remainder.  This
    file raises the order to ANY `m ≥ 1` by induction, so the finite part carries every Bernoulli
    correction `B_2, B_4, …, B_{2K}` and the remainder decays like `N^{-(Re s + 2K - 1)}`:

      M1.  `poch`, `emC`            -- rising factorial `s(s+1)…(s+k-1)` and the k-th x-derivative
                                       coefficient `(-1)^k (s)_k` of `x^{-s}`.
      M2.  `em_tail_step`           -- ONE saw-order-raising step on the tail `[N, ∞)`, any k ≥ 1
                                       (generalises `EMZetaTail.em_tail2_step` / `em_tail3_step`).
      M3.  `emTail_unroll`          -- the induction: the saw-1 tail equals the explicit Bernoulli
                                       sum plus `(-1)^(m-1) emTail m / m!`.
      M4.  `em_zeta_order`          -- the general-order identity for `riemannZeta` on `Re s > 0`.
      M5.  `emTail_norm_le`         -- remainder bound from any sup bound of the order-m saw.
      M6.  `abs_sawBernoulli_even_le` -- `|B̃_{2K}(x)| ≤ |B_{2K}|` for every K ≥ 1 (Mathlib's
                                       Fourier cosine series of the Bernoulli polynomials).
      M6'. `abs_sawBernoulli_odd_le`  -- `|B̃_{2K+1}(x)| ≤ 2(2K+1)!/(2π)^{2K+1} (1 + (π²/6−1)/2^{2K−1})`
                                       (Fourier sine series + `ζ(p) ≤ 1 + (π²/6−1)/2^{p−2}`).
      M7.  `em_zeta_orderK_enclosure` -- THE THEOREM (general K), even-saw remainder:
             ‖ζ(s) − emFinite K s N‖ ≤ |B_{2K}|/(2K)! · ‖(s)_{2K}‖ · N^{-(σ+2K-1)}/(σ+2K-1),
           and `em_zeta_orderK_enclosure_odd`, the same finite part with the saw-(2K+1) remainder
             ‖ζ(s) − emFinite K s N‖ ≤ 2(1+(π²/6−1)/2^{2K−1})/(2π)^{2K+1} · ‖(s)_{2K+1}‖ · N^{-(σ+2K)}/(σ+2K)
           (smaller by about `|s+2K|/(2πN)`), with the evaluator-facing Dirichlet form
           `emFinite = Σ_{n<N} n^{-s} + N^{-s}·emCorr`; `em_line_remainder_le` / `_odd_le` are the
           critical-line forms with a rational majorant `Q` of the Pochhammer norm and `r ≤ √N`.
      M8.  exact Bernoulli numbers `B_2 … B_12` (the K ≤ 6 constants).

    conjecture1_proved = False.  A classical analysis lemma (Euler-Maclaurin), not a proof of RH.
-/



open MeasureTheory intervalIntegral Set Filter Topology Complex
open scoped Real Nat

namespace ZetaReflection

namespace EMHigh

/-! ## M1. Rising factorial and the derivative coefficients of `x^{-s}`. -/

/-- The rising factorial `(s)_k = s (s+1) ⋯ (s+k-1)`. -/
noncomputable def poch (s : ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => poch s k * (s + k)







/-- `d^k/dx^k x^{-s} = emC s k · x^{-s-k}` with `emC s k = (-1)^k (s)_k`. -/
noncomputable def emC (s : ℂ) (k : ℕ) : ℂ := (-1) ^ k * poch s k









/-! ## M2. The general saw-order-raising step on the tail `[N, ∞)`. -/





/-- The order-k tail integral `∫_N^∞ B̃_k(x) · emC s k · x^{-s-k} dx`. -/
noncomputable def emTail (s : ℂ) (N k : ℕ) : ℂ :=
  ∫ x in Ioi (N : ℝ), (sawBernoulli k x : ℂ) * (emC s k * (x : ℂ) ^ (-s - k))



/-! ## M3. The induction: unrolling the saw-1 tail to any order. -/





/-! ## M4. The general-order identity for `riemannZeta`. -/

/-- The explicit order-`m` finite part, Dirichlet form:
    `Σ_{n=1}^{N-1} n^{-s} + N^{1-s}/(s-1) + N^{-s}/2 + Σ_{i<m-1} B_{i+2} (s)_{i+1} N^{-s-(i+1)}/(i+2)!`. -/
noncomputable def emFiniteM (m : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s) / (s - 1) + (N : ℂ) ^ (-s) / 2
    + ∑ i ∈ Finset.range (m - 1), (bernoulli (i + 2) : ℂ) * poch s (i + 1) / ((i + 2)! : ℂ)
        * (N : ℂ) ^ (-s - ((i + 1 : ℕ) : ℂ))



/-! ## M5. The remainder bound from a sup bound of the order-m saw. -/



/-! ## M6. The sup bound `|B̃_{2K}(x)| ≤ |B_{2K}|` (general K ≥ 1). -/





/-! ## M6'. The odd sup bound `|B̃_{2K+1}(x)| ≤ 2 (2K+1)! ζ(2K+1) / (2π)^{2K+1}` (general K ≥ 1),
    with the elementary majorant `ζ(p) ≤ 1 + (π²/6 − 1)/2^(p−2)`. -/







/-! ## M7. THE THEOREM: general-K enclosure, evaluator (Dirichlet) form. -/

/-- The evaluator-facing correction factor, so that `emFinite K s N = Σ_{n<N} n^{-s} + N^{-s}·emCorr`:
    `emCorr K s N = N/(s-1) + 1/2 + Σ_{i<2K-1} B_{i+2} (s)_{i+1} / ((i+2)! N^{i+1})`
    (the order-(2K+1) Euler-Maclaurin correction: `B_2, B_4, …, B_{2K}`; odd `B`'s vanish). -/
noncomputable def emCorr (K : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  (N : ℂ) / (s - 1) + 1 / 2
    + ∑ i ∈ Finset.range (2 * K - 1),
        (bernoulli (i + 2) : ℂ) * poch s (i + 1) / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1)

/-- The order-(2K+1) Euler-Maclaurin finite part of ζ: the Dirichlet sum `Σ_{n=1}^{N-1} n^{-s}`
    plus `N^{-s}` times the correction factor. -/
noncomputable def emFinite (K : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (-s) * emCorr K s N









/-! ## M7'. The critical line: rational remainder and real/imaginary parts of the correction. -/

/-- `Π_{j<k} ((σ+j)² + t²)`, which is `‖(σ + i t)_k‖²`. -/
noncomputable def pochNormSq (σ t : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => pochNormSq σ t k * ((σ + k) ^ 2 + t ^ 2)









/-! ## M7''. Real and imaginary parts of the correction factor on a vertical line. -/

/-- Real and imaginary parts of `(σ + i t)_k` by the complex product recursion. -/
noncomputable def pochRI (σ t : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | k + 1 => ((pochRI σ t k).1 * (σ + k) - (pochRI σ t k).2 * t,
              (pochRI σ t k).1 * t + (pochRI σ t k).2 * (σ + k))



/-- `Re (emCorr K (σ + i t) N)` in closed real form. -/
noncomputable def emCorrRe (K : ℕ) (σ t : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) * (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) + 1 / 2
    + ∑ i ∈ Finset.range (2 * K - 1),
        (bernoulli (i + 2) : ℝ) / ((i + 2)! : ℝ) / (N : ℝ) ^ (i + 1) * (pochRI σ t (i + 1)).1

/-- `Im (emCorr K (σ + i t) N)` in closed real form. -/
noncomputable def emCorrIm (K : ℕ) (σ t : ℝ) (N : ℕ) : ℝ :=
  -((N : ℝ) * t) / ((σ - 1) ^ 2 + t ^ 2)
    + ∑ i ∈ Finset.range (2 * K - 1),
        (bernoulli (i + 2) : ℝ) / ((i + 2)! : ℝ) / (N : ℝ) ^ (i + 1) * (pochRI σ t (i + 1)).2





/-! ## M8. The exact Bernoulli numbers `B_2 … B_12` (the constants of K ≤ 6). -/






















end EMHigh

end ZetaReflection


def ArdaRH65K_Turing121_EMZetaHigh : Nat := 0


