-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_ciModel
-- name    : BauerleRiederMDP_RegimeSwitching_ciModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:51.920207+00:00
-- url     : https://prove2.me/theorems/c3885416-8485-40d7-bc9c-2d7a99d1fb68
-- title:
--   Markov Decision Model of the multiperiod consumption-investment problem (4.16)
-- statement:
--   The **multiperiod consumption-investment problem** (4.16) is the Markov Decision Model with
--
--   1. state space $E=[0,\infty)$ (wealth) and action space $A=\mathbb R_+\times\mathbb R^d$ (consumption $c$, amounts $a$ in the risky assets);
--   2. $D_n(x)=\{(c,a): 0\le c\le x,\ (1+i_{n+1})(x-c+a\cdot R_{n+1})\ge0\ \mathbb P\text{-a.s.}\}$;
--   3. disturbances $z\in\mathbb R^d$ with law $Q^Z_n=$ the distribution of $R_{n+1}$, independent of $(x,c,a)$;
--   4. transition $T_n(x,c,a,z)=(1+i_{n+1})(x-c+a\cdot z)$ and reward $r_n(x,c,a)=U_c(c)$;
--
--   the terminal reward $g_N=U_p$ is supplied with the value function $V_n$.
--
--   **Formalization Note** The interest rates $i_n$ and the laws $\mu_n$ of $R_n$ are parameters. The state space is $\mathbb R_{\ge0}$ and the next wealth is truncated at $0$; for admissible actions it is nonnegative almost surely, so the truncation changes no law of the controlled process.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.3, p.94 (PDF p.108)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_DisturbanceMDM
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BauerleRiederMDP.RegimeSwitching

/-- The Markov Decision Model of the **multiperiod consumption-investment problem** (4.16)
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §4.3, p.94, PDF p.108): state space `E = [0, ∞)` (wealth), action space
`A = ℝ_+ × ℝ^d` (consumption `c`, amounts `a` invested in the risky assets),
`D_n(x) = {(c, a) | 0 ≤ c ≤ x, (1 + i_{n+1})(x − c + a · R_{n+1}) ∈ E ℙ-a.s.}`, disturbance
space `ℝ^d`, `T_n(x, c, a, z) = (1 + i_{n+1})(x − c + a · z)`, `Q^Z_n(· | x, c, a)` = the
distribution of `R_{n+1}` (independent of `(x, c, a)`), and `r_n(x, c, a) = U_c(c)`; the terminal
reward `g_N = U_p` is passed to `valueFunction`.

**Formalization Note.** `i n = i_n` and `μ n` = the law of the relative risk `R_n`
(`n = 1, …, N`). The state space is `ℝ≥0`, so `T_n` is followed by `Real.toNNReal`; for
admissible `(c, a)` the wealth `(1 + i_{n+1})(x − c + a · z)` is `≥ 0` for `μ_{n+1}`-a.e. `z`,
so the truncation changes no law of the controlled process. That `Q^Z_n` is the law of
`R_{n+1}` regardless of the past is the book's independence of `R_1, …, R_N` (§4.2). -/
noncomputable def ciModel {d : ℕ} (i : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (Fin d → ℝ))
    (Uc : ℝ → ℝ) : DisturbanceMDM ℝ≥0 (ℝ × (Fin d → ℝ)) (Fin d → ℝ) where
  D n x := {ca | 0 ≤ ca.1 ∧ ca.1 ≤ x ∧
    ∀ᵐ z ∂(μ (n + 1) : Measure (Fin d → ℝ)), 0 ≤ (1 + i (n + 1)) * (x - ca.1 + ∑ k, ca.2 k * z k)}
  T n s z := Real.toNNReal ((1 + i (n + 1)) * (s.1 - s.2.1 + ∑ k, s.2.2 k * z k))
  measurable_T n := by
    apply Measurable.real_toNNReal
    fun_prop
  QZ n := Kernel.const _ (μ (n + 1))
  isMarkovKernel_QZ n := inferInstance
  r _ s := Uc s.2.1

end BauerleRiederMDP.RegimeSwitching


