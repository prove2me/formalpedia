-- Prove2me | Definitions.Def_BanditCovariates_SE_Setting
-- name    : BanditCovariates_SE_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T15:09:00.513536+00:00
-- url     : https://prove2.me/theorems/f5a8c727-7725-42d0-babb-f109978455a7
-- title:
--   §2, pp. 4–6 — successive elimination, confidence radius, gaps and regret
-- statement:
--   For $K+1\ge2$ arms, the reward stack $Y_{i,s}$ records the reward on the $(s+1)$st pull of arm $i$. The last arm is the uniquely best arm in the theorem. Define its gap by $\Delta_i=f^*-f_i$, and define $\Delta^-$ as the largest gap strictly below a cutoff $\Delta$, or zero if there is none.
--
--   The paper uses $\overline{\log}(x)=\max\{\log x,1\}$ and
--
--   $$U(\tau,T)=2\sqrt{\frac{2\overline{\log}(T/\tau)}{\tau}}.$$
--
--   Successive elimination begins with every arm active. In each round it pulls each active arm once in increasing order and then retains arms whose empirical mean is within $\gamma U(\tau,T)$ of the largest active empirical mean. The pull sequence concatenates the rounds; regret to a possibly random horizon $N$ is the sum of the gaps of its first $N$ pulls. A stopping round and the comparison function $\phi(x)=\overline{\log}(a x^2)/x$ support the bounds in §2.
--
--   **Formalization Note** Round zero in Lean is paper round one. The paper's prose and proof test after a round, while Policy 1's pseudocode tests before it; this definition follows the prose and proof and keeps equality in the retention test. $U$ and sample means are used only at positive rounds. The fallback of the total pull function is unreachable under the theorem's parameters.
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, pp. 4–6, static problem, (2.1), Policy 1; pp. 7–9, stopping round and φ

import Mathlib
import Definitions.Def_RegretBandits_Stochastic_model

namespace BanditCovariates.SE

open MeasureTheory

/-- The paper's overlined logarithm, `log(x) ∨ 1`. -/
noncomputable def logbar (x : ℝ) : ℝ := max (Real.log x) 1

/-- The confidence radius of (2.1). Used only at positive round indices. -/
noncomputable def U (τ T : ℝ) : ℝ :=
  2 * Real.sqrt (2 * logbar (T / τ) / τ)

/-- The largest empirical mean among a finite active set. The empty branch is unreachable
for the successive-elimination policy with positive confidence radius. -/
noncomputable def maxAverage {Ω : Type*} {K : ℕ}
    (Y : Fin (K + 1) → ℕ → Ω → ℝ) (ω : Ω)
    (s : Finset (Fin (K + 1))) (τ : ℕ) : ℝ :=
  if h : s.Nonempty then
    s.sup' h (fun i => RegretBandits.Stochastic.sampleMean Y i τ ω)
  else 0

/-- `active ... r` is the set at the beginning of paper round `r+1`. Every arm is pulled
once in the round and elimination then uses its mean from the first `r+1` rewards. -/
noncomputable def active {Ω : Type*} {K : ℕ}
    (T : ℕ) (γ : ℝ) (Y : Fin (K + 1) → ℕ → Ω → ℝ) (ω : Ω) :
    ℕ → Finset (Fin (K + 1))
  | 0 => Finset.univ
  | r + 1 =>
      let s := active T γ Y ω r
      s.filter (fun i =>
        maxAverage Y ω s (r + 1) -
          RegretBandits.Stochastic.sampleMean Y i (r + 1) ω ≤
            γ * U (r + 1) T)

/-- Pulls in the first `t+1` rounds, listed by round and then increasing arm index. -/
noncomputable def pullPrefix {Ω : Type*} {K : ℕ}
    (T : ℕ) (γ : ℝ) (Y : Fin (K + 1) → ℕ → Ω → ℝ) (ω : Ω)
    (t : ℕ) : List (Fin (K + 1)) :=
  ((List.range (t + 1)).map
    (fun r => (active T γ Y ω r).sort (· ≤ ·))).flatten

/-- The `(t+1)`-st arm pulled by round-based SE. Under the theorem's parameters every
round is nonempty, so the fallback arm is never selected. -/
noncomputable def sePull {Ω : Type*} {K : ℕ}
    (T : ℕ) (γ : ℝ) (Y : Fin (K + 1) → ℕ → Ω → ℝ) (ω : Ω)
    (t : ℕ) : Fin (K + 1) :=
  (pullPrefix T γ Y ω t).getD t (Fin.last K)

/-- The gap from the last, best arm of the sorted model. -/
def gap {K : ℕ} (f : Fin (K + 1) → ℝ) (i : Fin (K + 1)) : ℝ :=
  f (Fin.last K) - f i

/-- The largest gap strictly below the cutoff, or zero if there is none. -/
noncomputable def deltaMinus {K : ℕ} (f : Fin (K + 1) → ℝ) (Δ : ℝ) : ℝ :=
  let s := Finset.univ.filter (fun i : Fin (K + 1) => gap f i < Δ)
  if h : s.Nonempty then s.sup' h (gap f) else 0

/-- The first positive integer round whose confidence radius falls below `2Δ/(3γ)`.
For positive Δ and γ, this is the ceiling of the paper's real solution τ*. -/
noncomputable def stoppingRound (T : ℕ) (γ Δ : ℝ) : ℕ :=
  sInf {τ : ℕ | 1 ≤ τ ∧ (3 / 2 : ℝ) * γ * U τ T ≤ Δ}

/-- The empirical gap between the best arm and arm `i` after `τ` pulls of each. -/
noncomputable def estimatedGap {Ω : Type*} {K : ℕ}
    (Y : Fin (K + 1) → ℕ → Ω → ℝ) (i : Fin (K + 1))
    (τ : ℕ) (ω : Ω) : ℝ :=
  RegretBandits.Stochastic.sampleMean Y (Fin.last K) τ ω -
    RegretBandits.Stochastic.sampleMean Y i τ ω

/-- The paper's cumulative regret through the random horizon. -/
noncomputable def regret {Ω : Type*} {K : ℕ}
    (f : Fin (K + 1) → ℝ) (T : ℕ) (γ : ℝ)
    (Y : Fin (K + 1) → ℕ → Ω → ℝ) (N : Ω → ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range (N ω), gap f (sePull T γ Y ω t)

/-- The function φ used in the final comparison on p. 9, with the page's `T` reading. -/
noncomputable def phi (a x : ℝ) : ℝ := logbar (a * x ^ 2) / x

end BanditCovariates.SE


