-- Prove2me | Definitions.Def_EffRobustLearn_alg1
-- name    : EffRobustLearn_alg1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:39:43.701068+00:00
-- url     : https://prove2.me/theorems/13562ae8-a897-4589-9ba8-eb92ec57362a
-- title:
--   Algorithm 1 (Online Frank–Wolfe), one run
-- statement:
--   One run of Online-Frank-Wolfe($\bar S_{\mathrm{inp}},S_{\mathrm{ref}},\varepsilon,\delta$, ERM oracle) starts at $\bar\mu_1=c_0$. In round $t=1,\dots,T$ it sets $h_t=\mathrm{maj}_k\circ\bar\mu_t$, finds $c_t$ by one weighted ERM call (Fact 3.2) on $\bar S_{\mathrm{inp}}\cup\{(x,1):x\in S_{\mathrm{ref}}\}$ with weights (3.8), accuracy $\gamma_t/25$ and failure probability $\delta/T$, and updates $\bar\mu_{t+1}=(1-\gamma_t)\bar\mu_t+\gamma_tc_t$. It returns $\bar h_T=T^{-1}\sum_th_t$, from which the randomized hypothesis is $h(x)\sim\mathrm{Rad}(\bar h_T(x))$.
--
--   **Formalization Note** The run is a deterministic function of the oracle, $c_0$, the samples and a seed of i.i.d. uniform coordinates on $[0,1]$, one family per round. The paper makes no call when the gradient vanishes and then chooses any $c_t\in C$; here that case is $O([\,])$, reached through all-zero weights, and is counted as a call, so the count is exactly $T$. Work is counted in a unit-cost model: $\sum_{t\le T}[(n+m)(t+k+2)+2N_t+1]$ with $N_t$ the synthetic size of round $t$. No Turing machine is defined over an arbitrary domain $X$, so the paper's "time" is read as this count.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Algorithm 1, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_EffRobustLearn_weightedERM
import Definitions.Def_EffRobustLearn_weightVec

open MeasureTheory

namespace EffRobustLearn

/-- The weighted-ERM step of round `t` of Algorithm 1, line 7, Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.14: Fact 3.2 on
`S̄inp ∪ {(x, 1) : x ∈ Sref}`, indices in their fixed order, with weights (3.8), weight bound `b` of p.16, accuracy `γ_t/25` and failure
probability `δ/T`, on the seed coordinates of round `t`. It reads `c` only at rounds `< t`. -/
noncomputable def roundStep {X : Type*} {n m : ℕ} (O : List (X × Bool) → X → Bool) (CF ε δ : ℝ)
    (c0 : X → Bool) (Sinp : Fin n → X × Bool) (Sref : Fin m → X) (ω : ℕ × ℕ → unitInterval)
    (c : ℕ → X → Bool) (t : ℕ) : SamplerRun X :=
  weightedERM O CF (weightBound n m (numRounds ε)) (stepSize t / 25) (δ / (numRounds ε : ℝ))
    (weightedData Sinp Sref ∘ finSumFinEquiv.symm)
    (weightVec ε c0 c Sinp Sref t ∘ finSumFinEquiv.symm)
    (fun j => ω (t, j))

/-- The concepts `c_1, …, c_t` chosen by the first `t` rounds, by recursion on `t`; later entries are still `c0`. -/
noncomputable def runConcepts {X : Type*} {n m : ℕ} (O : List (X × Bool) → X → Bool) (CF ε δ : ℝ)
    (c0 : X → Bool) (Sinp : Fin n → X × Bool) (Sref : Fin m → X) (ω : ℕ × ℕ → unitInterval) :
    ℕ → ℕ → X → Bool
  | 0 => fun _ => c0
  | t + 1 => Function.update (runConcepts O CF ε δ c0 Sinp Sref ω t) (t + 1)
      (roundStep O CF ε δ c0 Sinp Sref ω (runConcepts O CF ε δ c0 Sinp Sref ω t) (t + 1)).concept

/-- The record of one run of Algorithm 1: iterates, concepts, hypotheses, output, oracle calls and work. -/
structure RunRecord (X : Type*) where
  mu : ℕ → X → ℝ
  c : ℕ → X → Bool
  h : ℕ → X → ℝ
  hbar : X → ℝ
  calls : ℕ
  work : ℕ

/-- Algorithm 1, p.14: Online-Frank-Wolfe(`S̄inp`, `Sref`, `ε`, `δ`, ERM oracle), started at `μ̄_1 = c0`, on the seed `ω`.

**Formalization Note.**
* The arbitrary `c ∈ C` of line 3 is the parameter `c0`, and the oracle is the parameter `O`; the theorems quantify over all of them.
* The seed `ω : ℕ × ℕ → [0, 1]` has i.i.d. uniform coordinates under `seedLaw`; `ω (t, j)` drives draw `j` of round `t`, so all draws are independent.
* The paper makes no call when `∇F_t(μ̄_t[S]) = 0` and then chooses any `c_t ∈ C`. Here that case is `O []`, reached through the all-zero weights, and is counted as a call. So `calls = T`.
* `work` is `∑_{t≤T} [(n + m)(t + k + 2) + 2 N_t + 1]` in a unit-cost model, with `N_t` the synthetic size of round `t`: per sample point and round,
  one update of `μ̄_t`, `k + 1` terms for `maj_k`, `t` terms for the weights (3.8) and one term of the final average; a draw and a write per synthetic example; `1` for the oracle call. Evaluating an oracle's answer at a point is a unit operation. -/
noncomputable def alg1 {X : Type*} {n m : ℕ} (O : List (X × Bool) → X → Bool) (CF ε δ : ℝ)
    (c0 : X → Bool) (Sinp : Fin n → X × Bool) (Sref : Fin m → X) (ω : ℕ × ℕ → unitInterval) :
    RunRecord X :=
  let c := runConcepts O CF ε δ c0 Sinp Sref ω (numRounds ε)
  { mu := muSeq c0 c
    c := c
    h := hSeq ε c0 c
    hbar := hbarSeq ε c0 c
    calls := ∑ t ∈ Finset.Icc 1 (numRounds ε), (roundStep O CF ε δ c0 Sinp Sref ω c t).calls
    work := ∑ t ∈ Finset.Icc 1 (numRounds ε),
      ((n + m) * (t + majParam ε + 1) + (roundStep O CF ε δ c0 Sinp Sref ω c t).work) }

/-- The law of the seed of `alg1`: i.i.d. uniform coordinates on `[0, 1]`. -/
noncomputable def seedLaw : Measure (ℕ × ℕ → unitInterval) :=
  Measure.infinitePi fun _ => (volume : Measure unitInterval)

end EffRobustLearn


