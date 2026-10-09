-- Prove2me | Definitions.Def_GreedWorks_OnlineTime_StochasticGreedy
-- name    : GreedWorks_OnlineTime_StochasticGreedy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:06:20.154989+00:00
-- url     : https://prove2.me/theorems/20f42922-acfb-4424-9e17-b00e0420604f
-- title:
--   §6.3, p. 17, and Lemma 8, p. 18 — the stochastic greedy policy S_{i,ℓ} = max{s_{i,ℓ}, S_{i,ℓ−1} + P_{i,ℓ−1}} and h(∆)
-- statement:
--   Let $(m,s)$ be an outcome of the online-time greedy algorithm run on the means $p_{ij}=\mathbb E[P_{ij}]$; this is the **nominal schedule**. The **greedy policy for stochastic processing times** keeps the assignment $m$ and the nominal order of the jobs on each machine, and never starts a job before its nominal start: if the jobs on machine $i$ in nominal order are the $1$st, $2$nd, $\dots$, then the $\ell$th starts at
--   $$S_{i,\ell}=\max\{s_{i,\ell},\;S_{i,\ell-1}+P_{i,\ell-1}\},\qquad S_{i,1}=s_{i,1},$$
--   where $s_{i,\ell}$ is its nominal start time and $P_{i,\ell-1}$ the realized processing time of its predecessor. Its completion time is $C_j=S_j+P_{m(j)j}$ and its expected cost is $\mathsf{ALG}=\mathbb E\big[\sum_jw_jC_j\big]$.
--
--   Lemma 8 uses the function
--   $$h(\Delta)=\begin{cases}1+\frac{\sqrt\Delta}{2},&\Delta\le1,\\[2pt] 1+\frac{\Delta}{\Delta+1},&\Delta\ge1,\end{cases}$$
--   which is $\tfrac32$ at $\Delta=1$ by either formula.
--
--   The forced idle time (no start before the nominal start) is what distinguishes this policy from list scheduling; the paper's Remark 2 shows it is necessary.
--
--   **Formalization Note** The predecessor of a job is the job on the same machine with the largest smaller nominal start (unique in a greedy schedule). The recursion is unfolded with a budget of $n$ steps; each step moves to a strictly earlier nominal start, so the budget is never exhausted. The policy is evaluated on the realization $P(\omega)$.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, p. 17, §6.3, Greedy Algorithm (Online Time Model with Stochastic Processing Times); p. 18, Lemma 8 (h(∆))

import Mathlib
import Definitions.Def_GreedWorks_OnlineTime_Model

namespace GreedWorks.OnlineTime

open MeasureTheory Classical

/-! # The greedy policy for stochastic processing times (§6.3, p. 17) and `h(Δ)` (Lemma 8)

The nominal schedule `(m, s)` is the deterministic greedy schedule computed with
`p_ij := 𝔼[P_ij]`. The policy keeps the assignment `m` and, on each GreedWorks.OnlineList.machine, the nominal order;
the `ℓ`-th job on GreedWorks.OnlineList.machine `i` starts at `S_{i,ℓ} = max{s_{i,ℓ}, S_{i,ℓ−1} + P_{i,ℓ−1}}`. -/

variable {M : Type*} [Fintype M] {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The job immediately preceding `j` on its GreedWorks.OnlineList.machine in the nominal schedule: among the jobs
`k` with `m k = m j` and `s k < s j`, one with the largest nominal GreedWorks.OnlineList.start `s k`; `none` if `j`
is the first job on its GreedWorks.OnlineList.machine. (Nominal starts on one GreedWorks.OnlineList.machine are distinct in a greedy
schedule, so the choice is unique there.) -/
noncomputable def nominalPred (m : Fin n → M) (s : Fin n → ℝ) (j : Fin n) : Option (Fin n) :=
  let B := Finset.univ.filter (fun k => m k = m j ∧ s k < s j)
  if h : B.Nonempty then some (Classical.choose (B.exists_max_image s h)) else none

/-- The recursion `S_{i,ℓ} = max{s_{i,ℓ}, S_{i,ℓ−1} + P_{i,ℓ−1}}` (`S_{i,1} = s_{i,1}`), on a
realization `p` of the processing times, unfolded at most `fuel` times. -/
noncomputable def stochStartAux (m : Fin n → M) (s : Fin n → ℝ) (p : GreedWorks.OnlineList.Realization M n) :
    ℕ → Fin n → ℝ
  | 0, j => s j
  | fuel + 1, j =>
    match nominalPred m s j with
    | none => s j
    | some k => max (s j) (stochStartAux m s p fuel k + (p (m k) k : ℝ))

/-- The GreedWorks.OnlineList.start time `S_j` of job `j` under the stochastic greedy policy on the realization `p`.
Each unfolding step moves to a job with strictly smaller nominal GreedWorks.OnlineList.start, so a chain has fewer
than `n` steps and the budget `n` is never exhausted. -/
noncomputable def stochStart (m : Fin n → M) (s : Fin n → ℝ) (p : GreedWorks.OnlineList.Realization M n)
    (j : Fin n) : ℝ :=
  stochStartAux m s p n j

/-- The GreedWorks.OnlineList.completion time `C_j = S_j + P_{m(j) j}` under the stochastic greedy policy. -/
noncomputable def stochCompletion (m : Fin n → M) (s : Fin n → ℝ) (p : GreedWorks.OnlineList.Realization M n)
    (j : Fin n) : ℝ :=
  stochStart m s p j + (p (m j) j : ℝ)

/-- `ALG = 𝔼[Σ_j w_j C_j]`, the expected total weighted GreedWorks.OnlineList.completion time of the stochastic
greedy policy with nominal schedule `(m, s)`. -/
noncomputable def stochValue (I : StochasticInstance M n Ω) (m : Fin n → M) (s : Fin n → ℝ) :
    ℝ :=
  ∫ ω, ∑ j : Fin n, I.weight j * stochCompletion m s (realize I ω) j ∂I.Pr

/-- Lemma 8 (p. 18): `h(Δ) = 1 + √Δ/2` for `Δ ≤ 1` and `h(Δ) = 1 + Δ/(Δ + 1)` for `Δ ≥ 1`
(both give `3/2` at `Δ = 1`). -/
noncomputable def hFactor (Δ : ℝ) : ℝ :=
  if Δ ≤ 1 then 1 + Real.sqrt Δ / 2 else 1 + Δ / (Δ + 1)

end GreedWorks.OnlineTime


