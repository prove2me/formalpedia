-- Prove2me | Definitions.Def_QApproxCount_Counting_Algorithm
-- name    : QApproxCount_Counting_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:29.157984+00:00
-- url     : https://prove2.me/theorems/d516dcdd-edab-465f-98fd-8ddd289a3e38
-- title:
--   The Approximate Counting algorithm of Theorem 1: rounds r_k, Lemma 2's r from (45)–(47), binomial measurement counts, bracket update, and the two loops (pp. 4, 9)
-- statement:
--   This file defines the algorithm of Theorem 1 (algorithm box, p. 4) as a probability distribution over its outputs.
--
--   1. **Measurement counts.** Preparing a state with marked-outcome probability $p$ and measuring it $m$ times gives a number of marked outcomes with the binomial law $\mathrm{Bin}(m,p)$.
--   2. **Step 1 rotation counts.** $r_k$ is the largest odd integer at most $1.05^k$.
--   3. **Repetitions.** Step 1 measures $\lceil 5000\ln(5/\delta)\rceil$ times per round. Step 2 measures $\lceil 250\ln(\delta_t^{-1})\rceil$ times in round $t$, with
--   $$\delta_t := \frac{\delta\varepsilon}{65}\,(0.9)^{-t}.$$
--   4. **Lemma 2's rotation count** (eqs. (45)–(47), p. 9): with $\Delta\theta := \theta_{\max}-\theta_{\min}$, $k$ is the closest integer to $\theta_{\min}/(2\Delta\theta)$ and $r$ the closest odd integer to $\pi k/\theta_{\min}$; ties are broken upward. $r$ depends on $\theta_{\min},\theta_{\max}$ only.
--   5. **Bracket update** (step 2(c)): with $\gamma := \theta_{\max}/\theta_{\min}-1$, if a marked item was measured at least 12% of the time set $\theta_{\min} := \theta_{\max}/(1+0.9\gamma)$, otherwise set $\theta_{\max} := (1+0.9\gamma)\theta_{\min}$.
--   6. **The algorithm** $\mathcal A(N,S,\varepsilon,\delta,F)$. Run on the padded instance $S\subseteq[N']$. Step 1: for $k=0,1,2,\dots$ prepare $G^{(r_k-1)/2}|\psi\rangle$ and measure it $\lceil 5000\ln(5/\delta)\rceil$ times; exit with $k_{\mathrm{end}}:=k$ as soon as at least 95% of the outcomes are marked. Step 2: start from $\theta_{\min}:=0.9\cdot1.05^{-k_{\mathrm{end}}}$, $\theta_{\max}:=1.65\,\theta_{\min}$; for $t=0,1,2,\dots$ compute $r_t$ by Lemma 2, prepare $G^{(r_t-1)/2}|\psi\rangle$ and measure it $\lceil250\ln(\delta_t^{-1})\rceil$ times, update the bracket, and exit once $\theta_{\max}\le(1+\varepsilon/5)\theta_{\min}$. Step 3: return
--   $$\hat K := N'\sin^2(\theta_{\max}).$$
--   The query count of a run is the sum of $(r-1)/2$ over all prepared states. Each loop runs for at most $F$ rounds; a run that exhausts either loop returns "no output".
--
--   **Formalization Note** The algorithm is a `PMF (Option (ℝ × ℕ))`: `some (K̂, q)` is an estimate with its query count $q$, and `none` is fuel exhaustion (a failure, never a default estimate). "At least $m$ times" is read as exactly $\lceil\cdot\rceil$ times. The coin uses Mathlib's `ProbabilityTheory.binomial`, with the bias projected onto $[0,1]$ as a junk guard (Born probabilities already lie in $[0,1]$). The heads tests compare reals: $h \ge 0.95m$ and $h \ge 0.12m$. The exponent $(r_t-1)/2$ is taken through `Int.toNat`, which is exact because $r_t$ is odd and positive under Lemma 2's hypotheses.
-- source:
--   Aaronson & Rall, Quantum Approximate Counting, Simplified, arXiv:1908.10846v6, p. 4, algorithm box of Theorem 1; p. 9, eqs. (45)–(47)

import Mathlib
import Definitions.Def_QApproxCount_Counting_Grover

namespace QApproxCount.Counting

/-- Law of the number of heads in `m` independent tosses of a coin with heads probability `p`:
Mathlib's binomial law `Bin(m, p)` (the number of successes among `m` independent Bernoulli(`p`)
trials), as a `PMF` on `ℕ`. The projection of `p` onto `[0, 1]` is only a junk guard: every `p`
the algorithm uses is a Born probability, already in `[0, 1]`. -/
noncomputable def coin (p : ℝ) (m : ℕ) : PMF ℕ :=
  (ProbabilityTheory.binomial m (Set.projIcc (0 : ℝ) 1 zero_le_one p)).toPMF

/-- `r_k`: the largest odd integer less than or equal to `1.05^k` (step 1(a), p. 4).
Since `1.05^k ≥ 1`, this is `⌊1.05^k⌋` if that is odd and `⌊1.05^k⌋ - 1` otherwise. -/
noncomputable def oddFloor (k : ℕ) : ℕ :=
  if Odd ⌊(1.05 : ℝ) ^ k⌋₊ then ⌊(1.05 : ℝ) ^ k⌋₊ else ⌊(1.05 : ℝ) ^ k⌋₊ - 1

/-- Number of preparations in each round of step 1: `⌈5000 ln(5/δ)⌉` (step 1(a)). -/
noncomputable def stepOneReps (δ : ℝ) : ℕ :=
  ⌈5000 * Real.log (5 / δ)⌉₊

/-- `δ_t := (δε/65) · 0.9^{-t}` (step 2(b), p. 4). -/
noncomputable def deltaT (ε δ : ℝ) (t : ℕ) : ℝ :=
  δ * ε / 65 * (0.9 : ℝ) ^ (-(t : ℤ))

/-- Number of preparations in round `t` of step 2: `⌈250 ln(δ_t^{-1})⌉` (step 2(b)). -/
noncomputable def stepTwoReps (ε δ : ℝ) (t : ℕ) : ℕ :=
  ⌈250 * Real.log (deltaT ε δ t)⁻¹⌉₊

/-- `k` of (46): the closest integer to `θmin / (2Δθ)` with `Δθ := θmax - θmin` (45);
ties are broken upward (`round`). -/
noncomputable def rotK (θmin θmax : ℝ) : ℤ :=
  round (θmin / (2 * (θmax - θmin)))

/-- `r` of (47), the rotation count of Lemma 2: the closest odd integer to `πk / θmin`,
computed as `2 · round((x - 1)/2) + 1` (ties broken upward). It depends on `θmin, θmax` only. -/
noncomputable def rotR (θmin θmax : ℝ) : ℤ :=
  2 * round ((Real.pi * (rotK θmin θmax : ℝ) / θmin - 1) / 2) + 1

/-- The bracket update of step 2(c): with `γ := θmax/θmin - 1`, if enough marked items were
seen set `θmin := θmax/(1 + 0.9γ)`, otherwise set `θmax := (1 + 0.9γ) θmin`.
Returns the new pair `(θmin, θmax)`. -/
noncomputable def bracketUpdate (heads : Bool) (θmin θmax : ℝ) : ℝ × ℝ :=
  if heads then (θmax / (1 + 0.9 * (θmax / θmin - 1)), θmax)
  else (θmin, (1 + 0.9 * (θmax / θmin - 1)) * θmin)

/-- Step 1 of the algorithm, run on the instance `T ⊆ [n]` with at most `fuel` rounds,
starting at round `k` with `q` queries already spent. Each round prepares
`G^{(r_k - 1)/2} |ψ⟩` `⌈5000 ln(5/δ)⌉` times (`(r_k - 1)/2` queries per preparation) and
measures; the number of marked outcomes is binomial with the Born probability. The loop exits
on `k =: k_end` when a marked item was seen in at least 95% of the measurements.
Output: `some (k_end, queries)`, or `none` if the fuel runs out. -/
noncomputable def stepOne {n : ℕ} (T : Finset (Fin n)) (δ : ℝ) :
    ℕ → ℕ → ℕ → PMF (Option (ℕ × ℕ))
  | 0, _, _ => PMF.pure none
  | fuel + 1, k, q =>
    (coin (markedProb T ((oddFloor k - 1) / 2)) (stepOneReps δ)).bind fun h =>
      if (0.95 : ℝ) * (stepOneReps δ : ℝ) ≤ (h : ℝ) then
        PMF.pure (some (k, q + stepOneReps δ * ((oddFloor k - 1) / 2)))
      else
        stepOne T δ fuel (k + 1) (q + stepOneReps δ * ((oddFloor k - 1) / 2))

/-- Step 2 of the algorithm (and step 3), run on `T ⊆ [n]` with at most `fuel` rounds,
starting at round `t` with bracket `(θmin, θmax)` and `q` queries spent. Each round computes
`r_t := rotR θmin θmax` (Lemma 2), prepares `G^{(r_t - 1)/2} |ψ⟩` `⌈250 ln(δ_t^{-1})⌉` times
and measures, updates the bracket by `bracketUpdate` (heads = a marked item was seen at least
12% of the time), and exits when `θmax ≤ (1 + ε/5) θmin`, returning
`some (K̂, queries)` with `K̂ := n · sin²(θmax)`; `none` if the fuel runs out. -/
noncomputable def stepTwo {n : ℕ} (T : Finset (Fin n)) (ε δ : ℝ) :
    ℕ → ℕ → ℝ → ℝ → ℕ → PMF (Option (ℝ × ℕ))
  | 0, _, _, _, _ => PMF.pure none
  | fuel + 1, t, θmin, θmax, q =>
    (coin (markedProb T (Int.toNat ((rotR θmin θmax - 1) / 2))) (stepTwoReps ε δ t)).bind
      fun h =>
        let q' := q + stepTwoReps ε δ t * Int.toNat ((rotR θmin θmax - 1) / 2)
        let b := bracketUpdate
          (if (0.12 : ℝ) * (stepTwoReps ε δ t : ℝ) ≤ (h : ℝ) then true else false) θmin θmax
        if b.2 ≤ (1 + ε / 5) * b.1 then
          PMF.pure (some ((n : ℝ) * Real.sin b.2 ^ 2, q'))
        else
          stepTwo T ε δ fuel (t + 1) b.1 b.2 q'

/-- The Approximate Counting algorithm of Theorem 1 (algorithm box, p. 4) on the marked set
`S ⊆ [N]`, with accuracy `ε`, failure probability `δ`, and at most `fuel` rounds in each of
its two loops. The list is first padded to `N' = (10^6 + 1) N` items (`padSet`); the algorithm
sees `S` only through the Born probabilities of the Grover states. Step 2 starts from
`θmin := 0.9 · 1.05^{-k_end}`, `θmax := 1.65 · θmin`. Output: `some (K̂, number of oracle
queries)` with `K̂ = N' sin²(θmax)`, or `none` if either loop exhausts its fuel. -/
noncomputable def approxCount (N : ℕ) (S : Finset (Fin N)) (ε δ : ℝ) (fuel : ℕ) :
    PMF (Option (ℝ × ℕ)) :=
  (stepOne (padSet N S) δ fuel 0 0).bind fun o =>
    match o with
    | none => PMF.pure none
    | some (kend, q) =>
      stepTwo (padSet N S) ε δ fuel 0 (0.9 * (1.05 : ℝ) ^ (-(kend : ℤ)))
        (1.65 * (0.9 * (1.05 : ℝ) ^ (-(kend : ℤ)))) q

end QApproxCount.Counting


