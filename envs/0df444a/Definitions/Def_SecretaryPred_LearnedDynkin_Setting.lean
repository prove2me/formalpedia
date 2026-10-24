-- Prove2me | Definitions.Def_SecretaryPred_LearnedDynkin_Setting
-- name    : SecretaryPred_LearnedDynkin_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:35.855833+00:00
-- url     : https://prove2.me/theorems/77f856b0-4eba-4422-9d49-843045f43588
-- title:
--   §2–§3, pp. 4–6 — continuous-time secretary model with predictions, the deviation set M, and Algorithm 1 (learned Dynkin)
-- statement:
--   The model and the algorithm of Fujii and Yoshida, *The Secretary Problem with Predictions* (§2, §2.1 and §3, pp. 4–6).
--
--   **Candidates and predictions.** There are $n$ candidates $N=\{1,\dots,n\}$. Candidate $i$ has a value $v(i)\ge 0$, revealed when the candidate is interviewed, and a prediction $\hat v(i)\ge 0$ known in advance.
--
--   **Arrival times.** In the continuous-time model each candidate $i$ independently receives an arrival time $t_i$ drawn uniformly from $[0,1]$. Candidates are interviewed in increasing order of arrival time, and every decision is irrevocable. The joint law of $t=(t_1,\dots,t_n)$ is the uniform distribution on the cube $[0,1]^n$.
--
--   **Deviating candidates.** For a threshold $\theta$, candidate $i$ *deviates* if $|1-\hat v(i)/v(i)|>\theta$, written without division as
--
--   $$\theta\, v(i) < |v(i)-\hat v(i)|.$$
--
--   The set of deviating candidates is $M$, and $m=|M|$.
--
--   **Ranking.** Candidate $i$ *beats* candidate $j$ if $v(j)<v(i)$, or $v(j)=v(i)$ and $i$ has the smaller index. This is a strict total order on the candidates. A candidate is *best so far* if it beats every candidate that arrived strictly before it.
--
--   **Algorithm 1 (learned Dynkin).** Fix a time $\tau$, a threshold $\theta$ and a maximizer $\hat\imath$ of $\hat v$. The algorithm starts in Prediction mode and interviews the candidates in arrival order. When candidate $i$ arrives:
--   1. if $i$ deviates, the mode becomes Secretary (and stays so);
--   2. in Prediction mode, it hires $i$ if $i=\hat\imath$;
--   3. in Secretary mode, it hires $i$ if $t_i>\tau$ and $i$ is best so far.
--
--   Hiring ends the process. So the mode at $i$'s arrival is Secretary exactly when some deviating candidate $j$ has $t_j\le t_i$ (including $j=i$), and $i$ is hired when it passes the hiring test of steps 2–3 and no earlier arrival did.
--
--   **Value.** The value of a run is the value of the hired candidate, or $0$ if nobody is hired. Its expectation over the arrival times is
--
--   $$\mathbb E[\mathrm{ALG}] = \int_{[0,1]^n} \mathrm{ALG}(t)\,dt.$$
--
--   These objects carry every statement of the mission: the goal (Theorem 1) bounds $\mathbb E[\mathrm{ALG}]$ below by $\max\{0.215,(1-\epsilon)/(1+\epsilon)\}\cdot\max_i v(i)$, and the milestones bound, case by case, the probability that the best candidate is hired.
--
--   **Formalization Note** Candidates are `Fin n` (0-based indices). `arrivalLaw n` is Lebesgue measure on `Fin n → ℝ` restricted to $[0,1]^n$, a probability measure. `Deviates θ v v̂ i` is the division-free test above, `Mset` is $M$, `Beats` the tie-broken order, `SecretaryAt` the mode at an arrival, `BestSoFar` the best-so-far test, `Stops` the hiring test of lines 6–9, `Hired` the first candidate to pass it, `algValue` the sum of the values of hired candidates (one candidate's value, or $0$, except on the null set of arrival vectors with two equal times), and `expectedValue` its integral against `arrivalLaw n`.
-- source:
--   Fujii, Yoshida, The Secretary Problem with Predictions, arXiv:2306.08340v1, pp. 4–6, §2 (model, competitive ratio), §2.1 (continuous-time model), Algorithm 1 and the definition of M (p. 6)

import Mathlib

namespace SecretaryPred.LearnedDynkin

open MeasureTheory

/-- The law of the arrival times in the continuous-time model (§2.1, p. 5): each of the `n`
candidates `i : Fin n` independently receives an arrival time `t i` uniform on `[0, 1]`. This is
Lebesgue measure on `ℝ^n` restricted to the unit cube `[0, 1]^n`, a probability measure. -/
noncomputable def arrivalLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  volume.restrict (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1)

/-- Candidate `i` deviates from its prediction by more than `θ` (line 4 of Algorithm 1, p. 6):
`|1 − v̂(i)/v(i)| > θ`, written without division as `θ · v(i) < |v(i) − v̂(i)|`. -/
def Deviates {n : ℕ} (theta : ℝ) (v vhat : Fin n → ℝ) (i : Fin n) : Prop :=
  theta * v i < |v i - vhat i|

/-- The set `M = {i ∈ N : |1 − v̂(i)/v(i)| > θ}` of candidates that significantly deviate from
the prediction (p. 6). Its cardinality is `m = |M|`. -/
noncomputable def Mset {n : ℕ} (theta : ℝ) (v vhat : Fin n → ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => Deviates theta v vhat i)

/-- The strict total order used to compare candidates: `i` beats `j` iff `v(j) < v(i)`, or
`v(j) = v(i)` and `i < j` (larger value, then smaller index). -/
def Beats {n : ℕ} (v : Fin n → ℝ) (i j : Fin n) : Prop :=
  v j < v i ∨ (v j = v i ∧ i < j)

/-- The mode of Algorithm 1 is `Secretary` when candidate `i` is processed: some deviating
candidate `j` has arrived no later than `i` (`j = i` included, since lines 4–5 run before
lines 6–9 for the same candidate). -/
def SecretaryAt {n : ℕ} (theta : ℝ) (v vhat t : Fin n → ℝ) (i : Fin n) : Prop :=
  ∃ j, t j ≤ t i ∧ Deviates theta v vhat j

/-- Candidate `i` is the best so far: it beats every candidate that arrived strictly earlier. -/
def BestSoFar {n : ℕ} (v t : Fin n → ℝ) (i : Fin n) : Prop :=
  ∀ j, t j < t i → Beats v i j

/-- Lines 6–9 of Algorithm 1: the algorithm would hire candidate `i` at its arrival, either in
`Prediction` mode with `i = ı̂`, or in `Secretary` mode with `t_i > τ` and `i` the best so far. -/
def Stops {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat : Fin n) (t : Fin n → ℝ)
    (i : Fin n) : Prop :=
  (¬ SecretaryAt theta v vhat t i ∧ i = ihat) ∨
    (SecretaryAt theta v vhat t i ∧ tau < t i ∧ BestSoFar v t i)

/-- Algorithm 1 hires candidate `i`: `i` satisfies the hiring test and no candidate that arrived
strictly earlier did (hiring ends the process). -/
def Hired {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat : Fin n) (t : Fin n → ℝ)
    (i : Fin n) : Prop :=
  Stops theta tau v vhat ihat t i ∧ ∀ j, t j < t i → ¬ Stops theta tau v vhat ihat t j

/-- The value obtained by Algorithm 1 on arrival times `t`: the value of the hired candidate,
and `0` if nobody is hired. (When two candidates share an arrival time both may count; this
happens on a null set of `t`.) -/
noncomputable def algValue {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat : Fin n)
    (t : Fin n → ℝ) : ℝ := by
  classical
  exact ∑ i, if Hired theta tau v vhat ihat t i then v i else 0

/-- The expected value of the output of Algorithm 1 over the iid Uniform[0, 1] arrival times. -/
noncomputable def expectedValue {n : ℕ} (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat : Fin n) :
    ℝ :=
  ∫ t, algValue theta tau v vhat ihat t ∂(arrivalLaw n)

end SecretaryPred.LearnedDynkin


