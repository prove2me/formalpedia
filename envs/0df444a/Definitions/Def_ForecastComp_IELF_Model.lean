-- Prove2me | Definitions.Def_ForecastComp_IELF_Model
-- name    : ForecastComp_IELF_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:52.289572+00:00
-- url     : https://prove2.me/theorems/149a27cb-908c-4274-8b0a-53bafbc3ece0
-- title:
--   §2–§5.3, pp. 4–14 — forecasters, binary events and reports, strictly proper scoring rules, the ELF lottery (1), I-ELF with uniform tie-breaking, belief independence and limit accuracy
-- statement:
--   This file fixes the model of a **forecasting competition** (Witkowski, Freeman, Wortman Vaughan, Pennock and Krause). There are $n$ forecasters $i\in[n]$ and $m$ binary events $k\in[m]$. An outcome vector is $x\in\{0,1\}^m$, where $x_k=1$ means that event $k$ occurred. Forecaster $i$ reports $y_{i,k}\in[0,1]$ on event $k$. A **scoring rule** is a map $R(y,x)$ from a report $y\in[0,1]$ and an outcome $x\in\{0,1\}$ to a real score.
--
--   1. **Expected score and properness (Definition 3).** For $p\in[0,1]$ write $\mathbb E_{X\sim p}R(y,X)=p\,R(y,1)+(1-p)\,R(y,0)$. The rule $R$ is *strictly proper* if $\mathbb E_{X\sim p}R(p,X)>\mathbb E_{X\sim p}R(y,X)$ for all $y,p\in[0,1]$ with $y\ne p$, and we write $R\in[0,1]$ when $0\le R(y,x)\le 1$ for all $y\in[0,1]$, $x\in\{0,1\}$.
--   2. **ELF lottery, eq. (1).** On a single event with reports $y_1,\dots,y_n$ and outcome $x$, forecaster $i$ wins with probability
--   $$f_i(y_1,\dots,y_n,x)=\frac1n+\frac1n\Big(R(y_i,x)-\frac1{n-1}\sum_{j\ne i}R(y_j,x)\Big).$$
--   3. **I-ELF (§5.3).** For each event $k$ an event winner $w_k$ is drawn, independently across events, with $\Pr(w_k=i)=f_{i,k}$, the ELF probability on event $k$. With $z_i=\sum_k\mathbb 1(w_k=i)$ the number of events won by $i$, the mechanism selects a forecaster in $\arg\max_i z_i$, breaking ties uniformly at random. $\Pr(M_{\text{I-ELF}^R}(y_1,\dots,y_n,x)=i)$ is the resulting selection probability; more generally, for any table $q_{k,l}$ of event-winner probabilities, $\mathrm{winProb}(q,i)=\sum_{w}\prod_k q_{k,w_k}\cdot \mathrm{tie}(w,i)$, with $\mathrm{tie}(w,i)=1/|\arg\max|$ if $i$ is among the forecasters with most wins and $0$ otherwise.
--   4. **Multi-event ELF, eq. (2)**, selects $i$ with probability $g_i=\frac1m\sum_k f_{i,k}$, and for a joint law $\theta$ of the outcomes the **expected score** of a report vector (p. 11) is $R(y_i,\theta)=\mathbb E_{X\sim\theta}\frac1m\sum_k R(y_{i,k},X_k)$.
--   5. **Strict incentive compatibility under belief independence (Definitions 8–9).** A mechanism, given by its selection probabilities, has this property if for every forecaster $i$, every belief-independent joint law $D$ of the outcomes $X$ and the others' reports $Y_{-i}$ with $\mathbb E_D[X]=p_i$, and every alternative report vector $y_i'\in[0,1]^m$ with $y_i'\ne p_i$,
--   $$\Pr_{D}\big(M(Y_1,\dots,p_i,\dots,Y_n,X)=i\big)>\Pr_{D}\big(M(Y_1,\dots,y_i',\dots,Y_n,X)=i\big).$$
--   Belief independence means that the per-event pairs $(X_k,Y_{-i,k})$ are independent across $k$; within one event, reports and outcome may be arbitrarily correlated.
--   6. **Independent outcomes.** For marginals $\theta\in[0,1]^m$ the outcome $x$ has probability $\prod_k\theta_k^{x_k}(1-\theta_k)^{1-x_k}$; $R(y_i,\theta)=\frac1m\sum_k\mathbb E_{X_k\sim\theta_k}R(y_{i,k},X_k)$. The expected number of event wins $\mathbb E[Z_i]$ and the probability $\Pr(z_j\ge z_i)$ are taken over the outcomes and the event lotteries.
--   7. **Limit accuracy (Definition 7, independent $\theta$).** A mechanism is limit accurate with respect to $R$ if for every $\underline\Delta>0$ and $\pi\in[0,1)$ there is $\underline m$ such that for all $m\ge\underline m$, all $\theta\in[0,1]^m$, all reports in $[0,1]$ and every forecaster $i$ with $R(y_i,\theta)-R(y_j,\theta)>\underline\Delta$ for all $j\ne i$, $\Pr_{X\sim\theta}(M(y_1,\dots,y_n,X)=i)>\pi$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Forecasters are `Fin n`, events `Fin m` (indexed from $0$), outcomes `Fin m → Bool` with `true` meaning "occurred". Reports are real numbers; membership in $[0,1]$ is imposed by hypotheses in the theorems, not by clamping. Selection probabilities are finite sums over event-winner vectors $w:[m]\to[n]$. A belief-independent law is `Measure.pi ν`, the product of per-event joint laws `ν k` on (outcome, all reports on event $k$); forecaster $i$'s coordinate of the sampled reports is overwritten by $i$'s own report (`Function.update`). The mean condition is $\int \mathbb 1[b_1]\,d\nu_k=p_k$. The incentive-compatibility predicate is stated for an arbitrary mechanism and instantiated at I-ELF; limit accuracy likewise takes the selection probability of any mechanism on $m$ independent events.
-- source:
--   Witkowski et al., arXiv:2101.01816v2, pp. 4–14, Definitions 1, 3, 7–9, eq. (1), eq. (2), p. 11 (R(y_i, θ)), §5.3 (I-ELF)

import Mathlib

namespace ForecastComp.IELF

open MeasureTheory

/-! Witkowski, Freeman, Wortman Vaughan, Pennock, Krause, *Incentive-Compatible Forecasting
Competitions*, arXiv:2101.01816v2, §2–§5.3, pp. 4–14.

Forecasters are `Fin n`, events are `Fin m`. An outcome is `x : Fin m → Bool`, where
`x k = true` means that event `k` occurred (`X_k = 1`). A report profile is
`y : Fin n → Fin m → ℝ`, with `y i k` the report `y_{i,k}` of forecaster `i` on event `k`;
reports are constrained to `[0,1]` by hypotheses, never by clamping. A scoring rule is
`R : ℝ → Bool → ℝ`; only its values on reports in `[0,1]` matter. -/

/-- Expected score `E_{X∼p} R(y, X) = p R(y,1) + (1-p) R(y,0)` of report `y` when the event
occurs with probability `p`. -/
def expScore (R : ℝ → Bool → ℝ) (y p : ℝ) : ℝ :=
  p * R y true + (1 - p) * R y false

/-- Definition 3, p. 6: `R` is strictly proper if for all `y, p ∈ [0,1]` with `y ≠ p`,
`E_{X∼p} R(p,X) > E_{X∼p} R(y,X)`. -/
def IsStrictlyProper (R : ℝ → Bool → ℝ) : Prop :=
  ∀ p ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, y ≠ p → expScore R y p < expScore R p p

/-- "`R ∈ [0,1]`" (p. 6): the scoring rule takes values in `[0,1]` on reports in `[0,1]`. -/
def IsUnitBounded (R : ℝ → Bool → ℝ) : Prop :=
  ∀ y ∈ Set.Icc (0:ℝ) 1, ∀ x : Bool, 0 ≤ R y x ∧ R y x ≤ 1

/-- Eq. (1), p. 8: the single-event ELF lottery. Given the reports `ys` of all forecasters on one
event and its outcome `x`, forecaster `i` wins with probability
`1/n + (1/n) (R(y_i,x) − (1/(n−1)) Σ_{j≠i} R(y_j,x))`. -/
noncomputable def elfProb {n : ℕ} (R : ℝ → Bool → ℝ) (ys : Fin n → ℝ) (x : Bool) (i : Fin n) : ℝ :=
  1 / (n:ℝ) + 1 / (n:ℝ) *
    (R (ys i) x - 1 / ((n:ℝ) - 1) * ∑ j ∈ Finset.univ.erase i, R (ys j) x)

/-- Number of events won by forecaster `i` under the event-winner vector `w`,
`Σ_k 𝟙(w_k = i)`. -/
def winCount {m n : ℕ} (w : Fin m → Fin n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun k => w k = i)).card

/-- The forecasters who won the most events, `argmax_i Σ_k 𝟙(w_k = i)` (nonempty when `n ≥ 1`). -/
def topSet {m n : ℕ} (w : Fin m → Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∀ j, winCount w j ≤ winCount w i)

/-- Uniform tie-breaking (p. 14, step 2): each forecaster in the arg max is selected with
probability `1/|argmax|`, the others with probability `0`. -/
noncomputable def tieShare {m n : ℕ} (w : Fin m → Fin n) (i : Fin n) : ℝ :=
  if i ∈ topSet w then 1 / ((topSet w).card : ℝ) else 0

/-- Probability that forecaster `i` is selected by "most event wins, uniform tie-breaking" when
the event winners `w_k` are drawn independently across events with `P(w_k = l) = q k l`. -/
noncomputable def winProbOf {m n : ℕ} (q : Fin m → Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ w : Fin m → Fin n, (∏ k, q k (w k)) * tieShare w i

/-- §5.3, pp. 13–14: the probability `Pr(M_{I-ELF^R}(y_1,…,y_n,x) = i)` over the mechanism's
randomness. Step 1 runs an independent ELF lottery (eq. (1)) on every event; step 2 selects the
forecaster with the most event wins, breaking ties uniformly at random. -/
noncomputable def ielfSelProb {m n : ℕ} (R : ℝ → Bool → ℝ) (y : Fin n → Fin m → ℝ)
    (x : Fin m → Bool) (i : Fin n) : ℝ :=
  winProbOf (fun k l => elfProb R (fun j => y j k) (x k) l) i

/-- Eq. (2), p. 9: multi-event ELF selects `i` with probability `g_i = (1/m) Σ_k f_{i,k}`. -/
noncomputable def elfMultiProb {m n : ℕ} (R : ℝ → Bool → ℝ) (y : Fin n → Fin m → ℝ)
    (x : Fin m → Bool) (i : Fin n) : ℝ :=
  1 / (m:ℝ) * ∑ k, elfProb R (fun j => y j k) (x k) i

/-- P. 11: the expected score `R(y_i, θ) = E_{X∼θ} (1/m) Σ_k R(y_{i,k}, X_k)` of the report vector
`y_i` under an arbitrary joint law `θ` of the outcomes. -/
noncomputable def avgScoreJoint {m : ℕ} (R : ℝ → Bool → ℝ) (θ : Measure (Fin m → Bool))
    (yi : Fin m → ℝ) : ℝ :=
  ∫ x, 1 / (m:ℝ) * ∑ k, R (yi k) (x k) ∂θ

/-- Outcome vector of a sample `ω`, whose `k`-th coordinate is the pair (outcome of event `k`,
reports of all forecasters on event `k`). -/
def outcomeOf {m n : ℕ} (ω : Fin m → Bool × (Fin n → ℝ)) : Fin m → Bool :=
  fun k => (ω k).1

/-- Report profile of a sample `ω`: forecaster `j`'s report on event `k` is `(ω k).2 j`. -/
def reportsOf {m n : ℕ} (ω : Fin m → Bool × (Fin n → ℝ)) : Fin n → Fin m → ℝ :=
  fun j k => (ω k).2 j

/-- Definitions 8–9, p. 13: a forecasting competition mechanism, given by its selection
probability `M y x i = Pr(M(y_1,…,y_n,x) = i)`, is strictly incentive compatible under belief
independence. For every forecaster `i`, every belief-independent joint law `D` of the outcomes and
the others' reports — the product `Measure.pi ν` of per-event laws `ν k` of
(outcome of event `k`, reports on event `k`), each an arbitrary joint law — whose outcome means are
`p`, and every alternative report vector `y' ∈ [0,1]^m` with `y' ≠ p`, reporting `p` gives a
strictly larger selection probability than reporting `y'`. The `i`-th report coordinate of a
sample is ignored: it is overwritten by `i`'s own report. -/
def StrictlyICUnderBeliefIndep {m n : ℕ}
    (M : (Fin n → Fin m → ℝ) → (Fin m → Bool) → Fin n → ℝ) : Prop :=
  ∀ (i : Fin n) (p : Fin m → ℝ) (ν : Fin m → Measure (Bool × (Fin n → ℝ)))
    [∀ k, IsProbabilityMeasure (ν k)],
    (∀ k, ∫ b, (if b.1 then (1:ℝ) else 0) ∂(ν k) = p k) →
    (∀ k, ∀ᵐ b ∂(ν k), ∀ j, b.2 j ∈ Set.Icc (0:ℝ) 1) →
    ∀ y' : Fin m → ℝ, (∀ k, y' k ∈ Set.Icc (0:ℝ) 1) → y' ≠ p →
      ∫ ω, M (Function.update (reportsOf ω) i y') (outcomeOf ω) i ∂(Measure.pi ν) <
        ∫ ω, M (Function.update (reportsOf ω) i p) (outcomeOf ω) i ∂(Measure.pi ν)

/-- Probability of the outcome vector `x` when the events occur independently with
probabilities `θ k`: `Π_k (θ_k if x_k = 1, 1 − θ_k if x_k = 0)`. -/
def bernWeight {m : ℕ} (θ : Fin m → ℝ) (x : Fin m → Bool) : ℝ :=
  ∏ k, if x k then θ k else 1 - θ k

/-- `Pr_{X∼θ}(M_{I-ELF^R}(y_1,…,y_n,X) = i)` for independent outcomes with marginals `θ`. -/
noncomputable def ielfSelProbIndep {m n : ℕ} (R : ℝ → Bool → ℝ) (θ : Fin m → ℝ)
    (y : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  ∑ x, bernWeight θ x * ielfSelProb R y x i

/-- P. 11, `R(y_i, θ)` for independent outcomes with marginals `θ`:
`(1/m) Σ_k E_{X_k∼θ_k} R(y_{i,k}, X_k)`. -/
noncomputable def avgScore {m : ℕ} (R : ℝ → Bool → ℝ) (θ : Fin m → ℝ) (yi : Fin m → ℝ) : ℝ :=
  1 / (m:ℝ) * ∑ k, expScore R (yi k) (θ k)

/-- Definition 7, p. 13, with `Θ` the independent laws: a mechanism, given by its selection
probability `S m θ y i = Pr_{X∼θ}(M(y_1,…,y_n,X) = i)` on `m` independent events with marginals
`θ`, is limit accurate with respect to `R` if for every gap `Δ̲ > 0` and every `π ∈ [0,1)` there is
a number of events `m̲` such that, for all `m ≥ m̲`, all `θ ∈ [0,1]^m`, all reports in `[0,1]`, and
every forecaster `i` whose expected score exceeds every other forecaster's by more than `Δ̲`,
`S m θ y i > π`. -/
def IsLimitAccurateIndep {n : ℕ} (R : ℝ → Bool → ℝ)
    (S : (m : ℕ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → Fin n → ℝ) : Prop :=
  ∀ Δ : ℝ, 0 < Δ → ∀ π ∈ Set.Ico (0:ℝ) 1, ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
    ∀ θ : Fin m → ℝ, (∀ k, θ k ∈ Set.Icc (0:ℝ) 1) →
    ∀ y : Fin n → Fin m → ℝ, (∀ j k, y j k ∈ Set.Icc (0:ℝ) 1) →
    ∀ i : Fin n, (∀ j, j ≠ i → Δ < avgScore R θ (y i) - avgScore R θ (y j)) →
      π < S m θ y i

/-- `E_{X∼θ}[Z_i]`: expected number of events won by forecaster `i` under I-ELF's event lotteries
when the outcomes are independent with marginals `θ`. -/
noncomputable def expWins {m n : ℕ} (R : ℝ → Bool → ℝ) (θ : Fin m → ℝ) (y : Fin n → Fin m → ℝ)
    (i : Fin n) : ℝ :=
  ∑ x, bernWeight θ x *
    ∑ w : Fin m → Fin n, (∏ k, elfProb R (fun j => y j k) (x k) (w k)) * (winCount w i : ℝ)

/-- `Pr_{X∼θ}(z_j ≥ z_i)`: probability that forecaster `j` wins at least as many event lotteries
as forecaster `i`, outcomes independent with marginals `θ`. -/
noncomputable def probWinsGe {m n : ℕ} (R : ℝ → Bool → ℝ) (θ : Fin m → ℝ) (y : Fin n → Fin m → ℝ)
    (j i : Fin n) : ℝ :=
  ∑ x, bernWeight θ x *
    ∑ w : Fin m → Fin n, (∏ k, elfProb R (fun l => y l k) (x k) (w k)) *
      (if winCount w i ≤ winCount w j then (1:ℝ) else 0)

end ForecastComp.IELF


