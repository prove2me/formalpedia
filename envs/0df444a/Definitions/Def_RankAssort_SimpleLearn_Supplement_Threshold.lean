-- Prove2me | Definitions.Def_RankAssort_SimpleLearn_Supplement_Threshold
-- name    : RankAssort_SimpleLearn_Supplement_Threshold
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:22:55.946963+00:00
-- url     : https://prove2.me/theorems/ebf874d2-5d38-4d34-b774-1d5992ab9c35
-- title:
--   Algorithm 3, p. 26 — the Threshold Acceptance Algorithm run on an i.i.d. customer stream, observing first clicks
-- statement:
--   Products are $[n]$ and a (partial) ranking $\tilde\pi$ is a duplicate-free list of products; its $r$-th entry is shown at rank $r$. In the learning phase customers arrive one after another. A customer has a type $\theta\sim\mathcal D$ with click probabilities $p_i(\theta)$ and window $k(\theta)$, and, given $\theta$, a **like-profile** $L\in\{0,1\}^n$ with independent coordinates $L_i\sim\mathrm{Bernoulli}(p_i(\theta))$: $L_i=1$ means she clicks $i$ if she sees it before any click. The **customer law** is the law of $(\theta,L)$.
--
--   Shown a ranking whose first $r-1$ positions are $\sigma$ and whose $r$-th position is $i$, the customer **only clicks on $i$** when $r\le k(\theta)$, $L_i=1$ and $L_j=0$ for every product $j$ of $\sigma$ inside her window: she clicks the rank-$r$ product without clicking any earlier one, the event $\bar C(r-1,\sigma\cup i)\,C_i(\sigma\cup i)=1$.
--
--   **Threshold Acceptance Algorithm (Algorithm 3).** Inputs: $\epsilon,\delta,\alpha>0$, thresholds $\tau^{\max}\ge\tau^{\min}>0$, and a scan order of the products. Start with the empty ranking $\tilde\pi$ and $\tau=\tau^{\max}$. While $\tau\ge\tau^{\min}$ and fewer than $n$ products are ranked, make one pass: for each product $i$ in scan order that is still unranked, display $\tilde\pi\cup i$ to the next
--   $$L=\Big\lceil \frac{n^2}{\epsilon^2}\log\frac{n}{\sqrt\delta}\Big\rceil$$
--   customers, let $\Delta$ be the fraction of them who only click on $i$, and append $i$ to $\tilde\pi$ if $\Delta\ge\tau$ (later products of the same pass are then tried at the next rank). After the pass set $\tau\leftarrow\tau/(1+\alpha)$. Pass $k$ uses the threshold $\tau^{\max}/(1+\alpha)^k$, so at most $1+\lfloor\log_{1+\alpha}(\tau^{\max}/\tau^{\min})\rfloor$ passes run. The output is the returned ranking $\tilde\pi$, possibly with fewer than $n$ products, together with the number of customers consumed, the length of the learning phase. Theorem 4 runs it with $\tau^{\max}=1$ and $\tau^{\min}=\epsilon/n$.
--
--   The same loop, with revenue observations in place of first-click indicators, is Algorithm 4 (see the revenue definitions).
--
--   **Formalization Note** Products are `Fin n`, ranks 0-based. The loop is `taOutput`: `taStep` is one iteration of "for $i\in U$", `taPass` one pass over the scan order, `taPasses k` the state after $k$ iterations of the `while` loop with the guard checked each time; once the guard fails it fails forever, so `numPasses` $=\lfloor\log_{1+\alpha}(\tau^{\max}/\tau^{\min})\rfloor_+ +1$ iterations reproduce the loop. Customer $s$ of the stream `z` is `(z s).1` (type) and `(z s).2` (like-profile); a display to $L$ customers consumes indices `used, …, used + L − 1`. `customerLaw D τ` is $\sum_L (\mathcal D$ with density $\theta\mapsto$ `likeWeight (τ θ) L`$)\otimes\delta_L$. With zero customers ($L=0$) $\Delta$ is $0$, so nothing is accepted.
-- source:
--   Ferreira, Parthasarathy, Sekar, Learning to Rank an Assortment of Products, SSRN 3395992 author manuscript, p. 26, Algorithm 3; pp. 9–11 (§2, the learning phase); pp. 60–61 (proof of Theorem 4: first-click samples); p. 53 (coupled first-click law)

import Mathlib
import Definitions.Def_RankAssort_SimpleLearn_Model

namespace RankAssort.SimpleLearn.Supplement
open MeasureTheory

/-! # The Threshold Acceptance Algorithm (Algorithm 3) and its customer stream

Ferreira, Parthasarathy, Sekar, *Learning to Rank an Assortment of Products*, SSRN 3395992 author
manuscript, Algorithm 3 (p. 26), the learning-phase model of §2 (pp. 9–11) and the first-click
observations of the proof of Theorem 4 (pp. 60–61). Products are `Fin n` (0-based); a (partial)
ranking is a `List (Fin n)`, its `r`-th entry (0-based) sitting at the paper's rank `r + 1`. -/

variable {n : ℕ}

/-- Law of one arriving customer in the learning phase: a type `θ ∼ D` and, given `θ`, a
like-profile `L : Fin n → Bool` drawn from the coupled first-click law of `θ` (independent
Bernoulli(`p i`) coordinates, `likeWeight`, p. 53). -/
noncomputable def customerLaw {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    (τ : Θ → CustomerType n) : Measure (Θ × (Fin n → Bool)) :=
  ∑ L : Fin n → Bool,
    (D.withDensity fun θ => ENNReal.ofReal (likeWeight (τ θ) L)).prod (Measure.dirac L)

/-- The customer with type `θ` and like-profile `L`, shown a ranking whose first `σ.length`
positions are `σ` and whose next position holds `i`, clicks on `i` (at 0-based rank `σ.length`,
inside her window) without clicking on any earlier-ranked product: the event
`C̄(r − 1, σ ∪ i) C_i(σ ∪ i) = 1` with `r = σ.length + 1` ("customers who only click on `i`",
p. 26; p. 61). -/
def firstClick (θ : CustomerType n) (σ : List (Fin n)) (i : Fin n) (L : Fin n → Bool) : Prop :=
  noClickTop θ (σ ++ [i]) σ.length L ∧ clicksAt θ (σ ++ [i]) σ.length L

/-- State of a threshold-acceptance run: the ranked prefix `π̃` and the number of customers
consumed so far. -/
structure TAState (n : ℕ) where
  ranked : List (Fin n)
  used : ℕ

/-- One iteration of the inner loop "for `i ∈ U`" at threshold `thr`. If `i` is already ranked
nothing happens. Otherwise `π̃ ∪ i` is displayed to the next `L` customers (indices
`used, …, used + L − 1`), `obs π̃ i s` is what customer `s` yields, `Δ` is their total divided by
`L`, and `i` is appended to `π̃` when `Δ ≥ thr`. -/
noncomputable def taStep (obs : List (Fin n) → Fin n → ℕ → ℝ) (L : ℕ) (thr : ℝ)
    (st : TAState n) (i : Fin n) : TAState n :=
  if i ∈ st.ranked then st
  else if thr ≤ (∑ s ∈ Finset.range L, obs st.ranked i (st.used + s)) / L then
    ⟨st.ranked ++ [i], st.used + L⟩
  else ⟨st.ranked, st.used + L⟩

/-- One pass through the unranked products, visited in the scan order `order`; a product accepted
during the pass leaves `U` at once, and the later products of the pass are tried at the next
rank. -/
noncomputable def taPass (obs : List (Fin n) → Fin n → ℕ → ℝ) (L : ℕ) (thr : ℝ)
    (order : List (Fin n)) (st : TAState n) : TAState n :=
  order.foldl (taStep obs L thr) st

/-- The state after `k` iterations of the outer `while` loop. Pass `k` (0-based) uses the
threshold `thrMax / (1 + α)^k` and runs only while `τ ≥ τmin` and `CurrentRank ≤ n`
(i.e. fewer than `n` products are ranked); once the guard fails it fails forever, so further
iterations leave the state unchanged. -/
noncomputable def taPasses (obs : List (Fin n) → Fin n → ℕ → ℝ) (L : ℕ)
    (thrMax thrMin α : ℝ) (order : List (Fin n)) : ℕ → TAState n
  | 0 => ⟨[], 0⟩
  | k + 1 =>
    let st := taPasses obs L thrMax thrMin α order k
    if thrMin ≤ thrMax / (1 + α) ^ k ∧ st.ranked.length < n then
      taPass obs L (thrMax / (1 + α) ^ k) order st
    else st

/-- The number of outer iterations that can run: the thresholds `thrMax / (1+α)^k` that are
`≥ thrMin` are exactly those with `k ≤ ⌊log_{1+α}(thrMax / thrMin)⌋`. -/
noncomputable def numPasses (thrMax thrMin α : ℝ) : ℕ :=
  ⌊Real.logb (1 + α) (thrMax / thrMin)⌋₊ + 1

/-- The final state of the threshold-acceptance loop (Algorithms 3 and 4): the returned, possibly
partial, ranking `π̃` and the length of the learning phase (customers consumed). -/
noncomputable def taOutput (obs : List (Fin n) → Fin n → ℕ → ℝ) (L : ℕ)
    (thrMax thrMin α : ℝ) (order : List (Fin n)) : TAState n :=
  taPasses obs L thrMax thrMin α order (numPasses thrMax thrMin α)

/-- Algorithm 3's sample size `L = (n²/ϵ²) log(n/√δ)` (natural logarithm), rounded up. -/
noncomputable def sampleSize (n : ℕ) (eps delta : ℝ) : ℕ :=
  ⌈((n : ℝ) ^ 2 / eps ^ 2) * Real.log (n / Real.sqrt delta)⌉₊

open Classical in
/-- A run of the Threshold Acceptance Algorithm (Algorithm 3, p. 26) with `τmax = 1`,
`τmin = ϵ/n`, parameters `ϵ, δ, α`, scan order `order` for "for `i ∈ U`", on the realized customer
stream `z` (customer `s` has type `(z s).1` and like-profile `(z s).2`). The algorithm observes, for
each displayed customer, only the indicator that she clicks the candidate product and nothing
ranked before it. -/
noncomputable def thresholdAcceptance {Θ : Type*} (τ : Θ → CustomerType n) (eps delta α : ℝ)
    (order : List (Fin n)) (z : ℕ → Θ × (Fin n → Bool)) : TAState n :=
  taOutput (fun σ i s => if firstClick (τ (z s).1) σ i (z s).2 then 1 else 0)
    (sampleSize n eps delta) 1 (eps / n) α order

end RankAssort.SimpleLearn.Supplement


