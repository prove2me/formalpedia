-- Prove2me | Definitions.Def_WeakStrongMSR_Supplement_QueryAlg
-- name    : WeakStrongMSR_Supplement_QueryAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:33:48.672111+00:00
-- url     : https://prove2.me/theorems/41a477a1-8f88-46d9-92de-d54da36f9838
-- title:
--   Randomized adaptive strong-query algorithms, their expected number of strong queries and success probability (§4)
-- statement:
--   Fix $n$ points, identified with $\{0,\dots,n-1\}$, and a number $k$ of balls. A **randomized adaptive strong-query algorithm** receives the whole weak distance table $\tilde d$ and a sequence of independent uniform random numbers $\omega=(\omega_0,\omega_1,\dots)\in[0,1]^{\mathbb N}$ (its coins). It runs in rounds. After $t$ strong queries it holds the **history** $H_t$, the list of the points $x_1,\dots,x_t$ it has queried strongly, each recorded with its exact distances $d(x_i,x_j)$, $j<i$, to the points queried before it; this is exactly what a strong point query reveals. From $(\tilde d,\omega,H_t)$ the algorithm either names the next point to query, which gives
--   $$H_{t+1}=H_t,\ (x_{t+1},\ (d(x_{t+1},x_1),\dots,d(x_{t+1},x_t))),$$
--   or stops and outputs $k$ centres and $k$ radii. No limit is placed on its computation, and the centres it outputs need not have been queried; it outputs no assignment of points to balls.
--
--   1. The **number of strong queries** $Q(\tilde d,\omega)$ is the round at which the algorithm stops (every query counts, repeats included), and $+\infty$ if it never stops.
--   2. A run **succeeds** with factor $\alpha$ if the algorithm stops and its balls form an $\alpha$-approximate minimum-sum-of-radii solution: the radii are nonnegative, every point lies in one of the balls, and the total radius is at most $\alpha\cdot\mathrm{OPT}$.
--   3. On an instance (a metric $d$ and an adversary) with corruption probability $\delta$, the **expected number of strong queries** and the **success probability** are taken over the random corruption set $C$ (each pair corrupted independently with probability $\delta$) and the coins:
--   $$\mathbb E[Q]=\sum_{C}\Pr[C]\ \mathbb E_\omega\big[Q(\tilde d_C,\omega)\big],\qquad \Pr[\text{success}]=\sum_C \Pr[C]\ \Pr_\omega[\text{the run on }\tilde d_C\text{ succeeds}].$$
--   4. The algorithm is **admissible** if its decisions are measurable functions of the coins.
--
--   This is the model in which the lower bounds of Section 4 (Theorems 4.5 and 4.6) are stated: it contains every algorithm of the weak–strong oracle model, including ones that inspect every weak distance.
--
--   **Formalization Note** The coins have the published law `MinSumFPT.tapeLaw`, which simulates any randomized algorithm. The expectation is in $[0,\infty]$, so a run that never stops contributes $+\infty$. Solutions, OPT and the corruption model are the published `WeakStrongMSR.Model` and `MinSumRadiiPTAS.Main.msrOpt`.
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Definition 1.1, p.1 (PDF 2); §4, p.29 (PDF 30); Lemmas 4.3–4.4 and Theorems 4.5–4.6, pp.31–33 (PDF 32–34)

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_MinSumFPT_Machine
import Definitions.Def_WeakStrongMSR_Model

open scoped Classical ENNReal

set_option autoImplicit false

namespace WeakStrongMSR.Supplement

open WeakStrongMSR

/-!
# Randomized adaptive strong-query algorithms (§4), their expected query count and success

Z. Friggstad, M. Jamshidian, A. Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak
Oracles*, manuscript (STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0): Definition 1.1, p.1
(PDF 2); §4, p.29 (PDF 30): "These bounds hold even if an algorithm sees every weak distance, makes
adaptive strong queries, and outputs centres that it never queried. We do not require the algorithm
to output an assignment"; Theorems 4.5 and 4.6, pp.32–33 (PDF 33–34).

**Formalization Note.**
* An algorithm for `n` points and `k` balls is a pair of functions of the full weak table `w`, a
  coin tape `ω : ℕ → ℝ` and the history of strong queries. Entry `t` of the history is the `t`-th
  strongly queried point together with its exact distances to the points queried before it, in
  order: this is exactly what a strong point query reveals (Definition 1.1: from `SO(x)` and
  `SO(y)` the algorithm computes `d(x, y)`). `next` names the next point to query, or `none` to
  stop; `out` gives `k` centres and `k` radii once it stops. No limit is put on computation, and
  the output centres need not have been queried.
* Randomness: the tape has the published law `MinSumFPT.tapeLaw` (i.i.d. uniform on `[0, 1]`), which
  simulates every randomized algorithm.
* `numQueries` counts every strong point query, repeats included; it is `⊤` on a run that never
  stops. The expectation and the probability are over the corruption set (each pair corrupted
  independently with probability `δ`, the published `corrWeight`) and the tape.
* `Admissible` asks that the algorithm's decisions be measurable functions of the tape, so that the
  expectation and the success probability are integrals of measurable functions; every algorithm
  that can be run has this property. -/

/-- A randomized adaptive strong-point-query algorithm for `n` points and `k` balls (§4). -/
structure QueryAlg (n k : ℕ) where
  /-- The next point to query strongly, from the weak table, the tape and the history; `none`
  means stop. -/
  next : (Fin n → Fin n → ℝ) → (ℕ → ℝ) → List (Fin n × List ℝ) → Option (Fin n)
  /-- The output when the algorithm stops: `k` centres and `k` radii (balls only, no assignment). -/
  out : (Fin n → Fin n → ℝ) → (ℕ → ℝ) → List (Fin n × List ℝ) → (Fin k → Fin n) × (Fin k → ℝ)

namespace QueryAlg

variable {n k : ℕ}

/-- The history after `t` steps of the run of `A` on the true metric `d`, the weak table `w` and
the tape `ω`: while `A` asks for a point `x`, append `x` with its exact distances `d x y` to the
points `y` queried before it, in order; once `A` stops the history stays fixed. -/
noncomputable def history (A : QueryAlg n k) (d w : Fin n → Fin n → ℝ) (ω : ℕ → ℝ) :
    ℕ → List (Fin n × List ℝ)
  | 0 => []
  | t + 1 =>
      match A.next w ω (history A d w ω t) with
      | some x => history A d w ω t ++ [(x, ((history A d w ω t).map Prod.fst).map (d x))]
      | none => history A d w ω t

/-- The run stops: at some step the algorithm asks for no further query. -/
def Stops (A : QueryAlg n k) (d w : Fin n → Fin n → ℝ) (ω : ℕ → ℝ) : Prop :=
  ∃ t, A.next w ω (A.history d w ω t) = none

/-- The number of strong point queries of the run, repeats included: the first step at which the
algorithm stops, and `⊤` if it never stops. -/
noncomputable def numQueries (A : QueryAlg n k) (d w : Fin n → Fin n → ℝ) (ω : ℕ → ℝ) : ℕ∞ :=
  if h : A.Stops d w ω then (Nat.find h : ℕ∞) else ⊤

/-- The run succeeds with approximation factor `α`: it stops, and its output balls form an
`α`-approximate MSR solution, i.e. some assignment of the points to the output balls is valid
(nonnegative radii, every point in its ball) and the total radius is at most `α · OPT`. -/
def Succeeds (A : QueryAlg n k) (α : ℝ) (d w : Fin n → Fin n → ℝ) (ω : ℕ → ℝ) : Prop :=
  ∃ h : A.Stops d w ω,
    ∃ σ : Fin n → Fin k,
      ValidSolution d σ (A.out w ω (A.history d w ω (Nat.find h))).1
          (A.out w ω (A.history d w ω (Nat.find h))).2 ∧
        solCost (A.out w ω (A.history d w ω (Nat.find h))).2 ≤
          α * MinSumRadiiPTAS.Main.msrOpt d k

/-- The expected number of strong queries on the instance `(d, adv)` with corruption probability
`δ`, over the corruption set and the tape. -/
noncomputable def expQueries (A : QueryAlg n k) (δ : ℝ) (d : Fin n → Fin n → ℝ)
    (adv : Adversary n) : ℝ≥0∞ :=
  ∑ C ∈ (pairs n).powerset, ENNReal.ofReal (corrWeight δ C) *
    ∫⁻ ω, ((A.numQueries d (weakDist d C adv) ω : ℕ∞) : ℝ≥0∞) ∂MinSumFPT.tapeLaw

/-- The probability that the algorithm returns an `α`-approximate solution on the instance
`(d, adv)` with corruption probability `δ`, over the corruption set and the tape. -/
noncomputable def succProb (A : QueryAlg n k) (α δ : ℝ) (d : Fin n → Fin n → ℝ)
    (adv : Adversary n) : ℝ≥0∞ :=
  ∑ C ∈ (pairs n).powerset, ENNReal.ofReal (corrWeight δ C) *
    MinSumFPT.tapeLaw {ω | A.Succeeds α d (weakDist d C adv) ω}

/-- The algorithm's decisions are measurable functions of the tape. -/
def Admissible (A : QueryAlg n k) : Prop :=
  (∀ (w : Fin n → Fin n → ℝ) (H : List (Fin n × List ℝ)) (x : Fin n),
      MeasurableSet {ω : ℕ → ℝ | A.next w ω H = some x}) ∧
    ∀ (w : Fin n → Fin n → ℝ) (H : List (Fin n × List ℝ)),
      Measurable (fun ω : ℕ → ℝ => A.out w ω H)

end QueryAlg

end WeakStrongMSR.Supplement


