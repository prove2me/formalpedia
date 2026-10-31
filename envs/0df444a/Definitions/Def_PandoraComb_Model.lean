-- Prove2me | Definitions.Def_PandoraComb_Model
-- name    : PandoraComb_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:55.326071+00:00
-- url     : https://prove2.me/theorems/061b76c5-c9d0-49db-8766-27f8d7058824
-- title:
--   Pandora's problem with combinatorial cost: instances, adaptive randomized strategies and the expected utility $u(\mathcal I;\pi)$
-- statement:
--   There are finitely many **boxes** $i\in\iota$ (the paper's $[n]=\{1,\dots,n\}$). Box $i$ holds a hidden value $V_i$ with law $D_i$, and the values are independent. Inspecting a *set* $S$ of boxes costs $c(S)$.
--
--   An **instance** $\mathcal I=(D_1,\dots,D_n,c)$ satisfies:
--
--   1. every $D_i$ is a probability measure on $\mathbb R$ with $D_i((-\infty,0))=0$ (non-negative values) and finite expectation;
--   2. $c(\emptyset)=0$ and $c$ is monotone: $S\subseteq T$ implies $c(S)\le c(T)$.
--
--   A **strategy** $\pi$ inspects boxes one at a time. Before each decision it sees the ordered **history** (the boxes opened so far, in the order they were opened, with their realized values) and a random seed $s$, uniform on $[0,1]$ and independent of the values. It then either names a box to inspect next or halts. A strategy is **admissible** if, for every fixed sequence of opened boxes, each of its decisions is a measurable event of the observed values and of the seed.
--
--   Running $\pi$ from the empty history yields the ordered set $S(\pi)$ of opened boxes. The reward and the expected utility are
--
--   $$V(\pi)=\max\Big(0,\ \max_{i\in S(\pi)}V_i\Big),\qquad u(\mathcal I;\pi)=\mathbb E\big[V(\pi)\big]-\mathbb E\big[c(S(\pi))\big],$$
--
--   the expectation being over the values and the seed. The cost is that of the set of opened boxes, charged once; it is not a sum of per-box charges.
--
--   These are the objects of every statement of the mission: optimality of a strategy means that its utility is at least that of every admissible strategy.
--
--   **Formalization Note** The history is a `List (ι × ℝ)`, first entry first; a strategy is `next : History ι → ℝ → Option ι` (`none` halts). A run lasts at most $|\iota|$ rounds, enough to open every box; a request for an already opened box halts the run (a legal strategy never makes one). The reward is computed as $\max(0,\max)$, which equals the paper's $V(\pi)$ almost surely because values are non-negative, and the empty strategy has utility $0$. The joint law of values and seed is `(Measure.pi D).prod seedLaw` with `seedLaw` the uniform law on $[0,1]$. The cost is real valued; non-negativity follows from $c(\emptyset)=0$ and monotonicity.
-- source:
--   Berger, Ezra, Feldman & Fusco, Pandora’s Problem with Combinatorial Cost, arXiv:2303.01078v1, §2, p.7 (model, strategies, S(π), V(π), u(π), randomized strategies, finite expectations)

import Mathlib

open MeasureTheory

noncomputable section

namespace PandoraComb

/-- **An ordered history** of Pandora's problem: the boxes opened so far, in the order they were
opened, each with its realized value.
Berger, Ezra, Feldman & Fusco, *Pandora’s Problem with Combinatorial Cost*, arXiv:2303.01078v1,
§2, p.7: "The decisions are based on the given instance and the sequence of opened boxes and
realized values so far."

**Formalization Note.** The first entry of the list is the first box opened. -/
abbrev History (ι : Type*) := List (ι × ℝ)

/-- **A (randomized, adaptive) strategy** (arXiv:2303.01078v1, §2, p.7). At each round the
strategy sees the ordered history and a random seed `s`, and either names an uninspected box to
inspect next (`some i`) or halts (`none`).

**Formalization Note.** Randomization ("A randomized strategy can toss coins before every decision
point. Note that these coins can be tossed a priori before the first box is inspected", p.7) is a
single seed `s ∈ [0, 1]` drawn uniformly and independently of the boxes before the first round
(`seedLaw`); one uniform seed generates any finite family of coin tosses. -/
structure Strategy (ι : Type*) where
  /-- The decision rule: `none` halts, `some i` inspects box `i`. -/
  next : History ι → ℝ → Option ι

/-- **Admissible strategy**: for every fixed sequence `l` of opened boxes, each decision of the
strategy is a measurable event of the observed values of the boxes in `l` and of the seed.

**Formalization Note.** This is what makes the expectations `E[V(π)]`, `E[c(S(π))]` of §2, p.7
defined for every strategy; it is imposed on every strategy and adds nothing else (no box must be
opened, no positivity). The values of the boxes in `l` are read off a full realization
`x.1 : ι → ℝ`; the seed is `x.2`. -/
def Admissible {ι : Type*} (π : Strategy ι) : Prop :=
  ∀ (l : List ι) (o : Option ι),
    MeasurableSet {x : (ι → ℝ) × ℝ | π.next (l.map fun i => (i, x.1 i)) x.2 = o}

/-- One run of a strategy with fuel `k` from the history `h`, for realized values `ω` and seed `s`.
A request for an already opened box halts (a legal strategy never makes one). -/
def runAux {ι : Type*} [DecidableEq ι] (π : Strategy ι) (ω : ι → ℝ) (s : ℝ) :
    ℕ → History ι → History ι
  | 0, h => h
  | k + 1, h =>
    match π.next h s with
    | none => h
    | some i => if i ∈ h.map Prod.fst then h else runAux π ω s k (h ++ [(i, ω i)])

/-- **The final history of a strategy**: the strategy is run from the empty history for at most
`n = Fintype.card ι` rounds (enough to open every box), with realized values `ω` and seed `s`.
`(run π ω s).map Prod.fst` is the paper's ordered set `S(π)` of opened boxes (§2, p.7). -/
def run {ι : Type*} [Fintype ι] [DecidableEq ι] (π : Strategy ι) (ω : ι → ℝ) (s : ℝ) :
    History ι :=
  runAux π ω s (Fintype.card ι) []

/-- **The reward** of a history: the largest observed value, or `0` if no box was opened
(§2, p.7: `V(π) := max_{i ∈ S(π)} V_i`).

**Formalization Note.** Computed as `max(0, max observed)`. Values are nonnegative almost surely
and the empty strategy has reward `0` (pp.8, 24), so this equals the paper's `V(π)` almost
surely. -/
def reward {ι : Type*} (h : History ι) : ℝ :=
  (h.map Prod.snd).foldr max 0

/-- The set of opened boxes of a history. -/
def openedSet {ι : Type*} [DecidableEq ι] (h : History ι) : Finset ι :=
  (h.map Prod.fst).toFinset

/-- **The realized utility** of a history: the reward minus the cost `c(S)` of the **set** of
opened boxes (§2, p.7: "attain as utility the difference between the largest observed value and
the cost of the set of opened boxes"). -/
def payoff {ι : Type*} [DecidableEq ι] (c : Finset ι → ℝ) (h : History ι) : ℝ :=
  reward h - c (openedSet h)

/-- The law of the randomization seed: uniform on `[0, 1]`. -/
def seedLaw : Measure ℝ :=
  volume.restrict (Set.Icc 0 1)

/-- The joint law of the box values and the seed: the values are independent with laws `D i`
(the coordinates under `Measure.pi D`) and the seed is independent of them. -/
def jointLaw {ι : Type*} [Fintype ι] (D : ι → Measure ℝ) : Measure ((ι → ℝ) × ℝ) :=
  (Measure.pi D).prod seedLaw

/-- **The expected utility** `u(I; π) := E[V(π)] − E[c(S(π))]` (§2, p.7) of the strategy `π` on
the instance `I = (D, c)`. -/
def utility {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ι → Measure ℝ) (c : Finset ι → ℝ)
    (π : Strategy ι) : ℝ :=
  ∫ x, payoff c (run π x.1 x.2) ∂(jointLaw D)

/-- **An instance** `I = (D_1, …, D_n, c)` of Pandora's problem with combinatorial cost
(§2, p.7): independent non-negative distributions `D_i` with finite expectations ("We thus assume
that all distributions `D_i` have finite expectations", p.7) and a cost function
`c : 2^[n] → ℝ≥0` that is normalized and monotone ("We assume that c is always normalized and
monotone, i.e, c(∅) = 0 and S ⊆ T implies c(S) ≤ c(T)", p.7).

**Formalization Note.** The boxes are a finite type `ι` (the paper's `[n]`), sets of boxes are
`Finset ι`. The cost is real valued; its nonnegativity follows from `c ∅ = 0` and monotonicity.
Each `D i` is a probability measure on `ℝ` with `D i (-∞, 0) = 0` and integrable identity. -/
def IsInstance {ι : Type*} (D : ι → Measure ℝ) (c : Finset ι → ℝ) : Prop :=
  (∀ i, IsProbabilityMeasure (D i)) ∧ (∀ i, D i (Set.Iio 0) = 0) ∧
    (∀ i, Integrable (fun x : ℝ => x) (D i)) ∧ c ∅ = 0 ∧ Monotone c

end PandoraComb


