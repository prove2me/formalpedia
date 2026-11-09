-- Prove2me | Definitions.Def_PagingDelay_PMD_Model
-- name    : PagingDelay_PMD_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:02.869967+00:00
-- url     : https://prove2.me/theorems/dead2066-d086-4051-86f8-d32aca2fe11b
-- title:
--   Weighted paging with delay: requests, schedules and online algorithms
-- statement:
--   A request specifies a page, a nonnegative arrival time and a nonnegative delay function on nonnegative real time. Validity requires continuous, nondecreasing, unbounded delay, zero at zero. An instance is an arbitrary finite list; repetitions and simultaneous arrivals are allowed.
--
--   A schedule is a finite nondecreasing list of timed cache configurations. Every configuration has at most $k$ pages, and the fixed initial cache has exactly $k$. At arrival a request sees the cache in force before that instant and every configuration visited at that instant. Its serving time is the minimum of the finite candidate list, with an absent minimum represented by `none` and infinite delay cost. Fetching each newly cached page $i$ costs its positive weight $w_i$; eviction is free.
--
--   $$\operatorname{cost}(s,\sigma)=\operatorname{fetch}(s)+\sum_{r\in\sigma}d_r(\tau_r-a_r),\qquad
--   \operatorname{Opt}(\sigma)=\inf_{s\text{ valid}}\operatorname{cost}(s,\sigma).$$
--
--   Costs and the optimum take values in the extended nonnegative reals. All offline schedules occur in this infimum. With positive weights, finite-cost schedules have finitely many fetches, and evictions can be deferred to those fetches, so finite event lists preserve the offline infimum.
--
--   A randomized algorithm consists of a probability space and a schedule map for each seed. For each seed, equal revealed request lists through time $t$, including full delay functions, imply equal action lists through $t$. Its cost, fetch and delay are measurable random variables. Expected costs are their nonnegative Lebesgue integrals. No service or competitive guarantee is built into this interface. Lazy comparators exchange one cached page for one absent page at every event; period caches are taken after each distinct walk time, with the initial period excluded.
-- source:
--   Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), §2, p. 6; Definition 24, p. 20. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/453.pdf

import Mathlib

noncomputable section

namespace PagingDelay.PMD
open MeasureTheory
open scoped ENNReal BigOperators

/-- §2: validity is separate from the request data. Delays use nonnegative real time. -/
structure Request (n : ℕ) where
  page : Fin n
  arrival : ℝ
  delay : NNReal → NNReal

abbrev Instance (n : ℕ) := List (Request n)

def ValidRequest {n : ℕ} (r : Request n) : Prop :=
  0 ≤ r.arrival ∧ Monotone r.delay ∧ Continuous r.delay ∧ r.delay 0 = 0 ∧
    ∀ b : NNReal, ∃ t : NNReal, b < r.delay t

def ValidInstance {n : ℕ} (σ : Instance n) : Prop := ∀ r ∈ σ, ValidRequest r

/-- A cache event is one configuration in an ordered, possibly instantaneous walk. -/
structure CacheEvent (n : ℕ) where
  time : ℝ
  cache : Finset (Fin n)

abbrev Schedule (n : ℕ) := List (CacheEvent n)

def ScheduleValid {n : ℕ} (k : ℕ) (O₀ : Finset (Fin n)) (s : Schedule n) : Prop :=
  O₀.card = k ∧ (∀ e ∈ s, 0 ≤ e.time ∧ e.cache.card ≤ k) ∧
    s.Pairwise (fun e f => e.time ≤ f.time)

/-- Strictly before a time: arrivals see this cache before all walks at that time. -/
def cacheBefore {n : ℕ} (O₀ : Finset (Fin n)) (s : Schedule n) (t : ℝ) :=
  ((s.filter (fun e => e.time < t)).map CacheEvent.cache).getLastD O₀

/-- Cache after the whole offline walk at t, for hit/miss and excess. -/
def cacheAfter {n : ℕ} (O₀ : Finset (Fin n)) (s : Schedule n) (t : ℝ) :=
  ((s.filter (fun e => e.time ≤ t)).map CacheEvent.cache).getLastD O₀

/-- Minimum of a finite list, with no value (rather than zero) for the empty list. -/
def firstTime (ts : List ℝ) : Option ℝ :=
  ts.foldr (fun t z => some (match z with | none => t | some u => min t u)) none

/-- All possible first service times. If already present just before arrival, serve then;
otherwise every configuration visited at or after arrival is considered, including transients. -/
def serviceTime {n : ℕ} (O₀ : Finset (Fin n)) (s : Schedule n) (r : Request n) : Option ℝ :=
  firstTime ((if r.page ∈ cacheBefore O₀ s r.arrival then [r.arrival] else []) ++
    (s.filter (fun e => r.arrival ≤ e.time ∧ r.page ∈ e.cache)).map CacheEvent.time)

def fetchCostFrom {n : ℕ} (w : Fin n → ℝ) : Finset (Fin n) → Schedule n → ENNReal
  | _, [] => 0
  | c, e :: es => (∑ i ∈ e.cache \ c, ENNReal.ofReal (w i)) + fetchCostFrom w e.cache es

def requestDelay {n : ℕ} (r : Request n) : Option ℝ → ENNReal
  | none => ⊤
  | some t => (r.delay (Real.toNNReal (t - r.arrival)) : ENNReal)

def delayCost {n : ℕ} (O₀ : Finset (Fin n)) (s : Schedule n) (σ : Instance n) : ENNReal :=
  (σ.map (fun r => requestDelay r (serviceTime O₀ s r))).sum

def totalCost {n : ℕ} (w : Fin n → ℝ) (O₀ : Finset (Fin n)) (s : Schedule n)
    (σ : Instance n) : ENNReal := fetchCostFrom w O₀ s + delayCost O₀ s σ

/-- All offline schedules; never restricted to lazy or PMD-generated schedules. -/
def optimum {n : ℕ} (k : ℕ) (w : Fin n → ℝ) (O₀ : Finset (Fin n))
    (σ : Instance n) : ENNReal :=
  ⨅ s : {s : Schedule n // ScheduleValid k O₀ s}, totalCost w O₀ s.val σ

def revealed {n : ℕ} (σ : Instance n) (t : ℝ) := σ.filter (fun r => r.arrival ≤ t)
def eventPrefix {n : ℕ} (s : Schedule n) (t : ℝ) := s.filter (fun e => e.time ≤ t)

def Online {n : ℕ} (A : Instance n → Schedule n) : Prop :=
  ∀ σ σ' t, ValidInstance σ → ValidInstance σ' → revealed σ t = revealed σ' t →
    eventPrefix (A σ) t = eventPrefix (A σ') t

/-- A distribution over deterministic clairvoyant online maps. No service or cost bound
is bundled here. Full delay curves are revealed with their requests. -/
structure RandomizedAlgorithm (n k : ℕ) (w : Fin n → ℝ) (O₀ : Finset (Fin n)) where
  Seed : Type
  measurableSpace : MeasurableSpace Seed
  law : @Measure Seed measurableSpace
  probability : @IsProbabilityMeasure Seed measurableSpace law
  act : Seed → Instance n → Schedule n
  feasible : ∀ ω σ, ValidInstance σ → ScheduleValid k O₀ (act ω σ)
  online : ∀ ω, Online (act ω)
  measurable : ∀ σ, ValidInstance σ →
    letI := measurableSpace
    Measurable (fun ω => totalCost w O₀ (act ω σ) σ)
  measurableFetch : ∀ σ, ValidInstance σ →
    letI := measurableSpace
    Measurable (fun ω => fetchCostFrom w O₀ (act ω σ))
  measurableDelay : ∀ σ, ValidInstance σ →
    letI := measurableSpace
    Measurable (fun ω => delayCost O₀ (act ω σ) σ)

def expectedCost {n k : ℕ} {w : Fin n → ℝ} {O₀ : Finset (Fin n)}
    (A : RandomizedAlgorithm n k w O₀) (σ : Instance n) : ENNReal :=
  letI := A.measurableSpace
  ∫⁻ ω, totalCost w O₀ (A.act ω σ) σ ∂A.law

def expectedFetch {n k : ℕ} {w : Fin n → ℝ} {O₀ : Finset (Fin n)}
    (A : RandomizedAlgorithm n k w O₀) (σ : Instance n) : ENNReal :=
  letI := A.measurableSpace
  ∫⁻ ω, fetchCostFrom w O₀ (A.act ω σ) ∂A.law

def expectedDelay {n k : ℕ} {w : Fin n → ℝ} {O₀ : Finset (Fin n)}
    (A : RandomizedAlgorithm n k w O₀) (σ : Instance n) : ENNReal :=
  letI := A.measurableSpace
  ∫⁻ ω, delayCost O₀ (A.act ω σ) σ ∂A.law

def ServesAll {n : ℕ} (O₀ : Finset (Fin n)) (s : Schedule n) (σ : Instance n) : Prop :=
  ∀ r ∈ σ, ∃ t, serviceTime O₀ s r = some t

def ServesAlmostSurely {n k : ℕ} {w : Fin n → ℝ} {O₀ : Finset (Fin n)}
    (A : RandomizedAlgorithm n k w O₀) (σ : Instance n) : Prop :=
  letI := A.measurableSpace
  ∀ᵐ ω ∂A.law, ServesAll O₀ (A.act ω σ) σ

/-- Every nontrivial event exchanges exactly one resident and one absent page. -/
def LazyFrom {n : ℕ} : Finset (Fin n) → Schedule n → Prop
  | _, [] => True
  | c, e :: es =>
    (∃ p ∈ c, ∃ q, q ∉ c ∧ e.cache = insert q (c.erase p)) ∧ LazyFrom e.cache es

def LazyFeasible {n : ℕ} (k : ℕ) (O₀ : Finset (Fin n)) (s : Schedule n)
    (σ : Instance n) : Prop := ScheduleValid k O₀ s ∧ LazyFrom O₀ s ∧ ServesAll O₀ s σ

/-- Distinct positive-cost walks; full offline cache after each walk, excluding period zero. -/
def periodTimes {n : ℕ} (s : Schedule n) : List ℝ := (s.map CacheEvent.time).dedup

def periodCaches {n : ℕ} (O₀ : Finset (Fin n)) (s : Schedule n) : List (Finset (Fin n)) :=
  (periodTimes s).map (cacheAfter O₀ s)

end PagingDelay.PMD


