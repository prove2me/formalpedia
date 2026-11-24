-- Prove2me | Definitions.Def_ValTrackRM_Public_Supplement_Sampling
-- name    : ValTrackRM_Public_Supplement_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:58:37.472671+00:00
-- url     : https://prove2.me/theorems/caeb6765-ce80-4fd0-9549-dc3a7f03a317
-- title:
--   Algorithm 2 and Definitions 7–9 — bounded sampling, execution counts and first-failure histories
-- statement:
--   Samp simulates fresh Algorithm 1 runs on independent past valuations until one has the current remaining inventory. It then draws a price from that run's next-price law. After exactly $C(k+1)t^2$ unsuccessful attempts it rejects, still observes the current distribution and advances. The hypothetical augmented Exp instead uses the exact conditional Exp kernel after an unsuccessful sampling stage. Both processes choose the price before drawing the actual current valuation.
--
--   Each branch of the finite random execution records its public observations, remaining inventory, earned revenue, arithmetic/scan/sampling operation count and number of simulated customer transitions. The bounded trial loop and every simulated customer transition are explicit recursions. A least-index minimum-level scan implements the selector used by the runtime theorem. Weighted lists enumerate execution-tree leaves mathematically; the algorithm traverses one branch with one categorical draw at each random node.
--
--   A first-failure history at time $t$ has arbitrary earlier prices and valuations, all earlier failure flags zero and final flag one. In particular,
--   $$
--   \mathcal F_t=\bigl(\{r^{(1)},\ldots,r^{(m)},\infty\}\times\{0,r^{(1)},\ldots,r^{(m)}\}\bigr)^{t-1}.
--   $$
--   The terminal flag at $T+1$ is one. Event masses and conditional expected revenues are finite weighted sums over executions; a zero-mass history has conditional expectation zero. All histories, including impossible ones, remain in the domain. Operations charge finite arithmetic, array scans/copies, input storage and categorical sampling oracles, including initialization and the final price choice. They do not claim arbitrary-real bit complexity.
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, pp. 21–23, Algorithm 2, Definitions 7–9; pp. ec14–ec16

import Mathlib
import Definitions.Def_ValTrackRM_Public_Supplement_Stochastic

namespace ValTrackRM.Public.Supplement

attribute [local instance] Classical.propDecidable

/-! Algorithm 2, pp.21–23. Lists below enumerate the leaves of finite random
executions, with their probability weights. FlatMap is their semantic enumeration,
not an instruction to enumerate all leaves at runtime. Each categorical node is one
oracle draw; counters charge scans, arithmetic, storage and the actual bounded loops.
No conditional inventory probability is used by the Samp implementation. -/

/-- Finite weighted branch composition (plain lists, without distribution axioms). -/
noncomputable def branch {α β : Type} (xs : List (α × ℝ))
    (f : α → List (β × ℝ)) : List (β × ℝ) :=
  xs.flatMap fun x => (f x.1).map fun y => (y.1, x.2 * y.2)

noncomputable def average {α : Type} (xs : List (α × ℝ)) (f : α → ℝ) : ℝ :=
  (xs.map fun x => x.2 * f x.1).sum

/-- A categorical node, including zero-weight leaves. -/
noncomputable def priceDraw {m : ℕ} (weights : Price m → ℝ) : List (Price m × ℝ) :=
  (List.finRange (m + 1)).map fun p => (p, weights p)

noncomputable def valueDraw {m : ℕ} (ν : PMF (Fin (m + 1))) : List (Fin (m + 1) × ℝ) :=
  (List.finRange (m + 1)).map fun v => (v, (ν v).toReal)

/-- Linear scan, retaining the least index in ties. Each comparison/lookup/update
is charged; initialized with index zero because k is positive. -/
def minScan {m k : ℕ} (hk : 0 < k) (L : Fin k → Fin (m + 1)) : Fin k × ℕ :=
  (List.finRange k).foldl (fun z i =>
    if L i < L z.1 then (i, z.2 + 4) else (z.1, z.2 + 4)) (⟨0, hk⟩, 1)

def leastSelector {m k : ℕ} (hk : 0 < k) (L : Fin k → Fin (m + 1)) : Fin k :=
  (minScan hk L).1

/-- Charge for the linear selector scan. This is used only for leastSelector
when a computational bound is asserted, never for an arbitrary selector. -/
def selectorWork (k : ℕ) : ℕ := (List.range k).foldl (fun c _ => c + 4) 1

/-- Offer table evaluation: each entry computes the q numerator, suffix sum and
ratio by a finite scan. Counting repeated suffix scans is conservative and polynomial.
Array updates and copies are charged separately in each simulation transition. -/
def offerWork (m ℓ : ℕ) : ℕ :=
  (List.range (m + 1)).foldl
    (fun c _ => c + 12 + (List.range (m - ℓ)).foldl (fun d _ => d + 5) 0) 3

structure SimFrame (m k : ℕ) where
  level : Fin k → Fin (m + 1)
  sold : Fin k → Bool
  operations : ℕ
  transitions : ℕ

/-- Algorithm 1 on independently sampled past valuations. Every simulated
customer draws its price before its valuation and updates the base levelStep. -/
noncomputable def simulate {m k : ℕ} (r : ℕ → ℝ)
    (sel : (Fin k → Fin (m + 1)) → Fin k) (ν : ℕ → PMF (Fin (m + 1))) :
    ℕ → List (SimFrame m k × ℝ)
  | 0 => [(⟨fun _ => 0, fun _ => false, 10 * (k + 1), 0⟩, 1)]
  | n + 1 => branch (simulate r sel ν n) fun st =>
      branch (priceDraw (unitPrice r sel st.level st.sold)) fun p =>
      branch (valueDraw (ν (n + 1))) fun v =>
        let s := if buys r (inventory st.sold) p v then Function.update st.sold (sel st.level) true
          else st.sold
        [(⟨levelStep sel st.level v, s,
          st.operations + selectorWork k + offerWork m (st.level (sel st.level)).val +
            12 * (k + m + 1), st.transitions + 1⟩, 1)]

structure TrialResult (m k : ℕ) where
  matched : Option (SimFrame m k)
  operations : ℕ
  transitions : ℕ

/-- Actual bounded rejection-sampling loop: each failed attempt runs a fresh
simulation from time zero; stop at the first inventory match, otherwise exhaust fuel. -/
noncomputable def trials {m k : ℕ} (r : ℕ → ℝ)
    (sel : (Fin k → Fin (m + 1)) → Fin k) (ν : ℕ → PMF (Fin (m + 1)))
    (n a : ℕ) : ℕ → List (TrialResult m k × ℝ)
  | 0 => [(⟨none, 1, 0⟩, 1)]
  | fuel + 1 => branch (simulate r sel ν n) fun st =>
      if inventory st.sold = a then
        [(⟨some st, st.operations + 3 * (k + 1), st.transitions⟩, 1)]
      else branch (trials r sel ν n a fuel) fun rest =>
        [(⟨rest.matched, st.operations + 3 * (k + 1) + rest.operations,
          st.transitions + rest.transitions⟩, 1)]

structure RoundChoice (m : ℕ) where
  failed : Bool
  price : Price m
  operations : ℕ
  transitions : ℕ

/-- On a matched run use its line6–11 price kernel; on failure Samp rejects.
The hypothetical augmented Exp uses the correct conditional kernel after failure.
The input contains only past distributions, time, inventory and fresh simulation. -/
noncomputable def samplePrice {m k : ℕ} (r : ℕ → ℝ)
    (sel : (Fin k → Fin (m + 1)) → Fin k) (ν : ℕ → PMF (Fin (m + 1)))
    (C t a : ℕ) (augmented : Bool) : List (RoundChoice m × ℝ) :=
  branch (trials r sel ν (t - 1) a (C * (k + 1) * t ^ 2)) fun result =>
    match result.matched with
    | some st => (priceDraw (unitPrice r sel st.level st.sold)).map fun pw =>
        (⟨false, pw.1, result.operations + selectorWork k +
          offerWork m (st.level (sel st.level)).val + 10, result.transitions⟩, pw.2)
    | none => (priceDraw (if augmented then expKernel r sel ν t a else reject)).map fun pw =>
        (⟨true, pw.1, result.operations + 10, result.transitions⟩, pw.2)

structure Observation (m : ℕ) where
  failed : Bool
  price : Price m
  value : Fin (m + 1)
  deriving DecidableEq

structure Execution (m : ℕ) where
  observations : List (Observation m)
  stock : ℕ
  revenue : ℝ
  operations : ℕ
  simulatedTransitions : ℕ

/-- Full public run. On failure still observe/store the distribution and advance.
Pricing never reads the actual hidden valuations in observations. The current law
is used by valueDraw only after samplePrice has selected the current price. -/
noncomputable def publicRun {m k : ℕ} (r : ℕ → ℝ)
    (sel : (Fin k → Fin (m + 1)) → Fin k) (ν : ℕ → PMF (Fin (m + 1)))
    (C : ℕ) (augmented : Bool) : ℕ → List (Execution m × ℝ)
  | 0 => [(⟨[], k, 0, 10 * (k + m + 1), 0⟩, 1)]
  | n + 1 => branch (publicRun r sel ν C augmented n) fun ex =>
      branch (samplePrice r sel ν C (n + 1) ex.stock augmented) fun ch =>
      branch (valueDraw (ν (n + 1))) fun v =>
        [(⟨ex.observations ++ [⟨ch.failed, ch.price, v⟩], nextStock r ex.stock ch.price v,
          ex.revenue + payment r ex.stock ch.price v,
          ex.operations + ch.operations + 10 * (n + k + m + 1),
          ex.simulatedTransitions + ch.transitions⟩, 1)]

noncomputable def samplingRevenue {m k : ℕ} (r : ℕ → ℝ)
    (sel : (Fin k → Fin (m + 1)) → Fin k) (ν : ℕ → PMF (Fin (m + 1)))
    (C T : ℕ) (augmented : Bool) : ℝ :=
  average (publicRun r sel ν C augmented T) Execution.revenue

/-- F_t has arbitrary prices/valuations at t-1 earlier positions, zero prior
failure flags, and final flag one. Thus no reachability restriction is imposed. -/
abbrev FirstHistory (m t : ℕ) := Fin (t - 1) → Price m × Fin (m + 1)

/-- H_t = h_t for h_t in F_t. The terminal flag at T+1 is one.
The length bound prevents an additional fictitious failure after T+1. -/
def matchesFirst {m : ℕ} (ex : Execution m) (t : ℕ) (h : FirstHistory m t) : Prop :=
  1 ≤ t ∧ t ≤ ex.observations.length + 1 ∧
  ex.observations.take (t - 1) = List.ofFn (fun i => (⟨false, (h i).1, (h i).2⟩ : Observation m)) ∧
  (if t ≤ ex.observations.length then
    (ex.observations[t - 1]?.map Observation.failed).getD false = true else True)

noncomputable def firstMass {m k : ℕ} (r : ℕ → ℝ)
    (sel : (Fin k → Fin (m + 1)) → Fin k) (ν : ℕ → PMF (Fin (m + 1)))
    (C T : ℕ) (augmented : Bool) (t : ℕ) (h : FirstHistory m t) : ℝ :=
  average (publicRun r sel ν C augmented T) fun ex => if matchesFirst ex t h then 1 else 0

noncomputable def conditionalRevenue {m k : ℕ} (r : ℕ → ℝ)
    (sel : (Fin k → Fin (m + 1)) → Fin k) (ν : ℕ → PMF (Fin (m + 1)))
    (C T : ℕ) (augmented : Bool) (t : ℕ) (h : FirstHistory m t) : ℝ :=
  (average (publicRun r sel ν C augmented T) fun ex =>
    if matchesFirst ex t h then ex.revenue else 0) / firstMass r sel ν C T augmented t h

/-- Mutually exclusive and collectively exhaustive, stated path by path. -/
def firstPartition {m : ℕ} (xs : List (Execution m × ℝ)) (T : ℕ) : Prop :=
  ∀ x ∈ xs, ∃! a : (t : Fin (T + 1)) × FirstHistory m (t.val + 1),
    matchesFirst x.1 (a.1.val + 1) a.2

noncomputable def firstFailureMass {m k : ℕ} (r : ℕ → ℝ)
    (sel : (Fin k → Fin (m + 1)) → Fin k) (ν : ℕ → PMF (Fin (m + 1)))
    (C T t : ℕ) : ℝ := ∑ h : FirstHistory m t, firstMass r sel ν C T false t h

/-- Exactly the printed C, including epsilon greater than one. -/
noncomputable def sampleConstant (ε : ℝ) : ℕ := ⌈6 / (Real.exp 1 * Real.pi ^ 2 * ε)⌉₊

end ValTrackRM.Public.Supplement


