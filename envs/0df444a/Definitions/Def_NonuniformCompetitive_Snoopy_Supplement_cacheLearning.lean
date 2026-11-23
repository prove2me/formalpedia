-- Prove2me | Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_cacheLearning
-- name    : NonuniformCompetitive_Snoopy_Supplement_cacheLearning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:53:40.183315+00:00
-- url     : https://prove2.me/theorems/ff20f75b-9465-44cf-97dc-cb4337a3653c
-- title:
--   Causal caching thresholds, empirical learning and the previous-run policy
-- statement:
--   A policy chooses a threshold $i\in\{0,\ldots,p\}$ from the lengths of completed write runs of the current block. The corresponding causal cache algorithm privatizes after $i$ writes and respects the published look-ahead-zero rule at every write. Repeated reads by the active processor do not end a run; a read by another processor completes it. The complete-run threshold loss is
--   $$L_p(i,l)=\min\{i,l\}+p\,\mathbf1_{\{i\le l\}}.$$
--   The empirical policy minimizes the sum of these losses over all past completed runs, with a fixed tie choice, and uses $A_p$ initially. The one-sample policy instead chooses $A_p$ if the previous run length $l\le p$ and $A_0$ if $l>p$, also starting with $A_p$.
--
--   Costs and offline optima add over an arbitrary fixed finite address space; interleavings do not change this sum. Distributional comparison quantifies over every finite per-block horizon and every joint law with the specified iid run-length marginal on each block. Laws can differ between blocks and need not have moments or finite support. The additive constant may depend on the fixed instance, laws and factor, but never on the horizons.
--
--   The finite threshold family is the support of the source randomized mixture; it is sufficient for the full existence guarantee. This does not claim that thresholds outside that family never improve a particular law's optimum.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, §3.1, p. 550; §3.4, pp. 556–558

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_randomized
import Definitions.Def_NonuniformCompetitive_Snoopy_ep

namespace NonuniformCompetitive.Snoopy.Supplement

open MeasureTheory
open scoped NNReal ENNReal

/-- Thresholds 0,...,p. A threshold i makes a block private after i writes
of the current run. The history consists of the lengths of COMPLETED runs. -/
abbrev CachePolicy (p : ℕ) := List ℕ → Fin (p + 1)

structure CacheMemory (n : ℕ) where
  active : Option (Fin n)
  writes : ℕ
  completed : List ℕ
  threshold : ℕ
  state : NonuniformCompetitive.Snoopy.State n

noncomputable def cacheReadMoment {n : ℕ} (s : NonuniformCompetitive.Snoopy.State n)
    (i : Fin n) : NonuniformCompetitive.Snoopy.State n := if s = some i then some i else none

noncomputable def cacheNext {n p : ℕ} (f : CachePolicy p) (q : CacheMemory n) :
    NonuniformCompetitive.Snoopy.Req n → CacheMemory n
  | .read i =>
      let newRun := q.active ≠ some i
      let past := if newRun ∧ q.active.isSome then q.completed ++ [q.writes] else q.completed
      let k := if newRun then (f past).val else q.threshold
      let m := cacheReadMoment q.state i
      {active := some i, writes := if newRun then 0 else q.writes,
       completed := past, threshold := k, state := if k = 0 then some i else m}
  | .write i =>
      {q with writes := q.writes + 1, state := if q.state = none ∧ q.threshold ≤ q.writes + 1 then some i else q.state}

noncomputable def cacheTrace {n p : ℕ} (f : CachePolicy p)
    (s₀ : NonuniformCompetitive.Snoopy.State n) : List (NonuniformCompetitive.Snoopy.Req n) → CacheMemory n
  | [] => {active := none, writes := 0, completed := [], threshold := (f []).val, state := s₀}
  | r :: rs => rs.foldl (cacheNext f) (cacheNext f
      {active := none, writes := 0, completed := [], threshold := (f []).val, state := s₀} r)

/-- An actual causal algorithm on the published request model, including the
look-ahead-zero rule for writes. Repeated reads by the active processor do not
end a run. Reads by another processor start a new run, possibly with zero writes. -/
noncomputable def cacheAlgorithm {n p : ℕ} (f : CachePolicy p)
    (s₀ : NonuniformCompetitive.Snoopy.State n) : NonuniformCompetitive.Snoopy.OnlineAlgorithm n where
  after h := (cacheTrace f s₀ h).state
  moment h := match h.reverse with
    | [] => s₀
    | .write _ :: rest => (cacheTrace f s₀ rest.reverse).state
    | .read i :: rest => cacheReadMoment (cacheTrace f s₀ rest.reverse).state i
  lookaheadZero := by intro h i; simp

/-- Cost of a complete write run at threshold i, including its terminal
broadcast when it became private. The final unfinished run is handled by the
additive constant in the finite-input comparison. -/
def thresholdRunCost (p i l : ℕ) : ℕ := min i l + if i ≤ l then p else 0

/-- Empirical minimization over the finite family A_0,...,A_p, using ALL past
completed runs. The first run uses A_p; later ties use a fixed classical choice
from the finite set of minimizers. The policy never takes a law P as input. -/
noncomputable def empiricalCachePolicy (p : ℕ) : CachePolicy p := fun h =>
  if h = [] then ⟨p, Nat.lt_succ_self p⟩ else
    Classical.choose (Finset.exists_min_image Finset.univ
      (fun i : Fin (p + 1) => (h.map (thresholdRunCost p i.val)).sum) Finset.univ_nonempty)

/-- Theorem 8's exact one-sample tie rule: A_p when l ≤ p, A_0 when l > p.
Use A_p on the first run. -/
def previousRunPolicy (p : ℕ) : CachePolicy p := fun h =>
  if h.getLast?.getD 0 ≤ p then ⟨p, Nat.lt_succ_self p⟩ else ⟨0, Nat.zero_lt_succ p⟩

/-- A completed run is a read followed by the given number of writes. -/
def cacheRun {n : ℕ} (i : Fin n) (l : ℕ) : List (NonuniformCompetitive.Snoopy.Req n) :=
  [.read i] ++ List.replicate l (.write i)

def cacheRunWord {n N : ℕ} (owners : Fin N → Fin n) (lengths : Fin N → ℕ) :
    List (NonuniformCompetitive.Snoopy.Req n) :=
  (List.ofFn fun j => cacheRun (owners j) (lengths j)).flatten

/-- Independent blocks in the unlimited-cache model: projections are sufficient
because costs and feasibility add over blocks. Arbitrary interleavings give the
same total cost. The finite address space is an instance parameter, not fixed to
one block. A different initial private/shared state is allowed for each block. -/
noncomputable def cacheFamilyCost {B : Type} [Fintype B] {n p : ℕ} (f : CachePolicy p)
    (s₀ : B → NonuniformCompetitive.Snoopy.State n)
    (σ : B → List (NonuniformCompetitive.Snoopy.Req n)) : ℝ≥0∞ :=
  ∑ b, (cacheAlgorithm f (s₀ b)).cost p (σ b)

noncomputable def cacheFamilyOpt {B : Type} [Fintype B] {n : ℕ} (p : ℕ)
    (s₀ : B → NonuniformCompetitive.Snoopy.State n)
    (σ : B → List (NonuniformCompetitive.Snoopy.Req n)) : ℝ≥0∞ :=
  ∑ b, NonuniformCompetitive.Snoopy.offlineCost p (s₀ b) (σ b)

/-- Expectation over arbitrary joint laws with iid run-length marginals on each
block. Distinct blocks may have distinct distributions and arbitrary dependence.
The one additive constant precedes all finite run horizons and processor choices.
Owners are permitted even to depend on the realized input (a harmless extension
because the cost bound is invariant under renaming the active processors). -/
def CacheIIDCompetitive {B : Type} [Fintype B] {n p : ℕ} (f : CachePolicy p)
    (s₀ : B → NonuniformCompetitive.Snoopy.State n) (P : B → Measure ℕ) (c : ℝ) : Prop :=
  ∃ a : ℝ, ∀ (N : B → ℕ)
    (owners : (∀ b, Fin (N b) → ℕ) → ∀ b, Fin (N b) → Fin n)
    (ν : Measure (∀ b, Fin (N b) → ℕ)),
    IsProbabilityMeasure ν →
    (∀ b, Measure.map (fun x => x b) ν = Measure.pi (fun _ : Fin (N b) => P b)) →
    (∀ x b (j : Fin (N b)) (k : Fin (N b)), j.val + 1 = k.val → owners x b j ≠ owners x b k) →
    (∫⁻ x, cacheFamilyCost f s₀ (fun b => cacheRunWord (owners x b) (x b)) ∂ν) ≤
      ENNReal.ofReal c *
        (∫⁻ x, cacheFamilyOpt p s₀ (fun b => cacheRunWord (owners x b) (x b)) ∂ν) +
      ENNReal.ofReal a

end NonuniformCompetitive.Snoopy.Supplement


