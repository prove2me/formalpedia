-- Prove2me | Definitions.Def_CorrKClust_BalancedPivot_Supplement_Uniform
-- name    : CorrKClust_BalancedPivot_Supplement_Uniform
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:26:19.626617+00:00
-- url     : https://prove2.me/theorems/8be0c0da-a340-444d-bc84-7775a2253530
-- title:
--   UNIFORM PIVOT, its conditional coin law and Section 6 events
-- statement:
--   Write $T_0$ for the arrival time of the $k$th chronological PIVOT root. UNIFORM PIVOT runs an arrival recursion: the first $k$ pivots receive fresh labels; nonpivots join their earliest adjacent pivot; when root $k$ arrives the set $S$ of labels with load at most $128\ln n$ is frozen. Every later pivot chooses independently uniformly from this same $S$. The threshold is $(128\ln2)\log_2n$, matching the proof with $c=32$.
--
--   Conditionally on the arrival order, the coin-table law is the product of the uniform laws on $S$. Coins attached to nonpivots and early pivots are unused and integrate out. If $S$ is empty, unused coins use the uniform law on all $k$ labels; in the valid cases needing a late choice, the $k$th pivot itself ensures $S\ne\varnothing$. Empty and singleton inputs, and inputs with at most $k$ cliques, retain their zero-cost behavior. The expected cost averages this conditional weighted law over all arrival permutations.
--
--   For the analysis, sort the original nonempty blocks by decreasing size. Put $c_1=\max\{40,2c_0+1\}$ and
--   $$B_i=\frac{c_1 n\log_2 n}{2^i},\qquad p_i=\frac{2^{i+1}}n.$$
--   The module defines $T_i=\{2^i\le T_0<2^{i+1}\}$, the simultaneous large-clique early-arrival event $G_1$, and the counts $Y_i,N_i$ from the fixed tails after $k$ and $r$, respectively, at deterministic time $\min\{2^{i+1},n\}$. It also counts top-$k$ cliques wholly uncovered at $T_0$. Counts and the set of small leading pivots reuse the published PIVOT interfaces.
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), §6, p. 22

import Definitions.Def_CorrKClust_BalancedPivot_Analysis

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot.Supplement

def logTwo (n : ℕ) : ℝ := Real.log n / Real.log 2

def uniformC0 : ℝ := 128 * Real.log 2

/-- Small leading pivots at T0, with the threshold passed explicitly. -/
def smallPivots {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (σ : ArrivalOrder (Fin n)) (threshold : ℝ) : Finset (Fin n) :=
  ((pivotRun G σ (kthPivotTime G k σ)).pivots.toFinset).filter
    (fun v => (pivotSize G σ (kthPivotTime G k σ) v : ℝ) ≤ threshold)

/-- Labels 0,…,k−1 correspond to the chronological first k pivots. -/
def frozenLabels {n k : ℕ} (G : SimpleGraph (Fin n))
    (σ : ArrivalOrder (Fin n)) : Finset (Fin k) :=
  Finset.univ.filter (fun b =>
    match (pivotRun G σ (kthPivotTime G k σ)).pivots[b.val]? with
    | none => False
    | some v => (pivotSize G σ (kthPivotTime G k σ) v : ℝ) ≤ uniformC0 * logTwo n)

structure UniformState (n k : ℕ) where
  seen : List (Fin n)
  roots : List (Fin n)
  assignment : Fin n → Fin k
  frozen : Finset (Fin k)

/-- Honest arrival recursion. S is computed once when root k appears and never updated.
The chosen coin at a later pivot is independent and uniform in this frozen set. -/
def uniformStep {n k : ℕ} (G : SimpleGraph (Fin n)) (coins : Fin n → Fin k)
    (s : UniformState n k) (v : Fin n) : UniformState n k :=
  match s.roots.find? (fun p => decide (G.Adj v p)) with
  | some p => ⟨s.seen ++ [v], s.roots,
      Function.update s.assignment v (s.assignment p), s.frozen⟩
  | none =>
    if h : s.roots.length < k then
      let b : Fin k := ⟨s.roots.length, h⟩
      let f := Function.update s.assignment v b
      let seen := s.seen ++ [v]
      let S := if s.roots.length + 1 = k then
        Finset.univ.filter (fun j => (historyLoad seen f j : ℝ) ≤ uniformC0 * logTwo n)
        else s.frozen
      ⟨seen, s.roots ++ [v], f, S⟩
    else ⟨s.seen ++ [v], s.roots ++ [v],
      Function.update s.assignment v (coins v), s.frozen⟩

def uniformRun {n k : ℕ} (hk : 0 < k) (G : SimpleGraph (Fin n))
    (σ : ArrivalOrder (Fin n)) (coins : Fin n → Fin k) : UniformState n k :=
  (arrivalList σ).foldl (uniformStep G coins) ⟨[], [], fun _ => ⟨0, hk⟩, ∅⟩

/-- Independent choices indexed by vertices, used only if that vertex becomes a late pivot.
Conditioned on σ, all n choices are uniform on S(σ); unused coordinates integrate out.
The empty-S fallback is used only when no later pivot needs a choice (n≤1 or <k pivots). -/
def coinWeight {n k : ℕ} (G : SimpleGraph (Fin n)) (σ : ArrivalOrder (Fin n))
    (coins : Fin n → Fin k) : ℝ :=
  let S := frozenLabels (k := k) G σ
  ∏ v : Fin n, if S.Nonempty then
    (if coins v ∈ S then 1 / (S.card : ℝ) else 0) else 1 / (k : ℝ)

def uniformCost {n k : ℕ} (hk : 0 < k) (G : SimpleGraph (Fin n)) : ℝ :=
  average (fun σ : ArrivalOrder (Fin n) =>
    wExp (coinWeight G σ) (fun coins => (cost G (uniformRun hk G σ coins).assignment : ℝ)))

/-- A deterministic size ordering, with arbitrary ties; it affects analysis only. -/
def sortedCliques {n : ℕ} (Q : Fin n → Fin n) : List (Finset (Fin n)) :=
  (blocks Q).toList.mergeSort (fun A B => decide (B.card ≤ A.card))

def tailVertices {n : ℕ} (Q : Fin n → Fin n) (r : ℕ) : Finset (Fin n) :=
  ((sortedCliques Q).drop r).toFinset.biUnion id

def dyadicB (n : ℕ) (c0 : ℝ) (i : ℕ) : ℝ :=
  max 40 (2 * c0 + 1) * n * logTwo n / (2 : ℝ) ^ i

def dyadicP (n i : ℕ) : ℝ := (2 : ℝ) ^ (i + 1) / n

def interval {n : ℕ} (G : SimpleGraph (Fin n)) (k i : ℕ)
    (σ : ArrivalOrder (Fin n)) : Prop :=
  2 ^ i ≤ kthPivotTime G k σ ∧ kthPivotTime G k σ < 2 ^ (i + 1)

def goodOne {n : ℕ} (Q : Fin n → Fin n) (c0 : ℝ)
    (σ : ArrivalOrder (Fin n)) : Prop :=
  ∀ j ≤ Nat.log 2 n, ∀ K ∈ blocks Q, dyadicB n c0 j ≤ (K.card : ℝ) →
    c0 * logTwo n < (prefixCount K (2 ^ j) σ : ℝ)

def countY {n : ℕ} (Q : Fin n → Fin n) (k i : ℕ)
    (σ : ArrivalOrder (Fin n)) : ℕ :=
  prefixCount (tailVertices Q k) (min (2 ^ (i + 1)) n) σ

def countN {n : ℕ} (Q : Fin n → Fin n) (k i : ℕ)
    (σ : ArrivalOrder (Fin n)) : ℕ :=
  prefixCount (tailVertices Q (cliqueR (blockSizes Q) k)) (min (2 ^ (i + 1)) n) σ

def missingTop {n : ℕ} (G : SimpleGraph (Fin n)) (Q : Fin n → Fin n)
    (k : ℕ) (σ : ArrivalOrder (Fin n)) : ℕ :=
  (((sortedCliques Q).take k).filter (fun K =>
    decide (K ⊆ uncovered G σ (kthPivotTime G k σ)))).length

end CorrKClust.BalancedPivot.Supplement


