-- Prove2me | Definitions.Def_SubquadCutReach_Faster_Reserve
-- name    : SubquadCutReach_Faster_Reserve
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T16:58:31.214706+00:00
-- url     : https://prove2.me/theorems/972ba9d0-fd08-46df-b79e-3fd100e3aa60
-- title:
--   Residual forest reserves and partial-orientation completion
-- statement:
--   Successive spanning forests are spanning acyclic subgraphs of successive residual graphs. Their union has $\lceil10n^{2/3}\log n\rceil$ rounds. A partition means disjoint nonempty induced vertex parts, each a singleton or $n^{2/3}$-edge-connected, with every inter-part edge in the forest union.
--
--   $$\left|\sum_{v\in S}b_{D_0}(v)\right|\le C_R(S)\quad\text{for every }S\subseteq V.$$
--
--   The reserved graph adds independently sampled potential edges at rate $\min\{1,a\log n/\sqrt{n^{2/3}}\}$. Independent fair pair directions orient the unreserved graph. The probability space couples both endpoint contributions of one pair, and makes distinct pairs independent. Completion input contains only the explicit reserve and measured imbalance vector. The construction grants no arbitrary subgraph-cut oracle.
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), §B.1–B.2, Observation B.1, Lemma B.2, Theorem B.3, Claim B.4, pp.24–26 (PDF pp.26–28)

import Mathlib
import Definitions.Def_SubquadCutReach_Faster_Protocol

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory

namespace SubquadCutReach.Faster

noncomputable def graphOfPairs {n : ℕ} (E : Finset (Fin n × Fin n)) : SimpleGraph (Fin n) where
  Adj u v := (u < v ∧ (u,v) ∈ E) ∨ (v < u ∧ (v,u) ∈ E)
  symm := ⟨fun {_ _} h => Or.symm h⟩
  loopless := ⟨by intro v h; rcases h with h|h <;> exact (lt_irrefl v h.1)⟩

/-- Mathlib acyclicity and equality of reachability express a spanning forest. -/
def SpanningForest {n : ℕ} (J : SimpleGraph (Fin n)) (E : Finset (Fin n × Fin n)) : Prop :=
  E ⊆ pairs J ∧ (graphOfPairs E).IsAcyclic ∧
    ∀ u v, (graphOfPairs E).Reachable u v ↔ J.Reachable u v

noncomputable def forestUnion {n : ℕ} (Fs : ℕ → Finset (Fin n × Fin n)) (r : ℕ) :=
  (Finset.range r).biUnion Fs

noncomputable def residual {n : ℕ} (J : SimpleGraph (Fin n))
    (Fs : ℕ → Finset (Fin n × Fin n)) (r : ℕ) : SimpleGraph (Fin n) :=
  graphOfPairs (pairs J \ forestUnion Fs r)

def ForestRun {n : ℕ} (J : SimpleGraph (Fin n)) (Fs : ℕ → Finset (Fin n × Fin n))
    (r : ℕ) : Prop := ∀ i < r, SpanningForest (residual J Fs i) (Fs i)

noncomputable def k (n : ℕ) : ℝ := (n:ℝ)^((2:ℝ)/3)
noncomputable def forestRounds (n : ℕ) : ℕ := Nat.ceil (10*k n*Real.log n)

/-- Induced parts; not connected components of the forest union. -/
def StrongPartition {n : ℕ} (J : SimpleGraph (Fin n)) (F : Finset (Fin n × Fin n))
    (parts : Finset (Finset (Fin n))) : Prop :=
  (∀ C ∈ parts, C.Nonempty) ∧
  (∀ v, ∃! C, C ∈ parts ∧ v ∈ C) ∧
  (∀ C ∈ parts, C.card = 1 ∨ ∀ S : Finset (Fin n),
    S ⊆ C → S.Nonempty → S ≠ C →
    k n ≤ ((pairs J).filter fun uv => (uv.1 ∈ S ∧ uv.2 ∈ C \ S) ∨
      (uv.2 ∈ S ∧ uv.1 ∈ C \ S)).card) ∧
  ∀ uv ∈ pairs J, (¬ ∃ C ∈ parts, uv.1 ∈ C ∧ uv.2 ∈ C) → uv ∈ F

noncomputable def remove {n : ℕ} (J : SimpleGraph (Fin n))
    (R : Finset (Fin n × Fin n)) : SimpleGraph (Fin n) := graphOfPairs (pairs J \ R)

def CompletionCondition {n : ℕ} (J : SimpleGraph (Fin n))
    (R : Finset (Fin n × Fin n)) (D₀ : Rule n) : Prop :=
  ∀ S : Finset (Fin n), |∑ v ∈ S, imbalance (induced (remove J R) D₀) v| ≤
    (cut (graphOfPairs R) S : ℤ)

/-- Independent uniforms for each potential pair and for its direction. Only increasing
pairs are used, so endpoint contributions are coupled, while distinct pairs are independent. -/
abbrev ReserveSample (n : ℕ) := (Fin n × Fin n) → (Fin 2 → ℝ)

noncomputable def reserveLaw (n : ℕ) : Measure (ReserveSample n) :=
  Measure.pi fun _ => Measure.pi fun _ : Fin 2 => volume.restrict (Set.Icc (0:ℝ) 1)

noncomputable def reserveRate (n : ℕ) (a : ℝ) : ℝ := min 1 (a*Real.log n/Real.sqrt (k n))

noncomputable def reserve {n : ℕ} (J : SimpleGraph (Fin n))
    (F : Finset (Fin n × Fin n)) (a : ℝ) (ω : ReserveSample n) : Finset (Fin n × Fin n) := by
  classical
  exact F ∪ (pairs J).filter fun uv => ω uv 0 ≤ reserveRate n a

noncomputable def randomDirection {n : ℕ} (ω : ReserveSample n) : Rule n :=
  fun u v => decide (ω (u,v) 1 ≤ (1/2:ℝ))

/-- Explicit reserve adjacency in a square block, then the measured partial imbalance. -/
noncomputable def completionInput {n : ℕ} (R : Finset (Fin n × Fin n)) (b : Fin n → ℤ) : Memory := by
  classical
  exact input n 0 0 fun i =>
    if hi : i < n*n then
      if hu : i/n < n then if hv : i%n < n then
        if (⟨i/n,hu⟩,⟨i%n,hv⟩) ∈ R then 1 else 0 else 0 else 0
    else if hi : i-n*n < n then b ⟨i-n*n,hi⟩ else 0

end SubquadCutReach.Faster


