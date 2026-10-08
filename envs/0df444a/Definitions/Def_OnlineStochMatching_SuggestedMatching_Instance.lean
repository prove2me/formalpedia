-- Prove2me | Definitions.Def_OnlineStochMatching_SuggestedMatching_Instance
-- name    : OnlineStochMatching_SuggestedMatching_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:33:03.162313+00:00
-- url     : https://prove2.me/theorems/2aa29988-8d44-44a6-939e-22f97d0e5769
-- title:
--   Integer-frequency online stochastic matching instance
-- statement:
--   An instance has finite advertiser set $A$, finite impression-type set $I$, bipartite edge set $E\subseteq A\times I$, and nonnegative integer expected counts $e_i$. The number of independent arrivals is
--
--   $$n=\sum_{i\in I}e_i>0,\qquad \Pr_D[i]=e_i/n.$$
--
--   A realization records each arrival separately, even when types repeat. Its hindsight optimum is the size of a maximum matching between the arrival positions and advertisers along allowed edges. An integral flow in the paper's unit-advertiser, $e_i$-capacity network is represented by a maximum cardinality degree-capped edge set $M\subseteq E$. A labelling assigns each selected edge to one of its type's $e_i$ copies, with no ad assigned to two copies. These definitions supply the common model for the mission.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, pp. 3–5, §2 and §4.1, Offline Algorithm

import Mathlib

namespace OnlineStochMatching.SuggestedMatching

/-- A finite stochastic matching instance with integer expected type counts. -/
structure Instance (A I : Type) [Fintype I] where
  E : Finset (A × I)
  e : I → ℕ
  n : ℕ
  n_eq : n = ∑ i, e i
  n_pos : 0 < n

variable {A I : Type} [Fintype A] [Fintype I]

/-- The `e_i` equally likely copies of each impression type. -/
abbrev Instance.Copy (inst : Instance A I) : Type :=
  Σ i : I, Fin (inst.e i)

/-- A feasible integral flow in the paper's graph, viewed as a degree-capped edge set. -/
def IsBMatching (inst : Instance A I) (M : Finset (A × I)) : Prop := by
  classical
  exact M ⊆ inst.E ∧
    (∀ a, (M.filter fun p => p.1 = a).card ≤ 1) ∧
    (∀ i, (M.filter fun p => p.2 = i).card ≤ inst.e i)

/-- Maximum cardinality among feasible degree-capped edge sets. -/
def IsMaxBMatching (inst : Instance A I) (M : Finset (A × I)) : Prop :=
  IsBMatching inst M ∧ ∀ M', IsBMatching inst M' → M'.card ≤ M.card

/-- The ads incident to the integral maximum flow. -/
noncomputable def coveredAds (M : Finset (A × I)) : Finset A := by
  classical
  exact Finset.univ.filter fun a => ∃ i, (a, i) ∈ M

/-- An assignment of each selected edge to one of its type's `e_i` copies. It is
surjective onto the selected edges and no advertiser appears on two copies. -/
def IsLabelling (inst : Instance A I) (M : Finset (A × I))
    (label : inst.Copy → Option A) : Prop :=
  (∀ i a, (a, i) ∈ M ↔ ∃ j : Fin (inst.e i), label ⟨i, j⟩ = some a) ∧
  (∀ c d a, label c = some a → label d = some a → c = d)

/-- A feasible matching in the graph with one node for each arrival position. -/
def IsRealizationMatching (inst : Instance A I) (ω : Fin inst.n → inst.Copy)
    (R : Finset (A × Fin inst.n)) : Prop := by
  classical
  exact (∀ p ∈ R, (p.1, (ω p.2).1) ∈ inst.E) ∧
    (∀ a, (R.filter fun p => p.1 = a).card ≤ 1) ∧
    (∀ t, (R.filter fun p => p.2 = t).card ≤ 1)

/-- Cardinality of a maximum matching of the realized arrival graph. -/
noncomputable def optimum (inst : Instance A I) (ω : Fin inst.n → inst.Copy) : ℕ := by
  classical
  exact (Finset.univ : Finset (Finset (A × Fin inst.n))).sup
    (fun R => if IsRealizationMatching inst ω R then R.card else 0)

end OnlineStochMatching.SuggestedMatching


