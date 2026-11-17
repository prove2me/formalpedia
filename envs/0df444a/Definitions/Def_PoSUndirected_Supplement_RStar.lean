-- Prove2me | Definitions.Def_PoSUndirected_Supplement_RStar
-- name    : PoSUndirected_Supplement_RStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:31:48.841217+00:00
-- url     : https://prove2.me/theorems/6b561ca0-c5a3-4092-92a4-80c064a93aca
-- title:
--   Labelled cut-user sets, admissible terminal orders and $R^*(D)$
-- statement:
--   Let $D$ be a nonempty labelled demand multigraph, with one edge for every nontrivial player and vertex set exactly the vertices incident with those demand edges. For a terminal set $A$, $U_D(A)$ is the exact labelled set of players with one terminal in $A$ and one outside. An order of all terminal vertices is admissible when its two extreme vertices form a demanded pair. For each admissible order, take the proper prefix cuts, deduplicate identical labelled user sets, and sum the reciprocals of their cardinalities. Then
--   $$
--   R^*(D)=\max_{\pi\ \mathrm{admissible}}\sum_{U\in\mathcal U_\pi}\frac1{|U|}.
--   $$
--
--   Different labelled sets of the same cardinality remain distinct. The interface also defines feasible positive-cost host realizations, universal approximate/weak/strict optimum stability, uniform player replication and the exact weak replication threshold.
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), §5 and Theorem 5.1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_PoSUndirected_Supplement_IsSocialOptimum

open CongestionPoA.AsymSum

set_option autoImplicit false

namespace PoSUndirected.Supplement

variable {T ι : Type*} [Fintype T] [DecidableEq T] [LinearOrder T] [Nonempty T]
  [Fintype ι] [DecidableEq ι]

/-!
# The labelled demand multigraph and `R⋆(D)`

Tsoufis, preprint sha256 c095d811…, §5, p.10 (PDF p.12).  Player labels are retained in
cut-user sets, so distinct sets of the same cardinality remain distinct.
-/

/-- The exact labelled set of demands crossing the terminal cut `A`. -/
def cutUsers (s t : ι → T) (A : Finset T) : Finset ι :=
  Finset.univ.filter fun i ↦ (s i ∈ A) ≠ (t i ∈ A)

/-- A permutation of all terminal vertices is admissible when its two extreme vertices are the
endpoints of some labelled demand edge. -/
def IsAdmissibleOrder (s t : ι → T) (π : Equiv.Perm T) : Prop :=
  ∃ i : ι,
    (s i = π (Finset.univ.min' Finset.univ_nonempty) ∧
      t i = π (Finset.univ.max' Finset.univ_nonempty)) ∨
    (t i = π (Finset.univ.min' Finset.univ_nonempty) ∧
      s i = π (Finset.univ.max' Finset.univ_nonempty))

/-- Prefix terminal set at the cut immediately after position `j` of the order `π`. -/
def orderPrefix (π : Equiv.Perm T) (j : T) : Finset T :=
  Finset.univ.filter fun v ↦ π.symm v ≤ j

/-- The *distinct* exact labelled cut-user sets occurring at proper prefixes of `π`.  Identical
sets are deduplicated by `Finset.image`; equal cardinality alone does not identify two sets. -/
def prefixUserSets (s t : ι → T) (π : Equiv.Perm T) : Finset (Finset ι) :=
  (Finset.univ.erase (Finset.univ.max' Finset.univ_nonempty)).image
    (fun j ↦ cutUsers s t (orderPrefix π j))

/-- Reciprocal cut-load sum of an admissible order. -/
noncomputable def orderReciprocalSum (s t : ι → T) (π : Equiv.Perm T) : ℝ :=
  ∑ U ∈ prefixUserSets s t π, 1 / (U.card : ℝ)

/-- `R⋆(D)`: the maximum reciprocal sum over admissible orders.  It is written as a supremum;
under `NonemptyDemand` the set is finite and nonempty, and every denominator is positive because
the extreme-pair demand crosses every proper prefix. -/
noncomputable def RStar (s t : ι → T) : ℝ :=
  sSup {x : ℝ | ∃ π : Equiv.Perm T, IsAdmissibleOrder s t π ∧ orderReciprocalSum s t π = x}

/-- The demand multigraph remaining after trivial pairs are discarded is nonempty, has no
trivial demand edge, and has vertex set exactly the vertices incident with its demand edges. -/
def NonemptyDemand (s t : ι → T) : Prop :=
  (Finset.univ : Finset ι).Nonempty ∧ (∀ i, s i ≠ t i) ∧
    ∀ v : T, ∃ i : ι, s i = v ∨ t i = v

/-- A finite positive-cost physical host realizing the terminal labels by an injective embedding;
every demand has at least one simple physical path. -/
def IsFeasibleHost (s t : ι → T) {nV nE : ℕ} (ends : Fin nE → Sym2 (Fin nV))
    (c : Fin nE → ℝ) (embed : T → Fin nV) : Prop :=
  Function.Injective embed ∧ IsLoopless ends ∧ (∀ e, 0 < c e) ∧
    ∀ i, (pathStrategies ends (embed (s i)) (embed (t i))).Nonempty

/-- The network-design game on a host realization of the labelled demand multigraph. -/
noncomputable def demandHostGame (s t : ι → T) {nV nE : ℕ}
    (ends : Fin nE → Sym2 (Fin nV)) (c : Fin nE → ℝ) (embed : T → Fin nV) :=
  ndGame ends c (fun i ↦ embed (s i)) (fun i ↦ embed (t i))

/-- Every optimum on every feasible positive-cost host is an `α`-approximate equilibrium. -/
def UniversalOptimumApprox (s t : ι → T) (α : ℝ) : Prop :=
  ∀ (nV nE : ℕ) (ends : Fin nE → Sym2 (Fin nV)) (c : Fin nE → ℝ)
    (embed : T → Fin nV) (O : ι → Finset (Fin nE)),
      IsFeasibleHost s t ends c embed →
      IsSocialOptimum (demandHostGame s t ends c embed) c O →
      IsApproxEquilibrium (demandHostGame s t ends c embed) α O

/-- Every optimum is a weak equilibrium on every feasible host. -/
def UniversalOptimumEquilibrium (s t : ι → T) : Prop :=
  ∀ (nV nE : ℕ) (ends : Fin nE → Sym2 (Fin nV)) (c : Fin nE → ℝ)
    (embed : T → Fin nV) (O : ι → Finset (Fin nE)),
      IsFeasibleHost s t ends c embed →
      IsSocialOptimum (demandHostGame s t ends c embed) c O →
      IsPureNash (demandHostGame s t ends c embed) O

/-- Every feasible host has ordinary price of stability exactly one. -/
def UniversalPoSOne (s t : ι → T) : Prop :=
  ∀ (nV nE : ℕ) (ends : Fin nE → Sym2 (Fin nV)) (c : Fin nE → ℝ)
    (embed : T → Fin nV), IsFeasibleHost s t ends c embed →
      OrdinaryPoSValue (demandHostGame s t ends c embed) c 1

/-- Every optimum is strict on every feasible host. -/
def UniversalOptimumStrict (s t : ι → T) : Prop :=
  ∀ (nV nE : ℕ) (ends : Fin nE → Sym2 (Fin nV)) (c : Fin nE → ℝ)
    (embed : T → Fin nV) (O : ι → Finset (Fin nE)),
      IsFeasibleHost s t ends c embed →
      IsSocialOptimum (demandHostGame s t ends c embed) c O →
      IsStrictEquilibrium (demandHostGame s t ends c embed) O

/-- Terminals after replacing every labelled player by `k` independently labelled copies. -/
def replicatedSource (s : ι → T) {k : ℕ} : ι × Fin k → T := fun p ↦ s p.1
def replicatedTarget (t : ι → T) {k : ℕ} : ι × Fin k → T := fun p ↦ t p.1

/-- `n` is the exact positive replication threshold for universal price of stability one. -/
def IsExactWeakReplicationThreshold (s t : ι → T) (n : ℕ) : Prop :=
  1 ≤ n ∧ UniversalPoSOne (replicatedSource s (k := n)) (replicatedTarget t (k := n)) ∧
    ∀ k : ℕ, 1 ≤ k →
      UniversalPoSOne (replicatedSource s (k := k)) (replicatedTarget t (k := k)) → n ≤ k

end PoSUndirected.Supplement


