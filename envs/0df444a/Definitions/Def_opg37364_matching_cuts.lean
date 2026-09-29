-- Prove2me | Definitions.Def_opg37364_matching_cuts
-- name    : opg37364_matching_cuts
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-08T04:51:16.7073+00:00
-- url     : https://prove2.me/theorems/ab3f2eb8-d49e-4e0f-ba12-2055a9430b33
-- title:
--   Matching cuts and immune high-girth graph packages
-- statement:
--   This module fixes finite simple-graph conventions for the cited paper. A matching cut is determined by a nonempty proper vertex shore and requires every vertex to have at most one neighbor across the resulting bipartition. An immune graph has no such cut.
--
--   A simple cycle is a cyclic list of at least three distinct vertices. Girth at least $g$ means every simple cycle has length at least $g$, with forests satisfying every threshold. Connectedness uses nonempty graph reachability, bipartiteness uses a Boolean side assignment, and exact regularity counts each neighbor set.
--
--   A perfect matching is represented by an adjacent involution on vertices. The combined package requires connectedness, bipartiteness, degree fourteen, the girth bound, absence of matching cuts, and a perfect matching.
-- source:
--   Feghali--Lucke--Paulusma--Ries, Matching Cuts in Graphs of High Girth and H-Free Graphs, Algorithmica 87 (2025), 1199-1221, https://doi.org/10.1007/s00453-025-01318-8, Section 2 and Lemma 5

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Card

namespace OPG37364

universe u

/-- A simple cycle encoded by a cyclic list of distinct vertices. -/
def IsCycleList {V : Type u} (G : SimpleGraph V) (vs : List V) : Prop :=
  ∃ x y : V, ∃ middle : List V,
    vs = x :: (middle ++ [y]) ∧ 3 ≤ vs.length ∧
    vs.Nodup ∧ vs.Chain' G.Adj ∧ G.Adj y x

/-- Every simple cycle has length at least `g`; forests satisfy this for every
`g`. -/
def HasGirthAtLeast {V : Type u} (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ vs : List V, IsCycleList G vs → g ≤ vs.length

/-- Boolean bipartiteness witness. -/
def IsBipartite {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ side : V → Bool, ∀ ⦃u v : V⦄, G.Adj u v → side u ≠ side v

/-- Nonempty connectedness under graph reachability. -/
def IsConnected {V : Type u} (G : SimpleGraph V) : Prop :=
  Nonempty V ∧ ∀ u v : V, Relation.ReflTransGen G.Adj u v

/-- A nontrivial shore `A` defines a matching cut when every vertex has at
most one neighbor across the cut. -/
def IsMatchingCut {V : Type u} (G : SimpleGraph V) (A : Set V) : Prop :=
  A.Nonempty ∧ Aᶜ.Nonempty ∧
  ∀ ⦃v x y : V⦄,
    G.Adj v x → ((v ∈ A ∧ x ∉ A) ∨ (v ∉ A ∧ x ∈ A)) →
    G.Adj v y → ((v ∈ A ∧ y ∉ A) ∨ (v ∉ A ∧ y ∈ A)) → x = y

def HasMatchingCut {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ A : Set V, IsMatchingCut G A

/-- Every vertex has exactly `d` neighbors. -/
def IsRegularOfDegree {V : Type u} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ v : V, (G.neighborSet v).encard = d

/-- A perfect matching represented by a fixed-point-free adjacent involution.
Fixed-point-freeness follows from looplessness and adjacency. -/
def HasPerfectMatching {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ mate : V → V,
    (∀ v : V, G.Adj v (mate v)) ∧ Function.Involutive mate

/-- The graph package asserted by Lemma 5 of Feghali--Lucke--Paulusma--Ries. -/
def IsImmuneHighGirthPackage {V : Type u} (G : SimpleGraph V) (g : ℕ) : Prop :=
  IsConnected G ∧ IsBipartite G ∧ IsRegularOfDegree G 14 ∧
  HasGirthAtLeast G g ∧ ¬ HasMatchingCut G ∧ HasPerfectMatching G

end OPG37364


