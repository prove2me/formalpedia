-- Prove2me | Definitions.Def_ListHadwiger
-- name    : ListHadwiger
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:17.484006+00:00
-- url     : https://prove2.me/theorems/7d12ec5d-f460-44db-8d32-649bc3a2fc71
-- statement:
--   A graph G on a vertex type V is list-colorable from an assignment L giving each vertex a finite set of allowed colors if there is a coloring c with c(v) in L(v) for every vertex v and c(v) different from c(w) whenever v and w are adjacent. G is k-choosable if, for every color type and every assignment of lists each of size at least k, G is list-colorable; listChromaticNumber(G) is the least such k, taken as an infimum in the natural numbers (so it is 0 if the set of choosable k were empty). HasCliqueMinor(G,t) means there are t pairwise disjoint vertex sets B_i, indexed by Fin t, each inducing a connected subgraph of G, such that any two distinct sets contain adjacent vertices, i.e. G has a K_t minor. hadwigerNumber(G) is the supremum in the natural numbers of all t for which G has a K_t minor (which is 0 if that set is unbounded, as can happen for infinite graphs). MainStatement is a defined proposition, not an established theorem: it asserts that there is a constant C with 1 ≤ C such that for every finite nonempty vertex type V and every simple graph G on V, listChromaticNumber(G) ≤ C · hadwigerNumber(G). This is a linear list-coloring version of Hadwiger's conjecture.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ListHadwiger.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ListHadwiger.lean; bytes 16..1068
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace LinearListHadwiger

def ListColorable {V : Type} (G : SimpleGraph V) {Color : Type}
    (L : V → Finset Color) : Prop :=
  ∃ c : V → Color, (∀ v, c v ∈ L v) ∧ ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w

def Choosable {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (Color : Type) (L : V → Finset Color), (∀ v, k ≤ (L v).card) → ListColorable G L

noncomputable def listChromaticNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | Choosable G k}

def HasCliqueMinor {V : Type} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ B : Fin t → Set V,
    (∀ i, (G.induce (B i)).Connected) ∧
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w)

noncomputable def hadwigerNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sSup {t : ℕ | HasCliqueMinor G t}

def MainStatement : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
    listChromaticNumber G ≤ C * hadwigerNumber G



end LinearListHadwiger
end OAI


