-- Prove2me | Definitions.Def_IntervalMaxCutEPTAS_Scheme_Supplement_Classes
-- name    : IntervalMaxCutEPTAS_Scheme_Supplement_Classes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:29:40.015519+00:00
-- url     : https://prove2.me/theorems/4a53a379-be72-48a3-8aff-db3c78567efa
-- title:
--   Perfect elimination orders and the split-plus-degree-two class
-- statement:
--   A perfect elimination order lists every vertex exactly once and makes every vertex's later neighbors a clique. Split graphs use the published clique-and-independent-set partition. The restricted class in Theorem 1.3 admits an independent set $D$ such that the graph induced by its complement is split and
--
--   $$\forall x\in D,\ \exists u\ne v\notin D:\quad N(x)=\{u,v\},\quad uv\in E.$$
--
--   Thus each added vertex has exactly two adjacent neighbors in the original split graph. The empty added set and empty graph are allowed. Chordality uses the published absence-of-chordless-cycles definition, independently of the PEO predicate. No partition, elimination order or optimum is part of an approximation algorithm's input.
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), §3 and §7.2, PDF p. 26 (printed p. 25)

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting
import Definitions.Def_BrouwerLaplacian_IsSplitWith

set_option autoImplicit false

namespace IntervalMaxCutEPTAS.Scheme.Supplement

/-- A genuine ordering: every vertex occurs exactly once; later neighbors form a clique. -/
def IsPEO {V : Type} [DecidableEq V] (G : SimpleGraph V) (xs : List V) : Prop :=
  xs.Nodup ∧ (∀ v, v ∈ xs) ∧
    ∀ v a b, G.Adj v a → G.Adj v b → xs.idxOf v < xs.idxOf a →
      xs.idxOf v < xs.idxOf b → a ≠ b → G.Adj a b

/-- Existential closure of the published split partition, with no nonemptiness condition. -/
def IsSplit {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ K : Finset V, BrouwerLaplacian.IsSplitWith G K

/-- Exactly the source subclass: adding an independent set of simplicial degree-two vertices
to an arbitrary split graph. Neither a split partition nor a PEO is supplied to an algorithm. -/
def SplitPlusTwo {V : Type} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ D : Finset V,
    G.IsIndepSet (D : Set V) ∧
    IsSplit (G.induce {v | v ∉ D}) ∧
    ∀ x ∈ D, ∃ u v, u ∉ D ∧ v ∉ D ∧ u ≠ v ∧ G.Adj u v ∧
      ∀ y, G.Adj x y ↔ y = u ∨ y = v

end IntervalMaxCutEPTAS.Scheme.Supplement


