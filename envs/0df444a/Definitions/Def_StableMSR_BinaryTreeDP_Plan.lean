-- Prove2me | Definitions.Def_StableMSR_BinaryTreeDP_Plan
-- name    : StableMSR_BinaryTreeDP_Plan
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-14T02:23:27.778277+00:00
-- url     : https://prove2.me/theorems/5833741a-d67a-4dc2-9bba-40d64f16913f
-- title:
--   Finite binary bag plans and their local accounting
-- statement:
--   A bag record contains a finite scope, finite assignment choices, a validity predicate, and nonnegative-integer count and real objective contributions. A binary plan is a finite tree of such records. Its coherence conditions express the running-intersection consequences needed for gluing. Locality, global validity, aggregate count and cost, node count, and uniform bag-record predicates are defined. These are finite semantic data structures, not an implementation or a running-time guarantee.
-- source:
--   Stable sum-of-radii clustering recovery formalization, local tree-decomposition dynamic programming and binary-plan representation.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
namespace StableMSR.Recovery.TreeDP
def AgreeOn {V X : Type*} (S : Finset V) (a b : V → X) : Prop :=
  ∀ v ∈ S, a v = b v

structure BagData (V X : Type*) where
  bag : Finset V
  choices : Finset (V → X)
  valid : (V → X) → Prop
  count : (V → X) → ℕ
  weight : (V → X) → ℝ

/-- A binary rooted execution representation. Higher fanout uses duplicate bags with
zero contributions; the transformation to this representation is a separate operation. -/
inductive Plan (V X : Type*) where
  | leaf (data : BagData V X)
  | branch (data : BagData V X) (left right : Plan V X)

def Plan.root {V X : Type*} : Plan V X → BagData V X
  | .leaf d => d
  | .branch d _ _ => d

def Plan.scope {V X : Type*} [DecidableEq V] : Plan V X → Finset V
  | .leaf d => d.bag
  | .branch d L R => d.bag ∪ L.scope ∪ R.scope

/-- Local separator consequences of running intersection for the rooted representation. -/
def Plan.Coherent {V X : Type*} [DecidableEq V] : Plan V X → Prop
  | .leaf _ => True
  | .branch d L R => L.Coherent ∧ R.Coherent ∧
      L.scope ∩ d.bag ⊆ L.root.bag ∧ R.scope ∩ d.bag ⊆ R.root.bag ∧
      L.scope ∩ R.scope ⊆ d.bag

def BagData.Local {V X : Type*} (d : BagData V X) : Prop :=
  ∀ a b, AgreeOn d.bag a b →
    (d.valid a ↔ d.valid b) ∧ d.count a = d.count b ∧ d.weight a = d.weight b

def Plan.Local {V X : Type*} : Plan V X → Prop
  | .leaf d => d.Local
  | .branch d L R => d.Local ∧ L.Local ∧ R.Local

def Plan.AllValid {V X : Type*} (whole : V → X) : Plan V X → Prop
  | .leaf d => d.valid whole
  | .branch d L R => d.valid whole ∧ L.AllValid whole ∧ R.AllValid whole

def Plan.totalCount {V X : Type*} (whole : V → X) : Plan V X → ℕ
  | .leaf d => d.count whole
  | .branch d L R => d.count whole + L.totalCount whole + R.totalCount whole

def Plan.totalWeight {V X : Type*} (whole : V → X) : Plan V X → ℝ
  | .leaf d => d.weight whole
  | .branch d L R => d.weight whole + L.totalWeight whole + R.totalWeight whole

def Plan.nodes {V X : Type*} : Plan V X → ℕ
  | .leaf _ => 1
  | .branch _ L R => 1 + L.nodes + R.nodes
def Plan.AllData {V X : Type*} (P : BagData V X → Prop) : Plan V X → Prop
  | .leaf d => P d
  | .branch d L R => P d ∧ L.AllData P ∧ R.AllData P
end StableMSR.Recovery.TreeDP


