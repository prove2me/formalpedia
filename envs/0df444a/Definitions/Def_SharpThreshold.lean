-- Prove2me | Definitions.Def_SharpThreshold
-- name    : SharpThreshold
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:07.014675+00:00
-- url     : https://prove2.me/theorems/acbdd227-eb34-4e24-80d9-8d9bce4f5da8
-- statement:
--   For a vertex count n, a GraphEdge is a two-element subset of Fin n, and a GraphConfig is a Boolean assignment to all such edges, i.e. a labelled graph on n vertices recording which edges are present. permEdge applies a permutation π of the vertices to an edge, and permuteConfig π x is the configuration whose value at an edge e is x at the edge obtained by applying π⁻¹ to e. A Boolean function f on configurations is a VertexInvariant if f(permuteConfig π x) = f(x) for every vertex permutation π and configuration x. ConfigLE x y means every edge present in x is also present in y, and f is an IncreasingGraphProperty if f x = true and ConfigLE x y force f y = true. f is a NontrivialGraphProperty if it takes the value true at some configuration and false at some configuration. boolReal sends false to 0 and true to 1. For a real p, graphWeight p x is the product over all edges of p for present edges and 1 − p for absent edges, so on [0,1] it is the Erdős–Rényi G(n,p) probability of x. graphMean p f is the sum over all configurations x of graphWeight p x times boolReal(f x), the probability that f holds under that weighting. graphQuantile a f is the infimum of the set of p in [0,1] with graphMean p f ≥ a; as a real infimum, it equals 0 if that set is empty. The block only makes these definitions and states no theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SharpThreshold.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SharpThreshold.lean; bytes 16..1535
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

namespace Problem313

abbrev GraphEdge (n : ℕ) := {e : Finset (Fin n) // e.card = 2}

abbrev GraphConfig (n : ℕ) := GraphEdge n → Bool

def permEdge {n : ℕ} (π : Equiv.Perm (Fin n)) (e : GraphEdge n) : GraphEdge n :=
  ⟨e.1.map π.toEmbedding, by simpa using e.2⟩

def permuteConfig {n : ℕ} (π : Equiv.Perm (Fin n))
    (x : GraphConfig n) : GraphConfig n :=
  fun e => x (permEdge π.symm e)

def VertexInvariant {n : ℕ} (f : GraphConfig n → Bool) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (x : GraphConfig n),
    f (permuteConfig π x) = f x

def ConfigLE {n : ℕ} (x y : GraphConfig n) : Prop :=
  ∀ e, x e = true → y e = true

def IncreasingGraphProperty {n : ℕ} (f : GraphConfig n → Bool) : Prop :=
  ∀ x y, ConfigLE x y → f x = true → f y = true

def NontrivialGraphProperty {n : ℕ} (f : GraphConfig n → Bool) : Prop :=
  (∃ x, f x = true) ∧ (∃ x, f x = false)

def boolReal (b : Bool) : ℝ :=
  match b with
  | false => 0
  | true => 1

def graphWeight {n : ℕ} (p : ℝ) (x : GraphConfig n) : ℝ := by
  classical
  exact Finset.univ.prod (fun e : GraphEdge n =>
    if x e = true then p else 1 - p)

def graphMean {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool) : ℝ := by
  classical
  exact Finset.univ.sum (fun x : GraphConfig n =>
    graphWeight p x * boolReal (f x))

def graphQuantile {n : ℕ} (a : ℝ) (f : GraphConfig n → Bool) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ graphMean p f ≥ a}



end Problem313
end
end OAI


