-- Prove2me | Definitions.Def_CayleyPercolation
-- name    : CayleyPercolation
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:03.609377+00:00
-- url     : https://prove2.me/theorems/aff080e0-3736-44d8-96e4-7f42611e34b0
-- statement:
--   A bond graph assigns each edge an unordered pair of vertices. For a set ω of open edges, two vertices are connected when a finite path of open edges joins them, allowing a path of length zero; the cluster of a vertex is the set of vertices connected to it, and infiniteClusters is the set of distinct infinite clusters. For p ∈ [0,1], law(p) is Bernoulli bond percolation, independently opening each edge with probability p. The critical value pc is the infimum of parameters with positive probability of an infinite cluster, while pu is the infimum of parameters for which exactly one infinite cluster exists with probability one. The two-point function τp(x,y) is the probability that x and y are connected. On the complex Hilbert space ℓ²(V), HasKernel means that a bounded linear operator A satisfies (Aδy)(x) = τp(x,y) for all vertices x,y, where δy is the unit vector at y. OperatorBounded asserts the existence of such an operator, and ptwo is the supremum of parameters for which it exists. A separate product measure assigns independent uniform labels in [0,1] to edges, with the edges whose labels are at most p declared open at parameter p. AmenableGroup is the defined proposition that, for every finite subset K of a group and every ε > 0, there is a nonempty finite set A such that |(Ag) ∖ A| < ε|A| for every g ∈ K. Given any finite subset S of a group, its Cayley edges are the unordered pairs {x,xs} with s ∈ S, and the Cayley bond graph assigns each such edge its pair of endpoints; S is not required here to be symmetric or generating.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CayleyPercolation.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CayleyPercolation.lean; bytes 16..2341
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-! Nonuniqueness of Bernoulli bond percolation on arbitrary Cayley graphs. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

abbrev BondGraph (V : Type u) (E : Type v) := E → Sym2 V

def Conn (G : BondGraph V E) (ω : Set E) (x y : V) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ e ∈ ω, G e = s(a, b)) x y

def cluster (G : BondGraph V E) (ω : Set E) (x : V) : Set V :=
  {y | Conn G ω x y}

def infiniteClusters (G : BondGraph V E) (ω : Set E) : Set (Set V) :=
  {C | C.Infinite ∧ ∃ x, C = cluster G ω x}

noncomputable def law (p : unitInterval) : Measure (Set E) :=
  setBernoulli Set.univ p

noncomputable def pc (G : BondGraph V E) : unitInterval :=
  sInf {p | 0 < law p {ω | (infiniteClusters G ω).Nonempty}}

noncomputable def pu (G : BondGraph V E) : unitInterval :=
  sInf {p | law p {ω | ∃! C, C ∈ infiniteClusters G ω} = 1}

noncomputable def twoPoint (G : BondGraph V E) (p : unitInterval) (x y : V) : ℝ :=
  (law p {ω | Conn G ω x y}).toReal

noncomputable abbrev Hilbert (V : Type u) := lp (fun _ : V => ℂ) 2

noncomputable def HasKernel [DecidableEq V]
    (G : BondGraph V E) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V) : Prop :=
  ∀ x y, (A (lp.single 2 y (1 : ℂ))) x = (twoPoint G p x y : ℂ)

noncomputable def OperatorBounded (G : BondGraph V E) (p : unitInterval) : Prop := by
  classical
  exact ∃ A : Hilbert V →L[ℂ] Hilbert V, HasKernel G p A

noncomputable def ptwo (G : BondGraph V E) : unitInterval :=
  sSup {p | OperatorBounded G p}

noncomputable def labelLaw : Measure (E → unitInterval) :=
  Measure.infinitePi (fun _ => (volume : Measure unitInterval))

def openEdges (labels : E → unitInterval) (p : unitInterval) : Set E :=
  {e | labels e ≤ p}

noncomputable def AmenableGroup (Λ : Type u) [Group Λ] : Prop := by
  classical
  exact ∀ K : Finset Λ, ∀ ε : ℝ, 0 < ε → ∃ A : Finset Λ, A.Nonempty ∧
    ∀ g ∈ K, (((A.image (fun x => x * g)) \ A).card : ℝ) < ε * A.card

def CayleyEdge {Λ : Type u} [Group Λ] (S : Finset Λ) :=
  {e : Sym2 Λ // ∃ x : Λ, ∃ s ∈ S, e = s(x, x * s)}

def cayleyGraph {Λ : Type u} [Group Λ] (S : Finset Λ) :
    BondGraph Λ (CayleyEdge S) := Subtype.val



end Percolation
end OAI


