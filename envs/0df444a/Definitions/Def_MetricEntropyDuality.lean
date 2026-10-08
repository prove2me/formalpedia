-- Prove2me | Definitions.Def_MetricEntropyDuality
-- name    : MetricEntropyDuality
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:19.107457+00:00
-- url     : https://prove2.me/theorems/bf6a59c6-3b32-4bf1-8d02-bd3f4e101def
-- statement:
--   Over a finite index type ι, RealSpace(ι) is the space of real vectors indexed by ι, with pairing(x,y) the standard inner product ∑ᵢ xᵢyᵢ. The cube is the set of vectors all of whose coordinates have absolute value at most 1, and polar(K) is the set of y with pairing(x,y) ≤ 1 for every x in K. For sets A and B and a list of M centers c₁,…,c_M, Covers(A,B,centers) means every x in A has some center cⱼ with x − cⱼ in B, that is, A is covered by M translates of B. Coverable(A,B) says that some finite number of centers achieves this, and coveringNumber(A,B) is the least such M (the infimum over admissible M, which is 0 by the natural-number convention if no finite cover exists). Finally, IsSymmetricConvexBody(K) is a structure whose fields assume that K is compact, convex, symmetric under x ↦ −x, and has nonempty interior. The block only sets up these definitions of duality and covering numbers and states no theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MetricEntropyDuality.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MetricEntropyDuality.lean; bytes 176..1327
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Order.Lattice.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

universe u

noncomputable section

namespace MetricEntropyDuality

open Filter Topology
open scoped BigOperators Pointwise

abbrev RealSpace (ι : Type u) := ι → ℝ

def pairing {ι : Type u} [Fintype ι] (x y : RealSpace ι) : ℝ :=
  ∑ i, x i * y i

def cube (ι : Type u) : Set (RealSpace ι) :=
  {x | ∀ i, |x i| ≤ 1}

def polar {ι : Type u} [Fintype ι] (K : Set (RealSpace ι)) : Set (RealSpace ι) :=
  {y | ∀ x ∈ K, pairing x y ≤ 1}

def Covers {ι : Type u} {M : ℕ} (A B : Set (RealSpace ι))
    (centers : Fin M → RealSpace ι) : Prop :=
  ∀ x ∈ A, ∃ j, x - centers j ∈ B

def Coverable {ι : Type u} (A B : Set (RealSpace ι)) : Prop :=
  ∃ M : ℕ, ∃ centers : Fin M → RealSpace ι, Covers A B centers

def coveringNumber {ι : Type u} (A B : Set (RealSpace ι)) : ℕ :=
  sInf {M : ℕ | ∃ centers : Fin M → RealSpace ι, Covers A B centers}

structure IsSymmetricConvexBody {ι : Type u} [Fintype ι]
    (K : Set (RealSpace ι)) : Prop where
  isCompact : IsCompact K
  convex : Convex ℝ K
  symmetric : ∀ x, x ∈ K ↔ -x ∈ K
  interior_nonempty : (interior K).Nonempty



end MetricEntropyDuality
end
end OAI


