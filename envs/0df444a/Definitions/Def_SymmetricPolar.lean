-- Prove2me | Definitions.Def_SymmetricPolar
-- name    : SymmetricPolar
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:28.305005+00:00
-- url     : https://prove2.me/theorems/8baa3748-2e8d-413d-8c0b-9b8ac5e1acea
-- statement:
--   Position(n) is n-dimensional real Euclidean space and Phase(n) is the product Position(n)×Position(n), whose points are pairs (q,p). IsSymmetricConvexBody(K) means that K ⊆ Position(n) is compact, convex, has nonempty interior, and satisfies x∈K if and only if −x∈K. The polar of K is the set of p such that the inner product ⟨q,p⟩ ≤ 1 for every q∈K. polarProduct(K) is the product of the interior of K with the interior of the polar of K, as a subset of Phase(n). capacityBall(n,c) is the open set of (q,p) in Phase(n) with π(‖q‖²+‖p‖²) < c. The bilinear form omega0(v,w) = ⟨v.1,w.2⟩ − ⟨w.1,v.2⟩ is the standard antisymmetric pairing on Phase(n). HasSymplecticEmbedding(U,V) says there is a map e from Phase(n) to itself that is infinitely differentiable on U, restricts to a topological embedding of U, sends U into V, and at every z∈U has Fréchet derivative preserving omega0, meaning omega0(De(z)v, De(z)w) = omega0(v,w) for all v and w. gromovWidth(U) is, as an extended nonnegative real, the supremum of those c>0 for which capacityBall(n,c) admits a symplectic embedding into U in this sense, and it is zero if no such c exists. These are definitions only; no theorem about the Gromov width of polarProduct(K) is asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SymmetricPolar.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SymmetricPolar.lean; bytes 16..1294
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open Set
open scoped ContDiff ENNReal

namespace SymmetricPolar

abbrev Position (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Phase (n : ℕ) := Position n × Position n

def IsSymmetricConvexBody {n : ℕ} (K : Set (Position n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧
    ∀ x, x ∈ K ↔ -x ∈ K

def polar {n : ℕ} (K : Set (Position n)) : Set (Position n) :=
  {p | ∀ q ∈ K, inner (𝕜 := ℝ) q p ≤ 1}

def polarProduct {n : ℕ} (K : Set (Position n)) : Set (Phase n) :=
  interior K ×ˢ interior (polar K)

def capacityBall (n : ℕ) (c : ℝ) : Set (Phase n) :=
  {z | Real.pi * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) < c}

noncomputable def omega0 {n : ℕ} (v w : Phase n) : ℝ :=
  inner (𝕜 := ℝ) v.1 w.2 - inner (𝕜 := ℝ) w.1 v.2

def HasSymplecticEmbedding {n : ℕ} (U V : Set (Phase n)) : Prop :=
  ∃ e : Phase n → Phase n,
    ContDiffOn ℝ ∞ e U ∧
    Topology.IsEmbedding (fun z : U => e z) ∧
    MapsTo e U V ∧
    ∀ z ∈ U, ∀ v w : Phase n,
      omega0 (fderiv ℝ e z v) (fderiv ℝ e z w) = omega0 v w

noncomputable def gromovWidth {n : ℕ} (U : Set (Phase n)) : ℝ≥0∞ :=
  sSup (ENNReal.ofReal '' {c : ℝ | 0 < c ∧ HasSymplecticEmbedding (capacityBall n c) U})



end SymmetricPolar
end OAI


