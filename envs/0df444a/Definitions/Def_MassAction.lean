-- Prove2me | Definitions.Def_MassAction
-- name    : MassAction
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:18.134401+00:00
-- url     : https://prove2.me/theorems/642b6d64-c68e-4cec-887e-9b0c4b1e4f9f
-- statement:
--   A ReactionNetwork(d) over d species consists of a finite set of complexes, which are vectors in ℕ^d of species counts, and a finite set of reactions, which are ordered pairs (y,z) of complexes. Both the source and the target of every reaction must lie in the set of complexes, and no reaction may have equal source and target. HasReaction(N,y,z) says (y,z) is a reaction, and Reaction(N) is the subtype of reactions in N. WeaklyReversible(N) means that for every reaction y→z there is a chain of one or more reactions leading from z back to y, using the transitive closure of HasReaction. The monomial of a real vector x at y∈ℕ^d is the product over i of x_i^{y_i}. Given positive or arbitrary real rate constants κ indexed by reactions (no sign condition is imposed on κ), massAction(N,κ,x) is the vector field whose ith component is the sum over reactions e=(y,z) of κ_e times the monomial of x at y times (z_i − y_i), the mass-action rate law. PositiveState(x) means every coordinate of x is strictly positive. IsGlobalForwardSolution(N,κ,x0,x) means that x:ℝ→ℝ^d starts at x(0)=x0 and, for every real t≥0, x has derivative massAction(N,κ,x(t)) at t. Here the derivative at t=0 is taken in the two-sided sense, and no positivity of x or of κ is part of this definition.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MassAction.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MassAction.lean; bytes 16..1432
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

namespace Problem326

structure ReactionNetwork (d : ℕ) where
  complexes : Finset (Fin d → ℕ)
  reactions : Finset ((Fin d → ℕ) × (Fin d → ℕ))
  source_mem : ∀ e ∈ reactions, e.1 ∈ complexes
  target_mem : ∀ e ∈ reactions, e.2 ∈ complexes
  source_ne_target : ∀ e ∈ reactions, e.1 ≠ e.2

abbrev Reaction {d : ℕ} (N : ReactionNetwork d) :=
  {e : (Fin d → ℕ) × (Fin d → ℕ) // e ∈ N.reactions}

def HasReaction {d : ℕ} (N : ReactionNetwork d)
    (y z : Fin d → ℕ) : Prop :=
  (y, z) ∈ N.reactions

def WeaklyReversible {d : ℕ} (N : ReactionNetwork d) : Prop :=
  ∀ e : Reaction N,
    Relation.TransGen (HasReaction N) e.val.2 e.val.1

def monomial {d : ℕ} (x : Fin d → ℝ) (y : Fin d → ℕ) : ℝ :=
  Finset.univ.prod (fun i => x i ^ y i)

def massAction {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => Finset.univ.sum (fun e : Reaction N =>
    κ e * monomial x e.val.1 *
      ((e.val.2 i : ℝ) - (e.val.1 i : ℝ)))

def PositiveState {d : ℕ} (x : Fin d → ℝ) : Prop :=
  ∀ i, 0 < x i

def IsGlobalForwardSolution {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) (x0 : Fin d → ℝ)
    (x : ℝ → (Fin d → ℝ)) : Prop :=
  x 0 = x0 ∧
    ∀ t : ℝ, 0 ≤ t →
      HasDerivAt x (massAction N κ (x t)) t



end Problem326
end
end OAI


