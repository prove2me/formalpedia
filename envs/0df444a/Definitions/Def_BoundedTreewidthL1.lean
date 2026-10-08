-- Prove2me | Definitions.Def_BoundedTreewidthL1
-- name    : BoundedTreewidthL1
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:02.580057+00:00
-- url     : https://prove2.me/theorems/701dc113-0503-4d55-ac93-51930bf7a4ce
-- statement:
--   For a simple graph G with real edge lengths ℓ, the length of a walk is the sum of its edge lengths, with the empty walk having length zero. The shortest-path distance between vertices u and v is defined as the real infimum of the lengths of all paths from u to v; these definitions alone do not assume positive lengths or connectivity. A tree decomposition with parameter k consists of a finite tree and a finite set of graph vertices, called a bag, at each tree vertex: every graph vertex belongs to a bag, the endpoints of every graph edge occur together in some bag, the tree vertices whose bags contain any fixed graph vertex induce a connected graph, and every bag has at most k vertices. An ℓ₁ embedding with bound C is a map F into some finite-dimensional real ℓ₁ space such that d(u,v) ≤ ‖F(u)−F(v)‖₁ ≤ C d(u,v) for every pair of vertices, where d is the defined shortest-path distance. MainStatement is the proposition that, for every integer k ≥ 2, there is a real C ≥ 1 such that every finite, nonempty, connected simple graph admitting this tree decomposition, with any assignment of strictly positive real edge lengths, has such an ℓ₁ embedding. The constant C depends only on k, while the target dimension and map may depend on the graph and its lengths.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BoundedTreewidthL1.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BoundedTreewidthL1.lean; bytes 16..1562
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

namespace BoundedTreewidthL1

universe u_1

variable {V : Type u_1} (G : SimpleGraph V)

/-- Sum of the given positive real edge lengths along a graph walk. -/
def walkLength (ℓ : G.edgeSet → ℝ) : {u v : V} → G.Walk u v → ℝ
  | _, _, .nil => 0
  | u, _, .cons (v := v) h p => ℓ ⟨s(u, v), h⟩ + walkLength ℓ p

noncomputable def shortestPathDistance (ℓ : G.edgeSet → ℝ) (u v : V) : ℝ :=
  sInf {r : ℝ | ∃ p : G.Walk u v, p.IsPath ∧ walkLength G ℓ p = r}

def HasTreeDecomposition [DecidableEq V] (k : ℕ) : Prop :=
  ∃ n : ℕ, ∃ T : SimpleGraph (Fin n), ∃ bag : Fin n → Finset V,
    T.IsTree ∧
    (∀ v : V, ∃ t, v ∈ bag t) ∧
    (∀ u v : V, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
    (∀ v : V, (T.induce {t | v ∈ bag t}).Connected) ∧
    (∀ t, (bag t).card ≤ k)

/-- A map to genuine finite-dimensional real ℓ₁, not just a cut pseudometric. -/
def HasL1Embedding (ℓ : G.edgeSet → ℝ) (C : ℝ) : Prop :=
  ∃ m : ℕ, ∃ F : V → PiLp (1 : ENNReal) (fun _ : Fin m => ℝ),
    ∀ u v : V,
      shortestPathDistance G ℓ u v ≤ ‖F u - F v‖ ∧
      ‖F u - F v‖ ≤ C * shortestPathDistance G ℓ u v

def MainStatement : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
      (G : SimpleGraph V),
      G.Connected → HasTreeDecomposition G k →
      ∀ ℓ : G.edgeSet → ℝ, (∀ e, 0 < ℓ e) → HasL1Embedding G ℓ C



end BoundedTreewidthL1
end
end OAI


