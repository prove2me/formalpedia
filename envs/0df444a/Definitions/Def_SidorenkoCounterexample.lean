-- Prove2me | Definitions.Def_SidorenkoCounterexample
-- name    : SidorenkoCounterexample
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:21.190353+00:00
-- url     : https://prove2.me/theorems/f654b43e-4f4d-49c8-a685-2bdf6075799c
-- statement:
--   A pattern graph H is built as the bipartite incidence graph between 13 points and 22 faces, where each face is a specific 3-element subset of the 13 points given by an explicit table (for example face 0 is {0,1,3} and face 21 is {8,9,12}); the vertex type is the disjoint sum of the 13 points and the 22 faces, a point and a face are adjacent exactly when the point lies in the face, and no other pairs are adjacent, with symmetry and looplessness verified. For general simple graphs F on V and G on W, homCount(F,G) is the number of maps V→W sending every edge of F to an edge of G, counting noninjective maps as well. homDensity(F,G) is this count divided by |W|^|V|, and edgeDensity(G) is 2·(number of edges of G) divided by |W|^2. The file contains only these definitions, setting up the finite pattern H for a counterexample to Sidorenko's conjecture, which compares homomorphism density of H with a power of edge density; no inequality or counterexample claim is itself stated or proved.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SidorenkoCounterexample.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SidorenkoCounterexample.lean; bytes 16..1459
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-! # A finite counterexample to Sidorenko's conjecture

The pattern is the incidence graph of the 22 triples in Table 1 of the source.
Homomorphism density counts all edge-preserving maps, including noninjective maps.
-/

namespace SidorenkoCounterexample

def faces : Fin 22 → Finset (Fin 13) := ![
  {0,1,3}, {0,1,9}, {0,2,3}, {0,2,9}, {1,3,10}, {1,7,10},
  {1,7,12}, {1,9,12}, {2,3,4}, {2,4,9}, {3,4,11}, {3,10,11},
  {4,8,9}, {4,8,11}, {5,6,7}, {5,6,11}, {5,7,10}, {5,10,11},
  {6,7,12}, {6,8,11}, {6,8,12}, {8,9,12}]

abbrev PatternVertex := Fin 13 ⊕ Fin 22

def incidence : PatternVertex → PatternVertex → Prop
  | .inl point, .inr face => point ∈ faces face
  | .inr face, .inl point => point ∈ faces face
  | _, _ => False

def H : SimpleGraph PatternVertex where
  Adj := incidence
  symm.symm := by intro left right; cases left <;> cases right <;> simp [incidence]
  loopless.irrefl := by intro vertex; cases vertex <;> simp [incidence]

noncomputable def homCount {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W) : ℕ :=
  Nat.card {hom : V → W // ∀ left right, F.Adj left right → G.Adj (hom left) (hom right)}

noncomputable def homDensity {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W) : ℝ :=
  (homCount F G : ℝ) / (Nat.card W : ℝ) ^ Nat.card V

noncomputable def edgeDensity {W : Type*} (G : SimpleGraph W) : ℝ :=
  2 * (Nat.card G.edgeSet : ℝ) / (Nat.card W : ℝ) ^ 2



end SidorenkoCounterexample
end OAI


