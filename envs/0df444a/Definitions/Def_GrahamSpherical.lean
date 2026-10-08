-- Prove2me | Definitions.Def_GrahamSpherical
-- name    : GrahamSpherical
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:13.30598+00:00
-- url     : https://prove2.me/theorems/29f75b13-38f7-4013-ae7d-077a1c515592
-- statement:
--   The block works in the Euclidean plane (and in n-dimensional Euclidean space for colorings) and builds an explicit set of twelve points on the unit circle. The parameter t is the Liouville-type sum over m≥0 of 10^-((m+1)!), and u=(1−t²)/(1+t²), v=2t/(1+t²), so (u,v) is a unit vector, the cosine and sine of the angle 2·arctan t. The four square corners are (1,0), (−1,0), (0,1), (0,−1). Labels are pairs (i,q) with i in {0,1,2} and q in {0,1,2,3}; the vertex with label (0,q) is the q-th corner rotated by the angle with cosine u and sine v, label (1,q) is the corner rotated by the opposite angle, and label (2,q) is the corner itself. The witness is the set of these twelve vertices. AvoidsCopy(X, color) says that a coloring of n-space with r colors has no isometric copy of X lying in a single color class. EuclideanRamsey(X) is the defined proposition that for every positive number r of colors there is a positive dimension n such that every r-coloring of n-dimensional Euclidean space contains a monochromatic isometric copy of X. FullAuthoredResult is a defined proposition, not an established theorem, asserting that the witness has exactly 12 points, lies on the unit sphere centered at the origin, that for every positive dimension n some 50-coloring of n-space avoids every monochromatic isometric copy of the witness, and that the witness is not Euclidean Ramsey.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GrahamSpherical.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GrahamSpherical.lean; bytes 97..1679
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

noncomputable section

namespace GrahamSpherical

abbrev Point (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Label := Fin 3 × Fin 4

def parameter : ℝ := ∑' m : ℕ, 1 / (10 : ℝ) ^ ((m + 1).factorial)

def u : ℝ := (1 - parameter ^ 2) / (1 + parameter ^ 2)
def v : ℝ := (2 * parameter) / (1 + parameter ^ 2)

def squareCoordinate (q : Fin 4) : Fin 2 → ℝ :=
  if q = 0 then ![1, 0] else
  if q = 1 then ![-1, 0] else
  if q = 2 then ![0, 1] else ![0, -1]

def coordinates (i : Label) : Fin 2 → ℝ :=
  let q := squareCoordinate i.2
  if i.1 = 0 then ![u * q 0 - v * q 1, v * q 0 + u * q 1] else
  if i.1 = 1 then ![u * q 0 + v * q 1, -v * q 0 + u * q 1] else q

def vertex (i : Label) : Point 2 := WithLp.toLp 2 (coordinates i)

def witness : Set (Point 2) := Set.range vertex

def AvoidsCopy {d n r : ℕ} (X : Set (Point d)) (color : Point n → Fin r) : Prop :=
  ¬ ∃ f : X → Point n, Isometry f ∧ ∃ c : Fin r, ∀ x, color (f x) = c

def EuclideanRamsey {d : ℕ} (X : Set (Point d)) : Prop :=
  ∀ r : ℕ, 0 < r → ∃ n : ℕ, 0 < n ∧
    ∀ color : Point n → Fin r,
      ∃ f : X → Point n, Isometry f ∧ ∃ c : Fin r, ∀ x, color (f x) = c

end GrahamSpherical

end

namespace GrahamSpherical.Specification

def FullAuthoredResult : Prop :=
  witness.ncard = 12 ∧
  witness ⊆ Metric.sphere (0 : Point 2) 1 ∧
  (∀ n : ℕ, 0 < n → ∃ color : Point n → Fin 50, AvoidsCopy witness color) ∧
  ¬ EuclideanRamsey witness

end GrahamSpherical.Specification

noncomputable section

namespace GrahamSpherical



end GrahamSpherical
end
end OAI


