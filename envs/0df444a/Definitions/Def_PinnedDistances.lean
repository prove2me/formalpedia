-- Prove2me | Definitions.Def_PinnedDistances
-- name    : PinnedDistances
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:38.892515+00:00
-- url     : https://prove2.me/theorems/bb44865c-7a38-4db3-a122-5b770e4e4dc8
-- statement:
--   Inside the namespace WeakPinned, Plane is the Euclidean plane ℝ². For a finite set P of plane points and points x, y, distanceFiber(P,x,y) is the set of points z of P other than x whose distance from x equals dist(y,x); that is, the points of P on the circle centered at x through y, excluding x itself. The number k(P,x,y) is the cardinality of this set. For a real exponent s, richPairs(P,s) is the set of ordered pairs (x,y) in P×P with x≠y such that k(P,x,y) ≥ |P|^s, so the circle around x through y contains at least |P|^s points of P other than x. The quantity pairFraction(P,s) is the number of such rich pairs divided by |P|(|P|−1). Finally, F(n,s) is defined as 0 when n<2, and for n≥2 as the supremum, over all n-point subsets P of the plane, of pairFraction(P,s). These are definitions only, with no theorem asserted about the value or growth of F.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PinnedDistances.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PinnedDistances.lean; bytes 16..783
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace WeakPinned
abbrev Plane := EuclideanSpace ℝ (Fin 2)

def distanceFiber (P : Finset Plane) (x y : Plane) : Finset Plane :=
  (P.erase x).filter (fun z => dist z x = dist y x)

def k (P : Finset Plane) (x y : Plane) : ℕ :=
  (distanceFiber P x y).card

def richPairs (P : Finset Plane) (s : ℝ) : Finset (Plane × Plane) :=
  (P ×ˢ P).filter (fun xy => xy.1 ≠ xy.2 ∧
    (P.card : ℝ) ^ s ≤ (k P xy.1 xy.2 : ℝ))

def pairFraction (P : Finset Plane) (s : ℝ) : ℝ :=
  (richPairs P s).card / ((P.card : ℝ) * ((P.card : ℝ) - 1))

def F (n : ℕ) (s : ℝ) : ℝ :=
  if 2 ≤ n then sSup {a : ℝ | ∃ P : Finset Plane, P.card = n ∧ a = pairFraction P s}
  else 0



end WeakPinned
end
end OAI


