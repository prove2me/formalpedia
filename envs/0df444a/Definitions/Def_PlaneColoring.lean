-- Prove2me | Definitions.Def_PlaneColoring
-- name    : PlaneColoring
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:06.693632+00:00
-- url     : https://prove2.me/theorems/e903c939-d016-4f5c-9f3e-a66057abf76e
-- statement:
--   Plane is the Euclidean plane ℝ², realized as EuclideanSpace ℝ (Fin 2). For a natural number k, ProperColoring(k) is the proposition that there exists a function c from the plane to Fin k, that is, a coloring of every point of the plane with one of k colors, such that any two points at Euclidean distance exactly 1 receive different colors. This is only a defined proposition, stated for an arbitrary k, with no particular value of k asserted and no claim that such a coloring exists or fails to exist. Since the color set is Fin k, the case k = 0 is impossible because the plane is nonempty.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PlaneColoring.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PlaneColoring.lean; bytes 16..237
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

namespace Problem160

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def ProperColoring (k : ℕ) : Prop :=
  ∃ c : Plane → Fin k,
    ∀ x y : Plane, dist x y = 1 → c x ≠ c y



end Problem160
end
end OAI


