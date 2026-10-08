-- Prove2me | Definitions.Def_LogBrunnMinkowski
-- name    : LogBrunnMinkowski
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:17.688232+00:00
-- url     : https://prove2.me/theorems/fdb79973-dbf5-4622-b5a9-b9b359118981
-- statement:
--   In n-dimensional Euclidean space Space(n), a convex body is a compact convex set with nonempty interior, and a set K is origin symmetric if x lies in K exactly when −x does. The support function of a set K in direction u is support(K,u) = sup of ⟨x,u⟩ over x in K (a real-valued supremum, which is taken in ℝ and so defaults to 0 if the set is empty or unbounded above). For a real function f on the space, wulff(f) is the Wulff shape: the set of points x such that ⟨x,u⟩ ≤ f(u) for every unit vector u. For sets K and L and a real parameter t, logCombination(K,L,t) is the logarithmic combination, defined as the Wulff shape of the function u ↦ support(K,u)^(1−t) · support(L,u)^t, a geometric interpolation of the two support functions using real powers. These are definitions only; no log-Brunn–Minkowski inequality or other result is stated, and the convex-body and symmetry predicates are not built into the combination itself.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/LogBrunnMinkowski.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/LogBrunnMinkowski.lean; bytes 16..785
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped ENNReal InnerProductSpace

namespace LogBrunnMinkowski

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def IsConvexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

def OriginSymmetric {n : ℕ} (K : Set (Space n)) : Prop :=
  ∀ x, x ∈ K ↔ -x ∈ K

def support {n : ℕ} (K : Set (Space n)) (u : Space n) : ℝ :=
  sSup ((fun x : Space n => ⟪x, u⟫_ℝ) '' K)

def wulff {n : ℕ} (f : Space n → ℝ) : Set (Space n) :=
  {x | ∀ u, ‖u‖ = 1 → ⟪x, u⟫_ℝ ≤ f u}

def logCombination {n : ℕ} (K L : Set (Space n)) (t : ℝ) :
    Set (Space n) :=
  wulff (fun u => (support K u) ^ (1 - t) * (support L u) ^ t)



end LogBrunnMinkowski
end
end OAI


