-- Prove2me | Definitions.Def_BinaryEditLower
-- name    : BinaryEditLower
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:01.797302+00:00
-- url     : https://prove2.me/theorems/ef075d7c-06bc-4a92-a71d-60e28d9878d1
-- statement:
--   For lists over any alphabet, an EditStep inserts or deletes one symbol at any position, or substitutes one symbol for another, at unit cost. An EditScript of length n is a sequence of n such steps, with no restriction on the lengths of intermediate lists; the empty script leaves a list unchanged. The edit distance ed(x,y) is the infimum of the natural numbers n for which such a script transforms x into y. Word(α,n) consists of lists of exactly n symbols from α, and RealL1 is the real sequence space ℓ₁ indexed by the natural numbers. For any real-valued function ρ on pairs of elements of a type X and any map f:X→ℓ₁, distortion(ρ,f) is the product of the supremum of ‖f(x)−f(y)‖/ρ(x,y) and the supremum of ρ(x,y)/‖f(x)−f(y)‖, each taken over distinct x,y. No metric assumptions on ρ are imposed in this definition. The quantity c1(X,ρ) is the infimum of these distortions over all injective maps into ℓ₁. For a finite set W of binary words of common length n, binarySetDistortion(W) applies c1 to W with edit distance, viewed as real-valued. Finally, for real c and natural d, growth(c,d) is exp(c√(log(d)log(log(d)))), using the real logarithm and square root.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BinaryEditLower.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BinaryEditLower.lean; bytes 16..1832
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace TreeEdit

universe u

/-- A single unit-cost insertion, deletion, or substitution at any position. -/
inductive EditStep {α : Type u} : List α → List α → Prop
  | insert (p q : List α) (a : α) : EditStep (p ++ q) (p ++ a :: q)
  | delete (p q : List α) (a : α) : EditStep (p ++ a :: q) (p ++ q)
  | substitute (p q : List α) (a b : α) : EditStep (p ++ a :: q) (p ++ b :: q)

/-- An edit script with no restriction on intermediate word lengths. -/
inductive EditScript {α : Type u} : List α → List α → ℕ → Prop
  | nil (x : List α) : EditScript x x 0
  | cons {x y z : List α} {n : ℕ} :
      EditStep x y → EditScript y z n → EditScript x z (n + 1)

noncomputable def ed {α : Type u} (x y : List α) : ℕ :=
  sInf {n | EditScript x y n}

abbrev RealL1 := lp (fun _ : ℕ => ℝ) 1
abbrev Word (α : Type u) (n : ℕ) := {x : List α // x.length = n}

namespace BinaryLower

/-- The product of the two maximal pairwise distance ratios. -/
noncomputable def distortion {X : Type u} (ρ : X → X → ℝ) (f : X → RealL1) : ℝ :=
  sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ‖f x - f y‖ / ρ x y} *
  sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y / ‖f x - f y‖}

/-- The infimum over every injective map into the full real sequence space ℓ₁. -/
noncomputable def c1 (X : Type u) (ρ : X → X → ℝ) : ℝ :=
  sInf {D : ℝ | ∃ f : X → RealL1, Function.Injective f ∧ D = distortion ρ f}

noncomputable def binarySetDistortion {n : ℕ} (W : Finset (Word Bool n)) : ℝ :=
  c1 {x : Word Bool n // x ∈ W}
    (fun x y => (ed x.val.val y.val.val : ℝ))

noncomputable def growth (c : ℝ) (d : ℕ) : ℝ :=
  Real.exp (c * Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ))))

end BinaryLower

open BinaryLower



end TreeEdit
end OAI


