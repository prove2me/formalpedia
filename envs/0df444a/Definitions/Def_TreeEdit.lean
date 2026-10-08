-- Prove2me | Definitions.Def_TreeEdit
-- name    : TreeEdit
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:34.332629+00:00
-- url     : https://prove2.me/theorems/bbda56a0-ddf7-4b09-a001-d5e9ebc3977d
-- statement:
--   EditStep x y is a single unit-cost edit on lists over an alphabet α: inserting one element at any position, deleting one element at any position, or substituting one element by another at any position. EditScript x y n holds when y can be reached from x by a chain of exactly n such steps, with no restriction on intermediate lengths. The edit distance ed(x,y) is the infimum of all n for which such a script exists (the set is nonempty, since one can delete everything and then insert). RealL1 is the full infinite-dimensional real ℓ₁ space of absolutely summable real sequences indexed by ℕ. For a finite set W of Boolean lists and a map f from W to RealL1, distortion(W,f) is the product of two suprema over pairs of distinct points x,y in W: the supremum of dist(f x, f y)/ed(x,y) and the supremum of ed(x,y)/dist(f x, f y). c1(W) is the infimum of distortion(W,f) over all injective maps f from W into RealL1. BinaryLowerBound is a defined proposition, not an established theorem: there exist a constant c>0 and a threshold d₀ such that for every d ≥ d₀ there are a length n ≤ d and a set W of at least two Boolean lists, all of length exactly n, with exp(c·√(log d · log log d)) ≤ c1(W), using natural logarithms.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TreeEdit.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TreeEdit.lean; bytes 16..1983
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace TreeEdit

universe u

/-- A single unit-cost insertion, deletion or substitution, at any position. -/
inductive EditStep {α : Type u} : List α → List α → Prop
  | insert (p q : List α) (a : α) : EditStep (p ++ q) (p ++ a :: q)
  | delete (p q : List α) (a : α) : EditStep (p ++ a :: q) (p ++ q)
  | substitute (p q : List α) (a b : α) : EditStep (p ++ a :: q) (p ++ b :: q)

/-- A script of precisely `n` edits. There is no restriction on its intermediate lengths. -/
inductive EditScript {α : Type u} : List α → List α → ℕ → Prop
  | nil (x : List α) : EditScript x x 0
  | cons {x y z : List α} {n : ℕ} :
      EditStep x y → EditScript y z n → EditScript x z (n + 1)

/-- Ordinary unit-cost edit distance. The set is nonempty (delete then insert). -/
noncomputable def ed {α : Type u} (x y : List α) : ℕ :=
  sInf {n | EditScript x y n}

/-- The full infinite-dimensional real ℓ₁ space. -/
abbrev RealL1 := lp (fun _ : ℕ => ℝ) 1

/-- Product of the two maximal pairwise distance ratios. -/
noncomputable def distortion (W : Finset (List Bool)) (f : W → RealL1) : ℝ :=
  sSup {r : ℝ | ∃ x y : W, x ≠ y ∧
      r = dist (f x) (f y) / (ed x.val y.val : ℝ)} *
  sSup {r : ℝ | ∃ x y : W, x ≠ y ∧
      r = (ed x.val y.val : ℝ) / dist (f x) (f y)}

/-- Infimum over all injective ℓ₁ maps, used on finite sets with at least two points. -/
noncomputable def c1 (W : Finset (List Bool)) : ℝ :=
  sInf {D : ℝ | ∃ f : W → RealL1, Function.Injective f ∧ distortion W f = D}

/-- The binary main endpoint, for every sufficiently large cap (natural logarithms). -/
def BinaryLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ∃ n : ℕ, n ≤ d ∧ ∃ W : Finset (List Bool),
      2 ≤ W.card ∧ (∀ w ∈ W, w.length = n) ∧
      Real.exp (c * Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ)))) ≤ c1 W



end TreeEdit
end OAI


