-- Prove2me | Definitions.Def_EditDistance
-- name    : EditDistance
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:09.271813+00:00
-- url     : https://prove2.me/theorems/0e7f7be0-8ed8-47f7-8339-eb6ed74f1ff2
-- statement:
--   For lists over any alphabet, a unit edit inserts or deletes one symbol at any position, or substitutes one symbol when substitutions are enabled. A script consists of exactly n such edits, with no restriction on intermediate words. The edit distance is the least script length when substitutions are enabled. Let ℓ¹ be the space of absolutely summable real sequences indexed by the natural numbers. For a real-valued function ρ on pairs of points and an injective map f into ℓ¹, its distortion is the product of the suprema, over distinct x and y, of ‖f(x)−f(y)‖/ρ(x,y) and ρ(x,y)/‖f(x)−f(y)‖. The least distortion is the infimum over all such injective maps. E(A,d) denotes this quantity for all words over A of length at most d, using edit distance. Define F(c,d)=exp(c√(log d·log log d)), and let alphabetSup(d) be the supremum of E(A,d) for standard finite alphabets of every cardinality at least two. BinaryWitness(c,d) is the proposition that some nonempty finite set of binary words, all of one common length n≤d, has least distortion at least F(c,d). MainClaim is the defined proposition that there exist positive real constants c,C and a natural threshold d₀ such that, for every d≥d₀, every finite alphabet A with at least two symbols satisfies F(c,d)≤E(A,d)≤F(C,d), BinaryWitness(c,d) holds, and F(c,d)≤alphabetSup(d)≤F(C,d). All extrema here are taken in the real numbers; the general distortion definition imposes no metric assumptions on ρ.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditDistance.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditDistance.lean; bytes 16..2913
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace EditDistortion

universe u

/-- A single unit-cost insertion, deletion, or (when enabled) substitution. -/
inductive Step (substitutions : Bool) {Alpha : Type u} : List Alpha → List Alpha → Prop
  | insert (p q : List Alpha) (a : Alpha) : Step substitutions (p ++ q) (p ++ a :: q)
  | delete (p q : List Alpha) (a : Alpha) : Step substitutions (p ++ a :: q) (p ++ q)
  | substitute (h : substitutions = true) (p q : List Alpha) (a b : Alpha) :
      Step substitutions (p ++ a :: q) (p ++ b :: q)

/-- An unrestricted script of exactly n unit edits. -/
inductive Script (substitutions : Bool) {Alpha : Type u} : ℕ → List Alpha → List Alpha → Prop
  | nil (x : List Alpha) : Script substitutions 0 x x
  | cons {n : ℕ} {x y z : List Alpha} (first : Step substitutions x y)
      (rest : Script substitutions n y z) : Script substitutions (n + 1) x z

/-- Minimum script length. Scripts always exist (delete x and insert y). -/
noncomputable def edit {Alpha : Type u} (x y : List Alpha) : ℕ :=
  sInf {n | Script true n x y}

abbrev L1 := lp (fun _ : ℕ => ℝ) 1

/-- The product of the two maximal distance ratios. -/
noncomputable def distortion {X : Type u} (ρ : X → X → ℝ) (f : X ↪ L1) : ℝ :=
  sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ‖f x - f y‖ / ρ x y} *
    sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y / ‖f x - f y‖}

/-- The infimum over injective maps to real absolutely summable sequences. -/
noncomputable def leastDistortion {X : Type u} (ρ : X → X → ℝ) : ℝ :=
  sInf (Set.range (distortion ρ))

abbrev Words (Alpha : Type u) (d : ℕ) := {x : List Alpha // x.length ≤ d}

noncomputable def E (Alpha : Type u) (d : ℕ) : ℝ :=
  leastDistortion (fun x y : Words Alpha d => (edit x.val y.val : ℝ))

noncomputable def exponentScale (c : ℝ) (d : ℕ) : ℝ :=
  Real.exp (c * Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ))))

/-- Supremum over finite alphabet cardinalities. -/
noncomputable def alphabetSup (d : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ n : ℕ, 2 ≤ n ∧ r = E (Fin n) d}

/-- A finite nonempty subset of binary words of one common length. -/
def BinaryWitness (c : ℝ) (d : ℕ) : Prop :=
  ∃ n : ℕ, n ≤ d ∧ ∃ S : Set (List Bool), S.Finite ∧ S.Nonempty ∧
    (∀ w ∈ S, w.length = n) ∧
    exponentScale c d ≤ leastDistortion (fun x y : S => (edit x.val y.val : ℝ))

/-- Uniform two-sided bounds with common positive constants and threshold. -/
def MainClaim : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    (∀ (Alpha : Type u) [Fintype Alpha], 2 ≤ Fintype.card Alpha →
      exponentScale c d ≤ E Alpha d ∧ E Alpha d ≤ exponentScale C d) ∧
    BinaryWitness c d ∧
    exponentScale c d ≤ alphabetSup d ∧ alphabetSup d ≤ exponentScale C d

end EditDistortion

universe u



end OAI


