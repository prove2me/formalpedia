-- Prove2me | Definitions.Def_SingleFold
-- name    : SingleFold
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:22.355134+00:00
-- url     : https://prove2.me/theorems/5cdb21fd-ae37-4a14-883f-6cb073ac30eb
-- statement:
--   For a polynomial P with integer coefficients in n input variables and m witness variables, evalNat(P,a,w) evaluates P over the integers at natural-number inputs a : Fin n → ℕ and witnesses w : Fin m → ℕ. Represents(P,S), for a set S of n-tuples of naturals, means that for every input a two things hold: a lies in S exactly when some witness w makes P(a,w)=0, and any two witnesses w and v that both make P(a,w)=0 and P(a,v)=0 must be equal, so the whole witness is unique whenever one exists and no coordinates are hidden outside w. MainStatement is a defined proposition, not an established theorem. It says that for every n ≥ 1 and every set S of n-tuples of naturals that is recursively enumerable (REPred applied to membership in S), there exist some m ≥ 1 and an integer polynomial P in n+m variables such that Represents(P,S) holds; that is, S has a single-fold Diophantine representation with positive input and witness lengths.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SingleFold.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SingleFold.lean; bytes 16..1005
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace SingleFold

/-- Evaluation over the integers of an integer polynomial at natural inputs. -/
noncomputable def evalNat {n m : ℕ} (P : MvPolynomial (Fin n ⊕ Fin m) ℤ)
    (a : Fin n → ℕ) (w : Fin m → ℕ) : ℤ :=
  MvPolynomial.eval (Sum.elim (fun i => (a i : ℤ)) (fun j => (w j : ℤ))) P

/-- Exact existence on members, no witness on nonmembers, and uniqueness of the
whole witness on every input. No coordinates are hidden outside `w`. -/
def Represents {n m : ℕ} (P : MvPolynomial (Fin n ⊕ Fin m) ℤ)
    (S : Set (Fin n → ℕ)) : Prop :=
  ∀ a, (a ∈ S ↔ ∃ w, evalNat P a w = 0) ∧
    ∀ w v, evalNat P a w = 0 → evalNat P a v = 0 → w = v

/-- Single-fold representation with positive input and witness lengths. -/
def MainStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (S : Set (Fin n → ℕ)), REPred (fun a => a ∈ S) →
    ∃ (m : ℕ), 1 ≤ m ∧ ∃ P : MvPolynomial (Fin n ⊕ Fin m) ℤ, Represents P S



end SingleFold
end OAI


