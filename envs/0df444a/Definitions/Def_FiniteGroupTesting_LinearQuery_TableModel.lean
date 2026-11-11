-- Prove2me | Definitions.Def_FiniteGroupTesting_LinearQuery_TableModel
-- name    : FiniteGroupTesting_LinearQuery_TableModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:12.857192+00:00
-- url     : https://prove2.me/theorems/d1b0285e-a8b1-4969-b36e-c73f9f7b9f7c
-- title:
--   Arbitrary labelled tables and same-carrier distance
-- statement:
--   Let $G=\{0,\ldots,n-1\}$ and let $* : G^2\to G$ be any total operation. A group law with identity $e$ satisfies associativity, both identity laws, and existence of a two-sided inverse for every element. Define
--
--   $$d(*,\circ)=\frac{|\{(x,y)\in G^2:x*y\ne x\circ y\}|}{n^2}.$$
--
--   The operation is $\epsilon$-far when this distance is at least $\epsilon$ for every group law on the entire same labelled set. Uniform probabilities are finite counting ratios on their full sample spaces. Applications assume positive size, so these ratios never use a zero denominator. This separates the arbitrary input table from the genuine group property.
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 1, 12–13, §§1, 2.1

import Mathlib

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery

/-- An arbitrary labelled multiplication table; no algebraic promise is imposed. -/
abbrev Table (n : ℕ) := Fin n → Fin n → Fin n

/-- The group axioms for the supplied multiplication, with its specified identity. -/
def GroupLawAt {X : Type*} (op : X → X → X) (e : X) : Prop :=
  (∀ x y z, op (op x y) z = op x (op y z)) ∧
  (∀ x, op e x = x) ∧ (∀ x, op x e = x) ∧
  ∀ x, ∃ y, op x y = e ∧ op y x = e

def IsGroupLaw {X : Type*} (op : X → X → X) : Prop :=
  ∃ e, GroupLawAt op e

noncomputable def tableDistance {n : ℕ} (op law : Table n) : ℝ :=
  ((Finset.univ.filter fun xy : Fin n × Fin n => op xy.1 xy.2 ≠ law xy.1 xy.2).card : ℝ) /
    (n : ℝ) ^ 2

/-- Distance to every genuine group law on the entire same labelled carrier. -/
def Far {n : ℕ} (ε : ℝ) (op : Table n) : Prop :=
  ∀ law : Table n, IsGroupLaw law → ε ≤ tableDistance op law

/-- Uniform probability on a finite sample space; all applications have a nonempty space. -/
noncomputable def uniformProbability {Ω : Type*} [Fintype Ω] (event : Ω → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter event).card : ℝ) / Fintype.card Ω

/-- The paper uses [n]={1,...,n}; Fin n relabels i to i+1. -/
def paperLabel {n : ℕ} (x : Fin n) : ℕ := x.val + 1

end FiniteGroupTesting.LinearQuery


