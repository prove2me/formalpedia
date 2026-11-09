-- Prove2me | Definitions.Def_FourBlockIP350_Main_IntegerPrograms
-- name    : FourBlockIP350_Main_IntegerPrograms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:38.8462+00:00
-- url     : https://prove2.me/theorems/4bef5308-0504-4cde-aee7-bf3d43022f77
-- title:
--   Integer programs with signed infinite bounds and three solver outcomes
-- statement:
--   An equality-form integer program has an integer matrix $A$, right-hand side $b$, costs $c$, and independent coordinate bounds. A lower endpoint may be $-\infty$ and an upper endpoint $+\infty$. For an integer vector $z$, feasibility and objective are
--   $$Az=b,\quad \ell\le z\le u,\qquad c^\top z.$$
--   An optimum answer contains an attaining vector and its exact integer cost; infeasibility means there is no integer feasible point. Unboundedness includes feasibility and arbitrarily small integer objective values. These alternatives keep an infeasible instance distinct from one with a negative recession direction.
--
--   **Formalization Note** The generic integer-program model is separate from the block structure. Missing lower and upper endpoints have their respective signed meanings; no extended-integer subtraction is used.
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 2, (4-Block ILP), lines 25–35 and 52–55

import Mathlib

namespace FourBlockIP350.Main

open scoped BigOperators

/-- Equality-form integer programs with independently signed infinite endpoints.
`none` means minus infinity in `lower`, plus infinity in `upper`. -/
structure IntegerProgram (R V : Type) where
  matrix : Matrix R V ℤ
  rhs : R → ℤ
  cost : V → ℤ
  lower : V → Option ℤ
  upper : V → Option ℤ

def InBounds {V : Type} (l u : V → Option ℤ) (z : V → ℤ) : Prop :=
  (∀ j a, l j = some a → a ≤ z j) ∧ (∀ j a, u j = some a → z j ≤ a)

def Objective {R V : Type} [Fintype V] (I : IntegerProgram R V) (z : V → ℤ) : ℤ :=
  ∑ j, I.cost j * z j

def Feasible {R V : Type} [Fintype V] (I : IntegerProgram R V) (z : V → ℤ) : Prop :=
  I.matrix.mulVec z = I.rhs ∧ InBounds I.lower I.upper z

def Optimal {R V : Type} [Fintype V] (I : IntegerProgram R V) (z : V → ℤ) : Prop :=
  Feasible I z ∧ ∀ w, Feasible I w → Objective I z ≤ Objective I w

def UnboundedBelow {R V : Type} [Fintype V] (I : IntegerProgram R V) : Prop :=
  (∃ z, Feasible I z) ∧ ∀ t : ℤ, ∃ z, Feasible I z ∧ Objective I z < t

inductive Answer (V : Type)
  | optimum (point : V → ℤ) (value : ℤ)
  | infeasible
  | unbounded

def CorrectAnswer {R V : Type} [Fintype V] (I : IntegerProgram R V) : Answer V → Prop
  | .optimum z v => Optimal I z ∧ v = Objective I z
  | .infeasible => ¬ ∃ z, Feasible I z
  | .unbounded => UnboundedBelow I

end FourBlockIP350.Main


