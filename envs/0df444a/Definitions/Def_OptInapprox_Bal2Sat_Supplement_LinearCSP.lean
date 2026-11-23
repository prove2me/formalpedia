-- Prove2me | Definitions.Def_OptInapprox_Bal2Sat_Supplement_LinearCSP
-- name    : OptInapprox_Bal2Sat_Supplement_LinearCSP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:53:45.794048+00:00
-- url     : https://prove2.me/theorems/20cdbdc2-b053-4e9e-8a78-213571152c61
-- title:
--   Definitions 14–15,22 — MAX-2LIN(q), difference equations and folding
-- statement:
--   A linear equation modulo $q$ has at most two variable occurrences, with arbitrary coefficients and right-hand side in $\mathbb Z/q\mathbb Z$. A missing variable represents a zero term, so constant and one-variable equations are included. A general weighted instance assigns nonnegative real weights to a finite collection of equations. Its objective is satisfied weight and its optimum fraction is the finite maximum objective divided by total weight.
--
--   The encodable inputs are lists of unit-weight equations, with repetition representing natural-number weights. A separate difference-equation input contains triples $(i,j,c)$ and embeds them into the general class as
--
--   $$1x_i+(-1)x_j=c\quad\Longleftrightarrow\quad x_i-x_j=c.$$
--
--   The structural lemma proves this equivalence. The unit-weight embedding preserves the normalized optimum. Both gap promises require a nonempty list. The unary encoding records variable counts, equation counts, optional variable indices, coefficients and right-hand sides. The difference encoding is exactly the general encoding composed with the inclusion.
--
--   Additive folding is $f(x+c\mathbf1)=f(x)+c$ over $\mathbb Z/q\mathbb Z$, including composite $q$. Neither a field structure nor primality is imposed. The source's later minus sign in reconstructing a query is not used; Definition 22 fixes the plus sign. This module defines the optimization model independently of all hardness claims.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), pp. 27,35, Definitions 14–15 and 22

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC

namespace OptInapprox.Bal2Sat.Supplement

/-- A linear equation modulo arbitrary q, with at most two variable occurrences.
An absent variable is the zero term; repeated variables are allowed. -/
structure LinEquation (q n : ℕ) where
  left : Option (Fin n)
  right : Option (Fin n)
  a : ZMod q
  b : ZMod q
  rhs : ZMod q

def LinEquation.holds {q n : ℕ} (e : LinEquation q n) (x : Fin n → ZMod q) : Prop :=
  e.a * (e.left.elim 0 x) + e.b * (e.right.elim 0 x) = e.rhs

/-- General real-weight optimization instance of Definition 14. -/
structure WeightedLinInstance (q : ℕ) where
  n : ℕ
  m : ℕ
  equation : Fin m → LinEquation q n
  weight : Fin m → ℝ
  nonneg : ∀ i, 0 ≤ weight i

open scoped Classical in
noncomputable def WeightedLinInstance.satWeight {q : ℕ} (I : WeightedLinInstance q)
    (x : Fin I.n → ZMod q) : ℝ :=
  ∑ i, I.weight i * if (I.equation i).holds x then 1 else 0

noncomputable def WeightedLinInstance.totalWeight {q : ℕ} (I : WeightedLinInstance q) : ℝ :=
  ∑ i, I.weight i

noncomputable def WeightedLinInstance.optFrac {q : ℕ} [NeZero q]
    (I : WeightedLinInstance q) : ℝ :=
  (Finset.univ.sup' Finset.univ_nonempty I.satWeight) / I.totalWeight

/-- Finite strings suffice for hardness: weights are multiplicities of listed equations. -/
structure LinInput (q : ℕ) where
  n : ℕ
  equations : List (LinEquation q n)

def LinInput.toWeighted {q : ℕ} (I : LinInput q) : WeightedLinInstance q where
  n := I.n
  m := I.equations.length
  equation := I.equations.get
  weight := fun _ => 1
  nonneg := fun _ => zero_le_one

/-- Γ-MAX-2LIN(q), retained as its own encodable subclass. -/
structure DifferenceInput (q : ℕ) where
  n : ℕ
  equations : List (Fin n × Fin n × ZMod q)

def DifferenceInput.toLinear {q : ℕ} (I : DifferenceInput q) : LinInput q where
  n := I.n
  equations := I.equations.map fun e => ⟨some e.1, some e.2.1, 1, -1, e.2.2⟩

/-- The subclass inclusion really is the equation x_i - x_j = c. -/
@[simp] theorem difference_equation_holds {q n : ℕ} (i j : Fin n) (c : ZMod q)
    (x : Fin n → ZMod q) :
    (LinEquation.mk (some i) (some j) 1 (-1) c).holds x ↔ x i - x j = c := by
  simp [LinEquation.holds, sub_eq_add_neg]

/-- q≥2 is a theorem premise, encoded here as a typeclass ensuring finite nonempty assignments. -/
noncomputable def LinInput.optFrac {q : ℕ} [NeZero q] (I : LinInput q) : ℝ :=
  (Finset.univ.sup' Finset.univ_nonempty (I.toWeighted.satWeight)) / I.equations.length

def encOptionVar {n : ℕ} (i : Option (Fin n)) : List OptInapprox.MaxCut.MCSym :=
  OptInapprox.MaxCut.MCSym.unary (i.elim 0 (fun j => j.val + 1))

/-- Repetition is interpreted as unit weight, preserving the normalized optimum. -/
@[simp] theorem LinInput.toWeighted_optFrac {q : ℕ} [NeZero q] (I : LinInput q) :
    I.toWeighted.optFrac = I.optFrac := by
  have hw : I.toWeighted.totalWeight = (I.equations.length : ℝ) := by
    change (∑ _ : Fin I.equations.length, (1 : ℝ)) = (I.equations.length : ℝ)
    simp
  unfold WeightedLinInstance.optFrac LinInput.optFrac
  rw [hw]

/-- Self-delimiting unary data, including coefficients and right-hand sides modulo fixed q. -/
def LinInput.enc {q : ℕ} [NeZero q] (I : LinInput q) : List OptInapprox.MaxCut.MCSym :=
  OptInapprox.MaxCut.MCSym.unary I.n ++
  OptInapprox.MaxCut.MCSym.unary I.equations.length ++
  I.equations.flatMap fun e => encOptionVar e.left ++ encOptionVar e.right ++
    OptInapprox.MaxCut.MCSym.unary e.a.val ++ OptInapprox.MaxCut.MCSym.unary e.b.val ++
    OptInapprox.MaxCut.MCSym.unary e.rhs.val

def LinearGapHard (q : ℕ) [NeZero q] (c s : ℝ) : Prop :=
  OptInapprox.MaxCut.GapNPHard LinInput.enc
    (fun I : LinInput q => I.equations ≠ [] ∧ c ≤ I.optFrac)
    (fun I : LinInput q => I.equations ≠ [] ∧ I.optFrac ≤ s)

def DifferenceGapHard (q : ℕ) [NeZero q] (c s : ℝ) : Prop :=
  OptInapprox.MaxCut.GapNPHard (fun I : DifferenceInput q => I.toLinear.enc)
    (fun I : DifferenceInput q => I.equations ≠ [] ∧ c ≤ I.toLinear.optFrac)
    (fun I : DifferenceInput q => I.equations ≠ [] ∧ I.toLinear.optFrac ≤ s)

/-- Definition 22, over the additive group Z/qZ, without primality assumptions. -/
def AdditivelyFolded {q M : ℕ} (f : (Fin M → ZMod q) → ZMod q) : Prop :=
  ∀ c x, f (fun i => x i + c) = f x + c

end OptInapprox.Bal2Sat.Supplement


