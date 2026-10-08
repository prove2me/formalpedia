-- Prove2me | Definitions.Def_QLLL_Classical_KSAT
-- name    : QLLL_Classical_KSAT
-- status  : Definition
-- author  : @sattath
-- created : 2026-10-06T17:42:07.303183+00:00
-- url     : https://prove2.me/theorems/d5dc919d-6426-41ea-994f-a3cf0e8da3ff
-- title:
--   Uniform probability as a valuation, boolean assignments, and clause events
-- statement:
--   Definitions for the classical local lemma and $k$-SAT (namespace `QLLL.SAT`).
--
--   1. **Uniform probability** (`countingFun`, `counting`). For a finite nonempty set $\Omega$, $\Pr(A) = |A| / |\Omega|$ for $A \subseteq \Omega$, packaged as a valuation on the lattice of subsets.
--   2. **Assignments** (`Asg V`). The boolean assignments $\{0,1\}^V$ to the variables $x_1, \dots, x_V$.
--   3. **Dependence on a set of variables** (`DependsOn S A`). A set $A$ of assignments depends only on the variables in $S$ if any two assignments agreeing on $S$ are either both in $A$ or both outside it.
--   4. **Gluing and cylinders** (`merge`, `fixedOn`). `merge S ω τ` takes the values of $\omega$ on $S$ and of $\tau$ off $S$; `fixedOn S g` is the set of assignments agreeing with $g$ on $S$.
--   5. **Clauses** (`clauseVars`, `clauseEvent`). For a clause $c$ of `Std.Sat.CNF`, the set of variables it mentions and the set of assignments satisfying it.
-- source:
--   A. Ambainis, J. Kempe, O. Sattath, A Quantum Lovász Local Lemma, J. ACM 59(5):24 (2012), arXiv:0911.1696 (numbering of the arXiv version), Theorems 1 and 13 and Corollary 2 (classical setting)

import Definitions.Def_QLLL_LocalLemma_Basic
import Mathlib
import Std.Sat.CNF

/-
Copyright (c) 2026 Or Sattath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Sattath
-/

/-!
# The classical Lovász Local Lemma and k-SAT

Towards Corollary 2 of arXiv:0911.1696: a `k`-SAT formula in which every
variable appears in at most `2 ^ k / (e * k)` clauses is satisfiable.

This is the classical shadow of the `k`-QSAT development in `QuantumLocalLemma.Quantum.KQSAT.Basic`.
The two share their whole structure; the only difference is the independence
step, which here is finite counting rather than tensor algebra.

Satisfiability is *not* defined here. We use `Std.Sat.CNF` from the Lean core
library, the same notion `bv_decide` is verified against, so that the statement
proved is the standard one rather than one shaped to fit the proof.

Instantiating `QLLL.Valuation` at `Finset Ω` with `R A = |A| / |Ω|` also yields
the classical asymmetric local lemma of Erdős and Lovász, which Mathlib does
not currently contain in any form.
-/

namespace QLLL.SAT

open Finset Std.Sat

/-! ## The counting valuation -/

variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

/-- Uniform probability of an event on a finite type. -/
noncomputable def countingFun (A : Finset Ω) : ℝ :=
  (A.card : ℝ) / (Fintype.card Ω : ℝ)

/-- Uniform probability on a finite nonempty type, as a `Valuation` on the
lattice of events. Modularity is inclusion/exclusion for cardinalities. -/
noncomputable def counting : Valuation (Finset Ω) where
  toFun := countingFun Ω
  nonneg' _ := by
    simp only [countingFun]
    positivity
  monotone' := by
    intro A B h
    simp only [countingFun]
    have hc : (A.card : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast Finset.card_le_card h
    gcongr
  modular' := by
    intro A B
    simp only [countingFun, Finset.sup_eq_union, Finset.inf_eq_inter]
    rw [← add_div, ← add_div]
    congr 1
    exact_mod_cast (Finset.card_union_add_card_inter A B).symm
  map_top' := by
    have h : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [countingFun, Finset.top_eq_univ, Finset.card_univ]
    exact div_self h
  map_bot' := by simp [countingFun]

/-! ## Events depending on a set of variables -/

variable {V : ℕ}

/-- Assignments to `V` boolean variables. -/
abbrev Asg (V : ℕ) := Fin V → Bool

/-- An event depends only on the variables in `S`. -/
def DependsOn (S : Finset (Fin V)) (A : Finset (Asg V)) : Prop :=
  ∀ ω τ : Asg V, (∀ i ∈ S, ω i = τ i) → (ω ∈ A ↔ τ ∈ A)

/-! ## The counting crux -/

/-- Glue two assignments: take `ω` on `S` and `τ` off `S`. -/
def merge (S : Finset (Fin V)) (ω τ : Asg V) : Asg V :=
  fun i => if i ∈ S then ω i else τ i

/-! ## Independence for the counting valuation -/

/-! ## Counting assignments prescribed on a set of variables -/

/-- The assignments agreeing with `g` on `S`. -/
def fixedOn (S : Finset (Fin V)) (g : Asg V) : Finset (Asg V) :=
  univ.filter fun a => ∀ i ∈ S, a i = g i

/-! ## Clauses -/

/-- The variables occurring in a clause. -/
def clauseVars (c : CNF.Clause (Fin V)) : Finset (Fin V) := (c.map Prod.fst).toFinset

/-- The assignments satisfying a clause. -/
def clauseEvent (c : CNF.Clause (Fin V)) : Finset (Asg V) :=
  univ.filter fun a => CNF.Clause.eval a c

/-! ## The k-SAT corollary -/

end QLLL.SAT


