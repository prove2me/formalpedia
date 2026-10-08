-- Prove2me | Definitions.Def_QLLL_Classical_InfiniteKSAT
-- name    : QLLL_Classical_InfiniteKSAT
-- status  : Definition
-- author  : @sattath
-- created : 2026-10-06T17:43:19.181416+00:00
-- url     : https://prove2.me/theorems/d7fbbea5-3fe7-4a1e-a74b-d3dd7acdbf77
-- title:
--   Variables of a clause and relabelling, over an arbitrary variable type
-- statement:
--   Definitions for $k$-SAT over arbitrary variable sets (namespace `QLLL.SAT`).
--
--   1. **Variables of a clause** (`clauseVars'`). For a clause $c$ over a variable type $\mathcal{V}$ with decidable equality, the finite set of variables occurring in $c$.
--   2. **Relabelling** (`relabelClause`). For a map $g : \mathcal{V} \to \mathcal{W}$, the clause obtained by renaming each variable $v$ of $c$ to $g(v)$.
--
--   These are used to state $k$-SAT for infinite formulas and to transport the finite statement to arbitrary types.
-- source:
--   Not in the paper; definitions for infinite k-SAT. Formalization companion to Ambainis, Kempe and Sattath, A Quantum Lovász Local Lemma, arXiv:0911.1696; see the blueprint https://sattath.github.io/Quantum-Lovasz-Local-Lemma/blueprint/

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Classical_KSAT
import Mathlib
import Std.Sat.CNF

/-
Copyright (c) 2026 Or Sattath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Sattath
-/

/-!
# The infinite classical Lovász Local Lemma

`QuantumLocalLemma.Classical.KSAT` proves Corollary 2 for a finite formula: finitely many variables,
finitely many clauses. This file removes both restrictions.

The route is compactness, not a measure-theoretic limit. Two halves:

* `exists_assignment_of_finset'`, a transport of the finite theorem to arbitrary
  variable and index types. For a finite set `T` of clauses only the finitely
  many variables occurring in them matter, so relabelling reduces to the `Fin`
  case already proved.
* `QLLL.Compactness.exists_forall_of_forall_finite`, propositional compactness.

The conclusion holds for **arbitrary** types `V` and `ι`. Neither is assumed
countable, and the proof never needs them to be: `Bool ^ V` is compact by
Tychonoff for any `V`, and the finite intersection property applies to a family
of closed sets of any cardinality.

Note the statement is not about `Std.Sat.CNF`, whose `clauses` field is an
`Array` and hence finite by construction. An infinite instance is a family
`C : ι → CNF.Clause V`, and satisfaction is `∀ i, Clause.eval a (C i) = true`.
-/

namespace QLLL.SAT

open Finset Std.Sat

/-! ## Clauses over an arbitrary variable type -/

/-- The variables occurring in a clause, for an arbitrary variable type. -/
def clauseVars' {V : Type*} [DecidableEq V] (c : CNF.Clause V) : Finset V :=
  (c.map Prod.fst).toFinset

/-- Relabel the variables of a clause along `g`. -/
def relabelClause {V W : Type*} (g : V → W) (c : CNF.Clause V) : CNF.Clause W :=
  c.map fun l => (g l.1, l.2)

/-! ## The finite theorem over arbitrary types -/

/-! ## The infinite theorem -/

end QLLL.SAT


