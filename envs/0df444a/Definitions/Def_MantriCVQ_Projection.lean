-- Prove2me | Definitions.Def_MantriCVQ_Projection
-- name    : MantriCVQ_Projection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:18.316061+00:00
-- url     : https://prove2.me/theorems/52238a7b-8667-4f5c-9e99-c13bb80d20aa
-- title:
--   Projections and projected DNFs
-- statement:
--   A **projection** substitutes a constant or a free variable for every variable $x_j$, so an assignment $z$ of the free variables gives the assignment $\rho(z)$. The projected DNF is normalized as in §3: a term containing a false literal is deleted, true literals are removed from the remaining terms, repeated literals are merged, and a term containing a variable together with its negation is deleted.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3, p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_SamplingAC0_DNF

open SamplingAC0

namespace MantriCVQ

/-- The assignment `ρ(z)` of a projection `ρ` from the variables `K` to the variables `V`, which
substitutes a constant or a variable of `K` for every variable of `V` (Mantri, arXiv:2610.37635 (PDF
sha256 d1fab777…1d0b33), §3, p. 13 (PDF p. 15)). -/
def applyProj {V K : Type} (ρ : V → Bool ⊕ K) (z : K → Bool) : V → Bool :=
  fun v => Sum.elim id z (ρ v)

/-- The projection of a term, normalized as in §3, p. 13: a term containing a false literal is
deleted, true literals are deleted from the remaining terms, repeated literals are merged, and a term
containing a variable together with its negation is deleted. -/
def projTerm {V K : Type} [DecidableEq K] (ρ : V → Bool ⊕ K) (t : Term V) : Option (Term K) :=
  if t.any (fun l => Sum.elim (fun c => c != l.2) (fun _ => false) (ρ l.1)) then none
  else
    let t' : Term K := (t.filterMap fun l => Sum.elim (fun _ => none) (fun i => some (i, l.2)) (ρ l.1)).dedup
    if t'.any (fun l => decide ((l.1, !l.2) ∈ t')) then none else some t'

/-- The projected and normalized DNF (§3, p. 13: "A projected DNF, after normalization, is a DNF of
the same or smaller width"). -/
def projDNF {V K : Type} [DecidableEq K] (ρ : V → Bool ⊕ K) (φ : DNF V) : DNF K :=
  φ.filterMap (projTerm ρ)

end MantriCVQ


