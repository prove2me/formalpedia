-- Prove2me | Definitions.Def_QMAvsQCMAH_DNF
-- name    : QMAvsQCMAH_DNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:18:32.330984+00:00
-- url     : https://prove2.me/theorems/b1af5dea-27d9-419c-8f31-048d532d14cd
-- title:
--   DNFs and their width
-- statement:
--   A **DNF** on a finite domain $\mathcal X$ is a disjunction of terms, each a conjunction of literals $[\mathcal O(u)=a]$ with $u\in\mathcal X$, $a\in\{0,1\}$. Its **width** is the largest number of literals in a term.
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Definition 22, p.35; Theorem 7, p.36

import Mathlib

set_option autoImplicit false

namespace QMAvsQCMAH

/-- A **DNF** over a finite domain `X`: a list of terms, each a list of literals `(u, a)` standing
for `[O(u) = a]`; the DNF is the disjunction of the conjunctions of its terms.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Definition 22, p.35 (PDF p.38); Theorem 7, p.36 (PDF p.39): "a DNF f of width at most k on
a finite domain X ⊆ {0, 1}∗". -/
abbrev DNF (X : Type) : Type := List (List (X × Bool))

/-- The value `f(O)` of a DNF on an assignment `O : X → {0,1}`. -/
def DNF.eval {X : Type} (f : DNF X) (O : X → Bool) : Bool :=
  f.any fun t => t.all fun l => decide (O l.1 = l.2)

/-- The **width** of a DNF: the largest number of literals in a term (`0` for no terms). -/
def DNF.width {X : Type} (f : DNF X) : ℕ := (f.map List.length).foldr max 0

end QMAvsQCMAH


