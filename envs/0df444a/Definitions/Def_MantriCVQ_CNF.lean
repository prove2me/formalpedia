-- Prove2me | Definitions.Def_MantriCVQ_CNF
-- name    : MantriCVQ_CNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:13.840716+00:00
-- url     : https://prove2.me/theorems/e4a18ee1-4e8b-4fbb-a785-8fc0abef9343
-- title:
--   CNF formulas and their evaluation
-- statement:
--   A **CNF** over variables $V$ is a list of clauses, each a list of literals $(v,b)$, where $(v,\mathsf{true})$ is $x_v$ and $(v,\mathsf{false})$ is $\neg x_v$. An empty clause is false and a CNF with no clauses is true. Together with the published DNF type, this gives the two kinds of formula used in the switching argument.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3, p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_SamplingAC0_DNF

open SamplingAC0

namespace MantriCVQ

/-- A CNF over the variables `V`: a list of clauses, each a list of literals `(v, b)`, where `(v, true)`
is `x_v` and `(v, false)` is `¬x_v` (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3,
p. 13 (PDF p. 15)). -/
abbrev CNF (V : Type) : Type := List (Term V)

/-- Evaluation of a CNF (§3, p. 13: "an empty clause is false … a CNF with no clauses is true"). -/
def CNF.eval {V : Type} (ψ : CNF V) (x : V → Bool) : Bool :=
  ψ.all fun c => c.any fun l => x l.1 == l.2

end MantriCVQ


