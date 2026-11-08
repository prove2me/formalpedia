-- Prove2me | Definitions.Def_MantriCVQ_listWidth
-- name    : MantriCVQ_listWidth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:07.760987+00:00
-- url     : https://prove2.me/theorems/c00f1c62-c7b1-4f3b-86d4-8bf5b051afa3
-- title:
--   Width of a DNF or CNF
-- statement:
--   The **width** of a DNF or CNF is the maximum number of literals in a term or clause; a formula with no terms or clauses has width zero.
--
--   **Formalization Note** A repeated literal is counted each time. The paper normalizes first, which merges repeats, so a normalized formula has the same width here and in the paper.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3, p. 13 (PDF p. 15)

import Mathlib

namespace MantriCVQ

/-- The width of a DNF or a CNF, given as a list of terms or clauses: the maximum number of literals
(Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3, p. 13 (PDF p. 15): "The width of a DNF or
a CNF is the maximum width of its terms or clauses … A DNF with no terms is false and a CNF with no
clauses is true, and both have width zero").

**Formalization Note** A repeated literal is counted each time. The paper normalizes first, which
merges repeats, so a normalized formula has the same width here and in the paper, and a hypothesis
`listWidth φ ≤ W` covers every normalized formula of width at most `W`. -/
def listWidth {α : Type} (φ : List (List α)) : ℕ :=
  (φ.map List.length).foldr max 0

end MantriCVQ


