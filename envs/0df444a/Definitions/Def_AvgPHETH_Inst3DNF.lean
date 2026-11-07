-- Prove2me | Definitions.Def_AvgPHETH_Inst3DNF
-- name    : AvgPHETH_Inst3DNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:25:02.062275+00:00
-- url     : https://prove2.me/theorems/770221c6-c5bd-48eb-8de6-6bae72b9edb4
-- title:
--   An instance of $\Sigma_2\mathrm{SAT}$: a 3DNF $\varphi(y,z)$
-- statement:
--   An instance of $\Sigma_2\mathrm{SAT}$ is a 3DNF formula $\varphi(y,z)$: numbers of variables $|y|$ and $|z|$, and a list of terms, each a list of at most three literals. An empty term is true, and an empty list of terms is false.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §1.1, p.2 (PDF 4)

import Mathlib

namespace AvgPHETH

/-- An instance of `Σ₂SAT`: a 3DNF formula `φ(y, z)` with `numY` variables `y` and `numZ` variables
`z`, as a list of terms, each a list of at most three literals (`(b, v)` is the literal "variable `v`
has value `b`") (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §1.1, p.2 (PDF 4)).

**Formalization Note** "3DNF" is read as "at most three literals per term". An empty term is true and
an empty list of terms is false. -/
structure Inst3DNF where
  /-- the number of variables `y` -/
  numY : ℕ
  /-- the number of variables `z` -/
  numZ : ℕ
  /-- the terms; the variables `Fin (numY + numZ)` list `y` first -/
  terms : List (List (Bool × Fin (numY + numZ)))
  /-- every term has at most three literals -/
  width : ∀ τ ∈ terms, τ.length ≤ 3

end AvgPHETH


