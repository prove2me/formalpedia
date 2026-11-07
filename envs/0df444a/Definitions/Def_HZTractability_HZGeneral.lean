-- Prove2me | Definitions.Def_HZTractability_HZGeneral
-- name    : HZTractability_HZGeneral
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:08:46.808202+00:00
-- url     : https://prove2.me/theorems/ec6dbe2f-1f84-4dc9-923c-34aa882fe83d
-- title:
--   The general problem: normalized additive $\varepsilon$-equilibria with utilities in $[0,1]$
-- statement:
--   An **instance** is an $N\times N$ rational utility matrix $u$ with $N\ge 1$ and entries in $[0,1]$, together with a positive rational accuracy $\varepsilon$, written in binary. An **answer** is a rational allocation $x$ and rational prices $p$ forming a normalized additive $\varepsilon$-equilibrium of $u$ (Definition 2.2).
--
--   This is the problem whose membership in PPAD the paper derives from [VY25, Section 7]; the problem of Theorem 1.1 is the special case $u_{ij}\in\{0,a,1\}$ with accuracy $\varepsilon^*(a)/N$.
--
--   **Formalization Note** Instances are `encRatMatrix N u ++ encRat ε`, answers `encRatMatrix N x ++ encRatVec N p`, with the public encodings.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), §1.1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_HZTractability_IsNormAddEq

namespace HZTractability

/-- **The general approximate HZ search problem** of the membership claim (Panageas–Shein–
Taherijam–Vazirani, arXiv:2610.35848, held version, sha256 74b7bf9f…, §1.1, p.1 (PDF 3):
"Membership in PPAD follows from [VY25, Section 7] … Their upper bound applies to rational
utilities in [0, 1] and positive rational accuracy").

An instance is the code `encRatMatrix N u ++ encRat ε` of an `N × N` rational utility matrix with
`N ≥ 1` and every entry in `[0, 1]`, followed by a positive rational accuracy `ε`. An answer is the
code `encRatMatrix N x ++ encRatVec N p` of a rational allocation `x` and rational prices `p` that
form a normalized additive `ε`-equilibrium of `u` (Definition 2.2, `IsNormAddEq`).

**Formalization Note** Encodings are the public self-delimiting `CardinalMatching.encRatMatrix`,
`encRatVec` and `QAlgorithms.LocalHamiltonian.encRat` (sign, numerator, denominator). Answers are
rational, as in `HZThreeValue`. -/
def HZGeneral : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (N : ℕ) (u : Fin N → Fin N → ℚ) (ε : ℚ), 1 ≤ N ∧
    (∀ i j, 0 ≤ u i j ∧ u i j ≤ 1) ∧ 0 < ε ∧
    s = CardinalMatching.encRatMatrix N u ++ QAlgorithms.LocalHamiltonian.encRat ε
  answer s t := ∃ (N : ℕ) (u : Fin N → Fin N → ℚ) (ε : ℚ), 1 ≤ N ∧
    (∀ i j, 0 ≤ u i j ∧ u i j ≤ 1) ∧ 0 < ε ∧
    s = CardinalMatching.encRatMatrix N u ++ QAlgorithms.LocalHamiltonian.encRat ε ∧
    ∃ (x : Fin N → Fin N → ℚ) (p : Fin N → ℚ),
      t = CardinalMatching.encRatMatrix N x ++ CardinalMatching.encRatVec N p ∧
      IsNormAddEq (fun i j => (u i j : ℝ)) (ε : ℝ) (fun i j => (x i j : ℝ)) (fun j => (p j : ℝ))

end HZTractability


