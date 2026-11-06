-- Prove2me | Definitions.Def_MatrixLewis_potential
-- name    : MatrixLewis_potential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:08:10.938171+00:00
-- url     : https://prove2.me/theorems/7ae12abd-8077-4d56-b3ef-b3d6af0e7b32
-- title:
--   Matrix Lewis potential $\varphi_q(S)$
-- statement:
--   Let $S\succ0$ and let $H_S$ be the Gram map of the scaled constraint matrices. The **matrix Lewis potential** is
--   $$
--   \varphi_q(S):=\frac12\sup_{Z\succeq0}\Bigl[\log\det H_S(Z)-\frac1p\operatorname{tr}Z^p\Bigr],
--   $$
--   with the convention $\log\det H_S(Z):=-\infty$ when $H_S(Z)$ is singular.
--
--   It is the matrix analogue of Lewis's variational characterization of $\ell_q$ Lewis weights; Theorem 3.9 shows the supremum is attained at a unique $Z_S\succ0$.
--
--   **Formalization Note** The supremum is a real supremum over the $Z\succeq0$ with $H_S(Z)\succ0$ (the bracket of such a $Z$ is `bracket`, the set of values `bracketSet`). The singular $Z$ contribute $-\infty$ and never attain the supremum, and $Z=I$ is admissible under Assumption 3.1, so leaving them out changes no value, and $\log 0=0$ of Lean never enters. At $S\succ0$ the set is nonempty, bounded above and its supremum attained (Theorem 3.9); elsewhere the value is a junk value no statement reads.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Definition 3.7, p.19, eq. (9)

import Mathlib
import Definitions.Def_MatrixLewis_gram
import Definitions.Def_MatrixLewis_pExp

namespace MatrixLewis

/-- The bracket `log det H_S(Z) − (1/p) tr Z^p` of eq. (9) (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), Definition 3.7, p.19),
at a `Z` with `H_S(Z)` nonsingular. -/
noncomputable def bracket {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S Z : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.log (gram A S Z).det - (1 / pExp q) * (mpow (pExp q) Z).trace

/-- The values of the bracket of eq. (9) over `Z ⪰ 0` with `H_S(Z) ≻ 0`. -/
def bracketSet {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) : Set ℝ :=
  {v | ∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef ∧ (gram A S Z).PosDef ∧ v = bracket q A S Z}

/-- The **matrix Lewis potential** (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), Definition 3.7, p.19, eq. (9)):
`φ_q(S) := ½ sup_{Z ⪰ 0} [log det H_S(Z) − (1/p) tr Z^p]`, with `log det H_S(Z) := −∞` when
`H_S(Z)` is singular.

**Formalization Note** The supremum is a real `sSup` over the `Z ⪰ 0` with `H_S(Z) ≻ 0`.
The `Z` with `H_S(Z)` singular contribute `−∞` in the paper and are left out (they never
attain the sup, and `Z = I` has `H_S(I) ≻ 0` under Assumption 3.1), so Lean's `Real.log 0 = 0`
never enters. At `S ≻ 0` the set is nonempty and bounded above and the sup is attained
(Theorem 3.9), so the real `sSup` is the paper's value; off the positive definite cone the value
is a junk value that no statement reads. `H_S(Z)` is positive semidefinite for `Z ⪰ 0`, so
nonsingular there means positive definite. -/
noncomputable def potential {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (1 / 2 : ℝ) * sSup (bracketSet q A S)

end MatrixLewis


