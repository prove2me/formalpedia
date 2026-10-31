-- Prove2me | Definitions.Def_SPQPoly_NSPQ
-- name    : SPQPoly_NSPQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:37:54.090673+00:00
-- url     : https://prove2.me/theorems/9055d889-b3d1-42a2-a6dd-9b913429f75b
-- title:
--   $N^{SPQ}_{n,d}$: nonnegative SPQ polynomials of degree $d$ in $n$ variables
-- statement:
--   $N^{SPQ}_{n,d}$ is the set of SPQ polynomials $p$ in $n$ variables of degree $d$ that are nonnegative, $p(x)\ge0$ for all $x\in\mathbb R^n$.
--
--   Theorem 3.1 asks when it coincides with $\Sigma^{SPQ}_{n,d}$.
--
--   **Formalization Note** "Degree $d$" is total degree exactly $d$; `NSPQle` is the "at most $d$" reading.
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, §2.2, p.6

import Mathlib
import Definitions.Def_SPQPoly_IsSPQ

open MvPolynomial

namespace SPQPoly

/-- **The set `N^SPQ_{n,d}` of nonnegative SPQ polynomials of degree `d` in `n` variables.**
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1, §2.2,
p.6: "N^SPQ_{n,d} : the set of nonnegative SPQ polynomials in n variables and degree d".
Nonnegative is defined on p.1: "p(x) ≥ 0 for all x ∈ Rn".

**Formalization Note.** "Degree d" is total degree exactly `d` (`totalDegree = d`); the
companion `NSPQle` uses total degree at most `d`. The paper never fixes which reading it means. -/
def NSPQ (n d : ℕ) : Set (MvPolynomial (Fin n) ℝ) :=
  {p | IsSPQ p ∧ p.totalDegree = d ∧ ∀ x : Fin n → ℝ, 0 ≤ eval x p}

end SPQPoly


