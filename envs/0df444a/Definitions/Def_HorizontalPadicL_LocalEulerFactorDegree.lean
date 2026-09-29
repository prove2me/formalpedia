-- Prove2me | Definitions.Def_HorizontalPadicL_LocalEulerFactorDegree
-- name    : HorizontalPadicL_LocalEulerFactorDegree
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-18T08:55:21.05754+00:00
-- url     : https://prove2.me/theorems/ea125242-d5d6-4832-81b7-63ae351d103f
-- title:
--   Degree of an elliptic curve local Euler factor
-- statement:
--   For an elliptic curve $E/\mathbb{Q}$ and a prime $p$, define coefficient-side predicates expressing the two possible recurrence types for its local Euler factor. `LocalEulerFactorDegreeBelowTwo E p` is the linear recurrence $a_{p^{r+2}}=a_p a_{p^{r+1}}$, covering local Euler polynomials of degree zero or one. `LocalEulerFactorDegreeTwo E p` is the normalized quadratic recurrence $a_{p^{r+2}}=a_p a_{p^{r+1}}-p a_{p^r}$.
-- source:
--   Silverman, The Arithmetic of Elliptic Curves, 2nd ed., Chapter V, §2; standard local Euler factors of elliptic curves over Q.

import Definitions.Def_KN_HorizontalPadicL

set_option autoImplicit false

namespace HorizontalPadicL

/-- Coefficient-side formulation that the local Euler polynomial of `E` at `p`
has degree strictly below two.  For an elliptic curve the reciprocal local Euler
factor then has the linear recurrence displayed here (including the degree-zero
case, when `E.LFunction p = 0`). -/
def LocalEulerFactorDegreeBelowTwo (E : WeierstrassCurve ℚ) (p : ℕ) : Prop :=
  ∀ r : ℕ,
    E.LFunction (p ^ (r + 2)) =
      E.LFunction p * E.LFunction (p ^ (r + 1))

/-- Coefficient-side formulation that the local Euler polynomial of `E` at `p`
has degree two, with its weight-two constant term equal to `p`. -/
def LocalEulerFactorDegreeTwo (E : WeierstrassCurve ℚ) (p : ℕ) : Prop :=
  ∀ r : ℕ,
    E.LFunction (p ^ (r + 2)) =
      E.LFunction p * E.LFunction (p ^ (r + 1)) -
        (p : ℤ) * E.LFunction (p ^ r)

end HorizontalPadicL


