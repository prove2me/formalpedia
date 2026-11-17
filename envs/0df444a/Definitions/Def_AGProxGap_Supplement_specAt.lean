-- Prove2me | Definitions.Def_AGProxGap_Supplement_specAt
-- name    : AGProxGap_Supplement_specAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:17:52.678403+00:00
-- url     : https://prove2.me/theorems/4f5f69a7-8cb8-4771-a637-daefab89f81f
-- title:
--   Bivariate polynomials over a function field: $R_{P_0}$, $R_a$, $\deg_Z$, $R(y,z)$
-- statement:
--   For a bivariate polynomial $R(Y,Z)=\sum_{a,b}c_{a,b}Y^aZ^b$ with coefficients $c_{a,b}$ in a function field and a point $P_0$ at which all $c_{a,b}$ are regular:
--   1. $R_{P_0}(Y,Z)=R(P_0;Y,Z)=\sum c_{a,b}(P_0)Y^aZ^b$, the specialization of the coefficients at $P_0$;
--   2. for a local parameter $t$ at $P_0$, $R_a(Y,Z)=\sum_{a',b}([t^a]c_{a',b})Y^{a'}Z^b$, so that $R(t,Y,Z)=\sum_{a\ge0}R_a(Y,Z)t^a$ and $R_0=R_{P_0}$;
--   3. $\deg_Z R$, the largest $Z$-degree of a coefficient of $R$;
--   4. $R(y,z)$, the value at $Y=y$, $Z=z$.
--
--   These are the operations of §4.2 (Lemma 4.5, the expansion $R_\nu(t,Y,Z)=\sum_aR_{\nu,a}t^a$, the degree bounds (6)).
--
--   **Formalization Note** A bivariate polynomial is a polynomial in $Y$ whose coefficients are polynomials in $Z$.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §2.5, p.16; §4.2, pp.26–27

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AGProxGap_evalPolyAt
import Definitions.Def_AGProxGap_Supplement_localCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

namespace AGProxGap.Supplement

/-- `deg_Z` of a bivariate polynomial `R ∈ A[Z][Y]` (§2.5, p.16): the largest `Z`-degree of its
`Y`-coefficients (`0` for `R = 0`; the paper's `−∞` there never occurs, as every polynomial it
is applied to is nonzero). -/
noncomputable def degZ {A : Type*} [Semiring A] (R : Polynomial (Polynomial A)) : ℕ :=
  R.support.sup (fun j => (R.coeff j).natDegree)

/-- The value `R(y, z) ∈ A` of a bivariate polynomial `R ∈ A[Z][Y]` at `Y = y`, `Z = z`. -/
noncomputable def evalYZ {A : Type*} [CommSemiring A] (R : Polynomial (Polynomial A)) (y z : A) : A :=
  (R.map (Polynomial.evalRingHom z)).eval y

/-- **Specialization of the function coefficients at a point** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §4.2, p.26: "For a point
P_0 ∈ X(F̄_q) at which all function coefficients of R_ν are regular, we write
R_{ν,P_0}(Y, Z) := R_ν(P_0; Y, Z) ∈ F̄_q[Y, Z] for the polynomial obtained by evaluating each of
these coefficients at P_0").

For `R = Σ_{a,b} c_{a,b} Y^a Z^b` with `c_{a,b}` in the function field, `specAt P_0 R` is
`Σ_{a,b} c_{a,b}(P_0) Y^a Z^b`.

**Formalization Note** Bivariate polynomials are `Polynomial (Polynomial _)`: the outer variable
is `Y`, the inner one `Z`. The coefficient `Y`-wise uses the base `AGProxGap.evalPolyAt`
(evaluation `Place.evalAt` of every `Z`-coefficient). Applied only to polynomials whose
coefficients are regular at `P_0`. -/
noncomputable def specAt {K F : Type*} [Field K] [Field F] [Algebra K F] (P0 : Place K F)
    (R : Polynomial (Polynomial F)) : Polynomial (Polynomial K) :=
  R.sum (fun j c => Polynomial.monomial j (AGProxGap.evalPolyAt P0 c))

/-- **The `t^a`-coefficient of the local expansion of a bivariate polynomial** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §4.2, p.27:
"Expanding the function coefficients of R_ν at P_0 gives R_ν(t, Y, Z) = Σ_{a≥0} R_{ν,a}(Y, Z)t^a
where R_{ν,a} ∈ F̄_q[Y, Z]").

`expCoeff P_0 t R a = R_a` replaces every function coefficient `c_{a',b}` of `R` by its local
expansion coefficient `[t^a]c_{a',b}` (`localCoeff`).

**Formalization Note** Same bivariate layout as `specAt`; for `a = 0` it is `specAt P_0 R`
(`[t^0]c = c(P_0)`). Applied only to polynomials whose coefficients are regular at `P_0`. -/
noncomputable def expCoeff {K F : Type*} [Field K] [Field F] [Algebra K F] (P0 : Place K F)
    (t : F) (R : Polynomial (Polynomial F)) (a : ℕ) : Polynomial (Polynomial K) :=
  R.sum (fun j c => Polynomial.monomial j (c.sum (fun k b => Polynomial.monomial k (localCoeff P0 t b a))))

end AGProxGap.Supplement


