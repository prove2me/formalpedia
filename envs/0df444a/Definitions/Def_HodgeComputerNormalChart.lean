-- Prove2me | Definitions.Def_HodgeComputerNormalChart
-- name    : HodgeComputerNormalChart
-- status  : Definition
-- author  : @shivm
-- created : 2026-11-06T23:03:55.472214+00:00
-- url     : https://prove2.me/theorems/90dac899-4320-46c5-8ae1-24b7d451ca83
-- title:
--   Polynomial coordinates for a normal derivative chart of a sextic certificate
-- statement:
--   Let $R=\mathbb C[z_0,\ldots,z_5]$ and let $F,A,S\in R$. These definitions give polynomial coordinates for the $q=1$ certificate equation on the chart where $P=\partial_0F$ is invertible. Given $W=(W_1,\ldots,W_5)$, put
--
--   $$
--   D=PS,\qquad N_0=AS-\sum_{j=1}^5(\partial_jF)W_j,\qquad N_j=PW_j\quad(1\le j\le5).
--   $$
--
--   Write $z=(X_0,X_1,X_2,Y_0,Y_1,Y_2)$, $F_i=\partial_i F$, $P=F_0$, and use subscripts on $P,S,A$ for partial derivatives. For five polynomials $W_1,\ldots,W_5$, define
--
--   $$
--   \begin{aligned}
--   \mathcal R_{F,A}(S,W)={}&S^2(PA_0-AP_0)\\
--   &+\sum_{j=1}^5\left[P^2S\,\partial_jW_j-PSF_j\,\partial_0W_j
--   +\bigl(F_j(SP_0+PS_0)-P(SP_j+PS_j)\bigr)W_j\right].
--   \end{aligned}
--   $$
--
--   These are explicit polynomial expressions, with no existence or coprimality assertion built into the definitions. The separate soundness theorem identifies $\mathcal R_{F,A}(S,W)$ with $D\operatorname{div}N-dD(N)$ and uses its divisibility by $F$ to construct a certificate. For a fixed $S$, the expression is affine linear in $W$.
--
--   **Formalization Note.** The five free components use `Fin 5`; its index `j` represents physical coordinate `j.succ`. The ambient ring is the existing `HodgeComputer.AmbientPoly 5`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/docs/01-certificates.md, section "One denominator and the normalized equations", equations E1 and E2. Derived coordinates: solve E1 for the first component after adjoining the factor P = partial_0 F to the denominator; expand E2 by the product rule.

import Definitions.Def_DiamondCertificate

set_option autoImplicit false
noncomputable section

namespace HodgeComputer.NormalChart
open MvPolynomial
open scoped BigOperators

/-- The normal derivative on the chart where the first partial derivative is invertible. -/
def normal (F : AmbientPoly 5) : AmbientPoly 5 := pderiv 0 F

/-- Five free numerator components; the first is determined by the gradient equation. -/
def numerator (F A S : AmbientPoly 5) (W : Fin 5 → AmbientPoly 5) :
    Fin 6 → AmbientPoly 5 :=
  Fin.cases (A * S - ∑ j : Fin 5, pderiv j.succ F * W j)
    (fun j => normal F * W j)

/-- The common denominator of the normal-chart vector field. -/
def denominator (F S : AmbientPoly 5) : AmbientPoly 5 := normal F * S

/-- The remaining scalar divergence equation, linear in `W` for a fixed `S`. -/
def residue (F A S : AmbientPoly 5) (W : Fin 5 → AmbientPoly 5) : AmbientPoly 5 :=
  S ^ 2 * (normal F * pderiv 0 A - A * pderiv 0 (normal F)) +
    ∑ j : Fin 5,
      (normal F ^ 2 * S * pderiv j.succ (W j) -
        normal F * S * pderiv j.succ F * pderiv 0 (W j) +
        (pderiv j.succ F * (S * pderiv 0 (normal F) + normal F * pderiv 0 S) -
          normal F * (S * pderiv j.succ (normal F) + normal F * pderiv j.succ S)) * W j)

end HodgeComputer.NormalChart


