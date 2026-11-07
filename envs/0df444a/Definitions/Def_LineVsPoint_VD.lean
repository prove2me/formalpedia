-- Prove2me | Definitions.Def_LineVsPoint_VD
-- name    : LineVsPoint_VD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:03:04.306247+00:00
-- url     : https://prove2.me/theorems/81f2ea78-b063-4527-8fa2-030a583be4c6
-- title:
--   The space $V_D$ of trivariate polynomials of weighted degree at most $D$
-- statement:
--   Assign the weights $1,1,d$ to the variables $X,Y,Z$, so that the monomial $X^iY^jZ^k$ has **weighted degree** $i+j+dk$, and $\mathrm{wdeg}(A)=\max\{i+j+dk:[X^iY^jZ^k]A\ne 0\}$. The space
--
--   $$
--   V_D=\operatorname{span}_{\mathbb F}\{X^iY^jZ^k : i+j+dk\le D\}
--   $$
--
--   consists of the trivariate polynomials of weighted degree at most $D$. Its dimension is the number of such monomials; Lemma 2.2 bounds it from below, which is what makes the interpolation of Lemma 3.2 possible.
--
--   **Formalization Note** $V_D$ is `MvPolynomial.restrictSupport`; $D$ is a real number (for non-integer $D$, $V_D=V_{\lfloor D\rfloor}$). The weighted degree of one polynomial is `weightedTotalDegree ![1, 1, d]`.
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), §2.3, p.11

import Mathlib

set_option autoImplicit false

namespace LineVsPoint

/-- The space `V_D` of **trivariate polynomials of weighted degree at most `D`**, with weights
`1, 1, d` on `X, Y, Z`: Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is Optimal for the
Line–versus–Point Test* (manuscript, sha256 328a8943…), §2.3, p.11: "the weighted degree of the
monomial `X^i Y^j Z^k` is `i + j + dk`", "Let `V_D` be the space of trivariate polynomials of
weighted degree at most `D`."

**Formalization Note.** `V_D` is the `F`-span of the monomials `X^i Y^j Z^k` with
`i + j + dk ≤ D` (`MvPolynomial.restrictSupport`); `D` is a real number, so the definition also
covers non-integer `D` (and then `V_D = V_{⌊D⌋}`). The weighted degree of a single polynomial is
`MvPolynomial.weightedTotalDegree ![1, 1, d]`. -/
noncomputable def VD (F : Type*) [Field F] (d : ℕ) (D : ℝ) :
    Submodule F (MvPolynomial (Fin 3) F) :=
  MvPolynomial.restrictSupport F {e : Fin 3 →₀ ℕ | ((e 0 + e 1 + d * e 2 : ℕ) : ℝ) ≤ D}

end LineVsPoint


