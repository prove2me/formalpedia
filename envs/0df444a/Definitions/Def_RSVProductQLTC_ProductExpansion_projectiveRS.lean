-- Prove2me | Definitions.Def_RSVProductQLTC_ProductExpansion_projectiveRS
-- name    : RSVProductQLTC_ProductExpansion_projectiveRS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:36.430725+00:00
-- url     : https://prove2.me/theorems/77cf6c8d-6e10-4d37-9100-024864f9ff03
-- title:
--   Definition 3.3 — projective Reed–Solomon code
-- statement:
--   Let $K=\mathbb F_s$ and $E$ be finite fields, with a specified inclusion $\iota:K\hookrightarrow E$. For $0\le d\le s-1$, define the **projective Reed–Solomon code** by
--   $$\operatorname{PRS}_{d}(K;E)=\left\{\bigl(f(\iota(r_a))\bigr)_{a\in K\cup\{\infty\}}:f(X,Y)=\sum_{j=0}^{d}f_jX^jY^{d-j},\ f_j\in E\right\}.$$
--   Finite coordinates are $f(\iota(x),1)$, and the infinity coordinate is $f_d$. The code supplies the base constraints in the construction.
--
--   **Formalization Note** The subspace is the $E$-span of the $d+1$ evaluated monomials, equivalently the image of all coefficient tuples in the displayed formula. A field homomorphism represents the inclusion and is automatically injective. The definition is total in $d$; both source theorem uses retain the entire range $d\le s-1$.
-- source:
--   Mitali Bafna, Anqi Li, Quynh T. Nguyen, STOC 2027 submission #1136 (October 2026), Definition 3.3, printed p.8 (PDF p.9)

import Mathlib
import Definitions.Def_GoodQLTC_dualCode
import Definitions.Def_RSVProductQLTC_ProductExpansion_projectiveLine
set_option autoImplicit false

namespace RSVProductQLTC.ProductExpansion

/-- Definition 3.3, printed p.8 (PDF p.9). Span of the d+1 evaluated homogeneous monomials.
The source domain `d ≤ |K|-1` is imposed on statements using this definition. -/
def projectiveRS {K E : Type} [Field K] [Field E] (ι : K →+* E) (d : ℕ) :
    Submodule E (ProjectiveLine K → E) :=
  Submodule.span E (Set.range fun j : Fin (d + 1) => fun a =>
    ι (projectiveRep a 0) ^ j.val * ι (projectiveRep a 1) ^ (d - j.val))

end RSVProductQLTC.ProductExpansion


