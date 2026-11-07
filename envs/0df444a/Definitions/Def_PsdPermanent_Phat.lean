-- Prove2me | Definitions.Def_PsdPermanent_Phat
-- name    : PsdPermanent_Phat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:32:37.636148+00:00
-- url     : https://prove2.me/theorems/8abc46c7-68ae-4909-99e8-4ec42b438c02
-- title:
--   The estimator $\widehat P(A)$
-- statement:
--   The estimator of the permanent is
--   $$\widehat P(A)=e^{\Phi(V)},$$
--   where $V$ is a Gram factor of $A$, with the convention $\widehat P(A)=0$ if $A$ has a zero diagonal entry.
--
--   **Formalization Note** $\Phi$ is defined on factors, so Lean's $\widehat P$ takes both $A$ and $V$ as arguments. Lemma 5 says the value does not depend on the factor.
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), Theorem 1, p.1; §4, p.6

import Mathlib
import Definitions.Def_PsdPermanent_Phi__d25d42
open Matrix

namespace PsdPermanent

open scoped Classical in
/-- **The estimator P̂(A).**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Theorem 1, p.1 and §4, p.6: "P̂(A) = exp(Φ(V)), with the convention P̂(A) = 0 if A has a zero
diagonal entry".

**Formalization Note.** A function of `A` and a factor `V`, because `Φ` is defined on factors; Lemma 5
says the value does not depend on the factor, and the statements quantify over every factor. -/
noncomputable def Phat {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin d) ℂ) : ℝ :=
  if ∃ i, A i i = 0 then 0 else Real.exp (Phi V)

end PsdPermanent


