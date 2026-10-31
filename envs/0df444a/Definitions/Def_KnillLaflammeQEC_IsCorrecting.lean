-- Prove2me | Definitions.Def_KnillLaflammeQEC_IsCorrecting
-- name    : KnillLaflammeQEC_IsCorrecting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:52.63343+00:00
-- url     : https://prove2.me/theorems/68268b13-4edd-40dc-8c0b-06edf05babb0
-- title:
--   $(\mathcal C,\mathcal R)$ is an $\mathcal A$-correcting code
-- statement:
--   Let $\mathcal C$ be a subspace of a finite-dimensional Hilbert space $\mathcal H$, $\mathcal R=\{R_r\}$ a finite family of operators on $\mathcal H$ and $\mathcal A=\{A_a\}_{a\in\alpha}$ a family of operators on $\mathcal H$ indexed by an arbitrary set $\alpha$. The pair $(\mathcal C,\mathcal R)$ is an **$\mathcal A$-correcting code** if
--
--   $$
--   E(\mathcal C,\mathcal R\{A_a\})=0\qquad\text{for every }a\in\alpha,
--   $$
--
--   where $E$ is the error of the code for one interaction operator. Knill and Laflamme define $\mathcal A$-correcting by $E(\mathcal C,\mathcal R\mathcal A)=0$ and observe that this is the same as asking it for each $A_a$, which makes sense also for infinite $\mathcal A$; the definition here is that per-operator form.
--
--   **Formalization Note** The family $\mathcal A$ is not required to satisfy the superoperator constraint $\sum_a A_a^\dagger A_a=I$ and may be infinite. Whether $\mathcal R$ is a superoperator is not part of this predicate: statements that need it assume `QAlgorithms.IsKrausFamily R` separately.
-- source:
--   Knill, Laflamme, A Theory of Quantum Error-Correcting Codes, arXiv:quant-ph/9604034v1, §3.1, p.12

import Mathlib
import Definitions.Def_KnillLaflammeQEC_codeError

namespace KnillLaflammeQEC

/-- Knill, Laflamme, *A Theory of Quantum Error-Correcting Codes*, arXiv:quant-ph/9604034v1,
§3.1, p.12: the pair `(C, R)` is an `A`-correcting code if `E(C, RA) = 0`; "this is equivalent
to saying that for each `A_a`, `E(C, RA_a) = 0`. Thus we can speak of `A`-correcting codes even
if `A` is not finite." This definition is that per-operator form.

**Formalization Note.** `A : α → Matrix ι ι ℂ` is an arbitrary family of interaction operators,
indexed by any type `α` (possibly infinite) and **not** required to satisfy the superoperator
constraint `Σ_a A_a† A_a = I` (Eq.(5)). Whether `R` is a superoperator is not part of this
predicate; statements that need it assume `QAlgorithms.IsKrausFamily R` separately. -/
def IsCorrecting {ι K α : Type*} [Fintype ι] [Fintype K]
    (C : Submodule ℂ (EuclideanSpace ℂ ι)) (R : K → Matrix ι ι ℂ) (A : α → Matrix ι ι ℂ) :
    Prop :=
  ∀ a, codeError C R (A a) = 0

end KnillLaflammeQEC


