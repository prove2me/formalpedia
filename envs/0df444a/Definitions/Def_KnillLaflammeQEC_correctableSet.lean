-- Prove2me | Definitions.Def_KnillLaflammeQEC_correctableSet
-- name    : KnillLaflammeQEC_correctableSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:59.448151+00:00
-- url     : https://prove2.me/theorems/02853b55-0826-4818-a543-35eac672d64c
-- title:
--   The family $\mathcal A(\mathcal C,\mathcal R)$ of operators corrected by $(\mathcal C,\mathcal R)$
-- statement:
--   For a subspace $\mathcal C$ of a finite-dimensional Hilbert space $\mathcal H$ and a finite family $\mathcal R=\{R_r\}$ of operators on $\mathcal H$, the family $\mathcal A(\mathcal C,\mathcal R)$ consists of all operators $A$ on $\mathcal H$ for which $(\mathcal C,\mathcal R)$ is $\{A\}$-correcting:
--
--   $$
--   \mathcal A(\mathcal C,\mathcal R)=\{A:\ E(\mathcal C,\mathcal R\{A\})=0\}.
--   $$
--
--   It answers the reverse question to the characterization of correcting codes: given the code and the recovery, which interactions are corrected. Theorem 3.1 of the paper describes it.
-- source:
--   Knill, Laflamme, A Theory of Quantum Error-Correcting Codes, arXiv:quant-ph/9604034v1, §3.1, p.12

import Mathlib
import Definitions.Def_KnillLaflammeQEC_codeError

namespace KnillLaflammeQEC

/-- Knill, Laflamme, *A Theory of Quantum Error-Correcting Codes*, arXiv:quant-ph/9604034v1,
§3.1, p.12: "the family `A(C, R)` of operators `A` for which `(C, R)` is `A`-correcting", i.e.
the set of operators `A₀` with `E(C, R{A₀}) = 0`.

**Formalization Note.** Operators are matrices `Matrix ι ι ℂ` on `H = EuclideanSpace ℂ ι`; the
error is `KnillLaflammeQEC.codeError`. -/
def correctableSet {ι K : Type*} [Fintype ι] [Fintype K]
    (C : Submodule ℂ (EuclideanSpace ℂ ι)) (R : K → Matrix ι ι ℂ) : Set (Matrix ι ι ℂ) :=
  {A₀ | codeError C R A₀ = 0}

end KnillLaflammeQEC


