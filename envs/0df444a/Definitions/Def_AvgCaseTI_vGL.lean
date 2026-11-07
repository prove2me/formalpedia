-- Prove2me | Definitions.Def_AvgCaseTI_vGL
-- name    : AvgCaseTI_vGL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:22.5922+00:00
-- url     : https://prove2.me/theorems/18c70c88-035c-4c53-8da7-1339264417d6
-- title:
--   Proportions $v(\mathrm{GL},n,q)$ and $u(\mathrm{GL},n,q)$ of eigenvalue-free and unipotent matrices
-- statement:
--   For a finite field $\mathbb F_q$ and $n\ge0$,
--   $$
--   v(\mathrm{GL},n,q)=\frac{|\{\text{eigenvalue-free matrices in }\mathrm{GL}(n,q)\}|}{|\mathrm{GL}(n,q)|},\qquad
--   u(\mathrm{GL},n,q)=\frac{|\{\text{unipotent matrices in }\mathrm{GL}(n,q)\}|}{|\mathrm{GL}(n,q)|},
--   $$
--   where $A$ is unipotent if $c_A(t)=(t-1)^n$. For $n=0$ both are $1$.
--
--   **Formalization Note** The formulas give $1$ at $n=0$ by themselves (the empty matrix has characteristic polynomial $1$), matching the paper's convention $u(\mathrm{GL},0,q)=v(\mathrm{GL},0,q)=1$.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Eqs. (36)–(37), p.35 (PDF p.37)

import Mathlib
import Definitions.Def_AvgCaseTI_UniqueSimpleEig

set_option autoImplicit false

namespace AvgCaseTI

/-- **`v(GL, n, q)`, the proportion of eigenvalue-free matrices in `GL(n, q)`.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Eq. (36), p.35
(PDF p.37): "v(GL, n, q) := |{eigenvalue-free matrices in GL(n, q)}| / |GL(n, q)|".

**Formalization Note.** For `n = 0` the formula gives `1` (the empty matrix has characteristic
polynomial `1`), which is the paper's convention `v(GL, 0, q) := 1`. -/
noncomputable def vGL (K : Type*) [Field K] (n : ℕ) : ℝ :=
  (Nat.card {A : GL (Fin n) K // EigenvalueFree (A : Mat K n)} : ℝ) / Nat.card (GL (Fin n) K)

/-- **`u(GL, n, q)`, the proportion of unipotent matrices in `GL(n, q)`**, Eq. (37), p.35
(PDF p.37): unipotent means `c_A(t) = (t − 1)^n`.

**Formalization Note.** For `n = 0` the formula gives `1`, the paper's convention. -/
noncomputable def uGL (K : Type*) [Field K] (n : ℕ) : ℝ :=
  (Nat.card {A : GL (Fin n) K //
      (A : Mat K n).charpoly = (Polynomial.X - Polynomial.C 1) ^ n} : ℝ) /
    Nat.card (GL (Fin n) K)

end AvgCaseTI


