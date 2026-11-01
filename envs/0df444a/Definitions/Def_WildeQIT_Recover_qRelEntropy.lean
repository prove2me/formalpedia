-- Prove2me | Definitions.Def_WildeQIT_Recover_qRelEntropy
-- name    : WildeQIT_Recover_qRelEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:21:07.740865+00:00
-- url     : https://prove2.me/theorems/82af282f-aa36-4669-a1b7-81c53e39e6bf
-- title:
--   Quantum relative entropy $D(\rho\|\sigma)$
-- statement:
--   Let $\rho$ be a density operator and $\sigma$ a positive semi-definite operator on a finite-dimensional Hilbert space $\mathcal H$. The **quantum relative entropy** is
--
--   $$
--   D(\rho\|\sigma)=\begin{cases}\operatorname{Tr}\{\rho\,[\log\rho-\log\sigma]\} & \text{if } \operatorname{supp}(\rho)\subseteq\operatorname{supp}(\sigma),\\ +\infty & \text{otherwise,}\end{cases}
--   $$
--
--   where $\log$ is the binary logarithm applied to the nonzero eigenvalues (the convention of Definition 3.3.1). The operator $\sigma$ need not have unit trace, so a finite value can be negative.
--
--   It is the quantity whose decrease under a quantum channel the recoverability theorem bounds from below.
--
--   **Formalization Note** The value is an extended real, so the $+\infty$ branch is represented exactly. The trace is taken through its real part; it is real for the book's arguments.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 11.8.2, (11.106)–(11.107), p. 340

import Definitions.Def_WildeQIT_Recover_spectralFun

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Definition 11.8.2, p. 340
(quantum relative entropy).
-/

open Matrix

namespace WildeQIT.Recover

open Classical in
/-- **Quantum relative entropy** (Wilde, arXiv:1106.1445v8, Definition 11.8.2, (11.106)–(11.107),
p. 340): for a density operator `ρ` and a positive semi-definite `σ`,
`D(ρ‖σ) = Tr{ρ [log ρ − log σ]}` if `supp(ρ) ⊆ supp(σ)`, and `+∞` otherwise.

**Formalization Note** The value lies in `EReal`, so the `+∞` branch is the book's. `log` is the
binary logarithm applied on the support (Definition 3.3.1), and the trace of the Hermitian
operator's product with `ρ` is taken through its real part (it is real for the book's
arguments). `σ` need not have unit trace, so a finite value may be negative, as in the book. -/
noncomputable def qRelEntropy {n : Type} [Fintype n] [DecidableEq n]
    (ρ σ : Matrix n n ℂ) : EReal :=
  if SuppSubset ρ σ then ((ρ * (log2Op ρ - log2Op σ)).trace.re : EReal) else ⊤

end WildeQIT.Recover


