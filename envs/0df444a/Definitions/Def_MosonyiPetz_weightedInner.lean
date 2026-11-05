-- Prove2me | Definitions.Def_MosonyiPetz_weightedInner
-- name    : MosonyiPetz_weightedInner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:42:14.535716+00:00
-- url     : https://prove2.me/theorems/29873cca-e6eb-4db4-8168-9f7d1e8786f5
-- title:
--   Weighted inner product $\langle A,B\rangle_D=\operatorname{Tr}A^*D^{1/2}BD^{1/2}$
-- statement:
--   For a positive definite matrix $D$ on $\mathcal H$ the paper uses the inner product
--
--   $$\langle A,B\rangle_D=\operatorname{Tr}\,A^*D^{1/2}BD^{1/2}\qquad(A,B\in\mathcal B(\mathcal H)).$$
--
--   With $D=D_1$ on $\mathcal B(\mathcal H)$ and $D=T(D_1)$ on $\mathcal B(\mathcal K)$ these are the two inner products with respect to which $\alpha$ is the dual of $T^*$ (eq. (4)).
--
--   **Formalization Note** $D^{1/2}$ is the continuous functional calculus of $\sqrt x$; $A^*$ is the conjugate transpose.
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, p.3, the inner products before eq. (4)

import Mathlib

open scoped Matrix

namespace MosonyiPetz

/-- **The weighted inner products of p.3.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, p.3: "⟨A, B⟩_{D1} := Tr A*D1^{1/2}BD1^{1/2} (A, B ∈ B(H))" and
"⟨X, Y⟩_{T(D1)} := Tr X*T(D1)^{1/2}YT(D1)^{1/2} (X, Y ∈ B(K))".

`weightedInner D A B = Tr (Aᴴ * D^{1/2} * B * D^{1/2})`; the two inner products of the paper are
`weightedInner D₁` and `weightedInner (T D₁)`.

**Formalization Note.** `D^{1/2}` is `cfc Real.sqrt D`, the positive square root on the positive
definite matrices the theorems use. -/
noncomputable def weightedInner {H : Type*} [Fintype H] [DecidableEq H]
    (D A B : Matrix H H ℂ) : ℂ :=
  (Aᴴ * cfc Real.sqrt D * B * cfc Real.sqrt D).trace

end MosonyiPetz


