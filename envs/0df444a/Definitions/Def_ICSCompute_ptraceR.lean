-- Prove2me | Definitions.Def_ICSCompute_ptraceR
-- name    : ICSCompute_ptraceR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:44:59.832788+00:00
-- url     : https://prove2.me/theorems/99e2f5bb-bb2f-4d07-895c-7dc67270c58b
-- title:
--   Partial trace over a feedback register shared by input and output
-- statement:
--   Let $H_R = \mathcal S(n)$, $H_P$ and $H_F$ be registers and $M \in \mathcal L(H_R\otimes H_P,\,H_R\otimes H_F)$. The **partial trace over the two copies of $H_R$** is
--   $$\operatorname{Tr}_R(M) := \sum_{x} \big(\langle x|\otimes I_{\mathcal L(H_F)}\big)\, M\, \big(|x\rangle\otimes I_{\mathcal L(H_P)}\big) \in \mathcal L(H_P, H_F).$$
--   When $H_P = H_F$ this is the usual partial trace of a square matrix (Definition 3.10).
--
--   The partial trace is the operation that "closes" a feedback loop: it identifies the input and output copies of $R$ and sums over its computational basis. It is used for the CJ inverse, for the generated unitary $\operatorname{Tr}_R(U_C)$ and for the operator $T_{\mathbf V}$.
--
--   **Formalization Note** A matrix in $\mathcal L(H_P, H_F)$ is indexed (output, input); the traced register is the first tensor factor, so the $(f,p)$ entry of $\operatorname{Tr}_R(M)$ is $\sum_r M_{(r,f),(r,p)}$.
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), Definitions 3.10–3.11, p.16 (PDF p.18)

import Mathlib

namespace ICSCompute

/-- **Partial trace over a register shared by input and output** (Shmueli, *What Can Be
Computed with Indefinite Causal Structure?*, arXiv:2610.40573, version of 2026-11-03, sha256
d3e36399…b606, Definitions 3.10–3.11, p.16 (PDF p.18)).

For `M ∈ L(H_R ⊗ H_P, H_R ⊗ H_F)`,
`Tr_R(M) := ∑_x (⟨x| ⊗ I_{L(H_F)}) M (|x⟩ ⊗ I_{L(H_P)})`, a matrix in `L(H_P, H_F)`.
Definition 3.10 is the case `H_P = H_F`.

**Formalization Note** Operators are matrices; a matrix in `L(H_P, H_F)` is
`Matrix F P ℂ` (rows = output basis, columns = input basis), and a tensor product of registers is
a product index type with the traced register `R` as the first factor. The `(f, p)` entry of
`Tr_R(M)` is `∑_r M (r, f) (r, p)`. -/
def ptraceR {R P F : Type*} [Fintype R] (M : Matrix (R × F) (R × P) ℂ) : Matrix F P ℂ :=
  Matrix.of fun f p => ∑ r : R, M (r, f) (r, p)

end ICSCompute


