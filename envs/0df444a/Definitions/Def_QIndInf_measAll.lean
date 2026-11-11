-- Prove2me | Definitions.Def_QIndInf_measAll
-- name    : QIndInf_measAll
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:27:57.286024+00:00
-- url     : https://prove2.me/theorems/6fe6789a-2e1a-4ceb-b110-8a18f2504e97
-- title:
--   Measured state $\omega_j=(\mathcal M_{\mathcal I_1}\otimes\cdots\otimes\mathcal M_{\mathcal I_j})(\cdot)$
-- statement:
--   For instruments $\mathcal I_1,\dots,\mathcal I_j$ and an operator $X$ on $R_1\cdots R_j$, measuring every register and recording the outcomes gives the classical–quantum operator
--
--   $$
--   (\mathcal M_{\mathcal I_1}\otimes\cdots\otimes\mathcal M_{\mathcal I_j})(X)=\sum_{x}|x\rangle\langle x|\otimes\mathcal A_{x}(X),\qquad \mathcal A_x=\mathcal E^{(1)}_{x_1}\otimes\cdots\otimes\mathcal E^{(j)}_{x_j},
--   $$
--
--   on $(X_1\cdots X_j)\otimes(R_1\cdots R_j)$. Applied to the true and the reference states it gives $\omega^\rho_j$ and $\omega^\mu_j$ of Eq. (61), whose relative entropy the proof of Theorem 4.2 telescopes.
--
--   **Formalization Note** The outcome registers are grouped first as one factor indexed by outcome strings; the operator is the published `P21.cqOperator` with unit weights and blocks $\mathcal A_x(X)$. For $j=0$ it is $X$ on a one-point outcome set.
-- source:
--   Hiroka, Hsieh, Shirakawa, arXiv:2609.36912 (PDF of 2026-11-02), §4.2, Eq. (61), p.20; Definition 3.1, Eq. (21), p.15

import Mathlib
import Definitions.Def_QIndInf_outcomeProb
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

set_option autoImplicit false

namespace QIndInf

open QAlgorithms QAlgorithms.CopyMeasurements

/-- **Measured state `ω_j = (M_{I₁} ⊗ ⋯ ⊗ M_{I_j})(X)`** (Eq. (61)): every one of the first `j`
registers of an operator `X` on `R₁ … R_j` is measured with its instrument and the outcomes are
recorded. The result is the classical–quantum operator `∑_x |x⟩⟨x| ⊗ A_x(X)` on
`(X₁ … X_j) ⊗ (R₁ … R_j)`, block diagonal in the outcome string `x = (x₁, …, x_j)`.

arXiv:2609.36912 (PDF of 2026-11-02), §4.2, Eq. (61), p.20 (`ω^ρ_j := (M_{I₁} ⊗ … ⊗ M_{I_j})ρ_{≤j}`,
`ω^μ_j := (M_{I₁} ⊗ … ⊗ M_{I_j})μ_{≤j}`), with `M_I` from Definition 3.1, Eq. (21), p.15.

**Formalization Note.** The outcome registers are grouped first, as one factor indexed by the
outcome strings; the published `P21.cqOperator` with unit weights builds the block-diagonal
operator. Since `M_I(ρ) = ∑_x |x⟩⟨x| ⊗ E_x(ρ)`, the tensor product of the `j` measurement channels
has block `E_{x₁} ⊗ ⋯ ⊗ E_{x_j} = A_x` (Eq. (51)) at outcome string `x`. For `j = 0` the result is
`X` itself on a one-point outcome set. -/
noncomputable def measAll {n j : ℕ} {k : Fin j → ℕ}
    (I : (l : Fin j) → QuantumInstrument (Reg n) (Fin (k l)))
    (X : Matrix (Regs n j) (Regs n j) ℂ) :
    Matrix (((l : Fin j) → Fin (k l)) × Regs n j) (((l : Fin j) → Fin (k l)) × Regs n j) ℂ :=
  QAlgorithms.Papers.Independent.Dependency50.P21.cqOperator (fun _ => (1 : ℝ))
    (fun x => histOp I x X)

end QIndInf


