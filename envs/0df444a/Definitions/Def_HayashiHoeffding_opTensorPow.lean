-- Prove2me | Definitions.Def_HayashiHoeffding_opTensorPow
-- name    : HayashiHoeffding_opTensorPow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:17:19.006401+00:00
-- url     : https://prove2.me/theorems/1a734bf7-2ede-4a43-8fc6-fc3367104a97
-- title:
--   Tensor power $A^{\otimes n}$ of a bounded operator
-- statement:
--   Let $A$ be a bounded operator on a complex Hilbert space $\mathcal H$. Its **tensor power** $A^{\otimes n}$ is the bounded operator on $\mathcal H^{\otimes n}$ determined by
--
--   $$A^{\otimes n}(x_1 \otimes \cdots \otimes x_n) = A x_1 \otimes \cdots \otimes A x_n .$$
--
--   It is defined recursively: $A^{\otimes 1} = A$, and $A^{\otimes (n+1)}$ is the continuous extension to the completion of the operator $A^{\otimes n} \otimes A$ on the algebraic tensor product $\mathcal H^{\otimes n} \otimes \mathcal H$.
--
--   For density operators $\rho$, $\sigma$ this gives the $n$-copy hypotheses $\rho^{\otimes n}$ and $\sigma^{\otimes n}$.
--
--   **Formalization Note** `opTensorPow A k` is $A^{\otimes (k+1)}$ (copies indexed $k \mapsto k+1$). The extension is Mathlib's `ContinuousLinearMap.completion` of `TensorProduct.mapL`.
-- source:
--   Hayashi, Error Exponent in Asymmetric Quantum Hypothesis Testing and Its Application to Classical-Quantum Channel coding, arXiv:quant-ph/0611013v2, "Formulation and main results", p.2

import Mathlib
import Definitions.Def_HayashiHoeffding_tensorPow

namespace HayashiHoeffding

universe u

/-- The tensor power `A^{⊗(k+1)}` of a bounded operator `A` on a complex Hilbert space `H`, as a
bounded operator on `H^{⊗(k+1)}` (`HayashiHoeffding.tensorPow H k`). At `k = 0` it is `A`; at
`k + 1` it is the continuous extension to the completion of `A^{⊗(k+1)} ⊗ A` on the algebraic
tensor product, so that `A^{⊗n}(x₁ ⊗ ⋯ ⊗ xₙ) = A x₁ ⊗ ⋯ ⊗ A xₙ` on elementary tensors.

Hayashi, arXiv:quant-ph/0611013v2, "Formulation and main results", p.2 (the operators `ρ⊗n`,
`σ⊗n`).

**Formalization Note.** Copies are indexed `k ↦ k + 1`: `opTensorPow A k` is `A^{⊗(k+1)}`. -/
noncomputable def opTensorPow {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →L[ℂ] H) : (k : ℕ) → (tensorPow H k →L[ℂ] tensorPow H k)
  | 0 => A
  | k + 1 => (TensorProduct.mapL (opTensorPow A k) A).completion

end HayashiHoeffding


