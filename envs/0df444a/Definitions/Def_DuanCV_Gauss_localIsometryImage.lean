-- Prove2me | Definitions.Def_DuanCV_Gauss_localIsometryImage
-- name    : DuanCV_Gauss_localIsometryImage
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:44.076357+00:00
-- url     : https://prove2.me/theorems/943d0fc9-030a-4aa8-9aa8-b2fe42faa031
-- title:
--   The image $\operatorname{tr}_E[(W_1\otimes W_2)\rho(W_1\otimes W_2)^\dagger]$ under local isometries
-- statement:
--   For isometries $W_1,W_2:\ell^2(\mathbb N)\to\ell^2(\mathbb N)\otimes\ell^2(\mathbb N)$, each embedding one mode into that mode tensored with an environment $E_j$, and a two-mode state $\rho$, this is the two-mode state
--
--   $$\operatorname{tr}_{E_1E_2}\bigl[(W_1\otimes W_2)\,\rho\,(W_1\otimes W_2)^\dagger\bigr].$$
--
--   The variance of $\hat u$ in this state is the variance in $\rho$ of the operator obtained from $\hat u$ by replacing $(\hat x_j,\hat p_j)$ with $(W_j^\dagger(\hat x_j\otimes I)W_j,\ W_j^\dagger(\hat p_j\otimes I)W_j)$. By the Stone–von Neumann theorem every Weyl-regular canonical pair on the one-mode space has this form, and $W_j\psi=U_j\psi\otimes|0\rangle$ gives the paper's local unitary $U_1\otimes U_2$. This is how the paper's remark that $\hat x_j,\hat p_j$ "can be any local operators satisfying the commutators" is expressed.
--
--   **Formalization Note** The isometries are arbitrary bounded isometries. The kernel is computed by the published `conjugateKernel` from the Fock-basis coefficients of $W_1$ and $W_2$ (`isometryCoeff`), followed by the sum over both environment indices (the partial trace); mode 1 is index 0.
-- source:
--   Duan, Giedke, Cirac, Zoller, Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, remark after Theorem 1, p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Claimed50.P19 (DensityKernel FockIndex)
open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel isometryCoeff)

namespace DuanCV.Gauss

/-- **The image `tr_E[(W₁ ⊗ W₂) ρ (W₁ ⊗ W₂)†]` of a two-mode kernel under local isometries.**
Duan, Giedke, Cirac, Zoller, *Inseparability criterion for continuous variable systems*, arXiv:quant-ph/9908056v2, remark after Theorem 1, p. 2.

`Wⱼ : ℓ²(ℕ) → ℓ²(ℕ × ℕ)` embeds mode `j` into the mode tensored with an environment `Eⱼ = ℓ²(ℕ)`
(the second coordinate). The kernel of `W₁ ⊗ W₂` has entries `⟨(i₀,e₁)|W₁|a₀⟩ ⟨(i₁,e₂)|W₂|a₁⟩`, with
mode 1 at index `0`; `conjugateKernel K ρ` is `K ρ K†`, and the sum over `(e₁, e₂)` is the partial
trace over both environments.

**Formalization Note.** The variance of `w·r̂` in this image is the variance in `ρ` of `w·r̂'`,
where `x̂ⱼ' = Wⱼ†(x̂ⱼ ⊗ I)Wⱼ`, `p̂ⱼ' = Wⱼ†(p̂ⱼ ⊗ I)Wⱼ` when `Wⱼ` is onto a subspace `ℓ²(ℕ) ⊗ K`. By the
Stone–von Neumann theorem every Weyl-regular canonical pair on the one-mode space is of this form
(a multiple of the Schrödinger pair), so these images cover the paper's "any local operators
satisfying the commutators"; `Wⱼψ = Uⱼψ ⊗ |0⟩` gives the paper's local unitary `U₁ ⊗ U₂`. -/
noncomputable def localIsometryImage (W1 W2 : Hilbert ℕ →ₗᵢ[ℂ] Hilbert (ℕ × ℕ))
    (ρ : DensityKernel 2) : DensityKernel 2 := fun i j =>
  ∑' e : ℕ × ℕ,
    conjugateKernel
      (fun (q : (ℕ × ℕ) × (ℕ × ℕ)) (a : FockIndex 2) =>
        isometryCoeff W1 q.1 (a 0) * isometryCoeff W2 q.2 (a 1)) ρ
      ((i 0, e.1), (i 1, e.2)) ((j 0, e.1), (j 1, e.2))

end DuanCV.Gauss


