-- Prove2me | Definitions.Def_ICSCompute_cj
-- name    : ICSCompute_cj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:45:54.255344+00:00
-- url     : https://prove2.me/theorems/b708e28c-a237-4659-8f6c-d7bc9b7310d8
-- title:
--   Choi–Jamiołkowski operator $\mathrm{CJ}(\mathcal C)$ and its inverse $\mathrm{CJ}^{-1}$
-- statement:
--   For a linear map $\mathcal C$ from $\mathcal L(H_0)$ to $\mathcal L(H_1)$ the **Choi–Jamiołkowski operator** is
--   $$\mathrm{CJ}(\mathcal C) := \sum_{x,y} |x\rangle\langle y| \otimes \mathcal C(|x\rangle\langle y|) \in \mathcal L(H_0\otimes H_1),$$
--   with the input register first. Conversely, for $M\in\mathcal L(H_0\otimes H_1)$ the **inverse CJ transformation** is the linear map
--   $$\big[\mathrm{CJ}^{-1}(M,H_0,H_1)\big](X) := \operatorname{Tr}_{H_0}\big((X^{\mathsf T}\otimes I_{\mathcal L(H_1)})\,M\big),$$
--   where $X^{\mathsf T}$ is the transpose in the computational basis of $H_0$.
--
--   A process matrix is the CJ operator of the circuit's channel, and the map it induces after connecting local channels is read off with $\mathrm{CJ}^{-1}$.
--
--   **Formalization Note** $|x\rangle\langle y|$ is `Matrix.single x y 1`; the spaces $H_0, H_1$ of $\mathrm{CJ}^{-1}$ are fixed by the product index type of $M$ (Remark 3.1). The two definitions are mutually inverse (checked in the mission's verification file, not uploaded).
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), Definitions 3.14–3.15, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_ICSCompute_ptraceR

namespace ICSCompute

/-- **Choi–Jamiołkowski operator** (Shmueli, *What Can Be Computed with Indefinite Causal
Structure?*, arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606, Definition 3.14,
p.17 (PDF p.19)): for `C ∈ L(L(H₀), L(H₁))`,
`CJ(C) := ∑_{x,y} |x⟩⟨y| ⊗ C(|x⟩⟨y|) ∈ L(H₀ ⊗ H₁)`.

**Formalization Note** The input register `H₀` is the first tensor factor; `|x⟩⟨y|` is
`Matrix.single x y 1`. The `((x, k), (y, k'))` entry of `CJ(C)` is `C(|x⟩⟨y|) k k'`. -/
def cj {ι κ : Type*} [DecidableEq ι] (C : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    Matrix (ι × κ) (ι × κ) ℂ :=
  Matrix.of fun a b => C (Matrix.single a.1 b.1 1) a.2 b.2

/-- **Inverse Choi–Jamiołkowski transformation** (Shmueli, arXiv:2610.40573, Definition 3.15,
p.17 (PDF p.19)): for `M ∈ L(H₀ ⊗ H₁)`, the linear map `CJ⁻¹(M, H₀, H₁) ∈ L(L(H₀), L(H₁))` with
`[CJ⁻¹(M, H₀, H₁)](X) = Tr_{H₀}((Xᵀ ⊗ I_{L(H₁)}) · M)`, where `Xᵀ` is the transpose in the
computational basis of `H₀`.

**Formalization Note** The spaces `H₀`, `H₁` are fixed by the index type `ι × κ` of `M`
(Remark 3.1); the partial trace is `ptraceR` over the first factor (Definition 3.10). -/
def cjInv {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix (ι × κ) (ι × κ) ℂ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ where
  toFun X := ptraceR (Matrix.kronecker X.transpose (1 : Matrix κ κ ℂ) * M)
  map_add' X Y := by
    ext k k'
    simp [ptraceR, Matrix.transpose_add, Matrix.add_kronecker, Matrix.add_mul,
      Finset.sum_add_distrib]
  map_smul' c X := by
    ext k k'
    simp [ptraceR, Matrix.transpose_smul, Matrix.smul_kronecker, Matrix.smul_mul,
      Finset.mul_sum]

end ICSCompute


