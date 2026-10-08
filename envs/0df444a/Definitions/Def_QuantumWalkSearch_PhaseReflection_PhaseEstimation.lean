-- Prove2me | Definitions.Def_QuantumWalkSearch_PhaseReflection_PhaseEstimation
-- name    : QuantumWalkSearch_PhaseReflection_PhaseEstimation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:40:37.349378+00:00
-- url     : https://prove2.me/theorems/b8ce9aba-bed6-48d5-8aa4-18ab8e99806f
-- title:
--   The phase-estimation circuit $C(U)=(\mathrm{Id}\otimes F^\dagger)\big(\sum_j U^j\otimes|j\rangle\langle j|\big)(\mathrm{Id}\otimes H^{\otimes s})$
-- statement:
--   Let $U$ be a $d\times d$ complex matrix acting on $\mathbb C^\iota$ ($\iota$ a finite index set) and $s\ge 0$ an integer. The ancilla register is $\mathbb C^{2^s}$, with basis $|j\rangle$, $0\le j<2^s$, $j$ read as an $s$-bit string $j_{s-1}\cdots j_0$. The **Walsh–Hadamard matrix** and the **quantum Fourier transform** are
--   $$(H^{\otimes s})_{jj'}=2^{-s/2}(-1)^{\sum_{b<s} j_b j'_b},\qquad F_{jk}=2^{-s/2}\,e^{2\pi i\,jk/2^s}.$$
--   The **phase-estimation circuit** of Cleve, Ekert, Macchiavello and Mosca on $\mathbb C^\iota\otimes\mathbb C^{2^s}$ is
--   $$C(U)=(\mathrm{Id}\otimes F^\dagger)\cdot\Big(\sum_{j<2^s}U^j\otimes|j\rangle\langle j|\Big)\cdot(\mathrm{Id}\otimes H^{\otimes s}).$$
--   The middle factor is the product of the controlled operators $c\text{-}U^{2^\ell}$, $\ell<s$ (bit $\ell$ of the ancilla controls $U^{2^\ell}$), written as one block-diagonal sum.
--
--   The file also names the product vector $|\psi\rangle|\omega\rangle$ (coordinates $\psi_i\omega_j$) and the vector $|\psi\rangle|0\rangle$ of a system state with the ancilla in its all-zeros basis state.
--
--   The circuit is the subroutine of Theorem 5 that the paper cites from [14]; the reflection circuit $R(P)$ of Theorem 6 is built from $k$ copies of it applied to the quantum walk.
--
--   **Formalization Note** The paper states Theorem 5 for $U$ of dimension $2^m\times 2^m$ and does not write the circuit out; here $C(U)$ is the standard circuit, defined for any finite index set $\iota$, as a matrix indexed by `ι × Fin (2^s)` (system register first). Gate counts are not modelled.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 9, Theorem 5 (circuit C(U), cited from Cleve, Ekert, Macchiavello, Mosca [14])

import Mathlib
noncomputable section

namespace QuantumWalkSearch.PhaseReflection

/-- The `s`-qubit Walsh–Hadamard matrix `H^{⊗s}` on `ℂ^{2^s}`, indexed by `Fin (2^s)` (a basis
state `|j⟩` is the binary string of `j`): `(H^{⊗s})_{jj'} = 2^{−s/2} (−1)^{Σ_b j_b j'_b}`, where
`j_b` is bit `b` of `j`. -/
def hadamardMatrix (s : ℕ) : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℂ :=
  fun j j' => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ s *
    ∏ b ∈ Finset.range s,
      (if (j : ℕ).testBit b && (j' : ℕ).testBit b then (-1 : ℂ) else 1)

/-- The `2^s`-point quantum Fourier transform `F`, `F_{jk} = 2^{−s/2} e^{2πi jk / 2^s}`. -/
def qftMatrix (s : ℕ) : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℂ :=
  fun j k => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ s *
    Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ) : ℂ) / (2 ^ s : ℂ))

/-- The controlled powers `Σ_{j < 2^s} U^j ⊗ |j⟩⟨j|` on `ℂ^ι ⊗ ℂ^{2^s}` (index `ι × Fin (2^s)`):
the product of the controlled operators `c-U^{2^ℓ}`, `ℓ < s`, written block-diagonally. -/
def controlledPowers {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (s : ℕ) :
    Matrix (ι × Fin (2 ^ s)) (ι × Fin (2 ^ s)) ℂ :=
  fun p q => if p.2 = q.2 then (U ^ (p.2 : ℕ)) p.1 q.1 else 0

/-- The phase-estimation circuit `C(U) = (Id ⊗ F†) · (Σ_j U^j ⊗ |j⟩⟨j|) · (Id ⊗ H^{⊗s})` of
Cleve, Ekert, Macchiavello and Mosca, acting on `ℂ^ι ⊗ ℂ^{2^s}` (system register first, the
`s`-qubit ancilla register second). -/
def phaseEstimation {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (s : ℕ) :
    Matrix (ι × Fin (2 ^ s)) (ι × Fin (2 ^ s)) ℂ :=
  Matrix.kroneckerMap (· * ·) (1 : Matrix ι ι ℂ) (qftMatrix s).conjTranspose *
    controlledPowers U s *
    Matrix.kroneckerMap (· * ·) (1 : Matrix ι ι ℂ) (hadamardMatrix s)

/-- The product vector `|ψ⟩|ω⟩ ∈ ℂ^ι ⊗ ℂ^κ`, with coordinates `ψ_i ω_j`. -/
def tensorVec {ι κ : Type*} (ψ : EuclideanSpace ℂ ι) (ω : EuclideanSpace ℂ κ) :
    EuclideanSpace ℂ (ι × κ) :=
  WithLp.toLp 2 fun p => ψ p.1 * ω p.2

/-- The vector `|ψ⟩|0⟩ ∈ ℂ^ι ⊗ ℂ^κ`, where `0 : κ` labels the all-zeros ancilla basis state. -/
def tensorZero {ι κ : Type*} [Zero κ] [DecidableEq κ] (ψ : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ (ι × κ) :=
  WithLp.toLp 2 fun p => if p.2 = 0 then ψ p.1 else 0

end QuantumWalkSearch.PhaseReflection


