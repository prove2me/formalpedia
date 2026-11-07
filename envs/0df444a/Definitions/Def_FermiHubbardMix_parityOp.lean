-- Prove2me | Definitions.Def_FermiHubbardMix_parityOp
-- name    : FermiHubbardMix_parityOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:39.56854+00:00
-- url     : https://prove2.me/theorems/71fd27c8-5188-40fa-a929-89776d009a2b
-- title:
--   Fock space operators: number $n_k$, parity $\Pi$, even and odd operators, operator norm (annihilation $c_k$ from the published GaussTesting.annihilator)
-- statement:
--   Let $N$ be the number of complex fermionic modes, ordered as $0,1,\dots,N-1$. The Fock space has orthonormal occupation-number basis $\{|s\rangle : s\in\{0,1\}^N\}$, where $s_k=1$ means that mode $k$ is occupied. Operators on it are complex $2^N\times 2^N$ matrices indexed by bitstrings.
--
--   The **annihilation operator** of mode $k$ is the Jordan–Wigner operator
--   $$
--   c_k=\tfrac12\bigl(\gamma_{2k}+i\,\gamma_{2k+1}\bigr)=Z^{\otimes k}\otimes|0\rangle\langle 1|\otimes I,
--   $$
--   where $\gamma_0,\dots,\gamma_{2N-1}$ are the Jordan–Wigner Majorana operators ($\gamma_{2k}=Z^{\otimes k}\otimes X\otimes I$, $\gamma_{2k+1}=Z^{\otimes k}\otimes Y\otimes I$). The operators $c_k$ and $c_k^\dagger$ satisfy the canonical anticommutation relations
--   $$
--   \{c_k,c_l\}=0,\qquad \{c_k,c_l^\dagger\}=\delta_{kl}I .
--   $$
--   The **number operator** is $n_k=c_k^\dagger c_k$ and the **parity operator** is $\Pi=(-1)^{\hat N}$ with $\hat N=\sum_k n_k$; it is diagonal with entry $(-1)^{|s|}$ at $|s\rangle$, $|s|$ the Hamming weight. An operator $A$ is **even** if $\Pi A\Pi=A$ and **odd** if $\Pi A\Pi=-A$ (the parity automorphism $\Theta(A)=\Pi A\Pi$). Finally $\|A\|$ denotes the operator norm.
--
--   These are the basic objects of Part II of the paper: the fermionic Fock space, its CAR operators, parity and the operator norm used in every bound.
--
--   **Formalization Note** $c_k$ is the published definition `GaussTesting.annihilator` (0-based modes, $c_k=\tfrac12(\gamma_{2k}+i\gamma_{2k+1})$), whose Majoranas are the published `FermiCap.Gaussian.majorana`; bit value $1$ at coordinate $k$ means "occupied". The CAR, the identity $c_k=Z^{\otimes k}\otimes|0\rangle\langle1|\otimes I$ and $\Pi=Z^{\otimes N}$ are proved in the mission's verification files.
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), §11.1, p.50; §11.2 and Definition 11.3, p.51; §1.1, p.3; §4, p.15

import Mathlib
import Definitions.Def_FermiCap_Gaussian_Majorana
import Definitions.Def_GaussTesting_annihilator
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

/-- Operators on the Fock space of `N` ordered complex fermionic modes: complex matrices indexed by
occupation bitstrings `Fin N → Fin 2` (the published `FermiCap.Gaussian.Op N`).
Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held
version, sha256 055b8f8f…), §11.1, p.50.

**Formalization Note** The annihilation operator `c_k` of mode `k` is the published
`GaussTesting.annihilator N k = (γ_{2k} + i γ_{2k+1})/2`, built from the published Jordan–Wigner
Majoranas `FermiCap.Gaussian.majorana` (`γ_{2k} = Z^{⊗k} ⊗ X ⊗ 1`, `γ_{2k+1} = Z^{⊗k} ⊗ Y ⊗ 1`), so
`c_k = Z^{⊗k} ⊗ |0⟩⟨1| ⊗ 1`: bit value `1` at coordinate `k` means that mode `k` is occupied. The
modes are ordered by `Fin N`; the paper's "fixed ordering of the modes" of `Λ × [m]` is a bijection
`Λ × Fin m ≃ Fin N` supplied by every later statement. -/
abbrev Op (N : ℕ) := FermiCap.Gaussian.Op N

/-- The number operator `n_k = c_k† c_k`, with `c_k = GaussTesting.annihilator N k`
(arXiv:2604.08408, held version sha256 055b8f8f…, §1.1, p.3, and Example 11.8, p.52). -/
def numOp (N : ℕ) (k : Fin N) : Op N :=
  (GaussTesting.annihilator N k)ᴴ * GaussTesting.annihilator N k

/-- The parity operator `Π = (-1)^{N̂}`, `N̂ = ∑ c_k† c_k` (arXiv:2604.08408, held version sha256
055b8f8f…, §11.2, p.51).

**Formalization Note** `N̂` is diagonal in the occupation basis with eigenvalue the Hamming weight
of the bitstring, so `Π` is the diagonal matrix with entry `(-1)^{|s|}` at `s`. -/
def parityOp (N : ℕ) : Op N :=
  Matrix.diagonal fun s : Fin N → Fin 2 => (-1 : ℂ) ^ (∑ k, (s k : ℕ))

/-- `A` is even: `Θ(A) = Π A Π = A` (arXiv:2604.08408, held version sha256 055b8f8f…,
§11.2 and Definition 11.3, p.51). -/
def IsEven {N : ℕ} (A : Op N) : Prop := parityOp N * A * parityOp N = A

/-- `A` is odd: `Θ(A) = Π A Π = -A` (arXiv:2604.08408, held version sha256 055b8f8f…,
Definition 11.3, p.51). -/
def IsOdd {N : ℕ} (A : Op N) : Prop := parityOp N * A * parityOp N = -A

/-- The operator norm `‖A‖` of an operator on the Fock space, i.e. the norm of `A` as a
continuous linear map of the Euclidean space `ℂ^{2^N}` (arXiv:2604.08408, held version sha256
055b8f8f…, §4, p.15: "For a matrix A, we write ‖A‖ for the operator norm"). -/
def opNorm {N : ℕ} (A : Op N) : ℝ := ‖Matrix.toEuclideanCLM (n := Fin N → Fin 2) (𝕜 := ℂ) A‖

end FermiHubbardMix


