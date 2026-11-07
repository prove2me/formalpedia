-- Prove2me | Definitions.Def_PRUPermLayer_productLayer
-- name    : PRUPermLayer_productLayer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:55.003017+00:00
-- url     : https://prove2.me/theorems/094adc03-8532-4328-8a6f-03834fcdd8f9
-- title:
--   Tensor product $C_1 \otimes \cdots \otimes C_n$ of single-qubit operators
-- statement:
--   For single-qubit operators $C_1, \dots, C_n$ (complex $2\times 2$ matrices), the operator $C_1 \otimes \cdots \otimes C_n$ on $(\mathbb C^2)^{\otimes n} = \mathbb C^N$, $N = 2^n$, has matrix entries
--   $$
--   \langle x | C_1 \otimes \cdots \otimes C_n | y\rangle = \prod_{k=1}^n \langle x_k | C_k | y_k\rangle ,
--   $$
--   where $x_k, y_k \in \{0,1\}$ are the $k$-th bits of the labels $x, y$.
--
--   **Formalization Note** The label $x \in \{0,\dots,N-1\}$ is read as an $n$-bit string, most significant bit first, and factor $C_k$ acts on bit $k$ of that string. In every use the factors are independent and identically distributed, so the choice of wire order does not change any law.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §1.1, p.1 (PDF p.3); §2.2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace PRUPermLayer

/-- The tensor product `C₁ ⊗ ⋯ ⊗ Cₙ` of `n` single-qubit operators, as an operator on `ℂ^N`,
`N = 2ⁿ` (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §1.1, p.1 (PDF p.3) and §2.2, p.9 (PDF p.11): "the layer L = C1 ⊗ · · · ⊗ Cn").
Its `(x, y)` entry is `∏ₖ Cₖ(x_k, y_k)`, where `x_k` is bit `k` of the label `x`.

**Formalization Note** The label `x : Fin (2 ^ n)` is read as the bit string
`(QAlgorithms.bitsEquivFin n).symm x`; factor `k : Fin n` (the source's `C_{k+1}`) acts on wire `k`
of that string, wire `0` being the most significant bit. Every use draws the factors i.i.d., so the
choice of wire order changes no law. -/
noncomputable def productLayer {n : ℕ} (C : Fin n → Matrix Bool Bool ℂ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.of fun x y =>
    ∏ k, C k ((QAlgorithms.bitsEquivFin n).symm x k) ((QAlgorithms.bitsEquivFin n).symm y k)

end PRUPermLayer


