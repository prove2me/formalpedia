-- Prove2me | Definitions.Def_BoundEntPPT_localOutput
-- name    : BoundEntPPT_localOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:24:49.996579+00:00
-- url     : https://prove2.me/theorems/fb42b571-8d4a-433e-8d71-766d719b6451
-- title:
--   Unnormalized output $\sum_i (A_i\otimes B_i)\,\varrho^{\otimes N}(A_i\otimes B_i)^\dagger$ of a local operation on $N$ copies (Eqs. (4)–(5))
-- statement:
--   Alice holds a finite-dimensional system $\mathcal H_A$ (basis indexed by $I$) and Bob holds $\mathcal H_B$ (basis indexed by $J$). They share $N$ copies of an operator $\varrho$ on $\mathcal H_A\otimes\mathcal H_B$, i.e. $\varrho^{\otimes N}$ on $\mathcal H_A^{\otimes N}\otimes\mathcal H_B^{\otimes N}$, Alice holding all $N$ $A$-systems and Bob all $N$ $B$-systems. Given a finite family of pairs $A_i:\mathcal H_A^{\otimes N}\to\mathcal K$, $B_i:\mathcal H_B^{\otimes N}\to\mathcal L$ ($i=1,\dots,m$) into finite-dimensional output spaces, the **unnormalized output** is
--
--   $$
--   \sigma \;=\; \sum_{i=1}^{m} (A_i\otimes B_i)\,\varrho^{\otimes N}\,(A_i\otimes B_i)^\dagger .
--   $$
--
--   With $\mathcal K=\mathcal L=\mathbb C^2$ this is Eq. (5); the normalized output of Eq. (4) is $\sigma/M$ with $M=\operatorname{Tr}\sigma$, the probability that the operation succeeds. Eq. (4) is "the most general operation producing a two-qubit pair" that Alice and Bob can perform on their $N$ pairs, and it contains every protocol of local operations and classical communication.
--
--   **Formalization Note** $\varrho^{\otimes N}$ is the published grouped tensor power `Information100.P04.copies ρ N` on `(Fin N → I) × (Fin N → J)`, with Alice's $N$ factors first so that $A_i\otimes B_i$ is a local operator. $A_i$ is a matrix whose rows are indexed by the output space. No completeness condition $\sum_i A_i^\dagger A_i\otimes B_i^\dagger B_i\le 1$ is imposed (the paper states none). The factor $1/M$ is dropped, as p.2 prescribes. For $m=0$ the output is $0$.
-- source:
--   M. Horodecki, P. Horodecki, R. Horodecki, Mixed-state entanglement and distillation: is there a "bound" entanglement in nature?, arXiv:quant-ph/9801069v1, p.2, Eqs. (4)–(5)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
open scoped Matrix ComplexOrder

namespace BoundEntPPT

/-- M. Horodecki, P. Horodecki, R. Horodecki, *Mixed-state entanglement and distillation: is there
a "bound" entanglement in nature?*, arXiv:quant-ph/9801069v1, p.2, Eqs. (4)–(5): the unnormalized
output
`ϱ_{2q} = Σ_i A_i ⊗ B_i ϱ^{⊗N} A_i† ⊗ B_i†`
of an operation on `N` copies of `ϱ`, where `A_i` maps Alice's `H_A^{⊗N}` and `B_i` maps Bob's
`H_B^{⊗N}` into the output spaces (`C²` in Eq. (4); "an arbitrary two-component system (not
necessarily 2 × 2 one)" in the generalization of p.2, last paragraph).

**Formalization Note.** `ϱ^{⊗N}` is the published grouped tensor power
`Information100.P04.copies ρ N` on `(Fin N → I) × (Fin N → J)`: Alice's `N` factors first, so that
`A i ⊗ₖ B i` is a local operator. `A i : Matrix K (Fin N → I) ℂ` has the output as its row index.
The family is finite (`Fin m`), as the sum `Σ_i` is; no completeness constraint
`Σ A_i†A_i ⊗ B_i†B_i ≤ 1` is imposed, since the paper states none. The factor `1/M` of Eq. (4) is
omitted, as p.2 prescribes ("For convenience, we will use unnormalized states"); its trace `M` is
the success probability. `ᴴ` is the conjugate transpose (†). At `m = 0` the output is `0`. -/
noncomputable def localOutput {I J K L : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (ρ : Matrix (I × J) (I × J) ℂ) (N : ℕ) {m : ℕ}
    (A : Fin m → Matrix K (Fin N → I) ℂ) (B : Fin m → Matrix L (Fin N → J) ℂ) :
    Matrix (K × L) (K × L) ℂ :=
  ∑ i, Matrix.kronecker (A i) (B i) *
    QAlgorithms.Papers.Independent.Information100.P04.copies ρ N *
    (Matrix.kronecker (A i) (B i))ᴴ

end BoundEntPPT


