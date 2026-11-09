-- Prove2me | Definitions.Def_GoodQLTC_pauliX
-- name    : GoodQLTC_pauliX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:36:32.769044+00:00
-- url     : https://prove2.me/theorems/2c165d01-0217-4594-b69d-aa79f5442e8c
-- title:
--   Pauli operators $X^x$, $Z^z$ and the weight $\mathrm{wt}(X^xZ^z)$
-- statement:
--   Let $\iota$ be a finite set of $N$ qubits and $\mathcal H_N=(\mathbb C^2)^{\otimes N}=\mathbb C^{\mathbb F_2^{\iota}}$ with computational basis $|b\rangle$, $b\in\mathbb F_2^{\iota}$. For $x,z\in\mathbb F_2^{\iota}$ the Pauli operators are
--   $$
--   X^x=\bigotimes_{i}X^{x_i},\qquad Z^z=\bigotimes_i Z^{z_i},\qquad X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
--   $$
--   so that $X^x|b\rangle=|b+x\rangle$ and $Z^z|b\rangle=(-1)^{z\cdot b}|b\rangle$. The weight of $i^cX^xZ^z$ is $\mathrm{wt}=|\mathrm{supp}\,x\cup\mathrm{supp}\,z|$.
--
--   These are the checks of a CSS code and the errors that define the quantum Hamming distance.
--
--   **Formalization Note** Operators are complex matrices indexed by $\mathbb F_2^{\iota}$; the phase $i^c$ does not enter the weight.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §3.2, p.13 (PDF p.16)

import Mathlib

namespace GoodQLTC

/-- **Pauli operators** `X^x`, `Z^z` and the **weight** `wt(X^x Z^z) = |supp x ∪ supp z|` on the
Hilbert space `H_N = (ℂ²)^{⊗N}` of `N` qubits, Gay–Jeronimo, *Asymptotically Good Quantum Locally
Testable Codes*, arXiv:2609.20780 (held version), §3.2, p.13.

The qubits are indexed by a finite type `ι` (`N = |ι|`), and `H_N` is `ℂ^{F_2^ι}` with the
computational basis `|b⟩`, `b : ι → ZMod 2`. `pauliX x` is the matrix of `X^x = ⨂_i X^{x_i}`, which
sends `|b⟩` to `|b + x⟩`; `pauliZ z` is the matrix of `Z^z = ⨂_i Z^{z_i}`, which multiplies `|b⟩` by
`(-1)^{z·b}`.

**Formalization Note.** Operators are matrices indexed by `ι → ZMod 2` (the tensor-product basis);
`X = (0 1; 1 0)` and `Z = (1 0; 0 −1)` give exactly these entries coordinatewise. -/
noncomputable def pauliX {ι : Type} [Fintype ι] [DecidableEq ι] (x : ι → ZMod 2) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  Matrix.of fun b' b => if b' = b + x then 1 else 0

/-- The Pauli `Z^z = ⨂_i Z^{z_i}`: the diagonal matrix with entry `(-1)^{z·b}` at `|b⟩`
(arXiv:2609.20780, §3.2, p.13). -/
noncomputable def pauliZ {ι : Type} [Fintype ι] [DecidableEq ι] (z : ι → ZMod 2) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  Matrix.of fun b' b => if b' = b then (-1 : ℂ) ^ (ZMod.val (z ⬝ᵥ b)) else 0

/-- The weight `wt(i^c X^x Z^z) := |supp x ∪ supp z|` of a Pauli operator (arXiv:2609.20780, §3.2,
p.13); the phase `i^c` does not enter. -/
def pauliWeight {ι : Type} [Fintype ι] (x z : ι → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ 0 ∨ z i ≠ 0).card

end GoodQLTC


