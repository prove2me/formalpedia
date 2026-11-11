-- Prove2me | Definitions.Def_StabTestMem_ROp
-- name    : StabTestMem_ROp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:21.763377+00:00
-- url     : https://prove2.me/theorems/1364968a-0331-499f-af19-a2a966f20e7e
-- title:
--   Representation $R(O)=r(O)^{\otimes n}$ on $t$ copies
-- statement:
--   For $O\in\mathbb F_2^{t\times t}$, write a basis state $|x_1\rangle\otimes\cdots\otimes|x_t\rangle$ of $t$ copies of $n$ qubits as the matrix $X\in\mathbb F_2^{t\times n}$ with rows $x_1,\dots,x_t$. Then
--
--   $$R(O)\,|X\rangle=|OX\rangle,$$
--
--   i.e. $R(O)=r(O)^{\otimes n}$ with $r(O)|x\rangle=|Ox\rangle$ acting transversally on the $t$ qubits at each position. For $O\in\mathcal O_t$ it permutes the basis.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), §2.3, Eqs. (19)–(21), p. 16

import Definitions.Def_QAlgorithms_Defs_Basic

namespace StabTestMem

open QAlgorithms

/-- **The representation `R(O) = r(O)^{⊗n}` of a `t × t` matrix on `t` copies of `n` qubits.**
Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), §2.3, Eqs. (19)–(21), p. 16: "r(O)|x⟩ = |Ox⟩ … R(O) := r(O)^{⊗n}, where r(O) is understood to
act transversally on a collection of t qubits, one from each copy … associate a matrix X ∈ F_2^{t×n}
[with rows x_1, …, x_t]. Then, R(O) acts by permuting these basis states according to OX."

A basis state of the `t`-copy register is `X : Fin t → Qubits n`, read as the `t × n` bit matrix
whose row `i` is copy `i`. `R(O)` has entry `1` in row `Y`, column `X` iff `Y = O X` (matrix
product over `F₂`), i.e. `R(O)|X⟩ = |OX⟩`. -/
noncomputable def ROp {n t : ℕ} (O : Matrix (Fin t) (Fin t) (ZMod 2)) :
    Matrix (Fin t → Qubits n) (Fin t → Qubits n) ℂ :=
  Matrix.of fun Y X =>
    if Y = (fun i j => decide (∑ l, O i l * (if X l j then (1 : ZMod 2) else 0) = 1)) then 1
    else 0

end StabTestMem


