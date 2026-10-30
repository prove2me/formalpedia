-- Prove2me | Definitions.Def_AKNMixed_FQP_padBlank
-- name    : AKNMixed_FQP_padBlank
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:52.229417+00:00
-- url     : https://prove2.me/theorems/721709ba-0dc4-4cd7-81c0-75b82aa955bb
-- title:
--   $\rho\otimes|0\cdots0\rangle\langle0\cdots0|$: a matrix on the first $a$ of $n$ wires, the rest blank
-- statement:
--   For $a\le n$ and an $a$-qubit matrix $\rho$, $\rho\otimes|0^{n-a}\rangle\langle0^{n-a}|$ is the $n$-qubit matrix with $\rho$ on wires $0,\dots,a-1$ and the blank state $|0\rangle$ on wires $a,\dots,n-1$:
--
--   $$(\rho\otimes|0\rangle\langle0|)_{y,z}=\begin{cases}\rho_{y|_{<a},\,z|_{<a}} & \text{if } y_t=z_t=0 \text{ for all } t\ge a,\\ 0&\text{otherwise.}\end{cases}$$
--
--   In Lemma 4, $n=a+b+\max(a,b)$ (the printed $2a+b$ when $b\le a$) and there are $b+\max(a,b)$ blank qubits.
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, Lemma 4, p. 9 (ρ ⊗ |0^{n+m}⟩⟨0^{n+m}|)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace AKNMixed.FQP

open QAlgorithms

/-- **`ρ ⊗ |0…0⟩⟨0…0|`: a matrix on the first `a` of `n` wires, the other wires blank.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1,
Lemma 4, p. 9: "g ∘ ρ = (U_g ∘ (ρ ⊗ |0^{n+m}⟩⟨0^{n+m}|))|_A".

For `h : a ≤ n` and an `a`-qubit matrix `ρ`, `padBlank h ρ` is the `n`-qubit matrix with entry
`ρ (y|_{first a}) (z|_{first a})` when the last `n − a` bits of both `y` and `z` are `0`, and `0`
otherwise.

**Formalization Note.** `ρ` sits on wires `0, …, a − 1` (most significant first) and the blanks
on wires `a, …, n − 1`. In Lemma 4, `n` is `a + b + max a b` (the printed `2a + b` when
`b ≤ a`) and the blanks are `b + max a b` qubits. -/
def padBlank {a n : ℕ} (h : a ≤ n) (ρ : Matrix (Qubits a) (Qubits a) ℂ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y z =>
    if ∀ t : Fin n, a ≤ (t : ℕ) → y t = false ∧ z t = false then
      ρ (fun i => y (Fin.castLE h i)) (fun i => z (Fin.castLE h i))
    else 0

end AKNMixed.FQP


