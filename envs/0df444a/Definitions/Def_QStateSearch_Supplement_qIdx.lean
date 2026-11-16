-- Prove2me | Definitions.Def_QStateSearch_Supplement_qIdx
-- name    : QStateSearch_Supplement_qIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:06:20.912345+00:00
-- url     : https://prove2.me/theorems/9d225cec-adcd-46ff-98ab-8678507776b7
-- title:
--   Identification of $\{0,1\}^n$ with $[2^n]$
-- statement:
--   The bijection $\{0,1\}^n\cong[2^n]$ that sends a bit string to the number whose binary digit of weight $2^i$ is bit $i$.
--
--   It identifies an $n$-qubit pure state with a vector of $\mathbb C^{2^n}$, the space $\mathbb C^D$, $D=2^n$, of the base mission, so that the published reflection $R_\psi$ can be used as an $n$-qubit gate.
--
--   **Formalization Note** Any fixed bijection would do: it is only used to transport arbitrary states.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 5, pp.14–15

import Mathlib

set_option autoImplicit false

namespace QStateSearch.Supplement

/-- The identification of the computational basis `{0,1}^n` of `n` qubits with `[2^n]`, so
that an `n`-qubit pure state is a vector of `ℂ^{2^n}` (the `D = 2^n` of the base mission).

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 5, p.14 ("an n-qubit pure state |ψ_n⟩", "D = 2^{n_i}", p.15).

**Formalization Note.** Bit `i` of a basis state is digit `i` (weight `2^i`) of its index
(Mathlib's `finFunctionFinEquiv`, with `false ↦ 0`, `true ↦ 1`). Any fixed bijection would do:
the states it is used with are arbitrary. -/
def qIdx (n : ℕ) : (Fin n → Bool) ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finFunctionFinEquiv

end QStateSearch.Supplement


