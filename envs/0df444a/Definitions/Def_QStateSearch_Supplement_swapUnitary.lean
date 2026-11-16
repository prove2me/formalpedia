-- Prove2me | Definitions.Def_QStateSearch_Supplement_swapUnitary
-- name    : QStateSearch_Supplement_swapUnitary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:21:44.996557+00:00
-- url     : https://prove2.me/theorems/607ca6b2-6f5f-46ef-a327-3d73ba6ed7b1
-- title:
--   $S(a)=|a\rangle\langle0|+|0\rangle\langle a|+I-|0\rangle\langle0|-|a\rangle\langle a|$
-- statement:
--   For a vector $|a\rangle$ on $k$ qubits and the all-zero basis state $|0\rangle$,
--   $$S(a)=|a\rangle\langle0|+|0\rangle\langle a|+I-|0\rangle\langle0|-|a\rangle\langle a| \qquad\text{(Eq. (5))}.$$
--   For a unit vector $|a\rangle\perp|0\rangle$ this unitary swaps $|0\rangle$ and $|a\rangle$ and fixes their common orthogonal complement; it is the sampler gate of Section 6.
--
--   **Formalization Note** The matrix is defined for every vector; the vectors it is used with, $|Y_{n,t}\rangle$ and $|N_n\rangle$, end in $|1\rangle$ and are orthogonal to $|0\rangle$.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Eq. (5), p.17

import Mathlib

set_option autoImplicit false

namespace QStateSearch.Supplement

/-- For a vector `|a⟩` of `k` qubits, `S(a) = |a⟩⟨0| + |0⟩⟨a| + I − |0⟩⟨0| − |a⟩⟨a|`, where `|0⟩` is
the all-zero basis state.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Eq. (5), p.17: "For a unit vector |a⟩ orthogonal to |0⟩, write
S(a) = |a⟩⟨0| + |0⟩⟨a| + I − |0⟩⟨0| − |a⟩⟨a|. This unitary swaps |0⟩ and |a⟩ and fixes their
common orthogonal complement."

**Formalization Note.** The matrix is defined for every vector; it is the stated unitary when
`a` is a unit vector orthogonal to `|0⟩`, which holds for the states `|Y_{n,t}⟩` and `|N_n⟩` it is
used with (their last qubit is `|1⟩`). -/
noncomputable def swapUnitary {k : ℕ} (a : (Fin k → Bool) → ℂ) :
    Matrix (Fin k → Bool) (Fin k → Bool) ℂ :=
  let e0 : (Fin k → Bool) → ℂ := fun z => if z = fun _ => false then 1 else 0
  Matrix.vecMulVec a (star e0) + Matrix.vecMulVec e0 (star a) + 1 -
    Matrix.vecMulVec e0 (star e0) - Matrix.vecMulVec a (star a)

end QStateSearch.Supplement


