-- Prove2me | Definitions.Def_DepthOneQExp_Supplement_tGate
-- name    : DepthOneQExp_Supplement_tGate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:32:54.136209+00:00
-- url     : https://prove2.me/theorems/4607033c-59be-4efa-961f-67d156d12171
-- title:
--   The gate $T = e^{-i\pi Z/8} = \mathrm{diag}(e^{-i\pi/8}, e^{i\pi/8}) \in \mathrm{SU}(2)$
-- statement:
--   The single-qubit gate
--   $$
--   T := e^{-i\pi Z/8} = \begin{pmatrix} e^{-i\pi/8} & 0 \\ 0 & e^{i\pi/8}\end{pmatrix} \in \mathrm{SU}(2),
--   $$
--   as a gate of arity 1. This is the convention fixed throughout §2.4 of the paper. It differs from the more common $\mathrm{diag}(1, e^{i\pi/4})$ by the global phase $e^{i\pi/8}$, and unlike that matrix it has determinant $1$. Its adjoint $T^\dagger = \mathrm{diag}(e^{i\pi/8}, e^{-i\pi/8})$ is the inverse gate.
--
--   $T$ is the only non-Clifford gate in the expander of Theorem 2.17, where $V_1 = T\otimes I_{n-1}$ and $V_2 = T^\dagger\otimes I_{n-1}$.
--
--   **Formalization Note** The gate is a `MITMSynthesis.Gate` of arity 1 (the base mission's gate framework); $|0\rangle$ is the bit string $0$. The adjoint is `MITMSynthesis.Gate.inv tGate`. Unitarity is proved in the module.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), §2.4, p.15 ("we use the convention that T := e^{−iπZ/8} ∈ SU(2)")

import Mathlib
import Definitions.Def_MITMSynthesis_Gate

namespace DepthOneQExp.Supplement

/-- The single-qubit gate `T := e^{−iπZ/8} = diag(e^{−iπ/8}, e^{iπ/8}) ∈ SU(2)` as a gate of arity 1
(Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group and
applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, §2.4, p.15: "Throughout this subsection, we use the convention that `T := e^{−iπZ/8} ∈ SU(2)`").

**Formalization Note** This is the paper's `T`, *not* the usual `diag(1, e^{iπ/4})` (which differs
from it by the global phase `e^{iπ/8}` and has determinant `e^{iπ/4} ≠ 1`). The basis state `|0⟩`
is the function `fun _ => 0 : Fin 1 → Fin 2`. Its adjoint `T† = diag(e^{iπ/8}, e^{−iπ/8})` is
`MITMSynthesis.Gate.inv tGate`. -/
noncomputable def tGate : MITMSynthesis.Gate :=
  ⟨1, one_pos,
    ⟨Matrix.diagonal fun x : MITMSynthesis.Q 1 =>
        if x 0 = 0 then Complex.exp (-(Real.pi / 8 : ℂ) * Complex.I)
        else Complex.exp ((Real.pi / 8 : ℂ) * Complex.I), by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext x
      have hc : ∀ z : ℂ, star (Complex.exp z) = Complex.exp (star z) := fun z => by
        rw [Complex.star_def, ← Complex.exp_conj]
      by_cases h : x 0 = 0 <;> simp only [h, if_true, if_false, Pi.star_apply, hc,
        ← Complex.exp_add] <;> rw [← Complex.exp_zero] <;> congr 1 <;>
        simp [Complex.conj_ofReal]⟩⟩

end DepthOneQExp.Supplement


