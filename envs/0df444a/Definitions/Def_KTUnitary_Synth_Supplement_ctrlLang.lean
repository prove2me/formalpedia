-- Prove2me | Definitions.Def_KTUnitary_Synth_Supplement_ctrlLang
-- name    : KTUnitary_Synth_Supplement_ctrlLang
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:15:03.949411+00:00
-- url     : https://prove2.me/theorems/28bf3cea-29ba-4e64-80a3-23904da5f0bb
-- title:
--   The controlled unitary language $c\mathcal U$
-- statement:
--   For a unitary language $\mathcal U=\{U_n\}_{n\in\mathbb N}$, $c\mathcal U$ is the unitary language whose member on $n+1$ qubits is the controlled unitary
--   $$cU_n=|0\rangle\langle 0|\otimes I+|1\rangle\langle 1|\otimes U_n,$$
--   with the control on the first qubit and $U_n$ acting on the remaining $n$ qubits.
--
--   Proposition 5.4 shows that the clean classes are closed under $\mathcal U\mapsto c\mathcal U$; Theorem 5.22 characterizes the clean classes as the languages whose controlled version lies in the projective classes.
--
--   **Formalization Note** The member on $0$ qubits, which the paper does not define, is the $1\times 1$ identity. The control is the first wire; since circuits may act on any wires, its position does not affect membership in any class.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Proposition 5.4, p. 17; Theorem 5.22, p. 23

import Mathlib
import Definitions.Def_KTUnitary_Synth_ULang
import Definitions.Def_KTUnitary_Synth_ctrlMat

open QAlgorithms.Complexity

namespace KTUnitary.Synth.Supplement

/-- **The controlled unitary language `c𝒰`** (Kretschmer, Tang, *Unitary Complexity in Polynomial
Space*, arXiv:2610.03705 (revision of 2026-10-31), Proposition 5.4, p. 17, and Theorem 5.22, p. 23):
for `𝒰 = {U_n}`, the unitary language whose member on `n + 1` qubits is the controlled unitary
`cU_n = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U_n` (published `KTUnitary.Synth.ctrlMat`, control qubit on wire `0`,
`U_n` on wires `1, …, n`).

**Formalization Note** The member on `0` qubits, which the paper does not define, is the `1 × 1`
identity. Every `cU_n` is unitary, so the identity branch of `ULang.ofMatrices` is never taken on
positive lengths. The control is the first wire; since circuits may act on any wires, the position
of the control does not change membership in any class of the mission. -/
noncomputable def ctrlLang (U : ULang) : ULang :=
  ULang.ofMatrices fun k =>
    match k with
    | 0 => 1
    | n + 1 => ctrlMat (U n : Matrix (Bits n) (Bits n) ℂ)

end KTUnitary.Synth.Supplement


