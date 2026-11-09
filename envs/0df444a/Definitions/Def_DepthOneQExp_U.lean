-- Prove2me | Definitions.Def_DepthOneQExp_U
-- name    : DepthOneQExp_U
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:47:32.998579+00:00
-- url     : https://prove2.me/theorems/6b2efce8-a1ff-4b7e-83d7-3f52d8b32620
-- title:
--   The sixteen unitaries $U_1,\dots,U_{16}$ of Theorem 2.2
-- statement:
--   For $s\ge1$, the sixteen $3s$-qubit unitaries of Theorem 2.2 (Eqs. (2.1)–(2.6)) are, in the paper's 1-based qubit labels with indices taken periodically mod $3s$:
--
--   1. $U_1 = X\otimes I_{2^{3s-1}}$ and $U_2 = Z\otimes I_{2^{3s-1}}$ (Pauli on qubit 1);
--   2. $U_3=\mathrm{CNOT}_{1,2}$, $U_4=\mathrm{CNOT}_{2,1}$, $U_5=\mathrm{CNOT}_{2,3}$, $U_6=\mathrm{CNOT}_{3,2}$ (tensored with the identity);
--   3. $U_7,\dots,U_{12} = \prod_{i=0}^{s-1}\mathrm{CNOT}_{3i+a,3i+b}$ for $(a,b)=(1,2),(1,3),(2,1),(2,3),(3,1),(3,2)$;
--   4. $$U_{13}=\prod_{i=0}^{s-1}\mathrm{CNOT}_{3i+4,3i+2},\quad U_{14}=\prod_{i=0}^{s-1}\mathrm{CNOT}_{3i+5,3i+1},\quad U_{15}=\prod_{i=0}^{s-1}\mathrm{CNOT}_{3i+5,3i+3},\quad U_{16}=\prod_{i=0}^{s-1}\mathrm{CNOT}_{3i+6,3i+2}.$$
--
--   Here $\mathrm{CNOT}_{a,b}$ is controlled by $a$ and acts on $b$.
--
--   **Formalization Note** `U s k` is $U_{k+1}$. Qubits are 0-based ($p\mapsto (p-1)\bmod 3s$). The matrices are defined as products of register-level permutation and diagonal matrices, not as circuits, so that "each $U_i$ is a depth-1 circuit" is a claim of Theorem 2.2 rather than part of the definition. The paper leaves the order of $U_7,\dots,U_{12}$ among the six pairs unspecified; the order above is lexicographic.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Theorem 2.2, Eqs. (2.1)–(2.6), pp.6–7

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_permToMatrix
import Definitions.Def_DepthOneQExp_xPerm
import Definitions.Def_DepthOneQExp_zMat
import Definitions.Def_DepthOneQExp_cnotPerm

namespace DepthOneQExp

/-- The sixteen `3s`-qubit unitaries `U_1, …, U_16` of Theorem 2.2
(Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group and
applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Eqs. (2.1)–(2.6), pp.6–7),
written in the paper's 1-based qubit labels with periodic indices:

* `U_1 = X ⊗ I`, `U_2 = Z ⊗ I` (Pauli on qubit 1), `U_3 = CNOT_{1,2}`, `U_4 = CNOT_{2,1}`,
  `U_5 = CNOT_{2,3}`, `U_6 = CNOT_{3,2}` (each tensored with the identity);
* `U_7, …, U_12 = ∏_{i=0}^{s−1} CNOT_{3i+a,3i+b}` for `(a, b) = (1,2), (1,3), (2,1), (2,3), (3,1),
  (3,2)`;
* `U_13 = ∏ CNOT_{3i+4,3i+2}`, `U_14 = ∏ CNOT_{3i+5,3i+1}`, `U_15 = ∏ CNOT_{3i+5,3i+3}`,
  `U_16 = ∏ CNOT_{3i+6,3i+2}`, indices mod `3s`.

`U s k` is the paper's `U_{k+1}`.

**Formalization Note** Qubits are 0-based (the paper's qubit `p` is index `(p − 1) mod 3s`), so for
instance `U_13` is the product of `CNOT` with control `3i + 3` and target `3i + 1`, 0-based, mod `3s`.
`CNOT_{a,b}` is controlled by `a` and acts on `b`. The matrices are defined as products of
register-level permutation and diagonal matrices, *not* as circuits: that each is a depth-1 circuit
is a statement (Theorem 2.2). The paper leaves the order of `U_7, …, U_12` among the six pairs
unspecified; the order above is lexicographic. The products over `i` are of commuting gates on
disjoint qubits, so their order does not matter. -/
noncomputable def U (s : ℕ) : Fin 16 → Matrix (MITMSynthesis.Q (3 * s)) (MITMSynthesis.Q (3 * s)) ℂ :=
  let C : ℕ → ℕ → Matrix (MITMSynthesis.Q (3 * s)) (MITMSynthesis.Q (3 * s)) ℂ :=
    fun a b => permToMatrix (cnotPerm (3 * s) a b)
  let L : ℕ → ℕ → Matrix (MITMSynthesis.Q (3 * s)) (MITMSynthesis.Q (3 * s)) ℂ :=
    fun a b => ((List.range s).map fun i => C (3 * i + a) (3 * i + b)).prod
  ![permToMatrix (xPerm (3 * s) 0), zMat (3 * s) 0, C 0 1, C 1 0, C 1 2, C 2 1,
    L 0 1, L 0 2, L 1 0, L 1 2, L 2 0, L 2 1,
    L 3 1, L 4 0, L 4 2, L 5 1]

end DepthOneQExp


