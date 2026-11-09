-- Prove2me | Definitions.Def_DepthOneQExp_cnotU
-- name    : DepthOneQExp_cnotU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:49:55.55934+00:00
-- url     : https://prove2.me/theorems/ae0a8396-1d08-4fad-a998-699eab70848c
-- title:
--   $U_3,\dots,U_{16}$ as elements of the CNOT group $G_{3s}$
-- statement:
--   The unitaries $U_3,\dots,U_{16}$ of Theorem 2.2 are products of CNOT gates and hence elements of $G_{3s}$; Theorem 2.3 averages a representation of $G_{3s}$ over them. `cnotU s k` is the element of $G_{3s}$ (a permutation of the computational basis) whose permutation matrix is $U_{k+3}$, with the same qubit conventions and the same order of $U_7,\dots,U_{12}$ as the definition of the $U_i$.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Theorem 2.2, Eqs. (2.2)–(2.6), pp.6–7; Theorem 2.3, p.8

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_cnotPerm
import Definitions.Def_DepthOneQExp_cnotGroup

namespace DepthOneQExp

/-- The unitaries `U_3, …, U_16` of Theorem 2.2 as elements of the CNOT group `G_{3s}`
(Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group and
applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Eqs. (2.2)–(2.6), pp.6–7,
used as elements of `G_{3s}` in Theorem 2.3, p.8): `cnotU s k` is the permutation of the
computational basis whose matrix is `U_{k+3}`, i.e. `permToMatrix (cnotU s k) = U s (k + 2)`.

**Formalization Note** Same 0-based periodic qubit indices and the same order of `U_7, …, U_12` as
`U`. Each entry is a product of `CNOT` permutations, which lie in `G_{3s}`. -/
def cnotU (s : ℕ) : Fin 14 → cnotGroup (3 * s) :=
  let C : ℕ → ℕ → cnotGroup (3 * s) :=
    fun a b => ⟨cnotPerm (3 * s) a b, cnotPerm_mem_cnotGroup (3 * s) a b⟩
  let L : ℕ → ℕ → cnotGroup (3 * s) :=
    fun a b => ((List.range s).map fun i => C (3 * i + a) (3 * i + b)).prod
  ![C 0 1, C 1 0, C 1 2, C 2 1,
    L 0 1, L 0 2, L 1 0, L 1 2, L 2 0, L 2 1,
    L 3 1, L 4 0, L 4 2, L 5 1]

end DepthOneQExp


