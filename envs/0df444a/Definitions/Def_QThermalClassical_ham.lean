-- Prove2me | Definitions.Def_QThermalClassical_ham
-- name    : QThermalClassical_ham
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:11:28.658212+00:00
-- url     : https://prove2.me/theorems/7504f832-6752-4372-83e9-a5dd59729c87
-- title:
--   Pauli Hamiltonian $H=\sum_a c_aP_a$
-- statement:
--   A **Pauli Hamiltonian** on a register $Q$ is
--   $$
--   H=\sum_{a\in A}c_aP_a,
--   $$
--   where the $P_a$ are distinct non-identity Pauli strings and $c_a\in\mathbb R$ (eq. (5)). It is given by its real coefficient function $c$ on Pauli words: $H=\sum_P c_P\,P$, with label set $A=\{P : c_P\neq0\}$.
--
--   **Formalization Note** Encoding $H$ by a coefficient function makes the strings automatically distinct. The non-identity requirement is the condition $c(I)=0$, imposed where it is needed (it is part of the long-range class).
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), §2.1, eq. (5), p.11

import Mathlib
import Definitions.Def_QThermalClassical_pauliOp

set_option autoImplicit false

namespace QThermalClassical

/-- The Pauli Hamiltonian `H = Σ_{a∈A} c_a P_a` of eq. (5) with real coefficients, given by its
coefficient function `c` on Pauli words; the label set is `A = {P : c P ≠ 0}`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), §2.1, eq. (5), p.11.

**Formalization Note.** Encoding a Hamiltonian by its coefficient function makes the Pauli
strings `P_a` automatically distinct; words with coefficient `0` change neither the operator
nor any of the paper's conditions. The paper's "non-identity" requirement is the separate
condition `c (fun _ => 0) = 0`, stated wherever it is used. -/
def ham {Q : Type} [Fintype Q] [DecidableEq Q] (c : PauliWord Q → ℝ) : Op Q :=
  ∑ P : PauliWord Q, ((c P : ℝ) : ℂ) • pauliOp P

end QThermalClassical


