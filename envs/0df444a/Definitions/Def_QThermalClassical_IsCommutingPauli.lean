-- Prove2me | Definitions.Def_QThermalClassical_IsCommutingPauli
-- name    : QThermalClassical_IsCommutingPauli
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:11:34.750755+00:00
-- url     : https://prove2.me/theorems/9812387e-6e9d-4ae2-9f9b-4c295a236205
-- title:
--   Commuting Pauli Hamiltonian
-- statement:
--   A Pauli Hamiltonian $H=\sum_{a\in A}c_aP_a$ is **commuting** if $P_aP_b=P_bP_a$ for all $a,b\in A$, i.e. any two of its terms with nonzero coefficient commute.
--
--   This is the sense of "even if the Hamiltonian is commuting" in Theorem 1(a) and of "commuting Hamiltonian" in Theorem 35.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 1(a), p.14; Theorem 35, p.84

import Mathlib
import Definitions.Def_QThermalClassical_pauliOp

set_option autoImplicit false

namespace QThermalClassical

/-- A Pauli Hamiltonian `Σ_P c_P P` is *commuting* when any two of its terms (Pauli words with
nonzero coefficient) commute.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 1(a), p.14 ("even if the
Hamiltonian is commuting"), and Theorem 35, p.84. -/
def IsCommutingPauli {Q : Type} [Fintype Q] [DecidableEq Q] (c : PauliWord Q → ℝ) : Prop :=
  ∀ P P' : PauliWord Q, c P ≠ 0 → c P' ≠ 0 → Commute (pauliOp P) (pauliOp P')

end QThermalClassical


