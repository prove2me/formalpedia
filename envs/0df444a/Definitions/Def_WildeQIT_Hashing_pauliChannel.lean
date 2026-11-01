-- Prove2me | Definitions.Def_WildeQIT_Hashing_pauliChannel
-- name    : WildeQIT_Hashing_pauliChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:21:39.909751+00:00
-- url     : https://prove2.me/theorems/bfb19031-f4cb-4924-8248-235707a2c0d9
-- title:
--   Pauli channel $\rho\mapsto p_I\rho+p_XX\rho X+p_YY\rho Y+p_ZZ\rho Z$
-- statement:
--   Let $p=(p_I,p_X,p_Y,p_Z)$ be a probability vector. The **Pauli channel** with error law $p$ acts on a qubit operator $\rho$ as
--
--   $$
--   \mathcal N_p(\rho)=p_I\,\rho+p_X\,X\rho X+p_Y\,Y\rho Y+p_Z\,Z\rho Z ,
--   $$
--
--   with $X|0\rangle=|1\rangle$, $X|1\rangle=|0\rangle$, $Y|0\rangle=i|1\rangle$, $Y|1\rangle=-i|0\rangle$, $Z|0\rangle=|0\rangle$, $Z|1\rangle=-|1\rangle$: it applies the Pauli error $P$ with probability $p_P$.
--
--   **Formalization Note** The qubit is indexed by `Bool` (`false` is $|0\rangle$); the Paulis are the published `Stabilizer.Pauli` with matrices `Pauli.mat`; $p$ is a `WildeQIT.FinDist` on the four labels.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 24.6.2, p. 674, (24.104); Pauli matrices (24.91)–(24.94), p. 672

import Definitions.Def_QAlgorithms_Defs_QECC
import Definitions.Def_WildeQIT_FinDist

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 24.6.2,
(24.104), p. 674 (the Pauli channel).
-/

namespace WildeQIT.Hashing

open QAlgorithms Stabilizer

/-- **The Pauli channel** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, (24.104), p. 674):
`ρ ↦ p_I ρ + p_X XρX + p_Y YρY + p_Z ZρZ`, with `p = (p_I, p_X, p_Y, p_Z)` a probability vector.

**Formalization Note.** The qubit is indexed by `Bool` (`false = |0⟩`); the one-qubit Paulis
`I, X, Y, Z` are the published `Stabilizer.Pauli` with matrices `Pauli.mat`
(`Y = [[0, −i], [i, 0]]`, so `Y|0⟩ = i|1⟩`, `Y|1⟩ = −i|0⟩` as in (24.93)). The probability vector
is a `FinDist` on the four labels. -/
noncomputable def pauliChannel (p : FinDist Pauli) : Superop Bool Bool :=
  fun ρ => ∑ a : Pauli, (p.prob a : ℂ) • (a.mat * ρ * a.mat)

end WildeQIT.Hashing


