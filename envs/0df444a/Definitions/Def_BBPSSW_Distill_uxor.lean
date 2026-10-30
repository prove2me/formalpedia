-- Prove2me | Definitions.Def_BBPSSW_Distill_uxor
-- name    : BBPSSW_Distill_uxor
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:40.891994+00:00
-- url     : https://prove2.me/theorems/a4a0713f-a0a2-4ec3-826f-6bb41a655e66
-- title:
--   Unilateral quantum XOR $U_{XOR}$, Eq. (5)
-- statement:
--   The quantum XOR (controlled-NOT) on two spins held by one observer flips the target spin $T$ when the source spin $S$ is up:
--
--   $$U_{XOR}=|{\uparrow_S\uparrow_T}\rangle\langle{\uparrow_S\downarrow_T}|+|{\uparrow_S\downarrow_T}\rangle\langle{\uparrow_S\uparrow_T}|+|{\downarrow_S\downarrow_T}\rangle\langle{\downarrow_S\downarrow_T}|+|{\downarrow_S\uparrow_T}\rangle\langle{\downarrow_S\uparrow_T}|.$$
--
--   **Formalization Note** The index is (source, target) with $0=\uparrow$, $1=\downarrow$; the four matrix units are the four terms of Eq. (5), so the control is on $\uparrow$, as printed.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, Eq. (5), p. 2

import Mathlib

namespace BBPSSW.Distill

/-- **The unilateral quantum XOR (controlled-NOT), Eq. (5).**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, Eq. (5), p. 2: "The unilateral quantum-XOR is an operation on two qubits held by the same
observer which conditionally flips the second or “target” spin if the first or “source” spin is
up, and does nothing otherwise. As a unitary operator it is expressed
U_XOR = |↑S↑T⟩⟨↑S↓T| + |↑S↓T⟩⟨↑S↑T| + |↓S↓T⟩⟨↓S↓T| + |↓S↑T⟩⟨↓S↑T|. (5)"

`Matrix.single i j 1` is the matrix unit |i⟩⟨j|; the four terms are those of Eq. (5).

**Formalization Note.** The index is (source spin, target spin), with `0` = ↑ and `1` = ↓, so
the target is flipped exactly when the source is ↑ = `0`, as Eq. (5) writes it. -/
def uxor : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.single (0, 0) (0, 1) 1 + Matrix.single (0, 1) (0, 0) 1 +
    Matrix.single (1, 1) (1, 1) 1 + Matrix.single (1, 0) (1, 0) 1

end BBPSSW.Distill


