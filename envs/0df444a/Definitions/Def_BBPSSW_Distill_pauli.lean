-- Prove2me | Definitions.Def_BBPSSW_Distill_pauli
-- name    : BBPSSW_Distill_pauli
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:32.022068+00:00
-- url     : https://prove2.me/theorems/b10b765e-8607-4394-98dd-ac26cccd0b50
-- title:
--   Pauli matrices $\sigma_x,\sigma_y,\sigma_z$
-- statement:
--   In the basis $\uparrow=0$, $\downarrow=1$ of one spin,
--
--   $$\sigma_x=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad \sigma_y=\begin{pmatrix}0&-i\\ i&0\end{pmatrix},\quad \sigma_z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.$$
--
--   Up to the global phase $-i$, $\sigma_a$ is the rotation of a spin by $\pi$ about the axis $a$ (the paper's "unilateral Pauli rotation" when applied to one particle of a pair).
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 2, unnumbered bullet ("Unilateral Pauli rotations (that is, rotations by π radians about the x, y, or z axis)")

import Mathlib
import Definitions.Def_BBPSSW_Distill_Axis

namespace BBPSSW.Distill

/-- **The Pauli matrices `σx, σy, σz`.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 2 (unnumbered bullet: "Unilateral Pauli rotations (that is, rotations by π radians
about the x, y, or z axis) of one particle"; the operators are written σx, σy, σz).

`pauli .x = [[0, 1], [1, 0]]`, `pauli .y = [[0, −i], [i, 0]]`, `pauli .z = [[1, 0], [0, −1]]`.

**Formalization Note.** Matrices act on one spin in the basis `0` = ↑, `1` = ↓. A rotation by
π about an axis is the corresponding Pauli matrix up to the global phase −i, which the paper
ignores. -/
def pauli : Axis → Matrix (Fin 2) (Fin 2) ℂ
  | .x => !![0, 1; 1, 0]
  | .y => !![0, -Complex.I; Complex.I, 0]
  | .z => !![1, 0; 0, -1]

end BBPSSW.Distill


