-- Prove2me | Definitions.Def_SingleInteraction_hSIH
-- name    : SingleInteraction_hSIH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:54:12.853805+00:00
-- url     : https://prove2.me/theorems/165aa04b-f2bb-44ff-abf0-5c2db0b7d4ef
-- title:
--   The interaction $h=Z\otimes Z+X\otimes Y-Y\otimes X$ of eq. (30)
-- statement:
--   The fixed two-qubit interaction of Theorem 60,
--
--   $$h=Z\otimes Z+X\otimes Y-Y\otimes X,$$
--
--   with the Pauli matrices $X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$, $Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix}$, $Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}$. The order of the tensor factors matters: $h_{u,v}=Z_uZ_v+D_{uv}$ and $h_{v,u}=Z_uZ_v-D_{uv}$ with $D_{uv}=X_uY_v-Y_uX_v$, so $h_{u,v}+h_{v,u}=2Z_uZ_v$. Equivalently $h=4\Pi-3I$ with $\Pi=I-|\psi\rangle\langle\psi|$, $|\psi\rangle=(|01\rangle+i|10\rangle)/\sqrt2$ (Corollary 62).
--
--   **Formalization Note** The Pauli matrices are the published `MIPRE.LCS.Pauli.X`, `Y`, `Z`.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Theorem 60, p.55, eq. (30)

import Mathlib
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_SingleInteraction_twoQubit

namespace SingleInteraction

/-- The fixed two-qubit interaction of eq. (30) (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), Theorem 60, p.55):
`h = Z ⊗ Z + X ⊗ Y − Y ⊗ X`.

**Formalization Note** The Pauli matrices are the published `MIPRE.LCS.Pauli.X`, `Y`, `Z`, with
`X = [[0, 1], [1, 0]]`, `Y = [[0, −i], [i, 0]]`, `Z = diag(1, −1)`. The first tensor factor acts on
qubit `0` (see `twoQubit`), so `X ⊗ Y` is `X` on the first qubit and `Y` on the second. -/
def hSIH : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  twoQubit MIPRE.LCS.Pauli.Z MIPRE.LCS.Pauli.Z + twoQubit MIPRE.LCS.Pauli.X MIPRE.LCS.Pauli.Y -
    twoQubit MIPRE.LCS.Pauli.Y MIPRE.LCS.Pauli.X

end SingleInteraction


