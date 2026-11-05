-- Prove2me | Definitions.Def_BaconOQEC_pauliXZ
-- name    : BaconOQEC_pauliXZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:36.136352+00:00
-- url     : https://prove2.me/theorems/252e0204-fb47-4237-a020-9fb8b38995b8
-- title:
--   Pauli operator $P(a,b) = \prod_{i,j} X_{i,j}^{a_{i,j}} Z_{i,j}^{b_{i,j}}$
-- statement:
--   For two $n\times n$ bit matrices $a, b$ the Pauli operator $P(a,b)$ on the $n^2$ lattice qubits is
--
--   $$
--   P(a,b) = \prod_{i,j=1}^n X_{i,j}^{a_{i,j}} Z_{i,j}^{b_{i,j}},
--   $$
--
--   with $X = \begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $Z = \begin{pmatrix}1&0\\0&-1\end{pmatrix}$. It acts as $X$ on the sites with $a_{i,j}=1, b_{i,j}=0$, as $Z$ on those with $a_{i,j}=0, b_{i,j}=1$, as the product $XZ = \begin{pmatrix}0&-1\\1&0\end{pmatrix}$ on those with $a_{i,j}=b_{i,j}=1$, and as the identity elsewhere. Every Pauli operator on the lattice is $i^\varphi P(a,b)$ for some phase.
--
--   **Formalization Note** The matrix is the published tensor product `QAlgorithms.kronAll` of one $2\times 2$ factor per wire, the factor on wire $w$ being $X^{a_{ij}}Z^{b_{ij}}$ for the site $(i,j)$ with $w = \mathrm{site}(i,j)$, built from the published `QAlgorithms.pauliX`, `pauliZ` (basis bit `false` is $|0\rangle$). The paper calls the factor $XZ$ both "$iY$" (display (6), which prints exactly this matrix) and "$-iY$" (display (7)); the product $X^aZ^b$ itself is what (7) defines, and no extra phase is attached.
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.A, eqs. (6)–(7), pp.3–4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BinaryStabilizer
import Definitions.Def_BaconOQEC_Bits

open QAlgorithms

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.A, eq. (7), p.4: the Pauli operator on the `n²` qubits of the lattice
labelled by two bit matrices,
"P(a, b) = ∏_{i,j=1}^n X_{i,j}^{a_{i,j}} Z_{i,j}^{b_{i,j}}", i.e. `X` on the sites with
`a_{i,j} = 1` only, `Z` on the sites with `b_{i,j} = 1` only, and the product `XZ` on the sites with
`a_{i,j} = b_{i,j} = 1`.

**Formalization Note.** The register is the published `QAlgorithms.Qubits ((m + 1) * (m + 1))`
(`n = m + 1`), and the matrix is the published tensor product `QAlgorithms.kronAll` of one
single-qubit factor per wire. The factor on wire `w` belongs to the site
`(i, j) = finProdFinEquiv.symm w` (the inverse of `BaconOQEC.site`), and is the matrix product
`X^{a_{ij}} Z^{b_{ij}}` of the published `QAlgorithms.pauliX = [[0,1],[1,0]]` and
`QAlgorithms.pauliZ = diag(1, −1)` (basis bit `false` is `|0⟩`), exactly the product of (7). On a site
with `a = b = 1` the factor is `XZ = [[0,−1],[1,0]]`: the matrix (6) prints as "iY" and (7) calls
"−iY". The paper's two labels differ by a sign; the product `X^a Z^b` itself is unambiguous. No
further phase is attached: `P(a, b)` has phase `+1` as written in (7). -/
noncomputable def pauliXZ {m : ℕ} (a b : Bits m) :
    Matrix (Qubits ((m + 1) * (m + 1))) (Qubits ((m + 1) * (m + 1))) ℂ :=
  kronAll fun w =>
    (if a (finProdFinEquiv.symm w).1 (finProdFinEquiv.symm w).2 = 1 then pauliX else 1) *
      (if b (finProdFinEquiv.symm w).1 (finProdFinEquiv.symm w).2 = 1 then pauliZ else 1)

end BaconOQEC


