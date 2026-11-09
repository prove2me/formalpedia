-- Prove2me | Definitions.Def_GoodQLTC_codeSpace
-- name    : GoodQLTC_codeSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:40:30.28246+00:00
-- url     : https://prove2.me/theorems/890ec3d7-b38e-4927-ab48-3c995e8cf882
-- title:
--   Code space $Q\subseteq\mathcal H_N$ of a CSS code
-- statement:
--   The **code space** $Q\subseteq\mathcal H_N$ of the CSS code $(H_X,H_Z)$ is the common $+1$ eigenspace of all checks:
--   $$
--   Q=\{\psi\in\mathcal H_N:\ X^{h^X_a}\psi=\psi\ \text{for all }a,\ Z^{h^Z_b}\psi=\psi\ \text{for all }b\}.
--   $$
--
--   It is the space whose distance operator $D_Q$ and logical dimension the main theorem controls.
--
--   **Formalization Note** A subspace of `EuclideanSpace ℂ (ι → ZMod 2)`; matrices act through `Matrix.toEuclideanLin`.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §3.2, p.13 (PDF p.16)

import Mathlib
import Definitions.Def_GoodQLTC_pauliX

namespace GoodQLTC

/-- The **code space** `Q ⊆ H_N` of the CSS code `(H_X, H_Z)`, Gay–Jeronimo, arXiv:2609.20780
(held version), §3.2, p.13: the common `+1` eigenspace of the checks `X^{h^X_a}` (rows `h^X_a` of
`H_X`) and `Z^{h^Z_b}` (rows `h^Z_b` of `H_Z`).

**Formalization Note.** `H_N` is `EuclideanSpace ℂ (ι → ZMod 2)`; a matrix acts through
`Matrix.toEuclideanLin`. -/
noncomputable def codeSpace {ι κX κZ : Type} [Fintype ι] [DecidableEq ι]
    (HX : Matrix κX ι (ZMod 2)) (HZ : Matrix κZ ι (ZMod 2)) :
    Submodule ℂ (EuclideanSpace ℂ (ι → ZMod 2)) :=
  (⨅ a : κX, LinearMap.ker (Matrix.toEuclideanLin (pauliX (HX a)) - LinearMap.id)) ⊓
    (⨅ b : κZ, LinearMap.ker (Matrix.toEuclideanLin (pauliZ (HZ b)) - LinearMap.id))

end GoodQLTC


