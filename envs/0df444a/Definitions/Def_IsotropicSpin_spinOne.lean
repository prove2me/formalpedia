-- Prove2me | Definitions.Def_IsotropicSpin_spinOne
-- name    : IsotropicSpin_spinOne
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:24:20.168329+00:00
-- url     : https://prove2.me/theorems/795ec3c6-6806-432d-a8e9-99415d0cb124
-- title:
--   Spin-1 operators $S_1,S_2,S_3$ of eq. (13)
-- statement:
--   The **spin-1 operators** are the three $3\times 3$ Hermitian matrices of eq. (13):
--
--   $$
--   S_1=\frac1{\sqrt2}\begin{pmatrix}0&1&0\\1&0&1\\0&1&0\end{pmatrix},\qquad
--   S_2=\frac1{\sqrt2}\begin{pmatrix}0&-i&0\\ i&0&-i\\0&i&0\end{pmatrix},\qquad
--   S_3=\begin{pmatrix}1&0&0\\0&0&0\\0&0&-1\end{pmatrix}.
--   $$
--
--   They act on $\mathbb C^3$ with basis $(|{+}1\rangle,|0\rangle,|{-}1\rangle)$, the eigenvectors of $S_3$, satisfy $[S_1,S_2]=iS_3$ and $S_1^2+S_2^2+S_3^2=2\cdot\mathbf 1$, and define the spin-1 isotropic channel $\Lambda_1$ through (6).
--
--   **Formalization Note** The paper's index $k=1,2,3$ is the Lean index $0,1,2$; basis index $0$ is $|{+}1\rangle$, the order in which (13) is printed. $1/\sqrt2$ is the real number $(\sqrt2)^{-1}$ cast to $\mathbb C$.
-- source:
--   Alicki, Isotropic quantum spin channels and additivity questions, arXiv:quant-ph/0402080v1, eq. (13), p.2

import Mathlib

namespace IsotropicSpin

/-- **Spin-1 operators**, Alicki, arXiv:quant-ph/0402080v1, eq. (13), p. 2:
`S₁ = (1/√2) !![0, 1, 0; 1, 0, 1; 0, 1, 0]`, `S₂ = (1/√2) !![0, -i, 0; i, 0, -i; 0, i, 0]`,
`S₃ = !![1, 0, 0; 0, 0, 0; 0, 0, -1]`.

**Formalization Note** The paper's index `k = 1, 2, 3` is the Lean index `k = 0, 1, 2`. The basis of
`ℂ³` is ordered `(|+1⟩, |0⟩, |−1⟩)` (index `0` is `|+1⟩`, the eigenvector of `S₃` for `+1`), the
order in which (13) is printed. `1/√2` is the real number `(√2)⁻¹` cast to `ℂ`. -/
noncomputable def spinOne : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![((Real.sqrt 2)⁻¹ : ℂ) • !![0, 1, 0; 1, 0, 1; 0, 1, 0],
    ((Real.sqrt 2)⁻¹ : ℂ) • !![0, -Complex.I, 0; Complex.I, 0, -Complex.I; 0, Complex.I, 0],
    !![1, 0, 0; 0, 0, 0; 0, 0, -1]]

end IsotropicSpin


