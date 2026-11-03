-- Prove2me | Definitions.Def_IsotropicSpin_spinHalf
-- name    : IsotropicSpin_spinHalf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:24:16.015201+00:00
-- url     : https://prove2.me/theorems/e5818f2b-5114-41bd-8237-2aece56467e7
-- title:
--   Spin-1/2 operators $S_k = \tfrac12\sigma_k$
-- statement:
--   The **spin-1/2 operators** are the three $2\times 2$ Hermitian matrices $S_k=\tfrac12\sigma_k$, $k=1,2,3$, where $\sigma_k$ are the Pauli matrices:
--
--   $$
--   S_1=\frac12\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
--   S_2=\frac12\begin{pmatrix}0&-i\\ i&0\end{pmatrix},\qquad
--   S_3=\frac12\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
--   $$
--
--   They act on $\mathbb C^2$ with basis $(|{+}1/2\rangle,|{-}1/2\rangle)$, the eigenvectors of $S_3$ for $+1/2$ and $-1/2$. Together with (6) they define the spin-1/2 isotropic channel $\Lambda_{1/2}$.
--
--   **Formalization Note** The paper's index $k=1,2,3$ is the Lean index $0,1,2$; basis index $0$ is $|{+}1/2\rangle$, the order used by the time-reversal map (12).
-- source:
--   Alicki, Isotropic quantum spin channels and additivity questions, arXiv:quant-ph/0402080v1, §2, Case s = 1/2, p.2 ("Spin operators are given in terms of Pauli matrices, S_k = ½σ_k")

import Mathlib

namespace IsotropicSpin

/-- **Spin-1/2 operators** `S_k = ½ σ_k`, Alicki, *Isotropic quantum spin channels and additivity
questions*, arXiv:quant-ph/0402080v1, §2, Case s = 1/2, p. 2 ("Spin operators are given in terms of
Pauli matrices, S_k = ½σ_k").

`spinHalf 0 = ½σ₁ = ½ !![0, 1; 1, 0]`, `spinHalf 1 = ½σ₂ = ½ !![0, -i; i, 0]`,
`spinHalf 2 = ½σ₃ = ½ !![1, 0; 0, -1]`.

**Formalization Note** The paper's index `k = 1, 2, 3` is the Lean index `k = 0, 1, 2`. The basis
of `ℂ²` is ordered `(|+1/2⟩, |−1/2⟩)` (index `0` is `|+1/2⟩`, the eigenvector of `S₃` for `+1/2`),
the order used by the time-reversal map (12). -/
noncomputable def spinHalf : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![(1 / 2 : ℂ) • !![0, 1; 1, 0],
    (1 / 2 : ℂ) • !![0, -Complex.I; Complex.I, 0],
    (1 / 2 : ℂ) • !![1, 0; 0, -1]]

end IsotropicSpin


