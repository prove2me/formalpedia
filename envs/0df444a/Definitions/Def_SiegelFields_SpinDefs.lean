-- Prove2me | Definitions.Def_SiegelFields_SpinDefs
-- name    : SiegelFields_SpinDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T00:33:30.021748+00:00
-- url     : https://prove2.me/theorems/1dad27c0-c541-44ed-b768-311446422cb3
-- title:
--   Siegel's Fields §IIA: 3-vectors as traceless hermitian $2\times2$ matrices
-- statement:
--   Basic objects of Siegel's treatment of rotations and spin (*Fields*, §IIA1–IIA2, pp. 110–115).
--
--   1. The matrix $C=\begin{pmatrix}0&-i\\ i&0\end{pmatrix}$ (p. 112).
--   2. A matrix $V\in M_2(\mathbb C)$ is a **3-vector** if $V^\dagger=V$ and $\operatorname{tr}V=0$ (p. 111).
--   3. The book's basis (p. 111): for $v=(v_1,v_2,v_3)\in\mathbb R^3$
--
--   $$V(v)=\frac1{\sqrt2}\begin{pmatrix}v_1& v_2-iv_3\\ v_2+iv_3&-v_1\end{pmatrix},$$
--
--   and $E_i=V(e_i)$ for the standard basis vectors $e_i$.
--   4. For $U\in M_2(\mathbb C)$, the real $3\times3$ matrix $R(U)$ with entries
--
--   $$R(U)_{ij}=\operatorname{Re}\operatorname{tr}\big(E_i\,U\,E_j\,U^\dagger\big),$$
--
--   which is the matrix of $V\mapsto UVU^\dagger$ in the basis $E_1,E_2,E_3$ when $U$ is unitary.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Components are indexed by `Fin 3` $=\{0,1,2\}$, so the book's $V^1,V^2,V^3$ are `v 0, v 1, v 2`. `rotationOf` is defined for every $2\times2$ matrix; the theorems restrict to unitary or special unitary $U$.
-- source:
--   W. Siegel, *Fields*, arXiv:hep-th/9912205v3 (2005), https://arxiv.org/abs/hep-th/9912205, Chapter II (Spin), Section A (Two components), §IIA1 pp. 110–112 and §IIA2 p. 114

import Mathlib


open Matrix Complex

namespace SiegelFields

/-- The imaginary, hermitian matrix `C = [[0, -i], [i, 0]]` (Siegel, *Fields*, §IIA1, p. 112). -/
def matC : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- A 2×2 complex matrix represents a 3-vector when it is hermitian and traceless
(Siegel, *Fields*, §IIA1, p. 111: `V = V†`, `tr V = 0`). -/
def IsThreeVector (V : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  V.IsHermitian ∧ V.trace = 0

/-- The book's basis (§IIA1, p. 111):
`V = (1/√2) [[V¹, V² - i V³], [V² + i V³, -V¹]]`, with components indexed `0, 1, 2`. -/
noncomputable def vecToMatrix (v : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    !![(v 0 : ℂ), (v 1 : ℂ) - I * (v 2 : ℂ); (v 1 : ℂ) + I * (v 2 : ℂ), -(v 0 : ℂ)]

/-- The `i`-th basis 3-vector as a 2×2 matrix, `E_i = vecToMatrix (e_i)`. -/
noncomputable def basisMatrix (i : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  vecToMatrix (Pi.single i 1)

/-- The real 3×3 matrix of the transformation `V ↦ U V U†` in the book's basis:
`R(U)_{ij} = Re tr(E_i U E_j U†)`. -/
noncomputable def rotationOf (U : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => (trace (basisMatrix i * U * basisMatrix j * Uᴴ)).re

end SiegelFields


