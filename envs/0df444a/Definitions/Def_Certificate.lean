-- Prove2me | Definitions.Def_Certificate
-- name    : Certificate
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-09T05:11:23.677997+00:00
-- url     : https://prove2.me/theorems/3d766a3f-ef62-46a8-bdb1-80c16eb39053
-- title:
--   Certificate objects: interpolation residual, the matrix Q_j, potentials V_j, and the square terms
-- statement:
--   This module collects the scalar building blocks of the master telescoping certificate, transcribed from the source. The smooth-convex interpolation residual at a pair of points is
--
--   $$I_{ij} = F_i - F_j - \langle g_j,\, x_i - x_j\rangle - \tfrac12\|g_i - g_j\|^2,$$
--
--   with $F_i = f(x_i)$ and $g_i = \nabla f(x_i)$, and its minimiser variant $I_{\star,j}$ is the same expression with $x_\star = 0$, $F_\star = 0$, $g_\star = 0$. The $2 \times 2$ matrix $Q_j$ is stored as its three independent entries $Q_{11}, Q_{12}, Q_{22}$ (source (8.1)), built from the coefficient sequences $a_j, b_j, h_j, D_j$, and acts on a pair of vectors $p, q$ through the source's own expansion $Q_{11}\|p\|^2 + 2Q_{12}\langle p, q\rangle + Q_{22}\|q\|^2$ (source (8.2)). The local potentials are $V_0 = 0$ and, for $1 \le j < N$,
--
--   $$V_j = a_{j-1} F_j - \tau_N\|r\|^2 - \tfrac{a_{j-1}}{2}\|g_j\|^2 + b_j\langle g_j, y_{j+1}\rangle + \mathrm{quadForm}(Q_j;\, y_j, y_{j+1}),$$
--
--   together with the terminal potential $V_N$ (source (8.5)). The nonnegative square terms of section 6 are the initial $S_0$, the interior $S_j$ with coefficients $\alpha_j = a_{j+1}/2$ and $\beta_j$ of (6.3), and the terminal $S_{N-1}$ with coefficient $\beta_T$ of (6.5); `Sterm` assembles the full list $S_0, \dots, S_{N-1}$ that the certificate sums. Every object in the module is a definition; the identities relating them are proved elsewhere.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §2, §6, §8, eq. (2.1), (6.1)-(6.6), (8.1)-(8.5); Lean: FullFormalization.Certificate lines 1-137

-- Generated from F:/20261008/FullFormalization\FullFormalization\Certificate.lean by skeleton subtraction (Phase 3-4):
-- every unselected declaration deleted, project imports rewritten.
/-
  FullFormalization.Certificate

  The certificate objects of source sections 6 and 8, and the interpolation
  residual of section 2 — transcribed verbatim.

  Everything in this file is a *definition*.  The identities relating them
  ((9.1), (10.1), (11.1), (11.2) and the master certificate (7.1)) are proved in
  `CertificateIdentities.lean`; the positivity of the weights is proved in
  `Positivity.lean`.

  Representation choices (documented in DEPENDENCY_MAP.md, section 9, D-1):

  * `Ival` takes `F_i, F_j, g_i, g_j` as free arguments rather than being
    derived from a fixed `f`.  This is exactly the source's own reading: the
    certificate identities of sections 9-11 are identities that hold "for any
    vectors and function values satisfying the algorithm relations"
    (source line 715), with `F_i` and `g_i` free.  The bridge back to a genuine
    function is the interpolation lemma `Ival_nonneg` of `Interpolation.lean`.

  * `Q_j` is represented by its three independent entries `(Q11, Q12, Q22)`
    rather than as a `Matrix (Fin 2) (Fin 2) ℝ`; `quadForm` implements the
    source's own expansion (8.2) verbatim.

  * The index shift `a N (j - 1)` inside `Q11`, `Q12`, `V_j` is the source's
    `a_{j-1}`; these objects are only used at `1 <= j`, where `j - 1` is the
    honest predecessor.  `V` is given its source value `V_0 = 0` (8.3) as an
    explicit case, and `D` already carries the source's separate `D_0` (4.7).
-/

import Mathlib
import Definitions.Def_Coefficients

namespace FullFormalization

open scoped Gradient RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Section 2: the smooth-convex interpolation residual -/

/-- Source (2.1): `I_{ij} = F_i - F_j - ⟪g_j, x_i - x_j⟫ - ½‖g_i - g_j‖²`.

Written with `F_i, F_j, g_i, g_j` free, as the source uses it from section 9
onwards (see the module header). -/
noncomputable def Ival (Fi Fj : ℝ) (xi xj gi gj : E) : ℝ :=
  Fi - Fj - ⟪gj, xi - xj⟫ - (1 / 2) * ‖gi - gj‖ ^ 2

/-- The residual `I_{⋆,j}` from the minimizer: `x_⋆ = 0`, `F_⋆ = 0`, `g_⋆ = 0`
(source lines 194-200). -/
noncomputable def Istar (Fj : ℝ) (xj gj : E) : ℝ := Ival 0 Fj 0 xj 0 gj



/-! ### Section 8.1: the `2 × 2` matrix `Q_j` -/

/-- Source (8.1), entry `(1,1)`. -/
noncomputable def Q11 (N j : ℕ) : ℝ :=
  (1 - h N j + D N (j + 1) * (a N (j - 1) + a N j / D N j)) / D N j / 2

/-- Source (8.1), entry `(1,2) = (2,1)`. -/
noncomputable def Q12 (N j : ℕ) : ℝ := (-a N (j - 1) - a N j / D N j) / 2

/-- Source (8.1), entry `(2,2)`. -/
noncomputable def Q22 (N j : ℕ) : ℝ := a N j / 2

/-- Source (8.2): the quadratic form of `Q_j` on a pair of vectors, expanded
exactly as the source states it. -/
noncomputable def quadForm (q11 q12 q22 : ℝ) (p q : E) : ℝ :=
  q11 * ‖p‖ ^ 2 + 2 * q12 * ⟪p, q⟫ + q22 * ‖q‖ ^ 2

/-! ### Section 8.3-8.5: the potential `V` -/

/-- Source (8.4), the interior potential `V_j` for `1 <= j < N`. -/
noncomputable def Vterm (N : ℕ) (r : E) (y g : ℕ → E) (Fv : ℕ → ℝ) (j : ℕ) : ℝ :=
  a N (j - 1) * Fv j
    - tau N * ‖r‖ ^ 2
    - a N (j - 1) / 2 * ‖g j‖ ^ 2
    + b N j * ⟪g j, y (j + 1)⟫
    + quadForm (Q11 N j) (Q12 N j) (Q22 N j) (y j) (y (j + 1))

/-- Source (8.3)-(8.4): `V_0 = 0` and `V_j` for `1 <= j < N`. -/
noncomputable def V (N : ℕ) (r : E) (y g : ℕ → E) (Fv : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else Vterm N r y g Fv j

/-- Source (8.5): the terminal potential `V_N`. -/
noncomputable def VN (N : ℕ) (r : E) (x g : ℕ → E) (Fv : ℕ → ℝ) : ℝ :=
  a N (N - 1) * Fv N
    - tau N * ‖r‖ ^ 2
    + b N N * (⟪g N, x N⟫ - (1 / 2) * ‖g N‖ ^ 2)

/-! ### Section 6: the nonnegative square terms -/

/-- Source (6.2): `α_j = a_{j+1} / 2`. -/
noncomputable def alpha (N j : ℕ) : ℝ := a N (j + 1) / 2

/-- Source (6.3): `β_j`. -/
noncomputable def beta (N j : ℕ) : ℝ :=
  (1 / 2) * (a N j * (D N (j + 1)) ^ 2
    + (a N j - 1) * D N (j + 1)
    - (h N j - 1) * (D N j + D N (j + 1))
    - a N (j + 1) * (mom j) ^ 2 * (D N j) ^ 2)

/-- Source (6.5): `β_T = ½ (a_{N-1} - (m_{N-1} + b_N)²)`. -/
noncomputable def betaT (N : ℕ) : ℝ :=
  (1 / 2) * (a N (N - 1) - (mom (N - 1) + b N N) ^ 2)

/-- Source (6.1): the initial square term `S_0`. -/
noncomputable def S0 (N : ℕ) (r : E) (x g : ℕ → E) : ℝ :=
  1 / (2 * D N 0) * ‖r - (D N 0 / D N 1) • x 1‖ ^ 2
    + a N 1 / 2 * ‖g 1 - (1 / D N 1) • x 1‖ ^ 2

/-- Source (6.4): the interior square term `S_j`, `1 <= j <= N-2`. -/
noncomputable def Sj (N : ℕ) (y g : ℕ → E) (j : ℕ) : ℝ :=
  alpha N j * ‖g (j + 1) - (1 / D N (j + 1)) • y (j + 1)‖ ^ 2
    + beta N j * ‖(1 / D N j) • y j - (1 / D N (j + 1)) • y (j + 1)‖ ^ 2

/-- Source (6.6): the terminal square term `S_{N-1}`. -/
noncomputable def Slast (N : ℕ) (y x g : ℕ → E) : ℝ :=
  (1 / 2) * ‖g N - x N + a N (N - 1) • y N‖ ^ 2
    + betaT N * ‖y N - (D N N / D N (N - 1)) • y (N - 1)‖ ^ 2

/-- The full list of nonnegative square terms summed in the master certificate:
`S_0, S_1, …, S_{N-2}, S_{N-1}`. -/
noncomputable def Sterm (N : ℕ) (r : E) (y x g : ℕ → E) (j : ℕ) : ℝ :=
  if j = 0 then S0 N r x g
  else if j = N - 1 then Slast N y x g
  else Sj N y g j

/-! ### The algorithm relations used by the certificate (source section 3) -/



end FullFormalization


