-- Prove2me | Definitions.Def_hardy2001_qubit
-- name    : hardy2001_qubit
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-02T11:13:08.553339+00:00
-- url     : https://prove2.me/theorems/32b84424-eb90-41c0-9658-9b3536e341a2
-- title:
--   The $N=2$ matrices $D$, $C$, $A$ and the roots $c_\pm$
-- statement:
--   For real parameters $a,b,c$, Section 8.6 (and Section 5) of the paper consider the $4\times4$ matrix
--
--   $$D=\begin{pmatrix}1&0&1-a&1-b\\0&1&a&b\\1-a&a&1&c\\1-b&b&c&1\end{pmatrix},$$
--
--   the change-of-variables matrix
--
--   $$C=\begin{pmatrix}1&0&0&0\\1&1&0&0\\0&0&1&0\\0&0&0&1\end{pmatrix},$$
--
--   the $3\times3$ matrix
--
--   $$A=\begin{pmatrix}\tfrac12&a-\tfrac12&b-\tfrac12\\a-\tfrac12&\tfrac12&c-\tfrac12\\b-\tfrac12&c-\tfrac12&\tfrac12\end{pmatrix},$$
--
--   and the two numbers
--
--   $$c_\pm=1-a-b+2ab\pm2\sqrt{ab(1-a)(1-b)} .$$
--
--   $D_{ij}$ is the probability of obtaining the $i$-th fiducial measurement on the $j$-th fiducial state of a system with $N=2$, $K=4$. Pure states then lie on the surface $\vec v^{\,T}A\vec v=\tfrac12$.
--
--   **Formalization Note** Rows and columns are indexed from $0$. $\sqrt{\cdot}$ is `Real.sqrt`, which returns $0$ on negative arguments. Statements that use $c_\pm$ assume $0\le a,b\le1$, where the radicand is nonnegative.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, p. 9, Eqs. (34), (37); pp. 20–21, Section 8.6, Eqs. (74), (78), (83), (85)

import Mathlib

namespace HardyFiveAxioms

/-- The matrix `D` of the `N = 2`, `K = 4` case (Hardy 2001, Eqs. (34) and (74)), with
fiducial vectors indexed `0, 1, 2, 3` (the paper's `1, 2, 3, 4`). -/
def qubitD (a b c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 1 - a, 1 - b;
     0, 1, a, b;
     1 - a, a, 1, c;
     1 - b, b, c, 1]

/-- The change of variables `r = C v` (Hardy 2001, Eq. (78)). -/
def qubitC : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     1, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/-- The `3 × 3` matrix `A` of Hardy 2001, Eq. (83). -/
noncomputable def qubitA (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 / 2, a - 1 / 2, b - 1 / 2;
     a - 1 / 2, 1 / 2, c - 1 / 2;
     b - 1 / 2, c - 1 / 2, 1 / 2]

/-- `c₊ = 1 - a - b + 2ab + 2√(ab(1-a)(1-b))` (Hardy 2001, Eqs. (37) and (85)). -/
noncomputable def cPlus (a b : ℝ) : ℝ :=
  1 - a - b + 2 * a * b + 2 * Real.sqrt (a * b * (1 - a) * (1 - b))

/-- `c₋ = 1 - a - b + 2ab - 2√(ab(1-a)(1-b))` (Hardy 2001, Eqs. (37) and (85)). -/
noncomputable def cMinus (a b : ℝ) : ℝ :=
  1 - a - b + 2 * a * b - 2 * Real.sqrt (a * b * (1 - a) * (1 - b))

end HardyFiveAxioms


