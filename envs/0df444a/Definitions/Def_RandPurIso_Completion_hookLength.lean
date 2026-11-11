-- Prove2me | Definitions.Def_RandPurIso_Completion_hookLength
-- name    : RandPurIso_Completion_hookLength
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:26:14.001526+00:00
-- url     : https://prove2.me/theorems/bd3f75d1-3140-4546-94b7-5cbdd34e98c6
-- title:
--   Hook lengths, $f_\lambda$ and $d_{\lambda,N}$
-- statement:
--   For a Young diagram $\lambda$ and a box $(i,j)$, the **hook length** $h_\lambda(i,j)$ is one plus the number of boxes strictly to its right and strictly below it. For $|\lambda|=t$,
--   $$f_\lambda=\frac{t!}{\prod_{(i,j)\in\lambda}h_\lambda(i,j)},\qquad d_{\lambda,N}=\prod_{(i,j)\in\lambda}\frac{N+j-i}{h_\lambda(i,j)}\quad(1).$$
--   These are the dimensions of the irreducible representations $\mathcal P_\lambda$ of $S_t$ and $\mathcal Q_{\lambda,N}$ of $U(N)$.
--
--   **Formalization Note** The paper defines $f_\lambda=\dim\mathcal P_\lambda$, $d_{\lambda,N}=\dim\mathcal Q_{\lambda,N}$ and quotes the formulas (hook-length formula, Eq. (1)) from [FLM+26]; the formulas are used as the definitions (same values). Mathlib cells are 0-indexed, which leaves $N+j-i$ unchanged.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, §3.3, pp. 22–23, Eq. (1)

import Mathlib
open Matrix

namespace RandPurIso.Completion

/-- **Hook length** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §3.3, p. 22): `h_λ(i, j)` is one plus the number of boxes strictly
to the right of `(i, j)` in its row and strictly below it in its column.

**Formalization Note.** Cells of a Mathlib `YoungDiagram` are 0-indexed pairs `(row, column)`. -/
def hookLength (μ : YoungDiagram) (c : ℕ × ℕ) : ℕ :=
  (μ.rowLen c.1 - c.2 - 1) + (μ.colLen c.2 - c.1 - 1) + 1

/-- `f_λ = dim P_λ`, by the hook-length formula `f_λ = t! / Π_{(i,j)∈λ} h_λ(i, j)` (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §3.3,
p. 23), for `|λ| = t`.

**Formalization Note.** The paper defines `f_λ` as the dimension of the Specht module and quotes the
hook-length formula from [FLM+26]; the formula is used as the definition (same value). -/
noncomputable def spechtDim (t : ℕ) (μ : YoungDiagram) : ℝ :=
  (t.factorial : ℝ) / ∏ c ∈ μ.cells, (hookLength μ c : ℝ)

/-- `d_{λ,N} = dim Q_{λ,N}`, by Eq. (1): `d_{λ,N} = Π_{(i,j)∈λ} (N + j − i)/h_λ(i, j)` (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 23).

**Formalization Note.** As for `spechtDim`, the paper's Eq. (1) is used as the definition. With
0-indexed cells `(i, j)`, `N + j − i` is the same as with the paper's 1-indexed cells. -/
noncomputable def weylDim (N : ℕ) (μ : YoungDiagram) : ℝ :=
  ∏ c ∈ μ.cells, ((N : ℝ) + (c.2 : ℝ) - (c.1 : ℝ)) / (hookLength μ c : ℝ)

end RandPurIso.Completion


