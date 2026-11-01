-- Prove2me | Definitions.Def_NoSignalPA_chshCoef
-- name    : NoSignalPA_chshCoef
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:02:28.096579+00:00
-- url     : https://prove2.me/theorems/45d61583-c197-4af0-993d-889fdcfc44b1
-- title:
--   The CHSH coefficient vector $|\mathrm{CHSH}\rangle$ (2)
-- statement:
--   The CHSH coefficient vector of (2):
--
--   $$
--   |\mathrm{CHSH}\rangle=\frac{1}{4\sqrt2}\begin{bmatrix}1&5&1&5\\5&1&5&1\\1&5&5&1\\5&1&1&5\end{bmatrix}
--   $$
--
--   in the layout (3) (rows $(a,x)=00,10,01,11$, columns $(b,y)$ in the same order). Its entry at $(a,b,x,y)$ is $\frac{1}{4\sqrt2}$ when $a\oplus b=xy$ and $\frac{5}{4\sqrt2}$ otherwise. With this normalization the CHSH inequality reads $\langle\mathrm{CHSH}|P_{a,b|x,y}\rangle\ge\sqrt2$, and the PR box attains $1/\sqrt2$.
--
--   **Formalization Note** The entry is read from the printed table; its closed form for the tensor power is a milestone.
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, eq. (2), p.1

import Mathlib
import Definitions.Def_NoSignalPA_cell

namespace NoSignalPA

/-- **The CHSH coefficient vector (2).**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, eq. (2), p. 1 (PDF p. 1):

`|CHSH⟩ = 1/(4√2) · [1 5 | 1 5; 5 1 | 5 1; 1 5 | 5 1; 5 1 | 1 5]`,

in the layout (3): rows `(a, x) = 00, 10, 01, 11`, columns `(b, y)` in the same order.
`chshCoef a b x y` is the entry in row `cell a x`, column `cell b y`. With this normalization
`⟨CHSH|P⟩ ≥ √2` for every local box and `⟨CHSH|P⟩ = 1/√2` for the PR box (p. 1).

**Formalization Note.** The entry is read off the printed table, not from a closed form; the
closed form of its tensor power is milestone `NoSignalPA.chsh_tensor_entry`. -/
noncomputable def chshCoef (a b x y : Bool) : ℝ :=
  1 / (4 * Real.sqrt 2) *
    (!![1, 5, 1, 5; 5, 1, 5, 1; 1, 5, 5, 1; 5, 1, 1, 5] : Matrix (Fin 4) (Fin 4) ℝ)
      (cell a x) (cell b y)

end NoSignalPA


