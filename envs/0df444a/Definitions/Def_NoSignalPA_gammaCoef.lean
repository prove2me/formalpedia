-- Prove2me | Definitions.Def_NoSignalPA_gammaCoef
-- name    : NoSignalPA_gammaCoef
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:02:33.753543+00:00
-- url     : https://prove2.me/theorems/8fe6922a-9599-49f3-8505-7624b7a65dca
-- title:
--   The vectors $|\gamma_0\rangle,|\gamma_1\rangle$ of Lemma 1 (corrected: transposed tables)
-- statement:
--   The two vectors of $\mathbb R^{16}$ used in Lemma 1, in the layout (3):
--
--   $$
--   |\gamma_0\rangle=\frac18\begin{bmatrix}1&5&1&5\\-3&1&-3&1\\1&-3&5&1\\5&1&1&-3\end{bmatrix},\qquad
--   |\gamma_1\rangle=\frac18\begin{bmatrix}1&-3&1&-3\\5&1&5&1\\1&5&-3&1\\-3&1&1&5\end{bmatrix}.
--   $$
--
--   These are the transposes of the tables printed in Lemma 1. The printed tables do not follow the layout (3) that the paper's own (2) and the vectors $\gamma'$, $\gamma''$ of the Appendix use; with them, Lemma 1 fails already for $N_r=1$ (the deterministic box $a=1\oplus x$, $b=0$ has $P_{a=0|x=0}=0$, while the printed $\langle\gamma_0|P\rangle=1$).
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, Lemma 1, p.2 (tables), with layout (3), p.1, and the Appendix, p.4

import Mathlib
import Definitions.Def_NoSignalPA_cell

namespace NoSignalPA

/-- **The single-system vectors `|γ₀⟩, |γ₁⟩` of Lemma 1 (corrected: transposed tables).**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, Lemma 1, p. 2 (PDF p. 2), with the layout (3) of p. 1:

`γ₀ = 1/8 · [1 5 | 1 5; -3 1 | -3 1; 1 -3 | 5 1; 5 1 | 1 -3]`,
`γ₁ = 1/8 · [1 -3 | 1 -3; 5 1 | 5 1; 1 5 | -3 1; -3 1 | 1 5]`,

rows `(a, x) = 00, 10, 01, 11`, columns `(b, y)` in the same order. `gammaCoef s a b x y` is the
entry of `|γ_s⟩` in row `cell a x`, column `cell b y`.

**Formalization Note (correction).** These are the transposes of the tables printed in Lemma 1.
The printed tables do not follow layout (3), which the paper's own `|CHSH⟩` (2) and `|γ′⟩`,
`|γ″⟩` (p. 4) use: for the deterministic nonsignaling box `a = 1 ⊕ x`, `b = 0` (one system),
`P_{a=0|x=0} = 0` but the printed `⟨γ₀|P⟩ = 1`. With the transposes Lemma 1 holds. -/
noncomputable def gammaCoef (s a b x y : Bool) : ℝ :=
  1 / 8 *
    (cond s
      (!![1, -3, 1, -3; 5, 1, 5, 1; 1, 5, -3, 1; -3, 1, 1, 5] : Matrix (Fin 4) (Fin 4) ℝ)
      (!![1, 5, 1, 5; -3, 1, -3, 1; 1, -3, 5, 1; 5, 1, 1, -3] : Matrix (Fin 4) (Fin 4) ℝ))
      (cell a x) (cell b y)

end NoSignalPA


