-- Prove2me | Definitions.Def_ShendeQSD_Synthesis_csMat
-- name    : ShendeQSD_Synthesis_csMat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:33.687761+00:00
-- url     : https://prove2.me/theorems/ea399c5d-f4e6-4137-8918-c380d4fc5d33
-- title:
--   Cosine–Sine middle factor $\begin{pmatrix}C&-S\\S&C\end{pmatrix}$
-- statement:
--   For real diagonal matrices $C=\mathrm{diag}(C_i)$ and $S=\mathrm{diag}(S_i)$ on a register $\iota$, the **Cosine–Sine middle factor** is the block matrix
--
--   $$
--   \begin{pmatrix}C&-S\\ S&C\end{pmatrix}
--   $$
--
--   on one extra (most significant) qubit and the register. When $C^2+S^2=I$ it is the middle factor of the Cosine–Sine decomposition.
--
--   **Formalization Note** The index is `Bool × ι`, the Bool factor selecting the block row and column (`false` first); `C S : ι → ℝ` are the diagonal entries.
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, §5.1, p. 12

import Mathlib

namespace ShendeQSD.Synthesis

/-- **The middle factor `[[C, −S], [S, C]]` of the Cosine–Sine decomposition.**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
§5.1, p. 12: "U = (A₁ ; B₁)(C −S ; S C)(A₂ ; B₂)" with `C, S` real diagonal matrices.

`csMat C S` is the block matrix `[[C, −S], [S, C]]` with `C = diag(C i)`, `S = diag(S i)`.

**Formalization Note.** The index `Bool × ι`: the Bool factor (the most significant qubit) selects
the block row/column, `false` the first; the real diagonals are given by their entries
`C S : ι → ℝ`. -/
def csMat {ι : Type*} [DecidableEq ι] (C S : ι → ℝ) : Matrix (Bool × ι) (Bool × ι) ℂ :=
  Matrix.of fun p q =>
    if p.2 = q.2 then
      (match p.1, q.1 with
        | false, false => ((C p.2 : ℝ) : ℂ)
        | false, true => ((-S p.2 : ℝ) : ℂ)
        | true, false => ((S p.2 : ℝ) : ℂ)
        | true, true => ((C p.2 : ℝ) : ℂ))
    else 0

end ShendeQSD.Synthesis


