-- Prove2me | Definitions.Def_OctonionD8_blocks
-- name    : OctonionD8_blocks
-- status  : Definition
-- author  : @ShapeZero
-- created : 2026-09-27T05:22:09.875128+00:00
-- url     : https://prove2.me/theorems/95e2efbd-c41c-4ced-b225-7917e8751e7f
-- title:
--   The reordered basis $(e_0, e_1, e_2, e_4 \mid e_3, e_5, e_6, e_7)$ and the two $4\times4$ blocks of the flow matrix
-- statement:
--   **The reordering.** `blockEquiv` is the bijection from the indices $\{0, \dots, 7\}$ to two copies of $\{0, 1, 2, 3\}$ that sends $0, 1, 2, 4$ to positions $0, 1, 2, 3$ of the first block and $3, 5, 6, 7$ to positions $0, 1, 2, 3$ of the second: the basis order $(e_0, e_1, e_2, e_4 \mid e_3, e_5, e_6, e_7)$.
--
--   **The blocks.** For real $c, s$,
--
--   $$
--   A = \begin{pmatrix} 0 & -c-1 & -s & 0 \\ c+1 & 0 & 0 & s \\ s & 0 & 0 & 1-c \\ 0 & -s & c-1 & 0 \end{pmatrix},
--   \qquad
--   B = \begin{pmatrix} 0 & -s & 0 & 1-c \\ s & 0 & 1-c & 0 \\ 0 & c-1 & 0 & -s \\ c-1 & 0 & s & 0 \end{pmatrix},
--   $$
--
--   intended as the blocks of the flow matrix on $(e_0, e_1, e_2, e_4)$ and on $(e_3, e_5, e_6, e_7)$.
--
--   **Formalization Note** `blockEquiv : Fin 8 ≃ Fin 4 ⊕ Fin 4`; `blockA c s` and `blockB c s` are explicit `Matrix (Fin 4) (Fin 4) ℝ`.
-- source:
--   Motivated by the two-generator D8 flow in the Shape Zero derivation (Shape Zero LLC): https://github.com/ShapeZeroSZ/shape-zero/blob/main/00_START_HERE/MODEL_SPEC.md §1b and https://github.com/ShapeZeroSZ/shape-zero/blob/main/02_synthesis/D8_SYNTHESIS.md (block decomposition of the flow matrix) ; Fano plane: Prove2Me definition RolesForceSeven.fano (mission "The role postulates force exactly seven points") ; public references: Wikipedia, "Octonion": https://en.wikipedia.org/wiki/Octonion ; Wikipedia, "Fano plane": https://en.wikipedia.org/wiki/Fano_plane

import Mathlib
import Definitions.Def_OctonionD8_flow

namespace OctonionD8

/-- Reordering of the basis e₀, …, e₇ as (e₀, e₁, e₂, e₄ | e₃, e₅, e₆, e₇):
indices 0, 1, 2, 4 go to the first block, 3, 5, 6, 7 to the second, in that order. -/
def blockEquiv : Fin 8 ≃ Fin 4 ⊕ Fin 4 where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inl 3, Sum.inr 1, Sum.inr 2, Sum.inr 3]
  invFun := Sum.elim ![0, 1, 2, 4] ![3, 5, 6, 7]
  left_inv := by decide
  right_inv := by decide

/-- The block of `flowMat c s` on (e₀, e₁, e₂, e₄). -/
def blockA (c s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := !![0, -c - 1, -s, 0;
    c + 1, 0, 0, s;
    s, 0, 0, 1 - c;
    0, -s, c - 1, 0]

/-- The block of `flowMat c s` on (e₃, e₅, e₆, e₇). -/
def blockB (c s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := !![0, -s, 0, 1 - c;
    s, 0, 1 - c, 0;
    0, c - 1, 0, -s;
    c - 1, 0, s, 0]

end OctonionD8


