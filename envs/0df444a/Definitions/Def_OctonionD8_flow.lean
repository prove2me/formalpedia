-- Prove2me | Definitions.Def_OctonionD8_flow
-- name    : OctonionD8_flow
-- status  : Definition
-- author  : @ShapeZero
-- created : 2026-09-27T05:21:31.873448+00:00
-- url     : https://prove2.me/theorems/26727641-530f-4e8a-93d7-8a6e998b2232
-- title:
--   The octonion product from the Fano plane, and the flow matrix $R_{e_1} + L_{c e_1 + s e_2}$
-- statement:
--   Write $e_0 = 1, e_1, \dots, e_7$ for the standard basis of $\mathbb{R}^8$, and label the imaginary unit $e_u$ ($u = 1, \dots, 7$) by the Fano point $u - 1$. For each line $\{l, l+1, l+3\}$ (mod $7$) of the Fano plane, orient the product cyclically along $(l, l+1, l+3)$:
--
--   $$
--   e_{l+1}\,e_{l+2} = e_{l+4}, \qquad e_{l+2}\,e_{l+4} = e_{l+1}, \qquad e_{l+4}\,e_{l+1} = e_{l+2}
--   $$
--
--   (unit indices mod $7$ in $1, \dots, 7$), with reversed products negative, $e_u^2 = -1$ and $e_0$ the identity. Extend bilinearly to a product $pq$ on $\mathbb{R}^8$.
--
--   For $a, b \in \mathbb{R}^8$ let $R_a$ and $L_b$ be the matrices of $p \mapsto p\,a$ and $p \mapsto b\,p$ (column $j$ is the image of $e_j$). For real $c, s$ the **flow matrix** is
--
--   $$
--   M = R_{e_1} + L_{c\,e_1 + s\,e_2},
--   $$
--
--   the matrix of $p \mapsto p\,e_1 + (c\,e_1 + s\,e_2)\,p$.
--
--   **Formalization Note** `octTable i j k` is the coefficient of $e_k$ in $e_i e_j$; it is built from the published `RolesForceSeven.fanoLine`. `omul` is the product, `Rmat`/`Lmat` the multiplication matrices, and `flowMat c s` the flow matrix.
-- source:
--   Motivated by the two-generator D8 flow in the Shape Zero derivation (Shape Zero LLC): https://github.com/ShapeZeroSZ/shape-zero/blob/main/00_START_HERE/MODEL_SPEC.md §1b and https://github.com/ShapeZeroSZ/shape-zero/blob/main/02_synthesis/D8_SYNTHESIS.md ; Fano plane: Prove2Me definition RolesForceSeven.fano (mission "The role postulates force exactly seven points") ; public references: Wikipedia, "Octonion": https://en.wikipedia.org/wiki/Octonion ; Wikipedia, "Fano plane": https://en.wikipedia.org/wiki/Fano_plane

import Mathlib
import Definitions.Def_RolesForceSeven_fano

namespace OctonionD8

open Polynomial RolesForceSeven

/-- The Fano point labelling the imaginary unit `e_i` (`i = 1, …, 7` ↦ point `i - 1`). -/
def fanoPoint (i : Fin 8) : Fin 7 := ⟨(i.val + 6) % 7, Nat.mod_lt _ (by norm_num)⟩

/-- Structure constants of the octonion product on ℝ⁸ (index 0 = the real unit),
from mission 5's Fano lines {i, i+1, i+3} (mod 7), oriented cyclically:
e_{i+1} e_{i+2} = e_{i+4}, with e_k² = −1 and anticommuting distinct units.
`octTable i j k` is the coefficient of `e_k` in `e_i e_j`. -/
def octTable (i j k : Fin 8) : ℤ :=
  if i = 0 then (if j = k then 1 else 0)
  else if j = 0 then (if i = k then 1 else 0)
  else if i = j then (if k = 0 then -1 else 0)
  else if k = 0 then 0
  else if ∃ l : Fin 7, fanoLine l = {fanoPoint i, fanoPoint j, fanoPoint k} ∧
      ((fanoPoint i = l ∧ fanoPoint j = l + 1) ∨ (fanoPoint i = l + 1 ∧ fanoPoint j = l + 3) ∨
        (fanoPoint i = l + 3 ∧ fanoPoint j = l)) then 1
  else if ∃ l : Fin 7, fanoLine l = {fanoPoint i, fanoPoint j, fanoPoint k} then -1
  else 0

/-- The octonion product. -/
def omul (p q : Fin 8 → ℝ) : Fin 8 → ℝ :=
  fun k => ∑ i, ∑ j, p i * q j * (octTable i j k : ℝ)

/-- Matrix of p ↦ p · a (right multiplication by a). -/
def Rmat (a : Fin 8 → ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  fun k j => omul (Pi.single j 1) a k

/-- Matrix of p ↦ b · p (left multiplication by b). -/
def Lmat (b : Fin 8 → ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  fun k j => omul b (Pi.single j 1) k

/-- The two-generator flow for a = e₁, b = c·e₁ + s·e₂. -/
def flowMat (c s : ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  Rmat (Pi.single 1 1) + Lmat (fun i => if i = 1 then c else if i = 2 then s else 0)

end OctonionD8


