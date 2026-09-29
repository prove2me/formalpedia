-- Prove2me | Definitions.Def_mme_dwz_table2_step1_z_histogram_fibers
-- name    : mme_dwz_table2_step1_z_histogram_fibers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T05:41:13.026294+00:00
-- url     : https://prove2.me/theorems/e4b255bb-2ea2-4e61-a6b5-65b4165e1fc0
-- title:
--   Table-2 Z-split fibres for DWZ Additional Zeroing-Out Step 1
-- statement:
--   This definition package records the finite fibres used to count left fine $Z$-grades in DWZ Additional Zeroing-Out Step 1. For a coarse $Z$-grade $k$ and fine left grade $a$, it distinguishes: all positions of coarse grade $k$; positions belonging to a fixed boundary component; and positions belonging to the interior component with both $X$- and $Y$-grades nonzero. It also defines the total prescribed split count
--
--   $$
--   G_Z(k,a)=\sum_{b:\,a+b=k}\gamma_{a,b}.
--   $$
--
--   These definitions make the boundary/interior partition and its exact finite cardinality identity explicit.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 6.1, Claim 6.2 and Additional Zeroing-Out Step 1 (printed pp. 51--52 / PDF pp. 52--53). https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_split_assignments

open BigOperators

namespace MME.DWZStep1Histogram

open MME

set_option autoImplicit false

/-- The exact left-split count in all positions of coarse Z-grade `k`. -/
def table2TotalZSplit (k : Fin 5) (a : Fin 3) : ℕ :=
  ∑ b : Fin 3,
    if a.val + b.val = k.val then MME.DWZTable2Counts.gamma (a, b)
    else 0

/-- Boundary components of one fixed coarse Z-grade. -/
abbrev BoundaryComponentAt (k : Fin 5) :=
  {s : Fin 15 //
    (MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0) ∧
      MME.DWZSquare.shapeZ s = k}

/-- All positions with prescribed coarse Z-grade and left fine Z-grade. -/
abbrev TotalZFiber
    {Position : Type*}
    (outer : Position → Fin 15) (zLeft : Position → Fin 3)
    (k : Fin 5) (a : Fin 3) :=
  {t : Position //
    MME.DWZSquare.shapeZ (outer t) = k ∧ zLeft t = a}

/-- The prescribed left fine Z-grade inside one coarse component. -/
abbrev ComponentZFiber
    {Position : Type*}
    (outer : Position → Fin 15) (zLeft : Position → Fin 3)
    (s : Fin 15) (a : Fin 3) :=
  {t : Position // outer t = s ∧ zLeft t = a}

/-- Positions in the unique interior component of one coarse Z-grade. -/
abbrev InteriorZFiber
    {Position : Type*}
    (outer : Position → Fin 15) (zLeft : Position → Fin 3)
    (k : Fin 5) (a : Fin 3) :=
  {t : Position //
    MME.DWZSquare.shapeZ (outer t) = k ∧
      MME.DWZSquare.shapeX (outer t) ≠ 0 ∧
      MME.DWZSquare.shapeY (outer t) ≠ 0 ∧ zLeft t = a}

end MME.DWZStep1Histogram


