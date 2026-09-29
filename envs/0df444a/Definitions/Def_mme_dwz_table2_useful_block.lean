-- Prove2me | Definitions.Def_mme_dwz_table2_useful_block
-- name    : mme_dwz_table2_useful_block
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T06:56:29.386109+00:00
-- url     : https://prove2.me/theorems/3cb4c305-4c94-4954-a1dc-609cc1f0428d
-- title:
--   Table-2 available small Z-blocks of the standard-form tensor
-- statement:
--   Fix a Table-2 component word I. An available small Z-block of its standard-form tensor is a fine Z-word z with two exact requirements. Pointwise, each fine pair lies over the coarse Z-grade of its component: $$\operatorname{coarse}(z_t)=k_{I_t}.$$ Componentwise, for every Table-2 component s and left fine grade a, exactly split(s,a)m positions of component s have left grade a: $$|\{t:I_t=s,\ (z_t)_L=a\}|=\operatorname{split}(s,a)m.$$ This is the literal finite form of the available-block condition in Definition 5.4, specialized to the componentwise usefulness condition of Definition 6.3. It is deliberately stronger than the grouped compatibility conditions used in Equation (23).
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Definition 5.4 (PDF p.47 / printed p.46) and Definition 6.3 (PDF p.53 / printed p.52), specialized to the exact component and split counts of Table 2.

import Definitions.Def_mme_dwz_table2_split_assignments
import Definitions.Def_mme_dwz_table2_pair_coarsening

set_option autoImplicit false

namespace MME.DWZTable2StandardForm

/-- The available small Z-blocks in the Table-2 standard-form tensor attached to a fixed component word. -/
def UsefulBlock
    (m : ℕ) {Position : Type*} [Fintype Position]
    (outer : Position → Fin 15) :=
  {small : Position → Fin 3 × Fin 3 //
    (∀ t, MME.DWZTable2Counts.coarseOf (small t) =
      MME.DWZSquare.shapeZ (outer t)) ∧
    ∀ (s : Fin 15) (a : Fin 3),
      Fintype.card
          {t : Position // outer t = s ∧ (small t).1 = a} =
        MME.DWZTable2Counts.split s a * m}

noncomputable instance usefulBlockFintype
    (m : ℕ) {Position : Type*} [Fintype Position]
    (outer : Position → Fin 15) : Fintype (UsefulBlock m outer) := by
  classical
  unfold UsefulBlock
  exact Fintype.ofFinite _

noncomputable instance usefulBlockDecidableEq
    (m : ℕ) {Position : Type*} [Fintype Position]
    (outer : Position → Fin 15) : DecidableEq (UsefulBlock m outer) :=
  Classical.decEq _

end MME.DWZTable2StandardForm


