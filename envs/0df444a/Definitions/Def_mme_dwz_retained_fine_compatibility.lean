-- Prove2me | Definitions.Def_mme_dwz_retained_fine_compatibility
-- name    : mme_dwz_retained_fine_compatibility
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T09:27:16.787778+00:00
-- url     : https://prove2.me/theorems/11a6980c-93c5-4c2c-9283-c4cb0d4a6808
-- title:
--   Grouped compatibility of a retained outer word and a literal fine Z word
-- statement:
--   Fix an integral Table-2 scale $m$, a retained outer component word, and a literal fine $Z$ word in the canonical nine-grading of $CW_q\otimes CW_q$. Boundary components are kept as individual regions, while interior components with positive $X$ and $Y$ degree are grouped by their coarse $Z$ degree.
--
--   The outer and fine words are compatible when, for every such region $R$ and every left fine grade $a\in\{0,1,2\}$,
--
--   $$
--   \#\{t:\operatorname{region}(\operatorname{outer}(t))=R,\ \operatorname{left}(z(t))=a\}=\operatorname{cellCount}_m(R,a).
--   $$
--
--   This is the literal fine-word form of DWZ Definition 6.1 used by Additional Zeroing-Out Steps 1--2; it retains the address itself and makes no candidate-count or hole-survival assertion.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 6.1 and Claim 6.2, printed pp. 51--52 (PDF pp. 52--53), with the (+,+,k) grouping of Equation (23); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_retained_fine_address
import Definitions.Def_mme_dwz_table2_split_assignments

open MME.DWZStep1Support

namespace MME.DWZStep2Source

set_option autoImplicit false
set_option warningAsError true

/-- Literal grouped Table-2 compatibility of a fine-nine-grading Z word with
one retained outer component word. -/
def retainedFineCompatible
    (m : ℕ) {Copy Position : Type*} [Fintype Position]
    (outer : Copy → Position → Fin 15)
    (z : Position → Fin (3 * 3)) (j : Copy) : Prop :=
  let groupedRegion :
      Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
    if h : MME.DWZSquare.shapeX s = 0 ∨
        MME.DWZSquare.shapeY s = 0 then
      Sum.inl ⟨s, h⟩
    else
      Sum.inr (MME.DWZSquare.shapeZ s)
  ∀ (region : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
    Fintype.card
        {t : Position //
          groupedRegion (outer j t) = region ∧ fineSplitLeft (z t) = a} =
      MME.DWZTable2Cardinality.cellCount m region a

end MME.DWZStep2Source


