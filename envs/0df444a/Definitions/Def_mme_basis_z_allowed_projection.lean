-- Prove2me | Definitions.Def_mme_basis_z_allowed_projection
-- name    : mme_basis_z_allowed_projection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T07:16:57.22755+00:00
-- url     : https://prove2.me/theorems/cfe1ec21-e9ec-4b56-8270-2f71a73f9edf
-- title:
--   A Z-only allowed-basis projection for a tensor
-- statement:
--   Let $T$ be an order-three tensor over a field, and fix a basis of its $Z$-mode space together with a predicate selecting the allowed basis vectors. This definition gives a two-class grading in which every $X$- and $Y$-basis vector lies in class zero, while a $Z$-basis vector lies in class zero exactly when it is allowed. The all-zero graded block is therefore a single $Z$-mode projection of $T$; it does not take a direct sum of copies of $T$ and does not duplicate the $X$- or $Y$-mode spaces.
--
--   This is the generic linear-algebra operation used to model the component restriction $T_{i,j,k}^{\otimes n}[\widetilde\alpha]$ in a standard-form tensor: the split condition removes unavailable small $Z$-blocks while all small $X$- and $Y$-blocks remain present.
--
--   **Formalization Note** The selected $Z$ subspace is the span of the allowed members of the supplied basis. The complementary class spans the disallowed basis members, so the two classes form an internal direct sum even when the allowed set is empty or full.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Remark 5.1 and Definitions 5.2--5.4, PDF pp. 47--48 / printed pp. 46--47; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_CW_square_canonical_grading

/-!
# A basis-backed, Z-only projection grading

This is the generic linear-algebra interface needed for the restricted
component tensors `T_s[split_s]` in the DWZ standard-form construction.
The first two modes are placed wholly in grade zero.  A chosen basis of the
third mode is split into allowed and disallowed vectors.  Consequently the
all-zero block is one projection of the original tensor: it does not form a
direct sum of tensor copies and does not duplicate the X- or Y-mode spaces.
-/

universe u

namespace MME

open Module

variable {K : Type u} [Field K]

/-- The two-class grading which leaves modes zero and one unsplit and grades
the chosen basis of mode two by an allowed predicate. -/
noncomputable def TensorObj.basisZAllowedGrading
    (T : TensorObj K 3) {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (allowed : ι → Prop)
    [DecidablePred allowed] : T.TypeGrading 2 where
  decomp i := if h : i = (2 : Fin 3) then
      h.symm ▸ cwBasisGrade bZ
        (fun j ↦ if allowed j then 0 else 1)
    else
      cwBasisGrade (Module.finBasis K (T.V i))
        (fun _ ↦ (0 : Fin 2))
  is_internal i := by
    split
    · rename_i h
      exact h.symm ▸ cwBasisGrade_isInternal bZ
        (fun j ↦ if allowed j then 0 else 1)
    · exact cwBasisGrade_isInternal (Module.finBasis K (T.V i))
        (fun _ ↦ (0 : Fin 2))

/-- The selected all-zero block of `basisZAllowedGrading`.  This packages one
Z-mode projection of `T` as a tensor object while retaining the full first
and second mode classes. -/
noncomputable def TensorObj.basisZAllowedSubtensor
    (T : TensorObj K 3) {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (allowed : ι → Prop)
    [DecidablePred allowed] : TensorObj K 3 :=
  (T.basisZAllowedGrading bZ allowed).blockSubtensor (fun _ ↦ 0)

end MME


