-- Prove2me | Definitions.Def_mme_dwz_global_ambient_conditioned_broken_copy
-- name    : mme_dwz_global_ambient_conditioned_broken_copy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-28T02:42:54.189637+00:00
-- url     : https://prove2.me/theorems/123aef73-ce9d-4f06-9bcd-8465d17df081
-- title:
--   Ambient conditioned broken copies for aggregate DWZ hashing
-- statement:
--   Fix an exact-profile Table-2 outer word and a finite ambient family of exact-profile competitors. Restrict competitors to those with the same complete coarse-Z address. For a useful fine block z and a common affine weight word w, retain a competitor exactly when it satisfies the Table-2 fine compatibility constraints and its X-hash equals the Z-hash at the owner-conditioned value. The ambient conditioned broken copy keeps the useful blocks for which the retained owner is unique among all such competitors.
--
--   This is the pre-selection object counted by the aggregate form of Claim 6.8. A later canonical first-hash selection restricts the competitor family; monotonicity then transports its nonhole mass to the selected common-state broken copy.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Additional Zeroing-Out Step 2, Definition 6.3, and Claim 6.8, printed pp. 51--55; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_retained_fine_compatibility
import Definitions.Def_mme_dwz_step2_broken_copy
import Definitions.Def_mme_dwz_table2_useful_block

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZGlobalCorrelated

/-!
# Ambient exact-profile conditioned broken copy

This packages the literal broken copy whose nonhole cardinality is counted by
the ownerwise aggregate Claim 6.8 theorem, before the canonical first-hash
selector deletes competing owners.  Only the common affine weight word and
the owner-conditioned second-hash value enter this definition.
-/

noncomputable def ambientConditionedBrokenCopy
    (m : ℕ) {p N L : ℕ} (reindex : Fin (N + 1) ≃ Fin L)
    (T : Finset (Fin L → Fin 15))
    (retained : Fin L → Fin 15) (hretained : retained ∈ T)
    (weight : Fin (N + 1) → ZMod p) :
    MME.DWZSquare.BrokenBlockCopy
      (MME.DWZTable2StandardForm.UsefulBlock m retained) := by
  classical
  let sameZ : (Fin L → Fin 15) → Prop := fun w ↦
    ∀ t, MME.DWZSquare.shapeZ (w t) =
      MME.DWZSquare.shapeZ (retained t)
  let Outer := {w : Fin L → Fin 15 // w ∈ T ∧ sameZ w}
  let grade : MME.DWZTable2StandardForm.UsefulBlock m retained →
      Fin L → Fin (3 * 3) := fun z t ↦
    MME.DWZStep1Support.fineSplitGrade (z.1 t).1 (z.1 t).2
  let compatible : MME.DWZTable2StandardForm.UsefulBlock m retained →
      Outer → Prop := fun z A ↦
    MME.DWZStep2Source.retainedFineCompatible m
      (fun w : Fin L → Fin 15 ↦ w) (grade z) A.1
  let addressX : Outer → Fin (N + 1) → Fin 5 := fun A t ↦
    MME.DWZSquare.shapeX (A.1 (reindex t))
  let addressZ : Fin (N + 1) → Fin 5 := fun t ↦
    MME.DWZSquare.shapeZ (retained (reindex t))
  let conditionedW0 : ZMod p :=
    2 * (∑ t,
      (((MME.DWZSquare.shapeX (retained (reindex t))).val : ℕ) :
        ZMod p) * weight t) -
      ∑ t, ((4 : ZMod p) - (addressZ t).val) * weight t
  let hashRetained : Outer → Prop := fun A ↦
    (∑ t, (((addressX A) t).val : ZMod p) * weight t) =
      (2 : ZMod p)⁻¹ *
        (conditionedW0 +
          ∑ t, ((4 : ZMod p) - (addressZ t).val) * weight t)
  let retainedOuter : Outer := ⟨retained, hretained, fun _ ↦ rfl⟩
  exact MME.DWZStep2.brokenCopy
    (fun z A ↦ compatible z A ∧ hashRetained A)
    (fun _ _ ↦ True) retainedOuter

end MME.DWZGlobalCorrelated


