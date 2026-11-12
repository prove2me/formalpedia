-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ConjugationFieldModel
-- name    : OddOrder_GroupTheory_RepresentationTheory_ConjugationFieldModel
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:29:04.243068+00:00
-- url     : https://prove2.me/theorems/7c2efe52-2054-4cde-81bd-f29411a94c85
-- title:
--   Galois-field models for faithful conjugation actions
-- statement:
--   Supplies the group-level adapter between the abstract Singer mechanism and the semilinear field-model embedding used in Peterfalvi (14.2)(a) and (14.4).
--
--   Main declarations: `conjugate` (Conjugation of `x ∈ E` by `c ∈ C`, transported back to `E` using `C ≤ N_G(E)`).
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ConjugationFieldModel.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ConjugationFieldModel.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_NormSet
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorMaschke
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerField

namespace OddOrder.RepresentationTheory.ConjugationFieldModel

open OddOrder.GroupTheory

open OddOrder.BG.AppC.NormSet

variable {G : Type*} [Group G]

/-- Conjugation of `x ∈ E` by `c ∈ C`, transported back to `E` using `C ≤ N_G(E)`. -/
def conjugate {E C : Subgroup G} (hCnorm : C ≤ Subgroup.normalizer (E : Set G))
    (c : ↥C) (x : ↥E) : ↥E :=
  ⟨(c : G) * (x : G) * (c : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hCnorm c.2) (x : G)).mp x.2⟩

@[simp] theorem conjugate_val {E C : Subgroup G}
    (hCnorm : C ≤ Subgroup.normalizer (E : Set G)) (c : ↥C) (x : ↥E) :
    (conjugate hCnorm c x : G) = (c : G) * (x : G) * (c : G)⁻¹ :=
  rfl

end OddOrder.RepresentationTheory.ConjugationFieldModel


