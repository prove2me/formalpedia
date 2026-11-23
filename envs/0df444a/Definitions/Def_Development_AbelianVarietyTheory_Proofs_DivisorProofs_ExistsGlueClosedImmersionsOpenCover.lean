-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueClosedImmersionsOpenCover
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueClosedImmersionsOpenCover
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:00.844696+00:00
-- url     : https://prove2.me/theorems/406477e2-44f5-48d5-85e8-9d9a31ab2bc3
-- title:
--   Exists Glue Closed Immersions Open Cover
-- statement:
--   Definitions and structural lemmas for Exists Glue Closed Immersions Open Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlueClosedImmersionsOpenCover.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.GlueClosed
theorem exists_lift_eq {X : Scheme.{0}} (U V : X.Opens) (x : (pullback U.ι V.ι).carrier) :
    ∃ y : (U ⊓ V).toScheme, pullback.lift (X.homOfLE (inf_le_left : U ⊓ V ≤ U))
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (by simp) y = x := by
  have hx : U.ι (pullback.fst U.ι V.ι x) ∈ U ⊓ V := by
    refine ⟨(pullback.fst U.ι V.ι x).2, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact (pullback.snd U.ι V.ι x).2
  obtain ⟨y, hy⟩ : ∃ y : (U ⊓ V).toScheme, (U ⊓ V).ι y = U.ι (pullback.fst U.ι V.ι x) :=
    ⟨⟨_, hx⟩, rfl⟩
  refine ⟨y, ?_⟩
  apply (pullback.fst U.ι V.ι ≫ U.ι).isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply _ (pullback.fst U.ι V.ι ≫ U.ι), pullback.lift_fst_assoc,
    Scheme.homOfLE_ι, hy]
  rfl
section
variable {X : Scheme.{0}} (S : Set X.Opens) (hcov : ∀ x : X, ∃ U ∈ S, x ∈ U)
noncomputable def coverOfSet : X.OpenCover where
  I₀ := S
  X U := U.1.toScheme
  f U := U.1.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun U ↦ inferInstanceAs (IsOpenImmersion U.1.ι)⟩
    obtain ⟨U, hU, hx⟩ := hcov x
    exact ⟨⟨U, hU⟩, ⟨x, hx⟩, rfl⟩
instance : Preorder (coverOfSet S hcov).I₀ := inferInstanceAs (Preorder S)
@[reducible] noncomputable def locallyDirected (hinf : ∀ U ∈ S, ∀ V ∈ S, U ⊓ V ∈ S) :
    (coverOfSet S hcov).LocallyDirected where
  trans {U V} h := X.homOfLE (show U.1 ≤ V.1 from h.le)
  trans_id U := X.homOfLE_rfl _
  trans_comp h k := (X.homOfLE_homOfLE _ _).symm
  w h := X.homOfLE_ι _
  directed {U V} x := by
    obtain ⟨y, hy⟩ := exists_lift_eq U.1 V.1 x
    exact ⟨⟨U.1 ⊓ V.1, hinf _ U.2 _ V.2⟩, homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1),
      homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1), y, hy⟩
  property_trans h := inferInstanceAs (IsOpenImmersion (X.homOfLE _))
end
end GlobalTheory.GlueClosed


