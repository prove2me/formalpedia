-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.baseChange_addMor_subMor_comp_map
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:38.278256+00:00
-- url     : https://prove2.me/submissions/bc5e5b12-4f84-4d8a-962a-e3f3cea624ee

import Mathlib
import Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame
import Theorems.Thm_AlgebraicGeometry_Polarisation_baseChange_negMor_comp_fst

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.Polarisation

/-- Addition and subtraction commute with the canonical map on self-products after base change. -/
theorem _root_.solution {k k' : Type} [Field k] [Field k']
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)} (G : RelativeGroupLaw k f)
    (b : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) :
    let f' := pullback.snd f b
    let π := pullback.map f' f' f f (pullback.fst f b) (pullback.fst f b) b
      pullback.condition.symm pullback.condition.symm
    addMor f' (G.baseChange b) ≫ pullback.fst f b = π ≫ addMor f G ∧
      subMor f' (G.baseChange b) ≫ pullback.fst f b = π ≫ subMor f G := by
  dsimp only
  let f' := pullback.snd f b
  let g := pullback.fst f b
  let π := pullback.map f' f' f f g g b pullback.condition.symm pullback.condition.symm
  have hπ : π ≫ (pullback.fst f f ≫ f) =
      (pullback.fst f' f' ≫ f') ≫ b := by
    change π ≫ (pullback.fst f f ≫ f) = _
    rw [← Category.assoc]
    simp only [π, pullback.map, pullback.lift_fst]
    change (pullback.fst f' f' ≫ pullback.fst f b) ≫ f = _
    rw [Category.assoc, pullback.condition, ← Category.assoc]
  have ha : addMor f' (G.baseChange b) ≫ g = π ≫ addMor f G := by
    have h := congrArg Subtype.val (G.mul_natural (pullback.fst f f ≫ f)
      ((pullback.fst f' f' ≫ f') ≫ b) π hπ
      ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
    simpa [addMor, RelativeGroupLaw.baseChange, RelativeGroupLaw.baseChangePointOfBase,
      RelativeGroupLaw.baseChangePointToBase, GoodReductionJacobian.schemeHomOverComp,
      π, pullback.map, f', g, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc] using h.symm
  refine ⟨ha, ?_⟩
  let r := pullback.lift (pullback.fst f f) (pullback.snd f f ≫ negMor f G)
    (by rw [Category.assoc, negMor_over]; exact pullback.condition)
  let r' := pullback.lift (pullback.fst f' f') (pullback.snd f' f' ≫ negMor f' (G.baseChange b))
    (by rw [Category.assoc, negMor_over]; exact pullback.condition)
  have hr : r' ≫ π = π ≫ r := by
    apply pullback.hom_ext
    · simp [r', r, π, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    · simp only [r', r, π, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc]
      exact congrArg (fun t => pullback.snd f' f' ≫ t) (baseChange_negMor_comp_fst G b)
  change (r' ≫ addMor f' (G.baseChange b)) ≫ g = π ≫ (r ≫ addMor f G)
  rw [Category.assoc, ha, ← Category.assoc, hr, Category.assoc]

end AlgebraicGeometry.Polarisation
