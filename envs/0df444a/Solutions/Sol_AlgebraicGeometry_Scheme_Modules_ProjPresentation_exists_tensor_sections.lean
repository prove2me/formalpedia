-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_tensor_sections
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:06:17.620955+00:00
-- url     : https://prove2.me/submissions/d7f8ce4b-9bf1-4e67-ab4f-950889818036

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- The full tensor tuple gives a presentation, with every product chart retained. -/
theorem _root_.solution
    {K : Type} [Field K] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {L M : X.Modules} {N N' : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation f N') :
    ∃ (idx : Fin (N * N' + N + N' + 1) ≃ Fin (N + 1) × Fin (N' + 1))
      (R : (L ⊗ M).ProjPresentation f (N * N' + N + N')),
      (∀ k, R.σ k = Scheme.Modules.tensorSections (P.σ (idx k).1) (Q.σ (idx k).2)) ∧
      ∀ k, (P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).1)) ⊓
        (Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).2)) ≤
        R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k) := by
  classical
  have hcard : (N + 1) * (N' + 1) = N * N' + N + N' + 1 := by ring
  let idx : Fin (N * N' + N + N' + 1) ≃ Fin (N + 1) × Fin (N' + 1) :=
    (finCongr hcard.symm).trans finProdFinEquiv.symm
  let U : Fin (N * N' + N + N' + 1) → X.Opens := fun k =>
    (P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).1)) ⊓
      (Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).2))
  have hcoverP : (⨆ i : Fin (N + 1), P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i)) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup,
      Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X K N)]
    rfl
  have hcoverQ : (⨆ j : Fin (N' + 1), Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup,
      Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X K N')]
    rfl
  have hcover : iSup U = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    have hp : x ∈ (⨆ i : Fin (N + 1), P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i)) := by
      rw [hcoverP]; trivial
    have hq : x ∈ (⨆ j : Fin (N' + 1), Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)) := by
      rw [hcoverQ]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hq
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨idx.symm (i, j), ?_⟩
    change x ∈ (P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx (idx.symm (i,j))).1)) ⊓
      (Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx (idx.symm (i,j))).2))
    rw [Equiv.apply_symm_apply]
    exact ⟨hi, hj⟩
  have hframe (k : Fin (N * N' + N + N' + 1)) :
      Scheme.Modules.IsFrameOn
        (Scheme.Modules.tensorSections (P.σ (idx k).1) (Q.σ (idx k).2)) (U k) := by
    apply Scheme.Modules.IsFrameOn.tensorSections_monoidalV2
    · exact fun _ _ h => P.frame _ _ (h.trans inf_le_left)
    · exact fun _ _ h => Q.frame _ _ (h.trans inf_le_right)
  obtain ⟨R, hσ, hU⟩ := Scheme.Modules.exists_projPresentation_of_iSup_eq_top f (L ⊗ M)
    (N * N' + N + N') (fun k => Scheme.Modules.tensorSections (P.σ (idx k).1) (Q.σ (idx k).2))
    U hcover (fun k _ h => hframe k le_top h)
  exact ⟨idx, R, fun k => congrFun hσ k, hU⟩

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
