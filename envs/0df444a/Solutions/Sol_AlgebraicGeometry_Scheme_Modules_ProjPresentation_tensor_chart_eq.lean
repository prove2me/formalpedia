-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.tensor_chart_eq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:46.92898+00:00
-- url     : https://prove2.me/submissions/54c47308-c863-4175-8baf-0e270fd86108

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_app_ratio_tensor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_mem_chart_of_isUnit_ratio

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- A tensor presentation has exactly the product coordinate charts. -/
theorem _root_.solution
    {K : Type} [Field K] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {L M : X.Modules} {N N' : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation f N')
    (idx : Fin (N*N'+N+N'+1) ≃ Fin (N+1) × Fin (N'+1))
    (R : (L ⊗ M).ProjPresentation f (N*N'+N+N'))
    (hσ : ∀ k, R.σ k = Scheme.Modules.tensorSections (P.σ (idx k).1) (Q.σ (idx k).2))
    (hU : ∀ k, (P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).1)) ⊓
      (Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).2)) ≤
      R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k))
    (k : Fin (N*N'+N+N'+1)) :
    R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k) =
      (P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).1)) ⊓
        (Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).2)) := by
  apply le_antisymm ?_ (hU k)
  intro x hx
  have coverP : (⨆ i : Fin (N+1), P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i)) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup,
      Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X K N)]
    rfl
  have coverQ : (⨆ j : Fin (N'+1), Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup,
      Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X K N')]
    rfl
  have hp : x ∈ (⨆ i : Fin (N+1), P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i)) := by rw [coverP]; trivial
  have hq : x ∈ (⨆ j : Fin (N'+1), Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)) := by rw [coverQ]; trivial
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  obtain ⟨j,hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hq
  let l := idx.symm (i,j)
  have hli : (idx l).1 = i := by simp [l]
  have hlj : (idx l).2 = j := by simp [l]
  let O : X.Opens := (R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k)) ⊓
    ((P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx l).1)) ⊓
      (Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx l).2)))
  have hi' : x ∈ P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx l).1) := by
    rw [hli]
    exact hi
  have hj' : x ∈ Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx l).2) := by
    rw [hlj]
    exact hj
  have hxO : x ∈ O := ⟨hx,hi',hj'⟩
  have hOk : O ≤ R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k) := inf_le_left
  have hOl : O ≤ R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X l) := inf_le_right.trans (hU l)
  have hOP : O ≤ P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx l).1) := inf_le_right.trans inf_le_left
  have hOQ : O ≤ Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx l).2) := inf_le_right.trans inf_le_right
  let c := X.presheaf.map (homOfLE hOl).op
    (R.toProj.app (Proj.basicOpen _ (MvPolynomial.X l))
      (Proj.awayToSection _ (MvPolynomial.X l) (ProjSpace.ratio K _ l k)))
  have hc : c • (L ⊗ M).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (R.σ l) =
      (L ⊗ M).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (R.σ k) := by
    dsimp only [c]
    have ht := congrArg ((L ⊗ M).presheaf.map (homOfLE hOl).op) (R.app_ratio_smul l k)
    simpa only [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp, homOfLE_comp] using ht
  obtain ⟨d,hd⟩ := (R.frame k O hOk).surjective
    ((L ⊗ M).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (R.σ l))
  dsimp only at hd
  have hdc : d*c = 1 := by
    apply (R.frame l O hOl).injective
    dsimp only
    rw [mul_smul,hc,hd,one_smul]
  have hu : IsUnit c := isUnit_iff_exists_inv'.mpr ⟨d,hdc⟩
  dsimp only [c] at hu
  rw [P.app_ratio_tensor Q idx R hσ l k O hOP hOQ hOl] at hu
  exact ⟨P.mem_chart_of_isUnit_ratio hOP hxO (isUnit_of_mul_isUnit_left hu),
    Q.mem_chart_of_isUnit_ratio hOQ hxO (isUnit_of_mul_isUnit_right hu)⟩

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
