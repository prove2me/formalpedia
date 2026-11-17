-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.app_ratio_tensor
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:45.020232+00:00
-- url     : https://prove2.me/submissions/d6e80826-1c5e-451c-a0b5-72942c37a9c6

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- On a product chart the tensor coordinates have the product of the two ratios. -/
theorem _root_.solution
    {K : Type} [Field K] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {L M : X.Modules} {N N' : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation f N')
    (idx : Fin (N * N' + N + N' + 1) ≃ Fin (N + 1) × Fin (N' + 1))
    (R : (L ⊗ M).ProjPresentation f (N * N' + N + N'))
    (hσ : ∀ k, R.σ k = Scheme.Modules.tensorSections (P.σ (idx k).1) (Q.σ (idx k).2))
    (k l : Fin (N * N' + N + N' + 1))
    (W : X.Opens)
    (hP : W ≤ P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).1))
    (hQ : W ≤ Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).2))
    (hR : W ≤ R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k)) :
    X.presheaf.map (homOfLE hR).op
      (R.toProj.app (Proj.basicOpen _ (MvPolynomial.X k))
        (Proj.awayToSection _ (MvPolynomial.X k) (ProjSpace.ratio K _ k l))) =
    X.presheaf.map (homOfLE hP).op
      (P.toProj.app (Proj.basicOpen _ (MvPolynomial.X (idx k).1))
        (Proj.awayToSection _ (MvPolynomial.X (idx k).1)
          (ProjSpace.ratio K _ (idx k).1 (idx l).1))) *
    X.presheaf.map (homOfLE hQ).op
      (Q.toProj.app (Proj.basicOpen _ (MvPolynomial.X (idx k).2))
        (Proj.awayToSection _ (MvPolynomial.X (idx k).2)
          (ProjSpace.ratio K _ (idx k).2 (idx l).2))) := by
  have restrict_ratio {A : X.Modules} {d : ℕ} (T : A.ProjPresentation f d)
      (i j : Fin (d + 1)) (h : W ≤ T.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i)) :
      X.presheaf.map (homOfLE h).op
        (T.toProj.app (Proj.basicOpen _ (MvPolynomial.X i))
          (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio K d i j))) •
        A.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (T.σ i) =
        A.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (T.σ j) := by
    have ht := congrArg (A.presheaf.map (homOfLE h).op) (T.app_ratio_smul i j)
    simpa only [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp, homOfLE_comp] using ht
  apply (R.frame k W hR).injective
  dsimp only
  rw [restrict_ratio R k l hR, hσ k, hσ l,
    Scheme.Modules.map_homOfLE_tensorSections, Scheme.Modules.map_homOfLE_tensorSections]
  rw [mul_smul, ← Scheme.Modules.tensorSections_smul_right,
    ← Scheme.Modules.tensorSections_smul_left, restrict_ratio Q _ _ hQ, restrict_ratio P _ _ hP]

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
