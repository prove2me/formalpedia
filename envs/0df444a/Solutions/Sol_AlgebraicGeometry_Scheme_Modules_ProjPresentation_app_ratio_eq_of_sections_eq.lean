-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.app_ratio_eq_of_sections_eq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:15:54.33622+00:00
-- url     : https://prove2.me/submissions/9e4283dd-6faa-44b3-99fd-dfb0dc8474de

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- Transporting a subsystem of sections preserves the corresponding coordinate ratios
on each original chart included in the new chart. -/
theorem _root_.solution {K : Type} [Field K]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {M₁ M₂ : X.Modules} {N₁ N₂ : ℕ}
    (P₁ : M₁.ProjPresentation f N₁) (P₂ : M₂.ProjPresentation f N₂)
    (e : M₁ ≅ M₂) (inc : Fin (N₁ + 1) → Fin (N₂ + 1))
    (hσ : ∀ i, e.hom.app ⊤ (P₁.σ i) = P₂.σ (inc i))
    (hU : ∀ i, P₁.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i) ≤
      P₂.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (inc i)))
    (i j : Fin (N₁ + 1)) :
    P₁.toProj.app (Proj.basicOpen _ (MvPolynomial.X i))
        (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio K N₁ i j)) =
      X.presheaf.map (homOfLE (hU i)).op
        (P₂.toProj.app (Proj.basicOpen _ (MvPolynomial.X (inc i)))
          (Proj.awayToSection _ (MvPolynomial.X (inc i))
            (ProjSpace.ratio K N₂ (inc i) (inc j)))) := by
  let U := P₁.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i)
  have hres (k : Fin (N₁ + 1)) :
      e.hom.app U (M₁.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (P₁.σ k)) =
        M₂.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (P₂.σ (inc k)) := by
    have hn := (e.hom.mapPresheaf).naturality (homOfLE (le_top : U ≤ ⊤)).op
    have hn' := congrFun (congrArg
      (fun t => (ConcreteCategory.hom t : Γ(M₁, ⊤) → Γ(M₂, U))) hn) (P₁.σ k)
    exact hn'.trans (congrArg (M₂.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) (hσ k))
  apply (P₂.frame (inc i) U (hU i)).injective
  have hleft := congrArg (e.hom.app U) (P₁.app_ratio_smul i j)
  simp only [Scheme.Modules.Hom.app_smul, hres] at hleft
  refine hleft.trans ?_
  symm
  have hright := congrArg (M₂.presheaf.map (homOfLE (hU i)).op)
    (P₂.app_ratio_smul (inc i) (inc j))
  simpa only [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← op_comp, homOfLE_comp] using hright

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
