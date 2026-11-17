-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.isFinite_of_external_charts
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:08.34725+00:00
-- url     : https://prove2.me/submissions/0f1c5413-9c56-4f7b-92d2-7bbf9a7b3be6

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

private theorem affine_product_chart
    {X Y S : Scheme.{0}} [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S)
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
  let φ := pullback.map (hU.fromSpec ≫ f) (hV.fromSpec ≫ g) f g
    hU.fromSpec hV.fromSpec (𝟙 S) (by simp) (by simp)
  have hrange : Scheme.Hom.opensRange φ =
      pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V := by
    ext x
    show x ∈ Set.range φ ↔ x ∈
      ((pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V : (CategoryTheory.Limits.pullback f g).Opens) : Set _)
    rw [Scheme.Pullback.range_map, IsAffineOpen.range_fromSpec, IsAffineOpen.range_fromSpec]
    rfl
  rw [← hrange]
  exact isAffineOpen_opensRange φ

/-- A presentation whose standard charts are products of finite presentation charts is finite. -/
theorem _root_.solution
    {K : Type} [Field K] {X Y : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of K)} {g : Y ⟶ Spec (CommRingCat.of K)}
    {L : X.Modules} {M : Y.Modules} {N N' NR : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation g N')
    (hP : IsFinite P.toProj) (hQ : IsFinite Q.toProj)
    {T : (CategoryTheory.Limits.pullback f g).Modules}
    (R : T.ProjPresentation (pullback.fst f g ≫ f) NR)
    (idx : Fin (NR + 1) → Fin (N + 1) × Fin (N' + 1))
    (hc : ∀ k, R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k) =
      pullback.fst f g ⁻¹ᵁ (P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).1)) ⊓
      pullback.snd f g ⁻¹ᵁ (Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).2))) :
    IsFinite R.toProj := by
  haveI := hP
  haveI := hQ
  haveI : IsProper f := by rw [← P.toProj_π]; infer_instance
  haveI : IsProper g := by rw [← Q.toProj_π]; infer_instance
  rw [IsFinite.iff_isProper_and_isAffineHom]
  constructor
  · haveI : IsProper (R.toProj ≫ ProjSpace.π K NR) := by
      rw [R.toProj_π]
      infer_instance
    exact IsProper.of_comp R.toProj (ProjSpace.π K NR)
  · rw [HasAffineProperty.iff_of_iSup_eq_top (P := @IsAffineHom.{0})
      (fun k : Fin (NR + 1) =>
        (⟨Proj.basicOpen _ (MvPolynomial.X k),
          Proj.isAffineOpen_basicOpen _ (MvPolynomial.X k)
            (ProjSpace.X_mem_one K NR k) one_pos⟩ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (NR + 1)) K)).affineOpens))
      (Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X K NR))]
    intro k
    change IsAffineOpen (R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k))
    rw [hc k]
    exact affine_product_chart f g
      ((Proj.isAffineOpen_basicOpen _ (MvPolynomial.X (idx k).1)
        (ProjSpace.X_mem_one K N (idx k).1) one_pos).preimage P.toProj)
      ((Proj.isAffineOpen_basicOpen _ (MvPolynomial.X (idx k).2)
        (ProjSpace.X_mem_one K N' (idx k).2) one_pos).preimage Q.toProj)

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
