-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.pointProjectivization_eq_mk_comp_of_sections_eq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:15:58.329204+00:00
-- url     : https://prove2.me/submissions/5d225f98-d079-46ae-8398-09e5673956a3

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_appLE_awayToSection_eq_of_specMap
import Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_mem_basicOpen_iff
import Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_chart
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointEquivProjectivization_kPointOfVec
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence
import Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_eq_of_chart
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_app_ratio_eq_of_sections_eq

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- A transported subsystem of a presentation has the restricted homogeneous coordinates. -/
theorem _root_.solution {K : Type} [Field K]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {M₁ M₂ : X.Modules} {N₁ N₂ : ℕ}
    (P₁ : M₁.ProjPresentation f N₁) (P₂ : M₂.ProjPresentation f N₂)
    (e : M₁ ≅ M₂) (inc : Fin (N₁ + 1) → Fin (N₂ + 1))
    (hσ : ∀ i, e.hom.app ⊤ (P₁.σ i) = P₂.σ (inc i))
    (hU : ∀ i, P₁.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i) ≤
      P₂.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (inc i)))
    (x : Scheme.KPoint f) (v : Fin (N₂ + 1) → K) (hv : v ≠ 0)
    (hvpoint : (ProjSpace.kPointOfVec K N₂ v hv).1 = x.1 ≫ P₂.toProj) :
    ∃ hinc : v ∘ inc ≠ 0,
      P₁.pointProjectivization x = Projectivization.mk K (v ∘ inc) hinc := by
  classical
  let y : Scheme.KPoint (ProjSpace.π K N₁) :=
    ⟨x.1 ≫ P₁.toProj, by rw [Category.assoc, P₁.toProj_π]; exact x.2⟩
  let p : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hcover := Proj.iSup_basicOpen_eq_top
    (MvPolynomial.homogeneousSubmodule (Fin (N₁ + 1)) K)
    (fun i : Fin (N₁ + 1) => MvPolynomial.X i) (ProjSpace.irrelevant_le_span_X K N₁)
  have hp : y.1 p ∈ (⨆ i : Fin (N₁ + 1),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N₁ + 1)) K) (MvPolynomial.X i)) := by
    rw [hcover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  have hxP : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤
      x.1 ⁻¹ᵁ (P₁.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i)) := by
    intro q hq
    have hqp : q = p := Subsingleton.elim _ _
    subst q
    exact hi
  have hxQ : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤
      x.1 ⁻¹ᵁ (P₂.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (inc i))) :=
    hxP.trans (x.1.preimage_mono (hU i))
  have hvi : v (inc i) ≠ 0 := by
    apply (ProjSpace.kPointOfVec_mem_basicOpen_iff K N₂ v hv (inc i)).mp
    rw [hvpoint]
    exact hxQ (show p ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) from trivial)
  have hinc : v ∘ inc ≠ 0 := by
    intro h
    exact hvi (congrFun h i)
  let a := Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N₁ + 1)) K)
    (MvPolynomial.X i) (ProjSpace.X_mem_one K N₁ i) one_pos
  have hrange : Set.range y.1.base ⊆ Set.range a.base := by
    rintro q ⟨q', rfl⟩
    change y.1 q' ∈ a.opensRange
    rw [Proj.opensRange_awayι]
    exact hxP (show q' ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) from trivial)
  let g := IsOpenImmersion.lift a y.1 hrange
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g
  have hy : y.1 = Spec.map φ ≫ a := by
    rw [hφ]
    exact (IsOpenImmersion.lift_fac a y.1 hrange).symm
  obtain ⟨ψ, hψ, hvchart⟩ := ProjSpace.kPointOfVec_chart K N₂ v hv (inc i) hvi
  have hyQ : x.1 ≫ P₂.toProj = Spec.map (CommRingCat.ofHom ψ) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N₂ + 1)) K)
        (MvPolynomial.X (inc i)) (ProjSpace.X_mem_one K N₂ (inc i)) one_pos := by
    rw [← hvpoint]
    exact hvchart
  have hrat (j : Fin (N₁ + 1)) :
      φ.hom (ProjSpace.ratio K N₁ i j) = (v ∘ inc) j / (v ∘ inc) i := by
    change φ.hom (ProjSpace.ratio K N₁ i j) = v (inc j) / v (inc i)
    have hs := P₁.app_ratio_eq_of_sections_eq P₂ e inc hσ hU i j
    have heval := congrArg (fun s => (Scheme.ΓSpecIso (CommRingCat.of K)).hom
      (x.1.appLE (P₁.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i)) ⊤ hxP s)) hs
    have hP := appLE_awayToSection_eq_of_specMap (x.1 ≫ P₁.toProj) i φ.hom hy hxP
      (ProjSpace.ratio K N₁ i j)
    have hQ := appLE_awayToSection_eq_of_specMap (x.1 ≫ P₂.toProj) (inc i) ψ hyQ hxQ
      (ProjSpace.ratio K N₂ (inc i) (inc j))
    rw [← hP, ← hψ (inc j), ← hQ]
    have hcompP : (x.1 ≫ P₁.toProj).appLE
        (Proj.basicOpen _ (MvPolynomial.X i)) ⊤ hxP =
        P₁.toProj.app (Proj.basicOpen _ (MvPolynomial.X i)) ≫
          x.1.appLE (P₁.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i)) ⊤ hxP :=
      Scheme.Hom.comp_appLE x.1 P₁.toProj _ _ hxP
    have hcompQ : (x.1 ≫ P₂.toProj).appLE
        (Proj.basicOpen _ (MvPolynomial.X (inc i))) ⊤ hxQ =
        P₂.toProj.app (Proj.basicOpen _ (MvPolynomial.X (inc i))) ≫
          x.1.appLE (P₂.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (inc i))) ⊤ hxQ :=
      Scheme.Hom.comp_appLE x.1 P₂.toProj _ _ hxQ
    rw [hcompP, hcompQ]
    simpa only [← ConcreteCategory.comp_apply, Category.assoc,
      Scheme.Hom.map_appLE, Scheme.Hom.map_appLE_assoc] using heval
  have hycoord : ProjSpace.kPointOfVec K N₁ (v ∘ inc) hinc = y :=
    ProjSpace.kPointOfVec_eq_of_chart y (v ∘ inc) hinc i hvi φ.hom hrat hy
  refine ⟨hinc, ?_⟩
  change ProjSpace.kPointEquivProjectivization K N₁ y = Projectivization.mk K (v ∘ inc) hinc
  rw [← hycoord]
  exact ProjSpace.kPointEquivProjectivization_kPointOfVec K N₁ (v ∘ inc) hinc

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
