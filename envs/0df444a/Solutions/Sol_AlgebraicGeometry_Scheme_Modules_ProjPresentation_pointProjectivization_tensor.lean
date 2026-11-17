-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.pointProjectivization_tensor
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:09.474472+00:00
-- url     : https://prove2.me/submissions/eb376f6a-f4d3-45bb-bc4f-f53213f88f12

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_chart
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_eq_of_chart
import Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_mem_basicOpen_iff
import Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointEquivProjectivization_kPointOfVec
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_appLE_awayToSection_eq_of_specMap
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_app_ratio_tensor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- Tensor sections give the products of the two homogeneous coordinate tuples. -/
theorem _root_.solution
    {K : Type} [Field K] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {L M : X.Modules} {N N' : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation f N')
    (idx : Fin (N * N' + N + N' + 1) ≃ Fin (N + 1) × Fin (N' + 1))
    (R : (L ⊗ M).ProjPresentation f (N * N' + N + N'))
    (hσ : ∀ k, R.σ k = Scheme.Modules.tensorSections (P.σ (idx k).1) (Q.σ (idx k).2))
    (hU : ∀ k, (P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).1)) ⊓
      (Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).2)) ≤
      R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k))
    (x : Scheme.KPoint f)
    (a : Fin (N+1) → K) (ha : a ≠ 0)
    (b : Fin (N'+1) → K) (hb : b ≠ 0)
    (hap : (ProjSpace.kPointOfVec K N a ha).1 = x.1 ≫ P.toProj)
    (hbp : (ProjSpace.kPointOfVec K N' b hb).1 = x.1 ≫ Q.toProj) :
    ∃ hc : (fun k => a (idx k).1 * b (idx k).2) ≠ 0,
      R.pointProjectivization x = Projectivization.mk K (fun k => a (idx k).1 * b (idx k).2) hc := by
  classical
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp ha
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hb
  obtain ⟨k,hi,hj⟩ : ∃ k, a (idx k).1 ≠ 0 ∧ b (idx k).2 ≠ 0 := by
    refine ⟨idx.symm (i₀,j₀),?_,?_⟩
    · simpa using hi₀
    · simpa using hj₀
  let i := (idx k).1
  let j := (idx k).2
  let W : X.Opens := (P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i)) ⊓
    (Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j))
  have hWP : W ≤ P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i) := inf_le_left
  have hWQ : W ≤ Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j) := inf_le_right
  have hWR : W ≤ R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k) := by
    exact hU k
  let p : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hxP : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤
      x.1 ⁻¹ᵁ (P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i)) := by
    intro q _
    have hq : q = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst q
    change (x.1 ≫ P.toProj) (IsLocalRing.closedPoint K) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) K) (MvPolynomial.X i)
    rw [← hap]
    exact (ProjSpace.kPointOfVec_mem_basicOpen_iff K N a ha i).mpr hi
  have hxQ : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤
      x.1 ⁻¹ᵁ (Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)) := by
    intro q _
    have hq : q = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst q
    change (x.1 ≫ Q.toProj) (IsLocalRing.closedPoint K) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N'+1)) K) (MvPolynomial.X j)
    rw [← hbp]
    exact (ProjSpace.kPointOfVec_mem_basicOpen_iff K N' b hb j).mpr hj
  have hxW : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤ x.1 ⁻¹ᵁ W :=
    fun q hq => ⟨hxP hq,hxQ hq⟩
  have hxR : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤
      x.1 ⁻¹ᵁ (R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k)) :=
    hxW.trans (x.1.preimage_mono hWR)
  let y : Scheme.KPoint (ProjSpace.π K (N*N'+N+N')) :=
    ⟨x.1 ≫ R.toProj, by rw [Category.assoc,R.toProj_π]; exact x.2⟩
  let ι := Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N*N'+N+N'+1)) K)
    (MvPolynomial.X k) (ProjSpace.X_mem_one K _ k) one_pos
  have hrange : Set.range y.1.base ⊆ Set.range ι.base := by
    rintro q ⟨q',rfl⟩
    change y.1 q' ∈ ι.opensRange
    rw [Proj.opensRange_awayι]
    exact hxR (show q' ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) from trivial)
  let g := IsOpenImmersion.lift ι y.1 hrange
  obtain ⟨φ,hφ⟩ := Spec.map_surjective g
  have hy : y.1 = Spec.map φ ≫ ι := by
    rw [hφ]
    exact (IsOpenImmersion.lift_fac ι y.1 hrange).symm
  obtain ⟨ψ,hψ,hachart⟩ := ProjSpace.kPointOfVec_chart K N a ha i hi
  obtain ⟨χ,hχ,hbchart⟩ := ProjSpace.kPointOfVec_chart K N' b hb j hj
  have hyP := hachart
  rw [hap] at hyP
  have hyQ := hbchart
  rw [hbp] at hyQ
  have eval_ratio {A : X.Modules} {d : ℕ} (T : A.ProjPresentation f d)
      (t : Fin (d+1))
      (hWT : W ≤ T.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X t))
      (θ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (d+1)) K)
        (MvPolynomial.X t) →+* K)
      (ht : x.1 ≫ T.toProj = Spec.map (CommRingCat.ofHom θ) ≫
        Proj.awayι _ (MvPolynomial.X t) (ProjSpace.X_mem_one K d t) one_pos)
      (l : Fin (d+1)) :
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom
        (x.1.appLE W ⊤ hxW (X.presheaf.map (homOfLE hWT).op
          (T.toProj.app (Proj.basicOpen _ (MvPolynomial.X t))
            (Proj.awayToSection _ (MvPolynomial.X t) (ProjSpace.ratio K d t l))))) =
        θ (ProjSpace.ratio K d t l) := by
    have hxt := hxW.trans (x.1.preimage_mono hWT)
    have he := appLE_awayToSection_eq_of_specMap (x.1 ≫ T.toProj) t θ ht hxt
      (ProjSpace.ratio K d t l)
    have hcomp : (x.1 ≫ T.toProj).appLE
        (Proj.basicOpen _ (MvPolynomial.X t)) ⊤ hxt =
        T.toProj.app (Proj.basicOpen _ (MvPolynomial.X t)) ≫
          x.1.appLE (T.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X t)) ⊤ hxt :=
      Scheme.Hom.comp_appLE x.1 T.toProj _ _ hxt
    rw [hcomp] at he
    simpa only [← ConcreteCategory.comp_apply, Category.assoc,
      Scheme.Hom.map_appLE, Scheme.Hom.map_appLE_assoc] using he
  let c : Fin (N*N'+N+N'+1) → K := fun l => a (idx l).1 * b (idx l).2
  have hck : c k ≠ 0 := by exact mul_ne_zero hi hj
  have hc : c ≠ 0 := by intro h; exact hck (congrFun h k)
  have hrat (l : Fin (N*N'+N+N'+1)) :
      φ.hom (ProjSpace.ratio K _ k l) = c l / c k := by
    have hs := P.app_ratio_tensor Q idx R hσ k l W
      hWP hWQ hWR
    have he := congrArg (fun s => (Scheme.ΓSpecIso (CommRingCat.of K)).hom
      (x.1.appLE W ⊤ hxW s)) hs
    rw [map_mul,map_mul] at he
    rw [eval_ratio R k hWR φ.hom hy l] at he
    have heP := eval_ratio P i hWP ψ hyP (idx l).1
    have heQ := eval_ratio Q j hWQ χ hyQ (idx l).2
    rw [heP,heQ,hψ,hχ] at he
    simpa only [c,i,j,mul_div_mul_comm] using he
  have hycoord := ProjSpace.kPointOfVec_eq_of_chart y c hc k hck φ.hom hrat hy
  refine ⟨hc,?_⟩
  change ProjSpace.kPointEquivProjectivization K _ y = Projectivization.mk K c hc
  rw [← hycoord]
  exact ProjSpace.kPointEquivProjectivization_kPointOfVec K _ c hc

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
