-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_projMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/9f79e3b0-ebe9-52f3-ac7d-9538dec8efc9

import Mathlib
import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_projMap

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_projMap.AlgebraicGeometry HomogeneousLocalization"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Proj.awayι_toSpecZero_assoc Proj.awayι_comp_map_assoc Scheme.Hom Scheme.Hom.appLE_comp_appLE Proj.awayToSection_comp_appLE Spec Spec.map Scheme Proj.awayι Proj.toSpecZero Proj Proj.mapAffineOpenCover Proj.basicOpen Scheme.Modules Proj.awayToSection Proj.map GradedOAlgebra.IsCanonicalToProj"
namespace GradedOAlgebra
p2m_export "AlgebraicGeometry.GradedOAlgebra" "IsCanonicalToProj"
namespace CompProjMap
p2m_open "AlgebraicGeometry.GradedOAlgebra AlgebraicGeometry"

variable {S : Type u} [CommRing S] {S' : Type u} [CommRing S'] [Algebra S S']
    {R : Type u} [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    {R' : Type u} [CommRing R'] [Algebra S' R'] [Algebra S R'] [IsScalarTower S S' R']
    (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ϑ : R →ₐ[S] R') (hϑdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)

abbrev ϑg : 𝓡 →+*ᵍ 𝓡' := { ϑ.toRingHom with map_mem := fun {_ _} h => hϑdeg _ _ h }

theorem ϑg_apply (x : R) : ϑg 𝓡 𝓡' ϑ hϑdeg x = ϑ x := rfl

theorem awayMap_fromZero_compat (t : R) :
    (Away.map (ϑg 𝓡 𝓡' ϑ hϑdeg) t).comp
        ((fromZeroRingHom 𝓡 _).comp ((GradedRing.projZeroRingHom' 𝓡).comp (algebraMap S R)))
      = ((fromZeroRingHom 𝓡' _).comp ((GradedRing.projZeroRingHom' 𝓡').comp (algebraMap S' R'))).comp
          (algebraMap S S') := by
  ext x
  have h1 : GradedRing.projZeroRingHom' 𝓡 (algebraMap S R x) = ⟨algebraMap S R x, SetLike.algebraMap_mem_graded 𝓡 x⟩ :=
    GradedRing.projZeroRingHom'_apply_coe 𝓡 ⟨_, _⟩
  have h2 : GradedRing.projZeroRingHom' 𝓡' (algebraMap S' R' (algebraMap S S' x))
      = ⟨algebraMap S' R' (algebraMap S S' x), SetLike.algebraMap_mem_graded 𝓡' _⟩ :=
    GradedRing.projZeroRingHom'_apply_coe 𝓡' ⟨_, _⟩
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [h1, h2]
  show (Localization.mk _ _ : Localization.Away ((ϑg 𝓡 𝓡' ϑ hϑdeg) t)) = Localization.mk _ _
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
  simp [ϑg_apply, IsScalarTower.algebraMap_apply S S' R']

variable (hirr : HomogeneousIdeal.irrelevant 𝓡' ≤
      (HomogeneousIdeal.irrelevant 𝓡).map (ϑg 𝓡 𝓡' ϑ hϑdeg))

theorem w_chart {d : ℕ} (hd : 0 < d) (t : R) (ht : t ∈ 𝓡 d) :
    Proj.awayι 𝓡' ((ϑg 𝓡 𝓡' ϑ hϑdeg) t) ((ϑg 𝓡 𝓡' ϑ hϑdeg).map_mem ht) hd
      ≫ Proj.map (ϑg 𝓡 𝓡' ϑ hϑdeg) hirr ≫ Proj.toSpecZero 𝓡
        ≫ Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' 𝓡).comp (algebraMap S R)))
    = Proj.awayι 𝓡' ((ϑg 𝓡 𝓡' ϑ hϑdeg) t) ((ϑg 𝓡 𝓡' ϑ hϑdeg).map_mem ht) hd
      ≫ Proj.toSpecZero 𝓡'
        ≫ Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' 𝓡').comp (algebraMap S' R')))
        ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')) := by
  rw [Proj.awayι_comp_map_assoc (ϑg 𝓡 𝓡' ϑ hϑdeg) hirr hd t ht, Proj.awayι_toSpecZero_assoc,
    Proj.awayι_toSpecZero_assoc]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  simpa only [RingHom.comp_assoc] using awayMap_fromZero_compat 𝓡 𝓡' ϑ hϑdeg t

theorem w :
    Proj.map (ϑg 𝓡 𝓡' ϑ hϑdeg) hirr ≫ Proj.toSpecZero 𝓡
        ≫ Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' 𝓡).comp (algebraMap S R)))
      = Proj.toSpecZero 𝓡'
        ≫ Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' 𝓡').comp (algebraMap S' R')))
        ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')) := by
  refine (Proj.mapAffineOpenCover (ϑg 𝓡 𝓡' ϑ hϑdeg) hirr).openCover.hom_ext _ _ fun i => ?_
  obtain ⟨⟨d, hd⟩, t, ht⟩ := i
  exact w_chart 𝓡 𝓡' ϑ hϑdeg hirr hd t ht

end AlgebraicGeometry.GradedOAlgebra.CompProjMap

end

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_projMap.AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization"

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    {X' : Scheme.{u}} (f' : X' ⟶ Spec (CommRingCat.of S')) (L' : X'.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (R' : Type u) [CommRing R'] [Algebra S' R'] [Algebra S R'] [IsScalarTower S S' R']
    (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ι' : ∀ n : ℕ, 𝓡' n → Γ(L'.tensorPow n, ⊤))
    (ϑ : R →ₐ[S] R') (hϑdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)
    (hirr : HomogeneousIdeal.irrelevant 𝓡' ≤
      (HomogeneousIdeal.irrelevant 𝓡).map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡'))
    (θ' : X' ⟶ Proj 𝓡') (hθ' : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f' L' R' 𝓡' ι' θ') :
    AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S'))) L' R 𝓡
      (fun (n : ℕ) (x : 𝓡 n) => ι' n ⟨ϑ x, hϑdeg n x x.2⟩)
      (θ' ≫ Proj.map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') hirr) := by

  change AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj _ L' R 𝓡 _
    (θ' ≫ Proj.map (AlgebraicGeometry.GradedOAlgebra.CompProjMap.ϑg 𝓡 𝓡' ϑ hϑdeg) hirr)
  set ϑg := AlgebraicGeometry.GradedOAlgebra.CompProjMap.ϑg 𝓡 𝓡' ϑ hϑdeg with hϑg
  have hϑg_apply : ∀ x, ϑg x = ϑ x := fun x => rfl
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [Category.assoc, AlgebraicGeometry.GradedOAlgebra.CompProjMap.w 𝓡 𝓡' ϑ hϑdeg hirr,
      ← hθ'.comp_toSpecZero]
    simp only [Category.assoc]
  ·
    intro n hn σ
    exact hθ'.isFrameOn n hn ⟨ϑ σ, hϑdeg n σ σ.2⟩
  ·
    intro n hn σ k s

    have hσ' : ϑ (σ : R) ∈ 𝓡' n := hϑdeg n σ σ.2
    have hs' : ϑ (s : R) ∈ 𝓡' (k • n) := hϑdeg _ s s.2
    have key := hθ'.appLE_awayToSection_smul n hn ⟨ϑ σ, hσ'⟩ k ⟨ϑ s, hs'⟩

    have hpow : (⟨ϑ ((⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩ : 𝓡 (k • n)) : R),
        hϑdeg (k • n) _ (SetLike.pow_mem_graded k σ.2)⟩ : 𝓡' (k • n))
        = ⟨((⟨ϑ σ, hσ'⟩ : 𝓡' n) : R') ^ k, SetLike.pow_mem_graded k hσ'⟩ :=
      Subtype.ext (map_pow ϑ _ _)

    have hV : (θ' ≫ Proj.map ϑg hirr) ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)
        = θ' ⁻¹ᵁ Proj.basicOpen 𝓡' ((⟨ϑ σ, hσ'⟩ : 𝓡' n) : R') := rfl

    have happ : (θ' ≫ Proj.map ϑg hirr).appLE (Proj.basicOpen 𝓡 (σ : R))
          ((θ' ≫ Proj.map ϑg hirr) ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) le_rfl
          (Proj.awayToSection 𝓡 (σ : R) (Away.mk 𝓡 σ.2 k (s : R) s.2))
        = θ'.appLE (Proj.basicOpen 𝓡' ((⟨ϑ σ, hσ'⟩ : 𝓡' n) : R'))
            (θ' ⁻¹ᵁ Proj.basicOpen 𝓡' ((⟨ϑ σ, hσ'⟩ : 𝓡' n) : R')) le_rfl
            (Proj.awayToSection 𝓡' ((⟨ϑ σ, hσ'⟩ : 𝓡' n) : R') (Away.mk 𝓡' hσ' k (ϑ s) hs')) := by
      have hc := Scheme.Hom.appLE_comp_appLE θ' (Proj.map ϑg hirr) (Proj.basicOpen 𝓡 (σ : R))
        (Proj.basicOpen 𝓡' (ϑg σ)) (θ' ⁻¹ᵁ Proj.basicOpen 𝓡' (ϑg σ)) (by rfl) le_rfl
      have hc' := congrArg (fun φ => φ (Proj.awayToSection 𝓡 (σ : R) (Away.mk 𝓡 σ.2 k (s : R) s.2))) hc
      simp only [CommRingCat.comp_apply] at hc'
      have ha : (Proj.map ϑg hirr).appLE (Proj.basicOpen 𝓡 (σ : R)) (Proj.basicOpen 𝓡' (ϑg σ)) (by rfl)
            (Proj.awayToSection 𝓡 (σ : R) (Away.mk 𝓡 σ.2 k (s : R) s.2))
          = Proj.awayToSection 𝓡' (ϑg σ) (Away.map ϑg (σ : R) (Away.mk 𝓡 σ.2 k (s : R) s.2)) :=
        ConcreteCategory.congr_hom (Proj.awayToSection_comp_appLE ϑg hirr σ.2) (Away.mk 𝓡 σ.2 k (s : R) s.2)
      rw [Away.map_mk] at ha
      rw [ha] at hc'
      exact hc'.symm
    rw [happ]
    convert key using 2 <;>
      first
        | exact congrArg _ (congrArg _ hpow)
        | exact heq_of_eq (congrArg _ (congrArg _ hpow))
        | exact hirr
        | rfl

end S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_projMap
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_projMap (solution)
