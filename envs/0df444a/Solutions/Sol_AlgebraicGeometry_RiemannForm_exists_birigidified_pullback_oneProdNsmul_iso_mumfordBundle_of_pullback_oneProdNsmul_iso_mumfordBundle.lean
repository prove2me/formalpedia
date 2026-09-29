-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.exists_birigidified_pullback_oneProdNsmul_iso_mumfordBundle_of_pullback_oneProdNsmul_iso_mumfordBundle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/56db5ec1-01d2-5bb4-ba19-3fd769ddd0f5

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_sliceAt_zero_mumfordBundle_iso_unit_and_swap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_exists_birigidified_pullback_oneProdNsmul_iso_mumfordBundle_of_pullback_oneProdNsmul_iso_mumfordBundle
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.sndPoint_coe GoodReductionJacobian.RelativeGroupLaw.fstPoint_coe"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm AlgebraicGeometry.Polarisation"

namespace BiRigidify

noncomputable def cancelIso {X Y : Scheme.{0}} (p : X ⟶ Y) [IsIso p] {M M' : Y.Modules}
    (e : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback p).obj M') : M ≅ M' :=
  let idIso : ∀ N : Y.Modules, (Scheme.Modules.pullback (inv p)).obj ((Scheme.Modules.pullback p).obj N) ≅ N := fun N =>
    (Scheme.Modules.pullbackComp (inv p) p).app N ≪≫ (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id p)).app N ≪≫
      (Scheme.Modules.pullbackId Y).app N
  (idIso M).symm ≪≫ (Scheme.Modules.pullback (inv p)).mapIso e ≪≫ idIso M'

theorem triv_of_isInvertible_field {k : Type} [Field k] (N : (Spec (CommRingCat.of k)).Modules)
    (hN : Scheme.Modules.IsInvertible N) : Nonempty (N ≅ 𝟙_ (Spec (CommRingCat.of k)).Modules) := by
  obtain ⟨U, hU, ⟨e⟩⟩ := hN.1 default
  have hall : ∀ p : ↥(Spec (CommRingCat.of k)), p ∈ U := fun p => by rw [Subsingleton.elim p default]; exact hU
  let s : Spec (CommRingCat.of k) ⟶ (U : Scheme.{0}) :=
    IsOpenImmersion.lift U.ι (𝟙 _) (by rintro p ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; exact hall _)
  have hs : s ≫ U.ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  exact ⟨((Scheme.Modules.pullbackId _).app N).symm ≪≫ ((Scheme.Modules.pullbackCongr hs).app N).symm ≪≫
    ((Scheme.Modules.pullbackComp s U.ι).app N).symm ≪≫ (Scheme.Modules.pullback s).mapIso e ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso s⟩

noncomputable def unit_of_tensor_unit {X : Scheme.{0}} {N M : X.Modules} (d : N ⊗ M ≅ 𝟙_ _) (e : N ≅ 𝟙_ _) : M ≅ 𝟙_ _ :=
  (λ_ M).symm ≪≫ (e.symm ⊗ᵢ Iso.refl M) ≪≫ d

variable {k : Type} [Field k] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)

theorem one_comp_schemeNsmul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    (L.one t).1 ≫ L.schemeNsmul n = (L.one t).1 := by
  have h := congrArg Subtype.val (L.nsmul_natural f t (L.one t).1 (L.one t).2 n RelativeGroupLaw.idPoint)
  have h1 : schemeHomOverComp (L.one t).1 (L.one t).2 (RelativeGroupLaw.idPoint (f := f)) = L.one t :=
    Subtype.ext (Category.comp_id _)
  rw [h1, L.nsmul_unit] at h
  exact h

end BiRigidify

open BiRigidify in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (ℓ : ℕ)
    (𝓟 : (pullback f f).Modules) (h𝓟 : Scheme.Modules.IsInvertible 𝓟)
    (h : Nonempty ((Scheme.Modules.pullback (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ L.schemeNsmul ℓ)
          (by rw [Category.assoc, RelativeGroupLaw.schemeNsmul_over]; exact pullback.condition))).obj 𝓟 ≅
        mumfordBundle f L 𝓛)) :
    ∃ 𝓟' : (pullback f f).Modules, Scheme.Modules.IsInvertible 𝓟' ∧
      Nonempty ((Scheme.Modules.pullback (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ L.schemeNsmul ℓ)
          (by rw [Category.assoc, RelativeGroupLaw.schemeNsmul_over]; exact pullback.condition))).obj 𝓟' ≅
        mumfordBundle f L 𝓛) ∧
      Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj 𝓟' ≅ 𝟙_ _) ∧
      Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓟') ≅ 𝟙_ _) := by
  classical
  obtain ⟨eπ⟩ := h
  obtain ⟨⟨r1⟩, ⟨r2⟩⟩ := AlgebraicGeometry.Polarisation.nonempty_sliceAt_zero_mumfordBundle_iso_unit_and_swap k f L hc 𝓛 h𝓛

  let Λ := mumfordBundle f L 𝓛
  let z₀ := RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)
  let t := Spec.map (CommRingCat.ofHom (algebraMap k k))
  let z : Spec (CommRingCat.of k) ⟶ A := z₀.1
  have hzf : z ≫ f = t := z₀.2
  have ht : t = 𝟙 _ := specMap_algebraMap_self
  have htc : ∀ {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of k)), g ≫ t = g := fun g => by rw [ht, Category.comp_id]
  haveI : IsIso t := by rw [ht]; infer_instance
  let π : pullback f f ⟶ pullback f f := pullback.lift (pullback.fst f f) (pullback.snd f f ≫ L.schemeNsmul ℓ)
    (by rw [Category.assoc, RelativeGroupLaw.schemeNsmul_over]; exact pullback.condition)
  let σ₀ : pullback f t ⟶ pullback f f := sliceAt f z₀
  let F := pullback.fst f t
  let S := pullback.snd f t
  let flip := (pullbackSymmetry f f).hom
  let p₂ := pullback.snd f f
  let εA : A ⟶ pullback f f := pullback.lift (f ≫ z) (𝟙 A) (by rw [Category.assoc, hzf, htc, Category.id_comp])

  have hz : z ≫ L.schemeNsmul ℓ = z := by
    change (L.one t).1 ≫ L.schemeNsmul ℓ = (L.one t).1
    exact one_comp_schemeNsmul L t ℓ
  have hε : σ₀ ≫ flip = F ≫ εA := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, Category.assoc, pullback.lift_fst]
      change pullback.lift (pullback.fst f t) (pullback.snd f t ≫ z) _ ≫ pullback.snd f f = F ≫ f ≫ z
      rw [pullback.lift_snd, ← Category.assoc, pullback.condition, htc]
    · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
      exact pullback.lift_fst _ _ _
  have hεπ : εA ≫ π = L.schemeNsmul ℓ ≫ εA := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc,
        RelativeGroupLaw.schemeNsmul_over]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd,
        Category.id_comp, Category.comp_id]
  have hσπ : σ₀ ≫ π = σ₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc]
      change (pullback.lift (pullback.fst f t) (pullback.snd f t ≫ z) _ ≫ pullback.snd f f) ≫ L.schemeNsmul ℓ =
        pullback.lift (pullback.fst f t) (pullback.snd f t ≫ z) _ ≫ pullback.snd f f
      rw [pullback.lift_snd, Category.assoc, hz]
  have hεp₂ : εA ≫ p₂ = 𝟙 A := pullback.lift_snd _ _ _
  have hσp₂ : σ₀ ≫ p₂ = S ≫ z := pullback.lift_snd _ _ _
  have hπp₂ : π ≫ p₂ = p₂ ≫ L.schemeNsmul ℓ := pullback.lift_snd _ _ _

  let N : A.Modules := (Scheme.Modules.pullback εA).obj 𝓟
  have hN : Scheme.Modules.IsInvertible N := h𝓟.pullback _
  let Nv := Scheme.Modules.dual N
  have hNv : Scheme.Modules.IsInvertible Nv := (AlgebraicGeometry.Scheme.Modules.IsInvertible.dual_monoidalV2 hN).1
  obtain ⟨dN⟩ := (AlgebraicGeometry.Scheme.Modules.IsInvertible.dual_monoidalV2 hN).2
  let 𝓟' : (pullback f f).Modules := 𝓟 ⊗ (Scheme.Modules.pullback p₂).obj Nv
  have h𝓟' : Scheme.Modules.IsInvertible 𝓟' := h𝓟.tensor_monoidalV2 (hNv.pullback _)

  have eΛ : (Scheme.Modules.pullback εA).obj Λ ≅ 𝟙_ _ := by
    refine cancelIso F ?_
    exact (Scheme.Modules.pullbackComp F εA).app Λ ≪≫ (Scheme.Modules.pullbackCongr hε.symm).app Λ ≪≫
      ((Scheme.Modules.pullbackComp σ₀ flip).app Λ).symm ≪≫ r2 ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso F).symm

  have eN : (Scheme.Modules.pullback (L.schemeNsmul ℓ)).obj N ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackComp (L.schemeNsmul ℓ) εA).app 𝓟 ≪≫ (Scheme.Modules.pullbackCongr hεπ.symm).app 𝓟 ≪≫
      ((Scheme.Modules.pullbackComp εA π).app 𝓟).symm ≪≫ (Scheme.Modules.pullback εA).mapIso eπ ≪≫ eΛ
  have eNv : (Scheme.Modules.pullback (L.schemeNsmul ℓ)).obj Nv ≅ 𝟙_ _ :=
    unit_of_tensor_unit
      ((Scheme.Modules.pullbackTensorObjIso (L.schemeNsmul ℓ) N Nv).symm ≪≫ (Scheme.Modules.pullback _).mapIso dN ≪≫
        Scheme.Modules.pullbackTensorUnitObjIso _) eN

  obtain ⟨ez⟩ := triv_of_isInvertible_field ((Scheme.Modules.pullback z).obj Nv) (hNv.pullback z)
  refine ⟨𝓟', h𝓟', ⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  ·
    exact Scheme.Modules.pullbackTensorObjIso π _ _ ≪≫
      (eπ ⊗ᵢ ((Scheme.Modules.pullbackComp π p₂).app Nv ≪≫ (Scheme.Modules.pullbackCongr hπp₂).app Nv ≪≫
        ((Scheme.Modules.pullbackComp p₂ (L.schemeNsmul ℓ)).app Nv).symm ≪≫ (Scheme.Modules.pullback p₂).mapIso eNv ≪≫
        Scheme.Modules.pullbackTensorUnitObjIso p₂)) ≪≫ ρ_ _
  ·
    exact Scheme.Modules.pullbackTensorObjIso σ₀ _ _ ≪≫
      ((((Scheme.Modules.pullbackCongr hσπ).app 𝓟).symm ≪≫ ((Scheme.Modules.pullbackComp σ₀ π).app 𝓟).symm ≪≫
          (Scheme.Modules.pullback σ₀).mapIso eπ ≪≫ r1) ⊗ᵢ
        ((Scheme.Modules.pullbackComp σ₀ p₂).app Nv ≪≫ (Scheme.Modules.pullbackCongr hσp₂).app Nv ≪≫
          ((Scheme.Modules.pullbackComp S z).app Nv).symm ≪≫ (Scheme.Modules.pullback S).mapIso ez ≪≫
          Scheme.Modules.pullbackTensorUnitObjIso S)) ≪≫ λ_ _
  ·
    refine (Scheme.Modules.pullbackComp σ₀ flip).app 𝓟' ≪≫ (Scheme.Modules.pullbackCongr hε).app 𝓟' ≪≫
      ((Scheme.Modules.pullbackComp F εA).app 𝓟').symm ≪≫ (Scheme.Modules.pullback F).mapIso ?_ ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso F
    exact Scheme.Modules.pullbackTensorObjIso εA _ _ ≪≫
      (Iso.refl N ⊗ᵢ ((Scheme.Modules.pullbackComp εA p₂).app Nv ≪≫ (Scheme.Modules.pullbackCongr hεp₂).app Nv ≪≫
        (Scheme.Modules.pullbackId A).app Nv)) ≪≫ dN

end S_AlgebraicGeometry_RiemannForm_exists_birigidified_pullback_oneProdNsmul_iso_mumfordBundle_of_pullback_oneProdNsmul_iso_mumfordBundle
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_exists_birigidified_pullback_oneProdNsmul_iso_mumfordBundle_of_pullback_oneProdNsmul_iso_mumfordBundle (solution)
