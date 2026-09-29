-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.geomFibreH0Finrank_pos_of_pos_pullback_of_kernelIsTwoTorsion_of_isLocalHom_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3caeddba-97a5-522b-bad0-ea2aa16b1c87

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isClosed_setOf_le_finrank_sections_pullback_residueField
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_geomFibreH0Finrank_pos_of_pos_pullback_of_kernelIsTwoTorsion_of_isLocalHom_of_injective
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    {T R : Type} [CommRing T] [CommRing R] [IsLocalRing T] [IsNoetherianRing T] [IsLocalRing R]
    (φ : T →+* R) (hφ : Function.Injective φ) (hφl : IsLocalHom φ)
    {AT : Scheme.{0}} {fT : AT ⟶ Spec (CommRingCat.of T)} (LT : RelativeGroupLaw T fT)
    (hA : AbelianSchemePropertyBundle T fT)
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (g : A ⟶ AT)
    (hg : CategoryTheory.IsPullback g f fT (Spec.map (CommRingCat.ofHom φ)))
    (𝓜T : AT.Modules) (hT : Scheme.Modules.IsInvertible 𝓜T) (hK : KernelIsTwoTorsion fT LT 𝓜T)
    (hpos : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : R →+* k),
      0 < Scheme.Modules.geomFibreH0Finrank f ((Scheme.Modules.pullback g).obj 𝓜T) k sk) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : T →+* k), 0 < Scheme.Modules.geomFibreH0Finrank fT 𝓜T k sk := by
  intro k _ _ sk
  haveI : IsProper fT := hA.proper
  haveI : Smooth fT := hA.smooth

  have hpos' : ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (sK : R →+* K'),
      0 < Scheme.Modules.geomFibreH0Finrank fT 𝓜T K' (sK.comp φ) := by
    intro K' _ _ sK
    rw [← Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback φ fT f g hg 𝓜T _ (Iso.refl _) K' sK]
    exact hpos K' sK

  let Z : Set (PrimeSpectrum T) := {𝔭 : PrimeSpectrum T |
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd fT (Scheme.TwoAffineOpenCover.specMap T 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback
          (Limits.pullback.fst fT (Scheme.TwoAffineOpenCover.specMap T 𝔭.asIdeal.ResidueField))).obj 𝓜T) ⊤
      1 ≤ Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback
          (Limits.pullback.fst fT (Scheme.TwoAffineOpenCover.specMap T 𝔭.asIdeal.ResidueField))).obj 𝓜T, ⊤)}
  have hZ : IsClosed Z :=
    Scheme.Modules.isClosed_setOf_le_finrank_sections_pullback_residueField fT 𝓜T hT.exists_trivialization 1
  have hZiff : ∀ 𝔭 : PrimeSpectrum T, 𝔭 ∈ Z ↔
      1 ≤ Scheme.Modules.geomFibreH0Finrank fT 𝓜T 𝔭.asIdeal.ResidueField (algebraMap T 𝔭.asIdeal.ResidueField) :=
    fun 𝔭 => Iff.rfl

  have hpt : ∀ (𝔮 : PrimeSpectrum T) (K' : Type) [Field K'] (s : T →+* K'), RingHom.ker s = 𝔮.asIdeal →
      Scheme.Modules.geomFibreH0Finrank fT 𝓜T K' s =
        Scheme.Modules.geomFibreH0Finrank fT 𝓜T 𝔮.asIdeal.ResidueField (algebraMap T 𝔮.asIdeal.ResidueField) := by
    intro 𝔮 K' _ s hs
    have hf₁ : 𝔮.asIdeal ≤ RingHom.ker s := le_of_eq hs.symm
    have hf₂ : 𝔮.asIdeal.primeCompl ≤ (IsUnit.submonoid K').comap s := fun x hx => by
      show IsUnit (s x)
      apply IsUnit.mk0 _
      intro h0
      apply hx
      rw [← RingHom.mem_ker, hs] at h0
      exact h0
    let j : 𝔮.asIdeal.ResidueField →+* K' := Ideal.ResidueField.lift 𝔮.asIdeal s hf₁ hf₂
    have hj : j.comp (algebraMap T 𝔮.asIdeal.ResidueField) = s := by
      ext r
      exact Ideal.ResidueField.lift_algebraMap 𝔮.asIdeal s hf₁ hf₂ r
    rw [← hj, Scheme.Modules.geomFibreH0Finrank_comp_eq fT 𝓜T hT 𝔮.asIdeal.ResidueField K'
      (algebraMap T 𝔮.asIdeal.ResidueField) j]

  have himg : Set.range (PrimeSpectrum.comap φ) ⊆ Z := by
    rintro _ ⟨𝔓, rfl⟩
    rw [hZiff]
    let κ := 𝔓.asIdeal.ResidueField
    let Kb := AlgebraicClosure κ
    let sK : R →+* Kb := (algebraMap κ Kb).comp (algebraMap R κ)
    have hker : RingHom.ker (sK.comp φ) = (PrimeSpectrum.comap φ 𝔓).asIdeal := by
      ext x
      rw [RingHom.mem_ker, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.comp_apply,
        show sK (φ x) = algebraMap κ Kb (algebraMap R κ (φ x)) from rfl,
        map_eq_zero_iff _ (algebraMap κ Kb).injective, ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]
    have h1 := hpos' Kb sK
    rwa [hpt (PrimeSpectrum.comap φ 𝔓) Kb (sK.comp φ) hker] at h1

  have hdense : DenseRange (PrimeSpectrum.comap φ) := by
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot φ).mp hφ]
    exact bot_le
  have hZuniv : Z = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hdense.closure_range]
    exact hZ.closure_subset_iff.mpr himg

  haveI hqprime : (RingHom.ker sk).IsPrime := RingHom.ker_isPrime sk
  let 𝔮 : PrimeSpectrum T := ⟨RingHom.ker sk, hqprime⟩
  have h𝔮 : 𝔮 ∈ Z := by rw [hZuniv]; exact Set.mem_univ _
  rw [hZiff] at h𝔮
  rw [hpt 𝔮 k sk rfl]
  exact h𝔮

end S_AlgebraicGeometry_Polarisation_geomFibreH0Finrank_pos_of_pos_pullback_of_kernelIsTwoTorsion_of_isLocalHom_of_injective
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_geomFibreH0Finrank_pos_of_pos_pullback_of_kernelIsTwoTorsion_of_isLocalHom_of_injective (solution)
