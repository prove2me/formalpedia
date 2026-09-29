-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.projective_H0_and_bijective_kerBaseChangeHom_of_isReduced_of_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/576d2d24-b147-536d-beef-3799dbae129e

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_projective_H0_and_bijective_kerBaseChangeHom_of_isReduced_of_finrank_eq
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace TensorProduct

namespace P2mReducedBaseChangeH0

section FibreDim

variable {R : Type u} [CommRing R]

noncomputable abbrev fibreDim (Q : Type u) [AddCommGroup Q] [Module R Q]
    (𝔭 : PrimeSpectrum R) : ℕ :=
  Module.finrank 𝔭.asIdeal.ResidueField (𝔭.asIdeal.ResidueField ⊗[R] Q)

variable {Q : Type u} [AddCommGroup Q] [Module R Q]

noncomputable def baseChangeCokerEquiv {P : Type u} [AddCommGroup P] [Module R P]
    (φ : P →ₗ[R] Q) (A : Type u) [CommRing A] [Algebra R A] :
    ((A ⊗[R] Q) ⧸ LinearMap.range (φ.baseChange A)) ≃ₗ[A]
      A ⊗[R] (Q ⧸ LinearMap.range φ) := by
  have hex : Function.Exact φ (LinearMap.range φ).mkQ := LinearMap.exact_map_mkQ_range φ
  have hsurj : Function.Surjective (LinearMap.range φ).mkQ := Submodule.mkQ_surjective _
  have hexA : Function.Exact (φ.baseChange A) ((LinearMap.range φ).mkQ.baseChange A) := by
    have h := lTensor_exact A hex hsurj
    rwa [← LinearMap.baseChange_eq_ltensor, ← LinearMap.baseChange_eq_ltensor] at h
  exact hexA.linearEquivOfSurjective (LinearMap.baseChange_surjective A hsurj)

theorem exists_family_card_eq (𝔭 : PrimeSpectrum R) [Module.Finite R Q] :
    ∃ (ι : Type u) (_ : Fintype ι) (q : ι → Q),
      Fintype.card ι = fibreDim Q 𝔭 ∧
        Subsingleton (𝔭.asIdeal.ResidueField ⊗[R]
          (Q ⧸ LinearMap.range (Fintype.linearCombination R q))) := by
  set K := 𝔭.asIdeal.ResidueField

  have hspan : Submodule.span K (Set.range (TensorProduct.mk R K Q 1)) = ⊤ := by
    have h := (Submodule.baseChange_eq_span (p := (⊤ : Submodule R Q)) (A := K)).symm.trans
      (Submodule.baseChange_top (R := R) (M := Q) (A := K))
    rwa [Submodule.map_coe, Submodule.top_coe, Set.image_univ] at h
  obtain ⟨ι, a, -, hspan', hli⟩ := exists_linearIndependent' (K := K) (TensorProduct.mk R K Q 1)
  rw [hspan] at hspan'
  let b : Module.Basis ι K (K ⊗[R] Q) := Module.Basis.mk hli hspan'.ge
  haveI : IsNoetherian K (K ⊗[R] Q) := IsNoetherian.iff_fg.2 inferInstance
  letI : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  refine ⟨ι, inferInstance, a, (Module.finrank_eq_card_basis b).symm, ?_⟩
  classical
  set φ : (ι → R) →ₗ[R] Q := Fintype.linearCombination R a
  have hrange : LinearMap.range (φ.baseChange K) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨1 ⊗ₜ[R] Pi.single i 1, ?_⟩
    rw [LinearMap.baseChange_tmul, Module.Basis.coe_mk]
    change (1 : K) ⊗ₜ[R] φ (Pi.single i 1) = (1 : K) ⊗ₜ[R] a i
    rw [Fintype.linearCombination_apply_single, one_smul]
  haveI : Subsingleton ((K ⊗[R] Q) ⧸ LinearMap.range (φ.baseChange K)) :=
    Submodule.Quotient.subsingleton_iff.mpr hrange
  exact (baseChangeCokerEquiv φ K).symm.toEquiv.subsingleton

end FibreDim

section TwoTerm

variable {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, u} R)

theorem fibreH0_add_finrank (𝔭 : PrimeSpectrum R) :
    G.fibreH0 𝔭 + Module.finrank R G.C1 =
      Module.finrank R G.C0 + fibreDim (G.C1 ⧸ LinearMap.range G.d) 𝔭 := by
  haveI : Nontrivial R := ⟨⟨0, 1, fun h => 𝔭.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).mpr (h ▸ 𝔭.asIdeal.zero_mem))⟩⟩
  set K := 𝔭.asIdeal.ResidueField
  set dK := G.d.baseChange K
  have h1 : Module.finrank K (LinearMap.range dK) + Module.finrank K (LinearMap.ker dK) =
      Module.finrank K (K ⊗[R] G.C0) := LinearMap.finrank_range_add_finrank_ker dK
  have h2 : Module.finrank K (K ⊗[R] G.C0) = Module.finrank R G.C0 := Module.finrank_baseChange
  have h3 : Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range dK) +
      Module.finrank K (LinearMap.range dK) = Module.finrank K (K ⊗[R] G.C1) :=
    Submodule.finrank_quotient_add_finrank _
  have h4 : Module.finrank K (K ⊗[R] G.C1) = Module.finrank R G.C1 := Module.finrank_baseChange
  have h5 : Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range dK) =
      fibreDim (G.C1 ⧸ LinearMap.range G.d) 𝔭 := (baseChangeCokerEquiv G.d K).finrank_eq
  have h0 : G.fibreH0 𝔭 = Module.finrank K (LinearMap.ker dK) := rfl
  omega

end TwoTerm

section Reduced

variable {R : Type u} [CommRing R]
variable {Q : Type u} [AddCommGroup Q] [Module R Q]

theorem span_range_mk_one (K : Type u) [CommRing K] [Algebra R K] :
    Submodule.span K (Set.range (TensorProduct.mk R K Q 1)) = ⊤ := by
  have h := (Submodule.baseChange_eq_span (p := (⊤ : Submodule R Q)) (A := K)).symm.trans
    (Submodule.baseChange_top (R := R) (M := Q) (A := K))
  rwa [Submodule.map_coe, Submodule.top_coe, Set.image_univ] at h

theorem exists_local_presentation [IsReduced R] [Module.Finite R Q] (μ : ℕ)
    (hconst : ∀ 𝔮 : PrimeSpectrum R, fibreDim Q 𝔮 = μ) (𝔭 : PrimeSpectrum R) :
    ∃ (ι : Type u) (_ : Fintype ι) (q : ι → Q) (g : R), g ∉ 𝔭.asIdeal ∧
      (∀ x : Q, g • x ∈ LinearMap.range (Fintype.linearCombination R q)) ∧
      (∀ b : ι → R, Fintype.linearCombination R q b = 0 → g • b = 0) := by
  classical
  obtain ⟨ι, _, q, hcard, hsub⟩ := exists_family_card_eq (Q := Q) 𝔭
  set φ : (ι → R) →ₗ[R] Q := Fintype.linearCombination R q
  let Q' := Q ⧸ LinearMap.range φ
  have h𝔭 : 𝔭 ∉ Module.support R Q' := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]
    exact hsub
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus, Set.not_subset] at h𝔭
  obtain ⟨g, hgann, hg𝔭⟩ := h𝔭
  have hgQ : ∀ x : Q, g • x ∈ LinearMap.range φ := fun x => by
    have h := (Module.mem_annihilator.mp hgann) (Submodule.Quotient.mk x : Q')
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  refine ⟨ι, inferInstance, q, g, hg𝔭, hgQ, fun b hb => ?_⟩

  funext i
  rw [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.mpr fun J hJ => ?_)
  by_cases hgJ : g ∈ J
  · exact J.mul_mem_right _ hgJ
  refine J.mul_mem_left _ ?_
  let 𝔮 : PrimeSpectrum R := ⟨J, hJ⟩
  set K := 𝔮.asIdeal.ResidueField

  have hgK : algebraMap R K g ≠ 0 := fun h => hgJ (Ideal.algebraMap_residueField_eq_zero.mp h)
  have hspanK : ⊤ ≤ Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[R] q i) := by
    rw [← span_range_mk_one K, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    obtain ⟨c, hc⟩ := hgQ x
    have hx : (1 : K) ⊗ₜ[R] x = (algebraMap R K g)⁻¹ • ((1 : K) ⊗ₜ[R] (g • x)) := by
      rw [tmul_smul, ← algebraMap_smul K g, smul_smul, inv_mul_cancel₀ hgK, one_smul]
    change (1 : K) ⊗ₜ[R] x ∈ _
    rw [hx, ← hc]
    refine Submodule.smul_mem _ _ ?_
    simp only [φ, Fintype.linearCombination_apply, tmul_sum, tmul_smul]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← algebraMap_smul K (c j)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hli : LinearIndependent K (fun i => (1 : K) ⊗ₜ[R] q i) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspanK
      (hcard.trans ((hconst 𝔭).trans (hconst 𝔮).symm))

  have hrel : ∑ i, algebraMap R K (b i) • ((1 : K) ⊗ₜ[R] q i) = 0 := by
    have h0 : (1 : K) ⊗ₜ[R] (φ b) = 0 := by rw [hb, tmul_zero]
    simp only [φ, Fintype.linearCombination_apply, tmul_sum, tmul_smul] at h0
    simpa only [algebraMap_smul] using h0
  have hbi : algebraMap R K (b i) = 0 :=
    Fintype.linearIndependent_iff.mp hli (fun i => algebraMap R K (b i)) hrel i
  exact Ideal.algebraMap_residueField_eq_zero.mp hbi

theorem projective_of_isReduced_of_fibreDim_eq [IsReduced R] [Module.FinitePresentation R Q] (μ : ℕ)
    (hconst : ∀ 𝔮 : PrimeSpectrum R, fibreDim Q 𝔮 = μ) : Module.Projective R Q := by
  rw [← Module.freeLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  intro 𝔭
  let Rp := Localization.AtPrime 𝔭.asIdeal
  rw [Module.mem_freeLocus_iff_tensor 𝔭 Rp]
  obtain ⟨ι, _, q, g, hg𝔭, hgQ, hgker⟩ := exists_local_presentation μ hconst 𝔭
  set φ : (ι → R) →ₗ[R] Q := Fintype.linearCombination R q
  have hunit : IsUnit (algebraMap R Rp g) := IsLocalization.map_units Rp (⟨g, hg𝔭⟩ : 𝔭.asIdeal.primeCompl)
  have halg : ∀ {N : Type u} [AddCommGroup N] [Module R N] (r : R) (x : N),
      (algebraMap R Rp r) ⊗ₜ[R] x = (1 : Rp) ⊗ₜ[R] (r • x) := fun r x => by
    rw [Algebra.algebraMap_eq_smul_one, smul_tmul]

  have hsurj : Function.Surjective (φ.baseChange Rp) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul s x =>
      obtain ⟨c, hc⟩ := hgQ x
      refine ⟨(s * ↑hunit.unit⁻¹) • ((1 : Rp) ⊗ₜ[R] c), ?_⟩
      rw [map_smul, LinearMap.baseChange_tmul, hc, ← halg, smul_tmul', smul_eq_mul, mul_assoc,
        IsUnit.val_inv_mul, mul_one]
    | add y z hy hz =>
      obtain ⟨a, rfl⟩ := hy; obtain ⟨b, rfl⟩ := hz
      exact ⟨a + b, map_add _ a b⟩

  have hinj : Function.Injective (φ.baseChange Rp) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalizedModule.surj 𝔭.asIdeal.primeCompl (TensorProduct.mk R Rp (ι → R) 1) y
    change s • y = (1 : Rp) ⊗ₜ[R] a at e
    have h1 : (TensorProduct.mk R Rp Q 1) (φ a) = 0 := by
      change (1 : Rp) ⊗ₜ[R] φ a = 0
      rw [← LinearMap.baseChange_tmul, ← e, Submonoid.smul_def, LinearMap.map_smul_of_tower, hy, smul_zero]
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff 𝔭.asIdeal.primeCompl (TensorProduct.mk R Rp Q 1)).mp h1
    rw [Submonoid.smul_def, ← map_smul] at ht
    have hgta : (g * (t : R)) • a = 0 := by rw [mul_smul]; exact hgker _ ht
    have hunit' : IsUnit (algebraMap R Rp (g * (t : R))) :=
      IsLocalization.map_units Rp (⟨g * t, 𝔭.asIdeal.primeCompl.mul_mem hg𝔭 t.2⟩ : 𝔭.asIdeal.primeCompl)
    have h2 : (1 : Rp) ⊗ₜ[R] a = 0 := by
      have h3 : algebraMap R Rp (g * (t : R)) • ((1 : Rp) ⊗ₜ[R] a) = 0 := by
        rw [smul_tmul', smul_eq_mul, mul_one, halg, hgta, tmul_zero]
      exact (hunit'.smul_left_cancel).mp (h3.trans (smul_zero _).symm)
    have h4 : s • y = 0 := e.trans h2
    exact IsLocalizedModule.smul_injective (TensorProduct.mk R Rp (ι → R) 1) s
      (h4.trans (smul_zero _).symm)
  exact Module.Free.of_equiv (LinearEquiv.ofBijective (φ.baseChange Rp) ⟨hinj, hsurj⟩)

end Reduced

section TwoTermReduced

variable {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, u} R)

theorem exists_retractions (hQ : Module.Projective R (G.C1 ⧸ LinearMap.range G.d)) :
    (∃ t : G.C0 →ₗ[R] LinearMap.ker G.d, t ∘ₗ (LinearMap.ker G.d).subtype = LinearMap.id) ∧
      (∃ s : G.C1 →ₗ[R] LinearMap.range G.d, s ∘ₗ (LinearMap.range G.d).subtype = LinearMap.id) := by
  set π := (LinearMap.range G.d).mkQ
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id (Submodule.mkQ_surjective _)

  have hs : ∃ s : G.C1 →ₗ[R] LinearMap.range G.d, s ∘ₗ (LinearMap.range G.d).subtype = LinearMap.id := by
    refine ⟨LinearMap.codRestrict (LinearMap.range G.d) (LinearMap.id - σ ∘ₗ π) fun x => ?_, ?_⟩
    · refine (Submodule.Quotient.mk_eq_zero _).mp ?_
      change π (x - σ (π x)) = 0
      rw [map_sub, ← LinearMap.comp_apply, hσ, LinearMap.id_apply, sub_self]
    · ext ⟨x, hx⟩
      have hπ : π x = 0 := by rwa [← LinearMap.mem_ker, Submodule.ker_mkQ]
      simp [hπ]
  obtain ⟨s, hs'⟩ := hs
  haveI : Module.Projective R (LinearMap.range G.d) := Module.Projective.of_split _ s hs'
  set d' := G.d.rangeRestrict
  obtain ⟨σ₂, hσ₂⟩ := Module.projective_lifting_property d' LinearMap.id (LinearMap.surjective_rangeRestrict _)
  refine ⟨⟨LinearMap.codRestrict (LinearMap.ker G.d) (LinearMap.id - σ₂ ∘ₗ d') fun x => ?_, ?_⟩, ⟨s, hs'⟩⟩
  · rw [← LinearMap.ker_rangeRestrict G.d, LinearMap.mem_ker]
    change d' (x - σ₂ (d' x)) = 0
    rw [map_sub, ← LinearMap.comp_apply, hσ₂, LinearMap.id_apply, sub_self]
  · ext ⟨x, hx⟩
    have hd : d' x = 0 := by
      rw [← LinearMap.mem_ker, LinearMap.ker_rangeRestrict]; exact hx
    simp [hd]

theorem projective_ker_and_bijective_kerBaseChangeHom [IsReduced R] (r : ℕ)
    (hconst : ∀ 𝔭 : PrimeSpectrum R, G.fibreH0 𝔭 = r) :
    Module.Projective R (LinearMap.ker G.d) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerBaseChangeHom G.d A) := by

  have hfd : ∀ 𝔮 : PrimeSpectrum R,
      fibreDim (G.C1 ⧸ LinearMap.range G.d) 𝔮 = r + Module.finrank R G.C1 - Module.finrank R G.C0 := by
    intro 𝔮
    have h := fibreH0_add_finrank G 𝔮
    rw [hconst 𝔮] at h
    omega
  haveI : Module.FinitePresentation R G.C1 := Module.finitePresentation_of_projective _ _
  haveI : Module.FinitePresentation R (G.C1 ⧸ LinearMap.range G.d) := by
    refine Module.finitePresentation_of_surjective (LinearMap.range G.d).mkQ (Submodule.mkQ_surjective _) ?_
    rw [Submodule.ker_mkQ, ← Submodule.map_top]
    exact Module.Finite.fg_top.map _
  have hQ : Module.Projective R (G.C1 ⧸ LinearMap.range G.d) :=
    projective_of_isReduced_of_fibreDim_eq _ hfd
  obtain ⟨⟨t, ht⟩, ⟨s, hs⟩⟩ := exists_retractions G hQ
  refine ⟨Module.Projective.of_split _ t ht, fun A _ _ => ⟨?_, ?_⟩⟩
  ·
    intro x y hxy
    have h := congrArg (t.baseChange A) (congrArg Subtype.val hxy)
    change (t.baseChange A) ((LinearMap.ker G.d).subtype.baseChange A x)
      = (t.baseChange A) ((LinearMap.ker G.d).subtype.baseChange A y) at h
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ht,
      LinearMap.baseChange_id, LinearMap.id_apply, LinearMap.id_apply] at h
  ·
    rintro ⟨y, hy⟩
    set d' := G.d.rangeRestrict
    have hex : Function.Exact (LinearMap.ker G.d).subtype d' := by
      rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
    have hexA : Function.Exact ((LinearMap.ker G.d).subtype.baseChange A) (d'.baseChange A) := by
      have h := lTensor_exact A hex (LinearMap.surjective_rangeRestrict _)
      rwa [← LinearMap.baseChange_eq_ltensor, ← LinearMap.baseChange_eq_ltensor] at h
    have hd'y : d'.baseChange A y = 0 := by
      have hcomp : G.d = (LinearMap.range G.d).subtype ∘ₗ d' := (LinearMap.subtype_comp_codRestrict _ _ _).symm
      have hy' : ((LinearMap.range G.d).subtype.baseChange A) (d'.baseChange A y) = 0 := by
        rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← hcomp]; exact hy
      have h := congrArg (s.baseChange A) hy'
      rwa [map_zero, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hs, LinearMap.baseChange_id,
        LinearMap.id_apply] at h
    obtain ⟨x, hx⟩ := (hexA y).mp hd'y
    exact ⟨x, Subtype.ext hx⟩

end TwoTermReduced

section KerTransfer

variable {R : Type u} [CommRing R]
variable {K0 K1 C0 C1 : Type u} [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
  [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

theorem lid_baseChange_apply (f : C0 →ₗ[R] C1) (x : R ⊗[R] C0) :
    TensorProduct.lid R C1 (f.baseChange R x) = f (TensorProduct.lid R C0 x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r m => rw [LinearMap.baseChange_tmul, TensorProduct.lid_tmul, TensorProduct.lid_tmul, map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
  (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK)

theorem tmul_one_mem_ker {N P : Type u} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] P) (x : LinearMap.ker f) :
    (1 : R) ⊗ₜ[R] (x : N) ∈ LinearMap.ker (f.baseChange R) := by
  rw [LinearMap.mem_ker, LinearMap.baseChange_tmul, LinearMap.mem_ker.mp x.2, tmul_zero]

theorem kerMap_bijective (h : Function.Bijective (TwoChartCech.kerMapBaseChange dK d ι0 ι1 comm R)) :
    Function.Bijective (TwoChartCech.kerMap dK d ι0 ι1 comm) := by
  constructor
  · intro x y hxy
    have hv : ι0 x = ι0 y := congrArg Subtype.val hxy
    have h1 : TwoChartCech.kerMapBaseChange dK d ι0 ι1 comm R ⟨_, tmul_one_mem_ker dK x⟩
        = TwoChartCech.kerMapBaseChange dK d ι0 ι1 comm R ⟨_, tmul_one_mem_ker dK y⟩ := by
      apply Subtype.ext
      change ι0.baseChange R ((1 : R) ⊗ₜ[R] (x : K0)) = ι0.baseChange R ((1 : R) ⊗ₜ[R] (y : K0))
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, hv]
    have h2 := congrArg (fun z => TensorProduct.lid R K0 (Subtype.val z)) (h.1 h1)
    simp only [TensorProduct.lid_tmul, one_smul] at h2
    exact Subtype.ext h2
  · intro y
    obtain ⟨x, hx⟩ := h.2 ⟨_, tmul_one_mem_ker d y⟩
    have hxv : ι0.baseChange R (x : R ⊗[R] K0) = (1 : R) ⊗ₜ[R] (y : C0) := congrArg Subtype.val hx
    refine ⟨⟨TensorProduct.lid R K0 x, ?_⟩, Subtype.ext ?_⟩
    · rw [LinearMap.mem_ker, ← lid_baseChange_apply, LinearMap.mem_ker.mp x.2, map_zero]
    · change ι0 (TensorProduct.lid R K0 x) = y
      rw [← lid_baseChange_apply, hxv, TensorProduct.lid_tmul, one_smul]

theorem kerMapBaseChange_kerBaseChangeHom (A : Type u) [CommRing A] [Algebra R A]
    (x : A ⊗[R] LinearMap.ker dK) :
    TwoChartCech.kerMapBaseChange dK d ι0 ι1 comm A (TwoChartCech.kerBaseChangeHom dK A x)
      = TwoChartCech.kerBaseChangeHom d A ((TwoChartCech.kerMap dK d ι0 ι1 comm).baseChange A x) := by
  apply Subtype.ext
  change ι0.baseChange A (((LinearMap.ker dK).subtype.baseChange A) x)
    = ((LinearMap.ker d).subtype.baseChange A) ((TwoChartCech.kerMap dK d ι0 ι1 comm).baseChange A x)
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← LinearMap.comp_apply,
    ← LinearMap.baseChange_comp]
  rfl

theorem bijective_kerBaseChangeHom_of_transfer (A : Type u) [CommRing A] [Algebra R A]
    (hK : Function.Bijective (TwoChartCech.kerBaseChangeHom dK A))
    (hBC : Function.Bijective (TwoChartCech.kerMapBaseChange dK d ι0 ι1 comm A))
    (hMap : Function.Bijective (TwoChartCech.kerMap dK d ι0 ι1 comm)) :
    Function.Bijective (TwoChartCech.kerBaseChangeHom d A) := by
  set e := LinearEquiv.ofBijective (TwoChartCech.kerMap dK d ι0 ι1 comm) hMap
  set eA := e.baseChange R A _ _
  have heA : ∀ x, eA x = (TwoChartCech.kerMap dK d ι0 ι1 comm).baseChange A x := fun x => by
    change (e.toLinearMap.baseChange A) x = _
    congr 2
  have hfun : ⇑(TwoChartCech.kerBaseChangeHom d A)
      = (⇑(TwoChartCech.kerMapBaseChange dK d ι0 ι1 comm A) ∘ ⇑(TwoChartCech.kerBaseChangeHom dK A))
          ∘ ⇑eA.symm := by
    funext y
    obtain ⟨x, rfl⟩ := eA.surjective y
    rw [Function.comp_apply, Function.comp_apply, LinearEquiv.symm_apply_apply, heA,
      kerMapBaseChange_kerBaseChangeHom]
  rw [hfun]
  exact (hBC.comp hK).comp eA.symm.bijective

end KerTransfer

section H0

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)
  (K : V.OrderedAffineCover)

def toCochain :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    Γ(M, ⊤) →ₗ[R] (OModulePresheaf.ofModules π M).cochain K 0 :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
  LinearMap.pi fun s => (OModulePresheaf.ofModules π M).res (le_top : K.inter s ≤ ⊤)

theorem toCochain_apply' (x : Γ(M, ⊤)) (s : K.Idx 0) :
    toCochain π M K x s = (OModulePresheaf.ofModules π M).res (le_top : K.inter s ≤ ⊤)
      (show (OModulePresheaf.ofModules π M).obj ⊤ from x) := rfl

theorem d_toCochain (x : Γ(M, ⊤)) :
    (OModulePresheaf.ofModules π M).d K 0 (toCochain π M K x) = 0 := by
  funext s
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, toCochain_apply',
    OModulePresheaf.res_res]
  exact add_neg_cancel _

theorem toCochain_mem (x : Γ(M, ⊤)) : toCochain π M K x ∈ (OModulePresheaf.ofModules π M).H0 K :=
  d_toCochain π M K x

theorem toCochain_injective : Function.Injective (toCochain π M K) := by
  intro x y hxy
  obtain ⟨z, -, huniq⟩ := (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique π M K _).mp
    (d_toCochain π M K x)
  exact (huniq x fun s => rfl).trans (huniq y fun s => by rw [hxy]; rfl).symm

theorem exists_toCochain_eq (c : (OModulePresheaf.ofModules π M).cochain K 0)
    (hc : c ∈ (OModulePresheaf.ofModules π M).H0 K) : ∃ x : Γ(M, ⊤), toCochain π M K x = c := by
  obtain ⟨x, hx, -⟩ := (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique π M K c).mp hc
  exact ⟨x, funext fun s => (hx s).symm⟩

def H0Equiv :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    (OModulePresheaf.ofModules π M).H0 K ≃ₗ[R] Γ(M, ⊤) :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
  (LinearEquiv.ofBijective (LinearMap.codRestrict ((OModulePresheaf.ofModules π M).H0 K)
      (toCochain π M K) (toCochain_mem π M K))
    ⟨fun x y h => toCochain_injective π M K (congrArg Subtype.val h),
     fun ⟨c, hc⟩ => by
      obtain ⟨x, rfl⟩ := exists_toCochain_eq π M K c hc
      exact ⟨x, rfl⟩⟩).symm

end H0

section Main

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover"

theorem main
    {R : Type u} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (r : ℕ)
    (hconst : ∀ 𝔭 : PrimeSpectrum R,
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))).obj M) ⊤
      Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))).obj M, ⊤) = r)
    (𝒰 : X.OrderedAffineCover) :
    Module.Projective R ((OModulePresheaf.ofModules f M).H0 𝒰) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerBaseChangeHom ((OModulePresheaf.ofModules f M).d 𝒰 0) A) := by
  obtain ⟨G, ι0, ι1, comm, hbij⟩ :=
    OModulePresheaf.exists_twoTermComplex_kerMapBaseChange_bijective_ofModules f M htriv 𝒰

  have hconstG : ∀ 𝔭 : PrimeSpectrum R, G.fibreH0 𝔭 = r := by
    intro 𝔭
    let K := 𝔭.asIdeal.ResidueField
    let p₁ := Limits.pullback.fst f (specMap R K)
    let p₂ := Limits.pullback.snd f (specMap R K)
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p₂ ((Scheme.Modules.pullback p₁).obj M) ⊤
    obtain ⟨⟨⟨e1⟩, -⟩, -⟩ := OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial f 𝒰 M htriv K
    let e2 := H0Equiv p₂ ((Scheme.Modules.pullback p₁).obj M) (𝒰.baseChange f K)
    let e3 := LinearEquiv.ofBijective
      (TwoChartCech.kerMapBaseChange G.d ((OModulePresheaf.ofModules f M).d 𝒰 0) ι0 ι1 comm K) (hbij K)
    exact ((e2.symm.trans (e1.trans e3.symm)).finrank_eq).symm.trans (hconst 𝔭)
  obtain ⟨hproj, hbc⟩ := projective_ker_and_bijective_kerBaseChangeHom G r hconstG
  have hMap := kerMap_bijective G.d ((OModulePresheaf.ofModules f M).d 𝒰 0) ι0 ι1 comm (hbij R)
  refine ⟨?_, fun A _ _ => ?_⟩
  · haveI := hproj
    exact Module.Projective.of_equiv
      (LinearEquiv.ofBijective (TwoChartCech.kerMap G.d ((OModulePresheaf.ofModules f M).d 𝒰 0) ι0 ι1 comm) hMap)
  · exact bijective_kerBaseChangeHom_of_transfer G.d ((OModulePresheaf.ofModules f M).d 𝒰 0) ι0 ι1 comm A
      (hbc A) (hbij A) hMap

end Main

end P2mReducedBaseChangeH0

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (r : ℕ)
    (hconst : ∀ 𝔭 : PrimeSpectrum R,
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))).obj M) ⊤
      Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))).obj M, ⊤) = r)
    (𝒰 : X.OrderedAffineCover) :
    Module.Projective R ((OModulePresheaf.ofModules f M).H0 𝒰) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerBaseChangeHom ((OModulePresheaf.ofModules f M).d 𝒰 0) A) :=
  P2mReducedBaseChangeH0.main f M htriv r hconst 𝒰

end S_AlgebraicGeometry_OModulePresheaf_projective_H0_and_bijective_kerBaseChangeHom_of_isReduced_of_finrank_eq
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_projective_H0_and_bijective_kerBaseChangeHom_of_isReduced_of_finrank_eq (solution)
