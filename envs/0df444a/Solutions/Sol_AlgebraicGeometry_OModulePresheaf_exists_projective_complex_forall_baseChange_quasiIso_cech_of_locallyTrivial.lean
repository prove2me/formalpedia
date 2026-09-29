-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_projective_complex_forall_baseChange_quasiIso_cech_of_locallyTrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/8e2c9260-b124-506c-9972-189a3ff3fd40

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial
import Theorems.Thm_Module_exists_projective_complex_quasiIso_of_flat_complex
import Theorems.Thm_Module_quasiIso_baseChange_of_quasiIso_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_projective_complex_forall_baseChange_quasiIso_cech_of_locallyTrivial
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

noncomputable section

namespace S32F2

section Transport

variable {A : Type u} [CommRing A]
  {K : ℕ → Type u} [∀ i, AddCommGroup (K i)] [∀ i, Module A (K i)]
  {P : ℕ → Type u} [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
  {Q : ℕ → Type u} [∀ i, AddCommGroup (Q i)] [∀ i, Module A (Q i)]
  (δ : ∀ i, K i →ₗ[A] K (i + 1)) (dP : ∀ i, P i →ₗ[A] P (i + 1)) (dQ : ∀ i, Q i →ₗ[A] Q (i + 1))
  (ψ : ∀ i, K i →ₗ[A] P i) (E : ∀ i, P i ≃ₗ[A] Q i)

lemma E_dP (hE : ∀ i, (E (i + 1)).toLinearMap ∘ₗ dP i = dQ i ∘ₗ (E i).toLinearMap) (i : ℕ) (x : P i) :
    E (i + 1) (dP i x) = dQ i (E i x) := by
  have h := congrArg (fun f : P i →ₗ[A] Q (i + 1) => f x) (hE i)
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] using h

lemma Esymm_dQ (hE : ∀ i, (E (i + 1)).toLinearMap ∘ₗ dP i = dQ i ∘ₗ (E i).toLinearMap) (i : ℕ) (y : Q i) :
    (E (i + 1)).symm (dQ i y) = dP i ((E i).symm y) := by
  apply (E (i + 1)).injective
  rw [LinearEquiv.apply_symm_apply, E_dP dP dQ E hE, LinearEquiv.apply_symm_apply]

lemma transport_comm (hE : ∀ i, (E (i + 1)).toLinearMap ∘ₗ dP i = dQ i ∘ₗ (E i).toLinearMap)
    (hψ : ∀ i, dP i ∘ₗ ψ i = ψ (i + 1) ∘ₗ δ i) (i : ℕ) :
    ((E (i + 1)).toLinearMap ∘ₗ ψ (i + 1)) ∘ₗ δ i = dQ i ∘ₗ ((E i).toLinearMap ∘ₗ ψ i) := by
  rw [LinearMap.comp_assoc, ← hψ i, ← LinearMap.comp_assoc, hE i, LinearMap.comp_assoc]

lemma transport_h0inj
    (h0inj : ∀ x : K 0, δ 0 x = 0 → ψ 0 x = 0 → x = 0) (x : K 0) (hx : δ 0 x = 0)
    (hx' : ((E 0).toLinearMap ∘ₗ ψ 0) x = 0) : x = 0 := by
  apply h0inj x hx
  have : E 0 (ψ 0 x) = 0 := hx'
  exact (E 0).map_eq_zero_iff.1 this

lemma transport_h0surj (hE : ∀ i, (E (i + 1)).toLinearMap ∘ₗ dP i = dQ i ∘ₗ (E i).toLinearMap)
    (h0surj : ∀ y : P 0, dP 0 y = 0 → ∃ x : K 0, δ 0 x = 0 ∧ ψ 0 x = y) (y : Q 0) (hy : dQ 0 y = 0) :
    ∃ x : K 0, δ 0 x = 0 ∧ ((E 0).toLinearMap ∘ₗ ψ 0) x = y := by
  have hy' : dP 0 ((E 0).symm y) = 0 := by
    rw [← Esymm_dQ dP dQ E hE, hy, map_zero]
  obtain ⟨x, hx, hxy⟩ := h0surj _ hy'
  refine ⟨x, hx, ?_⟩
  show E 0 (ψ 0 x) = y
  rw [hxy, LinearEquiv.apply_symm_apply]

lemma transport_hinj (hE : ∀ i, (E (i + 1)).toLinearMap ∘ₗ dP i = dQ i ∘ₗ (E i).toLinearMap) (i : ℕ)
    (hinj : ∀ x : K (i + 1), δ (i + 1) x = 0 → ψ (i + 1) x ∈ LinearMap.range (dP i) → x ∈ LinearMap.range (δ i))
    (x : K (i + 1)) (hx : δ (i + 1) x = 0)
    (hx' : ((E (i + 1)).toLinearMap ∘ₗ ψ (i + 1)) x ∈ LinearMap.range (dQ i)) : x ∈ LinearMap.range (δ i) := by
  apply hinj x hx
  obtain ⟨z, hz⟩ := hx'
  refine ⟨(E i).symm z, ?_⟩
  apply (E (i + 1)).injective
  rw [E_dP dP dQ E hE, LinearEquiv.apply_symm_apply, hz]
  rfl

lemma transport_hsurj (hE : ∀ i, (E (i + 1)).toLinearMap ∘ₗ dP i = dQ i ∘ₗ (E i).toLinearMap) (i : ℕ)
    (hsurj : ∀ y : P (i + 1), dP (i + 1) y = 0 →
      ∃ x : K (i + 1), δ (i + 1) x = 0 ∧ ψ (i + 1) x - y ∈ LinearMap.range (dP i))
    (y : Q (i + 1)) (hy : dQ (i + 1) y = 0) :
    ∃ x : K (i + 1), δ (i + 1) x = 0 ∧ ((E (i + 1)).toLinearMap ∘ₗ ψ (i + 1)) x - y ∈ LinearMap.range (dQ i) := by
  have hy' : dP (i + 1) ((E (i + 1)).symm y) = 0 := by
    rw [← Esymm_dQ dP dQ E hE, hy, map_zero]
  obtain ⟨x, hx, ⟨w, hw⟩⟩ := hsurj _ hy'
  refine ⟨x, hx, ⟨E i w, ?_⟩⟩
  rw [← E_dP dP dQ E hE, hw, map_sub, LinearEquiv.apply_symm_apply]
  rfl

end Transport

theorem isEmpty_idx {V : Scheme.{u}} (K : V.OrderedAffineCover) {i : ℕ} (hi : Fintype.card K.ι < i + 1) :
    IsEmpty (K.Idx i) := by
  refine ⟨fun s => ?_⟩
  have := Fintype.card_le_of_injective s.1 s.2.injective
  simp only [Fintype.card_fin] at this
  omega

theorem subsingleton_cochain {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) {i : ℕ} (hi : Fintype.card K.ι < i + 1) :
    Subsingleton (F.cochain K i) := by
  haveI := isEmpty_idx K hi
  infer_instance

end S32F2

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    [IsProper π] [Flat π] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (𝒰 : X.OrderedAffineCover) (n : ℕ) (hn : Fintype.card 𝒰.ι ≤ n + 1) :
    ∃ (K : ℕ → Type u) (_ : ∀ i, AddCommGroup (K i)) (_ : ∀ i, Module R (K i))
      (_ : ∀ i, Module.Finite R (K i)) (_ : ∀ i, Module.Projective R (K i))
      (δ : ∀ i, K i →ₗ[R] K (i + 1)) (_ : ∀ i, δ (i + 1) ∘ₗ δ i = 0) (_ : ∀ i, n < i → Subsingleton (K i))
      (φ : ∀ i, K i →ₗ[R] (OModulePresheaf.ofModules π M).cochain 𝒰 i)
      (_ : ∀ i, (OModulePresheaf.ofModules π M).d 𝒰 i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i)
      (Θ : ∀ (A : Type u) [CommRing A] [Algebra R A] (i : ℕ), A ⊗[R] K i →ₗ[A]
        (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).cochain (𝒰.baseChange π A) i),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        (∀ i : ℕ, Θ A (i + 1) ∘ₗ (δ i).baseChange A
          = (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d (𝒰.baseChange π A) i
            ∘ₗ Θ A i) ∧
        (∀ (i : ℕ) (a : A) (k : K i) (s : 𝒰.Idx i),
          Θ A i (a ⊗ₜ[R] k) s
            = a • (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
                ((Scheme.Modules.pullback
                  (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).res
                (𝒰.baseChange_inter_le π A s)
                ((((Scheme.Modules.pullbackPushforwardAdjunction
                  (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app
                  (𝒰.inter s)).hom (φ i k s))) ∧
        (∀ x : A ⊗[R] K 0, (δ 0).baseChange A x = 0 → Θ A 0 x = 0 → x = 0) ∧
        (∀ y : (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).cochain (𝒰.baseChange π A) 0,
          (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d (𝒰.baseChange π A) 0 y = 0 →
          ∃ x : A ⊗[R] K 0, (δ 0).baseChange A x = 0 ∧ Θ A 0 x = y) ∧
        (∀ (i : ℕ) (x : A ⊗[R] K (i + 1)), (δ (i + 1)).baseChange A x = 0 →
          Θ A (i + 1) x ∈ LinearMap.range
            ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d (𝒰.baseChange π A) i) →
          x ∈ LinearMap.range ((δ i).baseChange A)) ∧
        (∀ (i : ℕ) (y : (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).cochain (𝒰.baseChange π A) (i + 1)),
          (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d (𝒰.baseChange π A) (i + 1) y = 0 →
          ∃ x : A ⊗[R] K (i + 1), (δ (i + 1)).baseChange A x = 0 ∧
            Θ A (i + 1) x - y ∈ LinearMap.range
              ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
                ((Scheme.Modules.pullback
                  (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d (𝒰.baseChange π A) i)) := by
  classical

  haveI hflat : ∀ i, Module.Flat R ((OModulePresheaf.ofModules π M).cochain 𝒰 i) := fun i =>
    OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial π M htriv 𝒰 i
  have hfinC : (OModulePresheaf.ofModules π M).CechFinite 𝒰 :=
    OModulePresheaf.cechFinite_ofModules_of_locallyTrivial π M htriv 𝒰
  have hCbdd : ∀ i, n < i → Subsingleton ((OModulePresheaf.ofModules π M).cochain 𝒰 i) := fun i hi =>
    S32F2.subsingleton_cochain (OModulePresheaf.ofModules π M) 𝒰 (by omega)

  obtain ⟨K, instACG, instMod, hKfin, hKproj, δ, hδδ, hKbdd, φ, hφ, h0inj, h0surj, hinj, hsurj⟩ :=
    Module.exists_projective_complex_quasiIso_of_flat_complex R (fun i => (OModulePresheaf.ofModules π M).cochain 𝒰 i)
      (fun i => (OModulePresheaf.ofModules π M).d 𝒰 i) (fun i => (OModulePresheaf.ofModules π M).d_comp_d 𝒰 i) n hCbdd
      hfinC.1 hfinC.2

  have hE := fun (A : Type u) [CommRing A] [Algebra R A] =>
    OModulePresheaf.exists_cochain_baseChange_equiv_of_locallyTrivial π 𝒰 M htriv A
  refine ⟨K, instACG, instMod, hKfin, hKproj, δ, hδδ, hKbdd, φ, hφ,
    fun A _ _ i => ((hE A).choose i).toLinearMap ∘ₗ (φ i).baseChange A, fun A _ _ => ?_⟩
  obtain ⟨hEd, hEtmul⟩ := (hE A).choose_spec

  obtain ⟨hA0inj, hA0surj, hAinj, hAsurj⟩ :=
    Module.quasiIso_baseChange_of_quasiIso_of_flat R K δ hδδ (fun i => (OModulePresheaf.ofModules π M).cochain 𝒰 i)
      (fun i => (OModulePresheaf.ofModules π M).d 𝒰 i) (fun i => (OModulePresheaf.ofModules π M).d_comp_d 𝒰 i) n hKbdd
      hCbdd φ hφ h0inj h0surj hinj hsurj A
  have hφA : ∀ i, ((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A ∘ₗ (φ i).baseChange A
      = (φ (i + 1)).baseChange A ∘ₗ (δ i).baseChange A := by
    intro i; rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hφ i]
  refine ⟨fun i => S32F2.transport_comm (fun i => (δ i).baseChange A)
      (fun i => ((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A) _ (fun i => (φ i).baseChange A) _ hEd hφA i,
    fun i a k s => ?_,
    fun x hx hx' => S32F2.transport_h0inj (fun i => (δ i).baseChange A) (fun i => (φ i).baseChange A) _ hA0inj x hx hx',
    fun y hy => S32F2.transport_h0surj (fun i => (δ i).baseChange A)
      (fun i => ((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A) _ (fun i => (φ i).baseChange A) _ hEd hA0surj y hy,
    fun i x hx hx' => S32F2.transport_hinj (fun i => (δ i).baseChange A)
      (fun i => ((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A) _ (fun i => (φ i).baseChange A) _ hEd i (hAinj i) x hx hx',
    fun i y hy => S32F2.transport_hsurj (fun i => (δ i).baseChange A)
      (fun i => ((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A) _ (fun i => (φ i).baseChange A) _ hEd i (hAsurj i) y hy⟩

  rw [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, hEtmul]

end

end S_AlgebraicGeometry_OModulePresheaf_exists_projective_complex_forall_baseChange_quasiIso_cech_of_locallyTrivial
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_projective_complex_forall_baseChange_quasiIso_cech_of_locallyTrivial (solution)
