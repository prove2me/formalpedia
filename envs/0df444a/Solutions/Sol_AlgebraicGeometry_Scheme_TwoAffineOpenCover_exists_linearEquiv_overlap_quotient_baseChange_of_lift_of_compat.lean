-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_overlap_quotient_baseChange_of_lift_of_compat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/befa42eb-36d2-5b47-b553-9bd6949b57af

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_overlap_quotient_baseChange_of_lift_of_compat

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 16000000

noncomputable section

section N4Transport

variable {R R' : Type u} [CommRing R] [CommRing R']

scoped instance instRHIPfwd (φ : R ≃+* R') : RingHomInvPair (φ : R →+* R') (φ.symm : R' →+* R) :=
  ⟨RingHom.ext φ.symm_apply_apply, RingHom.ext φ.apply_symm_apply⟩
scoped instance instRHIPbwd (φ : R ≃+* R') : RingHomInvPair (φ.symm : R' →+* R) (φ : R →+* R') :=
  ⟨RingHom.ext φ.apply_symm_apply, RingHom.ext φ.symm_apply_apply⟩

variable {S S' : Type u} [CommRing S] [CommRing S']

theorem transportAndApply_exists (φR : R ≃+* R') (φS : S ≃+* S')
    (ψ : R →+* S) (ρ : R' →+* S')
    (hcompat : ∀ r, φS (ψ r) = ρ (φR r))
    (M N : Type u) [AddCommGroup M] [Module R' M] [AddCommGroup N] [Module S' N]
    (e : letI : Algebra R' S' := ρ.toAlgebra; S' ⊗[R'] M ≃ₗ[S'] N) :
    letI : Algebra R S := ψ.toAlgebra
    letI : Algebra R' S' := ρ.toAlgebra
    letI : Module R M := Module.compHom M φR.toRingHom
    letI : Module S N := Module.compHom N φS.toRingHom
    ∃ ta : (S ⊗[R] M) ≃ₗ[S] N, ∀ m : M, ta ((1:S) ⊗ₜ[R] m) = e ((1:S') ⊗ₜ[R'] m) := by
  letI : Algebra R S := ψ.toAlgebra
  letI : Algebra R' S' := ρ.toAlgebra
  letI : Module R M := Module.compHom M φR.toRingHom
  letI : Module S N := Module.compHom N φS.toRingHom
  let e1 : S ≃ₛₗ[(φR : R →+* R')] S' :=
    { toFun := φS, map_add' := φS.map_add,
      map_smul' := fun r s => by
        show φS (ψ r * s) = ρ (φR r) * φS s
        rw [map_mul, hcompat],
      invFun := φS.symm, left_inv := φS.symm_apply_apply,
      right_inv := φS.apply_symm_apply }
  let e2 : M ≃ₛₗ[(φR : R →+* R')] M :=
    { toFun := id, map_add' := fun _ _ => rfl,
      map_smul' := fun r m => rfl,
      invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  let tc := TensorProduct.congr e1 e2
  have htc_tmul : ∀ (t : S) (m : M), tc (t ⊗ₜ[R] m) = (φS t) ⊗ₜ[R'] m := fun t m => rfl
  have hta_one_tmul : ∀ m : M, e (tc ((1:S) ⊗ₜ[R] m)) = e ((1:S') ⊗ₜ[R'] m) := fun m => by
    rw [htc_tmul, map_one]
  refine ⟨⟨⟨⟨fun x => e (tc x), fun x y => by simp only [map_add]⟩, fun s x => ?_⟩,
    fun n => tc.symm (e.symm n), fun x => by simp, fun n => by simp⟩, hta_one_tmul⟩
  show e (tc (s • x)) = s • e (tc x)
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul t m =>
    show e (tc ((s * t) ⊗ₜ[R] m)) = φS s • e (tc (t ⊗ₜ[R] m))
    rw [htc_tmul, htc_tmul, ← e.map_smul, TensorProduct.smul_tmul', smul_eq_mul, ← map_mul]

noncomputable def transportAndApply (φR : R ≃+* R') (φS : S ≃+* S')
    (ψ : R →+* S) (ρ : R' →+* S')
    (hcompat : ∀ r, φS (ψ r) = ρ (φR r))
    (M N : Type u) [AddCommGroup M] [Module R' M] [AddCommGroup N] [Module S' N]
    (e : letI : Algebra R' S' := ρ.toAlgebra; S' ⊗[R'] M ≃ₗ[S'] N) :
    letI : Algebra R S := ψ.toAlgebra
    letI : Module R M := Module.compHom M φR.toRingHom
    letI : Module S N := Module.compHom N φS.toRingHom
    (S ⊗[R] M) ≃ₗ[S] N :=
  letI : Algebra R S := ψ.toAlgebra
  letI : Algebra R' S' := ρ.toAlgebra
  letI : Module R M := Module.compHom M φR.toRingHom
  letI : Module S N := Module.compHom N φS.toRingHom
  (transportAndApply_exists φR φS ψ ρ hcompat M N e).choose

theorem transportAndApply_one_tmul (φR : R ≃+* R') (φS : S ≃+* S')
    (ψ : R →+* S) (ρ : R' →+* S')
    (hcompat : ∀ r, φS (ψ r) = ρ (φR r))
    (M N : Type u) [AddCommGroup M] [Module R' M] [AddCommGroup N] [Module S' N]
    (e : letI : Algebra R' S' := ρ.toAlgebra; S' ⊗[R'] M ≃ₗ[S'] N) (m : M) :
    letI : Algebra R S := ψ.toAlgebra
    letI : Algebra R' S' := ρ.toAlgebra
    letI : Module R M := Module.compHom M φR.toRingHom
    letI : Module S N := Module.compHom N φS.toRingHom
    transportAndApply φR φS ψ ρ hcompat M N e ((1:S) ⊗ₜ[R] m) = e ((1:S') ⊗ₜ[R'] m) :=
  letI : Algebra R S := ψ.toAlgebra
  letI : Algebra R' S' := ρ.toAlgebra
  letI : Module R M := Module.compHom M φR.toRingHom
  letI : Module S N := Module.compHom N φS.toRingHom
  (transportAndApply_exists φR φS ψ ρ hcompat M N e).choose_spec m

end N4Transport

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (𝒱 : C.TwoAffineOpenCover)
    {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B)
    (M : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (B ⧸ I))).Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (J0 : Ideal ((𝒱.pullback c B).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B))).A0)
    (J1 : Ideal ((𝒱.pullback c B).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B))).A1)
    (J01 : Ideal ((𝒱.pullback c B).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B))).A01) :
    let 𝒱B := 𝒱.pullback c B
    let cB := Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B)
    let 𝒱BI := 𝒱.pullback c (B ⧸ I)
    let cBI := Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R (B ⧸ I))
    let A0B := (𝒱B.cover cB).A0
    let A1B := (𝒱B.cover cB).A1
    let A01B := (𝒱B.cover cB).A01
    let P0 := (𝒱BI.sectionsOf cBI M).M0
    let P1 := (𝒱BI.sectionsOf cBI M).M1
    ∀ (φ0 : A0B ⧸ J0 ≃+* (𝒱BI.cover cBI).A0)
      (φ1 : A1B ⧸ J1 ≃+* (𝒱BI.cover cBI).A1)
      (φ01 : A01B ⧸ J01 ≃+* (𝒱BI.cover cBI).A01)
      (_ : ∀ a, φ01 (Ideal.Quotient.mk J01 ((𝒱B.cover cB).ρ0 a)) =
                (𝒱BI.cover cBI).ρ0 (φ0 (Ideal.Quotient.mk J0 a)))
      (_ : ∀ a, φ01 (Ideal.Quotient.mk J01 ((𝒱B.cover cB).ρ1 a)) =
                (𝒱BI.cover cBI).ρ1 (φ1 (Ideal.Quotient.mk J1 a)))
      (P0' : Type u) [AddCommGroup P0'] [Module A0B P0'] [Module.Projective A0B P0']
      (P1' : Type u) [AddCommGroup P1'] [Module A1B P1'] [Module.Projective A1B P1'],
      letI : Module (A0B ⧸ J0) P0 := Module.compHom P0 φ0.toRingHom
      letI : Module (A1B ⧸ J1) P1 := Module.compHom P1 φ1.toRingHom
      ∀ (iso0 : (A0B ⧸ J0) ⊗[A0B] P0' ≃ₗ[A0B ⧸ J0] P0)
        (iso1 : (A1B ⧸ J1) ⊗[A1B] P1' ≃ₗ[A1B ⧸ J1] P1),
      letI : Algebra A0B A01B := (𝒱B.cover cB).ρ0.toRingHom.toAlgebra
      letI : Algebra A1B A01B := (𝒱B.cover cB).ρ1.toRingHom.toAlgebra
      letI : Module (A01B ⧸ J01) (𝒱BI.sectionsOf cBI M).M01 := Module.compHom _ φ01.toRingHom
      ∃ (iso01₀ : (A01B ⧸ J01) ⊗[A01B] (A01B ⊗[A0B] P0') ≃ₗ[A01B ⧸ J01] (𝒱BI.sectionsOf cBI M).M01)
        (iso01₁ : (A01B ⧸ J01) ⊗[A01B] (A01B ⊗[A1B] P1') ≃ₗ[A01B ⧸ J01] (𝒱BI.sectionsOf cBI M).M01),
        (∀ p : P0', iso01₀ ((1 : A01B ⧸ J01) ⊗ₜ[A01B] ((1 : A01B) ⊗ₜ[A0B] p)) =
              (𝒱BI.sectionsOf cBI M).r0 (iso0 ((1 : A0B ⧸ J0) ⊗ₜ[A0B] p))) ∧
        (∀ p : P1', iso01₁ ((1 : A01B ⧸ J01) ⊗ₜ[A01B] ((1 : A01B) ⊗ₜ[A1B] p)) =
              (𝒱BI.sectionsOf cBI M).r1 (iso1 ((1 : A1B ⧸ J1) ⊗ₜ[A1B] p))) := by
  intro 𝒱B cB 𝒱BI cBI A0B A1B A01B P0 P1 φ0 φ1 φ01 hφρ0 hφρ1
    P0' _ _ _ P1' _ _ _ iso0 iso1

  letI instM0 : Module (A0B ⧸ J0) P0 := Module.compHom P0 φ0.toRingHom
  letI instM1 : Module (A1B ⧸ J1) P1 := Module.compHom P1 φ1.toRingHom
  letI instAlg0 : Algebra A0B A01B := (𝒱B.cover cB).ρ0.toRingHom.toAlgebra
  letI instAlg1 : Algebra A1B A01B := (𝒱B.cover cB).ρ1.toRingHom.toAlgebra

  set A0BI := (𝒱BI.cover cBI).A0
  set A1BI := (𝒱BI.cover cBI).A1
  set A01BI := (𝒱BI.cover cBI).A01
  letI algρ0BI : Algebra A0BI A01BI := (𝒱BI.cover cBI).ρ0.toRingHom.toAlgebra
  letI algρ1BI : Algebra A1BI A01BI := (𝒱BI.cover cBI).ρ1.toRingHom.toAlgebra

  obtain ⟨rbc0, rbc1, hrbc0, hrbc1⟩ :=
    𝒱BI.exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible cBI M hM

  have hker0 : ∀ a ∈ J0, (Ideal.Quotient.mk J01) ((𝒱B.cover cB).ρ0 a) = 0 := by
    intro a ha
    have h := hφρ0 a
    have : φ0 (Ideal.Quotient.mk J0 a) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]; exact map_zero φ0
    rw [this, map_zero] at h
    exact φ01.injective (h.trans (map_zero φ01).symm)
  let ψ0 : A0B ⧸ J0 →+* A01B ⧸ J01 :=
    Ideal.Quotient.lift J0 ((Ideal.Quotient.mk J01).comp (𝒱B.cover cB).ρ0.toRingHom) (by
      intro a ha; simp only [RingHom.comp_apply]; exact hker0 a ha)

  have hψ0 : ∀ x, φ01 (ψ0 x) = (𝒱BI.cover cBI).ρ0 (φ0 x) := by
    intro x; obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hφρ0 a

  letI algψ0 : Algebra (A0B ⧸ J0) (A01B ⧸ J01) := ψ0.toAlgebra
  haveI istA0B_qt0_qt01 : IsScalarTower A0B (A0B ⧸ J0) (A01B ⧸ J01) :=
    IsScalarTower.of_algebraMap_eq (fun a => (Ideal.Quotient.lift_mk J0 _ _).symm)

  let e1₀ : (A01B ⧸ J01) ⊗[A01B] (A01B ⊗[A0B] P0') ≃ₗ[A01B ⧸ J01] (A01B ⧸ J01) ⊗[A0B] P0' :=
    AlgebraTensorModule.cancelBaseChange A0B A01B (A01B ⧸ J01) (A01B ⧸ J01) P0'

  let e2₀ : (A01B ⧸ J01) ⊗[A0B] P0' ≃ₗ[A01B ⧸ J01]
      (A01B ⧸ J01) ⊗[A0B ⧸ J0] ((A0B ⧸ J0) ⊗[A0B] P0') :=
    (AlgebraTensorModule.cancelBaseChange A0B (A0B ⧸ J0) (A01B ⧸ J01) (A01B ⧸ J01) P0').symm

  let e3₀ : (A01B ⧸ J01) ⊗[A0B ⧸ J0] ((A0B ⧸ J0) ⊗[A0B] P0') ≃ₗ[A01B ⧸ J01]
      (A01B ⧸ J01) ⊗[A0B ⧸ J0] P0 :=
    LinearEquiv.baseChange (A0B ⧸ J0) (A01B ⧸ J01) _ _ iso0

  letI : Module (A01B ⧸ J01) (𝒱BI.sectionsOf cBI M).M01 :=
    Module.compHom (𝒱BI.sectionsOf cBI M).M01 φ01.toRingHom
  let e4₀ : (A01B ⧸ J01) ⊗[A0B ⧸ J0] P0 ≃ₗ[A01B ⧸ J01] (𝒱BI.sectionsOf cBI M).M01 :=
    transportAndApply φ0 φ01 ψ0 (𝒱BI.cover cBI).ρ0.toRingHom hψ0 P0 _ rbc0

  have hker1 : ∀ a ∈ J1, (Ideal.Quotient.mk J01) ((𝒱B.cover cB).ρ1 a) = 0 := by
    intro a ha
    have h := hφρ1 a
    have : φ1 (Ideal.Quotient.mk J1 a) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]; exact map_zero φ1
    rw [this, map_zero] at h
    exact φ01.injective (h.trans (map_zero φ01).symm)
  let ψ1 : A1B ⧸ J1 →+* A01B ⧸ J01 :=
    Ideal.Quotient.lift J1 ((Ideal.Quotient.mk J01).comp (𝒱B.cover cB).ρ1.toRingHom) (by
      intro a ha; simp only [RingHom.comp_apply]; exact hker1 a ha)
  have hψ1 : ∀ x, φ01 (ψ1 x) = (𝒱BI.cover cBI).ρ1 (φ1 x) := by
    intro x; obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x; exact hφρ1 a
  letI algψ1 : Algebra (A1B ⧸ J1) (A01B ⧸ J01) := ψ1.toAlgebra
  haveI : IsScalarTower A1B (A1B ⧸ J1) (A01B ⧸ J01) :=
    IsScalarTower.of_algebraMap_eq (fun a => (Ideal.Quotient.lift_mk J1 _ _).symm)
  let e1₁ : (A01B ⧸ J01) ⊗[A01B] (A01B ⊗[A1B] P1') ≃ₗ[A01B ⧸ J01] (A01B ⧸ J01) ⊗[A1B] P1' :=
    AlgebraTensorModule.cancelBaseChange A1B A01B (A01B ⧸ J01) (A01B ⧸ J01) P1'
  let e2₁ : (A01B ⧸ J01) ⊗[A1B] P1' ≃ₗ[A01B ⧸ J01]
      (A01B ⧸ J01) ⊗[A1B ⧸ J1] ((A1B ⧸ J1) ⊗[A1B] P1') :=
    (AlgebraTensorModule.cancelBaseChange A1B (A1B ⧸ J1) (A01B ⧸ J01) (A01B ⧸ J01) P1').symm
  let e3₁ : (A01B ⧸ J01) ⊗[A1B ⧸ J1] ((A1B ⧸ J1) ⊗[A1B] P1') ≃ₗ[A01B ⧸ J01]
      (A01B ⧸ J01) ⊗[A1B ⧸ J1] P1 :=
    LinearEquiv.baseChange (A1B ⧸ J1) (A01B ⧸ J01) _ _ iso1
  let e4₁ : (A01B ⧸ J01) ⊗[A1B ⧸ J1] P1 ≃ₗ[A01B ⧸ J01] (𝒱BI.sectionsOf cBI M).M01 :=
    transportAndApply φ1 φ01 ψ1 (𝒱BI.cover cBI).ρ1.toRingHom hψ1 P1 _ rbc1

  refine ⟨e1₀.trans (e2₀.trans (e3₀.trans e4₀)),
          e1₁.trans (e2₁.trans (e3₁.trans e4₁)), ?_, ?_⟩
  · intro p
    simp only [LinearEquiv.trans_apply]

    have he1 : e1₀ ((1 : A01B ⧸ J01) ⊗ₜ[A01B] ((1 : A01B) ⊗ₜ[A0B] p)) =
               (1 : A01B ⧸ J01) ⊗ₜ[A0B] p := by
      simp only [e1₀, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
    have he2 : e2₀ ((1 : A01B ⧸ J01) ⊗ₜ[A0B] p) =
               (1 : A01B ⧸ J01) ⊗ₜ[A0B ⧸ J0] ((1 : A0B ⧸ J0) ⊗ₜ[A0B] p) := by
      simp only [e2₀]
      rw [LinearEquiv.symm_apply_eq,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
    have he3 : e3₀ ((1 : A01B ⧸ J01) ⊗ₜ[A0B ⧸ J0] ((1 : A0B ⧸ J0) ⊗ₜ[A0B] p)) =
               (1 : A01B ⧸ J01) ⊗ₜ[A0B ⧸ J0] iso0 ((1 : A0B ⧸ J0) ⊗ₜ[A0B] p) := by
      simp only [e3₀, LinearEquiv.baseChange_tmul]
    have he4 : e4₀ ((1 : A01B ⧸ J01) ⊗ₜ[A0B ⧸ J0] iso0 ((1 : A0B ⧸ J0) ⊗ₜ[A0B] p)) =
               (𝒱BI.sectionsOf cBI M).r0 (iso0 ((1 : A0B ⧸ J0) ⊗ₜ[A0B] p)) := by
      rw [show e4₀ = transportAndApply φ0 φ01 ψ0 (𝒱BI.cover cBI).ρ0.toRingHom hψ0 P0 _ rbc0 from rfl,
          transportAndApply_one_tmul]
      exact hrbc0 _
    rw [he1, he2, he3, he4]
  · intro p
    simp only [LinearEquiv.trans_apply]

    have he1 : e1₁ ((1 : A01B ⧸ J01) ⊗ₜ[A01B] ((1 : A01B) ⊗ₜ[A1B] p)) =
               (1 : A01B ⧸ J01) ⊗ₜ[A1B] p := by
      simp only [e1₁, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
    have he2 : e2₁ ((1 : A01B ⧸ J01) ⊗ₜ[A1B] p) =
               (1 : A01B ⧸ J01) ⊗ₜ[A1B ⧸ J1] ((1 : A1B ⧸ J1) ⊗ₜ[A1B] p) := by
      simp only [e2₁]
      rw [LinearEquiv.symm_apply_eq,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
    have he3 : e3₁ ((1 : A01B ⧸ J01) ⊗ₜ[A1B ⧸ J1] ((1 : A1B ⧸ J1) ⊗ₜ[A1B] p)) =
               (1 : A01B ⧸ J01) ⊗ₜ[A1B ⧸ J1] iso1 ((1 : A1B ⧸ J1) ⊗ₜ[A1B] p) := by
      simp only [e3₁, LinearEquiv.baseChange_tmul]
    have he4 : e4₁ ((1 : A01B ⧸ J01) ⊗ₜ[A1B ⧸ J1] iso1 ((1 : A1B ⧸ J1) ⊗ₜ[A1B] p)) =
               (𝒱BI.sectionsOf cBI M).r1 (iso1 ((1 : A1B ⧸ J1) ⊗ₜ[A1B] p)) := by
      rw [show e4₁ = transportAndApply φ1 φ01 ψ1 (𝒱BI.cover cBI).ρ1.toRingHom hψ1 P1 _ rbc1 from rfl,
          transportAndApply_one_tmul]
      exact hrbc1 _
    rw [he1, he2, he3, he4]

end
end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_overlap_quotient_baseChange_of_lift_of_compat
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_overlap_quotient_baseChange_of_lift_of_compat (solution)
