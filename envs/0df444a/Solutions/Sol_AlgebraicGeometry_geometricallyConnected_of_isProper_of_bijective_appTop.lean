-- Prove2me | solution 1 for AlgebraicGeometry.geometricallyConnected_of_isProper_of_bijective_appTop
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/2629070b-3b45-5b83-95bc-2434d93fa702

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop
import Theorems.Thm_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat
import Theorems.Thm_AlgebraicGeometry_finite_appTop_of_isProper_of_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

p2m_open_scoped "TensorProduct Polynomial AlgebraicGeometry.Polynomial"

namespace P2mKcGeomConnFibres

universe u

def TrivialIdem (R : Type*) [Mul R] [Zero R] [One R] : Prop :=
  ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1

section transfer

variable {R S : Type*} [CommRing R] [CommRing S]

theorem trivialIdem_of_subsingleton [Subsingleton R] : TrivialIdem R :=
  fun e _ => Or.inl (Subsingleton.elim _ _)

theorem trivialIdem_of_surjective_of_ker_nil (f : R →+* S) (hf : Function.Surjective f)
    (hker : ∀ x ∈ RingHom.ker f, IsNilpotent x) (h : TrivialIdem R) : TrivialIdem S := by
  intro e he
  obtain ⟨e', he', rfl⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent f hker e (hf e) he
  rcases h e' he' with rfl | rfl <;> simp

theorem trivialIdem_of_ker_nil (f : R →+* S)
    (hker : ∀ x ∈ RingHom.ker f, IsNilpotent x) (h : TrivialIdem S) : TrivialIdem R := by
  intro e he
  rcases h (f e) (he.map f) with h0 | h1
  · left
    obtain ⟨n, hn⟩ := hker e h0
    rw [← he.pow_succ_eq n, pow_succ, hn, zero_mul]
  · right
    have h1' : (1 - e) ∈ RingHom.ker f := by simp [RingHom.mem_ker, map_sub, h1]
    obtain ⟨n, hn⟩ := hker _ h1'
    have := (he.one_sub).pow_succ_eq n
    rw [pow_succ, hn, zero_mul] at this
    exact (sub_eq_zero.mp this.symm).symm

theorem trivialIdem_of_ringEquiv (e : R ≃+* S) (h : TrivialIdem R) : TrivialIdem S := by
  intro x hx
  rcases h (e.symm x) (hx.map e.symm.toRingHom) with h0 | h1
  · left; simpa using congrArg e h0
  · right; simpa using congrArg e h1

end transfer

section artin

variable {R : Type*} [CommRing R]

theorem isNilpotent_or_isUnit_of_isArtinianRing [IsArtinianRing R] (h : TrivialIdem R)
    (x : R) : IsNilpotent x ∨ IsUnit x := by
  let f : ℕ →o (Ideal R)ᵒᵈ :=
    ⟨fun n => OrderDual.toDual (Ideal.span {x ^ n}), fun m n hmn => by
      change Ideal.span {x ^ n} ≤ Ideal.span {x ^ m}
      rw [Ideal.span_singleton_le_span_singleton]
      exact pow_dvd_pow x hmn⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes f
  set N := n + 1 with hN
  have hstab : Ideal.span {x ^ N} = Ideal.span {x ^ (2 * N)} := by
    have h1 := hn N (by omega)
    have h2 := hn (2 * N) (by omega)
    exact (congrArg OrderDual.ofDual h1).symm.trans (congrArg OrderDual.ofDual h2)
  have hx : x ^ N ∈ Ideal.span {x ^ (2 * N)} := hstab ▸ Ideal.mem_span_singleton_self _
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hx

  set e := z * x ^ N with he_def
  have he : IsIdempotentElem e := by
    change z * x ^ N * (z * x ^ N) = z * x ^ N
    calc z * x ^ N * (z * x ^ N) = z * (z * x ^ (2 * N)) := by ring
      _ = z * x ^ N := by rw [hz]
  rcases h e he with h0 | h1
  · left
    refine ⟨N, ?_⟩
    calc x ^ N = z * x ^ (2 * N) := hz.symm
      _ = e * x ^ N := by rw [he_def]; ring
      _ = 0 := by rw [h0, zero_mul]
  · right
    have hu : IsUnit (x ^ N) := IsUnit.of_mul_eq_one_right z h1
    exact (isUnit_pow_iff (by omega)).mp hu

theorem isLocalRing_of_isArtinianRing [IsArtinianRing R] [Nontrivial R] (h : TrivialIdem R) :
    IsLocalRing R := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases isNilpotent_or_isUnit_of_isArtinianRing h a with ha | ha
  · exact Or.inr ha.isUnit_one_sub
  · exact Or.inl ha

theorem isNilpotent_of_mem_maximalIdeal [IsArtinianRing R] [Nontrivial R] (h : TrivialIdem R)
    {x : R} (hx : x ∈ @IsLocalRing.maximalIdeal R _ (isLocalRing_of_isArtinianRing h)) :
    IsNilpotent x := by
  letI := isLocalRing_of_isArtinianRing h
  rcases isNilpotent_or_isUnit_of_isArtinianRing h x with h' | h'
  · exact h'
  · exact absurd h' ((IsLocalRing.mem_maximalIdeal _).mp hx)

end artin

section kernil

variable (κ : Type u) [Field κ] (L : Type u) [CommRing L] [Algebra κ L]

theorem ker_lTensor_nil {L' : Type u} [CommRing L'] [Algebra κ L'] (g : L →ₐ[κ] L')
    (hg : Function.Surjective g) (hnil : IsNilpotent (RingHom.ker g))
    (A : Type u) [CommRing A] [Algebra κ A] :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id κ A) g) ∧
    ∀ x ∈ RingHom.ker (Algebra.TensorProduct.map (AlgHom.id κ A) g), IsNilpotent x := by
  refine ⟨?_, ?_⟩
  · exact Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hg
  · intro x hx
    rw [Algebra.TensorProduct.lTensor_ker g hg] at hx
    obtain ⟨n, hn⟩ := hnil
    have hpow : (Ideal.map (Algebra.TensorProduct.includeRight : L →ₐ[κ] A ⊗[κ] L)
        (RingHom.ker g)) ^ n = ⊥ := by
      rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rw [hpow] at this
    simpa using this

end kernil

section purelyInsep

variable (κ : Type u) [Field κ] (ℓ : Type u) [Field ℓ] [Algebra κ ℓ]
    (k : Type u) [Field k] [Algebra κ k]

theorem trivialIdem_tensor_of_isPurelyInseparable [IsPurelyInseparable κ ℓ] :
    TrivialIdem (k ⊗[κ] ℓ) := by
  classical
  haveI : Nontrivial (k ⊗[κ] ℓ) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain κ k ℓ
      (algebraMap κ k).injective (algebraMap κ ℓ).injective
  let q := ringExpChar κ
  haveI hq : ExpChar κ q := ringExpChar.expChar κ
  haveI : ExpChar (k ⊗[κ] ℓ) q :=
    expChar_of_injective_algebraMap (algebraMap κ (k ⊗[κ] ℓ)).injective q

  have key : ∀ z : k ⊗[κ] ℓ, ∃ (n : ℕ) (c : k), z ^ q ^ n = c ⊗ₜ[κ] 1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul μ lam =>
      obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem κ q lam
      refine ⟨n, c • μ ^ q ^ n, ?_⟩
      rw [Algebra.TensorProduct.tmul_pow, ← hc, Algebra.algebraMap_eq_smul_one,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    | add z₁ z₂ h₁ h₂ =>
      obtain ⟨n₁, c₁, h₁⟩ := h₁
      obtain ⟨n₂, c₂, h₂⟩ := h₂
      refine ⟨n₁ + n₂, c₁ ^ q ^ n₂ + c₂ ^ q ^ n₁, ?_⟩
      rw [add_pow_expChar_pow z₁ z₂, TensorProduct.add_tmul]
      congr 1
      · rw [pow_add, pow_mul, h₁, Algebra.TensorProduct.tmul_pow, one_pow]
      · rw [add_comm n₁, pow_add, pow_mul, h₂, Algebra.TensorProduct.tmul_pow, one_pow]
  intro e he
  obtain ⟨n, c, hc⟩ := key e
  have hqn : q ^ n ≠ 0 := pow_ne_zero _ (expChar_pos κ q).ne'
  have hepow : e ^ q ^ n = e := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hqn
    rw [hm, he.pow_succ_eq]
  rw [hepow] at hc
  by_cases hc0 : c = 0
  · left; rw [hc, hc0, TensorProduct.zero_tmul]
  · right
    have hunit : IsUnit e := by
      rw [hc]
      refine IsUnit.of_mul_eq_one (c⁻¹ ⊗ₜ[κ] (1 : ℓ)) ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hc0, one_mul]
      rfl
    obtain ⟨u, hu⟩ := hunit
    calc e = ((↑u⁻¹ : k ⊗[κ] ℓ) * ↑u) * e := by simp
      _ = ↑u⁻¹ * (e * e) := by rw [hu, mul_assoc]
      _ = ↑u⁻¹ * e := by rw [he.eq]
      _ = 1 := by rw [← hu, Units.inv_mul]

end purelyInsep

section separableStep

variable (κ : Type u) [Field κ] (ℓ : Type u) [Field ℓ] [Algebra κ ℓ] [Module.Finite κ ℓ]

theorem mem_range_of_isSeparable_of_trivialIdem (a : ℓ) (hsep : IsSeparable κ a)
    (h : TrivialIdem (AdjoinRoot (minpoly κ a) ⊗[κ] ℓ)) : a ∈ (algebraMap κ ℓ).range := by
  classical
  by_contra hna
  have hint : IsIntegral κ a := hsep.isIntegral
  set P := minpoly κ a with hPdef
  haveI hirr : Fact (Irreducible P) := ⟨minpoly.irreducible hint⟩
  have hdeg : 2 ≤ P.natDegree := (minpoly.two_le_natDegree_iff hint).mpr hna

  let ℓb := AlgebraicClosure ℓ
  have hsplit : (P.map (algebraMap κ ℓb)).Splits := IsAlgClosed.splits _
  have hcard : Fintype.card (P.rootSet ℓb) = P.natDegree :=
    Polynomial.card_rootSet_eq_natDegree hsep hsplit
  have ha' : algebraMap ℓ ℓb a ∈ P.rootSet ℓb := by
    rw [Polynomial.mem_rootSet_of_ne (minpoly.ne_zero hint), Polynomial.aeval_algebraMap_apply,
      minpoly.aeval, map_zero]
  have h1lt : 1 < Fintype.card (P.rootSet ℓb) := by omega
  obtain ⟨⟨b, hb⟩, hba⟩ :=
    Fintype.exists_ne_of_one_lt_card (by convert h1lt) (⟨_, ha'⟩ : P.rootSet ℓb)
  have hba' : b ≠ algebraMap ℓ ℓb a := fun h' => hba (Subtype.ext h')
  have hbroot : P.aeval b = 0 := (Polynomial.mem_rootSet_of_ne (minpoly.ne_zero hint)).mp hb

  let E := AdjoinRoot P
  haveI : Module.Finite κ E := (AdjoinRoot.powerBasis (minpoly.ne_zero hint)).finite
  let m₁ : E ⊗[κ] ℓ →ₐ[κ] ℓ :=
    Algebra.TensorProduct.lift
      (AdjoinRoot.liftAlgHom P (Algebra.ofId κ ℓ) a (by
        change Polynomial.eval₂ (algebraMap κ ℓ) a P = 0
        rw [← Polynomial.aeval_def]; exact minpoly.aeval κ a))
      (AlgHom.id κ ℓ) (fun _ _ => Commute.all _ _)
  let m₂ : E ⊗[κ] ℓ →ₐ[κ] ℓb :=
    Algebra.TensorProduct.lift
      (AdjoinRoot.liftAlgHom P (Algebra.ofId κ ℓb) b (by
        change Polynomial.eval₂ (algebraMap κ ℓb) b P = 0
        rw [← Polynomial.aeval_def]; exact hbroot))
      (IsScalarTower.toAlgHom κ ℓ ℓb) (fun _ _ => Commute.all _ _)
  let z : E ⊗[κ] ℓ := AdjoinRoot.root P ⊗ₜ[κ] 1 - 1 ⊗ₜ[κ] a
  have hz₁ : m₁ z = 0 := by
    simp only [z, map_sub, m₁, Algebra.TensorProduct.lift_tmul, map_one, mul_one, one_mul,
      AlgHom.id_apply]
    rw [AdjoinRoot.coe_liftAlgHom, AdjoinRoot.lift_root, sub_self]
  have hz₂ : m₂ z = b - algebraMap ℓ ℓb a := by
    simp only [z, map_sub, m₂, Algebra.TensorProduct.lift_tmul, map_one, mul_one, one_mul,
      IsScalarTower.coe_toAlgHom']
    rw [AdjoinRoot.coe_liftAlgHom, AdjoinRoot.lift_root]

  haveI : IsArtinianRing (E ⊗[κ] ℓ) := IsArtinianRing.of_finite κ _
  rcases isNilpotent_or_isUnit_of_isArtinianRing h z with hz | hz
  · have : IsNilpotent (m₂ z) := hz.map m₂
    rw [hz₂] at this
    exact hba' (sub_eq_zero.mp this.eq_zero)
  · have : IsUnit (m₁ z) := hz.map m₁
    rw [hz₁] at this
    exact not_isUnit_zero this

end separableStep

section descent

variable (κ : Type u) [Field κ] (L : Type u) [CommRing L] [Algebra κ L] [Module.Finite κ L]

theorem trivialIdem_baseChange (h1 : TrivialIdem L)
    (h2 : ∀ P : κ[X], P.Monic → Irreducible P → TrivialIdem (AdjoinRoot P ⊗[κ] L))
    (k : Type u) [Field k] [Algebra κ k] : TrivialIdem (k ⊗[κ] L) := by
  classical
  rcases subsingleton_or_nontrivial L with hL | hL
  · haveI : Subsingleton (k ⊗[κ] L) := by
      haveI : Subsingleton L := hL
      infer_instance
    exact trivialIdem_of_subsingleton
  haveI : IsArtinianRing L := IsArtinianRing.of_finite κ L
  haveI : IsLocalRing L := isLocalRing_of_isArtinianRing h1

  let ℓ := IsLocalRing.ResidueField L
  let res : L →ₐ[κ] ℓ := Ideal.Quotient.mkₐ κ (IsLocalRing.maximalIdeal L)
  have hres : Function.Surjective res := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker res = IsLocalRing.maximalIdeal L := Ideal.mk_ker
  have hnil : IsNilpotent (RingHom.ker res) := by
    rw [hker]
    have hle : IsLocalRing.maximalIdeal L ≤ nilradical L := fun x hx =>
      isNilpotent_of_mem_maximalIdeal h1 (by convert hx)
    obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical L
    refine ⟨n, le_bot_iff.mp ?_⟩
    calc IsLocalRing.maximalIdeal L ^ n ≤ nilradical L ^ n := Ideal.pow_right_mono hle n
      _ = ⊥ := by rw [hn, Ideal.zero_eq_bot]
  haveI : Module.Finite κ ℓ := Module.Finite.of_surjective res.toLinearMap hres

  haveI : IsPurelyInseparable κ ℓ := by
    refine ⟨Algebra.IsIntegral.of_finite κ ℓ, fun x hx => ?_⟩
    apply mem_range_of_isSeparable_of_trivialIdem κ ℓ x hx
    have hP := h2 (minpoly κ x) (minpoly.monic hx.isIntegral) (minpoly.irreducible hx.isIntegral)
    obtain ⟨hs, hk⟩ := ker_lTensor_nil κ L res hres hnil (AdjoinRoot (minpoly κ x))
    exact trivialIdem_of_surjective_of_ker_nil _ hs hk hP

  obtain ⟨hs, hk⟩ := ker_lTensor_nil κ L res hres hnil k
  exact trivialIdem_of_ker_nil _ hk (trivialIdem_tensor_of_isPurelyInseparable κ ℓ k)

end descent

section idem

variable (Y : Scheme.{u})

theorem nontrivial_sections_of_nonempty (U : Y.Opens) (hU : (U : Set Y).Nonempty) :
    Nontrivial Γ(Y, U) := by
  obtain ⟨x, hx⟩ := hU
  exact (Y.presheaf.germ U x hx).hom.domain_nontrivial

theorem trivialIdem_of_preconnectedSpace [PreconnectedSpace Y] : TrivialIdem Γ(Y, ⊤) := by
  intro e he

  have hdisj : Y.basicOpen e ⊓ Y.basicOpen (1 - e) = ⊥ := by
    rw [← Scheme.basicOpen_mul, he.mul_one_sub_self, Scheme.basicOpen_zero]
  have hcov : ∀ x : Y, x ∈ Y.basicOpen e ∨ x ∈ Y.basicOpen (1 - e) := by
    intro x
    rw [Scheme.mem_basicOpen_top, Scheme.mem_basicOpen_top]
    apply IsLocalRing.isUnit_or_isUnit_of_isUnit_add
    rw [← map_add, add_sub_cancel, map_one]
    exact isUnit_one
  have hcompl : ((Y.basicOpen e : Set Y))ᶜ = (Y.basicOpen (1 - e) : Set Y) := by
    ext x
    constructor
    · intro hx
      exact (hcov x).resolve_left hx
    · intro hx hx'
      have : x ∈ (Y.basicOpen e ⊓ Y.basicOpen (1 - e) : Y.Opens) := ⟨hx', hx⟩
      rw [hdisj] at this
      exact this
  have hclopen : IsClopen ((Y.basicOpen e : Set Y)) := by
    refine ⟨⟨?_⟩, (Y.basicOpen e).isOpen⟩
    rw [hcompl]; exact (Y.basicOpen (1 - e)).isOpen
  rcases isClopen_iff.mp hclopen with h0 | h1
  ·
    left
    have hunit : IsUnit (1 - e) := by
      apply RingedSpace.isUnit_of_isUnit_germ
      intro x hx
      have := hcov x
      rw [Scheme.mem_basicOpen_top, Scheme.mem_basicOpen_top] at this
      rcases this with h | h
      · exfalso
        have hx' : x ∈ (Y.basicOpen e : Set Y) := (Scheme.mem_basicOpen_top Y e x).mpr h
        rw [h0] at hx'; exact hx'
      · exact h
    obtain ⟨u, hu⟩ := hunit
    have h1e := he.one_sub
    have : (1 - e) = 1 := by
      calc (1 - e) = ((↑u⁻¹ : Γ(Y, ⊤)) * ↑u) * (1 - e) := by simp
        _ = ↑u⁻¹ * ((1 - e) * (1 - e)) := by rw [hu, mul_assoc]
        _ = ↑u⁻¹ * (1 - e) := by rw [h1e.eq]
        _ = 1 := by rw [← hu, Units.inv_mul]
    simpa using this
  · right
    have hunit : IsUnit e := by
      apply RingedSpace.isUnit_of_isUnit_germ
      intro x hx
      have hx' : x ∈ (Y.basicOpen e : Set Y) := by rw [h1]; trivial
      exact (Scheme.mem_basicOpen_top Y e x).mp hx'
    obtain ⟨u, hu⟩ := hunit
    calc e = ((↑u⁻¹ : Γ(Y, ⊤)) * ↑u) * e := by simp
      _ = ↑u⁻¹ * (e * e) := by rw [hu, mul_assoc]
      _ = ↑u⁻¹ * e := by rw [he.eq]
      _ = 1 := by rw [← hu, Units.inv_mul]

theorem preconnectedSpace_of_trivialIdem (h : TrivialIdem Γ(Y, ⊤)) : PreconnectedSpace Y := by
  classical
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  by_contra hcon
  push_neg at hcon
  obtain ⟨hne, hnu⟩ := hcon

  let U : ULift.{u} Bool → Y.Opens := fun b =>
    if b.down then ⟨s, hs.isOpen⟩ else ⟨sᶜ, hs.compl.isOpen⟩
  have hUt : U ⟨true⟩ = ⟨s, hs.isOpen⟩ := rfl
  have hUf : U ⟨false⟩ = ⟨sᶜ, hs.compl.isOpen⟩ := rfl
  have hcover : (⊤ : Y.Opens) ≤ iSup U := by
    intro x _
    rw [Opens.mem_iSup]
    by_cases hx : x ∈ s
    · exact ⟨⟨true⟩, hx⟩
    · exact ⟨⟨false⟩, hx⟩

  let sf : ∀ b, Γ(Y, U b) := fun b => if b.down then 1 else 0
  have hsf : TopCat.Presheaf.IsCompatible Y.presheaf U sf := by
    rintro ⟨i⟩ ⟨j⟩
    rcases i with _ | _ <;> rcases j with _ | _
    · simp [sf]
    · have : U ⟨false⟩ ⊓ U ⟨true⟩ = ⊥ := by
        rw [hUt, hUf]; ext x; simp
      have hsub : Subsingleton Γ(Y, U ⟨false⟩ ⊓ U ⟨true⟩) := by rw [this]; infer_instance
      exact Subsingleton.elim _ _
    · have : U ⟨true⟩ ⊓ U ⟨false⟩ = ⊥ := by
        rw [hUt, hUf]; ext x; simp
      have hsub : Subsingleton Γ(Y, U ⟨true⟩ ⊓ U ⟨false⟩) := by rw [this]; infer_instance
      exact Subsingleton.elim _ _
    · simp [sf]
  have hex : ∃ e : Γ(Y, ⊤), ∀ b, (Y.presheaf.map (homOfLE (le_top : U b ≤ ⊤)).op).hom e = sf b := by
    obtain ⟨e, hglue, -⟩ :=
      TopCat.Sheaf.existsUnique_gluing' Y.sheaf U ⊤ (fun b => homOfLE le_top) hcover sf hsf
    exact ⟨e, hglue⟩
  obtain ⟨e, hglue⟩ := hex

  have hidem : IsIdempotentElem e := by
    change e * e = e
    apply TopCat.Sheaf.eq_of_locally_eq' Y.sheaf U ⊤ (fun b => homOfLE le_top) hcover
    intro b
    have hb := hglue b
    change (Y.presheaf.map (homOfLE le_top).op).hom (e * e) = (Y.presheaf.map (homOfLE le_top).op).hom e
    rw [map_mul, hb]
    rcases b with ⟨_ | _⟩ <;> simp [sf]

  have hnt : Nontrivial Γ(Y, U ⟨true⟩) :=
    nontrivial_sections_of_nonempty Y _ (by rw [hUt]; exact hne)
  have hnf : Nontrivial Γ(Y, U ⟨false⟩) := by
    refine nontrivial_sections_of_nonempty Y _ ?_
    rw [hUf]
    exact Set.nonempty_compl.mpr hnu
  rcases h e hidem with h0 | h1
  · have hb := hglue ⟨true⟩
    rw [h0, map_zero] at hb
    simp only [sf] at hb
    exact zero_ne_one hb
  · have hb := hglue ⟨false⟩
    rw [h1, map_one] at hb
    simp only [sf] at hb
    exact one_ne_zero hb

theorem preconnectedSpace_of_iso {Y Y' : Scheme.{u}} (e : Y ≅ Y') [PreconnectedSpace Y] :
    PreconnectedSpace Y' := by
  refine ⟨?_⟩
  have h := (isPreconnected_univ (α := Y)).image e.hom.base e.hom.base.hom.continuous.continuousOn
  have hr : e.hom.base '' Set.univ = Set.univ :=
    Set.image_univ_of_surjective e.hom.homeomorph.surjective
  rwa [hr] at h

end idem

section fibre

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of A))

noncomputable abbrev bc (R : Type u) [CommRing R] (γ : A →+* R) : Scheme.{u} :=
  pullback πX (Spec.map (CommRingCat.ofHom γ))

noncomputable def bcCompIso (R S : Type u) [CommRing R] [CommRing S] (γ : A →+* R)
    (θ : R →+* S) :
    pullback (pullback.snd πX (Spec.map (CommRingCat.ofHom γ))) (Spec.map (CommRingCat.ofHom θ))
      ≅ bc πX S (θ.comp γ) :=
  pullbackLeftPullbackSndIso πX (Spec.map (CommRingCat.ofHom γ)) (Spec.map (CommRingCat.ofHom θ))
    ≪≫ pullback.congrHom rfl (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])

theorem preconnectedSpace_bc_of_surjective (B : Type u) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] (β : A →+* B) [IsProper (pullback.snd πX (Spec.map (CommRingCat.ofHom β)))]
    (hStein : Function.Bijective (pullback.snd πX (Spec.map (CommRingCat.ofHom β))).appTop)
    (E : Type u) [Field E] (θ : B →+* E) (hθ : Function.Surjective θ)
    (γ : A →+* E) (hγ : γ = θ.comp β) :
    PreconnectedSpace ↥(bc πX E γ) := by
  subst hγ
  set q := pullback.snd πX (Spec.map (CommRingCat.ofHom β)) with hq

  have hZ := AlgebraicGeometry.isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop
    q hStein

  set sθ := Spec.map (CommRingCat.ofHom θ) with hsθ
  haveI : IsClosedImmersion sθ := IsClosedImmersion.spec_of_surjective _ hθ
  have hker : RingHom.ker θ = IsLocalRing.maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective θ hθ)
  have hpt : ∀ y : PrimeSpectrum E, sθ y = IsLocalRing.closedPoint B := by
    intro y
    apply PrimeSpectrum.ext
    change Ideal.comap θ y.asIdeal = IsLocalRing.maximalIdeal B
    rw [Ideal.eq_bot_of_prime y.asIdeal, ← RingHom.ker_eq_comap_bot, hker]
  have hrange : Set.range sθ = {IsLocalRing.closedPoint B} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩; exact hpt y
    · rintro (rfl : x = _)
      exact ⟨⟨⊥, Ideal.isPrime_bot⟩, hpt _⟩

  have hrangeY : Set.range (pullback.fst q sθ) = q ⁻¹' {IsLocalRing.closedPoint B} := by
    rw [Scheme.Pullback.range_fst, hrange]
  have hemb : Topology.IsEmbedding (pullback.fst q sθ) :=
    (pullback.fst q sθ).isClosedEmbedding.isEmbedding
  haveI : PreconnectedSpace ↥(pullback q sθ) := by
    refine ⟨?_⟩
    rw [← hemb.isInducing.isPreconnected_image, Set.image_univ, hrangeY]
    exact hZ
  exact preconnectedSpace_of_iso (bcCompIso πX B E β θ)

theorem nonempty_ringEquiv_bc_tensor (κ : Type u) [Field κ] (ψ : A →+* κ)
    [IsProper (pullback.snd πX (Spec.map (CommRingCat.ofHom ψ)))]
    [Algebra κ Γ(bc πX κ ψ, ⊤)]
    (halg : algebraMap κ Γ(bc πX κ ψ, ⊤) = ((Scheme.ΓSpecIso (CommRingCat.of κ)).inv ≫
      (pullback.snd πX (Spec.map (CommRingCat.ofHom ψ))).appTop).hom)
    (F : Type u) [Field F] [Algebra κ F] (γ : A →+* F) (hγ : γ = (algebraMap κ F).comp ψ) :
    Nonempty (Γ(bc πX F γ, ⊤) ≃+* F ⊗[κ] Γ(bc πX κ ψ, ⊤)) := by
  subst hγ
  set fκ := pullback.snd πX (Spec.map (CommRingCat.ofHom ψ)) with hfκ
  haveI : CompactSpace ↥(bc πX κ ψ) := QuasiCompact.compactSpace_of_compactSpace fκ
  haveI : QuasiSeparatedSpace ↥(bc πX κ ψ) := quasiSeparatedSpace_of_quasiSeparated fκ
  have hP := AlgebraicGeometry.isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat fκ F
  set S' : CommRingCat.{u} := Γ(pullback fκ (Spec.map (CommRingCat.ofHom (algebraMap κ F))), ⊤)
    with hS'def
  set inl : CommRingCat.of F ⟶ S' := (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
      (pullback.snd fκ (Spec.map (CommRingCat.ofHom (algebraMap κ F)))).appTop with hinl
  set inr : Γ(bc πX κ ψ, ⊤) ⟶ S' :=
    (pullback.fst fκ (Spec.map (CommRingCat.ofHom (algebraMap κ F)))).appTop with hinr
  set g : CommRingCat.of κ ⟶ Γ(bc πX κ ψ, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of κ)).inv ≫ fκ.appTop with hg
  letI algFS : Algebra F S' := inl.hom.toAlgebra
  letI algLS : Algebra Γ(bc πX κ ψ, ⊤) S' := inr.hom.toAlgebra
  letI algκS : Algebra κ S' := (inr.hom.comp (algebraMap κ Γ(bc πX κ ψ, ⊤))).toAlgebra
  haveI : IsScalarTower κ Γ(bc πX κ ψ, ⊤) S' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hgalg : g.hom = algebraMap κ Γ(bc πX κ ψ, ⊤) := halg.symm
  have hsq : ∀ x : κ, inl.hom (algebraMap κ F x) = inr.hom (algebraMap κ Γ(bc πX κ ψ, ⊤) x) :=
    fun x => by
    have := congrArg (fun φ : CommRingCat.of κ ⟶ S' => φ.hom x) hP.w
    simpa [CommRingCat.hom_comp, hgalg] using this
  haveI : IsScalarTower κ F S' := IsScalarTower.of_algebraMap_eq (fun x => (hsq x).symm)
  have hP' : IsPushout (CommRingCat.ofHom (algebraMap κ F))
      (CommRingCat.ofHom (algebraMap κ Γ(bc πX κ ψ, ⊤)))
      (CommRingCat.ofHom (algebraMap F S')) (CommRingCat.ofHom (algebraMap Γ(bc πX κ ψ, ⊤) S')) := by
    refine hP.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) ?_
      (by simp; rfl) (by simp; rfl)
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    ext x
    change g.hom x = algebraMap κ Γ(bc πX κ ψ, ⊤) x
    rw [hgalg]
  have hAP : Algebra.IsPushout κ F Γ(bc πX κ ψ, ⊤) S' := CommRingCat.isPushout_iff_isPushout.mp hP'
  let e1 : F ⊗[κ] Γ(bc πX κ ψ, ⊤) ≃ₐ[F] S' := Algebra.IsPushout.equiv κ F Γ(bc πX κ ψ, ⊤) S'

  let e2 := bcCompIso πX κ F ψ (algebraMap κ F)
  let r2 : Γ(bc πX F ((algebraMap κ F).comp ψ), ⊤) ≃+* S' :=
    (Scheme.Γ.mapIso e2.op).commRingCatIsoToRingEquiv
  exact ⟨r2.trans e1.symm.toRingEquiv⟩

theorem bijective_appTop_snd_of_flat [CompactSpace X] [QuasiSeparatedSpace X]
    (hΓ : Function.Bijective πX.appTop)
    (R : Type u) [CommRing R] [Algebra A R] [Module.Flat A R] :
    Function.Bijective (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap A R)))).appTop := by
  have hP := AlgebraicGeometry.isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat πX R
  haveI : IsIso πX.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hΓ
  haveI : IsIso ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ πX.appTop) := IsIso.comp_isIso
  haveI := hP.isIso_inl_of_isIso
  haveI : IsIso (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap A R)))).appTop :=
    IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of R)).inv _
  exact ConcreteCategory.bijective_of_isIso _

end fibre

section thickening

theorem isLocalRing_adjoinRoot (R : Type u) [CommRing R] [IsLocalRing R] (P : R[X]) (hP : P.Monic)
    (hirr : Irreducible (P.map (IsLocalRing.residue R))) : IsLocalRing (AdjoinRoot P) := by
  classical
  haveI : Fact (Irreducible (P.map (IsLocalRing.residue R))) := ⟨hirr⟩
  let B := AdjoinRoot P

  let 𝔪 : Ideal B := (IsLocalRing.maximalIdeal R).map (AdjoinRoot.of P)
  have h𝔪 : 𝔪.IsMaximal := by
    apply Ideal.Quotient.maximal_of_isField
    have e := AdjoinRoot.quotEquivQuotMap P (IsLocalRing.maximalIdeal R)
    exact MulEquiv.isField (Field.toIsField (AdjoinRoot (P.map (IsLocalRing.residue R))))
      e.toMulEquiv
  haveI : Module.Finite R B := (AdjoinRoot.powerBasis' hP).finite
  haveI : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  refine IsLocalRing.of_unique_max_ideal ⟨𝔪, h𝔪, fun 𝔫 h𝔫 => ?_⟩
  have h1 : (𝔫.comap (algebraMap R B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔫
  have h2 : 𝔫.comap (algebraMap R B) = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal h1
  have h3 : 𝔪 ≤ 𝔫 := by
    change (IsLocalRing.maximalIdeal R).map (AdjoinRoot.of P) ≤ 𝔫
    rw [← h2, ← AdjoinRoot.algebraMap_eq]
    exact Ideal.map_comap_le
  exact (h𝔪.eq_of_le h𝔫.ne_top h3).symm

end thickening

section main

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of A))

theorem preconnectedSpace_bc_of_isAlgClosed [IsNoetherianRing A] [IsProper πX]
    (hΓ : Function.Bijective πX.appTop) (k : Type u) [Field k] [IsAlgClosed k] (φ : A →+* k) :
    PreconnectedSpace ↥(bc πX k φ) := by
  classical

  set 𝔭 : Ideal A := RingHom.ker φ with h𝔭
  haveI h𝔭p : 𝔭.IsPrime := RingHom.ker_isPrime φ
  let R := Localization.AtPrime 𝔭
  let κ := IsLocalRing.ResidueField R
  let ψ : A →+* κ := (IsLocalRing.residue R).comp (algebraMap A R)
  have hunit : ∀ s : 𝔭.primeCompl, IsUnit (φ s) := fun s =>
    isUnit_iff_ne_zero.mpr (fun h0 => s.2 (by simpa [h𝔭, RingHom.mem_ker] using h0))
  let φR : R →+* k := IsLocalization.lift (M := 𝔭.primeCompl) hunit
  have hφR : ∀ a : A, φR (algebraMap A R a) = φ a := fun a => IsLocalization.lift_eq hunit a
  have hle : IsLocalRing.maximalIdeal R ≤ RingHom.ker φR := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, hφR]
    exact ha
  let ι : κ →+* k := Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) φR (fun x hx => hle hx)
  have hφ : φ = ι.comp ψ := by
    ext a
    change φ a = Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) φR (fun x hx => hle hx)
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (algebraMap A R a))
    rw [Ideal.Quotient.lift_mk, hφR]
  letI algκk : Algebra κ k := ι.toAlgebra

  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace πX
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated πX
  haveI : Module.Flat A R := IsLocalization.flat R 𝔭.primeCompl

  set fκ := pullback.snd πX (Spec.map (CommRingCat.ofHom ψ)) with hfκ
  set inlκ : CommRingCat.of κ ⟶ Γ(bc πX κ ψ, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of κ)).inv ≫ fκ.appTop with hinlκ
  letI algκL : Algebra κ Γ(bc πX κ ψ, ⊤) := inlκ.hom.toAlgebra
  have halg : algebraMap κ Γ(bc πX κ ψ, ⊤) = inlκ.hom := rfl
  haveI : Module.Finite κ Γ(bc πX κ ψ, ⊤) := by
    have h1 : fκ.appTop.hom.Finite :=
      AlgebraicGeometry.finite_appTop_of_isProper_of_isNoetherianRing fκ
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    have h3 : inlκ.hom.Finite := by
      have := RingHom.Finite.comp h1 h2
      simpa [hinlκ, CommRingCat.hom_comp] using this
    rw [RingHom.Finite] at h3
    convert h3

  have hSteinR := bijective_appTop_snd_of_flat πX hΓ R
  have h1 : TrivialIdem Γ(bc πX κ ψ, ⊤) := by
    haveI := preconnectedSpace_bc_of_surjective πX R (algebraMap A R) hSteinR κ
      (IsLocalRing.residue R) (Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal R)) ψ rfl
    exact trivialIdem_of_preconnectedSpace _

  have h2 : ∀ P : κ[X], P.Monic → Irreducible P →
      TrivialIdem (AdjoinRoot P ⊗[κ] Γ(bc πX κ ψ, ⊤)) := by
    intro P₀ hmon₀ hirr₀

    have hlifts : P₀ ∈ Polynomial.lifts (IsLocalRing.residue R) := by
      obtain ⟨Q, hQ⟩ := Polynomial.map_surjective (IsLocalRing.residue R)
        (Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal R)) P₀
      exact (Polynomial.mem_lifts _).mpr ⟨Q, hQ⟩
    obtain ⟨P, hPmap, -, hPmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hmon₀
    subst hPmap
    haveI hfact : Fact (Irreducible (P.map (IsLocalRing.residue R))) := ⟨hirr₀⟩

    let B := AdjoinRoot P
    haveI : IsLocalRing B := isLocalRing_adjoinRoot R P hPmon hirr₀
    haveI : Module.Free R B := Module.Free.of_basis (AdjoinRoot.powerBasis' hPmon).basis
    haveI : Module.Flat A B := Module.Flat.trans A R B
    have hSteinB := bijective_appTop_snd_of_flat πX hΓ B

    let E := AdjoinRoot (P.map (IsLocalRing.residue R))
    have hroot : Polynomial.eval₂ ((AdjoinRoot.of (P.map (IsLocalRing.residue R))).comp
        (IsLocalRing.residue R)) (AdjoinRoot.root (P.map (IsLocalRing.residue R))) P = 0 := by
      rw [← Polynomial.eval₂_map, AdjoinRoot.eval₂_root]
    let θ : B →+* E := AdjoinRoot.lift ((AdjoinRoot.of _).comp (IsLocalRing.residue R))
      (AdjoinRoot.root _) hroot
    have hθ : Function.Surjective θ := by
      intro y
      obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective y
      obtain ⟨Q, rfl⟩ := Polynomial.map_surjective (IsLocalRing.residue R)
        (Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal R)) g
      refine ⟨AdjoinRoot.mk P Q, ?_⟩
      change AdjoinRoot.lift _ _ hroot (AdjoinRoot.mk P Q) = _
      rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq,
        ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]
    have hγ : θ.comp (algebraMap A B) = (algebraMap κ E).comp ψ := by
      ext a
      change AdjoinRoot.lift _ _ hroot (algebraMap A B a) = AdjoinRoot.of _ (IsLocalRing.residue R _)
      rw [IsScalarTower.algebraMap_apply A R B, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
      rfl
    haveI := preconnectedSpace_bc_of_surjective πX B (algebraMap A B) hSteinB E θ hθ
      ((algebraMap κ E).comp ψ) hγ.symm
    have hE : TrivialIdem Γ(bc πX E ((algebraMap κ E).comp ψ), ⊤) :=
      trivialIdem_of_preconnectedSpace _
    obtain ⟨r⟩ := nonempty_ringEquiv_bc_tensor πX κ ψ halg E ((algebraMap κ E).comp ψ) rfl
    exact trivialIdem_of_ringEquiv r hE

  have hk : TrivialIdem (k ⊗[κ] Γ(bc πX κ ψ, ⊤)) := trivialIdem_baseChange κ _ h1 h2 k
  obtain ⟨r⟩ := nonempty_ringEquiv_bc_tensor πX κ ψ halg k ((algebraMap κ k).comp ψ) rfl
  have hk' : TrivialIdem Γ(bc πX k ((algebraMap κ k).comp ψ), ⊤) := trivialIdem_of_ringEquiv r.symm hk
  haveI := preconnectedSpace_of_trivialIdem _ hk'
  have hmap : Spec.map (CommRingCat.ofHom ((algebraMap κ k).comp ψ)) = Spec.map (CommRingCat.ofHom φ) := by
    rw [hφ]
  exact preconnectedSpace_of_iso (pullback.congrHom (rfl : πX = πX) hmap)

end main

section corollaries

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of A))

theorem exists_factor_residueField {K : Type u} [Field K] (φ : A →+* K)
    [(RingHom.ker φ).IsPrime] :
    ∃ ι : IsLocalRing.ResidueField (Localization.AtPrime (RingHom.ker φ)) →+* K,
      φ = ι.comp ((IsLocalRing.residue _).comp (algebraMap A _)) := by
  set 𝔭 : Ideal A := RingHom.ker φ with h𝔭
  let R := Localization.AtPrime 𝔭
  have hunit : ∀ s : 𝔭.primeCompl, IsUnit (φ s) := fun s =>
    isUnit_iff_ne_zero.mpr (fun h0 => s.2 (by simpa [h𝔭, RingHom.mem_ker] using h0))
  let φR : R →+* K := IsLocalization.lift (M := 𝔭.primeCompl) hunit
  have hφR : ∀ a : A, φR (algebraMap A R a) = φ a := fun a => IsLocalization.lift_eq hunit a
  have hle : IsLocalRing.maximalIdeal R ≤ RingHom.ker φR := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, hφR]
    exact ha
  refine ⟨Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) φR (fun x hx => hle hx), ?_⟩
  ext a
  change φ a = Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) φR (fun x hx => hle hx)
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (algebraMap A R a))
  rw [Ideal.Quotient.lift_mk, hφR]

theorem surjective_fst_bc_field (K K' : Type u) [Field K] [Field K'] (φ : A →+* K)
    (j : K →+* K') :
    Function.Surjective (pullback.fst (pullback.snd πX (Spec.map (CommRingCat.ofHom φ)))
      (Spec.map (CommRingCat.ofHom j))) := by
  intro x
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.snd πX (Spec.map (CommRingCat.ofHom φ))) (g := Spec.map (CommRingCat.ofHom j))
    x default (Subsingleton.elim _ _)
  exact ⟨z, hz⟩

theorem preconnectedSpace_bc [IsNoetherianRing A] [IsProper πX]
    (hΓ : Function.Bijective πX.appTop) (K : Type u) [Field K] (φ : A →+* K) :
    PreconnectedSpace ↥(bc πX K φ) := by
  let Kb := AlgebraicClosure K
  haveI := preconnectedSpace_bc_of_isAlgClosed πX hΓ Kb ((algebraMap K Kb).comp φ)
  haveI : PreconnectedSpace ↥(pullback (pullback.snd πX (Spec.map (CommRingCat.ofHom φ)))
      (Spec.map (CommRingCat.ofHom (algebraMap K Kb)))) :=
    preconnectedSpace_of_iso (bcCompIso πX K Kb φ (algebraMap K Kb)).symm
  have hsurj := surjective_fst_bc_field πX K Kb φ (algebraMap K Kb)
  refine ⟨?_⟩
  have h := (isPreconnected_univ (α := ↥(pullback (pullback.snd πX
      (Spec.map (CommRingCat.ofHom φ))) (Spec.map (CommRingCat.ofHom (algebraMap K Kb)))))).image _
    (pullback.fst (pullback.snd πX (Spec.map (CommRingCat.ofHom φ)))
      (Spec.map (CommRingCat.ofHom (algebraMap K Kb)))).base.hom.continuous.continuousOn
  rwa [Set.image_univ_of_surjective hsurj] at h

theorem nonempty_bc [IsNoetherianRing A] [IsProper πX]
    (hΓ : Function.Bijective πX.appTop) (K : Type u) [Field K] (φ : A →+* K) :
    Nonempty ↥(bc πX K φ) := by
  classical
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨ι, hφ⟩ := exists_factor_residueField φ
  let R := Localization.AtPrime (RingHom.ker φ)
  let κ := IsLocalRing.ResidueField R
  let ψ : A →+* κ := (IsLocalRing.residue R).comp (algebraMap A R)
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace πX
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated πX
  haveI : Module.Flat A R := IsLocalization.flat R (RingHom.ker φ).primeCompl

  set q := pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap A R))) with hq
  have hStein := bijective_appTop_snd_of_flat πX hΓ R
  have hne : Nonempty ↥(bc πX R (algebraMap A R)) := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have htop : (⊤ : (bc πX R (algebraMap A R)).Opens) = ⊥ := by
      ext x; exact (IsEmpty.false x).elim
    have hsub : Subsingleton Γ(bc πX R (algebraMap A R), ⊤) := by rw [htop]; infer_instance
    have h01 : q.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv 0) =
        q.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv 1) := Subsingleton.elim _ _
    have := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1
      (hStein.1 h01)
    exact zero_ne_one this

  obtain ⟨x0⟩ := hne
  have hclosed : IsClosed (Set.range q) := q.isClosedMap.isClosed_range
  have hmem : IsLocalRing.closedPoint R ∈ Set.range q := by
    by_contra hnot
    let U : Opens ↥(Spec (CommRingCat.of R)) := ⟨(Set.range q)ᶜ, hclosed.isOpen_compl⟩
    have hU : IsLocalRing.closedPoint R ∈ U := hnot
    have hUtop := (IsLocalRing.closedPoint_mem_iff U).mp hU
    have : q x0 ∈ (U : Set _) := by rw [hUtop]; trivial
    exact this ⟨x0, rfl⟩
  obtain ⟨x, hx⟩ := hmem

  have hpt : ∀ y : PrimeSpectrum κ, Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) y =
      IsLocalRing.closedPoint R := by
    intro y
    apply PrimeSpectrum.ext
    change Ideal.comap (IsLocalRing.residue R) y.asIdeal = IsLocalRing.maximalIdeal R
    rw [Ideal.eq_bot_of_prime y.asIdeal, ← RingHom.ker_eq_comap_bot]
    exact Ideal.mk_ker
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q)
    (g := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) x default
    (by rw [hx, hpt])
  have hz : Nonempty ↥(bc πX κ ψ) := ⟨(bcCompIso πX R κ (algebraMap A R) (IsLocalRing.residue R)).hom z⟩

  obtain ⟨w⟩ := hz
  obtain ⟨v, -⟩ := surjective_fst_bc_field πX κ K ψ ι w
  have hv : Nonempty ↥(bc πX K (ι.comp ψ)) := ⟨(bcCompIso πX κ K ψ ι).hom v⟩
  have hmap : Spec.map (CommRingCat.ofHom (ι.comp ψ)) = Spec.map (CommRingCat.ofHom φ) :=
    congrArg (fun f : A →+* K => Spec.map (CommRingCat.ofHom f)) hφ.symm
  obtain ⟨t⟩ := hv
  exact ⟨(pullback.congrHom (rfl : πX = πX) hmap).hom t⟩

theorem connectedSpace_bc [IsNoetherianRing A] [IsProper πX]
    (hΓ : Function.Bijective πX.appTop) (K : Type u) [Field K] (φ : A →+* K) :
    ConnectedSpace ↥(bc πX K φ) :=
  haveI := preconnectedSpace_bc πX hΓ K φ
  ⟨nonempty_bc πX hΓ K φ⟩

theorem geometricallyConnected [IsNoetherianRing A] [IsProper πX]
    (hΓ : Function.Bijective πX.appTop) : GeometricallyConnected πX := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  haveI := connectedSpace_bc πX hΓ K φ.hom
  have e : Z ≅ bc πX K φ.hom := h.isoPullback ≪≫ pullback.congrHom rfl (by simp)
  haveI := preconnectedSpace_of_iso e.symm
  exact ⟨⟨e.inv (Classical.arbitrary _)⟩⟩

end corollaries

end P2mKcGeomConnFibres

open CategoryTheory AlgebraicGeometry

universe u

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (hf : Function.Bijective f.appTop) :
    GeometricallyConnected f :=
  P2mKcGeomConnFibres.geometricallyConnected f hf

end S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop
end P2MW
export P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop (solution)
