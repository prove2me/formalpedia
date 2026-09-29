-- Prove2me | solution 1 for AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_completeOrthogonalIdempotents_forall_act_schrodingerFrame_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/e19a1fc5-ca5c-5ce7-8aaf-013d38563e90

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_mul_act
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_one_act
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_act_add_and_act_baseScalar_smul
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_units_forall_thetaPt_act_act_eq_smul_act_act
import Theorems.Thm_AlgebraicGeometry_ThetaLevel_exists_completeOrthogonalIdempotents_smul_eq_smul_schrodMat_of_forall_mul_schrodMat_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_completeOrthogonalIdempotents_forall_act_schrodingerFrame_eq
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

namespace K78C9

section Dict

variable {S O V : Type*} [CommRing S] [CommRing O] [AddCommGroup V] [Module O V]
  (bs : S →+* O) {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ι → V)

def Φ (c : ι → S) : V := ∑ i, bs (c i) • σ i

omit [DecidableEq ι] in
theorem Φ_add (a b : ι → S) : Φ bs σ (a + b) = Φ bs σ a + Φ bs σ b := by
  simp only [Φ, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]

omit [DecidableEq ι] in
theorem Φ_smul (r : S) (a : ι → S) : Φ bs σ (r • a) = bs r • Φ bs σ a := by
  simp only [Φ, Pi.smul_apply, smul_eq_mul, map_mul, Finset.smul_sum, smul_smul]

theorem Φ_single (x : ι) (r : S) : Φ bs σ (fun y => if y = x then r else 0) = bs r • σ x := by
  simp only [Φ]
  rw [Finset.sum_eq_single x (fun y _ hy => by simp [hy]) (fun h => absurd (Finset.mem_univ x) h)]
  simp

omit [DecidableEq ι] in

theorem map_Φ (U : V → V) (hUa : ∀ v w, U (v + w) = U v + U w) (hUs : ∀ (r : S) (v : V), U (bs r • v) = bs r • U v)
    (T : Matrix ι ι S) (hT : ∀ x, U (σ x) = Φ bs σ (fun y => T y x)) (c : ι → S) :
    U (Φ bs σ c) = Φ bs σ (T.mulVec c) := by
  have hU0 : U 0 = 0 := by
    have h := hUa 0 0
    rw [add_zero] at h
    simpa using h
  let Uh : V →+ V := { toFun := U, map_zero' := hU0, map_add' := hUa }
  have hUsum : U (∑ i, bs (c i) • σ i) = ∑ i, U (bs (c i) • σ i) := map_sum Uh _ _
  simp only [Φ]
  rw [hUsum]
  simp_rw [hUs, hT, Φ, Finset.smul_sum, smul_smul, ← map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_smul, ← map_sum]
  congr 2
  simp only [Matrix.mulVec, dotProduct, mul_comm]

omit [Fintype ι] [DecidableEq ι] in

theorem map_lincomb (U : V → V) (hUa : ∀ v w, U (v + w) = U v + U w) (hUs : ∀ (r : S) (v : V), U (bs r • v) = bs r • U v)
    {κ : Type*} (s : Finset κ) (a : κ → S) (v : κ → V) :
    U (∑ i ∈ s, bs (a i) • v i) = ∑ i ∈ s, bs (a i) • U (v i) := by
  have hU0 : U 0 = 0 := by
    have h := hUa 0 0
    rw [add_zero] at h
    simpa using h
  let Uh : V →+ V := { toFun := U, map_zero' := hU0, map_add' := hUa }
  have : U (∑ i ∈ s, bs (a i) • v i) = ∑ i ∈ s, U (bs (a i) • v i) := map_sum Uh _ _
  rw [this]
  exact Finset.sum_congr rfl fun i _ => hUs _ _

variable (hσ : Function.Bijective (Φ bs σ))

noncomputable def mat (U : V → V) : Matrix ι ι S := fun y x => (hσ.2 (U (σ x))).choose y

omit [DecidableEq ι] in
theorem Φ_mat (U : V → V) (x : ι) : Φ bs σ (fun y => mat bs σ hσ U y x) = U (σ x) :=
  (hσ.2 (U (σ x))).choose_spec

omit [DecidableEq ι] in
theorem sum_mat_smul (U : V → V) (x : ι) : ∑ y, bs (mat bs σ hσ U y x) • σ y = U (σ x) := Φ_mat bs σ hσ U x

omit [DecidableEq ι] in
theorem mat_comp (U U' : V → V) (hUa : ∀ v w, U (v + w) = U v + U w) (hUs : ∀ (r : S) (v : V), U (bs r • v) = bs r • U v) :
    mat bs σ hσ (U ∘ U') = mat bs σ hσ U * mat bs σ hσ U' := by
  funext y x
  have h1 : Φ bs σ (fun y => mat bs σ hσ (U ∘ U') y x) = U (U' (σ x)) := Φ_mat bs σ hσ (U ∘ U') x
  have h2 : U (U' (σ x)) = Φ bs σ ((mat bs σ hσ U).mulVec fun z => mat bs σ hσ U' z x) := by
    rw [← Φ_mat bs σ hσ U' x]
    exact map_Φ bs σ U hUa hUs (mat bs σ hσ U) (fun z => (Φ_mat bs σ hσ U z).symm) _
  have := congrFun (hσ.1 (h1.trans h2)) y
  rw [this]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem mat_id : mat bs σ hσ id = 1 := by
  funext y x
  have h1 : Φ bs σ (fun y => mat bs σ hσ id y x) = σ x := Φ_mat bs σ hσ id x
  have h2 : Φ bs σ (fun y => (1 : Matrix ι ι S) y x) = σ x := by
    simp only [Matrix.one_apply]
    rw [Φ_single, map_one, one_smul]
  exact congrFun (hσ.1 (h1.trans h2.symm)) y

omit [DecidableEq ι] in

theorem mat_eq_of_cols (U : V → V) (M : Matrix ι ι S) (h : ∀ x, Φ bs σ (fun y => M y x) = U (σ x)) :
    mat bs σ hσ U = M := by
  funext y x
  exact congrFun (hσ.1 ((Φ_mat bs σ hσ U x).trans (h x).symm)) y

omit [DecidableEq ι] in

theorem mat_smul (U : V → V) (c : S) : mat bs σ hσ (fun v => bs c • U v) = c • mat bs σ hσ U := by
  funext y x
  have h1 := Φ_mat bs σ hσ (fun v => bs c • U v) x
  have h2 : Φ bs σ (fun y => (c • mat bs σ hσ U) y x) = bs c • U (σ x) := by
    rw [← Φ_mat bs σ hσ U x, ← Φ_smul]
    rfl
  exact congrFun (hσ.1 (h1.trans h2.symm)) y

omit hσ [DecidableEq ι] in

theorem Φ_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (c : κ → S) :
    Φ bs (σ ∘ e) c = Φ bs σ (fun x => c (e.symm x)) := by
  simp only [Φ, Function.comp_apply]
  exact Fintype.sum_equiv e _ _ (fun i => by simp)

omit hσ [DecidableEq ι] in
theorem bijective_Φ_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (hσ : Function.Bijective (Φ bs σ)) :
    Function.Bijective (Φ bs (σ ∘ e)) := by
  have : Φ bs (σ ∘ e) = Φ bs σ ∘ (fun c : κ → S => fun x => c (e.symm x)) := funext fun c => Φ_comp_equiv bs σ e c
  rw [this]
  exact hσ.comp (Equiv.piCongrLeft' (fun _ => S) e).bijective

end Dict

end K78C9

open K78C9 _root_.AlgebraicGeometry.ThetaLevel in
theorem solution
    (g N n : ℕ) (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = N + 1)
    (S : Type) [CommRing S] (hd : IsUnit ((N + 1 : ℕ) : S))
    (ζ : S) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : S) (hω : ω ^ 2 = ζ)
    (X : FramedPolarisedAbelianScheme g N n S)
    (F : SchrodingerFrame X.f X.L X.pol (𝟙 (Spec (CommRingCat.of S))) δ)
    (θ : ThetaPt X.f X.L X.pol (𝟙 (Spec (CommRingCat.of S)))) :
    ∃ (ε : ((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)) → S) (u : Sˣ),
      CompleteOrthogonalIdempotents ε ∧
      ∀ (c : ((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) (x : ((i : Fin g) → ZMod (δ i))),
        baseScalar X.f (𝟙 (Spec (CommRingCat.of S))) (ε c) • θ.act (F.σ x) =
          baseScalar X.f (𝟙 (Spec (CommRingCat.of S))) (ε c * u * ThetaLevel.thetaChar δ (N + 1) S ω c.2 x) •
            F.σ (x + c.1) := by
  classical
  have hω2 : ω ^ (2 * (N + 1)) = 1 := by rw [pow_mul, hω, hζ]
  let bs : S →+* Γ(pullback X.f (𝟙 (Spec (CommRingCat.of S))), ⊤) := baseScalarHom X.f (𝟙 (Spec (CommRingCat.of S)))
  have hbs : ∀ r : S, bs r = baseScalar X.f (𝟙 (Spec (CommRingCat.of S))) r := fun _ => rfl

  have lin : ∀ θ' : ThetaPt X.f X.L X.pol (𝟙 (Spec (CommRingCat.of S))),
      (∀ v w, θ'.act (v + w) = θ'.act v + θ'.act w) ∧ (∀ (r : S) v, θ'.act (bs r • v) = bs r • θ'.act v) :=
    fun θ' => ThetaPt.act_add_and_act_baseScalar_smul X.f X.L X.pol (𝟙 (Spec (CommRingCat.of S))) θ'

  let e : Fin (Fintype.card (HH δ)) ≃ HH δ := (Fintype.equivFin (HH δ)).symm
  have hσ : Function.Bijective (Φ bs (F.σ ∘ e)) := bijective_Φ_comp_equiv bs F.σ e F.basis

  set T : Matrix (Fin (Fintype.card (HH δ))) (Fin (Fintype.card (HH δ))) S := mat bs (F.σ ∘ e) hσ θ.act with hTdef
  have hT : ∀ j, θ.act (F.σ (e j)) = ∑ i, bs (T i j) • F.σ (e i) := fun j => (sum_mat_smul bs (F.σ ∘ e) hσ θ.act j).symm

  have hTunit : IsUnit T := by
    have hc1 : (θ.act ∘ θ⁻¹.act) = id := by
      funext s; show θ.act (θ⁻¹.act s) = s; rw [← ThetaPt.mul_act, mul_inv_cancel, ThetaPt.one_act]
    have hc2 : (θ⁻¹.act ∘ θ.act) = id := by
      funext s; show θ⁻¹.act (θ.act s) = s; rw [← ThetaPt.mul_act, inv_mul_cancel, ThetaPt.one_act]
    have h1 : T * mat bs (F.σ ∘ e) hσ θ⁻¹.act = 1 := by
      rw [hTdef, ← mat_comp bs (F.σ ∘ e) hσ _ _ (lin θ).1 (lin θ).2, hc1, mat_id]
    have h2 : mat bs (F.σ ∘ e) hσ θ⁻¹.act * T = 1 := by
      rw [hTdef, ← mat_comp bs (F.σ ∘ e) hσ _ _ (lin θ⁻¹).1 (lin θ⁻¹).2, hc2, mat_id]
    exact ⟨⟨T, _, h1, h2⟩, rfl⟩

  let χ : HH δ → AddChar (HH δ) S := fun k =>
    { toFun := thetaChar δ (N + 1) S ω k
      map_zero_eq_one' := by simp only [thetaChar, pair_zero_right, omegaPow_zero]
      map_add_eq_mul' := fun a b => by simp only [thetaChar, pair_add_right, omegaPow_add (N + 1) S ω hω2] }
  have hχ : ∀ k y, χ k y = thetaChar δ (N + 1) S ω k y := fun _ _ => rfl

  have hMθ : ∀ h' : HH δ, schrodMat δ (N + 1) S ω e (Heis.theta h') = mat bs (F.σ ∘ e) hσ (F.lift h').act := by
    intro h'
    refine (mat_eq_of_cols bs (F.σ ∘ e) hσ _ _ fun j => ?_).symm
    rw [Function.comp_apply, F.lift_act]
    simp only [Φ, schrodMat_apply, Heis.theta_h, Heis.theta_a, Heis.theta_k, pair_zero_left, add_zero, omegaPow_zero,
      Function.comp_apply]
    rw [Finset.sum_eq_single (e.symm (e j + h')) (fun i _ hi => by
      rw [if_neg (fun h => hi (by rw [← h, Equiv.symm_apply_apply])), map_zero, zero_smul])
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [if_pos (by rw [Equiv.apply_symm_apply]), map_one, one_smul, Equiv.apply_symm_apply]
    exact congrArg F.σ (add_comm _ _)
  have hMη : ∀ k' : HH δ, schrodMat δ (N + 1) S ω e (Heis.eta k') = mat bs (F.σ ∘ e) hσ (F.dualLift (χ k')).act := by
    intro k'
    refine (mat_eq_of_cols bs (F.σ ∘ e) hσ _ _ fun j => ?_).symm
    rw [Function.comp_apply, F.dualLift_act, hχ, ← hbs]
    simp only [Φ, schrodMat_apply, Heis.eta_h, Heis.eta_a, Heis.eta_k, add_zero, zero_add, Function.comp_apply]
    rw [Finset.sum_eq_single j (fun i _ hi => by
      rw [if_neg (fun h => hi (e.injective h)), map_zero, zero_smul]) (fun h => absurd (Finset.mem_univ _) h)]
    rw [if_pos rfl]
    rfl

  have hcomθ : ∀ h' : HH δ, ∃ c : S, (θ.act ∘ (F.lift h').act) = fun s => bs c • ((F.lift h').act ∘ θ.act) s := by
    intro h'
    obtain ⟨c, hc⟩ := AlgebraicGeometry.PolarisedAbelianScheme.exists_units_forall_thetaPt_act_act_eq_smul_act_act
      X.toPolarisedAbelianScheme (𝟙 (Spec (CommRingCat.of S))) θ (F.lift h')
    exact ⟨c, funext hc⟩
  have hcomη : ∀ k' : HH δ, ∃ c : S,
      (θ.act ∘ (F.dualLift (χ k')).act) = fun s => bs c • ((F.dualLift (χ k')).act ∘ θ.act) s := by
    intro k'
    obtain ⟨c, hc⟩ := AlgebraicGeometry.PolarisedAbelianScheme.exists_units_forall_thetaPt_act_act_eq_smul_act_act
      X.toPolarisedAbelianScheme (𝟙 (Spec (CommRingCat.of S))) θ (F.dualLift (χ k'))
    exact ⟨c, funext hc⟩
  choose lam hlam using hcomθ
  choose mu hmu using hcomη
  have hθ : ∀ h' : HH δ, T * schrodMat δ (N + 1) S ω e (Heis.theta h') =
      lam h' • (schrodMat δ (N + 1) S ω e (Heis.theta h') * T) := by
    intro h'
    rw [hMθ, hTdef, ← mat_comp bs (F.σ ∘ e) hσ _ _ (lin θ).1 (lin θ).2,
      ← mat_comp bs (F.σ ∘ e) hσ _ _ (lin (F.lift h')).1 (lin (F.lift h')).2, hlam, mat_smul]
  have hη : ∀ k' : HH δ, T * schrodMat δ (N + 1) S ω e (Heis.eta k') =
      mu k' • (schrodMat δ (N + 1) S ω e (Heis.eta k') * T) := by
    intro k'
    rw [hMη, hTdef, ← mat_comp bs (F.σ ∘ e) hσ _ _ (lin θ).1 (lin θ).2,
      ← mat_comp bs (F.σ ∘ e) hσ _ _ (lin (F.dualLift (χ k'))).1 (lin (F.dualLift (χ k'))).2, hmu, mat_smul]

  obtain ⟨ε, u, hε, hnorm⟩ :=
    AlgebraicGeometry.ThetaLevel.exists_completeOrthogonalIdempotents_smul_eq_smul_schrodMat_of_forall_mul_schrodMat_eq_smul
      δ (N + 1) hδd S hd ζ ω hζ hζu hω e T hTunit lam mu hθ hη
  refine ⟨ε, u, hε, fun c x => ?_⟩

  have col : ∀ i, ε c * T i (e.symm x) =
      ε c * u * (if e i = x + c.1 then omegaPow (N + 1) S ω (pair δ (N + 1) c.2 x) else 0) := fun i => by
    have := congrFun (congrFun (hnorm c) i) (e.symm x)
    rw [Matrix.smul_apply, Matrix.smul_apply, schrodMat_apply, Equiv.apply_symm_apply, zero_add, smul_eq_mul,
      smul_eq_mul] at this
    exact this
  conv_lhs => rw [← e.apply_symm_apply x, hT (e.symm x), Finset.smul_sum]
  simp_rw [← hbs, smul_smul, ← map_mul, col]
  rw [Finset.sum_eq_single (e.symm (x + c.1)) (fun i _ hi => by
      rw [if_neg (fun h => hi (by rw [← h, Equiv.symm_apply_apply])), mul_zero, map_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [if_pos (by rw [Equiv.apply_symm_apply]), Equiv.apply_symm_apply]
  rfl

end S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_completeOrthogonalIdempotents_forall_act_schrodingerFrame_eq
end P2MW
export P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_completeOrthogonalIdempotents_forall_act_schrodingerFrame_eq (solution)
