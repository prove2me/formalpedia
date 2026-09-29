-- Prove2me | solution 1 for AlgebraicCurve.exists_ringEquiv_closure_of_support_correspondence_single_eq_of_essFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/de8c57da-6c2e-5c5f-b5c5-58db84f620db

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_Algebra_exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_exists_isRational_forall_mem_and_evalAt_eq_of_algHom
import Theorems.Thm_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Divisor_mem_support_correspondence_single_iff_exists_and_iff_mem_support_correspondence_single
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_ringEquiv_closure_of_support_correspondence_single_eq_of_essFiniteType
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open AlgebraicCurve

open scoped TensorProduct

namespace ImageCurveDet

open scoped TensorProduct

variable {K : Type} [Field K]

section Tensor
variable {F₀ F : Type} [Field F₀] [Algebra K F₀] [Field F] [Algebra K F]

noncomputable def Phi (φ₀ φ₁ : F₀ →ₐ[K] F) : F₀ ⊗[K] F₀ →ₐ[K] F :=
  Algebra.TensorProduct.lift φ₀ φ₁ (fun _ _ => Commute.all _ _)

theorem Phi_tmul (φ₀ φ₁ : F₀ →ₐ[K] F) (a b : F₀) : Phi φ₀ φ₁ (a ⊗ₜ[K] b) = φ₀ a * φ₁ b :=
  Algebra.TensorProduct.lift_tmul _ _ _ a b

theorem Phi_left (φ₀ φ₁ : F₀ →ₐ[K] F) (a : F₀) : Phi φ₀ φ₁ (a ⊗ₜ[K] 1) = φ₀ a := by
  rw [Phi_tmul, map_one, mul_one]

theorem Phi_right (φ₀ φ₁ : F₀ →ₐ[K] F) (b : F₀) : Phi φ₀ φ₁ (1 ⊗ₜ[K] b) = φ₁ b := by
  rw [Phi_tmul, map_one, one_mul]

theorem closure_eq_closure_range (φ₀ φ₁ : F₀ →ₐ[K] F) :
    Subfield.closure (Set.range φ₀ ∪ Set.range φ₁) = Subfield.closure (Set.range (Phi φ₀ φ₁)) := by
  apply le_antisymm
  · apply Subfield.closure_mono
    rintro x (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact ⟨a ⊗ₜ[K] 1, Phi_left φ₀ φ₁ a⟩
    · exact ⟨1 ⊗ₜ[K] b, Phi_right φ₀ φ₁ b⟩
  · rw [Subfield.closure_le]
    rintro x ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul a b =>
      rw [Phi_tmul]
      exact mul_mem (Subfield.subset_closure (Or.inl ⟨a, rfl⟩)) (Subfield.subset_closure (Or.inr ⟨b, rfl⟩))
    | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem subringClosure_eq_range (φ₀ φ₁ : F₀ →ₐ[K] F) :
    Subring.closure (Set.range φ₀ ∪ Set.range φ₁) = (Phi φ₀ φ₁).toRingHom.range := by
  apply Subring.closure_eq_of_le
  · rintro x (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact ⟨a ⊗ₜ[K] 1, Phi_left φ₀ φ₁ a⟩
    · exact ⟨1 ⊗ₜ[K] b, Phi_right φ₀ φ₁ b⟩
  · rintro x ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => show Phi φ₀ φ₁ 0 ∈ _; rw [map_zero]; exact zero_mem _
    | tmul a b =>
      show Phi φ₀ φ₁ (a ⊗ₜ[K] b) ∈ _
      rw [Phi_tmul]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨a, rfl⟩)) (Subring.subset_closure (Or.inr ⟨b, rfl⟩))
    | add x y hx hy => show Phi φ₀ φ₁ (x + y) ∈ _; rw [map_add]; exact add_mem hx hy

end Tensor

section RangeIso
variable {A B C : Type} [CommRing A] [CommRing B] [CommRing C]

noncomputable def rangeEquivOfKerEq (f : A →+* B) (g : A →+* C) (h : RingHom.ker f = RingHom.ker g) :
    ↥f.range ≃+* ↥g.range :=
  (RingHom.quotientKerEquivRange f).symm.trans
    ((Ideal.quotEquivOfEq h).trans (RingHom.quotientKerEquivRange g))

theorem rangeEquivOfKerEq_apply (f : A →+* B) (g : A →+* C) (h : RingHom.ker f = RingHom.ker g) (a : A) :
    rangeEquivOfKerEq f g h ⟨f a, ⟨a, rfl⟩⟩ = ⟨g a, ⟨a, rfl⟩⟩ := by
  unfold rangeEquivOfKerEq
  simp only [RingEquiv.trans_apply]
  have h1 : (RingHom.quotientKerEquivRange f).symm ⟨f a, ⟨a, rfl⟩⟩ = Ideal.Quotient.mk (RingHom.ker f) a := by
    apply (RingHom.quotientKerEquivRange f).injective
    rw [RingEquiv.apply_symm_apply]
    rfl
  rw [h1]
  rfl

end RangeIso

section FracExt
variable {F F' : Type} [Field F] [Field F']

@[reducible] noncomputable def closureAlgebra (S : Subring F) : Algebra ↥S ↥(Subfield.closure (S : Set F)) :=
  (Subring.inclusion (show S ≤ (Subfield.closure (S : Set F)).toSubring from
    fun _ hx => Subfield.subset_closure hx)).toAlgebra

theorem closureAlgebra_algebraMap_apply (S : Subring F) (x : ↥S) :
    (@algebraMap ↥S ↥(Subfield.closure (S : Set F)) _ _ (closureAlgebra S) x : F) = (x : F) := rfl

theorem isFractionRing_closure (S : Subring F) :
    @IsFractionRing ↥S _ ↥(Subfield.closure (S : Set F)) _ (closureAlgebra S) := by
  letI := closureAlgebra S
  haveI : FaithfulSMul ↥S ↥(Subfield.closure (S : Set F)) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).2 ?_
    intro a b h
    apply Subtype.ext
    have := congrArg (fun z : ↥(Subfield.closure (S : Set F)) => (z : F)) h
    simpa [closureAlgebra_algebraMap_apply] using this
  refine IsFractionRing.of_field ↥S ↥(Subfield.closure (S : Set F)) ?_
  rintro ⟨z, hz⟩
  obtain ⟨y, hy, w, hw, rfl⟩ := Subfield.mem_closure_iff.1 hz
  rw [Subring.closure_eq_of_le (le_refl S) Subring.subset_closure] at hy hw
  · refine ⟨⟨y, hy⟩, ⟨w, hw⟩, ?_⟩
    apply Subtype.ext
    simp [closureAlgebra_algebraMap_apply]

noncomputable def closureEquiv (S : Subring F) (S' : Subring F') (σ : ↥S ≃+* ↥S') :
    ↥(Subfield.closure (S : Set F)) ≃+* ↥(Subfield.closure (S' : Set F')) :=
  letI := closureAlgebra S
  letI := closureAlgebra S'
  haveI := isFractionRing_closure S
  haveI := isFractionRing_closure S'
  IsFractionRing.ringEquivOfRingEquiv σ

theorem closureEquiv_apply_coe (S : Subring F) (S' : Subring F') (σ : ↥S ≃+* ↥S') (x : ↥S)
    (hx : (x : F) ∈ Subfield.closure (S : Set F)) :
    (closureEquiv S S' σ ⟨(x : F), hx⟩ : F') = ((σ x : ↥S') : F') := by
  have h := @IsFractionRing.ringEquivOfRingEquiv_algebraMap ↥S ↥(Subfield.closure (S : Set F)) ↥S' ↥(Subfield.closure (S' : Set F'))
    _ _ _ _ (closureAlgebra S) (isFractionRing_closure S) (closureAlgebra S') (isFractionRing_closure S') σ x
  exact congrArg (fun z : ↥(Subfield.closure (S' : Set F')) => (z : F')) h

def subfieldCongr {T₁ T₂ : Subfield F} (h : T₁ = T₂) : ↥T₁ ≃+* ↥T₂ where
  toFun x := ⟨x.1, h ▸ x.2⟩
  invFun y := ⟨y.1, h.symm ▸ y.2⟩
  left_inv x := rfl
  right_inv y := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[scoped simp] theorem subfieldCongr_apply_coe {T₁ T₂ : Subfield F} (h : T₁ = T₂) (x : ↥T₁) :
    (subfieldCongr h x : F) = (x : F) := rfl

@[scoped simp] theorem subfieldCongr_symm_apply_coe {T₁ T₂ : Subfield F} (h : T₁ = T₂) (x : ↥T₂) :
    ((subfieldCongr h).symm x : F) = (x : F) := rfl

end FracExt

section Eval
variable {F F' : Type} [Field F] [Algebra K F] [Field F'] [Algebra K F']

theorem isRational_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) : v.IsRational := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact IsSepClosed.algebraMap_surjective K v.ResidueField

theorem evalAt_restrict [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']
    (w : Place K F') (hw : w.IsRational) (hP : (w.restrict F).IsRational) {a : F}
    (ha : a ∈ (w.restrict F).toValuationSubring) :
    w.evalAt (algebraMap F F' a) = (w.restrict F).evalAt a := by
  apply (algebraMap K w.ResidueField).injective
  have ha' : algebraMap F F' a ∈ w.toValuationSubring := (Place.mem_restrict_iff (w := w)).1 ha
  rw [w.algebraMap_evalAt hw ha', IsScalarTower.algebraMap_apply K (w.restrict F).ResidueField w.ResidueField,
    (w.restrict F).algebraMap_evalAt hP ha, Place.algebraMap_residueField_eq, Place.restrictResidueMap_residue]
  rfl

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (a : F) :
    a ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ a ∈ w.toValuationSubring :=
  Iff.rfl

theorem evalAt_restrictAlong [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') {a : F}
    (ha : a ∈ (w.restrictAlong φ hφ).toValuationSubring) :
    w.evalAt (φ a) = (w.restrictAlong φ hφ).evalAt a := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact evalAt_restrict w (isRational_of_isAlgClosed w) (isRational_of_isAlgClosed _) ha

end Eval

section Supplied

variable {F : Type} [Field F] [Algebra K F]

theorem isRational_of_isAlgClosed' [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) : v.IsRational := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

noncomputable def residueFieldEquiv (v : Place K F) (hv : v.IsRational) : K ≃+* v.ResidueField :=
  RingEquiv.ofBijective (algebraMap K v.ResidueField) ⟨v.algebraMap_residueField_injective, hv⟩

@[scoped simp] theorem residueFieldEquiv_apply (v : Place K F) (hv : v.IsRational) (a : K) :
    residueFieldEquiv v hv a = algebraMap K v.ResidueField a := rfl

noncomputable def evalHom (v : Place K F) (hv : v.IsRational) : ↥v.toValuationSubring →+* K :=
  (residueFieldEquiv v hv).symm.toRingHom.comp (IsLocalRing.residue ↥v.toValuationSubring)

theorem algebraMap_evalHom (v : Place K F) (hv : v.IsRational) (f : ↥v.toValuationSubring) :
    algebraMap K v.ResidueField (evalHom v hv f) = IsLocalRing.residue ↥v.toValuationSubring f := by
  show algebraMap K v.ResidueField ((residueFieldEquiv v hv).symm (IsLocalRing.residue ↥v.toValuationSubring f)) = _
  rw [← residueFieldEquiv_apply v hv, RingEquiv.apply_symm_apply]

theorem evalHom_eq_evalAt (v : Place K F) (hv : v.IsRational) (f : ↥v.toValuationSubring) :
    evalHom v hv f = v.evalAt (f : F) := by
  apply v.algebraMap_residueField_injective
  rw [algebraMap_evalHom, v.algebraMap_evalAt hv f.2]

theorem evalAt_eq_evalHom (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt f = evalHom v hv ⟨f, hf⟩ :=
  (evalHom_eq_evalAt v hv ⟨f, hf⟩).symm

theorem evalAt_zero (v : Place K F) (hv : v.IsRational) : v.evalAt (0 : F) = 0 := by
  rw [evalAt_eq_evalHom v hv (zero_mem _)]
  exact map_zero (evalHom v hv)

theorem evalAt_add (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  rw [evalAt_eq_evalHom v hv (add_mem hf hg), evalAt_eq_evalHom v hv hf, evalAt_eq_evalHom v hv hg, ← map_add]
  rfl

theorem evalAt_mul (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  rw [evalAt_eq_evalHom v hv (mul_mem hf hg), evalAt_eq_evalHom v hv hf, evalAt_eq_evalHom v hv hg, ← map_mul]
  rfl

theorem evalAt_neg (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (-f) = -v.evalAt f := by
  rw [evalAt_eq_evalHom v hv (neg_mem hf), evalAt_eq_evalHom v hv hf, ← map_neg]
  rfl

theorem evalAt_sub (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  rw [evalAt_eq_evalHom v hv (sub_mem hf hg), evalAt_eq_evalHom v hv hf, evalAt_eq_evalHom v hv hg, ← map_sub]
  rfl

theorem evalAt_pow (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  rw [evalAt_eq_evalHom v hv (pow_mem hf n), evalAt_eq_evalHom v hv hf, ← map_pow]
  rfl

theorem evalAt_algebraMap (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have : IsLocalRing.residue ↥v.toValuationSubring ⟨algebraMap K F a, v.algebraMap_mem' a⟩ = algebraMap K v.ResidueField a := rfl
  rw [this, v.residueInv_algebraMap]

theorem evalAt_sum (v : Place K F) (hv : v.IsRational) {ι : Type} (s : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ s, f i ∈ v.toValuationSubring) :
    v.evalAt (∑ i ∈ s, f i) = ∑ i ∈ s, v.evalAt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evalAt_zero v hv
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      evalAt_add v hv (hf a (Finset.mem_insert_self a s))
        (Subring.sum_mem _ fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem evalAt_prod (v : Place K F) (hv : v.IsRational) {ι : Type} (s : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ s, f i ∈ v.toValuationSubring) :
    v.evalAt (∏ i ∈ s, f i) = ∏ i ∈ s, v.evalAt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      evalAt_mul v hv (hf a (Finset.mem_insert_self a s))
        (Subring.prod_mem _ fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem evalAt_ne_zero_of_inv_mem (v : Place K F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring) (hf' : f⁻¹ ∈ v.toValuationSubring) : v.evalAt f ≠ 0 := by
  intro h0
  have h1 : v.evalAt (f * f⁻¹) = 1 := by rw [mul_inv_cancel₀ hf0]; exact v.evalAt_one
  rw [evalAt_mul v hv hf hf', h0, zero_mul] at h1
  exact zero_ne_one h1

theorem inv_mem_of_evalAt_ne_zero (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) : f⁻¹ ∈ v.toValuationSubring := by
  have hres : IsLocalRing.residue ↥v.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
    intro h0
    apply h
    apply v.algebraMap_residueField_injective
    rw [v.algebraMap_evalAt hv hf, h0, map_zero]
  have hnot : (⟨f, hf⟩ : ↥v.toValuationSubring) ∉ IsLocalRing.maximalIdeal ↥v.toValuationSubring :=
    fun hm => hres ((IsLocalRing.residue_eq_zero_iff _).2 hm)
  have hunit : IsUnit (⟨f, hf⟩ : ↥v.toValuationSubring) := by
    by_contra hnu
    exact hnot ((IsLocalRing.mem_maximalIdeal _).2 hnu)
  have hcoe : ((hunit.unit : (↥v.toValuationSubring)ˣ) : ↥v.toValuationSubring) = ⟨f, hf⟩ := hunit.unit_spec
  have key : (v.toValuationSubring.subtype ((hunit.unit⁻¹ : (↥v.toValuationSubring)ˣ) : ↥v.toValuationSubring)) = f⁻¹ := by
    rw [map_units_inv, hcoe]
    rfl
  rw [← key]
  exact SetLike.coe_mem _

end Supplied

section Heart
variable {F₀ F F' : Type} [Field F₀] [Algebra K F₀] [Field F] [Algebra K F] [Field F'] [Algebra K F']

theorem ker_le_ker [IsAlgClosed K] [IsCurveOver K F₀] [IsCurveOver K F] [IsCurveOver K F']
    [Algebra.EssFiniteType K F] [Algebra.EssFiniteType K F']
    (φ₀ φ₁ : F₀ →ₐ[K] F) (hφ₀ : φ₀.toRingHom.IsIntegral) (hφ₁ : φ₁.toRingHom.IsIntegral)
    (hfin₀ : FiniteAlong K φ₀) (hfin₁ : FiniteAlong K φ₁)
    (φ'₀ φ'₁ : F₀ →ₐ[K] F') (hφ'₀ : φ'₀.toRingHom.IsIntegral) (hφ'₁ : φ'₁.toRingHom.IsIntegral)
    (hfin'₀ : FiniteAlong K φ'₀) (hfin'₁ : FiniteAlong K φ'₁)
    (hsupp : ∀ P : Place K F₀,
      (Divisor.correspondence φ'₀ φ'₁ hφ'₀ hφ'₁ (Finsupp.single P 1)).support ⊆
        (Divisor.correspondence φ₀ φ₁ hφ₀ hφ₁ (Finsupp.single P 1)).support) :
    RingHom.ker (Phi φ₀ φ₁).toRingHom ≤ RingHom.ker (Phi φ'₀ φ'₁).toRingHom := by
  classical
  intro t ht
  rw [RingHom.mem_ker] at ht
  rw [RingHom.mem_ker]
  by_contra hne

  obtain ⟨S, hS⟩ := TensorProduct.exists_finset (R := K) t
  have hsumF : (Phi φ₀ φ₁).toRingHom t = ∑ i ∈ S, φ₀ i.1 * φ₁ i.2 := by
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hS, map_sum]
    exact Finset.sum_congr rfl fun i _ => Phi_tmul φ₀ φ₁ i.1 i.2
  have hsumF' : (Phi φ'₀ φ'₁).toRingHom t = ∑ i ∈ S, φ'₀ i.1 * φ'₁ i.2 := by
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hS, map_sum]
    exact Finset.sum_congr rfl fun i _ => Phi_tmul φ'₀ φ'₁ i.1 i.2

  obtain ⟨x, hx, -, -⟩ :=
    (AlgebraicCurve.isCurveOver_iff_exists_transcendental_finiteDimensional (K := K) (F := F')).1 inferInstance

  obtain ⟨T, hT⟩ : ∃ T : Finset F', T = insert x (insert ((Phi φ'₀ φ'₁).toRingHom t)
      (S.image (fun i => φ'₀ i.1) ∪ S.image (fun i => φ'₁ i.2))) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Subalgebra K F', B = Algebra.adjoin K (T : Set F') := ⟨_, rfl⟩
  have hTB : ∀ z ∈ T, z ∈ B := fun z hz => hB ▸ Algebra.subset_adjoin (Finset.mem_coe.2 hz)
  have hxB : x ∈ B := hTB x (hT ▸ Finset.mem_insert_self _ _)
  have hyB : (Phi φ'₀ φ'₁).toRingHom t ∈ B :=
    hTB _ (hT ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h0B : ∀ i ∈ S, φ'₀ i.1 ∈ B := fun i hi =>
    hTB _ (hT ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image_of_mem (fun i : F₀ × F₀ => φ'₀ i.1) hi))))
  have h1B : ∀ i ∈ S, φ'₁ i.2 ∈ B := fun i hi =>
    hTB _ (hT ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun i : F₀ × F₀ => φ'₁ i.2) hi))))
  haveI hFT : Algebra.FiniteType K ↥B := by
    rw [hB]; exact (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset T)

  obtain ⟨χ, hχ⟩ := Algebra.exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed
      (k := K) (B := ↥B) (ι := Unit) (fun _ => (⟨(Phi φ'₀ φ'₁).toRingHom t, hyB⟩ : ↥B))
      (fun _ h => hne (by simpa using congrArg Subtype.val h))

  obtain ⟨R', hR'rat, hR'⟩ := AlgebraicCurve.exists_isRational_forall_mem_and_evalAt_eq_of_algHom
      (L := K) (F := F') B χ ⟨⟨x, hxB⟩, by
        rintro ⟨a, ha⟩
        exact hx (by rw [show x = algebraMap K F' a from ha.symm]; exact isAlgebraic_algebraMap a)⟩

  obtain ⟨P, hP⟩ : ∃ P : Place K F₀, R'.restrictAlong φ'₀ hφ'₀ = P := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Place K F₀, R'.restrictAlong φ'₁ hφ'₁ = Q := ⟨_, rfl⟩

  have hQ' := (AlgebraicCurve.Divisor.mem_support_correspondence_single_iff_exists_and_iff_mem_support_correspondence_single
      φ'₀ φ'₁ hφ'₀ hφ'₁ hfin'₀ hfin'₁ P Q).1.2 ⟨R', hP, hQ⟩
  obtain ⟨R, hR₀, hR₁⟩ := (AlgebraicCurve.Divisor.mem_support_correspondence_single_iff_exists_and_iff_mem_support_correspondence_single
      φ₀ φ₁ hφ₀ hφ₁ hfin₀ hfin₁ P Q).1.1 (hsupp P hQ')

  have hreg₀ : ∀ i ∈ S, φ'₀ i.1 ∈ R'.toValuationSubring := fun i hi => (hR' ⟨φ'₀ i.1, h0B i hi⟩).1
  have hreg₁ : ∀ i ∈ S, φ'₁ i.2 ∈ R'.toValuationSubring := fun i hi => (hR' ⟨φ'₁ i.2, h1B i hi⟩).1
  have hPreg : ∀ i ∈ S, i.1 ∈ P.toValuationSubring := fun i hi => by
    rw [← hP]; exact (mem_restrictAlong_iff φ'₀ hφ'₀ R' i.1).2 (hreg₀ i hi)
  have hQreg : ∀ i ∈ S, i.2 ∈ Q.toValuationSubring := fun i hi => by
    rw [← hQ]; exact (mem_restrictAlong_iff φ'₁ hφ'₁ R' i.2).2 (hreg₁ i hi)
  have hRreg₀ : ∀ i ∈ S, φ₀ i.1 ∈ R.toValuationSubring := fun i hi => by
    have h := hPreg i hi
    rw [← hR₀] at h
    exact (mem_restrictAlong_iff φ₀ hφ₀ R i.1).1 h
  have hRreg₁ : ∀ i ∈ S, φ₁ i.2 ∈ R.toValuationSubring := fun i hi => by
    have h := hQreg i hi
    rw [← hR₁] at h
    exact (mem_restrictAlong_iff φ₁ hφ₁ R i.2).1 h
  have hratR : R.IsRational := isRational_of_isAlgClosed R

  have heval' : R'.evalAt ((Phi φ'₀ φ'₁).toRingHom t) = ∑ i ∈ S, P.evalAt i.1 * Q.evalAt i.2 := by
    rw [hsumF', evalAt_sum R' hR'rat S (fun i => φ'₀ i.1 * φ'₁ i.2)
      (fun i hi => mul_mem (hreg₀ i hi) (hreg₁ i hi))]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [evalAt_mul R' hR'rat (hreg₀ i hi) (hreg₁ i hi),
      evalAt_restrictAlong φ'₀ hφ'₀ R' ((mem_restrictAlong_iff φ'₀ hφ'₀ R' i.1).2 (hreg₀ i hi)),
      evalAt_restrictAlong φ'₁ hφ'₁ R' ((mem_restrictAlong_iff φ'₁ hφ'₁ R' i.2).2 (hreg₁ i hi)), hP, hQ]
  have hevalR : R.evalAt ((Phi φ₀ φ₁).toRingHom t) = ∑ i ∈ S, P.evalAt i.1 * Q.evalAt i.2 := by
    rw [hsumF, evalAt_sum R hratR S (fun i => φ₀ i.1 * φ₁ i.2)
      (fun i hi => mul_mem (hRreg₀ i hi) (hRreg₁ i hi))]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [evalAt_mul R hratR (hRreg₀ i hi) (hRreg₁ i hi),
      evalAt_restrictAlong φ₀ hφ₀ R ((mem_restrictAlong_iff φ₀ hφ₀ R i.1).2 (hRreg₀ i hi)),
      evalAt_restrictAlong φ₁ hφ₁ R ((mem_restrictAlong_iff φ₁ hφ₁ R i.2).2 (hRreg₁ i hi)), hR₀, hR₁]

  apply hχ ()
  rw [← (hR' ⟨(Phi φ'₀ φ'₁).toRingHom t, hyB⟩).2]
  show R'.evalAt ((Phi φ'₀ φ'₁).toRingHom t) = 0
  rw [heval', ← hevalR, ht, evalAt_zero R hratR]

end Heart

section Assembly
variable {F₀ F F' : Type} [Field F₀] [Algebra K F₀] [Field F] [Algebra K F] [Field F'] [Algebra K F']

theorem closure_eq_closure_coe_range (φ₀ φ₁ : F₀ →ₐ[K] F) :
    Subfield.closure (Set.range φ₀ ∪ Set.range φ₁) =
      Subfield.closure (((Phi φ₀ φ₁).toRingHom.range : Subring F) : Set F) := by
  rw [closure_eq_closure_range, RingHom.coe_range]
  rfl

noncomputable def theta (φ₀ φ₁ : F₀ →ₐ[K] F) (φ'₀ φ'₁ : F₀ →ₐ[K] F')
    (hker : RingHom.ker (Phi φ₀ φ₁).toRingHom = RingHom.ker (Phi φ'₀ φ'₁).toRingHom) :
    ↥(Subfield.closure (Set.range φ₀ ∪ Set.range φ₁)) ≃+* ↥(Subfield.closure (Set.range φ'₀ ∪ Set.range φ'₁)) :=
  (subfieldCongr (closure_eq_closure_coe_range φ₀ φ₁)).trans
    ((closureEquiv _ _ (rangeEquivOfKerEq _ _ hker)).trans (subfieldCongr (closure_eq_closure_coe_range φ'₀ φ'₁)).symm)

theorem theta_coe (φ₀ φ₁ : F₀ →ₐ[K] F) (φ'₀ φ'₁ : F₀ →ₐ[K] F')
    (hker : RingHom.ker (Phi φ₀ φ₁).toRingHom = RingHom.ker (Phi φ'₀ φ'₁).toRingHom)
    (y : ↥(Subfield.closure (Set.range φ₀ ∪ Set.range φ₁))) :
    (theta φ₀ φ₁ φ'₀ φ'₁ hker y : F') =
      ((closureEquiv _ _ (rangeEquivOfKerEq _ _ hker) (subfieldCongr (closure_eq_closure_coe_range φ₀ φ₁) y)) : F') := by
  unfold theta
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply, subfieldCongr_symm_apply_coe]

theorem step_closure (φ₀ φ₁ : F₀ →ₐ[K] F) (φ'₀ φ'₁ : F₀ →ₐ[K] F')
    (hker : RingHom.ker (Phi φ₀ φ₁).toRingHom = RingHom.ker (Phi φ'₀ φ'₁).toRingHom)
    (t : F₀ ⊗[K] F₀) (hy : (Phi φ₀ φ₁).toRingHom t ∈ Subfield.closure (((Phi φ₀ φ₁).toRingHom.range : Subring F) : Set F)) :
    ((closureEquiv _ _ (rangeEquivOfKerEq _ _ hker) ⟨(Phi φ₀ φ₁).toRingHom t, hy⟩) : F') =
      ((rangeEquivOfKerEq (Phi φ₀ φ₁).toRingHom (Phi φ'₀ φ'₁).toRingHom hker ⟨(Phi φ₀ φ₁).toRingHom t, ⟨t, rfl⟩⟩ : ↥((Phi φ'₀ φ'₁).toRingHom.range)) : F') :=
  closureEquiv_apply_coe (Phi φ₀ φ₁).toRingHom.range (Phi φ'₀ φ'₁).toRingHom.range (rangeEquivOfKerEq _ _ hker)
    ⟨(Phi φ₀ φ₁).toRingHom t, ⟨t, rfl⟩⟩ hy

theorem step_range (φ₀ φ₁ : F₀ →ₐ[K] F) (φ'₀ φ'₁ : F₀ →ₐ[K] F')
    (hker : RingHom.ker (Phi φ₀ φ₁).toRingHom = RingHom.ker (Phi φ'₀ φ'₁).toRingHom) (t : F₀ ⊗[K] F₀) :
    ((rangeEquivOfKerEq (Phi φ₀ φ₁).toRingHom (Phi φ'₀ φ'₁).toRingHom hker ⟨(Phi φ₀ φ₁).toRingHom t, ⟨t, rfl⟩⟩ : ↥((Phi φ'₀ φ'₁).toRingHom.range)) : F') =
      (Phi φ'₀ φ'₁).toRingHom t := by
  rw [rangeEquivOfKerEq_apply]

theorem theta_apply (φ₀ φ₁ : F₀ →ₐ[K] F) (φ'₀ φ'₁ : F₀ →ₐ[K] F')
    (hker : RingHom.ker (Phi φ₀ φ₁).toRingHom = RingHom.ker (Phi φ'₀ φ'₁).toRingHom)
    (t : F₀ ⊗[K] F₀) (hy : (Phi φ₀ φ₁).toRingHom t ∈ Subfield.closure (Set.range φ₀ ∪ Set.range φ₁)) :
    (theta φ₀ φ₁ φ'₀ φ'₁ hker ⟨(Phi φ₀ φ₁).toRingHom t, hy⟩ : F') = (Phi φ'₀ φ'₁).toRingHom t := by
  rw [theta_coe, ← step_range φ₀ φ₁ φ'₀ φ'₁ hker t, ← step_closure φ₀ φ₁ φ'₀ φ'₁ hker t ((closure_eq_closure_coe_range φ₀ φ₁).le hy)]
  rfl

theorem exists_of_kerEq (φ₀ φ₁ : F₀ →ₐ[K] F) (φ'₀ φ'₁ : F₀ →ₐ[K] F')
    (hker : RingHom.ker (Phi φ₀ φ₁).toRingHom = RingHom.ker (Phi φ'₀ φ'₁).toRingHom) :
    ∃ θ : ↥(Subfield.closure (Set.range φ₀ ∪ Set.range φ₁)) ≃+* ↥(Subfield.closure (Set.range φ'₀ ∪ Set.range φ'₁)),
      (∀ x : F₀, (θ ⟨φ₀ x, Subfield.subset_closure (Set.mem_union_left _ (Set.mem_range_self x))⟩ : F') = φ'₀ x) ∧
      (∀ x : F₀, (θ ⟨φ₁ x, Subfield.subset_closure (Set.mem_union_right _ (Set.mem_range_self x))⟩ : F') = φ'₁ x) := by
  have hl : ∀ x : F₀, (Phi φ₀ φ₁).toRingHom (x ⊗ₜ[K] 1) = φ₀ x := fun x => by
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Phi_left]
  have hr : ∀ x : F₀, (Phi φ₀ φ₁).toRingHom (1 ⊗ₜ[K] x) = φ₁ x := fun x => by
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Phi_right]
  have hl' : ∀ x : F₀, (Phi φ'₀ φ'₁).toRingHom (x ⊗ₜ[K] 1) = φ'₀ x := fun x => by
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Phi_left]
  have hr' : ∀ x : F₀, (Phi φ'₀ φ'₁).toRingHom (1 ⊗ₜ[K] x) = φ'₁ x := fun x => by
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Phi_right]
  refine ⟨theta φ₀ φ₁ φ'₀ φ'₁ hker, fun x => ?_, fun x => ?_⟩
  · have hy : (Phi φ₀ φ₁).toRingHom (x ⊗ₜ[K] 1) ∈ Subfield.closure (Set.range φ₀ ∪ Set.range φ₁) := by
      rw [hl]; exact Subfield.subset_closure (Set.mem_union_left _ (Set.mem_range_self x))
    have h := theta_apply φ₀ φ₁ φ'₀ φ'₁ hker (x ⊗ₜ[K] 1) hy
    rw [hl'] at h
    refine Eq.trans ?_ h
    congr 2
    exact Subtype.ext (hl x).symm
  · have hy : (Phi φ₀ φ₁).toRingHom (1 ⊗ₜ[K] x) ∈ Subfield.closure (Set.range φ₀ ∪ Set.range φ₁) := by
      rw [hr]; exact Subfield.subset_closure (Set.mem_union_right _ (Set.mem_range_self x))
    have h := theta_apply φ₀ φ₁ φ'₀ φ'₁ hker (1 ⊗ₜ[K] x) hy
    rw [hr'] at h
    refine Eq.trans ?_ h
    congr 2
    exact Subtype.ext (hr x).symm

end Assembly

end ImageCurveDet
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ringEquiv_closure_of_support_correspondence_single_eq_of_essFiniteType.ImageCurveDet"

theorem solution
    (K : Type) [Field K] [IsAlgClosed K]
    (F₀ : Type) [Field F₀] [Algebra K F₀] [IsCurveOver K F₀]
    (F : Type) [Field F] [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (F' : Type) [Field F'] [Algebra K F'] [IsCurveOver K F'] [Algebra.EssFiniteType K F']

    (φ₀ φ₁ : F₀ →ₐ[K] F) (hφ₀ : φ₀.toRingHom.IsIntegral) (hφ₁ : φ₁.toRingHom.IsIntegral)
    (hfin₀ : FiniteAlong K φ₀) (hfin₁ : FiniteAlong K φ₁)
    (φ'₀ φ'₁ : F₀ →ₐ[K] F') (hφ'₀ : φ'₀.toRingHom.IsIntegral) (hφ'₁ : φ'₁.toRingHom.IsIntegral)
    (hfin'₀ : FiniteAlong K φ'₀) (hfin'₁ : FiniteAlong K φ'₁)

    (hsupp : ∀ P : Place K F₀,
      (Divisor.correspondence φ₀ φ₁ hφ₀ hφ₁ (Finsupp.single P 1)).support =
        (Divisor.correspondence φ'₀ φ'₁ hφ'₀ hφ'₁ (Finsupp.single P 1)).support) :
    ∃ θ : ↥(Subfield.closure (Set.range φ₀ ∪ Set.range φ₁)) ≃+* ↥(Subfield.closure (Set.range φ'₀ ∪ Set.range φ'₁)),
      (∀ x : F₀, (θ ⟨φ₀ x, Subfield.subset_closure (Set.mem_union_left _ (Set.mem_range_self x))⟩ : F') = φ'₀ x) ∧
      (∀ x : F₀, (θ ⟨φ₁ x, Subfield.subset_closure (Set.mem_union_right _ (Set.mem_range_self x))⟩ : F') = φ'₁ x) := by
  have hker : RingHom.ker (ImageCurveDet.Phi φ₀ φ₁).toRingHom = RingHom.ker (ImageCurveDet.Phi φ'₀ φ'₁).toRingHom :=
    le_antisymm
      (ImageCurveDet.ker_le_ker φ₀ φ₁ hφ₀ hφ₁ hfin₀ hfin₁ φ'₀ φ'₁ hφ'₀ hφ'₁ hfin'₀ hfin'₁
        (fun P => Finset.subset_of_eq (hsupp P).symm))
      (ImageCurveDet.ker_le_ker φ'₀ φ'₁ hφ'₀ hφ'₁ hfin'₀ hfin'₁ φ₀ φ₁ hφ₀ hφ₁ hfin₀ hfin₁
        (fun P => Finset.subset_of_eq (hsupp P)))
  exact ImageCurveDet.exists_of_kerEq φ₀ φ₁ φ'₀ φ'₁ hker

end S_AlgebraicCurve_exists_ringEquiv_closure_of_support_correspondence_single_eq_of_essFiniteType
end P2MW
export P2MW.S_AlgebraicCurve_exists_ringEquiv_closure_of_support_correspondence_single_eq_of_essFiniteType (solution)
