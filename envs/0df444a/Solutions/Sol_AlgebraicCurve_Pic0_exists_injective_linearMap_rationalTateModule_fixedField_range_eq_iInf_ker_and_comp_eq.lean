-- Prove2me | solution 1 for AlgebraicCurve.Pic0.exists_injective_linearMap_rationalTateModule_fixedField_range_eq_iInf_ker_and_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/aa2f3d5f-b033-5df5-8f91-c2ddccdf07ea

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_AlgebraicCurve_Divisor_sum_galois_smul_eq_pullback_pushforward
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardNormFormula_of_isSeparable
import Theorems.Thm_AlgebraicCurve_Pic0_pushforwardHom_pullbackHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_exists_injective_linearMap_rationalTateModule_fixedField_range_eq_iInf_ker_and_comp_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace FixedFieldTateDescent

open AlgebraicCurve

section Naturality

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

omit [IsScalarTower K F F'] in

theorem compat_inv (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F)
    (h : ∀ y : F, σ (algebraMap F F' y) = algebraMap F F' (τ y)) :
    ∀ y : F, σ⁻¹ (algebraMap F F' y) = algebraMap F F' (τ⁻¹ y) := by
  intro y
  rw [AlgEquiv.aut_inv, AlgEquiv.aut_inv]
  apply σ.injective
  rw [AlgEquiv.apply_symm_apply, h, AlgEquiv.apply_symm_apply]

theorem restrict_smul_of_compat [Algebra.IsIntegral F F'] (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F)
    (h : ∀ y : F, σ (algebraMap F F' y) = algebraMap F F' (τ y)) (w : Place K F') :
    (σ • w).restrict F = τ • w.restrict F := by
  apply Place.ext
  ext x
  rw [Place.restrict_toValuationSubring, ValuationSubring.mem_comap, Place.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, Place.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, Place.restrict_toValuationSubring,
    ValuationSubring.mem_comap]
  have key : σ⁻¹ • algebraMap F F' x = algebraMap F F' (τ⁻¹ • x) := by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def]
    exact compat_inv σ τ h x
  rw [key]

omit [IsScalarTower K F F'] in

theorem ramificationIndex_smul_of_compat (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F)
    (h : ∀ y : F, σ (algebraMap F F' y) = algebraMap F F' (τ y)) (w : Place K F') :
    (σ • w).ramificationIndex F = w.ramificationIndex F := by
  unfold Place.ramificationIndex
  congr 1
  ext n
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => ?_

  have hord : ∀ f : F, (σ • w).ord (algebraMap F F' f) = w.ord (algebraMap F F' (τ.symm f)) := by
    intro f
    have hf : algebraMap F F' f = σ (algebraMap F F' (τ.symm f)) := by
      rw [h, AlgEquiv.apply_symm_apply]
    rw [hf]
    exact Place.ord_smul σ w _
  constructor
  · rintro ⟨f, hf, hn⟩
    exact ⟨τ.symm f, by simpa using hf, by rw [← hord]; exact hn⟩
  · rintro ⟨f, hf, hn⟩
    refine ⟨τ f, by simpa using hf, ?_⟩
    rw [hord, AlgEquiv.symm_apply_apply]
    exact hn

variable [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

theorem smul_pullback_of_compat (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F)
    (h : ∀ y : F, σ (algebraMap F F' y) = algebraMap F F' (τ y)) (D : Divisor K F) :
    σ • Divisor.pullback F' D = Divisor.pullback F' (τ • D) := by
  ext w
  rw [Divisor.smul_apply, Divisor.pullback_apply, Divisor.pullback_apply, Divisor.smul_apply,
    ramificationIndex_smul_of_compat σ⁻¹ τ⁻¹ (compat_inv σ τ h) w,
    restrict_smul_of_compat σ⁻¹ τ⁻¹ (compat_inv σ τ h) w]

theorem smul_pullbackHom_of_compat [FundamentalIdentity K F F'] (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F)
    (h : ∀ y : F, σ (algebraMap F F' y) = algebraMap F F' (τ y)) (x : Pic0 K F) :
    σ • Pic0.pullbackHom F' x = Pic0.pullbackHom F' (τ • x) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.pullbackHom_mk, Pic0.smul_mk, Pic0.smul_mk, Pic0.pullbackHom_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  simp only [Pic0.coe_degZeroSMulHom, Pic0.coe_pullbackDegZeroHom]
  exact smul_pullback_of_compat σ τ h D

end Naturality

section Actions

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ofAlgAut_smul_place (σ : F ≃ₐ[K] F) (v : Place K F) :
    SemilinearAut.ofAlgAut σ • v = σ • v := by
  apply Place.ext
  ext x
  rw [SemilinearAut.smul_toValuationSubring, Place.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
  exact Iff.rfl

theorem ofAlgAut_smul_divisor (σ : F ≃ₐ[K] F) (D : Divisor K F) :
    SemilinearAut.ofAlgAut σ • D = σ • D :=
  have h : (fun v : Place K F => SemilinearAut.ofAlgAut σ • v) = fun v => σ • v :=
    funext fun v => ofAlgAut_smul_place σ v
  (SemilinearAut.divisor_smul_def _ D).trans
    ((congrArg (Finsupp.mapDomain · D) h).trans (Divisor.smul_def σ D).symm)

end Actions

section Tate

variable {p : ℕ} [Fact p.Prime]
variable {J J' : Type} [AddCommGroup J] [AddCommGroup J']

def tmap (f : J →+ J') : TateModule p J →ₗ[ℤ_[p]] TateModule p J' where
  toFun x := ⟨fun n => f ((x : ℕ → J) n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, map_zero],
     by rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    show f (((x + y : TateModule p J) : ℕ → J) n) = f ((x : ℕ → J) n) + f ((y : ℕ → J) n)
    rw [TateModule.coe_add, Pi.add_apply, map_add])
  map_smul' a x := Subtype.ext (funext fun n => by
    show f (((a • x : TateModule p J) : ℕ → J) n) = ((a.appr n : ℕ) : ℤ) • f ((x : ℕ → J) n)
    rw [TateModule.smul_apply, map_zsmul])

@[scoped simp] theorem coe_tmap_apply (f : J →+ J') (x : TateModule p J) (n : ℕ) :
    ((tmap f x : TateModule p J') : ℕ → J') n = f ((x : ℕ → J) n) := rfl

omit [Fact p.Prime] in
theorem coe_nsmul_apply (n : ℕ) (x : TateModule p J) (m : ℕ) :
    ((n • x : TateModule p J) : ℕ → J) m = n • (x : ℕ → J) m := by
  rw [AddSubmonoidClass.coe_nsmul, Pi.smul_apply]

omit [Fact p.Prime] in
theorem coe_sum_apply {I : Type*} (s : Finset I) (x : I → TateModule p J) (m : ℕ) :
    ((∑ i ∈ s, x i : TateModule p J) : ℕ → J) m = ∑ i ∈ s, (x i : ℕ → J) m := by
  rw [AddSubgroup.val_finsetSum, Finset.sum_apply]

theorem tmap_tmap_eq_nsmul {ι : J →+ J'} {N : J' →+ J} {n : ℕ}
    (h : ∀ x : J, N (ι x) = (n : ℤ) • x) (x : TateModule p J) :
    tmap N (tmap ι x) = n • x := by
  refine Subtype.ext (funext fun m => ?_)
  rw [coe_tmap_apply, coe_tmap_apply, h, coe_nsmul_apply, natCast_zsmul]

theorem sum_rep_eq_tmap_tmap {G : Type} [Monoid G] [DistribMulAction G J']
    {I : Type*} (s : Finset I) (e : I → G) {ι : J →+ J'} {N : J' →+ J}
    (h : ∀ y : J', ∑ i ∈ s, e i • y = ι (N y)) (x : TateModule p J') :
    ∑ i ∈ s, TateModule.rep p J' G (e i) x = tmap ι (tmap N x) := by
  refine Subtype.ext (funext fun m => ?_)
  rw [coe_sum_apply, coe_tmap_apply, coe_tmap_apply, ← h]
  rfl

theorem tmap_comp_rep_eq {G G' : Type} [Monoid G] [Monoid G'] [DistribMulAction G J]
    [DistribMulAction G' J'] {ι : J →+ J'} {σ : G'} {τ : G}
    (h : ∀ y : J, ι (τ • y) = σ • ι y) :
    tmap ι ∘ₗ TateModule.rep p J G τ = TateModule.rep p J' G' σ ∘ₗ tmap ι := by
  refine LinearMap.ext fun x => Subtype.ext (funext fun m => ?_)
  show ι (τ • (x : ℕ → J) m) = σ • ι ((x : ℕ → J) m)
  exact h _

theorem nsmul_eq_cast_smul_rat (n : ℕ) (v : ModularCurve.RationalTateModule p J) :
    n • v = (n : ℚ_[p]) • v :=
  (Nat.cast_smul_eq_nsmul ℚ_[p] n v).symm

theorem bc_tmap_tmap_eq_nsmul {ι : J →+ J'} {N : J' →+ J} {n : ℕ}
    (h : ∀ x : J, N (ι x) = (n : ℤ) • x) (v : ModularCurve.RationalTateModule p J) :
    (tmap N).baseChange ℚ_[p] ((tmap ι).baseChange ℚ_[p] v) = n • v := by
  induction v using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, nsmul_zero]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, tmap_tmap_eq_nsmul h,
      ← Nat.cast_smul_eq_nsmul ℤ_[p] n x, TensorProduct.tmul_smul, Nat.cast_smul_eq_nsmul]
  | add v w hv hw => rw [map_add, map_add, hv, hw, nsmul_add]

theorem sum_rationalGaloisRep_eq {G : Type} [Monoid G] [DistribMulAction G J']
    {I : Type*} (s : Finset I) (e : I → G) {ι : J →+ J'} {N : J' →+ J}
    (h : ∀ y : J', ∑ i ∈ s, e i • y = ι (N y)) (v : ModularCurve.RationalTateModule p J') :
    ∑ i ∈ s, ModularCurve.rationalGaloisRep p J' G (e i) v =
      (tmap ι).baseChange ℚ_[p] ((tmap N).baseChange ℚ_[p] v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finset.sum_const_zero]
  | tmul a x =>
    simp only [ModularCurve.rationalGaloisRep_tmul, LinearMap.baseChange_tmul]
    rw [← TensorProduct.tmul_sum, sum_rep_eq_tmap_tmap s e h x]
  | add v w hv hw => simp only [map_add, Finset.sum_add_distrib, hv, hw]

theorem bc_tmap_comp_rationalGaloisRep_eq {G G' : Type} [Monoid G] [Monoid G']
    [DistribMulAction G J] [DistribMulAction G' J'] {ι : J →+ J'} {σ : G'} {τ : G}
    (h : ∀ y : J, ι (τ • y) = σ • ι y) :
    (tmap ι).baseChange ℚ_[p] ∘ₗ ModularCurve.rationalGaloisRep p J G τ =
      ModularCurve.rationalGaloisRep p J' G' σ ∘ₗ (tmap ι).baseChange ℚ_[p] := by
  rw [ModularCurve.rationalGaloisRep_apply, ModularCurve.rationalGaloisRep_apply,
    ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, tmap_comp_rep_eq h]

end Tate

section FixedField

open IntermediateField

variable {k : Type} [Field k] {F : Type} [Field F] [Algebra k F]
  (G : Subgroup (F ≃ₐ[k] F)) [Finite G]

def galEquiv : G ≃* (F ≃ₐ[fixedField G] F) := FixedPoints.toAlgAutMulEquiv G F

theorem galEquiv_restrictScalars (g : G) :
    (galEquiv G g).restrictScalars k = (g : F ≃ₐ[k] F) := by
  apply AlgEquiv.ext
  intro x
  rfl

theorem finiteDimensional_fixedField : FiniteDimensional (fixedField G) F :=
  (inferInstance : FiniteDimensional (FixedPoints.subfield G F) F)

theorem isGalois_fixedField : IsGalois (fixedField G) F :=
  (inferInstance : IsGalois (FixedPoints.subfield G F) F)

omit [Finite G] in

theorem finrank_fixedField [Fintype G] : Module.finrank (fixedField G) F = Fintype.card G :=
  FixedPoints.finrank_eq_card G F

variable [HasPrincipalDivisors k F]

theorem sum_smul_eq_pullbackHom_pushforwardHom [Fintype G]
    [FiniteDimensional (fixedField G) F] [IsGalois (fixedField G) F]
    [SumRamificationInertia k (fixedField G) F]
    (H : Divisor.PushforwardNormFormula k (fixedField G) F) (y : Pic0 k F) :
    ∑ g : G, (g : F ≃ₐ[k] F) • y =
      Pic0.pullbackHom F (Pic0.pushforwardHom k (fixedField G) F H y) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective y
  rw [Pic0.pushforwardHom_mk, Pic0.pullbackHom_mk]
  simp only [Pic0.smul_mk]
  show ∑ g : G, QuotientAddGroup.mk' _ (Pic0.degZeroSMulHom (g : F ≃ₐ[k] F) D) =
    QuotientAddGroup.mk' _ _
  rw [← map_sum]
  refine congrArg _ (Subtype.ext ?_)
  rw [AddSubgroup.val_finsetSum]
  simp only [Pic0.coe_degZeroSMulHom, Pic0.coe_pullbackDegZeroHom, Pic0.coe_pushforwardDegZeroHom]
  rw [← Divisor.sum_galois_smul_eq_pullback_pushforward (K := k) (F := fixedField G) (D : Divisor k F)]
  refine (Fintype.sum_equiv (galEquiv G).toEquiv _ _ fun g => ?_)
  show (g : F ≃ₐ[k] F) • (D : Divisor k F) =
    SemilinearAut.ofAlgAut ((galEquiv G g).restrictScalars k) • (D : Divisor k F)
  rw [galEquiv_restrictScalars, ofAlgAut_smul_divisor]

end FixedField

section Descent

variable {p : ℕ} [Fact p.Prime]
variable {J₀ J : Type} [AddCommGroup J₀] [AddCommGroup J]
variable {G₀ G : Type} [Group G₀] [Group G] [DistribMulAction G₀ J₀] [DistribMulAction G J]

theorem descent {I : Type} [Fintype I] [Nonempty I] (e : I → G)
    (ι : J₀ →+ J) (N : J →+ J₀)
    (hNι : ∀ x : J₀, N (ι x) = (Fintype.card I : ℤ) • x)
    (hsum : ∀ y : J, ∑ i ∈ (Finset.univ : Finset I), e i • y = ι (N y))
    (compat : G → G₀ → Prop)
    (hnat : ∀ (σ : G) (τ : G₀), compat σ τ → ∀ x : J₀, ι (τ • x) = σ • ι x)
    (hone : ∀ i : I, compat (e i) 1) :
    ∃ Φ : ModularCurve.RationalTateModule p J₀ →ₗ[ℚ_[p]] ModularCurve.RationalTateModule p J,
      Function.Injective Φ ∧
      LinearMap.range Φ =
        ⨅ i : I, LinearMap.ker (ModularCurve.rationalGaloisRep p J G (e i) - 1) ∧
      ∀ (σ : G) (τ : G₀), compat σ τ →
        Φ ∘ₗ ModularCurve.rationalGaloisRep p J₀ G₀ τ = ModularCurve.rationalGaloisRep p J G σ ∘ₗ Φ := by
  have hn0 : (Fintype.card I : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := I)).ne'
  refine ⟨(tmap ι).baseChange ℚ_[p], ?_, ?_, ?_⟩
  ·
    intro v w hvw
    have h1 := congrArg ((tmap (p := p) N).baseChange ℚ_[p]) hvw
    simp only [bc_tmap_tmap_eq_nsmul hNι, nsmul_eq_cast_smul_rat] at h1
    have h2 := congrArg (fun u => (Fintype.card I : ℚ_[p])⁻¹ • u) h1
    simp only [inv_smul_smul₀ hn0] at h2
    exact h2
  ·
    apply le_antisymm
    ·
      rintro _ ⟨v, rfl⟩
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
        sub_eq_zero]
      intro i
      have h3 := bc_tmap_comp_rationalGaloisRep_eq (p := p) (hnat (e i) 1 (hone i))
      rw [map_one, Module.End.one_eq_id, LinearMap.comp_id] at h3
      exact (LinearMap.congr_fun h3 v).symm
    ·
      intro v hv
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
        sub_eq_zero] at hv
      have h2 := sum_rationalGaloisRep_eq (p := p) (Finset.univ : Finset I) e hsum v
      rw [Finset.sum_congr rfl fun i _ => hv i, Finset.sum_const, Finset.card_univ,
        nsmul_eq_cast_smul_rat] at h2
      have h5 : v = (Fintype.card I : ℚ_[p])⁻¹ •
          (tmap ι).baseChange ℚ_[p] ((tmap N).baseChange ℚ_[p] v) := by
        rw [← h2, inv_smul_smul₀ hn0]
      rw [h5]
      exact Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)
  ·
    intro σ τ h
    exact bc_tmap_comp_rationalGaloisRep_eq (hnat σ τ h)

end Descent

end FixedFieldTateDescent
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_injective_linearMap_rationalTateModule_fixedField_range_eq_iInf_ker_and_comp_eq.FixedFieldTateDescent"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_injective_linearMap_rationalTateModule_fixedField_range_eq_iInf_ker_and_comp_eq.FixedFieldTateDescent"

open FixedFieldTateDescent AlgebraicCurve IntermediateField in
theorem solution
    {k : Type} [Field k] [IsAlgClosed k] {F : Type} [Field F] [Algebra k F] [AlgebraicCurve.IsCurveOver k F]
    (G : Subgroup (F ≃ₐ[k] F)) [Finite G]
    [AlgebraicCurve.IsCurveOver k ↥(IntermediateField.fixedField G)]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ Φ : ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k ↥(IntermediateField.fixedField G)) →ₗ[ℚ_[ℓ]]
        ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k F),
      Function.Injective Φ ∧
      LinearMap.range Φ =
        ⨅ g : G, LinearMap.ker
          (ModularCurve.rationalGaloisRep ℓ (AlgebraicCurve.Pic0 k F) (F ≃ₐ[k] F) (g : F ≃ₐ[k] F) - 1) ∧
      ∀ (σ : F ≃ₐ[k] F)
        (τ : ↥(IntermediateField.fixedField G) ≃ₐ[k] ↥(IntermediateField.fixedField G)),
        (∀ y : ↥(IntermediateField.fixedField G), σ (y : F) = ((τ y : ↥(IntermediateField.fixedField G)) : F)) →
          Φ ∘ₗ ModularCurve.rationalGaloisRep ℓ (AlgebraicCurve.Pic0 k ↥(IntermediateField.fixedField G))
              (↥(IntermediateField.fixedField G) ≃ₐ[k] ↥(IntermediateField.fixedField G)) τ =
            ModularCurve.rationalGaloisRep ℓ (AlgebraicCurve.Pic0 k F) (F ≃ₐ[k] F) σ ∘ₗ Φ := by
  classical

  haveI : FiniteDimensional (fixedField G) F := finiteDimensional_fixedField G
  haveI : IsGalois (fixedField G) F := isGalois_fixedField G
  haveI : HasPrincipalDivisors k F := IsCurveOver.hasPrincipalDivisors
  haveI : SumRamificationInertia k (fixedField G) F :=
    ⟨fun v => Place.sum_ramificationIndex_mul_inertiaDeg v⟩
  letI : Fintype G := Fintype.ofFinite G
  haveI : Nonempty G := ⟨1⟩
  have H : Divisor.PushforwardNormFormula k (fixedField G) F :=
    Divisor.pushforwardNormFormula_of_isSeparable

  have hNι : ∀ x : Pic0 k (fixedField G),
      Pic0.pushforwardHom k (fixedField G) F H (Pic0.pullbackHom F x) = (Fintype.card G : ℤ) • x :=
    fun x => by rw [Pic0.pushforwardHom_pullbackHom H x, finrank_fixedField G]

  have hnat : ∀ (σ : F ≃ₐ[k] F) (τ : fixedField G ≃ₐ[k] fixedField G),
      (∀ y : fixedField G, σ (y : F) = ((τ y : fixedField G) : F)) →
      ∀ x : Pic0 k (fixedField G), Pic0.pullbackHom F (τ • x) = σ • Pic0.pullbackHom F x :=
    fun σ τ h x => (smul_pullbackHom_of_compat (K := k) (F := fixedField G) (F' := F) σ τ h x).symm

  have hone : ∀ g : G, ∀ y : fixedField G, (g : F ≃ₐ[k] F) (y : F) =
      (((1 : fixedField G ≃ₐ[k] fixedField G) y : fixedField G) : F) := fun g y => by
    rw [AlgEquiv.one_apply]
    exact (mem_fixedField_iff G (y : F)).1 y.2 g g.2

  have key := @descent ℓ _ (Pic0 k (fixedField G)) (Pic0 k F) _ _
    (fixedField G ≃ₐ[k] fixedField G) (F ≃ₐ[k] F) _ _ _ _ G _ _
    (fun g : G => (g : F ≃ₐ[k] F)) (Pic0.pullbackHom F) (Pic0.pushforwardHom k (fixedField G) F H)
  have key2 := key hNι
  have key3 := key2 (sum_smul_eq_pullbackHom_pushforwardHom G H)
    (fun σ τ => ∀ y : fixedField G, σ (y : F) = ((τ y : fixedField G) : F))
  have key4 := key3 hnat
  exact key4 hone

end S_AlgebraicCurve_Pic0_exists_injective_linearMap_rationalTateModule_fixedField_range_eq_iInf_ker_and_comp_eq
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_exists_injective_linearMap_rationalTateModule_fixedField_range_eq_iInf_ker_and_comp_eq (solution)
