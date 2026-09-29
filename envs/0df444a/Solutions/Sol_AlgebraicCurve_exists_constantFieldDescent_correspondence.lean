-- Prove2me | solution 1 for AlgebraicCurve.exists_constantFieldDescent_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/08cdd390-291f-5ff6-b187-e0e69c0ee364

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_constantFieldDescent_correspondence
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

p2m_open "Polynomial IntermediateField Cardinal AlgebraicCurve P2MW.S_AlgebraicCurve_exists_constantFieldDescent_correspondence.AlgebraicCurve"

universe u v w x

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along FiniteAlong IsCurveOver isCurveOver_of_transcendental_of_isSeparable finiteDimensional_adjoin_of_transcendental"
namespace DescentCorrespondenceProof
p2m_open "AlgebraicCurve"

theorem nonempty_ringHom_complex (k : Type u) [Field k] [CharZero k] [Countable k] :
    Nonempty (k →+* ℂ) := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℤ k
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℤ ℂ
  have htcard : #ℂ = #t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht
      (by simp) (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
  have hst : Cardinal.lift.{0} #s ≤ Cardinal.lift.{u} #t := by
    rw [← htcard, Cardinal.mk_complex]
    calc Cardinal.lift.{0} #s ≤ ℵ₀ := by simp
      _ ≤ Cardinal.lift.{u} 𝔠 := by simpa using Cardinal.aleph0_le_continuum
  obtain ⟨e⟩ := Cardinal.lift_mk_le'.1 hst
  have hv : AlgebraicIndependent ℤ (((↑) : t → ℂ) ∘ e) := ht.1.comp e e.injective
  set R₀ := Algebra.adjoin ℤ (Set.range ((↑) : s → k))
  let φ : R₀ →+* ℂ :=
    ((Subalgebra.val _).comp
      (hv.aevalEquiv.toAlgHom.comp hs.1.aevalEquiv.symm.toAlgHom)).toRingHom
  have hφ : Function.Injective φ := by
    change Function.Injective (fun z => (Subalgebra.val _) (hv.aevalEquiv (hs.1.aevalEquiv.symm z)))
    exact Subtype.val_injective.comp (hv.aevalEquiv.injective.comp hs.1.aevalEquiv.symm.injective)
  letI : Algebra R₀ ℂ := φ.toAlgebra
  haveI : Algebra.IsAlgebraic R₀ k := hs.isAlgebraic
  haveI : Module.IsTorsionFree R₀ ℂ := Module.isTorsionFree_iff_algebraMap_injective.2 hφ
  exact ⟨(IsAlgClosed.lift (R := R₀) (S := k) (M := ℂ)).toRingHom⟩

theorem isAlgebraic_of_rational_relation {k Φ : Type*} [Field k] [Field Φ] [Algebra k Φ]
    (x y : Φ) (J : Finset ℕ) (r s : ℕ → k[X])
    (hrel : ∑ j ∈ J, (aeval x (r j) / aeval x (s j)) * y ^ j = 0)
    (hne : ∃ j ∈ J, aeval x (r j) / aeval x (s j) ≠ 0) :
    IsAlgebraic k⟮x⟯ y := by
  classical
  have hmem : ∀ j, aeval x (r j) / aeval x (s j) ∈ k⟮x⟯ := fun j =>
    (mem_adjoin_simple_iff (F := k) _).2 ⟨r j, s j, rfl⟩
  let c : ℕ → k⟮x⟯ := fun j => ⟨_, hmem j⟩
  have hc : ∀ j, (c j : Φ) = aeval x (r j) / aeval x (s j) := fun j => rfl
  let q : k⟮x⟯[X] := ∑ j ∈ J, C (c j) * X ^ j
  have hcoeff : ∀ j ∈ J, q.coeff j = c j := by
    intro j hj
    simp only [q, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd hj h
  refine ⟨q, ?_, ?_⟩
  · obtain ⟨j₀, hj₀, hne⟩ := hne
    intro hq
    apply hne
    have := hcoeff j₀ hj₀
    rw [hq, coeff_zero] at this
    rw [← hc, ← this]; rfl
  · simp only [q, map_sum, map_mul, map_pow, aeval_C, aeval_X]
    convert hrel using 2
    rw [← hc]; rfl

theorem descent_abstract {k F : Type*} [Field k] [Field F] [Algebra k F]
    {x y : F} (hx : Transcendental k x) (J : Finset ℕ) (r s : ℕ → k[X])
    (hrel : ∑ j ∈ J, (aeval x (r j) / aeval x (s j)) * y ^ j = 0)
    (hne : ∃ j ∈ J, aeval x (r j) / aeval x (s j) ≠ 0) :
    ∃ x₀ y₀ : k⟮x, y⟯, (x₀ : F) = x ∧ (y₀ : F) = y ∧ Transcendental k x₀ ∧
      FiniteDimensional k⟮x₀⟯ k⟮x, y⟯ ∧ k⟮x₀, y₀⟯ = ⊤ := by
  classical
  set F₀ : IntermediateField k F := k⟮x, y⟯ with hF₀
  let x₀ : F₀ := ⟨x, subset_adjoin k _ (by simp)⟩
  let y₀ : F₀ := ⟨y, subset_adjoin k _ (by simp)⟩
  have hval : ∀ p : k[X], ((aeval x₀ p : F₀) : F) = aeval x p := by
    intro p
    rw [← IntermediateField.coe_val, ← aeval_algHom_apply]
    rfl
  have hx₀ : Transcendental k x₀ :=
    (transcendental_algebraMap_iff (R := k) (S := F₀) (A := F) (algebraMap F₀ F).injective).1 hx
  have hrel₀ : ∑ j ∈ J, (aeval x₀ (r j) / aeval x₀ (s j)) * y₀ ^ j = 0 := by
    apply (algebraMap F₀ F).injective
    rw [map_sum, map_zero, ← hrel]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_div₀, map_pow]
    change ((aeval x₀ (r j) : F₀) : F) / ((aeval x₀ (s j) : F₀) : F) * (y₀ : F) ^ j = _
    rw [hval, hval]
  have hne₀ : ∃ j ∈ J, aeval x₀ (r j) / aeval x₀ (s j) ≠ 0 := by
    obtain ⟨j, hj, hne⟩ := hne
    refine ⟨j, hj, fun h => hne ?_⟩
    have h' := congrArg (algebraMap F₀ F) h
    rw [map_div₀, map_zero] at h'
    change ((aeval x₀ (r j) : F₀) : F) / ((aeval x₀ (s j) : F₀) : F) = 0 at h'
    rwa [hval, hval] at h'
  have hyint : IsIntegral k⟮x₀⟯ y₀ :=
    (isAlgebraic_of_rational_relation x₀ y₀ J r s hrel₀ hne₀).isIntegral
  have htop₀ : k⟮x₀, y₀⟯ = (⊤ : IntermediateField k F₀) := by
    apply IntermediateField.lift_injective
    rw [lift_adjoin, lift_top]
    simp [Set.image_insert_eq, Set.image_singleton, x₀, y₀, hF₀]
  have hfin₀ : FiniteDimensional k⟮x₀⟯ F₀ := by
    have h1 : FiniteDimensional k⟮x₀⟯ k⟮x₀⟯⟮y₀⟯ := adjoin.finiteDimensional hyint
    have h2 : k⟮x₀⟯⟮y₀⟯ = ⊤ := by
      rw [← restrictScalars_eq_top_iff (K := k), adjoin_simple_adjoin_simple, htop₀]
    rw [h2] at h1
    exact LinearEquiv.finiteDimensional
      (IntermediateField.topEquiv (F := k⟮x₀⟯) (E := F₀)).toLinearEquiv
  exact ⟨x₀, y₀, rfl, rfl, hx₀, hfin₀, htop₀⟩

theorem aeval_mem_of_lift {K₀ K F : Type*} [Field K₀] [Field K] [Field F] [Algebra K₀ K]
    [Algebra K F] [Algebra K₀ F] [IsScalarTower K₀ K F]
    {M : IntermediateField K₀ F} {x : F} (hx : x ∈ M) {p : K[X]}
    (hp : ∃ p₀ : K₀[X], p₀.map (algebraMap K₀ K) = p) : aeval x p ∈ M := by
  obtain ⟨p₀, rfl⟩ := hp
  rw [aeval_map_algebraMap]
  have : aeval x p₀ = M.val (aeval (⟨x, hx⟩ : M) p₀) := by
    rw [← aeval_algHom_apply]; rfl
  rw [this]
  exact SetLike.coe_mem _

theorem aeval_mem_of_repr {K₀ K F : Type*} [Field K₀] [Field K] [Field F] [Algebra K₀ K]
    [Algebra K F] [Algebra K₀ F] [IsScalarTower K₀ K F]
    {M : IntermediateField K₀ F} {x y : F} (hx : x ∈ M) (hy : y ∈ M)
    (P : K⟮x⟯[X]) (rp sp : ℕ → K[X])
    (hrep : ∀ i, ((P.coeff i : K⟮x⟯) : F) = aeval x (rp i) / aeval x (sp i))
    (hr : ∀ i ∈ P.support, ∃ r₀ : K₀[X], r₀.map (algebraMap K₀ K) = rp i)
    (hs : ∀ i ∈ P.support, ∃ s₀ : K₀[X], s₀.map (algebraMap K₀ K) = sp i) :
    aeval y P ∈ M := by
  rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def]
  refine sum_mem fun i hi => mul_mem ?_ (pow_mem hy i)
  change ((P.coeff i : K⟮x⟯) : F) ∈ M
  rw [hrep i]
  exact div_mem (aeval_mem_of_lift hx (hr i hi)) (aeval_mem_of_lift hx (hs i hi))

section Tools

variable {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']

theorem finiteDimensional_adjoin_map {x : F} (hfin : FiniteDimensional k⟮x⟯ F)
    (ψ : F →ₐ[k] F') (hψfin : FiniteAlong k ψ) : FiniteDimensional k⟮ψ x⟯ F' := by
  letI : Algebra F F' := algebraAlong ψ
  haveI := isScalarTower_along ψ
  haveI : Module.Finite F F' := hψfin
  haveI := hfin
  set Kx : IntermediateField k F := k⟮x⟯ with hKx
  set Ky : IntermediateField k F' := k⟮ψ x⟯ with hKy
  have hmap : ∀ z ∈ Kx, ψ z ∈ Ky := by
    intro z hz
    have hKxy : Kx.map ψ = Ky := by
      rw [hKx, IntermediateField.adjoin_map, Set.image_singleton]
    rw [← hKxy]
    exact ⟨z, hz, rfl⟩
  let f : Kx →+* Ky := ψ.toRingHom.restrict Kx Ky hmap
  letI algKxF' : Algebra Kx F' := ((algebraMap F F').comp (algebraMap Kx F)).toAlgebra
  haveI : IsScalarTower Kx F F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite Kx F' := Module.Finite.trans F F'
  letI : Algebra Kx Ky := f.toAlgebra
  haveI : IsScalarTower Kx Ky F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite Kx Ky F'

noncomputable def restrictHom {k₀ : Type*} [Field k₀] [Algebra k₀ k] [Algebra k₀ F] [Algebra k₀ F']
    [IsScalarTower k₀ k F] [IsScalarTower k₀ k F']
    (σ : F →ₐ[k] F') (M : IntermediateField k₀ F) (N : IntermediateField k₀ F')
    (h : ∀ z ∈ M, σ z ∈ N) : M →ₐ[k₀] N where
  toFun z := ⟨σ (z : F), h z z.2⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' a b := Subtype.ext (map_mul σ (a : F) (b : F))
  map_zero' := Subtype.ext (map_zero σ)
  map_add' a b := Subtype.ext (map_add σ (a : F) (b : F))
  commutes' c := Subtype.ext (by
    show σ (algebraMap k₀ F c) = algebraMap k₀ F' c
    rw [IsScalarTower.algebraMap_apply k₀ k F, σ.commutes, ← IsScalarTower.algebraMap_apply])

@[scoped simp] theorem coe_restrictHom {k₀ : Type*} [Field k₀] [Algebra k₀ k] [Algebra k₀ F]
    [Algebra k₀ F'] [IsScalarTower k₀ k F] [IsScalarTower k₀ k F']
    (σ : F →ₐ[k] F') (M : IntermediateField k₀ F) (N : IntermediateField k₀ F')
    (h : ∀ z ∈ M, σ z ∈ N) (z : M) : ((restrictHom σ M N h z : N) : F') = σ (z : F) := rfl

theorem finiteAlong_of_isIntegral_of_adjoin_eq_top {A B : Type*} [Field A] [Field B]
    [Algebra k A] [Algebra k B] (φ : A →ₐ[k] B)
    (hφ : φ.toRingHom.IsIntegral) (T : Finset B)
    (hT : IntermediateField.adjoin k (T : Set B) = ⊤) : FiniteAlong k φ := by
  letI : Algebra A B := algebraAlong φ
  haveI := isScalarTower_along φ
  have hT' : IntermediateField.adjoin A (T : Set B) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hle : IntermediateField.adjoin k (T : Set B) ≤
        (IntermediateField.adjoin A (T : Set B)).restrictScalars k :=
      IntermediateField.adjoin_le_iff.2 (IntermediateField.subset_adjoin A _)
    have hy : y ∈ IntermediateField.adjoin k (T : Set B) := by rw [hT]; trivial
    exact hle hy
  haveI : FiniteDimensional A (IntermediateField.adjoin A (T : Set B)) :=
    IntermediateField.finiteDimensional_adjoin (fun t _ => hφ t)
  have e : (IntermediateField.adjoin A (T : Set B)) ≃ₗ[A] B :=
    ((IntermediateField.equivOfEq hT').trans IntermediateField.topEquiv).toLinearEquiv
  exact Module.Finite.equiv e

theorem finiteAlong_of_transcendental_image {A B : Type*} [Field A] [Field B]
    [Algebra k A] [Algebra k B] (σ₀ : A →ₐ[k] B)
    (T : Finset B) (hT : IntermediateField.adjoin k (T : Set B) = ⊤)
    (w : B) [FiniteDimensional k⟮w⟯ B]
    (a₀ : A) (ha₀ : Transcendental k (σ₀ a₀)) : FiniteAlong k σ₀ := by
  classical
  haveI hfd : FiniteDimensional k⟮σ₀ a₀⟯ B :=
    AlgebraicCurve.finiteDimensional_adjoin_of_transcendental w ha₀
  refine finiteAlong_of_isIntegral_of_adjoin_eq_top σ₀ ?_ T hT
  intro z

  have hzint : IsIntegral k⟮σ₀ a₀⟯ z := IsIntegral.of_finite _ z
  set m := minpoly k⟮σ₀ a₀⟯ z with hm
  have hmmonic : m.Monic := minpoly.monic hzint

  set m' : B[X] := m.map (algebraMap k⟮σ₀ a₀⟯ B) with hm'
  have hlifts : m' ∈ Polynomial.lifts σ₀.toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [hm', Polynomial.coeff_map]
    have hmapeq : (k⟮a₀⟯).map σ₀ = k⟮σ₀ a₀⟯ := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]
    have hc : ((m.coeff n : k⟮σ₀ a₀⟯) : B) ∈ (k⟮a₀⟯).map σ₀ := by
      rw [hmapeq]; exact (m.coeff n).2
    obtain ⟨d, -, hd⟩ := hc
    exact ⟨d, hd⟩
  have hm'monic : m'.Monic := hmmonic.map _
  obtain ⟨q, hqmap, -, hqmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hm'monic
  refine ⟨q, hqmonic, ?_⟩
  have h1 : Polynomial.eval₂ σ₀.toRingHom z q = (q.map σ₀.toRingHom).eval z := by
    rw [Polynomial.eval_map]
  rw [h1, hqmap, hm', Polynomial.eval_map, ← Polynomial.aeval_def]
  exact minpoly.aeval _ z

end Tools

end AlgebraicCurve.DescentCorrespondenceProof
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_constantFieldDescent_correspondence.AlgebraicCurve P2MW.S_AlgebraicCurve_exists_constantFieldDescent_correspondence.AlgebraicCurve.DescentCorrespondenceProof"
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_constantFieldDescent_correspondence.AlgebraicCurve"

open AlgebraicCurve.DescentCorrespondenceProof in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {ι : Type w} [Finite ι] (F' : ι → Type x) [∀ i, Field (F' i)] [∀ i, Algebra K (F' i)]
    (φ ψ : ∀ i, F →ₐ[K] F' i)
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral) (hfin : ∀ i, FiniteAlong K (ψ i)) :
    ∃ (K₀ : Type u) (F₀ : Type v) (F'₀ : ι → Type x)
      (_ : Field K₀) (_ : Field F₀) (_ : ∀ i, Field (F'₀ i))
      (_ : Algebra K₀ K) (_ : Algebra K₀ ℂ) (_ : IsAlgClosed K₀) (_ : Countable K₀)
      (_ : Algebra K₀ F₀) (_ : Algebra F₀ F) (_ : Algebra K₀ F)
      (_ : IsScalarTower K₀ K F) (_ : IsScalarTower K₀ F₀ F) (_ : IsCurveOver K₀ F₀)
      (_ : ∀ i, Algebra K₀ (F'₀ i)) (_ : ∀ i, Algebra (F'₀ i) (F' i)) (_ : ∀ i, Algebra K₀ (F' i))
      (_ : ∀ i, IsScalarTower K₀ K (F' i)) (_ : ∀ i, IsScalarTower K₀ (F'₀ i) (F' i))
      (_ : ∀ i, IsCurveOver K₀ (F'₀ i))
      (φ₀ ψ₀ : ∀ i, F₀ →ₐ[K₀] F'₀ i),
      (∃ x : F₀, Transcendental K₀ x ∧
        FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀) ∧
      IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤ ∧
      (∀ i, ∃ x : F'₀ i, Transcendental K₀ x ∧
        FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set (F'₀ i))) (F'₀ i)) ∧
      (∀ i, IntermediateField.adjoin K (Set.range (algebraMap (F'₀ i) (F' i))) = ⊤) ∧
      (∀ i (f : F₀), φ i (algebraMap F₀ F f) = algebraMap (F'₀ i) (F' i) (φ₀ i f)) ∧
      (∀ i (f : F₀), ψ i (algebraMap F₀ F f) = algebraMap (F'₀ i) (F' i) (ψ₀ i f)) ∧
      (∀ i, FiniteAlong K₀ (φ₀ i)) ∧ (∀ i, FiniteAlong K₀ (ψ₀ i)) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨x, hx, hxfin⟩ := hfg
  haveI := hxfin
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  haveI : ∀ i, CharZero (F' i) := fun i =>
    charZero_of_injective_algebraMap (algebraMap K (F' i)).injective

  haveI : PerfectField K⟮x⟯ := PerfectField.ofCharZero
  haveI : Algebra.IsSeparable K⟮x⟯ F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨y, hy⟩ := Field.exists_primitive_element K⟮x⟯ F
  have hxy : K⟮x, y⟯ = ⊤ := by
    rw [← adjoin_simple_adjoin_simple, hy, restrictScalars_top]
  obtain ⟨q, hq0, hqy⟩ : IsAlgebraic K⟮x⟯ y := Algebra.IsAlgebraic.isAlgebraic y
  have hcoef : ∀ j, ∃ r s : K[X], (q.coeff j : F) = aeval x r / aeval x s := fun j =>
    (mem_adjoin_simple_iff (F := K) _).1 (q.coeff j).2
  choose r s hrs using hcoef
  set J := q.support with hJ
  have hrel : ∑ j ∈ J, (aeval x (r j) / aeval x (s j)) * y ^ j = 0 := by
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def] at hqy
    simp_rw [← hrs]
    exact hqy
  have hne : ∃ j ∈ J, aeval x (r j) / aeval x (s j) ≠ 0 := by
    obtain ⟨j, hj⟩ := Polynomial.support_nonempty.2 hq0
    refine ⟨j, hj, ?_⟩
    rw [← hrs]
    exact fun h => (mem_support_iff.1 hj) (ZeroMemClass.coe_eq_zero.1 h)

  have hxi : ∀ i, Transcendental K (ψ i x) := fun i h =>
    hx ((isAlgebraic_algHom_iff (ψ i) (ψ i).toRingHom.injective).mp h)
  haveI hfini : ∀ i, FiniteDimensional K⟮ψ i x⟯ (F' i) := fun i =>
    finiteDimensional_adjoin_map hxfin (ψ i) (hfin i)
  haveI : ∀ i, PerfectField K⟮ψ i x⟯ := fun i => PerfectField.ofCharZero
  haveI : ∀ i, Algebra.IsSeparable K⟮ψ i x⟯ (F' i) := fun i =>
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hprim : ∀ i, ∃ u : F' i, K⟮ψ i x⟯⟮u⟯ = ⊤ := fun i =>
    Field.exists_primitive_element K⟮ψ i x⟯ (F' i)
  choose u hu using hprim
  have hxu : ∀ i, K⟮ψ i x, u i⟯ = ⊤ := fun i => by
    rw [← adjoin_simple_adjoin_simple, hu i, restrictScalars_top]

  have halg : ∀ i, IsAlgebraic K⟮ψ i x⟯ (u i) := fun i => Algebra.IsAlgebraic.isAlgebraic (u i)
  choose qi hqi0 hqiu using halg
  have hcoefi : ∀ i j, ∃ r' s' : K[X], ((qi i).coeff j : F' i) = aeval (ψ i x) r' / aeval (ψ i x) s' :=
    fun i j => (mem_adjoin_simple_iff (F := K) _).1 ((qi i).coeff j).2
  choose ri si hrsi using hcoefi
  have hreli : ∀ i, ∑ j ∈ (qi i).support,
      (aeval (ψ i x) (ri i j) / aeval (ψ i x) (si i j)) * u i ^ j = 0 := fun i => by
    have h := hqiu i
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def] at h
    simp_rw [← hrsi i]
    exact h
  have hnei : ∀ i, ∃ j ∈ (qi i).support,
      aeval (ψ i x) (ri i j) / aeval (ψ i x) (si i j) ≠ 0 := fun i => by
    obtain ⟨j, hj⟩ := Polynomial.support_nonempty.2 (hqi0 i)
    refine ⟨j, hj, ?_⟩
    rw [← hrsi i]
    exact fun h => (mem_support_iff.1 hj) (ZeroMemClass.coe_eq_zero.1 h)

  set tt : ∀ i, Fin 3 → F' i := fun i => ![φ i x, φ i y, ψ i y] with htt
  have hrepr : ∀ i (z : F' i), ∃ P Q : K⟮ψ i x⟯[X], z = aeval (u i) P / aeval (u i) Q :=
    fun i z => (mem_adjoin_simple_iff (F := K⟮ψ i x⟯) _).1 (by rw [hu i]; exact mem_top)
  choose P Q hPQ using hrepr
  have hcoefP : ∀ i (z : F' i) (n : ℕ), ∃ r' s' : K[X],
      (((P i z).coeff n : K⟮ψ i x⟯) : F' i) = aeval (ψ i x) r' / aeval (ψ i x) s' :=
    fun i z n => (mem_adjoin_simple_iff (F := K) _).1 ((P i z).coeff n).2
  have hcoefQ : ∀ i (z : F' i) (n : ℕ), ∃ r' s' : K[X],
      (((Q i z).coeff n : K⟮ψ i x⟯) : F' i) = aeval (ψ i x) r' / aeval (ψ i x) s' :=
    fun i z n => (mem_adjoin_simple_iff (F := K) _).1 ((Q i z).coeff n).2
  choose rp sp hrsp using hcoefP
  choose rq sq hrsq using hcoefQ

  let C₁ : Set K := ⋃ j ∈ J, (((r j).coeffs ∪ (s j).coeffs : Finset K) : Set K)
  let C₂ : Set K := ⋃ i : ι, ⋃ j ∈ (qi i).support,
    (((ri i j).coeffs ∪ (si i j).coeffs : Finset K) : Set K)
  let C₃ : Set K := ⋃ i : ι, ⋃ l : Fin 3,
    ⋃ n ∈ ((P i (tt i l)).support ∪ (Q i (tt i l)).support),
      (((rp i (tt i l) n).coeffs ∪ (sp i (tt i l) n).coeffs ∪
        ((rq i (tt i l) n).coeffs ∪ (sq i (tt i l) n).coeffs) : Finset K) : Set K)
  let C : Set K := C₁ ∪ (C₂ ∪ C₃)
  have hCfin : C.Finite := by
    refine Set.Finite.union ?_ (Set.Finite.union ?_ ?_)
    · exact Set.Finite.biUnion J.finite_toSet fun j _ => Finset.finite_toSet _
    · exact Set.finite_iUnion fun i =>
        Set.Finite.biUnion (Finset.finite_toSet _) fun j _ => Finset.finite_toSet _
    · exact Set.finite_iUnion fun i => Set.finite_iUnion fun l =>
        Set.Finite.biUnion (Finset.finite_toSet _) fun n _ => Finset.finite_toSet _
  let L : Subfield K := Subfield.closure C
  let K₀ : IntermediateField L K := algebraicClosure L K
  haveI : IsAlgClosed K₀ := IsAlgClosure.isAlgClosed L
  haveI : Countable L := by
    haveI : Countable C := hCfin.countable.to_subtype
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Subfield.cardinalMk_closure_le_max C).trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  haveI : Countable K₀ := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Algebra.IsAlgebraic.cardinalMk_le_max L K₀).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl)
  haveI : CharZero K₀ := charZero_of_injective_algebraMap (algebraMap L K₀).injective
  have hCK₀ : C ⊆ Set.range (algebraMap K₀ K) := by
    intro c hc
    exact ⟨⟨c, K₀.algebraMap_mem ⟨c, Subfield.subset_closure hc⟩⟩, rfl⟩

  have hlift : ∀ p : K[X], (p.coeffs : Set K) ⊆ C →
      ∃ p₀ : K₀[X], p₀.map (algebraMap K₀ K) = p := fun p hp =>
    (mem_lifts _).1 ((lifts_iff_coeffs_subset_range _).2 (hp.trans hCK₀))

  have hrC : ∀ j ∈ J, ((r j).coeffs : Set K) ⊆ C := fun j hj c hc =>
    Set.mem_union_left _ (Set.mem_biUnion hj (by simp [hc]))
  have hsC : ∀ j ∈ J, ((s j).coeffs : Set K) ⊆ C := fun j hj c hc =>
    Set.mem_union_left _ (Set.mem_biUnion hj (by simp [hc]))
  have hr₀ : ∀ j, ∃ p₀ : K₀[X], j ∈ J → p₀.map (algebraMap K₀ K) = r j := fun j => by
    by_cases hj : j ∈ J
    · obtain ⟨p₀, hp₀⟩ := hlift _ (hrC j hj); exact ⟨p₀, fun _ => hp₀⟩
    · exact ⟨0, fun h => absurd h hj⟩
  have hs₀ : ∀ j, ∃ p₀ : K₀[X], j ∈ J → p₀.map (algebraMap K₀ K) = s j := fun j => by
    by_cases hj : j ∈ J
    · obtain ⟨p₀, hp₀⟩ := hlift _ (hsC j hj); exact ⟨p₀, fun _ => hp₀⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose r₀ hr₀ using hr₀
  choose s₀ hs₀ using hs₀
  have hrel' : ∑ j ∈ J, (aeval x (r₀ j) / aeval x (s₀ j)) * y ^ j = 0 := by
    rw [← hrel]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← aeval_map_algebraMap K x (r₀ j), ← aeval_map_algebraMap K x (s₀ j), hr₀ j hj, hs₀ j hj]
  have hne' : ∃ j ∈ J, aeval x (r₀ j) / aeval x (s₀ j) ≠ 0 := by
    obtain ⟨j, hj, hne⟩ := hne
    refine ⟨j, hj, ?_⟩
    rwa [← aeval_map_algebraMap K x (r₀ j), ← aeval_map_algebraMap K x (s₀ j), hr₀ j hj,
      hs₀ j hj]

  have hriC : ∀ i, ∀ j ∈ (qi i).support, ((ri i j).coeffs : Set K) ⊆ C ∧
      ((si i j).coeffs : Set K) ⊆ C := by
    intro i j hj
    have hsub : (((ri i j).coeffs ∪ (si i j).coeffs : Finset K) : Set K) ⊆ C := by
      intro c hc
      refine Set.mem_union_right _ (Set.mem_union_left _ ?_)
      exact Set.mem_iUnion.2 ⟨i, Set.mem_biUnion (Finset.mem_coe.2 hj) hc⟩
    refine ⟨?_, ?_⟩ <;> intro c hc <;> apply hsub <;> simp [hc]
  have hri₀ : ∀ i j, ∃ p₀ : K₀[X], j ∈ (qi i).support → p₀.map (algebraMap K₀ K) = ri i j :=
    fun i j => by
    by_cases hj : j ∈ (qi i).support
    · obtain ⟨p₀, hp₀⟩ := hlift _ (hriC i j hj).1; exact ⟨p₀, fun _ => hp₀⟩
    · exact ⟨0, fun h => absurd h hj⟩
  have hsi₀ : ∀ i j, ∃ p₀ : K₀[X], j ∈ (qi i).support → p₀.map (algebraMap K₀ K) = si i j :=
    fun i j => by
    by_cases hj : j ∈ (qi i).support
    · obtain ⟨p₀, hp₀⟩ := hlift _ (hriC i j hj).2; exact ⟨p₀, fun _ => hp₀⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose ri₀ hri₀ using hri₀
  choose si₀ hsi₀ using hsi₀
  have hreli' : ∀ i, ∑ j ∈ (qi i).support,
      (aeval (ψ i x) (ri₀ i j) / aeval (ψ i x) (si₀ i j)) * u i ^ j = 0 := fun i => by
    rw [← hreli i]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← aeval_map_algebraMap K (ψ i x) (ri₀ i j), ← aeval_map_algebraMap K (ψ i x) (si₀ i j),
      hri₀ i j hj, hsi₀ i j hj]
  have hnei' : ∀ i, ∃ j ∈ (qi i).support,
      aeval (ψ i x) (ri₀ i j) / aeval (ψ i x) (si₀ i j) ≠ 0 := fun i => by
    obtain ⟨j, hj, hne⟩ := hnei i
    refine ⟨j, hj, ?_⟩
    rwa [← aeval_map_algebraMap K (ψ i x) (ri₀ i j), ← aeval_map_algebraMap K (ψ i x) (si₀ i j),
      hri₀ i j hj, hsi₀ i j hj]

  have htC : ∀ i (l : Fin 3), ∀ n ∈ (P i (tt i l)).support ∪ (Q i (tt i l)).support,
      ((rp i (tt i l) n).coeffs : Set K) ⊆ C ∧ ((sp i (tt i l) n).coeffs : Set K) ⊆ C ∧
        ((rq i (tt i l) n).coeffs : Set K) ⊆ C ∧ ((sq i (tt i l) n).coeffs : Set K) ⊆ C := by
    intro i l n hn
    have hsub : (((rp i (tt i l) n).coeffs ∪ (sp i (tt i l) n).coeffs ∪
        ((rq i (tt i l) n).coeffs ∪ (sq i (tt i l) n).coeffs) : Finset K) : Set K) ⊆ C := by
      intro c hc
      refine Set.mem_union_right _ (Set.mem_union_right _ ?_)
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨l, Set.mem_biUnion (Finset.mem_coe.2 hn) hc⟩⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro c hc <;> apply hsub <;> simp [hc]

  obtain ⟨x₀, y₀, hx₀x, hy₀y, hx₀, hfin₀, htop₀⟩ :=
    descent_abstract (hx.of_tower_top K₀) J r₀ s₀ hrel' hne'

  have hdesc' : ∀ i, ∃ x₀' u₀' : K₀⟮ψ i x, u i⟯, (x₀' : F' i) = ψ i x ∧ (u₀' : F' i) = u i ∧
      Transcendental K₀ x₀' ∧ FiniteDimensional K₀⟮x₀'⟯ K₀⟮ψ i x, u i⟯ ∧ K₀⟮x₀', u₀'⟯ = ⊤ :=
    fun i => descent_abstract ((hxi i).of_tower_top K₀) _ (ri₀ i) (si₀ i) (hreli' i) (hnei' i)
  choose x₀' u₀' hx₀'x hu₀'u hx₀' hfin₀' htop₀' using hdesc'

  have hxM : x ∈ K₀⟮x, y⟯ := subset_adjoin K₀ _ (by simp)
  have hyM : y ∈ K₀⟮x, y⟯ := subset_adjoin K₀ _ (by simp)
  have hxiM : ∀ i, ψ i x ∈ K₀⟮ψ i x, u i⟯ := fun i => subset_adjoin K₀ _ (by simp)
  have huiM : ∀ i, u i ∈ K₀⟮ψ i x, u i⟯ := fun i => subset_adjoin K₀ _ (by simp)

  have httM : ∀ i (l : Fin 3), tt i l ∈ K₀⟮ψ i x, u i⟯ := by
    intro i l
    rw [hPQ i (tt i l)]
    refine div_mem ?_ ?_
    · exact aeval_mem_of_repr (hxiM i) (huiM i) (P i (tt i l)) (rp i (tt i l)) (sp i (tt i l))
        (hrsp i (tt i l))
        (fun n hn => hlift _ (htC i l n (Finset.mem_union_left _ hn)).1)
        (fun n hn => hlift _ (htC i l n (Finset.mem_union_left _ hn)).2.1)
    · exact aeval_mem_of_repr (hxiM i) (huiM i) (Q i (tt i l)) (rq i (tt i l)) (sq i (tt i l))
        (hrsq i (tt i l))
        (fun n hn => hlift _ (htC i l n (Finset.mem_union_right _ hn)).2.2.1)
        (fun n hn => hlift _ (htC i l n (Finset.mem_union_right _ hn)).2.2.2)
  have hφxM : ∀ i, φ i x ∈ K₀⟮ψ i x, u i⟯ := fun i => by simpa [htt] using httM i 0
  have hφyM : ∀ i, φ i y ∈ K₀⟮ψ i x, u i⟯ := fun i => by simpa [htt] using httM i 1
  have hψyM : ∀ i, ψ i y ∈ K₀⟮ψ i x, u i⟯ := fun i => by simpa [htt] using httM i 2

  have hmapφ : ∀ i, ∀ z ∈ K₀⟮x, y⟯, φ i z ∈ K₀⟮ψ i x, u i⟯ := by
    intro i
    have hle : K₀⟮x, y⟯ ≤ K₀⟮ψ i x, u i⟯.comap ((φ i).restrictScalars K₀) := by
      rw [adjoin_le_iff]
      rintro z (rfl | h)
      · exact hφxM i
      · rw [Set.mem_singleton_iff.1 h]; exact hφyM i
    exact fun z hz => hle hz
  have hmapψ : ∀ i, ∀ z ∈ K₀⟮x, y⟯, ψ i z ∈ K₀⟮ψ i x, u i⟯ := by
    intro i
    have hle : K₀⟮x, y⟯ ≤ K₀⟮ψ i x, u i⟯.comap ((ψ i).restrictScalars K₀) := by
      rw [adjoin_le_iff]
      rintro z (rfl | h)
      · exact hxiM i
      · rw [Set.mem_singleton_iff.1 h]; exact hψyM i
    exact fun z hz => hle hz
  set φ₀ : ∀ i, K₀⟮x, y⟯ →ₐ[K₀] K₀⟮ψ i x, u i⟯ := fun i => restrictHom (φ i) K₀⟮x, y⟯ K₀⟮ψ i x, u i⟯ (hmapφ i) with hφ₀
  set ψ₀ : ∀ i, K₀⟮x, y⟯ →ₐ[K₀] K₀⟮ψ i x, u i⟯ := fun i => restrictHom (ψ i) K₀⟮x, y⟯ K₀⟮ψ i x, u i⟯ (hmapψ i) with hψ₀

  set xF : K₀⟮x, y⟯ := ⟨x, hxM⟩ with hxF
  have hxFtr : ∀ i, Transcendental K₀ (φ₀ i xF) := fun i h => by
    have h' : IsAlgebraic K₀ (φ i x) :=
      (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom K₀ K₀⟮ψ i x, u i⟯ (F' i))
        (algebraMap K₀⟮ψ i x, u i⟯ (F' i)).injective).2 h
    have hφx : Transcendental K (φ i x) := fun h'' =>
      hx ((isAlgebraic_algHom_iff (φ i) (φ i).toRingHom.injective).mp h'')
    exact (hφx.of_tower_top K₀) h'
  have hxFtrψ : ∀ i, Transcendental K₀ (ψ₀ i xF) := fun i h => by
    have h' : IsAlgebraic K₀ (ψ i x) :=
      (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom K₀ K₀⟮ψ i x, u i⟯ (F' i))
        (algebraMap K₀⟮ψ i x, u i⟯ (F' i)).injective).2 h
    exact ((hxi i).of_tower_top K₀) h'

  have hgen₀' : ∀ i, IntermediateField.adjoin K₀
      (({x₀' i, u₀' i} : Finset K₀⟮ψ i x, u i⟯) : Set K₀⟮ψ i x, u i⟯) = ⊤ := fun i => by
    rw [Finset.coe_insert, Finset.coe_singleton]
    exact htop₀' i
  haveI : ∀ i, FiniteDimensional K₀⟮x₀' i⟯ K₀⟮ψ i x, u i⟯ := hfin₀'
  have hfinφ₀ : ∀ i, FiniteAlong K₀ (φ₀ i) := fun i =>
    finiteAlong_of_transcendental_image (φ₀ i) _ (hgen₀' i) (x₀' i) xF (hxFtr i)
  have hfinψ₀ : ∀ i, FiniteAlong K₀ (ψ₀ i) := fun i =>
    finiteAlong_of_transcendental_image (ψ₀ i) _ (hgen₀' i) (x₀' i) xF (hxFtrψ i)

  haveI : CharZero K₀⟮x, y⟯ := charZero_of_injective_algebraMap (algebraMap K₀ K₀⟮x, y⟯).injective
  haveI : Algebra.IsSeparable K₀⟮x₀⟯ K₀⟮x, y⟯ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hC₀ : IsCurveOver K₀ K₀⟮x, y⟯ :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable K₀ K₀⟮x, y⟯ x₀ hx₀ hfin₀ inferInstance
  haveI : ∀ i, CharZero K₀⟮ψ i x, u i⟯ := fun i =>
    charZero_of_injective_algebraMap (algebraMap K₀ K₀⟮ψ i x, u i⟯).injective
  haveI : ∀ i, Algebra.IsSeparable K₀⟮x₀' i⟯ K₀⟮ψ i x, u i⟯ := fun i =>
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hC₀' : ∀ i, IsCurveOver K₀ K₀⟮ψ i x, u i⟯ := fun i =>
    AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable K₀ K₀⟮ψ i x, u i⟯ (x₀' i) (hx₀' i)
      (hfin₀' i) inferInstance
  have hgenF : IntermediateField.adjoin K (Set.range (algebraMap K₀⟮x, y⟯ F)) = ⊤ := by
    rw [eq_top_iff, ← hxy]
    refine adjoin.mono K _ _ ?_
    rintro z (rfl | h)
    · exact ⟨⟨z, hxM⟩, rfl⟩
    · rw [Set.mem_singleton_iff.1 h]; exact ⟨⟨y, hyM⟩, rfl⟩
  have hgenF' : ∀ i, IntermediateField.adjoin K (Set.range (algebraMap K₀⟮ψ i x, u i⟯ (F' i))) = ⊤ := by
    intro i
    rw [eq_top_iff, ← hxu i]
    refine adjoin.mono K _ _ ?_
    rintro z (rfl | h)
    · exact ⟨⟨ψ i x, hxiM i⟩, rfl⟩
    · rw [Set.mem_singleton_iff.1 h]; exact ⟨⟨u i, huiM i⟩, rfl⟩

  obtain ⟨χ⟩ := nonempty_ringHom_complex K₀
  refine ⟨K₀, K₀⟮x, y⟯, fun i => K₀⟮ψ i x, u i⟯, inferInstance, inferInstance, inferInstance, inferInstance,
    χ.toAlgebra, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hC₀, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hC₀', φ₀, ψ₀, ⟨x₀, hx₀, hfin₀⟩, hgenF, fun i => ⟨x₀' i, hx₀' i, hfin₀' i⟩,
    hgenF', fun i f => rfl, fun i f => rfl, hfinφ₀, hfinψ₀⟩

end S_AlgebraicCurve_exists_constantFieldDescent_correspondence
end P2MW
export P2MW.S_AlgebraicCurve_exists_constantFieldDescent_correspondence (solution)
