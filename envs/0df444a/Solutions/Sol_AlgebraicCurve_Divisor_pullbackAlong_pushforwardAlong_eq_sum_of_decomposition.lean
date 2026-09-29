-- Prove2me | solution 1 for AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_sum_of_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/958b5014-4a6b-5018-b9b1-4b33290dfa69

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_sum_of_decomposition
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"
set_option autoImplicit false

open AlgebraicCurve
open scoped TensorProduct

noncomputable section

namespace PlaceExchange

private theorem algebra_adjoin_eq_top_of_intermediateField {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E] [FiniteDimensional F E]
    {S : Set E} (hS : IntermediateField.adjoin K S = ⊤) : Algebra.adjoin F S = ⊤ := by
  have hS' : IntermediateField.adjoin F S = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ IntermediateField.adjoin K S := hS ▸ IntermediateField.mem_top
    have hle : IntermediateField.adjoin K S ≤ (IntermediateField.adjoin F S).restrictScalars K :=
      IntermediateField.adjoin_le_iff.mpr fun y hy => IntermediateField.subset_adjoin F S hy
    exact hle hx
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun x _ => Algebra.IsAlgebraic.isAlgebraic x), hS', IntermediateField.top_toSubalgebra]

private theorem det_pi_hetero {R : Type*} [CommRing R] : ∀ {n : ℕ} (Z : Fin n → Type*)
    [∀ i, AddCommGroup (Z i)] [∀ i, Module R (Z i)]
    [∀ i, Module.Free R (Z i)] [∀ i, Module.Finite R (Z i)]
    (f : ∀ i, Z i →ₗ[R] Z i),
    LinearMap.det (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i)
      = ∏ i, LinearMap.det (f i)
  | 0, Z, _, _, _, _, f => by
    haveI : Subsingleton (∀ i : Fin 0, Z i) :=
      ⟨fun a b => funext fun i => i.elim0⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    exact LinearMap.det_eq_one_of_subsingleton _
  | (n + 1), Z, _, _, _, _, f => by
    have hconj : LinearMap.pi (fun i => f i ∘ₗ LinearMap.proj i)
        = (Fin.consLinearEquiv R Z).toLinearMap ∘ₗ
          (LinearMap.prodMap (f 0)
            (LinearMap.pi fun i : Fin n => f i.succ ∘ₗ LinearMap.proj i)) ∘ₗ
          (Fin.consLinearEquiv R Z).symm.toLinearMap := by
      apply LinearMap.ext
      intro x
      funext j
      refine Fin.cases ?_ (fun i => ?_) j <;>
        simp [Fin.consLinearEquiv, Fin.consEquiv, LinearMap.pi_apply,
          LinearMap.prodMap_apply, Fin.cons_zero, Fin.cons_succ, Fin.tail]
    rw [hconj]
    have h1 : LinearMap.det ((Fin.consLinearEquiv R Z).toLinearMap ∘ₗ
          (LinearMap.prodMap (f 0)
            (LinearMap.pi fun i : Fin n => f i.succ ∘ₗ LinearMap.proj i)) ∘ₗ
          (Fin.consLinearEquiv R Z).symm.toLinearMap)
        = LinearMap.det (LinearMap.prodMap (f 0)
            (LinearMap.pi fun i : Fin n => f i.succ ∘ₗ LinearMap.proj i)) :=
      LinearMap.det_conj _ (Fin.consLinearEquiv R Z)
    rw [h1, LinearMap.det_prodMap, det_pi_hetero]
    exact (Fin.prod_univ_succ fun i => LinearMap.det (f i)).symm

private theorem algebraMap_norm_eq_prod_norm_of_decomposition
    {F F₁ F₂ : Type*} [Field F] [Field F₁] [Field F₂]
    [Algebra F F₁] [Algebra F F₂]
    [FiniteDimensional F F₁] [FiniteDimensional F F₂]
    (n : ℕ) (Z : Fin n → Type*) [∀ i, Field (Z i)]
    [∀ i, Algebra F (Z i)] [∀ i, Algebra F₁ (Z i)] [∀ i, Algebra F₂ (Z i)]
    [∀ i, IsScalarTower F F₁ (Z i)] [∀ i, IsScalarTower F F₂ (Z i)]
    [∀ i, FiniteDimensional F₁ (Z i)]
    (hgen : ∀ i, Algebra.adjoin F
      (Set.range (algebraMap F₁ (Z i)) ∪ Set.range (algebraMap F₂ (Z i))) = ⊤)
    (hdeg : ∑ i, Module.finrank F₁ (Z i) = Module.finrank F F₂)
    (hsep : ∀ i j, i ≠ j → ∃ t : F₂ ⊗[F] F₁,
      Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom F F₂ (Z i))
        (IsScalarTower.toAlgHom F F₁ (Z i)) t = 0 ∧
      Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom F F₂ (Z j))
        (IsScalarTower.toAlgHom F F₁ (Z j)) t ≠ 0)
    (g : F₁) :
    algebraMap F F₂ (Algebra.norm F g) = ∏ i, Algebra.norm F₂ (algebraMap F₁ (Z i) g) := by
  classical
  haveI : ∀ i, FiniteDimensional F (Z i) := fun i => Module.Finite.trans F₁ (Z i)
  haveI : ∀ i, FiniteDimensional F₂ (Z i) := fun i => FiniteDimensional.right F F₂ (Z i)

  let η : ∀ i, (F₂ ⊗[F] F₁ →ₐ[F₂] Z i) := fun i =>
    Algebra.TensorProduct.lift (Algebra.ofId F₂ (Z i)) (IsScalarTower.toAlgHom F F₁ (Z i))
      (fun _ _ => Commute.all _ _)
  have hηtmul : ∀ (i) (c : F₂) (x : F₁),
      η i (c ⊗ₜ[F] x) = algebraMap F₂ (Z i) c * algebraMap F₁ (Z i) x := by
    intro i c x
    simp [η, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
  have hηsurj : ∀ i, Function.Surjective (η i) := by
    intro i z
    have hz : z ∈ Algebra.adjoin F
        (Set.range (algebraMap F₁ (Z i)) ∪ Set.range (algebraMap F₂ (Z i))) := by
      rw [hgen i]; trivial
    have hle : Algebra.adjoin F
        (Set.range (algebraMap F₁ (Z i)) ∪ Set.range (algebraMap F₂ (Z i)))
        ≤ ((η i).range.restrictScalars F) := by
      rw [Algebra.adjoin_le_iff]
      rintro w (⟨x, rfl⟩ | ⟨c, rfl⟩)
      · exact ⟨1 ⊗ₜ[F] x, by show η i _ = _; rw [hηtmul]; simp⟩
      · exact ⟨c ⊗ₜ[F] 1, by show η i _ = _; rw [hηtmul]; simp⟩
    exact hle hz

  have hkmax : ∀ i, (RingHom.ker (η i)).IsMaximal := fun i =>
    RingHom.ker_isMaximal_of_surjective _ (hηsurj i)
  have hηF : ∀ (i) (t : F₂ ⊗[F] F₁),
      Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom F F₂ (Z i))
        (IsScalarTower.toAlgHom F F₁ (Z i)) t = η i t := by
    intro i t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c x => rw [Algebra.TensorProduct.productMap_apply_tmul, hηtmul]; rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  have hkne : ∀ i j, i ≠ j → RingHom.ker (η i) ≠ RingHom.ker (η j) := by
    intro i j hij hkk
    obtain ⟨t, h0, hne⟩ := hsep i j hij
    apply hne
    rw [hηF] at h0 ⊢
    rw [← RingHom.mem_ker, ← hkk, RingHom.mem_ker]
    exact h0
  have hcop : Pairwise fun i j => IsCoprime (RingHom.ker (η i)) (RingHom.ker (η j)) := by
    intro i j hij
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne (hkmax i) (hkmax j) (hkne i j hij)

  let Ψ : F₂ ⊗[F] F₁ →ₐ[F₂] (∀ i, Z i) := Pi.algHom _ _ η
  have hΨapp : ∀ (x) (i), Ψ x i = η i x := fun _ _ => rfl
  have hΨsurj : Function.Surjective Ψ := by
    intro z
    choose y hy using fun i => hηsurj i (z i)
    obtain ⟨xq, hxq⟩ := Ideal.quotientInfToPiQuotient_surj hcop
      (fun i => Ideal.Quotient.mk (RingHom.ker (η i)) (y i))
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xq
    refine ⟨x, ?_⟩
    funext i
    have hxi := congrFun hxq i
    have hmk : Ideal.Quotient.mk (RingHom.ker (η i)) x
        = Ideal.Quotient.mk (RingHom.ker (η i)) (y i) := hxi
    have hdiff : x - y i ∈ RingHom.ker (η i) := by
      exact Ideal.Quotient.eq.mp hmk
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hdiff
    rw [hΨapp, hdiff, hy i]

  have hdim : Module.finrank F₂ (F₂ ⊗[F] F₁) = Module.finrank F₂ (∀ i, Z i) := by
    rw [Module.finrank_baseChange, Module.finrank_pi_fintype]
    have htower : ∀ i, Module.finrank F F₂ * Module.finrank F₂ (Z i)
        = Module.finrank F F₁ * Module.finrank F₁ (Z i) := by
      intro i
      rw [Module.finrank_mul_finrank, Module.finrank_mul_finrank]
    have hmul : Module.finrank F F₂ * ∑ i, Module.finrank F₂ (Z i)
        = Module.finrank F F₂ * Module.finrank F F₁ := by
      rw [Finset.mul_sum]
      calc ∑ i, Module.finrank F F₂ * Module.finrank F₂ (Z i)
          = ∑ i, Module.finrank F F₁ * Module.finrank F₁ (Z i) :=
            Finset.sum_congr rfl fun i _ => htower i
        _ = Module.finrank F F₁ * ∑ i, Module.finrank F₁ (Z i) := by rw [← Finset.mul_sum]
        _ = Module.finrank F F₁ * Module.finrank F F₂ := by rw [hdeg]
        _ = Module.finrank F F₂ * Module.finrank F F₁ := mul_comm _ _
    exact (Nat.eq_of_mul_eq_mul_left Module.finrank_pos hmul).symm
  have hΨinj : Function.Injective Ψ := by
    have h := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := Ψ.toLinearMap) hdim).mpr hΨsurj
    exact h

  let e : (F₂ ⊗[F] F₁) ≃ₐ[F₂] (∀ i, Z i) := AlgEquiv.ofBijective Ψ ⟨hΨinj, hΨsurj⟩
  have heapp : ∀ x, e x = Ψ x := fun _ => rfl

  have hA : algebraMap F F₂ (Algebra.norm F g)
      = LinearMap.det (((Algebra.lmul F F₁) g).baseChange F₂) := by
    let b := Module.finBasis F F₁
    rw [Algebra.norm_apply, ← LinearMap.det_toMatrix b ((Algebra.lmul F F₁) g),
      ← LinearMap.det_toMatrix (Algebra.TensorProduct.basis F₂ b)
        (((Algebra.lmul F F₁) g).baseChange F₂),
      LinearMap.toMatrix_baseChange]
    exact RingHom.map_det (algebraMap F F₂) _

  have hB : ((Algebra.lmul F F₁) g).baseChange F₂
      = (Algebra.lmul F₂ (F₂ ⊗[F] F₁)) ((1 : F₂) ⊗ₜ[F] g) := by
    apply LinearMap.restrictScalars_injective F
    apply TensorProduct.ext'
    intro c x
    simp only [LinearMap.coe_restrictScalars,
      LinearMap.baseChange_tmul, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply',
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]

  have hC : LinearMap.det ((Algebra.lmul F₂ (F₂ ⊗[F] F₁)) ((1 : F₂) ⊗ₜ[F] g))
      = LinearMap.det ((Algebra.lmul F₂ (∀ i, Z i)) (e ((1 : F₂) ⊗ₜ[F] g))) := by
    rw [← LinearMap.det_conj ((Algebra.lmul F₂ (F₂ ⊗[F] F₁)) ((1 : F₂) ⊗ₜ[F] g))
      e.toLinearEquiv]
    congr 1
    apply LinearMap.ext
    intro x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      AlgEquiv.toLinearEquiv_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
    rw [map_mul]
    simp

  have hD : LinearMap.det ((Algebra.lmul F₂ (∀ i, Z i)) (e ((1 : F₂) ⊗ₜ[F] g)))
      = ∏ i, LinearMap.det ((Algebra.lmul F₂ (Z i)) (e ((1 : F₂) ⊗ₜ[F] g) i)) := by
    have hmap : (Algebra.lmul F₂ (∀ i, Z i)) (e ((1 : F₂) ⊗ₜ[F] g))
        = LinearMap.pi (fun i =>
            ((Algebra.lmul F₂ (Z i)) (e ((1 : F₂) ⊗ₜ[F] g) i)) ∘ₗ LinearMap.proj i) := by
      apply LinearMap.ext
      intro x
      funext j
      simp only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', LinearMap.pi_apply,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply, Pi.mul_apply]
    rw [hmap, det_pi_hetero Z
      (fun i => (Algebra.lmul F₂ (Z i)) (e ((1 : F₂) ⊗ₜ[F] g) i))]

  have hE : ∀ i, e ((1 : F₂) ⊗ₜ[F] g) i = algebraMap F₁ (Z i) g := by
    intro i
    rw [heapp, hΨapp, hηtmul]
    simp
  rw [hA, hB, hC, hD]
  exact Finset.prod_congr rfl fun i _ => by rw [hE i, ← Algebra.norm_apply]

private theorem ord_prod {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {ι : Type*} (s : Finset ι) (x : ι → F) (hx : ∀ i ∈ s, x i ≠ 0) :
    v.ord (∏ i ∈ s, x i) = ∑ i ∈ s, v.ord (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Place.ord_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Place.ord_mul _ (hx a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hx i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hx i (Finset.mem_insert_of_mem hi)]

private theorem sum_sum_ramificationIndex_mul_inertiaDeg_exchange
    {K F F₁ F₂ : Type*} [Field K] [Field F] [Field F₁] [Field F₂]
    [Algebra K F] [Algebra K F₁] [Algebra K F₂]
    [Algebra F F₁] [Algebra F F₂]
    [IsScalarTower K F F₁] [IsScalarTower K F F₂]
    [FiniteDimensional F F₁] [FiniteDimensional F F₂] [CharZero F]
    (n : ℕ) (Z : Fin n → Type*) [∀ i, Field (Z i)]
    [∀ i, Algebra K (Z i)] [∀ i, Algebra F (Z i)]
    [∀ i, Algebra F₁ (Z i)] [∀ i, Algebra F₂ (Z i)]
    [∀ i, IsScalarTower K F (Z i)] [∀ i, IsScalarTower K F₁ (Z i)] [∀ i, IsScalarTower K F₂ (Z i)]
    [∀ i, IsScalarTower F F₁ (Z i)] [∀ i, IsScalarTower F F₂ (Z i)]
    [∀ i, FiniteDimensional F₁ (Z i)] [∀ i, FiniteDimensional F₂ (Z i)]
    (hgen : ∀ i, Algebra.adjoin F
      (Set.range (algebraMap F₁ (Z i)) ∪ Set.range (algebraMap F₂ (Z i))) = ⊤)
    (hdeg : ∑ i, Module.finrank F₁ (Z i) = Module.finrank F F₂)
    (hsep : ∀ i j, i ≠ j → ∃ t : F₂ ⊗[F] F₁,
      Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom F F₂ (Z i))
        (IsScalarTower.toAlgHom F F₁ (Z i)) t = 0 ∧
      Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom F F₂ (Z j))
        (IsScalarTower.toAlgHom F F₁ (Z j)) t ≠ 0)
    (w₁ : Place K F₁) (w₂ : Place K F₂) (hw : w₁.restrict F = w₂.restrict F)
    (T : ∀ i, Finset (Place K (Z i)))
    (hT : ∀ i W, W ∈ T i ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ i, ∑ W ∈ T i, W.ramificationIndex F₁ * W.inertiaDeg F₂
      = w₁.inertiaDeg F * w₂.ramificationIndex F := by
  classical
  haveI : PerfectField F := PerfectField.ofCharZero
  haveI : CharZero F₁ := charZero_of_injective_algebraMap (algebraMap F F₁).injective
  haveI : CharZero F₂ := charZero_of_injective_algebraMap (algebraMap F F₂).injective
  haveI : PerfectField F₂ := PerfectField.ofCharZero
  haveI : Algebra.IsSeparable F F₁ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : ∀ i, Algebra.IsSeparable F₂ (Z i) := fun i =>
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hrr : ∀ (i : Fin n) (W : Place K (Z i)),
      (W.restrict F₁).restrict F = (W.restrict F₂).restrict F := fun i W =>
    Place.ext (by simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])
  set v : Place K F := w₁.restrict F with hv

  obtain ⟨g, hg0, hg⟩ := Place.exists_forall_ord_eq (v.fiberOver F₁)
    (fun w => if w = w₁ then (1 : ℤ) else 0)
  have hg1 : w₁.ord g = 1 := by
    have := hg w₁ ((Place.mem_fiberOver _).mpr rfl)
    simpa using this
  have hgz : ∀ w ∈ v.fiberOver F₁, w ≠ w₁ → w.ord g = 0 := fun w hw hne => by
    have := hg w hw
    simpa [hne] using this
  have hgZ : ∀ i, algebraMap F₁ (Z i) g ≠ 0 := fun i => by simpa using hg0

  have hN := algebraMap_norm_eq_prod_norm_of_decomposition n Z hgen hdeg hsep g

  have h1 : w₂.ord (algebraMap F F₂ (Algebra.norm F g))
      = (w₂.ramificationIndex F : ℤ) * (w₁.inertiaDeg F : ℤ) := by
    rw [Place.ord_restrict, ← hw, Place.ord_norm_eq_sum_fiberOver (w₁.restrict F) hg0,
      Finset.sum_eq_single_of_mem w₁ ((Place.mem_fiberOver _).mpr rfl)]
    · rw [hg1, mul_one]
    · intro w hw hne
      rw [hgz w hw hne, mul_zero]

  have h2 : ∀ i, w₂.ord (Algebra.norm F₂ (algebraMap F₁ (Z i) g))
      = ∑ W ∈ T i, ((W.ramificationIndex F₁ : ℤ) * (W.inertiaDeg F₂ : ℤ)) := by
    intro i
    rw [Place.ord_norm_eq_sum_fiberOver w₂ (hgZ i)]
    have hTeq : T i = (w₂.fiberOver (Z i)).filter (fun W => W.restrict F₁ = w₁) := by
      ext W
      rw [hT, Finset.mem_filter, Place.mem_fiberOver, and_comm]
    rw [hTeq, Finset.sum_filter]
    refine Finset.sum_congr rfl fun W hW => ?_
    have hW2 : W.restrict F₂ = w₂ := (Place.mem_fiberOver _).mp hW
    rw [Place.ord_restrict]
    by_cases h : W.restrict F₁ = w₁
    · rw [if_pos h, h, hg1, mul_one, mul_comm]
    · rw [if_neg h, hgz (W.restrict F₁) ?_ h, mul_zero, mul_zero]
      rw [Place.mem_fiberOver, hrr, hW2, ← hw]

  have hprod : w₂.ord (algebraMap F F₂ (Algebra.norm F g))
      = ∑ i, w₂.ord (Algebra.norm F₂ (algebraMap F₁ (Z i) g)) := by
    rw [hN, ord_prod w₂ Finset.univ _
      (fun i _ => Algebra.norm_ne_zero_iff.mpr (hgZ i))]
  rw [h1] at hprod
  have hcast : ((∑ i, ∑ W ∈ T i, W.ramificationIndex F₁ * W.inertiaDeg F₂ : ℕ) : ℤ)
      = ((w₁.inertiaDeg F * w₂.ramificationIndex F : ℕ) : ℤ) := by
    push_cast
    rw [← Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => h2 i, ← hprod, mul_comm]
  exact_mod_cast hcast

end PlaceExchange

open PlaceExchange in

theorem solution
    {K F F₁ F₂ : Type} [Field K] [Field F] [Field F₁] [Field F₂]
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [CharZero K]
    [HasPrincipalDivisors K F₁]
    (φ : F →ₐ[K] F₁) (ψ' : F →ₐ[K] F₂)
    (hφ : φ.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral)
    (hφfin : FiniteAlong K φ) (hψ'fin : FiniteAlong K ψ')
    (n : ℕ) (Z : Fin n → Type)
    [∀ i, Field (Z i)] [∀ i, Algebra K (Z i)] [∀ i, HasPrincipalDivisors K (Z i)]
    (u : ∀ i, F₁ →ₐ[K] Z i) (u' : ∀ i, F₂ →ₐ[K] Z i)
    (hsq : ∀ i, (u i).comp φ = (u' i).comp ψ')
    (hu : ∀ i, (u i).toRingHom.IsIntegral) (hu' : ∀ i, (u' i).toRingHom.IsIntegral)
    (hufin : ∀ i, FiniteAlong K (u i)) (hu'fin : ∀ i, FiniteAlong K (u' i))
    (hgen : ∀ i, IntermediateField.adjoin K (Set.range (u i) ∪ Set.range (u' i)) = ⊤)
    (hdeg : ∑ i, finrankAlong K (u' i) = finrankAlong K φ)
    (hsep : ∀ i j, i ≠ j → ∃ t : F₁ ⊗[K] F₂,
      Algebra.TensorProduct.productMap (u i) (u' i) t = 0 ∧
      Algebra.TensorProduct.productMap (u j) (u' j) t ≠ 0)
    (D : Divisor K F₂) :
    Divisor.pullbackAlong φ hφ (Divisor.pushforwardAlong ψ' hψ' D)
      = ∑ i, Divisor.pushforwardAlong (u i) (hu i)
          (Divisor.pullbackAlong (u' i) (hu' i) D) := by
  classical
  letI : Algebra F F₁ := algebraAlong φ
  letI : Algebra F F₂ := algebraAlong ψ'
  letI : ∀ i, Algebra F₁ (Z i) := fun i => algebraAlong (u i)
  letI : ∀ i, Algebra F₂ (Z i) := fun i => algebraAlong (u' i)
  letI : ∀ i, Algebra F (Z i) := fun i => algebraAlong ((u i).comp φ)
  haveI : IsScalarTower K F F₁ := isScalarTower_along φ
  haveI : IsScalarTower K F F₂ := isScalarTower_along ψ'
  haveI : ∀ i, IsScalarTower K F₁ (Z i) := fun i => isScalarTower_along (u i)
  haveI : ∀ i, IsScalarTower K F₂ (Z i) := fun i => isScalarTower_along (u' i)
  haveI : ∀ i, IsScalarTower K F (Z i) := fun i => isScalarTower_along ((u i).comp φ)
  haveI : ∀ i, IsScalarTower F F₁ (Z i) := fun i => IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : ∀ i, IsScalarTower F F₂ (Z i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun x => AlgHom.congr_fun (hsq i) x
  haveI : Algebra.IsIntegral F F₁ := isIntegral_along φ hφ
  haveI : Algebra.IsIntegral F F₂ := isIntegral_along ψ' hψ'
  haveI : ∀ i, Algebra.IsIntegral F₁ (Z i) := fun i => isIntegral_along (u i) (hu i)
  haveI : ∀ i, Algebra.IsIntegral F₂ (Z i) := fun i => isIntegral_along (u' i) (hu' i)
  haveI : FiniteDimensional F F₁ := hφfin
  haveI : FiniteDimensional F F₂ := hψ'fin
  haveI : ∀ i, FiniteDimensional F₁ (Z i) := fun i => hufin i
  haveI : ∀ i, FiniteDimensional F₂ (Z i) := fun i => hu'fin i
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  haveI : ∀ i, FiniteDimensional F (Z i) := fun i => Module.Finite.trans F₁ (Z i)

  have hgenZ : ∀ i, Algebra.adjoin F
      (Set.range (algebraMap F₂ (Z i)) ∪ Set.range (algebraMap F₁ (Z i))) = ⊤ := fun i => by
    rw [Set.union_comm]
    exact algebra_adjoin_eq_top_of_intermediateField (K := K) (hgen i)
  have hdeg' : ∑ i, Module.finrank F₂ (Z i) = Module.finrank F F₁ := hdeg

  have hsep' : ∀ i j, i ≠ j → ∃ t : F₁ ⊗[F] F₂,
      Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom F F₁ (Z i))
        (IsScalarTower.toAlgHom F F₂ (Z i)) t = 0 ∧
      Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom F F₁ (Z j))
        (IsScalarTower.toAlgHom F F₂ (Z j)) t ≠ 0 := by
    intro i j hij
    obtain ⟨t₀, h0, hne⟩ := hsep i j hij
    refine ⟨Algebra.TensorProduct.productMap
      ((Algebra.TensorProduct.includeLeft :
        F₁ →ₐ[F] F₁ ⊗[F] F₂).restrictScalars K)
      ((Algebra.TensorProduct.includeRight :
        F₂ →ₐ[F] F₁ ⊗[F] F₂).restrictScalars K) t₀, ?_, ?_⟩
    all_goals
      have hcomm : ∀ (m : Fin n) (t : F₁ ⊗[K] F₂),
          Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom F F₁ (Z m))
            (IsScalarTower.toAlgHom F F₂ (Z m))
            (Algebra.TensorProduct.productMap
              ((Algebra.TensorProduct.includeLeft :
                F₁ →ₐ[F] F₁ ⊗[F] F₂).restrictScalars K)
              ((Algebra.TensorProduct.includeRight :
                F₂ →ₐ[F] F₁ ⊗[F] F₂).restrictScalars K) t)
          = Algebra.TensorProduct.productMap (u m) (u' m) t := by
        intro m t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul x y =>
          have h1 : ((Algebra.TensorProduct.includeLeft :
              F₁ →ₐ[F] F₁ ⊗[F] F₂).restrictScalars K) x = x ⊗ₜ[F] (1 : F₂) := rfl
          have h2 : ((Algebra.TensorProduct.includeRight :
              F₂ →ₐ[F] F₁ ⊗[F] F₂).restrictScalars K) y = (1 : F₁) ⊗ₜ[F] y := rfl
          rw [Algebra.TensorProduct.productMap_apply_tmul, map_mul, h1, h2,
            Algebra.TensorProduct.productMap_apply_tmul,
            Algebra.TensorProduct.productMap_apply_tmul,
            map_one, map_one, mul_one, one_mul,
            IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom']
          rfl
        | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
    · rw [hcomm, h0]
    · rw [hcomm]
      exact hne

  have eZ : ∀ (i : Fin n) (W : Place K (Z i)),
      Place.ramificationIndexAlong (u' i) W = W.ramificationIndex F₂ := fun _ _ => rfl
  have fZ : ∀ (i : Fin n) (W : Place K (Z i)),
      W.inertiaDegAlong (u i) (hu i) = W.inertiaDeg F₁ := fun _ _ => rfl
  have fF : ∀ w : Place K F₂, w.inertiaDegAlong ψ' hψ' = w.inertiaDeg F := fun _ => rfl
  have eF : ∀ w : Place K F₁, Place.ramificationIndexAlong φ w = w.ramificationIndex F := fun _ => rfl
  have hrr : ∀ (i : Fin n) (W : Place K (Z i)),
      (W.restrict F₁).restrict F = (W.restrict F₂).restrict F := fun i W =>
    Place.ext (by simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])

  suffices h : (Divisor.pullbackAlong φ hφ).comp (Divisor.pushforwardAlong ψ' hψ') =
      ∑ i, (Divisor.pushforwardAlong (u i) (hu i)).comp
        (Divisor.pullbackAlong (u' i) (hu' i)) by
    have := DFunLike.congr_fun h D
    simpa using this
  refine Finsupp.addHom_ext fun wA m => ?_
  simp only [AddMonoidHom.coe_comp, AddMonoidHom.finsetSum_apply, Function.comp_apply]
  rw [Divisor.pushforwardAlong_single, Divisor.pullbackAlong_single]
  simp only [Divisor.pullbackAlong_single, map_sum, Divisor.pushforwardAlong_single]
  ext wB
  rw [Finset.sum_apply']
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq']
  by_cases hv : wB.restrictAlong φ hφ = wA.restrictAlong ψ' hψ'
  · rw [if_pos (Place.mem_fiberAlong.mpr hv)]
    have hsum : ∀ i : Fin n,
        ((Place.fiberAlong (u' i) (hu' i) wA).sum fun W =>
          Finsupp.single (W.restrictAlong (u i) (hu i))
            (m * (Place.ramificationIndexAlong (u' i) W : ℤ) *
              (W.inertiaDegAlong (u i) (hu i) : ℤ))) wB
        = ∑ W ∈ (Place.fiberAlong (u' i) (hu' i) wA).filter
            (fun W => W.restrictAlong (u i) (hu i) = wB),
            m * (W.ramificationIndex F₂ : ℤ) * (W.inertiaDeg F₁ : ℤ) := by
      intro i
      rw [Finsupp.finsetSum_apply]
      simp only [Finsupp.single_apply, eZ, fZ]
      rw [← Finset.sum_filter]
    rw [Finset.sum_congr rfl fun i _ => hsum i]
    have hT : ∀ (i : Fin n) (W : Place K (Z i)),
        W ∈ (Place.fiberAlong (u' i) (hu' i) wA).filter
          (fun W => W.restrictAlong (u i) (hu i) = wB)
        ↔ W.restrict F₂ = wA ∧ W.restrict F₁ = wB := fun i W => by
      rw [Finset.mem_filter, Place.mem_fiberAlong]
      exact Iff.rfl
    have key := sum_sum_ramificationIndex_mul_inertiaDeg_exchange
      (K := K) (F := F) (F₁ := F₂) (F₂ := F₁) n Z hgenZ hdeg' hsep'
      wA wB (Eq.symm hv)
      (fun i => (Place.fiberAlong (u' i) (hu' i) wA).filter
        (fun W => W.restrictAlong (u i) (hu i) = wB))
      (fun i W => hT i W)
    rw [fF, eF]
    have hkeyZ : ((wA.inertiaDeg F * wB.ramificationIndex F : ℕ) : ℤ)
        = ((∑ i, ∑ W ∈ (Place.fiberAlong (u' i) (hu' i) wA).filter
            (fun W => W.restrictAlong (u i) (hu i) = wB),
            W.ramificationIndex F₂ * W.inertiaDeg F₁ : ℕ) : ℤ) := by
      exact_mod_cast key.symm
    calc m * (wA.inertiaDeg F : ℤ) * (wB.ramificationIndex F : ℤ)
        = m * ((wA.inertiaDeg F * wB.ramificationIndex F : ℕ) : ℤ) := by push_cast; ring
      _ = m * ((∑ i, ∑ W ∈ (Place.fiberAlong (u' i) (hu' i) wA).filter
            (fun W => W.restrictAlong (u i) (hu i) = wB),
            W.ramificationIndex F₂ * W.inertiaDeg F₁ : ℕ) : ℤ) := by rw [hkeyZ]
      _ = ∑ i, ∑ W ∈ (Place.fiberAlong (u' i) (hu' i) wA).filter
            (fun W => W.restrictAlong (u i) (hu i) = wB),
            m * (W.ramificationIndex F₂ : ℤ) * (W.inertiaDeg F₁ : ℤ) := by
          push_cast
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun W _ => by ring
  · rw [if_neg (fun h => hv (Place.mem_fiberAlong.mp h))]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun W hW => ?_
    rw [Finsupp.single_apply, if_neg]
    intro hWB
    apply hv
    have h₁ : W.restrict F₂ = wA := Place.mem_fiberAlong.mp hW
    have h₂ : W.restrict F₁ = wB := hWB
    show wB.restrict F = wA.restrict F
    rw [← h₁, ← h₂, hrr]

#print axioms solution

end
end S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_sum_of_decomposition
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_sum_of_decomposition (solution)
