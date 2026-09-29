-- Prove2me | solution 1 for AlgebraicCurve.Place.hasValue_norm_along_of_separableAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/49c57767-efc7-5f55-a875-e85585374edf

import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_eq_ramificationIdx_fiberCenter
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_inertiaDeg_fiberCenter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_hasValue_norm_along_of_separableAlong
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

open AlgebraicCurve

section Shortcuts

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra F F']

@[reducible] private noncomputable def instModuleResidueQuotientMap (v : Place K F) :
    Module (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
      (Place.integralClosureAt F' v ⧸
        Ideal.map (algebraMap v.toValuationSubring (Place.integralClosureAt F' v))
          (IsLocalRing.maximalIdeal v.toValuationSubring)) :=
  @Algebra.toModule _ _ _ _ Ideal.Quotient.algebraQuotientMapQuotient

@[reducible] private noncomputable def instModuleResidueQuotientPow (v : Place K F)
    (Q : Ideal (Place.integralClosureAt F' v)) :
    Module (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
      (Place.integralClosureAt F' v ⧸
        Q ^ (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx' Q) :=
  @Algebra.toModule _ _ _ _ (Ideal.Quotient.algebraQuotientPowRamificationIdx _ Q)

private theorem instAddMonoidHomClassQuotientMk (v : Place K F)
    (J : Ideal (Place.integralClosureAt F' v)) :
    AddMonoidHomClass (Place.integralClosureAt F' v →+* Place.integralClosureAt F' v ⧸ J)
      (Place.integralClosureAt F' v) (Place.integralClosureAt F' v ⧸ J) :=
  RingHom.instRingHomClass.toAddMonoidHomClass

end Shortcuts

attribute [local instance high] instModuleResidueQuotientMap instModuleResidueQuotientPow
  instAddMonoidHomClassQuotientMk

private theorem exists_unit_of_forall_hasValue {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F) (g : F') (a : Place K F' → Kˣ)
    (ha : ∀ w ∈ v.fiberOver F', w.HasValue g (a w)) :
    ∃ b : (Place.integralClosureAt F' v)ˣ, algebraMap (Place.integralClosureAt F' v) F' b = g := by
  classical

  obtain ⟨w₀, hw₀⟩ : (v.fiberOver F').Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have h := Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver (F' := F') (v := v)
    rw [hne, Finset.sum_empty] at h
    have hpos : 0 < Module.finrank F F' := Module.finrank_pos
    omega
  have hg0 : g ≠ 0 := by
    intro hg
    apply ((ha w₀ hw₀).isUnit (a w₀).ne_zero).ne_zero
    exact Subtype.ext (by simpa using hg)

  have hmem : ∀ P : IsDedekindDomain.HeightOneSpectrum (Place.integralClosureAt F' v),
      g ∈ (Place.placeOfPrime P).toValuationSubring ∧
        g⁻¹ ∈ (Place.placeOfPrime P).toValuationSubring := by
    intro P
    have hP : Place.placeOfPrime P ∈ v.fiberOver F' :=
      (Place.mem_fiberOver v).mpr (Place.restrict_placeOfPrime P)
    have hv := ha _ hP
    obtain ⟨u, hu⟩ := hv.isUnit (a _).ne_zero
    refine ⟨hv.mem, ?_⟩
    have hmul : g * ((u⁻¹ : (Place.placeOfPrime P).toValuationSubringˣ) :
        (Place.placeOfPrime P).toValuationSubring) = 1 := by
      have h : ((u : (Place.placeOfPrime P).toValuationSubring) *
          ((u⁻¹ : (Place.placeOfPrime P).toValuationSubringˣ) :
            (Place.placeOfPrime P).toValuationSubring)) = 1 := u.mul_inv
      rw [hu] at h
      exact congrArg Subtype.val h
    rw [← eq_inv_of_mul_eq_one_right hmul]
    exact Subtype.mem _

  have hint : ∀ x : F', (∀ P : IsDedekindDomain.HeightOneSpectrum (Place.integralClosureAt F' v),
      x ∈ (Place.placeOfPrime P).toValuationSubring) →
      ∃ b : Place.integralClosureAt F' v, algebraMap (Place.integralClosureAt F' v) F' b = x := by
    intro x hx
    refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F' x ?_
    intro P
    have h := hx P
    rw [Place.placeOfPrime_toValuationSubring,
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at h
    exact h
  obtain ⟨b, hb⟩ := hint g fun P => (hmem P).1
  obtain ⟨b', hb'⟩ := hint g⁻¹ fun P => (hmem P).2
  have hbb' : b * b' = 1 := by
    apply IsFractionRing.injective (Place.integralClosureAt F' v) F'
    rw [map_mul, hb, hb', map_one, mul_inv_cancel₀ hg0]
  exact ⟨Units.mkOfMulEqOne b b' hbb', hb⟩

private theorem norm_algebraMap_integralClosureAt {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F)
    (x : Place.integralClosureAt F' v) :
    Algebra.norm F (algebraMap (Place.integralClosureAt F' v) F' x) =
      algebraMap v.toValuationSubring F (Algebra.norm v.toValuationSubring x) := by
  haveI : IsLocalization
      (Algebra.algebraMapSubmonoid (Place.integralClosureAt F' v) (nonZeroDivisors v.toValuationSubring))
      F' :=
    IsIntegralClosure.isLocalization v.toValuationSubring F F' (Place.integralClosureAt F' v)
  classical
  let bs := Module.Free.chooseBasis v.toValuationSubring (Place.integralClosureAt F' v)
  rw [Algebra.norm_eq_matrix_det (bs.localizationLocalization F (nonZeroDivisors v.toValuationSubring) F'),
    Algebra.norm_eq_matrix_det bs, RingHom.map_det]
  congr 1
  ext i j
  simp only [Matrix.map_apply, RingHom.mapMatrix_apply, Algebra.leftMulMatrix_eq_repr_mul, ← map_mul,
    Module.Basis.localizationLocalization_apply, Module.Basis.localizationLocalization_repr_algebraMap]

private theorem mk_norm_eq_norm_quotient {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F)
    (x : Place.integralClosureAt F' v) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.toValuationSubring)
        (Algebra.norm v.toValuationSubring x) =
      Algebra.norm (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
        (Ideal.Quotient.mk
          (Ideal.map (algebraMap v.toValuationSubring (Place.integralClosureAt F' v))
            (IsLocalRing.maximalIdeal v.toValuationSubring)) x) := by
  classical
  let bs := Module.Free.chooseBasis v.toValuationSubring (Place.integralClosureAt F' v)

  have hsmul : ∀ (r : v.toValuationSubring) (b : Place.integralClosureAt F' v),
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.toValuationSubring) r •
          Ideal.Quotient.mk (Ideal.map (algebraMap v.toValuationSubring (Place.integralClosureAt F' v))
            (IsLocalRing.maximalIdeal v.toValuationSubring)) b =
        Ideal.Quotient.mk (Ideal.map (algebraMap v.toValuationSubring (Place.integralClosureAt F' v))
            (IsLocalRing.maximalIdeal v.toValuationSubring)) (r • b) := by
    intro r b
    rw [Ideal.Quotient.mk_smul_mk_quotient_map_quotient, Algebra.smul_def]

  have hmk_sum : ∀ b : Place.integralClosureAt F' v,
      Ideal.Quotient.mk (Ideal.map (algebraMap v.toValuationSubring (Place.integralClosureAt F' v))
          (IsLocalRing.maximalIdeal v.toValuationSubring)) b =
        ∑ i, Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.toValuationSubring) (bs.repr b i) •
          Ideal.Quotient.mk (Ideal.map (algebraMap v.toValuationSubring (Place.integralClosureAt F' v))
            (IsLocalRing.maximalIdeal v.toValuationSubring)) (bs i) := by
    intro b
    conv_lhs => rw [← bs.sum_repr b]
    rw [map_sum]
    simp only [hsmul]
  have hsp : (⊤ : Submodule (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
      (Place.integralClosureAt F' v ⧸
        Ideal.map (algebraMap v.toValuationSubring (Place.integralClosureAt F' v))
          (IsLocalRing.maximalIdeal v.toValuationSubring))) ≤
      Submodule.span (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
        (Set.range fun i => Ideal.Quotient.mk
          (Ideal.map (algebraMap v.toValuationSubring (Place.integralClosureAt F' v))
            (IsLocalRing.maximalIdeal v.toValuationSubring)) (bs i)) := by
    rintro y -
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hmk_sum b]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
      fun i => Ideal.Quotient.mk
        (Ideal.map (algebraMap v.toValuationSubring (Place.integralClosureAt F' v))
          (IsLocalRing.maximalIdeal v.toValuationSubring)) (bs i) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    beta_reduce at hc
    choose r hr using fun k => Ideal.Quotient.mk_surjective (c k)
    have hmem : (∑ k, r k • bs k) ∈
        Ideal.map (algebraMap v.toValuationSubring (Place.integralClosureAt F' v))
          (IsLocalRing.maximalIdeal v.toValuationSubring) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      simp only [← hr, hsmul] at hc
      exact hc
    have hcoeff : r i ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
      have hmem' : (∑ k, r k • bs k) ∈
          IsLocalRing.maximalIdeal v.toValuationSubring •
            Submodule.span v.toValuationSubring (Set.range (bs : _ → Place.integralClosureAt F' v)) := by
        rw [bs.span_eq, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
        exact hmem
      obtain ⟨a, ha, hx⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum
        (IsLocalRing.maximalIdeal v.toValuationSubring) (bs : _ → Place.integralClosureAt F' v) _).1 hmem'
      rw [Finsupp.sum_fintype _ _ (fun k => zero_smul _ (bs k))] at hx
      have h1 := bs.repr_sum_self (a : _ → v.toValuationSubring)
      rw [hx, bs.repr_sum_self] at h1
      rw [h1]
      exact ha i
    rw [← hr i]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hcoeff
  let qb := Module.Basis.mk hli hsp
  have hqb_repr : ∀ (b : Place.integralClosureAt F' v) (i : _),
      qb.repr (Ideal.Quotient.mk
        (Ideal.map (algebraMap v.toValuationSubring (Place.integralClosureAt F' v))
          (IsLocalRing.maximalIdeal v.toValuationSubring)) b) i =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.toValuationSubring) (bs.repr b i) := by
    intro b i
    have hq : ∀ k, Ideal.Quotient.mk
        (Ideal.map (algebraMap v.toValuationSubring (Place.integralClosureAt F' v))
          (IsLocalRing.maximalIdeal v.toValuationSubring)) (bs k) = qb k := by
      intro k
      simp only [qb, Module.Basis.mk_apply]
    rw [hmk_sum b]
    simp only [hq]
    exact congrFun (qb.repr_sum_self fun k =>
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.toValuationSubring) (bs.repr b k)) i
  rw [Algebra.norm_eq_matrix_det bs x, Algebra.norm_eq_matrix_det qb, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, ← hqb_repr, map_mul]
  simp only [qb, Module.Basis.mk_apply]

private theorem sub_const_mem_fiberCenter {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F) {w : Place K F'} (hw : w.restrict F = v)
    (x : Place.integralClosureAt F' v) (a : K)
    (hx : w.HasValue (algebraMap (Place.integralClosureAt F' v) F' x) a) :
    x - algebraMap v.toValuationSubring (Place.integralClosureAt F' v)
        ⟨algebraMap K F a, v.algebraMap_mem' a⟩ ∈
      (Place.fiberCenter F' v hw).asIdeal := by
  by_cases hd : x - algebraMap v.toValuationSubring (Place.integralClosureAt F' v)
      ⟨algebraMap K F a, v.algebraMap_mem' a⟩ = 0
  · rw [hd]
    exact Ideal.zero_mem _
  · have hconst : algebraMap (Place.integralClosureAt F' v) F'
        (algebraMap v.toValuationSubring (Place.integralClosureAt F' v)
          ⟨algebraMap K F a, v.algebraMap_mem' a⟩) = algebraMap K F' a := by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply v.toValuationSubring F F',
        show algebraMap v.toValuationSubring F ⟨algebraMap K F a, v.algebraMap_mem' a⟩
          = algebraMap K F a from rfl, ← IsScalarTower.algebraMap_apply]
    have hmem : algebraMap (Place.integralClosureAt F' v) F' x - algebraMap K F' a
        ∈ w.toValuationSubring := sub_mem hx.mem (w.algebraMap_mem' a)
    have hne : algebraMap (Place.integralClosureAt F' v) F' x - algebraMap K F' a ≠ 0 := by
      intro h0
      apply hd
      apply IsFractionRing.injective (Place.integralClosureAt F' v) F'
      rw [map_sub, map_zero, hconst]
      exact h0
    rw [Place.mem_fiberCenter_iff_ord_pos hw hd, map_sub, hconst,
      ← w.mem_maximalIdeal_iff_ord_pos hne hmem, ← IsLocalRing.residue_eq_zero_iff]
    have hsplit : (⟨_, hmem⟩ : w.toValuationSubring)
        = ⟨_, hx.mem⟩ - ⟨_, (w.hasValue_algebraMap a).mem⟩ := rfl
    rw [hsplit, map_sub, hx.residue_eq, (w.hasValue_algebraMap a).residue_eq, sub_self]

private theorem norm_algebraMap_add_of_isNilpotent {k A : Type*} [CommRing k] [IsDomain k]
    [CommRing A] [Algebra k A] [Module.Free k A] [Module.Finite k A]
    (c : k) (n : A) (hn : IsNilpotent n) :
    Algebra.norm k (algebraMap k A c + n) = c ^ Module.finrank k A := by
  classical
  let bs := Module.Free.chooseBasis k A
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex k A) = Module.finrank k A :=
    (Module.finrank_eq_card_chooseBasisIndex k A).symm
  have hN : IsNilpotent (Algebra.leftMulMatrix bs n) := hn.map (Algebra.leftMulMatrix bs)
  have hchar : (Algebra.leftMulMatrix bs n).charpoly = Polynomial.X ^ Module.finrank k A := by
    have h := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN
    rw [hcard] at h
    exact sub_eq_zero.mp h.eq_zero
  rw [Algebra.norm_eq_matrix_det bs, map_add, (Algebra.leftMulMatrix bs).commutes,
    Matrix.algebraMap_eq_diagonal]
  have hdet : (Matrix.diagonal (fun _ : Module.Free.ChooseBasisIndex k A => c) +
      Algebra.leftMulMatrix bs n).det =
        (-1) ^ Module.finrank k A * ((Algebra.leftMulMatrix bs n).charpoly.eval (-c)) := by
    rw [Matrix.eval_charpoly]
    have hneg := Matrix.det_neg (Matrix.scalar (Module.Free.ChooseBasisIndex k A) (-c) -
      Algebra.leftMulMatrix bs n)
    rw [hcard] at hneg
    rw [← hneg]
    congr 1
    ext i j
    simp only [Matrix.neg_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply]
    split_ifs <;> ring
  exact hdet.trans (by
    rw [hchar, Polynomial.eval_pow, Polynomial.eval_X, ← mul_pow, neg_one_mul, neg_neg])

private theorem norm_pi {R ι : Type*} [CommRing R] [Fintype ι] (A : ι → Type*)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Module.Free R (A i)]
    [∀ i, Module.Finite R (A i)] (x : ∀ i, A i) :
    Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  classical
  let bs : ∀ i, Module.Basis (Module.Free.ChooseBasisIndex R (A i)) R (A i) :=
    fun i => Module.Free.chooseBasis R (A i)

  have hmat : Algebra.leftMulMatrix (Pi.basis bs) x =
      Matrix.blockDiagonal' (fun i => Algebra.leftMulMatrix (bs i) (x i)) := by
    ext ⟨k, i⟩ ⟨k', j⟩
    rw [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.mul_apply, Pi.basis_apply]
    by_cases h : k = k'
    · subst h
      rw [Pi.single_eq_same, Matrix.blockDiagonal'_apply_eq, Algebra.leftMulMatrix_eq_repr_mul]
    · rw [Pi.single_eq_of_ne h, mul_zero, map_zero, Finsupp.zero_apply,
        Matrix.blockDiagonal'_apply_ne _ _ _ h]
  rw [Algebra.norm_eq_matrix_det (Pi.basis bs), hmat,
    (Matrix.blockTriangular_blockDiagonal' _).det_fintype]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [Algebra.norm_eq_matrix_det (bs k)]

  let e : Module.Free.ChooseBasisIndex R (A k) ≃
      { a : Σ i, Module.Free.ChooseBasisIndex R (A i) // a.1 = k } :=
    { toFun := fun i => ⟨⟨k, i⟩, rfl⟩
      invFun := fun a => a.2 ▸ a.1.2
      left_inv := fun i => rfl
      right_inv := by rintro ⟨⟨k', i⟩, rfl⟩; rfl }
  rw [← Matrix.det_reindex_self e (Algebra.leftMulMatrix (bs k) (x k))]
  congr 1
  ext ⟨⟨k₁, i⟩, hk₁⟩ ⟨⟨k₂, j⟩, hk₂⟩
  simp only at hk₁ hk₂
  subst hk₁
  subst hk₂
  rw [Matrix.toSquareBlock_def]
  simp only [Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.blockDiagonal'_apply_eq]
  rfl

private theorem free_quotient_pow_ramificationIdx {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F) (Q : Ideal (Place.integralClosureAt F' v)) :
    Module.Free (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
      (Place.integralClosureAt F' v ⧸ Q ^
        (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx' Q) := by
  letI : Field (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring) :=
    Ideal.Quotient.field _
  exact Module.Free.of_divisionRing _ _

private theorem norm_mk_pow_fiberCenter {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F) {w : Place K F'} (hw : w.restrict F = v)
    (P : IsDedekindDomain.HeightOneSpectrum (Place.integralClosureAt F' v))
    (hP : P = Place.fiberCenter F' v hw)
    (x : Place.integralClosureAt F' v) (a : K)
    (hx : w.HasValue (algebraMap (Place.integralClosureAt F' v) F' x) a) :
    Algebra.norm (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
        (Ideal.Quotient.mk (P.asIdeal ^
            (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx' P.asIdeal) x) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.toValuationSubring)
          (algebraMap K v.toValuationSubring a) ^
        (w.ramificationIndex F * w.inertiaDeg F) := by
  classical

  have hmemP : P.asIdeal ∈ (UniqueFactorizationMonoid.factors
      ((IsLocalRing.maximalIdeal v.toValuationSubring).map
        (algebraMap v.toValuationSubring (Place.integralClosureAt F' v)))).toFinset := by
    show P.asIdeal ∈ IsDedekindDomain.primesOverFinset _ _
    rw [IsDedekindDomain.mem_primesOverFinset_iff (Place.maximalIdeal_ne_bot v)]
    subst hP
    exact ⟨(Place.fiberCenter F' v hw).isPrime, Place.fiberCenter_liesOver hw⟩

  have hrank : Module.finrank (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
      (Place.integralClosureAt F' v ⧸ P.asIdeal ^
        (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx' P.asIdeal) =
      w.ramificationIndex F * w.inertiaDeg F := by
    rw [Place.ramificationIndex_eq_ramificationIdx_fiberCenter v hw,
      Place.inertiaDeg_eq_inertiaDeg_fiberCenter v hw, ← hP]
    exact Ideal.Factors.finrank_pow_ramificationIdx _ ⟨P.asIdeal, hmemP⟩
  haveI : Module.Finite (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
      (Place.integralClosureAt F' v ⧸ P.asIdeal ^
        (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx' P.asIdeal) :=
    Ideal.Factors.finiteDimensional_quotient_pow _ ⟨P.asIdeal, hmemP⟩

  have hconst : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring) =
      algebraMap K v.toValuationSubring a :=
    Subtype.ext (v.coe_algebraMap a).symm
  have hmem : x - algebraMap v.toValuationSubring (Place.integralClosureAt F' v)
      (algebraMap K v.toValuationSubring a) ∈ P.asIdeal := by
    have h := sub_const_mem_fiberCenter v hw x a hx
    rw [hconst] at h
    rw [hP]
    exact h
  have hnil : IsNilpotent (Ideal.Quotient.mk (P.asIdeal ^
      (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx' P.asIdeal)
      (x - algebraMap v.toValuationSubring (Place.integralClosureAt F' v)
        (algebraMap K v.toValuationSubring a))) :=
    ⟨_, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hmem _⟩
  have hsplit : Ideal.Quotient.mk (P.asIdeal ^
        (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx' P.asIdeal) x =
      algebraMap (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
          (Place.integralClosureAt F' v ⧸ P.asIdeal ^
            (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx' P.asIdeal)
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.toValuationSubring)
            (algebraMap K v.toValuationSubring a)) +
        Ideal.Quotient.mk (P.asIdeal ^
            (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx' P.asIdeal)
          (x - algebraMap v.toValuationSubring (Place.integralClosureAt F' v)
            (algebraMap K v.toValuationSubring a)) := by
    rw [Ideal.Quotient.algebraMap_quotient_pow_ramificationIdx, ← map_add, add_sub_cancel]
  haveI := free_quotient_pow_ramificationIdx v P.asIdeal
  rw [hsplit]
  exact (norm_algebraMap_add_of_isNilpotent _ _ hnil).trans (by rw [hrank])

open scoped Classical in

private theorem fiberCenter_mem_factors {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F) {w : Place K F'} (hw : w.restrict F = v) :
    (Place.fiberCenter F' v hw).asIdeal ∈ (UniqueFactorizationMonoid.factors
      ((IsLocalRing.maximalIdeal v.toValuationSubring).map
        (algebraMap v.toValuationSubring (Place.integralClosureAt F' v)))).toFinset := by
  show _ ∈ IsDedekindDomain.primesOverFinset _ _
  rw [IsDedekindDomain.mem_primesOverFinset_iff (Place.maximalIdeal_ne_bot v)]
  exact ⟨(Place.fiberCenter F' v hw).isPrime, Place.fiberCenter_liesOver hw⟩

open scoped Classical in

private theorem piQuotientEquiv_algebraMap {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F)
    (hmap : (IsLocalRing.maximalIdeal v.toValuationSubring).map
      (algebraMap v.toValuationSubring (Place.integralClosureAt F' v)) ≠ ⊥)
    (r : v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring) :
    Ideal.Factors.piQuotientEquiv (S := Place.integralClosureAt F' v)
        (IsLocalRing.maximalIdeal v.toValuationSubring) hmap
        (algebraMap (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
          (Place.integralClosureAt F' v ⧸ (IsLocalRing.maximalIdeal v.toValuationSubring).map
            (algebraMap v.toValuationSubring (Place.integralClosureAt F' v))) r) =
      algebraMap (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
        (∀ Q : (UniqueFactorizationMonoid.factors
          ((IsLocalRing.maximalIdeal v.toValuationSubring).map
            (algebraMap v.toValuationSubring (Place.integralClosureAt F' v)))).toFinset,
          Place.integralClosureAt F' v ⧸ ((Q : Ideal (Place.integralClosureAt F' v)) ^
            (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
              (Q : Ideal (Place.integralClosureAt F' v)))) r := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  funext Q
  simp only [Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Factors.piQuotientEquiv_mk,
    Pi.algebraMap_apply, Ideal.Quotient.algebraMap_quotient_pow_ramificationIdx]

open scoped Classical in

private theorem norm_mk_map_eq_norm_pi {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F) (x : Place.integralClosureAt F' v) :
    Algebra.norm (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
        (Ideal.Quotient.mk
          (Ideal.map (algebraMap v.toValuationSubring (Place.integralClosureAt F' v))
            (IsLocalRing.maximalIdeal v.toValuationSubring)) x) =
      Algebra.norm (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
        (fun Q : (UniqueFactorizationMonoid.factors
          ((IsLocalRing.maximalIdeal v.toValuationSubring).map
            (algebraMap v.toValuationSubring (Place.integralClosureAt F' v)))).toFinset =>
          Ideal.Quotient.mk ((Q : Ideal (Place.integralClosureAt F' v)) ^
            (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
              (Q : Ideal (Place.integralClosureAt F' v))) x) := by
  have hmap : (IsLocalRing.maximalIdeal v.toValuationSubring).map
      (algebraMap v.toValuationSubring (Place.integralClosureAt F' v)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot (Place.maximalIdeal_ne_bot v)
  exact (Algebra.norm_eq_of_algEquiv
      (AlgEquiv.ofRingEquiv (piQuotientEquiv_algebraMap v hmap)) _).symm.trans
    (congrArg _ ((AlgEquiv.ofRingEquiv_apply _ _).trans
      (Ideal.Factors.piQuotientEquiv_mk (S := Place.integralClosureAt F' v)
        (IsLocalRing.maximalIdeal v.toValuationSubring) hmap x)))

open scoped Classical in

private theorem free_quotient_pow_factors {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F)
    (Q : (UniqueFactorizationMonoid.factors
          ((IsLocalRing.maximalIdeal v.toValuationSubring).map
            (algebraMap v.toValuationSubring (Place.integralClosureAt F' v)))).toFinset) :
    Module.Free (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
      (Place.integralClosureAt F' v ⧸ (Q : Ideal (Place.integralClosureAt F' v)) ^
          (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
            (Q : Ideal (Place.integralClosureAt F' v))) := by
  letI : Field (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring) :=
    Ideal.Quotient.field _
  exact Module.Free.of_divisionRing
    (K := v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
    (V := Place.integralClosureAt F' v ⧸ (Q : Ideal (Place.integralClosureAt F' v)) ^
      (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
        (Q : Ideal (Place.integralClosureAt F' v)))

open scoped Classical in

private theorem finite_quotient_pow_factors {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F)
    (Q : (UniqueFactorizationMonoid.factors
          ((IsLocalRing.maximalIdeal v.toValuationSubring).map
            (algebraMap v.toValuationSubring (Place.integralClosureAt F' v)))).toFinset) :
    Module.Finite (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
      (Place.integralClosureAt F' v ⧸ (Q : Ideal (Place.integralClosureAt F' v)) ^
          (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
            (Q : Ideal (Place.integralClosureAt F' v))) :=
  Ideal.Factors.finiteDimensional_quotient_pow _ Q

open scoped Classical in

private theorem norm_mk_map_eq_prod_factors {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F) (x : Place.integralClosureAt F' v) :
    Algebra.norm (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
        (Ideal.Quotient.mk
          (Ideal.map (algebraMap v.toValuationSubring (Place.integralClosureAt F' v))
            (IsLocalRing.maximalIdeal v.toValuationSubring)) x) =
      ∏ Q : (UniqueFactorizationMonoid.factors
          ((IsLocalRing.maximalIdeal v.toValuationSubring).map
            (algebraMap v.toValuationSubring (Place.integralClosureAt F' v)))).toFinset,
        Algebra.norm (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
          (Ideal.Quotient.mk ((Q : Ideal (Place.integralClosureAt F' v)) ^
            (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
              (Q : Ideal (Place.integralClosureAt F' v))) x) := by
  haveI := free_quotient_pow_factors (F' := F') v
  haveI := finite_quotient_pow_factors (F' := F') v
  exact (norm_mk_map_eq_norm_pi v x).trans
    (norm_pi (fun Q : (UniqueFactorizationMonoid.factors
          ((IsLocalRing.maximalIdeal v.toValuationSubring).map
            (algebraMap v.toValuationSubring (Place.integralClosureAt F' v)))).toFinset =>
      Place.integralClosureAt F' v ⧸ (Q : Ideal (Place.integralClosureAt F' v)) ^
          (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
            (Q : Ideal (Place.integralClosureAt F' v))) _)

open scoped Classical in

private theorem prod_fiberOver_eq_prod_factors {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F) {β : Type*} [CommMonoid β]
    (g : (UniqueFactorizationMonoid.factors
      ((IsLocalRing.maximalIdeal v.toValuationSubring).map
        (algebraMap v.toValuationSubring (Place.integralClosureAt F' v)))).toFinset → β)
    (h : Place K F' → β)
    (hgh : ∀ (w : Place K F') (hw : w.restrict F = v),
      h w = g ⟨(Place.fiberCenter F' v hw).asIdeal, fiberCenter_mem_factors v hw⟩) :
    ∏ w ∈ v.fiberOver F', h w = ∏ Q, g Q := by
  refine Finset.prod_bij (fun w hw => ⟨(Place.fiberCenter F' v ((Place.mem_fiberOver v).mp hw)).asIdeal,
    fiberCenter_mem_factors v _⟩) ?_ ?_ ?_ ?_
  · intro w hw
    exact Finset.mem_univ _
  · intro w hw w' hw' hww'
    exact Place.eq_of_fiberCenter_eq ((Place.mem_fiberOver v).mp hw) ((Place.mem_fiberOver v).mp hw')
      (IsDedekindDomain.HeightOneSpectrum.ext (congrArg Subtype.val hww'))
  · rintro ⟨Q, hQ⟩ -
    have hQ' := hQ
    change Q ∈ IsDedekindDomain.primesOverFinset _ _ at hQ'
    rw [IsDedekindDomain.mem_primesOverFinset_iff (Place.maximalIdeal_ne_bot v)] at hQ'
    obtain ⟨hQ1, hQ2⟩ := hQ'
    have hQne : Q ≠ ⊥ := by
      intro hbot
      apply Place.maximalIdeal_ne_bot v
      have h2 := hQ2.over
      rw [hbot, Ideal.under_def, Ideal.comap_bot_of_injective _
        (Place.algebraMap_integralClosureAt_injective v)] at h2
      exact h2
    refine ⟨Place.placeOfPrime ⟨Q, hQ1, hQne⟩,
      (Place.mem_fiberOver v).mpr (Place.restrict_placeOfPrime _), ?_⟩
    exact Subtype.ext (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
      (Place.fiberCenter_placeOfPrime (⟨Q, hQ1, hQne⟩ :
        IsDedekindDomain.HeightOneSpectrum (Place.integralClosureAt F' v))))
  · intro w hw
    exact hgh w ((Place.mem_fiberOver v).mp hw)

private theorem norm_quotient_eq_prod {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F)
    (x : Place.integralClosureAt F' v) (a : Place K F' → Kˣ)
    (ha : ∀ w ∈ v.fiberOver F', w.HasValue (algebraMap (Place.integralClosureAt F' v) F' x) (a w)) :
    Algebra.norm (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
        (Ideal.Quotient.mk
          (Ideal.map (algebraMap v.toValuationSubring (Place.integralClosureAt F' v))
            (IsLocalRing.maximalIdeal v.toValuationSubring)) x) =
      algebraMap K v.ResidueField
        (∏ w ∈ v.fiberOver F', (a w : K) ^ (w.ramificationIndex F * w.inertiaDeg F)) := by
  classical
  rw [norm_mk_map_eq_prod_factors v x, map_prod]
  refine (prod_fiberOver_eq_prod_factors v _ _ ?_).symm
  intro w hw
  beta_reduce
  rw [map_pow, ← Place.residue_algebraMap]
  exact (norm_mk_pow_fiberCenter v hw _ rfl x (a w) (ha w ((Place.mem_fiberOver v).mpr hw))).symm

private theorem residue_norm_unit {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F)
    (b : (Place.integralClosureAt F' v)ˣ) (a : Place K F' → Kˣ)
    (ha : ∀ w ∈ v.fiberOver F', w.HasValue (algebraMap (Place.integralClosureAt F' v) F' b) (a w)) :
    IsLocalRing.residue v.toValuationSubring
        (Algebra.norm v.toValuationSubring (b : Place.integralClosureAt F' v)) =
      algebraMap K v.ResidueField
        (∏ w ∈ v.fiberOver F', (a w : K) ^ (w.ramificationIndex F * w.inertiaDeg F)) := by
  change Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.toValuationSubring)
      (Algebra.norm v.toValuationSubring (b : Place.integralClosureAt F' v)) = _
  rw [mk_norm_eq_norm_quotient v (b : Place.integralClosureAt F' v)]
  exact norm_quotient_eq_prod v (b : Place.integralClosureAt F' v) a ha

private theorem hasValue_norm_of_unit {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F) (b : (Place.integralClosureAt F' v)ˣ) (a : Place K F' → Kˣ)
    (ha : ∀ w ∈ v.fiberOver F', w.HasValue (algebraMap (Place.integralClosureAt F' v) F' b) (a w)) :
    v.HasValue (Algebra.norm F (algebraMap (Place.integralClosureAt F' v) F' b))
      (∏ w ∈ v.fiberOver F', (a w : K) ^ (w.ramificationIndex F * w.inertiaDeg F)) := by
  have hnorm : Algebra.norm F (algebraMap (Place.integralClosureAt F' v) F' b) =
      algebraMap v.toValuationSubring F
        (Algebra.norm v.toValuationSubring (b : Place.integralClosureAt F' v)) :=
    norm_algebraMap_integralClosureAt v (b : Place.integralClosureAt F' v)
  have hmem : Algebra.norm F (algebraMap (Place.integralClosureAt F' v) F' b) ∈
      v.toValuationSubring := by
    rw [hnorm]
    exact (Algebra.norm v.toValuationSubring (b : Place.integralClosureAt F' v)).2
  refine ⟨hmem, ?_⟩
  have hsub : (⟨Algebra.norm F (algebraMap (Place.integralClosureAt F' v) F' b), hmem⟩ :
      v.toValuationSubring) = Algebra.norm v.toValuationSubring (b : Place.integralClosureAt F' v) :=
    Subtype.ext hnorm
  rw [hsub]
  exact residue_norm_unit v b a ha

private theorem hasValue_norm_of_forall_hasValue {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F) (g : F') (a : Place K F' → Kˣ)
    (ha : ∀ w ∈ v.fiberOver F', w.HasValue g (a w)) :
    v.HasValue (Algebra.norm F g)
      (∏ w ∈ v.fiberOver F', (a w : K) ^ (w.ramificationIndex F * w.inertiaDeg F)) := by
  obtain ⟨b, rfl⟩ := exists_unit_of_forall_hasValue v g a ha
  exact hasValue_norm_of_unit v b a ha

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ)
    (v : Place K F) (g : F') (a : Place K F' → Kˣ)
    (ha : ∀ w ∈ Place.fiberAlong φ hφ v, w.HasValue g (a w)) :
    letI := algebraAlong φ
    v.HasValue (Algebra.norm F g)
      (∏ w ∈ Place.fiberAlong φ hφ v,
        (a w : K) ^ (w.ramificationIndexAlong φ * w.inertiaDegAlong φ hφ)) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : FiniteDimensional F F' := hfin
  haveI : Algebra.IsSeparable F F' := hsep
  have hfib : Place.fiberAlong φ hφ v = v.fiberOver F' := by
    change v.fiber F' = v.fiberOver F'
    exact Place.fiber_eq_fiberOver v
  have ha' : ∀ w ∈ v.fiberOver F', w.HasValue g (a w) := by
    intro w hw
    exact ha w (hfib ▸ hw)
  have h := hasValue_norm_of_forall_hasValue v g a ha'
  rw [hfib]
  exact h

#print axioms solution

end S_AlgebraicCurve_Place_hasValue_norm_along_of_separableAlong
end P2MW
export P2MW.S_AlgebraicCurve_Place_hasValue_norm_along_of_separableAlong (solution)
