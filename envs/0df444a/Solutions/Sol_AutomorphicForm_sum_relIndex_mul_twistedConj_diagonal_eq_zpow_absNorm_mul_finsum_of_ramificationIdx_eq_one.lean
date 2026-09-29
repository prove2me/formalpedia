-- Prove2me | solution 1 for AutomorphicForm.sum_relIndex_mul_twistedConj_diagonal_eq_zpow_absNorm_mul_finsum_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c09effbd-4a81-5ac2-8f40-dad0f2cee2f2

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Theorems.Thm_LocalGL2_iwasawa_decomposition_diag
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_sum_relIndex_mul_twistedConj_diagonal_eq_zpow_absNorm_mul_finsum_of_ramificationIdx_eq_one

set_option autoImplicit false

open NumberField IsDedekindDomain

noncomputable section

namespace TwistedUnfolding

section LocalIntegers

section CompactSubring

variable {E Γ₀ : Type*} [Field E] [LinearOrderedCommGroupWithZero Γ₀] [TopologicalSpace E]
  [IsTopologicalRing E]

private theorem val_le_one_of_mem_of_isCompact (w : Valuation E Γ₀) (hball : IsOpen {a : E | w a ≤ 1})
    (S : Subring E) (hS : IsCompact (S : Set E)) {x : E} (hx : x ∈ S) : w x ≤ 1 := by
  by_contra hcon
  have hlt : 1 < w x := lt_of_not_ge hcon
  have hcover : (S : Set E) ⊆ ⋃ s ∈ (S : Set E), (fun a : E => s + a) '' {a : E | w a ≤ 1} := by
    intro s hs
    refine Set.mem_iUnion₂.2 ⟨s, hs, 0, ?_, add_zero s⟩
    show w 0 ≤ 1
    rw [map_zero]
    exact zero_le_one
  obtain ⟨t, -, htfin, hsub⟩ := hS.elim_finite_subcover_image
    (fun s _ => (Homeomorph.addLeft s).isOpenMap _ hball) hcover
  have hmem : ∀ k : ℕ, x ^ (k + 1) ∈ (S : Set E) := fun k => S.pow_mem hx _
  choose f hft hf using fun k => Set.mem_iUnion₂.1 (hsub (hmem k))
  haveI : Finite t := htfin.to_subtype
  obtain ⟨i, j, hij, hfij⟩ :=
    Finite.exists_ne_map_eq_of_infinite fun k : ℕ => (⟨f k, hft k⟩ : t)
  have hfij' : f i = f j := congrArg Subtype.val hfij
  obtain ⟨a, ha, hxa⟩ := hf i
  obtain ⟨b, hb, hxb⟩ := hf j

  have hdiff : w (x ^ (i + 1) - x ^ (j + 1)) ≤ 1 := by
    have : x ^ (i + 1) - x ^ (j + 1) = a - b := by
      rw [← hxa, ← hxb, hfij']
      exact add_sub_add_left_eq_sub a b (f j)
    rw [this]
    exact (w.map_sub a b).trans (max_le ha hb)

  rcases lt_or_gt_of_ne hij with h | h
  · have hpow : w (x ^ (i + 1)) < w (x ^ (j + 1)) := by
      rw [map_pow, map_pow]
      exact pow_lt_pow_right₀ hlt (by omega)
    rw [Valuation.map_sub_swap, Valuation.map_sub_eq_of_lt_left _ hpow, map_pow] at hdiff
    exact absurd hdiff (not_le.2 (one_lt_pow₀ hlt (Nat.succ_ne_zero j)))
  · have hpow : w (x ^ (j + 1)) < w (x ^ (i + 1)) := by
      rw [map_pow, map_pow]
      exact pow_lt_pow_right₀ hlt (by omega)
    rw [Valuation.map_sub_eq_of_lt_left _ hpow, map_pow] at hdiff
    exact absurd hdiff (not_le.2 (one_lt_pow₀ hlt (Nat.succ_ne_zero i)))

end CompactSubring

section Completion

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

private theorem mem_adicCompletionIntegers_of_mem_of_isCompact (S : Subring (u.adicCompletion F))
    (hS : IsCompact (S : Set (u.adicCompletion F))) {x : u.adicCompletion F} (hx : x ∈ S) :
    x ∈ u.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  refine val_le_one_of_mem_of_isCompact (Valued.v : Valuation (u.adicCompletion F) _) ?_ S hS hx
  have h := (AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 F) F).out u
  convert h using 1
  rfl

end Completion

section ContinuousMap

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
variable (F' : Type) [Field F'] [NumberField F'] (u' : HeightOneSpectrum (𝓞 F'))

private theorem map_mem_adicCompletionIntegers_of_continuous (f : u.adicCompletion F →+* u'.adicCompletion F')
    (hf : Continuous f) {y : u.adicCompletion F} (hy : y ∈ u.adicCompletionIntegers F) :
    f y ∈ u'.adicCompletionIntegers F' := by
  refine mem_adicCompletionIntegers_of_mem_of_isCompact F' u'
    ((u.adicCompletionIntegers F).toSubring.map f) ?_ ⟨y, hy, rfl⟩
  rw [Subring.coe_map]
  exact (isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 F) F u)).image hf

private theorem valued_coe_unit (x : (u.adicCompletionIntegers F)ˣ) :
    Valued.v ((x : u.adicCompletionIntegers F) : u.adicCompletion F) = 1 := by
  have hmul : ((x : u.adicCompletionIntegers F) : u.adicCompletion F) *
      ((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F) = 1 :=
    congrArg Subtype.val (Units.mul_inv x)
  have hx : Valued.v ((x : u.adicCompletionIntegers F) : u.adicCompletion F) ≤ 1 := by
    have h := (x : u.adicCompletionIntegers F).2
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  have hxi : Valued.v (((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F) :
      u.adicCompletion F) ≤ 1 := by
    have h := ((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F).2
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  refine le_antisymm hx ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (((x : u.adicCompletionIntegers F) : u.adicCompletion F) *
        ((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F)) := by rw [hmul, map_one]
    _ = Valued.v ((x : u.adicCompletionIntegers F) : u.adicCompletion F) *
        Valued.v (((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F) :
          u.adicCompletion F) := map_mul _ _ _
    _ ≤ Valued.v ((x : u.adicCompletionIntegers F) : u.adicCompletion F) := mul_le_of_le_one_right' hxi

end ContinuousMap

section Pair

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
  (L : Type) [Field L] [NumberField L] [Algebra K L] (w : v.Extension (𝓞 L))

private theorem irreducible_of_valued_eq {π : v.adicCompletionIntegers K}
    (hπ : Valued.v (π : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) : Irreducible π :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    (HeightOneSpectrum.adicCompletion.uniformizer_ne_zero hπ)
    (HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer K v hπ)

private theorem natCard_residueField_eq_absNorm :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField K v).symm.toEquiv

private theorem exists_valued_eq_ofAdd {x : v.adicCompletion K} (hx : x ≠ 0) :
    ∃ j : ℤ, Valued.v x = ((Multiplicative.ofAdd j : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rcases h0 : Valued.v x with _ | g
  · exact absurd h0 ((Valuation.ne_zero_iff _).2 hx)
  · exact ⟨Multiplicative.toAdd g, by rw [ofAdd_toAdd]; rfl⟩

private theorem exists_pow_mul_mem_integers {π : v.adicCompletion K}
    (hπ : Valued.v π = Multiplicative.ofAdd (-1 : ℤ)) (x : v.adicCompletion K) :
    ∃ k : ℕ, π ^ k * x ∈ v.adicCompletionIntegers K := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  obtain ⟨j, hj⟩ := exists_valued_eq_ofAdd K v hx
  refine ⟨j.toNat, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_pow, hπ, hj, ← WithZero.coe_pow,
    ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_nsmul, ← ofAdd_add, ← ofAdd_zero]
  simp only [smul_neg, nsmul_eq_mul, mul_one, Multiplicative.ofAdd_le]
  omega

private theorem exists_zpow_mul_unit {π : v.adicCompletion K} (hπ : Valued.v π = Multiplicative.ofAdd (-1 : ℤ))
    (x : (v.adicCompletion K)ˣ) :
    ∃ (j : ℤ) (y : (v.adicCompletion K)ˣ), (y : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
      ((y⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
      (x : v.adicCompletion K) = π ^ j * y := by
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  obtain ⟨i, hi⟩ := exists_valued_eq_ofAdd K v x.ne_zero

  have hval : Valued.v (π ^ i * (x : v.adicCompletion K)) = 1 := by
    rw [map_mul, map_zpow₀, hπ, hi, ← WithZero.coe_zpow, ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_inj,
      ← ofAdd_zsmul, ← ofAdd_add]
    simp
  refine ⟨-i, Units.mk0 _ (mul_ne_zero (zpow_ne_zero i hπ0) x.ne_zero), ?_, ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_mk0, hval]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, hval, inv_one]
  · rw [Units.val_mk0, zpow_neg, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero i hπ0), one_mul]

private theorem algebraMap_mem_integers {c : v.adicCompletion K} (hc : c ∈ v.adicCompletionIntegers K) :
    algebraMap (v.adicCompletion K) (w.1.adicCompletion L) c ∈ w.1.adicCompletionIntegers L :=
  map_mem_adicCompletionIntegers_of_continuous K v L w.1 (algebraMap (v.adicCompletion K) (w.1.adicCompletion L))
    (w.adicCompletionSemialgHom_continuous K L) hc

private theorem valued_algebraMap_eq
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1) {π : v.adicCompletion K}
    (hπ : Valued.v π = Multiplicative.ofAdd (-1 : ℤ)) :
    Valued.v (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) π) = Multiplicative.ofAdd (-1 : ℤ) := by
  change Valued.v (w.adicCompletionSemialgHom K L π) = _
  rw [w.valued_adicCompletionSemialgHom K L, hw, pow_one, hπ]

private theorem algEquiv_mem_integers [FiniteDimensional K L]
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) {y : w.1.adicCompletion L}
    (hy : y ∈ w.1.adicCompletionIntegers L) : θ y ∈ w.1.adicCompletionIntegers L :=
  map_mem_adicCompletionIntegers_of_continuous L w.1 L w.1 θ.toAlgHom.toRingHom
    (IsModuleTopology.continuous_of_linearMap θ.toLinearMap) hy

private noncomputable scoped instance intModule : Module (v.adicCompletionIntegers K) (w.1.adicCompletion L) :=
  Module.compHom (w.1.adicCompletion L) (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))

private theorem int_smul_def (r : v.adicCompletionIntegers K) (x : w.1.adicCompletion L) :
    r • x = (r : v.adicCompletion K) • x := rfl

private scoped instance intTower :
    IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) (w.1.adicCompletion L) :=
  ⟨fun r c x => by
    show ((r : v.adicCompletion K) * c) • x = (r : v.adicCompletion K) • (c • x)
    exact mul_smul _ _ _⟩

private def intLattice : Submodule (v.adicCompletionIntegers K) (w.1.adicCompletion L) where
  carrier := w.1.adicCompletionIntegers L
  add_mem' := fun ha hb => add_mem ha hb
  zero_mem' := zero_mem _
  smul_mem' := fun r x hx => by
    rw [int_smul_def, Algebra.smul_def]
    exact mul_mem (algebraMap_mem_integers K v L w r.2) hx

end Pair

end LocalIntegers

section TwistedDeterminant

open Module Polynomial

variable {F E : Type} [Field F] [Field E] [Algebra F E]

private theorem orderOf_eq_finrank [FiniteDimensional F E] (θ : E ≃ₐ[F] E)
    (hθ : ∀ x : E, θ x = x ↔ x ∈ Set.range (algebraMap F E)) : orderOf θ = Module.finrank F E := by
  have hfix : IntermediateField.fixedField (Subgroup.zpowers θ) = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [IntermediateField.mem_bot]
    exact (hθ x).1 (hx ⟨θ, Subgroup.mem_zpowers θ⟩)
  have htower := Module.finrank_mul_finrank F (IntermediateField.fixedField (Subgroup.zpowers θ)) E
  rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hfix, IntermediateField.finrank_bot,
    one_mul] at htower
  exact htower

private def twistedShift (θ : E ≃ₐ[F] E) (c : E) : E →ₗ[F] E :=
  θ.symm.toLinearMap ∘ₗ LinearMap.mulLeft F c

private def shiftCoeff (θ : E ≃ₐ[F] E) (c : E) (i : ℕ) : E :=
  ∏ j ∈ Finset.range i, (θ.symm ^ (j + 1)) c

private theorem twistedShift_pow_apply (θ : E ≃ₐ[F] E) (c : E) (i : ℕ) (x : E) :
    (twistedShift θ c ^ i) x = shiftCoeff θ c i * (θ.symm ^ i) x := by
  induction i with
  | zero => simp [shiftCoeff]
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    simp only [twistedShift, LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgEquiv.toLinearMap_apply, map_mul,
      shiftCoeff, Finset.prod_range_succ', pow_zero, AlgEquiv.one_apply, map_prod, pow_succ', AlgEquiv.mul_apply]
    ring

private theorem shiftCoeff_ne_zero (θ : E ≃ₐ[F] E) {c : E} (hc : c ≠ 0) (i : ℕ) :
    shiftCoeff θ c i ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => (map_ne_zero_iff _ (AlgEquiv.injective _)).2 hc

private theorem shiftCoeff_orderOf (θ : E ≃ₐ[F] E) (c : E) :
    shiftCoeff θ c (orderOf θ) = ∏ i ∈ Finset.range (orderOf θ), (θ ^ i) c := by
  unfold shiftCoeff
  rw [← Finset.prod_range_reflect (fun i => (θ ^ i) c) (orderOf θ)]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  congr 1
  rw [← AlgEquiv.aut_inv, inv_pow, inv_eq_iff_mul_eq_one, ← pow_add]
  have : j + 1 + (orderOf θ - 1 - j) = orderOf θ := by omega
  rw [this, pow_orderOf_eq_one]

private theorem twistedShift_pow_orderOf (θ : E ≃ₐ[F] E) (c : E) (μ : F)
    (hμ : algebraMap F E μ = ∏ i ∈ Finset.range (orderOf θ), (θ ^ i) c) :
    twistedShift θ c ^ orderOf θ = algebraMap F (Module.End F E) μ := by
  ext x
  rw [twistedShift_pow_apply, shiftCoeff_orderOf, ← hμ, Module.algebraMap_end_apply, Algebra.smul_def,
    ← AlgEquiv.aut_inv, inv_pow, pow_orderOf_eq_one, inv_one, AlgEquiv.one_apply]

private theorem eq_zero_of_aeval_twistedShift (θ : E ≃ₐ[F] E) {c : E} (hc : c ≠ 0) {p : F[X]}
    (hdeg : p.natDegree < orderOf θ) (hp : aeval (twistedShift θ c) p = 0) : p = 0 := by
  classical
  set n := orderOf θ with hn

  let f : Fin n → (E →* E) := fun i => ((θ.symm ^ (i : ℕ)).toAlgHom : E →ₐ[F] E).toRingHom.toMonoidHom
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : θ.symm ^ (i : ℕ) = θ.symm ^ (j : ℕ) := by
      ext x
      exact DFunLike.congr_fun hij x
    have hord : orderOf θ.symm = n := by rw [← AlgEquiv.aut_inv, orderOf_inv]
    exact Fin.ext (pow_injOn_Iio_orderOf (by rw [hord]; exact i.2) (by rw [hord]; exact j.2) h1)
  have hli : LinearIndependent E fun i : Fin n => ((f i : E →* E) : E → E) :=
    (linearIndependent_monoidHom E E).comp f hf

  have hrel : ∑ i : Fin n, (p.coeff i • shiftCoeff θ c i) • ((f i : E →* E) : E → E) = 0 := by
    funext x
    have hx := LinearMap.congr_fun hp x
    rw [aeval_eq_sum_range' hdeg, LinearMap.sum_apply, Finset.sum_range, LinearMap.zero_apply] at hx
    rw [Finset.sum_apply, Pi.zero_apply, ← hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, LinearMap.smul_apply, twistedShift_pow_apply, smul_eq_mul, smul_mul_assoc]
    rfl
  have hcoeff : ∀ i : Fin n, p.coeff i = 0 := by
    intro i
    have h0 := Fintype.linearIndependent_iff.1 hli _ hrel i
    rcases smul_eq_zero.1 h0 with h | h
    · exact h
    · exact absurd h (shiftCoeff_ne_zero θ hc i)
  ext i
  rcases lt_or_ge i n with hi | hi
  · exact hcoeff ⟨i, hi⟩
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg hi)

private theorem charpoly_twistedShift [FiniteDimensional F E] (θ : E ≃ₐ[F] E)
    (hord : orderOf θ = Module.finrank F E) {c : E} (hc : c ≠ 0) (μ : F)
    (hμ : algebraMap F E μ = ∏ i ∈ Finset.range (orderOf θ), (θ ^ i) c) :
    (twistedShift θ c).charpoly = X ^ orderOf θ - C μ := by
  have hn : orderOf θ ≠ 0 := by rw [hord]; exact Module.finrank_pos.ne'
  have hmonic : (X ^ orderOf θ - C μ : F[X]).Monic := monic_X_pow_sub_C μ hn
  have hroot : aeval (twistedShift θ c) (X ^ orderOf θ - C μ : F[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, twistedShift_pow_orderOf θ c μ hμ, sub_self]
  have hmin : minpoly F (twistedShift θ c) = X ^ orderOf θ - C μ := by
    have hdvd : minpoly F (twistedShift θ c) ∣ X ^ orderOf θ - C μ := minpoly.dvd F _ hroot
    have hle : (X ^ orderOf θ - C μ : F[X]).natDegree ≤ (minpoly F (twistedShift θ c)).natDegree := by
      by_contra hlt
      push Not at hlt
      rw [natDegree_X_pow_sub_C] at hlt
      exact minpoly.ne_zero (twistedShift θ c).isIntegral (eq_zero_of_aeval_twistedShift θ hc hlt (minpoly.aeval F _))
    exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (twistedShift θ c).isIntegral) hmonic hdvd hle).symm
  have hdvd' : minpoly F (twistedShift θ c) ∣ (twistedShift θ c).charpoly := LinearMap.minpoly_dvd_charpoly _
  have hdeg' : (twistedShift θ c).charpoly.natDegree ≤ (minpoly F (twistedShift θ c)).natDegree := by
    rw [LinearMap.charpoly_natDegree, hmin, natDegree_X_pow_sub_C, hord]
  rw [← hmin]
  exact eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (twistedShift θ c).isIntegral) (LinearMap.charpoly_monic _)
    hdvd' hdeg'

private theorem det_toLinearMap_sub_mulLeft [FiniteDimensional F E] (θ : E ≃ₐ[F] E)
    (hord : orderOf θ = Module.finrank F E) {c : E} (hc : c ≠ 0) (μ : F)
    (hμ : algebraMap F E μ = ∏ i ∈ Finset.range (orderOf θ), (θ ^ i) c) :
    LinearMap.det (θ.toLinearMap - LinearMap.mulLeft F c) = LinearMap.det θ.toLinearMap * (1 - μ) := by
  have hfactor : θ.toLinearMap - LinearMap.mulLeft F c = θ.toLinearMap ∘ₗ (1 - twistedShift θ c) := by
    ext x
    simp [twistedShift, AlgEquiv.toLinearMap_apply]
  have hcharpoly := charpoly_twistedShift θ hord hc μ hμ
  have hev := LinearMap.eval_charpoly (twistedShift θ c) 1
  rw [hcharpoly, eval_sub, eval_pow, eval_X, eval_C, one_pow, map_one] at hev
  rw [hfactor, LinearMap.det_comp, ← hev]

private theorem det_toLinearMap_pow_orderOf [FiniteDimensional F E] (θ : E ≃ₐ[F] E) :
    LinearMap.det θ.toLinearMap ^ orderOf θ = 1 := by
  rw [← map_pow, ← AlgEquiv.pow_toLinearMap, pow_orderOf_eq_one, AlgEquiv.one_toLinearMap, Module.End.one_eq_id,
    LinearMap.det_id]

private theorem eq_zero_of_apply_eq_mul (θ : E ≃ₐ[F] E) (c : E) (μ : F)
    (hμ : algebraMap F E μ = ∏ i ∈ Finset.range (orderOf θ), (θ ^ i) c) (hμ1 : μ ≠ 1) (q : E) (hq : θ q = c * q) :
    q = 0 := by
  by_contra hq0
  have hstep : ∀ i : ℕ, (θ ^ (i + 1)) q = (θ ^ i) c * (θ ^ i) q := by
    intro i
    rw [pow_succ, AlgEquiv.mul_apply, hq, map_mul]
  have h1 : ∏ i ∈ Finset.range (orderOf θ), (θ ^ (i + 1)) q =
      (∏ i ∈ Finset.range (orderOf θ), (θ ^ i) c) * ∏ i ∈ Finset.range (orderOf θ), (θ ^ i) q := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => hstep i
  have h2 : ∏ i ∈ Finset.range (orderOf θ), (θ ^ (i + 1)) q = ∏ i ∈ Finset.range (orderOf θ), (θ ^ i) q := by
    have h3 := Finset.prod_range_succ' (fun i => (θ ^ i) q) (orderOf θ)
    rw [Finset.prod_range_succ, pow_orderOf_eq_one, AlgEquiv.one_apply, pow_zero, AlgEquiv.one_apply] at h3
    exact mul_right_cancel₀ hq0 h3.symm
  have hN : ∏ i ∈ Finset.range (orderOf θ), (θ ^ i) q ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => (map_ne_zero_iff _ (AlgEquiv.injective _)).2 hq0
  rw [h2] at h1
  have h4 : ∏ i ∈ Finset.range (orderOf θ), (θ ^ i) c = 1 := by
    have h5 := h1
    conv_lhs at h5 => rw [← one_mul (∏ i ∈ Finset.range (orderOf θ), (θ ^ i) q)]
    exact (mul_right_cancel₀ hN h5).symm
  rw [← hμ, ← (algebraMap F E).map_one] at h4
  exact hμ1 ((algebraMap F E).injective h4)

private theorem algebraMap_div_eq_prod (θ : E ≃ₐ[F] E) (n : ℕ) {a b : E} {α β : F}
    (hα : algebraMap F E α = ∏ i ∈ Finset.range n, (θ ^ i) a)
    (hβ : algebraMap F E β = ∏ i ∈ Finset.range n, (θ ^ i) b) :
    algebraMap F E (β / α) = ∏ i ∈ Finset.range n, (θ ^ i) (b / a) := by
  simp only [map_div₀, hα, hβ, Finset.prod_div_distrib]

end TwistedDeterminant

section QuotientSums

variable {E : Type} [AddCommGroup E]

private theorem finsum_prod_fst {A B : Type} [Finite B] (g : A → ℂ) (hg : (Function.support g).Finite) :
    ∑ᶠ p : A × B, g p.1 = (Nat.card B : ℂ) * ∑ᶠ a : A, g a := by
  classical
  haveI : Fintype B := Fintype.ofFinite B
  have hsub : Function.support (fun p : A × B => g p.1) ⊆ ↑(hg.toFinset ×ˢ (Finset.univ : Finset B)) := by
    intro p hp
    simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod, Set.mem_univ, and_true, Set.Finite.coe_toFinset]
    exact hp
  rw [finsum_eq_sum_of_support_subset _ hsub, finsum_eq_sum_of_support_subset g hg.coe_toFinset.symm.subset,
    Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card]

private theorem apply_out_symm_eq {O L : AddSubgroup E} (hLO : L ≤ O) (G : E → ℂ)
    (hG : ∀ x : E, ∀ o ∈ O, G (x + o) = G x) (p : (E ⧸ O) × (↥O ⧸ L.addSubgroupOf O)) :
    G (Quotient.out ((AddSubgroup.quotientEquivProdOfLE hLO).symm p)) = G (Quotient.out p.1) := by
  set e := AddSubgroup.quotientEquivProdOfLE hLO with he
  have h1 : (e (e.symm p)).1 = p.1 := by rw [Equiv.apply_symm_apply]
  have h2 : (e (e.symm p)).1 = (QuotientAddGroup.mk (Quotient.out (e.symm p)) : E ⧸ O) := by
    conv_lhs => rw [← QuotientAddGroup.out_eq' (e.symm p)]
    rfl
  rw [h2] at h1
  have h3 : (QuotientAddGroup.mk (Quotient.out p.1) : E ⧸ O) = p.1 := QuotientAddGroup.out_eq' p.1
  rw [← h3, QuotientAddGroup.eq] at h1
  have h4 := hG (Quotient.out (e.symm p)) _ h1
  rw [add_neg_cancel_left] at h4
  exact h4.symm

private theorem finsum_quotient_of_le {O L : AddSubgroup E} (hLO : L ≤ O) (hidx : L.relIndex O ≠ 0) (G : E → ℂ)
    (hG : ∀ x : E, ∀ o ∈ O, G (x + o) = G x)
    (hfin : (Function.support fun c : E ⧸ O => G (Quotient.out c)).Finite) :
    ∑ᶠ c : E ⧸ L, G (Quotient.out c) = (L.relIndex O : ℂ) * ∑ᶠ c : E ⧸ O, G (Quotient.out c) := by
  haveI : (L.addSubgroupOf O).FiniteIndex := ⟨hidx⟩
  calc ∑ᶠ c : E ⧸ L, G (Quotient.out c)
      = ∑ᶠ p : (E ⧸ O) × (↥O ⧸ L.addSubgroupOf O), G (Quotient.out ((AddSubgroup.quotientEquivProdOfLE hLO).symm p)) :=
        (finsum_comp_equiv (AddSubgroup.quotientEquivProdOfLE hLO).symm
          (f := fun c : E ⧸ L => G (Quotient.out c))).symm
    _ = ∑ᶠ p : (E ⧸ O) × (↥O ⧸ L.addSubgroupOf O), G (Quotient.out p.1) := finsum_congr (apply_out_symm_eq hLO G hG)
    _ = (L.relIndex O : ℂ) * ∑ᶠ c : E ⧸ O, G (Quotient.out c) := by
        rw [finsum_prod_fst _ hfin, ← AddSubgroup.index_eq_card]
        rfl

private theorem finite_support_quotient_of_le {O L : AddSubgroup E} (hLO : L ≤ O) (hidx : L.relIndex O ≠ 0)
    (G : E → ℂ) (hG : ∀ x : E, ∀ o ∈ O, G (x + o) = G x)
    (hfin : (Function.support fun c : E ⧸ O => G (Quotient.out c)).Finite) :
    (Function.support fun c : E ⧸ L => G (Quotient.out c)).Finite := by
  haveI : (L.addSubgroupOf O).FiniteIndex := ⟨hidx⟩
  set e := AddSubgroup.quotientEquivProdOfLE hLO with he
  refine ((hfin.prod (Set.finite_univ (α := ↥O ⧸ L.addSubgroupOf O))).preimage e.injective.injOn).subset ?_
  intro c hc
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, Function.mem_support]
  have h := apply_out_symm_eq hLO G hG (e c)
  rw [Equiv.symm_apply_apply] at h
  rw [← h]
  exact hc

private theorem apply_map_out_eq (ψ : E ≃+ E) (L : AddSubgroup E) (G : E → ℂ)
    (hG : ∀ x : E, ∀ o ∈ L.map ψ.toAddMonoidHom, G (x + o) = G x) (c : E ⧸ L) :
    G (ψ (Quotient.out c)) = G (Quotient.out (QuotientAddGroup.congr L (L.map ψ.toAddMonoidHom) ψ rfl c)) := by
  set e := QuotientAddGroup.congr L (L.map ψ.toAddMonoidHom) ψ rfl with he
  have h1 : (QuotientAddGroup.mk (ψ (Quotient.out c)) : E ⧸ L.map ψ.toAddMonoidHom) = e c := by
    conv_rhs => rw [← QuotientAddGroup.out_eq' c]
    rfl
  have h2 : (QuotientAddGroup.mk (Quotient.out (e c)) : E ⧸ L.map ψ.toAddMonoidHom) = e c :=
    QuotientAddGroup.out_eq' _
  rw [← h2, QuotientAddGroup.eq] at h1
  have h3 := hG (ψ (Quotient.out c)) _ h1
  rw [add_neg_cancel_left] at h3
  exact h3.symm

private theorem finsum_quotient_map (ψ : E ≃+ E) (L : AddSubgroup E) (G : E → ℂ)
    (hG : ∀ x : E, ∀ o ∈ L.map ψ.toAddMonoidHom, G (x + o) = G x) :
    ∑ᶠ c : E ⧸ L, G (ψ (Quotient.out c)) = ∑ᶠ c : E ⧸ L.map ψ.toAddMonoidHom, G (Quotient.out c) := by
  rw [← finsum_comp_equiv (QuotientAddGroup.congr L (L.map ψ.toAddMonoidHom) ψ rfl).toEquiv
    (f := fun c : E ⧸ L.map ψ.toAddMonoidHom => G (Quotient.out c))]
  exact finsum_congr fun c => apply_map_out_eq ψ L G hG c

private theorem finite_support_quotient_map (ψ : E ≃+ E) (L : AddSubgroup E) (G : E → ℂ)
    (hG : ∀ x : E, ∀ o ∈ L.map ψ.toAddMonoidHom, G (x + o) = G x)
    (hfin : (Function.support fun c : E ⧸ L.map ψ.toAddMonoidHom => G (Quotient.out c)).Finite) :
    (Function.support fun c : E ⧸ L => G (ψ (Quotient.out c))).Finite := by
  refine (hfin.preimage (QuotientAddGroup.congr L (L.map ψ.toAddMonoidHom) ψ rfl).injective.injOn).subset ?_
  intro c hc
  simp only [Set.mem_preimage, Function.mem_support] at hc ⊢
  rwa [apply_map_out_eq ψ L G hG c] at hc

private theorem finite_support_comp (O L : AddSubgroup E) (hLO : L ≤ O) (ψ : E ≃+ E)
    (hψL : L.map ψ.toAddMonoidHom ≤ O) (hidx' : (L.map ψ.toAddMonoidHom).relIndex O ≠ 0) (G : E → ℂ)
    (hGO : ∀ x : E, ∀ o ∈ O, G (x + o) = G x)
    (hfin : (Function.support fun c : E ⧸ O => G (Quotient.out c)).Finite) :
    (Function.support fun c : E ⧸ O => G (ψ (Quotient.out c))).Finite := by
  have h1 : (Function.support fun c : E ⧸ L.map ψ.toAddMonoidHom => G (Quotient.out c)).Finite :=
    finite_support_quotient_of_le hψL hidx' G hGO hfin
  have h2 : (Function.support fun c : E ⧸ L => G (ψ (Quotient.out c))).Finite :=
    finite_support_quotient_map ψ L G (fun x o ho => hGO x o (hψL ho)) h1
  let j : E ⧸ O → E ⧸ L := fun q => QuotientAddGroup.mk (Quotient.out q)
  have hj : Function.Injective j := by
    intro q q' h
    have h' := QuotientAddGroup.eq.1 h
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq]
    exact hLO h'
  refine (h2.preimage hj.injOn).subset ?_
  intro q hq
  simp only [Set.mem_preimage, Function.mem_support] at hq ⊢

  have hl : -Quotient.out q + Quotient.out (j q) ∈ L := by
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
  have hψ : ψ (-Quotient.out q + Quotient.out (j q)) ∈ O :=
    hψL (AddSubgroup.mem_map_of_mem ψ.toAddMonoidHom hl)
  have h3 : ψ (Quotient.out (j q)) = ψ (Quotient.out q) + ψ (-Quotient.out q + Quotient.out (j q)) := by
    rw [← map_add, add_neg_cancel_left]
  rw [h3, hGO _ _ hψ]
  exact hq

private theorem relIndex_mul_finsum_quotient_comp (O L : AddSubgroup E) (hLO : L ≤ O) (ψ : E ≃+ E)
    (hψL : L.map ψ.toAddMonoidHom ≤ O) (hidx : L.relIndex O ≠ 0) (hidx' : (L.map ψ.toAddMonoidHom).relIndex O ≠ 0)
    (G : E → ℂ) (hGO : ∀ x : E, ∀ o ∈ O, G (x + o) = G x)
    (hGψ : ∀ x : E, ∀ o ∈ O, G (x + ψ o) = G x)
    (hfin : (Function.support fun c : E ⧸ O => G (Quotient.out c)).Finite) :
    (L.relIndex O : ℂ) * ∑ᶠ c : E ⧸ O, G (ψ (Quotient.out c)) =
      ((L.map ψ.toAddMonoidHom).relIndex O : ℂ) * ∑ᶠ c : E ⧸ O, G (Quotient.out c) := by
  have hGψO : ∀ x : E, ∀ o ∈ O, G (ψ (x + o)) = G (ψ x) := fun x o ho => by rw [map_add]; exact hGψ _ o ho
  have hfin' : (Function.support fun c : E ⧸ O => G (ψ (Quotient.out c))).Finite :=
    finite_support_comp O L hLO ψ hψL hidx' G hGO hfin
  rw [← finsum_quotient_of_le hLO hidx (fun x => G (ψ x)) hGψO hfin',
    ← finsum_quotient_of_le hψL hidx' G hGO hfin]
  exact finsum_quotient_map ψ L G fun x o ho => hGO x o (hψL ho)

end QuotientSums

section IndexAndLattice

open Module

section PrincipalIdealDomain

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {M : Type} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

private theorem exists_card_quotient_range_eq (f : M →ₗ[R] M) (hf : Function.Injective f) :
    ∃ (ι : Type) (_ : Fintype ι) (d : ι → R), Associated (LinearMap.det f) (∏ i, d i) ∧
      Nat.card (M ⧸ LinearMap.range f) = ∏ i, Nat.card (R ⧸ Ideal.span ({d i} : Set R)) := by
  classical
  set N : Submodule R M := LinearMap.range f with hN
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective f hf
  have h : Module.finrank R N = Module.finrank R M := e.finrank_eq.symm
  let b := Module.Free.chooseBasis R M
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
  let g : M →ₗ[R] M := N.subtype ∘ₗ (e' : M →ₗ[R] N)
  refine ⟨Module.Free.ChooseBasisIndex R M, inferInstance, a, ?_, ?_⟩
  · have hfe : f = N.subtype ∘ₗ (e : M →ₗ[R] N) := by
      ext x
      rfl
    have hg : ∀ i, g (b' i) = a i • b' i := by
      intro i
      change (N.subtype) (b'.equiv ab (Equiv.refl _) (b' i)) = _
      rw [Basis.equiv_apply, Equiv.refl_apply]
      exact ab_eq i
    have hdet : LinearMap.det g = ∏ i, a i := by
      rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
      congr 1
      ext i j
      rw [LinearMap.toMatrix_apply, hg, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]
      by_cases hij : i = j
      · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
      · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
    rw [hfe, ← hdet]
    exact LinearMap.associated_det_comp_equiv N.subtype e e'
  · rw [Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv, Nat.card_pi]

end PrincipalIdealDomain

section DiscreteValuationRing

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

private theorem natCard_quotient_span_pow {ϖ : R} (hϖ : Irreducible ϖ) (k : ℕ) :
    Nat.card (R ⧸ Ideal.span ({ϖ ^ k} : Set R)) = Nat.card (IsLocalRing.ResidueField R) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, Ideal.span_singleton_one]
    haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.2 rfl
    exact Nat.card_of_subsingleton (0 : R ⧸ (⊤ : Ideal R))
  | succ k ih =>
    have hle : Ideal.span ({ϖ ^ (k + 1)} : Set R) ≤ Ideal.span ({ϖ ^ k} : Set R) :=
      Ideal.span_singleton_le_span_singleton.2 (Dvd.intro ϖ (pow_succ ϖ k).symm)
    classical
    rw [← Submodule.card_quotient_mul_card_quotient _ _ hle, ih, pow_succ (Nat.card (IsLocalRing.ResidueField R)) k,
      mul_comm _ (Nat.card (IsLocalRing.ResidueField R) ^ k)]
    congr 1

    let φ : R →ₗ[R] R ⧸ Ideal.span ({ϖ ^ (k + 1)} : Set R) :=
      (Ideal.span ({ϖ ^ (k + 1)} : Set R)).mkQ ∘ₗ LinearMap.toSpanSingleton R R (ϖ ^ k)
    have hrange :
        LinearMap.range φ =
          Submodule.map (Ideal.span ({ϖ ^ (k + 1)} : Set R)).mkQ (Ideal.span ({ϖ ^ k} : Set R)) := by
      rw [LinearMap.range_comp, LinearMap.range_toSpanSingleton, Ideal.submodule_span_eq]
    have hker : LinearMap.ker φ = Ideal.span ({ϖ} : Set R) := by
      ext r
      simp only [φ, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, smul_eq_mul,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
      rw [pow_succ, mul_comm (ϖ ^ k) ϖ]
      exact mul_dvd_mul_iff_right (pow_ne_zero k hϖ.ne_zero)
    have hmax : IsLocalRing.maximalIdeal R = Ideal.span ({ϖ} : Set R) :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    calc Nat.card (Submodule.map (Ideal.span ({ϖ ^ (k + 1)} : Set R)).mkQ (Ideal.span ({ϖ ^ k} : Set R)))
        = Nat.card (LinearMap.range φ) := by rw [hrange]
      _ = Nat.card (R ⧸ LinearMap.ker φ) := (Nat.card_congr φ.quotKerEquivRange.toEquiv).symm
      _ = Nat.card (IsLocalRing.ResidueField R) := by
          rw [hker]
          exact (Nat.card_congr (Submodule.quotEquivOfEq _ _ hmax).toEquiv).symm

private theorem pow_eq_of_associated {ϖ : R} (hϖ : Irreducible ϖ) {j k : ℕ} (h : Associated (ϖ ^ j) (ϖ ^ k)) :
    j = k := by
  have h1 := IsDiscreteValuationRing.addVal_pow ϖ j
  have h2 := IsDiscreteValuationRing.addVal_pow ϖ k
  rw [IsDiscreteValuationRing.addVal_uniformizer hϖ] at h1 h2
  have hv : IsDiscreteValuationRing.addVal R (ϖ ^ j) = IsDiscreteValuationRing.addVal R (ϖ ^ k) :=
    le_antisymm (IsDiscreteValuationRing.addVal_le_iff_dvd.2 h.dvd)
      (IsDiscreteValuationRing.addVal_le_iff_dvd.2 h.symm.dvd)
  rw [h1, h2, nsmul_one, nsmul_one] at hv
  exact_mod_cast hv

variable {M : Type} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

private theorem natCard_quotient_range_eq_pow (f : M →ₗ[R] M) (hf : Function.Injective f) {ϖ : R}
    (hϖ : Irreducible ϖ) {k : ℕ} (hdet : Associated (LinearMap.det f) (ϖ ^ k)) :
    Nat.card (M ⧸ LinearMap.range f) = Nat.card (IsLocalRing.ResidueField R) ^ k := by
  classical
  obtain ⟨ι, _, d, hassoc, hcard⟩ := exists_card_quotient_range_eq f hf
  have hd : ∀ i, d i ≠ 0 := by
    intro i hi
    have hprod : ∏ j, d j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hprod] at hassoc
    have hzero : LinearMap.det f = 0 := (associated_zero_iff_eq_zero _).1 hassoc
    rw [hzero] at hdet
    exact pow_ne_zero k hϖ.ne_zero ((associated_zero_iff_eq_zero _).1 hdet.symm)
  choose e u hde using fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hd i) hϖ
  have hcard_i : ∀ i, Nat.card (R ⧸ Ideal.span ({d i} : Set R)) = Nat.card (IsLocalRing.ResidueField R) ^ e i := by
    intro i
    rw [hde i, Ideal.span_singleton_mul_left_unit (u i).isUnit]
    exact natCard_quotient_span_pow hϖ (e i)
  have hprod : Associated (∏ i, d i) (ϖ ^ ∑ i, e i) := by
    simp_rw [hde, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    refine ⟨(∏ i, u i)⁻¹, ?_⟩
    rw [← Units.coe_prod, mul_right_comm, Units.mul_inv, one_mul]
  have hsum : ∑ i, e i = k := pow_eq_of_associated hϖ (hprod.symm.trans (hassoc.symm.trans hdet))
  rw [hcard, Finset.prod_congr rfl fun i _ => hcard_i i, Finset.prod_pow_eq_pow_sum, hsum]

end DiscreteValuationRing

section Lattice

variable {R F E : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F] [Algebra R F]
  [AddCommGroup E] [Module F E] [Module R E] [IsScalarTower R F E]

omit [IsDomain R] [IsDiscreteValuationRing R] in

private theorem exists_pow_smul_eq_algebraMap {ϖ : R} (hF : ∀ c : F, ∃ k : ℕ, ∃ r : R, ϖ ^ k • c = algebraMap R F r)
    {ι : Type} [Fintype ι] (c : ι → F) : ∃ k : ℕ, ∀ i, ∃ r : R, ϖ ^ k • c i = algebraMap R F r := by
  classical
  choose k r hkr using fun i => hF (c i)
  refine ⟨Finset.univ.sup k, fun i => ?_⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := k) (Finset.mem_univ i))
  refine ⟨ϖ ^ d * r i, ?_⟩
  rw [hd, pow_add, mul_comm, mul_smul, hkr i, map_mul, Algebra.smul_def, map_pow]

omit [IsDomain R] [IsDiscreteValuationRing R] in

private theorem exists_pow_smul_map_mem (M : Submodule R E) (hM : M.FG) {ϖ : R}
    (hE : ∀ x : E, ∃ k : ℕ, ϖ ^ k • x ∈ M) (ψ : E →ₗ[F] E) : ∃ N : ℕ, ∀ x ∈ M, ϖ ^ N • ψ x ∈ M := by
  classical
  obtain ⟨s, hs⟩ := hM
  choose k hk using fun x : E => hE (ψ x)
  refine ⟨s.sup k, fun x hx => ?_⟩

  let g : E →ₗ[R] E := (ϖ ^ s.sup k) • ψ.restrictScalars R
  have hg : ∀ y ∈ (s : Set E), g y ∈ M := by
    intro y hy
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := k) hy)
    show ϖ ^ s.sup k • ψ y ∈ M
    rw [hd, pow_add, mul_comm, mul_smul]
    exact M.smul_mem _ (hk y)
  have hle : Submodule.span R (s : Set E) ≤ M.comap g := Submodule.span_le.2 hg
  rw [hs] at hle
  exact hle hx

variable (M : Submodule R E)

omit [IsDomain R] [IsDiscreteValuationRing R] in

private theorem linearIndependent_subtype_comp {ι : Type} [Fintype ι] (b : Basis ι R M) {ϖ : R}
    (hϖ0 : algebraMap R F ϖ ≠ 0) (hF : ∀ c : F, ∃ k : ℕ, ∃ r : R, ϖ ^ k • c = algebraMap R F r) :
    LinearIndependent F fun i => (b i : E) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  obtain ⟨k, hk⟩ := exists_pow_smul_eq_algebraMap hF c
  choose r hr using hk
  have hsum : ∑ i, r i • b i = 0 := by
    apply Subtype.val_injective
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
    have h2 : ∑ i, (ϖ ^ k • c i) • (b i : E) = 0 := by
      have h3 : ∑ i, (ϖ ^ k • c i) • (b i : E) = ϖ ^ k • ∑ i, c i • (b i : E) := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => smul_assoc _ _ _
      rw [h3, hc, smul_zero]
    calc ∑ i, r i • (b i : E) = ∑ i, (ϖ ^ k • c i) • (b i : E) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hr i, algebraMap_smul]
      _ = 0 := h2
  have hr0 : ∀ i, r i = 0 := Fintype.linearIndependent_iff.1 b.linearIndependent r hsum
  intro i
  have h := hr i
  rw [hr0 i, map_zero, Algebra.smul_def, map_pow] at h
  exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hϖ0)

omit [IsDomain R] [IsDiscreteValuationRing R] in
private theorem span_subtype_comp_eq_top {ι : Type} [Fintype ι] (b : Basis ι R M) {ϖ : R}
    (hϖ0 : algebraMap R F ϖ ≠ 0) (hE : ∀ x : E, ∃ k : ℕ, ϖ ^ k • x ∈ M) :
    Submodule.span F (Set.range fun i => (b i : E)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨k, hk⟩ := hE x

  have hmem : ϖ ^ k • x ∈ Submodule.span F (Set.range fun i => (b i : E)) := by
    have h1 : (⟨ϖ ^ k • x, hk⟩ : M) ∈ Submodule.span R (Set.range b) := by rw [b.span_eq]; trivial
    have h2 : ∀ m ∈ Submodule.span R (Set.range b), (m : E) ∈ Submodule.span F (Set.range fun i => (b i : E)) := by
      intro m hm
      induction hm using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact Submodule.subset_span ⟨i, rfl⟩
      | zero =>
        rw [Submodule.coe_zero]
        exact Submodule.zero_mem _
      | add y z _ _ hy hz =>
        rw [Submodule.coe_add]
        exact Submodule.add_mem _ hy hz
      | smul a y _ hy =>
        rw [Submodule.coe_smul, ← algebraMap_smul F a (y : E)]
        exact Submodule.smul_mem _ _ hy
    exact h2 _ h1
  have hϖk : algebraMap R F (ϖ ^ k) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ hϖ0
  have hx : x = (algebraMap R F (ϖ ^ k))⁻¹ • (ϖ ^ k • x) := by
    rw [← algebraMap_smul F (ϖ ^ k) x, smul_smul, inv_mul_cancel₀ hϖk, one_smul]
  rw [hx]
  exact Submodule.smul_mem _ _ hmem

private def latticeBasis {ι : Type} [Fintype ι] (b : Basis ι R M) {ϖ : R} (hϖ0 : algebraMap R F ϖ ≠ 0)
    (hF : ∀ c : F, ∃ k : ℕ, ∃ r : R, ϖ ^ k • c = algebraMap R F r) (hE : ∀ x : E, ∃ k : ℕ, ϖ ^ k • x ∈ M) :
    Basis ι F E :=
  Basis.mk (linearIndependent_subtype_comp M b hϖ0 hF) (span_subtype_comp_eq_top M b hϖ0 hE).ge

omit [IsDomain R] [IsDiscreteValuationRing R] in

private theorem algebraMap_det_restrict [Module.Free R M] [Module.Finite R M] {ϖ : R}
    (hϖ0 : algebraMap R F ϖ ≠ 0) (hF : ∀ c : F, ∃ k : ℕ, ∃ r : R, ϖ ^ k • c = algebraMap R F r)
    (hE : ∀ x : E, ∃ k : ℕ, ϖ ^ k • x ∈ M) (ψ : E →ₗ[F] E) (hψ : ∀ x ∈ M, ψ x ∈ M) :
    algebraMap R F (LinearMap.det ((ψ.restrictScalars R).restrict hψ)) = LinearMap.det ψ := by
  classical
  let b := Module.Free.chooseBasis R M
  let bE := latticeBasis M b hϖ0 hF hE
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix bE, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]

  have hbE : ∀ l, bE l = (b l : E) := fun l => Basis.mk_apply _ _ l
  have hval : ψ (bE j) = ∑ l, algebraMap R F (b.repr ((ψ.restrictScalars R).restrict hψ (b j)) l) • bE l := by
    rw [hbE]
    have h := congrArg (fun m : M => (m : E)) (b.sum_repr ((ψ.restrictScalars R).restrict hψ (b j)))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [show ψ (b j : E) = (((ψ.restrictScalars R).restrict hψ) (b j) : E) from rfl, ← h]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hbE, algebraMap_smul]
  rw [hval, map_sum]
  simp only [map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.finsetSum_apply,
    Finsupp.single_apply]
  simp [Finset.sum_ite_eq']

omit [IsDomain R] [IsDiscreteValuationRing R] in

private theorem relIndex_map_subtype (P : Submodule R M) :
    (P.map M.subtype).toAddSubgroup.relIndex M.toAddSubgroup = Nat.card (M ⧸ P) := by
  unfold AddSubgroup.relIndex
  rw [AddSubgroup.index_eq_card]
  have h : (P.map M.subtype).toAddSubgroup.addSubgroupOf M.toAddSubgroup = P.toAddSubgroup := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact (Subtype.ext hyx : y = x) ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [h]
  exact Nat.card_congr (Equiv.refl _)

omit [IsDomain R] [IsDiscreteValuationRing R] in
private theorem map_subtype_range_restrict (ψ : E →ₗ[F] E) (hψ : ∀ x ∈ M, ψ x ∈ M) :
    (LinearMap.range ((ψ.restrictScalars R).restrict hψ)).map M.subtype = M.map (ψ.restrictScalars R) := by
  ext x
  simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.subtype_apply, LinearMap.restrictScalars_apply]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, y.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(ψ.restrictScalars R).restrict hψ ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, rfl⟩

private theorem relIndex_map_eq_pow [Module.Free R M] [Module.Finite R M] {ϖ : R} (hϖ : Irreducible ϖ)
    (ψ : E →ₗ[F] E) (hψ : ∀ x ∈ M, ψ x ∈ M) (hinj : Function.Injective ψ) {k : ℕ}
    (hdet : Associated (LinearMap.det ((ψ.restrictScalars R).restrict hψ)) (ϖ ^ k)) :
    (M.map (ψ.restrictScalars R)).toAddSubgroup.relIndex M.toAddSubgroup =
      Nat.card (IsLocalRing.ResidueField R) ^ k := by
  rw [← map_subtype_range_restrict M ψ hψ, relIndex_map_subtype]
  exact natCard_quotient_range_eq_pow _ (fun x y hxy => Subtype.ext (hinj (congrArg Subtype.val hxy))) hϖ hdet

end Lattice

end IndexAndLattice

section ValuationExponents

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

private theorem exists_associated_pow_of_valued_eq {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (hϖv : Valued.v (ϖ : u.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (hunit : ∀ x : (u.adicCompletionIntegers F)ˣ,
      Valued.v ((x : u.adicCompletionIntegers F) : u.adicCompletion F) = 1)
    {r : u.adicCompletionIntegers F} (hr : r ≠ 0) {z : ℤ}
    (hz : Valued.v (r : u.adicCompletion F) = Multiplicative.ofAdd z) :
    ∃ k : ℕ, (k : ℤ) = -z ∧ Associated r (ϖ ^ k) := by
  obtain ⟨n, e, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  refine ⟨n, ?_, associated_unit_mul_left _ _ e.isUnit⟩
  change Valued.v (((e : u.adicCompletionIntegers F) : u.adicCompletion F) * (ϖ : u.adicCompletion F) ^ n) = _ at hz
  rw [map_mul, map_pow, hunit, hϖv, one_mul, ← WithZero.coe_pow, WithZero.coe_inj, ← ofAdd_nsmul] at hz
  have h := Multiplicative.ofAdd.injective hz
  simp only [smul_neg, nsmul_eq_mul, mul_one] at h
  omega

private theorem valued_eq_one_of_pow_eq_one {x : u.adicCompletion F} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n = 1) :
    Valued.v x = 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hx
    exact zero_ne_one hx
  have h : Valued.v x ^ n = 1 := by rw [← map_pow, hx, map_one]
  obtain ⟨g, hg⟩ : ∃ g : Multiplicative ℤ, (g : WithZero (Multiplicative ℤ)) = Valued.v x := by
    rcases h0 : Valued.v x with _ | g
    · exact absurd h0 ((Valuation.ne_zero_iff _).2 hx0)
    · exact ⟨g, rfl⟩
  rw [← hg, ← WithZero.coe_pow, ← WithZero.coe_one, WithZero.coe_inj] at h
  have h2 := congrArg Multiplicative.toAdd h
  rw [toAdd_pow, toAdd_one] at h2
  have hg1 : g = 1 := toAdd_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left hn)
  rw [← hg, hg1, WithZero.coe_one]

end ValuationExponents

section LocalLayer

section Unipotent

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private noncomputable def unipOf (y : v.adicCompletion K) : GL (Fin 2) (v.adicCompletion K) where
  val := !![1, y; 0, 1]
  inv := !![1, -y; 0, 1]
  val_inv := by simp [Matrix.one_fin_two]
  inv_val := by simp [Matrix.one_fin_two]

private theorem coe_unipOf (y : v.adicCompletion K) :
    (unipOf y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![1, y; 0, 1] := rfl

private theorem coe_unipOf_inv (y : v.adicCompletion K) :
    ((unipOf y)⁻¹ : GL (Fin 2) (v.adicCompletion K)) = (unipOf (-y) : GL (Fin 2) (v.adicCompletion K)) :=
  Units.ext rfl

private theorem unipOf_mul (y z : v.adicCompletion K) : unipOf y * unipOf z = unipOf (y + z) :=
  Units.ext <| by simp [coe_unipOf, add_comm]

private theorem unipOf_zero : (unipOf (0 : v.adicCompletion K)) = 1 :=
  Units.ext <| by simp [coe_unipOf, Matrix.one_fin_two]

private noncomputable def diagOf (a b : (v.adicCompletion K)ˣ) : GL (Fin 2) (v.adicCompletion K) where
  val := !![(a : v.adicCompletion K), 0; 0, (b : v.adicCompletion K)]
  inv := !![((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K), 0; 0,
    ((b⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)]
  val_inv := by simp [Matrix.one_fin_two]
  inv_val := by simp [Matrix.one_fin_two]

private theorem coe_diagOf (a b : (v.adicCompletion K)ˣ) :
    (diagOf a b : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(a : v.adicCompletion K), 0; 0, (b : v.adicCompletion K)] := rfl

private theorem coe_diagOf_inv (a b : (v.adicCompletion K)ˣ) :
    (((diagOf a b)⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K), 0; 0,
        ((b⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)] := rfl

private theorem unipOf_mul_diagOf (a b : (v.adicCompletion K)ˣ) (z w : v.adicCompletion K)
    (hw : (a : v.adicCompletion K) * w = z * b) : unipOf z * diagOf a b = diagOf a b * unipOf w :=
  Units.ext <| by simp [coe_unipOf, coe_diagOf, hw]

private theorem inv_mul_mul_unipOf (α β : (v.adicCompletion K)ˣ) (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)])
    (c : v.adicCompletion K) (hc : (α : v.adicCompletion K) * c = α - β) (w : v.adicCompletion K) :
    (unipOf w)⁻¹ * γ * unipOf w = γ * unipOf (c * w) := by
  have hcw : (α : v.adicCompletion K) * (c * w) = α * w + -(w * β) := by
    rw [← mul_assoc, hc]
    ring
  refine Units.ext ?_
  simp [coe_unipOf_inv, coe_unipOf, hγ, hcw]

private theorem eq_mul_unipOf_of_upper (α β : (v.adicCompletion K)ˣ) (γ g : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)])
    (h10 : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)
    (h00 : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 = α)
    (h11 : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = β) :
    g = γ * unipOf ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 / (α : v.adicCompletion K)) := by
  refine Units.ext ?_
  rw [Units.val_mul, hγ, coe_unipOf, Matrix.mul_fin_two, mul_div_cancel₀ _ α.ne_zero]
  conv_lhs => rw [Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))]
  rw [h10, h00, h11]
  simp

private theorem mul_unipOf_upper (α β : (v.adicCompletion K)ˣ) (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)]) (y : v.adicCompletion K) :
    ((γ * unipOf y : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
    ((γ * unipOf y : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 = α ∧
    ((γ * unipOf y : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = β := by
  simp [Units.val_mul, hγ, coe_unipOf]

end Unipotent

section IntegralSubgroup

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private theorem _root_.TwistedUnfolding.mem_integralSubgroup_iff (g : GL (Fin 2) (v.adicCompletion K)) :
    g ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) ↔
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
        ∈ v.adicCompletionIntegers K := by
  rw [LocalGL2.mem_integralSubgroup_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨fun i j => ((y : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j).2,
      fun i j => (((y⁻¹ : GL (Fin 2) (v.adicCompletionIntegers K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j).2⟩
  · rintro ⟨h, h'⟩
    let A : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K) := fun i j => ⟨_, h i j⟩
    let B : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K) := fun i j => ⟨_, h' i j⟩
    have hA : A.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) =
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
      ext i j
      rfl
    have hB : B.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) =
        ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
      ext i j
      rfl
    have hinj : Function.Injective fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K) =>
        M.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
      intro M N hMN
      ext i j
      exact congrArg (fun P : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) => P i j) hMN
    have hAB : A * B = 1 := by
      apply hinj
      show (A * B).map _ = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)).map _
      rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv
    have hBA : B * A = 1 := by
      apply hinj
      show (B * A).map _ = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)).map _
      rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul
    exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

p2m_export "TwistedUnfolding" "mem_integralSubgroup_iff"
private theorem unipOf_mem {y : v.adicCompletion K} (hy : y ∈ v.adicCompletionIntegers K) :
    unipOf y ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) := by
  rw [mem_integralSubgroup_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_unipOf]
    fin_cases i <;> fin_cases j <;> simp [hy]
  · rw [coe_unipOf_inv, coe_unipOf]
    fin_cases i <;> fin_cases j <;> simp [hy]

private theorem mem_of_unipOf_mem {y : v.adicCompletion K}
    (h : unipOf y ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) :
    y ∈ v.adicCompletionIntegers K := by
  rw [mem_integralSubgroup_iff] at h
  simpa [coe_unipOf] using h.1 0 1

private theorem unipOf_mem_iff (y : v.adicCompletion K) :
    unipOf y ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) ↔
      y ∈ v.adicCompletionIntegers K :=
  ⟨mem_of_unipOf_mem, unipOf_mem⟩

private theorem mk_mul_unipOf_eq_iff (g : GL (Fin 2) (v.adicCompletion K)) (y z : v.adicCompletion K) :
    (QuotientGroup.mk (g * unipOf y) : GL (Fin 2) (v.adicCompletion K) ⧸
        LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) =
      QuotientGroup.mk (g * unipOf z) ↔ -y + z ∈ v.adicCompletionIntegers K := by
  rw [QuotientGroup.eq, mul_inv_rev, mul_assoc, inv_mul_cancel_left, coe_unipOf_inv, unipOf_mul, unipOf_mem_iff]

private theorem mk_unipOf_eq_iff (y z : v.adicCompletion K) :
    (QuotientGroup.mk (unipOf y) : GL (Fin 2) (v.adicCompletion K) ⧸
        LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) =
      QuotientGroup.mk (unipOf z) ↔ -y + z ∈ v.adicCompletionIntegers K := by
  simpa using mk_mul_unipOf_eq_iff 1 y z

private theorem coe_diagOf_mul_unipOf (a b : (v.adicCompletion K)ˣ) (z : v.adicCompletion K) :
    ((diagOf a b * unipOf z : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(a : v.adicCompletion K), a * z; 0, (b : v.adicCompletion K)] := by
  rw [Units.val_mul, coe_diagOf, coe_unipOf, Matrix.mul_fin_two]
  simp

private theorem coe_diagOf_mul_unipOf_inv (a b : (v.adicCompletion K)ˣ) (z : v.adicCompletion K) :
    (((diagOf a b * unipOf z)⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K),
          -(z * ((b⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K));
        0, ((b⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)] := by
  rw [mul_inv_rev, coe_unipOf_inv, Units.val_mul, coe_unipOf, coe_diagOf_inv, Matrix.mul_fin_two]
  simp

private theorem diagOf_mem_iff (a b : (v.adicCompletion K)ˣ) :
    diagOf a b ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) ↔
      ((a : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧ (b : v.adicCompletion K) ∈ v.adicCompletionIntegers K) ∧
        ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
          ((b⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
  rw [mem_integralSubgroup_iff, coe_diagOf, coe_diagOf_inv]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨⟨by simpa using h 0 0, by simpa using h 1 1⟩, by simpa using h' 0 0, by simpa using h' 1 1⟩
  · rintro ⟨⟨ha, hb⟩, ha', hb'⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [ha, hb]
    · rw [Units.val_inv_eq_inv_val] at ha' hb'
      fin_cases i <;> fin_cases j <;> simp [ha', hb']

private theorem diagOf_mul_unipOf_mem_iff (a b : (v.adicCompletion K)ˣ) (z : v.adicCompletion K) :
    diagOf a b * unipOf z ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) ↔
      diagOf a b ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) ∧
        z ∈ v.adicCompletionIntegers K := by
  constructor
  · intro h
    have h' := (mem_integralSubgroup_iff _).1 h
    rw [coe_diagOf_mul_unipOf, coe_diagOf_mul_unipOf_inv] at h'
    have hd : diagOf a b ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) := by
      rw [diagOf_mem_iff]
      exact ⟨⟨by simpa using h'.1 0 0, by simpa using h'.1 1 1⟩, by simpa using h'.2 0 0, by simpa using h'.2 1 1⟩
    refine ⟨hd, mem_of_unipOf_mem ?_⟩
    have hu := mul_mem (inv_mem hd) h
    rwa [inv_mul_cancel_left] at hu
  · rintro ⟨hd, hz⟩
    exact mul_mem hd (unipOf_mem hz)

private theorem diagOf_mul_diagOf (a b a' b' : (v.adicCompletion K)ˣ) :
    diagOf a b * diagOf a' b' = diagOf (a * a') (b * b') :=
  Units.ext <| by simp [coe_diagOf]

end IntegralSubgroup

section Spherical

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private theorem hecke_apply_eq_of_mk_eq
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    {g h : GL (Fin 2) (v.adicCompletion K)}
    (hgh : (QuotientGroup.mk g : GL (Fin 2) (v.adicCompletion K) ⧸
        LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) = QuotientGroup.mk h) :
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) g = (f : GL (Fin 2) (v.adicCompletion K) → ℂ) h := by
  rw [QuotientGroup.eq] at hgh
  rw [← HeckePair.apply_mul_right f hgh g, mul_inv_cancel_left]

private theorem hecke_apply_out
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (g : GL (Fin 2) (v.adicCompletion K)) :
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (Quotient.out (QuotientGroup.mk g : GL (Fin 2) (v.adicCompletion K) ⧸
      LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))) =
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) g :=
  hecke_apply_eq_of_mk_eq f (QuotientGroup.out_eq' _)

private theorem hecke_mul_unipOf_add_of_mem
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (γ : GL (Fin 2) (v.adicCompletion K)) (y : v.adicCompletion K) {o : v.adicCompletion K}
    (ho : o ∈ v.adicCompletionIntegers K) :
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (y + o)) =
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf y) := by
  rw [← unipOf_mul, ← mul_assoc, HeckePair.apply_mul_right f (unipOf_mem ho)]

end Spherical

section Classes

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private noncomputable abbrev intAdd (v : HeightOneSpectrum (𝓞 K)) : AddSubgroup (v.adicCompletion K) :=
  (v.adicCompletionIntegers K).toSubring.toAddSubgroup

private theorem mem_intAdd {x : v.adicCompletion K} : x ∈ intAdd v ↔ x ∈ v.adicCompletionIntegers K := Iff.rfl

private theorem exists_out_mk_eq_add (y : v.adicCompletion K) :
    ∃ o ∈ v.adicCompletionIntegers K,
      Quotient.out (QuotientAddGroup.mk y : v.adicCompletion K ⧸ intAdd v) = y + o := by
  obtain ⟨o, ho⟩ := QuotientAddGroup.mk_out_eq_mul (s := intAdd v) y
  exact ⟨o, o.2, ho⟩

end Classes

section Cosets

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private noncomputable def upperCoset (γ : GL (Fin 2) (v.adicCompletion K)) (q : v.adicCompletion K ⧸ intAdd v) :
    GL (Fin 2) (v.adicCompletion K) ⧸ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  QuotientGroup.mk (γ * unipOf (Quotient.out q))

private theorem upperCoset_mk (γ : GL (Fin 2) (v.adicCompletion K)) (y : v.adicCompletion K) :
    upperCoset γ (QuotientAddGroup.mk y) = QuotientGroup.mk (γ * unipOf y) := by
  obtain ⟨o, ho, hout⟩ := exists_out_mk_eq_add (v := v) y
  rw [upperCoset, hout, mk_mul_unipOf_eq_iff]
  simpa using neg_mem ho

private theorem upperCoset_injective (γ : GL (Fin 2) (v.adicCompletion K)) : Function.Injective (upperCoset γ) := by
  intro q q' h
  rw [upperCoset, upperCoset, mk_mul_unipOf_eq_iff] at h
  rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq]
  exact h

private theorem range_upperCoset (α β : (v.adicCompletion K)ˣ) (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)]) :
    Set.range (upperCoset γ) =
      {c : GL (Fin 2) (v.adicCompletion K) ⧸
          LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
        ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 = (α : v.adicCompletion K) ∧
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = (β : v.adicCompletion K)} := by
  ext c
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨h10, h00, h11⟩ := mul_unipOf_upper α β γ hγ (Quotient.out q)
    exact ⟨γ * unipOf (Quotient.out q), rfl, h10, h00, h11⟩
  · rintro ⟨g, rfl, h10, h00, h11⟩
    refine ⟨QuotientAddGroup.mk ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 / (α : v.adicCompletion K)), ?_⟩
    rw [upperCoset_mk, ← eq_mul_unipOf_of_upper α β γ g hγ h10 h00 h11]

private theorem finsum_indicator_eq
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (α β : (v.adicCompletion K)ˣ) (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)]) :
    ∑ᶠ c : GL (Fin 2) (v.adicCompletion K) ⧸
        LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
      Set.indicator
        {c : GL (Fin 2) (v.adicCompletion K) ⧸
            LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
          ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
            (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
            (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 = (α : v.adicCompletion K) ∧
            (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = (β : v.adicCompletion K)}
        (fun c => (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (Quotient.out c)) c =
      ∑ᶠ q : v.adicCompletion K ⧸ intAdd v,
        (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (Quotient.out q)) := by
  rw [← finsum_mem_def, ← range_upperCoset α β γ hγ, finsum_mem_range (upperCoset_injective γ)]
  exact finsum_congr fun q => hecke_apply_out f _

private theorem finite_support_out
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (γ : GL (Fin 2) (v.adicCompletion K)) :
    (Function.support fun q : v.adicCompletion K ⧸ intAdd v =>
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (γ * unipOf (Quotient.out q))).Finite := by
  refine (HeckePair.finite_cosets f).preimage (upperCoset_injective γ).injOn |>.subset ?_
  intro q hq
  exact Set.mem_image_of_mem _ hq

end Cosets

section Iwasawa

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private theorem exists_eq_diagOf_mul_unipOf_mul (x : GL (Fin 2) (v.adicCompletion K)) :
    ∃ (a b : (v.adicCompletion K)ˣ) (w : v.adicCompletion K) (k : GL (Fin 2) (v.adicCompletion K)),
      k ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) ∧
        x = diagOf a b * unipOf w * k := by
  obtain ⟨z, a₁, a₂, k, hk, hx⟩ :=
    LocalGL2.iwasawa_decomposition_diag (v.adicCompletionIntegers K) (v.adicCompletion K) x
  refine ⟨a₁, a₂, z * a₂ / a₁, k, hk, ?_⟩
  rw [← unipOf_mul_diagOf a₁ a₂ z _ (mul_div_cancel₀ _ a₁.ne_zero)]
  exact Units.ext hx

end Iwasawa

section Twisted

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private theorem coe_map_apply (σ : v.adicCompletion K →+* v.adicCompletion K) (x : GL (Fin 2) (v.adicCompletion K)) :
    ((Matrix.GeneralLinearGroup.map σ x : GL (Fin 2) (v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).map σ := rfl

private theorem map_unipOf (σ : v.adicCompletion K →+* v.adicCompletion K) (y : v.adicCompletion K) :
    Matrix.GeneralLinearGroup.map σ (unipOf y) = unipOf (σ y) := by
  refine Units.ext ?_
  rw [coe_map_apply, coe_unipOf, coe_unipOf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem map_diagOf (σ : v.adicCompletion K →+* v.adicCompletion K) (t₁ t₂ : (v.adicCompletion K)ˣ)
    (h₁ : σ t₁ = t₁) (h₂ : σ t₂ = t₂) : Matrix.GeneralLinearGroup.map σ (diagOf t₁ t₂) = diagOf t₁ t₂ := by
  refine Units.ext ?_
  rw [coe_map_apply, coe_diagOf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h₁, h₂]

private theorem map_mem_integralSubgroup (σ : v.adicCompletion K →+* v.adicCompletion K)
    (hσ : ∀ y ∈ v.adicCompletionIntegers K, σ y ∈ v.adicCompletionIntegers K) {u : GL (Fin 2) (v.adicCompletion K)}
    (hu : u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) :
    Matrix.GeneralLinearGroup.map σ u ∈
      LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) := by
  rw [mem_integralSubgroup_iff] at hu ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_map_apply, Matrix.map_apply]
    exact hσ _ (hu.1 i j)
  · rw [← map_inv, coe_map_apply, Matrix.map_apply]
    exact hσ _ (hu.2 i j)

private theorem unipOf_inv_mul_diagOf_mul_unipOf (a b : (v.adicCompletion K)ˣ) (y w : v.adicCompletion K) :
    (unipOf y)⁻¹ * diagOf a b * unipOf w =
      diagOf a b * unipOf (w - (b : v.adicCompletion K) / (a : v.adicCompletion K) * y) := by
  have hw₀ : (a : v.adicCompletion K) * (-y * (b : v.adicCompletion K) / (a : v.adicCompletion K)) =
      -y * (b : v.adicCompletion K) :=
    mul_div_cancel₀ _ a.ne_zero
  rw [coe_unipOf_inv, unipOf_mul_diagOf a b (-y) _ hw₀, mul_assoc, unipOf_mul]
  congr 2
  ring

private theorem unipOf_inv_mul_diagOf_mul_map_unipOf (σ : v.adicCompletion K →+* v.adicCompletion K)
    (a b : (v.adicCompletion K)ˣ) (y : v.adicCompletion K) :
    (unipOf y)⁻¹ * diagOf a b * Matrix.GeneralLinearGroup.map σ (unipOf y) =
      diagOf a b * unipOf (σ y - (b : v.adicCompletion K) / (a : v.adicCompletion K) * y) := by
  rw [map_unipOf, unipOf_inv_mul_diagOf_mul_unipOf]

private theorem hecke_diagOf_mul_unipOf_add_of_mem
    (φ : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (σ : v.adicCompletion K →+* v.adicCompletion K)
    (hσ : ∀ y ∈ v.adicCompletionIntegers K, σ y ∈ v.adicCompletionIntegers K) (a b : (v.adicCompletion K)ˣ)
    (z : v.adicCompletion K) {o : v.adicCompletion K} (ho : o ∈ v.adicCompletionIntegers K) :
    (φ : GL (Fin 2) (v.adicCompletion K) → ℂ)
        (diagOf a b * unipOf (z + (σ o - (b : v.adicCompletion K) / (a : v.adicCompletion K) * o))) =
      (φ : GL (Fin 2) (v.adicCompletion K) → ℂ) (diagOf a b * unipOf z) := by
  have h1 : diagOf a b * unipOf (z + (σ o - (b : v.adicCompletion K) / (a : v.adicCompletion K) * o)) =
      (unipOf o)⁻¹ * (diagOf a b * unipOf z) * unipOf (σ o) := by
    rw [← mul_assoc, unipOf_inv_mul_diagOf_mul_unipOf, mul_assoc, unipOf_mul]
    congr 2
    ring
  rw [h1, HeckePair.apply_mul_right φ (unipOf_mem (hσ o ho)), HeckePair.apply_left_mul φ (inv_mem (unipOf_mem ho))]

private theorem mul_comm_of_mem (σ : v.adicCompletion K →+* v.adicCompletion K)
    (T : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hT : ∀ x : GL (Fin 2) (v.adicCompletion K),
      x ∈ T ↔ ∃ t₁ t₂ : (v.adicCompletion K)ˣ, σ t₁ = t₁ ∧ σ t₂ = t₂ ∧ x = diagOf t₁ t₂)
    {t y : GL (Fin 2) (v.adicCompletion K)} (ht : t ∈ T) (hy : y ∈ T) : t * y = y * t := by
  obtain ⟨t₁, t₂, -, -, rfl⟩ := (hT t).1 ht
  obtain ⟨y₁, y₂, -, -, rfl⟩ := (hT y).1 hy
  rw [diagOf_mul_diagOf, diagOf_mul_diagOf, mul_comm t₁, mul_comm t₂]

private theorem inv_mul_diagOf_mul_map_of_mem (σ : v.adicCompletion K →+* v.adicCompletion K)
    (a b : (v.adicCompletion K)ˣ) (T : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hT : ∀ x : GL (Fin 2) (v.adicCompletion K),
      x ∈ T ↔ ∃ t₁ t₂ : (v.adicCompletion K)ˣ, σ t₁ = t₁ ∧ σ t₂ = t₂ ∧ x = diagOf t₁ t₂)
    {t : GL (Fin 2) (v.adicCompletion K)} (ht : t ∈ T) :
    t⁻¹ * diagOf a b * Matrix.GeneralLinearGroup.map σ t = diagOf a b := by
  obtain ⟨t₁, t₂, h₁, h₂, rfl⟩ := (hT t).1 ht
  rw [map_diagOf σ t₁ t₂ h₁ h₂, mul_assoc, diagOf_mul_diagOf, mul_comm (a : (v.adicCompletion K)ˣ),
    mul_comm (b : (v.adicCompletion K)ˣ), ← diagOf_mul_diagOf, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem hecke_twisted_mul_left
    (φ : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (σ : v.adicCompletion K →+* v.adicCompletion K) (a b : (v.adicCompletion K)ˣ)
    (T : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hT : ∀ x : GL (Fin 2) (v.adicCompletion K),
      x ∈ T ↔ ∃ t₁ t₂ : (v.adicCompletion K)ˣ, σ t₁ = t₁ ∧ σ t₂ = t₂ ∧ x = diagOf t₁ t₂)
    {t : GL (Fin 2) (v.adicCompletion K)} (ht : t ∈ T) (x : GL (Fin 2) (v.adicCompletion K)) :
    (φ : GL (Fin 2) (v.adicCompletion K) → ℂ) ((t * x)⁻¹ * diagOf a b * Matrix.GeneralLinearGroup.map σ (t * x)) =
      (φ : GL (Fin 2) (v.adicCompletion K) → ℂ) (x⁻¹ * diagOf a b * Matrix.GeneralLinearGroup.map σ x) := by
  rw [map_mul, mul_inv_rev, mul_assoc x⁻¹, mul_assoc x⁻¹, ← mul_assoc (t⁻¹ * diagOf a b),
    inv_mul_diagOf_mul_map_of_mem σ a b T hT ht, mul_assoc]

private theorem hecke_twisted_mul_right
    (φ : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (σ : v.adicCompletion K →+* v.adicCompletion K)
    (hσ : ∀ y ∈ v.adicCompletionIntegers K, σ y ∈ v.adicCompletionIntegers K) (a b : (v.adicCompletion K)ˣ)
    (x : GL (Fin 2) (v.adicCompletion K)) {u : GL (Fin 2) (v.adicCompletion K)}
    (hu : u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) :
    (φ : GL (Fin 2) (v.adicCompletion K) → ℂ) ((x * u)⁻¹ * diagOf a b * Matrix.GeneralLinearGroup.map σ (x * u)) =
      (φ : GL (Fin 2) (v.adicCompletion K) → ℂ) (x⁻¹ * diagOf a b * Matrix.GeneralLinearGroup.map σ x) := by
  have h1 : (x * u)⁻¹ * diagOf a b * Matrix.GeneralLinearGroup.map σ (x * u) =
      u⁻¹ * (x⁻¹ * diagOf a b * Matrix.GeneralLinearGroup.map σ x) * Matrix.GeneralLinearGroup.map σ u := by
    rw [map_mul, mul_inv_rev]
    simp only [mul_assoc]
  rw [h1, HeckePair.apply_mul_right φ (map_mem_integralSubgroup σ hσ hu), HeckePair.apply_left_mul φ (inv_mem hu)]

private theorem mem_map_conj_iff (s y : GL (Fin 2) (v.adicCompletion K)) :
    y ∈ (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)).map (MulAut.conj s).toMonoidHom ↔
      s⁻¹ * y * s ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hu
  · intro h
    exact ⟨s⁻¹ * y * s, h, by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem inf_map_conj_mul_mul (σ : v.adicCompletion K →+* v.adicCompletion K)
    (T : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hT : ∀ x : GL (Fin 2) (v.adicCompletion K),
      x ∈ T ↔ ∃ t₁ t₂ : (v.adicCompletion K)ˣ, σ t₁ = t₁ ∧ σ t₂ = t₂ ∧ x = diagOf t₁ t₂)
    {t : GL (Fin 2) (v.adicCompletion K)} (ht : t ∈ T) (s : GL (Fin 2) (v.adicCompletion K))
    {u : GL (Fin 2) (v.adicCompletion K)}
    (hu : u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) :
    T ⊓ (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)).map
        (MulAut.conj (t * s * u)).toMonoidHom =
      T ⊓ (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)).map
        (MulAut.conj s).toMonoidHom := by
  ext y
  simp only [Subgroup.mem_inf, mem_map_conj_iff]
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨hy, ?_⟩
    have h2 : (t * s * u)⁻¹ * y * (t * s * u) = u⁻¹ * (s⁻¹ * y * s) * u := by
      have hc : t⁻¹ * y * t = y := by
        rw [mul_comm_of_mem σ T hT (inv_mem ht) hy, mul_assoc, inv_mul_cancel, mul_one]
      calc (t * s * u)⁻¹ * y * (t * s * u) = u⁻¹ * (s⁻¹ * (t⁻¹ * y * t) * s) * u := by
            simp only [mul_inv_rev, mul_assoc]
        _ = u⁻¹ * (s⁻¹ * y * s) * u := by rw [hc]
    rw [h2] at h
    have h3 := mul_mem (mul_mem hu h) (inv_mem hu)
    rwa [mul_assoc, mul_assoc, mul_inv_cancel, mul_one, ← mul_assoc, mul_inv_cancel, one_mul] at h3
  · rintro ⟨hy, h⟩
    refine ⟨hy, ?_⟩
    have hc : t⁻¹ * y * t = y := by
      rw [mul_comm_of_mem σ T hT (inv_mem ht) hy, mul_assoc, inv_mul_cancel, mul_one]
    have h4 : (t * s * u)⁻¹ * y * (t * s * u) = u⁻¹ * (s⁻¹ * y * s) * u := by
      calc (t * s * u)⁻¹ * y * (t * s * u) = u⁻¹ * (s⁻¹ * (t⁻¹ * y * t) * s) * u := by
            simp only [mul_inv_rev, mul_assoc]
        _ = u⁻¹ * (s⁻¹ * y * s) * u := by rw [hc]
    rw [h4]
    exact mul_mem (mul_mem (inv_mem hu) h) hu

private theorem entries_of_diagOf_mul_map_eq (σ : v.adicCompletion K →+* v.adicCompletion K)
    (a b : (v.adicCompletion K)ˣ) (x : GL (Fin 2) (v.adicCompletion K))
    (h : diagOf a b * Matrix.GeneralLinearGroup.map σ x = x * diagOf a b) (i j : Fin 2) :
    ![(a : v.adicCompletion K), (b : v.adicCompletion K)] i *
        σ ((x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) =
      (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j *
        ![(a : v.adicCompletion K), (b : v.adicCompletion K)] j := by
  have h' := congrArg
    (fun g : GL (Fin 2) (v.adicCompletion K) => (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) h
  simp only [Units.val_mul, coe_map_apply, coe_diagOf, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply] at h'
  fin_cases i <;> fin_cases j <;> simpa using h'

private theorem twistedConj_eq_self_iff (σ : v.adicCompletion K →+* v.adicCompletion K) (a b : (v.adicCompletion K)ˣ)
    (hq : ∀ q : v.adicCompletion K, σ q = (b : v.adicCompletion K) / (a : v.adicCompletion K) * q → q = 0)
    (hr : ∀ r : v.adicCompletion K, σ r = (a : v.adicCompletion K) / (b : v.adicCompletion K) * r → r = 0)
    (x : GL (Fin 2) (v.adicCompletion K)) :
    x⁻¹ * diagOf a b * Matrix.GeneralLinearGroup.map σ x = diagOf a b ↔
      ∃ t₁ t₂ : (v.adicCompletion K)ˣ, σ t₁ = t₁ ∧ σ t₂ = t₂ ∧ x = diagOf t₁ t₂ := by
  constructor
  · intro h
    have h' : diagOf a b * Matrix.GeneralLinearGroup.map σ x = x * diagOf a b := by
      have h1 := congrArg (fun g => x * g) h
      simpa only [← mul_assoc, mul_inv_cancel, one_mul] using h1
    have h00 := entries_of_diagOf_mul_map_eq σ a b x h' 0 0
    have h01 := entries_of_diagOf_mul_map_eq σ a b x h' 0 1
    have h10 := entries_of_diagOf_mul_map_eq σ a b x h' 1 0
    have h11 := entries_of_diagOf_mul_map_eq σ a b x h' 1 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h01 h10 h11
    have ha : (a : v.adicCompletion K) ≠ 0 := a.ne_zero
    have hb : (b : v.adicCompletion K) ≠ 0 := b.ne_zero
    set X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) := (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) with hX
    have hX01 : X 0 1 = 0 := hq _ (by field_simp; linear_combination h01)
    have hX10 : X 1 0 = 0 := hr _ (by field_simp; linear_combination h10)
    have hf00 : σ (X 0 0) = X 0 0 := mul_left_cancel₀ ha (by rw [h00, mul_comm])
    have hf11 : σ (X 1 1) = X 1 1 := mul_left_cancel₀ hb (by rw [h11, mul_comm])
    have hdet : X 0 0 * X 1 1 ≠ 0 := by
      have hu : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).1 x.isUnit
      rw [Matrix.det_fin_two, hX01, hX10, mul_zero, sub_zero] at hu
      exact hu.ne_zero
    refine ⟨Units.mk0 (X 0 0) (left_ne_zero_of_mul hdet), Units.mk0 (X 1 1) (right_ne_zero_of_mul hdet), hf00, hf11,
      Units.ext ?_⟩
    rw [coe_diagOf, Units.val_mk0, Units.val_mk0, ← hX]
    conv_lhs => rw [Matrix.eta_fin_two X]
    rw [hX01, hX10]
  · rintro ⟨t₁, t₂, h₁, h₂, rfl⟩
    have hcomm : diagOf a b * diagOf t₁ t₂ = diagOf t₁ t₂ * diagOf a b := by
      rw [diagOf_mul_diagOf, diagOf_mul_diagOf, mul_comm a t₁, mul_comm b t₂]
    rw [map_diagOf σ t₁ t₂ h₁ h₂, mul_assoc, hcomm, inv_mul_cancel_left]

end Twisted

section Counting

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private noncomputable def twistedFn
    (φ : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (σ : v.adicCompletion K →+* v.adicCompletion K) (a b : (v.adicCompletion K)ˣ)
    (x : GL (Fin 2) (v.adicCompletion K)) : ℂ :=
  (φ : GL (Fin 2) (v.adicCompletion K) → ℂ) (x⁻¹ * diagOf a b * Matrix.GeneralLinearGroup.map σ x)

private noncomputable def weight (T : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (s : GL (Fin 2) (v.adicCompletion K)) : ℕ :=
  (T ⊓ (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)).map
      (MulAut.conj s).toMonoidHom).relIndex
    (T ⊓ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))

private def classSet (T : Subgroup (GL (Fin 2) (v.adicCompletion K))) (s : GL (Fin 2) (v.adicCompletion K)) :
    Set (v.adicCompletion K ⧸ intAdd v) :=
  {q | ∃ t ∈ T, ∃ u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
    unipOf (Quotient.out q) = t * s * u}

private theorem twistedFn_unipOf
    (φ : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (σ : v.adicCompletion K →+* v.adicCompletion K) (a b : (v.adicCompletion K)ˣ) (y : v.adicCompletion K) :
    twistedFn φ σ a b (unipOf y) =
      (φ : GL (Fin 2) (v.adicCompletion K) → ℂ)
        (diagOf a b * unipOf (σ y - (b : v.adicCompletion K) / (a : v.adicCompletion K) * y)) := by
  rw [twistedFn, unipOf_inv_mul_diagOf_mul_map_unipOf]

private theorem twistedFn_mul_mul
    (φ : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (σ : v.adicCompletion K →+* v.adicCompletion K)
    (hσ : ∀ y ∈ v.adicCompletionIntegers K, σ y ∈ v.adicCompletionIntegers K) (a b : (v.adicCompletion K)ˣ)
    (T : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hT : ∀ x : GL (Fin 2) (v.adicCompletion K),
      x ∈ T ↔ ∃ t₁ t₂ : (v.adicCompletion K)ˣ, σ t₁ = t₁ ∧ σ t₂ = t₂ ∧ x = diagOf t₁ t₂)
    {t : GL (Fin 2) (v.adicCompletion K)} (ht : t ∈ T) (s : GL (Fin 2) (v.adicCompletion K))
    {u : GL (Fin 2) (v.adicCompletion K)}
    (hu : u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) :
    twistedFn φ σ a b (t * s * u) = twistedFn φ σ a b s := by
  unfold twistedFn
  rw [hecke_twisted_mul_right φ σ hσ a b (t * s) hu, hecke_twisted_mul_left φ σ a b T hT ht s]

private theorem exists_mem_mul_unipOf_mul (σ : v.adicCompletion K →+* v.adicCompletion K)
    (T : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hT : ∀ x : GL (Fin 2) (v.adicCompletion K),
      x ∈ T ↔ ∃ t₁ t₂ : (v.adicCompletion K)ˣ, σ t₁ = t₁ ∧ σ t₂ = t₂ ∧ x = diagOf t₁ t₂)
    (hfac : ∀ x : (v.adicCompletion K)ˣ, ∃ t u : (v.adicCompletion K)ˣ, σ t = t ∧
      (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧ x = t * u)
    (x : GL (Fin 2) (v.adicCompletion K)) :
    ∃ t ∈ T, ∃ y : v.adicCompletion K,
      ∃ k ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K), x = t * unipOf y * k := by
  obtain ⟨a, b, w, k, hk, rfl⟩ := exists_eq_diagOf_mul_unipOf_mul x
  obtain ⟨t₁, u₁, ht₁, hu₁, hu₁', rfl⟩ := hfac a
  obtain ⟨t₂, u₂, ht₂, hu₂, hu₂', rfl⟩ := hfac b
  have hdu : diagOf u₁ u₂ ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :=
    (diagOf_mem_iff u₁ u₂).2 ⟨⟨hu₁, hu₂⟩, hu₁', hu₂'⟩
  have hw : (u₁ : v.adicCompletion K) * w =
      (u₁ : v.adicCompletion K) * w * ((u₂⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) * u₂ :=
    (Units.inv_mul_cancel_right _ u₂).symm
  refine ⟨diagOf t₁ t₂, (hT _).2 ⟨t₁, t₂, ht₁, ht₂, rfl⟩,
    (u₁ : v.adicCompletion K) * w * ((u₂⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K), diagOf u₁ u₂ * k,
    mul_mem hdu hk, ?_⟩
  rw [← diagOf_mul_diagOf, mul_assoc (diagOf t₁ t₂), ← unipOf_mul_diagOf u₁ u₂ _ w hw, ← mul_assoc, ← mul_assoc,
    mul_assoc _ (diagOf u₁ u₂) k]

private theorem weight_mul_mul (σ : v.adicCompletion K →+* v.adicCompletion K)
    (T : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hT : ∀ x : GL (Fin 2) (v.adicCompletion K),
      x ∈ T ↔ ∃ t₁ t₂ : (v.adicCompletion K)ˣ, σ t₁ = t₁ ∧ σ t₂ = t₂ ∧ x = diagOf t₁ t₂)
    {t : GL (Fin 2) (v.adicCompletion K)} (ht : t ∈ T) (s : GL (Fin 2) (v.adicCompletion K))
    {u : GL (Fin 2) (v.adicCompletion K)}
    (hu : u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) :
    weight T (t * s * u) = weight T s := by
  unfold weight
  rw [inf_map_conj_mul_mul σ T hT ht s hu]

private theorem classSet_mul_mul (T : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    {t : GL (Fin 2) (v.adicCompletion K)} (ht : t ∈ T) (s : GL (Fin 2) (v.adicCompletion K))
    {u : GL (Fin 2) (v.adicCompletion K)}
    (hu : u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) :
    classSet T (t * s * u) = classSet T s := by
  ext q
  simp only [classSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t', ht', u', hu', h⟩
    refine ⟨t' * t, mul_mem ht' ht, u * u', mul_mem hu hu', ?_⟩
    rw [h]
    simp only [mul_assoc]
  · rintro ⟨t', ht', u', hu', h⟩
    refine ⟨t' * t⁻¹, mul_mem ht' (inv_mem ht), u⁻¹ * u', mul_mem (inv_mem hu) hu', ?_⟩
    rw [h]
    simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]

private theorem mem_integralSubgroup_of_mul_unipOf_mul_eq (σ : v.adicCompletion K →+* v.adicCompletion K)
    (T : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hT : ∀ x : GL (Fin 2) (v.adicCompletion K),
      x ∈ T ↔ ∃ t₁ t₂ : (v.adicCompletion K)ˣ, σ t₁ = t₁ ∧ σ t₂ = t₂ ∧ x = diagOf t₁ t₂)
    {t : GL (Fin 2) (v.adicCompletion K)} (ht : t ∈ T) {y₀ y : v.adicCompletion K}
    {u : GL (Fin 2) (v.adicCompletion K)}
    (hu : u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
    (h : unipOf y = t * unipOf y₀ * u) :
    t ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) := by
  obtain ⟨t₁, t₂, -, -, rfl⟩ := (hT t).1 ht
  have h1 : (unipOf y)⁻¹ * diagOf t₁ t₂ * unipOf y₀ = u⁻¹ := by
    rw [h]
    group
  rw [unipOf_inv_mul_diagOf_mul_unipOf] at h1
  have h2 : diagOf t₁ t₂ * unipOf (y₀ - (t₂ : v.adicCompletion K) / (t₁ : v.adicCompletion K) * y) ∈
      LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) := by
    rw [h1]
    exact inv_mem hu
  exact ((diagOf_mul_unipOf_mem_iff t₁ t₂ _).1 h2).1

private theorem natCard_classSet_unipOf (σ : v.adicCompletion K →+* v.adicCompletion K)
    (T : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hT : ∀ x : GL (Fin 2) (v.adicCompletion K),
      x ∈ T ↔ ∃ t₁ t₂ : (v.adicCompletion K)ˣ, σ t₁ = t₁ ∧ σ t₂ = t₂ ∧ x = diagOf t₁ t₂)
    (y₀ : v.adicCompletion K) : Nat.card (classSet T (unipOf y₀)) = weight T (unipOf y₀) := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : GL (Fin 2) (v.adicCompletion K) ⧸ LocalGL2.integralSubgroup (v.adicCompletionIntegers K)
      (v.adicCompletion K), c₀ = QuotientGroup.mk (unipOf y₀) := ⟨_, rfl⟩

  have hbij : Set.BijOn (upperCoset 1) (classSet T (unipOf y₀))
      (MulAction.orbit (↥(T ⊓ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))) c₀) := by
    refine ⟨?_, (upperCoset_injective 1).injOn, ?_⟩
    · rintro q ⟨t, ht, u, hu, h⟩
      have htU : t ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :=
        mem_integralSubgroup_of_mul_unipOf_mul_eq σ T hT ht hu h
      have hq : upperCoset 1 q =
          (⟨t, ht, htU⟩ :
            ↥(T ⊓ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))) • c₀ := by
        rw [← QuotientAddGroup.out_eq' q, upperCoset_mk, one_mul, h, QuotientGroup.mk_mul_of_mem _ hu, hc₀]
        rfl
      rw [hq]
      exact MulAction.mem_orbit c₀ _
    · intro c hc
      obtain ⟨⟨t, ht, htU⟩, rfl⟩ := MulAction.mem_orbit_iff.1 hc
      obtain ⟨t₁, t₂, -, -, rfl⟩ := (hT t).1 ht
      set z : v.adicCompletion K :=
        (t₁ : v.adicCompletion K) * y₀ * ((t₂⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) with hz
      have hz' : (t₁ : v.adicCompletion K) * y₀ = z * t₂ := (Units.inv_mul_cancel_right _ t₂).symm
      have hcomm : unipOf z * diagOf t₁ t₂ = diagOf t₁ t₂ * unipOf y₀ := unipOf_mul_diagOf t₁ t₂ z y₀ hz'
      refine ⟨QuotientAddGroup.mk z, ?_, ?_⟩
      · obtain ⟨o, ho, hout⟩ := exists_out_mk_eq_add z
        simp only [classSet, Set.mem_setOf_eq]
        refine ⟨diagOf t₁ t₂, ht, (diagOf t₁ t₂)⁻¹ * unipOf o, mul_mem (inv_mem htU) (unipOf_mem ho), ?_⟩
        rw [hout, ← unipOf_mul, ← hcomm]
        group
      · rw [upperCoset_mk, one_mul]
        show _ = (diagOf t₁ t₂) • c₀
        rw [hc₀, MulAction.Quotient.smul_mk, smul_eq_mul, ← hcomm, QuotientGroup.mk_mul_of_mem _ htU]

  have hstab : MulAction.stabilizer
        (↥(T ⊓ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))) c₀ =
      (T ⊓ (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)).map
          (MulAut.conj (unipOf y₀)).toMonoidHom).subgroupOf
        (T ⊓ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
    ext ⟨g, hgT, hgU⟩
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show g • c₀ = c₀ ↔ _
    rw [hc₀, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, mem_map_conj_iff, mul_inv_rev]
    constructor
    · intro h
      refine ⟨hgT, ?_⟩
      have h' := inv_mem h
      rwa [mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, ← mul_assoc] at h'
    · rintro ⟨-, h⟩
      have h' := inv_mem h
      rwa [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc] at h'
  calc Nat.card (classSet T (unipOf y₀))
      = Nat.card (MulAction.orbit
          (↥(T ⊓ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))) c₀) :=
        Nat.card_congr (hbij.equiv _)
    _ = Nat.card (↥(T ⊓ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ⧸
          MulAction.stabilizer
            (↥(T ⊓ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))) c₀) :=
        Nat.card_congr (MulAction.orbitEquivQuotientStabilizer _ c₀)
    _ = (MulAction.stabilizer
          (↥(T ⊓ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))) c₀).index :=
        (Subgroup.index_eq_card
          (H := MulAction.stabilizer
            (↥(T ⊓ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))) c₀)).symm
    _ = weight T (unipOf y₀) := by rw [hstab]; rfl

private theorem natCard_classSet (σ : v.adicCompletion K →+* v.adicCompletion K)
    (T : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hT : ∀ x : GL (Fin 2) (v.adicCompletion K),
      x ∈ T ↔ ∃ t₁ t₂ : (v.adicCompletion K)ˣ, σ t₁ = t₁ ∧ σ t₂ = t₂ ∧ x = diagOf t₁ t₂)
    (hfac : ∀ x : (v.adicCompletion K)ˣ, ∃ t u : (v.adicCompletion K)ˣ, σ t = t ∧
      (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧ x = t * u)
    (s : GL (Fin 2) (v.adicCompletion K)) : Nat.card (classSet T s) = weight T s := by
  obtain ⟨t, ht, y, k, hk, rfl⟩ := exists_mem_mul_unipOf_mul σ T hT hfac s
  rw [classSet_mul_mul T ht _ hk, weight_mul_mul σ T hT ht _ hk]
  exact natCard_classSet_unipOf σ T hT y

private theorem sum_weight_mul_twistedFn
    (φ : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (σ : v.adicCompletion K →+* v.adicCompletion K)
    (hσ : ∀ y ∈ v.adicCompletionIntegers K, σ y ∈ v.adicCompletionIntegers K) (a b : (v.adicCompletion K)ˣ)
    (T : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hT : ∀ x : GL (Fin 2) (v.adicCompletion K),
      x ∈ T ↔ ∃ t₁ t₂ : (v.adicCompletion K)ˣ, σ t₁ = t₁ ∧ σ t₂ = t₂ ∧ x = diagOf t₁ t₂)
    (hfac : ∀ x : (v.adicCompletion K)ˣ, ∃ t u : (v.adicCompletion K)ˣ, σ t = t ∧
      (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧ x = t * u)
    (S : Finset (GL (Fin 2) (v.adicCompletion K)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ T,
      ∀ u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K), s' = t * s * u → s' = s)
    (hcov : ∀ x : GL (Fin 2) (v.adicCompletion K), twistedFn φ σ a b x ≠ 0 →
      ∃ s ∈ S, ∃ t ∈ T,
        ∃ u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K), x = t * s * u)
    (hfin : (Function.support fun q : v.adicCompletion K ⧸ intAdd v =>
      twistedFn φ σ a b (unipOf (Quotient.out q))).Finite) :
    ∑ s ∈ S, (weight T s : ℂ) * twistedFn φ σ a b s =
      ∑ᶠ q : v.adicCompletion K ⧸ intAdd v, twistedFn φ σ a b (unipOf (Quotient.out q)) := by
  classical
  set F : v.adicCompletion K ⧸ intAdd v → ℂ := fun q => twistedFn φ σ a b (unipOf (Quotient.out q)) with hF
  set A : GL (Fin 2) (v.adicCompletion K) → Finset (v.adicCompletion K ⧸ intAdd v) :=
    fun s => hfin.toFinset.filter fun q => q ∈ classSet T s with hA
  have hmemA : ∀ s q, q ∈ A s ↔ F q ≠ 0 ∧ q ∈ classSet T s := by
    intro s q
    rw [hA, Finset.mem_filter, Set.Finite.mem_toFinset, Function.mem_support]

  have hval : ∀ s q, q ∈ classSet T s → F q = twistedFn φ σ a b s := by
    rintro s q ⟨t, ht, u, hu, h⟩
    show twistedFn φ σ a b (unipOf (Quotient.out q)) = _
    rw [h, twistedFn_mul_mul φ σ hσ a b T hT ht s hu]

  have hunion : hfin.toFinset = S.biUnion A := by
    ext q
    rw [Set.Finite.mem_toFinset, Function.mem_support, Finset.mem_biUnion]
    constructor
    · intro hq
      obtain ⟨s, hs, t, ht, u, hu, h⟩ := hcov _ hq
      exact ⟨s, hs, (hmemA s q).2 ⟨hq, ⟨t, ht, u, hu, h⟩⟩⟩
    · rintro ⟨s, -, hq⟩
      exact ((hmemA s q).1 hq).1
  have hdisj : (S : Set (GL (Fin 2) (v.adicCompletion K))).PairwiseDisjoint A := by
    intro s hs s' hs' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro q hq hq'
    obtain ⟨-, t, ht, u, hu, h⟩ := (hmemA s q).1 hq
    obtain ⟨-, t', ht', u', hu', h'⟩ := (hmemA s' q).1 hq'
    apply hne
    symm
    refine hS s hs s' hs' (t'⁻¹ * t) (mul_mem (inv_mem ht') ht) (u * u'⁻¹) (mul_mem hu (inv_mem hu')) ?_
    have h2 : t' * s' * u' = t * s * u := by rw [← h, ← h']
    calc s' = t'⁻¹ * (t' * s' * u') * u'⁻¹ := by group
      _ = t'⁻¹ * (t * s * u) * u'⁻¹ := by rw [h2]
      _ = t'⁻¹ * t * s * (u * u'⁻¹) := by group
  rw [finsum_eq_sum_of_support_subset F hfin.coe_toFinset.symm.subset, hunion, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.sum_congr rfl fun q hq => hval s q ((hmemA s q).1 hq).2, Finset.sum_const, nsmul_eq_mul]
  by_cases h0 : twistedFn φ σ a b s = 0
  · rw [h0, mul_zero, mul_zero]
  · congr 1
    have hAs : ∀ q, q ∈ A s ↔ q ∈ classSet T s := fun q =>
      ⟨fun hq => ((hmemA s q).1 hq).2, fun hq => (hmemA s q).2 ⟨by rw [hval s q hq]; exact h0, hq⟩⟩
    have hcard : (A s).card = Nat.card (classSet T s) := by
      rw [← Nat.card_eq_finsetCard]
      exact Nat.card_congr (Equiv.subtypeEquivRight hAs)
    rw [hcard, natCard_classSet σ T hT hfac s]

end Counting

end LocalLayer

section Carriers

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
  (L : Type) [Field L] [NumberField L] [Algebra K L] (w : v.Extension (𝓞 L))

private theorem intLattice_toAddSubgroup : (intLattice K v L w).toAddSubgroup = intAdd w.1 :=
  AddSubgroup.ext fun _ => Iff.rfl

private theorem finite_intLattice [FiniteDimensional K L] :
    Module.Finite (v.adicCompletionIntegers K) (intLattice K v L w) :=
  Module.Finite.equiv
    ({ toFun := fun y => ⟨(y : w.1.adicCompletion L), y.2⟩
       map_add' := fun _ _ => rfl
       map_smul' := fun r y => Subtype.ext (by
         change ((r • y : w.1.adicCompletionIntegers L) : w.1.adicCompletion L) =
           (r : v.adicCompletion K) • (y : w.1.adicCompletion L)
         rw [Algebra.smul_def, MulMemClass.coe_mul, Algebra.smul_def]
         rfl)
       invFun := fun x => ⟨(x : w.1.adicCompletion L), x.2⟩
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl } :
      w.1.adicCompletionIntegers L ≃ₗ[v.adicCompletionIntegers K] intLattice K v L w)

private theorem isTorsionFree_intLattice :
    Module.IsTorsionFree (v.adicCompletionIntegers K) (intLattice K v L w) :=
  Module.IsTorsionFree.of_smul_eq_zero fun r x hrx => by
    have h : (r : v.adicCompletion K) • (x : w.1.adicCompletion L) = 0 := congrArg Subtype.val hrx
    rw [Algebra.smul_def, mul_eq_zero, map_eq_zero] at h
    rcases h with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

private theorem exists_pow_smul_mem_intLattice {π : v.adicCompletionIntegers K}
    (hπE : Valued.v (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (π : v.adicCompletion K)) =
      Multiplicative.ofAdd (-1 : ℤ)) (x : w.1.adicCompletion L) :
    ∃ k : ℕ, π ^ k • x ∈ intLattice K v L w := by
  obtain ⟨k, hk⟩ := exists_pow_mul_mem_integers L w.1 hπE x
  refine ⟨k, ?_⟩
  change ((π ^ k : v.adicCompletionIntegers K) : v.adicCompletion K) • x ∈ w.1.adicCompletionIntegers L
  rw [SubmonoidClass.coe_pow, Algebra.smul_def, map_pow]
  exact hk

private theorem exists_pow_smul_eq_algebraMap_of_valued {π : v.adicCompletionIntegers K}
    (hπ : Valued.v (π : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) (c : v.adicCompletion K) :
    ∃ k : ℕ, ∃ r : v.adicCompletionIntegers K,
      π ^ k • c = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r := by
  obtain ⟨k, hk⟩ := exists_pow_mul_mem_integers K v hπ c
  refine ⟨k, ⟨_, hk⟩, ?_⟩
  rw [Algebra.smul_def, map_pow]
  rfl

private theorem exists_fixed_mul_unit (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    {π : v.adicCompletion K}
    (hπE : Valued.v (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) π) = Multiplicative.ofAdd (-1 : ℤ))
    (x : (w.1.adicCompletion L)ˣ) :
    ∃ t u : (w.1.adicCompletion L)ˣ, θ.toAlgHom.toRingHom t = t ∧
      (u : w.1.adicCompletion L) ∈ w.1.adicCompletionIntegers L ∧
      ((u⁻¹ : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) ∈ w.1.adicCompletionIntegers L ∧ x = t * u := by
  have hπE0 : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπE
    exact WithZero.zero_ne_coe hπE
  obtain ⟨j, y, hy, hy', hxy⟩ := exists_zpow_mul_unit L w.1 hπE x
  refine ⟨Units.mk0 _ (zpow_ne_zero j hπE0), y, ?_, hy, hy', Units.ext ?_⟩
  · rw [Units.val_mk0, map_zpow₀]
    exact congrArg (· ^ j) (θ.commutes π)
  · rw [Units.val_mul, Units.val_mk0]
    exact hxy

private theorem twistedConj_eq_iff [FiniteDimensional K L]
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : ∀ x : w.1.adicCompletion L,
      θ x = x ↔ x ∈ Set.range (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)))
    (a b : (w.1.adicCompletion L)ˣ) (α β : (v.adicCompletion K)ˣ)
    (hα : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K) =
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (a : w.1.adicCompletion L))
    (hβ : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K) =
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (b : w.1.adicCompletion L))
    (hne : (β : v.adicCompletion K) / (α : v.adicCompletion K) ≠ 1) (x : GL (Fin 2) (w.1.adicCompletion L)) :
    x⁻¹ * diagOf a b * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x = diagOf a b ↔
      ∃ t₁ t₂ : (w.1.adicCompletion L)ˣ,
        θ.toAlgHom.toRingHom t₁ = t₁ ∧ θ.toAlgHom.toRingHom t₂ = t₂ ∧ x = diagOf t₁ t₂ := by
  have hord : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := orderOf_eq_finrank θ hθ
  rw [← hord] at hα hβ
  have hμ := algebraMap_div_eq_prod θ (orderOf θ) hα hβ
  have hμ' := algebraMap_div_eq_prod θ (orderOf θ) hβ hα
  have hne' : (α : v.adicCompletion K) / (β : v.adicCompletion K) ≠ 1 := by
    intro h
    apply hne
    rw [← inv_div, h, inv_one]
  exact twistedConj_eq_self_iff θ.toAlgHom.toRingHom a b (fun q hq => eq_zero_of_apply_eq_mul θ _ _ hμ hne q hq)
    (fun r hr => eq_zero_of_apply_eq_mul θ _ _ hμ' hne' r hr) x

private noncomputable def thetaSub (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (a b : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L →ₗ[v.adicCompletion K] w.1.adicCompletion L :=
  θ.toLinearMap - LinearMap.mulLeft (v.adicCompletion K) ((b : w.1.adicCompletion L) / (a : w.1.adicCompletion L))

private theorem injective_theta_sub [FiniteDimensional K L]
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : ∀ x : w.1.adicCompletion L,
      θ x = x ↔ x ∈ Set.range (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)))
    (a b : (w.1.adicCompletion L)ˣ) (α β : (v.adicCompletion K)ˣ)
    (hα : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K) =
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (a : w.1.adicCompletion L))
    (hβ : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K) =
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (b : w.1.adicCompletion L))
    (hne : (β : v.adicCompletion K) / (α : v.adicCompletion K) ≠ 1) :
    Function.Injective ⇑(thetaSub K v L w θ a b) := by
  have hord : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := orderOf_eq_finrank θ hθ
  rw [← hord] at hα hβ
  have hμ := algebraMap_div_eq_prod θ (orderOf θ) hα hβ
  have hc : (b : w.1.adicCompletion L) / (a : w.1.adicCompletion L) ≠ 0 := div_ne_zero b.ne_zero a.ne_zero
  have hdetψ : LinearMap.det (θ.toLinearMap -
      LinearMap.mulLeft (v.adicCompletion K) ((b : w.1.adicCompletion L) / (a : w.1.adicCompletion L))) =
      LinearMap.det θ.toLinearMap * ((1 : v.adicCompletion K) - (β : v.adicCompletion K) / (α : v.adicCompletion K)) :=
    det_toLinearMap_sub_mulLeft θ hord hc ((β : v.adicCompletion K) / (α : v.adicCompletion K)) hμ
  have hn0 : orderOf θ ≠ 0 := by
    rw [hord]
    exact Module.finrank_pos.ne'
  have hdetθ0 : LinearMap.det θ.toLinearMap ≠ 0 := by
    intro h
    have h1 := det_toLinearMap_pow_orderOf θ
    rw [h, zero_pow hn0] at h1
    exact zero_ne_one h1
  rw [← LinearMap.ker_eq_bot]
  by_contra h
  have h0 : LinearMap.det (θ.toLinearMap -
      LinearMap.mulLeft (v.adicCompletion K) ((b : w.1.adicCompletion L) / (a : w.1.adicCompletion L))) = 0 :=
    LinearMap.det_eq_zero_iff_ker_ne_bot.2 h
  rw [hdetψ] at h0
  exact mul_ne_zero hdetθ0 (sub_ne_zero.2 hne.symm) h0

private noncomputable def scaledMap (ψ : w.1.adicCompletion L →ₗ[v.adicCompletion K] w.1.adicCompletion L)
    (s : v.adicCompletionIntegers K) :
    w.1.adicCompletion L →ₗ[v.adicCompletionIntegers K] w.1.adicCompletion L :=
  (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) s • ψ).restrictScalars (v.adicCompletionIntegers K)

private theorem relIndex_smul_id [FiniteDimensional K L] {ϖ : v.adicCompletionIntegers K}
    (hϖ : Valued.v (ϖ : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) (N : ℕ)
    (hE : ∀ x : w.1.adicCompletion L, ∃ k : ℕ, ϖ ^ k • x ∈ intLattice K v L w)
    (hF : ∀ c : v.adicCompletion K, ∃ k : ℕ, ∃ r : v.adicCompletionIntegers K,
      ϖ ^ k • c = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) :
    ((intLattice K v L w).map (scaledMap K v L w LinearMap.id (ϖ ^ N))).toAddSubgroup.relIndex
        (intLattice K v L w).toAddSubgroup =
      Ideal.absNorm v.asIdeal ^ (N * Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)) := by
  haveI := finite_intLattice K v L w
  haveI := isTorsionFree_intLattice K v L w
  have hϖirr : Irreducible ϖ := irreducible_of_valued_eq K v hϖ
  have hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0 := fun h =>
    hϖirr.ne_zero (Subtype.ext h)
  have hs0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ ^ N) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero N hϖ0
  have hψ₀ : ∀ x ∈ intLattice K v L w, scaledMap K v L w LinearMap.id (ϖ ^ N) x ∈ intLattice K v L w :=
    fun x hx => (intLattice K v L w).smul_mem (ϖ ^ N) hx
  have hinj₀ : Function.Injective
      ⇑(algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ ^ N) • (LinearMap.id :
        w.1.adicCompletion L →ₗ[v.adicCompletion K] w.1.adicCompletion L)) := fun x y hxy =>
    smul_right_injective (w.1.adicCompletion L) hs0 hxy
  have hd₀ := algebraMap_det_restrict (intLattice K v L w) hϖ0 hF hE
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ ^ N) •
      (LinearMap.id : w.1.adicCompletion L →ₗ[v.adicCompletion K] w.1.adicCompletion L)) hψ₀
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one] at hd₀
  have hd₀' : ((LinearMap.det ((scaledMap K v L w LinearMap.id (ϖ ^ N)).restrict hψ₀) : v.adicCompletionIntegers K) :
        v.adicCompletion K) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ ^ N) ^
        Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := hd₀
  have hv₀ : Valued.v ((LinearMap.det ((scaledMap K v L w LinearMap.id (ϖ ^ N)).restrict hψ₀) :
        v.adicCompletionIntegers K) : v.adicCompletion K) =
      Multiplicative.ofAdd ((N * Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)) • (-1 : ℤ)) := by
    have hϖ' : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) =
      Multiplicative.ofAdd (-1 : ℤ) := hϖ
    rw [hd₀', map_pow, map_pow, map_pow, hϖ', ← pow_mul, ← WithZero.coe_pow, ← ofAdd_nsmul]
  have hd₀0 : LinearMap.det ((scaledMap K v L w LinearMap.id (ϖ ^ N)).restrict hψ₀) ≠ 0 := by
    intro h
    rw [h, ZeroMemClass.coe_zero, map_zero] at hv₀
    exact WithZero.zero_ne_coe hv₀
  obtain ⟨k₀, hk₀, hassoc₀⟩ := exists_associated_pow_of_valued_eq K v hϖirr hϖ (valued_coe_unit K v) hd₀0 hv₀
  have h := relIndex_map_eq_pow (intLattice K v L w) hϖirr
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ ^ N) •
      (LinearMap.id : w.1.adicCompletion L →ₗ[v.adicCompletion K] w.1.adicCompletion L)) hψ₀ hinj₀ hassoc₀
  rw [natCard_residueField_eq_absNorm] at h
  refine h.trans ?_
  congr 1
  have hk : (k₀ : ℤ) = ((N * Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) : ℕ) : ℤ) := by
    rw [hk₀]
    simp
  exact_mod_cast hk

private theorem valued_det_thetaSub [FiniteDimensional K L]
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : ∀ x : w.1.adicCompletion L,
      θ x = x ↔ x ∈ Set.range (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)))
    (a b : (w.1.adicCompletion L)ˣ) (α β : (v.adicCompletion K)ˣ)
    (hα : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K) =
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (a : w.1.adicCompletion L))
    (hβ : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K) =
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (b : w.1.adicCompletion L))
    (m : ℤ)
    (hm : Valued.v ((1 : v.adicCompletion K) - (β : v.adicCompletion K) / (α : v.adicCompletion K)) =
      ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    :
    Valued.v (LinearMap.det (thetaSub K v L w θ a b)) =
      ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have hord : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := orderOf_eq_finrank θ hθ
  rw [← hord] at hα hβ
  have hμ := algebraMap_div_eq_prod θ (orderOf θ) hα hβ
  have hc : (b : w.1.adicCompletion L) / (a : w.1.adicCompletion L) ≠ 0 := div_ne_zero b.ne_zero a.ne_zero
  have hn0 : orderOf θ ≠ 0 := by
    rw [hord]
    exact Module.finrank_pos.ne'
  have hdetθ1 : Valued.v (LinearMap.det θ.toLinearMap) = 1 :=
    valued_eq_one_of_pow_eq_one K v hn0 (det_toLinearMap_pow_orderOf θ)
  have hdet' : LinearMap.det (θ.toLinearMap -
      LinearMap.mulLeft (v.adicCompletion K) ((b : w.1.adicCompletion L) / (a : w.1.adicCompletion L))) =
      LinearMap.det θ.toLinearMap * ((1 : v.adicCompletion K) - (β : v.adicCompletion K) / (α : v.adicCompletion K)) :=
    det_toLinearMap_sub_mulLeft θ hord hc ((β : v.adicCompletion K) / (α : v.adicCompletion K)) hμ
  show Valued.v (LinearMap.det (θ.toLinearMap -
      LinearMap.mulLeft (v.adicCompletion K) ((b : w.1.adicCompletion L) / (a : w.1.adicCompletion L)))) = _
  rw [hdet', map_mul, hdetθ1, one_mul, hm]

private theorem valued_det_restrict_scaledMap [FiniteDimensional K L]
    (ψ : w.1.adicCompletion L →ₗ[v.adicCompletion K] w.1.adicCompletion L) (m : ℤ)
    (hdet : Valued.v (LinearMap.det ψ) =
      ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {ϖ : v.adicCompletionIntegers K} (hϖ : Valued.v (ϖ : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) (N : ℕ)
    (hψ : ∀ x ∈ intLattice K v L w, scaledMap K v L w ψ (ϖ ^ N) x ∈ intLattice K v L w)
    (hE : ∀ x : w.1.adicCompletion L, ∃ k : ℕ, ϖ ^ k • x ∈ intLattice K v L w)
    (hF : ∀ c : v.adicCompletion K, ∃ k : ℕ, ∃ r : v.adicCompletionIntegers K,
      ϖ ^ k • c = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r)
    :
    Valued.v ((LinearMap.det ((scaledMap K v L w ψ (ϖ ^ N)).restrict hψ) : v.adicCompletionIntegers K) :
        v.adicCompletion K) =
      Multiplicative.ofAdd ((N * Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)) • (-1 : ℤ) + -m) := by
  haveI := finite_intLattice K v L w
  haveI := isTorsionFree_intLattice K v L w
  have hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0 := fun h =>
    (irreducible_of_valued_eq K v hϖ).ne_zero (Subtype.ext h)
  have hd := algebraMap_det_restrict (intLattice K v L w) hϖ0 hF hE
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ ^ N) • ψ) hψ
  rw [LinearMap.det_smul] at hd
  have hd' : ((LinearMap.det ((scaledMap K v L w ψ (ϖ ^ N)).restrict hψ) : v.adicCompletionIntegers K) :
        v.adicCompletion K) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ ^ N) ^
        Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) * LinearMap.det ψ := hd
  have hϖ' : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) =
    Multiplicative.ofAdd (-1 : ℤ) := hϖ
  rw [hd', map_mul, hdet, map_pow, map_pow, map_pow, hϖ', ← pow_mul, ← WithZero.coe_pow, ← ofAdd_nsmul,
    ← WithZero.coe_mul, ← ofAdd_add]

private theorem relIndex_scaledMap_thetaSub [FiniteDimensional K L]
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : ∀ x : w.1.adicCompletion L,
      θ x = x ↔ x ∈ Set.range (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)))
    (a b : (w.1.adicCompletion L)ˣ) (α β : (v.adicCompletion K)ˣ)
    (hα : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K) =
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (a : w.1.adicCompletion L))
    (hβ : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K) =
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (b : w.1.adicCompletion L))
    (m : ℤ)
    (hm : Valued.v ((1 : v.adicCompletion K) - (β : v.adicCompletion K) / (α : v.adicCompletion K)) =
      ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {ϖ : v.adicCompletionIntegers K} (hϖ : Valued.v (ϖ : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) (N : ℕ)
    (hN : ∀ x ∈ intLattice K v L w, ϖ ^ N • thetaSub K v L w θ a b x ∈ intLattice K v L w)
    (hE : ∀ x : w.1.adicCompletion L, ∃ k : ℕ, ϖ ^ k • x ∈ intLattice K v L w)
    (hF : ∀ c : v.adicCompletion K, ∃ k : ℕ, ∃ r : v.adicCompletionIntegers K,
      ϖ ^ k • c = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r)
    :
    (((intLattice K v L w).map (scaledMap K v L w (thetaSub K v L w θ a b) (ϖ ^ N))).toAddSubgroup.relIndex
        (intLattice K v L w).toAddSubgroup : ℂ) =
      (Ideal.absNorm v.asIdeal : ℂ) ^
        (((N * Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) : ℕ) : ℤ) + m) := by
  haveI := finite_intLattice K v L w
  haveI := isTorsionFree_intLattice K v L w
  have hne : (β : v.adicCompletion K) / (α : v.adicCompletion K) ≠ 1 := by
    intro h
    rw [h, sub_self, map_zero] at hm
    exact WithZero.zero_ne_coe hm
  have hinjψ := injective_theta_sub K v L w θ hθ a b α β hα hβ hne
  have hϖirr : Irreducible ϖ := irreducible_of_valued_eq K v hϖ
  have hs0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ ^ N) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero N fun h => hϖirr.ne_zero (Subtype.ext h)
  have hψN : ∀ x ∈ intLattice K v L w, scaledMap K v L w (thetaSub K v L w θ a b) (ϖ ^ N) x ∈ intLattice K v L w :=
    fun x hx => hN x hx
  have hinjN : Function.Injective
      ⇑(algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ ^ N) • thetaSub K v L w θ a b) :=
    fun x y hxy => hinjψ (smul_right_injective (w.1.adicCompletion L) hs0 hxy)
  have hvN := valued_det_restrict_scaledMap K v L w (thetaSub K v L w θ a b) m
    (valued_det_thetaSub K v L w θ hθ a b α β hα hβ m hm) hϖ N hψN hE hF
  have hdN0 : LinearMap.det ((scaledMap K v L w (thetaSub K v L w θ a b) (ϖ ^ N)).restrict hψN) ≠ 0 := by
    intro h
    rw [h, ZeroMemClass.coe_zero, map_zero] at hvN
    exact WithZero.zero_ne_coe hvN
  obtain ⟨kN, hkN, hassocN⟩ := exists_associated_pow_of_valued_eq K v hϖirr hϖ (valued_coe_unit K v) hdN0 hvN
  have h := relIndex_map_eq_pow (intLattice K v L w) hϖirr
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ ^ N) • thetaSub K v L w θ a b) hψN hinjN hassocN
  rw [natCard_residueField_eq_absNorm] at h
  have h' : ((intLattice K v L w).map (scaledMap K v L w (thetaSub K v L w θ a b) (ϖ ^ N))).toAddSubgroup.relIndex
      (intLattice K v L w).toAddSubgroup = Ideal.absNorm v.asIdeal ^ kN := h
  rw [h', Nat.cast_pow, ← zpow_natCast]
  congr 1
  rw [hkN]
  simp only [smul_neg, nsmul_eq_mul, mul_one, neg_neg, neg_add_rev, Nat.cast_mul]
  ring

private theorem finite_and_finsum_twisted_eq [FiniteDimensional K L]
    (φ : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (a b : (w.1.adicCompletion L)ˣ) (m : ℤ)
    (hinjψ : Function.Injective ⇑(thetaSub K v L w θ a b)) {ϖ : v.adicCompletionIntegers K} (N : ℕ)
    (hN : ∀ x ∈ intLattice K v L w, ϖ ^ N • thetaSub K v L w θ a b x ∈ intLattice K v L w)
    (h₀ : ((intLattice K v L w).map (scaledMap K v L w LinearMap.id (ϖ ^ N))).toAddSubgroup.relIndex
        (intLattice K v L w).toAddSubgroup =
      Ideal.absNorm v.asIdeal ^ (N * Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)))
    (hN' : (((intLattice K v L w).map (scaledMap K v L w (thetaSub K v L w θ a b) (ϖ ^ N))).toAddSubgroup.relIndex
        (intLattice K v L w).toAddSubgroup : ℂ) =
      (Ideal.absNorm v.asIdeal : ℂ) ^
        (((N * Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) : ℕ) : ℤ) + m)) :
    (Function.support fun q : w.1.adicCompletion L ⧸ intAdd w.1 => (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
      (diagOf a b * unipOf (θ.toAlgHom.toRingHom (Quotient.out q) -
        (b : w.1.adicCompletion L) / (a : w.1.adicCompletion L) * Quotient.out q))).Finite ∧
    ∑ᶠ q : w.1.adicCompletion L ⧸ intAdd w.1, (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
        (diagOf a b * unipOf (θ.toAlgHom.toRingHom (Quotient.out q) -
        (b : w.1.adicCompletion L) / (a : w.1.adicCompletion L) * Quotient.out q)) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ m *
        ∑ᶠ q : w.1.adicCompletion L ⧸ intAdd w.1,
          (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (diagOf a b * unipOf (Quotient.out q)) := by
  rw [intLattice_toAddSubgroup] at h₀ hN'
  have hσ : ∀ y ∈ w.1.adicCompletionIntegers L, θ.toAlgHom.toRingHom y ∈ w.1.adicCompletionIntegers L :=
    fun y hy => algEquiv_mem_integers K v L w θ hy
  have hNv : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
  have hLO : ((intLattice K v L w).map (scaledMap K v L w LinearMap.id (ϖ ^ N))).toAddSubgroup ≤ intAdd w.1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact (intLattice K v L w).smul_mem (ϖ ^ N) hx
  have hcomm : ∀ x : w.1.adicCompletion L,
      thetaSub K v L w θ a b (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ ^ N) • x) =
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ ^ N) • thetaSub K v L w θ a b x :=
    fun x => map_smul _ _ _
  have hψL : ((intLattice K v L w).map (scaledMap K v L w LinearMap.id (ϖ ^ N))).toAddSubgroup.map
      (LinearEquiv.ofInjectiveEndo _ hinjψ).toAddEquiv.toAddMonoidHom =
      ((intLattice K v L w).map (scaledMap K v L w (thetaSub K v L w θ a b) (ϖ ^ N))).toAddSubgroup := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (hcomm x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ ^ N) • x, ⟨x, hx, rfl⟩, hcomm x⟩
  have hψL' : ((intLattice K v L w).map (scaledMap K v L w LinearMap.id (ϖ ^ N))).toAddSubgroup.map
      (LinearEquiv.ofInjectiveEndo _ hinjψ).toAddEquiv.toAddMonoidHom ≤ intAdd w.1 :=
    hψL.le.trans fun _ hz => by
      obtain ⟨x, hx, rfl⟩ := hz
      exact hN x hx
  have hidx : ((intLattice K v L w).map (scaledMap K v L w LinearMap.id (ϖ ^ N))).toAddSubgroup.relIndex
      (intAdd w.1) ≠ 0 := by
    rw [h₀]
    exact pow_ne_zero _ (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
  have hidx' : (((intLattice K v L w).map (scaledMap K v L w LinearMap.id (ϖ ^ N))).toAddSubgroup.map
      (LinearEquiv.ofInjectiveEndo _ hinjψ).toAddEquiv.toAddMonoidHom).relIndex (intAdd w.1) ≠ 0 := by
    rw [hψL]
    intro h
    rw [h, Nat.cast_zero] at hN'
    exact zpow_ne_zero _ hNv hN'.symm
  have hψapp : ∀ y : w.1.adicCompletion L, (LinearEquiv.ofInjectiveEndo _ hinjψ).toAddEquiv y =
      θ.toAlgHom.toRingHom y - (b : w.1.adicCompletion L) / (a : w.1.adicCompletion L) * y := fun _ => rfl
  have hfin' := finite_support_comp (intAdd w.1) _ hLO (LinearEquiv.ofInjectiveEndo _ hinjψ).toAddEquiv hψL' hidx'
    (fun z => (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (diagOf a b * unipOf z))
    (fun z o ho => hecke_mul_unipOf_add_of_mem φ (diagOf a b) z ho) (finite_support_out φ (diagOf a b))
  have hQ := relIndex_mul_finsum_quotient_comp (intAdd w.1) _ hLO (LinearEquiv.ofInjectiveEndo _ hinjψ).toAddEquiv
    hψL' hidx hidx' (fun z => (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (diagOf a b * unipOf z))
    (fun z o ho => hecke_mul_unipOf_add_of_mem φ (diagOf a b) z ho)
    (fun z o ho => hecke_diagOf_mul_unipOf_add_of_mem φ θ.toAlgHom.toRingHom hσ a b z ho)
    (finite_support_out φ (diagOf a b))
  simp only [hψapp] at hfin' hQ
  refine ⟨hfin', ?_⟩
  rw [hψL, h₀, hN', Nat.cast_pow, zpow_add₀ hNv, zpow_natCast, mul_assoc] at hQ
  exact mul_left_cancel₀ (pow_ne_zero _ hNv) hQ

end Carriers

end TwistedUnfolding
p2m_reactivate "P2MW.S_AutomorphicForm_sum_relIndex_mul_twistedConj_diagonal_eq_zpow_absNorm_mul_finsum_of_ramificationIdx_eq_one.TwistedUnfolding"

end
p2m_reactivate "P2MW.S_AutomorphicForm_sum_relIndex_mul_twistedConj_diagonal_eq_zpow_absNorm_mul_finsum_of_ramificationIdx_eq_one.TwistedUnfolding"

open AutomorphicForm TwistedUnfolding in

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (L : Type) [Field L] [NumberField L] [Algebra K L] (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : ∀ x : w.1.adicCompletion L,
      θ x = x ↔ x ∈ Set.range (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)))
    (φ : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ)
    (a b : (w.1.adicCompletion L)ˣ) (α β : (v.adicCompletion K)ˣ)
    (hα : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K) =
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (a : w.1.adicCompletion L))
    (hβ : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K) =
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (b : w.1.adicCompletion L))
    (m : ℤ)
    (hm : Valued.v ((1 : v.adicCompletion K) - (β : v.adicCompletion K) / (α : v.adicCompletion K)) =
      ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (δ : GL (Fin 2) (w.1.adicCompletion L))
    (hδ : (δ : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      !![(a : w.1.adicCompletion L), 0; 0, (b : w.1.adicCompletion L)])
    (T : Subgroup (GL (Fin 2) (w.1.adicCompletion L)))
    (hT : ∀ x : GL (Fin 2) (w.1.adicCompletion L),
      x ∈ T ↔ x⁻¹ * δ * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x = δ)
    (S : Finset (GL (Fin 2) (w.1.adicCompletion L)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ T,
      ∀ u ∈ LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L),
        s' = t * s * u → s' = s)
    (hcov : ∀ x : GL (Fin 2) (w.1.adicCompletion L),
      (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
          (x⁻¹ * δ * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x) ≠ 0 →
        ∃ s ∈ S, ∃ t ∈ T,
          ∃ u ∈ LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L), x = t * s * u) :
    ∑ x ∈ S,
        (((T ⊓ (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)).map
              (MulAut.conj x).toMonoidHom).relIndex
            (T ⊓ LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) : ℕ) : ℂ) *
          (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
            (x⁻¹ * δ * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ m *
        ∑ᶠ c : GL (Fin 2) (w.1.adicCompletion L) ⧸
          LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L),
        Set.indicator
          {c : GL (Fin 2) (w.1.adicCompletion L) ⧸
              LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) |
            ∃ g : GL (Fin 2) (w.1.adicCompletion L), QuotientGroup.mk g = c ∧
              (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 0 = 0 ∧
              (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 0 0 = (a : w.1.adicCompletion L) ∧
              (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 1 = (b : w.1.adicCompletion L)}
          (fun c => (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (Quotient.out c)) c := by
  haveI hKL : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have hδ' : δ = diagOf a b := Units.ext (by rw [hδ, coe_diagOf])
  subst hδ'
  have hne : (β : v.adicCompletion K) / (α : v.adicCompletion K) ≠ 1 := by
    intro h
    rw [h, sub_self, map_zero] at hm
    exact WithZero.zero_ne_coe hm
  have hT' : ∀ x : GL (Fin 2) (w.1.adicCompletion L), x ∈ T ↔ ∃ t₁ t₂ : (w.1.adicCompletion L)ˣ,
      θ.toAlgHom.toRingHom t₁ = t₁ ∧ θ.toAlgHom.toRingHom t₂ = t₂ ∧ x = diagOf t₁ t₂ := fun x =>
    (hT x).trans (twistedConj_eq_iff K v L w θ hθ a b α β hα hβ hne x)
  have hσ : ∀ y ∈ w.1.adicCompletionIntegers L, θ.toAlgHom.toRingHom y ∈ w.1.adicCompletionIntegers L :=
    fun y hy => algEquiv_mem_integers K v L w θ hy
  obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.adicCompletion.exists_uniformizer K v
  have hϖE := valued_algebraMap_eq K v L w hw hϖ
  have hfac := exists_fixed_mul_unit K v L w θ hϖE
  have hE := exists_pow_smul_mem_intLattice K v L w hϖE
  have hF := exists_pow_smul_eq_algebraMap_of_valued K v hϖ
  haveI := finite_intLattice K v L w
  obtain ⟨N, hN⟩ := exists_pow_smul_map_mem (intLattice K v L w) (Module.Finite.iff_fg.1 inferInstance) hE
    (thetaSub K v L w θ a b)
  obtain ⟨hfinT, hsum⟩ := finite_and_finsum_twisted_eq K v L w φ θ a b m
    (injective_theta_sub K v L w θ hθ a b α β hα hβ hne) N hN (relIndex_smul_id K v L w hϖ N hE hF)
    (relIndex_scaledMap_thetaSub K v L w θ hθ a b α β hα hβ m hm hϖ N hN hE hF)
  have hfinT' : (Function.support fun q : w.1.adicCompletion L ⧸ intAdd w.1 =>
      twistedFn φ θ.toAlgHom.toRingHom a b (unipOf (Quotient.out q))).Finite := by
    simpa only [twistedFn_unipOf] using hfinT
  have hL := sum_weight_mul_twistedFn φ θ.toAlgHom.toRingHom hσ a b T hT' hfac S hS hcov hfinT'
  rw [finsum_indicator_eq φ a b (diagOf a b) hδ]
  refine hL.trans ?_
  simp only [twistedFn_unipOf]
  exact hsum

end S_AutomorphicForm_sum_relIndex_mul_twistedConj_diagonal_eq_zpow_absNorm_mul_finsum_of_ramificationIdx_eq_one
end P2MW
export P2MW.S_AutomorphicForm_sum_relIndex_mul_twistedConj_diagonal_eq_zpow_absNorm_mul_finsum_of_ramificationIdx_eq_one (solution)
