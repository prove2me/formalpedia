-- Prove2me | solution 1 for AlgebraicCurve.residue_norm_eq_norm_residue_of_retraction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/ab9726fe-d29b-5891-a7de-e7fb2aa1bbd2

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_residue_norm_eq_norm_residue_of_retraction

open AlgebraicCurve
open scoped Polynomial

namespace DeuringNormResidue

section RationalPlace

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A)
  (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)

include hKA in
theorem valuation_algebraMap_eq_one {k : K} (hk : k ≠ 0) :
    A.valuation (algebraMap K E k) = 1 := by
  apply le_antisymm ((A.valuation_le_one_iff _).mpr (hKA k))
  have h1 : A.valuation (algebraMap K E k) * A.valuation (algebraMap K E k⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hk, map_one, map_one]
  have h2 : A.valuation (algebraMap K E k⁻¹) ≤ 1 := (A.valuation_le_one_iff _).mpr (hKA _)
  calc (1 : A.ValueGroup) = _ := h1.symm
    _ ≤ A.valuation (algebraMap K E k) * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

include hKA in
theorem valuation_algebraMap_le_one (k : K) : A.valuation (algebraMap K E k) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (hKA k)

include hKA in

theorem const_unique {a : E} {k k' : K}
    (hk : A.valuation (a - algebraMap K E k) < 1) (hk' : A.valuation (a - algebraMap K E k') < 1) :
    k = k' := by
  by_contra hne
  have hsub : algebraMap K E k' - algebraMap K E k =
      (a - algebraMap K E k) - (a - algebraMap K E k') := by ring
  have h1 : A.valuation (algebraMap K E k' - algebraMap K E k) < 1 := by
    rw [hsub]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hk hk')
  have h2 : A.valuation (algebraMap K E k' - algebraMap K E k) = 1 := by
    rw [← map_sub]
    exact valuation_algebraMap_eq_one A hKA (sub_ne_zero.mpr (Ne.symm hne))
  exact (lt_irrefl (1 : A.ValueGroup)) (h2 ▸ h1)

noncomputable def sigmaFun (a : A) : K := (hArat a a.2).choose

theorem sigmaFun_spec (a : A) :
    A.valuation ((a : E) - algebraMap K E (sigmaFun A hArat a)) < 1 :=
  (hArat a a.2).choose_spec

include hKA in
theorem sigmaFun_eq_iff (a : A) (k : K) :
    sigmaFun A hArat a = k ↔ A.valuation ((a : E) - algebraMap K E k) < 1 :=
  ⟨fun h => h ▸ sigmaFun_spec A hArat a, fun h => const_unique A hKA (sigmaFun_spec A hArat a) h⟩

noncomputable def sigma : A →+* K where
  toFun := sigmaFun A hArat
  map_one' := by
    rw [sigmaFun_eq_iff A hKA hArat]
    simp
  map_mul' a b := by
    rw [sigmaFun_eq_iff A hKA hArat]
    have ha := sigmaFun_spec A hArat a
    have hb := sigmaFun_spec A hArat b
    set k := sigmaFun A hArat a
    set k' := sigmaFun A hArat b
    have hid : ((a * b : A) : E) - algebraMap K E (k * k') =
        (a : E) * ((b : E) - algebraMap K E k') + algebraMap K E k' * ((a : E) - algebraMap K E k) := by
      simp only [MulMemClass.coe_mul, map_mul]; ring
    rw [hid]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]
      exact (mul_le_mul_left (A.valuation_le_one a) _).trans_lt (by rwa [one_mul])
    · rw [map_mul]
      exact (mul_le_mul_left (valuation_algebraMap_le_one A hKA k') _).trans_lt
        (by rwa [one_mul])
  map_zero' := by
    rw [sigmaFun_eq_iff A hKA hArat]
    simp
  map_add' a b := by
    rw [sigmaFun_eq_iff A hKA hArat]
    have ha := sigmaFun_spec A hArat a
    have hb := sigmaFun_spec A hArat b
    set k := sigmaFun A hArat a
    set k' := sigmaFun A hArat b
    have hid : ((a + b : A) : E) - algebraMap K E (k + k') =
        ((a : E) - algebraMap K E k) + ((b : E) - algebraMap K E k') := by
      simp only [AddMemClass.coe_add, map_add]; ring
    rw [hid]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)

theorem sigma_spec (a : A) :
    A.valuation ((a : E) - algebraMap K E (sigma A hKA hArat a)) < 1 :=
  sigmaFun_spec A hArat a

theorem sigma_eq_iff (a : A) (k : K) :
    sigma A hKA hArat a = k ↔ A.valuation ((a : E) - algebraMap K E k) < 1 :=
  sigmaFun_eq_iff A hKA hArat a k

end RationalPlace

open Polynomial in

theorem linearIndependent_pow_of_transcendental' {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    {x : S} (hx : Transcendental R x) : LinearIndependent R fun k : ℕ => x ^ k := by
  rw [linearIndependent_iff]
  intro l hl
  set p : R[X] := l.sum fun n a => Polynomial.monomial n a with hp
  have hcoeff : ∀ n, p.coeff n = l n := fun n => by
    rw [hp, Finsupp.sum, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · exact (Finsupp.notMem_support_iff.mp h).symm
  have h1 : aeval x p = Finsupp.linearCombination R (fun k : ℕ => x ^ k) l := by
    rw [hp, Finsupp.sum, map_sum, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [aeval_monomial, Algebra.smul_def]
  have h2 := (transcendental_iff.mp hx) p (h1.trans hl)
  ext n
  rw [← hcoeff, h2, Polynomial.coeff_zero, Finsupp.zero_apply]

theorem transcendental_ratFunc_X (K : Type*) [Field K] :
    Transcendental K (RatFunc.X : RatFunc K) := by
  rw [transcendental_iff_injective]
  intro p q hpq
  simp only [RatFunc.aeval_X_left_eq_algebraMap] at hpq
  exact IsFractionRing.injective K[X] (RatFunc K) hpq

theorem isUnit_iff_inv_mem {L : Type*} [Field L] (O : ValuationSubring L) (z : O) (hz : (z : L) ≠ 0) :
    IsUnit z ↔ (z : L)⁻¹ ∈ O := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 := congrArg (fun w : O => (w : L)) u.mul_inv
    simp only [Subring.coe_one, hu] at h1
    push_cast at h1
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact SetLike.coe_mem _
  · intro h
    exact ⟨⟨z, ⟨(z : L)⁻¹, h⟩, Subtype.ext (mul_inv_cancel₀ hz), Subtype.ext (inv_mul_cancel₀ hz)⟩, rfl⟩

theorem map_eq_zero_of_not_isUnit {L R : Type*} [Field L] [Semiring R] (O : ValuationSubring L)
    (ρ : O →+* R) (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O) {z : O} (hz : ¬ IsUnit z) :
    ρ z = 0 := by
  rw [← RingHom.mem_ker, hker]
  exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hz)

theorem isUnit_of_map_ne_zero {L R : Type*} [Field L] [Semiring R] (O : ValuationSubring L)
    (ρ : O →+* R) (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O) {z : O} (hz : ρ z ≠ 0) :
    IsUnit z := by
  by_contra h
  exact hz (map_eq_zero_of_not_isUnit O ρ hker h)

section TwoTowers

variable {K F E FE : Type*} [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra (RatFunc E) FE] [IsScalarTower E (RatFunc E) FE]

theorem algebraMap_polynomial_map
    (hX : algebraMap (RatFunc E) FE RatFunc.X = algebraMap F FE (algebraMap (RatFunc K) F RatFunc.X))
    (p : K[X]) :
    algebraMap (RatFunc E) FE (algebraMap E[X] (RatFunc E) (p.map (algebraMap K E))) =
      algebraMap F FE (algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) p)) := by
  set fL : K[X] →+* FE := (algebraMap (RatFunc E) FE).comp
    ((algebraMap E[X] (RatFunc E)).comp (Polynomial.mapRingHom (algebraMap K E))) with hfL
  set fR : K[X] →+* FE := (algebraMap F FE).comp
    ((algebraMap (RatFunc K) F).comp (algebraMap K[X] (RatFunc K))) with hfR
  have hLR : fL = fR := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [hfL, hfR, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        RatFunc.algebraMap_C]
      rw [← RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_eq_C,
        ← IsScalarTower.algebraMap_apply E (RatFunc E) FE,
        ← IsScalarTower.algebraMap_apply K E FE, ← IsScalarTower.algebraMap_apply K (RatFunc K) F,
        ← IsScalarTower.algebraMap_apply K F FE]
    · simp only [hfL, hfR, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
        RatFunc.algebraMap_X, hX]
  have := DFunLike.congr_fun hLR p
  simpa [hfL, hfR] using this

theorem exists_algebraMap_eq
    (hX : algebraMap (RatFunc E) FE RatFunc.X = algebraMap F FE (algebraMap (RatFunc K) F RatFunc.X))
    (l : RatFunc K) :
    ∃ m : RatFunc E, algebraMap (RatFunc E) FE m = algebraMap F FE (algebraMap (RatFunc K) F l) := by
  refine ⟨algebraMap E[X] (RatFunc E) (l.num.map (algebraMap K E)) /
    algebraMap E[X] (RatFunc E) (l.denom.map (algebraMap K E)), ?_⟩
  conv_rhs => rw [← RatFunc.num_div_denom l]
  rw [map_div₀, map_div₀, map_div₀, algebraMap_polynomial_map hX, algebraMap_polynomial_map hX]

theorem algebraMap_ratFunc_polynomial (p : E[X]) :
    algebraMap (RatFunc E) FE (algebraMap E[X] (RatFunc E) p) =
      Polynomial.aeval (algebraMap (RatFunc E) FE RatFunc.X) p := by
  rw [Polynomial.aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap]

variable [IsAlgClosed K] [CharZero K]

theorem exists_basis_algebraMap
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hX : algebraMap (RatFunc E) FE RatFunc.X = algebraMap F FE (algebraMap (RatFunc K) F RatFunc.X))
    {ι : Type*} [Finite ι] (b : Module.Basis ι (RatFunc K) F) :
    ∃ β : Module.Basis ι (RatFunc E) FE, ∀ i, β i = algebraMap F FE (b i) := by
  classical
  cases nonempty_fintype ι
  set b' : ι → FE := fun i => algebraMap F FE (b i) with hb'

  have hpow : LinearIndependent K fun k : ℕ => (RatFunc.X : RatFunc K) ^ k :=
    linearIndependent_pow_of_transcendental' (transcendental_ratFunc_X K)
  have h1 : LinearIndependent K fun q : ℕ × ι => ((RatFunc.X : RatFunc K) ^ q.1) • b q.2 :=
    linearIndependent_smul hpow b.linearIndependent
  have hW := AlgebraicCurve.linearIndependent_of_constantFieldExtension K F E FE hfg hfgE hgen h1
  have hW' : LinearIndependent E fun q : ℕ × ι =>
      algebraMap (RatFunc E) FE RatFunc.X ^ q.1 * b' q.2 := by
    convert hW using 1
    funext q
    simp only [hb', Algebra.smul_def, map_mul, map_pow, hX]

  letI : Algebra E[X] FE :=
    ((algebraMap (RatFunc E) FE).comp (algebraMap E[X] (RatFunc E))).toAlgebra
  haveI : IsScalarTower E[X] (RatFunc E) FE := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halg : ∀ p : E[X], algebraMap E[X] FE p =
      Polynomial.aeval (algebraMap (RatFunc E) FE RatFunc.X) p := fun p =>
    algebraMap_ratFunc_polynomial p
  have hR : LinearIndependent E[X] b' := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    set D : ℕ := (s.sup fun i => (g i).natDegree) + 1 with hD
    have hdeg : ∀ i ∈ s, (g i).natDegree < D := fun i hi =>
      Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (g i).natDegree) hi)
    rw [linearIndependent_iff'] at hW'
    have key := hW' (Finset.range D ×ˢ s) (fun q => (g q.2).coeff q.1) ?_
    · ext k
      by_cases hk : k < D
      · simpa using key (k, i) (Finset.mk_mem_product (Finset.mem_range.mpr hk) hi)
      · rw [Polynomial.coeff_zero]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_lt_of_le (hdeg i hi) (not_lt.mp hk))
    · rw [Finset.sum_product_right, ← hg]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Algebra.smul_def, halg, Polynomial.aeval_eq_sum_range' (hdeg j hj), Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_mul_assoc]
  have hu : LinearIndependent (RatFunc E) b' := hR.localization (RatFunc E) (nonZeroDivisors E[X])

  set V : Submodule (RatFunc E) FE := Submodule.span (RatFunc E) (Set.range b') with hV_def
  have hFV : ∀ f : F, algebraMap F FE f ∈ V := by
    intro f
    rw [← b.sum_repr f, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨m, hm⟩ := exists_algebraMap_eq hX (b.repr f i)
    have : algebraMap F FE (b.repr f i • b i) = m • b' i := by
      rw [Algebra.smul_def, map_mul, Algebra.smul_def, hm]
    rw [this]
    exact V.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hVV : V * V ≤ V := by
    rw [hV_def, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    show b' i * b' j ∈ V
    rw [hb']; dsimp only; rw [← map_mul]; exact hFV _
  have h1V : (1 : FE) ∈ V := by simpa using hFV 1
  let S : Subalgebra (RatFunc E) FE :=
    { carrier := V
      mul_mem' := fun ha hb => hVV (Submodule.mul_mem_mul ha hb)
      one_mem' := h1V
      add_mem' := fun ha hb => V.add_mem ha hb
      zero_mem' := V.zero_mem
      algebraMap_mem' := fun e' => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact V.smul_mem _ h1V }
  have hSfg : (Subalgebra.toSubmodule S).FG := Submodule.fg_span (Set.finite_range b')
  have hinv : ∀ z ∈ S, z⁻¹ ∈ S := fun z hz =>
    S.inv_mem_of_algebraic (x := ⟨z, hz⟩) (IsIntegral.of_mem_of_fg S hSfg z hz).isAlgebraic
  let IF : IntermediateField E FE := (S.restrictScalars E).toIntermediateField hinv
  have hIF : IF = ⊤ := by
    rw [eq_top_iff, ← hgen, IntermediateField.adjoin_le_iff]
    rintro _ ⟨f, rfl⟩
    exact hFV f
  have hVtop : V = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ IF := hIF ▸ IntermediateField.mem_top
    exact hz
  refine ⟨Module.Basis.mk hu (by rw [← hV_def, hVtop]), fun i => ?_⟩
  rw [Module.Basis.mk_apply]

end TwoTowers

section Reduction

variable {K F E FE : Type*} [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    (A : ValuationSubring E)
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (O : ValuationSubring FE) (ρ : O →+* F)
    (hO : ∀ c : E, algebraMap E FE c ∈ O ↔ c ∈ A)
    (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
    (hρ : ∀ f : F, ∃ h : algebraMap F FE f ∈ O, ρ ⟨algebraMap F FE f, h⟩ = f)

include hρ in
theorem algebraMap_mem (f : F) : algebraMap F FE f ∈ O := by
  obtain ⟨h, -⟩ := hρ f
  exact h

include hρ in
theorem rho_algebraMap (f : F) (h : algebraMap F FE f ∈ O) : ρ ⟨algebraMap F FE f, h⟩ = f := by
  obtain ⟨h', hh⟩ := hρ f
  exact hh

def constEmb : A →+* O where
  toFun a := ⟨algebraMap E FE a, (hO a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_constEmb (a : A) : ((constEmb A O hO a : O) : FE) = algebraMap E FE a := rfl

include hKA hker hρ in

theorem rho_constEmb (a : A) :
    ρ (constEmb A O hO a) = algebraMap K F (sigma A hKA hArat a) := by
  set k := sigma A hKA hArat a with hk_def
  have hk : A.valuation ((a : E) - algebraMap K E k) < 1 := sigma_spec A hKA hArat a
  have hmA : (a : E) - algebraMap K E k ∈ A := A.sub_mem a.2 (hKA k)

  have hconst : ρ (constEmb A O hO ⟨algebraMap K E k, hKA k⟩) = algebraMap K F k := by
    have e1 : constEmb A O hO ⟨algebraMap K E k, hKA k⟩ =
        ⟨algebraMap F FE (algebraMap K F k), algebraMap_mem O ρ hρ _⟩ :=
      Subtype.ext (by
        simp only [coe_constEmb]
        rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply])
    rw [e1, rho_algebraMap O ρ hρ]

  have hinf : ρ (constEmb A O hO ⟨_, hmA⟩) = 0 := by
    by_cases hm0 : (a : E) - algebraMap K E k = 0
    · have : constEmb A O hO ⟨_, hmA⟩ = 0 := Subtype.ext (by simp [hm0])
      rw [this, map_zero]
    apply map_eq_zero_of_not_isUnit O ρ hker
    intro hu
    have hinv := (isUnit_iff_inv_mem O _ (by
      show algebraMap E FE ((a : E) - algebraMap K E k) ≠ 0
      exact (map_ne_zero _).mpr hm0)).mp hu
    simp only [coe_constEmb, ← map_inv₀] at hinv
    rw [hO] at hinv

    have hunitA : IsUnit (⟨_, hmA⟩ : A) :=
      (isUnit_iff_inv_mem A ⟨_, hmA⟩ hm0).mpr hinv
    have hmax : (⟨_, hmA⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
      (ValuationSubring.valuation_lt_one_iff A _).mpr hk
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmax) hunitA
  have hsplit : a = ⟨algebraMap K E k, hKA k⟩ + ⟨_, hmA⟩ := Subtype.ext (by simp)
  rw [hsplit, map_add, map_add, hconst, hinf, add_zero]

variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra (RatFunc E) FE] [IsScalarTower E (RatFunc E) FE]
    (hX : algebraMap (RatFunc E) FE RatFunc.X = algebraMap F FE (algebraMap (RatFunc K) F RatFunc.X))

omit [Algebra K F] [Algebra E FE] [Algebra K E] [Algebra K FE] [IsScalarTower K E FE]
  [IsScalarTower K F FE] [IsScalarTower K (RatFunc K) F] [IsScalarTower E (RatFunc E) FE] in
include hX hρ in
theorem X_mem : algebraMap (RatFunc E) FE RatFunc.X ∈ O := by
  rw [hX]; exact algebraMap_mem O ρ hρ _

noncomputable def polyEmb : A[X] →+* O :=
  Polynomial.eval₂RingHom (constEmb A O hO) ⟨_, X_mem O ρ hρ hX⟩

omit [Algebra K F] [Algebra K E] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
  [IsScalarTower K (RatFunc K) F] in
theorem coe_polyEmb (p₀ : A[X]) :
    ((polyEmb A O ρ hO hρ hX p₀ : O) : FE) =
      algebraMap (RatFunc E) FE (algebraMap E[X] (RatFunc E) (p₀.map (algebraMap A E))) := by
  have hLR : O.subtype.comp (polyEmb A O ρ hO hρ hX) =
      (algebraMap (RatFunc E) FE).comp
        ((algebraMap E[X] (RatFunc E)).comp (Polynomial.mapRingHom (algebraMap A E))) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [polyEmb, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        Polynomial.coe_mapRingHom, Polynomial.map_C, RatFunc.algebraMap_C]
      rw [← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply E (RatFunc E) FE]
      rfl
    · simp only [polyEmb, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        Polynomial.coe_mapRingHom, Polynomial.map_X, RatFunc.algebraMap_X]
      rfl
  have := DFunLike.congr_fun hLR p₀
  simpa using this

omit [IsScalarTower E (RatFunc E) FE] in
include hKA hArat hker in
theorem rho_polyEmb (p₀ : A[X]) :
    ρ (polyEmb A O ρ hO hρ hX p₀) =
      algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) (p₀.map (sigma A hKA hArat))) := by
  have hLR : ρ.comp (polyEmb A O ρ hO hρ hX) =
      ((algebraMap (RatFunc K) F).comp (algebraMap K[X] (RatFunc K))).comp
        (Polynomial.mapRingHom (sigma A hKA hArat)) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [polyEmb, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        Polynomial.coe_mapRingHom, Polynomial.map_C, RatFunc.algebraMap_C]
      rw [rho_constEmb A hKA hArat O ρ hO hker hρ, ← RatFunc.algebraMap_eq_C,
        ← IsScalarTower.algebraMap_apply K (RatFunc K) F]
    · simp only [polyEmb, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        Polynomial.coe_mapRingHom, Polynomial.map_X, RatFunc.algebraMap_X]
      have e1 : (⟨_, X_mem O ρ hρ hX⟩ : O) =
          ⟨algebraMap F FE (algebraMap (RatFunc K) F RatFunc.X), algebraMap_mem O ρ hρ _⟩ :=
        Subtype.ext hX
      rw [e1, rho_algebraMap O ρ hρ]
  have := DFunLike.congr_fun hLR p₀
  simpa using this

theorem coeff_C_inv_mul_mem (f : E[X]) (c₀ : E)
    (hmax : ∀ c ∈ f.coeffs, A.valuation c ≤ A.valuation c₀) (n : ℕ) :
    (Polynomial.C c₀⁻¹ * f).coeff n ∈ A := by
  rw [Polynomial.coeff_C_mul]
  by_cases hn : f.coeff n = 0
  · rw [hn, mul_zero]; exact A.zero_mem
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀, ← div_eq_inv_mul]
  exact div_le_one_of_le₀ (hmax _ (Polynomial.coeff_mem_coeffs hn)) zero_le'

include hKA hArat hO hker hρ hX in

theorem exists_rho_eq_algebraMap (m : RatFunc E) (hm : algebraMap (RatFunc E) FE m ∈ O) :
    ∃ l : RatFunc K, ρ ⟨algebraMap (RatFunc E) FE m, hm⟩ = algebraMap (RatFunc K) F l := by
  classical
  have hden : m.denom ≠ 0 := RatFunc.denom_ne_zero m
  let T : Finset E := m.num.coeffs ∪ m.denom.coeffs
  have hTne : T.Nonempty :=
    ⟨m.denom.coeff m.denom.natDegree, Finset.mem_union_right _
      (Polynomial.coeff_mem_coeffs (Polynomial.leadingCoeff_ne_zero.mpr hden))⟩
  obtain ⟨c₀, hc₀T, hmax⟩ := Finset.exists_max_image T (fun c => A.valuation c) hTne
  have hTne0 : ∀ c ∈ T, c ≠ 0 := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc <;>
    · obtain ⟨n, hn, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
      exact Polynomial.mem_support_iff.mp hn
  have hc₀ : c₀ ≠ 0 := hTne0 c₀ hc₀T

  have hp : ∀ n, (Polynomial.C c₀⁻¹ * m.num).coeff n ∈ A := coeff_C_inv_mul_mem A _ c₀
    (fun c hc => hmax c (Finset.mem_union_left _ hc))
  have hq : ∀ n, (Polynomial.C c₀⁻¹ * m.denom).coeff n ∈ A := coeff_C_inv_mul_mem A _ c₀
    (fun c hc => hmax c (Finset.mem_union_right _ hc))
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : A[X], p₀.map (algebraMap A E) = Polynomial.C c₀⁻¹ * m.num := by
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, hp n⟩, rfl⟩
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : A[X], q₀.map (algebraMap A E) = Polynomial.C c₀⁻¹ * m.denom := by
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, hq n⟩, rfl⟩

  have hone : (∃ n, p₀.coeff n = 1) ∨ (∃ n, q₀.coeff n = 1) := by
    rcases Finset.mem_union.mp hc₀T with hc | hc
    · obtain ⟨n, hn, hcn⟩ := Polynomial.mem_coeffs_iff.mp hc
      refine Or.inl ⟨n, ?_⟩
      apply Subtype.ext
      have := congrArg (fun f => Polynomial.coeff f n) hp₀
      simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at this
      rw [show ((p₀.coeff n : A) : E) = algebraMap A E (p₀.coeff n) from rfl, this, ← hcn,
        inv_mul_cancel₀ hc₀]
      rfl
    · obtain ⟨n, hn, hcn⟩ := Polynomial.mem_coeffs_iff.mp hc
      refine Or.inr ⟨n, ?_⟩
      apply Subtype.ext
      have := congrArg (fun f => Polynomial.coeff f n) hq₀
      simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at this
      rw [show ((q₀.coeff n : A) : E) = algebraMap A E (q₀.coeff n) from rfl, this, ← hcn,
        inv_mul_cancel₀ hc₀]
      rfl

  have hred : ∀ r₀ : A[X], (∃ n, r₀.coeff n = 1) → r₀.map (sigma A hKA hArat) ≠ 0 := by
    rintro r₀ ⟨n, hn⟩ h0
    have := congrArg (fun f => Polynomial.coeff f n) h0
    simp only [Polynomial.coeff_map, hn, map_one, Polynomial.coeff_zero] at this
    exact one_ne_zero this
  have hunit : ∀ r₀ : A[X], (∃ n, r₀.coeff n = 1) → IsUnit (polyEmb A O ρ hO hρ hX r₀) := by
    intro r₀ hr₀
    apply isUnit_of_map_ne_zero O ρ hker
    rw [rho_polyEmb A hKA hArat O ρ hO hker hρ hX]
    exact fun h => hred r₀ hr₀ (IsFractionRing.injective K[X] (RatFunc K)
      ((algebraMap (RatFunc K) F).injective (by rw [h, map_zero, map_zero])))

  have hCne : (Polynomial.C c₀⁻¹ : E[X]) ≠ 0 := Polynomial.C_ne_zero.mpr (inv_ne_zero hc₀)
  have hm' : algebraMap E[X] (RatFunc E) m.num = m * algebraMap E[X] (RatFunc E) m.denom :=
    (div_eq_iff ((map_ne_zero_iff _ (IsFractionRing.injective E[X] (RatFunc E))).mpr hden)).mp
      (RatFunc.num_div_denom m)
  have hmq : m * algebraMap E[X] (RatFunc E) (Polynomial.C c₀⁻¹ * m.denom) =
      algebraMap E[X] (RatFunc E) (Polynomial.C c₀⁻¹ * m.num) := by
    rw [map_mul, map_mul, hm']; ring
  have hOid : (⟨algebraMap (RatFunc E) FE m, hm⟩ : O) * polyEmb A O ρ hO hρ hX q₀ =
      polyEmb A O ρ hO hρ hX p₀ := by
    apply Subtype.ext
    show algebraMap (RatFunc E) FE m * (polyEmb A O ρ hO hρ hX q₀ : FE) = _
    rw [coe_polyEmb, coe_polyEmb, hp₀, hq₀, ← map_mul, hmq]
  rcases hone with hone | hone
  ·
    by_cases hq0 : q₀.map (sigma A hKA hArat) = 0
    · exfalso
      have hqmax : polyEmb A O ρ hO hρ hX q₀ ∈ IsLocalRing.maximalIdeal O := by
        rw [← hker, RingHom.mem_ker, rho_polyEmb A hKA hArat O ρ hO hker hρ hX, hq0, map_zero,
          map_zero]
      have hpmax : polyEmb A O ρ hO hρ hX p₀ ∈ IsLocalRing.maximalIdeal O := by
        rw [← hOid]; exact Ideal.mul_mem_left _ _ hqmax
      exact (IsLocalRing.mem_maximalIdeal _).mp hpmax (hunit p₀ hone)
    ·
      obtain ⟨u, hu⟩ := isUnit_of_map_ne_zero O ρ hker (z := polyEmb A O ρ hO hρ hX q₀) (by
        rw [rho_polyEmb A hKA hArat O ρ hO hker hρ hX]
        exact fun h => hq0 (IsFractionRing.injective K[X] (RatFunc K)
          ((algebraMap (RatFunc K) F).injective (by rw [h, map_zero, map_zero]))))
      refine ⟨algebraMap K[X] (RatFunc K) (p₀.map (sigma A hKA hArat)) /
        algebraMap K[X] (RatFunc K) (q₀.map (sigma A hKA hArat)), ?_⟩
      have hval : (⟨algebraMap (RatFunc E) FE m, hm⟩ : O) = polyEmb A O ρ hO hρ hX p₀ * ↑u⁻¹ := by
        rw [← hOid, ← hu, mul_assoc, Units.mul_inv, mul_one]
      have hρu : ρ ↑u⁻¹ = (ρ (polyEmb A O ρ hO hρ hX q₀))⁻¹ := by
        rw [← hu]
        exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
      rw [hval, map_mul, hρu, rho_polyEmb A hKA hArat O ρ hO hker hρ hX,
        rho_polyEmb A hKA hArat O ρ hO hker hρ hX, map_div₀, div_eq_mul_inv]
  · obtain ⟨u, hu⟩ := hunit q₀ hone
    refine ⟨algebraMap K[X] (RatFunc K) (p₀.map (sigma A hKA hArat)) /
      algebraMap K[X] (RatFunc K) (q₀.map (sigma A hKA hArat)), ?_⟩
    have hval : (⟨algebraMap (RatFunc E) FE m, hm⟩ : O) = polyEmb A O ρ hO hρ hX p₀ * ↑u⁻¹ := by
      rw [← hOid, ← hu, mul_assoc, Units.mul_inv, mul_one]
    have hρu : ρ ↑u⁻¹ = (ρ (polyEmb A O ρ hO hρ hX q₀))⁻¹ := by
      rw [← hu]
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    rw [hval, map_mul, hρu, rho_polyEmb A hKA hArat O ρ hO hker hρ hX,
      rho_polyEmb A hKA hArat O ρ hO hker hρ hX, map_div₀, div_eq_mul_inv]

include hKA hArat hO hker hρ hX in

theorem algebraMap_coord_mem {ι : Type*} [Fintype ι] (b : ι → F)
    (hb : LinearIndependent (RatFunc K) b) (c : ι → RatFunc E)
    (hc : (∑ i, c i • algebraMap F FE (b i)) ∈ O) (i : ι) :
    algebraMap (RatFunc E) FE (c i) ∈ O := by
  classical
  by_contra hi
  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j => O.valuation (algebraMap (RatFunc E) FE (c j))) ⟨i, Finset.mem_univ _⟩
  have hi₀ : algebraMap (RatFunc E) FE (c i₀) ∉ O := by
    intro h
    apply hi
    rw [← O.valuation_le_one_iff] at h ⊢
    exact (hmax i (Finset.mem_univ _)).trans h
  have hC₀ : algebraMap (RatFunc E) FE (c i₀) ≠ 0 := fun h => hi₀ (h ▸ O.zero_mem)
  have hc₀ : c i₀ ≠ 0 := fun h => hC₀ (by rw [h, map_zero])

  have hd : ∀ j, algebraMap (RatFunc E) FE (c j / c i₀) ∈ O := by
    intro j
    rw [← O.valuation_le_one_iff, map_div₀, map_div₀]
    exact div_le_one_of_le₀ (hmax j (Finset.mem_univ _)) zero_le'
  choose l hl using fun j => exists_rho_eq_algebraMap A hKA hArat O ρ hO hker hρ hX (c j / c i₀) (hd j)
  have hl₀ : l i₀ = 1 := by
    have h1 : (⟨algebraMap (RatFunc E) FE (c i₀ / c i₀), hd i₀⟩ : O) = 1 :=
      Subtype.ext (by simp [div_self hc₀])
    have := hl i₀
    rw [h1, map_one] at this
    exact (algebraMap (RatFunc K) F).injective (by rw [map_one]; exact this.symm)

  set z : FE := ∑ j, c j • algebraMap F FE (b j) with hz_def
  set z' : O := ∑ j, (⟨algebraMap (RatFunc E) FE (c j / c i₀), hd j⟩ : O) *
    ⟨algebraMap F FE (b j), algebraMap_mem O ρ hρ (b j)⟩ with hz'_def
  have hz' : (z' : FE) = (algebraMap (RatFunc E) FE (c i₀))⁻¹ * z := by
    rw [hz'_def, hz_def, AddSubmonoidClass.coe_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [MulMemClass.coe_mul, map_div₀, Algebra.smul_def]
    rw [div_eq_inv_mul, mul_assoc]
  have hρz' : ρ z' = ∑ j, l j • b j := by
    rw [hz'_def, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hl, rho_algebraMap O ρ hρ, Algebra.smul_def]
  have hρz'_ne : ρ z' ≠ 0 := by
    rw [hρz']
    intro h0
    have := Fintype.linearIndependent_iff.mp hb l h0 i₀
    rw [hl₀] at this
    exact one_ne_zero this
  have hunit : IsUnit z' := isUnit_of_map_ne_zero O ρ hker hρz'_ne
  have hz'0 : (z' : FE) ≠ 0 := fun h => hρz'_ne (by
    have : z' = 0 := Subtype.ext h
    rw [this, map_zero])
  have hinv : (z' : FE)⁻¹ ∈ O := (isUnit_iff_inv_mem O _ hz'0).mp hunit
  apply hi₀
  have hz0 : z ≠ 0 := by
    intro h; apply hz'0; rw [hz', h, mul_zero]
  have : algebraMap (RatFunc E) FE (c i₀) = z * (z' : FE)⁻¹ := by
    rw [hz', mul_inv, inv_inv, mul_left_comm, mul_inv_cancel₀ hz0, mul_one]
  rw [this]
  exact O.mul_mem _ _ hc hinv

include hKA hArat hO hker hρ hX in

theorem residue_norm_eq_norm_residue [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    [FiniteDimensional (RatFunc K) F] [FiniteDimensional (RatFunc E) FE]
    (g : O) :
    ∃ h : algebraMap (RatFunc E) FE (Algebra.norm (RatFunc E) (g : FE)) ∈ O,
      ρ ⟨_, h⟩ = algebraMap (RatFunc K) F (Algebra.norm (RatFunc K) (ρ g)) := by
  classical
  let b := Module.finBasis (RatFunc K) F
  obtain ⟨β, hβ⟩ := exists_basis_algebraMap hfg hfgE hgen hX b

  set μ := Algebra.leftMulMatrix β (g : FE) with hμ_def
  have hsum : ∀ j, ∑ i, μ i j • algebraMap F FE (b i) = (g : FE) * algebraMap F FE (b j) := by
    intro j
    have := β.sum_repr ((g : FE) * β j)
    simp_rw [hμ_def, Algebra.leftMulMatrix_eq_repr_mul, ← hβ]
    exact this
  have hμO : ∀ i j, algebraMap (RatFunc E) FE (μ i j) ∈ O := fun i j =>
    algebraMap_coord_mem A hKA hArat O ρ hO hker hρ hX b b.linearIndependent (fun i => μ i j)
      (by rw [hsum]; exact O.mul_mem _ _ g.2 (algebraMap_mem O ρ hρ _)) i
  choose l hl using fun i j =>
    exists_rho_eq_algebraMap A hKA hArat O ρ hO hker hρ hX (μ i j) (hμO i j)

  have hl' : ∀ i j, l i j = Algebra.leftMulMatrix b (ρ g) i j := by
    intro i j
    have hOid : g * ⟨algebraMap F FE (b j), algebraMap_mem O ρ hρ (b j)⟩ =
        ∑ i, (⟨algebraMap (RatFunc E) FE (μ i j), hμO i j⟩ : O) *
          ⟨algebraMap F FE (b i), algebraMap_mem O ρ hρ (b i)⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, ← hsum j]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MulMemClass.coe_mul, Algebra.smul_def]
    have hF : ρ g * b j = ∑ i, l i j • b i := by
      have := congrArg ρ hOid
      rw [map_mul, rho_algebraMap O ρ hρ, map_sum] at this
      rw [this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hl, rho_algebraMap O ρ hρ, Algebra.smul_def]
    have hrepr := congr_fun (b.repr_sum_self (fun i => l i j)) i
    rw [Algebra.leftMulMatrix_eq_repr_mul, hF]
    exact hrepr.symm

  let O' : ValuationSubring (RatFunc E) := O.comap (algebraMap (RatFunc E) FE)
  let ρ' : O' →+* F := ρ.comp ((algebraMap (RatFunc E) FE).restrict O'.toSubring O.toSubring
    fun z hz => (ValuationSubring.mem_comap.mp hz))
  let Mx : Matrix _ _ O' := Matrix.of fun i j => ⟨μ i j, ValuationSubring.mem_comap.mpr (hμO i j)⟩
  have h1 : O'.subtype.mapMatrix Mx = μ := by
    ext i j; rfl
  have h2 : ρ'.mapMatrix Mx = (algebraMap (RatFunc K) F).mapMatrix (Algebra.leftMulMatrix b (ρ g)) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [← hl' i j, ← hl i j]
    rfl
  have hdet : ((Mx.det : O') : RatFunc E) = Algebra.norm (RatFunc E) (g : FE) := by
    rw [Algebra.norm_eq_matrix_det β, show ((Mx.det : O') : RatFunc E) = O'.subtype Mx.det from rfl,
      RingHom.map_det, h1]
  have hρ'det : ρ' Mx.det = algebraMap (RatFunc K) F (Algebra.norm (RatFunc K) (ρ g)) := by
    rw [RingHom.map_det, h2, ← RingHom.map_det, Algebra.norm_eq_matrix_det b]
  have hmem : algebraMap (RatFunc E) FE (Mx.det : RatFunc E) ∈ O :=
    ValuationSubring.mem_comap.mp Mx.det.2
  refine ⟨hdet ▸ hmem, ?_⟩
  have e : (⟨algebraMap (RatFunc E) FE (Algebra.norm (RatFunc E) (g : FE)), hdet ▸ hmem⟩ : O) =
      ⟨algebraMap (RatFunc E) FE (Mx.det : RatFunc E), hmem⟩ :=
    Subtype.ext (show algebraMap (RatFunc E) FE (Algebra.norm (RatFunc E) (g : FE)) =
      algebraMap (RatFunc E) FE (Mx.det : RatFunc E) by rw [hdet])
  rw [e]
  exact hρ'det

end Reduction

end DeuringNormResidue
p2m_reactivate "P2MW.S_AlgebraicCurve_residue_norm_eq_norm_residue_of_retraction.DeuringNormResidue"

set_option linter.unusedVariables false in
open DeuringNormResidue in

theorem solution
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [Algebra (RatFunc E) FE] [IsScalarTower E (RatFunc E) FE] [FiniteDimensional (RatFunc E) FE]
    (hX : algebraMap (RatFunc E) FE RatFunc.X = algebraMap F FE (algebraMap (RatFunc K) F RatFunc.X))
    (A : ValuationSubring E)
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (O : ValuationSubring FE) (ρ : O →+* F)
    (hO : ∀ c : E, algebraMap E FE c ∈ O ↔ c ∈ A)
    (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
    (hρ : ∀ f : F, ∃ h : algebraMap F FE f ∈ O, ρ ⟨algebraMap F FE f, h⟩ = f)
    (g : O) (hg : ρ g ≠ 0) :
    ∃ h : algebraMap (RatFunc E) FE (Algebra.norm (RatFunc E) (g : FE)) ∈ O,
      ρ ⟨_, h⟩ = algebraMap (RatFunc K) F (Algebra.norm (RatFunc K) (ρ g)) := by
  clear hg
  exact residue_norm_eq_norm_residue A hKA hArat O ρ hO hker hρ hX hfg hfgE hgen g

end S_AlgebraicCurve_residue_norm_eq_norm_residue_of_retraction
end P2MW
export P2MW.S_AlgebraicCurve_residue_norm_eq_norm_residue_of_retraction (solution)
