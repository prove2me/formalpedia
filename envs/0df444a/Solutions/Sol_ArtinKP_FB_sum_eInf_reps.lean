-- Prove2me | solution 1 for ArtinKP.FB.sum_eInf_reps
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:06:34.567221+00:00
-- url     : https://prove2.me/submissions/d47727a5-7f13-4ea8-b0fc-323a027eef50

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ArtinKPB017

section
-- module Solutions.Artin.KP.B7_Sum
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # B7_Sum: sums over residues modulo a principal ideal

For a commutative ring `R`, `c : R` and `f : R → ℂ`, `rsum c f` is the sum of `f` over chosen
representatives of `R ⧸ (c)` (the same `Function.surjInv` choice as `ArtinPrimitiveRoots.quotLift`).
For `f` periodic modulo `c` (`Per c f`) it does not depend on the choice, and we prove the
reindexing lemmas used for Gauss sums: translation, multiplication by a unit modulo `c`, the
Chinese remainder theorem, and the fibre formula for a function periodic modulo a divisor.
-/

namespace ArtinKP.B7

variable {R : Type*} [CommRing R]

lemma mk_rep (c : R) (x : R ⧸ Ideal.span {c}) :
    Ideal.Quotient.mk (Ideal.span {c}) (rep c x) = x :=
  Function.surjInv_eq Ideal.Quotient.mk_surjective x

lemma mk_eq_mk_iff {c a b : R} :
    Ideal.Quotient.mk (Ideal.span {c}) a = Ideal.Quotient.mk (Ideal.span {c}) b ↔ c ∣ a - b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

lemma dvd_rep_mk_sub (c a : R) : c ∣ rep c (Ideal.Quotient.mk (Ideal.span {c}) a) - a :=
  mk_eq_mk_iff.1 (mk_rep c _)

lemma Per.rep_mk {c : R} {f : R → ℂ} (hf : Per c f) (a : R) :
    f (rep c (Ideal.Quotient.mk (Ideal.span {c}) a)) = f a :=
  hf _ _ (dvd_rep_mk_sub c a)

lemma Per.of_dvd {c c' : R} {f : R → ℂ} (hf : Per c f) (h : c ∣ c') : Per c' f :=
  fun a b hab => hf a b (h.trans hab)

lemma rsum_congr {c : R} {f g : R → ℂ} (h : ∀ d, f d = g d) : rsum c f = rsum c g := by
  unfold rsum; exact finsum_congr fun x => h _

lemma rsum_mul_const (c : R) (f : R → ℂ) (z : ℂ) : rsum c (fun d => f d * z) = rsum c f * z := by
  unfold rsum; rw [finsum_mul]

lemma rsum_one (c : R) [Finite (R ⧸ Ideal.span {c})] :
    rsum c (fun _ => 1) = (Nat.card (R ⧸ Ideal.span {c}) : ℂ) := by
  unfold rsum
  have := Fintype.ofFinite (R ⧸ Ideal.span {c})
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  simp

/-- Reindexing by a map of `R` that induces a permutation of the residues. -/
lemma rsum_comp {c : R} {f : R → ℂ} (hf : Per c f) (σ : R → R)
    (τ : (R ⧸ Ideal.span {c}) ≃ (R ⧸ Ideal.span {c}))
    (h : ∀ a, Ideal.Quotient.mk (Ideal.span {c}) (σ a) = τ (Ideal.Quotient.mk (Ideal.span {c}) a)) :
    rsum c (fun d => f (σ d)) = rsum c f := by
  unfold rsum
  refine Eq.trans ?_ (finsum_comp_equiv τ)
  refine finsum_congr fun x => hf _ _ ?_
  rw [← mk_eq_mk_iff, h, mk_rep, mk_rep]

/-- Translation invariance. -/
lemma rsum_add_right {c : R} {f : R → ℂ} (hf : Per c f) (a : R) :
    rsum c (fun d => f (d + a)) = rsum c f :=
  rsum_comp hf (fun d => d + a) (Equiv.addRight (Ideal.Quotient.mk (Ideal.span {c}) a))
    (fun d => by simp)

/-- **Fibre formula**: a function periodic modulo `c` summed modulo `c * c'`. -/
lemma rsum_mul_of_per [IsDomain R] {c c' : R} [Finite (R ⧸ Ideal.span {c})]
    [Finite (R ⧸ Ideal.span {c'})] (hc : c ≠ 0) {f : R → ℂ} (hf : Per c f) :
    rsum (c * c') f = (Nat.card (R ⧸ Ideal.span {c'}) : ℂ) * rsum c f := by
  set Φ : (R ⧸ Ideal.span {c}) × (R ⧸ Ideal.span {c'}) → R ⧸ Ideal.span {c * c'} :=
    fun p => Ideal.Quotient.mk _ (rep c p.1 + c * rep c' p.2) with hΦ
  have hbij : Function.Bijective Φ := by
    constructor
    · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ hxy
      simp only [hΦ, mk_eq_mk_iff] at hxy
      have e1 : c ∣ rep c x₁ - rep c x₂ := by
        have := (dvd_mul_right c c').trans hxy
        have h2 : rep c x₁ - rep c x₂ =
            (rep c x₁ + c * rep c' y₁ - (rep c x₂ + c * rep c' y₂)) -
              c * (rep c' y₁ - rep c' y₂) := by ring
        rw [h2]; exact dvd_sub this (dvd_mul_right _ _)
      rw [← mk_eq_mk_iff, mk_rep, mk_rep] at e1
      subst e1
      have e2 : c * c' ∣ c * (rep c' y₁ - rep c' y₂) := by
        have h2 : c * (rep c' y₁ - rep c' y₂) =
            (rep c x₁ + c * rep c' y₁ - (rep c x₁ + c * rep c' y₂)) := by ring
        rw [h2]; exact hxy
      have e2' := (mul_dvd_mul_iff_left hc).1 e2
      rw [← mk_eq_mk_iff, mk_rep, mk_rep] at e2'
      rw [e2']
    · intro z
      obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨s, hs⟩ := dvd_rep_mk_sub c d
      obtain ⟨t, ht⟩ := dvd_rep_mk_sub c' (-s)
      refine ⟨(Ideal.Quotient.mk _ d, Ideal.Quotient.mk _ (-s)), ?_⟩
      simp only [hΦ, mk_eq_mk_iff]
      refine ⟨t, ?_⟩
      linear_combination hs + c * ht
  unfold rsum
  rw [← finsum_eq_of_bijective Φ hbij (g := fun z => f (rep (c * c') z))
    (f := fun p => f (rep c p.1)) (fun p => ?_)]
  · rw [finsum_curry _ (Set.toFinite _)]
    have := Fintype.ofFinite (R ⧸ Ideal.span {c'})
    have : ∀ a : R ⧸ Ideal.span {c}, (∑ᶠ _b : R ⧸ Ideal.span {c'}, f (rep c a)) =
        (Nat.card (R ⧸ Ideal.span {c'}) : ℂ) * f (rep c a) := by
      intro a
      rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
      simp
    simp only [this]
    rw [mul_finsum]
  · simp only [hΦ]
    rw [(hf.of_dvd (dvd_mul_right c c')).rep_mk]
    exact hf _ _ ⟨-rep c' p.2, by ring⟩

/-- Summing a function periodic modulo `c` over the residues modulo `c ^ (k+1)`. -/
lemma rsum_pow_of_per [IsDomain R] {c : R} [Finite (R ⧸ Ideal.span {c})] (hc : c ≠ 0)
    (hfin : ∀ k : ℕ, Finite (R ⧸ Ideal.span {c ^ k})) {f : R → ℂ} (hf : Per c f) (k : ℕ) :
    rsum (c ^ (k + 1)) f = (Nat.card (R ⧸ Ideal.span {c}) : ℂ) ^ k * rsum c f := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := hfin (k + 1)
    rw [pow_succ c (k + 1), rsum_mul_of_per (pow_ne_zero _ hc) (hf.of_dvd (dvd_pow_self c (by omega))),
      ih, pow_succ]
    ring

end ArtinKP.B7
end

section
-- module Solutions.Artin.KP.B7_Gauss
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # B7_Gauss: the cubic Gauss sum `g(ν, c)` over a ring of `S`-integers, abstractly

`R` is a domain with fraction-type field `K` (in the application `R = SInt 𝔪`, `K = F`).

* `CubicSymbol R` is the interface to WP-A: the cubic exterior symbol `(d/c)`, with exactly the
  properties used here.
* `AddData R K` is an additive character of `K` trivial on `R` (in the application `sAddChar 𝔪`,
  see `B7_Link`).
* `gauss S A ν c = ∑_{d mod c} (d/c)⁻¹ e(ν d / c)` (terms with `(d, c) ≠ 1` vanish since
  `(d/c) = 0` there and `0⁻¹ = 0`).

Main results (MATH.md (B7)): `gauss_mul` (twisted multiplicativity), `gauss_mul_left`
(`g(μν, c) = (μ/c) g(ν, c)`), the prime-power table `gauss_prime_pow_le`,
`gauss_prime_pow_succ`, `gauss_prime_pow_eq_zero`, and the constant-term sums `csum_eq_phi`,
`csum_eq_zero`, `csum_of_cube`, `csum_eq_zero_of_val`, `csum_prime_pow`, `phi_prime_pow`.
-/

set_option linter.unusedSectionVars false

namespace ArtinKP.B7

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]

/-! ### The additive character on fractions -/

namespace AddData

variable (A : AddData R K)

omit A in
lemma map_ne_zero (A : AddData R K) {c : R} (hc : c ≠ 0) : algebraMap R K c ≠ 0 := fun h =>
  hc (A.inj (h.trans (map_zero _).symm))

lemma ψ_add (a b c : R) : A.ψ (a + b) c = A.ψ a c * A.ψ b c := by
  unfold ψ; rw [map_add, add_div, A.e_add]

lemma ψ_mul_self {c : R} (hc : c ≠ 0) (r : R) : A.ψ (c * r) c = 1 := by
  unfold ψ
  rw [map_mul, mul_div_cancel_left₀ _ (A.map_ne_zero hc), A.e_int]

lemma ψ_per {c : R} (hc : c ≠ 0) {a b : R} (h : c ∣ a - b) : A.ψ a c = A.ψ b c := by
  obtain ⟨r, hr⟩ := h
  have : a = b + c * r := by rw [← hr]; ring
  rw [this, ψ_add, ψ_mul_self A hc, mul_one]

lemma ψ_mul_right_cancel (a c : R) {c' : R} (hc' : c' ≠ 0) : A.ψ (a * c') (c * c') = A.ψ a c := by
  unfold ψ
  rw [map_mul, map_mul, mul_div_mul_right _ _ (A.map_ne_zero hc')]

end AddData

/-! ### Elementary facts about the symbol -/

/-! ### The Gauss sum -/

/-! ### Constant-term sums -/

/-! ### Prime powers -/

end ArtinKP.B7
end

section
-- module Solutions.Artin.T12.C3I_Res
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # C3I_Res: the residue rings `R / P^j R` at a prime `P ∉ S`

For a height-one prime `v` of `𝓞 F` outside `S = placesOf 𝔪`:
* `mem_map_pow_iff`: `r ∈ v^j R ↔ v(r) ≤ exp(-j)` for `r ∈ R`;
* `quotEquiv`: `𝓞/v^j ≃+* R/v^j R`; `natCard_quot`: `#(R/v^j R) = N(v)^j`;
* `isMaximal_map`: `v R` is maximal;
* `finsum_quot_fibre`: summing a function that only depends on the class mod `v^i R`
  over `R/v^j R` (`i ≤ j`) gives `N(v)^(j-i)` times the sum over `R/v^i R`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section val

variable {v : HeightOneSpectrum (𝓞 F)}

/-- Discreteness: a valuation strictly above `exp(-(j+1))` is at least `exp(-j)`. -/
lemma exp_le_of_lt {γ : ℤᵐ⁰} {j : ℤ} (h : exp (j - 1) < γ) : exp j ≤ γ := by
  have hγ : γ ≠ 0 := ne_zero_of_lt h
  rw [← exp_log hγ] at h ⊢
  rw [exp_lt_exp] at h
  rw [exp_le_exp]
  omega

lemma exp_le_val_of_not_mem (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪)
    (h : r ∉ (v.asIdeal ^ (j + 1)).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    exp (-(j : ℤ)) ≤ v.valuation F (r : F) := by
  rw [mem_map_pow_iff hv, not_le] at h
  apply exp_le_of_lt
  convert h using 2
  push_cast; ring

lemma isExterior_mul {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    IsExterior 𝔪 (I * J) := by
  refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
  have h1 : IsCoprime I 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hI.2
  have h2 : IsCoprime J 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hJ.2
  exact Ideal.isCoprime_iff_sup_eq.mp (h1.mul_left h2)

lemma isExterior_pow {I : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (n : ℕ) :
    IsExterior 𝔪 (I ^ n) := by
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact ⟨top_ne_bot, top_sup_eq _⟩
  | succ k ih => rw [pow_succ]; exact isExterior_mul ih hI

/-- A uniformizer in `𝓞`. -/
lemma exists_uniformizer : ∃ p : 𝓞 F, v.valuation F (algebraMap (𝓞 F) F p) = exp (-1 : ℤ) := by
  obtain ⟨p, hp⟩ := v.intValuation_exists_uniformizer
  exact ⟨p, by rw [val_alg, hp]⟩

end val

end C3I

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3I_Add
attribute [-instance] _root_.ArtinKP.B1.PairClass.instNonempty _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # C3I_Add: the additive character `e`

* `HasWit 𝔪 x`: `x` has a witness `y` in the definition of `sAddChar` (`x - y ∈ R`, `y` integral
  at `S`). `hasWit_of_mul_mem`: true when `x I ⊆ R` for an ideal `I` coprime to `𝔪`; in particular
  `hasWit_div_gen`: `a / gen 𝔞` for `a ∈ R`, `𝔞` exterior.
* `sAddChar_eq_of_wit`: `e(x) = exp(-2πi Tr y)` for every witness; `sAddChar_add`: `e` is additive
  on elements with witnesses.
* `exists_trace_not_int`: for `P ∤ 𝔇`, some `z ∈ P⁻¹` has `Tr z ∉ ℤ`; `sAddChar_ne_one_of_dual`.
* `exists_sAddChar_ne_one`: primitivity at every level: for `x ∈ R ∖ P^j R` some `r ∈ R` has
  `e(x r / gen(P^j)) ≠ 1`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

variable {ι : F →+* ℂ}

/-! ### The inverse different -/

/-- For `P ∤ 𝔇`, some `z ∈ P⁻¹` has non-integral trace. -/
lemma exists_trace_not_int (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥)
    (hD : ¬ differentIdeal ℤ (𝓞 F) ≤ P) :
    ∃ z : F, (∀ p ∈ P, ∃ a : 𝓞 F, z * algebraMap (𝓞 F) F p = algebraMap (𝓞 F) F a) ∧
      ∀ n : ℤ, Algebra.trace ℚ F z ≠ n := by
  rw [differentialIdeal_le_iff (K := ℚ) (L := F) hP0, Submodule.map_le_iff_le_comap] at hD
  rw [SetLike.not_le_iff_exists] at hD
  obtain ⟨z, hz, hz'⟩ := hD
  have hP' : (P : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
    simpa using hP0
  have hz2 : z ∈ ((P : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)⁻¹) := hz
  rw [FractionalIdeal.mem_inv_iff hP'] at hz2
  refine ⟨z, fun p hp => ?_, fun n hn => hz' ?_⟩
  · have := hz2 (algebraMap (𝓞 F) F p) ((FractionalIdeal.mem_coeIdeal _).2 ⟨p, hp, rfl⟩)
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 this
    exact ⟨a, ha.symm⟩
  · simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_one]
    exact ⟨n, by rw [hn]; simp⟩

/-- For `P` exterior and `z ∈ P⁻¹` with non-integral trace, `e(z) ≠ 1`. -/
lemma sAddChar_ne_one_of_dual (P : Ideal (𝓞 F)) (hPS : P ⊔ 𝔪 = ⊤) (z : F)
    (hz : ∀ p ∈ P, ∃ a : 𝓞 F, z * algebraMap (𝓞 F) F p = algebraMap (𝓞 F) F a)
    (htr : ∀ n : ℤ, Algebra.trace ℚ F z ≠ n) : sAddChar 𝔪 z ≠ 1 := by
  have hw : ∀ v ∈ placesOf 𝔪, v.valuation F z ≤ 1 := by
    intro v hv
    have hvm : 𝔪 ≤ v.asIdeal := hv
    have hPv : ¬ P ≤ v.asIdeal := by
      intro h
      apply v.isPrime.ne_top
      rw [eq_top_iff, ← hPS]
      exact sup_le h hvm
    obtain ⟨p, hp, hpv⟩ := SetLike.not_le_iff_exists.mp hPv
    obtain ⟨a, ha⟩ := hz p hp
    have h1 : v.valuation F (algebraMap (𝓞 F) F p) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hpv
    have := v.valuation_le_one (K := F) a
    change v.valuation F (algebraMap (𝓞 F) F a) ≤ 1 at this
    rw [← ha, map_mul, h1, mul_one] at this
    exact this
  rw [sAddChar_eq_of_wit (y := z) (by simp) hw]
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  apply htr (-n)
  have h2 : ((Algebra.trace ℚ F z : ℚ) : ℂ) = ((-n : ℤ) : ℂ) := by
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ hpi
    push_cast
    linear_combination -hn
  exact_mod_cast h2

/-! ### Primitivity at every level -/

section prim

variable {v : HeightOneSpectrum (𝓞 F)}

/-- `z (v R) ⊆ R` for `z ∈ v⁻¹`. -/
lemma mul_mem_of_mem_map (z : F)
    (hz : ∀ p ∈ v.asIdeal, ∃ a : 𝓞 F, z * algebraMap (𝓞 F) F p = algebraMap (𝓞 F) F a)
    {y : SInt 𝔪} (hy : y ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    z * (y : F) ∈ (placesOf 𝔪).integer F := by
  rw [Ideal.map] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hz p hp
    rw [coe_alg, ha]
    exact (algebraMap (𝓞 F) (SInt 𝔪) a).2
  | zero => simp
  | add x y _ _ hx hy => rw [Subalgebra.coe_add, mul_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [smul_eq_mul, Subalgebra.coe_mul, mul_left_comm]
    exact mul_mem a.2 hx

/-- Primitivity of `x ↦ e(x / gen(P^j))` on `R / P^j R`: for `x ∉ P^j R` there is `r ∈ R` with
`e(x r / gen(P^j)) ≠ 1`, when `P ∤ 𝔇`. -/
lemma exists_sAddChar_ne_one (g : AllowedGen ι 𝔪) (hv : v ∉ placesOf 𝔪)
    (hPS : v.asIdeal ⊔ 𝔪 = ⊤) (hD : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) {j : ℕ} (hj : 1 ≤ j)
    (x : SInt 𝔪) (hx : x ∉ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ∃ r : SInt 𝔪, sAddChar 𝔪 ((x : F) * (r : F) / (g.gen (v.asIdeal ^ j) : F)) ≠ 1 := by
  obtain ⟨z, hz, htr⟩ := exists_trace_not_int v.asIdeal v.ne_bot hD
  have hez := sAddChar_ne_one_of_dual v.asIdeal hPS z hz htr
  have hext : IsExterior 𝔪 (v.asIdeal ^ j) :=
    isExterior_pow ⟨v.ne_bot, hPS⟩ j
  set B := g.gen (v.asIdeal ^ j)
  have hB0 : (B : F) ≠ 0 := C3B.gen_ne_zero g _ hext
  have hBmem : B ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← g.span_gen _ hext]; exact Ideal.mem_span_singleton_self _
  have hB1 : B ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    have : (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ≤
        v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
      Ideal.map_mono (by simpa using Ideal.pow_le_pow_right (I := v.asIdeal) hj)
    exact this hBmem
  -- `w = z B ∈ R`
  have hwR : z * (B : F) ∈ (placesOf 𝔪).integer F := mul_mem_of_mem_map z hz hB1
  set w : SInt 𝔪 := ⟨z * (B : F), hwR⟩
  -- valuations
  have hvz : v.valuation F z ≤ exp (1 : ℤ) := by
    obtain ⟨p, hp⟩ := exists_uniformizer (v := v)
    have hpm : p ∈ v.asIdeal := by
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), hp]
      exact exp_lt_exp.2 (by norm_num) |>.trans_eq exp_zero
    obtain ⟨a, ha⟩ := hz p hpm
    have h1 := v.valuation_le_one (K := F) a
    change v.valuation F (algebraMap (𝓞 F) F a) ≤ 1 at h1
    rw [← ha, map_mul, hp] at h1
    have : v.valuation F z * exp (-1 : ℤ) * exp 1 ≤ 1 * exp 1 := mul_le_mul_left h1 _
    rwa [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one, one_mul] at this
  have hvB := val_le_of_mem hv j hBmem
  have hvw : v.valuation F (w : F) ≤ exp (1 - (j : ℤ)) := by
    change v.valuation F (z * (B : F)) ≤ _
    rw [map_mul, show (1 - (j : ℤ)) = 1 + (-(j : ℤ)) by ring, exp_add]
    exact mul_le_mul' hvz hvB
  have hvx : exp (1 - (j : ℤ)) ≤ v.valuation F (x : F) := by
    have := exp_le_val_of_not_mem hv (j - 1) x (by rwa [Nat.sub_add_cancel hj])
    convert this using 2
    push_cast [Nat.cast_sub hj]; ring
  have hx0 : (x : F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvx
    exact exp_ne_zero (le_antisymm hvx bot_le)
  have hvx0 : v.valuation F (x : F) ≠ 0 := by
    rw [Ne, map_eq_zero]; exact hx0
  -- `f = w / x` is `v`-integral
  have hvf : v.valuation F ((w : F) / (x : F)) ≤ 1 := by
    rw [map_div₀, div_le_one₀ (pos_iff_ne_zero.2 hvx0)]
    exact hvw.trans hvx
  obtain ⟨a, ha⟩ := exists_val_sub_le (v := v) j _ hvf
  -- `w - x a ∈ P^j R`
  set δ : SInt 𝔪 := w - x * algebraMap (𝓞 F) (SInt 𝔪) a
  have hδ : δ ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    apply mem_of_val_le hv j
    have : (δ : F) = (x : F) * ((w : F) / (x : F) - algebraMap (𝓞 F) F a) := by
      simp only [δ, Subalgebra.coe_sub, Subalgebra.coe_mul, coe_alg]
      field_simp
    rw [this, map_mul]
    calc v.valuation F (x : F) * v.valuation F ((w : F) / (x : F) - algebraMap (𝓞 F) F a)
        ≤ 1 * exp (-(j : ℤ)) := mul_le_mul' (val_le_one hv x) ha
      _ = _ := one_mul _
  refine ⟨algebraMap (𝓞 F) (SInt 𝔪) a, fun h1 => hez ?_⟩
  have hzeq : z = (x : F) * ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) / (B : F) +
      (δ : F) / (B : F) := by
    simp only [δ, Subalgebra.coe_sub, Subalgebra.coe_mul]
    change z = _ + (z * (B : F) - _) / (B : F)
    field_simp
    ring
  rw [hzeq, C3B.sAddChar_add_mem _ _ (C3B.div_gen_mem g _ hext δ hδ), h1]

end prim

end C3I

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3I_Gauss
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # C3I_Gauss: the additive character, Gauss sums and Davenport–Hasse on `L = R / P R`

* `psi g h : AddChar L ℂ`, `psi_mk : psi (mk x) = e(x / gen P)`, `psi_isPrimitive`.
* `card_sqrt`: `#{u | u² = w} = 1 + χ³(w)`; `jacobi_dh`: `χ(4) J(χ, χ) = J(χ³, χ)`.
* Gauss sums `g_j = gaussSum (χ^j) ψ`: `gs_mul_gs_inv`, `gs_three_sq`, `star_gs`, `dh`:
  `χ(4) g₁ g₃ = g₂²`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false


open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

lemma quotLift_mk_sub {I : Ideal (SInt 𝔪)} (x : SInt 𝔪) :
    quotLift (Ideal.Quotient.mk I x) - x ∈ I := by
  rw [← Ideal.Quotient.eq]; exact Function.surjInv_eq Ideal.Quotient.mk_surjective _

lemma psi_apply (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) (y) :
    psi g h y = sAddChar 𝔪 ((quotLift y : F) / (g.gen v.asIdeal : F)) := rfl

lemma psi_mk (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) (x : SInt 𝔪) :
    psi g h (Ideal.Quotient.mk _ x) = sAddChar 𝔪 ((x : F) / (g.gen v.asIdeal : F)) :=
  sAddChar_div_congr g _ h.ext (quotLift_mk_sub x)

lemma psi_isPrimitive (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) : (psi g h).IsPrimitive := by
  intro a ha hone
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hx : x ∉ (v.asIdeal ^ 1).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [pow_one]; rwa [Ne, Ideal.Quotient.eq_zero_iff_mem] at ha
  obtain ⟨r, hr⟩ := exists_sAddChar_ne_one g h.notS h.cop h.diff le_rfl x hx
  apply hr
  have := congrArg (fun φ => φ (Ideal.Quotient.mk _ r)) hone
  simp only [AddChar.mulShift_apply, AddChar.one_apply] at this
  rw [← map_mul, psi_mk, Subalgebra.coe_mul] at this
  rw [pow_one]
  exact this

/-! ### Characters on the finite field `L` -/

end C3I

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.L2B_Quot
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# L2B_Quot: exterior ideals of `𝓞 F` and of `R` (copied from L2A_FSQuot, prover A, to decouple)

* `exists_pow_mul_mem`: every `r ∈ R` has `𝔪^N r ⊆ 𝓞`.
* `mem_of_map_mem`: `I R ∩ 𝓞 = I` for `I + 𝔪 = 1`.
* `exists_sub_mem_map`: `𝓞 → R / I R` is onto for `I + 𝔪 = 1`; `finite_quot_map`,

-/

open NumberField IsDedekindDomain WithZero

namespace ArtinPrimitiveRoots.L2B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

lemma quotHom_surjective (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤) :
    Function.Surjective (C3I.quotHom 𝔪 I) := by
  intro y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨c, hc⟩ := exists_sub_mem_map I hI r
  exact ⟨Ideal.Quotient.mk _ c, by rw [C3I.quotHom_mk]; exact (Ideal.Quotient.eq.mpr hc).symm⟩

lemma finite_quot_map (I : Ideal (𝓞 F)) (hI0 : I ≠ ⊥) (hI : I ⊔ 𝔪 = ⊤) :
    Finite (SInt 𝔪 ⧸ I.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have : Finite (𝓞 F ⧸ I) := Ring.HasFiniteQuotients.finiteQuotient hI0
  exact Finite.of_surjective _ (quotHom_surjective I hI)

end ArtinPrimitiveRoots.L2B
end

section
-- module Solutions.Artin.KP.B7_Link
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # B7_Link: the Gauss sums over `R = SInt 𝔪` and the normalization of the frozen statement

* `sAdd 𝔪 h𝔪 : AddData (SInt 𝔪) F` is `sAddChar 𝔪` (additive on all of `F`: `sAddChar_add_all`;
  trivial on `R`), so `gauss S (sAdd 𝔪 h𝔪) ν c = ∑_{d mod c} (d/c)⁻¹ sAddChar 𝔪 (ν d / c)`
  (`gauss_sAdd`).
* `finite_quot_span`: `R ⧸ (c)` is finite for `c ≠ 0`.
* At a good exterior prime `P` (`C3I.Good 𝔪 v`, automatic for `SmallPrimesDvd N₀ 𝔪`,
  `N₀ ≥ C3I.cutN F`) with `π = g.gen P` and a symbol with `(d/π) = χ_P(d)²`:
  `gaussP_one_eq_tau : g₁(π) = tau P 2 = conj (√q γ₂(P))`,
  `gaussP_two_eq_tau : g₂(π) = tau P 4 = √q γ₂(P)`, `γ₂(P) = gaussPhase g 2 P`,
  `gaussP_one_mul_two : g₁ g₂ = N P`, and the complete table `gauss_gen_table` in the form of
  `B7_System.tab` with `G = (ν₀/π) tau P 2`, `G' = (ν₀/π)² tau P 4`, `G G' = N P`, `conj G = G'`.
* `theta_ratio`: the solution of the formal system at `x₀ = q^{-4/3}` gives
  `q^{-1/3} C₁ = (ν₀/π)² · Wv P 1 · C₀` with `Wv P 1 = q^{-1/2} gaussPhase g 2 P` exactly as in the
  frozen statement (and `Wv P 0 = 1`, `Wv P 2 = 0 ↔ Ψ₂ = 0`).
-/

open NumberField IsDedekindDomain

namespace ArtinKP.B7

open ArtinPrimitiveRoots

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The additive character -/

/-- `R ⧸ (c)` is finite for `c ≠ 0`. -/
theorem finite_quot_span (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) :
    Finite (SInt 𝔪 ⧸ Ideal.span {c}) := by
  have hcF : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (c : F)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : algebraMap (𝓞 F) F b ≠ 0 := by
    intro h; exact hb0 (by simpa using h)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact hcF hab.symm
  have hI : Ideal.span ({a} : Set (𝓞 F)) ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨𝔄, hE, hmap⟩ := exists_exterior_map_eq 𝔪 h𝔪 _ hI
  have hle : 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ Ideal.span {c} := by
    rw [← hmap, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_span_singleton]
    refine ⟨algebraMap (𝓞 F) (SInt 𝔪) b, Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, ← hab]
    show algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F b
    field_simp
  have := L2B.finite_quot_map (𝔪 := 𝔪) 𝔄 hE.1 hE.2
  exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)

/-! ### Transport of residue sums to the quotient by an equal ideal -/

/-! ### A good exterior prime -/

section prime

variable {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}
variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (g : AllowedGen ι 𝔪)
  (h𝔪 : 𝔪 ≠ ⊥) (S : CubicSymbol (SInt 𝔪))
  (hS : ∀ d : SInt 𝔪, S.sym d (g.gen v.asIdeal) = sexticResidueSymbol ι 𝔪 v.asIdeal d ^ 2)

include h in
lemma card_quot_gen :
    Nat.card (SInt 𝔪 ⧸ Ideal.span {g.gen v.asIdeal}) = Ideal.absNorm v.asIdeal :=
  (congrArg (fun I : Ideal (SInt 𝔪) => Nat.card (SInt 𝔪 ⧸ I)) (span_gen h g)).trans (C3I.natCard_L h)

include h h𝔪 in
lemma finite_quot_gen_pow (k : ℕ) : Finite (SInt 𝔪 ⧸ Ideal.span {g.gen v.asIdeal ^ k}) :=
  finite_quot_span h𝔪 (pow_ne_zero _ (gen_ne_zero h g))

include h in
/-- Primitivity: `e(a₀/π) ≠ 1` for some `a₀ ∈ R`. -/
lemma exists_ψ_ne_one : ∃ a₀ : SInt 𝔪, (sAdd 𝔪 h𝔪).ψ a₀ (g.gen v.asIdeal) ≠ 1 := by
  have := C3I.isMaximal_v h
  let _ := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hp := C3I.psi_isPrimitive g h
  by_contra hcon
  push Not at hcon
  refine hp (a := 1) one_ne_zero ?_
  ext y
  rw [AddChar.mulShift_apply, one_mul, AddChar.one_apply, C3I.psi_apply]
  exact hcon (quotLift y)

end prime

end ArtinKP.B7
end

section
-- module Solutions.Artin.KP.B_FourArch
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply
/-!
# WP-B, part 2: the characters and the archimedean integral

* `eInf x = ∏_w archChar (-x_w)` on `ℂ^r`; `eInf (emb a) = exp(-2πi Tr a)` for `a ∈ F`.
* `psiS h𝔪 : SfChar 𝔪`, `ψ_{S_f}(x) = sAddChar 𝔪 x · conj (eInf (emb x))`; it is trivial on
  `𝔩_0`, and `eInf (emb x) = sAddChar 𝔪 x · conj ψ_{S_f}(x)` (`eInf_emb_eq`).
* `kerA v x = ∏_w v_w / (|x_w|² + v_w²)`; `I_{(c,d)}(x, v) = N_∞(c)⁻¹ · kerA v (x + d/c)`.
* `Winf s ν v = ∏_w jacquet s (-σ_w ν) v_w`; the integral of a shifted kernel against
  `conj eInf(ν x)` (`integral_shift_kernel`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.K

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The archimedean character -/

/-! ### The `S_f`-character -/

theorem psiS_apply [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) (x : F) :
    psiS h𝔪 x = sAddChar 𝔪 x * conj (eInf (emb x)) := rfl

/-- `e_∞(x) = sAddChar(x) · conj ψ_{S_f}(x)` for `x ∈ F` (MATH2 §0.2). -/
theorem eInf_emb_eq [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) (x : F) :
    eInf (emb x) = sAddChar 𝔪 x * conj (psiS h𝔪 x) := by
  have h1 : sAddChar 𝔪 x * conj (sAddChar 𝔪 x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_sAddChar h𝔪]
    simp
  rw [psiS_apply, map_mul, Complex.conj_conj, ← mul_assoc, h1, one_mul]

/-- `ψ_{S_f}` is trivial on `𝔩_0`. -/
theorem psiS_small [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) {x : F} (hx : Small 𝔪 0 x) :
    psiS h𝔪 x = 1 := by
  have h2 : ∀ v ∈ placesOf 𝔪, v.valuation F x ≤ 1 := fun v hv => by
    have := hx v hv
    simpa using this
  rw [psiS_apply, C3I.sAddChar_eq_of_wit (y := x) (by simp) h2, ← eInf_emb, eInf_mul_conj]

/-! ### The archimedean kernel -/

/-! ### Shifted kernels -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.F_Alg_Sum
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-FA, part 1: summation tools for cube periodicity (MATH2 §5)

* `tsum_orbit_rel`: reindexing of a sum over orbits of a group action along an equivariant
  partial bijection given as a relation (used for rows modulo units).
* `IsReps c T`: `T` is a complete set of representatives of `R ⧸ (c)`; `sum_reps`: sums over `T`
  of periodic functions are `B7.rsum`s; affine substitution; the counts and the vanishing of
  twisted sums used in the strata of Proposition 5.4.
* `sum_reps_addChar` (MATH2 §5.1): `∑_{t ∈ T} e(μ t / π^n) = q^n · 1[π^n ∣ μ]` — the character sum
  behind `(U u)_ν = q³ · 1[v_P(ν) ≥ 0] · u_{νπ³}`.
-/

set_option autoImplicit false

namespace ArtinKP.FA

open ArtinKP.B7

/-! ### Sums over orbits -/

/-! ### Complete sets of representatives -/

section reps

variable {R : Type*} [CommRing R]

/-- A sum over a complete set of representatives is the residue sum. -/
theorem sum_reps {c : R} {T : Finset R} (hT : IsReps c T) {f : R → ℂ} (hf : Per c f) :
    ∑ t ∈ T, f t = rsum c f := by
  classical
  let e : {t // t ∈ T} → R ⧸ Ideal.span {c} := fun t => Ideal.Quotient.mk _ t.1
  have he : Function.Bijective e := by
    constructor
    · intro t t' h
      have h' : c ∣ t.1 - t'.1 := mk_eq_mk_iff.1 h
      obtain ⟨u, -, hu⟩ := hT t.1
      have h1 := hu t.1 ⟨t.2, by simp⟩
      have h2 := hu t'.1 ⟨t'.2, h'⟩
      exact Subtype.ext (h1.trans h2.symm)
    · intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨t, ⟨ht, hdvd⟩, -⟩ := hT a
      exact ⟨⟨t, ht⟩, (mk_eq_mk_iff.2 hdvd).symm⟩
  unfold rsum
  rw [← finsum_eq_of_bijective e he (f := fun t : {t // t ∈ T} => f t.1)
    (g := fun x => f (rep c x)) (fun t => (hf.rep_mk t.1).symm)]
  exact ((finsum_eq_sum_of_fintype _).trans (Finset.sum_coe_sort T f)).symm

variable [IsDomain R] {π : R} (hπ : π ≠ 0) (hfin : ∀ k : ℕ, Finite (R ⧸ Ideal.span {π ^ k}))

include hπ hfin in
/-- `#(R/π^n) = q^n`. -/
lemma rsum_pow_one (n : ℕ) :
    rsum (π ^ n) (fun _ => (1 : ℂ)) = (Nat.card (R ⧸ Ideal.span {π}) : ℂ) ^ n := by
  have h1 := hfin 1
  rw [pow_one] at h1
  cases n with
  | zero =>
    rw [pow_zero, pow_zero]
    have : Subsingleton (R ⧸ Ideal.span {(1 : R)}) :=
      Ideal.Quotient.subsingleton_iff.2 (by simp)
    rw [rsum_one, Nat.card_of_subsingleton (0 : R ⧸ Ideal.span {(1 : R)})]
    simp
  | succ k =>
    rw [rsum_pow_of_per hπ hfin (fun _ _ _ => rfl), rsum_one, pow_succ]

end reps

/-! ### The additive character sum of §5.1 -/

section addchar

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] (A : AddData R K)
  {π : R} (hπ : π ≠ 0) (hmax : (Ideal.span {π}).IsMaximal)
  (hfin : ∀ k : ℕ, Finite (R ⧸ Ideal.span {π ^ k}))

include hπ hmax hfin in
open Classical in
/-- **MATH2 §5.1, the character sum.**  For a complete set `T` of representatives modulo `π^n`
and an additive character `e` trivial on `R` but not on `π⁻¹R`:
`∑_{t ∈ T} e(μ t / π^n) = q^n` if `π^n ∣ μ`, and `0` otherwise. -/
theorem sum_reps_addChar {a₀ : R} (ha₀ : A.ψ a₀ π ≠ 1) (n : ℕ) {T : Finset R}
    (hT : IsReps (π ^ n) T) (μ : R) :
    ∑ t ∈ T, A.ψ (μ * t) (π ^ n)
      = if π ^ n ∣ μ then (Nat.card (R ⧸ Ideal.span {π}) : ℂ) ^ n else 0 := by
  have hπn : π ^ n ≠ 0 := pow_ne_zero _ hπ
  have hper : Per (π ^ n) (fun t => A.ψ (μ * t) (π ^ n)) := fun a b hab =>
    A.ψ_per hπn (by rw [← mul_sub]; exact hab.mul_left μ)
  rw [sum_reps hT hper]
  split_ifs with hdvd
  · obtain ⟨r, rfl⟩ := hdvd
    rw [← rsum_pow_one hπ hfin n]
    exact rsum_congr fun t => by rw [mul_assoc]; exact A.ψ_mul_self hπn _
  · -- the exact power of `π` in `μ`
    have hex : ∃ k, ¬ π ^ (k + 1) ∣ μ := by
      cases n with
      | zero => exact absurd (by simp) hdvd
      | succ n => exact ⟨n, hdvd⟩
    have hspec := Nat.find_spec hex
    have hmin := fun (m : ℕ) (h : m < Nat.find hex) => Nat.find_min hex h
    set k := Nat.find hex with hk
    have hkn : k + 1 ≤ n := by
      by_contra hlt
      rw [not_le] at hlt
      rcases Nat.eq_zero_or_pos n with h1 | h1
      · rw [h1, pow_zero] at hdvd; exact hdvd (one_dvd _)
      · have := hmin (n - 1) (by omega)
        rw [not_not] at this
        have hn : n - 1 + 1 = n := by omega
        rw [hn] at this
        exact hdvd this
    have hdk : π ^ k ∣ μ := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0, pow_zero]; exact one_dvd _
      · have := hmin (k - 1) (by omega)
        rw [not_not, Nat.sub_add_cancel hpos] at this
        exact this
    obtain ⟨μ₀, hμ⟩ := hdk
    have hμ₀ : ¬ π ∣ μ₀ := by
      rintro ⟨r, rfl⟩
      apply hspec
      rw [hμ, pow_succ, ← mul_assoc]
      exact Dvd.intro _ rfl
    obtain ⟨x, y, hxy⟩ := (isCoprime_iff_not_dvd hmax μ₀).2 hμ₀
    obtain ⟨l, rfl⟩ : ∃ l, n = k + 1 + l := ⟨n - (k + 1), by omega⟩
    set b : R := x * a₀ * π ^ l with hb
    have hz : A.ψ (μ * b) (π ^ (k + 1 + l)) = A.ψ a₀ π := by
      have e1 : μ * b = (μ₀ * (x * a₀)) * π ^ (k + l) := by rw [hμ, hb, pow_add]; ring
      have e2 : π ^ (k + 1 + l) = π * π ^ (k + l) := by ring
      rw [e1, e2, A.ψ_mul_right_cancel _ _ (pow_ne_zero _ hπ)]
      refine A.ψ_per hπ ⟨-(y * a₀), ?_⟩
      linear_combination a₀ * hxy
    have e1 := rsum_add_right hper b
    have e2 : rsum (π ^ (k + 1 + l)) (fun d => A.ψ (μ * (d + b)) (π ^ (k + 1 + l)))
        = rsum (π ^ (k + 1 + l)) (fun d => A.ψ (μ * d) (π ^ (k + 1 + l))) * A.ψ a₀ π := by
      rw [← rsum_mul_const]
      exact rsum_congr fun d => by rw [mul_add, A.ψ_add, hz]
    rw [e2] at e1
    by_contra hne
    apply ha₀
    exact mul_left_cancel₀ hne (e1.trans (mul_one _).symm)

end addchar

end ArtinKP.FA
end

section
-- module Solutions.Artin.KP.F_Alg_Link
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-FA, part 5: the hypotheses of `F_Alg_*` at an allowed generator

* `PrimeElt.of_span`: `PrimeElt` from `span {π} = P·R`, maximality and a nontrivial symbol;
* `primeElt_gen`: `PrimeElt ι 𝔪 v (g.gen v.asIdeal)` at a good exterior prime, for any
  `S : CubicSymbol (SInt 𝔪)` that agrees with `cubicExt` (the same hypotheses as `E.pairingHS`
  and `B7_Link`);
* `sum_reps_sAddChar`: the character sum of MATH2 §5.1 for `sAddChar` at `g.gen P`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.FA

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}

section gen

variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (g : AllowedGen ι 𝔪)
  (h𝔪 : 𝔪 ≠ ⊥) (S : CubicSymbol (SInt 𝔪))
  (hS : ∀ d : SInt 𝔪, S.sym d (g.gen v.asIdeal) = sexticResidueSymbol ι 𝔪 v.asIdeal d ^ 2)
  (hsym : ∀ d c : SInt 𝔪, c ≠ 0 → S.sym d c = cubicExt ι 𝔪 d c)

include h h𝔪 in
open Classical in
/-- **MATH2 §5.1** for `sAddChar`: `∑_{t ∈ T} e(μ t/π^n) = (N P)^n · 1[π^n ∣ μ]`, `π = g.gen P`. -/
theorem sum_reps_sAddChar (n : ℕ) {T : Finset (SInt 𝔪)} (hT : IsReps (g.gen v.asIdeal ^ n) T)
    (μ : SInt 𝔪) :
    ∑ t ∈ T, sAddChar 𝔪 ((μ : F) * (t : F) / (g.gen v.asIdeal : F) ^ n)
      = if g.gen v.asIdeal ^ n ∣ μ then (Ideal.absNorm v.asIdeal : ℂ) ^ n else 0 := by
  obtain ⟨a₀, ha₀⟩ := exists_ψ_ne_one h g h𝔪
  have := sum_reps_addChar (sAdd 𝔪 h𝔪) (gen_ne_zero h g) (isMaximal_span_gen h g)
    (finite_quot_gen_pow h g h𝔪) ha₀ n hT μ
  rw [card_quot_gen h g] at this
  rw [← this]
  refine Finset.sum_congr rfl fun t _ => ?_
  change _ = sAddChar 𝔪 _
  congr 1

end gen

end ArtinKP.FA
end
end

section
-- module Solutions.Artin.KP.F_Eis_Fourier
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-FB, part 4: the operator `U` on Fourier coefficients (MATH2 §5.1)

Vocabulary of WP-B (`B_FourArch`): `emb : F →+ ℂ^r`, `eInf`, and the character
`chiInf ν x = conj e_∞(ν x)` against which the `ν`-th coefficient is taken; a coefficient is an
integral over a cell `D` (a fundamental domain of a lattice `L ⊂ ℂ^r` of periods).

* `sum_eInf_reps`: `∑_{t ∈ T} e_∞(μ t/πⁿ) = (N P)ⁿ · 1[πⁿ ∣ μ]` for `T` deep
  (`FA.sum_reps_sAddChar` and `B.psiS_small`);
* `setIntegral_image_mulE`: the change of variables `x = a·y` on `ℂ^r`, Jacobian `N_∞(a)`;
* `setIntegral_translate`, `integrableOn_translate`: integrals of periodic functions over a
  cell are translation invariant;
* `coeff_sum_translate`: on `ℂ^r`, for an `L`-periodic `h`,
  `∫_{aD} (∑_t h((x+t)/a)) conj e_∞(νx) dx = N_∞(a) (∑_t e_∞(νt)) ∫_D h(y) conj e_∞(νa·y) dy`;
* `coeff_U`: the same for `U a T u` at height `v`;
* `coeff_U_gen`: **`(Uu)_ν(v) = q³ · 1[ν ∈ R] · u_{νπ³}(v/|π³|)`** at `π = g.gen P`
  (cells `π³D` and `D`; the factor `N_∞(π³) = vol(π³D)/vol(D)` is the normalization of the cell).
-/

set_option autoImplicit false

open scoped ComplexConjugate Pointwise
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.FB

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E ArtinKP.FA ArtinKP.X ArtinKP.B ArtinKP.B1

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}

/-! ### The character sum in `e_∞` form -/

open Classical in
/-- **MATH2 §5.1, character sum**: for `T` a complete set of representatives of `R/πⁿR` with
`μ t/πⁿ` integral at `S_f` for all `t ∈ T`, `∑_t e_∞(μ t/πⁿ) = (N P)ⁿ · 1[πⁿ ∣ μ]`. -/
theorem sum_eInf_reps_oai [IsTotallyComplex F] (h : C3I.Good 𝔪 v) (g : AllowedGen ι 𝔪) (h𝔪 : 𝔪 ≠ ⊥)
    (n : ℕ) {T : Finset (SInt 𝔪)} (hT : IsReps (g.gen v.asIdeal ^ n) T) (μ : SInt 𝔪)
    (hdeep : ∀ t ∈ T, Small 𝔪 0 ((μ : F) * (t : F) / (g.gen v.asIdeal : F) ^ n)) :
    ∑ t ∈ T, eInf (emb ((μ : F) * (t : F) / (g.gen v.asIdeal : F) ^ n))
      = if g.gen v.asIdeal ^ n ∣ μ then (Ideal.absNorm v.asIdeal : ℂ) ^ n else 0 := by
  rw [← sum_reps_sAddChar h g h𝔪 n hT μ]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [eInf_emb_eq h𝔪, psiS_small h𝔪 (hdeep t ht), map_one, mul_one]

/-! ### Scaling on `ℂ^r` -/

/-! ### Translation invariance over a cell -/

end ArtinKP.FB
end
end

theorem solution.{u_1} : type_of% @ArtinKP.FB.sum_eInf_reps_oai.{u_1} := @ArtinKP.FB.sum_eInf_reps_oai.{u_1}
