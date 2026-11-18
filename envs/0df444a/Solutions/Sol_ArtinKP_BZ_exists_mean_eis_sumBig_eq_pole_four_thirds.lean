-- Prove2me | solution 1 for ArtinKP.BZ.exists_mean_eis_sumBig_eq_pole_four_thirds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:12:02.038015+00:00
-- url     : https://prove2.me/submissions/847682d1-7386-4ee5-a5e4-b1fea5d00e6a

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
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_ArtinKPB017
import Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc
import Theorems.Thm_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Theorems.Thm_ArtinKP_B_fourier_coeff
import Theorems.Thm_ArtinKP_Z_tsum_G0

section
-- module Solutions.Artin.KP.B1_Const
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-B1, file 6: the constant term of `Tinf` (Lemma K) by unfolding and scaling

`constTerm S σ v = ∫_{ℂ^r/𝓞} ∑_{p ≠ ∞} ht_p(x, v)^σ dx` (integral over the fundamental cell `fundD`).
Unfolding over the free action of the translations `n(β)`, `β ∈ 𝓞_F`, on the classes `≠ ∞`
(`orbEquiv`) turns it into a sum of integrals over all of `ℂ^r`, each of which scales exactly like
`ht(v)^{2-σ}` (`lintegral_sHt_scale`).  Hence `constTerm S σ v = ht(v)^{2-σ} · constTerm S σ 1`
(`constTerm_scale`), and `constTerm S σ 1 < ∞` by the locally uniform convergence (`constTerm_one_lt_top`).
No zeta function and no strong approximation are needed.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

theorem instCountableField : Countable F := by
  haveI _iCO := ArtinKP.X.instCountableRingOfIntegers (F := F)
  have : Function.Surjective (fun p : 𝓞 F × 𝓞 F => ((p.1 : F) / (p.2 : F))) := by
    intro z
    obtain ⟨x, y, -, h⟩ := IsFractionRing.div_surjective (A := 𝓞 F) z
    exact ⟨(x, y), h⟩
  exact this.countable

instance instCountableSPair {S : Finset (FinitePlace F)} : Countable (SPair S) := by
  haveI _iCF := ArtinKP.B1.instCountableField (F := F)
  have : Function.Injective (fun q : SPair S => (q.c, q.d)) := by
    intro q q' h
    exact SPair.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  exact this.countable

instance instCountablePairClass {S : Finset (FinitePlace F)} : Countable (PairClass S) :=
  Quotient.countable

variable [IsTotallyComplex F]

/-! ### The lattice `𝓞_F ⊂ ℂ^r` -/

lemma isFund : IsAddFundamentalDomain (latSub F) (fundD F) volume :=
  ZSpan.isAddFundamentalDomain' (latE (F := F)) volume

lemma fundD_bounded : Bornology.IsBounded (fundD F) := ZSpan.fundamentalDomain_isBounded _

/-! ### Scaling -/

/-! ### Orbits of the translations on the classes `≠ ∞` -/

/-! ### The constant term -/

end

end ArtinKP.B1
end

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

lemma Per.mul {c : R} {f g : R → ℂ} (hf : Per c f) (hg : Per c g) : Per c (fun d => f d * g d) :=
  fun a b hab => by simp only [hf a b hab, hg a b hab]

lemma rsum_congr {c : R} {f g : R → ℂ} (h : ∀ d, f d = g d) : rsum c f = rsum c g := by
  unfold rsum; exact finsum_congr fun x => h _

lemma rsum_const_mul (c : R) (f : R → ℂ) (z : ℂ) : rsum c (fun d => z * f d) = z * rsum c f := by
  unfold rsum; rw [mul_finsum]

lemma rsum_mul_const (c : R) (f : R → ℂ) (z : ℂ) : rsum c (fun d => f d * z) = rsum c f * z := by
  unfold rsum; rw [finsum_mul]

/-- Reindexing by a map of `R` that induces a permutation of the residues. -/
lemma rsum_comp {c : R} {f : R → ℂ} (hf : Per c f) (σ : R → R)
    (τ : (R ⧸ Ideal.span {c}) ≃ (R ⧸ Ideal.span {c}))
    (h : ∀ a, Ideal.Quotient.mk (Ideal.span {c}) (σ a) = τ (Ideal.Quotient.mk (Ideal.span {c}) a)) :
    rsum c (fun d => f (σ d)) = rsum c f := by
  unfold rsum
  refine Eq.trans ?_ (finsum_comp_equiv τ)
  refine finsum_congr fun x => hf _ _ ?_
  rw [← mk_eq_mk_iff, h, mk_rep, mk_rep]

/-- Invariance under multiplication by a unit modulo `c`. -/
lemma rsum_mul_unit {c : R} {f : R → ℂ} (hf : Per c f) {u u' : R} (hu : c ∣ u * u' - 1) :
    rsum c (fun d => f (u * d)) = rsum c f := by
  have h1 : Ideal.Quotient.mk (Ideal.span {c}) u * Ideal.Quotient.mk (Ideal.span {c}) u' = 1 := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {c})), mk_eq_mk_iff]; exact hu
  refine rsum_comp hf (fun d => u * d)
    { toFun := fun x => Ideal.Quotient.mk (Ideal.span {c}) u * x
      invFun := fun x => Ideal.Quotient.mk (Ideal.span {c}) u' * x
      left_inv := fun x => by
        show Ideal.Quotient.mk (Ideal.span {c}) u' * (Ideal.Quotient.mk (Ideal.span {c}) u * x) = x
        rw [← mul_assoc, mul_comm _ (Ideal.Quotient.mk _ u), h1, one_mul]
      right_inv := fun x => by
        show Ideal.Quotient.mk (Ideal.span {c}) u * (Ideal.Quotient.mk (Ideal.span {c}) u' * x) = x
        rw [← mul_assoc, h1, one_mul] } (fun d => by simp)

lemma rsum_mul_coprime_unit {c : R} {f : R → ℂ} (hf : Per c f) {u : R} (hu : IsCoprime u c) :
    rsum c (fun d => f (u * d)) = rsum c f := by
  obtain ⟨a, b, hab⟩ := hu
  refine rsum_mul_unit hf (u' := a) ⟨-b, ?_⟩
  linear_combination hab

/-- **Chinese remainder theorem** for residue sums. -/
lemma rsum_mul_coprime {c c' : R} [Finite (R ⧸ Ideal.span {c})] [Finite (R ⧸ Ideal.span {c'})]
    (h : IsCoprime c c') {f : R → ℂ} (hf : Per (c * c') f) :
    rsum (c * c') f = rsum c (fun d₁ => rsum c' (fun d₂ => f (d₁ * c' + d₂ * c))) := by
  set Φ : (R ⧸ Ideal.span {c}) × (R ⧸ Ideal.span {c'}) → R ⧸ Ideal.span {c * c'} :=
    fun p => Ideal.Quotient.mk _ (rep c p.1 * c' + rep c' p.2 * c) with hΦ
  have hbij : Function.Bijective Φ := by
    constructor
    · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ hxy
      simp only [hΦ, mk_eq_mk_iff] at hxy
      have e1 : c ∣ (rep c x₁ - rep c x₂) * c' := by
        have := (dvd_mul_right c c').trans hxy
        have h2 : (rep c x₁ - rep c x₂) * c' =
            (rep c x₁ * c' + rep c' y₁ * c - (rep c x₂ * c' + rep c' y₂ * c)) -
              c * (rep c' y₁ - rep c' y₂) := by ring
        rw [h2]; exact dvd_sub this (dvd_mul_right _ _)
      have e2 : c' ∣ (rep c' y₁ - rep c' y₂) * c := by
        have := (dvd_mul_left c' c).trans hxy
        have h2 : (rep c' y₁ - rep c' y₂) * c =
            (rep c x₁ * c' + rep c' y₁ * c - (rep c x₂ * c' + rep c' y₂ * c)) -
              c' * (rep c x₁ - rep c x₂) := by ring
        rw [h2]; exact dvd_sub this (dvd_mul_right _ _)
      have e1' := h.dvd_of_dvd_mul_right e1
      have e2' := h.symm.dvd_of_dvd_mul_right e2
      rw [← mk_eq_mk_iff, mk_rep, mk_rep] at e1' e2'
      rw [e1', e2']
    · intro z
      obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨a, b, hab⟩ := h
      refine ⟨(Ideal.Quotient.mk _ (d * b), Ideal.Quotient.mk _ (d * a)), ?_⟩
      simp only [hΦ, mk_eq_mk_iff]
      obtain ⟨s, hs⟩ := dvd_rep_mk_sub c (d * b)
      obtain ⟨t, ht⟩ := dvd_rep_mk_sub c' (d * a)
      refine ⟨s + t, ?_⟩
      linear_combination c' * hs + c * ht + d * hab
  unfold rsum
  rw [← finsum_eq_of_bijective Φ hbij (g := fun z => f (rep (c * c') z))
    (f := fun p => f (rep c p.1 * c' + rep c' p.2 * c)) (fun p => (hf.rep_mk _).symm)]
  rw [finsum_curry _ (Set.toFinite _)]

end ArtinKP.B7
end

section
-- module Solutions.Artin.KP.B7_Gauss
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
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

lemma ψ_zero (c : R) : A.ψ 0 c = 1 := by
  unfold ψ; rw [map_zero, zero_div, ← map_zero (algebraMap R K), A.e_int]

lemma ψ_per {c : R} (hc : c ≠ 0) {a b : R} (h : c ∣ a - b) : A.ψ a c = A.ψ b c := by
  obtain ⟨r, hr⟩ := h
  have : a = b + c * r := by rw [← hr]; ring
  rw [this, ψ_add, ψ_mul_self A hc, mul_one]

lemma ψ_mul_right_cancel (a c : R) {c' : R} (hc' : c' ≠ 0) : A.ψ (a * c') (c * c') = A.ψ a c := by
  unfold ψ
  rw [map_mul, map_mul, mul_div_mul_right _ _ (A.map_ne_zero hc')]

lemma ψ_mul_left_cancel (a c : R) {c' : R} (hc' : c' ≠ 0) : A.ψ (c' * a) (c' * c) = A.ψ a c := by
  rw [mul_comm c' a, mul_comm c' c, ψ_mul_right_cancel A a c hc']

end AddData

/-! ### Elementary facts about the symbol -/

namespace CubicSymbol

variable (S : CubicSymbol R)

lemma sym_ne_zero {d c : R} (hc : c ≠ 0) (h : IsCoprime d c) : S.sym d c ≠ 0 := fun h0 =>
  (S.sym_eq_zero_iff d c hc).1 h0 h

lemma sym_pow_right (d : R) {c : R} (hc : c ≠ 0) (j : ℕ) : S.sym d (c ^ j) = S.sym d c ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero]; exact S.sym_unit_right d 1 isUnit_one
  | succ j ih => rw [pow_succ, S.sym_mul_right d _ _ (pow_ne_zero _ hc) hc, ih, pow_succ]

lemma sym_per {c : R} (hc : c ≠ 0) : Per c (fun d => (S.sym d c)⁻¹) :=
  fun a b hab => by simp only [S.sym_congr a b c hc hab]

end CubicSymbol

lemma pow_ne_one_of_cube {z : ℂ} (h3 : z ^ 3 = 1) (h1 : z ≠ 1) {j : ℕ} (hj : ¬ 3 ∣ j) :
    z ^ j ≠ 1 := by
  have hz : z ^ j = z ^ (j % 3) := by
    conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, h3, one_pow, one_mul]
  rw [hz]
  have h : j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases h with h | h
  · rw [h, pow_one]; exact h1
  · rw [h]
    intro h2
    apply h1
    have : z ^ 3 = z ^ 2 * z := by ring
    rw [h3, h2, one_mul] at this
    exact this.symm

lemma pow_eq_one_of_cube {z : ℂ} (h3 : z ^ 3 = 1) {j : ℕ} (hj : 3 ∣ j) : z ^ j = 1 := by
  obtain ⟨m, rfl⟩ := hj
  rw [pow_mul, h3, one_pow]

/-! ### The Gauss sum -/

variable (S : CubicSymbol R) (A : AddData R K)

/-- The summand of `g(ν, c)` is periodic modulo `c` (well-definedness). -/
lemma gauss_per (ν : R) {c : R} (hc : c ≠ 0) :
    Per c (fun d => (S.sym d c)⁻¹ * A.ψ (ν * d) c) := by
  refine (S.sym_per hc).mul fun a b hab => A.ψ_per hc ?_
  rw [← mul_sub]; exact hab.mul_left ν

lemma gauss_zero_left (c : R) : gauss S A 0 c = csum S c := by
  unfold gauss csum
  refine rsum_congr fun d => ?_
  rw [zero_mul, A.ψ_zero, mul_one]

/-- **(B7), twisted multiplicativity**: for coprime `c`, `c'`,
`g(ν, c c') = (c/c')⁻¹ (c'/c)⁻¹ g(ν, c) g(ν, c')`. -/
theorem gauss_mul (ν : R) {c c' : R} (hc : c ≠ 0) (hc' : c' ≠ 0)
    [Finite (R ⧸ Ideal.span {c})] [Finite (R ⧸ Ideal.span {c'})] (h : IsCoprime c c') :
    gauss S A ν (c * c') =
      (S.sym c c')⁻¹ * (S.sym c' c)⁻¹ * gauss S A ν c * gauss S A ν c' := by
  have key : ∀ d₁ d₂ : R,
      (S.sym (d₁ * c' + d₂ * c) (c * c'))⁻¹ * A.ψ (ν * (d₁ * c' + d₂ * c)) (c * c') =
        ((S.sym c c')⁻¹ * (S.sym c' c)⁻¹ * ((S.sym d₁ c)⁻¹ * A.ψ (ν * d₁) c)) *
          ((S.sym d₂ c')⁻¹ * A.ψ (ν * d₂) c') := by
    intro d₁ d₂
    have h1 : S.sym (d₁ * c' + d₂ * c) c = S.sym d₁ c * S.sym c' c := by
      rw [S.sym_congr (d₁ * c' + d₂ * c) (d₁ * c') c hc ⟨d₂, by ring⟩, S.sym_mul_left _ _ _ hc]
    have h2 : S.sym (d₁ * c' + d₂ * c) c' = S.sym d₂ c' * S.sym c c' := by
      rw [S.sym_congr (d₁ * c' + d₂ * c) (d₂ * c) c' hc' ⟨d₁, by ring⟩, S.sym_mul_left _ _ _ hc']
    have h3 : A.ψ (ν * (d₁ * c' + d₂ * c)) (c * c') = A.ψ (ν * d₁) c * A.ψ (ν * d₂) c' := by
      rw [show ν * (d₁ * c' + d₂ * c) = ν * d₁ * c' + c * (ν * d₂) by ring, A.ψ_add,
        A.ψ_mul_right_cancel _ _ hc', A.ψ_mul_left_cancel _ _ hc]
    rw [S.sym_mul_right _ _ _ hc hc', h1, h2, h3]
    simp only [mul_inv]
    ring
  unfold gauss
  rw [rsum_mul_coprime h (gauss_per S A ν (mul_ne_zero hc hc'))]
  rw [rsum_congr (fun d₁ => (rsum_congr (fun d₂ => key d₁ d₂)).trans (rsum_const_mul c' _ _))]
  rw [rsum_mul_const, rsum_const_mul]

/-! ### Constant-term sums -/

/-- If `(·/c)` is trivial on residues prime to `c`, the constant-term sum is `φ_R(c)`. -/
theorem csum_eq_phi {c : R} (hc : c ≠ 0) (h : ∀ d : R, IsCoprime d c → S.sym d c = 1) :
    csum S c = phi c := by
  classical
  unfold csum phi
  refine rsum_congr fun d => ?_
  by_cases hd : IsCoprime d c
  · rw [if_pos hd, h d hd, inv_one]
  · rw [if_neg hd, (S.sym_eq_zero_iff d c hc).2 hd, inv_zero]

/-- If `(·/c)` is nontrivial on residues prime to `c`, the constant-term sum vanishes. -/
theorem csum_eq_zero {c : R} (hc : c ≠ 0) {d₀ : R} (h : IsCoprime d₀ c) (h1 : S.sym d₀ c ≠ 1) :
    csum S c = 0 := by
  have h0 := S.sym_ne_zero hc h
  have e1 : csum S c = (S.sym d₀ c)⁻¹ * csum S c := by
    unfold csum
    rw [← rsum_const_mul]
    conv_lhs => rw [← rsum_mul_coprime_unit (S.sym_per hc) h]
    refine rsum_congr fun d => ?_
    rw [S.sym_mul_left _ _ _ hc, mul_inv]
  by_contra hne
  apply h1
  have h2 : (S.sym d₀ c)⁻¹ = 1 := by
    have := mul_right_cancel₀ hne (e1.symm.trans (one_mul _).symm)
    exact this
  exact inv_eq_one.1 h2

/-- `(·/c)` is trivial when `c` is a unit times a cube. -/
lemma sym_eq_one_of_cube {u b : R} (hu : IsUnit u) (hb : b ≠ 0) {d : R}
    (hd : IsCoprime d (u * b ^ 3)) : S.sym d (u * b ^ 3) = 1 := by
  have hdb : IsCoprime d b := (IsCoprime.pow_right_iff (by norm_num : 0 < 3)).1 hd.of_mul_right_right
  rw [S.sym_mul_right d u (b ^ 3) hu.ne_zero (pow_ne_zero _ hb), S.sym_unit_right d u hu, one_mul,
    S.sym_pow_right d hb, S.sym_pow_three d b hb hdb]

/-- **(B6)/(B7), constant term, cube case**: `∑_{d mod c} (d/c)⁻¹ = φ_R(c)` for `c = u b³`. -/
theorem csum_of_cube {u b : R} (hu : IsUnit u) (hb : b ≠ 0) :
    csum S (u * b ^ 3) = phi (u * b ^ 3) :=
  csum_eq_phi S (mul_ne_zero hu.ne_zero (pow_ne_zero _ hb)) fun _ hd =>
    sym_eq_one_of_cube S hu hb hd

/-! ### Prime powers -/

section prime

variable {π : R} (hπ : π ≠ 0) (hmax : (Ideal.span {π}).IsMaximal)
  (hfin : ∀ k : ℕ, Finite (R ⧸ Ideal.span {π ^ k}))

include hπ in
/-- The constant-term sum at a prime power: `φ(π^j)` if `3 ∣ j`, else `0`. -/
theorem csum_prime_pow {d₀ : R} (hd₀ : IsCoprime d₀ π) (h1 : S.sym d₀ π ≠ 1) (j : ℕ) :
    csum S (π ^ j) = if 3 ∣ j then phi (π ^ j) else 0 := by
  have hpj : π ^ j ≠ 0 := pow_ne_zero _ hπ
  split_ifs with h3
  · refine csum_eq_phi S hpj fun d hd => ?_
    rw [S.sym_pow_right d hπ]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [pow_zero]
    · exact pow_eq_one_of_cube (S.sym_pow_three d π hπ ((IsCoprime.pow_right_iff hj).1 hd)) h3
  · refine csum_eq_zero S hpj (d₀ := d₀) hd₀.pow_right ?_
    rw [S.sym_pow_right d₀ hπ]
    exact pow_ne_one_of_cube (S.sym_pow_three d₀ π hπ hd₀) h1 h3

end prime

end ArtinKP.B7
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

/-- `I R ∩ 𝓞 = I` for an ideal `I` coprime to `𝔪`. -/
lemma mem_of_map_mem (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤) (a : 𝓞 F)
    (ha : algebraMap (𝓞 F) (SInt 𝔪) a ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪))) : a ∈ I := by
  set φ := algebraMap (𝓞 F) (SInt 𝔪)
  have hinj : Function.Injective φ := by
    intro x y hxy
    have := congrArg (fun z : SInt 𝔪 => (z : F)) hxy
    simp only [φ, C3I.coe_alg] at this
    exact IsFractionRing.injective (𝓞 F) F this
  -- the predicate
  have hQ : ∀ x ∈ I.map φ, ∃ N : ℕ, ∀ w ∈ 𝔪 ^ N, ∃ i ∈ I, φ w * x = φ i := by
    intro x hx
    rw [Ideal.map] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i0, hi0, rfl⟩ := hx
      exact ⟨0, fun w _ => ⟨w * i0, I.mul_mem_left _ hi0, by rw [map_mul]⟩⟩
    | zero => exact ⟨0, fun w _ => ⟨0, I.zero_mem, by simp⟩⟩
    | add x y _ _ hx hy =>
      obtain ⟨N1, h1⟩ := hx
      obtain ⟨N2, h2⟩ := hy
      refine ⟨max N1 N2, fun w hw => ?_⟩
      obtain ⟨i1, hi1, e1⟩ := h1 w (Ideal.pow_le_pow_right (le_max_left _ _) hw)
      obtain ⟨i2, hi2, e2⟩ := h2 w (Ideal.pow_le_pow_right (le_max_right _ _) hw)
      exact ⟨i1 + i2, I.add_mem hi1 hi2, by rw [mul_add, e1, e2, map_add]⟩
    | smul r x _ hx =>
      obtain ⟨Nx, hNx⟩ := hx
      obtain ⟨Nr, hNr⟩ := exists_pow_mul_mem (𝔪 := 𝔪) r
      refine ⟨Nr + Nx, fun w hw => ?_⟩
      rw [pow_add] at hw
      refine Submodule.mul_induction_on hw ?_ ?_
      · intro w1 hw1 w2 hw2
        obtain ⟨c, hc⟩ := hNr w1 hw1
        obtain ⟨i, hi, ei⟩ := hNx w2 hw2
        refine ⟨c * i, I.mul_mem_left _ hi, ?_⟩
        rw [smul_eq_mul, map_mul, map_mul, ← hc, ← ei]; ring
      · rintro w1 w2 ⟨i1, hi1, e1⟩ ⟨i2, hi2, e2⟩
        exact ⟨i1 + i2, I.add_mem hi1 hi2, by rw [map_add, add_mul, e1, e2, map_add]⟩
  obtain ⟨N, hN⟩ := hQ _ ha
  have hcop : IsCoprime I (𝔪 ^ N) := (Ideal.isCoprime_iff_sup_eq.mpr hI).pow_right
  obtain ⟨u, hu, w, hw, huw⟩ := hcop.exists
  obtain ⟨i, hi, ei⟩ := hN w hw
  have : w * a = i := hinj (by rw [map_mul, ei])
  have ha' : a = u * a + w * a := by rw [← add_mul, huw, one_mul]
  rw [ha', this]
  exact I.add_mem (I.mul_mem_right _ hu) hi

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

end ArtinKP.B7
end

section
-- module Solutions.Artin.KP.S_Basic
attribute [-instance] _root_.ArtinKP.B1.PairClass.instNonempty _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-S, part 1: `S_f`-adic smallness, norms, the pairing `⟨·,·⟩` on `F`, rows of `SL₂(R)`

* `Small 𝔪 N x`: `v(x) ≤ exp(-N)` at every `v ∣ 𝔪` (`N : ℤ`; `N < 0` means "bounded").
* `absS 𝔪 x = |x|_{S_f}`, `normS 𝔪 c d = ‖(c,d)‖ = ∏_{v ∣ 𝔪} max(|c|_v, |d|_v)`.
* `brk ι P 𝔪 x y = ⟨x, y⟩ = ι (x, y)_S` for `x, y ≠ 0`, and `1` if `x = 0` or `y = 0`.
  With WP-A's orientation `⟨c, d⟩ = (d/c)(c/d)⁻¹` on coprime elements of `R` (`brk_reciprocity`).
* `sig`: Kubota's `σ_S` evaluated on a pair and a matrix, through `ι`.
* `Row 𝔪`: primitive pairs of `R = SInt 𝔪`; right action of `SL₂(R)`; scaling by `Rˣ`;
  `kappaRow` and its transformation laws (`kappaRow_act` is Lemma A5 on rows).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

/-! ### Smallness at the places of `S_f` -/

namespace Small

variable {𝔪 : Ideal (𝓞 F)} {N M : ℤ} {x y : F}

theorem deep_inv (hN : 1 ≤ N) (hx : Small 𝔪 N (x - 1)) : Small 𝔪 N (x⁻¹ - 1) := fun v hv => by
  have h1 := hx.val_eq_one hN v hv
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, map_zero] at h1; exact zero_ne_one h1
  have e : x⁻¹ - 1 = -(x - 1) * x⁻¹ := by field_simp; ring
  rw [e, map_mul, Valuation.map_neg, map_inv₀, h1, inv_one, mul_one]
  exact hx v hv

end Small

/-! ### Absolute values at `S_f` -/

/-! ### The pairing `⟨x, y⟩ = ι (x, y)_S` on `F` -/

/-! ### Kubota's `σ_S` on a pair and a matrix -/

/-! ### Primitive rows -/

/-! ### The Kubota symbol on rows -/

/-! ### The matrices `w` and `n(t)` -/

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.K_Jacquet
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-K, file 2: the Jacquet integral at a complex place

Additive character: `archChar z = exp(2πi (z + z̄)) = exp(2πi · 2 Re z)` (the trace form `e(Tr z)`
of `ℂ/ℝ`; the goal's `sAddChar` is `exp(−2πi Tr_{F/ℚ}(·))` on fractional parts, whose factor at a
complex place `w` is `archChar (−σ_w ·)`; the Jacquet integral is even in `ν`, so the sign is
immaterial).

`jacquet s ν v = ∫_ℂ (v / (|x|² + v²))^s · archChar(−ν x) dx`. For `Re s > 1`, `v > 0`:

* `jacquet_zero`: `jacquet s 0 v = π/(s−1) · v^{2−s}`;
* `jacquet_eq`: for `ν ≠ 0`,
  `jacquet s ν v = (2π/Γ(s)) · (2π|ν|)^{s−1} · v · K_{s−1}(4π|ν|v)`
  `= (2π^s/Γ(s)) · (2|ν|)^{s−1} · v · K_{s−1}(4π|ν|v)` (`jacquet_eq'`).

The proof is OpenAI's (`OAI.CubicEisenstein.sourceFourierKernel_bessel`, openai/math family 003,
`Eisenstein/HyperbolicSpace.lean`, Apache 2.0; in our port `Definitions.Def_OAIHecke78B005`),
**copied** and restated for `besselK` (importing the bundle would drag B000–B004, ~45k lines).
-/

namespace ArtinKP.K

open MeasureTheory Set Filter
open scoped FourierTransform RealInnerProductSpace

noncomputable section

theorem archChar_zero : archChar 0 = 1 := by simp [archChar]

/-! ## Radial integrals on `ℂ` (copied from OpenAI) -/

lemma integral_radial_sq (f : ℝ → ℂ) :
    (∫ z : ℂ, f (‖z‖ ^ 2)) = (Real.pi : ℂ) * ∫ t : ℝ in Set.Ioi 0, f t := by
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  have hpolar := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => f (r^2))
  have hsub := integral_comp_rpow_Ioi (E := ℂ) f (p := 2) (by norm_num)
  norm_num [Real.rpow_two, Real.rpow_one] at hsub
  simp only [Complex.finrank_real_complex, hball, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Complex.real_smul, ] at hpolar hsub
  rw [hpolar]
  rw [← hsub]
  rw [show (fun x : ℝ => (2:ℂ)*x*f (x^2)) =
      (fun x : ℝ => (2:ℂ)*(x*f (x^2))) by funext x; ring, integral_const_mul]
  ring

lemma add_one_image_Ioi : (fun x : ℝ => x+1) '' Set.Ioi 0 = Set.Ioi 1 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    simp only [Set.mem_Ioi] at *
    linarith
  · intro hy
    refine ⟨y-1, ?_, by ring⟩
    simp only [Set.mem_Ioi] at *
    linarith

lemma integral_add_one_Ioi (f : ℝ → ℂ) :
    (∫ x : ℝ in Set.Ioi 0, f (x+1)) = ∫ x : ℝ in Set.Ioi 1, f x := by
  have h := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

theorem integral_hyperbolicKernel (s : ℂ) (hs : 1 < s.re) :
    (∫ z : ℂ, hyperbolicKernel s z) = (Real.pi : ℂ) / (s-1) := by
  unfold hyperbolicKernel
  rw [integral_radial_sq (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  simp_rw [add_comm (1:ℝ)]
  rw [integral_add_one_Ioi (fun t : ℝ => (t : ℂ)^(-s))]
  rw [integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1)]
  simp only [Complex.ofReal_one, Complex.one_cpow]
  have hn : (-s+1)⁻¹ = -(s-1)⁻¹ := by
    rw [show -s+1=-(s-1) by ring, inv_neg]
  simp only [div_eq_mul_inv, hn]
  ring

lemma sourceFourierKernel_zero (s : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s 0 = (Real.pi : ℂ)/(s-1) := by
  simpa only [sourceFourierKernel, neg_zero, zero_mul, archChar_zero, mul_one]
    using integral_hyperbolicKernel s hs

/-! ## The Bessel form (ours, for `besselK`) -/

lemma traceIntegral_scale (v : ℝ) (hv : 0 < v) (s freq : ℂ) :
    (∫ z : ℂ,hyperbolicKernel s (z/(v:ℂ))*archChar (-freq*z))=
      (v:ℂ)^2*sourceFourierKernel s (freq*v) := by
  have heq (z : ℂ) : hyperbolicKernel s (z/(v:ℂ))*archChar (-freq*z)=
      (fun w : ℂ => hyperbolicKernel s w*archChar (-(freq*v)*w)) (v⁻¹ • z) := by
    simp only [Complex.real_smul,Complex.ofReal_inv]
    congr 2
    · ring
    · field_simp [Complex.ofReal_ne_zero.mpr hv.ne']
  simp_rw [heq]
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure ℂ)
    (fun w : ℂ => hyperbolicKernel s w*archChar (-(freq*v)*w)) hv.le
  simpa only [Complex.finrank_real_complex,Complex.real_smul,Complex.ofReal_pow,sourceFourierKernel] using h

/-! ## The Jacquet integral -/

lemma height_cpow (s : ℂ) {v : ℝ} (hv : 0 < v) (x : ℂ) :
    ((v / (‖x‖ ^ 2 + v ^ 2) : ℝ) : ℂ) ^ s = (v : ℂ) ^ (-s) * hyperbolicKernel s (x / (v : ℂ)) := by
  unfold hyperbolicKernel
  have h1 : (v / (‖x‖ ^ 2 + v ^ 2) : ℝ) = v⁻¹ * (1 + ‖x / (v : ℂ)‖ ^ 2)⁻¹ := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hv.le]
    field_simp
    ring
  have hpos : (0 : ℝ) < 1 + ‖x / (v : ℂ)‖ ^ 2 := by positivity
  rw [h1, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (inv_nonneg.2 hv.le)
    (inv_nonneg.2 hpos.le), Complex.ofReal_inv, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg hv.le, Complex.inv_cpow_ofReal_nonneg hpos.le,
    Complex.cpow_neg, Complex.cpow_neg]

theorem jacquet_eq_sourceFourierKernel (s ν : ℂ) {v : ℝ} (hv : 0 < v) :
    jacquet s ν v = (v : ℂ) ^ (2 - s) * sourceFourierKernel s (ν * v) := by
  unfold jacquet
  simp_rw [height_cpow s hv, mul_assoc]
  rw [integral_const_mul, traceIntegral_scale v hv s ν, ← mul_assoc]
  congr 1
  rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')]
  congr 1
  push_cast; ring

/-- The constant term: `∫_ℂ (v/(|x|²+v²))^s dx = π/(s−1) · v^{2−s}`. -/
theorem jacquet_zero (s : ℂ) (hs : 1 < s.re) {v : ℝ} (hv : 0 < v) :
    jacquet s 0 v = (Real.pi : ℂ) / (s - 1) * (v : ℂ) ^ (2 - s) := by
  rw [jacquet_eq_sourceFourierKernel s 0 hv, zero_mul, sourceFourierKernel_zero s hs, mul_comm]

/-! ## Holomorphy in `s` -/

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.S_BigCell
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-S, part 6: big-cell and small-cell sections

For `η ∈ Fˣ`, a deep level `N ≥ 1`, and a lattice coset `L = {u : Small M (u - t₀)}`:

* `InClass 𝔪 N η c`: `c ∈ η · U_S · (Fˣ)³ · U_N` (`U_N` = units `N`-close to `1`); this is the
  rational form of MATH2's cube-saturated class `η U_S U_𝔫 (F_{S_f}ˣ)³`.
* `bigCell`: `Φ^{big}_s(c, d) = ⟨η, c⟩ |c|_{S_f}^{-s} 1[c ∈ class η] 1[d/c ∈ L]`.
  The unitary factor `⟨η, c⟩` equals MATH2's `⟨η₀, ε⟩` for `c = η₀ ε t³ u` and needs no choice.
* `smallCell = w · bigCell`: `⟨c, d⟩ ⟨η, d⟩ |d|^{-s} 1[d ∈ class η] 1[-c/d ∈ L]`.
* `nT_bigCell`, `twist_smallCell`: the translates by `n(t)` and `w`.
* `sum_bigCell_apply`: the sum over pairwise disjoint classes (MATH2 §3.1, `Φ^Σ`).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### Classes -/

/-! ### The support of a big-cell section and its stability -/

theorem bigCell_apply (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : P.IsDeepLevel 𝔪 N) (η : F) (hη : η ≠ 0) (M : ℤ) (t₀ : F) (s : ℂ) (c d : F) :
    bigCell ι P hG hN1 hN η hη M t₀ s c d = bigFun ι P 𝔪 N η M t₀ s c d := rfl

/-! ### Small-cell sections -/

/-! ### Finite sums: the sum over classes and additive projections -/

namespace GSection

variable {ι : F →+* ℂ} {P : CubicPkg F}

theorem sum_apply {α : Type*} (T : Finset α) (f : α → GSection ι P 𝔪) (s : ℂ) (c d : F) :
    (∑ i ∈ T, f i) s c d = ∑ i ∈ T, f i s c d := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

end GSection

/-- **The sum of big-cell sections over (pairwise disjoint) classes** is a section, and on the
class of `η₀` it is `⟨η₀, c⟩ |c|^{-s} 1_L(d/c)`: a big-cell function with the unitary symbol
factor `⟨η₀, c⟩` depending on the class of `c` (MATH2 §3.1). -/
theorem sum_bigCell_apply (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : P.IsDeepLevel 𝔪 N) (M : ℤ) (t₀ : F) (T : Finset {η : F // η ≠ 0})
    (hdisj : ∀ η ∈ T, ∀ η' ∈ T, η ≠ η' → ∀ c : F, InClass 𝔪 N η.1 c → ¬ InClass 𝔪 N η'.1 c)
    {η₀ : {η : F // η ≠ 0}} (hη₀ : η₀ ∈ T) {c : F} (hc : InClass 𝔪 N η₀.1 c) (s : ℂ) (d : F) :
    (∑ η ∈ T, bigCell ι P hG hN1 hN η.1 η.2 M t₀) s c d = bigFun ι P 𝔪 N η₀.1 M t₀ s c d := by
  rw [GSection.sum_apply, Finset.sum_eq_single η₀]
  · rfl
  · intro η hη hne
    rw [bigCell_apply]
    exact bigFun_of_not_supp (fun h => hdisj η₀ hη₀ η hη (Ne.symm hne) c hc h.1) s
  · intro h
    exact absurd hη₀ h

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.S_Jacquet
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-S, part 7: finite Jacquet functionals

`F_{S_f}/𝔩` is the discrete countable group `F/𝔩_M`, `𝔩_M = {x : Small M x}` (strong
approximation is not needed to *define* the functional).  For `f : F → ℂ` invariant under `𝔩_M`:

`jac ψ M f ν = vol(𝔩_M) · Σ_{u ∈ F/𝔩_M} f(u) · conj ψ(ν u)`   (`= ∫_{F_{S_f}} f(u) conj ψ(νu) du`),

`J_Φ(c; ν, s) = jac ψ M (u ↦ Φ_s(c, cu)) ν`, `λ_η(Φ_s; ν) = |η|^s J_Φ(η; ν, s)` (`lam`).

* `lam_bigCell`: `λ_η(Φ^{big}_{η,L}; ν) = vol(𝔩) conj ψ(ν t₀)` for `ν ∈ 𝔩^⊥`.
* `jac_eq_zero`: the functional vanishes when `ψ(ν ·)` is non-trivial on a lattice of periods.
* `norm_lam_le`: the uniform bound `|c|^σ |J_Φ(c; ν, s)| ≤ B·K_σ` (MATH2 §0.2), `K_σ = vol·Σ_u
  ∏_v max(1,|u|_v)^{-σ}`.
* `kir`, `xi_bound`: the bound for the Kirillov function (MATH2 §6.3 (K2), (K3)).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem out_spec {M : ℤ} (x : F) :
    ∃ h : F, Small 𝔪 M h ∧ (QuotientAddGroup.mk x : F ⧸ lat 𝔪 M).out = x + h := by
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add (lat 𝔪 M) x
  exact ⟨h.1, h.2, hh⟩

section jac

variable (ψ : SfChar 𝔪) {M : ℤ} {f : F → ℂ} {ν : F}

open Classical in
/-- The functional of the indicator of a coset `t₀ + 𝔩_M`. -/
theorem jac_indicator (A : ℂ) (t₀ : F) (hψ : ∀ h : F, Small 𝔪 M h → ψ (ν * h) = 1) :
    jac ψ M (fun u => if Small 𝔪 M (u - t₀) then A else 0) ν
      = (vol 𝔪 M : ℂ) * (A * (starRingEnd ℂ) (ψ (ν * t₀))) := by
  rw [jac]
  congr 1
  rw [tsum_eq_single (QuotientAddGroup.mk t₀ : F ⧸ lat 𝔪 M)]
  · obtain ⟨h, hh, he⟩ := out_spec (𝔪 := 𝔪) (M := M) t₀
    rw [he, if_pos (by rw [add_sub_cancel_left]; exact hh), mul_add, ψ.map_add, hψ h hh, mul_one]
  · intro u hu
    rw [if_neg, zero_mul]
    intro hs
    apply hu
    rw [← QuotientAddGroup.out_eq' u, QuotientAddGroup.eq]
    have e : -u.out + t₀ = -(u.out - t₀) := by ring
    rw [e]
    exact (lat 𝔪 M).neg_mem hs

end jac

/-! ### The Kirillov function -/

end ArtinKP.S
end
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

/-! ### The archimedean kernel -/

theorem cpow_prod_nonneg {α : Type*} (t : Finset α) (f : α → ℝ) (hf : ∀ i, 0 ≤ f i) (s : ℂ) :
    (((∏ i ∈ t, f i : ℝ)) : ℂ) ^ s = ∏ i ∈ t, ((f i : ℝ) : ℂ) ^ s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun i _ => hf i), ih]

theorem chiInf_zero (x : InfinitePlace F → ℂ) : chiInf (0 : F) x = 1 := by
  simp [chiInf, eInf, archChar]

/-! ### Shifted kernels -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_FourIndex
attribute [-instance] _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-B, part 4: the index set of the unfolded sum

* `exists_sInt_sub_small`: strong approximation `F = R + 𝔩_M` (from `B7.hasWit_all`).
* `latR 𝔪 M = R ∩ 𝔩_M`, `transLat 𝔪 M = emb (R ∩ 𝔩_M) ⊂ ℂ^r` (the translation lattice `Λ_M`).
* `sec`: for `c ≠ 0` a section of `R → R/cR × F/𝔩_M`, `d ↦ (d mod c, d/c mod 𝔩_M)`.
* `thetaEquiv`: `((Σ a, R/c_a R) × F/𝔩_M) × Λ_M ≃ (R∖0)/Rˣ × R`,
  `(((a, α), u), b) ↦ (a, sec(α, u) + c_a b)` — MATH2's `R/cΛ ≅ R/cR × F_{S_f}/cΛ̂`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### Strong approximation -/

/-! ### The translation lattice -/

instance instCountableSInt : Countable (SInt 𝔪) :=
  haveI _iCF := ArtinKP.B1.instCountableField (F := F)
  (Subtype.val_injective : Function.Injective fun b : SInt 𝔪 => (b : F)).countable

instance instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupTransLat (M : ℤ) : Countable (transLat 𝔪 M) := (latREquiv 𝔪 M).symm.injective.countable

/-! ### The section -/

/-! ### The index equivalence -/

/-! ### Rows with `c ≠ 0` modulo units -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.RO_Ring
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-RO, file 1: the ring of `S`-integers is a PID; `SBezout`

`SOf 𝔪 : Finset (FinitePlace F)` is the set of finite places dividing `𝔪`, in the form used by
WP-B1.  For `𝔪 ≠ ⊥`, `B1.IsSInt (SOf 𝔪)` is membership in `SInt 𝔪` (`isSInt_SOf_iff`), so
`B1.SIntRing (SOf 𝔪) ≃+* SInt 𝔪` (`sIntEquiv`).

* `isPrincipalIdealRing_SInt (hG : Good 𝔪) : IsPrincipalIdealRing (SInt 𝔪)`: every ideal of `SInt 𝔪`
  is extended from `𝓞 F` (clear denominators by an `S`-unit, `B1.exists_unit_rescale`), and extended
  ideals are principal (`Good.principal`).
* `isPrincipalIdealRing_SIntRing`, `sBezout (hG : Good 𝔪) : B1.SBezout (SOf 𝔪)`.
-/

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RO

open ArtinKP.A ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- **`R = SInt 𝔪` is a principal ideal ring** when `𝔪` is good. -/
theorem isPrincipalIdealRing_SInt (hG : Good 𝔪) : IsPrincipalIdealRing (SInt 𝔪) :=
  ⟨fun J => by
    rw [← map_comap_eq hG.ne_bot J]
    exact hG.principal _⟩

end

end ArtinKP.RO
end

section
-- module Solutions.Artin.T12.T12B_Euler
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.B1.PairClass.instNonempty _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# T12B: elementary Euler-product glue for `HeckeChar.LSeries`

* `T12B.norm_le_one`: `‖χ I‖ ≤ 1` (values on coprime ideals are roots of unity: class group and
  `(𝓞/𝔪)ˣ` are finite).
* `T12B.lseries_eq_tsum`: `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` for `Re s > 1`.
* `T12B.sieve`: `(∑' g) · ∏_{P ∈ T} (1 − g P) = ∑'_{I coprime to T} g I` for completely
  multiplicative `g` (finite Euler sieve; no infinite product needed).
* `T12B.sieve_bound`: the sieved sum is close to `1` once `T` kills a large finite set.
-/

namespace ArtinPrimitiveRoots

open NumberField Filter Topology
open scoped nonZeroDivisors

namespace T12B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Summability of `∑_I N(I)^{-σ}` -/

theorem lseriesSummable_card {y : ℝ} (hy : 1 < y) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) y := by
  have hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue F)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ))
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim))
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one (s := (y : ℂ)) (by simpa using hy)
  simpa using h

theorem fiber_finite (n : ℕ) : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-- `∑_I N(I)^{-σ}` converges for `σ > 1`. -/
theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)) := by
  haveI _iFF := ArtinPrimitiveRoots.T12B.fiber_finite (F := F)
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  rw [← e.summable_iff]
  refine (summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
    ⟨fun n => Summable.of_finite, ?_⟩
  refine (lseriesSummable_card (F := F) hσ).norm.congr fun n => ?_
  have hfib : ∀ y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      ((Ideal.absNorm (e ⟨n, y⟩) : ℕ) : ℝ) ^ (-σ) = (n : ℝ) ^ (-σ) := fun y => by
    simp [e, Equiv.sigmaFiberEquiv, y.2]
  simp only [Function.comp_apply, hfib, tsum_const, nsmul_eq_mul, LSeries.norm_term_eq,
    Complex.ofReal_re, Complex.norm_natCast]
  split_ifs with hn
  · subst hn
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero]
  · rw [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

/-! ### Basic facts on Hecke characters -/

/-! ### The Dirichlet series as a sum over ideals -/

/-! ### The finite sieve -/

theorem sieve (g : Ideal (𝓞 F) → ℂ) (hmul : ∀ I J, g (I * J) = g I * g J) (hg : Summable g)
    (T : Finset (Ideal (𝓞 F))) (hT : ∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥) :
    (∑' I, g I) * ∏ P ∈ T, (1 - g P) = ∑' I, (Cop T).indicator g I := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [Cop]
  | insert P T hPT ih =>
    have hP := hT P (Finset.mem_insert_self P T)
    have ih' := ih (fun Q hQ => hT Q (Finset.mem_insert_of_mem hQ))
    rw [Finset.prod_insert hPT, mul_left_comm, mul_comm, ih']
    set h := (Cop T).indicator g with hh
    have hhs : Summable h := hg.indicator _
    have hPI : ∀ I, h (P * I) = g P * h I := by
      intro I
      by_cases hI : I ∈ Cop T
      · have hPI' : P * I ∈ Cop T := by
          intro Q hQ hle
          rcases (hT Q (Finset.mem_insert_of_mem hQ)).1.mul_le.1 hle with h1 | h1
          · have := (hP.1.isMaximal hP.2).eq_of_le (hT Q (Finset.mem_insert_of_mem hQ)).1.ne_top h1
            exact hPT (this ▸ hQ)
          · exact hI Q hQ h1
        rw [hh, Set.indicator_of_mem hPI', Set.indicator_of_mem hI, hmul]
      · have hPI' : P * I ∉ Cop T := by
          intro hc
          simp only [Cop, Set.mem_setOf_eq, not_forall, not_not] at hI
          obtain ⟨Q, hQ, hle⟩ := hI
          exact hc Q hQ (Ideal.mul_le_right.trans hle)
        rw [hh, Set.indicator_of_notMem hPI', Set.indicator_of_notMem hI, mul_zero]
    have hshift : g P * ∑' I, h I = ∑' J, {J | J ≤ P}.indicator h J := by
      rw [← hhs.tsum_mul_left]
      have hinj : Function.Injective (fun I : Ideal (𝓞 F) => P * I) := by
        intro a b hab
        have hP0 : P ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hP.2
        exact mul_left_cancel₀ hP0 hab
      rw [← hinj.tsum_eq (f := {J | J ≤ P}.indicator h)]
      · congr 1
        funext I
        rw [Set.indicator_of_mem (show P * I ∈ {J | J ≤ P} from Ideal.mul_le_left), hPI]
      · intro J hJ
        have hle : J ≤ P := by
          by_contra hc
          exact hJ (Set.indicator_of_notMem hc _)
        obtain ⟨c, rfl⟩ := Ideal.dvd_iff_le.2 hle
        exact ⟨c, rfl⟩
    rw [mul_sub, mul_one, mul_comm, hshift, ← hhs.tsum_sub (hhs.indicator _)]
    congr 1
    funext J
    simp only [hh, Set.indicator, Cop, Set.mem_setOf_eq, Finset.mem_insert, forall_eq_or_imp]
    by_cases h1 : J ≤ P <;> by_cases h2 : ∀ Q ∈ T, ¬J ≤ Q <;> simp [h1, h2]

theorem primesOf_spec (S : Finset (Ideal (𝓞 F))) :
    (∀ P ∈ primesOf S, P.IsPrime ∧ P ≠ ⊥) ∧
      ∀ I ∈ S, I ≠ ⊤ → I ≠ ⊥ → ∃ P ∈ primesOf S, I ≤ P := by
  classical
  constructor
  · intro P hP
    simp only [primesOf, Finset.mem_image, Finset.mem_filter] at hP
    obtain ⟨I, ⟨-, hI, hI0⟩, rfl⟩ := hP
    rw [dif_pos hI]
    obtain ⟨hM, hle⟩ := (Ideal.exists_le_maximal I hI).choose_spec
    refine ⟨hM.isPrime, fun hb => hI0 ?_⟩
    rw [hb] at hle
    exact le_bot_iff.1 hle
  · intro I hI hIt hIb
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hI, hIt, hIb⟩), ?_⟩
    simp only [dif_pos hIt]
    exact (Ideal.exists_le_maximal I hIt).choose_spec.2

theorem sieve_bound (g : Ideal (𝓞 F) → ℂ) (hmul : ∀ I J, g (I * J) = g I * g J)
    (h0 : g ⊥ = 0) (h1 : g ⊤ = 1) (f : Ideal (𝓞 F) → ℝ) (hf : Summable f)
    (hgf : ∀ I, ‖g I‖ ≤ f I) (S : Finset (Ideal (𝓞 F))) :
    ‖(∑' I, g I) * ∏ P ∈ primesOf S, (1 - g P) - 1‖ ≤ ∑' I : {I // I ∉ S}, f I := by
  classical
  have hg : Summable g := Summable.of_norm_bounded hf hgf
  obtain ⟨hT, hcov⟩ := primesOf_spec S
  rw [sieve g hmul hg _ hT]
  have hite : Summable (fun I : Ideal (𝓞 F) => if I = ⊤ then (1 : ℂ) else 0) :=
    (hasSum_ite_eq ⊤ (1 : ℂ)).summable
  have hf0 : ∀ I, 0 ≤ f I := fun I => (norm_nonneg _).trans (hgf I)
  have hpt : ∀ I, ‖(Cop (primesOf S)).indicator g I - (if I = ⊤ then (1 : ℂ) else 0)‖ ≤
      ({I | I ∉ S} : Set (Ideal (𝓞 F))).indicator f I := by
    intro I
    by_cases hIt : I = ⊤
    · subst hIt
      have : (⊤ : Ideal (𝓞 F)) ∈ Cop (primesOf S) := fun P hP hle =>
        (hT P hP).1.ne_top (top_le_iff.1 hle)
      rw [Set.indicator_of_mem this, h1, if_pos rfl, sub_self, norm_zero]
      exact Set.indicator_nonneg (fun I _ => hf0 I) _
    rw [if_neg hIt, sub_zero]
    by_cases hS : I ∈ S
    · rw [Set.indicator_of_notMem (show I ∉ {I | I ∉ S} from fun h => h hS)]
      by_cases hIb : I = ⊥
      · subst hIb
        rw [norm_le_zero_iff]
        simp [Set.indicator, h0]
      · obtain ⟨P, hP, hle⟩ := hcov I hS hIt hIb
        have hn : I ∉ Cop (primesOf S) := by
          intro h
          simp only [Cop, Set.mem_setOf_eq] at h
          exact h P hP hle
        rw [Set.indicator_of_notMem hn, norm_zero]
    · rw [Set.indicator_of_mem (show I ∈ {I | I ∉ S} from hS)]
      exact (norm_indicator_le_norm_self _ _).trans (hgf I)
  rw [← tsum_ite_eq (⊤ : Ideal (𝓞 F)) (fun _ => (1 : ℂ)), ← (hg.indicator _).tsum_sub hite]
  have hsn : Summable (fun I => ‖(Cop (primesOf S)).indicator g I -
      (if I = ⊤ then (1 : ℂ) else 0)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hf.indicator _)
  refine (norm_tsum_le_tsum_norm hsn).trans ?_
  refine (hsn.tsum_le_tsum hpt (hf.indicator _)).trans_eq ?_
  exact (tsum_subtype {I | I ∉ S} f).symm

/-- A finite set outside of which the tail of `f` is small. -/
theorem exists_tail_lt (f : Ideal (𝓞 F) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset (Ideal (𝓞 F)), ∑' I : {I // I ∉ S}, f I < ε :=
  ((tendsto_tsum_compl_atTop_zero f).eventually (gt_mem_nhds hε)).exists

end T12B

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3P_Zeta
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # C3P_Zeta: the incomplete Dedekind zeta function `ζ^S`

`ζ^S(s) = ∏_{P ⊇ 𝔪}(1 − N P^{-s}) ζ_F(s) = R(s)/(s − 1)` with `R` entire, `R(1) = R_S`
(`sZetaResidue`), and `‖R(s)‖ ≤ C (2 + |Im s|)^k` on `9/10 ≤ Re s ≤ 12`. From 8087d96f
(`(s − 1) ζ_K` entire), 4f76b464 (convexity bound for `(s − 1) ζ_{K,T}`, here with `T = ∅`), the
Euler product 4d2ff9db, and Mathlib's class number formula; a field in an arbitrary universe is
replaced by a `Type` model. -/

set_option maxHeartbeats 1000000

open NumberField Complex Filter Topology

namespace ArtinPrimitiveRoots

namespace C3P

universe u

theorem exists_small_model (F : Type u) [Field F] [NumberField F] :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : NumberField F₀), Nonempty (F₀ ≃+* F) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ F
  have hint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  haveI : Fact (Irreducible (minpoly ℚ α)) := ⟨minpoly.irreducible hint⟩
  let e : AdjoinRoot (minpoly ℚ α) ≃ₐ[ℚ] F :=
    (IntermediateField.adjoinRootEquivAdjoin ℚ hint).trans
      ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)
  haveI : FiniteDimensional ℚ (AdjoinRoot (minpoly ℚ α)) :=
    LinearEquiv.finiteDimensional e.toLinearEquiv.symm
  haveI : NumberField (AdjoinRoot (minpoly ℚ α)) := { }
  exact ⟨_, inferInstance, inferInstance, ⟨e.toRingEquiv⟩⟩

theorem card_absNorm_eq_congr {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] (e : K₁ ≃+* K₂) (n : ℕ) :
    Nat.card {I : Ideal (𝓞 K₁) // Ideal.absNorm I = n} =
      Nat.card {I : Ideal (𝓞 K₂) // Ideal.absNorm I = n} := by
  set f : 𝓞 K₁ ≃+* 𝓞 K₂ := RingOfIntegers.mapRingEquiv e
  have hnorm : ∀ I : Ideal (𝓞 K₁), Ideal.absNorm (I.map f) = Ideal.absNorm I := by
    intro I
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv I (I.map f) f rfl).toEquiv).symm
  have h1 : ∀ I : Ideal (𝓞 K₁), (I.map f).map f.symm = I := fun I => Ideal.map_of_equiv f
  have h2 : ∀ J : Ideal (𝓞 K₂), (J.map f.symm).map f = J := fun J => by
    have := Ideal.map_of_equiv (I := J) f.symm; rwa [RingEquiv.symm_symm] at this
  refine Nat.card_congr
    { toFun := fun I => ⟨I.1.map f, by rw [hnorm]; exact I.2⟩
      invFun := fun J => ⟨J.1.map f.symm, by rw [← hnorm, h2]; exact J.2⟩
      left_inv := fun I => Subtype.ext (h1 I.1)
      right_inv := fun J => Subtype.ext (h2 J.1) }

theorem dedekindZeta_congr {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] (e : K₁ ≃+* K₂) : dedekindZeta K₁ = dedekindZeta K₂ := by
  funext s
  unfold dedekindZeta
  congr 1
  funext n
  rw [card_absNorm_eq_congr e n]

/-- `(s − 1) ζ_F` continued: entire, with value the residue at 1 and polynomial growth on
`−1/2 ≤ Re s ≤ 5/2`. -/
theorem exists_R0 (F : Type u) [Field F] [NumberField F] :
    ∃ R0 : ℂ → ℂ, Differentiable ℂ R0 ∧ (∀ s : ℂ, 1 < s.re → R0 s = (s - 1) * dedekindZeta F s) ∧
      R0 1 = (dedekindZeta_residue F : ℂ) ∧
      ∃ C A : ℝ, 0 < A ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 5 / 2 → ‖R0 s‖ ≤ C * (2 + |s.im|) ^ A := by
  obtain ⟨F₀, _, _, ⟨e⟩⟩ := exists_small_model F
  have hζ : dedekindZeta F₀ = dedekindZeta F := dedekindZeta_congr e
  obtain ⟨R0, hR0, -, hR0eq, -⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
      F₀
  refine ⟨R0, hR0, fun s hs => by rw [hR0eq s hs, hζ], ?_, ?_⟩
  · -- the residue, by uniqueness of limits along real `s → 1⁺`
    have h1 : Tendsto (fun s : ℝ => R0 s) (𝓝[>] 1) (𝓝 (R0 1)) := by
      have := ((hR0 1).continuousAt.tendsto).comp
        ((Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1)))
      convert this using 2
      simp
    have h2 := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT F
    refine tendsto_nhds_unique h1 (h2.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hR0eq s (by simpa using hs), hζ]
  · obtain ⟨C, A, -, hA, hb⟩ :=
      NumberField.TateGlobal.exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc
        F₀ ∅
    refine ⟨C, A, hA, hb R0 hR0 fun s hs => ?_⟩
    rw [hR0eq s hs]
    congr 1
    have hp := NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta F₀ s hs
    rw [← hp.tprod_eq]
    exact ((Equiv.subtypeUnivEquiv (fun v => Finset.notMem_empty v)).tprod_eq
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F₀) =>
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)).symm

/-- `‖ζ_F(s)‖` is bounded on `Re s ≥ 5/2`. -/
theorem exists_dedekindZeta_bound (F : Type*) [Field F] [NumberField F] :
    ∃ B : ℝ, ∀ s : ℂ, 5 / 2 ≤ s.re → ‖dedekindZeta F s‖ ≤ B := by
  set f : ℕ → ℂ := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)
  have hs0 : LSeriesSummable f ((5 / 2 : ℝ) : ℂ) := T12B.lseriesSummable_card (by norm_num)
  refine ⟨∑' n, ‖LSeries.term f ((5 / 2 : ℝ) : ℂ) n‖, fun s hs => ?_⟩
  have hre : ((5 / 2 : ℝ) : ℂ).re ≤ s.re := by simpa using hs
  have hss : LSeriesSummable f s := hs0.of_re_le_re hre
  unfold dedekindZeta
  refine (norm_tsum_le_tsum_norm hss.norm).trans ?_
  exact hss.norm.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re f hre n) hs0.norm

/-- The package for `ζ^S`. -/
theorem zetaS_package {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ R : ℂ → ℂ, Differentiable ℂ R ∧ (∀ s : ℂ, 1 < s.re → zetaS 𝔪 s = R s / (s - 1)) ∧
      R 1 = (sZetaResidue 𝔪 : ℂ) ∧
      ∃ C k : ℝ, 0 ≤ k ∧ ∀ s : ℂ, 9 / 10 ≤ s.re → s.re ≤ 12 → ‖R s‖ ≤ C * (2 + |s.im|) ^ k := by
  classical
  obtain ⟨R0, hR0, hR0eq, hR01, C, A, hA, hC⟩ := exists_R0 F
  obtain ⟨B₀, hB₀⟩ := exists_dedekindZeta_bound F
  set B := max B₀ 0
  have hB : ∀ s : ℂ, 5 / 2 ≤ s.re → ‖dedekindZeta F s‖ ≤ B := fun s hs =>
    (hB₀ s hs).trans (le_max_left _ _)
  have hfin := finite_primes_ge h𝔪
  set T := hfin.toFinset with hT
  have hTmem : ∀ P, P ∈ T ↔ P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P := fun P => by simp [hT]
  have hN0 : ∀ P ∈ T, (Ideal.absNorm P : ℂ) ≠ 0 := fun P hP => by
    have := ((hTmem P).1 hP).2.1
    exact_mod_cast (by rwa [Ne, Ideal.absNorm_eq_zero_iff] : Ideal.absNorm P ≠ 0)
  have hN1 : ∀ P ∈ T, (1 : ℝ) ≤ Ideal.absNorm P := fun P hP => by
    have := ((hTmem P).1 hP).2.1
    have : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  set E : ℂ → ℂ := fun s => ∏ P ∈ T, (1 - (Ideal.absNorm P : ℂ) ^ (-s))
  have hE : ∀ s, (∏ᶠ P ∈ {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P},
      (1 - (Ideal.absNorm P : ℂ) ^ (-s))) = E s := fun s =>
    finprod_mem_eq_finite_toFinset_prod _ hfin
  have hEd : Differentiable ℂ E := by
    intro s
    refine DifferentiableAt.fun_finsetProd fun P hP => ?_
    exact (differentiableAt_const _).sub
      ((differentiableAt_id.neg).const_cpow (Or.inl (hN0 P hP)))
  have hEb : ∀ s : ℂ, 0 ≤ s.re → ‖E s‖ ≤ 2 ^ T.card := by
    intro s hs
    refine (Finset.norm_prod_le _ _).trans ?_
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun P hP => ?_
    refine (norm_sub_le _ _).trans ?_
    have hP1 := hN1 P hP
    have : ‖(Ideal.absNorm P : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [show ((Ideal.absNorm P : ℕ) : ℂ) = ((Ideal.absNorm P : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hP1 (by simp; linarith)
    rw [norm_one]; linarith
  refine ⟨fun s => E s * R0 s, hEd.mul hR0, ?_, ?_, ?_⟩
  · intro s hs
    have hs1 : s - 1 ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0; simp at this; linarith
    rw [zetaS, hE]
    show E s * dedekindZeta F s = E s * R0 s / (s - 1)
    rw [hR0eq s hs]
    field_simp
  · simp only
    rw [hR01, sZetaResidue, finprod_mem_eq_finite_toFinset_prod _ hfin]
    push_cast
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [Complex.cpow_neg_one]
  · refine ⟨2 ^ T.card * max (max C 0) (11 * B), max A 1, by positivity, fun s h1 h2 => ?_⟩
    have hb1 : (1 : ℝ) ≤ 2 + |s.im| := by linarith [abs_nonneg s.im]
    rw [norm_mul]
    have hEs := hEb s (by linarith)
    have hRs : ‖R0 s‖ ≤ max (max C 0) (11 * B) * (2 + |s.im|) ^ max A 1 := by
      rcases le_total s.re (5 / 2) with h3 | h3
      · refine (hC s (by linarith) h3).trans ?_
        have : (2 + |s.im|) ^ A ≤ (2 + |s.im|) ^ max A 1 :=
          Real.rpow_le_rpow_of_exponent_le hb1 (le_max_left _ _)
        calc C * (2 + |s.im|) ^ A ≤ max C 0 * (2 + |s.im|) ^ A := by
              gcongr; exact le_max_left _ _
          _ ≤ max (max C 0) (11 * B) * (2 + |s.im|) ^ max A 1 :=
              mul_le_mul (le_max_left _ _) this (by positivity)
                (le_trans (by positivity) (le_max_left _ _))
      · have hs1 : 1 < s.re := by linarith
        rw [hR0eq s hs1, norm_mul]
        have hz := hB s h3
        have hB0 : 0 ≤ B := (norm_nonneg _).trans hz
        have hsn : ‖s - 1‖ ≤ 11 * (2 + |s.im|) := by
          refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
          simp only [sub_re, one_re, sub_im, one_im, sub_zero]
          rw [abs_of_nonneg (by linarith)]
          linarith [abs_nonneg s.im]
        have hp : (2 + |s.im|) ≤ (2 + |s.im|) ^ max A 1 := by
          conv_lhs => rw [← Real.rpow_one (2 + |s.im|)]
          exact Real.rpow_le_rpow_of_exponent_le hb1 (le_max_right _ _)
        calc ‖s - 1‖ * ‖dedekindZeta F s‖ ≤ (11 * (2 + |s.im|)) * B := by gcongr
          _ = (11 * B) * (2 + |s.im|) := by ring
          _ ≤ max (max C 0) (11 * B) * (2 + |s.im|) ^ max A 1 := by
              gcongr
              · exact le_max_right _ _
    calc ‖E s‖ * ‖R0 s‖ ≤ 2 ^ T.card * (max (max C 0) (11 * B) * (2 + |s.im|) ^ max A 1) := by
          gcongr
      _ = _ := by ring

end C3P

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.Z_Series
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # Z_Series: the constant-term Dirichlet series `∑ φ(𝔞³) N(𝔞³)^{-s} = ζ^S(3s-3)/ζ^S(3s-2)`

`ζ^S = C3P.zetaS 𝔪` (Dedekind zeta with the Euler factors at the primes over `𝔪` removed).

* `Z.zetaS_eq_tsum`: `ζ^S(w) = ∑_{𝔞 exterior} N𝔞^{-w}` for `Re w > 1`.
* `Z.zetaS_ne_zero`: `ζ^S(w) ≠ 0` for `Re w > 1`.
* `Z.tsum_phi`: `∑_{𝔞 exterior} φ(𝔞) N𝔞^{-w} = ζ^S(w-1)/ζ^S(w)` for `Re w > 2`.
* `Z.tsum_cubeTerm`, `Z.summable_cubeTerm`: the cube form, `Re s > 4/3`.
* `Z.tsum_G0`: the same as a sum over exterior ideals `𝔠` of `G₀(𝔠) N𝔠^{-s}`,
  `G₀(𝔠) = φ(𝔠)·1[𝔠 is a cube]` (MATH2 §3.1).
-/

set_option autoImplicit false

open NumberField ArtinPrimitiveRoots

namespace ArtinKP

namespace Z

variable {F : Type*} [Field F] [NumberField F]

lemma nrm_bot {w : ℂ} (hw : 0 < w.re) : nrm w (⊥ : Ideal (𝓞 F)) = 0 := by
  rw [nrm, Ideal.absNorm_bot, Nat.cast_zero, Complex.zero_cpow]
  intro h
  rw [neg_eq_zero.1 h, Complex.zero_re] at hw
  exact lt_irrefl _ hw

lemma nrm_mul (w : ℂ) (I J : Ideal (𝓞 F)) : nrm w (I * J) = nrm w I * nrm w J := by
  simp only [nrm, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]

lemma norm_nrm {w : ℂ} {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    ‖nrm w I‖ = (Ideal.absNorm I : ℝ) ^ (-w.re) := by
  rw [nrm, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (absNorm_ne_zero hI)),
    Complex.neg_re]

lemma norm_nrm_le {w : ℂ} (hw : 0 < w.re) (I : Ideal (𝓞 F)) :
    ‖nrm w I‖ ≤ (Ideal.absNorm I : ℝ) ^ (-w.re) := by
  by_cases hI : I = ⊥
  · rw [hI, nrm_bot hw, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact (norm_nrm hI).le

lemma summable_norm_nrm {w : ℂ} (hw : 1 < w.re) :
    Summable (fun I : Ideal (𝓞 F) => ‖nrm w I‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_nrm_le (by linarith))
    (T12B.summable_absNorm_rpow hw)

/-- `ζ_F(w) = ∑_I N(I)^{-w}` on `Re w > 1`. -/
theorem dedekindZeta_eq_tsum {w : ℂ} (hw : 1 < w.re) :
    dedekindZeta F w = ∑' I : Ideal (𝓞 F), nrm w I := by
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  have hsum : Summable (fun I : Ideal (𝓞 F) => nrm w I) := (summable_norm_nrm hw).of_norm
  have hs2 : Summable (fun p => nrm w (e p)) := (e.summable_iff).2 hsum
  rw [← e.tsum_eq, hs2.tsum_sigma, dedekindZeta, LSeries]
  congr 1
  funext n
  have hfib : ∀ y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      nrm w (e ⟨n, y⟩) = (n : ℂ) ^ (-w) := fun y => by
    simp [e, Equiv.sigmaFiberEquiv, nrm, y.2]
  simp only [hfib]
  rw [tsum_const, nsmul_eq_mul]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, Nat.cast_zero, Complex.zero_cpow, mul_zero]
    intro h
    rw [neg_eq_zero.1 h, Complex.zero_re] at hw
    linarith
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

lemma mem_cop_iff {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    I ∈ T12B.Cop (C3P.finite_primes_ge h𝔪).toFinset ↔ I ∈ Ext 𝔪 := by
  constructor
  · intro h
    refine ⟨hI, ?_⟩
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    have hmP : 𝔪 ≤ P := le_sup_right.trans hle
    have hP0 : P ≠ ⊥ := fun h0 => h𝔪 (le_bot_iff.1 (h0 ▸ hmP))
    exact h P ((Set.Finite.mem_toFinset _).2 ⟨hP.isPrime, hP0, hmP⟩) (le_sup_left.trans hle)
  · rintro ⟨-, hsup⟩ P hP hIP
    obtain ⟨hPp, -, hmP⟩ := (Set.Finite.mem_toFinset _).1 hP
    exact hPp.ne_top (top_le_iff.1 (hsup ▸ sup_le hIP hmP))

/-- `ζ^S(w) = ∑_{𝔞 exterior} N𝔞^{-w}` for `Re w > 1`. -/
theorem zetaS_eq_tsum {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {w : ℂ} (hw : 1 < w.re) :
    C3P.zetaS 𝔪 w = ∑' I : Ideal (𝓞 F), (Ext 𝔪).indicator (nrm w) I := by
  classical
  have hfin := C3P.finite_primes_ge h𝔪
  have hsieve := T12B.sieve (nrm w) (nrm_mul w) (summable_norm_nrm hw).of_norm hfin.toFinset
    (fun P hP => by
      obtain ⟨h1, h2, -⟩ := (Set.Finite.mem_toFinset _).1 hP
      exact ⟨h1, h2⟩)
  rw [C3P.zetaS, finprod_mem_eq_finite_toFinset_prod _ hfin, mul_comm, dedekindZeta_eq_tsum hw]
  refine hsieve.trans (tsum_congr fun I => ?_)
  by_cases hI : I = ⊥
  · have h0 : nrm w (⊥ : Ideal (𝓞 F)) = 0 := nrm_bot (by linarith)
    rw [hI, Set.indicator_apply, Set.indicator_apply]
    split_ifs <;> simp [h0]
  · by_cases hE : I ∈ Ext 𝔪
    · rw [Set.indicator_of_mem hE, Set.indicator_of_mem ((mem_cop_iff h𝔪 hI).2 hE)]
    · rw [Set.indicator_of_notMem hE,
        Set.indicator_of_notMem (fun h => hE ((mem_cop_iff h𝔪 hI).1 h))]

lemma two_le_absNorm {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    2 ≤ Ideal.absNorm P := by
  have h0 := absNorm_ne_zero hP0
  have h1 : Ideal.absNorm P ≠ 1 := fun h => hP.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

/-- `ζ_F(w) ≠ 0` on `Re w > 1` (finite sieve; no platform import). -/
theorem dedekindZeta_ne_zero {w : ℂ} (hw : 1 < w.re) : dedekindZeta F w ≠ 0 := by
  have hw0 : 0 < w.re := by linarith
  obtain ⟨S, hS⟩ := T12B.exists_tail_lt
    (fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℝ) ^ (-w.re)) one_pos
  have hb := T12B.sieve_bound (nrm w) (nrm_mul w) (nrm_bot hw0)
    (by simp [nrm]) _ (T12B.summable_absNorm_rpow hw) (norm_nrm_le hw0) S
  intro h0
  rw [← dedekindZeta_eq_tsum hw, h0, zero_mul, zero_sub, norm_neg, norm_one] at hb
  linarith

/-- `ζ^S(w) ≠ 0` on `Re w > 1`. -/
theorem zetaS_ne_zero {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {w : ℂ} (hw : 1 < w.re) :
    C3P.zetaS 𝔪 w ≠ 0 := by
  classical
  have hfin := C3P.finite_primes_ge h𝔪
  rw [C3P.zetaS, finprod_mem_eq_finite_toFinset_prod _ hfin]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun P hP => ?_)
    (dedekindZeta_ne_zero hw)
  obtain ⟨hPp, hP0, -⟩ := (Set.Finite.mem_toFinset _).1 hP
  intro h
  have h1 : ‖nrm w P‖ = 1 := by
    rw [nrm, ← sub_eq_zero.1 h, norm_one]
  rw [norm_nrm hP0] at h1
  have h2 : (1 : ℝ) < Ideal.absNorm P := by exact_mod_cast two_le_absNorm hPp hP0
  have := Real.rpow_lt_one_of_one_lt_of_neg h2 (by linarith : -w.re < 0)
  linarith

/-! ### The cube form -/

/-! ### The form `∑_𝔠 G₀(𝔠) N𝔠^{-s}` of MATH2 §3.1 -/

end Z

end ArtinKP
end

section
-- module Solutions.Artin.T12.L2B_Orth
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# L2B_Orth: `#(R/𝔰R) = q_𝔰`, primitivity and orthogonality of `j ↦ e(j k / s)`

* `natCard_quot_eq`: `#(R/𝔰R) = N 𝔰` for exterior `𝔰`;
* `exists_primePow_not_mem`: `k ∉ 𝔰R` ⇒ `k ∉ P^a R` for a prime power `P^a ∣ 𝔰`;
* `exists_sAddChar_ne_one_gen`: primitivity of `j ↦ e(j k / s)` for `k ∉ 𝔰R`;
* `finsum_sAddChar`: `∑_{j mod 𝔰} e(j k / s) = q_𝔰 [k ∈ 𝔰R]`.
-/

namespace ArtinPrimitiveRoots.L2B

open NumberField IsDedekindDomain UniqueFactorizationMonoid

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

theorem natCard_quot_eq {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) :
    Nat.card (SInt 𝔪 ⧸ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) = Ideal.absNorm 𝔞 := by
  have hbij : Function.Bijective (C3I.quotHom 𝔪 𝔞) := by
    refine ⟨?_, quotHom_surjective 𝔞 h𝔞.2⟩
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [C3I.quotHom_mk, Ideal.Quotient.eq_zero_iff_mem] at hy
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact mem_of_map_mem 𝔞 h𝔞.2 a hy
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Ideal.absNorm_apply, Submodule.cardQuot_apply]

end ArtinPrimitiveRoots.L2B
end

section
-- module Solutions.Artin.KP.B_Norm
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-B, part 3: the norm of an `S`-integer

* `extOf h𝔪 hc`: the exterior ideal `𝔠 ⊂ 𝓞` with `𝔠R = cR`, for `c ∈ R ∖ 0`.
* `natCard_quot_span`: `#(R/cR) = N𝔠`.
* **Product formula** `Ninf_mul_absS_eq`: `N_∞(c) · |c|_{S_f} = #(R/cR)` for `c ∈ R ∖ 0`
  (class-number trick: `𝔠^h` is principal in `𝓞`).
* `summable_nrm_rpow`: `∑_{c ∈ (R∖0)/Rˣ} #(R/cR)^{-t} < ∞` for `t > 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem extOf_isExterior (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) :
    IsExterior 𝔪 (extOf h𝔪 hc) := (exists_ext h𝔪 hc).choose_spec.1

theorem map_extOf (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) :
    (extOf h𝔪 hc).map (algebraMap (𝓞 F) (SInt 𝔪)) = Ideal.span {c} :=
  (exists_ext h𝔪 hc).choose_spec.2

/-- `#(R/cR) = N𝔠`. -/
theorem natCard_quot_span (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) :
    Nat.card (SInt 𝔪 ⧸ Ideal.span {c}) = Ideal.absNorm (extOf h𝔪 hc) := by
  rw [← map_extOf h𝔪 hc]
  exact L2B.natCard_quot_eq (extOf_isExterior h𝔪 hc)

theorem isExterior_pow {𝔄 : Ideal (𝓞 F)} (h : IsExterior 𝔪 𝔄) (n : ℕ) : IsExterior 𝔪 (𝔄 ^ n) :=
  ⟨pow_ne_zero n h.1,
    Ideal.isCoprime_iff_sup_eq.1 ((Ideal.isCoprime_iff_sup_eq.2 h.2).pow_left)⟩

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_FourThm
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-B, part 8: the Fourier expansion at `∞` — statements

For a genuine section `Φ`, `Re s > 2`, `ν ∈ R`, a depth `M` valid for `(Φ, ν)`
(`ValidDepth hG Φ ν M`), and any fundamental cell `D` of finite volume of the translation
lattice `Λ_M = transLat 𝔪 M = emb (R ∩ 𝔩_M) ⊂ ℂ^r`:

* `fourier_coeff` (all `ν`), `fourier_coeff_ne_zero` (`ν ≠ 0`), `const_term` (`ν = 0`).

Normalizations: `chiInf ν x = conj e_∞(νx)`, `e_∞(x) = ∏_w archChar (-x_w)` (so
`e_∞ = exp(-2πi Tr)` on `F`); `dx` is Lebesgue measure on `ℂ^r = (ℝ²)^r`;
`Winf s ν v = ∏_w jacquet s (-σ_w ν) v_w`; `vol 𝔪 M = ∏_{v ∣ 𝔪} q_v^{-M}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate Pointwise
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

instance instCountableIdxI (M : ℤ) : Countable (IdxI 𝔪 M) := by
  haveI _iCF := ArtinKP.B1.instCountableField (F := F)
  have : Countable (Associates (SInt 𝔪)) := Associates.mk_surjective.countable
  have : ∀ c : SInt 𝔪, Countable (SInt 𝔪 ⧸ Ideal.span {c}) := fun c =>
    Ideal.Quotient.mk_surjective.countable
  have : Countable (F ⧸ lat 𝔪 M) := QuotientAddGroup.mk_surjective.countable
  infer_instance

/-! ### Characters on the cell -/

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (s : ℂ) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (M : ℤ)

theorem Winf_zero {s : ℂ} (hs : 1 < s.re) {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) :
    Winf s (0 : F) v = ((Real.pi : ℂ) / (s - 1)) ^ Fintype.card (InfinitePlace F)
      * ((∏ w, v w : ℝ) : ℂ) ^ (2 - s) := by
  rw [Winf, cpow_prod_nonneg _ _ (fun w => (hv w).le)]
  simp only [map_zero, neg_zero]
  rw [Finset.prod_congr rfl fun w _ => jacquet_zero s hs (hv w), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]

include hz6 in
/-- **The constant term** (MATH2 §0.2 (B6)):
`∫_D E = vol(D) Φ_s(0,1) ht^s + vol(𝔩_M)⁻¹ (π/(s-1))^r ht^{2-s} ∑_c g(0,c) λ(c;0,s) N(c)^{-s}`. -/
theorem const_term (hV : ValidDepth hG Φ ((0 : SInt 𝔪) : F) M) (hs : 2 < s.re)
    {D : Set (InfinitePlace F → ℂ)} (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume)
    (hDfin : volume D ≠ ⊤) :
    ∫ x in D, eis (Φ.twist hG hz6) s (X.mk x v hv)
      = ((volume D).toReal : ℂ) * (Φ s 0 1 * ((∏ w, v w : ℝ) : ℂ) ^ s)
        + ((vol 𝔪 M : ℝ) : ℂ)⁻¹
          * (((Real.pi : ℂ) / (s - 1)) ^ Fintype.card (InfinitePlace F)
            * ((∏ w, v w : ℝ) : ℂ) ^ (2 - s))
          * ∑' a : Cls (SInt 𝔪),
              B7.gauss (S2.cubicSymbol ι P hG hz6) (B7.sAdd 𝔪 hG.ne_bot) 0 (rp a.1)
                * lam (psiS hG.ne_bot) M Φ ((rp a.1 : SInt 𝔪) : F) 0 s * nrm (rp a.1) ^ (-s) := by
  have h := fourier_coeff hG hz6 Φ s v hv M (0 : SInt 𝔪) hV hs hD hDfin
  have h0 : ((0 : SInt 𝔪) : F) = 0 := rfl
  rw [h0] at h
  simp only [chiInf_zero, mul_one] at h
  rw [setIntegral_const, Measure.real, Complex.real_smul, mul_one] at h
  rw [h, Winf_zero (by linarith) hv]
  ring

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.S2_Kubota
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-S2, part 8: the normalized finite Jacquet functional `Lam` and the laws of `E.Kubota`

`Lam ψ hG Φ c ν s := |c|_{S_f}^s · J_Φ(c; ν, s)`, the functional of WP-S (`S.lam`) taken at a
valid depth; by `jacD_eq_of_le` it does not depend on the valid depth (`Lam_eq_lamD`).

* `Lam_unit` (J1), `Lam_cube` (S1³), `Lam_act` (MATH2 Lemma 6.1 (iii), any frequency),
  `torusT_torusT_inv` and `Lam_act_surj`: the laws required by the interface `E.Kubota`.
* `kubota`: the instance `E.Kubota (cubicSymbol …) (B7.sAdd 𝔪 h𝔪) (GSection ι P 𝔪)` with
  `act β = Ã(β)`, **given** its field `summable` as a hypothesis.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

theorem Lam_eq_lam (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {ν : F} {M : ℤ}
    (h : Valid ψ Φ ν (fun _ => M)) (c : F) (s : ℂ) :
    Lam ψ hG Φ c ν s = lam ψ M Φ c ν s :=
  Lam_eq_lamD ψ hG Φ h c s

/-! ### The interface `E.Kubota` -/

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.B_Kub
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-B, part 9: the Kubota series — convergence, holomorphy, the `E.Kubota` instance

* `kTerm`, `aCoeff`: `𝔞_Φ(ν, s) = ∑_{c ∈ (R∖0)/Rˣ} g(ν, c) · Lam Φ c ν s · N(c)^{-s}`, for every
  `ν ∈ R` (`ν = 0` gives the Dirichlet series of the constant term), with
  `Lam = S2.LamR ψ_{S_f}` (WP-S2's normalized finite Jacquet functional at a valid depth).
* `exists_majorant_kTerm`: locally uniform absolute convergence on `Re s > 2`
  (`|g(ν,c)| ≤ N(c)`, `S2.norm_Lam_le`, S-1, `∑ N(c)^{1-σ} < ∞`).
* `differentiableOn_aCoeff`: holomorphy on `Re s > 2`.
* `kubota hG hz6 : E.Kubota (S2.cubicSymbol …) (B7.sAdd 𝔪 _) (GSection ι P 𝔪)` — no hypothesis left.
* `fourier_coeff_aSer`, `const_term_aCoeff`: the Fourier coefficients in this normalization.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K ArtinKP.B7

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable [IsTotallyComplex F] (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (Φ : GSection ι P 𝔪) (ν : SInt 𝔪)

/-- `Lam` is `S.lam` at any valid depth. -/
theorem LamR_eq_lam {M : ℤ} (hV : ValidDepth hG Φ (ν : F) M) (c : SInt 𝔪) (s : ℂ) :
    S2.LamR (psiS hG.ne_bot) hG Φ c ν s = lam (psiS hG.ne_bot) M Φ (c : F) (ν : F) s :=
  S2.Lam_eq_lam (psiS hG.ne_bot) hG Φ ⟨hV.unip, hV.char⟩ (c : F) s

theorem aCoeff_eq {M : ℤ} (hV : ValidDepth hG Φ (ν : F) M) (s : ℂ) :
    aCoeff hG hz6 Φ ν s = ∑' a : Cls (SInt 𝔪),
      gauss (S2.cubicSymbol ι P hG hz6) (sAdd 𝔪 hG.ne_bot) ν (rp a.1)
        * lam (psiS hG.ne_bot) M Φ ((rp a.1 : SInt 𝔪) : F) (ν : F) s * nrm (rp a.1) ^ (-s) :=
  tsum_congr fun a => by rw [kTerm, LamR_eq_lam hG Φ ν hV]

/-- **The constant term of `E_Φ` at `∞`**:
`∫_D E(x, v) dx = vol(D) Φ_s(0,1) ht^s + vol(𝔩_M)⁻¹ m_Φ(s) ht^{2-s}`. -/
theorem const_term_mCoeff {M : ℤ} (hV : ValidDepth hG Φ ((0 : SInt 𝔪) : F) M) {s : ℂ}
    (hs : 2 < s.re) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w)
    {D : Set (InfinitePlace F → ℂ)} (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume)
    (hDfin : volume D ≠ ⊤) :
    ∫ x in D, eis (Φ.twist hG hz6) s (X.mk x v hv)
      = ((volume D).toReal : ℂ) * (Φ s 0 1 * ((∏ w, v w : ℝ) : ℂ) ^ s)
        + ((vol 𝔪 M : ℝ) : ℂ)⁻¹ * (mCoeff hG hz6 Φ s * ((∏ w, v w : ℝ) : ℂ) ^ (2 - s)) := by
  rw [const_term hG hz6 Φ s v hv M hV hs hD hDfin, mCoeff, aCoeff_eq hG hz6 Φ 0 hV]
  have h0 : ((0 : SInt 𝔪) : F) = 0 := rfl
  rw [h0]
  ring

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_Const
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply
/-!
# WP-B, part 10: the sum of big-cell sections over the classes (MATH2 §3.1), first half

`sumBig = ∑_{η ∈ T} bigCell η 𝔩_M` for a complete system `T` of pairwise disjoint classes
(`RO.exists_classReps`).

* `validDepth_sumBig`: `M` is a valid depth for `sumBig` at the frequency `0`.
* `LamR_sumBig`: `Lam Φ^Σ c 0 s = vol(𝔩_M) · ⟨η_c, c⟩` for `c ≠ 0` of class `η_c ∈ T`.
* `brk_of_cube`: `⟨η_c, c⟩ = 1` when `c = u b³` (`u ∈ U_S`): the symbol factor disappears on the
  support of `G₀`.
* `kTerm_sumBig_cube`: the summand of `𝔞_{Φ^Σ}(0, s)` at `c = u b³` is
  `vol(𝔩_M) · φ(c) · N(c)^{-s}` (`φ = B7.phi`).

What remains for `m_{Φ^Σ}` is stated in `B_Stubs.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K ArtinKP.B7

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

theorem supp_add_iff {N : ℕ} {M : ℤ} {η c d b : F} (hc : c ≠ 0) (hb : Small 𝔪 M b) :
    Supp 𝔪 N η M 0 c (d + c * b) ↔ Supp 𝔪 N η M 0 c d := by
  unfold Supp
  have e : (d + c * b) / c - 0 = (d / c - 0) + b := by
    field_simp
    ring
  rw [e]
  exact and_congr_right fun _ => ⟨fun h => by simpa using h.sub hb, fun h => h.add hb⟩

/-- The symbol factor of a big cell is trivial on `U_S · (F^×)³`. -/
theorem brk_of_cube (hG : Good 𝔪) {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) {η c : F}
    (hη : InClass 𝔪 N η c) (u : (SInt 𝔪)ˣ) {b : F} (hb : b ≠ 0)
    (hc : c = ((u : SInt 𝔪) : F) * b ^ 3) : brk ι P 𝔪 η c = 1 := by
  obtain ⟨ε, t, u', ht, hu', hceq⟩ := hη
  have huF : ((u : SInt 𝔪) : F) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
  have hεF : ((ε : SInt 𝔪) : F) ≠ 0 := fun h => ε.ne_zero (Subtype.ext h)
  have hc0 : c ≠ 0 := by rw [hc]; exact mul_ne_zero huF (pow_ne_zero 3 hb)
  have hu'0 : u' ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [hceq, mul_zero])
  have hεε : ((ε : SInt 𝔪) : F) * (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← MulMemClass.coe_mul, ε.mul_inv]
    rfl
  have hinv : (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = ((ε : SInt 𝔪) : F)⁻¹ :=
    eq_inv_of_mul_eq_one_right hεε
  have hw : (((u * ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F)
      = ((u : SInt 𝔪) : F) * ((ε : SInt 𝔪) : F)⁻¹ := by
    rw [← hinv]
    rfl
  have hwF : (((u * ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) ≠ 0 := fun h =>
    (u * ε⁻¹).ne_zero (Subtype.ext h)
  have hη_eq : η = (((u * ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) * (b * t⁻¹) ^ 3 * u'⁻¹ := by
    have key : η * (((ε : SInt 𝔪) : F) * t ^ 3 * u') = ((u : SInt 𝔪) : F) * b ^ 3 := by
      rw [← hc, hceq]
      ring
    rw [hw]
    field_simp
    linear_combination key
  have h1 : brk ι P 𝔪 (((u * ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) c = 1 := by
    rw [hc, brk_mul_right _ huF (pow_ne_zero 3 hb), brk_pow_three_right, mul_one]
    exact brk_sunit hG (unit_val_eq_one (u * ε⁻¹)) (unit_val_eq_one u)
  have h2 : brk ι P 𝔪 ((b * t⁻¹) ^ 3) c = 1 := brk_pow_three_left _ _
  have h3 : brk ι P 𝔪 u'⁻¹ c = 1 :=
    brk_deep_left hG hN c (Small.deep_inv (by exact_mod_cast hN1) hu')
  rw [hη_eq, brk_mul_left _ (mul_ne_zero hwF (pow_ne_zero 3 (mul_ne_zero hb (inv_ne_zero ht))))
    (inv_ne_zero hu'0), brk_mul_left _ hwF (pow_ne_zero 3 (mul_ne_zero hb (inv_ne_zero ht))),
    h1, h2, h3]
  ring

variable [IsTotallyComplex F] (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) (M : ℤ) (T : Finset {η : F // η ≠ 0})
  (hdisj : ∀ η ∈ T, ∀ η' ∈ T, η ≠ η' → ∀ c : F, InClass 𝔪 N η.1 c → ¬ InClass 𝔪 N η'.1 c)
  (hcov : ∀ c : F, c ≠ 0 → ∃ η ∈ T, InClass 𝔪 N η.1 c)

include hdisj in
theorem sumBig_apply {η₀ : {η : F // η ≠ 0}} (hη₀ : η₀ ∈ T) {c : F}
    (hc : InClass 𝔪 N η₀.1 c) (s : ℂ) (d : F) :
    sumBig ι hG hN1 hN M T s c d = bigFun ι P 𝔪 N η₀.1 M 0 s c d :=
  sum_bigCell_apply ι P hG hN1 hN M 0 T hdisj hη₀ hc s d

include hdisj hcov in
/-- `M` is a valid depth for `Φ^Σ` at the frequency `0`. -/
theorem validDepth_sumBig :
    ValidDepth hG (sumBig ι hG hN1 hN M T) ((0 : SInt 𝔪) : F) M where
  unip b hb s c d := by
    by_cases hc : c = 0
    · rw [hc, zero_mul, add_zero]
    obtain ⟨η₀, hη₀, hcl⟩ := hcov c hc
    rw [sumBig_apply hG hN1 hN M T hdisj hη₀ hcl, sumBig_apply hG hN1 hN M T hdisj hη₀ hcl]
    have h := supp_add_iff (N := N) (η := η₀.1) (d := d) hc hb
    simp only [bigFun]
    by_cases hS : Supp 𝔪 N η₀.1 M 0 c d
    · rw [if_pos hS, if_pos (h.mpr hS)]
    · rw [if_neg hS, if_neg fun h' => hS (h.mp h')]
  char h _ := by
    have h0 : ((0 : SInt 𝔪) : F) = 0 := rfl
    rw [h0, zero_mul]
    exact SfChar.map_zero _

include hdisj hcov in
/-- `Lam Φ^Σ c 0 s = vol(𝔩_M) ⟨η_c, c⟩`. -/
theorem LamR_sumBig {c : SInt 𝔪} (hc : c ≠ 0) {η₀ : {η : F // η ≠ 0}} (hη₀ : η₀ ∈ T)
    (hcl : InClass 𝔪 N η₀.1 (c : F)) (s : ℂ) :
    S2.LamR (psiS hG.ne_bot) hG (sumBig ι hG hN1 hN M T) c 0 s
      = ((vol 𝔪 M : ℝ) : ℂ) * brk ι P 𝔪 η₀.1 (c : F) := by
  classical
  have hcF : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  rw [LamR_eq_lam hG _ 0 (validDepth_sumBig hG hN1 hN M T hdisj hcov) c s]
  have h0 : ((0 : SInt 𝔪) : F) = 0 := rfl
  rw [h0, lam]
  have hfun : (fun u => sumBig ι hG hN1 hN M T s (c : F) ((c : F) * u))
      = fun u => if Small 𝔪 M (u - 0)
          then brk ι P 𝔪 η₀.1 (c : F) * ((absS 𝔪 (c : F) : ℝ) : ℂ) ^ (-s) else 0 := by
    funext u
    rw [sumBig_apply hG hN1 hN M T hdisj hη₀ hcl]
    by_cases hu : Small 𝔪 M (u - 0)
    · rw [if_pos hu, bigFun_of_supp ⟨hcl, by rw [mul_div_cancel_left₀ _ hcF]; exact hu⟩]
    · rw [if_neg hu, bigFun_of_not_supp fun h => hu (by
        have := h.2
        rwa [mul_div_cancel_left₀ _ hcF] at this)]
  rw [hfun, jac_indicator (psiS hG.ne_bot) _ 0
    (fun h _ => by rw [zero_mul]; exact SfChar.map_zero _), zero_mul, SfChar.map_zero, map_one,
    mul_one]
  have hcp := S2.cpow_mul_cpow_neg (absS_pos (𝔪 := 𝔪) hcF) s
  linear_combination (((vol 𝔪 M : ℝ) : ℂ) * brk ι P 𝔪 η₀.1 (c : F)) * hcp

include hdisj hcov in
/-- The summand of `𝔞_{Φ^Σ}(0, s)` at a class `a` whose representative is `u b³`:
`vol(𝔩_M) · φ(c) · N(c)^{-s}`. -/
theorem kTerm_sumBig_cube (a : Cls (SInt 𝔪)) (u : (SInt 𝔪)ˣ) {b : SInt 𝔪} (hb : b ≠ 0)
    (hab : rp a.1 = (u : SInt 𝔪) * b ^ 3) (s : ℂ) :
    kTerm hG hz6 (sumBig ι hG hN1 hN M T) 0 a s
      = ((vol 𝔪 M : ℝ) : ℂ) * (phi (rp a.1) * nrm (rp a.1) ^ (-s)) := by
  have hc := rp_ne_zero a.2
  have hcF : ((rp a.1 : SInt 𝔪) : F) ≠ 0 := fun h => hc (Subtype.ext h)
  have hbF : (b : F) ≠ 0 := fun h => hb (Subtype.ext h)
  obtain ⟨η₀, hη₀, hcl⟩ := hcov _ hcF
  have hbrk : brk ι P 𝔪 η₀.1 ((rp a.1 : SInt 𝔪) : F) = 1 :=
    brk_of_cube hG hN1 hN hcl u hbF (by rw [hab]; push_cast; rfl)
  have hg : gauss (S2.cubicSymbol ι P hG hz6) (sAdd 𝔪 hG.ne_bot) 0 (rp a.1) = phi (rp a.1) := by
    rw [gauss_zero_left, hab]
    exact csum_of_cube _ u.isUnit hb
  rw [kTerm, LamR_sumBig hG hN1 hN M T hdisj hcov hc hη₀ hcl, hbrk, hg]
  ring

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.BZ_Char
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply
/-!
# WP-BZ, part 1: the constant-term character sum vanishes off `U_S · R³`

* `exists_sextic_sq_ne_one`: at every exterior prime `v` the cubic residue character `χ_v²` is
  non-trivial.  Only `A.Good 𝔪` and a primitive sixth root of unity in `𝓞 F` are used:
  `6 ∣ N v - 1` for every exterior `v` (`A.sextic_spec`), and the residue field's unit group is
  not killed by `(N v - 1)/3`.  (No `C3I.Good 𝔪 v`: neither `12 ∣ N v - 1` nor the different.)
* `exists_sym_ne_one_of_prime`: for every prime element `π` of `R = SInt 𝔪` there is `d₀` prime to
  `π` with `(d₀/π) ≠ 1`, for `S2.cubicSymbol`.
* `exists_unit_cube_of_csum_ne_zero`, `csum_eq_zero`: `∑_{d mod c} (d/c)⁻¹ = 0` unless
  `c = u b³` with `u ∈ Rˣ` — the hypothesis `hchar` of `B.aCoeff_sumBig`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.BZ

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E ArtinKP.B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- At every exterior prime the cubic residue character `χ_v²` takes a value `≠ 0, 1`. -/
theorem exists_sextic_sq_ne_one (ι : F →+* ℂ) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) :
    ∃ d : SInt 𝔪, sexticResidueSymbol ι 𝔪 v.asIdeal d ^ 2 ≠ 1 ∧
      sexticResidueSymbol ι 𝔪 v.asIdeal d ≠ 0 := by
  classical
  obtain ⟨p, hp⟩ := (hG.principal v.asIdeal).principal
  have hp' : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := hp.symm
  have h6 := hG.six_notMem v hv
  let _ : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  let _ : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have h6N : 6 ∣ Ideal.absNorm v.asIdeal - 1 :=
    (sextic_spec ι v hv p hp' hz6 h6 1 (by
      have : ((1 : SInt 𝔪) : F) = 1 := rfl
      rw [this, map_one])).1
  have hN2 : 2 ≤ Ideal.absNorm v.asIdeal := Z.two_le_absNorm v.isPrime v.ne_bot
  obtain ⟨k, hk⟩ := h6N
  have hk1 : 1 ≤ k := by omega
  have hk6 : (Ideal.absNorm v.asIdeal - 1) / 6 = k := by omega
  have hnd : ¬ (Fintype.card (𝓞 F ⧸ v.asIdeal) - 1 ∣ k * 2) := by
    rw [hcard]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hex : ∃ x : (𝓞 F ⧸ v.asIdeal)ˣ, x ^ (k * 2) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hnd ((FiniteField.forall_pow_eq_one_iff (𝓞 F ⧸ v.asIdeal) (k * 2)).1 hcon)
  obtain ⟨x, hx⟩ := hex
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (x : 𝓞 F ⧸ v.asIdeal)
  have hyP : y ∉ v.asIdeal := by
    intro h
    have h0 : (x : 𝓞 F ⧸ v.asIdeal) = 0 := by
      rw [← hy]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h
    exact x.ne_zero h0
  have hdF : ((algebraMap (𝓞 F) (SInt 𝔪) y : SInt 𝔪) : F) = algebraMap (𝓞 F) F y := rfl
  have hval : v.valuation F ((algebraMap (𝓞 F) (SInt 𝔪) y : SInt 𝔪) : F) = 1 := by
    rw [hdF, HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact hyP
  obtain ⟨-, ξ, hξ6, hlt, hsym⟩ :=
    sextic_spec ι v hv p hp' hz6 h6 (algebraMap (𝓞 F) (SInt 𝔪) y) hval
  have hξ0 : ι (algebraMap (𝓞 F) F ξ) ≠ 0 := by
    intro h0
    have : ι (algebraMap (𝓞 F) F ξ) ^ 6 = 1 := by
      rw [← map_pow, ← map_pow, hξ6, map_one, map_one]
    rw [h0] at this
    norm_num at this
  refine ⟨algebraMap (𝓞 F) (SInt 𝔪) y, ?_, by rw [hsym]; exact hξ0⟩
  rw [hsym, ← map_pow]
  intro h1
  have hξ2 : algebraMap (𝓞 F) F ξ ^ 2 = 1 := ι.injective (by rw [h1, map_one])
  have hξ2' : ξ ^ 2 = 1 :=
    FaithfulSMul.algebraMap_injective (𝓞 F) F (by rw [map_pow, hξ2, map_one])
  have hmem : y ^ k - ξ ∈ v.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F)]
    rw [hk6, hdF] at hlt
    have e : (((y ^ k - ξ : 𝓞 F)) : F) = algebraMap (𝓞 F) F y ^ k - algebraMap (𝓞 F) F ξ := by
      push_cast
      rfl
    rw [← e] at hlt
    exact hlt
  apply hx
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, ← hy, pow_mul, ← map_pow,
    (Ideal.Quotient.eq.mpr hmem : Ideal.Quotient.mk v.asIdeal (y ^ k) = Ideal.Quotient.mk _ ξ),
    ← map_pow, hξ2', map_one]

variable (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- A prime element of `R` generates the extension of an exterior prime of `𝓞`. -/
theorem exists_place_of_prime (h𝔪 : 𝔪 ≠ ⊥) {π : SInt 𝔪} (hπ : Prime π) :
    ∃ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal ∧ IsExterior 𝔪 v.asIdeal ∧
      Ideal.span {π} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  have hJ : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  set Q : Ideal (𝓞 F) := (Ideal.span {π}).comap (algebraMap (𝓞 F) (SInt 𝔪)) with hQ
  have hmap : Q.map (algebraMap (𝓞 F) (SInt 𝔪)) = Ideal.span {π} := RO.map_comap_eq h𝔪 _
  have hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQ0 : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.map_bot] at hmap
    exact hπ.ne_zero (Ideal.span_singleton_eq_bot.mp hmap.symm)
  have hv : ¬ 𝔪 ≤ Q := by
    intro hle
    rw [C0R.map_eq_top_of_primes 𝔪 h𝔪 Q fun _ _ hPQ => le_trans hle hPQ] at hmap
    exact hJ.ne_top hmap.symm
  refine ⟨⟨Q, hQp, hQ0⟩, hv, ⟨hQ0, ?_⟩, hmap.symm⟩
  have hmax : Q.IsMaximal := hQp.isMaximal hQ0
  by_contra hne
  exact hv (by
    have := hmax.eq_of_le hne le_sup_left
    rw [this]
    exact le_sup_right)

include P hG hz6 in
/-- **Non-triviality of the cubic symbol at every prime element of `R`.** -/
theorem exists_sym_ne_one_of_prime {π : SInt 𝔪} (hπ : Prime π) :
    ∃ d₀ : SInt 𝔪, IsCoprime d₀ π ∧ (S2.cubicSymbol ι P hG hz6).sym d₀ π ≠ 1 := by
  obtain ⟨v, hv, hext, hspan⟩ := exists_place_of_prime hG.ne_bot hπ
  obtain ⟨d, hd1, hd0⟩ := exists_sextic_sq_ne_one ι hG hz6 v hv
  have hsym : (S2.cubicSymbol ι P hG hz6).sym d π = sexticResidueSymbol ι 𝔪 v.asIdeal d ^ 2 := by
    rw [S2.cubicSymbol_sym, cubicExt_eq_residueSymbol ι hext π d hspan,
      C3I.residueSymbol_v (ι := ι) (𝔪 := 𝔪) (v := v) d]
  refine ⟨d, ?_, by rw [hsym]; exact hd1⟩
  by_contra hnc
  have h0 := ((S2.cubicSymbol ι P hG hz6).sym_eq_zero_iff d π hπ.ne_zero).2 hnc
  rw [hsym] at h0
  exact hd0 (pow_eq_zero_iff (by norm_num) |>.mp h0)

include P hG hz6 in
/-- If the constant-term sum at `c ≠ 0` does not vanish, `c` is a unit times a cube. -/
theorem exists_unit_cube_of_csum_ne_zero (c : SInt 𝔪) (hc : c ≠ 0)
    (h : csum (S2.cubicSymbol ι P hG hz6) c ≠ 0) :
    ∃ (u : (SInt 𝔪)ˣ) (b : SInt 𝔪), c = (u : SInt 𝔪) * b ^ 3 := by
  have := RO.isPrincipalIdealRing_SInt hG
  set S := S2.cubicSymbol ι P hG hz6 with hS
  revert hc h
  refine UniqueFactorizationMonoid.induction_on_coprime
    (P := fun c : SInt 𝔪 => c ≠ 0 → csum S c ≠ 0 →
      ∃ (u : (SInt 𝔪)ˣ) (b : SInt 𝔪), c = (u : SInt 𝔪) * b ^ 3) c ?_ ?_ ?_ ?_
  · intro h0
    exact absurd rfl h0
  · intro x hx _ _
    obtain ⟨u, rfl⟩ := hx
    exact ⟨u, 1, by rw [one_pow, mul_one]⟩
  · intro p i hp _ hcs
    obtain ⟨d₀, hd₀, hd₁⟩ := exists_sym_ne_one_of_prime ι P hG hz6 hp
    have h3 : 3 ∣ i := by
      by_contra h3
      apply hcs
      rw [csum_prime_pow S hp.ne_zero hd₀ hd₁, if_neg h3]
    obtain ⟨j, rfl⟩ := h3
    exact ⟨1, p ^ j, by rw [Units.val_one, one_mul, ← pow_mul, mul_comm]⟩
  · intro x y hxy ihx ihy hne hcs
    have hx0 : x ≠ 0 := left_ne_zero_of_mul hne
    have hy0 : y ≠ 0 := right_ne_zero_of_mul hne
    have := finite_quot_span hG.ne_bot hx0
    have := finite_quot_span hG.ne_bot hy0
    have hmul := gauss_mul S (sAdd 𝔪 hG.ne_bot) 0 hx0 hy0 hxy.isCoprime
    rw [gauss_zero_left, gauss_zero_left, gauss_zero_left] at hmul
    have hx1 : csum S x ≠ 0 := by
      intro h0
      apply hcs
      rw [hmul, h0]
      ring
    have hy1 : csum S y ≠ 0 := by
      intro h0
      apply hcs
      rw [hmul, h0]
      ring
    obtain ⟨u, b, rfl⟩ := ihx hx0 hx1
    obtain ⟨u', b', rfl⟩ := ihy hy0 hy1
    exact ⟨u * u', b * b', by rw [Units.val_mul]; ring⟩

include P hG hz6 in
/-- **The hypothesis `hchar` of `B.aCoeff_sumBig`**: the constant-term sum vanishes unless `c` is
a unit times a cube. -/
theorem csum_eq_zero (c : SInt 𝔪) (hc : c ≠ 0)
    (h : ¬ ∃ (u : (SInt 𝔪)ˣ) (b : SInt 𝔪), c = (u : SInt 𝔪) * b ^ 3) :
    csum (S2.cubicSymbol ι P hG hz6) c = 0 := by
  by_contra hne
  exact h (exists_unit_cube_of_csum_ne_zero ι P hG hz6 c hc hne)

end ArtinKP.BZ
end
end

section
-- module Solutions.Artin.KP.BZ_Vol
attribute [-instance] _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instSigmaFiniteE1Mu1 _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-BZ, part 4: stub B-2 — the covolume of the translation lattice `Λ_M`

* `exists_fund_sublattice`, `measure_fund_sublattice` (Mathlib only): for countable subgroups
  `L' ≤ L` of finite index of a measurable additive group with an invariant measure, a
  fundamental domain of `L'` has measure `[L : L'] ·` that of a fundamental domain of `L`.
* `card_transLat_quot`: `[Λ_M : Λ_{M'}] = ∏_{v ∣ 𝔪} q_v^{M' - M}` for `M ≤ M'`
  (`S2.card_latD_quot` transported by strong approximation `F = R + 𝔩_{M'}`).
* `transLat_zero`: `Λ_0 = emb(𝓞_F)`.
* **`volume_cell`** (B-2): `vol(D) · vol(𝔩_M) = vol(B1.fundD F)` for every fundamental cell `D`
  of `Λ_M`, every `M : ℤ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Pointwise
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.BZ

/-! ### Fundamental domains of a sublattice -/

section abstract

variable {E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E]
  (μ : Measure E) [μ.IsAddLeftInvariant]

/-- From a fundamental domain of `L` to one of a subgroup `L' ≤ L` of finite index. -/
theorem exists_fund_sublattice {L' L : AddSubgroup E} [Countable L] (hle : L' ≤ L)
    [Finite (L ⧸ L'.addSubgroupOf L)] {D : Set E} (hD : IsAddFundamentalDomain L D μ) :
    ∃ D' : Set E, IsAddFundamentalDomain L' D' μ ∧
      μ D' = (Nat.card (L ⧸ L'.addSubgroupOf L) : ENNReal) * μ D := by
  classical
  set K := L'.addSubgroupOf L with hK
  let σ : L ⧸ K → L := fun q => Quotient.out q
  have hσ : ∀ q, (QuotientAddGroup.mk (σ q) : L ⧸ K) = q := fun q => Quotient.out_eq q
  have hσinj : ∀ q₁ q₂ : L ⧸ K, ((σ q₁ : L) : E) - ((σ q₂ : L) : E) ∈ L' → q₁ = q₂ := by
    intro q₁ q₂ h
    rw [← hσ q₁, ← hσ q₂, QuotientAddGroup.eq, hK, AddSubgroup.mem_addSubgroupOf]
    have : ((-(σ q₁) + σ q₂ : L) : E) = -(((σ q₁ : L) : E) - ((σ q₂ : L) : E)) := by
      push_cast
      abel
    rw [this]
    exact L'.neg_mem h
  let f : L ⧸ K → Set E := fun q => (σ q : L) +ᵥ D
  have hfm : ∀ q, NullMeasurableSet (f q) μ := fun q => hD.nullMeasurableSet_vadd (σ q)
  have hfd : Pairwise (Function.onFun (AEDisjoint μ) f) := by
    intro q₁ q₂ hq
    refine hD.aedisjoint fun h => hq (hσinj q₁ q₂ ?_)
    rw [h, sub_self]
    exact L'.zero_mem
  refine ⟨⋃ q, f q, ⟨NullMeasurableSet.iUnion hfm, ?_, ?_⟩, ?_⟩
  · -- covering
    filter_upwards [hD.ae_covers] with x hx
    obtain ⟨g, hg⟩ := hx
    set q : L ⧸ K := QuotientAddGroup.mk (-g) with hq
    have hmem : ((σ q : L) : E) + (g : E) ∈ L' := by
      have h1 : (QuotientAddGroup.mk (σ q) : L ⧸ K) = QuotientAddGroup.mk (-g) := hσ q
      rw [QuotientAddGroup.eq, hK, AddSubgroup.mem_addSubgroupOf] at h1
      have h2 : ((σ q : L) : E) + (g : E) = -((-(σ q) + -g : L) : E) := by
        push_cast
        abel
      rw [h2]
      exact L'.neg_mem h1
    refine ⟨⟨_, hmem⟩, Set.mem_iUnion.2 ⟨q, ?_⟩⟩
    refine ⟨g +ᵥ x, hg, ?_⟩
    change ((σ q : L) : E) + ((g : E) + x) = (((σ q : L) : E) + (g : E)) + x
    rw [add_assoc]
  · -- disjointness
    intro g₁ g₂ hg
    change AEDisjoint μ (g₁ +ᵥ ⋃ q, f q) (g₂ +ᵥ ⋃ q, f q)
    rw [Set.vadd_set_iUnion, Set.vadd_set_iUnion, AEDisjoint.iUnion_left_iff]
    intro q₁
    rw [AEDisjoint.iUnion_right_iff]
    intro q₂
    have e : ∀ (g : L') (q : L ⧸ K),
        g +ᵥ f q = ((⟨(g : E), hle g.2⟩ + σ q : L)) +ᵥ D := by
      intro g q
      ext y
      constructor
      · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨w, hw, by
          change ((g : E) + ((σ q : L) : E)) + w = (g : E) + (((σ q : L) : E) + w)
          rw [add_assoc]⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨(σ q : L) +ᵥ w, ⟨w, hw, rfl⟩, by
          change (g : E) + (((σ q : L) : E) + w) = ((g : E) + ((σ q : L) : E)) + w
          rw [add_assoc]⟩
    rw [e, e]
    refine hD.aedisjoint fun h => hg ?_
    have h' : (g₁ : E) + ((σ q₁ : L) : E) = (g₂ : E) + ((σ q₂ : L) : E) :=
      congrArg (fun z : L => (z : E)) h
    have hq : q₁ = q₂ := by
      refine hσinj q₁ q₂ ?_
      have : ((σ q₁ : L) : E) - ((σ q₂ : L) : E) = (g₂ : E) - (g₁ : E) := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm, h', add_comm]
      rw [this]
      exact L'.sub_mem g₂.2 g₁.2
    rw [hq] at h'
    exact Subtype.ext (add_right_cancel h')
  · -- measure
    let _ := Fintype.ofFinite (L ⧸ K)
    rw [measure_iUnion₀ hfd hfm, tsum_fintype]
    have : ∀ q, μ (f q) = μ D := fun q => by
      change μ (((σ q : L) : E) +ᵥ D) = μ D
      exact measure_vadd μ _ D
    rw [Finset.sum_congr rfl fun q _ => this q, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.card_eq_fintype_card]

/-- A fundamental domain of a sublattice `L' ≤ L` of finite index has measure
`[L : L'] · μ(D)`. -/
theorem measure_fund_sublattice {L' L : AddSubgroup E} [Countable L] (hle : L' ≤ L)
    [Finite (L ⧸ L'.addSubgroupOf L)] {D D' : Set E} (hD : IsAddFundamentalDomain L D μ)
    (hD' : IsAddFundamentalDomain L' D' μ) :
    μ D' = (Nat.card (L ⧸ L'.addSubgroupOf L) : ENNReal) * μ D := by
  have : Countable L' := (AddSubgroup.inclusion_injective hle).countable
  obtain ⟨D'', h1, h2⟩ := exists_fund_sublattice μ hle hD
  rw [← h2]
  exact hD'.measure_eq h1

end abstract

/-- Two surjective homomorphisms with the same kernel have equinumerous targets. -/
theorem card_eq_of_ker_eq {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : A →+ C) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : f.ker = g.ker) : Nat.card B = Nat.card C := by
  rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv,
    ← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv, h]

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem transLat_mono {M M' : ℤ} (h : M ≤ M') : transLat 𝔪 M' ≤ transLat 𝔪 M := by
  rintro x ⟨b, hb, rfl⟩
  exact ⟨b, Small.mono (𝔪 := 𝔪) h hb, rfl⟩

theorem embR_mem_transLat {M : ℤ} {b : SInt 𝔪} :
    (embR b : InfinitePlace F → ℂ) ∈ transLat 𝔪 M ↔ b ∈ latR 𝔪 M := by
  constructor
  · rintro ⟨b', hb', h⟩
    rwa [← embR_injective h]
  · intro hb
    exact ⟨b, hb, rfl⟩

/-- `[Λ_M : Λ_{M'}] = ∏_{v ∣ 𝔪} q_v^{M' - M}` for `M ≤ M'`. -/
theorem card_transLat_quot (h𝔪 : 𝔪 ≠ ⊥) {M M' : ℤ} (h : M ≤ M') :
    Nat.card (transLat 𝔪 M ⧸ (transLat 𝔪 M').addSubgroupOf (transLat 𝔪 M))
      = ∏ v ∈ CubicPkg.sFin 𝔪, Ideal.absNorm v.asIdeal ^ (M' - M).toNat := by
  rw [← S2.card_latD_quot h𝔪 (k := fun _ => M) (k' := fun _ => M') fun _ _ => h]
  -- the two maps out of `R ∩ 𝔩_M`
  let f₀ : latR 𝔪 M →+ transLat 𝔪 M := (embR (𝔪 := 𝔪)).addSubgroupMap (latR 𝔪 M)
  have hf₀ : Function.Surjective f₀ := (embR (𝔪 := 𝔪)).addSubgroupMap_surjective (latR 𝔪 M)
  let g₀ : latR 𝔪 M →+ S2.latD 𝔪 (fun _ => M) :=
    { toFun := fun b => ⟨((b : SInt 𝔪) : F), b.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let f : latR 𝔪 M →+ transLat 𝔪 M ⧸ (transLat 𝔪 M').addSubgroupOf (transLat 𝔪 M) :=
    (QuotientAddGroup.mk' _).comp f₀
  let g : latR 𝔪 M →+
      S2.latD 𝔪 (fun _ => M) ⧸ (S2.latD 𝔪 (fun _ => M')).addSubgroupOf (S2.latD 𝔪 (fun _ => M)) :=
    (QuotientAddGroup.mk' _).comp g₀
  have hf : Function.Surjective f := (QuotientAddGroup.mk'_surjective _).comp hf₀
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    obtain ⟨r, hr⟩ := exists_sInt_sub_small h𝔪 M' (x : F)
    have hrM : Small 𝔪 M ((r : SInt 𝔪) : F) := by
      have h1 : Small 𝔪 M ((x : F) - (r : F)) := Small.mono (𝔪 := 𝔪) h hr
      have h2 : Small 𝔪 M (x : F) := x.2
      have := h2.sub h1
      rwa [sub_sub_cancel] at this
    refine ⟨⟨r, hrM⟩, ?_⟩
    change (QuotientAddGroup.mk (g₀ ⟨r, hrM⟩) : S2.latD 𝔪 (fun _ => M) ⧸ _) = QuotientAddGroup.mk x
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    change Small 𝔪 M' (-((r : SInt 𝔪) : F) + (x : F))
    rwa [neg_add_eq_sub]
  refine card_eq_of_ker_eq f g hf hg ?_
  ext b
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
  change (QuotientAddGroup.mk (f₀ b) : transLat 𝔪 M ⧸ _) = 0 ↔
    (QuotientAddGroup.mk (g₀ b) : S2.latD 𝔪 (fun _ => M) ⧸ _) = 0
  rw [QuotientAddGroup.eq_zero_iff, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.mem_addSubgroupOf]
  change (embR (b : SInt 𝔪) : InfinitePlace F → ℂ) ∈ transLat 𝔪 M' ↔ _
  rw [embR_mem_transLat]
  rfl

variable [IsTotallyComplex F]

/-- `Λ_0 = emb(𝓞_F)`. -/
theorem transLat_zero (𝔪 : Ideal (𝓞 F)) : transLat 𝔪 0 = latSub F := by
  ext x
  rw [mem_latSub]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F ((b : SInt 𝔪) : F) ≤ 1 := by
      intro v
      by_cases hv : 𝔪 ≤ v.asIdeal
      · have := hb v hv
        rwa [neg_zero, WithZero.exp_zero] at this
      · exact sInt_val_le_one b v hv
    obtain ⟨β, hβ⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hall
    exact ⟨β, by rw [embR_apply, ← hβ]⟩
  · rintro ⟨β, rfl⟩
    refine ⟨algebraMap (𝓞 F) (SInt 𝔪) β, fun v _ => ?_, rfl⟩
    rw [neg_zero, WithZero.exp_zero]
    exact v.valuation_le_one β

/-- **Stub B-2, proved** (only `𝔪 ≠ ⊥` is used): `vol(D) · vol(𝔩_M) = covol(𝓞_F)`. -/
theorem volume_cell' (h𝔪 : 𝔪 ≠ ⊥) (M : ℤ) {D : Set (InfinitePlace F → ℂ)}
    (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume) :
    volume D * ENNReal.ofReal (vol 𝔪 M) = volume (B1.fundD F) := by
  classical
  set M' : ℤ := max M 0 with hM'
  have h1 : M ≤ M' := le_max_left _ _
  have h0 : (0 : ℤ) ≤ M' := le_max_right _ _
  have hq : ∀ v : HeightOneSpectrum (𝓞 F), 0 < Ideal.absNorm v.asIdeal := fun v => by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    omega
  set n₁ : ℕ := ∏ v ∈ CubicPkg.sFin 𝔪, Ideal.absNorm v.asIdeal ^ (M' - M).toNat with hn₁
  set n₀ : ℕ := ∏ v ∈ CubicPkg.sFin 𝔪, Ideal.absNorm v.asIdeal ^ (M' - 0).toNat with hn₀
  have hn₁0 : n₁ ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hq v).ne'
  have hn₀0 : n₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hq v).ne'
  have hc₁ := card_transLat_quot h𝔪 h1
  have hc₀ := card_transLat_quot h𝔪 h0
  have hfin₁ : Finite (transLat 𝔪 M ⧸ (transLat 𝔪 M').addSubgroupOf (transLat 𝔪 M)) :=
    Nat.finite_of_card_ne_zero (by rw [hc₁]; exact hn₁0)
  have hfin₀ : Finite (transLat 𝔪 0 ⧸ (transLat 𝔪 M').addSubgroupOf (transLat 𝔪 0)) :=
    Nat.finite_of_card_ne_zero (by rw [hc₀]; exact hn₀0)
  have hF : IsAddFundamentalDomain (transLat 𝔪 0) (B1.fundD F) volume := by
    rw [transLat_zero]
    exact B1.isFund
  obtain ⟨D', hD', hvol₀⟩ := exists_fund_sublattice volume (transLat_mono h0) hF
  have hvol₁ := measure_fund_sublattice volume (transLat_mono h1) hD hD'
  rw [hc₀] at hvol₀
  rw [hc₁] at hvol₁
  -- `vol 𝔪 M = n₁ / n₀`
  have hvolM : vol 𝔪 M = (n₁ : ℝ) / (n₀ : ℝ) := by
    rw [vol, hn₁, hn₀, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hqv : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by exact_mod_cast (hq v).ne'
    push_cast
    rw [← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg (by omega),
      Int.toNat_of_nonneg (by omega), ← zpow_sub₀ hqv]
    congr 1
    ring
  have hn₀pos : (0 : ℝ) < n₀ := by exact_mod_cast Nat.pos_of_ne_zero hn₀0
  rw [hvolM, ENNReal.ofReal_div_of_pos hn₀pos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    ← mul_div_assoc, mul_comm (volume D), ← hvol₁, hvol₀, mul_comm,
    ENNReal.mul_div_cancel_right (by exact_mod_cast hn₀0) (ENNReal.natCast_ne_top n₀)]

end ArtinKP.BZ
end
end

section
-- module Solutions.Artin.KP.BZ_Phi
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-BZ, part 2: `B7.phi c = Z.phi (extOf c)`; the exterior ideal of a unit times a cube

* `quotHom_bijective`: `𝓞/𝔞 → R/𝔞R` is bijective for exterior `𝔞` (the proof of
  `L2B.natCard_quot_eq`).
* `ext_eq_of_map_eq`, `extOf_eq`: an exterior ideal is determined by its extension to `R`.
* `phi_eq`: `B7.phi c = Z.phi (extOf c)` — B7's count of residues prime to `c` is the Euler
  function of the exterior ideal of `c` (WP-Z's open bridge).
* `extOf_unit_mul_cube`: `extOf (u b³) = (extOf b)³`.
* `extOf_injective`, `exists_cls_extOf_eq`: classes of `R ∖ 0` modulo units ≃ exterior ideals.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.BZ

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E ArtinKP.B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- `𝓞/𝔞 → R/𝔞R` is bijective for exterior `𝔞`. -/
theorem quotHom_bijective {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) :
    Function.Bijective (C3I.quotHom 𝔪 𝔞) := by
  refine ⟨?_, L2B.quotHom_surjective 𝔞 h𝔞.2⟩
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [C3I.quotHom_mk, Ideal.Quotient.eq_zero_iff_mem] at hy
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact L2B.mem_of_map_mem 𝔞 h𝔞.2 a hy

/-- An exterior ideal is determined by its extension to `R`. -/
theorem ext_eq_of_map_eq {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J)
    (h : I.map (algebraMap (𝓞 F) (SInt 𝔪)) = J.map (algebraMap (𝓞 F) (SInt 𝔪))) : I = J := by
  refine le_antisymm (fun a ha => ?_) (fun a ha => ?_)
  · exact L2B.mem_of_map_mem J hJ.2 a (h ▸ Ideal.mem_map_of_mem _ ha)
  · exact L2B.mem_of_map_mem I hI.2 a (h.symm ▸ Ideal.mem_map_of_mem _ ha)

/-- `extOf c` is the exterior ideal with extension `cR`. -/
theorem extOf_eq (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) {I : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I)
    (h : I.map (algebraMap (𝓞 F) (SInt 𝔪)) = Ideal.span {c}) : extOf h𝔪 hc = I :=
  ext_eq_of_map_eq (extOf_isExterior h𝔪 hc) hI (by rw [map_extOf, h])

/-- `extOf (u b³) = (extOf b)³`. -/
theorem extOf_unit_mul_cube (h𝔪 : 𝔪 ≠ ⊥) {c b : SInt 𝔪} (hc : c ≠ 0) (hb : b ≠ 0)
    (u : (SInt 𝔪)ˣ) (h : c = (u : SInt 𝔪) * b ^ 3) : extOf h𝔪 hc = extOf h𝔪 hb ^ 3 := by
  refine extOf_eq h𝔪 hc (isExterior_pow (extOf_isExterior h𝔪 hb) 3) ?_
  rw [Ideal.map_pow, map_extOf, Ideal.span_singleton_pow, h,
    Ideal.span_singleton_mul_left_unit u.isUnit]

/-- `c ↦ extOf c` is injective on classes modulo units. -/
theorem extOf_injective (h𝔪 : 𝔪 ≠ ⊥) :
    Function.Injective fun a : Cls (SInt 𝔪) => extOf h𝔪 (rp_ne_zero a.2) := by
  intro a b hab
  have h1 : Ideal.span {rp a.1} = Ideal.span {rp b.1} := by
    rw [← map_extOf h𝔪 (rp_ne_zero a.2), ← map_extOf h𝔪 (rp_ne_zero b.2)]
    exact congrArg _ hab
  have h2 := Ideal.span_singleton_eq_span_singleton.mp h1
  apply Subtype.ext
  rw [← mk_rp a.1, ← mk_rp b.1]
  exact Associates.mk_eq_mk_iff_associated.mpr h2

/-- Every exterior ideal is `extOf` of a class (`R` is a PID). -/
theorem exists_cls_extOf_eq (hG : Good 𝔪) {J : Ideal (𝓞 F)} (hJ : IsExterior 𝔪 J) :
    ∃ a : Cls (SInt 𝔪), extOf hG.ne_bot (rp_ne_zero a.2) = J := by
  obtain ⟨c, hcJ⟩ := (hG.principal J).principal
  have hcJ' : J.map (algebraMap (𝓞 F) (SInt 𝔪)) = Ideal.span {c} := hcJ
  have hinj : Function.Injective (algebraMap (𝓞 F) (SInt 𝔪)) := by
    intro a b hab
    have := congrArg (fun x : SInt 𝔪 => (x : F)) hab
    exact FaithfulSMul.algebraMap_injective (𝓞 F) F this
  have hc : c ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl, Ideal.map_eq_bot_iff_of_injective hinj] at hcJ'
    exact hJ.1 hcJ'
  have ha : Associates.mk c ≠ 0 := by
    rw [Ne, Associates.mk_eq_zero]
    exact hc
  refine ⟨⟨Associates.mk c, ha⟩, extOf_eq hG.ne_bot _ hJ ?_⟩
  rw [hcJ']
  exact (Ideal.span_singleton_eq_span_singleton.mpr
    (Associates.mk_eq_mk_iff_associated.mp (mk_rp (Associates.mk c)))).symm

/-- Units of `R/cR` are the classes prime to `c`. -/
theorem isUnit_mk_iff {R : Type*} [CommRing R] (c d : R) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {c}) d) ↔ IsCoprime d c := by
  constructor
  · intro hu
    obtain ⟨e, he⟩ := isUnit_iff_exists_inv.1 hu
    obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective e
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {c})), Ideal.Quotient.eq,
      Ideal.mem_span_singleton] at he
    obtain ⟨k, hk⟩ := he
    exact ⟨e, -k, by linear_combination hk⟩
  · rintro ⟨a, b, hab⟩
    refine isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {c})), Ideal.Quotient.eq,
      Ideal.mem_span_singleton]
    exact ⟨-b, by linear_combination hab⟩

/-- B7's residue count is the number of units of `R/cR`. -/
theorem phi_eq_card_units {R : Type*} [CommRing R] (c : R) [Finite (R ⧸ Ideal.span {c})] :
    B7.phi c = (Nat.card (R ⧸ Ideal.span {c})ˣ : ℂ) := by
  classical
  let _ := Fintype.ofFinite (R ⧸ Ideal.span {c})
  have h1 : Nat.card (R ⧸ Ideal.span {c})ˣ = Nat.card {x : R ⧸ Ideal.span {c} // IsUnit x} :=
    Nat.card_congr ((Submonoid.unitsTypeEquivIsUnitSubmonoid
      (M := R ⧸ Ideal.span {c})).toEquiv.trans
      (Equiv.subtypeEquivRight fun x => IsUnit.mem_submonoid_iff x))
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.sum_boole]
  unfold B7.phi rsum
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun x _ => if_congr ?_ rfl rfl
  rw [← isUnit_mk_iff, mk_rep]

/-- **`B7.phi c = Z.phi (extOf c)`.** -/
theorem phi_eq (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) :
    B7.phi c = (Z.phi (extOf h𝔪 hc) : ℂ) := by
  have := finite_quot_span h𝔪 hc
  rw [phi_eq_card_units, Z.phi]
  congr 1
  let e1 : 𝓞 F ⧸ extOf h𝔪 hc ≃+* SInt 𝔪 ⧸ (extOf h𝔪 hc).map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    RingEquiv.ofBijective _ (quotHom_bijective (extOf_isExterior h𝔪 hc))
  let e2 : SInt 𝔪 ⧸ (extOf h𝔪 hc).map (algebraMap (𝓞 F) (SInt 𝔪)) ≃+* SInt 𝔪 ⧸ Ideal.span {c} :=
    Ideal.quotEquivOfEq (map_extOf h𝔪 hc)
  exact (Nat.card_congr (Units.mapEquiv (e1.trans e2).toMulEquiv).toEquiv).symm

end ArtinKP.BZ
end
end

section
-- module Solutions.Artin.KP.BZ_Zeta
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply
/-!
# WP-BZ, part 3: stub B-1 — the constant-term Dirichlet series of `Φ^Σ` is the zeta ratio

* `kTerm_sumBig`: for every class `a`, the summand of `𝔞_{Φ^Σ}(0, s)` is
  `vol(𝔩_M) · G₀(𝔠) N𝔠^{-s}` with `𝔠 = extOf (rp a)` (`Z.g0Term`).
* **`aCoeff_sumBig`** (B-1, without the hypothesis `hchar` of `B_Stubs`):
  `𝔞_{Φ^Σ}(0, s) = vol(𝔩_M) · ζ^S(3s-3)/ζ^S(3s-2)` for `Re s > 2`.
* `mCoeff_sumBig`: `m_{Φ^Σ}(s) = (π/(s-1))^r · vol(𝔩_M) · ζ^S(3s-3)/ζ^S(3s-2)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.BZ

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K ArtinKP.B7 ArtinKP.B

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) (M : ℤ) (T : Finset {η : F // η ≠ 0})
  (hdisj : ∀ η ∈ T, ∀ η' ∈ T, η ≠ η' → ∀ c : F, InClass 𝔪 N η.1 c → ¬ InClass 𝔪 N η'.1 c)
  (hcov : ∀ c : F, c ≠ 0 → ∃ η ∈ T, InClass 𝔪 N η.1 c)

include hdisj hcov in
/-- The summand of `𝔞_{Φ^Σ}(0, s)` at any class: `vol(𝔩_M) · G₀(𝔠) · N𝔠^{-s}`, `𝔠 = extOf c`. -/
theorem kTerm_sumBig (a : Cls (SInt 𝔪)) (s : ℂ) :
    kTerm hG hz6 (sumBig ι hG hN1 hN M T) 0 a s
      = ((vol 𝔪 M : ℝ) : ℂ) * Z.g0Term 𝔪 s (extOf hG.ne_bot (rp_ne_zero a.2)) := by
  classical
  have hc := rp_ne_zero a.2
  have hE := extOf_isExterior hG.ne_bot hc
  rw [Z.g0Term, Set.indicator_of_mem (show extOf hG.ne_bot hc ∈ Z.Ext 𝔪 from hE), Z.G0]
  by_cases hcube : ∃ d : Ideal (𝓞 F), extOf hG.ne_bot hc = d ^ 3
  · rw [if_pos hcube]
    obtain ⟨d, hd⟩ := hcube
    obtain ⟨b, hbd⟩ := (hG.principal d).principal
    have hbd' : d.map (algebraMap (𝓞 F) (SInt 𝔪)) = Ideal.span {b} := hbd
    have hspan : Ideal.span {rp a.1} = Ideal.span {b ^ 3} := by
      rw [← map_extOf hG.ne_bot hc, hd, Ideal.map_pow, hbd', Ideal.span_singleton_pow]
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
    have hb : b ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num), mul_eq_zero] at hu
      exact hu.elim hc u.ne_zero
    have hab : rp a.1 = ((u⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) * b ^ 3 := by
      rw [← hu, mul_comm, mul_assoc, Units.mul_inv, mul_one]
    rw [kTerm_sumBig_cube hG hz6 hN1 hN M T hdisj hcov a u⁻¹ hb hab s, phi_eq hG.ne_bot hc,
      E.nrm, natCard_quot_span hG.ne_bot hc]
  · rw [if_neg hcube, Nat.cast_zero, zero_mul, mul_zero, kTerm, gauss_zero_left,
      csum_eq_zero ι P hG hz6 _ hc, zero_mul, zero_mul]
    rintro ⟨u, b, hub⟩
    have hb : b ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num), mul_zero] at hub
      exact hc hub
    exact hcube ⟨_, extOf_unit_mul_cube hG.ne_bot hc hb u hub⟩

include hdisj hcov in
/-- **Stub B-1, proved (without the hypothesis `hchar`)**: the Dirichlet series of the constant
term of `Φ^Σ` is `vol(𝔩_M) · ζ^S(3s-3)/ζ^S(3s-2)` for `Re s > 2`. -/
theorem aCoeff_sumBig {s : ℂ} (hs : 2 < s.re) :
    aCoeff hG hz6 (sumBig ι hG hN1 hN M T) 0 s
      = ((vol 𝔪 M : ℝ) : ℂ) * (C3P.zetaS 𝔪 (3 * s - 3) / C3P.zetaS 𝔪 (3 * s - 2)) := by
  have hs' : 4 / 3 < s.re := by linarith
  rw [← Z.tsum_G0 hG.ne_bot hs']
  have hsupp : Function.support (Z.g0Term 𝔪 s) ⊆
      Set.range fun a : Cls (SInt 𝔪) => extOf hG.ne_bot (rp_ne_zero a.2) := by
    intro J hJ
    have hJE : J ∈ Z.Ext 𝔪 := by
      by_contra hne
      exact hJ (by rw [Z.g0Term, Set.indicator_of_notMem hne])
    exact exists_cls_extOf_eq hG hJE
  rw [← (extOf_injective hG.ne_bot).tsum_eq hsupp, ← tsum_mul_left]
  exact tsum_congr fun a => kTerm_sumBig hG hz6 hN1 hN M T hdisj hcov a s

include hdisj hcov in
/-- `m_{Φ^Σ}(s) = (π/(s-1))^r · vol(𝔩_M) · ζ^S(3s-3)/ζ^S(3s-2)` for `Re s > 2`. -/
theorem mCoeff_sumBig {s : ℂ} (hs : 2 < s.re) :
    mCoeff hG hz6 (sumBig ι hG hN1 hN M T) s
      = ((Real.pi : ℂ) / (s - 1)) ^ Fintype.card (InfinitePlace F)
        * (((vol 𝔪 M : ℝ) : ℂ) * (C3P.zetaS 𝔪 (3 * s - 3) / C3P.zetaS 𝔪 (3 * s - 2))) := by
  rw [mCoeff, aCoeff_sumBig hG hz6 hN1 hN M T hdisj hcov hs]

end ArtinKP.BZ
end
end

section
-- module Solutions.Artin.KP.Z_Limit
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # Z_Limit: Lemma Z and the residue of the zeta ratio at `s = 4/3`

Everything is a genuine complex limit (no sector needed): the platform theorem 8087d96f
(`(s-1) ζ_K` is entire), through `C3P.zetaS_package`, gives an entire `R` with
`ζ^S(s) = R(s)/(s-1)` on `Re s > 1` and `R 1 = sZetaResidue 𝔪`.

* `Z.sZetaResidue_pos`, `Z.zetaS_two_pos`.
* `Z.differentiableAt_zetaS`: `ζ^S` is holomorphic on `Re s > 1`.
* `Z.tendsto_sub_one_mul_zetaS` (**Lemma Z**): `(s-1) ζ^S(s) → ρ_S` as `s → 1`, `Re s > 1`.
* `Z.exists_zetaRatio`: `ζ^S(3s-3)/ζ^S(3s-2) = G(s)/(s-4/3)` on `Re s > 4/3` with `G` holomorphic
  on `Re s > 1` and `G(4/3) = ρ_S/(3 ζ^S(2)) ≠ 0` (a simple pole at `4/3`).
* `Z.tendsto_zetaRatio`, `Z.tendsto_ray_zetaRatio`, `Z.tendsto_ray_tsum_cubeTerm`: the limits
  consumed by (C9), along `s_t = 4/3 + t e^{iπ/4}`.
* `Z.differentiableOn_zetaRatio`, `Z.differentiableOn_tsum_cubeTerm`.
-/

set_option autoImplicit false

open NumberField ArtinPrimitiveRoots Filter Topology

namespace ArtinKP

namespace Z

variable {F : Type*} [Field F] [NumberField F]

/-- `ρ_S > 0`. -/
theorem sZetaResidue_pos {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) : 0 < sZetaResidue 𝔪 := by
  classical
  have hfin := C3P.finite_primes_ge h𝔪
  rw [sZetaResidue, finprod_mem_eq_finite_toFinset_prod _ hfin]
  refine mul_pos (dedekindZeta_residue_pos F) (Finset.prod_pos fun P hP => ?_)
  obtain ⟨hPp, hP0, -⟩ := (Set.Finite.mem_toFinset _).1 hP
  have h2 : (2 : ℝ) ≤ Ideal.absNorm P := by exact_mod_cast two_le_absNorm hPp hP0
  have h3 : ((Ideal.absNorm P : ℝ))⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h2
  have h4 : (2 : ℝ)⁻¹ < 1 := by norm_num
  linarith

lemma re_three_mul_sub_two (s : ℂ) : (3 * s - 2).re = 3 * s.re - 2 := by
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero]

lemma re_three_mul_sub_three (s : ℂ) : (3 * s - 3).re = 3 * s.re - 3 := by
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero]

lemma re_four_thirds : ((4 : ℂ) / 3).re = 4 / 3 := by
  rw [show ((4 : ℂ) / 3) = ((4 / 3 : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]

/-- `ζ^S(2)` is a positive real number. -/
theorem zetaS_two_pos {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ z : ℝ, 0 < z ∧ C3P.zetaS 𝔪 2 = (z : ℂ) := by
  classical
  set f : Ideal (𝓞 F) → ℝ :=
    fun I => (Ext 𝔪).indicator (fun I => (Ideal.absNorm I : ℝ) ^ (-(2 : ℝ))) I with hf
  have hnn : ∀ I, 0 ≤ f I := fun I =>
    Set.indicator_nonneg (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) I
  have hsum : Summable f := by
    refine Summable.of_nonneg_of_le hnn (fun I => ?_)
      (T12B.summable_absNorm_rpow (F := F) (σ := 2) (by norm_num))
    exact Set.indicator_le_self' (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) I
  have htop : (⊤ : Ideal (𝓞 F)) ∈ Ext 𝔪 := ⟨top_ne_bot, top_sup_eq _⟩
  have h1 : f ⊤ = 1 := by
    rw [hf]
    simp only
    rw [Set.indicator_of_mem htop, Ideal.absNorm_top, Nat.cast_one, Real.one_rpow]
  refine ⟨∑' I, f I, hsum.tsum_pos hnn ⊤ (by rw [h1]; exact one_pos), ?_⟩
  rw [zetaS_eq_tsum h𝔪 (by simp), Complex.ofReal_tsum]
  refine tsum_congr fun I => ?_
  by_cases hE : I ∈ Ext 𝔪
  · rw [hf]
    simp only
    rw [Set.indicator_of_mem hE, Set.indicator_of_mem hE, nrm,
      Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rfl
  · rw [hf]
    simp only
    rw [Set.indicator_of_notMem hE, Set.indicator_of_notMem hE, Complex.ofReal_zero]

/-- `ζ^S` is holomorphic on `Re s > 1`. -/
theorem differentiableAt_zetaS {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {w : ℂ} (hw : 1 < w.re) :
    DifferentiableAt ℂ (C3P.zetaS 𝔪) w := by
  obtain ⟨R, hR, hRe, -, -⟩ := C3P.zetaS_package h𝔪
  have hne : w - 1 ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0
    simp at this
    linarith
  have hev : C3P.zetaS 𝔪 =ᶠ[𝓝 w] fun s => R s / (s - 1) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw] with s hs
      using hRe s hs
  exact ((hR w).div (differentiableAt_id.sub_const 1) hne).congr_of_eventuallyEq hev

/-- The zeta ratio has (at most) a simple pole at `4/3` with nonzero residue
`ρ_S / (3 ζ^S(2))`, and is meromorphic on `Re s > 1`. -/
theorem exists_zetaRatio {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 < s.re} ∧
      (∀ s : ℂ, 4 / 3 < s.re →
        C3P.zetaS 𝔪 (3 * s - 3) / C3P.zetaS 𝔪 (3 * s - 2) = G s / (s - 4 / 3)) ∧
      G (4 / 3) = (sZetaResidue 𝔪 : ℂ) / (3 * C3P.zetaS 𝔪 2) ∧ G (4 / 3) ≠ 0 := by
  obtain ⟨R, hR, hRe, hR1, -⟩ := C3P.zetaS_package h𝔪
  have hval : (fun s : ℂ => R (3 * s - 3) / (3 * C3P.zetaS 𝔪 (3 * s - 2))) (4 / 3) =
      (sZetaResidue 𝔪 : ℂ) / (3 * C3P.zetaS 𝔪 2) := by
    show R (3 * (4 / 3) - 3) / (3 * C3P.zetaS 𝔪 (3 * (4 / 3) - 2)) = _
    rw [show (3 : ℂ) * (4 / 3) - 3 = 1 by norm_num, show (3 : ℂ) * (4 / 3) - 2 = 2 by norm_num,
      hR1]
  refine ⟨fun s => R (3 * s - 3) / (3 * C3P.zetaS 𝔪 (3 * s - 2)), ?_, ?_, hval, ?_⟩
  · intro s hs
    have hs' : 1 < s.re := hs
    have hre : 1 < (3 * s - 2).re := by rw [re_three_mul_sub_two]; linarith
    have ha : DifferentiableAt ℂ (fun s : ℂ => 3 * s - 2) s :=
      (differentiableAt_id.const_mul 3).sub_const 2
    have hb : DifferentiableAt ℂ (fun s : ℂ => 3 * s - 3) s :=
      (differentiableAt_id.const_mul 3).sub_const 3
    have hz : DifferentiableAt ℂ (fun s : ℂ => C3P.zetaS 𝔪 (3 * s - 2)) s :=
      DifferentiableAt.comp (g := C3P.zetaS 𝔪) s (differentiableAt_zetaS h𝔪 hre) ha
    have hr : DifferentiableAt ℂ (fun s : ℂ => R (3 * s - 3)) s := (hR _).comp s hb
    exact (hr.div (hz.const_mul 3)
      (mul_ne_zero three_ne_zero (zetaS_ne_zero h𝔪 hre))).differentiableWithinAt
  · intro s hs
    have hre : 1 < (3 * s - 2).re := by rw [re_three_mul_sub_two]; linarith
    have hre' : 1 < (3 * s - 3).re := by rw [re_three_mul_sub_three]; linarith
    have hZ := zetaS_ne_zero h𝔪 hre
    have hne : s - 4 / 3 ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0
      rw [Complex.sub_re, re_four_thirds, Complex.zero_re] at this
      linarith
    have hne' : 3 * s - 3 - 1 ≠ 0 := fun h0 => hne (by linear_combination h0 / 3)
    rw [hRe _ hre']
    field_simp
    ring
  · rw [hval]
    obtain ⟨z, hz, hzeq⟩ := zetaS_two_pos h𝔪
    rw [hzeq]
    refine div_ne_zero ?_ (mul_ne_zero three_ne_zero ?_)
    · exact_mod_cast (sZetaResidue_pos h𝔪).ne'
    · exact_mod_cast hz.ne'

end Z

end ArtinKP
end

section
-- module Solutions.Artin.KP.BZ_Main
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instSigmaFiniteE1Mu1 _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply
/-!
# WP-BZ, part 5: the constant term of `E(Φ^Σ)` — what C9 uses

`Φ^Σ = sumBig ι hG hN1 hN M T`, `T` a complete system of pairwise disjoint classes, `D` any
fundamental cell of `Λ_M = transLat 𝔪 M`, `Re s > 2`, `ht = ∏_w v_w`.

* `vol_pos`, `volume_cell_ne_top`, `volume_cell_toReal`: `vol(D) = covol(𝓞_F)/vol(𝔩_M)`, finite.
* `sumBig_zero_left`: `Φ^Σ_s(0, d) = 0`, so the constant term has **no** `ht^s` term.
* **`const_term_sumBig`**:
  `∫_D E(Φ^Σ)(x, v) dx = (π/(s-1))^r · ζ^S(3s-3)/ζ^S(3s-2) · ht^{2-s}`.
* **`mean_const_term_sumBig`**: the mean over the cell,
  `vol(D)⁻¹ ∫_D E(Φ^Σ) = C · (π/(s-1))^r · ζ^S(3s-3)/ζ^S(3s-2) · ht^{2-s}` with
  `C = vol(𝔩_M)/covol(𝓞_F) = vol 𝔪 M / (volume (B1.fundD F)).toReal > 0` (`constC_pos`).
* **`exists_mean_const_term_pole`**: with the function `G` of `Z.exists_zetaRatio` (holomorphic on
  `Re s > 1`, `G(4/3) = ρ_S/(3ζ^S(2)) ≠ 0`), the coefficient is
  `C · (π/(s-1))^r · G(s)/(s - 4/3)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.BZ

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K ArtinKP.B7 ArtinKP.B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

theorem vol_pos (𝔪 : Ideal (𝓞 F)) (M : ℤ) : 0 < vol 𝔪 M :=
  Finset.prod_pos fun v _ => zpow_pos (by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (by omega : 0 < Ideal.absNorm v.asIdeal)) _

/-- `Φ^Σ` vanishes on the rows `(0, d)`. -/
theorem sumBig_zero_left (hG : Good 𝔪) {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) (M : ℤ)
    (T : Finset {η : F // η ≠ 0}) (s : ℂ) (d : F) : sumBig ι hG hN1 hN M T s 0 d = 0 := by
  rw [sumBig, GSection.sum_apply]
  refine Finset.sum_eq_zero fun η _ => ?_
  rw [bigCell_apply]
  exact bigFun_of_not_supp (fun h => InClass.ne_zero hG hN1 η.2 h.1 rfl) s

variable [IsTotallyComplex F]

/-- A fundamental cell of `Λ_M` has finite volume. -/
theorem volume_cell_ne_top (h𝔪 : 𝔪 ≠ ⊥) (M : ℤ) {D : Set (InfinitePlace F → ℂ)}
    (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume) : volume D ≠ ⊤ := by
  intro htop
  have h := volume_cell' h𝔪 M hD
  rw [htop, ENNReal.top_mul (by simpa using vol_pos 𝔪 M)] at h
  exact (fundD_bounded (F := F)).measure_lt_top.ne h.symm

/-- `vol(D) = covol(𝓞_F)/vol(𝔩_M)`. -/
theorem volume_cell_toReal (h𝔪 : 𝔪 ≠ ⊥) (M : ℤ) {D : Set (InfinitePlace F → ℂ)}
    (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume) :
    (volume D).toReal = (volume (B1.fundD F)).toReal / vol 𝔪 M := by
  have h := congrArg ENNReal.toReal (volume_cell' h𝔪 M hD)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (vol_pos 𝔪 M).le] at h
  rw [← h, mul_div_assoc, div_self (vol_pos 𝔪 M).ne', mul_one]

theorem inv_volume_cell_toReal (h𝔪 : 𝔪 ≠ ⊥) (M : ℤ) {D : Set (InfinitePlace F → ℂ)}
    (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume) :
    ((volume D).toReal)⁻¹ = constC 𝔪 M := by
  rw [volume_cell_toReal h𝔪 M hD, inv_div, constC]

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) (M : ℤ) (T : Finset {η : F // η ≠ 0})
  (hdisj : ∀ η ∈ T, ∀ η' ∈ T, η ≠ η' → ∀ c : F, InClass 𝔪 N η.1 c → ¬ InClass 𝔪 N η'.1 c)
  (hcov : ∀ c : F, c ≠ 0 → ∃ η ∈ T, InClass 𝔪 N η.1 c)

include hdisj hcov in
/-- **The constant term of `E(Φ^Σ)` over a cell of `Λ_M`**, `Re s > 2`: there is no `ht^s`
term, and the `ht^{2-s}` term is `(π/(s-1))^r · ζ^S(3s-3)/ζ^S(3s-2)`. -/
theorem const_term_sumBig {s : ℂ} (hs : 2 < s.re) (v : InfinitePlace F → ℝ)
    (hv : ∀ w, 0 < v w) {D : Set (InfinitePlace F → ℂ)}
    (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume) :
    ∫ x in D, eis ((sumBig ι hG hN1 hN M T).twist hG hz6) s (X.mk x v hv)
      = ((Real.pi : ℂ) / (s - 1)) ^ Fintype.card (InfinitePlace F)
        * (C3P.zetaS 𝔪 (3 * s - 3) / C3P.zetaS 𝔪 (3 * s - 2))
        * ((∏ w, v w : ℝ) : ℂ) ^ (2 - s) := by
  have hvol : ((vol 𝔪 M : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (vol_pos 𝔪 M).ne'
  rw [const_term_mCoeff hG hz6 _ (validDepth_sumBig hG hN1 hN M T hdisj hcov) hs v hv hD
    (volume_cell_ne_top hG.ne_bot M hD), sumBig_zero_left,
    mCoeff_sumBig hG hz6 hN1 hN M T hdisj hcov hs]
  field_simp
  ring

include hdisj hcov in
/-- **The mean of the constant term over the cell**:
`vol(D)⁻¹ ∫_D E(Φ^Σ) = C · (π/(s-1))^r · ζ^S(3s-3)/ζ^S(3s-2) · ht^{2-s}`,
`C = vol(𝔩_M)/covol(𝓞_F) > 0`. -/
theorem mean_const_term_sumBig {s : ℂ} (hs : 2 < s.re) (v : InfinitePlace F → ℝ)
    (hv : ∀ w, 0 < v w) {D : Set (InfinitePlace F → ℂ)}
    (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume) :
    (((volume D).toReal : ℝ) : ℂ)⁻¹
        * ∫ x in D, eis ((sumBig ι hG hN1 hN M T).twist hG hz6) s (X.mk x v hv)
      = ((constC 𝔪 M : ℝ) : ℂ) * ((Real.pi : ℂ) / (s - 1)) ^ Fintype.card (InfinitePlace F)
        * (C3P.zetaS 𝔪 (3 * s - 3) / C3P.zetaS 𝔪 (3 * s - 2))
        * ((∏ w, v w : ℝ) : ℂ) ^ (2 - s) := by
  rw [const_term_sumBig hG hz6 hN1 hN M T hdisj hcov hs v hv hD, ← Complex.ofReal_inv,
    inv_volume_cell_toReal hG.ne_bot M hD]
  ring

/-- **The statement for C9.**  There is `G`, holomorphic on `Re s > 1`, with
`G(4/3) = ρ_S/(3 ζ^S(2)) ≠ 0`, such that for every complete disjoint system of classes `T`, every
depth `M`, every cell `D` of `Λ_M` and `Re s > 2`, the mean constant term of `E(Φ^Σ)` is
`C · (π/(s-1))^r · G(s)/(s - 4/3) · ht^{2-s}` with `C = vol(𝔩_M)/covol(𝓞_F) > 0`. -/
theorem exists_mean_eis_sumBig_eq_pole_four_thirds_oai (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 < s.re} ∧
      G (4 / 3) = (sZetaResidue 𝔪 : ℂ) / (3 * C3P.zetaS 𝔪 2) ∧ G (4 / 3) ≠ 0 ∧
      ∀ {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) (M : ℤ) (T : Finset {η : F // η ≠ 0}),
        (∀ η ∈ T, ∀ η' ∈ T, η ≠ η' → ∀ c : F, InClass 𝔪 N η.1 c → ¬ InClass 𝔪 N η'.1 c) →
        (∀ c : F, c ≠ 0 → ∃ η ∈ T, InClass 𝔪 N η.1 c) →
        ∀ {D : Set (InfinitePlace F → ℂ)}, IsAddFundamentalDomain (transLat 𝔪 M) D volume →
        ∀ {s : ℂ}, 2 < s.re → ∀ (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w),
          (((volume D).toReal : ℝ) : ℂ)⁻¹
              * ∫ x in D, eis ((sumBig ι hG hN1 hN M T).twist hG hz6) s (X.mk x v hv)
            = ((constC 𝔪 M : ℝ) : ℂ)
              * ((Real.pi : ℂ) / (s - 1)) ^ Fintype.card (InfinitePlace F)
              * (G s / (s - 4 / 3)) * ((∏ w, v w : ℝ) : ℂ) ^ (2 - s) := by
  obtain ⟨G, hGd, hGe, hG1, hG0⟩ := Z.exists_zetaRatio hG.ne_bot
  refine ⟨G, hGd, hG1, hG0, fun hN1 hN M T hdisj hcov D hD s hs v hv => ?_⟩
  rw [mean_const_term_sumBig hG hz6 hN1 hN M T hdisj hcov hs v hv hD, hGe s (by linarith)]

end ArtinKP.BZ
end
end

theorem solution.{u_1} : type_of% @ArtinKP.BZ.exists_mean_eis_sumBig_eq_pole_four_thirds_oai.{u_1} := @ArtinKP.BZ.exists_mean_eis_sumBig_eq_pole_four_thirds_oai.{u_1}
