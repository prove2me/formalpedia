-- Prove2me | solution 1 for ArtinKP.GK.tau_eq_rpow_mul_coefF_mul_kir
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:09:09.917204+00:00
-- url     : https://prove2.me/submissions/50708f92-9b51-4d0c-ad0b-d64c59da3eaa

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
import Theorems.Thm_ArtinKP_E_primeDatum_gen
import Theorems.Thm_ArtinKP_E_wloc_mul_sym_eq
import Theorems.Thm_ArtinKP_GK_theta_per_gen_of_isExterior

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

lemma Per.mul {c : R} {f g : R → ℂ} (hf : Per c f) (hg : Per c g) : Per c (fun d => f d * g d) :=
  fun a b hab => by simp only [hf a b hab, hg a b hab]

lemma rsum_congr {c : R} {f g : R → ℂ} (h : ∀ d, f d = g d) : rsum c f = rsum c g := by
  unfold rsum; exact finsum_congr fun x => h _

lemma rsum_const_mul (c : R) (f : R → ℂ) (z : ℂ) : rsum c (fun d => z * f d) = z * rsum c f := by
  unfold rsum; rw [mul_finsum]

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

lemma sym_one_left {c : R} (hc : c ≠ 0) : S.sym 1 c = 1 := by
  have h0 := S.sym_ne_zero hc (isCoprime_one_left (x := c))
  have := S.sym_mul_left 1 1 c hc
  rw [one_mul] at this
  exact (mul_eq_left₀ h0).1 this.symm

lemma sym_pow_right (d : R) {c : R} (hc : c ≠ 0) (j : ℕ) : S.sym d (c ^ j) = S.sym d c ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero]; exact S.sym_unit_right d 1 isUnit_one
  | succ j ih => rw [pow_succ, S.sym_mul_right d _ _ (pow_ne_zero _ hc) hc, ih, pow_succ]

lemma sym_per {c : R} (hc : c ≠ 0) : Per c (fun d => (S.sym d c)⁻¹) :=
  fun a b hab => by simp only [S.sym_congr a b c hc hab]

end CubicSymbol

/-! ### The Gauss sum -/

variable (S : CubicSymbol R) (A : AddData R K)

/-- The summand of `g(ν, c)` is periodic modulo `c` (well-definedness). -/
lemma gauss_per (ν : R) {c : R} (hc : c ≠ 0) :
    Per c (fun d => (S.sym d c)⁻¹ * A.ψ (ν * d) c) := by
  refine (S.sym_per hc).mul fun a b hab => A.ψ_per hc ?_
  rw [← mul_sub]; exact hab.mul_left ν

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

/-- **(B7)**: `g(μ ν, c) = (μ/c) g(ν, c)` for `μ` prime to `c`. -/
theorem gauss_mul_left (ν : R) {μ c : R} (hc : c ≠ 0) (h : IsCoprime μ c) :
    gauss S A (μ * ν) c = S.sym μ c * gauss S A ν c := by
  have h0 := S.sym_ne_zero hc h
  unfold gauss
  rw [← rsum_mul_coprime_unit (gauss_per S A ν hc) h, ← rsum_const_mul]
  refine rsum_congr fun d => ?_
  rw [S.sym_mul_left _ _ _ hc, mul_inv, show ν * (μ * d) = μ * ν * d by ring]
  field_simp

/-! ### Constant-term sums -/

/-! ### Prime powers -/

end ArtinKP.B7
end

section
-- module Solutions.Artin.KP.B7_System
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # B7_System: the formal three-term linear system of MATH.md §4.1 and its solution (§4.3)

Everything here is polynomial algebra in formal quantities `q`, `G`, `G'`, `x`, `Ψ 0`, `Ψ 1`, `Ψ 2`.

* `tab q G G' k j` is the prime-power table of the Gauss sum `g(ν₀ π^k, π^j)` (`B7_Gauss`:
  `gauss_prime_pow_le`, `csum_prime_pow`, `phi_prime_pow`, `gauss_prime_pow_succ`,
  `gaussP_of_three_dvd`, `gauss_prime_pow_eq_zero`), with `G = g(ν₀, π) = (ν₀/π) g₁(π)` and
  `G' = (ν₀/π)² g₂(π)`.
* `Cform q G G' x Ψ k = ∑_{j ≤ k+1} tab k j · x^j · Ψ_{(k+j) mod 3}` is (4.1).
* `Cform_zero` … `Cform_five` are the closed forms listed in MATH §4.1 (all correct as printed).
* `Cform_add_three`: the general recursion `C_{k+3} = q³x³ C_k + (1 - q²x³) Ψ_{k mod 3}`.
* `solve`: at a point with `q⁴x³ = 1` (the theta point `x₀ = q^{-4/3}`), `C₃ = C₀` and `C₅ = C₂`
  force `Ψ₂ = 0`, `q·G·x·Ψ₁ = Ψ₀`, `q·C₀ = (q+1)Ψ₀` and `C₁ = q²x²·G'·C₀`.
* `periodic_of_solution`: conversely these relations give `q·C_k = (q+1)Ψ_{k mod 3}` and
  `C_{k+3} = C_k` for all `k` (so `C₄ = C₁` is automatic).
* `ratio_rpow`: over `ℂ` with `x₀ = q^{-4/3}`: `C₁ = q^{-2/3} · G' · C₀`.
-/

namespace ArtinKP.B7

section table

variable {A : Type*} [CommRing A]

variable (q G G' x : A) (Ψ : ℕ → A)

theorem Cform_zero : Cform q G G' x Ψ 0 = Ψ 0 + G * x * Ψ 1 := by
  simp [Cform, tab, Finset.sum_range_succ]

theorem Cform_one : Cform q G G' x Ψ 1 = Ψ 1 + q * G' * x ^ 2 * Ψ 0 := by
  simp [Cform, tab, Finset.sum_range_succ]

theorem Cform_two : Cform q G G' x Ψ 2 = (1 - q ^ 2 * x ^ 3) * Ψ 2 := by
  simp [Cform, tab, Finset.sum_range_succ]; ring

theorem Cform_three :
    Cform q G G' x Ψ 3 = (1 + (q ^ 3 - q ^ 2) * x ^ 3) * Ψ 0 + q ^ 3 * G * x ^ 4 * Ψ 1 := by
  simp [Cform, tab, Finset.sum_range_succ]; ring

theorem Cform_four :
    Cform q G G' x Ψ 4 = (1 + (q ^ 3 - q ^ 2) * x ^ 3) * Ψ 1 + q ^ 4 * G' * x ^ 5 * Ψ 0 := by
  simp [Cform, tab, Finset.sum_range_succ]; ring

theorem Cform_five :
    Cform q G G' x Ψ 5 = (1 + (q ^ 3 - q ^ 2) * x ^ 3 - q ^ 5 * x ^ 6) * Ψ 2 := by
  simp [Cform, tab, Finset.sum_range_succ]; ring

end table

end ArtinKP.B7
end

section
-- module Solutions.Artin.T12.C3B_Norm
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # C3B_Norm: the additive character on `R`, the unit ideal, and `a(1,1,1,1) = 1` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

lemma normalizedFactors_top : normalizedFactors (⊤ : Ideal (𝓞 F)) = 0 := by
  rw [← Ideal.one_eq_top, normalizedFactors_one]

end C3B

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

end ArtinKP.B7
end

section
-- module Solutions.Artin.KP.E_Series
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.thetaEquiv_apply _root_.ArtinKP.S2.cubicSymbol_sym
/-! # E_Series: the Kubota coefficient series and its splitting at a prime (corrected (4.1))

Abstract setting (`R` a domain; in the application `R = SInt 𝔪`):

* `Cls R` = nonzero classes of `R` modulo units (`(R∖0)/U_S`), `ClsP π` = those prime to `π`;
  `tsum_split`: a unit-invariant absolutely summable family over `Cls R` is the iterated sum over
  `c = π^j c'`, `π ∤ c'`.
* `Pairing S`: the pairing `⟨c, d⟩` (in the application `ι (c, d)_S`, WP-A's `HS`).
* `Kubota S A Sec`: the **interface** to the analytic packages.  A section `Φ : Sec` is seen only
  through its normalized finite Jacquet functional `Lam Φ c ν s = |c|_{S_f}^s · J_Φ(c; ν, s)`, and
  `act β = Ã(β)` (MATH2 §6.1).  The coefficient series is
  `aSer Φ ν s = ∑_{c ∈ (R∖0)/U} g(ν, c) · Lam Φ c ν s · N(c)^{-s}`.
* `aSer_split` — **(4.1′)**: for `π ∤ ν₀`, `Re s > 2`,
  `aSer Φ (ν₀ π^k) s = Cform q G G' x (m ↦ Y_m(Ã(π)^k Φ)) k`, with B7's `Cform` verbatim, `x = q^{-s}`,
  and the three `π`-coprime twisted series `Y_m(Ψ) = ∑_{π ∤ c'} g(ν₀,c') ((π/c')(c'/π))^{-m}
  Lam Ψ (π^m c') ν₀ s N(c')^{-s}`.
* `aSer_unit` (MATH2 Lemma 6.2), `Lam_act_act` (`Ã(β)Ã(β') = ⟨β,β'⟩ Ã(ββ')` on `Lam`),
  `Lam_iter_eq_pow`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ArtinKP.E

open ArtinKP.B7

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]

/-! ### Classes modulo units -/

lemma rp_not_dvd {π : R} (b : ClsP π) : ¬ π ∣ rp b.1 := by
  intro h
  apply b.2.2
  rw [← mk_rp b.1]
  exact Associates.mk_dvd_mk.2 h

lemma isCoprime_of_isUnit {u : R} (hu : IsUnit u) {c : R} : IsCoprime u c := by
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  exact ⟨v, 0, by rw [zero_mul, add_zero, hv]⟩

lemma UInv.of_associated {f : R → ℂ} (hf : UInv f) {c d : R} (hc : c ≠ 0) (h : Associated c d) :
    f c = f d := by
  obtain ⟨u, rfl⟩ := h
  rw [mul_comm, hf _ _ u.isUnit hc]

lemma UInv.rp_mk {f : R → ℂ} (hf : UInv f) {c : R} (hc : c ≠ 0) :
    f (rp (Associates.mk c)) = f c := by
  have hne : rp (Associates.mk c) ≠ 0 := rp_ne_zero (by simpa using hc)
  exact hf.of_associated hne (Associates.mk_eq_mk_iff_associated.1 (mk_rp _))

theorem split_bijective {π : R} (hπ : Prime π)
    (hmult : ∀ c : R, c ≠ 0 → ∃ n : ℕ, ¬ π ^ (n + 1) ∣ c) :
    Function.Bijective
      (fun p : ℕ × ClsP π => (⟨splitFun π p, splitFun_ne_zero hπ.ne_zero p⟩ : Cls R)) := by
  have hP0 : Associates.mk π ≠ 0 := by simpa using hπ.ne_zero
  have key : ∀ (j j' : ℕ) (b b' : ClsP π), j < j' →
      Associates.mk π ^ j * b.1 ≠ Associates.mk π ^ j' * b'.1 := by
    intro j j' b b' hjj' h
    obtain ⟨d, rfl⟩ : ∃ d, j' = j + (d + 1) := ⟨j' - j - 1, by omega⟩
    rw [pow_add, mul_assoc] at h
    have h2 := mul_left_cancel₀ (pow_ne_zero j hP0) h
    apply b.2.2
    rw [h2]
    exact Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero d)) _
  constructor
  · rintro ⟨j, b⟩ ⟨j', b'⟩ h
    have h' : Associates.mk π ^ j * b.1 = Associates.mk π ^ j' * b'.1 := congrArg Subtype.val h
    rcases Nat.lt_trichotomy j j' with hlt | heq | hgt
    · exact absurd h' (key j j' b b' hlt)
    · subst heq
      have := mul_left_cancel₀ (pow_ne_zero j hP0) h'
      rw [Prod.mk.injEq]
      exact ⟨rfl, Subtype.ext this⟩
    · exact absurd h'.symm (key j' j b' b hgt)
  · rintro ⟨a, ha⟩
    have hc : rp a ≠ 0 := rp_ne_zero ha
    have hex := hmult (rp a) hc
    classical
    have hmin := fun (m : ℕ) (h : m < Nat.find hex) => Nat.find_min hex h
    have hspec := Nat.find_spec hex
    set j := Nat.find hex with hj
    have hdvd : π ^ j ∣ rp a := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0, pow_zero]; exact one_dvd _
      · have := hmin (j - 1) (by omega)
        rw [not_not, Nat.sub_add_cancel hpos] at this
        exact this
    obtain ⟨c', hc'⟩ := hdvd
    have hc'0 : c' ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hc'
      exact hc hc'
    have hnd : ¬ π ∣ c' := by
      rintro ⟨r, rfl⟩
      apply hspec
      rw [hc', pow_succ, ← mul_assoc]
      exact Dvd.intro _ rfl
    refine ⟨(j, ⟨Associates.mk c', by simpa using hc'0, by
      rw [Associates.mk_dvd_mk]; exact hnd⟩), ?_⟩
    apply Subtype.ext
    show Associates.mk π ^ j * Associates.mk c' = a
    rw [← Associates.mk_pow, Associates.mk_mul_mk, ← hc', mk_rp]

/-- **Splitting of an absolutely convergent sum over classes** at a prime `π` of finite
multiplicity: `∑_c f(c) = ∑_j ∑_{π ∤ c'} f(π^j c')`. -/
theorem tsum_split {π : R} (hπ : Prime π)
    (hmult : ∀ c : R, c ≠ 0 → ∃ n : ℕ, ¬ π ^ (n + 1) ∣ c) (f : R → ℂ) (hf : UInv f)
    (hs : Summable (fun a : Cls R => f (rp a.1))) :
    ∑' a : Cls R, f (rp a.1) = ∑' j : ℕ, ∑' b : ClsP π, f (π ^ j * rp b.1) := by
  set E := Equiv.ofBijective _ (split_bijective hπ hmult) with hE
  have hterm : ∀ p : ℕ × ClsP π, f (rp (E p).1) = f (π ^ p.1 * rp p.2.1) := by
    rintro ⟨j, b⟩
    have hb0 : rp b.1 ≠ 0 := rp_ne_zero b.2.1
    have h1 : (E (j, b)).1 = Associates.mk (π ^ j * rp b.1) := by
      show Associates.mk π ^ j * b.1 = _
      rw [← Associates.mk_mul_mk, Associates.mk_pow, mk_rp]
    rw [h1]
    exact hf.rp_mk (mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hb0)
  have hs' : Summable (fun p : ℕ × ClsP π => f (rp (E p).1)) := E.summable_iff.2 hs
  rw [← E.tsum_eq (fun a : Cls R => f (rp a.1))]
  rw [hs'.tsum_prod' (fun j => hs'.comp_injective (Prod.mk_right_injective j))]
  exact tsum_congr fun j => tsum_congr fun b => hterm (j, b)

/-! ### The norm `N(c) = #(R/cR)` -/

lemma nrm_unit_mul {u : R} (c : R) (hu : IsUnit u) : nrm (u * c) = nrm c := by
  unfold nrm
  rw [Ideal.span_singleton_mul_left_unit hu]

lemma nrm_one : nrm (1 : R) = 1 := by
  unfold nrm
  have : Subsingleton (R ⧸ Ideal.span {(1 : R)}) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  rw [Nat.card_of_subsingleton (0 : R ⧸ Ideal.span {(1 : R)})]
  simp

lemma nrm_mul (hfin : ∀ c : R, c ≠ 0 → Finite (R ⧸ Ideal.span {c})) {c c' : R} (hc : c ≠ 0)
    (hc' : c' ≠ 0) : nrm (c * c') = nrm c * nrm c' := by
  have := hfin c hc
  have := hfin c' hc'
  have := hfin (c * c') (mul_ne_zero hc hc')
  have h := rsum_mul_of_per (c := c) (c' := c') hc (f := fun _ => (1 : ℂ)) (fun _ _ _ => rfl)
  rw [rsum_one, rsum_one] at h
  unfold nrm
  rw [h, mul_comm]

lemma nrm_pow (hfin : ∀ c : R, c ≠ 0 → Finite (R ⧸ Ideal.span {c})) {c : R} (hc : c ≠ 0)
    (j : ℕ) : nrm (c ^ j) = nrm c ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero, nrm_one]
  | succ j ih => rw [pow_succ, nrm_mul hfin (pow_ne_zero _ hc) hc, ih, pow_succ]

lemma natpow_cpow (q j : ℕ) (s : ℂ) : (((q : ℂ)) ^ j) ^ s = ((q : ℂ) ^ s) ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero, Complex.one_cpow]
  | succ j ih =>
    rw [pow_succ, pow_succ, ← ih, ← Nat.cast_pow, Complex.natCast_mul_natCast_cpow]

lemma nrm_pow_mul_cpow (hfin : ∀ c : R, c ≠ 0 → Finite (R ⧸ Ideal.span {c})) {π c' : R}
    (hπ : π ≠ 0) (hc' : c' ≠ 0) (j : ℕ) (s : ℂ) :
    nrm (π ^ j * c') ^ s = (nrm π ^ s) ^ j * nrm c' ^ s := by
  rw [nrm_mul hfin (pow_ne_zero _ hπ) hc', nrm_pow hfin hπ]
  unfold nrm
  rw [← Nat.cast_pow, Complex.natCast_mul_natCast_cpow, Nat.cast_pow, natpow_cpow]

/-! ### Symbols -/

lemma inv_eq_sq_of_cube {z : ℂ} (h : z ^ 3 = 1) : z⁻¹ = z ^ 2 :=
  (eq_inv_of_mul_eq_one_left (by rw [← h]; ring)).symm

lemma pow_eq_pow_of_cube {z : ℂ} (h : z ^ 3 = 1) {a b : ℕ} (hab : a % 3 = b % 3) :
    z ^ a = z ^ b := by
  have ha : z ^ a = z ^ (a % 3) := by
    conv_lhs => rw [← Nat.div_add_mod a 3, pow_add, pow_mul, h, one_pow, one_mul]
  have hb : z ^ b = z ^ (b % 3) := by
    conv_lhs => rw [← Nat.div_add_mod b 3, pow_add, pow_mul, h, one_pow, one_mul]
  rw [ha, hb, hab]

lemma sym_pow_left (S : CubicSymbol R) (d : R) {c : R} (hc : c ≠ 0) (j : ℕ) :
    S.sym (d ^ j) c = S.sym d c ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero, S.sym_one_left hc]
  | succ j ih => rw [pow_succ, S.sym_mul_left _ _ _ hc, ih, pow_succ]

namespace Pairing

variable {S : CubicSymbol R} (B : Pairing S)

lemma br_ne_zero {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) : B.br a b ≠ 0 := by
  intro h
  have := B.br_pow_three a b ha hb
  rw [h] at this
  norm_num at this

lemma br_one_left {b : R} (hb : b ≠ 0) : B.br 1 b = 1 := by
  have h := B.br_mul_left 1 1 b one_ne_zero one_ne_zero hb
  rw [one_mul] at h
  exact (mul_eq_left₀ (B.br_ne_zero one_ne_zero hb)).1 h.symm

lemma br_one_right {a : R} (ha : a ≠ 0) : B.br a 1 = 1 := by
  have h := B.br_mul_right a 1 1 ha one_ne_zero one_ne_zero
  rw [one_mul] at h
  exact (mul_eq_left₀ (B.br_ne_zero ha one_ne_zero)).1 h.symm

lemma br_pow_left {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) (n : ℕ) :
    B.br (a ^ n) b = B.br a b ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, B.br_one_left hb]
  | succ n ih => rw [pow_succ, B.br_mul_left _ _ _ (pow_ne_zero _ ha) ha hb, ih, pow_succ]

lemma br_pow_right {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) (n : ℕ) :
    B.br a (b ^ n) = B.br a b ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, B.br_one_right ha]
  | succ n ih => rw [pow_succ, B.br_mul_right _ _ _ ha (pow_ne_zero _ hb) hb, ih, pow_succ]

/-- `⟨π^n c, π⟩ = ⟨c, π⟩`. -/
lemma br_pow_mul_self {π c : R} (hπ : π ≠ 0) (hc : c ≠ 0) (n : ℕ) :
    B.br (π ^ n * c) π = B.br c π := by
  rw [B.br_mul_left _ _ _ (pow_ne_zero _ hπ) hc hπ, B.br_pow_left hπ hπ, B.br_self π hπ, one_pow,
    one_mul]

/-- `⟨c, ε⟩ = (ε/c)` for a unit `ε` (MATH2 §0.1). -/
lemma br_unit {c ε : R} (hc : c ≠ 0) (hε : IsUnit ε) : B.br c ε = S.sym ε c := by
  have h := B.br_coprime c ε hc hε.ne_zero (isCoprime_comm.1 (isCoprime_of_isUnit hε))
  rwa [S.sym_unit_right c ε hε, mul_one] at h

end Pairing

/-! ### Gauss sums: units and the splitting `c = π^j c'` -/

section gauss

variable (S : CubicSymbol R) (A : AddData R K)
  (hfin : ∀ c : R, c ≠ 0 → Finite (R ⧸ Ideal.span {c}))

lemma gauss_of_isUnit (ν : R) {u : R} (hu : IsUnit u) : gauss S A ν u = 1 := by
  have : Subsingleton (R ⧸ Ideal.span {u}) :=
    Ideal.Quotient.subsingleton_iff.2 (Ideal.span_singleton_eq_top.2 hu)
  have : Unique (R ⧸ Ideal.span {u}) := Unique.mk' _
  unfold gauss rsum
  rw [finsum_unique]
  beta_reduce
  rw [S.sym_unit_right _ u hu, inv_one, one_mul]
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have key : ∀ d : R, A.ψ (ν * d) u = 1 := fun d => by
    have h : ν * d = u * (v * (ν * d)) := by rw [← mul_assoc, hv, one_mul]
    rw [h, A.ψ_mul_self hu.ne_zero]
  exact key _

include hfin in
/-- `g(ν, εc) = (ε/c)⁻¹ g(ν, c)` for a unit `ε`. -/
theorem gauss_unit_mul (ν : R) {u c : R} (hu : IsUnit u) (hc : c ≠ 0) :
    gauss S A ν (u * c) = (S.sym u c)⁻¹ * gauss S A ν c := by
  have := hfin u hu.ne_zero
  have := hfin c hc
  rw [gauss_mul S A ν hu.ne_zero hc (isCoprime_of_isUnit hu), S.sym_unit_right c u hu,
    gauss_of_isUnit S A ν hu]
  simp

include hfin in
/-- **(4.2)** in symmetric form, with no reciprocity: for `c'` prime to `π`,
`g(ν₀π^k, π^j c') = g(ν₀π^k, π^j) · g(ν₀, c') · (π/c')^{k−j} · (c'/π)^{−j}`. -/
theorem gauss_split {π : R} (hπ : π ≠ 0) (ν₀ : R) (k j : ℕ) {c' : R} (hc' : c' ≠ 0)
    (hcop : IsCoprime π c') :
    gauss S A (ν₀ * π ^ k) (π ^ j * c') =
      gauss S A (ν₀ * π ^ k) (π ^ j) * gauss S A ν₀ c' * S.sym π c' ^ k *
        ((S.sym π c')⁻¹) ^ j * ((S.sym c' π)⁻¹) ^ j := by
  have := hfin (π ^ j) (pow_ne_zero _ hπ)
  have := hfin c' hc'
  rw [gauss_mul S A _ (pow_ne_zero _ hπ) hc' hcop.pow_left, sym_pow_left S π hc',
    S.sym_pow_right c' hπ, mul_comm ν₀ (π ^ k), gauss_mul_left S A ν₀ hc' hcop.pow_left,
    sym_pow_left S π hc', inv_pow, inv_pow]
  ring

end gauss

/-! ### The interface -/

namespace Kubota

variable {S : CubicSymbol R} {A : AddData R K} {Sec : Type*} (D : Kubota S A Sec)
  (hfin : ∀ c : R, c ≠ 0 → Finite (R ⧸ Ideal.span {c}))

include hfin in
lemma term_uinv (Φ : Sec) (ν : R) {s : ℂ} (hs : 2 < s.re) : UInv (D.term Φ ν s) := by
  intro u c hu hc
  have h0 : S.sym u c ≠ 0 := S.sym_ne_zero hc (isCoprime_of_isUnit hu)
  unfold term
  rw [gauss_unit_mul S A hfin ν hu hc, D.Lam_unit Φ u c ν s hu hc hs, nrm_unit_mul c hu]
  field_simp

lemma LEq.refl (Φ : Sec) : D.LEq Φ Φ 1 := fun c ν s _ _ => (one_mul _).symm

lemma LEq.trans {Φ Ψ Ξ : Sec} {z w : ℂ} (h₁ : D.LEq Φ Ψ z) (h₂ : D.LEq Ψ Ξ w) :
    D.LEq Φ Ξ (z * w) := fun c ν s hc hs => by rw [h₁ c ν s hc hs, h₂ c ν s hc hs, mul_assoc]

lemma LEq.act {Φ Ψ : Sec} {z : ℂ} (h : D.LEq Φ Ψ z) {β : R} (hβ : β ≠ 0) :
    D.LEq (D.act β Φ) (D.act β Ψ) z := fun c ν s hc hs => by
  rw [D.Lam_act Φ β c ν s hβ hc hs, D.Lam_act Ψ β c ν s hβ hc hs,
    h _ _ s (mul_ne_zero (pow_ne_zero _ hβ) hc) hs]
  ring

lemma LEq.iterate {Φ Ψ : Sec} {z : ℂ} (h : D.LEq Φ Ψ z) {β : R} (hβ : β ≠ 0) (n : ℕ) :
    D.LEq ((D.act β)^[n] Φ) ((D.act β)^[n] Ψ) z := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact ih.act D hβ

lemma LEq.aSer {Φ Ψ : Sec} {z : ℂ} (h : D.LEq Φ Ψ z) (ν : R) {s : ℂ} (hs : 2 < s.re) :
    D.aSer Φ ν s = z * D.aSer Ψ ν s := by
  unfold Kubota.aSer
  rw [← tsum_mul_left]
  refine tsum_congr fun a => ?_
  unfold term
  rw [h _ ν s (rp_ne_zero a.2) hs]
  ring

/-- `Ã(β)Ã(β') = ⟨β,β'⟩ Ã(ββ')` at the level of `Lam` (MATH2 Lemma 6.1(ii)). -/
theorem Lam_act_act (Φ : Sec) {β β' : R} (hβ : β ≠ 0) (hβ' : β' ≠ 0) :
    D.LEq (D.act β (D.act β' Φ)) (D.act (β * β') Φ) (D.br β β') := by
  intro c ν s hc hs
  have hβc : β ^ 2 * c ≠ 0 := mul_ne_zero (pow_ne_zero _ hβ) hc
  rw [D.Lam_act _ β c ν s hβ hc hs, D.Lam_act Φ β' _ _ s hβ' hβc hs,
    D.Lam_act Φ (β * β') c ν s (mul_ne_zero hβ hβ') hc hs,
    D.br_mul_left _ _ _ (pow_ne_zero _ hβ) hc hβ', D.toPairing.br_pow_left hβ hβ',
    D.br_mul_right _ _ _ hc hβ hβ',
    show β' ^ 2 * (β ^ 2 * c) = (β * β') ^ 2 * c by ring, show β' * (β * ν) = β * β' * ν by ring]
  have h3 := D.br_pow_three β β' hβ hβ'
  have h4 : D.br β β' ^ 4 = D.br β β' := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
  linear_combination (D.br c β ^ 2 * D.br c β' ^ 2 * D.Lam Φ ((β * β') ^ 2 * c) (β * β' * ν) s) * h4

/-- `Ã(π)^k` on `Lam`: `Lam (Ã(π)^k Φ) c ν = ⟨c,π⟩^{2k} Lam Φ (π^{2k} c) (π^k ν)`. -/
theorem Lam_iter (Φ : Sec) {π : R} (hπ : π ≠ 0) (k : ℕ) (c ν : R) {s : ℂ} (hc : c ≠ 0)
    (hs : 2 < s.re) :
    D.Lam ((D.act π)^[k] Φ) c ν s =
      D.br c π ^ (2 * k) * D.Lam Φ (π ^ (2 * k) * c) (π ^ k * ν) s := by
  induction k generalizing c ν with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', D.Lam_act _ π c ν s hπ hc hs,
      ih _ _ (mul_ne_zero (pow_ne_zero _ hπ) hc), D.toPairing.br_pow_mul_self hπ hc,
      show π ^ (2 * k) * (π ^ 2 * c) = π ^ (2 * (k + 1)) * c by ring,
      show π ^ k * (π * ν) = π ^ (k + 1) * ν by ring]
    ring

/-- `Ã(π)^e` and `Ã(π^e)` have the same `Lam`. -/
theorem Lam_iter_eq_pow (Φ : Sec) {π : R} (hπ : π ≠ 0) (e : ℕ) :
    D.LEq ((D.act π)^[e] Φ) (D.act (π ^ e) Φ) 1 := by
  intro c ν s hc hs
  rw [D.Lam_iter Φ hπ e c ν hc hs, D.Lam_act Φ (π ^ e) c ν s (pow_ne_zero _ hπ) hc hs,
    D.toPairing.br_pow_right hc hπ, one_mul, ← pow_mul, ← pow_mul, mul_comm e 2]

include hfin in
/-- **MATH2 Lemma 6.2** (units, exact in `s`): `𝔞_Φ(εν, s) = 𝔞_{Ã(ε)Φ}(ν, s)`. -/
theorem aSer_unit (Φ : Sec) {ε : R} (hε : IsUnit ε) (ν : R) {s : ℂ} (hs : 2 < s.re) :
    D.aSer Φ (ε * ν) s = D.aSer (D.act ε Φ) ν s := by
  unfold aSer
  refine tsum_congr fun a => ?_
  have hc : rp a.1 ≠ 0 := rp_ne_zero a.2
  set c := rp a.1
  have hcop : IsCoprime ε c := isCoprime_of_isUnit hε
  have h3 := S.sym_pow_three ε c hc hcop
  unfold term
  rw [gauss_mul_left S A ν hc hcop, D.Lam_act Φ ε c ν s hε.ne_zero hc hs,
    D.Lam_unit Φ (ε ^ 2) c (ε * ν) s (hε.pow 2) hc hs, sym_pow_left S ε hc,
    D.toPairing.br_unit hc hε]
  have h4 : S.sym ε c ^ 4 = S.sym ε c := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
  linear_combination
    (-(gauss S A ν c * D.Lam Φ c (ε * ν) s * nrm c ^ (-s))) * h4

end Kubota

/-! ### The prime datum and the splitting (4.1′) -/

lemma PrimeDatum.prime {S : CubicSymbol R} {A : AddData R K} {π : R} {g1 g2 : ℂ}
    (P : PrimeDatum S A π g1 g2) : Prime π :=
  (Ideal.span_singleton_prime P.ne_zero).1 P.isMax.isPrime

namespace Kubota

variable {S : CubicSymbol R} {A : AddData R K} {Sec : Type*} (D : Kubota S A Sec)
  (hfin : ∀ c : R, c ≠ 0 → Finite (R ⧸ Ideal.span {c}))

lemma LEq.Y {Φ Ψ : Sec} {z : ℂ} (h : D.LEq Φ Ψ z) (π ν₀ : R) (hπ : π ≠ 0) (m : ℕ) {s : ℂ}
    (hs : 2 < s.re) : D.Y π Φ ν₀ m s = z * D.Y π Ψ ν₀ m s := by
  unfold Kubota.Y
  rw [← tsum_mul_left]
  refine tsum_congr fun b => ?_
  unfold Yterm
  rw [h _ ν₀ s (mul_ne_zero (pow_ne_zero _ hπ) (rp_ne_zero b.2.1)) hs]
  ring

include hfin in
/-- The termwise identity behind (4.1′). -/
theorem term_split {π : R} {g1 g2 : ℂ} (P : PrimeDatum S A π g1 g2)
    {ν₀ : R} (hν₀ : ¬ π ∣ ν₀) {s : ℂ} (hs : 2 < s.re) (Φ : Sec) (k j : ℕ) {c' : R}
    (hc' : c' ≠ 0) (hcop : ¬ π ∣ c') :
    D.term Φ (ν₀ * π ^ k) s (π ^ j * c') =
      tab (nrm π) (S.sym ν₀ π * g1) (S.sym ν₀ π ^ 2 * g2) k j * (nrm π ^ (-s)) ^ j *
        D.Yterm π ((D.act π)^[k] Φ) ν₀ ((k + j) % 3) s c' := by
  have hπ := P.ne_zero
  have hc1 : IsCoprime c' π := (isCoprime_iff_not_dvd P.isMax c').2 hcop
  have hc2 : IsCoprime π c' := hc1.symm
  unfold term Yterm
  rw [gauss_split S A hfin hπ ν₀ k j hc' hc2, P.table ν₀ hν₀ k j,
    nrm_pow_mul_cpow hfin hπ hc' j (-s)]
  by_cases hj : j ≤ k + 1
  · obtain ⟨t, ht⟩ : ∃ t, 2 * k + (k + j) % 3 = j + 3 * t :=
      ⟨(2 * k + (k + j) % 3 - j) / 3, by omega⟩
    have hLam : D.Lam ((D.act π)^[k] Φ) (π ^ ((k + j) % 3) * c') ν₀ s =
        D.br c' π ^ (2 * k) * D.Lam Φ (π ^ j * c') (ν₀ * π ^ k) s := by
      rw [D.Lam_iter Φ hπ k _ ν₀ (mul_ne_zero (pow_ne_zero _ hπ) hc') hs,
        D.toPairing.br_pow_mul_self hπ hc', ← mul_assoc, ← pow_add, ht, mul_comm (π ^ k) ν₀,
        show π ^ (j + 3 * t) * c' = (π ^ t) ^ 3 * (π ^ j * c') by ring,
        D.Lam_cube Φ (π ^ t) _ _ s (pow_ne_zero _ hπ) (mul_ne_zero (pow_ne_zero _ hπ) hc') hs]
    rw [hLam]
    set u := S.sym π c' with hu
    set v := S.sym c' π with hv
    set b := D.br c' π with hb
    have hu3 : u ^ 3 = 1 := S.sym_pow_three π c' hc' hc2
    have hv3 : v ^ 3 = 1 := S.sym_pow_three c' π hπ hc1
    have hbv : b * v = u := D.br_coprime c' π hc' hπ hc1
    have hv0 : v ≠ 0 := S.sym_ne_zero hπ hc1
    have hb' : b = u * v ^ 2 := by
      rw [← hbv]
      linear_combination (-b) * hv3
    have hwt : u ^ k * (u⁻¹) ^ j * (v⁻¹) ^ j = wt S π ((k + j) % 3) c' * b ^ (2 * k) := by
      unfold wt
      rw [← hu, ← hv, hb', mul_inv, inv_eq_sq_of_cube hu3, inv_eq_sq_of_cube hv3, mul_pow, mul_pow,
        ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
      have e1 : u ^ k * u ^ (2 * j) = u ^ (2 * ((k + j) % 3)) * u ^ (2 * k) := by
        rw [← pow_add, ← pow_add]
        exact pow_eq_pow_of_cube hu3 (by omega)
      have e2 : v ^ (2 * j) = v ^ (2 * ((k + j) % 3)) * v ^ (2 * (2 * k)) := by
        rw [← pow_add]
        exact pow_eq_pow_of_cube hv3 (by omega)
      rw [e2]
      linear_combination (v ^ (2 * ((k + j) % 3)) * v ^ (2 * (2 * k))) * e1
    linear_combination
      (tab (nrm π) (S.sym ν₀ π * g1) (S.sym ν₀ π ^ 2 * g2) k j * gauss S A ν₀ c' *
        D.Lam Φ (π ^ j * c') (ν₀ * π ^ k) s * ((nrm π ^ (-s)) ^ j * nrm c' ^ (-s))) * hwt
  · have h0 : tab (nrm π) (S.sym ν₀ π * g1) (S.sym ν₀ π ^ 2 * g2) k j = 0 := by
      unfold tab
      rw [if_neg (by omega), if_neg (by omega)]
    rw [h0]
    simp

include hfin in
/-- **(4.1′), the corrected (4.1)** (MATH2 §4.3 in the `Lam`-normalization): for `π ∤ ν₀` and
`Re s > 2`, as an identity of absolutely convergent series,
`𝔞_Φ(ν₀π^k, s) = ∑_{j ≤ k+1} g(ν₀π^k, π^j) x^j Y_{(k+j) mod 3}(Ã(π)^k Φ; ν₀, s)`, `x = q^{-s}`. -/
theorem aSer_split {π : R} {g1 g2 : ℂ} (P : PrimeDatum S A π g1 g2)
    {ν₀ : R} (hν₀ : ¬ π ∣ ν₀) {s : ℂ} (hs : 2 < s.re) (Φ : Sec) (k : ℕ) :
    D.aSer Φ (ν₀ * π ^ k) s =
      Cform (nrm π) (S.sym ν₀ π * g1) (S.sym ν₀ π ^ 2 * g2) (nrm π ^ (-s))
        (fun m => D.Y π ((D.act π)^[k] Φ) ν₀ m s) k := by
  have hν0 : ν₀ ≠ 0 := fun h => hν₀ (h ▸ dvd_zero π)
  have hne : ν₀ * π ^ k ≠ 0 := mul_ne_zero hν0 (pow_ne_zero _ P.ne_zero)
  have hsum := D.summable Φ (ν₀ * π ^ k) s hne hs
  unfold aSer
  rw [tsum_split P.prime P.mult _ (D.term_uinv hfin Φ _ hs) hsum]
  have h1 : ∀ j : ℕ, ∑' b : ClsP π, D.term Φ (ν₀ * π ^ k) s (π ^ j * rp b.1) =
      tab (nrm π) (S.sym ν₀ π * g1) (S.sym ν₀ π ^ 2 * g2) k j * (nrm π ^ (-s)) ^ j *
        D.Y π ((D.act π)^[k] Φ) ν₀ ((k + j) % 3) s := by
    intro j
    unfold Kubota.Y
    rw [← tsum_mul_left]
    exact tsum_congr fun b =>
      D.term_split hfin P hν₀ hs Φ k j (rp_ne_zero b.2.1) (rp_not_dvd b)
  simp_rw [h1]
  rw [tsum_eq_sum (s := Finset.range (k + 2))]
  · rfl
  · intro j hj
    rw [Finset.mem_range, not_lt] at hj
    have h0 : tab (nrm π) (S.sym ν₀ π * g1) (S.sym ν₀ π ^ 2 * g2) k j = 0 := by
      unfold tab
      rw [if_neg (by omega), if_neg (by omega)]
    rw [h0, zero_mul, zero_mul]

end Kubota

end ArtinKP.E
end

section
-- module Solutions.Artin.KP.E_Residue
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
/-! # E_Residue: passage to residues and the solution of the system at one prime

* `ResFun s₀`: the abstract **residue functional** — a relation `HasRes f r` ("`f`, given on
  `Re s > 2`, has residue `r` at `s₀`") with exactly the properties (R3)/(R5) of MATH §3.0:
  it depends only on `f` on `Re s > 2`, is additive, is compatible with multiplication by entire
  functions, and the residue is unique.  (`E_Model` shows that the intended definition —
  holomorphic continuation to a connected open set followed by a limit along a ray — has these
  properties.)
* `Theta D s₀`: a residue functional together with the residues `tau Φ ν` of the coefficient
  series `D.aSer Φ ν`.
* `PER T π`: cube periodicity in the exact form of MATH2 §4.4, `τ_Φ(νπ³) = τ_{Ã(π)³Φ}(ν)`.
* Given `PER T π` and `q⁴ x₀³ = 1` (`x₀ = q^{-s₀}`, i.e. `s₀ = 4/3`), for `π ∤ ν₀`:
  `tau_mul_prime` (E1): `τ_Φ(ν₀π) = q² x₀² (ν₀/π)² g₂ · τ_{Ã(π)Φ}(ν₀)`,
  `tau_mul_prime_sq` (E2): `τ_Φ(ν₀π²) = 0`,
  `tau_mul_prime_pow`: `τ_Φ(ν₀π^e) = w(e) (ν₀/π)^{2e} τ_{Ã(π)^eΦ}(ν₀)`, `w = 1, q²x₀²g₂, 0`.
  No division by the determinant is needed and the `Y_m` need no residues: the unknowns are
  eliminated among `C₀, C₁, C₃, C₄` (resp. `C₂, C₅`) by polynomial multipliers.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ArtinKP.E

open ArtinKP.B7

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]

namespace ResFun

variable {s₀ : ℂ} (T : ResFun s₀)

/-- One-term transfer of an identity on `Re s > 2` to residues. -/
lemma lin1 {f₁ f₂ : ℂ → ℂ} {r₁ r₂ : ℂ} (h₁ h₂ : ℂ → ℂ) (d₁ : Differentiable ℂ h₁)
    (d₂ : Differentiable ℂ h₂) (R₁ : T.HasRes f₁ r₁) (R₂ : T.HasRes f₂ r₂)
    (H : ∀ s : ℂ, 2 < s.re → h₁ s * f₁ s = h₂ s * f₂ s) : h₁ s₀ * r₁ = h₂ s₀ * r₂ :=
  T.unique (T.congr (T.smul h₁ d₁ R₁) H) (T.smul h₂ d₂ R₂)

/-- Two-term transfer of an identity on `Re s > 2` to residues. -/
lemma lin2 {f₁ f₂ f₃ f₄ : ℂ → ℂ} {r₁ r₂ r₃ r₄ : ℂ} (h₁ h₂ h₃ h₄ : ℂ → ℂ)
    (d₁ : Differentiable ℂ h₁) (d₂ : Differentiable ℂ h₂) (d₃ : Differentiable ℂ h₃)
    (d₄ : Differentiable ℂ h₄) (R₁ : T.HasRes f₁ r₁) (R₂ : T.HasRes f₂ r₂)
    (R₃ : T.HasRes f₃ r₃) (R₄ : T.HasRes f₄ r₄)
    (H : ∀ s : ℂ, 2 < s.re → h₁ s * f₁ s + h₂ s * f₂ s = h₃ s * f₃ s + h₄ s * f₄ s) :
    h₁ s₀ * r₁ + h₂ s₀ * r₂ = h₃ s₀ * r₃ + h₄ s₀ * r₄ :=
  T.unique (T.congr (T.add (T.smul h₁ d₁ R₁) (T.smul h₂ d₂ R₂)) H)
    (T.add (T.smul h₃ d₃ R₃) (T.smul h₄ d₄ R₄))

end ResFun

namespace Theta

variable {S : CubicSymbol R} {A : AddData R K} {Sec : Type*} {D : Kubota S A Sec} {s₀ : ℂ}
  (T : Theta D s₀) (hfin : ∀ c : R, c ≠ 0 → Finite (R ⧸ Ideal.span {c}))

/-- `τ` sees a section only through `Lam`, linearly. -/
theorem tau_congr {Φ Ψ : Sec} {z : ℂ} (h : D.LEq Φ Ψ z) {ν : R} (hν : ν ≠ 0) :
    T.tau Φ ν = z * T.tau Ψ ν := by
  have h1 := T.smul (fun _ => z) (differentiable_const z) (T.tau_spec Ψ ν hν)
  have h2 := T.congr h1 (fun s hs => (h.aSer D ν hs).symm)
  exact T.unique (T.tau_spec Φ ν hν) h2

include hfin in
/-- MATH2 Lemma 6.2 for residues: `τ_Φ(εν) = τ_{Ã(ε)Φ}(ν)` for a unit `ε`. -/
theorem tau_unit (Φ : Sec) {ε : R} (hε : IsUnit ε) {ν : R} (hν : ν ≠ 0) :
    T.tau Φ (ε * ν) = T.tau (D.act ε Φ) ν :=
  T.unique (T.tau_spec Φ _ (mul_ne_zero hε.ne_zero hν))
    (T.congr (T.tau_spec (D.act ε Φ) ν hν) (fun s hs => (D.aSer_unit hfin Φ hε ν hs).symm))

/-- Preimages under iterates of `Ã(π)`, up to `Lam`. -/
lemma _root_.ArtinKP.E.Kubota.exists_pre (D : Kubota S A Sec) {π : R} (hπ : π ≠ 0) (n : ℕ)
    (Φ : Sec) :
    ∃ Φ' : Sec, D.LEq ((D.act π)^[n] Φ') Φ 1 := by
  induction n generalizing Φ with
  | zero => exact ⟨Φ, Kubota.LEq.refl D Φ⟩
  | succ n ih =>
    obtain ⟨Φ₁, h₁⟩ := D.act_surj π Φ hπ
    obtain ⟨Φ', h'⟩ := ih Φ₁
    refine ⟨Φ', ?_⟩
    rw [Function.iterate_succ_apply']
    intro c ν s hc hs
    rw [(h'.act D hπ) c ν s hc hs, h₁ c ν s hc hs]

section prime

variable {π : R} {g1 g2 : ℂ} (P : PrimeDatum S A π g1 g2)

include P in
lemma nrm_ne_zero : nrm π ≠ 0 := by
  unfold nrm
  have := P.one_lt
  exact_mod_cast (by omega : Nat.card (R ⧸ Ideal.span {π}) ≠ 0)

include P in
lemma nrm_ne_one : nrm π ≠ 1 := by
  unfold nrm
  have := P.one_lt
  exact_mod_cast (by omega : Nat.card (R ⧸ Ideal.span {π}) ≠ 1)

include P in
lemma differentiable_x : Differentiable ℂ (fun s : ℂ => nrm π ^ (-s)) :=
  (differentiable_id.neg).const_cpow (Or.inl (nrm_ne_zero P))

include P hfin in
/-- The series identity with a fixed section of the unknowns: if `Ã(π)^k Φ` and `Ψ` have the same
`Lam`, then `𝔞_Φ(ν₀π^k, s) = C_k(Y(Ψ))`. -/
lemma aSer_eq_Cform {ν₀ : R} (hν₀ : ¬ π ∣ ν₀) {Φ Ψ : Sec} (k : ℕ)
    (h : D.LEq ((D.act π)^[k] Φ) Ψ 1) {s : ℂ} (hs : 2 < s.re) :
    D.aSer Φ (ν₀ * π ^ k) s =
      Cform (nrm π) (S.sym ν₀ π * g1) (S.sym ν₀ π ^ 2 * g2) (nrm π ^ (-s))
        (fun m => D.Y π Ψ ν₀ m s) k := by
  rw [D.aSer_split hfin P hν₀ hs Φ k]
  congr 1
  funext m
  rw [h.Y D π ν₀ P.ne_zero m hs, one_mul]

include P hfin in
/-- **(E1)**: `τ_Φ(ν₀π) = q² x₀² · (ν₀/π)² g₂ · τ_{Ã(π)Φ}(ν₀)` for `π ∤ ν₀`, given cube periodicity
at `π` (`x₀ = q^{-s₀}`, `q⁴x₀³ = 1`; so `q²x₀² = q^{-2/3}`). -/
theorem tau_mul_prime (hper : T.PER π) (hx : nrm π ^ 4 * (nrm π ^ (-s₀)) ^ 3 = 1)
    {ν₀ : R} (hν₀ : ¬ π ∣ ν₀) (Φ : Sec) :
    T.tau Φ (ν₀ * π) =
      nrm π ^ 2 * (nrm π ^ (-s₀)) ^ 2 * (S.sym ν₀ π ^ 2 * g2) * T.tau (D.act π Φ) ν₀ := by
  have hπ := P.ne_zero
  have hν0 : ν₀ ≠ 0 := fun h => hν₀ (h ▸ dvd_zero π)
  obtain ⟨Φ₃, h₃⟩ := D.exists_pre hπ 3 Φ
  set Ψ := D.act π Φ with hΨ
  set Φ₂ := D.act π Φ₃ with hΦ₂
  -- the four sections all have `Ã(π)^k (·) ≈ Ψ`
  have e0 : D.LEq ((D.act π)^[0] Ψ) Ψ 1 := Kubota.LEq.refl D Ψ
  have e1 : D.LEq ((D.act π)^[1] Φ) Ψ 1 := Kubota.LEq.refl D Ψ
  have e3 : D.LEq ((D.act π)^[3] Φ₂) Ψ 1 := by
    have : (D.act π)^[3] Φ₂ = D.act π ((D.act π)^[3] Φ₃) := by
      rw [hΦ₂, ← Function.iterate_succ_apply, Function.iterate_succ_apply']
    rw [this]
    exact h₃.act D hπ
  have e4 : D.LEq ((D.act π)^[4] Φ₃) Ψ 1 := by
    rw [Function.iterate_succ_apply']
    exact h₃.act D hπ
  -- residues
  have c3 : T.tau Φ₂ (ν₀ * π ^ 3) = T.tau Ψ ν₀ := by
    rw [hper Φ₂ ν₀ hν0, T.tau_congr e3 hν0, one_mul]
  have c4 : T.tau Φ₃ (ν₀ * π ^ 4) = T.tau Φ (ν₀ * π) := by
    rw [show ν₀ * π ^ 4 = ν₀ * π * π ^ 3 by ring, hper Φ₃ _ (mul_ne_zero hν0 hπ),
      T.tau_congr h₃ (mul_ne_zero hν0 hπ), one_mul]
  set q := nrm π with hq
  set G := S.sym ν₀ π * g1 with hG
  set G' := S.sym ν₀ π ^ 2 * g2 with hG'
  have hd : ∀ X : ℂ → ℂ, Differentiable ℂ X →
      Differentiable ℂ (fun s => 1 - q ^ 2 * X s ^ 3 + q ^ 3 * X s ^ 3) ∧
      Differentiable ℂ (fun s => q ^ 4 * G' * X s ^ 5) ∧
      Differentiable ℂ (fun s => q * G' * X s ^ 2) := by
    intro X hX
    refine ⟨by fun_prop, by fun_prop, by fun_prop⟩
  obtain ⟨d1, d2, d3⟩ := hd _ (differentiable_x P)
  have hne1 : ν₀ * π ≠ 0 := mul_ne_zero hν0 hπ
  have key := T.lin2 (fun s => 1 - q ^ 2 * (q ^ (-s)) ^ 3 + q ^ 3 * (q ^ (-s)) ^ 3)
    (fun s => q ^ 4 * G' * (q ^ (-s)) ^ 5) (fun _ => 1) (fun s => q * G' * (q ^ (-s)) ^ 2)
    d1 d2 (differentiable_const 1) d3
    (T.tau_spec Φ (ν₀ * π) hne1) (T.tau_spec Ψ ν₀ hν0)
    (T.tau_spec Φ₃ (ν₀ * π ^ 4) (mul_ne_zero hν0 (pow_ne_zero _ hπ)))
    (T.tau_spec Φ₂ (ν₀ * π ^ 3) (mul_ne_zero hν0 (pow_ne_zero _ hπ)))
    (by
      intro s hs
      have a0 := aSer_eq_Cform hfin P hν₀ 0 e0 hs
      have a1 := aSer_eq_Cform hfin P hν₀ 1 e1 hs
      have a3 := aSer_eq_Cform hfin P hν₀ 3 e3 hs
      have a4 := aSer_eq_Cform hfin P hν₀ 4 e4 hs
      rw [pow_zero, mul_one] at a0
      rw [pow_one] at a1
      rw [a0, a1, a3, a4, Cform_zero, Cform_one, Cform_three, Cform_four]
      ring)
  beta_reduce at key
  rw [c3, c4] at key
  have hq1 : q - 1 ≠ 0 := sub_ne_zero.2 (nrm_ne_one P)
  apply mul_left_cancel₀ hq1
  linear_combination q ^ 2 * key -
    ((q - 1) * T.tau Φ (ν₀ * π) + q ^ 2 * G' * (q ^ (-s₀)) ^ 2 * T.tau Ψ ν₀) * hx

include P hfin in
/-- **(E2)**: `τ_Φ(ν₀π²) = 0` for `π ∤ ν₀`, given cube periodicity at `π`. -/
theorem tau_mul_prime_sq (hper : T.PER π) (hx : nrm π ^ 4 * (nrm π ^ (-s₀)) ^ 3 = 1)
    {ν₀ : R} (hν₀ : ¬ π ∣ ν₀) (Φ : Sec) : T.tau Φ (ν₀ * π ^ 2) = 0 := by
  have hπ := P.ne_zero
  have hν0 : ν₀ ≠ 0 := fun h => hν₀ (h ▸ dvd_zero π)
  obtain ⟨Φ₃, h₃⟩ := D.exists_pre hπ 3 Φ
  set Ψ := (D.act π)^[2] Φ with hΨ
  have e2 : D.LEq ((D.act π)^[2] Φ) Ψ 1 := Kubota.LEq.refl D Ψ
  have e5 : D.LEq ((D.act π)^[5] Φ₃) Ψ 1 := by
    rw [show (5 : ℕ) = 2 + 3 by norm_num, Function.iterate_add_apply]
    exact h₃.iterate D hπ 2
  have hne2 : ν₀ * π ^ 2 ≠ 0 := mul_ne_zero hν0 (pow_ne_zero _ hπ)
  have c5 : T.tau Φ₃ (ν₀ * π ^ 5) = T.tau Φ (ν₀ * π ^ 2) := by
    rw [show ν₀ * π ^ 5 = ν₀ * π ^ 2 * π ^ 3 by ring, hper Φ₃ _ hne2, T.tau_congr h₃ hne2,
      one_mul]
  set q := nrm π with hq
  have hd : ∀ X : ℂ → ℂ, Differentiable ℂ X →
      Differentiable ℂ (fun s => 1 + q ^ 3 * X s ^ 3) := by
    intro X hX
    fun_prop
  have key := T.lin1 (fun _ => 1) (fun s => 1 + q ^ 3 * (q ^ (-s)) ^ 3) (differentiable_const 1)
    (hd _ (differentiable_x P))
    (T.tau_spec Φ₃ (ν₀ * π ^ 5) (mul_ne_zero hν0 (pow_ne_zero _ hπ)))
    (T.tau_spec Φ (ν₀ * π ^ 2) hne2)
    (by
      intro s hs
      have a2 := aSer_eq_Cform hfin P hν₀ 2 e2 hs
      have a5 := aSer_eq_Cform hfin P hν₀ 5 e5 hs
      rw [a2, a5, Cform_two, Cform_five]
      ring)
  beta_reduce at key
  rw [c5] at key
  have hq0 : q ≠ 0 := nrm_ne_zero P
  -- `q³ x₀³ c₂ = 0` and `q³ x₀³ = q⁻¹ ≠ 0`
  have h0 : q ^ 3 * (q ^ (-s₀)) ^ 3 * T.tau Φ (ν₀ * π ^ 2) = 0 := by
    linear_combination -key
  have hne : q ^ 3 * (q ^ (-s₀)) ^ 3 ≠ 0 := by
    intro h
    have : q ^ 4 * (q ^ (-s₀)) ^ 3 = 0 := by
      rw [show q ^ 4 * (q ^ (-s₀)) ^ 3 = q * (q ^ 3 * (q ^ (-s₀)) ^ 3) by ring, h, mul_zero]
    rw [hx] at this
    exact one_ne_zero this
  exact (mul_eq_zero.1 h0).resolve_left hne

include P hfin in
/-- **All prime powers**: `τ_Φ(ν₀π^e) = w(e) · (ν₀/π)^{2e} · τ_{Ã(π)^eΦ}(ν₀)` for `π ∤ ν₀`
(MATH2 §4.4, "in one formula"; `(ν₀/π)^{2e} = χ_P(ν₀)^{4e}`). -/
theorem tau_mul_prime_pow (hper : T.PER π) (hx : nrm π ^ 4 * (nrm π ^ (-s₀)) ^ 3 = 1)
    {ν₀ : R} (hν₀ : ¬ π ∣ ν₀) (e : ℕ) (Φ : Sec) :
    T.tau Φ (ν₀ * π ^ e) =
      wloc (nrm π) (nrm π ^ (-s₀)) g2 e * S.sym ν₀ π ^ (2 * e) *
        T.tau ((D.act π)^[e] Φ) ν₀ := by
  have hπ := P.ne_zero
  have hν0 : ν₀ ≠ 0 := fun h => hν₀ (h ▸ dvd_zero π)
  have h3 : S.sym ν₀ π ^ 3 = 1 :=
    S.sym_pow_three ν₀ π hπ ((isCoprime_iff_not_dvd P.isMax ν₀).2 hν₀)
  induction e using Nat.strong_induction_on generalizing Φ with
  | _ e ih =>
    rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ 3 ≤ e) with rfl | rfl | rfl | he
    · simp [wloc]
    · have hw : wloc (nrm π) (nrm π ^ (-s₀)) g2 1 = nrm π ^ 2 * (nrm π ^ (-s₀)) ^ 2 * g2 := by
        simp [wloc]
      rw [pow_one, T.tau_mul_prime hfin P hper hx hν₀ Φ, hw, Function.iterate_one]
      ring
    · rw [T.tau_mul_prime_sq hfin P hper hx hν₀ Φ]
      simp [wloc]
    · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 3 := ⟨e - 3, by omega⟩
      rw [show ν₀ * π ^ (e' + 3) = ν₀ * π ^ e' * π ^ 3 by ring,
        hper Φ _ (mul_ne_zero hν0 (pow_ne_zero _ hπ)), ih e' (by omega),
        ← Function.iterate_add_apply]
      have hw : wloc (nrm π) (nrm π ^ (-s₀)) g2 (e' + 3) =
          wloc (nrm π) (nrm π ^ (-s₀)) g2 e' := by
        unfold wloc
        rw [Nat.add_mod_right]
      rw [hw, pow_eq_pow_of_cube h3 (show (2 * (e' + 3)) % 3 = (2 * e') % 3 by omega)]

end prime

end Theta

end ArtinKP.E
end

section
-- module Solutions.Artin.KP.E_Main
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
/-! # E_Main: Theorem E at the formal level (MATH2 §6.2)

`theoremE`: for `ν = u · ∏_{i ∈ t} π_i^{e_i}` (`u` a unit, the `π_i` pairwise coprime primes with
B7's table, cube periodicity at each `π_i`, `q_i⁴ x₀³ = 1`):

`τ_Φ(ν) = (∏_i w_i(e_i) · (ν π_i^{-e_i} / π_i)^{e_i}) · τ_{Ã(ν)Φ}(1)`,

where `(d/π_i) = χ_{P_i}(d)²`, so the twist is `χ_{P_i}(ν/π_i^{e_i})^{2 e_i}` — the `lsym^{2e}` of the
frozen `Wsph` — and `w_i(e) = q_i^{e/3} Wv P_i e`.  The proof is by induction on `t`; the product on
the right is symmetric, so the order of the primes is immaterial.  The only inputs are the
one-prime formula `Theta.tau_mul_prime_pow`, the units lemma, `Ã(ν₀)Ã(π^e) = ⟨ν₀,π⟩^e Ã(ν₀π^e)` and
reciprocity in the form `⟨ν₀,π⟩ (ν₀/π) = (π/ν₀)` (`Pairing.br_coprime`).

`tau_unit_mul_prime` settles B7's open unit-twist point: for a unit `ε`,
`τ_Φ(επ) = q²x₀²g₂ · (ε/π) · τ_{Ã(επ)Φ}(1)`: the one-prime system produces `(ε/π)² = χ_P(ε)⁴`, and
the pairing `⟨ε,π⟩ = (ε/π)⁻¹` (from commuting `Ã(ε)` past `Ã(π)`) reduces it to `χ_P(ε)²`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ArtinKP.E

open ArtinKP.B7

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]

lemma sym_prod_right (S : CubicSymbol R) {ι : Type*} (t : Finset ι) (d : R) (c : ι → R)
    (hc : ∀ i ∈ t, c i ≠ 0) : S.sym d (∏ i ∈ t, c i) = ∏ i ∈ t, S.sym d (c i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [S.sym_unit_right d 1 isUnit_one]
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      S.sym_mul_right _ _ _ (hc a (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.2 fun i hi => hc i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))]

namespace Theta

variable {S : CubicSymbol R} {A : AddData R K} {Sec : Type*} {D : Kubota S A Sec} {s₀ : ℂ}
  (T : Theta D s₀) (hfin : ∀ c : R, c ≠ 0 → Finite (R ⧸ Ideal.span {c}))

include hfin in
/-- **Theorem E, formal level** (MATH2 §6.2). -/
theorem theoremE {ι : Type*} [DecidableEq ι] (t : Finset ι) (π : ι → R) (g1 g2 : ι → ℂ)
    (e : ι → ℕ) (hP : ∀ i ∈ t, PrimeDatum S A (π i) (g1 i) (g2 i))
    (hper : ∀ i ∈ t, T.PER (π i))
    (hx : ∀ i ∈ t, nrm (π i) ^ 4 * (nrm (π i) ^ (-s₀)) ^ 3 = 1)
    (hcop : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → IsCoprime (π i) (π j))
    {u : R} (hu : IsUnit u) (Φ : Sec) :
    T.tau Φ (u * ∏ i ∈ t, π i ^ e i) =
      (∏ i ∈ t, wloc (nrm (π i)) (nrm (π i) ^ (-s₀)) (g2 i) (e i) *
          S.sym (u * ∏ j ∈ t.erase i, π j ^ e j) (π i) ^ e i) *
        T.tau (D.act (u * ∏ i ∈ t, π i ^ e i) Φ) 1 := by
  induction t using Finset.induction_on generalizing Φ with
  | empty =>
    simp only [Finset.prod_empty, mul_one, one_mul]
    have := T.tau_unit hfin Φ hu (one_ne_zero (α := R))
    rwa [mul_one] at this
  | insert i₀ t hi₀ ih =>
    have hP₀ := hP i₀ (Finset.mem_insert_self _ _)
    have hπ₀ := hP₀.ne_zero
    have hπne : ∀ i ∈ t, π i ≠ 0 := fun i hi => (hP i (Finset.mem_insert_of_mem hi)).ne_zero
    have hpne : ∀ (t' : Finset ι), t' ⊆ t → ∏ i ∈ t', π i ^ e i ≠ 0 := fun t' ht' =>
      Finset.prod_ne_zero_iff.2 fun i hi => pow_ne_zero _ (hπne i (ht' hi))
    have IH := ih (fun i hi => hP i (Finset.mem_insert_of_mem hi))
      (fun i hi => hper i (Finset.mem_insert_of_mem hi))
      (fun i hi => hx i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj => hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
      ((D.act (π i₀))^[e i₀] Φ)
    have hνdef : u * ∏ i ∈ insert i₀ t, π i ^ e i = (u * ∏ i ∈ t, π i ^ e i) * π i₀ ^ e i₀ := by
      rw [Finset.prod_insert hi₀]; ring
    set ν₀ := u * ∏ i ∈ t, π i ^ e i with hν₀def
    have hν₀0 : ν₀ ≠ 0 := mul_ne_zero hu.ne_zero (hpne t (Finset.Subset.refl t))
    have hcopi : ∀ i ∈ t, IsCoprime (π i₀) (π i) := fun i hi =>
      hcop i₀ (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
        (by rintro rfl; exact hi₀ hi)
    have hcop₀ : IsCoprime (π i₀) ν₀ :=
      IsCoprime.mul_right (isCoprime_comm.1 (isCoprime_of_isUnit hu))
        (IsCoprime.prod_right fun i hi => IsCoprime.pow_right (hcopi i hi))
    have hnd : ¬ π i₀ ∣ ν₀ := (isCoprime_iff_not_dvd hP₀.isMax ν₀).1 hcop₀.symm
    have hL : D.LEq (D.act ν₀ ((D.act (π i₀))^[e i₀] Φ)) (D.act (ν₀ * π i₀ ^ e i₀) Φ)
        (D.br ν₀ (π i₀ ^ e i₀)) := by
      have h1 := (D.Lam_iter_eq_pow Φ hπ₀ (e i₀)).act D hν₀0
      have h2 := D.Lam_act_act Φ hν₀0 (pow_ne_zero (e i₀) hπ₀)
      simpa using h1.trans D h2
    -- the symbol `(π₀/ν₀)` as a product over `t`
    have hc : S.sym (π i₀) ν₀ = ∏ i ∈ t, S.sym (π i₀) (π i) ^ e i := by
      rw [hν₀def, S.sym_mul_right _ _ _ hu.ne_zero (hpne t (Finset.Subset.refl t)),
        S.sym_unit_right _ u hu, one_mul,
        sym_prod_right S t _ _ (fun i hi => pow_ne_zero _ (hπne i hi))]
      exact Finset.prod_congr rfl fun i hi => S.sym_pow_right _ (hπne i hi) _
    have hprod : ∏ i ∈ t, (wloc (nrm (π i)) (nrm (π i) ^ (-s₀)) (g2 i) (e i) *
          S.sym (u * ∏ j ∈ (insert i₀ t).erase i, π j ^ e j) (π i) ^ e i) =
        (∏ i ∈ t, wloc (nrm (π i)) (nrm (π i) ^ (-s₀)) (g2 i) (e i) *
          S.sym (u * ∏ j ∈ t.erase i, π j ^ e j) (π i) ^ e i) * S.sym (π i₀) ν₀ ^ e i₀ := by
      rw [hc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i₀ ≠ i := by rintro rfl; exact hi₀ hi
      rw [Finset.erase_insert_of_ne hne,
        Finset.prod_insert (fun h => hi₀ (Finset.mem_of_mem_erase h)),
        show u * (π i₀ ^ e i₀ * ∏ j ∈ t.erase i, π j ^ e j) =
          π i₀ ^ e i₀ * (u * ∏ j ∈ t.erase i, π j ^ e j) by ring,
        S.sym_mul_left _ _ _ (hπne i hi), sym_pow_left S _ (hπne i hi)]
      ring
    have hb : D.br ν₀ (π i₀) * S.sym ν₀ (π i₀) = S.sym (π i₀) ν₀ :=
      D.br_coprime ν₀ (π i₀) hν₀0 hπ₀ hcop₀.symm
    rw [hνdef, T.tau_mul_prime_pow hfin hP₀ (hper i₀ (Finset.mem_insert_self _ _))
      (hx i₀ (Finset.mem_insert_self _ _)) hnd, IH, T.tau_congr hL one_ne_zero,
      Finset.prod_insert hi₀, Finset.erase_insert hi₀, hprod, ← hb,
      D.toPairing.br_pow_right hν₀0 hπ₀]
    ring

end Theta

end ArtinKP.E
end

section
-- module Solutions.Artin.T12.L2A_FSQuot
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# L2A_FSQuot: exterior ideals of `𝓞 F` and of `R`

* `exists_pow_mul_mem`: every `r ∈ R` has `𝔪^N r ⊆ 𝓞`.
* `mem_of_map_mem`: `I R ∩ 𝓞 = I` for `I + 𝔪 = 1`.
* `exists_sub_mem_map`: `𝓞 → R / I R` is onto for `I + 𝔪 = 1`; `finite_quot_map`,
  `natCard_quot_map_le : #(R / I R) ≤ N I`.
-/

open NumberField IsDedekindDomain WithZero

namespace ArtinPrimitiveRoots.L2A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- Every `r ∈ R` has `𝔪^N r ⊆ 𝓞` for some `N`. -/
lemma exists_pow_mul_mem (r : SInt 𝔪) : ∃ N : ℕ, ∀ w ∈ 𝔪 ^ N, ∃ c : 𝓞 F,
    algebraMap (𝓞 F) (SInt 𝔪) w * r = algebraMap (𝓞 F) (SInt 𝔪) c := by
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (r : F)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  set N := Ideal.absNorm (Ideal.span {d}) with hN
  refine ⟨N, fun w hw => ?_⟩
  have hint : ∀ v : HeightOneSpectrum (𝓞 F),
      v.valuation F (algebraMap (𝓞 F) F w * (r : F)) ≤ 1 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · have hvm : 𝔪 ≤ v.asIdeal := hv
      have hdN : d ∉ v.asIdeal ^ N := by
        intro hmem
        have hle : Ideal.span {d} ≤ v.asIdeal ^ N := (Ideal.span_singleton_le_iff_mem _).2 hmem
        have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
        rw [map_pow] at hdvd
        have hN0 : N ≠ 0 := by
          rw [hN, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd0
        have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by
          have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
            rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
          have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
            rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
          omega
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd
        have h3 : 2 ^ N ≤ Ideal.absNorm v.asIdeal ^ N := Nat.pow_le_pow_left h2 N
        have h4 : N < 2 ^ N := Nat.lt_two_pow_self
        omega
      have hvd : exp (-(N : ℤ)) < v.valuation F (algebraMap (𝓞 F) F d) := by
        rw [C3I.val_alg, ← not_le, v.intValuation_le_pow_iff_mem]; exact hdN
      have hvw : v.valuation F (algebraMap (𝓞 F) F w) ≤ exp (-(N : ℤ)) := by
        rw [C3I.val_alg, v.intValuation_le_pow_iff_mem]
        exact Ideal.pow_right_mono hvm N hw
      have hdpos : v.valuation F (algebraMap (𝓞 F) F d) ≠ 0 := ne_zero_of_lt hvd
      have hxd : (r : F) * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F b := by
        rw [← hbd, div_mul_cancel₀]
        exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
      have key : v.valuation F (algebraMap (𝓞 F) F w * (r : F)) *
          v.valuation F (algebraMap (𝓞 F) F d) ≤ 1 * v.valuation F (algebraMap (𝓞 F) F d) := by
        rw [← map_mul, show algebraMap (𝓞 F) F w * (r : F) * algebraMap (𝓞 F) F d =
          algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F w by rw [mul_assoc, hxd]; ring, map_mul]
        exact mul_le_mul' (v.valuation_le_one b) (hvw.trans hvd.le)
      exact C3I.le_of_mul_le_mul_ne key hdpos
    · rw [map_mul]
      exact mul_le_one' (v.valuation_le_one w) (r.2 v hv)
  obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hint
  refine ⟨c, Subtype.ext ?_⟩
  rw [Subalgebra.coe_mul, C3I.coe_alg, C3I.coe_alg, hc]

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

end ArtinPrimitiveRoots.L2A
end

section
-- module Solutions.Artin.T12.L3V_Val
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # L3V_Val: valuations of allowed generators and the unit-part symbol `uSym`

* `val_gen_eq`: `v(gen I) = exp(−v_P(I))` for exterior `I` at a good prime;
* `vP P x = −log v(x)` (the `P`-adic valuation), `uSym g P x = χ_P(x p^{−v_P(x)})`, the symbol of the
  unit part;
* `uSym_mul`, `uSym_inv`, `uSym_pow_six`, `uSym_ne_zero`, `uSym_of_unit`, `uSym_SInt` (for
  `y ∈ R ∖ P R`: `uSym y = χ_P(y)`), `uSym_unit_pow_six` (`= 1` on `U_S^6`), `vP_gen`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

section good

variable (h : C3I.Good 𝔪 v) (g : AllowedGen ι 𝔪)
include h

lemma gen_not_mem_of_ne {Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQe : IsExterior 𝔪 Q)
    (hne : Q ≠ v.asIdeal) :
    g.gen Q ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  intro hmem
  have hspan : Q.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← g.span_gen Q hQe, Ideal.span_le, Set.singleton_subset_iff]; exact hmem
  have hle : Q ≤ v.asIdeal := fun a ha =>
    L2A.mem_of_map_mem v.asIdeal h.cop a (hspan (Ideal.mem_map_of_mem _ ha))
  have hmax : Q.IsMaximal := hQ.isMaximal hQe.1
  exact hne (hmax.eq_of_le v.isPrime.ne_top hle)

end good

end L3V

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.E_Link
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # E_Link: Theorem E over `R = SInt 𝔪` in the shape of the frozen statement

* `primeDatum_gen`: at a good exterior prime `P`, `π = g.gen P` satisfies `PrimeDatum` with
  `g₁ = tau P 2`, `g₂ = tau P 4` (B7's table).
* `wloc_eq`: at `s₀ = 4/3`, `w_P(e) = (N P)^{e/3} · Wv P e` (`Wv` of the frozen statement).
* `theoremE_SInt`: `τ_Φ(ν) = N(𝔷)^{1/3} · ∏_{P ∣ 𝔷} Wsph P (v_P 𝔷) (ν / gen(P)^{v_P 𝔷}) · τ_{Ã(ν)Φ}(1)`
  for `νR = 𝔷R`, `𝔷` exterior.
* `exists_cutoff_theoremE`: the same as one cutoff statement with the `let`s of the frozen goal
  copied verbatim.

Of `AllowedGen` only `span_gen` is used (through B7 and `L3V`): `gen_mul` and `reciprocity` are
not needed.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinKP.E

open ArtinPrimitiveRoots ArtinKP.B7

lemma hx_of_nat (q : ℕ) (hq : 0 < q) :
    (q : ℂ) ^ 4 * ((q : ℂ) ^ (-(4 / 3 : ℂ))) ^ 3 = 1 := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [← Complex.cpow_nat_mul,
    show ((3 : ℕ) : ℂ) * -(4 / 3 : ℂ) = -((4 : ℕ) : ℂ) by push_cast; ring, Complex.cpow_neg,
    Complex.cpow_natCast]
  exact mul_inv_cancel₀ (pow_ne_zero _ hq0)

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The global statement -/

section global

variable {ι : F →+* ℂ} (g : AllowedGen ι 𝔪) (h𝔪 : 𝔪 ≠ ⊥) (S : CubicSymbol (SInt 𝔪))
  {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
  (hgood : ∀ (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hext : IsExterior 𝔪 P),
    C3I.Good 𝔪 (⟨P, hP, hext.1⟩ : HeightOneSpectrum (𝓞 F)))
  (hS : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ∀ d : SInt 𝔪,
    S.sym d (g.gen P) = sexticResidueSymbol ι 𝔪 P d ^ 2)

lemma exterior_of_mem_factors {𝔷 P : Ideal (𝓞 F)} (h𝔷 : IsExterior 𝔪 𝔷)
    (hP : P ∈ normalizedFactors 𝔷) : P.IsPrime ∧ IsExterior 𝔪 P := by
  have hprime := prime_of_normalized_factor P hP
  have hle : 𝔷 ≤ P := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP)
  refine ⟨Ideal.isPrime_of_prime hprime, hprime.ne_zero, eq_top_iff.2 ?_⟩
  rw [← h𝔷.2]
  exact sup_le_sup_right hle 𝔪

/-- `ν = u · ∏_{P ∣ 𝔷} gen(P)^{v_P 𝔷}` with `u` a unit, when `νR = 𝔷R`. Uses only `span_gen`. -/
lemma exists_unit_mul_prod {𝔷 : Ideal (𝓞 F)} (h𝔷 : IsExterior 𝔪 𝔷) {ν : SInt 𝔪}
    (hν : Ideal.span {ν} = 𝔷.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ∃ u : SInt 𝔪, IsUnit u ∧ ν = u * ∏ P ∈ (normalizedFactors 𝔷).toFinset,
      g.gen P ^ (normalizedFactors 𝔷).count P := by
  have hprod : Ideal.span {∏ P ∈ (normalizedFactors 𝔷).toFinset,
      g.gen P ^ (normalizedFactors 𝔷).count P} = 𝔷.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    conv_rhs => rw [← Ideal.prod_normalizedFactors_eq_self h𝔷.1, Finset.prod_multiset_count]
    rw [← Ideal.mapHom_apply, map_prod, ← Ideal.prod_span_singleton]
    refine Finset.prod_congr rfl fun P hP => ?_
    have hPe := (exterior_of_mem_factors h𝔷 (Multiset.mem_toFinset.1 hP)).2
    rw [map_pow, Ideal.mapHom_apply, ← g.span_gen P hPe, Ideal.span_singleton_pow]
  have hassoc := Ideal.span_singleton_eq_span_singleton.1 (hprod.trans hν.symm)
  obtain ⟨u, hu⟩ := hassoc
  exact ⟨u, u.isUnit, by rw [← hu, mul_comm]⟩

include hω hgood hS in
/-- **Theorem E over `SInt 𝔪`** with the frozen local factors (`L3V.Wsph` is verbatim the `Wsph`
of the frozen statement). -/
theorem theoremE_SInt {Sec : Type*} (D : Kubota S (sAdd 𝔪 h𝔪) Sec) (T : Theta D (4 / 3 : ℂ))
    (hper : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → T.PER (g.gen P))
    {𝔷 : Ideal (𝓞 F)} (h𝔷 : IsExterior 𝔪 𝔷) {ν : SInt 𝔪}
    (hν : Ideal.span {ν} = 𝔷.map (algebraMap (𝓞 F) (SInt 𝔪))) (Φ : Sec) :
    T.tau Φ ν =
      (((Ideal.absNorm 𝔷 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        (∏ P ∈ (normalizedFactors 𝔷).toFinset,
          L3V.Wsph g P ((normalizedFactors 𝔷).count P : ℤ)
            ((ν : F) * (g.gen P : F) ^ (-((normalizedFactors 𝔷).count P : ℤ)))) *
        T.tau (D.act ν Φ) 1 := by
  classical
  have hfin : ∀ c : SInt 𝔪, c ≠ 0 → Finite (SInt 𝔪 ⧸ Ideal.span {c}) :=
    fun c hc => finite_quot_span h𝔪 hc
  set t := (normalizedFactors 𝔷).toFinset with ht
  set e : Ideal (𝓞 F) → ℕ := fun P => (normalizedFactors 𝔷).count P with he
  have hmem : ∀ P ∈ t, P.IsPrime ∧ IsExterior 𝔪 P := fun P hP =>
    exterior_of_mem_factors h𝔷 (Multiset.mem_toFinset.1 hP)
  obtain ⟨u, hu, hνu⟩ := exists_unit_mul_prod g h𝔷 hν
  have hPD : ∀ P ∈ t, PrimeDatum S (sAdd 𝔪 h𝔪) (g.gen P) (L3V.tau g P 2) (L3V.tau g P 4) :=
    fun P hP => primeDatum_gen (v := ⟨P, (hmem P hP).1, (hmem P hP).2.1⟩)
      (hgood P (hmem P hP).1 (hmem P hP).2) hω g h𝔪 S (hS P (hmem P hP).1 (hmem P hP).2)
  have hx : ∀ P ∈ t, nrm (g.gen P) ^ 4 * (nrm (g.gen P) ^ (-(4 / 3 : ℂ))) ^ 3 = 1 := by
    intro P hP
    have := (hPD P hP).one_lt
    exact hx_of_nat _ (by omega)
  have hcop : ∀ P ∈ t, ∀ Q ∈ t, P ≠ Q → IsCoprime (g.gen P) (g.gen Q) := by
    intro P hP Q hQ hPQ
    have hgQ := hgood Q (hmem Q hQ).1 (hmem Q hQ).2
    rw [isCoprime_iff_not_dvd (hPD Q hQ).isMax, ← Ideal.mem_span_singleton,
      g.span_gen Q (hmem Q hQ).2]
    exact L3V.gen_not_mem_of_ne hgQ g (hmem P hP).1 (hmem P hP).2 hPQ
  have hE := T.theoremE hfin t (fun P => g.gen P) (fun P => L3V.tau g P 2)
    (fun P => L3V.tau g P 4) e hPD (fun P hP => hper P (hmem P hP).1 (hmem P hP).2) hx hcop hu Φ
  rw [← hνu] at hE
  rw [hE]
  congr 1
  -- the local factors
  have hloc : ∀ P ∈ t,
      Theta.wloc (nrm (g.gen P)) (nrm (g.gen P) ^ (-(4 / 3 : ℂ))) (L3V.tau g P 4) (e P) *
          S.sym (u * ∏ Q ∈ t.erase P, g.gen Q ^ e Q) (g.gen P) ^ e P =
        (((Ideal.absNorm P : ℝ) ^ ((e P : ℝ) / 3) : ℝ) : ℂ) *
          L3V.Wsph g P (e P : ℤ) ((ν : F) * (g.gen P : F) ^ (-(e P : ℤ))) := by
    intro P hP
    refine wloc_mul_sym_eq (v := ⟨P, (hmem P hP).1, (hmem P hP).2.1⟩)
      (hgood P (hmem P hP).1 (hmem P hP).2) hω g h𝔪 S (hS P (hmem P hP).1 (hmem P hP).2) (e P) ?_
    rw [hνu, ← Finset.mul_prod_erase t (fun Q => g.gen Q ^ e Q) hP]
    ring
  rw [Finset.prod_congr rfl hloc, Finset.prod_mul_distrib]
  congr 1
  -- the norm
  have hN : (Ideal.absNorm 𝔷 : ℝ) = ∏ P ∈ t, ((Ideal.absNorm P : ℝ)) ^ e P := by
    have h1 : 𝔷 = ∏ P ∈ t, P ^ e P := by
      conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self h𝔷.1, Finset.prod_multiset_count]
    conv_lhs => rw [h1]
    rw [map_prod]
    push_cast
    exact Finset.prod_congr rfl fun P _ => by rw [map_pow]; push_cast; rfl
  rw [hN, ← Real.finsetProd_rpow _ _ (fun P _ => by positivity), ← Complex.ofReal_prod]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

end global

end ArtinKP.E
end

section
-- module Solutions.Artin.KP.B_Kub
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

theorem kubota_act (β : SInt 𝔪) : (kubota hG hz6).act β Φ = S2.actR hG β Φ := rfl

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.G1_Kir
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-G1, part 7: the Kirillov function — (K1)–(K4), the class decomposition, the bound

Section level (any `S_f`-character `ψ` with bounded dual lattices, `HasDual ψ d₀`):

* `exists_Kt_support` (K3): `Kt Φ β η s = 0` unless `β ∈ 𝔩_D` (support in a fractional ideal,
  i.e. `|β|_v ≤ q_v^{-D}` at every `v ∈ S_f` separately); from `S.kir_eq_zero` and DUAL.
* `exists_Kt_bound` (K2): `|β|^{1/3} |Kt Φ β η (4/3)| ≤ C ∏_{v ∈ S_f} min(1, |β|_v^{1/3})` for all
  `β ∈ F^×`, all classes `η`; from `GL.xi_bound`, the support, and `S2.K_eq`.
* `exists_Kt_deep` (K1): `Kt Φ (βu) η s = Kt Φ β η s` for `u` deep.

`τ` level, for `D = B.kubota hG hz6` (`ψ = B.psiS`), any `T : E.Theta D (4/3)`:

* `tau_smul`, `tau_nT`, `tau_addProj`, `tau_sum`, `tau_smulFun`.
* `Kir T Φ β := τ_{Ã(β)Φ}(1)` (MATH3 §0), `xi T Φ β := |β|^{1/3} Kir T Φ β`; **(K4)**:
  `Kir_torusT` (`𝒦_{Ã(β₀)Φ}(β) = ⟨β,β₀⟩𝒦_Φ(ββ₀)`), `Kir_nT` (`𝒦_{n(t)Φ}(β) = ψ(βt)𝒦_Φ(β)`),
  `Kir_smulFun`, `Kir_addProj` (G2), `Kir_sum`, `xi_torusT`, `xi_nT`; `exists_Kir_deep` (K1);
  `Kir_cusp`/`xi_cusp` (MATH3 (2.2)).
* `tau_classDecomp` — **(CD)**: `τ_Ψ(ν) = Σ_η Lam Ψ η ν (4/3) · vol(𝔩_M)⁻¹ τ_{bigCell_η}(ν)`,
  given the scalar law `T.SmulOn {Re s > 1}` (true for `resFunSlit`: `resFunSlit_smulOn`).
* `exists_Kir_classDecomp`: one finite set of classes and weights `w_η` with
  `𝒦_Φ(β) = Σ_η Kt Φ β η (4/3) · w_η` for all `β ∈ F^×`.
* `exists_xi_le` — **the majorant for `ξ`** (MATH3 §4.3):
  `|ξ_Φ(β)| ≤ C ∏_v min(1, |β|_v^{1/3})` and `ξ_Φ(β) = 0` unless `β ∈ 𝔩_D`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2 ArtinKP.E ArtinKP.B7

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### Section level: support, bound, deep invariance -/

/-! ### `τ` level -/

section tau

variable [IsTotallyComplex F] (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (T : Theta (B.kubota (ι := ι) (P := P) hG hz6) (4 / 3 : ℂ))

/-! ### The Kirillov function -/

theorem Kir_of_ne (Φ : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0) :
    Kir hG hz6 T Φ β = T.tau (Φ.torusT hG β hβ) 1 := by
  rw [Kir, dif_neg hβ]

/-! ### The class decomposition and the majorant -/

end tau

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.H0_Row
/-! # WP-H0, file 3: the coordinate dictionary, part 1 — rows and frequencies

`(z, γ) ↦ γ · rowElt g z` is a bijection `RowClass 𝔪 × U_S⁶ ≃ R ∖ {0}` (`rowEquiv`), so each of the
two `∑'` of the frozen goal is a sum over `ν ∈ R ∖ 0` (`tsum_forward`, `tsum_reflected`, with the
exact summands of the goal). `rowOf ν` is the row class of `ν`: its ideal is the unique exterior
ideal `𝔷` with `𝔷R = νR` (`span_eq_map_rowOf`, `rowOf_ideal_unique`), its multiplicities are the
valuations of `ν` (`count_rowOf`), and it only depends on `ν` modulo `U_S⁶` (`rowOf_gam_mul`). -/

namespace ArtinKP.H0

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

section

variable (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪)
include h𝔪

theorem coe_eq_gamOf_mul (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    ((ν : SInt 𝔪) : F) =
      (((gamOf h𝔪 g ν : SUnit 𝔪) : Fˣ) : F) * (rowElt g (rowOf h𝔪 g ν) : F) := by
  have h := congrArg (fun x : {ν : SInt 𝔪 // ν ≠ 0} => ((x : SInt 𝔪) : F))
    ((rowEquiv h𝔪 g).apply_symm_apply ν)
  exact h.symm

/-! ### Reindexing the two sums of the frozen goal -/

end

end

end ArtinKP.H0
end

section
-- module Solutions.Artin.T12.L3X_Rev
/-! # L3X_Rev: the reflected orbit unfolding

`∫_{X_l} Φ(y) · (reflected expansion)(y) = Σ_z E_z L(ν_z)⁻¹ H_{[ν_z]}(|ν_z|_S / l)`: the sum over
`γ ∈ Γ` is collapsed by the partition of unity `ρ`, then `y ↦ ν/y` maps the sheet `X_l` to
`X_{|ν|/l}`. Absolute convergence comes from the product majorant of the reflected `S`-function
and `Σ N𝔷^{-2} < ∞`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid

set_option linter.unusedSectionVars false

open scoped Classical ENNReal

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

theorem span_rowElt_R (g : AllowedGen ι 𝔪) (z : RowClass 𝔪) :
    Ideal.span {rowElt g z} = z.1.1.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [rowElt, ← g.span_gen _ z.1.2]
  exact Ideal.span_singleton_mul_left_unit (Units.isUnit _) _

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.KP.H_Tau
/-! # WP-HA, file 6: the forward coefficient of `AutInput` from Theorem E

With the interface of WP-E (`D : E.Kubota S (sAdd 𝔪 h𝔪) Sec`, `T : E.Theta D (4/3)`, cube
periodicity at every exterior prime):

* `tau_eq_coefF'`: for every `ν ∈ R ∖ 0` and every section `Φ`,
  `τ_Φ(ν) = N(νR)^{1/3} · coefF' g ⊤ (rowOf ν) · τ_{Ã(ν)Φ}(1)`.
  (`E.theoremE_SInt` at the row representative `ρ = rowElt g (rowOf ν)`, `ν = μ⁶ρ`, and
  `τ_Φ(μ⁶ρ) = τ_{Ã(μ⁶)Φ}(ρ)`, `Ã(ρ)Ã(μ⁶) = ⟨ρ, μ⁶⟩ Ã(ν) = Ã(ν)`.)
* `forward_of_tau`: a Fourier expansion with coefficients `τ_Φ(ν) · Arch(ν)` whose Kirillov
  normalization `N(νR)^{1/3} τ_{Ã(ν)Φ}(1) Arch(ν) = fp(sEmb ν + y)` holds is the forward expansion
  of `AutInput`, term by term. -/

namespace ArtinKP.H

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots ArtinKP.B7 ArtinKP.E

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

theorem coefF'_top (g : AllowedGen ι 𝔪) (z : RowClass 𝔪) :
    L3X.coefF' g ⊤ z =
      ∏ P ∈ (normalizedFactors z.1.1).toFinset,
        L3V.Wsph g P ((normalizedFactors z.1.1).count P : ℤ)
          ((rowElt g z : F) * (g.gen P : F) ^ (-((normalizedFactors z.1.1).count P : ℤ))) := by
  have h1 : residueSymbol ι 𝔪 ⊤ (rowElt g z) = 1 := by
    unfold residueSymbol; rw [C3B.normalizedFactors_top]; simp
  unfold L3X.coefF'
  rw [h1, one_mul]

section tau

variable (g : AllowedGen ι 𝔪) (h𝔪 : 𝔪 ≠ ⊥) (S : CubicSymbol (SInt 𝔪))
  {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
  (hgood : ∀ (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hext : IsExterior 𝔪 P),
    C3I.Good 𝔪 (⟨P, hP, hext.1⟩ : HeightOneSpectrum (𝓞 F)))
  (hS : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ∀ d : SInt 𝔪,
    S.sym d (g.gen P) = sexticResidueSymbol ι 𝔪 P d ^ 2)

include hω hgood hS

/-- **Theorem E at `ν ∈ R ∖ 0`, with the forward coefficient of the cut.** -/
theorem tau_eq_coefF' {Sec : Type*} (D : Kubota S (sAdd 𝔪 h𝔪) Sec) (T : Theta D (4 / 3 : ℂ))
    (hper : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → T.PER (g.gen P))
    (ν : {ν : SInt 𝔪 // ν ≠ 0}) (Φ : Sec) :
    T.tau Φ (ν : SInt 𝔪) =
      (((Ideal.absNorm (H0.rowOf h𝔪 g ν).1.1 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        L3X.coefF' g ⊤ (H0.rowOf h𝔪 g ν) * T.tau (D.act (ν : SInt 𝔪) Φ) 1 := by
  have hfin : ∀ c : SInt 𝔪, c ≠ 0 → Finite (SInt 𝔪 ⧸ Ideal.span {c}) :=
    fun c hc => finite_quot_span h𝔪 hc
  obtain ⟨δ, hδ⟩ := (H0.gamOf h𝔪 g ν).2
  set μ : SInt 𝔪 := ((H0.uInt δ : (SInt 𝔪)ˣ) : SInt 𝔪) with hμ
  have hμu : IsUnit μ := Units.isUnit _
  have hμ0 : μ ≠ 0 := hμu.ne_zero
  have hF : ((ν : SInt 𝔪) : F) = ((μ ^ 6 * rowElt g (H0.rowOf h𝔪 g ν) : SInt 𝔪) : F) := by
    rw [H0.coe_eq_gamOf_mul h𝔪 g ν, ← hδ]
    simp only [hμ, powMonoidHom_apply, Subalgebra.coe_mul, Subalgebra.coe_pow, H0.coe_uInt,
      Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have hν : (ν : SInt 𝔪) = μ ^ 6 * rowElt g (H0.rowOf h𝔪 g ν) := Subtype.ext hF
  have hu : IsUnit (μ ^ 6) := hμu.pow 6
  have hρ0 : rowElt g (H0.rowOf h𝔪 g ν) ≠ 0 := by
    intro h0; exact ν.2 (by rw [hν, h0, mul_zero])
  have hE := theoremE_SInt g h𝔪 S hω hgood hS D T hper (H0.rowOf h𝔪 g ν).1.2
    (L3X.span_rowElt_R g (H0.rowOf h𝔪 g ν)) (D.act (μ ^ 6) Φ)
  have h1 : T.tau Φ (μ ^ 6 * rowElt g (H0.rowOf h𝔪 g ν)) =
      T.tau (D.act (μ ^ 6) Φ) (rowElt g (H0.rowOf h𝔪 g ν)) := T.tau_unit hfin Φ hu hρ0
  have hbr : D.br (rowElt g (H0.rowOf h𝔪 g ν)) (μ ^ 6) = 1 := by
    have hm2 : μ ^ 2 ≠ 0 := pow_ne_zero _ hμ0
    have e6 : μ ^ 6 = μ ^ 2 * (μ ^ 2 * μ ^ 2) := by ring
    rw [e6, D.br_mul_right _ _ _ hρ0 hm2 (mul_ne_zero hm2 hm2), D.br_mul_right _ _ _ hρ0 hm2 hm2,
      ← D.br_pow_three _ _ hρ0 hm2]
    ring
  have h2 : T.tau (D.act (rowElt g (H0.rowOf h𝔪 g ν)) (D.act (μ ^ 6) Φ)) 1 =
      T.tau (D.act (μ ^ 6 * rowElt g (H0.rowOf h𝔪 g ν)) Φ) 1 := by
    rw [T.tau_congr (D.Lam_act_act Φ hρ0 hu.ne_zero) one_ne_zero, hbr, one_mul, mul_comm]
  rw [show T.tau Φ (ν : SInt 𝔪) = T.tau Φ (μ ^ 6 * rowElt g (H0.rowOf h𝔪 g ν)) from
      congrArg _ hν,
    show T.tau (D.act (ν : SInt 𝔪) Φ) 1 =
      T.tau (D.act (μ ^ 6 * rowElt g (H0.rowOf h𝔪 g ν)) Φ) 1 from by rw [← hν],
    h1, hE, h2, coefF'_top]

end tau

end

end ArtinKP.H
end

section
-- module Solutions.Artin.KP.GK_E
/-! # WP-GK, file 1: Theorem E without hypotheses, `hsm`, `hne`, Lemma KW

Setting of the cut: `hG : Good 𝔪`, `hz6`, `g : AllowedGen ι 𝔪`, `hgood` (every exterior prime is
`C3I.Good`), `hd : DD.DiffInS 𝔪`.  The theta functional is WP-T's `T.theta hG hz6`.

* `hsm`: the scalar law `SmulOn {Re s > 1}` of `T.theta` (G1's hypothesis `hsm`).
* `per_all`: cube periodicity at every exterior prime (from `F.per`).
* **`tau_eq_coefF'`** (Theorem E): `τ_Φ(ν) = N(νR)^{1/3} · coefF' g ⊤ (rowOf ν) · τ_{Ã(ν)Φ}(1)`;
  `tau_eq_Kir`: the same with G1's Kirillov function.
* **`hne`**: some Kirillov value is nonzero (G1's hypothesis `hne`).
* `tau_eq_zero_of_theta`: `θ_Φ = 0 ⇒ τ_Φ(ν) = 0` for every `ν ∈ R ∖ 0` (converse of (C10′)).
* `theta_wSec_eq_zero`: `θ_Φ = 0 ⇒ θ_{wΦ} = 0` (Corollary N, `N2.theta_eq_zero_iff`).
* **`KW`**: MATH3's Lemma KW in G1's form `G1.KW hG hz6 (T.theta hG hz6)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.GK

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N
  ArtinKP.B7

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

section E

variable (g : AllowedGen ι 𝔪)
  (hgood : ∀ (Q : Ideal (𝓞 F)) (hQ : Q.IsPrime) (hext : IsExterior 𝔪 Q),
    C3I.Good 𝔪 (⟨Q, hQ, hext.1⟩ : HeightOneSpectrum (𝓞 F)))

include hgood in
/-- **Theorem E, unconditional**: for every genuine section `Φ` and `ν ∈ R ∖ 0`,
`τ_Φ(ν) = N(νR)^{1/3} · coefF' g ⊤ (rowOf ν) · τ_{Ã(ν)Φ}(1)`. -/
theorem tau_eq_coefF' (ν : {ν : SInt 𝔪 // ν ≠ 0}) (Φ : GSection ι P 𝔪) :
    T.tau hG hz6 Φ (ν : SInt 𝔪) =
      (((Ideal.absNorm (H0.rowOf hG.ne_bot g ν).1.1 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g ν) *
        T.tau hG hz6 (Φ.torusT hG ((ν : SInt 𝔪) : F) (T.coe_ne_zero ν.2)) 1 := by
  have h := H.tau_eq_coefF' g hG.ne_bot (S2.cubicSymbol ι P hG hz6) hz6 hgood
    (S2.cubicSymbol_gen ι P hG hz6 g) (B.kubota hG hz6) (T.theta hG hz6)
    (theta_per_gen_of_isExterior hG hz6 g hgood) ν Φ
  have ha : (B.kubota hG hz6).act (ν : SInt 𝔪) Φ
      = Φ.torusT hG ((ν : SInt 𝔪) : F) (T.coe_ne_zero ν.2) := by
    rw [B.kubota_act, S2.actR, dif_neg (T.coe_ne_zero ν.2)]
  rw [ha] at h
  exact h

include hgood in
/-- Theorem E with G1's Kirillov function: `τ_Φ(ν) = N(νR)^{1/3} · coef^S(ν) · 𝒦_Φ(ν)`. -/
theorem tau_eq_rpow_mul_coefF_mul_kir_oai (ν : {ν : SInt 𝔪 // ν ≠ 0}) (Φ : GSection ι P 𝔪) :
    T.tau hG hz6 Φ (ν : SInt 𝔪) =
      (((Ideal.absNorm (H0.rowOf hG.ne_bot g ν).1.1 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g ν) *
        G1.Kir hG hz6 (T.theta hG hz6) Φ ((ν : SInt 𝔪) : F) := by
  rw [G1.Kir_of_ne hG hz6 _ Φ (T.coe_ne_zero ν.2)]
  exact tau_eq_coefF' hG hz6 g hgood ν Φ

end E

/-! ### `θ = 0 ⇒ τ ≡ 0`, and `θ_Φ = 0 ⇒ θ_{wΦ} = 0` -/

/-! ### Lemma KW -/

end

end ArtinKP.GK
end

theorem solution.{u_1} : type_of% @ArtinKP.GK.tau_eq_rpow_mul_coefF_mul_kir_oai.{u_1} := @ArtinKP.GK.tau_eq_rpow_mul_coefF_mul_kir_oai.{u_1}
