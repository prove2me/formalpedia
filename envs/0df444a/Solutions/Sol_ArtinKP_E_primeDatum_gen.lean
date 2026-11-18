-- Prove2me | solution 1 for ArtinKP.E.primeDatum_gen
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:04:31.120651+00:00
-- url     : https://prove2.me/submissions/902bba5f-9275-4590-872d-46288d5c8ce9

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
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

lemma Per.mul {c : R} {f g : R → ℂ} (hf : Per c f) (hg : Per c g) : Per c (fun d => f d * g d) :=
  fun a b hab => by simp only [hf a b hab, hg a b hab]

lemma Per.comp_mul_left {c : R} {f : R → ℂ} (hf : Per c f) (u : R) : Per c (fun d => f (u * d)) :=
  fun a b hab => hf _ _ (by rw [← mul_sub]; exact hab.mul_left u)

lemma rsum_congr {c : R} {f g : R → ℂ} (h : ∀ d, f d = g d) : rsum c f = rsum c g := by
  unfold rsum; exact finsum_congr fun x => h _

lemma rsum_const_mul (c : R) (f : R → ℂ) (z : ℂ) : rsum c (fun d => z * f d) = z * rsum c f := by
  unfold rsum; rw [mul_finsum]

lemma rsum_mul_const (c : R) (f : R → ℂ) (z : ℂ) : rsum c (fun d => f d * z) = rsum c f * z := by
  unfold rsum; rw [finsum_mul]

lemma rsum_sub (c : R) [Finite (R ⧸ Ideal.span {c})] (f g : R → ℂ) :
    rsum c (fun d => f d - g d) = rsum c f - rsum c g := by
  unfold rsum
  exact finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)

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

/-- Only the zero class contributes to a sum supported on multiples of `c`. -/
lemma rsum_ite_dvd (c : R) (f : R → ℂ) [DecidablePred fun d : R => c ∣ d] :
    rsum c (fun d => if c ∣ d then f d else 0) = f (rep c 0) := by
  unfold rsum
  rw [finsum_eq_single _ (0 : R ⧸ Ideal.span {c})]
  · beta_reduce
    rw [if_pos]
    have := mk_rep c 0
    rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
  · intro x hx
    beta_reduce
    rw [if_neg]
    intro hdvd
    apply hx
    rw [← mk_rep c x, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hdvd

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

/-- `g(ν c, c) = ∑_{d mod c} (d/c)⁻¹`. -/
lemma gauss_mul_self (ν : R) {c : R} (hc : c ≠ 0) : gauss S A (ν * c) c = csum S c := by
  unfold gauss csum
  refine rsum_congr fun d => ?_
  rw [show ν * c * d = c * (ν * d) by ring, A.ψ_mul_self hc, mul_one]

lemma gauss_dvd {ν c : R} (hc : c ≠ 0) (h : c ∣ ν) : gauss S A ν c = csum S c := by
  obtain ⟨r, rfl⟩ := h
  rw [mul_comm]; exact gauss_mul_self S A r hc

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

/-! ### Prime powers -/

section prime

variable {π : R} (hπ : π ≠ 0) (hmax : (Ideal.span {π}).IsMaximal)
  (hfin : ∀ k : ℕ, Finite (R ⧸ Ideal.span {π ^ k}))

include hπ in
lemma gaussP_per (j : ℕ) : Per π (fun d => (S.sym d π)⁻¹ ^ j * A.ψ d π) := by
  intro a b hab
  simp only [S.sym_congr a b π hπ hab, A.ψ_per hπ hab]

include hπ in
/-- `g_j(π)` depends only on `j mod 3` for `j ≥ 1`. -/
lemma gaussP_add_three {j : ℕ} (hj : 0 < j) : gaussP S A π (j + 3) = gaussP S A π j := by
  unfold gaussP
  refine rsum_congr fun d => ?_
  by_cases hd : IsCoprime d π
  · rw [pow_add, inv_pow _ 3, S.sym_pow_three d π hπ hd, inv_one, mul_one]
  · rw [(S.sym_eq_zero_iff d π hπ).2 hd, inv_zero, zero_pow (by omega), zero_pow (by omega)]

include hπ in
/-- Orthogonality: `∑_{d mod π} e(d/π) = 0` for a nontrivial character. -/
lemma rsum_ψ_eq_zero {a₀ : R} (ha₀ : A.ψ a₀ π ≠ 1) : rsum π (fun d => A.ψ d π) = 0 := by
  have hper : Per π (fun d => A.ψ d π) := fun a b hab => A.ψ_per hπ hab
  have e1 := rsum_add_right hper a₀
  have e2 : rsum π (fun d => A.ψ (d + a₀) π) = rsum π (fun d => A.ψ d π) * A.ψ a₀ π := by
    rw [← rsum_mul_const]
    exact rsum_congr fun d => A.ψ_add d a₀ π
  rw [e2] at e1
  by_contra hne
  apply ha₀
  exact mul_left_cancel₀ hne (e1.trans (mul_one _).symm)

include hπ hmax hfin in
/-- `g_j(π) = -1` for `3 ∣ j`, `j ≥ 1` (Ramanujan sum at a prime). -/
theorem gaussP_of_three_dvd {a₀ : R} (ha₀ : A.ψ a₀ π ≠ 1) {j : ℕ} (hj : 0 < j) (h3 : 3 ∣ j) :
    gaussP S A π j = -1 := by
  classical
  have := hfin 1
  rw [pow_one] at this
  have e1 : ∀ d : R, (S.sym d π)⁻¹ ^ j * A.ψ d π =
      A.ψ d π - (if π ∣ d then A.ψ d π else 0) := by
    intro d
    by_cases hd : π ∣ d
    · have hnc : ¬ IsCoprime d π := fun h => (isCoprime_iff_not_dvd hmax d).1 h hd
      rw [if_pos hd, (S.sym_eq_zero_iff d π hπ).2 hnc, inv_zero, zero_pow (by omega)]
      ring
    · have hc : IsCoprime d π := (isCoprime_iff_not_dvd hmax d).2 hd
      rw [if_neg hd, inv_pow, pow_eq_one_of_cube (S.sym_pow_three d π hπ hc) h3]
      ring
  unfold gaussP
  rw [rsum_congr e1, rsum_sub, rsum_ψ_eq_zero A hπ ha₀, rsum_ite_dvd]
  have h0 : π ∣ rep π 0 := by
    have := mk_rep π 0
    rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
  obtain ⟨r, hr⟩ := h0
  rw [hr, A.ψ_mul_self hπ]
  ring

include hπ in
/-- **(B7) table, `j ≤ k`**: `g(ν π^k, π^j) = ∑_{d mod π^j} (d/π^j)⁻¹`. -/
theorem gauss_prime_pow_le (ν : R) {j k : ℕ} (hjk : j ≤ k) :
    gauss S A (ν * π ^ k) (π ^ j) = csum S (π ^ j) :=
  gauss_dvd S A (pow_ne_zero _ hπ) (Dvd.dvd.mul_left (pow_dvd_pow π hjk) ν)

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

include hπ hmax hfin in
/-- `φ_R(π^{j+1}) = q^j (q - 1)`, `q = |R/π|`. -/
theorem phi_prime_pow (j : ℕ) :
    phi (π ^ (j + 1)) = (Nat.card (R ⧸ Ideal.span {π}) : ℂ) ^ j *
      ((Nat.card (R ⧸ Ideal.span {π}) : ℂ) - 1) := by
  classical
  have := hfin 1
  rw [pow_one] at this
  have e1 : ∀ d : R, (if IsCoprime d (π ^ (j + 1)) then (1 : ℂ) else 0) =
      1 - (if π ∣ d then 1 else 0) := by
    intro d
    rw [IsCoprime.pow_right_iff (Nat.succ_pos j)]
    by_cases hd : π ∣ d
    · rw [if_pos hd, if_neg (fun h => (isCoprime_iff_not_dvd hmax d).1 h hd)]; ring
    · rw [if_neg hd, if_pos ((isCoprime_iff_not_dvd hmax d).2 hd)]; ring
  have hper : Per π (fun d => (1 : ℂ) - (if π ∣ d then 1 else 0)) := by
    intro a b hab
    have : π ∣ a ↔ π ∣ b := ⟨fun h => by simpa using dvd_sub h hab, fun h => by simpa using dvd_add hab h⟩
    simp only [this]
  unfold phi
  rw [rsum_congr e1, rsum_pow_of_per hπ hfin hper, rsum_sub, rsum_one,
    rsum_ite_dvd π (fun _ => (1 : ℂ))]

lemma phi_one : phi (1 : R) = 1 := by
  classical
  unfold phi rsum
  have : Subsingleton (R ⧸ Ideal.span {(1 : R)}) := by
    rw [Ideal.span_singleton_one]; exact Ideal.Quotient.subsingleton_iff.2 rfl
  rw [finsum_eq_single _ (0 : R ⧸ Ideal.span {(1 : R)}) (fun x hx => (hx (Subsingleton.elim _ _)).elim)]
  beta_reduce
  rw [if_pos isCoprime_one_right]

include hπ hmax hfin in
/-- **(B7) table, `j = k + 1`**: `g(ν₀ π^k, π^{k+1}) = q^k (ν₀/π)^{k+1} g_{k+1}(π)`. -/
theorem gauss_prime_pow_succ {ν₀ : R} (hν₀ : ¬ π ∣ ν₀) (k : ℕ) :
    gauss S A (ν₀ * π ^ k) (π ^ (k + 1)) =
      (Nat.card (R ⧸ Ideal.span {π}) : ℂ) ^ k * S.sym ν₀ π ^ (k + 1) * gaussP S A π (k + 1) := by
  have := hfin 1
  rw [pow_one] at this
  have hcop : IsCoprime ν₀ π := (isCoprime_iff_not_dvd hmax ν₀).2 hν₀
  have h0 := S.sym_ne_zero hπ hcop
  have e1 : ∀ d : R, (S.sym d (π ^ (k + 1)))⁻¹ * A.ψ (ν₀ * π ^ k * d) (π ^ (k + 1)) =
      S.sym ν₀ π ^ (k + 1) * ((S.sym (ν₀ * d) π)⁻¹ ^ (k + 1) * A.ψ (ν₀ * d) π) := by
    intro d
    have h3 : S.sym ν₀ π ^ (k + 1) * (S.sym ν₀ π * S.sym d π)⁻¹ ^ (k + 1) =
        (S.sym d π ^ (k + 1))⁻¹ := by
      rw [← mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ h0, one_mul, inv_pow]
    rw [S.sym_pow_right d hπ, show ν₀ * π ^ k * d = ν₀ * d * π ^ k by ring, pow_succ' π k,
      A.ψ_mul_right_cancel _ _ (pow_ne_zero _ hπ), S.sym_mul_left _ _ _ hπ, ← mul_assoc, h3]
  unfold gauss
  rw [rsum_congr e1, rsum_const_mul,
    rsum_pow_of_per hπ hfin ((gaussP_per S A hπ (k + 1)).comp_mul_left ν₀),
    rsum_mul_coprime_unit (gaussP_per S A hπ (k + 1)) hcop]
  unfold gaussP
  ring

include hπ hmax in
/-- **(B7) table, `j ≥ k + 2`**: `g(ν₀ π^k, π^j) = 0`. -/
theorem gauss_prime_pow_eq_zero {a₀ : R} (ha₀ : A.ψ a₀ π ≠ 1) {ν₀ : R} (hν₀ : ¬ π ∣ ν₀)
    {j k : ℕ} (hjk : k + 2 ≤ j) : gauss S A (ν₀ * π ^ k) (π ^ j) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = k + 2 + m := ⟨j - (k + 2), by omega⟩
  obtain ⟨u, b, hub⟩ := (isCoprime_iff_not_dvd hmax ν₀).2 hν₀
  set a := u * a₀ with ha
  have hψa : A.ψ (ν₀ * a) π ≠ 1 := by
    rwa [A.ψ_per hπ (a := ν₀ * a) (b := a₀) ⟨-b * a₀, by rw [ha]; linear_combination a₀ * hub⟩]
  have hpj : π ^ (k + 2 + m) ≠ 0 := pow_ne_zero _ hπ
  have e1 := rsum_add_right (gauss_per S A (ν₀ * π ^ k) hpj) (π ^ (m + 1) * a)
  have e2 : ∀ d : R, (S.sym (d + π ^ (m + 1) * a) (π ^ (k + 2 + m)))⁻¹ *
      A.ψ (ν₀ * π ^ k * (d + π ^ (m + 1) * a)) (π ^ (k + 2 + m)) =
      (S.sym d (π ^ (k + 2 + m)))⁻¹ * A.ψ (ν₀ * π ^ k * d) (π ^ (k + 2 + m)) * A.ψ (ν₀ * a) π := by
    intro d
    have h1 : S.sym (d + π ^ (m + 1) * a) (π ^ (k + 2 + m)) = S.sym d (π ^ (k + 2 + m)) := by
      rw [S.sym_pow_right _ hπ, S.sym_pow_right _ hπ,
        S.sym_congr (d + π ^ (m + 1) * a) d π hπ ⟨π ^ m * a, by ring⟩]
    have h2 : A.ψ (ν₀ * π ^ k * (π ^ (m + 1) * a)) (π ^ (k + 2 + m)) = A.ψ (ν₀ * a) π := by
      rw [show ν₀ * π ^ k * (π ^ (m + 1) * a) = ν₀ * a * π ^ (k + 1 + m) by ring,
        show π ^ (k + 2 + m) = π * π ^ (k + 1 + m) by ring,
        A.ψ_mul_right_cancel _ _ (pow_ne_zero _ hπ)]
    rw [h1, mul_add, A.ψ_add, h2]
    ring
  rw [rsum_congr e2, rsum_mul_const] at e1
  unfold gauss
  by_contra hne
  apply hψa
  exact mul_left_cancel₀ hne (e1.trans (mul_one _).symm)

end prime

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
-- module Solutions.Artin.T12.C3I_Char
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # C3I_Char: `χ_P` as a multiplicative character and `x ↦ e(x/π)` as a primitive additive
character of the residue field `L = R / P R`

Standing hypotheses `Good 𝔪 v`: `v` coprime to `𝔪`, `12 ∣ N v − 1`, `v ∤ 𝔇`; and a primitive
sixth root of unity `ω ∈ 𝓞`.

* `chi`: `MulChar L ℂ` with `chi (mk x) = sexticResidueSymbol ι 𝔪 v x`; `chi_neg_one`,
  `chi_pow_six`, `chi_pow_ne_one` (`6 ∤ j`), `chi_cube_eq` (`χ³` is the quadratic character).
* `psi`: `AddChar L ℂ` with `psi (mk x) = e(x / gen P)`; `psi_isPrimitive`.
* `cubicResidueChar_eq`: `ρ_P(x) = χ(x)²` through `𝓞/P ≃ L`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

variable {v : HeightOneSpectrum (𝓞 F)}

/-! ### The sixth roots of unity -/

section chi

variable {ι : F →+* ℂ}

lemma chi_apply (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (y) :
    chi ι h hω y = sexFun ι 𝔪 v y := rfl

lemma chi_neg_one (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    chi ι h hω (-1) = 1 := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hne : (-1 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ≠ 0 :=
    neg_ne_zero.2 one_ne_zero
  have heven : Even ((Ideal.absNorm v.asIdeal - 1) / 6) := by
    obtain ⟨k, hk⟩ := h.twelve
    rw [hk, show 12 * k = 6 * (2 * k) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    exact even_two_mul k
  rw [chi_eq_pow h hω hne (i := 0) (by rw [heven.neg_one_pow, pow_zero]), pow_zero]

lemma chi_pow_six_apply (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    chi ι h hω y ^ 6 = 1 := by
  obtain ⟨i, -, hi⟩ := exists_pow_e h hω hy
  rw [chi_eq_pow h hω hy hi, ← pow_mul, mul_comm, pow_mul, (iota_omega_prim hω).pow_eq_one,
    one_pow]

lemma chi_pow_six (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    chi ι h hω ^ 6 = 1 := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  ext u
  rw [MulChar.pow_apply' _ (by norm_num), MulChar.one_apply_coe]
  exact chi_pow_six_apply h hω u.ne_zero

end chi

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

section field

variable (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
variable [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

include h hω

lemma chi_pow_mod (n : ℕ) : chi ι h hω ^ n = chi ι h hω ^ (n % 6) := by
  conv_lhs => rw [← Nat.div_add_mod n 6, pow_add, pow_mul, chi_pow_six h hω, one_pow, one_mul]

lemma chi_pow_neg_one (j : ℕ) : (chi ι h hω ^ j) (-1) = 1 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero]
    exact MulChar.one_apply (isUnit_one.neg (α := SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))))
  rw [MulChar.pow_apply' _ hj.ne', chi_neg_one h hω, one_pow]

variable (g : AllowedGen ι 𝔪)

/-- `g(φ, ψ⁻¹) = g(φ, ψ)` for the powers of `χ` (as `χ(-1) = 1`). -/
lemma gs_inv_psi (j : ℕ) :
    gaussSum (chi ι h hω ^ j) (psi g h)⁻¹ = gaussSum (chi ι h hω ^ j) (psi g h) := by
  have h1 := chi_pow_neg_one (ι := ι) h hω j
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have := mul_gaussSum_inv_eq_gaussSum (chi ι h hω ^ j) (psi g h)
  rw [h1, one_mul] at this
  exact this

end field

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
-- module Solutions.Artin.T12.L3V_Loc
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # L3V_Loc: characters, Gauss sums and masks on `k_P = R / P R`

At a good prime `v` (with `χ = C3I.chi`, `ψ = C3I.psi`):
* `chi_ql`, `add_ql`: the cut's `χ_P(quotLift y)` and `e(−quotLift y / p)` are `χ y`, `ψ(−y)`;
* `conj_chi_pow`: `conj(χ y)^j = (χ^{5j}) y`; `tau_eq`: `τ_j = g(χ^{5j}, ψ)`;
* `norm_gs`, `norm_gs_le`: `‖g(χ^m, ψ)‖ = √q` (`6 ∤ m`), `≤ √q` (all `m`); `norm_tau`;
* the masks: `mask_zero_of_ne`, `norm_mask_zero_le`, `norm_mask_le`, `mask_mul`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

section loc

variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (g : AllowedGen ι 𝔪)
include h hω

lemma chi_ql (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sexticResidueSymbol ι 𝔪 v.asIdeal (quotLift y) = C3I.chi ι h hω y := by
  rw [← C3I.chi_mk h hω, C3I.mk_quotLift]

omit hω in
lemma add_ql (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sAddChar 𝔪 (-((quotLift y : F) / (g.gen v.asIdeal : F))) = C3I.psi g h (-y) := by
  have := C3I.psi_mk g h (-(quotLift y))
  rw [map_neg, C3I.mk_quotLift] at this
  rw [this, Subalgebra.coe_neg, neg_div]

lemma chi_zero : C3I.chi ι h hω (0 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) = 0 := by
  rw [C3I.chi_apply]; exact C3I.sexFun_zero

lemma norm_chi_eq_one {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    ‖C3I.chi ι h hω y‖ = 1 := by
  have h6 := C3I.chi_pow_six_apply (ι := ι) h hω hy
  have := norm_pow (C3I.chi ι h hω y) 6
  rw [h6, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this.symm

lemma conj_chi {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    starRingEnd ℂ (C3I.chi ι h hω y) = C3I.chi ι h hω y ^ 5 := by
  have h6 := C3I.chi_pow_six_apply (ι := ι) h hω hy
  have hn := norm_chi_eq_one (ι := ι) h hω hy
  have h0 : C3I.chi ι h hω y ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hn; exact zero_ne_one hn
  have hc : starRingEnd ℂ (C3I.chi ι h hω y) * C3I.chi ι h hω y = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  apply mul_right_cancel₀ h0
  rw [hc, ← pow_succ, h6]

lemma conj_chi_pow {j : ℕ} (hj : j ≠ 0) (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    starRingEnd ℂ (C3I.chi ι h hω y) ^ j = (C3I.chi ι h hω ^ (5 * j)) y := by
  rw [MulChar.pow_apply' _ (by omega)]
  by_cases hy : y = 0
  · rw [hy, chi_zero h hω, map_zero, zero_pow hj, zero_pow (by omega)]
  · rw [conj_chi (ι := ι) h hω hy, ← pow_mul]

variable [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

lemma tau_eq {j : ℕ} (hj : j ≠ 0) :
    tau g v.asIdeal j = gaussSum (C3I.chi ι h hω ^ (5 * j)) (C3I.psi g h) := by
  rw [← C3I.gs_inv_psi h hω g (5 * j)]
  unfold tau
  rw [finsum_eq_sum_of_fintype, gaussSum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [chi_ql h hω, add_ql h g, conj_chi_pow h hω hj, AddChar.inv_apply]

/-! ### Masks -/

end loc

end L3V

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.B7_Link
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
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

lemma rsum_eq_finsum {R : Type*} [CommRing R] {c : R} {I : Ideal R} (hI : Ideal.span {c} = I)
    (f : R → ℂ) :
    rsum c f = ∑ᶠ y : R ⧸ I, f (Function.surjInv Ideal.Quotient.mk_surjective y) := by
  subst hI; rfl

lemma pow_mod_three {z : ℂ} (h3 : z ^ 3 = 1) (j : ℕ) : z ^ j = z ^ (j % 3) := by
  conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, h3, one_pow, one_mul]

/-- `g_j(π)` depends only on `j mod 3` (`j ≥ 1`). -/
lemma gaussP_mod {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    (S : CubicSymbol R) (A : AddData R K) {π : R} (hπ : π ≠ 0) {j : ℕ} (hj : 0 < j) :
    gaussP S A π j = gaussP S A π ((j - 1) % 3 + 1) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases h4 : j ≤ 3
    · interval_cases j <;> rfl
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 3 := ⟨j - 3, by omega⟩
      rw [gaussP_add_three S A hπ (by omega), ih m (by omega) (by omega)]
      congr 1; omega

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

section fin

variable [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

include h hω hS in
/-- `g_j(π) = g(χ_P^{4j}, ψ_P)` in the notation of `C3I`. -/
lemma gaussP_eq_gs {j : ℕ} (hj : 0 < j) :
    gaussP S (sAdd 𝔪 h𝔪) (g.gen v.asIdeal) j =
      gaussSum (C3I.chi ι h hω ^ (4 * j)) (C3I.psi g h) := by
  unfold gaussP
  rw [rsum_eq_finsum (span_gen h g), finsum_eq_sum_of_fintype, gaussSum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have e1 : S.sym (Function.surjInv Ideal.Quotient.mk_surjective y) (g.gen v.asIdeal) =
      C3I.chi ι h hω y ^ 2 := by
    rw [hS]; exact congrArg (· ^ 2) (C3I.chi_mk_quotLift h hω y)
  rw [e1, MulChar.pow_apply' _ (by omega), C3I.psi_apply]
  congr 1
  by_cases hy : y = 0
  · rw [hy, C3I.chi_apply, C3I.sexFun_zero, zero_pow (by norm_num), inv_zero, zero_pow (by omega),
      zero_pow (by omega)]
  · have h6 := C3I.chi_pow_six_apply (ι := ι) h hω hy
    have : (C3I.chi ι h hω y ^ 2)⁻¹ = C3I.chi ι h hω y ^ 4 :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact h6)
    rw [this, ← pow_mul]

include h hω hS in
theorem gaussP_two_eq_tau :
    gaussP S (sAdd 𝔪 h𝔪) (g.gen v.asIdeal) 2 = L3V.tau g v.asIdeal 4 := by
  rw [gaussP_eq_gs h hω g h𝔪 S hS (by norm_num), L3V.tau_eq h hω g (by norm_num),
    C3I.chi_pow_mod h hω, C3I.chi_pow_mod h hω (5 * 4)]

include h hω hS in
theorem gaussP_one_eq_tau :
    gaussP S (sAdd 𝔪 h𝔪) (g.gen v.asIdeal) 1 = L3V.tau g v.asIdeal 2 := by
  rw [gaussP_eq_gs h hω g h𝔪 S hS (by norm_num), L3V.tau_eq h hω g (by norm_num),
    C3I.chi_pow_mod h hω (5 * 2)]

end fin

include h hω hS in
/-- The prime Gauss sums `g_j(π)`, `π = g.gen P`, in the notation of the frozen statement:
`tau P 2` for `j ≡ 1`, `tau P 4` for `j ≡ 2`, `-1` for `j ≡ 0 (mod 3)`. -/
theorem gaussP_gen {j : ℕ} (hj : 0 < j) :
    gaussP S (sAdd 𝔪 h𝔪) (g.gen v.asIdeal) j =
      if j % 3 = 1 then L3V.tau g v.asIdeal 2
      else if j % 3 = 2 then L3V.tau g v.asIdeal 4 else -1 := by
  have := C3I.finite_L h
  let _ : Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) := Fintype.ofFinite _
  obtain ⟨a₀, ha₀⟩ := exists_ψ_ne_one h g h𝔪
  rw [gaussP_mod S _ (gen_ne_zero h g) hj]
  rcases (by omega : j % 3 = 1 ∨ j % 3 = 2 ∨ j % 3 = 0) with h1 | h1 | h1
  · rw [if_pos h1, show (j - 1) % 3 + 1 = 1 by omega, gaussP_one_eq_tau h hω g h𝔪 S hS]
  · rw [if_neg (by omega), if_pos h1, show (j - 1) % 3 + 1 = 2 by omega,
      gaussP_two_eq_tau h hω g h𝔪 S hS]
  · rw [if_neg (by omega), if_neg (by omega), show (j - 1) % 3 + 1 = 3 by omega]
    exact gaussP_of_three_dvd S _ (gen_ne_zero h g) (isMaximal_span_gen h g)
      (finite_quot_gen_pow h g h𝔪) ha₀ (by norm_num) (dvd_refl 3)

include h hω hS in
/-- **The prime-power table over `R`** (MATH (B7)), in the form of `B7_System.tab`:
`g(ν₀ π^k, π^j) = tab q G G' k j` with `q = N P`, `G = (ν₀/π)·tau P 2`, `G' = (ν₀/π)²·tau P 4`. -/
theorem gauss_gen_table {ν₀ : SInt 𝔪} (hν₀ : ¬ g.gen v.asIdeal ∣ ν₀) (k j : ℕ) :
    gauss S (sAdd 𝔪 h𝔪) (ν₀ * g.gen v.asIdeal ^ k) (g.gen v.asIdeal ^ j) =
      tab (Ideal.absNorm v.asIdeal : ℂ) (S.sym ν₀ (g.gen v.asIdeal) * L3V.tau g v.asIdeal 2)
        (S.sym ν₀ (g.gen v.asIdeal) ^ 2 * L3V.tau g v.asIdeal 4) k j := by
  have hπ := gen_ne_zero h g
  have hmax := isMaximal_span_gen h g
  have hfin := finite_quot_gen_pow h g h𝔪
  obtain ⟨a₀, ha₀⟩ := exists_ψ_ne_one h g h𝔪
  obtain ⟨d₀, hd₀, hd₁⟩ := exists_sym_gen_ne_one h hω g S hS
  have hcard : (Nat.card (SInt 𝔪 ⧸ Ideal.span {g.gen v.asIdeal}) : ℂ) =
      (Ideal.absNorm v.asIdeal : ℂ) := by rw [card_quot_gen h g]
  have hcop : IsCoprime ν₀ (g.gen v.asIdeal) := (isCoprime_iff_not_dvd hmax ν₀).2 hν₀
  have h3 := S.sym_pow_three ν₀ _ hπ hcop
  unfold tab
  by_cases h1 : j ≤ k
  · rw [if_pos h1, gauss_prime_pow_le S _ hπ ν₀ h1, csum_prime_pow S hπ hd₀ hd₁]
    by_cases h3j : 3 ∣ j
    · rw [if_pos h3j, if_pos h3j]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [if_pos rfl, pow_zero, phi_one]
      · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
        rw [if_neg (by omega), phi_prime_pow hπ hmax hfin, hcard, Nat.add_sub_cancel]
        ring
    · rw [if_neg h3j, if_neg h3j]
  · rw [if_neg h1]
    by_cases h2 : j = k + 1
    · subst h2
      rw [if_pos rfl, gauss_prime_pow_succ S _ hπ hmax hfin hν₀, hcard,
        gaussP_gen h hω g h𝔪 S hS (Nat.succ_pos k), pow_mod_three h3 (k + 1)]
      rcases (by omega : (k + 1) % 3 = 1 ∨ (k + 1) % 3 = 2 ∨ (k + 1) % 3 = 0) with h5 | h5 | h5
      · rw [h5, if_pos rfl, if_pos rfl]; ring
      · rw [h5, if_neg (by norm_num), if_pos rfl, if_neg (by norm_num), if_pos rfl]; ring
      · rw [h5, if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
          if_neg (by norm_num)]; ring
    · rw [if_neg h2]
      exact gauss_prime_pow_eq_zero S _ hπ hmax ha₀ hν₀ (by omega)

end prime

end ArtinKP.B7
end

section
-- module Solutions.Artin.KP.E_Series
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The norm `N(c) = #(R/cR)` -/

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

/-! ### Symbols -/

/-! ### Gauss sums: units and the splitting `c = π^j c'` -/

/-! ### The interface -/

/-! ### The prime datum and the splitting (4.1′) -/

end ArtinKP.E
end

section
-- module Solutions.Artin.KP.E_Link
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-- Finite multiplicity from finiteness of the quotients. -/
lemma mult_of_finite {R : Type*} [CommRing R] [IsDomain R]
    (hfin : ∀ c : R, c ≠ 0 → Finite (R ⧸ Ideal.span {c})) {π : R} (hπ : π ≠ 0)
    (h1 : 1 < Nat.card (R ⧸ Ideal.span {π})) (c : R) (hc : c ≠ 0) :
    ∃ n : ℕ, ¬ π ^ (n + 1) ∣ c := by
  by_contra hcon
  push Not at hcon
  set N := Nat.card (R ⧸ Ideal.span {c}) with hN
  have hdvd := hcon N
  haveI := hfin c hc
  have hle : Ideal.span {c} ≤ Ideal.span {π ^ (N + 1)} := by
    rw [Ideal.span_singleton_le_span_singleton]; exact hdvd
  have hcard := Nat.card_le_card_of_surjective _ (Ideal.Quotient.factor_surjective hle)
  have hpow : Nat.card (R ⧸ Ideal.span {π ^ (N + 1)}) =
      Nat.card (R ⧸ Ideal.span {π}) ^ (N + 1) := by
    have := nrm_pow hfin hπ (N + 1)
    unfold nrm at this
    exact_mod_cast this
  rw [hpow] at hcard
  have h2 : N < 2 ^ (N + 1) :=
    lt_trans Nat.lt_two_pow_self (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have h3 : 2 ^ (N + 1) ≤ Nat.card (R ⧸ Ideal.span {π}) ^ (N + 1) := Nat.pow_le_pow_left h1 _
  omega

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section prime

variable {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}
variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (g : AllowedGen ι 𝔪)
  (h𝔪 : 𝔪 ≠ ⊥) (S : CubicSymbol (SInt 𝔪))
  (hS : ∀ d : SInt 𝔪, S.sym d (g.gen v.asIdeal) = sexticResidueSymbol ι 𝔪 v.asIdeal d ^ 2)

include h in
lemma nrm_gen : nrm (g.gen v.asIdeal) = (Ideal.absNorm v.asIdeal : ℂ) := by
  unfold nrm; rw [card_quot_gen h g]

include h in
lemma one_lt_card_gen : 1 < Nat.card (SInt 𝔪 ⧸ Ideal.span {g.gen v.asIdeal}) := by
  rw [card_quot_gen h g]
  have h1 := C3I.absNorm_pos v
  have h2 := C3I.absNorm_ne_one v
  omega

include h hω hS in
/-- B7's table as a `PrimeDatum` at `π = g.gen P`. -/
theorem primeDatum_gen_oai :
    PrimeDatum S (sAdd 𝔪 h𝔪) (g.gen v.asIdeal) (L3V.tau g v.asIdeal 2) (L3V.tau g v.asIdeal 4) where
  ne_zero := gen_ne_zero h g
  isMax := isMaximal_span_gen h g
  mult := mult_of_finite (fun c hc => finite_quot_span h𝔪 hc) (gen_ne_zero h g)
    (one_lt_card_gen h g)
  one_lt := one_lt_card_gen h g
  table := fun ν₀ hν₀ k j => by
    rw [nrm_gen h g]; exact gauss_gen_table h hω g h𝔪 S hS hν₀ k j

end prime

/-! ### The global statement -/

end ArtinKP.E
end

theorem solution.{u_1} : type_of% @ArtinKP.E.primeDatum_gen_oai.{u_1} := @ArtinKP.E.primeDatum_gen_oai.{u_1}
