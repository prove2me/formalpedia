-- Prove2me | solution 1 for ArtinKP.FA.prop54
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:05:21.749537+00:00
-- url     : https://prove2.me/submissions/df748272-5714-44d0-b9ab-d531be5f45eb

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

lemma rsum_const_mul (c : R) (f : R → ℂ) (z : ℂ) : rsum c (fun d => z * f d) = z * rsum c f := by
  unfold rsum; rw [mul_finsum]

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

/-! ### Elementary facts about the symbol -/

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

/-! ### The Gauss sum -/

/-! ### Constant-term sums -/

/-! ### Prime powers -/

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

section orbit

variable {G α β : Type*} [Group G] [MulAction G α] [MulAction G β]

lemma out_mk_smul (a : α) :
    ∃ ε : G, (Quotient.mk (MulAction.orbitRel G α) a).out = ε • a := by
  have h : (Quotient.mk (MulAction.orbitRel G α) a).out ∈ MulAction.orbit G a :=
    Quotient.mk_out (s := MulAction.orbitRel G α) a
  obtain ⟨ε, hε⟩ := h
  exact ⟨ε, hε.symm⟩

lemma mk_smul_eq (ε : G) (a : α) :
    Quotient.mk (MulAction.orbitRel G α) (ε • a) = Quotient.mk (MulAction.orbitRel G α) a :=
  Quotient.sound (MulAction.mem_orbit a ε)

/-- An equivariant partial bijection `Rel` between `α` and `β` induces a bijection between the
orbits meeting its domain and the orbits meeting its range. -/
theorem exists_orbit_equiv (Rel : α → β → Prop)
    (hsm : ∀ (ε : G) (a : α) (b : β), Rel a b → Rel (ε • a) (ε • b))
    (hfun : ∀ a b b', Rel a b → Rel a b' → b = b')
    (hinj : ∀ a a' b, Rel a b → Rel a' b → a = a') :
    ∃ e : {x : OQ G α // ∃ b, Rel x.out b} ≃ {y : OQ G β // ∃ a, Rel a y.out},
      ∀ x, ∃ ε : G, Rel (ε • x.1.out) (e x).1.out := by
  have fwd : ∀ x : {x : OQ G α // ∃ b, Rel x.out b},
      ∃ ε : G, Rel (ε • x.1.out) (Quotient.mk (MulAction.orbitRel G β) x.2.choose).out := by
    intro x
    obtain ⟨ε, hε⟩ := out_mk_smul (G := G) x.2.choose
    exact ⟨ε, by rw [hε]; exact hsm ε _ _ x.2.choose_spec⟩
  let f : {x : OQ G α // ∃ b, Rel x.out b} → {y : OQ G β // ∃ a, Rel a y.out} :=
    fun x => ⟨Quotient.mk _ x.2.choose, (fwd x).imp' (fun ε => ε • x.1.out) fun _ h => h⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x x' h
      have h' : Quotient.mk (MulAction.orbitRel G β) x.2.choose
          = Quotient.mk (MulAction.orbitRel G β) x'.2.choose := congrArg Subtype.val h
      have h'' : x.2.choose ∈ MulAction.orbit G x'.2.choose := Quotient.exact h'
      obtain ⟨ε, hε⟩ := h''
      have hε' : ε • x'.2.choose = x.2.choose := hε
      have h1 := hsm ε _ _ x'.2.choose_spec
      rw [hε'] at h1
      have h2 := hinj _ _ _ h1 x.2.choose_spec
      apply Subtype.ext
      calc x.1 = Quotient.mk _ x.1.out := (Quotient.out_eq _).symm
        _ = Quotient.mk _ x'.1.out := by rw [← h2]; exact mk_smul_eq ε _
        _ = x'.1 := Quotient.out_eq _
    · intro y
      obtain ⟨a, ha⟩ := y.2
      obtain ⟨ε, hε⟩ := out_mk_smul (G := G) a
      have hx : ∃ b, Rel (Quotient.mk (MulAction.orbitRel G α) a).out b :=
        ⟨ε • y.1.out, by rw [hε]; exact hsm ε _ _ ha⟩
      refine ⟨⟨Quotient.mk _ a, hx⟩, ?_⟩
      apply Subtype.ext
      have h1 := hx.choose_spec
      have h2 := hfun _ _ _ h1 (by rw [hε]; exact hsm ε _ _ ha)
      calc (f ⟨Quotient.mk _ a, hx⟩).1 = Quotient.mk _ hx.choose := rfl
        _ = Quotient.mk _ y.1.out := by rw [h2]; exact mk_smul_eq ε _
        _ = y.1 := Quotient.out_eq _
  exact ⟨Equiv.ofBijective f hf, fun x => fwd x⟩

open Classical in
/-- **Reindexing of orbit sums** along an equivariant partial bijection. -/
theorem tsum_orbit_rel (g : α → ℂ) (h : β → ℂ) (Rel : α → β → Prop)
    (hg : ∀ (ε : G) (a : α), g (ε • a) = g a)
    (hsm : ∀ (ε : G) (a : α) (b : β), Rel a b → Rel (ε • a) (ε • b))
    (hfun : ∀ a b b', Rel a b → Rel a b' → b = b')
    (hinj : ∀ a a' b, Rel a b → Rel a' b → a = a')
    (hval : ∀ a b, Rel a b → g a = h b) :
    (Summable (fun x : OQ G α => if ∃ b, Rel x.out b then g x.out else 0) →
      Summable (fun y : OQ G β => if ∃ a, Rel a y.out then h y.out else 0)) ∧
    (∑' x : OQ G α, (if ∃ b, Rel x.out b then g x.out else 0)) =
      ∑' y : OQ G β, (if ∃ a, Rel a y.out then h y.out else 0) := by
  obtain ⟨e, he⟩ := exists_orbit_equiv Rel hsm hfun hinj
  have key : ∀ x, h (e x).1.out = g x.1.out := fun x => by
    obtain ⟨ε, hε⟩ := he x
    rw [← hg ε, hval _ _ hε]
  have e1 : (fun x : OQ G α => if ∃ b, Rel x.out b then g x.out else 0)
      = Set.indicator {x : OQ G α | ∃ b, Rel x.out b} (fun x => g x.out) := by
    funext x
    rw [Set.indicator_apply]
    rfl
  have e2 : (fun y : OQ G β => if ∃ a, Rel a y.out then h y.out else 0)
      = Set.indicator {y : OQ G β | ∃ a, Rel a y.out} (fun y => h y.out) := by
    funext y
    rw [Set.indicator_apply]
    rfl
  rw [e1, e2]
  constructor
  · intro hs
    rw [← summable_subtype_iff_indicator] at hs ⊢
    have hs' : Summable ((fun y : {y : OQ G β // ∃ a, Rel a y.out} => h y.1.out) ∘ e) :=
      hs.congr fun x => (key x).symm
    exact (e.summable_iff).1 hs'
  · rw [← tsum_subtype, ← tsum_subtype]
    exact (tsum_congr fun x => (key x).symm).trans
      (e.tsum_eq (fun y : {y : OQ G β // ∃ a, Rel a y.out} => h y.1.out))

end orbit

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

lemma rsum_affine {c : R} {g : R → ℂ} (hg : Per c g) {u : R} (hu : IsCoprime u c) (a : R) :
    rsum c (fun t => g (a - u * t)) = rsum c g := by
  have h1 : Per c (fun d => g (d + a)) := fun x y hxy => hg _ _ (by simpa using hxy)
  have h2 := rsum_mul_coprime_unit (f := fun d => g (d + a)) h1 (u := -u) hu.neg_left
  rw [← rsum_add_right hg a, ← h2]
  exact rsum_congr fun d => by congr 1; ring

/-- Sum over representatives after an affine substitution `t ↦ a - u t`, `u` prime to `c`. -/
theorem sum_reps_affine {c : R} {T : Finset R} (hT : IsReps c T) {g : R → ℂ} (hg : Per c g)
    {u : R} (hu : IsCoprime u c) (a : R) : ∑ t ∈ T, g (a - u * t) = rsum c g := by
  have hper : Per c (fun t => g (a - u * t)) := fun x y hxy => hg _ _ (by
    have e : a - u * x - (a - u * y) = -u * (x - y) := by ring
    rw [e]; exact hxy.mul_left _)
  rw [sum_reps hT hper, rsum_affine hg hu]

/-- A residue sum that is multiplied by `z ≠ 1` under `x ↦ u x` vanishes. -/
lemma rsum_eq_zero_of_mul {c : R} {g : R → ℂ} (hg : Per c g) {u : R} (hu : IsCoprime u c)
    {z : ℂ} (hz : z ≠ 1) (h : ∀ x, g (u * x) = z * g x) : rsum c g = 0 := by
  have h1 := rsum_mul_coprime_unit hg hu
  rw [rsum_congr h, rsum_const_mul] at h1
  have h2 : (z - 1) * rsum c g = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (sub_eq_zero.1 h3) hz
  · exact h3

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

omit [IsDomain R] in
lemma per_dvd (π : R) (z w : ℂ) [DecidablePred fun d : R => π ∣ d] :
    Per π (fun d => if π ∣ d then z else w) := by
  intro a b hab
  have : π ∣ a ↔ π ∣ b :=
    ⟨fun h => by simpa using dvd_sub h hab, fun h => by simpa using dvd_add hab h⟩
  simp only [this]

include hπ hfin in
open Classical in
/-- The number of residues modulo `π^(k+1)` not divisible by `π` is `q^(k+1) - q^k`. -/
lemma rsum_not_dvd (k : ℕ) :
    rsum (π ^ (k + 1)) (fun d => if π ∣ d then (0 : ℂ) else 1)
      = (Nat.card (R ⧸ Ideal.span {π}) : ℂ) ^ (k + 1) - (Nat.card (R ⧸ Ideal.span {π}) : ℂ) ^ k := by
  have h1 := hfin 1
  rw [pow_one] at h1
  have e : ∀ d : R, (if π ∣ d then (0 : ℂ) else 1) = 1 - (if π ∣ d then 1 else 0) := by
    intro d; split_ifs <;> ring
  have hper : Per π (fun d => (1 : ℂ) - (if π ∣ d then 1 else 0)) := by
    intro a b hab
    have := per_dvd π (1 : ℂ) 0 a b hab
    simp only [this]
  rw [rsum_congr e, rsum_pow_of_per hπ hfin hper, rsum_sub, rsum_one,
    rsum_ite_dvd π (fun _ => (1 : ℂ)), pow_succ]
  ring

end reps

/-! ### The additive character sum of §5.1 -/

end ArtinKP.FA
end

section
-- module Solutions.Artin.KP.S_Twisted
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.Row.inf_c _root_.ArtinKP.RO.rowClassEquiv_mk _root_.ArtinKP.RO.rowPair_c _root_.ArtinKP.RO.rowPair_d _root_.ArtinKP.S.GSection.twist_apply
/-!
# WP-S, part 3: twisted sections on primitive rows

A *twisted section* (`TSection`) is MATH2's `Ψ_s = κ·Φ_s` restricted to primitive pairs of `R`:
a family `Ψ : ℂ → Row 𝔪 → ℂ`, entire in `s`, with

* `hom`: `Ψ_s(εp) = |ε|_{S_f}^{-s} Ψ_s(p)` for `ε ∈ U_S` (**no symbol**: the factor `⟨c, ε⟩` of the
  genuine section is cancelled by `κ(εp) = ⟨c, ε⟩⁻¹ κ(p)`, `kappaRow_smul`);
* `bound`: `|Ψ_s(p)| ≤ B ‖p‖^{-Re s}`, `B` uniform for `|s| ≤ M`;
* `level`: `Ψ_s(pγ) = κ(γ) Ψ_s(p)` for `γ ∈ Γ(𝔫)`, some `𝔫 ≠ 0`.

`SL₂(R)` acts by plain right translation (`TSection.translate`), with no cocycle; the
Eisenstein series `E_Ψ(P, s) = Σ_{p ∈ Row/U_S} Ψ_s(p) I_p(P)^s` then satisfies
`E_Ψ(γP) = E_{γ·Ψ}(P)` by reindexing `p ↦ pγ`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### Comparison of norms -/

/-! ### Twisted sections -/

/-! ### `Ψ ↦ Ψ · 1[P ∤ c]` for an exterior prime -/

namespace TSection

variable {ι : F →+* ℂ}

theorem restrict_apply_of_val {v : HeightOneSpectrum (𝓞 F)} (hv : ¬ 𝔪 ≤ v.asIdeal)
    (Ψ : TSection ι 𝔪) (s : ℂ) {p : Row 𝔪} (h : v.valuation F (p.c : F) = 1) :
    restrict v hv Ψ s p = Ψ s p := by
  simp [restrict, h]

theorem restrict_apply_of_not_val {v : HeightOneSpectrum (𝓞 F)} (hv : ¬ 𝔪 ≤ v.asIdeal)
    (Ψ : TSection ι 𝔪) (s : ℂ) {p : Row 𝔪} (h : v.valuation F (p.c : F) ≠ 1) :
    restrict v hv Ψ s p = 0 := by
  simp [restrict, h]

end TSection

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.S_Ops
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-S, part 5: operations on genuine sections

* `GSection.nT t`: `(n(t)Φ)_s(c, d) = Φ_s(c, d + ct)`, `t ∈ F` (no symbol).
* `wFun`: `(wΦ)_s(c, d) = ⟨c, d⟩ Φ_s(d, -c)`; `twist_wFun`: its twist is the `w`-translate of the
  twist of `Φ` (MATH §5.2; the symbol is `σ_S((c,d), w)⁻¹·κ(w) = ⟨c, d⟩`).
* `GSection.torus β`: `(A(β)Φ)_s(c, d) = ⟨c, β⟩² Φ_s(β²c, βd)` for `c ≠ 0`, and
  `⟨d, β⟩ Φ_s(0, βd)` on the cell `c = 0` (MATH2 §6.1, with the `c = 0` factor decided by proof);
  `GSection.torusT β = |β|^{2s-1} A(β)` is `Ã(β)`.
  `torus_torus`: `A(β) A(β') = ⟨β, β'⟩ A(β β')`.
* `GSection.sharp π`: `Φ♯_s(c, d) = Φ_s(c, d/π³)`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The Weyl element -/

/-! ### The formal torus action `A(β)` -/

namespace GSection

variable {ι : F →+* ℂ} {P : CubicPkg F}

theorem cpow_sq_cancel {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ (6 * s) * ((x ^ 2 : ℝ) : ℂ) ^ (-(3 * s)) = 1 := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hx2 : ((x ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_pos hx 2).ne'
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.cpow_def_of_ne_zero hx2, ← Complex.exp_add,
    ← Complex.ofReal_log hx.le, ← Complex.ofReal_log (pow_pos hx 2).le, Real.log_pow]
  push_cast
  ring_nf
  exact Complex.exp_zero

theorem sharp_apply (hG : Good 𝔪) (π : F) (hπ : π ≠ 0) (Φ : GSection ι P 𝔪) (s : ℂ) (c d : F) :
    Φ.sharp hG π hπ s c d = Φ s c (d / π ^ 3) := by
  have htf : tf ι P 𝔪 (π ^ 3) c d = 1 := by
    unfold tf
    split_ifs
    · exact brk_pow_three_right _ _
    · rw [brk_pow_three_right, one_pow]
  have e1 : (π ^ 3) ^ 2 * c = (π ^ 2) ^ 3 * c := by ring
  have e2 : π ^ 3 * d = (π ^ 2) ^ 3 * (d / π ^ 3) := by field_simp
  change ((absS 𝔪 π : ℝ) : ℂ) ^ (6 * s) * (tf ι P 𝔪 (π ^ 3) c d
    * Φ s ((π ^ 3) ^ 2 * c) (π ^ 3 * d)) = _
  rw [htf, one_mul, e1, e2, Φ.cube s (π ^ 2) (pow_ne_zero 2 hπ), absS_pow, ← mul_assoc,
    cpow_sq_cancel (absS_pos hπ), one_mul]

end GSection

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.F_Alg_Symbol
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.Row.inf_c _root_.ArtinKP.B.Row.inf_d _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.RO.rowClassEquiv_mk _root_.ArtinKP.RO.rowPair_c _root_.ArtinKP.RO.rowPair_d _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-FA, part 2: the strata of Proposition 5.4 and their symbols (MATH2 §5.3)

`π` generates an exterior prime (`PrimeElt`).  For `m ≤ 3` and `t ∈ R` the relation
`Rel π m t p p₁` says `p · [[1, t], [0, π³]] = π^m · p₁` with `m = min(v_P(c), 3)`:

  `p = (π^m c₁, d)`,  `p₁ = (c₁, c₁ t + π^(3-m) d)`,  and `π ∤ c₁` if `m < 3`.

* bijection part: `rel_smul`, `rel_fun`, `rel_inj`, `rel_dom_iff`, `rel_cod_iff`;
* symbol part: `kappa_rel` (`π ∤ c₁`), `kappa_rel_three` (`m = 3`, all cells, incl. the lower
  cells `π ∣ c₁`), `Phi_rel` (the `S_f`-part for a `t` that is deep for `Φ`);
* the phase `Theta` on the strata `m = 1, 2` and its vanishing sum `rsum_Theta`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.FA

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section basic

variable {ι : F →+* ℂ} {v : HeightOneSpectrum (𝓞 F)} {π : SInt 𝔪}

theorem PrimeElt.coprime_iff (H : PrimeElt ι 𝔪 v π) (d : SInt 𝔪) : IsCoprime d π ↔ ¬ π ∣ d :=
  isCoprime_iff_not_dvd H.isMax d

theorem PrimeElt.not_isUnit (H : PrimeElt ι 𝔪 v π) : ¬ IsUnit π := fun h =>
  H.isMax.ne_top (Ideal.span_singleton_eq_top.2 h)

/-- `v(c) = 1 ↔ π ∤ c`: the condition of `TSection.restrict` in terms of `π`. -/
theorem PrimeElt.val_iff (H : PrimeElt ι 𝔪 v π) (hv : ¬ 𝔪 ≤ v.asIdeal) (c : SInt 𝔪) :
    v.valuation F (c : F) = 1 ↔ ¬ π ∣ c := by
  constructor
  · rintro h ⟨r, rfl⟩
    have h1 : v.valuation F (((π * r : SInt 𝔪)) : F) < 1 := by
      push_cast
      rw [map_mul]
      exact mul_lt_one_of_lt_of_le H.val_lt (sInt_val_le_one r v hv)
    rw [h] at h1
    exact lt_irrefl _ h1
  · intro h
    rcases val_of_isCoprime ((H.coprime_iff c).2 h) v hv with h1 | h1
    · exact h1
    · exact absurd h1 H.val_lt.ne

theorem PrimeElt.not_dvd_of_coprime (H : PrimeElt ι 𝔪 v π) {a b : SInt 𝔪} (h : IsCoprime a b)
    (ha : π ∣ a) : ¬ π ∣ b := by
  rintro hb
  obtain ⟨x, y, hxy⟩ := h
  apply H.not_isUnit
  exact isUnit_of_dvd_one (hxy ▸ dvd_add (ha.mul_left x) (hb.mul_left y))

end basic

/-! ### The relation -/

section rel

variable {ι : F →+* ℂ} {v : HeightOneSpectrum (𝓞 F)} {π : SInt 𝔪} {m : ℕ} {t : SInt 𝔪}

/-- The matrix identity behind `Rel`: `(c, c t + π³ d) = π^m (c₁, d₁)`. -/
theorem Rel.mat (hm : m ≤ 3) {p p₁ : Row 𝔪} (h : Rel π m t p p₁) :
    p.c * t + π ^ 3 * p.d = π ^ m * p₁.d := by
  have hpow : π ^ m * π ^ (3 - m) = π ^ 3 := by rw [← pow_add]; congr 1; omega
  rw [h.1, h.2.1, ← hpow]
  ring

theorem Rel.not_dvd_d (H : PrimeElt ι 𝔪 v π) (hpos : 0 < m) {p p₁ : Row 𝔪}
    (h : Rel π m t p p₁) : ¬ π ∣ p.d := by
  have hcop := p.coprime
  rw [h.1] at hcop
  have h4 : IsCoprime π p.d := (IsCoprime.pow_left_iff hpos).1 hcop.of_mul_left_left
  exact (H.coprime_iff p.d).1 h4.symm

theorem rel_smul (ε : (SInt 𝔪)ˣ) {p p₁ : Row 𝔪} (h : Rel π m t p p₁) :
    Rel π m t (ε • p) (ε • p₁) := by
  refine ⟨?_, ?_, fun hm hd => h.2.2 hm ?_⟩
  · rw [Row.smul_c, Row.smul_c, h.1]; ring
  · rw [Row.smul_d, Row.smul_d, Row.smul_c, h.2.1]; ring
  · rw [Row.smul_c] at hd
    exact (Units.dvd_mul_left).1 hd

theorem rel_fun (hπ : π ≠ 0) {p p₁ p₁' : Row 𝔪} (h : Rel π m t p p₁) (h' : Rel π m t p p₁') :
    p₁ = p₁' := by
  have hc : p₁.c = p₁'.c := mul_left_cancel₀ (pow_ne_zero m hπ) (h.1.symm.trans h'.1)
  refine Row.ext hc ?_
  rw [h.2.1, h'.2.1, hc]

theorem rel_inj (hπ : π ≠ 0) {p p' p₁ : Row 𝔪} (h : Rel π m t p p₁) (h' : Rel π m t p' p₁) :
    p = p' := by
  refine Row.ext (h.1.trans h'.1.symm) ?_
  have e : π ^ (3 - m) * p.d = π ^ (3 - m) * p'.d := by
    have h1 := h.2.1.symm.trans h'.2.1
    exact add_left_cancel h1
  exact mul_left_cancel₀ (pow_ne_zero _ hπ) e

/-- The domain of `Rel π m t`: the rows with `min(v_P(c), 3) = m`. -/
theorem rel_dom_iff (H : PrimeElt ι 𝔪 v π) (hm : m ≤ 3) (t : SInt 𝔪) (p : Row 𝔪) :
    (∃ p₁, Rel π m t p p₁) ↔ π ^ m ∣ p.c ∧ (m < 3 → ¬ π ^ (m + 1) ∣ p.c) := by
  constructor
  · rintro ⟨p₁, h1, -, h3⟩
    refine ⟨⟨p₁.c, h1⟩, fun hlt hd => h3 hlt ?_⟩
    rw [h1, pow_succ] at hd
    exact (mul_dvd_mul_iff_left (pow_ne_zero m H.ne_zero)).1 hd
  · rintro ⟨⟨c₁, hc₁⟩, h2⟩
    have hnd : m < 3 → ¬ π ∣ c₁ := by
      rintro hlt ⟨r, rfl⟩
      apply h2 hlt
      rw [hc₁, pow_succ]
      exact ⟨r, by ring⟩
    have h1 : IsCoprime c₁ p.d := by
      have := p.coprime
      rw [hc₁] at this
      exact this.of_mul_left_right
    have h3 : IsCoprime c₁ (π ^ (3 - m)) := by
      rcases Nat.lt_or_ge m 3 with hlt | hge
      · exact ((H.coprime_iff c₁).2 (hnd hlt)).pow_right
      · have : 3 - m = 0 := by omega
        rw [this, pow_zero]
        exact isCoprime_one_right
    have h4 : IsCoprime c₁ (c₁ * t + π ^ (3 - m) * p.d) := by
      rw [add_comm]
      exact (h3.mul_right h1).add_mul_left_right t
    exact ⟨⟨(c₁, c₁ * t + π ^ (3 - m) * p.d), h4⟩, hc₁, rfl, hnd⟩

/-- The range of `Rel π m t`. -/
theorem rel_cod_iff (H : PrimeElt ι 𝔪 v π) (m : ℕ) (t : SInt 𝔪) (p₁ : Row 𝔪) :
    (∃ p, Rel π m t p p₁) ↔ (m < 3 → ¬ π ∣ p₁.c) ∧
      ∃ d, p₁.d = p₁.c * t + π ^ (3 - m) * d ∧ (0 < m → ¬ π ∣ d) := by
  constructor
  · rintro ⟨p, h1, h2, h3⟩
    refine ⟨h3, p.d, h2, fun hpos hd => ?_⟩
    have hcop := p.coprime
    rw [h1] at hcop
    have h4 : IsCoprime π p.d := (IsCoprime.pow_left_iff hpos).1 hcop.of_mul_left_left
    exact (H.coprime_iff p.d).1 h4.symm hd
  · rintro ⟨h3, d, h2, h4⟩
    have h5 : IsCoprime p₁.c d := by
      have := p₁.coprime
      rw [h2, add_comm] at this
      exact (IsCoprime.of_add_mul_left_right this).of_mul_right_right
    have h6 : IsCoprime (π ^ m) d := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [h0, pow_zero]; exact isCoprime_one_left
      · exact ((H.coprime_iff d).2 (h4 hpos)).symm.pow_left
    exact ⟨⟨(π ^ m * p₁.c, d), h6.mul_left h5⟩, rfl, h2, h3⟩

end rel

/-! ### Powers in the cubic symbol -/

section symbols

variable (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

theorem valc {a b : SInt 𝔪} (h : IsCoprime a b) (w : HeightOneSpectrum (𝓞 F))
    (hw : ¬ 𝔪 ≤ w.asIdeal) (hb : w.valuation F (b : F) ≠ 1) : w.valuation F (a : F) = 1 :=
  (val_of_isCoprime h w hw).resolve_right hb

theorem val_isUnit {c : SInt 𝔪} (hc : IsUnit c) (w : HeightOneSpectrum (𝓞 F))
    (hw : ¬ 𝔪 ≤ w.asIdeal) : w.valuation F (c : F) = 1 := by
  obtain ⟨ε, rfl⟩ := hc
  exact unit_val_eq_one ε w hw

include P hG hz6

theorem cubicExt_ne_zero {d c : SInt 𝔪} (hc : c ≠ 0) (hd : d ≠ 0) (h : IsCoprime d c) :
    cubicExt ι 𝔪 d c ≠ 0 := by
  intro h0
  have := cubicExt_pow_three ι P hG hz6 c d hc hd (valc h)
  rw [h0] at this
  norm_num at this

theorem cubicExt_one_left {c : SInt 𝔪} (hc : c ≠ 0) : cubicExt ι 𝔪 1 c = 1 := by
  have h0 := cubicExt_ne_zero ι P hG hz6 hc one_ne_zero (isCoprime_one_left (x := c))
  have := cubicExt_mul_left ι P hG hz6 c 1 1 hc (valc isCoprime_one_left) (valc isCoprime_one_left)
  rw [one_mul] at this
  exact (mul_eq_left₀ h0).1 this.symm

theorem cubicExt_pow_left {d c : SInt 𝔪} (hc : c ≠ 0) (h : IsCoprime d c) (k : ℕ) :
    cubicExt ι 𝔪 (d ^ k) c = cubicExt ι 𝔪 d c ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, cubicExt_one_left ι P hG hz6 hc]
  | succ k ih =>
    rw [pow_succ, cubicExt_mul_left ι P hG hz6 c (d ^ k) d hc (valc h.pow_left) (valc h), ih,
      pow_succ]

theorem cubicExt_pow_right {d c : SInt 𝔪} (hc : c ≠ 0) (hd : d ≠ 0) (k : ℕ)
    (h : IsCoprime d (c ^ k)) : cubicExt ι 𝔪 d (c ^ k) = cubicExt ι 𝔪 d c ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact cubicExt_of_unit_right ι d 1 (fun w _ => by simp)
  | succ k ih =>
    have h1 : IsCoprime d c := (IsCoprime.pow_right_iff (Nat.succ_pos k)).1 h
    rw [pow_succ, cubicExt_mul_right ι P hG hz6 (c ^ k) c d (pow_ne_zero k hc) hc hd
      (valc h1.pow_right) (valc h1), ih h1.pow_right, pow_succ]

variable {v : HeightOneSpectrum (𝓞 F)} {π : SInt 𝔪} {m : ℕ} {t : SInt 𝔪}

/-- **Symbols, strata with `π ∤ c₁`** (`m = 0, 1, 2`, and `m = 3` on the top cell):
`κ(π^m c₁, d) = (d/π)^{-m} (π/c₁)^{3-m} κ(c₁, d₁)`. -/
theorem kappa_rel (H : PrimeElt ι 𝔪 v π) (hm : m ≤ 3) {p p₁ : Row 𝔪} (h : Rel π m t p p₁)
    (hc₁ : ¬ π ∣ p₁.c) :
    kappaRow ι p = ((cubicExt ι 𝔪 p.d π)⁻¹) ^ m * cubicExt ι 𝔪 π p₁.c ^ (3 - m) * kappaRow ι p₁ := by
  obtain ⟨h1, h2, -⟩ := h
  have hπ := H.ne_zero
  have hc0 : p₁.c ≠ 0 := by rintro h0; exact hc₁ (h0 ▸ dvd_zero π)
  have hpc0 : p.c ≠ 0 := by rw [h1]; exact mul_ne_zero (pow_ne_zero m hπ) hc0
  have hπc : IsCoprime π p₁.c := ((H.coprime_iff p₁.c).2 hc₁).symm
  have hcop : IsCoprime (π ^ m * p₁.c) p.d := h1 ▸ p.coprime
  have hdc : IsCoprime p.d p₁.c := hcop.of_mul_left_right.symm
  have hdπ : IsCoprime p.d (π ^ m) := hcop.of_mul_left_left.symm
  have hχ3 : cubicExt ι 𝔪 π p₁.c ^ 3 = 1 :=
    cubicExt_pow_three ι P hG hz6 p₁.c π hc0 hπ (valc hπc)
  have hχ0 : cubicExt ι 𝔪 π p₁.c ≠ 0 := cubicExt_ne_zero ι P hG hz6 hc0 hπ hπc
  rw [kappaRow, if_neg hpc0, kappaRow, if_neg hc0]
  by_cases hd0 : p.d = 0
  · -- then `π^m c₁` is a unit: `m = 0` and `c₁` is a unit
    have hu : IsUnit (π ^ m * p₁.c) := by
      have := hcop
      rw [hd0] at this
      exact isCoprime_zero_right.1 this
    have hm0 : m = 0 := by
      by_contra hne
      exact H.not_isUnit (isUnit_of_dvd_unit (Dvd.dvd.mul_right (dvd_pow_self π hne) _) hu)
    subst hm0
    rw [pow_zero, one_mul] at hu h1
    have e1 : cubicExt ι 𝔪 p.d p.c = 1 :=
      cubicExt_of_unit_right ι _ _ (fun w hw => by rw [h1]; exact val_isUnit hu w hw)
    have e2 : cubicExt ι 𝔪 p₁.d p₁.c = 1 := cubicExt_of_unit_right ι _ _ (val_isUnit hu)
    rw [e1, e2, pow_zero, hχ3]
    simp
  have e1 : cubicExt ι 𝔪 p.d p.c = cubicExt ι 𝔪 p.d π ^ m * cubicExt ι 𝔪 p.d p₁.c := by
    rw [h1, cubicExt_mul_right ι P hG hz6 (π ^ m) p₁.c p.d (pow_ne_zero m hπ) hc0 hd0
      (valc hdπ) (valc hdc), cubicExt_pow_right ι P hG hz6 hπ hd0 m hdπ]
  have e2 : cubicExt ι 𝔪 p₁.d p₁.c
      = cubicExt ι 𝔪 π p₁.c ^ (3 - m) * cubicExt ι 𝔪 p.d p₁.c := by
    have hcong : cubicExt ι 𝔪 p₁.d p₁.c = cubicExt ι 𝔪 (π ^ (3 - m) * p.d) p₁.c := by
      refine cubicExt_congr ι hG p₁.c _ _ hc0 ?_
      rw [h2, Ideal.mem_span_singleton]
      exact ⟨t, by ring⟩
    rw [hcong, cubicExt_mul_left ι P hG hz6 p₁.c (π ^ (3 - m)) p.d hc0 (valc hπc.pow_left)
      (valc hdc), cubicExt_pow_left ι P hG hz6 hc0 hπc]
  have hχd0 : cubicExt ι 𝔪 p.d p₁.c ≠ 0 := cubicExt_ne_zero ι P hG hz6 hc0 hd0 hdc
  have hpow0 : cubicExt ι 𝔪 π p₁.c ^ (3 - m) ≠ 0 := pow_ne_zero _ hχ0
  rw [e1, e2, mul_inv, mul_inv, inv_pow]
  field_simp

/-- **Symbols, stratum `m = 3`, all cells** (including the lower cells `π ∣ c₁`):
`κ(π³ c₁, d₁ - c₁ t) = κ(c₁, d₁)`. -/
theorem kappa_rel_three (H : PrimeElt ι 𝔪 v π) {p p₁ : Row 𝔪} (h : Rel π 3 t p p₁) :
    kappaRow ι p = kappaRow ι p₁ := by
  obtain ⟨h1, h2, -⟩ := h
  have hπ := H.ne_zero
  rw [Nat.sub_self, pow_zero, one_mul] at h2
  by_cases hc0 : p₁.c = 0
  · have hpc : p.c = 0 := by rw [h1, hc0, mul_zero]
    rw [kappaRow, if_pos hpc, kappaRow, if_pos hc0]
  have hpc0 : p.c ≠ 0 := by rw [h1]; exact mul_ne_zero (pow_ne_zero 3 hπ) hc0
  have hcop : IsCoprime (π ^ 3 * p₁.c) p.d := h1 ▸ p.coprime
  have hdc : IsCoprime p.d p₁.c := hcop.of_mul_left_right.symm
  have hdπ3 : IsCoprime p.d (π ^ 3) := hcop.of_mul_left_left.symm
  have hdπ : IsCoprime p.d π := (IsCoprime.pow_right_iff (by norm_num)).1 hdπ3
  have hd0 : p.d ≠ 0 := by
    rintro h0
    rw [h0] at hdπ
    exact H.not_isUnit (isCoprime_zero_left.1 hdπ)
  rw [kappaRow, if_neg hpc0, kappaRow, if_neg hc0]
  congr 1
  rw [h1, cubicExt_mul_right ι P hG hz6 (π ^ 3) p₁.c p.d (pow_ne_zero 3 hπ) hc0 hd0
    (valc hdπ3) (valc hdc), cubicExt_pow_right ι P hG hz6 hπ hd0 3 hdπ3,
    cubicExt_pow_three ι P hG hz6 π p.d hπ hd0 (valc hdπ), one_mul]
  refine (cubicExt_congr ι hG p₁.c _ _ hc0 ?_).symm
  rw [h2, Ideal.mem_span_singleton]
  exact ⟨t, by ring⟩

omit hG hz6 in
/-- **The `S_f`-part**: for `t` deep for `Φ` (`Φ_s(c, d + c t/π³) = Φ_s(c, d)`),
`Φ_s(π^m c₁, d) = Φ_s(π^m c₁, π^m d₁/π³)`. -/
theorem Phi_rel (hπ : π ≠ 0) (hm : m ≤ 3) {p p₁ : Row 𝔪} (h : Rel π m t p p₁)
    (Φ : GSection ι P 𝔪)
    (hdeep : ∀ (s : ℂ) (c d : F), Φ s c (d + c * ((t : F) / (π : F) ^ 3)) = Φ s c d) (s : ℂ) :
    Φ s (p.c : F) (p.d : F)
      = Φ s ((π : F) ^ m * (p₁.c : F)) ((π : F) ^ m * ((p₁.d : F) / (π : F) ^ 3)) := by
  have hπF : (π : F) ≠ 0 := fun h0 => hπ (Subtype.ext h0)
  have hpow : (π : F) ^ m * (π : F) ^ (3 - m) = (π : F) ^ 3 := by
    rw [← pow_add]; congr 1; omega
  have hc : (p.c : F) = (π : F) ^ m * (p₁.c : F) := by rw [h.1]; push_cast; rfl
  have hd : (p₁.d : F) = (p₁.c : F) * (t : F) + (π : F) ^ (3 - m) * (p.d : F) := by
    rw [h.2.1]; push_cast; rfl
  have e : (π : F) ^ m * ((p₁.d : F) / (π : F) ^ 3)
      = (p.d : F) + ((π : F) ^ m * (p₁.c : F)) * ((t : F) / (π : F) ^ 3) := by
    have h3 : ((π : F) ^ 3) ≠ 0 := pow_ne_zero 3 hπF
    rw [hd]
    calc (π : F) ^ m * (((p₁.c : F) * (t : F) + (π : F) ^ (3 - m) * (p.d : F)) / (π : F) ^ 3)
        = ((π : F) ^ m * (p₁.c : F) * (t : F)
            + ((π : F) ^ m * (π : F) ^ (3 - m)) * (p.d : F)) / (π : F) ^ 3 := by ring
      _ = ((π : F) ^ m * (p₁.c : F) * (t : F) + (π : F) ^ 3 * (p.d : F)) / (π : F) ^ 3 := by
          rw [hpow]
      _ = _ := by field_simp; ring
  rw [e, hdeep, hc]

end symbols

/-! ### The phase on the strata `m = 1, 2` -/

section theta

variable {ι : F →+* ℂ} {π : SInt 𝔪} {m : ℕ}

theorem Theta_eq (hπ : π ≠ 0) {x d : SInt 𝔪} (hx : x = π ^ (3 - m) * d) (hd : ¬ π ∣ d) :
    Theta ι π m x = ((cubicExt ι 𝔪 d π)⁻¹) ^ m := by
  have h : ∃ d, x = π ^ (3 - m) * d ∧ ¬ π ∣ d := ⟨d, hx, hd⟩
  have hch : h.choose = d :=
    mul_left_cancel₀ (pow_ne_zero (3 - m) hπ) (h.choose_spec.1.symm.trans hx)
  rw [Theta, dif_pos h, hch]

theorem Theta_of_not {x : SInt 𝔪} (h : ¬ ∃ d, x = π ^ (3 - m) * d ∧ ¬ π ∣ d) :
    Theta ι π m x = 0 := by
  rw [Theta, dif_neg h]

variable (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {v : HeightOneSpectrum (𝓞 F)}

private theorem guard_shift (hm1 : 1 ≤ m) (hm : m ≤ 3) {x d : SInt 𝔪}
    (hx : x = π ^ (3 - m) * d) (hd : ¬ π ∣ d) (r : SInt 𝔪) :
    x + π ^ 3 * r = π ^ (3 - m) * (d + π ^ m * r) ∧ ¬ π ∣ d + π ^ m * r := by
  have hpow : π ^ (3 - m) * π ^ m = π ^ 3 := by rw [← pow_add]; congr 1; omega
  refine ⟨by rw [hx, ← hpow]; ring, fun h => hd ?_⟩
  have h2 : π ∣ π ^ m * r := Dvd.dvd.mul_right (dvd_pow_self π (by omega)) r
  exact (dvd_add_left h2).1 h

include hG in
theorem Theta_per (hπ : π ≠ 0) (hm1 : 1 ≤ m) (hm : m ≤ 3) : Per (π ^ 3) (Theta ι π m) := by
  have key : ∀ (x d r : SInt 𝔪), x = π ^ (3 - m) * d → ¬ π ∣ d →
      Theta ι π m (x + π ^ 3 * r) = Theta ι π m x := by
    intro x d r hx hd
    obtain ⟨h1, h2⟩ := guard_shift hm1 hm hx hd r
    rw [Theta_eq hπ h1 h2, Theta_eq hπ hx hd]
    congr 2
    refine cubicExt_congr ι hG π _ _ hπ ?_
    rw [Ideal.mem_span_singleton]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact ⟨π ^ k * r, by ring⟩
  intro a b (hab : π ^ 3 ∣ a - b)
  obtain ⟨r, hr⟩ := hab
  have ha : a = b + π ^ 3 * r := by rw [← hr]; ring
  have hb : b = a + π ^ 3 * (-r) := by rw [ha]; ring
  by_cases h : ∃ d, b = π ^ (3 - m) * d ∧ ¬ π ∣ d
  · obtain ⟨d, hx, hd⟩ := h
    rw [ha, key b d r hx hd]
  · by_cases h' : ∃ d, a = π ^ (3 - m) * d ∧ ¬ π ∣ d
    · obtain ⟨d, hx, hd⟩ := h'
      rw [hb, key a d (-r) hx hd]
    · rw [Theta_of_not h, Theta_of_not h']

include P hG hz6 in
theorem Theta_mul (H : PrimeElt ι 𝔪 v π) {u : SInt 𝔪} (hu : ¬ π ∣ u) (x : SInt 𝔪) :
    Theta ι π m (u * x) = ((cubicExt ι 𝔪 u π)⁻¹) ^ m * Theta ι π m x := by
  have hπ := H.ne_zero
  have huc : IsCoprime u π := (H.coprime_iff u).2 hu
  by_cases h : ∃ d, x = π ^ (3 - m) * d ∧ ¬ π ∣ d
  · obtain ⟨d, hx, hd⟩ := h
    have hdc : IsCoprime d π := (H.coprime_iff d).2 hd
    have h1 : u * x = π ^ (3 - m) * (u * d) := by rw [hx]; ring
    have h2 : ¬ π ∣ u * d := (H.coprime_iff _).1 (huc.mul_left hdc)
    rw [Theta_eq hπ h1 h2, Theta_eq hπ hx hd,
      cubicExt_mul_left ι P hG hz6 π u d hπ (valc huc) (valc hdc), mul_inv, mul_pow]
  · have h' : ¬ ∃ d, u * x = π ^ (3 - m) * d ∧ ¬ π ∣ d := by
      rintro ⟨d', hx', hd'⟩
      apply h
      have hdvd : π ^ (3 - m) ∣ x * u := by rw [mul_comm, hx']; exact dvd_mul_right _ _
      obtain ⟨d, hd⟩ := (huc.symm.pow_left (m := 3 - m)).dvd_of_dvd_mul_right hdvd
      refine ⟨d, hd, fun hπd => hd' ?_⟩
      have e : d' = u * d := by
        apply mul_left_cancel₀ (pow_ne_zero (3 - m) hπ)
        rw [← hx', hd]; ring
      rw [e]
      exact hπd.mul_left u
    rw [Theta_of_not h, Theta_of_not h', mul_zero]

include P hG hz6 in
/-- **The strata `m = 1, 2` cancel**: `∑_{x mod π³} Θ_m(x) = 0`. -/
theorem rsum_Theta (H : PrimeElt ι 𝔪 v π) (hm1 : 1 ≤ m) (hm2 : m ≤ 2) :
    rsum (π ^ 3) (Theta ι π m) = 0 := by
  obtain ⟨u, hu, hne⟩ := H.nontriv
  have hπ := H.ne_zero
  have huc : IsCoprime u π := (H.coprime_iff u).2 hu
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero π)
  have h3 : cubicExt ι 𝔪 u π ^ 3 = 1 := cubicExt_pow_three ι P hG hz6 π u hπ hu0 (valc huc)
  have h3' : (cubicExt ι 𝔪 u π)⁻¹ ^ 3 = 1 := by rw [inv_pow, h3, inv_one]
  have hne' : (cubicExt ι 𝔪 u π)⁻¹ ≠ 1 := fun h => hne (inv_eq_one.1 h)
  refine rsum_eq_zero_of_mul (Theta_per hG hπ hm1 (by omega)) huc.pow_right
    (pow_ne_one_of_cube h3' hne' (by omega)) (Theta_mul P hG hz6 H hu)

end theta

end ArtinKP.FA
end
end

section
-- module Solutions.Artin.KP.F_Alg_Main
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.Row.inf_c _root_.ArtinKP.B.Row.inf_d _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.RO.rowClassEquiv_mk _root_.ArtinKP.RO.rowPair_c _root_.ArtinKP.RO.rowPair_d _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-FA, part 3: Proposition 5.4 as a reindexing identity (MATH2 §5.3)

`π` generates the exterior prime `v` (`PrimeElt`), `T` is a complete set of representatives of
`R/π³R` whose elements are deep for the genuine section `Φ`, and `f : F → F → ℂ` is an arbitrary
function with `f(πc, πd) = cc · f(c, d)` and `f(εc, εd) = |ε|_{S_f}^s f(c, d)` for `ε ∈ U_S`
(in the application `f = I_{(c,d)}(P)^s`, `cc = N_∞(π)^{-s}`).  With `Ψ = κΦ`, `Ψ♯ = κΦ♯`,
`X = cc³ |π|_{S_f}^{-3s}` and `q = #(R/πR)`:

  `∑_{t ∈ T} ∑_{p ∈ Row/U_S} Ψ_s(p) f(p·[[1,t],[0,π³]])
      = q³X · ∑_{p₁} Ψ♯_s(p₁) f(p₁) + (1 - q²X) · ∑_{p₁} (Ψ♯·1[P ∤ c₁])_s(p₁) f(p₁)`

(`prop54`; `prop54_omega` is the form with the weight `ω(a₁)` and needs no summability of the
right-hand side).  The counting part is `fiber_sum`, the symbol part is `W_spec`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.FA

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

variable {ι : F →+* ℂ} (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {v : HeightOneSpectrum (𝓞 F)} {π : SInt 𝔪} (H : PrimeElt ι 𝔪 v π) (Φ : GSection ι P 𝔪)

/-- **Symbol part of Proposition 5.4**: on the stratum `(m, t)`,
`Ψ_s(π^m c₁, π^{m-3}(d₁ - c₁ t)) = W m t s (c₁, d₁)`. -/
theorem W_spec {m : ℕ} (hm : m ≤ 3) {t : SInt 𝔪}
    (hdeep : ∀ (s : ℂ) (c d : F), Φ s c (d + c * ((t : F) / (π : F) ^ 3)) = Φ s c d) (s : ℂ)
    {p p₁ : Row 𝔪} (h : Rel π m t p p₁) :
    Φ.twist hG hz6 s p = W P hG hz6 H Φ m t s p₁ := by
  have hπ := H.ne_zero
  have hΦ := Phi_rel ι P hπ hm h Φ hdeep s
  rw [GSection.twist_apply, hΦ]
  by_cases h0 : m = 0
  · subst h0
    have hk := kappa_rel ι P hG hz6 H hm h (h.2.2 (by norm_num))
    have hc0 : p₁.c ≠ 0 := by rintro e; exact h.2.2 (by norm_num) (e ▸ dvd_zero π)
    have hπc : IsCoprime π p₁.c := ((H.coprime_iff p₁.c).2 (h.2.2 (by norm_num))).symm
    have hχ3 : cubicExt ι 𝔪 π p₁.c ^ 3 = 1 :=
      cubicExt_pow_three ι P hG hz6 p₁.c π hc0 hπ (valc hπc)
    rw [W, if_pos rfl, GSection.twist_apply, GSection.sharp_apply, hk, pow_zero, hχ3, pow_zero,
      one_mul, one_mul, one_mul, one_mul]
  by_cases h3 : m = 3
  · subst h3
    rw [W, if_neg (by norm_num), if_pos rfl, GSection.twist_apply, GSection.sharp_apply,
      kappa_rel_three ι P hG hz6 H h, Φ.cube s (π : F) H.coe_ne_zero]
    ring
  · have hlt : m < 3 := by omega
    have hpos : 0 < m := by omega
    have hk := kappa_rel ι P hG hz6 H hm h (h.2.2 hlt)
    have hT : Theta ι π m (p₁.d - p₁.c * t) = ((cubicExt ι 𝔪 p.d π)⁻¹) ^ m :=
      Theta_eq hπ (by rw [h.2.1]; ring) (h.not_dvd_d H hpos)
    rw [W, if_neg h0, if_neg h3, hT, hk]

section counting

variable {T : Finset (SInt 𝔪)} (hT : IsReps (π ^ 3) T)

include H hT

omit hz6 in
include hG in
theorem card_reps : (T.card : ℂ) = (Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 3 := by
  have hfin : ∀ k : ℕ, Finite (SInt 𝔪 ⧸ Ideal.span {π ^ k}) := fun k =>
    finite_quot_span hG.ne_bot (pow_ne_zero k H.ne_zero)
  have h := sum_reps hT (f := fun _ => (1 : ℂ)) (fun _ _ _ => rfl)
  rw [rsum_pow_one H.ne_zero hfin 3] at h
  rw [← h]
  simp

open Classical in
/-- Stratum `m = 0`: the unique `t ≡ d₁/c₁ mod π³`. -/
theorem count_zero (p₁ : Row 𝔪) :
    ∑ t ∈ T, (if ∃ p, Rel π 0 t p p₁ then (1 : ℂ) else 0) = if π ∣ p₁.c then 0 else 1 := by
  have hcond : ∀ t, (∃ p, Rel π 0 t p p₁) ↔ ¬ π ∣ p₁.c ∧ π ^ 3 ∣ p₁.d - p₁.c * t := by
    intro t
    rw [rel_cod_iff H 0 t p₁]
    constructor
    · rintro ⟨h1, d, h2, -⟩
      exact ⟨h1 (by norm_num), d, by rw [h2]; ring⟩
    · rintro ⟨h1, d, h2⟩
      exact ⟨fun _ => h1, d, by linear_combination h2, fun h => absurd h (lt_irrefl 0)⟩
  simp only [hcond]
  by_cases hc : π ∣ p₁.c
  · simp [hc]
  · simp only [hc, not_false_eq_true, true_and, if_false]
    have hu : IsCoprime p₁.c (π ^ 3) := ((H.coprime_iff p₁.c).2 hc).pow_right
    rw [sum_reps_affine hT (per_dvd (π ^ 3) (1 : ℂ) 0) hu p₁.d,
      rsum_ite_dvd (π ^ 3) (fun _ => (1 : ℂ))]

include hG in
open Classical in
/-- Stratum `m = 3`: `q³ - q²` values of `t` on the top cell, all `q³` on the lower cells. -/
theorem count_three (p₁ : Row 𝔪) :
    ∑ t ∈ T, (if ∃ p, Rel π 3 t p p₁ then (1 : ℂ) else 0)
      = if π ∣ p₁.c then (Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 3 else (Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 3 - (Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 2 := by
  have hfin : ∀ k : ℕ, Finite (SInt 𝔪 ⧸ Ideal.span {π ^ k}) := fun k =>
    finite_quot_span hG.ne_bot (pow_ne_zero k H.ne_zero)
  have hcond : ∀ t, (∃ p, Rel π 3 t p p₁) ↔ ¬ π ∣ p₁.d - p₁.c * t := by
    intro t
    rw [rel_cod_iff H 3 t p₁]
    constructor
    · rintro ⟨-, d, h2, h3⟩
      have e : p₁.d - p₁.c * t = d := by rw [h2]; ring
      rw [e]
      exact h3 (by norm_num)
    · intro h
      exact ⟨fun h3 => absurd h3 (lt_irrefl 3), p₁.d - p₁.c * t, by ring, fun _ => h⟩
  simp only [hcond]
  by_cases hc : π ∣ p₁.c
  · have hall : ∀ t, ¬ π ∣ p₁.d - p₁.c * t := by
      intro t hd
      have hd1 : π ∣ p₁.d := by
        have := dvd_add hd (hc.mul_right t)
        rwa [sub_add_cancel] at this
      exact H.not_dvd_of_coprime p₁.coprime hc hd1
    simp only [hall, not_false_eq_true, if_true, hc, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact card_reps hG H hT
  · simp only [hc, if_false]
    have hu : IsCoprime p₁.c (π ^ 3) := ((H.coprime_iff p₁.c).2 hc).pow_right
    have e : ∀ t, (if ¬ π ∣ p₁.d - p₁.c * t then (1 : ℂ) else 0)
        = (fun x => if π ∣ x then (0 : ℂ) else 1) (p₁.d - p₁.c * t) := by
      intro t; simp only; split_ifs <;> rfl
    simp only [e]
    have h2 := rsum_not_dvd H.ne_zero hfin 2
    rw [sum_reps_affine hT ((per_dvd π (0 : ℂ) 1).of_dvd (dvd_pow_self π (by norm_num))) hu p₁.d]
    exact h2

include P hG hz6 in
/-- Strata `m = 1, 2`: the phases cancel. -/
theorem sum_Theta_reps {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m ≤ 2) (p₁ : Row 𝔪) (hc : ¬ π ∣ p₁.c) :
    ∑ t ∈ T, Theta ι π m (p₁.d - p₁.c * t) = 0 := by
  have hu : IsCoprime p₁.c (π ^ 3) := ((H.coprime_iff p₁.c).2 hc).pow_right
  rw [sum_reps_affine hT (Theta_per hG H.ne_zero hm1 (by omega)) hu p₁.d,
    rsum_Theta P hG hz6 H hm1 hm2]

include P hG hz6 in
open Classical in
/-- **Counting part of Proposition 5.4**: the sum over the fibre `{(m, t)}` over `p₁` of the
values `W` with weights `cc^m` is `ω(p₁) · Ψ♯_s(p₁)`, with
`ω = q³X + (1 - q²X)·1[π ∤ c₁]`, `X = cc³ |π|^{-3s}`. -/
theorem fiber_sum (s cc : ℂ) (p₁ : Row 𝔪) :
    ∑ t ∈ T, ∑ m ∈ Finset.range 4,
        (if ∃ p, Rel π m t p p₁ then W P hG hz6 H Φ m t s p₁ * cc ^ m else 0)
      = ((Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 3 * (cc ^ 3 * ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s)))
          + (1 - (Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 2 * (cc ^ 3 * ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s))))
            * (if π ∣ p₁.c then 0 else 1))
        * (Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6 s p₁ := by
  set Ψs := (Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6 s p₁ with hΨs
  set A := ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s)) with hA
  rw [Finset.sum_comm]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  -- m = 0
  have e0 : ∑ t ∈ T, (if ∃ p, Rel π 0 t p p₁ then W P hG hz6 H Φ 0 t s p₁ * cc ^ 0 else 0)
      = (if π ∣ p₁.c then 0 else 1) * Ψs := by
    rw [← count_zero H hT p₁, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [W, if_pos rfl, pow_zero, mul_one]
    split_ifs <;> simp [hΨs]
  -- m = 3
  have e3 : ∑ t ∈ T, (if ∃ p, Rel π 3 t p p₁ then W P hG hz6 H Φ 3 t s p₁ * cc ^ 3 else 0)
      = (if π ∣ p₁.c then (Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 3 else (Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 3 - (Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 2) * (A * Ψs * cc ^ 3) := by
    rw [← count_three hG H hT p₁, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [W, if_neg (show ¬ (3 : ℕ) = 0 by norm_num), if_pos rfl]
    split_ifs <;> simp [hΨs, hA]
  -- m = 1, 2
  have e12 : ∀ m, 1 ≤ m → m ≤ 2 →
      ∑ t ∈ T, (if ∃ p, Rel π m t p p₁ then W P hG hz6 H Φ m t s p₁ * cc ^ m else 0) = 0 := by
    intro m hm1 hm2
    by_cases hc : π ∣ p₁.c
    · refine Finset.sum_eq_zero fun t _ => ?_
      rw [if_neg]
      rintro ⟨p, hp⟩
      exact hp.2.2 (by omega) hc
    · have key : ∀ t, (if ∃ p, Rel π m t p p₁ then W P hG hz6 H Φ m t s p₁ * cc ^ m else 0)
          = Theta ι π m (p₁.d - p₁.c * t) * (cubicExt ι 𝔪 π p₁.c ^ (3 - m) * kappaRow ι p₁
            * Φ s ((π : F) ^ m * (p₁.c : F)) ((π : F) ^ m * ((p₁.d : F) / (π : F) ^ 3))
            * cc ^ m) := by
        intro t
        split_ifs with hex
        · rw [W, if_neg (show ¬ m = 0 by omega), if_neg (show ¬ m = 3 by omega)]
          ring
        · have hg : ¬ ∃ d, p₁.d - p₁.c * t = π ^ (3 - m) * d ∧ ¬ π ∣ d := by
            rintro ⟨d, hd1, hd2⟩
            apply hex
            rw [rel_cod_iff H m t p₁]
            exact ⟨fun _ => hc, d, by linear_combination hd1, fun _ => hd2⟩
          rw [Theta_of_not hg, zero_mul]
      simp only [key]
      rw [← Finset.sum_mul, sum_Theta_reps P hG hz6 H hT hm1 hm2 p₁ hc, zero_mul]
  rw [e0, e12 1 le_rfl (by norm_num), e12 2 (by norm_num) le_rfl, e3]
  split_ifs <;> ring

end counting

/-! ### The reindexing identity -/

section main

variable {T : Finset (SInt 𝔪)} (hT : IsReps (π ^ 3) T)
  (hdeep : ∀ t ∈ T, ∀ (s : ℂ) (c d : F), Φ s c (d + c * ((t : F) / (π : F) ^ 3)) = Φ s c d)
  (f : F → F → ℂ) (s cc : ℂ)
  (hfπ : ∀ c d : F, f ((π : F) * c) ((π : F) * d) = cc * f c d)
  (hfU : ∀ (ε : (SInt 𝔪)ˣ) (c d : F), f (((ε : SInt 𝔪) : F) * c) (((ε : SInt 𝔪) : F) * d)
    = ((absS 𝔪 ((ε : SInt 𝔪) : F) : ℝ) : ℂ) ^ s * f c d)

include hfπ in
theorem f_pow (m : ℕ) (c d : F) : f ((π : F) ^ m * c) ((π : F) ^ m * d) = cc ^ m * f c d := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, mul_assoc, hfπ, ih, pow_succ']
    ring

include hfU in
theorem gU_smul (t : SInt 𝔪) (ε : (SInt 𝔪)ˣ) (p : Row 𝔪) :
    gU (π := π) P hG hz6 Φ f s t (ε • p) = gU (π := π) P hG hz6 Φ f s t p := by
  have hx : ((absS 𝔪 ((ε : SInt 𝔪) : F) : ℝ) : ℂ) ≠ 0 := by
    have hε : ((ε : SInt 𝔪) : F) ≠ 0 := fun h => ε.ne_zero (Subtype.ext h)
    exact Complex.ofReal_ne_zero.mpr (absS_pos hε).ne'
  have h1 : ((absS 𝔪 ((ε : SInt 𝔪) : F) : ℝ) : ℂ) ^ (-s)
      * ((absS 𝔪 ((ε : SInt 𝔪) : F) : ℝ) : ℂ) ^ s = 1 := by
    rw [← Complex.cpow_add _ _ hx, neg_add_cancel, Complex.cpow_zero]
  have hc : (((ε • p).c : SInt 𝔪) : F) = ((ε : SInt 𝔪) : F) * (p.c : F) := by
    rw [Row.smul_c]; push_cast; rfl
  have hd : (((ε • p).d : SInt 𝔪) : F) = ((ε : SInt 𝔪) : F) * (p.d : F) := by
    rw [Row.smul_d]; push_cast; rfl
  have e : ((ε : SInt 𝔪) : F) * (p.c : F) * (t : F) + (π : F) ^ 3 * (((ε : SInt 𝔪) : F) * (p.d : F))
      = ((ε : SInt 𝔪) : F) * ((p.c : F) * (t : F) + (π : F) ^ 3 * (p.d : F)) := by ring
  unfold gU
  rw [(Φ.twist hG hz6).hom, hc, hd, e, hfU]
  linear_combination ((Φ.twist hG hz6) s p
    * f (p.c : F) ((p.c : F) * (t : F) + (π : F) ^ 3 * (p.d : F))) * h1

include hfπ in
/-- On the stratum `(m, t)`: `gU t p = W m t s p₁ · cc^m · f(p₁)`. -/
theorem gU_rel {m : ℕ} (hm : m ≤ 3) {t : SInt 𝔪}
    (hd : ∀ (s : ℂ) (c d : F), Φ s c (d + c * ((t : F) / (π : F) ^ 3)) = Φ s c d)
    {p p₁ : Row 𝔪} (h : Rel π m t p p₁) :
    gU (π := π) P hG hz6 Φ f s t p = W P hG hz6 H Φ m t s p₁ * cc ^ m * f (p₁.c : F) (p₁.d : F) := by
  have h1 : (p.c : F) = (π : F) ^ m * (p₁.c : F) := by rw [h.1]; push_cast; rfl
  have h2 : (p.c : F) * (t : F) + (π : F) ^ 3 * (p.d : F) = (π : F) ^ m * (p₁.d : F) := by
    have := congrArg (fun x : SInt 𝔪 => (x : F)) (h.mat hm)
    push_cast at this
    exact this
  unfold gU
  rw [W_spec P hG hz6 H Φ hm hd s h, h2, h1, f_pow f cc hfπ]
  ring

include P H hT hdeep hfπ hfU in
open Classical in
/-- **Proposition 5.4, weight form.**  No summability of the right-hand side is assumed; it is
part of the conclusion. -/
theorem prop54_omega
    (hsum : ∀ t ∈ T, Summable fun x : RowQ 𝔪 => gU (π := π) P hG hz6 Φ f s t x.out) :
    (Summable fun y : RowQ 𝔪 =>
      ((Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 3
            * (cc ^ 3 * ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s)))
          + (1 - (Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 2
            * (cc ^ 3 * ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s))))
            * (if π ∣ y.out.c then 0 else 1))
        * (Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6 s y.out
        * f (y.out.c : F) (y.out.d : F)) ∧
    ∑ t ∈ T, ∑' x : RowQ 𝔪, gU (π := π) P hG hz6 Φ f s t x.out
      = ∑' y : RowQ 𝔪,
          ((Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 3
              * (cc ^ 3 * ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s)))
            + (1 - (Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 2
              * (cc ^ 3 * ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s))))
              * (if π ∣ y.out.c then 0 else 1))
          * (Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6 s y.out
          * f (y.out.c : F) (y.out.d : F) := by
  have hπ := H.ne_zero
  -- the term of the stratum `(m, t)` on the target side
  set term : ℕ → SInt 𝔪 → RowQ 𝔪 → ℂ := fun m t y =>
    if ∃ p, Rel π m t p y.out then
      W P hG hz6 H Φ m t s y.out * cc ^ m * f (y.out.c : F) (y.out.d : F) else 0 with hterm
  -- transfer of one stratum
  have hstr : ∀ t ∈ T, ∀ m, m ≤ 3 →
      Summable (term m t) ∧
      (∑' x : RowQ 𝔪, (if ∃ p₁, Rel π m t x.out p₁ then gU (π := π) P hG hz6 Φ f s t x.out else 0))
        = ∑' y : RowQ 𝔪, term m t y := by
    intro t ht m hm
    have hs1 : Summable (fun x : RowQ 𝔪 =>
        if ∃ p₁, Rel π m t x.out p₁ then gU (π := π) P hG hz6 Φ f s t x.out else 0) := by
      refine Summable.of_norm_bounded (hsum t ht).norm fun x => ?_
      split_ifs
      · exact le_rfl
      · rw [norm_zero]; exact norm_nonneg _
    have := tsum_orbit_rel (G := (SInt 𝔪)ˣ) (gU (π := π) P hG hz6 Φ f s t)
      (fun p₁ : Row 𝔪 => W P hG hz6 H Φ m t s p₁ * cc ^ m * f (p₁.c : F) (p₁.d : F))
      (Rel π m t) (fun ε p => gU_smul P hG hz6 Φ f s hfU t ε p)
      (fun ε p p₁ h => rel_smul ε h) (fun p p₁ p₁' h h' => rel_fun hπ h h')
      (fun p p' p₁ h h' => rel_inj hπ h h')
      (fun p p₁ h => gU_rel P hG hz6 H Φ f s cc hfπ hm (hdeep t ht) h)
    exact ⟨this.1 hs1, this.2⟩
  -- decomposition of the source side into strata
  have hdec : ∀ t ∈ T, ∑' x : RowQ 𝔪, gU (π := π) P hG hz6 Φ f s t x.out
      = ∑ m ∈ Finset.range 4, ∑' y : RowQ 𝔪, term m t y := by
    intro t ht
    have hpt : ∀ x : RowQ 𝔪, gU (π := π) P hG hz6 Φ f s t x.out
        = ∑ m ∈ Finset.range 4,
          (if ∃ p₁, Rel π m t x.out p₁ then gU (π := π) P hG hz6 Φ f s t x.out else 0) := by
      intro x
      set z := gU (π := π) P hG hz6 Φ f s t x.out
      have hd : ∀ m ∈ Finset.range 4, (if ∃ p₁, Rel π m t x.out p₁ then z else 0)
          = if π ^ m ∣ x.out.c ∧ (m < 3 → ¬ π ^ (m + 1) ∣ x.out.c) then z else 0 := by
        intro m hm
        rw [Finset.mem_range] at hm
        simp only [rel_dom_iff H (by omega : m ≤ 3) t x.out]
      rw [Finset.sum_congr rfl hd]
      by_cases h1 : π ∣ x.out.c
      · by_cases h2 : π ^ 2 ∣ x.out.c
        · by_cases h3 : π ^ 3 ∣ x.out.c
          · simp [Finset.sum_range_succ, h1, h2, h3]
          · simp [Finset.sum_range_succ, h1, h2, h3]
        · have h3 : ¬ π ^ 3 ∣ x.out.c := fun h =>
            h2 (dvd_trans (pow_dvd_pow π (by norm_num)) h)
          simp [Finset.sum_range_succ, h1, h2, h3]
      · have h2 : ¬ π ^ 2 ∣ x.out.c := fun h => h1 (dvd_trans (dvd_pow_self π (by norm_num)) h)
        have h3 : ¬ π ^ 3 ∣ x.out.c := fun h => h1 (dvd_trans (dvd_pow_self π (by norm_num)) h)
        simp [Finset.sum_range_succ, h1, h2, h3]
    have hs : ∀ m ∈ Finset.range 4, Summable (fun x : RowQ 𝔪 =>
        if ∃ p₁, Rel π m t x.out p₁ then gU (π := π) P hG hz6 Φ f s t x.out else 0) := by
      intro m _
      refine Summable.of_norm_bounded (hsum t ht).norm fun x => ?_
      split_ifs
      · exact le_rfl
      · rw [norm_zero]; exact norm_nonneg _
    rw [tsum_congr hpt, Summable.tsum_finsetSum hs]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    exact (hstr t ht m (by omega)).2
  have hsm : ∀ t ∈ T, ∀ m ∈ Finset.range 4, Summable (term m t) := fun t ht m hm =>
    (hstr t ht m (by rw [Finset.mem_range] at hm; omega)).1
  have hst : ∀ t ∈ T, Summable (fun y : RowQ 𝔪 => ∑ m ∈ Finset.range 4, term m t y) :=
    fun t ht => summable_sum (hsm t ht)
  -- the pointwise fibre identity
  have hfib : ∀ y : RowQ 𝔪, ∑ t ∈ T, ∑ m ∈ Finset.range 4, term m t y
      = ((Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 3
              * (cc ^ 3 * ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s)))
            + (1 - (Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 2
              * (cc ^ 3 * ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s))))
              * (if π ∣ y.out.c then 0 else 1))
          * (Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6 s y.out
          * f (y.out.c : F) (y.out.d : F) := by
    intro y
    rw [← fiber_sum P hG hz6 H Φ hT s cc y.out, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [hterm]
    split_ifs
    · rfl
    · rw [zero_mul]
  constructor
  · exact (summable_sum hst).congr fun y => hfib y
  · rw [Finset.sum_congr rfl hdec]
    rw [← tsum_congr hfib, Summable.tsum_finsetSum hst]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Summable.tsum_finsetSum (hsm t ht)]

include P H hT hdeep hfπ hfU in
/-- **Proposition 5.4** (MATH2 §5.3) as a reindexing identity:
`∑_t ∑_p Ψ_s(p) f(p·[[1,t],[0,π³]]) = q³X · ∑ Ψ♯_s f + (1 - q²X) · ∑ (Ψ♯·1[P ∤ c])_s f`,
`X = cc³ |π|_{S_f}^{-3s}`. -/
theorem prop54_oai (hv : ¬ 𝔪 ≤ v.asIdeal)
    (hsum : ∀ t ∈ T, Summable fun x : RowQ 𝔪 => gU (π := π) P hG hz6 Φ f s t x.out)
    (hsum' : Summable fun y : RowQ 𝔪 =>
      (Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6 s y.out * f (y.out.c : F) (y.out.d : F)) :
    ∑ t ∈ T, ∑' x : RowQ 𝔪, gU (π := π) P hG hz6 Φ f s t x.out
      = (Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 3
            * (cc ^ 3 * ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s)))
          * ∑' y : RowQ 𝔪, (Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6 s y.out
              * f (y.out.c : F) (y.out.d : F)
        + (1 - (Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 2
            * (cc ^ 3 * ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s))))
          * ∑' y : RowQ 𝔪,
              TSection.restrict v hv ((Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6) s y.out
                * f (y.out.c : F) (y.out.d : F) := by
  classical
  have hres : ∀ p : Row 𝔪,
      TSection.restrict v hv ((Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6) s p
        = (if π ∣ p.c then 0 else 1) * (Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6 s p := by
    intro p
    by_cases hc : π ∣ p.c
    · rw [TSection.restrict_apply_of_not_val hv _ s (fun h => (H.val_iff hv p.c).1 h hc),
        if_pos hc, zero_mul]
    · rw [TSection.restrict_apply_of_val hv _ s ((H.val_iff hv p.c).2 hc), if_neg hc, one_mul]
  have hsumR : Summable fun y : RowQ 𝔪 =>
      TSection.restrict v hv ((Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6) s y.out
        * f (y.out.c : F) (y.out.d : F) := by
    refine Summable.of_norm_bounded hsum'.norm fun y => ?_
    rw [hres]
    split_ifs
    · rw [zero_mul, zero_mul, norm_zero]; exact norm_nonneg _
    · rw [one_mul]
  rw [(prop54_omega P hG hz6 H Φ hT hdeep f s cc hfπ hfU hsum).2, ← tsum_mul_left, ← tsum_mul_left,
    ← (hsum'.mul_left _).tsum_add (hsumR.mul_left _)]
  refine tsum_congr fun y => ?_
  rw [hres]
  ring

end main

end ArtinKP.FA
end
end

theorem solution.{u_1} : type_of% @ArtinKP.FA.prop54_oai.{u_1} := @ArtinKP.FA.prop54_oai.{u_1}
