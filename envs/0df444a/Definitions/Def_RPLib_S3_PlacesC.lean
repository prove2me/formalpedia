-- Prove2me | Definitions.Def_RPLib_S3_PlacesC
-- name    : RPLib_S3_PlacesC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:21:34.065957+00:00
-- url     : https://prove2.me/theorems/95e3d6b2-0e72-4a55-8965-25ddd7c2b6e3
-- title:
--   Weight-two Ramanujan-Petersson library: Functions without poles are constants
-- statement:
--   Functions without poles are constants
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_PlacesB

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Polynomial IsDedekindDomain Module

namespace RamanujanPetersson.Places

/-! ## 8. Functions without poles are constants -/

section Valuation

variable {S : Type*} [CommRing S] [IsDedekindDomain S] {K : Type*} [Field K] [Algebra S K]
  [IsFractionRing S K]

theorem valuation_le_one_of_neg_log_nonneg (P : HeightOneSpectrum S) {f : K}
    (h : 0 ≤ -WithZero.log (P.valuation K f)) : P.valuation K f ≤ 1 := by
  by_cases hf : f = 0
  · simp [hf]
  have hv : P.valuation K f ≠ 0 := by simpa using hf
  rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem neg_log_nonneg_of_valuation_le_one (P : HeightOneSpectrum S) {f : K}
    (h : P.valuation K f ≤ 1) : 0 ≤ -WithZero.log (P.valuation K f) := by
  by_cases hf : f = 0
  · simp [hf]
  have hv : P.valuation K f ≠ 0 := by simpa using hf
  rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

theorem neg_log_nonneg_algebraMap (P : HeightOneSpectrum S) (a : S) :
    0 ≤ -WithZero.log (P.valuation K (algebraMap S K a)) :=
  neg_log_nonneg_of_valuation_le_one P (P.valuation_le_one a)

/-- The ultrametric inequality for `ord = -log v`. -/
theorem min_neg_log_le_neg_log_add (P : HeightOneSpectrum S) {f g : K} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) :
    min (-WithZero.log (P.valuation K f)) (-WithZero.log (P.valuation K g)) ≤
      -WithZero.log (P.valuation K (f + g)) := by
  have h := Valuation.map_add (P.valuation K) f g
  have hv1 : P.valuation K f ≠ 0 := by simpa using hf
  have hv2 : P.valuation K g ≠ 0 := by simpa using hg
  have hv3 : P.valuation K (f + g) ≠ 0 := by simpa using hfg
  rw [← WithZero.exp_log hv1, ← WithZero.exp_log hv2, ← WithZero.exp_log hv3, le_max_iff,
    WithZero.exp_le_exp, WithZero.exp_le_exp] at h
  rcases h with h | h
  · exact min_le_of_left_le (by omega)
  · exact min_le_of_right_le (by omega)

end Valuation

section NoPoles

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

theorem isIntegral_poly_of_ord_nonneg {f : F}
    (h : ∀ P : HeightOneSpectrum (Rfin Fq F), 0 ≤ ord P f) : IsIntegral Fq[X] f := by
  obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (K := F) f
    (fun P => valuation_le_one_of_neg_log_nonneg P (h P))
  exact a.2

theorem isIntegral_Oinf_of_ord_nonneg {f : F}
    (h : ∀ P : HeightOneSpectrum (Rinf Fq F), 0 ≤ ord P f) : IsIntegral (Oinf Fq) f := by
  obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (K := F) f
    (fun P => valuation_le_one_of_neg_log_nonneg P (h P))
  exact a.2

/-- A polynomial in `x` that is regular at `x = ∞` is a constant. -/
theorem mem_range_of_mem_Oinf {p : Fq[X]} (h : algebraMap Fq[X] (RatFunc Fq) p ∈ Oinf Fq) :
    algebraMap Fq[X] (RatFunc Fq) p ∈ Set.range (algebraMap Fq (RatFunc Fq)) := by
  by_cases hp : p = 0
  · exact ⟨0, by simp [hp]⟩
  have hne : algebraMap Fq[X] (RatFunc Fq) p ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))]
  have h2 := (mem_Oinf_iff' Fq hne).mp h
  rw [RatFunc.intDegree_polynomial] at h2
  have hdeg : p.natDegree = 0 := by omega
  refine ⟨p.coeff 0, ?_⟩
  rw [IsScalarTower.algebraMap_apply Fq Fq[X] (RatFunc Fq), Polynomial.algebraMap_eq,
    ← eq_C_of_natDegree_eq_zero hdeg]

/-- Integral over `Fq[x]` and over the valuation ring at `∞` implies integral over `Fq`. -/
theorem isIntegral_of_isIntegral_poly_Oinf {f : F} (h1 : IsIntegral Fq[X] f)
    (h2 : IsIntegral (Oinf Fq) f) : IsIntegral Fq f := by
  have e1 := minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc Fq) h1
  have e2 := minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc Fq) h2
  have hl : minpoly (RatFunc Fq) f ∈ lifts (algebraMap Fq (RatFunc Fq)) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    have hc2 : (minpoly (RatFunc Fq) f).coeff n ∈ Oinf Fq := by
      rw [e2, coeff_map]
      exact SetLike.coe_mem _
    rw [e1, coeff_map] at hc2 ⊢
    exact mem_range_of_mem_Oinf Fq hc2
  obtain ⟨q, hq, -, hmon⟩ := lifts_and_degree_eq_and_monic hl (minpoly.monic h1.tower_top)
  refine ⟨q, hmon, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap (RatFunc Fq), hq, minpoly.aeval]

/-- **A function without poles is a constant** (Riemann-Roch's `L(0) = k`). -/
theorem mem_constField_of_ord_nonneg {f : F} (h : ∀ P : Place Fq F, 0 ≤ P.ord f) :
    f ∈ constField Fq F :=
  mem_algebraicClosure_iff.mpr (isIntegral_of_isIntegral_poly_Oinf Fq F
    (isIntegral_poly_of_ord_nonneg Fq F fun P => h (Sum.inl P))
    (isIntegral_Oinf_of_ord_nonneg Fq F fun P => h (Sum.inr P))).isAlgebraic

/-- Constants have no poles. -/
theorem ord_nonneg_of_mem_constField {f : F} (hf : f ∈ constField Fq F) (P : Place Fq F) :
    0 ≤ P.ord f := by
  rcases P with P | P
  · show 0 ≤ -WithZero.log (P.valuation F f)
    exact neg_log_nonneg_algebraMap (K := F) P (constToRfin Fq F ⟨f, hf⟩)
  · show 0 ≤ -WithZero.log (P.valuation F f)
    exact neg_log_nonneg_algebraMap (K := F) P (constToRinf Fq F ⟨f, hf⟩)

theorem Place.ord_one (P : Place Fq F) : P.ord (1 : F) = 0 := by
  have h := P.ord_mul (one_ne_zero (α := F)) (one_ne_zero (α := F))
  rw [mul_one] at h
  omega

theorem Place.ord_add (P : Place Fq F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (P.ord f) (P.ord g) ≤ P.ord (f + g) := by
  rcases P with P | P
  exacts [min_neg_log_le_neg_log_add P hf hg hfg, min_neg_log_le_neg_log_add P hf hg hfg]

theorem Place.ord_neg (P : Place Fq F) (f : F) : P.ord (-f) = P.ord f := by
  rcases P with P | P
  · show -WithZero.log (P.valuation F (-f)) = -WithZero.log (P.valuation F f)
    rw [Valuation.map_neg]
  · show -WithZero.log (P.valuation F (-f)) = -WithZero.log (P.valuation F f)
    rw [Valuation.map_neg]

/-- Nonzero constants have neither zeros nor poles. -/
theorem ord_eq_zero_of_mem_constField {f : F} (hf : f ∈ constField Fq F) (hf0 : f ≠ 0)
    (P : Place Fq F) : P.ord f = 0 := by
  have h1 := ord_nonneg_of_mem_constField Fq F hf P
  have h2 := ord_nonneg_of_mem_constField Fq F (inv_mem hf) P
  have h3 : P.ord (f * f⁻¹) = P.ord f + P.ord f⁻¹ := P.ord_mul hf0 (inv_ne_zero hf0)
  rw [mul_inv_cancel₀ hf0, Place.ord_one] at h3
  omega

/-- Multiplying by a nonzero constant does not change orders. -/
theorem ord_const_mul {c f : F} (hc : c ∈ constField Fq F) (hc0 : c ≠ 0) (hf : f ≠ 0) (P : Place Fq F) :
    P.ord (c * f) = P.ord f := by
  rw [P.ord_mul hc0 hf, ord_eq_zero_of_mem_constField Fq F hc hc0, zero_add]

/-- `div f = 0` exactly for the nonzero constants. -/
theorem div_eq_zero_iff {f : F} (hf : f ≠ 0) :
    (div f : Divisor Fq F) = 0 ↔ f ∈ constField Fq F := by
  constructor
  · intro h
    apply mem_constField_of_ord_nonneg
    intro P
    have h' := congrArg (fun D : Divisor Fq F => D P) h
    simp only [div_apply, Finsupp.coe_zero, Pi.zero_apply] at h'
    omega
  · intro h
    ext P
    rw [div_apply, Finsupp.coe_zero, Pi.zero_apply, ord_eq_zero_of_mem_constField Fq F h hf P]

end NoPoles

/-! ## 9. Degree-one places of a constant field extension -/

section ConstantFieldExtension

/-- Degree-one places are the rational points: `#Hom_K(S, K) = #{P : deg P = 1}`. -/
theorem card_algHom_self_eq_card_deg_one (K : Type*) [Field K] [Fintype K] {S : Type*} [CommRing S]
    [IsDedekindDomain S] [Algebra K S] [FiniteQuot S] [Infinite S] :
    Nat.card (S →ₐ[K] K) = Nat.card {P : HeightOneSpectrum S // deg K P = 1} := by
  have hfr : finrank K K = 1 := Module.finrank_self K
  have hdeg : ∀ φ : S →ₐ[K] K, deg K (kerPlace K K φ) = 1 := by
    intro φ
    have := (kerPlace K K φ).isMaximal
    letI : Field (S ⧸ (kerPlace K K φ).asIdeal) := Ideal.Quotient.field _
    exact Nat.dvd_one.mp (hfr ▸ finrank_dvd_of_algHom_field K (fiberEquiv K K _ ⟨φ, rfl⟩))
  have hone : ∀ P : HeightOneSpectrum S, deg K P = 1 →
      Nat.card {φ : S →ₐ[K] K // kerPlace K K φ = P} = 1 := by
    intro P hP
    rw [card_fiber K K P, hP, hfr, if_pos (dvd_refl 1)]
  refine Nat.card_congr (Equiv.ofBijective (fun φ => ⟨kerPlace K K φ, hdeg φ⟩) ⟨?_, ?_⟩)
  · intro φ ψ h
    have h' : kerPlace K K ψ = kerPlace K K φ := (congrArg Subtype.val h).symm
    have := (Nat.card_eq_one_iff_unique.mp (hone _ (hdeg φ))).1
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨φ, rfl⟩ : {χ : S →ₐ[K] K // kerPlace K K χ = kerPlace K K φ}) ⟨ψ, h'⟩)
  · rintro ⟨P, hP⟩
    obtain ⟨⟨φ, hφ⟩⟩ := (Nat.card_eq_one_iff_unique.mp (hone P hP)).2
    exact ⟨φ, Subtype.ext hφ⟩

/-- Places of degree one after extending the constants from `Fq` to `L`: for an `L`-algebra `S'`
presented as `L ⊗[Fq] S`, they are counted by the `L`-valued points `#Hom_Fq(S, L)`. -/
theorem card_deg_one_baseChange (Fq : Type*) [Field Fq] (L : Type*) [Field L] [Fintype L]
    [Algebra Fq L] {S : Type*} [CommRing S] [Algebra Fq S]
    {S' : Type*} [CommRing S'] [IsDedekindDomain S'] [Algebra L S'] [FiniteQuot S'] [Infinite S']
    (e : TensorProduct Fq L S ≃ₐ[L] S') :
    Nat.card {P : HeightOneSpectrum S' // deg L P = 1} = Nat.card (S →ₐ[Fq] L) := by
  rw [← card_algHom_self_eq_card_deg_one L (S := S')]
  exact Nat.card_congr ((AlgEquiv.arrowCongr e AlgEquiv.refl).symm.trans (AlgHom.liftEquiv Fq L S L).symm)

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

theorem numPlaces_eq_card (d : ℕ) : numPlaces Fq F d = Nat.card {P : Place Fq F // P.deg = d} :=
  (Nat.card_eq_card_finite_toFinset (finite_place_deg_eq Fq F d)).symm

/-- `B_d` split into finite places and places over `x = ∞`. -/
theorem numPlaces_eq_card_add (d : ℕ) : numPlaces Fq F d =
    Nat.card {P : HeightOneSpectrum (Rfin Fq F) // deg Fq P = d} +
      Nat.card {P : HeightOneSpectrum (Rinf Fq F) // deg Fq P = d} := by
  rw [numPlaces_eq_card, Nat.card_congr Equiv.subtypeSum]
  exact @Nat.card_sum _ _ (finite_deg_eq_of Fq (fun N hN => X_pow_ne_self Fq F hN) d).to_subtype
    (finite_deg_eq_of Fq (fun N hN => piInf_pow_ne_self Fq F hN) d).to_subtype

variable (L : Type*) [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable (F' : Type*) [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']

/-- **Constant field extension**: if `F'` over `L` (of degree `m` over `Fq`) has its two rings of
places presented as `L ⊗[Fq] Rfin(F)` and `L ⊗[Fq] Rinf(F)` (the constant field extension
`F' = L ⊗[Fq] F` with the same `x`), then `B_1(F') = N_m(F)`. -/
theorem numPlaces_one_eq_numPoints
    (e1 : TensorProduct Fq L (Rfin Fq F) ≃ₐ[L] Rfin L F')
    (e2 : TensorProduct Fq L (Rinf Fq F) ≃ₐ[L] Rinf L F') :
    numPlaces L F' 1 = numPoints Fq F (finrank Fq L) := by
  rw [numPlaces_eq_card_add, numPoints_eq_card_algHom Fq F L, card_deg_one_baseChange Fq L e1,
    card_deg_one_baseChange Fq L e2]

/-- `B_1(F_m) = Σ_{d ∣ m} d B_d(F)` for the constant field extension `F_m` of degree `m`. -/
theorem numPlaces_one_eq_sum_divisors
    (e1 : TensorProduct Fq L (Rfin Fq F) ≃ₐ[L] Rfin L F')
    (e2 : TensorProduct Fq L (Rinf Fq F) ≃ₐ[L] Rinf L F') :
    numPlaces L F' 1 = ∑ d ∈ (finrank Fq L).divisors, d * numPlaces Fq F d := by
  have : Module.Finite Fq L := Module.Finite.of_finite
  rw [numPlaces_one_eq_numPoints Fq F L F' e1 e2,
    numPoints_eq_sum_divisors Fq F (Module.finrank_pos (R := Fq) (M := L)).ne']

end ConstantFieldExtension

end RamanujanPetersson.Places


