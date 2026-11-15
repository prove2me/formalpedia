-- Prove2me | Definitions.Def_RPLib_S3_PlacesB
-- name    : RPLib_S3_PlacesB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:20:05.61613+00:00
-- url     : https://prove2.me/theorems/551ac1c4-a437-441c-911e-eba8aa15d8f5
-- title:
--   Weight-two Ramanujan-Petersson library: Function fields over `Fq`: the two rings of places
-- statement:
--   Function fields over `Fq`: the two rings of places
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_PlacesA

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Polynomial IsDedekindDomain Module

namespace RamanujanPetersson.Places

/-! ## 4. Function fields over `Fq`: the two rings of places -/

section FunctionFieldSetup

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

instance isScalarTower_ratFunc : IsScalarTower Fq (RatFunc Fq) F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply Fq Fq[X] F, IsScalarTower.algebraMap_apply Fq[X] (RatFunc Fq) F,
      ← IsScalarTower.algebraMap_apply Fq Fq[X] (RatFunc Fq)]

instance isScalarTower_Oinf : IsScalarTower Fq (Oinf Fq) F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply (Oinf Fq) (RatFunc Fq) F]
    exact IsScalarTower.algebraMap_apply Fq (RatFunc Fq) F c

/-- The ring of functions regular away from `x = ∞` (finite places). -/
abbrev Rfin : Type _ := FunctionField.ringOfIntegers Fq F

/-- The ring of functions regular at all places over `x = ∞` (infinite places). -/
abbrev Rinf : Type _ := integralClosure (Oinf Fq) F

instance : IsDedekindDomain (Rinf Fq F) := integralClosure.isDedekindDomain (Oinf Fq) (RatFunc Fq) F

instance : IsFractionRing (Rinf Fq F) F := integralClosure.isFractionRing_of_finite_extension (RatFunc Fq) F

instance : Module.Finite (Oinf Fq) (Rinf Fq F) := IsIntegralClosure.finite (Oinf Fq) (RatFunc Fq) F _

instance : Module.Free (Oinf Fq) (Rinf Fq F) := IsIntegralClosure.module_free (Oinf Fq) (RatFunc Fq) F _

instance faithfulSMul_poly : FaithfulSMul Fq[X] F :=
  (faithfulSMul_iff_algebraMap_injective Fq[X] F).mpr (by
    rw [IsScalarTower.algebraMap_eq Fq[X] (RatFunc Fq) F]
    exact (algebraMap (RatFunc Fq) F).injective.comp (IsFractionRing.injective Fq[X] (RatFunc Fq)))

instance : Module.Free Fq[X] (Rfin Fq F) := IsIntegralClosure.module_free Fq[X] (RatFunc Fq) F _

instance : Module.Finite Fq[X] (Rfin Fq F) := IsIntegralClosure.finite Fq[X] (RatFunc Fq) F _

instance : Infinite (Rfin Fq F) :=
  Infinite.of_injective _ (FunctionField.ringOfIntegers.algebraMap_injective Fq F)

theorem algebraMap_Oinf_Rinf_injective : Function.Injective (algebraMap (Oinf Fq) (Rinf Fq F)) := by
  intro a b h
  have h2 : algebraMap (Oinf Fq) F a = algebraMap (Oinf Fq) F b := congrArg Subtype.val h
  rw [IsScalarTower.algebraMap_apply (Oinf Fq) (RatFunc Fq) F,
    IsScalarTower.algebraMap_apply (Oinf Fq) (RatFunc Fq) F b] at h2
  exact Subtype.ext ((algebraMap (RatFunc Fq) F).injective h2)

instance : Infinite (Rinf Fq F) := Infinite.of_injective _ (algebraMap_Oinf_Rinf_injective Fq F)

instance : FiniteQuot (Rfin Fq F) where
  finite a ha := by
    have hN : Algebra.norm Fq[X] a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
    apply Nat.finite_of_card_ne_zero
    rw [card_quot_eq_card_quot_norm (A := Fq[X]) a ha, card_polyQuot hN]
    exact pow_ne_zero _ Fintype.card_ne_zero

instance : FiniteQuot (Rinf Fq F) where
  finite a ha := by
    have hN : Algebra.norm (Oinf Fq) a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
    apply Nat.finite_of_card_ne_zero
    rw [card_quot_eq_card_quot_norm (A := Oinf Fq) a ha, card_quot_Oinf Fq hN]
    exact pow_ne_zero _ Fintype.card_ne_zero

/-! ### Norm bridge -/

theorem norm_bridge_fin (a : Rfin Fq F) :
    algebraMap Fq[X] (RatFunc Fq) (Algebra.norm Fq[X] a) =
      Algebra.norm (RatFunc Fq) (algebraMap (Rfin Fq F) F a) := by
  have := IsIntegralClosure.isLocalization Fq[X] (RatFunc Fq) F (Rfin Fq F)
  exact (Algebra.norm_localization Fq[X] (nonZeroDivisors Fq[X]) (Rₘ := RatFunc Fq) (Sₘ := F) a).symm

theorem norm_bridge_inf (c : Rinf Fq F) :
    ((Algebra.norm (Oinf Fq) c : Oinf Fq) : RatFunc Fq) =
      Algebra.norm (RatFunc Fq) (algebraMap (Rinf Fq F) F c) := by
  have := IsIntegralClosure.isLocalization (Oinf Fq) (RatFunc Fq) F (Rinf Fq F)
  exact (Algebra.norm_localization (Oinf Fq) (nonZeroDivisors (Oinf Fq)) (Rₘ := RatFunc Fq) (Sₘ := F) c).symm

theorem two_le_card : 2 ≤ Fintype.card Fq := Fintype.one_lt_card

/-- Finite part: `deg (div a)|_fin = deg_x N(a)`. -/
theorem degS_fin {a : Rfin Fq F} (ha : a ≠ 0) :
    degS Fq (divS (Rfin Fq F) (algebraMap (Rfin Fq F) F a)) =
      (Algebra.norm (RatFunc Fq) (algebraMap (Rfin Fq F) F a)).intDegree := by
  have hN : Algebra.norm Fq[X] a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
  have h1 := card_quot_eq_pow Fq (S := Rfin Fq F) ha
  rw [card_quot_eq_card_quot_norm (A := Fq[X]) a ha, card_polyQuot hN] at h1
  have h2 := Nat.pow_right_injective (two_le_card Fq) h1
  rw [degS_divS_algebraMap Fq ha, ← h2, ← norm_bridge_fin, RatFunc.intDegree_polynomial]

/-- Infinite part: `deg (div c)|_inf = -deg_x N(c)`. -/
theorem degS_inf {c : Rinf Fq F} (hc : c ≠ 0) :
    degS Fq (divS (Rinf Fq F) (algebraMap (Rinf Fq F) F c)) =
      -(Algebra.norm (RatFunc Fq) (algebraMap (Rinf Fq F) F c)).intDegree := by
  have hN : Algebra.norm (Oinf Fq) c ≠ 0 := Algebra.norm_ne_zero_iff.mpr hc
  have hN' : ((Algebra.norm (Oinf Fq) c : Oinf Fq) : RatFunc Fq) ≠ 0 := fun h => hN (Subtype.ext h)
  have h1 := card_quot_eq_pow Fq (S := Rinf Fq F) hc
  rw [card_quot_eq_card_quot_norm (A := Oinf Fq) c hc, card_quot_Oinf Fq hN] at h1
  have h2 := Nat.pow_right_injective (two_le_card Fq) h1
  have hle := (mem_Oinf_iff' Fq hN').mp (Algebra.norm (Oinf Fq) c).2
  rw [degS_divS_algebraMap Fq hc, ← h2, ← norm_bridge_inf]
  omega

/-- The product formula, split into the finite and the infinite places. -/
theorem degS_fin_add_degS_inf {f : F} (hf : f ≠ 0) :
    degS Fq (divS (Rfin Fq F) f) + degS Fq (divS (Rinf Fq F) f) = 0 := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (Rfin Fq F) f
  obtain ⟨c, d, hd, hcd⟩ := IsFractionRing.div_surjective (Rinf Fq F) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab; exact hf hab.symm
  have hc0 : c ≠ 0 := by rintro rfl; simp at hcd; exact hf hcd.symm
  have inj1 := IsFractionRing.injective (Rfin Fq F) F
  have inj2 := IsFractionRing.injective (Rinf Fq F) F
  have ha' : algebraMap (Rfin Fq F) F a ≠ 0 := (map_ne_zero_iff _ inj1).mpr ha0
  have hb' : algebraMap (Rfin Fq F) F b ≠ 0 := (map_ne_zero_iff _ inj1).mpr hb0
  have hc' : algebraMap (Rinf Fq F) F c ≠ 0 := (map_ne_zero_iff _ inj2).mpr hc0
  have hd' : algebraMap (Rinf Fq F) F d ≠ 0 := (map_ne_zero_iff _ inj2).mpr hd0
  have e1 : Algebra.norm (RatFunc Fq) f * Algebra.norm (RatFunc Fq) (algebraMap (Rfin Fq F) F b) =
      Algebra.norm (RatFunc Fq) (algebraMap (Rfin Fq F) F a) := by
    rw [← map_mul, ← hab, div_mul_cancel₀ _ hb']
  have e2 : Algebra.norm (RatFunc Fq) f * Algebra.norm (RatFunc Fq) (algebraMap (Rinf Fq F) F d) =
      Algebra.norm (RatFunc Fq) (algebraMap (Rinf Fq F) F c) := by
    rw [← map_mul, ← hcd, div_mul_cancel₀ _ hd']
  have nf : Algebra.norm (RatFunc Fq) f ≠ 0 := Algebra.norm_ne_zero_iff.mpr hf
  have nb : Algebra.norm (RatFunc Fq) (algebraMap (Rfin Fq F) F b) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hb'
  have nd : Algebra.norm (RatFunc Fq) (algebraMap (Rinf Fq F) F d) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hd'
  have i1 := congrArg RatFunc.intDegree e1
  have i2 := congrArg RatFunc.intDegree e2
  rw [RatFunc.intDegree_mul nf nb] at i1
  rw [RatFunc.intDegree_mul nf nd] at i2
  have p1 : degS Fq (divS (Rfin Fq F) f) =
      (Algebra.norm (RatFunc Fq) (algebraMap (Rfin Fq F) F a)).intDegree -
        (Algebra.norm (RatFunc Fq) (algebraMap (Rfin Fq F) F b)).intDegree := by
    rw [← hab, divS_div ha' hb', degS_sub, degS_fin Fq F ha0, degS_fin Fq F hb0]
  have p2 : degS Fq (divS (Rinf Fq F) f) =
      -(Algebra.norm (RatFunc Fq) (algebraMap (Rinf Fq F) F c)).intDegree +
        (Algebra.norm (RatFunc Fq) (algebraMap (Rinf Fq F) F d)).intDegree := by
    rw [← hcd, divS_div hc' hd', degS_sub, degS_inf Fq F hc0, degS_inf Fq F hd0]; ring
  rw [p1, p2]
  omega

end FunctionFieldSetup

/-! ## 5. Places, divisors, principal divisors -/

section Divisors

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- The places of `F` (relative to the chosen separating element `x`): the finite places
(`HeightOneSpectrum` of `Rfin`) and the places over `x = ∞` (`HeightOneSpectrum` of `Rinf`). -/
abbrev Place : Type _ := HeightOneSpectrum (Rfin Fq F) ⊕ HeightOneSpectrum (Rinf Fq F)

/-- Divisors: finitely supported `ℤ`-valued functions on places. -/
abbrev Divisor : Type _ := Place Fq F →₀ ℤ

variable {Fq F}

/-- The degree of a place over `Fq` (the `Fq`-dimension of its residue field). -/
def Place.deg : Place Fq F → ℕ :=
  Sum.elim (_root_.RamanujanPetersson.Places.deg Fq) (_root_.RamanujanPetersson.Places.deg Fq)

/-- The order of `f` at a place. -/
def Place.ord : Place Fq F → F → ℤ :=
  Sum.elim (fun P f => _root_.RamanujanPetersson.Places.ord P f)
    (fun P f => _root_.RamanujanPetersson.Places.ord P f)

@[simp] theorem Place.deg_inl (P : HeightOneSpectrum (Rfin Fq F)) :
    Place.deg (Sum.inl P : Place Fq F) = _root_.RamanujanPetersson.Places.deg Fq P := rfl
@[simp] theorem Place.deg_inr (P : HeightOneSpectrum (Rinf Fq F)) :
    Place.deg (Sum.inr P : Place Fq F) = _root_.RamanujanPetersson.Places.deg Fq P := rfl
@[simp] theorem Place.ord_inl (P : HeightOneSpectrum (Rfin Fq F)) (f : F) :
    Place.ord (Sum.inl P : Place Fq F) f = _root_.RamanujanPetersson.Places.ord P f := rfl
@[simp] theorem Place.ord_inr (P : HeightOneSpectrum (Rinf Fq F)) (f : F) :
    Place.ord (Sum.inr P : Place Fq F) f = _root_.RamanujanPetersson.Places.ord P f := rfl

theorem Place.deg_pos (P : Place Fq F) : 0 < P.deg := by
  rcases P with P | P
  exacts [_root_.RamanujanPetersson.Places.deg_pos Fq P, _root_.RamanujanPetersson.Places.deg_pos Fq P]

theorem Place.ord_mul (P : Place Fq F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    P.ord (f * g) = P.ord f + P.ord g := by
  rcases P with P | P
  exacts [_root_.RamanujanPetersson.Places.ord_mul P hf hg, _root_.RamanujanPetersson.Places.ord_mul P hf hg]

theorem Place.ord_div (P : Place Fq F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    P.ord (f / g) = P.ord f - P.ord g := by
  rcases P with P | P
  exacts [_root_.RamanujanPetersson.Places.ord_div P hf hg, _root_.RamanujanPetersson.Places.ord_div P hf hg]

/-- The degree of a divisor. -/
def Divisor.deg (D : Divisor Fq F) : ℤ := D.sum fun P n => n * (P.deg : ℤ)

theorem Divisor.deg_add (D E : Divisor Fq F) : Divisor.deg (D + E) = D.deg + E.deg := by
  unfold Divisor.deg
  rw [Finsupp.sum_add_index'] <;> intros <;> ring

theorem Divisor.deg_neg (D : Divisor Fq F) : Divisor.deg (-D) = -D.deg := by
  unfold Divisor.deg
  rw [Finsupp.sum_neg_index (fun _ => by ring), Finsupp.sum, Finsupp.sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem Divisor.deg_sub (D E : Divisor Fq F) : Divisor.deg (D - E) = D.deg - E.deg := by
  rw [sub_eq_add_neg, Divisor.deg_add, Divisor.deg_neg, sub_eq_add_neg]

theorem Divisor.deg_single (P : Place Fq F) (n : ℤ) : Divisor.deg (Finsupp.single P n : Divisor Fq F) = n * P.deg := by
  unfold Divisor.deg
  rw [Finsupp.sum_single_index (by ring)]

theorem Divisor.deg_sumElim (D : HeightOneSpectrum (Rfin Fq F) →₀ ℤ)
    (E : HeightOneSpectrum (Rinf Fq F) →₀ ℤ) :
    Divisor.deg (D.sumElim E : Divisor Fq F) = degS Fq D + degS Fq E := by
  unfold Divisor.deg
  rw [Finsupp.sum_sumElim]
  rfl

/-- The principal divisor of `f` (the zero divisor for `f = 0`). -/
def div (f : F) : Divisor Fq F := (divS (Rfin Fq F) f).sumElim (divS (Rinf Fq F) f)

@[simp] theorem div_apply (f : F) (P : Place Fq F) : div f P = P.ord f := by
  rcases P with P | P <;> rfl

theorem div_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) : (div (f * g) : Divisor Fq F) = div f + div g := by
  ext P
  simp only [div_apply, Finsupp.coe_add, Pi.add_apply, P.ord_mul hf hg]

theorem div_div {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) : (div (f / g) : Divisor Fq F) = div f - div g := by
  ext P
  simp only [div_apply, Finsupp.coe_sub, Pi.sub_apply, P.ord_div hf hg]

/-- **Product formula**: a nonzero function has as many zeros as poles, counted with degrees. -/
theorem deg_div {f : F} (hf : f ≠ 0) : Divisor.deg (div f : Divisor Fq F) = 0 := by
  rw [div, Divisor.deg_sumElim]
  exact degS_fin_add_degS_inf Fq F hf

end Divisors

/-! ## 6. The full constant field -/

section ConstantField

theorem moduleFinite_of_algHom (Fq : Type*) [Field Fq] {k S : Type*} [Field k] [Algebra Fq k]
    [CommRing S] [Algebra Fq S] (φ : k →ₐ[Fq] S) (P : Ideal S) [P.IsMaximal] [Finite (S ⧸ P)] :
    Module.Finite Fq k ∧ finrank Fq k ∣ finrank Fq (S ⧸ P) := by
  letI : Field (S ⧸ P) := Ideal.Quotient.field P
  let ψ : k →ₐ[Fq] S ⧸ P := (Ideal.Quotient.mkₐ Fq P).comp φ
  letI : Algebra k (S ⧸ P) := ψ.toRingHom.toAlgebra
  have : IsScalarTower Fq k (S ⧸ P) := IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm
  have : Module.Finite Fq (S ⧸ P) := Module.Finite.of_finite
  have : Module.Finite k (S ⧸ P) := Module.Finite.of_restrictScalars_finite Fq k (S ⧸ P)
  have : Module.Finite Fq k :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom Fq k (S ⧸ P)).toLinearMap
      (algebraMap k (S ⧸ P)).injective
  exact ⟨inferInstance, Dvd.intro _ (Module.finrank_mul_finrank Fq k (S ⧸ P))⟩

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- The full constant field of `F`: the algebraic closure of `Fq` in `F`. -/
abbrev constField : IntermediateField Fq F := algebraicClosure Fq F

theorem isIntegral_of_mem_constField (c : constField Fq F) : IsIntegral Fq (c : F) :=
  (mem_algebraicClosure_iff.mp c.2).isIntegral

/-- Constants are regular at the finite places. -/
def constToRfin : constField Fq F →ₐ[Fq] Rfin Fq F where
  toFun c := ⟨(c : F), (isIntegral_of_mem_constField Fq F c).tower_top⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Constants are regular at the infinite places. -/
def constToRinf : constField Fq F →ₐ[Fq] Rinf Fq F where
  toFun c := ⟨(c : F), (isIntegral_of_mem_constField Fq F c).tower_top⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem not_isField_Rinf : ¬ IsField (Rinf Fq F) := by
  rw [← Algebra.IsIntegral.isField_iff_isField (algebraMap_Oinf_Rinf_injective Fq F)]
  exact IsDiscreteValuationRing.not_isField _

/-- There is at least one place over `x = ∞`. -/
theorem nonempty_infPlace : Nonempty (HeightOneSpectrum (Rinf Fq F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Rinf Fq F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (not_isField_Rinf Fq F)⟩⟩

theorem finrank_constField_dvd (P : Place Fq F) : finrank Fq (constField Fq F) ∣ P.deg := by
  rcases P with P | P
  · haveI := P.isMaximal
    exact (moduleFinite_of_algHom Fq (constToRfin Fq F) P.asIdeal).2
  · haveI := P.isMaximal
    exact (moduleFinite_of_algHom Fq (constToRinf Fq F) P.asIdeal).2

instance finiteDimensional_constField : FiniteDimensional Fq (constField Fq F) := by
  obtain ⟨P⟩ := nonempty_infPlace Fq F
  have := P.isMaximal
  exact (moduleFinite_of_algHom Fq (constToRinf Fq F) P.asIdeal).1

/-- A place of degree one forces the full constant field to be `Fq`. -/
theorem constField_eq_bot_of_deg_one {P : Place Fq F} (h : P.deg = 1) : constField Fq F = ⊥ :=
  IntermediateField.finrank_eq_one_iff.mp (Nat.dvd_one.mp (h ▸ finrank_constField_dvd Fq F P))

end ConstantField

/-! ## 7. Places of bounded degree; points with values in finite extensions of `Fq` -/

section FiniteFields

variable (Fq : Type*) [Field Fq] [Fintype Fq]

theorem pow_card_pow_eq {K : Type*} [Field K] [Fintype K] (x : K) (k : ℕ) :
    x ^ (Fintype.card K ^ k) = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, FiniteField.pow_card]

/-- An `Fq`-embedding of fields divides the degrees. -/
theorem finrank_dvd_of_algHom_field {K L : Type*} [Field K] [Field L] [Algebra Fq K] [Algebra Fq L]
    [Module.Finite Fq L] (φ : K →ₐ[Fq] L) : finrank Fq K ∣ finrank Fq L := by
  letI : Algebra K L := φ.toRingHom.toAlgebra
  have : IsScalarTower Fq K L := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have : Module.Finite K L := Module.Finite.of_restrictScalars_finite Fq K L
  have : Module.Finite Fq K :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom Fq K L).toLinearMap (algebraMap K L).injective
  exact Dvd.intro _ (Module.finrank_mul_finrank Fq K L)

/-- A finite field of degree `d` over `Fq` has `d` embeddings into one of degree divisible by `d`. -/
theorem card_algHom_of_dvd {K L : Type*} [Field K] [Field L] [Algebra Fq K] [Algebra Fq L]
    [Finite K] [Finite L] (h : finrank Fq K ∣ finrank Fq L) : Nat.card (K →ₐ[Fq] L) = finrank Fq K := by
  have : Fintype K := Fintype.ofFinite K
  have : Fintype L := Fintype.ofFinite L
  have : Module.Finite Fq K := Module.Finite.of_finite
  obtain ⟨k, hk⟩ := h
  have hcard : Fintype.card L = Fintype.card K ^ k := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := Fq) (V := L), Module.natCard_eq_pow_finrank (K := Fq) (V := K), hk,
      pow_mul]
  have hL1 : 1 < Fintype.card L := Fintype.one_lt_card
  have hsplit : (X ^ Fintype.card L - X : L[X]).Splits := by
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X, FiniteField.X_pow_card_sub_X_natDegree_eq L hL1]
    exact Finset.card_univ
  have hspl : ∀ x : K, (map (algebraMap Fq L) (minpoly Fq x)).Splits := by
    intro x
    apply Splits.of_dvd hsplit (FiniteField.X_pow_card_sub_X_ne_zero L hL1)
    have hd : minpoly Fq x ∣ (X ^ Fintype.card L - X : Fq[X]) := by
      apply minpoly.dvd
      rw [map_sub, map_pow, aeval_X, hcard, pow_card_pow_eq, sub_self]
    simpa using Polynomial.map_dvd (algebraMap Fq L) hd
  rw [← AlgHom.card_of_splits Fq K L hspl]
  exact Nat.card_eq_fintype_card

theorem card_algHom_eq_zero {K L : Type*} [Field K] [Field L] [Algebra Fq K] [Algebra Fq L]
    [Module.Finite Fq L] (h : ¬ finrank Fq K ∣ finrank Fq L) : Nat.card (K →ₐ[Fq] L) = 0 := by
  rw [Nat.card_eq_zero]
  exact Or.inl ⟨fun φ => h (finrank_dvd_of_algHom_field Fq φ)⟩

theorem finite_algHom {A B : Type*} [Ring A] [Ring B] [Algebra Fq A] [Algebra Fq B] [Finite A] [Finite B] :
    Finite (A →ₐ[Fq] B) :=
  Finite.of_injective _ DFunLike.coe_injective

end FiniteFields

section PointCount

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra Fq S] [FiniteQuot S]

/-- Places of a fixed degree are finite in number, as soon as some `t ∈ S` is not a root of any
`T ^ N - T` (`N ≥ 2`): a place of degree `d` contains `t ^ (q ^ d) - t`. -/
theorem finite_deg_eq_of {t : S} (ht : ∀ N : ℕ, 2 ≤ N → t ^ N ≠ t) (d : ℕ) :
    {P : HeightOneSpectrum S | deg Fq P = d}.Finite := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · convert Set.finite_empty
    ext P
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => (deg_pos Fq P).ne' (h.trans hd)
  set N := Fintype.card Fq ^ d with hNdef
  have hq : 2 ≤ Fintype.card Fq := Fintype.one_lt_card
  have hN : 2 ≤ N := hq.trans (Nat.le_self_pow hd.ne' _)
  have h0 : t ^ N - t ≠ 0 := sub_ne_zero.mpr (ht N hN)
  have hI : Ideal.span {t ^ N - t} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  refine (Ideal.finite_factors hI).subset fun P hP => ?_
  simp only [Set.mem_ofPred_eq] at hP ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow,
    sub_eq_zero]
  have := P.isMaximal
  letI : Field (S ⧸ P.asIdeal) := Ideal.Quotient.field _
  letI : Fintype (S ⧸ P.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card (S ⧸ P.asIdeal) = N := by
    rw [← Nat.card_eq_fintype_card, card_residue_eq Fq P, hP]
  rw [← hc]
  exact FiniteField.pow_card _

theorem finite_deg_dvd_of {t : S} (ht : ∀ N : ℕ, 2 ≤ N → t ^ N ≠ t) {m : ℕ} (hm : m ≠ 0) :
    {P : HeightOneSpectrum S | deg Fq P ∣ m}.Finite :=
  (m.divisors.finite_toSet.biUnion fun d _ => finite_deg_eq_of Fq ht d).subset fun P hP =>
    Set.mem_biUnion (Nat.mem_divisors.mpr ⟨hP, hm⟩) rfl

variable [Infinite S] (L : Type*) [Field L] [Algebra Fq L] [Finite L]

theorem ker_ne_bot (φ : S →ₐ[Fq] L) : RingHom.ker φ ≠ ⊥ := by
  intro h
  have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).mpr h
  have := Finite.of_injective φ hinj
  exact _root_.not_finite S

/-- The place cut out by an `L`-valued point. -/
def kerPlace (φ : S →ₐ[Fq] L) : HeightOneSpectrum S :=
  ⟨RingHom.ker φ, RingHom.ker_isPrime φ, ker_ne_bot Fq L φ⟩

/-- The `L`-valued points with kernel `P` are the `Fq`-embeddings of the residue field at `P`. -/
def fiberEquiv (P : HeightOneSpectrum S) :
    {φ : S →ₐ[Fq] L // kerPlace Fq L φ = P} ≃ (S ⧸ P.asIdeal →ₐ[Fq] L) where
  toFun φ := Ideal.Quotient.liftₐ P.asIdeal φ.1 (fun a ha => by
    rw [← φ.2] at ha
    exact RingHom.mem_ker.mp ha)
  invFun ψ := ⟨ψ.comp (Ideal.Quotient.mkₐ Fq P.asIdeal), by
    have := P.isMaximal
    letI : Field (S ⧸ P.asIdeal) := Ideal.Quotient.field _
    have hinj : Function.Injective ψ := ψ.toRingHom.injective
    apply HeightOneSpectrum.ext
    ext a
    change a ∈ RingHom.ker (ψ.comp (Ideal.Quotient.mkₐ Fq P.asIdeal)) ↔ a ∈ P.asIdeal
    rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, map_eq_zero_iff ψ hinj,
      Ideal.Quotient.eq_zero_iff_mem]⟩
  left_inv φ := Subtype.ext (AlgHom.ext fun _ => rfl)
  right_inv ψ := Ideal.Quotient.algHom_ext Fq (AlgHom.ext fun _ => rfl)

theorem card_fiber (P : HeightOneSpectrum S) :
    Nat.card {φ : S →ₐ[Fq] L // kerPlace Fq L φ = P} =
      if deg Fq P ∣ finrank Fq L then deg Fq P else 0 := by
  rw [Nat.card_congr (fiberEquiv Fq L P)]
  have := P.isMaximal
  letI : Field (S ⧸ P.asIdeal) := Ideal.Quotient.field _
  have : Module.Finite Fq L := Module.Finite.of_finite
  split_ifs with h
  · exact card_algHom_of_dvd Fq h
  · exact card_algHom_eq_zero Fq h

/-- **Point count**: `#Hom_Fq(S, L) = Σ_{deg P ∣ [L : Fq]} deg P`, for any finite set `T` of places
containing all places of degree dividing `[L : Fq]`. -/
theorem card_algHom_eq_sum {T : Finset (HeightOneSpectrum S)}
    (hT : ∀ P, deg Fq P ∣ finrank Fq L → P ∈ T) :
    Nat.card (S →ₐ[Fq] L) = ∑ P ∈ T with deg Fq P ∣ finrank Fq L, deg Fq P := by
  classical
  have : Module.Finite Fq L := Module.Finite.of_finite
  have hmem : ∀ φ : S →ₐ[Fq] L, kerPlace Fq L φ ∈ T := fun φ => hT _ (by
    have := (kerPlace Fq L φ).isMaximal
    letI : Field (S ⧸ (kerPlace Fq L φ).asIdeal) := Ideal.Quotient.field _
    exact finrank_dvd_of_algHom_field Fq (fiberEquiv Fq L _ ⟨φ, rfl⟩))
  have hfib : ∀ P : HeightOneSpectrum S, {φ : S →ₐ[Fq] L | kerPlace Fq L φ = P}.Finite := fun P => by
    have : Finite (S ⧸ P.asIdeal →ₐ[Fq] L) := finite_algHom Fq
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (fiberEquiv Fq L P).symm)
  have hfin : Finite (S →ₐ[Fq] L) :=
    Set.finite_univ_iff.mp ((T.finite_toSet.biUnion fun P _ => hfib P).subset fun φ _ =>
      Set.mem_biUnion (hmem φ) rfl)
  have := Fintype.ofFinite (S →ₐ[Fq] L)
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ,
    Finset.card_eq_sum_card_fiberwise (f := kerPlace Fq L) (t := T) (fun φ _ => hmem φ), Finset.sum_filter]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [← card_fiber Fq L P, Nat.card_eq_fintype_card, Fintype.card_subtype]

end PointCount

section FunctionFieldCount

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

theorem X_pow_ne_self {N : ℕ} (hN : 2 ≤ N) :
    (algebraMap Fq[X] (Rfin Fq F) X) ^ N ≠ algebraMap Fq[X] (Rfin Fq F) X := by
  rw [← map_pow, Ne, (FunctionField.ringOfIntegers.algebraMap_injective Fq F).eq_iff]
  intro h
  have := congrArg natDegree h
  rw [natDegree_X_pow, natDegree_X] at this
  omega

theorem piInf_pow_ne_self {N : ℕ} (hN : 2 ≤ N) :
    (algebraMap (Oinf Fq) (Rinf Fq F) (piInf Fq)) ^ N ≠ algebraMap (Oinf Fq) (Rinf Fq F) (piInf Fq) := by
  rw [← map_pow, Ne, (algebraMap_Oinf_Rinf_injective Fq F).eq_iff]
  intro h
  have h2 := congrArg (fun z : Oinf Fq => RatFunc.intDegree (z : RatFunc Fq)) h
  simp only [SubmonoidClass.coe_pow, coe_piInf, one_div, inv_pow] at h2
  rw [RatFunc.intDegree_inv, RatFunc.intDegree_inv, ← RatFunc.algebraMap_X, ← map_pow,
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, natDegree_X_pow, natDegree_X] at h2
  omega

theorem finite_place_deg_eq (d : ℕ) : {P : Place Fq F | P.deg = d}.Finite := by
  have h1 := finite_deg_eq_of Fq (fun N hN => X_pow_ne_self Fq F hN) d
  have h2 := finite_deg_eq_of Fq (fun N hN => piInf_pow_ne_self Fq F hN) d
  refine ((h1.image Sum.inl).union (h2.image Sum.inr)).subset ?_
  rintro (P | P) hP
  · exact Or.inl ⟨P, hP, rfl⟩
  · exact Or.inr ⟨P, hP, rfl⟩

theorem finite_place_deg_dvd {m : ℕ} (hm : m ≠ 0) : {P : Place Fq F | P.deg ∣ m}.Finite :=
  (m.divisors.finite_toSet.biUnion fun d _ => finite_place_deg_eq Fq F d).subset fun P hP =>
    Set.mem_biUnion (Nat.mem_divisors.mpr ⟨hP, hm⟩) rfl

/-- `B_d`: the number of places of `F` of degree `d`. -/
def numPlaces (d : ℕ) : ℕ := (finite_place_deg_eq Fq F d).toFinset.card

/-- `N_m = Σ_{deg P ∣ m} deg P` (`0` for `m = 0`). -/
def numPoints (m : ℕ) : ℕ :=
  if hm : m = 0 then 0 else ∑ P ∈ (finite_place_deg_dvd Fq F hm).toFinset, P.deg

/-- `N_m = Σ_{d ∣ m} d B_d`. -/
theorem numPoints_eq_sum_divisors {m : ℕ} (hm : m ≠ 0) :
    numPoints Fq F m = ∑ d ∈ m.divisors, d * numPlaces Fq F d := by
  classical
  rw [numPoints, dif_neg hm, ← Finset.sum_fiberwise_of_maps_to (g := Place.deg) (t := m.divisors)
    (fun P hP => Nat.mem_divisors.mpr ⟨by simpa using hP, hm⟩)]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.sum_congr rfl (fun P hP => (Finset.mem_filter.mp hP).2), Finset.sum_const, smul_eq_mul, mul_comm,
    numPlaces]
  congr 2
  ext P
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ Nat.dvd_of_mem_divisors hd, h⟩⟩

variable (L : Type*) [Field L] [Algebra Fq L] [Finite L]

/-- Affine points: `#Hom_Fq(Rfin, L) = Σ_{finite P, deg P ∣ [L:Fq]} deg P`. -/
theorem card_algHom_Rfin :
    Nat.card (Rfin Fq F →ₐ[Fq] L) = ∑ P ∈ (finite_deg_dvd_of Fq (fun N hN => X_pow_ne_self Fq F hN)
      (Module.finrank_pos (R := Fq) (M := L)).ne').toFinset, deg Fq P := by
  have : Module.Finite Fq L := Module.Finite.of_finite
  rw [card_algHom_eq_sum Fq L (T := (finite_deg_dvd_of Fq (fun N hN => X_pow_ne_self Fq F hN)
    (Module.finrank_pos (R := Fq) (M := L)).ne').toFinset) (fun P hP => (Set.Finite.mem_toFinset _).mpr hP)]
  congr 1
  exact Finset.filter_true_of_mem fun P hP => by simpa using hP

theorem card_algHom_Rinf :
    Nat.card (Rinf Fq F →ₐ[Fq] L) = ∑ P ∈ (finite_deg_dvd_of Fq (fun N hN => piInf_pow_ne_self Fq F hN)
      (Module.finrank_pos (R := Fq) (M := L)).ne').toFinset, deg Fq P := by
  have : Module.Finite Fq L := Module.Finite.of_finite
  rw [card_algHom_eq_sum Fq L (T := (finite_deg_dvd_of Fq (fun N hN => piInf_pow_ne_self Fq F hN)
    (Module.finrank_pos (R := Fq) (M := L)).ne').toFinset) (fun P hP => (Set.Finite.mem_toFinset _).mpr hP)]
  congr 1
  exact Finset.filter_true_of_mem fun P hP => by simpa using hP

/-- `N_m = #Hom_Fq(Rfin, L) + #Hom_Fq(Rinf, L)` for `L` of degree `m` over `Fq`. -/
theorem numPoints_eq_card_algHom :
    numPoints Fq F (finrank Fq L) = Nat.card (Rfin Fq F →ₐ[Fq] L) + Nat.card (Rinf Fq F →ₐ[Fq] L) := by
  classical
  have : Module.Finite Fq L := Module.Finite.of_finite
  have hm : finrank Fq L ≠ 0 := (Module.finrank_pos (R := Fq) (M := L)).ne'
  rw [card_algHom_Rfin, card_algHom_Rinf, numPoints, dif_neg hm]
  have hsplit : (finite_place_deg_dvd Fq F hm).toFinset =
      ((finite_deg_dvd_of Fq (fun N hN => X_pow_ne_self Fq F hN) hm).toFinset.map Function.Embedding.inl).disjUnion
      ((finite_deg_dvd_of Fq (fun N hN => piInf_pow_ne_self Fq F hN) hm).toFinset.map Function.Embedding.inr)
      (by
        rw [Finset.disjoint_left]
        rintro _ h1 h2
        obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp h1
        obtain ⟨b, -, hb⟩ := Finset.mem_map.mp h2
        exact Sum.inr_ne_inl hb) := by
    ext P
    rcases P with P | P <;> simp
  rw [hsplit, Finset.sum_disjUnion, Finset.sum_map, Finset.sum_map]
  rfl

end FunctionFieldCount

end RamanujanPetersson.Places


