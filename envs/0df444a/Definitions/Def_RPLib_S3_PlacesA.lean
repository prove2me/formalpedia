-- Prove2me | Definitions.Def_RPLib_S3_PlacesA
-- name    : RPLib_S3_PlacesA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:17:31.072668+00:00
-- url     : https://prove2.me/theorems/2d2e79d6-14ca-42fb-8d66-4ba98eb13eba
-- title:
--   Places of function fields over $\mathbb{F}_q$: residue cardinalities, the place at infinity, orders
-- statement:
--   Cardinality of quotients of Dedekind domains via norms, the valuation ring at infinity of $\mathbb{F}_q(x)$ with uniformizer $1/x$ and residue field $\mathbb{F}_q$, and for a Dedekind domain with finite residue rings the degree of a place and the order function $\mathrm{ord}_P$ on its fraction field.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Rosen, Number Theory in Function Fields, GTM 210, Springer 2002, doi:10.1007/978-1-4757-6046-0, Chapters 1 and 5

import Mathlib

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Polynomial IsDedekindDomain Module

namespace RamanujanPetersson.Places

/-! ## 1. Cardinality of quotients of Dedekind domains and of free modules over PIDs -/

section CardQuot

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Infinite S]

/-- `I ↦ Nat.card (S ⧸ I)` is multiplicative on an infinite Dedekind domain. -/
theorem cardQuot_mul' (I J : Ideal S) :
    Submodule.cardQuot (I * J) = Submodule.cardQuot I * Submodule.cardQuot J :=
  UniqueFactorizationMonoid.multiplicative_of_coprime Submodule.cardQuot I J
    (Submodule.cardQuot_bot _ _)
    (fun {I J} hI => by simp [Ideal.isUnit_iff.mp hI, Ideal.mul_top])
    (fun {I} i hI =>
      have : Ideal.IsPrime I := Ideal.isPrime_of_prime hI
      cardQuot_pow_of_prime hI.ne_zero)
    fun {I J} hIJ => cardQuot_mul_of_coprime <| Ideal.isCoprime_iff_sup_eq.mpr
      (Ideal.isUnit_iff.mp
        (hIJ (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)))

variable (S) in
/-- The cardinality of the quotient, as a monoid-with-zero hom on ideals. -/
def cardHom : Ideal S →*₀ ℕ where
  toFun := Submodule.cardQuot
  map_mul' I J := cardQuot_mul' I J
  map_one' := by rw [Ideal.one_eq_top, Submodule.cardQuot_top]
  map_zero' := by rw [Ideal.zero_eq_bot, Submodule.cardQuot_bot]

theorem cardHom_apply (I : Ideal S) : cardHom S I = Nat.card (S ⧸ I) :=
  Submodule.cardQuot_apply I

end CardQuot

section NormCard

variable {A : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [Infinite A]
variable {S : Type*} [CommRing S] [IsDomain S] [Algebra A S] [Module.Free A S] [Module.Finite A S]

/-- For `S` free of finite rank over a PID `A`: `#(S ⧸ a) = #(A ⧸ N(a))`. -/
theorem card_quot_eq_card_quot_norm (a : S) (ha : a ≠ 0) :
    Nat.card (S ⧸ Ideal.span {a}) = Nat.card (A ⧸ Ideal.span {Algebra.norm A a}) := by
  classical
  set N : Submodule A S := (Ideal.span {a}).restrictScalars A with hN
  have hmem : ∀ x : S, a * x ∈ N := fun x =>
    Ideal.mul_mem_right x _ (Ideal.mem_span_singleton_self a)
  let e0 : S →ₗ[A] N :=
    { toFun := fun x => ⟨a * x, hmem x⟩
      map_add' := fun x y => by ext; simp [mul_add]
      map_smul' := fun c x => by ext; simp }
  have e0bij : Function.Bijective e0 := by
    constructor
    · intro x y hxy
      have : a * x = a * y := congrArg Subtype.val hxy
      exact mul_left_cancel₀ ha this
    · rintro ⟨z, hz⟩
      obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      exact ⟨x, by ext; simp [e0, mul_comm]⟩
  let e : S ≃ₗ[A] N := LinearEquiv.ofBijective e0 e0bij
  have hdet : LinearMap.det (N.subtype ∘ₗ (e : S →ₗ[A] N)) = Algebra.norm A a := by
    rw [Algebra.norm_apply]
    congr 1
  let b := Module.Free.chooseBasis A S
  have h : Module.finrank A N = Module.finrank A S := e.symm.finrank_eq
  let c := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : S ≃ₗ[A] N := b'.equiv ab (Equiv.refl _)
  let f : S →ₗ[A] S := N.subtype.comp (e' : S →ₗ[A] N)
  have hf : ∀ i, f (b' i) = c i • b' i := by
    intro i
    show ((b'.equiv ab (Equiv.refl _)) (b' i) : S) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdetf : LinearMap.det f = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, hf, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hassoc : Associated (Algebra.norm A a) (∏ i, c i) := by
    rw [← hdet, ← hdetf]
    exact LinearMap.associated_det_comp_equiv _ _ _
  calc Nat.card (S ⧸ Ideal.span {a}) = Nat.card (S ⧸ N) :=
        Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {a})).toEquiv.symm
    _ = Nat.card (Π i, A ⧸ Ideal.span ({c i} : Set A)) :=
        Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv
    _ = ∏ i, Nat.card (A ⧸ Ideal.span ({c i} : Set A)) := Nat.card_pi
    _ = ∏ i, cardHom A (Ideal.span ({c i} : Set A)) := by simp only [cardHom_apply]
    _ = cardHom A (Ideal.span ({∏ i, c i} : Set A)) := by
        rw [← Ideal.prod_span_singleton, map_prod]
    _ = Nat.card (A ⧸ Ideal.span {Algebra.norm A a}) := by
        rw [cardHom_apply, Ideal.span_singleton_eq_span_singleton.mpr hassoc.symm]

end NormCard

section PolyCard

variable {Fq : Type*} [Field Fq] [Fintype Fq]

theorem card_polyQuot {g : Fq[X]} (hg : g ≠ 0) :
    Nat.card (Fq[X] ⧸ Ideal.span {g}) = Fintype.card Fq ^ g.natDegree := by
  let pb := AdjoinRoot.powerBasis hg
  have : Module.Finite Fq (AdjoinRoot g) := pb.finite
  have h1 := Module.natCard_eq_pow_finrank (K := Fq) (V := AdjoinRoot g)
  rw [pb.finrank, AdjoinRoot.powerBasis_dim, Nat.card_eq_fintype_card (α := Fq)] at h1
  exact h1

end PolyCard

/-! ## 2. The valuation ring at infinity of `Fq(x)` -/

section Oinf

variable (Fq : Type*) [Field Fq] [DecidableEq (RatFunc Fq)]

/-- The valuation ring of `Fq(x)` at `x = ∞`: `{f : deg num f ≤ deg den f}`. -/
abbrev Oinf : ValuationSubring (RatFunc Fq) := (RatFunc.inftyValuation Fq).valuationSubring

theorem mem_Oinf_iff (f : RatFunc Fq) : f ∈ Oinf Fq ↔ RatFunc.inftyValuation Fq f ≤ 1 :=
  Valuation.mem_valuationSubring_iff _ _

theorem inftyValuation_eq_exp {f : RatFunc Fq} (hf : f ≠ 0) :
    RatFunc.inftyValuation Fq f = WithZero.exp f.intDegree := by
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero Fq hf]

theorem mem_Oinf_iff' {f : RatFunc Fq} (hf : f ≠ 0) : f ∈ Oinf Fq ↔ f.intDegree ≤ 0 := by
  rw [mem_Oinf_iff, inftyValuation_eq_exp Fq hf, ← WithZero.exp_zero, WithZero.exp_le_exp]

theorem algebraMap_mem_Oinf (c : Fq) : algebraMap Fq (RatFunc Fq) c ∈ Oinf Fq := by
  rw [mem_Oinf_iff]
  by_cases hc : c = 0
  · simp [hc]
  · rw [RatFunc.algebraMap_eq_C, RatFunc.inftyValuation.C Fq hc]

instance : Algebra Fq (Oinf Fq) :=
  RingHom.toAlgebra ((algebraMap Fq (RatFunc Fq)).codRestrict (Oinf Fq) (algebraMap_mem_Oinf Fq))

@[simp] theorem coe_algebraMap_Oinf (c : Fq) :
    ((algebraMap Fq (Oinf Fq) c : Oinf Fq) : RatFunc Fq) = algebraMap Fq (RatFunc Fq) c := rfl

instance : IsScalarTower Fq (Oinf Fq) (RatFunc Fq) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The uniformizer `1/x` of `Oinf`. -/
def piInf : Oinf Fq := ⟨1 / RatFunc.X, by
  rw [mem_Oinf_iff, RatFunc.inftyValuation.X_inv, ← WithZero.exp_zero, WithZero.exp_le_exp]
  norm_num⟩

@[simp] theorem coe_piInf : ((piInf Fq : Oinf Fq) : RatFunc Fq) = 1 / RatFunc.X := rfl

theorem X_ne_zero' : (RatFunc.X : RatFunc Fq) ≠ 0 := RatFunc.X_ne_zero

theorem intDegree_div_polys {p d : Fq[X]} (hp : p ≠ 0) (hd : d ≠ 0) :
    RatFunc.intDegree (algebraMap Fq[X] (RatFunc Fq) p / algebraMap Fq[X] (RatFunc Fq) d) =
      (p.natDegree : ℤ) - d.natDegree := by
  have hp' : algebraMap Fq[X] (RatFunc Fq) p ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))).mpr hp
  have hd' : (algebraMap Fq[X] (RatFunc Fq) d)⁻¹ ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))).mpr hd
  rw [div_eq_mul_inv, RatFunc.intDegree_mul hp' hd', RatFunc.intDegree_inv,
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, sub_eq_add_neg]

theorem mem_span_piInf_iff (z : Oinf Fq) :
    z ∈ Ideal.span {piInf Fq} ↔ (z : RatFunc Fq) = 0 ∨ RatFunc.intDegree (z : RatFunc Fq) < 0 := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨w, rfl⟩
    by_cases hw : (w : RatFunc Fq) = 0
    · left; simp [hw]
    · right
      have hw' := (mem_Oinf_iff' Fq hw).mp w.2
      simp only [MulMemClass.coe_mul, coe_piInf]
      rw [RatFunc.intDegree_mul hw (by simpa using X_ne_zero' Fq), one_div, RatFunc.intDegree_inv,
        RatFunc.intDegree_X]
      omega
  · rintro (h | h)
    · exact ⟨0, by ext; simp [h]⟩
    · have hz : (z : RatFunc Fq) ≠ 0 := fun h0 => by simp [h0] at h
      have hzX : (z : RatFunc Fq) * RatFunc.X ∈ Oinf Fq := by
        rw [mem_Oinf_iff' Fq (mul_ne_zero hz (X_ne_zero' Fq)),
          RatFunc.intDegree_mul hz (X_ne_zero' Fq), RatFunc.intDegree_X]
        omega
      refine ⟨⟨_, hzX⟩, ?_⟩
      ext
      simp only [MulMemClass.coe_mul, coe_piInf]
      field_simp [X_ne_zero' Fq]

theorem algebraMap_mem_span_piInf_iff (c : Fq) :
    algebraMap Fq (Oinf Fq) c ∈ Ideal.span {piInf Fq} ↔ c = 0 := by
  rw [mem_span_piInf_iff]
  constructor
  · rintro (h | h)
    · simpa using h
    · rw [coe_algebraMap_Oinf, RatFunc.algebraMap_eq_C, RatFunc.intDegree_C] at h
      exact absurd h (lt_irrefl 0)
  · rintro rfl; left; simp

theorem exists_sub_mem_span_piInf (z : Oinf Fq) :
    ∃ c : Fq, z - algebraMap Fq (Oinf Fq) c ∈ Ideal.span {piInf Fq} := by
  set f : RatFunc Fq := (z : RatFunc Fq) with hfz
  by_cases hf : f = 0
  · exact ⟨0, by rw [map_zero, sub_zero, mem_span_piInf_iff]; left; exact hf⟩
  have hdeg := (mem_Oinf_iff' Fq hf).mp z.2
  have hle : f.num.natDegree ≤ f.denom.natDegree := by
    have : f.intDegree = (f.num.natDegree : ℤ) - f.denom.natDegree := rfl
    omega
  set d := f.denom.natDegree
  set c := f.num.coeff d
  refine ⟨c, ?_⟩
  rw [mem_span_piInf_iff]
  set p : Fq[X] := f.num - C c * f.denom with hp
  have hden0 : f.denom ≠ 0 := f.denom_ne_zero
  have hrepr : ((z - algebraMap Fq (Oinf Fq) c : Oinf Fq) : RatFunc Fq) =
      algebraMap Fq[X] (RatFunc Fq) p / algebraMap Fq[X] (RatFunc Fq) f.denom := by
    have hden' : algebraMap Fq[X] (RatFunc Fq) f.denom ≠ 0 := by
      simpa using (map_ne_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))).mpr hden0
    rw [hp, map_sub, map_mul, sub_div, mul_div_assoc, div_self hden', mul_one, RatFunc.num_div_denom]
    simp [f, RatFunc.algebraMap_eq_C, RatFunc.algebraMap_C]
  rw [hrepr]
  by_cases hp0 : p = 0
  · left; simp [hp0]
  right
  rw [intDegree_div_polys Fq hp0 hden0]
  have hmon : f.denom.Monic := f.monic_denom
  have hlt : p.natDegree < d := by
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · exfalso; apply hp0
      have h1 : f.denom = 1 := Polynomial.eq_one_of_monic_natDegree_zero hmon hd0
      have h2 : f.num = C c := by
        rw [Polynomial.eq_C_of_natDegree_le_zero (by omega : f.num.natDegree ≤ 0)]
        simp [c, hd0]
      rw [hp, h1, h2, mul_one, sub_self]
    · rw [Polynomial.natDegree_lt_iff_degree_lt hp0, Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      rw [hp, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      rcases eq_or_lt_of_le hm with h | h
      · subst h; rw [hmon.coeff_natDegree]; simp [c, d]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        simp
  omega

/-- The residue map `Fq → Oinf ⧸ (1/x)` is a bijection. -/
theorem residue_bijective :
    Function.Bijective ((Ideal.Quotient.mk (Ideal.span {piInf Fq})).comp (algebraMap Fq (Oinf Fq))) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hc
    exact (algebraMap_mem_span_piInf_iff Fq c).mp hc
  · intro w
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨c, hc⟩ := exists_sub_mem_span_piInf Fq z
    exact ⟨c, by rw [RingHom.comp_apply, Ideal.Quotient.eq]; rw [← neg_mem_iff, neg_sub]; exact hc⟩

theorem piInf_ne_zero : piInf Fq ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  simp [X_ne_zero' Fq] at this

theorem span_piInf_isMaximal : (Ideal.span {piInf Fq}).IsMaximal := by
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact (RingEquiv.ofBijective _ (residue_bijective Fq)).symm.toMulEquiv.isField (Field.toIsField Fq)

instance : Infinite (Oinf Fq) := by
  by_contra h
  rw [not_infinite_iff_finite] at h
  exact IsDiscreteValuationRing.not_isField (Oinf Fq) (Finite.isField_of_domain (Oinf Fq))

variable [Fintype Fq]

theorem card_residue : Nat.card (Oinf Fq ⧸ Ideal.span {piInf Fq}) = Fintype.card Fq := by
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (Equiv.ofBijective _ (residue_bijective Fq))).symm

/-- The order at infinity of a nonzero element of `Oinf` is `-intDegree`. -/
theorem span_eq_pow {y : Oinf Fq} (hy : y ≠ 0) :
    Ideal.span {y} = Ideal.span {piInf Fq} ^ (-(y : RatFunc Fq).intDegree).toNat := by
  set n := (-(y : RatFunc Fq).intDegree).toNat
  have hy' : (y : RatFunc Fq) ≠ 0 := fun h => hy (Subtype.ext h)
  have hdeg := (mem_Oinf_iff' Fq hy').mp y.2
  have hn : (n : ℤ) = -(y : RatFunc Fq).intDegree := Int.toNat_of_nonneg (by omega)
  have hXn : (RatFunc.X ^ n : RatFunc Fq).intDegree = n := by
    rw [← RatFunc.algebraMap_X, ← map_pow, RatFunc.intDegree_polynomial, Polynomial.natDegree_X_pow]
  have hu0 : (y : RatFunc Fq) * RatFunc.X ^ n ≠ 0 := mul_ne_zero hy' (pow_ne_zero _ (X_ne_zero' Fq))
  have hudeg : ((y : RatFunc Fq) * RatFunc.X ^ n).intDegree = 0 := by
    rw [RatFunc.intDegree_mul hy' (pow_ne_zero _ (X_ne_zero' Fq)), hXn]
    omega
  have hu : (y : RatFunc Fq) * RatFunc.X ^ n ∈ Oinf Fq := (mem_Oinf_iff' Fq hu0).mpr hudeg.le
  have hui : ((y : RatFunc Fq) * RatFunc.X ^ n)⁻¹ ∈ Oinf Fq :=
    (mem_Oinf_iff' Fq (inv_ne_zero hu0)).mpr (by rw [RatFunc.intDegree_inv, hudeg]; simp)
  let u : Oinf Fq := ⟨_, hu⟩
  have h1 : u * ⟨_, hui⟩ = 1 := by
    ext
    show ((y : RatFunc Fq) * RatFunc.X ^ n) * ((y : RatFunc Fq) * RatFunc.X ^ n)⁻¹ = 1
    exact mul_inv_cancel₀ hu0
  have hunit : IsUnit u := isUnit_iff_exists_inv.mpr ⟨_, h1⟩
  have hyu : y = u * piInf Fq ^ n := by
    ext
    simp only [u, MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_piInf]
    rw [one_div, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (X_ne_zero' Fq)), mul_one]
  rw [hyu, Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit hunit]

theorem span_piInf_ne_bot : Ideal.span {piInf Fq} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]; exact piInf_ne_zero Fq

/-- `#(Oinf ⧸ y) = q ^ (-intDegree y)`. -/
theorem card_quot_Oinf {y : Oinf Fq} (hy : y ≠ 0) :
    Nat.card (Oinf Fq ⧸ Ideal.span {y}) = Fintype.card Fq ^ (-(y : RatFunc Fq).intDegree).toNat := by
  have : (Ideal.span {piInf Fq}).IsPrime := (span_piInf_isMaximal Fq).isPrime
  rw [span_eq_pow Fq hy, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime (span_piInf_ne_bot Fq),
    Submodule.cardQuot_apply, card_residue]

end Oinf

/-! ## 3. Places of a Dedekind domain with finite residue rings: degree, order, divisors -/

section Generic

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra Fq S]

/-- Every nonzero principal ideal has finite index. -/
class FiniteQuot : Prop where
  finite : ∀ a : S, a ≠ 0 → Finite (S ⧸ Ideal.span {a})

variable {S}

/-- The degree of a place: the `Fq`-dimension of its residue field. -/
def deg (P : HeightOneSpectrum S) : ℕ := Module.finrank Fq (S ⧸ P.asIdeal)

variable [FiniteQuot S]

instance finite_residue (P : HeightOneSpectrum S) : Finite (S ⧸ P.asIdeal) := by
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have := FiniteQuot.finite (S := S) a ha0
  exact Finite.of_surjective _
    (Ideal.Quotient.factor_surjective ((Ideal.span_singleton_le_iff_mem _).mpr haP))

instance moduleFinite_residue (P : HeightOneSpectrum S) : Module.Finite Fq (S ⧸ P.asIdeal) :=
  Module.Finite.of_finite

theorem card_residue_eq (P : HeightOneSpectrum S) :
    Nat.card (S ⧸ P.asIdeal) = Fintype.card Fq ^ deg Fq P := by
  rw [Module.natCard_eq_pow_finrank (K := Fq), Nat.card_eq_fintype_card (α := Fq)]; rfl

theorem deg_pos (P : HeightOneSpectrum S) : 0 < deg Fq P := by
  have : Nontrivial (S ⧸ P.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr P.isPrime.ne_top
  exact Module.finrank_pos

variable {K : Type*} [Field K] [Algebra S K] [IsFractionRing S K]

/-- The order of `f` at `P` (`0` for `f = 0`). -/
def ord (P : HeightOneSpectrum S) (f : K) : ℤ := -WithZero.log (P.valuation K f)

/-- The multiplicity of `P` in the ideal `(a)`. -/
def cnt (P : HeightOneSpectrum S) (a : S) : ℕ :=
  (Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {a})).factors

theorem ord_algebraMap (P : HeightOneSpectrum S) {a : S} (ha : a ≠ 0) :
    ord P (algebraMap S K a) = cnt P a := by
  rw [ord, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_def, if_neg ha,
    WithZero.log_exp, neg_neg, cnt]

@[simp] theorem ord_zero (P : HeightOneSpectrum S) : ord P (0 : K) = 0 := by simp [ord]

theorem ord_mul (P : HeightOneSpectrum S) {f g : K} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord P (f * g) = ord P f + ord P g := by
  rw [ord, ord, ord, map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hf)
    ((Valuation.ne_zero_iff _).mpr hg)]; ring

theorem ord_div (P : HeightOneSpectrum S) {f g : K} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord P (f / g) = ord P f - ord P g := by
  rw [ord, ord, ord, map_div₀, WithZero.log_div ((Valuation.ne_zero_iff _).mpr hf)
    ((Valuation.ne_zero_iff _).mpr hg)]; ring

theorem finite_cnt {a : S} (ha : a ≠ 0) : {P : HeightOneSpectrum S | cnt P a ≠ 0}.Finite := by
  have h := Filter.eventually_cofinite.mp (Associates.finite_factors (I := Ideal.span {a})
    (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]))
  refine h.subset fun P hP => ?_
  simp only [Set.mem_ofPred_eq, cnt] at hP ⊢
  exact_mod_cast hP

theorem finite_ord (f : K) : {P : HeightOneSpectrum S | ord P f ≠ 0}.Finite := by
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hf
  have ha' : algebraMap S K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S K)).mpr ha0
  have hb' : algebraMap S K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S K)).mpr hb0
  refine ((finite_cnt ha0).union (finite_cnt hb0)).subset fun P hP => ?_
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hP ⊢
  rw [ord_div P ha' hb', ord_algebraMap P ha0, ord_algebraMap P hb0] at hP
  by_contra hcon
  push Not at hcon
  rw [hcon.1, hcon.2] at hP
  simp at hP

variable (S) in
/-- The divisor of `f` restricted to the places of `S`. -/
def divS (f : K) : HeightOneSpectrum S →₀ ℤ :=
  Finsupp.ofSupportFinite (fun P => ord P f) (finite_ord f)

@[simp] theorem divS_apply (f : K) (P : HeightOneSpectrum S) : divS S f P = ord P f := rfl

/-- Degree of a divisor supported on the places of `S`. -/
def degS (D : HeightOneSpectrum S →₀ ℤ) : ℤ := D.sum fun P n => n * (deg Fq P : ℤ)

theorem degS_sub (D E : HeightOneSpectrum S →₀ ℤ) : degS Fq (D - E) = degS Fq D - degS Fq E := by
  unfold degS
  rw [Finsupp.sum_sub_index]
  intro P a b; ring

theorem divS_div {f g : K} (hf : f ≠ 0) (hg : g ≠ 0) : divS S (f / g) = divS S f - divS S g := by
  ext P; simp [ord_div P hf hg]

variable [Infinite S]

/-- `#(S ⧸ a) = q ^ (Σ_P cnt_P(a) deg P)`. -/
theorem card_quot_eq_pow {a : S} (ha : a ≠ 0) :
    Nat.card (S ⧸ Ideal.span {a}) = Fintype.card Fq ^
      (∑ P ∈ (finite_cnt ha).toFinset, cnt P a * deg Fq P) := by
  have hI : Ideal.span {a} ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  rw [← cardHom_apply, ← Ideal.finprod_heightOneSpectrum_factorization hI]
  rw [show cardHom S (∏ᶠ v : HeightOneSpectrum S, v.maxPowDividing (Ideal.span {a})) =
      (cardHom S : Ideal S →* ℕ) (∏ᶠ v : HeightOneSpectrum S, v.maxPowDividing (Ideal.span {a}))
      from rfl, MonoidHom.map_finprod _ (Ideal.hasFiniteMulSupport hI)]
  rw [finprod_eq_prod_of_mulSupport_subset (s := (finite_cnt ha).toFinset)]
  · rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun P _ => ?_
    simp only [MonoidHom.coe_coe, HeightOneSpectrum.maxPowDividing, map_pow, cardHom_apply,
      card_residue_eq Fq P, ← pow_mul, cnt, mul_comm]
  · intro P hP
    simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    intro h0
    apply hP
    simp [HeightOneSpectrum.maxPowDividing, cnt] at h0 ⊢
    simp [h0]

theorem degS_divS_algebraMap {a : S} (ha : a ≠ 0) :
    degS Fq (divS S (algebraMap S K a)) =
      ((∑ P ∈ (finite_cnt ha).toFinset, cnt P a * deg Fq P : ℕ) : ℤ) := by
  unfold degS
  rw [Finsupp.sum_of_support_subset (s := (finite_cnt ha).toFinset)]
  · push_cast
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [divS_apply, ord_algebraMap P ha]
  · intro P hP
    simp only [Finsupp.mem_support_iff, divS_apply, ord_algebraMap P ha] at hP
    simp only [Set.mem_ofPred_eq, Set.Finite.mem_toFinset]
    exact_mod_cast hP
  · intro P _; simp

end Generic

end RamanujanPetersson.Places


