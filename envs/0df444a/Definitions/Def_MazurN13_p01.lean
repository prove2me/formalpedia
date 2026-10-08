-- Prove2me | Definitions.Def_MazurN13_p01
-- name    : MazurN13_p01
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-08T00:00:14.358198+00:00
-- url     : https://prove2.me/theorems/cae53fbf-d235-4326-9727-e48e83c61eab
-- title:
--   Mazur order 13 (Huang FLT port), part 1/33
-- statement:
--   Part 1 of 33 of a machine-checked Lean proof that no elliptic curve over $\mathbb{Q}$ has a rational point of exact order $13$ (the case $N=13$ of Mazur's torsion theorem). The chain as a whole proves that the only rational affine points of the genus-two curve $Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$ (a model of $X_1(13)$) have $X\in\{0,-1\}$ (cusps); the final result is `MazurProof.N13ConstructedRationalPointTheorem.affine_x_is_cuspidal` in part {N}.
--
--   This part is not a single definition: it is a verbatim, sorry-free slice of Xiang Huang's Lean development, ported to this Mathlib and split into compile-sized pieces, each importing the previous part. It contains the modules:
--
--   - `FLT.Assumptions.MazurProof.EvenPrincipalIdeal`
--   - `FLT.Assumptions.MazurProof.FakeSquareClass`
--   - `FLT.Assumptions.MazurProof.EvenSexticNormPair`
--   - `FLT.Assumptions.MazurProof.ExceptionalPrincipalIdeal`
--   - `FLT.Assumptions.MazurProof.GeneralizedGraphIdealCore`
--   - `FLT.Assumptions.MazurProof.GraphJacobianDecompositionFrame`
--   - `FLT.Assumptions.MazurProof.GraphJacobianDualFrame`
--   - `FLT.Assumptions.MazurProof.IntegralClosureOfEisensteinDiscr`
--   - `FLT.Assumptions.MazurProof.LinearAdjoinRootScalar`
--   - `FLT.Assumptions.MazurProof.TateNFDivision`
--   - `FLT.Assumptions.MazurProof.N13CurveModel`
--   - `FLT.Assumptions.MazurProof.N13GoodModelTwo`
--   - `FLT.Assumptions.MazurProof.N13SymmetricSquareTwo`
--   - `FLT.Assumptions.MazurProof.N13AbelFiberTwoModel`
--   - `FLT.Assumptions.MazurProof.N13FormalAbelLinearization`
--   - `FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral`
--   - `FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo`
--   - `FLT.Assumptions.MazurProof.N13GeneralizedMumfordReduction`
--   - `FLT.Assumptions.MazurProof.N13AbelChartBase`
--   - `FLT.Assumptions.MazurProof.SexticMumford`
--   - `FLT.Assumptions.MazurProof.N13Mumford`
--   - `FLT.Assumptions.MazurProof.N13GoodSexticCoordinateEquiv`
--   - `FLT.Assumptions.MazurProof.N13GoodSexticMumfordTransport`
--   - `FLT.Assumptions.MazurProof.N13TwoAdicMumfordTransport`
--   - `FLT.Assumptions.MazurProof.N13TwoAdicCoordinateBaseChange`
--
--   Port notes: API drift fixes only (transparency options, renamed lemmas, explicit instances); local notations expanded, `private` removed.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT commit 51bbb4f, directory FLT/Assumptions/MazurProof (N13* and SexticMumford* modules and their dependencies)

import Mathlib
set_option maxHeartbeats 1000000

-- module FLT.Assumptions.MazurProof.EvenPrincipalIdeal
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.EvenPrincipalIdeal =====
section

/-!
# Even height-one counts in a Dedekind PID

If every prime-ideal exponent of a nonzero principal ideal is even, halve
the ideal factorization itself.  This gives a literal square ideal, rather
than merely a class-group equality.  Principality of its square root then
recovers the original generator as a unit times a square.

The construction is structural: it uses the factorization Finsupp of an
ideal and never enumerates height-one primes or chooses prime elements.
-/

open scoped nonZeroDivisors

open IsDedekindDomain
open UniqueFactorizationMonoid

noncomputable section

namespace MazurProof.EvenPrincipalIdeal

/-! ## Halving a factorization -/

/-- In a unique factorization monoid with no nontrivial units, an element
whose factorization multiplicities are all even is literally a square. -/
theorem exists_sq_eq_of_all_factorization_even
    {A : Type*}
    [CommMonoidWithZero A]
    [Nontrivial A]
    [UniqueFactorizationMonoid A]
    [NormalizationMonoid A]
    [DecidableEq A]
    [Subsingleton Aˣ]
    (a : A)
    (ha : a ≠ 0)
    (hEven : ∀ p : A, Even (factorization a p)) :
    ∃ b : A, b ^ 2 = a := by
  let f : A →₀ ℕ := factorization a
  let g : A →₀ ℕ :=
    Finsupp.mapRange (fun n : ℕ => n / 2) (by simp) f

  have hfg : f = g + g := by
    ext p
    simp only [f, g, Finsupp.add_apply, Finsupp.mapRange_apply]
    obtain ⟨k, hk⟩ := hEven p
    omega

  let s : Multiset A := Finsupp.toMultiset g
  let b : A := s.prod

  have hsPrime : ∀ p ∈ s, Prime p := by
    intro p hp
    have hpsupp : p ∈ g.support :=
      (Finsupp.mem_toMultiset g p).mp
        (by simpa [s] using hp)
    have hpg : g p ≠ 0 :=
      Finsupp.mem_support_iff.mp hpsupp
    have hpf : f p ≠ 0 := by
      intro hzero
      apply hpg
      simp [g, hzero]
    have hpnf : p ∈ normalizedFactors a := by
      rw [← Multiset.count_ne_zero]
      simpa [f, factorization_eq_count] using hpf
    exact prime_of_normalized_factor p hpnf

  have hb0 : b ≠ 0 := by
    dsimp [b]
    exact s.prod_ne_zero_of_prime hsPrime

  have hnf_b : normalizedFactors b = s := by
    dsimp [b]
    exact normalizedFactors_prod_of_prime hsPrime

  have hfac_b : factorization b = g := by
    change Multiset.toFinsupp (normalizedFactors b) = g
    rw [hnf_b]
    exact Finsupp.toMultiset_toFinsupp g

  have hfac_sq :
      factorization (b ^ 2) = factorization a := by
    rw [factorization_pow, hfac_b]
    change 2 • g = f
    simpa [two_nsmul] using hfg.symm

  have hassoc : Associated (b ^ 2) a :=
    associated_of_factorization_eq
      (b ^ 2) a (pow_ne_zero 2 hb0) ha hfac_sq

  exact ⟨b, associated_iff_eq.mp hassoc⟩

/-! ## From fractional-ideal counts to the integral ideal factorization -/

variable {O L : Type*}
variable [CommRing O] [IsDedekindDomain O]
variable [Field L] [Algebra O L] [IsFractionRing O L]

/-- The height-one count of the principal fractional ideal generated by an
integral element. -/
noncomputable def principalCount
    (P : HeightOneSpectrum O) (x : O) : ℤ :=
  FractionalIdeal.count L P
    (FractionalIdeal.spanSingleton O⁰ (algebraMap O L x))

/-- Fractional-ideal count agrees with the factorization multiplicity of the
corresponding integral principal ideal. -/
theorem principalCount_eq_factorization_span
    (x : O) (hx : x ≠ 0)
    (P : HeightOneSpectrum O) :
    principalCount (L := L) P x =
      (factorization
        (Ideal.span ({x} : Set O)) P.asIdeal : ℤ) := by
  classical

  let I : Ideal O := Ideal.span ({x} : Set O)
  have hI : I ≠ 0 := by
    simpa [I, Ideal.zero_eq_bot,
      Ideal.span_singleton_eq_bot] using hx

  have hnat :
      (Associates.mk P.asIdeal).count
          (Associates.mk I).factors =
        factorization I P.asIdeal := by
    rw [factorization_eq_count,
      Associates.factors_mk _ hI,
      Associates.count_some
        (Associates.irreducible_mk.mpr P.irreducible),
      ← Multiset.count_map_eq_count' _ _
        Subtype.val_injective,
      Associates.map_subtype_coe_factors',
      factors_eq_normalizedFactors,
      ← Multiset.count_map_eq_count' _ _
        (Associates.mk_injective (M := Ideal O))]

  calc
    principalCount (L := L) P x =
      FractionalIdeal.count L P
        ((Ideal.span ({x} : Set O) : Ideal O) :
          FractionalIdeal O⁰ L) := by
            unfold principalCount
            rw [FractionalIdeal.coeIdeal_span_singleton]
    _ =
      ((Associates.mk P.asIdeal).count
        (Associates.mk
          (Ideal.span ({x} : Set O))).factors : ℤ) := by
          simpa [I] using
            FractionalIdeal.count_coe L P hI
    _ =
      (factorization
        (Ideal.span ({x} : Set O)) P.asIdeal : ℤ) := by
          simpa [I] using
            congrArg (fun n : ℕ => (n : ℤ)) hnat

/-! ## Unit times square -/

variable [IsPrincipalIdealRing O]

/-- If every height-one count of a nonzero principal ideal is even, its
generator is a unit times a square in the integral ring. -/
theorem exists_unit_mul_sq_of_all_principalCounts_even
    (x : O) (hx : x ≠ 0)
    (hcount : ∀ P : HeightOneSpectrum O,
      Even (principalCount (L := L) P x)) :
    ∃ ε : Oˣ, ∃ y : O,
      x = (ε : O) * y ^ 2 := by
  classical

  let I : Ideal O := Ideal.span ({x} : Set O)
  have hI : I ≠ 0 := by
    simpa [I, Ideal.zero_eq_bot,
      Ideal.span_singleton_eq_bot] using hx

  have hfacEven :
      ∀ q : Ideal O, Even (factorization I q) := by
    intro q
    by_cases hq0 : factorization I q = 0
    · simp [hq0]
    · have hqmem : q ∈ normalizedFactors I := by
        rw [← Multiset.count_ne_zero]
        simpa [factorization_eq_count] using hq0
      have hqprime : Prime q :=
        prime_of_normalized_factor q hqmem
      let P : HeightOneSpectrum O :=
        ⟨q, Ideal.isPrime_of_prime hqprime,
          hqprime.ne_zero⟩
      have hc := hcount P
      rw [principalCount_eq_factorization_span
        x hx P] at hc
      have hcNat :
          Even
            (factorization
              (Ideal.span ({x} : Set O))
              P.asIdeal) :=
        (Int.even_coe_nat _).mp hc
      simpa [I, P] using hcNat

  obtain ⟨J, hJ_sq⟩ :=
    exists_sq_eq_of_all_factorization_even
      I hI hfacEven

  let y : O := Submodule.IsPrincipal.generator J
  have hJy :
      Ideal.span ({y} : Set O) = J :=
    Ideal.span_singleton_generator J

  have hspan :
      Ideal.span ({y ^ 2} : Set O) =
        Ideal.span ({x} : Set O) := by
    calc
      Ideal.span ({y ^ 2} : Set O) =
          (Ideal.span ({y} : Set O)) ^ 2 := by
            simp [pow_two,
              Ideal.span_singleton_mul_span_singleton]
      _ = J ^ 2 := by rw [hJy]
      _ = I := hJ_sq
      _ = Ideal.span ({x} : Set O) := rfl

  have hassoc_yx : Associated (y ^ 2) x :=
    Ideal.span_singleton_eq_span_singleton.mp hspan

  rcases hassoc_yx with ⟨ε, hε⟩
  refine ⟨ε, y, ?_⟩
  simpa [mul_comm] using hε.symm

/-- Remove an explicit integral carrier from a principal element.  If all
corrected height-one counts are even, the residual factor is a unit times a
square.  The divisibility hypothesis is essential for the square root to
remain integral. -/
theorem exists_unit_mul_correction_mul_sq
    (a x : O)
    (ha : a ≠ 0) (hx : x ≠ 0)
    (hdiv : a ∣ x)
    (hparity : ∀ P : HeightOneSpectrum O,
      Even
        (principalCount (L := L) P x -
          principalCount (L := L) P a)) :
    ∃ ε : Oˣ, ∃ y : O,
      x = (ε : O) * a * y ^ 2 := by
  obtain ⟨z, hz⟩ := hdiv
  have hz0 : z ≠ 0 := by
    intro hz0
    apply hx
    simpa [hz0] using hz

  have hcount_z :
      ∀ P : HeightOneSpectrum O,
        Even (principalCount (L := L) P z) := by
    intro P
    have haL : algebraMap O L a ≠ 0 := by
      simpa only [map_zero] using
        (IsFractionRing.injective O L).ne ha
    have hzL : algebraMap O L z ≠ 0 := by
      simpa only [map_zero] using
        (IsFractionRing.injective O L).ne hz0
    have hmul :
        principalCount (L := L) P x =
          principalCount (L := L) P a +
            principalCount (L := L) P z := by
      unfold principalCount
      rw [hz, map_mul,
        ← FractionalIdeal.spanSingleton_mul_spanSingleton,
        FractionalIdeal.count_mul L P
          (FractionalIdeal.spanSingleton_ne_zero_iff.mpr
            haL)
          (FractionalIdeal.spanSingleton_ne_zero_iff.mpr
            hzL)]
    have hp := hparity P
    rw [hmul] at hp
    simpa only [add_sub_cancel_left] using hp

  obtain ⟨ε, y, hzy⟩ :=
    exists_unit_mul_sq_of_all_principalCounts_even
      z hz0 hcount_z

  refine ⟨ε, y, ?_⟩
  rw [hz, hzy]
  ring

end MazurProof.EvenPrincipalIdeal
end
end
end

-- module FLT.Assumptions.MazurProof.FakeSquareClass
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.FakeSquareClass =====
section

/-!
# The fake square-class target

This file defines
`Lˣ / ((Lˣ)^2 * image(Kˣ))`
for a homomorphism of commutative rings `K →+* L`.

The product of the two subgroups is written as their supremum: `Lˣ` is
commutative, so this is the subgroup generated by squares and rational scalars.
-/

namespace MazurProof.FakeSquareClass

variable {K L : Type*} [CommRing K] [CommRing L]

/-- The map on unit groups induced by a ring homomorphism `K →+* L`. -/
def scalarUnitsMap (e : K →+* L) : Kˣ →* Lˣ := Units.map e.toMonoidHom

/-- Squares together with the scalar subgroup of `Lˣ`. -/
def fakeSquareClassSubgroup (e : K →+* L) : Subgroup Lˣ :=
  Subgroup.square Lˣ ⊔ (⊤ : Subgroup Kˣ).map (scalarUnitsMap e)

/-- The usual fake square-class target. -/
abbrev Target (e : K →+* L) : Type _ :=
  Lˣ ⧸ fakeSquareClassSubgroup e

instance (e : K →+* L) : CommGroup (Target e) := inferInstance

/-- A scalar is trivial in the fake square-class target. -/
theorem scalar_eq_one (e : K →+* L) (q : Kˣ) :
    ((scalarUnitsMap e q : Lˣ) : Target e) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  apply Subgroup.mem_sup_right
  exact Subgroup.mem_map_of_mem (scalarUnitsMap e)
    (show q ∈ (⊤ : Subgroup Kˣ) from trivial)

/-- A square is trivial in the fake square-class target. -/
theorem square_eq_one (e : K →+* L) (s : Lˣ) :
    ((s ^ 2 : Lˣ) : Target e) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  apply Subgroup.mem_sup_left
  exact Subgroup.mem_square.mpr ⟨s, by simp [pow_two]⟩

/-- Every element of the fake square-class target has exponent two. -/
@[simp] theorem target_sq_eq_one (e : K →+* L) (z : Target e) :
    z ^ 2 = 1 := by
  refine QuotientGroup.induction_on z ?_
  intro s
  exact square_eq_one e s

/-- In an exponent-two square-class target, equality is detected by the
product rather than by a quotient. -/
theorem target_eq_iff_mul_eq_one (e : K →+* L) (x y : Target e) :
    x = y ↔ x * y = 1 := by
  constructor
  · intro hxy
    rw [hxy]
    rw [← pow_two]
    exact target_sq_eq_one e y
  · intro hxy
    calc
      x = x * 1 := (mul_one x).symm
      _ = x * (y * y) := by rw [← pow_two, target_sq_eq_one]
      _ = (x * y) * y := by ac_rfl
      _ = y := by rw [hxy, one_mul]

/-- If `z` differs from a scalar by a square, its fake class is trivial. -/
theorem eq_one_of_mul_sq_eq_scalar
    (e : K →+* L) (z s : Lˣ) (q : Kˣ)
    (h : z * s ^ 2 = scalarUnitsMap e q) :
    (z : Target e) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  have hscalar : scalarUnitsMap e q ∈ fakeSquareClassSubgroup e := by
    apply Subgroup.mem_sup_right
    exact Subgroup.mem_map_of_mem (scalarUnitsMap e)
      (show q ∈ (⊤ : Subgroup Kˣ) from trivial)
  have hprod : z * s ^ 2 ∈ fakeSquareClassSubgroup e := by
    rw [h]
    exact hscalar
  have hsq : s ^ 2 ∈ fakeSquareClassSubgroup e := by
    apply Subgroup.mem_sup_left
    exact Subgroup.mem_square.mpr ⟨s, by simp [pow_two]⟩
  have hdiv := (fakeSquareClassSubgroup e).div_mem hprod hsq
  simpa using hdiv

end MazurProof.FakeSquareClass

end
end

-- module FLT.Assumptions.MazurProof.EvenSexticNormPair
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.EvenSexticNormPair =====
section

/-!
# Full norm-pair and fake targets for an even sextic

For an even sextic, the full two-descent target remembers a pair
`(α,s)` satisfying `N(α)=s²`.  It is quotiented by

* `(β²,N(β))`, and
* `(q,q³)` for ground-field scalars.

Forgetting the second coordinate gives the usual fake square-class target.
This file develops that target algebra for abstract commutative groups.  The
only sextic-specific input is that the norm of a scalar is its sixth power.
No Picard group or Kummer exactness theorem is used here.
-/

namespace MazurProof.EvenSexticNormPair

noncomputable section

variable {A B : Type*} [CommGroup A] [CommGroup B]

/-- Pairs `(α,s)` satisfying the norm-square equation. -/
def normPairSubgroup (N : A →* B) : Subgroup (A × B) where
  carrier := {p | N p.1 = p.2 ^ 2}
  one_mem' := by
    change N 1 = (1 : B) ^ 2
    simp
  mul_mem' := by
    rintro ⟨a, s⟩ ⟨b, t⟩ ha hb
    change N (a * b) = (s * t) ^ 2
    rw [map_mul, ha, hb, mul_pow]
  inv_mem' := by
    rintro ⟨a, s⟩ ha
    change N a⁻¹ = s⁻¹ ^ 2
    rw [map_inv, ha, inv_pow]

abbrev NormPair (N : A →* B) :=
  ↥(normPairSubgroup N)

/-- Projection of a norm pair to its first coordinate. -/
def fstHom (N : A →* B) : NormPair N →* A :=
  (MonoidHom.fst A B).comp (normPairSubgroup N).subtype

@[simp] theorem fstHom_apply (N : A →* B) (p : NormPair N) :
    fstHom N p = p.1.1 :=
  rfl

/-- Projection of a norm pair to its chosen norm root. -/
def sndHom (N : A →* B) : NormPair N →* B :=
  (MonoidHom.snd A B).comp (normPairSubgroup N).subtype

@[simp] theorem sndHom_apply (N : A →* B) (p : NormPair N) :
    sndHom N p = p.1.2 :=
  rfl

@[simp] theorem norm_fst_eq_snd_sq (N : A →* B) (p : NormPair N) :
    N (fstHom N p) = sndHom N p ^ 2 :=
  p.2

/-- The square/norm gauge element `(β²,N(β))`. -/
def chi (N : A →* B) : A →* NormPair N where
  toFun β :=
    ⟨(β ^ 2, N β), by
      change N (β ^ 2) = (N β) ^ 2
      rw [map_pow]⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' β γ := by
    apply Subtype.ext
    ext <;> simp [mul_pow]

@[simp] theorem chi_fst (N : A →* B) (β : A) :
    fstHom N (chi N β) = β ^ 2 :=
  rfl

@[simp] theorem chi_snd (N : A →* B) (β : A) :
    (chi N β : A × B).2 = N β :=
  rfl

/-- The scalar gauge element `(q,q³)`.  The hypothesis is the degree-six
norm formula for scalars. -/
def iota (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6) :
    B →* NormPair N where
  toFun q :=
    ⟨(e q, q ^ 3), by
      change N (e q) = (q ^ 3) ^ 2
      rw [norm_scalar]
      group⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' q r := by
    apply Subtype.ext
    ext <;> simp [mul_pow]

@[simp] theorem iota_fst
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (q : B) :
    fstHom N (iota N e norm_scalar q) = e q :=
  rfl

@[simp] theorem iota_snd
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (q : B) :
    (iota N e norm_scalar q : A × B).2 = q ^ 3 :=
  rfl

/-- Squares and scalars in the first-coordinate fake target. -/
def fakeGauge (e : B →* A) : Subgroup A :=
  Subgroup.square A ⊔ (⊤ : Subgroup B).map e

/-- Membership in the fake gauge has the expected square-times-scalar
normal form.  This is subgroup plumbing, not an arithmetic input. -/
theorem mem_fakeGauge_iff_exists (e : B →* A) (a : A) :
    a ∈ fakeGauge e ↔
      ∃ β : A, ∃ q : B, a = β ^ 2 * e q := by
  constructor
  · intro ha
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      (Subgroup.mem_sup.mp ha)
    obtain ⟨β, hβ⟩ := Subgroup.mem_square.mp hx
    obtain ⟨q, -, hq⟩ := hy
    refine ⟨β, q, ?_⟩
    rw [← hxy, ← hq, hβ, pow_two]
  · rintro ⟨β, q, rfl⟩
    apply Subgroup.mul_mem_sup
    · exact Subgroup.mem_square.mpr ⟨β, by simp [pow_two]⟩
    · exact Subgroup.mem_map_of_mem e trivial

abbrev FakeTarget (e : B →* A) :=
  A ⧸ fakeGauge e

/-- The two gauge families in the full norm-pair target. -/
def fullGauge
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6) :
    Subgroup (NormPair N) :=
  (chi N).range ⊔ (iota N e norm_scalar).range

abbrev FullTarget
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6) :=
  NormPair N ⧸ fullGauge N e norm_scalar

/-- Forget the norm-root coordinate before quotienting the full target. -/
def forgetRaw (N : A →* B) (e : B →* A) :
    NormPair N →* FakeTarget e :=
  (QuotientGroup.mk' (fakeGauge e)).comp (fstHom N)

@[simp] theorem forgetRaw_apply
    (N : A →* B) (e : B →* A) (p : NormPair N) :
    forgetRaw N e p =
      QuotientGroup.mk' (fakeGauge e) p.1.1 :=
  rfl

theorem fullGauge_le_forgetRaw_ker
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6) :
    fullGauge N e norm_scalar ≤ (forgetRaw N e).ker := by
  rw [fullGauge, sup_le_iff]
  constructor
  · rintro _ ⟨β, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply (QuotientGroup.eq_one_iff _).mpr
    apply Subgroup.mem_sup_left
    change β ^ 2 ∈ Subgroup.square A
    exact Subgroup.mem_square.mpr ⟨β, by simp [pow_two]⟩
  · rintro _ ⟨q, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply (QuotientGroup.eq_one_iff _).mpr
    apply Subgroup.mem_sup_right
    exact Subgroup.mem_map_of_mem e trivial

/-- Forgetting the second coordinate descends from the full target to the
fake target. -/
def forget
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6) :
    FullTarget N e norm_scalar →* FakeTarget e :=
  QuotientGroup.lift
    (fullGauge N e norm_scalar)
    (forgetRaw N e)
    (fullGauge_le_forgetRaw_ker N e norm_scalar)

@[simp] theorem forget_mk
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (p : NormPair N) :
    forget N e norm_scalar
        (QuotientGroup.mk' (fullGauge N e norm_scalar) p) =
      QuotientGroup.mk' (fakeGauge e) p.1.1 :=
  rfl

/-- A norm pair with first coordinate one and square-one second coordinate.
Over the rational units there are only the choices `+1` and `-1`. -/
def signPair (N : A →* B) (ε : B) (hε : ε ^ 2 = 1) :
    NormPair N :=
  ⟨(1, ε), by
    change N 1 = ε ^ 2
    simpa using hε.symm⟩

@[simp] theorem forget_signPair
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (ε : B) (hε : ε ^ 2 = 1) :
    forget N e norm_scalar
        (QuotientGroup.mk' (fullGauge N e norm_scalar)
          (signPair N ε hε)) = 1 := by
  rw [forget_mk]
  exact map_one _

/-! ## The kernel of forgetting the norm root -/

/-- Remove a square gauge and a scalar gauge from a norm pair. -/
def normalize
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (p : NormPair N) (β : A) (q : B) :
    NormPair N :=
  p / (chi N β * iota N e norm_scalar q)

theorem fstHom_normalize_eq_one
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (p : NormPair N) (β : A) (q : B)
    (hp : fstHom N p = β ^ 2 * e q) :
    fstHom N (normalize N e norm_scalar p β q) = 1 := by
  change fstHom N p / (β ^ 2 * e q) = 1
  rw [hp]
  simp

theorem fullClass_normalize
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (p : NormPair N) (β : A) (q : B) :
    QuotientGroup.mk' (fullGauge N e norm_scalar) p =
      QuotientGroup.mk' (fullGauge N e norm_scalar)
        (normalize N e norm_scalar p β q) := by
  let g : NormPair N := chi N β * iota N e norm_scalar q
  have hg : g ∈ fullGauge N e norm_scalar := by
    apply Subgroup.mul_mem_sup
    · exact ⟨β, rfl⟩
    · exact ⟨q, rfl⟩
  have hgclass :
      QuotientGroup.mk' (fullGauge N e norm_scalar) g = 1 :=
    (QuotientGroup.eq_one_iff g).2 hg
  have hp : p = normalize N e norm_scalar p β q * g := by
    simp [normalize, g]
  calc
    QuotientGroup.mk' (fullGauge N e norm_scalar) p =
        QuotientGroup.mk' (fullGauge N e norm_scalar)
          (normalize N e norm_scalar p β q * g) := by
      exact congrArg
        (QuotientGroup.mk' (fullGauge N e norm_scalar)) hp
    _ = QuotientGroup.mk' (fullGauge N e norm_scalar)
          (normalize N e norm_scalar p β q) *
        QuotientGroup.mk' (fullGauge N e norm_scalar) g := by
      rw [map_mul]
    _ = QuotientGroup.mk' (fullGauge N e norm_scalar)
          (normalize N e norm_scalar p β q) := by
      rw [hgclass, mul_one]

theorem sndHom_normalize_sq_eq_one
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (p : NormPair N) (β : A) (q : B)
    (hp : fstHom N p = β ^ 2 * e q) :
    sndHom N (normalize N e norm_scalar p β q) ^ 2 = 1 := by
  have hnorm :=
    norm_fst_eq_snd_sq N
      (normalize N e norm_scalar p β q)
  rw [fstHom_normalize_eq_one N e norm_scalar p β q hp] at hnorm
  simpa using hnorm.symm

/-- The fibre of the full target over the trivial fake class consists of
classes represented by `(1, ε)` with `ε²=1`. -/
theorem forget_eq_one_iff_exists_signPair
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (z : FullTarget N e norm_scalar) :
    forget N e norm_scalar z = 1 ↔
      ∃ ε : B, ∃ hε : ε ^ 2 = 1,
        z = QuotientGroup.mk' (fullGauge N e norm_scalar)
          (signPair N ε hε) := by
  constructor
  · intro hz
    obtain ⟨p, rfl⟩ :=
      QuotientGroup.mk'_surjective
        (fullGauge N e norm_scalar) z
    have hfake :
        QuotientGroup.mk' (fakeGauge e) (fstHom N p) = 1 := by
      change QuotientGroup.mk' (fakeGauge e) p.1.1 = 1
      simpa only [forget_mk] using hz
    have hmem : fstHom N p ∈ fakeGauge e :=
      (QuotientGroup.eq_one_iff (fstHom N p)).1 hfake
    obtain ⟨β, q, hp⟩ :=
      (mem_fakeGauge_iff_exists e (fstHom N p)).1 hmem
    let r : NormPair N := normalize N e norm_scalar p β q
    have hrfst : fstHom N r = 1 :=
      fstHom_normalize_eq_one N e norm_scalar p β q hp
    have hrsq : sndHom N r ^ 2 = 1 :=
      sndHom_normalize_sq_eq_one N e norm_scalar p β q hp
    have hr :
        r = signPair N (sndHom N r) hrsq := by
      apply Subtype.ext
      apply Prod.ext
      · exact hrfst
      · rfl
    refine ⟨sndHom N r, hrsq, ?_⟩
    calc
      QuotientGroup.mk' (fullGauge N e norm_scalar) p =
          QuotientGroup.mk' (fullGauge N e norm_scalar) r :=
        fullClass_normalize N e norm_scalar p β q
      _ = QuotientGroup.mk' (fullGauge N e norm_scalar)
          (signPair N (sndHom N r) hrsq) :=
        congrArg
          (QuotientGroup.mk' (fullGauge N e norm_scalar)) hr
  · rintro ⟨ε, hε, rfl⟩
    exact forget_signPair N e norm_scalar ε hε

/-- If the base group has only two square roots of one, the forgetting
kernel has at most the identity and one sign class. -/
theorem forget_eq_one_iff_eq_one_or_eq_sign
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (σ : B) (hσ : σ ^ 2 = 1)
    (sqOne : ∀ ε : B, ε ^ 2 = 1 → ε = 1 ∨ ε = σ)
    (z : FullTarget N e norm_scalar) :
    forget N e norm_scalar z = 1 ↔
      z = 1 ∨
        z = QuotientGroup.mk' (fullGauge N e norm_scalar)
          (signPair N σ hσ) := by
  constructor
  · intro hz
    obtain ⟨ε, hε, hzε⟩ :=
      (forget_eq_one_iff_exists_signPair N e norm_scalar z).1 hz
    rcases sqOne ε hε with rfl | rfl
    · left
      rw [hzε]
      have hraw : signPair N 1 hε = 1 := by
        apply Subtype.ext
        ext <;> simp [signPair]
      rw [hraw]
      exact map_one _
    · exact Or.inr hzε
  · rintro (rfl | rfl)
    · exact map_one _
    · exact forget_signPair N e norm_scalar σ hσ

/-- Every class in the full norm-pair target has exponent two. -/
@[simp] theorem fullTarget_sq_eq_one
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (z : FullTarget N e norm_scalar) :
    z ^ 2 = 1 := by
  obtain ⟨p, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (fullGauge N e norm_scalar) z
  have hp : p ^ 2 = chi N (fstHom N p) := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · simpa [pow_two] using (norm_fst_eq_snd_sq N p).symm
  change QuotientGroup.mk' (fullGauge N e norm_scalar) (p ^ 2) = 1
  rw [hp]
  apply (QuotientGroup.eq_one_iff _).2
  apply Subgroup.mem_sup_left
  exact ⟨fstHom N p, rfl⟩

end

end MazurProof.EvenSexticNormPair

end
end

-- module FLT.Assumptions.MazurProof.ExceptionalPrincipalIdeal
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.ExceptionalPrincipalIdeal =====
section

/-!
# Principal ideals with two exceptional carriers

In a Dedekind PID, even height-one counts away from two explicit principal
primes leave exactly two parity bits.  The proof extracts those bits from
the ideal factorization, removes the corresponding integral carriers, and
halves the remaining factorization through EvenPrincipalIdeal.

No height-one primes are enumerated and no ideal-class computation is used.
-/

open scoped nonZeroDivisors

open IsDedekindDomain
open UniqueFactorizationMonoid

noncomputable section

namespace MazurProof.ExceptionalPrincipalIdeal

open EvenPrincipalIdeal

variable {O L : Type*}
variable [CommRing O] [IsDedekindDomain O]
variable [Field L] [Algebra O L] [IsFractionRing O L]

theorem factorization_heightOne_self
    (P : HeightOneSpectrum O) :
    factorization P.asIdeal P.asIdeal = 1 := by
  classical
  rw [factorization_eq_count,
    normalizedFactors_irreducible P.irreducible]
  simp

theorem factorization_heightOne_apply_of_ne
    (P R : HeightOneSpectrum O)
    (hRP : R ≠ P) :
    factorization P.asIdeal R.asIdeal = 0 := by
  classical
  rw [factorization_eq_count,
    normalizedFactors_irreducible P.irreducible]
  have hideal : R.asIdeal ≠ P.asIdeal := by
    intro h
    apply hRP
    exact HeightOneSpectrum.ext h
  simp [hideal]

theorem principalCount_mul
    {a b : O} (ha : a ≠ 0) (hb : b ≠ 0)
    (R : HeightOneSpectrum O) :
    principalCount (L := L) R (a * b) =
      principalCount (L := L) R a +
        principalCount (L := L) R b := by
  have haL : algebraMap O L a ≠ 0 :=
    by
      simpa only [map_zero] using
        (IsFractionRing.injective O L).ne ha
  have hbL : algebraMap O L b ≠ 0 :=
    by
      simpa only [map_zero] using
        (IsFractionRing.injective O L).ne hb
  unfold principalCount
  rw [map_mul,
    ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul L R
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr haL)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hbL)]

theorem principalCount_pow
    (a : O) (n : ℕ)
    (R : HeightOneSpectrum O) :
    principalCount (L := L) R (a ^ n) =
      (n : ℤ) * principalCount (L := L) R a := by
  unfold principalCount
  rw [map_pow, ← FractionalIdeal.spanSingleton_pow,
    FractionalIdeal.count_pow]

theorem principalCount_generator_self
    {A : O} (P : HeightOneSpectrum O)
    (hA : P.asIdeal =
      Ideal.span ({A} : Set O))
    (hA0 : A ≠ 0) :
    principalCount (L := L) P A = 1 := by
  rw [principalCount_eq_factorization_span A hA0 P,
    ← hA, factorization_heightOne_self]
  norm_num

theorem principalCount_generator_of_ne
    {A : O} (P R : HeightOneSpectrum O)
    (hA : P.asIdeal =
      Ideal.span ({A} : Set O))
    (hA0 : A ≠ 0)
    (hRP : R ≠ P) :
    principalCount (L := L) R A = 0 := by
  rw [principalCount_eq_factorization_span A hA0 R,
    ← hA, factorization_heightOne_apply_of_ne P R hRP]
  norm_num

/-- If every height-one count away from two explicit principal primes is
even, only the two parity bits of those primes remain. -/
theorem exists_unit_two_carriers_mul_sq_of_even_away
    [IsPrincipalIdealRing O]
    (P Q : HeightOneSpectrum O)
    (hPQ : P ≠ Q)
    (A Qelt x : O)
    (hPgen :
      P.asIdeal = Ideal.span ({A} : Set O))
    (hQgen :
      Q.asIdeal = Ideal.span ({Qelt} : Set O))
    (hx : x ≠ 0)
    (hAway :
      ∀ R : HeightOneSpectrum O,
        R ≠ P → R ≠ Q →
          Even (principalCount (L := L) R x)) :
    ∃ r q : ZMod 2, ∃ ε : Oˣ, ∃ y : O,
      x =
        (ε : O) * A ^ r.val *
          Qelt ^ q.val * y ^ 2 := by
  classical
  let I : Ideal O :=
    Ideal.span ({x} : Set O)
  let nP : ℕ := factorization I P.asIdeal
  let nQ : ℕ := factorization I Q.asIdeal
  let rN : ℕ := nP % 2
  let qN : ℕ := nQ % 2
  have hrN_lt : rN < 2 := by
    exact Nat.mod_lt _ (by omega)
  have hqN_lt : qN < 2 := by
    exact Nat.mod_lt _ (by omega)
  have hA0 : A ≠ 0 := by
    intro hzero
    apply P.ne_bot
    rw [hPgen, hzero]
    simp
  have hQ0 : Qelt ≠ 0 := by
    intro hzero
    apply Q.ne_bot
    rw [hQgen, hzero]
    simp
  have hxP_of_rN_eq_one
      (hr : rN = 1) :
      x ∈ P.asIdeal := by
    have hnP : nP ≠ 0 := by
      intro hzero
      simp [rN, hzero] at hr
    have hPmem :
        P.asIdeal ∈ normalizedFactors I := by
      rw [← Multiset.count_ne_zero]
      simpa [nP, factorization_eq_count] using hnP
    have hPdvd :
        P.asIdeal ∣ I :=
      dvd_of_mem_normalizedFactors hPmem
    exact
      (Ideal.dvd_span_singleton.mp
        (by simpa only [I] using hPdvd))
  have hxQ_of_qN_eq_one
      (hq : qN = 1) :
      x ∈ Q.asIdeal := by
    have hnQ : nQ ≠ 0 := by
      intro hzero
      simp [qN, hzero] at hq
    have hQmem :
        Q.asIdeal ∈ normalizedFactors I := by
      rw [← Multiset.count_ne_zero]
      simpa [nQ, factorization_eq_count] using hnQ
    have hQdvd :
        Q.asIdeal ∣ I :=
      dvd_of_mem_normalizedFactors hQmem
    exact
      (Ideal.dvd_span_singleton.mp
        (by simpa only [I] using hQdvd))
  have hdiv :
      A ^ rN * Qelt ^ qN ∣ x := by
    rcases Nat.mod_two_eq_zero_or_one nP with hr | hr
    · have hrN : rN = 0 := by
        exact hr
      rcases Nat.mod_two_eq_zero_or_one nQ with hq | hq
      · have hqN : qN = 0 := by
          exact hq
        simp [hrN, hqN]
      · have hqN : qN = 1 := by
          exact hq
        have hxQ : x ∈ Q.asIdeal :=
          hxQ_of_qN_eq_one hqN
        have hQdiv : Qelt ∣ x := by
          rw [← Ideal.mem_span_singleton,
            ← hQgen]
          exact hxQ
        simpa [hrN, hqN] using hQdiv
    · have hrN : rN = 1 := by
        exact hr
      rcases Nat.mod_two_eq_zero_or_one nQ with hq | hq
      · have hqN : qN = 0 := by
          exact hq
        have hxP : x ∈ P.asIdeal :=
          hxP_of_rN_eq_one hrN
        have hAdiv : A ∣ x := by
          rw [← Ideal.mem_span_singleton,
            ← hPgen]
          exact hxP
        simpa [hrN, hqN] using hAdiv
      · have hqN : qN = 1 := by
          exact hq
        have hxP : x ∈ P.asIdeal :=
          hxP_of_rN_eq_one hrN
        have hxQ : x ∈ Q.asIdeal :=
          hxQ_of_qN_eq_one hqN
        have hPQideal :
            P.asIdeal ≠ Q.asIdeal := by
          intro h
          apply hPQ
          exact HeightOneSpectrum.ext h
        have hcoprime :
            P.asIdeal ⊔ Q.asIdeal = ⊤ :=
          (P.isPrime.isMaximal P.ne_bot).coprime_of_ne
            (Q.isPrime.isMaximal Q.ne_bot) hPQideal
        have hxMul :
            x ∈ P.asIdeal * Q.asIdeal := by
          rw [Ideal.mul_eq_inf_of_coprime hcoprime]
          exact ⟨hxP, hxQ⟩
        have hAQdiv : A * Qelt ∣ x := by
          rw [← Ideal.mem_span_singleton,
            ← Ideal.span_singleton_mul_span_singleton,
            ← hPgen, ← hQgen]
          exact hxMul
        simpa [hrN, hqN] using hAQdiv
  have hcorrect0 :
      A ^ rN * Qelt ^ qN ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hA0)
      (pow_ne_zero _ hQ0)
  have hparity :
      ∀ R : HeightOneSpectrum O,
        Even
          (principalCount (L := L) R x -
            principalCount (L := L) R
              (A ^ rN * Qelt ^ qN)) := by
    intro R
    have hcountCorrection :
        principalCount (L := L) R
            (A ^ rN * Qelt ^ qN) =
          (rN : ℤ) *
              principalCount (L := L) R A +
            (qN : ℤ) *
              principalCount (L := L) R Qelt := by
      rw [principalCount_mul
          (pow_ne_zero _ hA0) (pow_ne_zero _ hQ0),
        principalCount_pow, principalCount_pow]
    by_cases hRP : R = P
    · subst R
      have hQP : P ≠ Q := hPQ
      rw [hcountCorrection,
        principalCount_generator_self P hPgen hA0,
        principalCount_generator_of_ne
          Q P hQgen hQ0 hQP]
      rw [principalCount_eq_factorization_span
        x hx P]
      change Even ((nP : ℤ) - ((rN : ℤ) * 1 + (qN : ℤ) * 0))
      refine ⟨(nP / 2 : ℕ), ?_⟩
      have hdivmod := Nat.mod_add_div nP 2
      dsimp only [rN]
      omega
    · by_cases hRQ : R = Q
      · subst R
        have hPQ' : Q ≠ P := Ne.symm hPQ
        rw [hcountCorrection,
          principalCount_generator_of_ne
            P Q hPgen hA0 hPQ',
          principalCount_generator_self Q hQgen hQ0]
        rw [principalCount_eq_factorization_span
          x hx Q]
        change Even ((nQ : ℤ) - ((rN : ℤ) * 0 + (qN : ℤ) * 1))
        refine ⟨(nQ / 2 : ℕ), ?_⟩
        have hdivmod := Nat.mod_add_div nQ 2
        dsimp only [qN]
        omega
      · rw [hcountCorrection,
          principalCount_generator_of_ne
            P R hPgen hA0 hRP,
          principalCount_generator_of_ne
            Q R hQgen hQ0 hRQ]
        simpa using hAway R hRP hRQ
  obtain ⟨ε, y, hxy⟩ :=
    exists_unit_mul_correction_mul_sq
      (L := L)
      (A ^ rN * Qelt ^ qN) x
      hcorrect0 hx hdiv hparity
  let r : ZMod 2 := rN
  let q : ZMod 2 := qN
  have hrval : r.val = rN := by
    exact ZMod.val_cast_of_lt hrN_lt
  have hqval : q.val = qN := by
    exact ZMod.val_cast_of_lt hqN_lt
  refine ⟨r, q, ε, y, ?_⟩
  simpa only [hrval, hqval, mul_assoc] using hxy


end MazurProof.ExceptionalPrincipalIdeal
end
end
end

-- module FLT.Assumptions.MazurProof.GeneralizedGraphIdealCore
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.GeneralizedGraphIdealCore =====
section

/-!
# Graph ideals on a generalized quadratic curve

Let `A` be an algebra generated by a horizontal coordinate map
`R[X] → A` and an ordinate `y` satisfying

`y² + h(x)y = rhs(x)`.

For a polynomial graph `y = v(x)` whose residual curve equation is
`v² + hv - rhs = uw`, the graph ideal and its hyperelliptic conjugate
multiply to the principal ideal `(u)`, provided the displayed generalized
Jacobian admits a Bézout identity.  The proof is purely ring-theoretic and
works over an arbitrary commutative base ring.
-/

open Polynomial

namespace MazurProof.GeneralizedGraphIdealCore

noncomputable section

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

set_option maxHeartbeats 4000000 in
/-- Polynomial graph data on `y² + hy = rhs`. -/
structure SemiGraph (h rhs : R[X]) where
  u : R[X]
  v : R[X]
  w : R[X]
  curve_eq : v ^ 2 + h * v - rhs = u * w

/-- Hyperelliptic conjugation on graph ordinates. -/
def conjugateV (h v : R[X]) : R[X] :=
  -h - v

def ySubClass
    (xClass : R[X] →+* A) (yClass : A) (v : R[X]) : A :=
  yClass - xClass v

def graphIdeal
    (xClass : R[X] →+* A) (yClass : A) (u v : R[X]) :
    Ideal A :=
  Ideal.span {xClass u, ySubClass xClass yClass v}

theorem xClass_mem_graphIdeal
    (xClass : R[X] →+* A) (yClass : A) (u v : R[X]) :
    xClass u ∈ graphIdeal xClass yClass u v :=
  Ideal.subset_span (by simp)

theorem ySubClass_mem_graphIdeal
    (xClass : R[X] →+* A) (yClass : A) (u v : R[X]) :
    ySubClass xClass yClass v ∈ graphIdeal xClass yClass u v :=
  Ideal.subset_span (by simp)

/-- Multiplying the horizontal equation by a factor whose image is a unit
does not change the graph ideal. -/
theorem graphIdeal_mul_left_eq_of_isUnit
    (xClass : R[X] →+* A) (yClass : A)
    (c u v : R[X]) (hc : IsUnit (xClass c)) :
    graphIdeal xClass yClass (c * u) v =
      graphIdeal xClass yClass u v := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · rw [map_mul]
      exact Ideal.mul_mem_left _
        (xClass c) (xClass_mem_graphIdeal xClass yClass u v)
    · exact ySubClass_mem_graphIdeal xClass yClass u v
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · obtain ⟨d, hdc⟩ := isUnit_iff_exists_inv.mp hc
      have hdc' : d * xClass c = 1 := by
        simpa [mul_comm] using hdc
      have hcu :
          xClass (c * u) ∈
            graphIdeal xClass yClass (c * u) v :=
        xClass_mem_graphIdeal xClass yClass (c * u) v
      have hdcu :=
        Ideal.mul_mem_left
          (graphIdeal xClass yClass (c * u) v) d hcu
      rw [map_mul] at hdcu
      simpa [← mul_assoc, hdc'] using hdcu
    · exact ySubClass_mem_graphIdeal xClass yClass (c * u) v

/-- Replacing the graph ordinate by a congruent polynomial modulo the
horizontal equation does not change the graph ideal. -/
theorem graphIdeal_eq_of_dvd_sub
    (xClass : R[X] →+* A) (yClass : A)
    (u v V : R[X]) (h : u ∣ V - v) :
    graphIdeal xClass yClass u V =
      graphIdeal xClass yClass u v := by
  obtain ⟨t, ht⟩ := h
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_graphIdeal xClass yClass u v
    · have hmultiple :
          xClass (V - v) ∈ graphIdeal xClass yClass u v := by
        rw [ht, map_mul, mul_comm]
        exact Ideal.mul_mem_left _
          (xClass t) (xClass_mem_graphIdeal xClass yClass u v)
      have heq :
          ySubClass xClass yClass V =
            ySubClass xClass yClass v - xClass (V - v) := by
        simp [ySubClass, map_sub]
      rw [heq]
      exact Ideal.sub_mem _
        (ySubClass_mem_graphIdeal xClass yClass u v) hmultiple
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_graphIdeal xClass yClass u V
    · have hmultiple :
          xClass (V - v) ∈ graphIdeal xClass yClass u V := by
        rw [ht, map_mul, mul_comm]
        exact Ideal.mul_mem_left _
          (xClass t) (xClass_mem_graphIdeal xClass yClass u V)
      have heq :
          ySubClass xClass yClass v =
            ySubClass xClass yClass V + xClass (V - v) := by
        simp [ySubClass, map_sub]
      rw [heq]
      exact Ideal.add_mem _
        (ySubClass_mem_graphIdeal xClass yClass u V) hmultiple

/-- Two graph ideals with coprime horizontal equations multiply to the
graph ideal of the product.  The common ordinate is only required modulo
the two factors, so this is the ideal-theoretic Chinese remainder theorem
for a split divisor. -/
theorem graphIdeal_mul_of_coprime
    (xClass : R[X] →+* A) (yClass : A)
    (u₁ u₂ v₁ v₂ V : R[X])
    (h₁ : u₁ ∣ V - v₁)
    (h₂ : u₂ ∣ V - v₂)
    (hcoprime :
      ∃ a b : R[X], a * u₁ + b * u₂ = 1) :
    graphIdeal xClass yClass u₁ v₁ *
        graphIdeal xClass yClass u₂ v₂ =
      graphIdeal xClass yClass (u₁ * u₂) V := by
  rw [← graphIdeal_eq_of_dvd_sub xClass yClass u₁ v₁ V h₁,
    ← graphIdeal_eq_of_dvd_sub xClass yClass u₂ v₂ V h₂]
  let I₁ := graphIdeal xClass yClass u₁ V
  let I₂ := graphIdeal xClass yClass u₂ V
  let I := graphIdeal xClass yClass (u₁ * u₂) V
  let g := ySubClass xClass yClass V
  apply le_antisymm
  · rw [graphIdeal, graphIdeal, graphIdeal,
      Ideal.span_pair_mul_span_pair]
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Ideal.subset_span (by simp [map_mul])
    · exact Ideal.mul_mem_left I (xClass u₁)
        (ySubClass_mem_graphIdeal xClass yClass (u₁ * u₂) V)
    · exact Ideal.mul_mem_right (xClass u₂) _
        (Ideal.subset_span
          (Set.mem_insert_iff.mpr
            (Or.inr (Set.mem_singleton _))))
    · exact Ideal.mul_mem_left I g
        (ySubClass_mem_graphIdeal xClass yClass (u₁ * u₂) V)
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · rw [map_mul]
      exact Ideal.mul_mem_mul
        (xClass_mem_graphIdeal xClass yClass u₁ V)
        (xClass_mem_graphIdeal xClass yClass u₂ V)
    · obtain ⟨a, b, hab⟩ := hcoprime
      have h₁g :
          xClass u₁ * g ∈ I₁ * I₂ :=
        Ideal.mul_mem_mul
          (xClass_mem_graphIdeal xClass yClass u₁ V)
          (ySubClass_mem_graphIdeal xClass yClass u₂ V)
      have hg₂ :
          g * xClass u₂ ∈ I₁ * I₂ :=
        Ideal.mul_mem_mul
          (ySubClass_mem_graphIdeal xClass yClass u₁ V)
          (xClass_mem_graphIdeal xClass yClass u₂ V)
      have ha :
          xClass a * (xClass u₁ * g) ∈ I₁ * I₂ :=
        Ideal.mul_mem_left _ (xClass a) h₁g
      have hb :
          xClass b * (g * xClass u₂) ∈ I₁ * I₂ :=
        Ideal.mul_mem_left _ (xClass b) hg₂
      have hsum := Ideal.add_mem (I₁ * I₂) ha hb
      have heq :
          xClass a * (xClass u₁ * g) +
              xClass b * (g * xClass u₂) = g := by
        calc
          _ = xClass (a * u₁ + b * u₂) * g := by
            simp only [map_add, map_mul]
            ring
          _ = g := by rw [hab, map_one, one_mul]
      rw [heq] at hsum
      exact hsum

/-- The product of the two raw graph functions is the negative substituted
curve equation. -/
theorem ySubClass_mul_conjugateV_raw
    (xClass : R[X] →+* A) (yClass : A) (h rhs v : R[X])
    (hy : yClass ^ 2 + xClass h * yClass = xClass rhs) :
    ySubClass xClass yClass v *
        ySubClass xClass yClass (conjugateV h v) =
      -xClass (v ^ 2 + h * v - rhs) := by
  calc
    ySubClass xClass yClass v *
          ySubClass xClass yClass (conjugateV h v) =
        yClass ^ 2 + xClass h * yClass -
          (xClass v ^ 2 + xClass h * xClass v) := by
      simp only [ySubClass, conjugateV, map_neg, map_sub]
      ring
    _ = xClass rhs - xClass (v ^ 2 + h * v) := by
      rw [hy, map_add, map_mul, map_pow]
    _ = -xClass (v ^ 2 + h * v - rhs) := by
      rw [map_sub]
      ring

theorem ySubClass_mul_conjugate
    (xClass : R[X] →+* A) (yClass : A) (h rhs : R[X])
    (D : SemiGraph h rhs)
    (hy : yClass ^ 2 + xClass h * yClass = xClass rhs) :
    ySubClass xClass yClass D.v *
        ySubClass xClass yClass (conjugateV h D.v) =
      -(xClass D.u * xClass D.w) := by
  calc
    ySubClass xClass yClass D.v *
          ySubClass xClass yClass (conjugateV h D.v) =
        -xClass (D.v ^ 2 + h * D.v - rhs) :=
      ySubClass_mul_conjugateV_raw xClass yClass h rhs D.v hy
    _ = -xClass (D.u * D.w) := by rw [D.curve_eq]
    _ = -(xClass D.u * xClass D.w) := by rw [map_mul]

/-- A generalized graph and its hyperelliptic conjugate multiply to `(u)`.
The only regularity input is the explicit Bézout identity for
`u`, `2v+h`, and `w`. -/
theorem graphIdeal_mul_conj
    (xClass : R[X] →+* A) (yClass : A) (h rhs : R[X])
    (D : SemiGraph h rhs)
    (hy : yClass ^ 2 + xClass h * yClass = xClass rhs)
    (hbez :
      ∃ a b c : R[X],
        a * D.u + b * (2 * D.v + h) + c * D.w = 1) :
    graphIdeal xClass yClass D.u D.v *
        graphIdeal xClass yClass D.u (conjugateV h D.v) =
      Ideal.span ({xClass D.u} : Set A) := by
  let I := graphIdeal xClass yClass D.u D.v
  let J :=
    graphIdeal xClass yClass D.u (conjugateV h D.v)
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro p hp q hq
    rw [Ideal.mem_span_singleton]
    obtain ⟨p₀, pY, hpEq⟩ := Ideal.mem_span_pair.mp hp
    obtain ⟨q₀, qY, hqEq⟩ := Ideal.mem_span_pair.mp hq
    refine
      ⟨p₀ * q₀ * xClass D.u +
          p₀ * qY *
            ySubClass xClass yClass (conjugateV h D.v) +
          pY * q₀ * ySubClass xClass yClass D.v -
          pY * qY * xClass D.w,
        ?_⟩
    rw [← hpEq, ← hqEq]
    linear_combination
      pY * qY *
        ySubClass_mul_conjugate xClass yClass h rhs D hy
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨a, b, c, habc⟩ := hbez
    have huI : xClass D.u ∈ I :=
      xClass_mem_graphIdeal xClass yClass D.u D.v
    have huJ : xClass D.u ∈ J :=
      xClass_mem_graphIdeal xClass yClass D.u
        (conjugateV h D.v)
    have hvI : ySubClass xClass yClass D.v ∈ I :=
      ySubClass_mem_graphIdeal xClass yClass D.u D.v
    have hvJ :
        ySubClass xClass yClass (conjugateV h D.v) ∈ J :=
      ySubClass_mem_graphIdeal xClass yClass D.u
        (conjugateV h D.v)
    have hu2 : xClass D.u * xClass D.u ∈ I * J :=
      Ideal.mul_mem_mul huI huJ
    have huv : xClass D.u * xClass (2 * D.v + h) ∈ I * J := by
      have hp :
          xClass D.u *
              ySubClass xClass yClass (conjugateV h D.v) ∈ I * J :=
        Ideal.mul_mem_mul huI hvJ
      have hm :
          ySubClass xClass yClass D.v * xClass D.u ∈ I * J :=
        Ideal.mul_mem_mul hvI huJ
      have hd := Ideal.sub_mem (I * J) hp hm
      convert hd using 1
      simp only [two_mul, ySubClass, conjugateV, map_neg, map_sub,
        map_add]
      ring
    have huw : xClass D.u * xClass D.w ∈ I * J := by
      have hg :
          ySubClass xClass yClass D.v *
              ySubClass xClass yClass (conjugateV h D.v) ∈ I * J :=
        Ideal.mul_mem_mul hvI hvJ
      have hneg := (I * J).neg_mem hg
      rw [ySubClass_mul_conjugate xClass yClass h rhs D hy] at hneg
      simpa using hneg
    have ha :
        xClass a * (xClass D.u * xClass D.u) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass a) hu2
    have hb :
        xClass b * (xClass D.u * xClass (2 * D.v + h)) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass b) huv
    have hc :
        xClass c * (xClass D.u * xClass D.w) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass c) huw
    have hsum :=
      Ideal.add_mem (I * J) (Ideal.add_mem (I * J) ha hb) hc
    have heq :
        xClass a * (xClass D.u * xClass D.u) +
            xClass b * (xClass D.u * xClass (2 * D.v + h)) +
            xClass c * (xClass D.u * xClass D.w) =
          xClass D.u := by
      calc
        _ = xClass D.u *
            xClass
              (a * D.u + b * (2 * D.v + h) + c * D.w) := by
          simp only [two_mul, map_add, map_mul]
          ring
        _ = xClass D.u * 1 := by rw [habc, map_one]
        _ = xClass D.u := mul_one _
    rw [heq] at hsum
    exact hsum

end

end MazurProof.GeneralizedGraphIdealCore

end
end

-- module FLT.Assumptions.MazurProof.GraphJacobianDecompositionFrame
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.GraphJacobianDecompositionFrame =====
section

open scoped nonZeroDivisors

/-!
# A decomposition form of the graph-Jacobian dual frame

For a two-generated ideal `(U,G)`, a complementary factorization
`G H = -U W` puts both integral scalars and integral multiples of
`-H/U` in the inverse ideal.  Arbitrary decompositions of two Jacobian
rows in the four elements `U,G,H,W`, together with a global Bézout
identity, therefore give an explicit dual frame.
-/

namespace MazurProof.GraphJacobianDecompositionFrame

noncomputable section

variable {A K : Type*}
variable [CommRing A] [IsDomain A]
variable [Field K] [Algebra A K] [IsFractionRing A K]

theorem graphJacobian_isUnit_of_decompositions
    (U G H W Fx Fy
      αx βx γx δx αy βy γy δy a b : A)
    (hU : U ≠ 0)
    (hGH : G * H = -(U * W))
    (hFx :
      Fx = U * αx + G * βx + H * γx + W * δx)
    (hFy :
      Fy = U * αy + G * βy + H * γy + W * δy)
    (hBez : a * Fx + b * Fy = 1) :
    IsUnit
      ((Ideal.span ({U, G} : Set A) : Ideal A) :
        FractionalIdeal A⁰ K) := by
  let M : Ideal A :=
    Ideal.span ({U, G} : Set A)
  let I : FractionalIdeal A⁰ K :=
    (M : FractionalIdeal A⁰ K)
  have hU_M : U ∈ M := by
    exact Ideal.subset_span (by simp)
  have hG_M : G ∈ M := by
    exact Ideal.subset_span (by simp)
  have hU_I : algebraMap A K U ∈ I := by
    simpa only [I] using
      (FractionalIdeal.mem_coeIdeal_of_mem A⁰ hU_M)
  have hG_I : algebraMap A K G ∈ I := by
    simpa only [I] using
      (FractionalIdeal.mem_coeIdeal_of_mem A⁰ hG_M)
  have hI_le_one : I ≤ 1 := by
    exact FractionalIdeal.coeIdeal_le_one
  have hI_ne : I ≠ 0 := by
    intro hI0
    have hmapU0 : algebraMap A K U = 0 :=
      (FractionalIdeal.eq_zero_iff.mp hI0)
        (algebraMap A K U) hU_I
    exact hU
      (IsFractionRing.to_map_eq_zero_iff.mp hmapU0)
  have hmapU_ne : algebraMap A K U ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective A K).ne hU
  have hGHK :
      algebraMap A K G * algebraMap A K H =
        -(algebraMap A K U * algebraMap A K W) := by
    simpa only [map_mul, map_neg] using
      congrArg (algebraMap A K) hGH
  let z : K :=
    -algebraMap A K H / algebraMap A K U
  have hzU :
      z * algebraMap A K U =
        -algebraMap A K H := by
    dsimp only [z]
    field_simp [hmapU_ne]
  have hzG :
      z * algebraMap A K G =
        algebraMap A K W := by
    calc
      z * algebraMap A K G =
          -(algebraMap A K H *
              algebraMap A K G) /
            algebraMap A K U := by
              dsimp only [z]
              ring
      _ =
          -(algebraMap A K G *
              algebraMap A K H) /
            algebraMap A K U := by ring
      _ =
          -(-(algebraMap A K U *
              algebraMap A K W)) /
            algebraMap A K U := by rw [hGHK]
      _ = algebraMap A K W := by
            field_simp [hmapU_ne]
  have hz_mem : z ∈ I⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hI_ne]
    intro y hy
    change y ∈ (M : FractionalIdeal A⁰ K) at hy
    rw [FractionalIdeal.mem_coeIdeal A⁰] at hy
    obtain ⟨yA, hyA, hyEq⟩ := hy
    subst y
    obtain ⟨c, d, hcd⟩ :=
      Ideal.mem_span_pair.mp
        (by simpa only [M] using hyA)
    rw [FractionalIdeal.mem_one_iff A⁰]
    refine ⟨-c * H + d * W, ?_⟩
    calc
      algebraMap A K (-c * H + d * W) =
          algebraMap A K c *
              (-algebraMap A K H) +
            algebraMap A K d *
              algebraMap A K W := by
                simp only [map_add, map_mul, map_neg]
                ring
      _ =
          algebraMap A K c *
              (z * algebraMap A K U) +
            algebraMap A K d *
              (z * algebraMap A K G) := by
                rw [← hzU, ← hzG]
      _ =
          z * algebraMap A K
            (c * U + d * G) := by
              simp only [map_add, map_mul]
              ring
      _ = z * algebraMap A K yA := by rw [hcd]
  have hone_inv : (1 : K) ∈ I⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hI_ne]
    intro y hy
    simpa only [one_mul] using hI_le_one hy
  have hIntegral (r : A) :
      algebraMap A K r ∈ I⁻¹ := by
    have hr :=
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).smul_mem r hone_inv)
    simpa only [FractionalIdeal.mem_coe,
      Algebra.smul_def, mul_one] using hr
  have hScalarZ (r : A) :
      algebraMap A K r * z ∈ I⁻¹ := by
    have hr :=
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).smul_mem r hz_mem)
    simpa only [FractionalIdeal.mem_coe,
      Algebra.smul_def] using hr
  let ux : K :=
    algebraMap A K αx - algebraMap A K γx * z
  let gx : K :=
    algebraMap A K βx + algebraMap A K δx * z
  let uy : K :=
    algebraMap A K αy - algebraMap A K γy * z
  let gy : K :=
    algebraMap A K βy + algebraMap A K δy * z
  have hux : ux ∈ I⁻¹ := by
    exact
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).sub_mem
          (hIntegral αx) (hScalarZ γx))
  have hgx : gx ∈ I⁻¹ := by
    exact
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
          (hIntegral βx) (hScalarZ δx))
  have huy : uy ∈ I⁻¹ := by
    exact
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).sub_mem
          (hIntegral αy) (hScalarZ γy))
  have hgy : gy ∈ I⁻¹ := by
    exact
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
          (hIntegral βy) (hScalarZ δy))
  have hHK :
      algebraMap A K H =
        -(z * algebraMap A K U) := by
    rw [hzU]
    ring
  have hWK :
      algebraMap A K W =
        z * algebraMap A K G :=
    hzG.symm
  have hFxK :
      algebraMap A K Fx =
        algebraMap A K U * ux +
          algebraMap A K G * gx := by
    rw [hFx]
    simp only [map_add, map_mul, ux, gx]
    rw [hHK, hWK]
    ring
  have hFyK :
      algebraMap A K Fy =
        algebraMap A K U * uy +
          algebraMap A K G * gy := by
    rw [hFy]
    simp only [map_add, map_mul, uy, gy]
    rw [hHK, hWK]
    ring
  let tU : K :=
    algebraMap A K a * ux +
      algebraMap A K b * uy
  let tG : K :=
    algebraMap A K a * gx +
      algebraMap A K b * gy
  have htU : tU ∈ I⁻¹ := by
    simpa only [FractionalIdeal.mem_coe,
      Algebra.smul_def, tU] using
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
          (((I⁻¹ : FractionalIdeal A⁰ K) :
            Submodule A K).smul_mem a hux)
          (((I⁻¹ : FractionalIdeal A⁰ K) :
            Submodule A K).smul_mem b huy))
  have htG : tG ∈ I⁻¹ := by
    simpa only [FractionalIdeal.mem_coe,
      Algebra.smul_def, tG] using
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
          (((I⁻¹ : FractionalIdeal A⁰ K) :
            Submodule A K).smul_mem a hgx)
          (((I⁻¹ : FractionalIdeal A⁰ K) :
            Submodule A K).smul_mem b hgy))
  have hBezK :
      algebraMap A K a *
            algebraMap A K Fx +
          algebraMap A K b *
            algebraMap A K Fy = 1 := by
    simpa only [map_add, map_mul, map_one] using
      congrArg (algebraMap A K) hBez
  have hframe :
      algebraMap A K U * tU +
          algebraMap A K G * tG = 1 := by
    calc
      algebraMap A K U * tU +
            algebraMap A K G * tG =
          algebraMap A K a *
              (algebraMap A K U * ux +
                algebraMap A K G * gx) +
            algebraMap A K b *
              (algebraMap A K U * uy +
                algebraMap A K G * gy) := by
          dsimp only [tU, tG]
          ring
      _ =
          algebraMap A K a * algebraMap A K Fx +
            algebraMap A K b * algebraMap A K Fy := by
        rw [← hFxK, ← hFyK]
      _ = 1 := hBezK
  have hmul_le : I * I⁻¹ ≤ 1 := by
    rw [FractionalIdeal.mul_le]
    intro x hx y hy
    have hxy :=
      (FractionalIdeal.mem_inv_iff hI_ne).mp
        hy x hx
    simpa only [mul_comm] using hxy
  have hone_le : 1 ≤ I * I⁻¹ := by
    rw [FractionalIdeal.one_le, ← hframe]
    simpa only [FractionalIdeal.mem_coe] using
      (((I * I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
          (FractionalIdeal.mul_mem_mul hU_I htU)
          (FractionalIdeal.mul_mem_mul hG_I htG))
  have hmul_eq : I * I⁻¹ = 1 :=
    le_antisymm hmul_le hone_le
  exact
    (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mp hmul_eq

end

end MazurProof.GraphJacobianDecompositionFrame

end
end

-- module FLT.Assumptions.MazurProof.GraphJacobianDualFrame
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.GraphJacobianDualFrame =====
section

/-!
# A Jacobian dual frame for a graph ideal

For a graph ideal `(U,G)`, the factorization

`G * Gbar = -(U * W)`

places `-Gbar/U` in the multiplier inverse.  If two Jacobian rows generate
one, their graph decompositions then give an explicit two-term dual frame.
This proves invertibility without Noetherian, regular-local, divisor-class,
or special-fibre arguments.
-/

open scoped nonZeroDivisors

namespace MazurProof.GraphJacobianDualFrame

noncomputable section

variable {A K : Type*}
variable [CommRing A] [IsDomain A]
variable [Field K] [Algebra A K] [IsFractionRing A K]

/-- A graph factorization and a global Jacobian Bézout identity produce an
explicit dual frame, hence an invertible graph fractional ideal. -/
theorem graphJacobian_isUnit
    (U G Gbar W Fy Fx Ux Wx Vx hx a b : A)
    (hU : U ≠ 0)
    (hGGbar : G * Gbar = -(U * W))
    (hFy : Fy = G + Gbar)
    (hFx :
      Fx =
        Ux * W + U * Wx - Vx * Gbar +
          (hx + Vx) * G)
    (hBez : a * Fx + b * Fy = 1) :
    IsUnit
      ((Ideal.span ({U, G} : Set A) : Ideal A) :
        FractionalIdeal A⁰ K) := by
  let M : Ideal A :=
    Ideal.span ({U, G} : Set A)
  let I : FractionalIdeal A⁰ K :=
    (M : FractionalIdeal A⁰ K)
  have hU_M : U ∈ M := by
    dsimp only [M]
    exact Ideal.subset_span (by simp)
  have hG_M : G ∈ M := by
    dsimp only [M]
    exact Ideal.subset_span (by simp)
  have hU_I : algebraMap A K U ∈ I := by
    simpa only [I] using
      (FractionalIdeal.mem_coeIdeal_of_mem A⁰ hU_M)
  have hG_I : algebraMap A K G ∈ I := by
    simpa only [I] using
      (FractionalIdeal.mem_coeIdeal_of_mem A⁰ hG_M)
  have hI_le_one : I ≤ 1 := by
    dsimp only [I]
    exact FractionalIdeal.coeIdeal_le_one
  have hI_ne : I ≠ 0 := by
    intro hI0
    have hmapU0 : algebraMap A K U = 0 :=
      (FractionalIdeal.eq_zero_iff.mp hI0)
        (algebraMap A K U) hU_I
    exact hU
      (IsFractionRing.to_map_eq_zero_iff.mp hmapU0)
  have hmapU_ne : algebraMap A K U ≠ 0 := by
    intro hmapU0
    exact hU
      (IsFractionRing.to_map_eq_zero_iff.mp hmapU0)
  have hGGbarK :
      algebraMap A K G * algebraMap A K Gbar =
        -(algebraMap A K U * algebraMap A K W) := by
    simpa only [map_mul, map_neg] using
      congrArg (algebraMap A K) hGGbar
  let z : K :=
    -algebraMap A K Gbar / algebraMap A K U
  have hzU :
      z * algebraMap A K U =
        -algebraMap A K Gbar := by
    dsimp only [z]
    field_simp [hmapU_ne]
  have hzG :
      z * algebraMap A K G =
        algebraMap A K W := by
    calc
      z * algebraMap A K G =
          -(algebraMap A K Gbar *
              algebraMap A K G) /
            algebraMap A K U := by
              dsimp only [z]
              ring
      _ =
          -(algebraMap A K G *
              algebraMap A K Gbar) /
            algebraMap A K U := by
              ring
      _ =
          -(-(algebraMap A K U *
              algebraMap A K W)) /
            algebraMap A K U := by
              rw [hGGbarK]
      _ = algebraMap A K W := by
            field_simp [hmapU_ne]
  have hz_mem : z ∈ I⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hI_ne]
    intro y hy
    change
      y ∈ (M : FractionalIdeal A⁰ K) at hy
    rw [FractionalIdeal.mem_coeIdeal A⁰] at hy
    obtain ⟨yA, hyA, hyEq⟩ := hy
    subst y
    obtain ⟨c, d, hcd⟩ :=
      Ideal.mem_span_pair.mp
        (by simpa only [M] using hyA)
    rw [FractionalIdeal.mem_one_iff A⁰]
    refine ⟨-c * Gbar + d * W, ?_⟩
    calc
      algebraMap A K (-c * Gbar + d * W) =
          algebraMap A K c *
              (-algebraMap A K Gbar) +
            algebraMap A K d *
              algebraMap A K W := by
                simp only [map_add, map_mul, map_neg]
                ring
      _ =
          algebraMap A K c *
              (z * algebraMap A K U) +
            algebraMap A K d *
              (z * algebraMap A K G) := by
                rw [← hzU, ← hzG]
      _ =
          z * algebraMap A K
            (c * U + d * G) := by
              simp only [map_add, map_mul]
              ring
      _ = z * algebraMap A K yA := by
            rw [hcd]
  have hone_inv : (1 : K) ∈ I⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hI_ne]
    intro y hy
    simpa only [one_mul] using hI_le_one hy
  have hIntegral (r : A) :
      algebraMap A K r ∈ I⁻¹ := by
    have hr :=
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).smul_mem r hone_inv)
    simpa only [FractionalIdeal.mem_coe,
      Algebra.smul_def, mul_one] using hr
  have hScalarZ (r : A) :
      algebraMap A K r * z ∈ I⁻¹ := by
    have hr :=
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).smul_mem r hz_mem)
    simpa only [FractionalIdeal.mem_coe,
      Algebra.smul_def] using hr
  let tU : K :=
    algebraMap A K a *
        (algebraMap A K Wx +
          algebraMap A K Vx * z) -
      algebraMap A K b * z
  let tG : K :=
    algebraMap A K a *
        (algebraMap A K Ux * z +
          algebraMap A K hx +
          algebraMap A K Vx) +
      algebraMap A K b
  have htU : tU ∈ I⁻¹ := by
    have hinner :
        algebraMap A K Wx +
            algebraMap A K Vx * z ∈ I⁻¹ :=
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
        (hIntegral Wx) (hScalarZ Vx))
    have hscaled :
        algebraMap A K a *
            (algebraMap A K Wx +
              algebraMap A K Vx * z) ∈ I⁻¹ := by
      simpa only [FractionalIdeal.mem_coe,
        Algebra.smul_def] using
        (((I⁻¹ : FractionalIdeal A⁰ K) :
          Submodule A K).smul_mem a hinner)
    simpa only [FractionalIdeal.mem_coe, tU] using
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).sub_mem
        hscaled (hScalarZ b))
  have htG : tG ∈ I⁻¹ := by
    have hinner :
        algebraMap A K Ux * z +
            algebraMap A K hx +
            algebraMap A K Vx ∈ I⁻¹ :=
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
        (((I⁻¹ : FractionalIdeal A⁰ K) :
          Submodule A K).add_mem
          (hScalarZ Ux) (hIntegral hx))
        (hIntegral Vx))
    have hscaled :
        algebraMap A K a *
            (algebraMap A K Ux * z +
              algebraMap A K hx +
              algebraMap A K Vx) ∈ I⁻¹ := by
      simpa only [FractionalIdeal.mem_coe,
        Algebra.smul_def] using
        (((I⁻¹ : FractionalIdeal A⁰ K) :
          Submodule A K).smul_mem a hinner)
    simpa only [FractionalIdeal.mem_coe, tG] using
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
        hscaled (hIntegral b))
  have hGbarK :
      algebraMap A K Gbar =
        -(z * algebraMap A K U) := by
    rw [hzU]
    ring
  have hWK :
      algebraMap A K W =
        z * algebraMap A K G :=
    hzG.symm
  have hFxK :
      algebraMap A K Fx =
        algebraMap A K Ux * algebraMap A K W +
          algebraMap A K U * algebraMap A K Wx -
          algebraMap A K Vx *
            algebraMap A K Gbar +
          (algebraMap A K hx +
              algebraMap A K Vx) *
            algebraMap A K G := by
    simpa only [map_add, map_sub, map_mul] using
      congrArg (algebraMap A K) hFx
  have hFx_decomp :
      algebraMap A K Fx =
        algebraMap A K U *
            (algebraMap A K Wx +
              algebraMap A K Vx * z) +
          algebraMap A K G *
            (algebraMap A K Ux * z +
              algebraMap A K hx +
              algebraMap A K Vx) := by
    calc
      algebraMap A K Fx =
          algebraMap A K Ux *
              algebraMap A K W +
            algebraMap A K U *
              algebraMap A K Wx -
            algebraMap A K Vx *
              algebraMap A K Gbar +
            (algebraMap A K hx +
                algebraMap A K Vx) *
              algebraMap A K G :=
        hFxK
      _ =
          algebraMap A K U *
              (algebraMap A K Wx +
                algebraMap A K Vx * z) +
            algebraMap A K G *
              (algebraMap A K Ux * z +
                algebraMap A K hx +
                algebraMap A K Vx) := by
              rw [hWK, hGbarK]
              ring
  have hFyK :
      algebraMap A K Fy =
        algebraMap A K G +
          algebraMap A K Gbar := by
    simpa only [map_add] using
      congrArg (algebraMap A K) hFy
  have hFy_decomp :
      algebraMap A K Fy =
        algebraMap A K U * (-z) +
          algebraMap A K G := by
    calc
      algebraMap A K Fy =
          algebraMap A K G +
            algebraMap A K Gbar :=
        hFyK
      _ =
          algebraMap A K U * (-z) +
            algebraMap A K G := by
              rw [hGbarK]
              ring
  have hBezK :
      algebraMap A K a *
            algebraMap A K Fx +
          algebraMap A K b *
            algebraMap A K Fy = 1 := by
    simpa only [map_add, map_mul, map_one] using
      congrArg (algebraMap A K) hBez
  have hframe :
      algebraMap A K U * tU +
          algebraMap A K G * tG = 1 := by
    calc
      algebraMap A K U * tU +
            algebraMap A K G * tG =
          algebraMap A K a *
              (algebraMap A K U *
                  (algebraMap A K Wx +
                    algebraMap A K Vx * z) +
                algebraMap A K G *
                  (algebraMap A K Ux * z +
                    algebraMap A K hx +
                    algebraMap A K Vx)) +
            algebraMap A K b *
              (algebraMap A K U * (-z) +
                algebraMap A K G) := by
                dsimp only [tU, tG]
                ring
      _ =
          algebraMap A K a *
              algebraMap A K Fx +
            algebraMap A K b *
              algebraMap A K Fy := by
                rw [← hFx_decomp, ← hFy_decomp]
      _ = 1 := hBezK
  have hmul_le : I * I⁻¹ ≤ 1 := by
    rw [FractionalIdeal.mul_le]
    intro x hx y hy
    have hxy :=
      (FractionalIdeal.mem_inv_iff hI_ne).mp
        hy x hx
    simpa only [mul_comm] using hxy
  have hone_le : 1 ≤ I * I⁻¹ := by
    rw [FractionalIdeal.one_le, ← hframe]
    simpa only [FractionalIdeal.mem_coe] using
      (((I * I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
          (FractionalIdeal.mul_mem_mul hU_I htU)
          (FractionalIdeal.mul_mem_mul hG_I htG))
  have hmul_eq : I * I⁻¹ = 1 :=
    le_antisymm hmul_le hone_le
  have hunitI : IsUnit I :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mp
      hmul_eq
  simpa only [I, M] using hunitI

end

end MazurProof.GraphJacobianDualFrame

end
end

-- module FLT.Assumptions.MazurProof.IntegralClosureOfEisensteinDiscr
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.IntegralClosureOfEisensteinDiscr =====
section

/-!
# A discriminant--Eisenstein criterion for a monogenic integral closure

Let `R` be an integrally closed domain with fraction field `K`, and let
`L / K` have an integral power basis generated by `θ`.  If the discriminant
of that basis is a power of a prime `p` and the minimal polynomial of `θ`
is Eisenstein at `p`, then every element of the integral closure belongs to
`R[θ]`.

The proof has two structural steps.  The trace discriminant first puts
`p ^ n • z` in `R[θ]`; Eisenstein denominator removal then divides out the
entire power of `p`.  There is no local valuation enumeration.
-/

open Algebra Polynomial

namespace MazurProof

noncomputable section

universe u v w

theorem integralClosure_eq_adjoin_of_discr_eq_prime_pow
    {R : Type u} {K : Type v} {L : Type w}
    [CommRing R] [Field K] [Field L]
    [Algebra R K] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L]
    [IsDomain R] [IsIntegrallyClosed R] [IsFractionRing R K]
    [Module.Finite K L] [Algebra.IsSeparable K L]
    {B : PowerBasis K L}
    {p : R} {n : ℕ}
    (hp : Prime p)
    (hBint : IsIntegral R B.gen)
    (hdisc : Algebra.discr K B.basis = algebraMap R K (p ^ n))
    (hei : (minpoly R B.gen).IsEisensteinAt
      (Submodule.span R {p})) :
    integralClosure R L = Algebra.adjoin R ({B.gen} : Set L) := by
  apply le_antisymm
  · intro z hz
    change IsIntegral R z at hz
    have hzDisc :
        Algebra.discr K B.basis • z ∈
          Algebra.adjoin R ({B.gen} : Set L) :=
      Algebra.discr_mul_isIntegral_mem_adjoin K hBint hz
    have hpz :
        p ^ n • z ∈ Algebra.adjoin R ({B.gen} : Set L) := by
      rw [hdisc] at hzDisc
      simpa only [IsScalarTower.algebraMap_smul] using hzDisc
    exact
      mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
        hp hBint hz hpz hei
  · exact adjoin_le_integralClosure hBint

end

end MazurProof

end
end

-- module FLT.Assumptions.MazurProof.LinearAdjoinRootScalar
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.LinearAdjoinRootScalar =====
section

/-!
# Elements of a linear polynomial quotient are scalar

A quotient by a monic polynomial of degree one has rank one over the
ground field.  Reducing an arbitrary representative modulo that polynomial
therefore gives a constant.  This is the degree-one degeneration of the
quadratic quotient step used in the N13 inverse Kummer construction.
-/

namespace MazurProof.LinearAdjoinRootScalar

noncomputable section

open Polynomial

variable {K : Type*} [Field K]

/-- Every element of a quotient by a monic linear polynomial comes from the
ground field. -/
theorem exists_eq_algebraMap
    (u : K[X]) (hu : u.Monic) (hu1 : u.natDegree = 1)
    (t : AdjoinRoot u) :
    ∃ r : K, t = algebraMap K (AdjoinRoot u) r := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective t
  let rpoly : K[X] := p %ₘ u
  have huNeOne : u ≠ 1 := by
    intro h
    rw [h, natDegree_one] at hu1
    omega
  have hrpoly : rpoly.natDegree ≤ 0 := by
    have hlt := natDegree_modByMonic_lt p hu huNeOne
    dsimp only [rpoly]
    rw [hu1] at hlt
    omega
  refine ⟨rpoly.coeff 0, ?_⟩
  have hrpolyEq : rpoly = C (rpoly.coeff 0) :=
    eq_C_of_natDegree_le_zero hrpoly
  calc
    AdjoinRoot.mk u p =
        AdjoinRoot.mk u
          (AdjoinRoot.modByMonicHom hu (AdjoinRoot.mk u p)) := by
            exact (AdjoinRoot.mk_leftInverse hu
              (AdjoinRoot.mk u p)).symm
    _ = AdjoinRoot.mk u rpoly := by
      rw [AdjoinRoot.modByMonicHom_mk]
    _ = AdjoinRoot.mk u (C (rpoly.coeff 0)) := by
      exact congrArg (AdjoinRoot.mk u) hrpolyEq
    _ = algebraMap K (AdjoinRoot u) (rpoly.coeff 0) := by
      rfl

/-- If an element of a monic linear quotient has scalar square `s`, then its
unique scalar representative is a square root of `s`. -/
theorem exists_scalar_square_root
    (u : K[X]) (hu : u.Monic) (hu1 : u.natDegree = 1)
    (t : AdjoinRoot u) (s : K)
    (hsq : t ^ 2 = algebraMap K (AdjoinRoot u) s) :
    ∃ r : K,
      t = algebraMap K (AdjoinRoot u) r ∧ r ^ 2 = s := by
  obtain ⟨r, hr⟩ := exists_eq_algebraMap u hu hu1 t
  refine ⟨r, hr, ?_⟩
  have hscalar :
      algebraMap K (AdjoinRoot u) (r ^ 2) =
        algebraMap K (AdjoinRoot u) s := by
    rw [map_pow, ← hr, hsq]
  have hdegree : u.degree ≠ 0 := by
    rw [degree_eq_natDegree hu.ne_zero, hu1]
    norm_num
  exact
    (AdjoinRoot.of.injective_of_degree_ne_zero hdegree) hscalar

end

end MazurProof.LinearAdjoinRootScalar

end
end

-- module FLT.Assumptions.MazurProof.TateNFDivision
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.TateNFDivision =====
section

/-!
# Division polynomials at the Tate normal form origin

For the Tate normal form `y² + (1-c)xy - by = x³ - bx²` with marked point
`P = (0,0)`, the division polynomials `ψₙ` evaluated at `P` factor as
`ψₙ(P) = b^eₙ · Fₙ(b,c)` where `Fₙ` is a small polynomial.

The condition "P has exact order n" is `Fₙ(b,c) = 0` (with `b ≠ 0` and
nonsingularity).  These compact factors are the foundation for all cyclic
torsion exclusions via Tate normal form.

## References

* Kubert, "Universal bounds on the torsion of elliptic curves", 1976
* The division polynomial recurrence specialized at the origin
-/

namespace MazurProof.TateNFDivision

variable {K : Type*} [Field K]

/-! ## Tate normal form curve and origin -/

/-! ## Weierstrass invariants of the Tate normal form -/

/-! ## Compact factors of ψₙ(0,0) / b^eₙ

These are the NON-trivial factors after removing the power of `b`.
The order-n condition at the Tate origin is `Fₙ(b,c) = 0`.
-/

/-- `ψ₈(0,0) / (-b²¹c) = 2b² - 3bc - bc² + c²`.  Order 8 at origin
    requires additionally `c ≠ 0`. -/
def F8 (b c : K) : K := 2 * b ^ 2 - 3 * b * c - b * c ^ 2 + c ^ 2

/-! ## Expanded forms (useful for ring-level reasoning) -/

/-! ## Two-division polynomial (for rational 2-torsion detection) -/

/-! ## Relation to Weierstrass invariants -/

/-! ## Order conditions at the Tate origin

Exact order `n` at the origin means `Fₙ(b,c) = 0` and all proper divisor
conditions are nonzero.
-/

/-! ## Composite order systems via coprime decomposition -/

end MazurProof.TateNFDivision

end
end

-- module FLT.Assumptions.MazurProof.N13CurveModel
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13CurveModel =====
section

/-!
# Equivalent affine models of `X₁(13)`

The optimized generalized model from `N13TateBridge` is completed to the
standard even-degree hyperelliptic model

`Y² = X⁶ + 4X⁵ + 6X⁴ + 2X³ + X² + 2X + 1`

by the elementary change of variables

`X = -x - 1`, `Y = 2y + x³ + x² + 1`.

This exposes the four affine cusps as the points over `X = 0,-1`.  The two
remaining cusps are the two points at infinity on the smooth projective
completion; they do not occur in the affine Tate chart.
-/

namespace MazurProof.N13CurveModel



/-- The standard sextic defining the hyperelliptic model of `X₁(13)`. -/
def sexticF13 (X : ℚ) : ℚ :=
  X ^ 6 + 4 * X ^ 5 + 6 * X ^ 4 + 2 * X ^ 3 + X ^ 2 + 2 * X + 1

/-- The affine standard hyperelliptic model of `X₁(13)`. -/
def C13SexticEq (X Y : ℚ) : Prop :=
  Y ^ 2 = sexticF13 X

@[simp] theorem sexticF13_zero : sexticF13 0 = 1 := by
  norm_num [sexticF13]

@[simp] theorem sexticF13_neg_one : sexticF13 (-1) = 1 := by
  norm_num [sexticF13]

/-- The four visible affine points above `X=0,-1` lie on the curve. -/
theorem affine_cusp_mem
    {X Y : ℚ} (hX : X = 0 ∨ X = -1) (hY : Y = 1 ∨ Y = -1) :
    C13SexticEq X Y := by
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;>
    norm_num [C13SexticEq]

end MazurProof.N13CurveModel

end
end

-- module FLT.Assumptions.MazurProof.N13GoodModelTwo
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodModelTwo =====
section

/-!
# A good characteristic-two model of `X₁(13)`

The completed-square sextic is not the model to reduce modulo two.  This file
uses the generalized hyperelliptic equation

`y² + (x³+x+1)y = x⁵+x⁴`.

Over the rationals, completing the square gives the existing N13 sextic.
In characteristic two, the affine chart and the chart at infinity both have
nonzero derivative in the second coordinate.  The `F₂`- and `F₄`-point
counts are obtained from Frobenius and the Artin--Schreier map, not by
enumerating field elements.
-/

namespace MazurProof.N13GoodModelTwo

noncomputable section

open scoped CharTwo
open Polynomial

universe u

variable {R : Type u} [CommRing R]

/-- The coefficient of `y` in the generalized equation. -/
def h (x : R) : R := x ^ 3 + x + 1

/-- The right-hand side of the generalized equation. -/
def rhs (x : R) : R := x ^ 5 + x ^ 4

/-- The affine equation with zero on the right. -/
def affineResidual (x y : R) : R :=
  y ^ 2 + h x * y - rhs x

/-- The affine generalized hyperelliptic equation. -/
def AffineEquation (x y : R) : Prop :=
  y ^ 2 + h x * y = rhs x

theorem affineEquation_iff_residual (x y : R) :
    AffineEquation x y ↔ affineResidual x y = 0 := by
  simp [AffineEquation, affineResidual, sub_eq_zero]

/-- Its completed-square polynomial. -/
def completedSextic (x : R) : R :=
  x ^ 6 + 4 * x ^ 5 + 6 * x ^ 4 + 2 * x ^ 3 + x ^ 2 + 2 * x + 1

theorem h_sq_add_four_rhs (x : R) :
    h x ^ 2 + 4 * rhs x = completedSextic x := by
  simp only [h, rhs, completedSextic]
  ring

/-- Completing the square before reduction. -/
theorem completed_square_identity (x y : R) :
    (2 * y + h x) ^ 2 =
      completedSextic x + 4 * (y ^ 2 + h x * y - rhs x) := by
  rw [← h_sq_add_four_rhs]
  ring

theorem completedSextic_rat (x : ℚ) :
    completedSextic x = N13CurveModel.sexticF13 x := by
  rfl

/-- The inverse completed-square coordinate over `ℚ`. -/
def sexticToGoodY (x Y : ℚ) : ℚ :=
  (Y - h x) / 2

theorem sextic_good_y_roundtrip (x Y : ℚ) :
    2 * sexticToGoodY x Y + h x = Y := by
  simp only [sexticToGoodY]
  ring

/-- The standard sextic maps back to the good generalized model over `ℚ`. -/
theorem sextic_to_good
    {x Y : ℚ} (hp : N13CurveModel.C13SexticEq x Y) :
    AffineEquation x (sexticToGoodY x Y) := by
  have hs := completed_square_identity x (sexticToGoodY x Y)
  rw [sextic_good_y_roundtrip] at hs
  rw [N13CurveModel.C13SexticEq, ← completedSextic_rat] at hp
  rw [hp] at hs
  have hz :
      sexticToGoodY x Y ^ 2 + h x * sexticToGoodY x Y - rhs x = 0 := by
    linarith
  exact sub_eq_zero.mp hz

/-! ## The two charts of the weighted projective completion -/

/-- Equation on the `X=1` chart, with `t=Z/X` and `v=Y/X³`. -/
def InfinityChartEquation (t v : R) : Prop :=
  v ^ 2 + (1 + t ^ 2 + t ^ 3) * v = t + t ^ 2

/-- Residual form of the `X=1` chart. -/
def infinityChartResidual (t v : R) : R :=
  v ^ 2 + (1 + t ^ 2 + t ^ 3) * v - (t + t ^ 2)

theorem infinityChartEquation_iff (t v : R) :
    InfinityChartEquation t v ↔ infinityChartResidual t v = 0 := by
  simp [InfinityChartEquation, infinityChartResidual, sub_eq_zero]

/-- Clearing the transition denominators identifies the two chart
residuals. -/
theorem overlap_residual
    {x t v : R} (hxt : x * t = 1) :
    affineResidual x (x ^ 3 * v) =
      x ^ 6 * infinityChartResidual t v := by
  have hx6t : x ^ 6 * t = x ^ 5 := by
    calc
      x ^ 6 * t = x ^ 5 * (x * t) := by ring
      _ = x ^ 5 := by rw [hxt, mul_one]
  have hx6t2 : x ^ 6 * t ^ 2 = x ^ 4 := by
    calc
      x ^ 6 * t ^ 2 = x ^ 4 * (x * t) ^ 2 := by ring
      _ = x ^ 4 := by rw [hxt, one_pow, mul_one]
  have hx6t3 : x ^ 6 * t ^ 3 = x ^ 3 := by
    calc
      x ^ 6 * t ^ 3 = x ^ 3 * (x * t) ^ 3 := by ring
      _ = x ^ 3 := by rw [hxt, one_pow, mul_one]
  calc
    affineResidual x (x ^ 3 * v) =
        x ^ 6 * v ^ 2 + (x ^ 6 + x ^ 4 + x ^ 3) * v -
          x ^ 5 - x ^ 4 := by
      simp only [affineResidual, h, rhs]
      ring
    _ = x ^ 6 * v ^ 2 +
          (x ^ 6 + x ^ 6 * t ^ 2 + x ^ 6 * t ^ 3) * v -
          x ^ 6 * t - x ^ 6 * t ^ 2 := by
      rw [hx6t, hx6t2, hx6t3]
    _ = x ^ 6 * infinityChartResidual t v := by
      simp only [infinityChartResidual]
      ring

/-- The two equations agree on the overlap `xt=1`. -/
theorem affine_iff_infinity_on_overlap
    {x t v : R} (hxt : x * t = 1) :
    AffineEquation x (x ^ 3 * v) ↔ InfinityChartEquation t v := by
  have hx : IsUnit x := IsUnit.of_mul_eq_one t hxt
  have hx6 : IsUnit (x ^ 6) := hx.pow 6
  rw [affineEquation_iff_residual, infinityChartEquation_iff,
    overlap_residual hxt]
  constructor
  · intro hz
    exact hx6.mul_left_cancel (by simpa using hz)
  · intro hz
    rw [hz, mul_zero]

/-- Derivative of the affine equation with respect to `y`. -/
def affineDerivativeY (x y : R) : R :=
  2 * y + h x

/-- The affine equation as a polynomial in the second coordinate. -/
def affineFiber (x : R) : R[X] :=
  X ^ 2 + C (h x) * X - C (rhs x)

@[simp] theorem affineFiber_eval (x y : R) :
    (affineFiber x).eval y = affineResidual x y := by
  simp [affineFiber, affineResidual]

theorem affineFiber_derivative (x : R) :
    (affineFiber x).derivative = 2 * X + C (h x) := by
  simp only [affineFiber, derivative_sub, derivative_add, derivative_pow,
    derivative_X, derivative_mul, derivative_C, zero_mul, zero_add, mul_one,
    sub_zero]
  norm_num [map_natCast]
  rw [C_ofNat]

theorem affineFiber_derivative_eval (x y : R) :
    (affineFiber x).derivative.eval y = affineDerivativeY x y := by
  rw [affineFiber_derivative]
  simp [affineDerivativeY]

/-! ## Structural characteristic-two point classification -/

variable {K : Type u} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem fixedTwo_eq_zero_or_one (x : K) (hx : x ^ 2 = x) :
    x = 0 ∨ x = 1 := by
  have hfac : x * (x - 1) = 0 := by
    calc
      x * (x - 1) = x ^ 2 - x := by ring
      _ = 0 := sub_eq_zero.mpr hx
  rcases mul_eq_zero.mp hfac with hx0 | hx1
  · exact Or.inl hx0
  · exact Or.inr (sub_eq_zero.mp hx1)

/-- In a field with four-power Frobenius, an affine point has both
coordinates in the prime subfield.  The non-prime-field branch is excluded
by the Artin--Schreier identity, not by a finite table. -/
theorem affineEquation_iff_fixed
    (hfour : ∀ z : K, z ^ 4 = z) (x y : K) :
    AffineEquation x y ↔ x ^ 2 = x ∧ y ^ 2 = y := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  constructor
  · intro hp
    have hidem : (x ^ 2 + x) ^ 2 = x ^ 2 + x := by
      linear_combination hfour x + x ^ 3 * htwo
    have hcases : x ^ 2 + x = 0 ∨ x ^ 2 + x = 1 := by
      have hfac : (x ^ 2 + x) * ((x ^ 2 + x) - 1) = 0 := by
        calc
          (x ^ 2 + x) * ((x ^ 2 + x) - 1) =
              (x ^ 2 + x) ^ 2 - (x ^ 2 + x) := by ring
          _ = 0 := sub_eq_zero.mpr hidem
      rcases mul_eq_zero.mp hfac with hzero | hone
      · exact Or.inl hzero
      · exact Or.inr (sub_eq_zero.mp hone)
    rcases hcases with hprime | hnonprime
    · have hx : x ^ 2 = x := by
        linear_combination hprime - x * htwo
      have hx3 : x ^ 3 = x := by
        calc
          x ^ 3 = x * x ^ 2 := by ring
          _ = x * x := by rw [hx]
          _ = x := by simpa [pow_two] using hx
      have hx4 : x ^ 4 = x := hfour x
      have hx5 : x ^ 5 = x := by
        calc
          x ^ 5 = x * x ^ 4 := by ring
          _ = x * x := by rw [hx4]
          _ = x := by simpa [pow_two] using hx
      have hh : h x = 1 := by
        simp only [h]
        linear_combination hx3 + x * htwo
      have hrhs : rhs x = 0 := by
        simp only [rhs]
        linear_combination hx5 + hx4 + x * htwo
      have hy : y ^ 2 = y := by
        unfold AffineEquation at hp
        rw [hh, hrhs] at hp
        linear_combination hp - y * htwo
      exact ⟨hx, hy⟩
    · have hx3 : x ^ 3 = 1 := by
        linear_combination x * hnonprime - hnonprime + (x - 1) * htwo
      have hx4 : x ^ 4 = x := hfour x
      have hx5 : x ^ 5 = x ^ 2 := by
        calc
          x ^ 5 = x * x ^ 4 := by ring
          _ = x * x := by rw [hx4]
          _ = x ^ 2 := by ring
      have hh : h x = x := by
        simp only [h]
        linear_combination hx3 + htwo
      have hrhs : rhs x = 1 := by
        simp only [rhs]
        linear_combination hx5 + hx4 + hnonprime
      have hp' : y ^ 2 + x * y = 1 := by
        simpa [AffineEquation, hh, hrhs] using hp
      let t : K := y * x ^ 2
      have ht : t ^ 2 + t = x := by
        have hx4' : x ^ 4 = x := hfour x
        calc
          t ^ 2 + t = y ^ 2 * x ^ 4 + y * x ^ 2 := by
            simp only [t]
            ring
          _ = y ^ 2 * x + y * x ^ 2 := by rw [hx4']
          _ = x * (y ^ 2 + x * y) := by ring
          _ = x := by rw [hp']; ring
      have htFixed : (t ^ 2 + t) ^ 2 = t ^ 2 + t := by
        linear_combination hfour t + t ^ 3 * htwo
      rw [ht] at htFixed
      have hsumzero : x ^ 2 + x = 0 := by
        linear_combination htFixed + x * htwo
      have hzeroone : (0 : K) = 1 := hsumzero.symm.trans hnonprime
      exact (zero_ne_one hzeroone).elim
  · rintro ⟨hx, hy⟩
    have hx3 : x ^ 3 = x := by
      calc
        x ^ 3 = x * x ^ 2 := by ring
        _ = x * x := by rw [hx]
        _ = x := by simpa [pow_two] using hx
    have hx4 : x ^ 4 = x := hfour x
    have hx5 : x ^ 5 = x := by
      calc
        x ^ 5 = x * x ^ 4 := by ring
        _ = x * x := by rw [hx4]
        _ = x := by simpa [pow_two] using hx
    have hh : h x = 1 := by
      simp only [h]
      linear_combination hx3 + x * htwo
    have hrhs : rhs x = 0 := by
      simp only [rhs]
      linear_combination hx5 + hx4 + x * htwo
    unfold AffineEquation
    rw [hh, hrhs, hy]
    linear_combination y * htwo

/-- Affine points as a finite type. -/
abbrev AffinePoint (K : Type u) [Field K] :=
  {p : K × K // AffineEquation p.1 p.2}

/-- Points on the fibre `t=0` of the infinity chart. -/
abbrev InfinityPoint (K : Type u) [Field K] :=
  {v : K // InfinityChartEquation 0 v}

theorem infinityChartEquation_zero_iff_fixed (v : K) :
    InfinityChartEquation 0 v ↔ v ^ 2 = v := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  unfold InfinityChartEquation
  constructor <;> intro hv
  · linear_combination hv - v * htwo
  · linear_combination hv + v * htwo

/-- The point type presented by the affine chart and its two infinity points. -/
abbrev CompletedPoint (K : Type u) [Field K] :=
  AffinePoint K ⊕ InfinityPoint K

/-! ## The fields `F₂` and `F₄` -/

abbrev F2 := ZMod 2
abbrev F4 := GaloisField 2 2

theorem f2_fourth_eq (x : F2) : x ^ 4 = x := by
  have hx : x ^ 2 = x := ZMod.pow_card x
  calc
    x ^ 4 = (x ^ 2) ^ 2 := by ring
    _ = x ^ 2 := congrArg (fun z : F2 => z ^ 2) hx
    _ = x := hx

local instance : Fintype F4 := Fintype.ofFinite F4

end

end MazurProof.N13GoodModelTwo

end
end

-- module FLT.Assumptions.MazurProof.N13SymmetricSquareTwo
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SymmetricSquareTwo =====
section

/-!
# The symmetric-square route to `#J(F₂)=19`

For a genus-two curve, the Abel map `Sym²(C) → J` is an isomorphism away
from the canonical divisor class.  Its exceptional fibre is the canonical
linear system `P¹`.  Over `F₂` this replaces three points by one.

The good N13 model has six `F₂`-points, so its ordinary symmetric square has
`6 multichoose 2 = 21` points.  This file proves the finite fibre-counting
argument that turns the geometric Abel-fibre statement into
`#J(F₂)=21-2=19`.  It deliberately isolates the remaining geometric input
as a structure, rather than assuming a general zeta-function API or
enumerating Jacobian representatives.
-/

namespace MazurProof.N13SymmetricSquareTwo

noncomputable section

open scoped BigOperators

abbrev CurvePoint :=
  N13GoodModelTwo.CompletedPoint N13GoodModelTwo.F2

/-- Unordered effective divisors of degree two on the special fibre. -/
abbrev EffectiveDivisorTwo :=
  Sym2 CurvePoint

section FiberCounting

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

end FiberCounting

end

end MazurProof.N13SymmetricSquareTwo

end
end

-- module FLT.Assumptions.MazurProof.N13AbelFiberTwoModel
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13AbelFiberTwoModel =====
section

/-!
# A finite set model for the N13 Abel fibres at two

The six points of the good characteristic-two model form three
hyperelliptic pairs.  On `Sym²(C)(F₂)`, collapse the three corresponding
canonical divisors to one class and leave every other divisor unchanged.
The resulting quotient has nineteen elements.

This quotient is only a set-level model of the expected Abel fibres.  It is
not asserted to be the geometric Picard group.  The structure
`GeometricAbelCriterion` records exactly the geometric statements required
to transfer the same fibre calculation to a genuine Picard target.
-/

namespace MazurProof.N13AbelFiberTwoModel

noncomputable section

open N13GoodModelTwo
open N13SymmetricSquareTwo

abbrev K := F2
abbrev CurvePoint := CompletedPoint K

/-- The three rational points of the hyperelliptic base. -/
abbrev BasePoint := K ⊕ Unit

/-- The six curve points are the three base points times two sheets. -/
def curvePointEquiv : CurvePoint ≃ BasePoint × K where
  toFun
    | Sum.inl P => (Sum.inl P.1.1, P.1.2)
    | Sum.inr P => (Sum.inr (), P.1)
  invFun
    | (Sum.inl x, y) =>
        Sum.inl ⟨(x, y), (affineEquation_iff_fixed f2_fourth_eq x y).2
          ⟨ZMod.pow_card x, ZMod.pow_card y⟩⟩
    | (Sum.inr _, v) =>
        Sum.inr ⟨v, (infinityChartEquation_zero_iff_fixed v).2
          (ZMod.pow_card v)⟩
  left_inv P := by
    rcases P with P | P
    · rfl
    · rfl
  right_inv P := by
    rcases P with ⟨b, z⟩
    rcases b with x | u
    · rfl
    · cases u
      rfl

/-- The hyperelliptic fibre over `b`, as an effective divisor of degree two. -/
def canonicalDivisor (b : BasePoint) : EffectiveDivisorTwo :=
  s(curvePointEquiv.symm (b, 0), curvePointEquiv.symm (b, 1))

/-- The three divisors in the canonical pencil over `F₂`. -/
def IsCanonical (D : EffectiveDivisorTwo) : Prop :=
  D ∈ Set.range canonicalDivisor

theorem canonicalDivisor_isCanonical (b : BasePoint) :
    IsCanonical (canonicalDivisor b) :=
  Set.mem_range_self b

/-- Equality except that all three canonical divisors are identified. -/
def AbelRel (D E : EffectiveDivisorTwo) : Prop :=
  D = E ∨ IsCanonical D ∧ IsCanonical E

theorem abelRel_equivalence : Equivalence AbelRel where
  refl D := Or.inl rfl
  symm := by
    intro D E h
    rcases h with rfl | ⟨hD, hE⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hE, hD⟩
  trans := by
    intro D E F hDE hEF
    rcases hDE with rfl | ⟨hD, hE⟩
    · exact hEF
    rcases hEF with rfl | ⟨_, hF⟩
    · exact Or.inr ⟨hD, hE⟩
    · exact Or.inr ⟨hD, hF⟩

def abelSetoid : Setoid EffectiveDivisorTwo :=
  ⟨AbelRel, abelRel_equivalence⟩

/-- Set-level quotient obtained by collapsing the canonical pencil. -/
abbrev PicTwoSetModel := Quotient abelSetoid

def abel : EffectiveDivisorTwo → PicTwoSetModel :=
  Quotient.mk''

theorem abel_eq_iff (D E : EffectiveDivisorTwo) :
    abel D = abel E ↔ AbelRel D E :=
  Quotient.eq''

def baseAtInfinity : BasePoint := Sum.inr ()

def canonicalClass : PicTwoSetModel :=
  abel (canonicalDivisor baseAtInfinity)

theorem abel_eq_canonicalClass_iff (D : EffectiveDivisorTwo) :
    abel D = canonicalClass ↔ IsCanonical D := by
  change abel D = abel (canonicalDivisor baseAtInfinity) ↔ IsCanonical D
  rw [abel_eq_iff]
  constructor
  · rintro (rfl | ⟨hD, _⟩)
    · exact canonicalDivisor_isCanonical baseAtInfinity
    · exact hD
  · intro hD
    exact Or.inr ⟨hD, canonicalDivisor_isCanonical baseAtInfinity⟩

/-! ## Interface to a genuine geometric Picard target -/

set_option maxHeartbeats 4000000 in
/-- The geometric facts needed to transfer the set-level fibre calculation.
Surjectivity is the genus-two Riemann--Roch input; `eq_iff` is the
degree-two linear-equivalence theorem. -/
structure GeometricAbelCriterion (J : Type*) where
  abel : EffectiveDivisorTwo → J
  canonicalClass : J
  canonical_eq :
    ∀ b : BasePoint, abel (canonicalDivisor b) = canonicalClass
  surjective : Function.Surjective abel
  eq_iff :
    ∀ D E : EffectiveDivisorTwo,
      abel D = abel E ↔ AbelRel D E

/-- The intrinsic nineteen-element quotient itself satisfies the geometric
Abel-fibre interface.  This lets later arguments use Abel rigidity without
postulating a separate special Picard-group implementation. -/
def picTwoSetModelCriterion :
    GeometricAbelCriterion PicTwoSetModel where
  abel := abel
  canonicalClass := canonicalClass
  canonical_eq := by
    intro b
    change
      abel (canonicalDivisor b) =
        abel (canonicalDivisor baseAtInfinity)
    rw [abel_eq_iff]
    exact Or.inr
      ⟨canonicalDivisor_isCanonical b,
        canonicalDivisor_isCanonical baseAtInfinity⟩
  surjective := Quotient.mk_surjective
  eq_iff := abel_eq_iff

namespace GeometricAbelCriterion

variable {J : Type*} (G : GeometricAbelCriterion J)

end GeometricAbelCriterion

end

end MazurProof.N13AbelFiberTwoModel

end
end

-- module FLT.Assumptions.MazurProof.N13FormalAbelLinearization
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FormalAbelLinearization =====
section

/-!
# The integral linearization of an N13 Abel chart

The two integral points `(0,0)` and `(-1,0)` reduce to points with distinct
`x`-coordinates.  Their degree-two sum is therefore away from the canonical
hyperelliptic pencil.  In generalized Mumford coordinates its base
polynomial is `X² + X`, and the linearized curve relation has determinant
`-1`.

This file proves the polynomial identities behind that unit Jacobian over an
arbitrary nontrivial commutative ring.  No point or divisor enumeration is
used.
-/

open Polynomial

namespace MazurProof.N13FormalAbelLinearization

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- The monic polynomial of the base divisor `(0,0)+(-1,0)`. -/
def uBase : R[X] :=
  X ^ 2 + X

/-- The coefficient of `Y` in the good generalized equation. -/
def hPoly : R[X] :=
  X ^ 3 + X + 1

theorem uBase_monic : (uBase : R[X]).Monic := by
  unfold uBase
  (monicity; norm_num)

/-! ## The Abel differential -/

end

end MazurProof.N13FormalAbelLinearization

end
end

-- module FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral =====
section

/-!
# Integral generalized Mumford graph quotients for N13

For the good equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`,

evaluation on a graph `Y=v mod u` identifies the graph quotient with
`R[X]/(u)` over any nontrivial commutative base ring.  If the base is a
domain and `u` is monic, this quotient is free and hence torsion-free.
Consequently every graph ideal is saturated with respect to each nonzero
base scalar.

This is the elementary integral algebra needed before reduction modulo two;
it uses neither normality of the affine ring nor a Picard scheme.
-/

open Polynomial

namespace MazurProof.N13GeneralizedMumfordIntegral

noncomputable section

universe u

variable {R : Type u} [CommRing R]

def hPoly : R[X] :=
  X ^ 3 + X + 1

def rhsPoly : R[X] :=
  X ^ 5 + X ^ 4

def curvePoly : R[X][X] :=
  X ^ 2 + C hPoly * X - C rhsPoly

theorem curvePoly_monic : (curvePoly : R[X][X]).Monic := by
  unfold curvePoly
  monicity <;> norm_num

theorem curvePoly_natDegree [Nontrivial R] :
    (curvePoly : R[X][X]).natDegree = 2 := by
  unfold curvePoly
  compute_degree <;> norm_num

abbrev CoordinateRing : Type u :=
  AdjoinRoot (curvePoly : R[X][X])

noncomputable instance : Algebra R (CoordinateRing (R := R)) :=
  inferInstance

noncomputable instance : Algebra R[X] (CoordinateRing (R := R)) :=
  inferInstance

def mk : R[X][X] →+* CoordinateRing (R := R) :=
  AdjoinRoot.mk (curvePoly (R := R))

def xClass (p : R[X]) : CoordinateRing (R := R) :=
  mk (R := R) (C p)

def yClass : CoordinateRing (R := R) :=
  mk (R := R) X

def xClassHom : R[X] →+* CoordinateRing (R := R) :=
  AdjoinRoot.of (curvePoly (R := R))

@[simp] theorem xClassHom_apply (p : R[X]) :
    xClassHom p = xClass p := rfl

@[simp] theorem xClass_zero : xClass (0 : R[X]) = 0 :=
  map_zero xClassHom

@[simp] theorem xClass_one : xClass (1 : R[X]) = 1 :=
  map_one xClassHom

@[simp] theorem xClass_natCast (n : ℕ) :
    xClass (n : R[X]) =
      (n : CoordinateRing (R := R)) :=
  map_natCast xClassHom n

@[simp] theorem xClass_add (p q : R[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q

@[simp] theorem xClass_sub (p q : R[X]) :
    xClass (p - q) = xClass p - xClass q :=
  map_sub xClassHom p q

@[simp] theorem xClass_neg (p : R[X]) :
    xClass (-p) = -xClass p :=
  map_neg xClassHom p

@[simp] theorem xClass_mul (p q : R[X]) :
    xClass (p * q) = xClass p * xClass q :=
  map_mul xClassHom p q

@[simp] theorem xClass_pow (p : R[X]) (n : ℕ) :
    xClass (p ^ n) = xClass p ^ n :=
  map_pow xClassHom p n

def normalPoly :
    CoordinateRing (R := R) →ₗ[R[X]] R[X][X] :=
  AdjoinRoot.modByMonicHom (curvePoly_monic (R := R))

def coeff0 :
    CoordinateRing (R := R) →ₗ[R[X]] R[X] :=
  (Polynomial.lcoeff R[X] 0).comp (normalPoly (R := R))

def coeffY :
    CoordinateRing (R := R) →ₗ[R[X]] R[X] :=
  (Polynomial.lcoeff R[X] 1).comp (normalPoly (R := R))

theorem curvePoly_degree [Nontrivial R] :
    (curvePoly : R[X][X]).degree = 2 := by
  rw [degree_eq_natDegree curvePoly_monic.ne_zero,
    curvePoly_natDegree]
  norm_num

theorem normalPoly_eq_C_add_C_mul_X
    [Nontrivial R]
    (z : CoordinateRing (R := R)) :
    normalPoly z = C (coeff0 z) + C (coeffY z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ curvePoly =
        C ((g %ₘ curvePoly).coeff 0) +
          C ((g %ₘ curvePoly).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := curvePoly) curvePoly_monic
        (n := 2) (by rw [curvePoly_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm

theorem recompose [Nontrivial R]
    (z : CoordinateRing (R := R)) :
    xClass (coeff0 z) + xClass (coeffY z) * yClass = z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        xClass (coeff0 (mk g)) +
              xClass (coeffY (mk g)) * yClass =
            mk
              (C (coeff0 (mk g)) +
                C (coeffY (mk g)) * X) := by
                  simp only [xClass, yClass, mk, map_add, map_mul,
                    AdjoinRoot.mk_C, AdjoinRoot.mk_X]
        _ = mk (normalPoly (mk g)) := by
              rw [normalPoly_eq_C_add_C_mul_X]
        _ = mk g :=
          AdjoinRoot.mk_leftInverse curvePoly_monic (mk g)

@[simp] theorem coeff0_xClass [Nontrivial R] (p : R[X]) :
    coeff0 (xClass p) = p := by
  change (C p %ₘ curvePoly).coeff 0 = p
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by rw [curvePoly_degree]; norm_num)

@[simp] theorem coeffY_xClass [Nontrivial R] (p : R[X]) :
    coeffY (xClass p) = 0 := by
  change (C p %ₘ curvePoly).coeff 1 = 0
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by rw [curvePoly_degree]; norm_num)

@[simp] theorem coeff0_yClass [Nontrivial R] :
    coeff0 (yClass (R := R)) = 0 := by
  change (X %ₘ curvePoly).coeff 0 = 0
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · rw [degree_X, curvePoly_degree]
    norm_num

@[simp] theorem coeffY_yClass [Nontrivial R] :
    coeffY (yClass (R := R)) = 1 := by
  change (X %ₘ curvePoly).coeff 1 = 1
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · rw [degree_X, curvePoly_degree]
    norm_num

@[simp] theorem coeff0_xClass_mul_yClass [Nontrivial R] (p : R[X]) :
    coeff0 (xClass p * yClass) = 0 := by
  change coeff0
    ((algebraMap R[X] (CoordinateRing (R := R)) p) * yClass) = 0
  rw [← Algebra.smul_def]
  simp

@[simp] theorem coeffY_xClass_mul_yClass [Nontrivial R] (p : R[X]) :
    coeffY (xClass p * yClass) = p := by
  change coeffY
    ((algebraMap R[X] (CoordinateRing (R := R)) p) * yClass) = p
  rw [← Algebra.smul_def]
  simp

/-- Equality in the generalized affine coordinate ring is coefficientwise
with respect to the basis `1, Y` over `R[X]`. -/
theorem eq_iff_coeff [Nontrivial R]
    (z w : CoordinateRing (R := R)) :
    z = w ↔ coeff0 z = coeff0 w ∧ coeffY z = coeffY w := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, hY⟩
    rw [← recompose z, ← recompose w, h0, hY]

set_option maxHeartbeats 4000000 in
/-- The generalized graph relation; no smoothness assumption is needed for
the evaluation-kernel and saturation theorems. -/
structure SemiMumford where
  u : R[X]
  v : R[X]
  w : R[X]
  u_monic : u.Monic
  curve_eq : v ^ 2 + hPoly * v - rhsPoly = u * w

/-- Hyperelliptic conjugation sends a graph value `v` to `-h-v`. -/
def conjugateV (v : R[X]) : R[X] :=
  -hPoly - v

def ySubClass (v : R[X]) : CoordinateRing (R := R) :=
  yClass - xClass v

def mumfordIdeal (u v : R[X]) :
    Ideal (CoordinateRing (R := R)) :=
  Ideal.span {xClass u, ySubClass v}

theorem xClass_mem_mumfordIdeal (u v : R[X]) :
    xClass u ∈ mumfordIdeal u v :=
  Ideal.subset_span (by simp)

theorem ySubClass_mem_mumfordIdeal (u v : R[X]) :
    ySubClass v ∈ mumfordIdeal u v :=
  Ideal.subset_span (by simp)

@[simp] theorem yClass_relation :
    yClass (R := R) ^ 2 +
        xClass (R := R) (hPoly (R := R)) *
          yClass (R := R) =
      xClass (R := R) (rhsPoly (R := R)) := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [curvePoly]
  ring

/-- The product of the two raw graph functions is the negative substituted
curve equation.  No divisibility or smoothness hypothesis is needed. -/
theorem ySubClass_mul_conjugateV_raw
    (v : R[X]) :
    ySubClass v * ySubClass (conjugateV v) =
      -xClass (v ^ 2 + hPoly * v - rhsPoly) := by
  calc
    ySubClass v * ySubClass (conjugateV v) =
        yClass ^ 2 + xClass hPoly * yClass -
          (xClass v ^ 2 + xClass hPoly * xClass v) := by
      simp only [ySubClass, conjugateV, xClass_neg, xClass_sub]
      ring
    _ = xClass rhsPoly -
          xClass (v ^ 2 + hPoly * v) := by
      rw [yClass_relation, xClass_add, xClass_mul, xClass_pow]
    _ = -xClass (v ^ 2 + hPoly * v - rhsPoly) := by
      rw [xClass_sub]
      ring

/-- The two conjugate graph functions multiply to the negative Cantor
quotient.  This identity is valid integrally, before reduction modulo two. -/
theorem ySubClass_mul_conjugate
    (D : SemiMumford (R := R)) :
    ySubClass D.v * ySubClass (conjugateV D.v) =
      -(xClass D.u * xClass D.w) := by
  calc
    ySubClass D.v * ySubClass (conjugateV D.v) =
        -xClass (D.v ^ 2 + hPoly * D.v - rhsPoly) :=
      ySubClass_mul_conjugateV_raw D.v
    _ = -xClass (D.u * D.w) := by rw [D.curve_eq]
    _ = -(xClass D.u * xClass D.w) := by rw [xClass_mul]

abbrev MumfordResidue
    (D : SemiMumford (R := R)) : Type u :=
  R[X] ⧸ Ideal.span ({D.u} : Set R[X])

theorem mumford_root_relation
    (D : SemiMumford (R := R)) :
    curvePoly.eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) D.v) = 0 := by
  change (X ^ 2 + C hPoly * X - C rhsPoly).eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) D.v) = 0
  simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
    eval₂_mul]
  change Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X]))
    (D.v ^ 2 + hPoly * D.v - rhsPoly) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨D.w, D.curve_eq⟩

def mumfordEval (D : SemiMumford (R := R)) :
    CoordinateRing (R := R) →+* MumfordResidue D :=
  AdjoinRoot.lift
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])))
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) D.v)
    (mumford_root_relation D)

@[simp] theorem mumfordEval_xClass
    (D : SemiMumford (R := R)) (p : R[X]) :
    mumfordEval D (xClass p) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) p := by
  change mumfordEval D (AdjoinRoot.of curvePoly p) = _
  exact AdjoinRoot.lift_of (mumford_root_relation D)

@[simp] theorem mumfordEval_yClass
    (D : SemiMumford (R := R)) :
    mumfordEval D yClass =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) D.v :=
  AdjoinRoot.lift_root (mumford_root_relation D)

@[simp] theorem mumfordEval_ySubClass
    (D : SemiMumford (R := R)) :
    mumfordEval D (ySubClass D.v) = 0 := by
  simp [ySubClass]

theorem mumfordIdeal_le_ker
    (D : SemiMumford (R := R)) :
    mumfordIdeal D.u D.v ≤ RingHom.ker (mumfordEval D) := by
  apply Ideal.span_le.2
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · change mumfordEval D (xClass D.u) = 0
    rw [mumfordEval_xClass,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  · exact mumfordEval_ySubClass D

theorem ker_mumfordEval
    [Nontrivial R]
    (D : SemiMumford (R := R)) :
    RingHom.ker (mumfordEval D) = mumfordIdeal D.u D.v := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    let p : R[X] := coeff0 z
    let q : R[X] := coeffY z
    have hz' : mumfordEval D
        (xClass p + xClass q * yClass) = 0 := by
      rw [recompose]
      exact hz
    have hquot : Ideal.Quotient.mk
        (Ideal.span ({D.u} : Set R[X]))
        (p + q * D.v) = 0 := by
      simpa only [map_add, map_mul, mumfordEval_xClass,
        mumfordEval_yClass] using hz'
    have hdvd : D.u ∣ p + q * D.v :=
      Ideal.mem_span_singleton.mp
        (Ideal.Quotient.eq_zero_iff_mem.mp hquot)
    obtain ⟨s, hs⟩ := hdvd
    have hu : xClass D.u ∈ mumfordIdeal D.u D.v :=
      xClass_mem_mumfordIdeal D.u D.v
    have hyv : ySubClass D.v ∈ mumfordIdeal D.u D.v :=
      ySubClass_mem_mumfordIdeal D.u D.v
    have hbase : xClass (p + q * D.v) ∈
        mumfordIdeal D.u D.v := by
      rw [hs, xClass_mul, mul_comm]
      exact Ideal.mul_mem_left
        (mumfordIdeal D.u D.v) (xClass s) hu
    have hgraph : xClass q * ySubClass D.v ∈
        mumfordIdeal D.u D.v :=
      Ideal.mul_mem_left
        (mumfordIdeal D.u D.v) (xClass q) hyv
    rw [← recompose z]
    have hdecomp :
        xClass p + xClass q * yClass =
          xClass (p + q * D.v) +
            xClass q * ySubClass D.v := by
      simp only [xClass_add, xClass_mul, ySubClass]
      ring
    rw [hdecomp]
    exact Ideal.add_mem _ hbase hgraph
  · exact mumfordIdeal_le_ker D

/-- Membership in a generalized Mumford graph ideal is the single monic
divisibility condition obtained by substituting `Y = v`. -/
theorem mem_mumfordIdeal_iff
    [Nontrivial R]
    (D : SemiMumford (R := R))
    (z : CoordinateRing (R := R)) :
    z ∈ mumfordIdeal D.u D.v ↔
      D.u ∣ coeff0 z + coeffY z * D.v := by
  rw [← ker_mumfordEval D, RingHom.mem_ker]
  conv_lhs =>
    rw [← recompose z]
  simp only [map_add, map_mul, mumfordEval_xClass,
    mumfordEval_yClass]
  change
    Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X]))
        (coeff0 z + coeffY z * D.v) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

theorem mumfordEval_surjective
    (D : SemiMumford (R := R)) :
    Function.Surjective (mumfordEval D) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨xClass p, mumfordEval_xClass D p⟩

noncomputable def mumfordQuotientEquiv
    [Nontrivial R]
    (D : SemiMumford (R := R)) :
    CoordinateRing ⧸ mumfordIdeal D.u D.v ≃+*
      MumfordResidue D :=
  (Ideal.quotEquivOfEq (ker_mumfordEval D).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (mumfordEval_surjective D))

/-- The graph quotient equivalence sends a quotient class to its graph
evaluation. -/
@[simp] theorem mumfordQuotientEquiv_apply_mk
    [Nontrivial R]
    (D : SemiMumford (R := R))
    (z : CoordinateRing (R := R)) :
    mumfordQuotientEquiv D
        (Ideal.Quotient.mk (mumfordIdeal D.u D.v) z) =
      mumfordEval D z := by
  simp [mumfordQuotientEquiv]

/-- The graph quotient equivalence respects the coefficient algebra. -/
noncomputable def mumfordQuotientAlgEquiv
    [Nontrivial R]
    (D : SemiMumford (R := R)) :
    (CoordinateRing ⧸ mumfordIdeal D.u D.v) ≃ₐ[R]
      MumfordResidue D :=
  AlgEquiv.ofRingEquiv
    (f := mumfordQuotientEquiv D)
    (by
      intro r
      change
        mumfordQuotientEquiv D
            (Ideal.Quotient.mk
              (mumfordIdeal D.u D.v) (xClass (C r))) =
          Ideal.Quotient.mk
            (Ideal.span ({D.u} : Set R[X])) (C r)
      rw [mumfordQuotientEquiv_apply_mk,
        mumfordEval_xClass])

/-- A monic graph quotient is free over the base. -/
noncomputable instance mumfordResidueFree
    (D : SemiMumford (R := R)) :
    Module.Free R (MumfordResidue D) :=
  D.u_monic.free_quotient

/-- A generalized Mumford graph ideal is saturated with respect to every
nonzero scalar from a domain base. -/
theorem scalar_saturated
    [IsDomain R]
    (D : SemiMumford (R := R))
    (r : R) (hr : r ≠ 0)
    (z : CoordinateRing (R := R))
    (hz : xClass (C r) * z ∈ mumfordIdeal D.u D.v) :
    z ∈ mumfordIdeal D.u D.v := by
  have hker :
      xClass (C r) * z ∈ RingHom.ker (mumfordEval D) := by
    rw [ker_mumfordEval]
    exact hz
  have hmap :
      mumfordEval D (xClass (C r) * z) = 0 :=
    hker
  have hscalar :
      r • mumfordEval D z =
        Ideal.Quotient.mk
          (Ideal.span ({D.u} : Set R[X])) (C r) *
            mumfordEval D z := by
    obtain ⟨p, hp⟩ :=
      Ideal.Quotient.mk_surjective (mumfordEval D z)
    rw [← hp]
    change
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) (r • p) =
        Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) (C r) *
          Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) p
    rw [Polynomial.smul_eq_C_mul]
    exact
      (Ideal.Quotient.mk
        (Ideal.span ({D.u} : Set R[X]))).map_mul (C r) p
  have hsmul : r • mumfordEval D z = 0 := by
    rw [hscalar]
    simpa only [map_mul, mumfordEval_xClass] using hmap
  have heval : mumfordEval D z = 0 :=
    (smul_eq_zero.mp hsmul).resolve_left hr
  rw [← ker_mumfordEval D, RingHom.mem_ker]
  exact heval

namespace TwoAdic

abbrev R₂ : Type := ℤ_[2]

abbrev SemiMumford₂ : Type :=
  SemiMumford (R := R₂)

end TwoAdic

end

end MazurProof.N13GeneralizedMumfordIntegral

end
end

-- module FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo =====
section

/-!
# The affine coordinate ring of the N13 good fibre at two

The good characteristic-two equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`

defines a quadratic extension of `F₂(X)`.  This file constructs its affine
coordinate ring as an `AdjoinRoot` and proves irreducibility structurally.
The proof uses degree dominance and two coefficient comparisons; it does not
enumerate polynomials over `F₂`.
-/

open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors

namespace MazurProof.N13GoodCoordinateRingTwo

noncomputable section

abbrev K := N13GoodModelTwo.F2

/-- The coefficient of `Y` in polynomial form. -/
def hPoly : K[X] :=
  X ^ 3 + X + 1

/-- The right-hand side in polynomial form. -/
def rhsPoly : K[X] :=
  X ^ 5 + X ^ 4

/-- The outer variable is `Y`, with coefficients in `F₂[X]`. -/
def curvePoly : K[X][X] :=
  X ^ 2 + C hPoly * X - C rhsPoly

theorem hPoly_monic : hPoly.Monic := by
  unfold hPoly
  (monicity; norm_num)

theorem hPoly_natDegree : hPoly.natDegree = 3 := by
  unfold hPoly
  (compute_degree; norm_num)

theorem rhsPoly_monic : rhsPoly.Monic := by
  unfold rhsPoly
  monicity <;> norm_num

theorem rhsPoly_natDegree : rhsPoly.natDegree = 5 := by
  unfold rhsPoly
  compute_degree <;> norm_num

theorem curvePoly_monic : curvePoly.Monic := by
  unfold curvePoly
  monicity <;> norm_num

theorem curvePoly_natDegree : curvePoly.natDegree = 2 := by
  unfold curvePoly
  compute_degree <;> norm_num

theorem zmod_two_nonzero_eq_one (z : K) (hz : z ≠ 0) :
    z = 1 := by
  simpa [K] using ZMod.pow_card_sub_one_eq_one hz

theorem artinSchreier_degree_le_three
    (q : K[X])
    (heq : q ^ 2 + hPoly * q = rhsPoly) :
    q.natDegree ≤ 3 := by
  have hq0 : q ≠ 0 := by
    intro hq
    subst q
    have : (rhsPoly : K[X]) = 0 := by simpa using heq.symm
    exact rhsPoly_monic.ne_zero this
  by_contra hdeg
  have h4 : 4 ≤ q.natDegree := by omega
  have hlt :
      (hPoly * q).natDegree < (q ^ 2).natDegree := by
    rw [natDegree_mul hPoly_monic.ne_zero hq0, hPoly_natDegree,
      natDegree_pow]
    omega
  have hsum :
      (q ^ 2 + hPoly * q).natDegree = (q ^ 2).natDegree :=
    natDegree_add_eq_left_of_natDegree_lt hlt
  rw [heq, rhsPoly_natDegree, natDegree_pow] at hsum
  omega

theorem artinSchreier_reduce_degree
    (q : K[X])
    (heq : q ^ 2 + hPoly * q = rhsPoly) :
    ∃ r : K[X],
      r.natDegree ≤ 2 ∧
      r ^ 2 + hPoly * r = rhsPoly := by
  have hdeg := artinSchreier_degree_le_three q heq
  by_cases hq3 : q.natDegree = 3
  · have hq0 : q ≠ 0 := by
      intro hq
      subst q
      norm_num at hq3
    have hlead : q.leadingCoeff = 1 :=
      zmod_two_nonzero_eq_one q.leadingCoeff
        (leadingCoeff_ne_zero.mpr hq0)
    have hqMonic : q.Monic := hlead
    have hqDegree : IsMonicOfDegree q 3 := ⟨hq3, hqMonic⟩
    have hhDegree : IsMonicOfDegree hPoly 3 :=
      ⟨hPoly_natDegree, hPoly_monic⟩
    refine ⟨q - hPoly, ?_, ?_⟩
    · have hlt :
          (q - hPoly).natDegree < 3 :=
        hqDegree.natDegree_sub_lt (n := 3) (by norm_num) hhDegree
      omega
    · have htwo : (2 : K[X]) = 0 :=
        CharP.cast_eq_zero (K[X]) 2
      calc
        (q - hPoly) ^ 2 + hPoly * (q - hPoly) =
            q ^ 2 + hPoly * q - 2 * (q * hPoly) := by ring
        _ = q ^ 2 + hPoly * q := by rw [htwo, zero_mul, sub_zero]
        _ = rhsPoly := heq
  · refine ⟨q, ?_, heq⟩
    omega

theorem no_artinSchreier_polynomial_root
    (q : K[X]) :
    q ^ 2 + hPoly * q ≠ rhsPoly := by
  intro heq
  obtain ⟨r, hrdeg, hre⟩ := artinSchreier_reduce_degree q heq
  have hr :
      r =
        C (r.coeff 2) * X ^ 2 +
          C (r.coeff 1) * X +
            C (r.coeff 0) := by
    ext n
    by_cases hn0 : n = 0
    · subst n
      simp
    by_cases hn1 : n = 1
    · subst n
      simp
    by_cases hn2 : n = 2
    · subst n
      simp
    have hn : 2 < n := by omega
    have hrzero : r.coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (hrdeg.trans_lt hn)
    have h1n : 1 ≠ n := by omega
    rw [hrzero]
    simp [coeff_X, coeff_C, hn0, h1n, hn2]
  rw [hr] at hre
  simp only [hPoly, rhsPoly] at hre
  ring_nf at hre
  have hcoeffFive :=
    congrArg (fun p : K[X] => p.coeff 5) hre
  have hcoeffTwo :=
    congrArg (fun p : K[X] => p.coeff 2) hre
  have htwoK : (2 : K) = 0 :=
    CharP.cast_eq_zero K 2
  simp only [← C_pow] at hcoeffFive hcoeffTwo
  simp [coeff_add, coeff_C_mul, coeff_mul_C, coeff_X_pow, htwoK] at hcoeffFive hcoeffTwo
  have hbb : r.coeff 1 + r.coeff 1 = 0 := by
    rw [← two_mul, htwoK, zero_mul]
  have hzero : r.coeff 2 = 0 := by
    linear_combination hcoeffTwo - hbb
  rw [hzero] at hcoeffFive
  exact zero_ne_one hcoeffFive

theorem curvePoly_not_isRoot (q : K[X]) :
    ¬IsRoot curvePoly q := by
  intro hq
  have heq :
      q ^ 2 + hPoly * q = rhsPoly := by
    have hzero :
        q ^ 2 + hPoly * q - rhsPoly = 0 := by
      simpa only [IsRoot.def, curvePoly, eval_sub, eval_add, eval_pow,
        eval_X, eval_C, eval_mul] using hq
    exact sub_eq_zero.mp hzero
  exact no_artinSchreier_polynomial_root q heq

theorem curvePoly_irreducible : Irreducible curvePoly := by
  rw [curvePoly_monic.irreducible_iff_roots_eq_zero_of_degree_le_three]
  · apply Multiset.eq_zero_of_forall_notMem
    intro q hq
    exact curvePoly_not_isRoot q
      ((mem_roots curvePoly_monic.ne_zero).mp hq)
  · norm_num [curvePoly_natDegree]
  · norm_num [curvePoly_natDegree]

instance curvePolyIrreducibleFact : Fact (Irreducible curvePoly) :=
  ⟨curvePoly_irreducible⟩

/-- The affine coordinate ring of the special fibre. -/
abbrev CoordinateRing : Type :=
  AdjoinRoot curvePoly

/-- Its fraction field. -/
abbrev FunctionField : Type :=
  FractionRing CoordinateRing

instance : IsDomain CoordinateRing :=
  AdjoinRoot.isDomain_of_prime curvePoly_irreducible.prime

noncomputable instance : Algebra K CoordinateRing :=
  inferInstance

noncomputable instance : Algebra K[X] CoordinateRing :=
  inferInstance

/-- Quotient map to the affine coordinate ring. -/
def mk : K[X][X] →+* CoordinateRing :=
  AdjoinRoot.mk curvePoly

/-- Embed a polynomial in the `X` coordinate. -/
def xClass (p : K[X]) : CoordinateRing :=
  mk (C p)

/-- The class of the `Y` coordinate. -/
def yClass : CoordinateRing :=
  mk X

/-- The polynomial-coordinate embedding. -/
def xClassHom : K[X] →+* CoordinateRing :=
  AdjoinRoot.of curvePoly

@[simp] theorem xClassHom_apply (p : K[X]) :
    xClassHom p = xClass p := rfl

@[simp] theorem xClass_zero : xClass 0 = 0 :=
  map_zero xClassHom

@[simp] theorem xClass_one : xClass 1 = 1 :=
  map_one xClassHom

@[simp] theorem xClass_natCast (n : ℕ) :
    xClass (n : K[X]) = (n : CoordinateRing) :=
  map_natCast xClassHom n

@[simp] theorem xClass_add (p q : K[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q

@[simp] theorem xClass_sub (p q : K[X]) :
    xClass (p - q) = xClass p - xClass q :=
  map_sub xClassHom p q

@[simp] theorem xClass_neg (p : K[X]) :
    xClass (-p) = -xClass p :=
  map_neg xClassHom p

@[simp] theorem xClass_mul (p q : K[X]) :
    xClass (p * q) = xClass p * xClass q :=
  map_mul xClassHom p q

@[simp] theorem xClass_pow (p : K[X]) (n : ℕ) :
    xClass (p ^ n) = xClass p ^ n :=
  map_pow xClassHom p n

/-- The canonical degree-less-than-two polynomial representative. -/
def normalPoly : CoordinateRing →ₗ[K[X]] K[X][X] :=
  AdjoinRoot.modByMonicHom curvePoly_monic

/-- Constant coefficient in the `1,Y` basis. -/
def coeff0 : CoordinateRing →ₗ[K[X]] K[X] :=
  (Polynomial.lcoeff K[X] 0).comp normalPoly

/-- `Y` coefficient in the `1,Y` basis. -/
def coeffY : CoordinateRing →ₗ[K[X]] K[X] :=
  (Polynomial.lcoeff K[X] 1).comp normalPoly

@[simp] theorem normalPoly_mk (g : K[X][X]) :
    normalPoly (mk g) = g %ₘ curvePoly := rfl

@[simp] theorem coeff0_mk (g : K[X][X]) :
    coeff0 (mk g) = (g %ₘ curvePoly).coeff 0 := rfl

@[simp] theorem coeffY_mk (g : K[X][X]) :
    coeffY (mk g) = (g %ₘ curvePoly).coeff 1 := rfl

theorem curvePoly_degree : curvePoly.degree = 2 := by
  rw [degree_eq_natDegree curvePoly_monic.ne_zero,
    curvePoly_natDegree]
  norm_num

theorem normalPoly_eq_C_add_C_mul_X (z : CoordinateRing) :
    normalPoly z = C (coeff0 z) + C (coeffY z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ curvePoly =
        C ((g %ₘ curvePoly).coeff 0) +
          C ((g %ₘ curvePoly).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := curvePoly) curvePoly_monic
        (n := 2) (by rw [curvePoly_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm

/-- Every coordinate-ring element has a unique rank-two expression. -/
theorem recompose (z : CoordinateRing) :
    xClass (coeff0 z) + xClass (coeffY z) * yClass = z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        xClass (coeff0 (mk g)) +
              xClass (coeffY (mk g)) * yClass =
            mk
              (C (coeff0 (mk g)) +
                C (coeffY (mk g)) * X) := by
                  simp only [xClass, yClass, mk, map_add, map_mul,
                    AdjoinRoot.mk_C, AdjoinRoot.mk_X]
        _ = mk (normalPoly (mk g)) := by
              rw [normalPoly_eq_C_add_C_mul_X]
        _ = mk g :=
          AdjoinRoot.mk_leftInverse curvePoly_monic (mk g)

@[simp] theorem coeff0_xClass (p : K[X]) :
    coeff0 (xClass p) = p := by
  change (C p %ₘ curvePoly).coeff 0 = p
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [degree_eq_natDegree curvePoly_monic.ne_zero,
        curvePoly_natDegree]
      norm_num)

@[simp] theorem coeffY_xClass (p : K[X]) :
    coeffY (xClass p) = 0 := by
  change (C p %ₘ curvePoly).coeff 1 = 0
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · exact degree_C_le.trans_lt (by
      rw [degree_eq_natDegree curvePoly_monic.ne_zero,
        curvePoly_natDegree]
      norm_num)

@[simp] theorem coeff0_yClass :
    coeff0 yClass = 0 := by
  change (X %ₘ curvePoly).coeff 0 = 0
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · rw [degree_X, degree_eq_natDegree curvePoly_monic.ne_zero,
      curvePoly_natDegree]
    norm_num

@[simp] theorem coeffY_yClass :
    coeffY yClass = 1 := by
  change (X %ₘ curvePoly).coeff 1 = 1
  rw [(modByMonic_eq_self_iff curvePoly_monic).mpr]
  · simp
  · rw [degree_X, degree_eq_natDegree curvePoly_monic.ne_zero,
      curvePoly_natDegree]
    norm_num

@[simp] theorem coeff0_xClass_mul_yClass (p : K[X]) :
    coeff0 (xClass p * yClass) = 0 := by
  change coeff0 ((algebraMap K[X] CoordinateRing p) * yClass) = 0
  rw [← Algebra.smul_def]
  simp

@[simp] theorem coeffY_xClass_mul_yClass (p : K[X]) :
    coeffY (xClass p * yClass) = p := by
  change coeffY ((algebraMap K[X] CoordinateRing p) * yClass) = p
  rw [← Algebra.smul_def]
  simp

@[simp] theorem yClass_relation :
    yClass ^ 2 + xClass hPoly * yClass = xClass rhsPoly := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [curvePoly]
  ring

theorem xClass_ne_zero {p : K[X]} (hp : p ≠ 0) :
    xClass p ≠ 0 := by
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt curvePoly_monic
    (C_ne_zero.mpr hp) (by rw [curvePoly_natDegree, natDegree_C]; norm_num)

/-! ## Generalized Mumford graph ideals -/

/-- Hyperelliptic conjugation sends a graph value `v` to `-h-v`. -/
def conjugateV (v : K[X]) : K[X] :=
  -hPoly - v

set_option maxHeartbeats 4000000 in
/-- Integral generalized Mumford data, including the Cantor quotient and
the precise smoothness Bézout identity needed for ideal invertibility. -/
structure SemiMumford where
  u : K[X]
  v : K[X]
  w : K[X]
  u_monic : u.Monic
  curve_eq : v ^ 2 + hPoly * v - rhsPoly = u * w
  bezout :
    ∃ a b c : K[X],
      a * u + b * (2 * v + hPoly) + c * w = 1

/-- The graph function `Y-v(X)`. -/
def ySubClass (v : K[X]) : CoordinateRing :=
  yClass - xClass v

/-- The integral graph ideal `(u,Y-v)`. -/
def mumfordIdeal (u v : K[X]) : Ideal CoordinateRing :=
  Ideal.span {xClass u, ySubClass v}

theorem xClass_mem_mumfordIdeal (u v : K[X]) :
    xClass u ∈ mumfordIdeal u v :=
  Ideal.subset_span (by simp)

theorem ySubClass_mem_mumfordIdeal (u v : K[X]) :
    ySubClass v ∈ mumfordIdeal u v :=
  Ideal.subset_span (by simp)

/-! ## Evaluation at a generalized Mumford graph -/

abbrev MumfordResidue (D : SemiMumford) : Type :=
  K[X] ⧸ Ideal.span ({D.u} : Set K[X])

theorem mumford_root_relation (D : SemiMumford) :
    curvePoly.eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v) = 0 := by
  change (X ^ 2 + C hPoly * X - C rhsPoly).eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v) = 0
  simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
    eval₂_mul]
  change Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X]))
    (D.v ^ 2 + hPoly * D.v - rhsPoly) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨D.w, D.curve_eq⟩

/-- Evaluation `X ↦ X mod u`, `Y ↦ v mod u`. -/
def mumfordEval (D : SemiMumford) :
    CoordinateRing →+* MumfordResidue D :=
  AdjoinRoot.lift
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v)
    (mumford_root_relation D)

@[simp] theorem mumfordEval_xClass
    (D : SemiMumford) (p : K[X]) :
    mumfordEval D (xClass p) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) p := by
  change mumfordEval D (AdjoinRoot.of curvePoly p) = _
  exact AdjoinRoot.lift_of (mumford_root_relation D)

@[simp] theorem mumfordEval_yClass (D : SemiMumford) :
    mumfordEval D yClass =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v :=
  AdjoinRoot.lift_root (mumford_root_relation D)

@[simp] theorem mumfordEval_ySubClass (D : SemiMumford) :
    mumfordEval D (ySubClass D.v) = 0 := by
  simp [ySubClass]

theorem mumfordIdeal_le_ker (D : SemiMumford) :
    mumfordIdeal D.u D.v ≤ RingHom.ker (mumfordEval D) := by
  apply Ideal.span_le.2
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · change mumfordEval D (xClass D.u) = 0
    rw [mumfordEval_xClass,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  · exact mumfordEval_ySubClass D

/-- The generalized Mumford graph ideal is exactly the evaluation kernel. -/
theorem ker_mumfordEval (D : SemiMumford) :
    RingHom.ker (mumfordEval D) = mumfordIdeal D.u D.v := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    let p : K[X] := coeff0 z
    let q : K[X] := coeffY z
    have hz' : mumfordEval D
        (xClass p + xClass q * yClass) = 0 := by
      rw [recompose]
      exact hz
    have hquot : Ideal.Quotient.mk
        (Ideal.span ({D.u} : Set K[X]))
        (p + q * D.v) = 0 := by
      simpa only [map_add, map_mul, mumfordEval_xClass,
        mumfordEval_yClass] using hz'
    have hdvd : D.u ∣ p + q * D.v :=
      Ideal.mem_span_singleton.mp
        (Ideal.Quotient.eq_zero_iff_mem.mp hquot)
    obtain ⟨s, hs⟩ := hdvd
    have hu : xClass D.u ∈ mumfordIdeal D.u D.v :=
      xClass_mem_mumfordIdeal D.u D.v
    have hyv : ySubClass D.v ∈ mumfordIdeal D.u D.v :=
      ySubClass_mem_mumfordIdeal D.u D.v
    have hbase : xClass (p + q * D.v) ∈
        mumfordIdeal D.u D.v := by
      rw [hs, xClass_mul, mul_comm]
      exact Ideal.mul_mem_left
        (mumfordIdeal D.u D.v) (xClass s) hu
    have hgraph : xClass q * ySubClass D.v ∈
        mumfordIdeal D.u D.v :=
      Ideal.mul_mem_left
        (mumfordIdeal D.u D.v) (xClass q) hyv
    rw [← recompose z]
    have hdecomp :
        xClass p + xClass q * yClass =
          xClass (p + q * D.v) +
            xClass q * ySubClass D.v := by
      simp only [xClass_add, xClass_mul, ySubClass]
      ring
    rw [hdecomp]
    exact Ideal.add_mem _ hbase hgraph
  · exact mumfordIdeal_le_ker D

theorem mumfordEval_surjective (D : SemiMumford) :
    Function.Surjective (mumfordEval D) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨xClass p, mumfordEval_xClass D p⟩

/-- The graph quotient is canonically the monic polynomial quotient. -/
noncomputable def mumfordQuotientEquiv (D : SemiMumford) :
    CoordinateRing ⧸ mumfordIdeal D.u D.v ≃+*
      MumfordResidue D :=
  (Ideal.quotEquivOfEq (ker_mumfordEval D).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (mumfordEval_surjective D))

@[simp] theorem mumfordQuotientEquiv_apply_mk
    (D : SemiMumford) (z : CoordinateRing) :
    mumfordQuotientEquiv D
        (Ideal.Quotient.mk (mumfordIdeal D.u D.v) z) =
      mumfordEval D z := by
  simp [mumfordQuotientEquiv]

/-- The graph quotient equivalence respects the coefficient field. -/
noncomputable def mumfordQuotientAlgEquiv (D : SemiMumford) :
    (CoordinateRing ⧸ mumfordIdeal D.u D.v) ≃ₐ[K]
      MumfordResidue D :=
  AlgEquiv.ofRingEquiv
    (f := mumfordQuotientEquiv D)
    (by
      intro r
      change
        mumfordQuotientEquiv D
            (Ideal.Quotient.mk
              (mumfordIdeal D.u D.v) (xClass (C r))) =
          Ideal.Quotient.mk
            (Ideal.span ({D.u} : Set K[X])) (C r)
      rw [mumfordQuotientEquiv_apply_mk,
        mumfordEval_xClass])

/-- The two graph generators multiply to the negative Cantor quotient. -/
theorem ySubClass_mul_conjugate (D : SemiMumford) :
    ySubClass D.v * ySubClass (conjugateV D.v) =
      -(xClass D.u * xClass D.w) := by
  calc
    ySubClass D.v * ySubClass (conjugateV D.v) =
        yClass ^ 2 + xClass hPoly * yClass -
          (xClass D.v ^ 2 + xClass hPoly * xClass D.v) := by
      simp only [ySubClass, conjugateV, xClass_neg, xClass_sub]
      ring
    _ = xClass rhsPoly -
          xClass (D.v ^ 2 + hPoly * D.v) := by
      rw [yClass_relation, xClass_add, xClass_mul, xClass_pow]
    _ = -xClass (D.v ^ 2 + hPoly * D.v - rhsPoly) := by
      rw [xClass_sub]
      ring
    _ = -xClass (D.u * D.w) := by rw [D.curve_eq]
    _ = -(xClass D.u * xClass D.w) := by rw [xClass_mul]

/-- The characteristic-two generalized graph ideal satisfies
`(u,Y-v)(u,Y+h+v)=(u)`. -/
theorem mumfordIdeal_mul_conj_integral (D : SemiMumford) :
    mumfordIdeal D.u D.v * mumfordIdeal D.u (conjugateV D.v) =
      Ideal.span ({xClass D.u} : Set CoordinateRing) := by
  let I := mumfordIdeal D.u D.v
  let J := mumfordIdeal D.u (conjugateV D.v)
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro p hp q hq
    rw [Ideal.mem_span_singleton]
    obtain ⟨p₀, pY, hpEq⟩ := Ideal.mem_span_pair.mp hp
    obtain ⟨q₀, qY, hqEq⟩ := Ideal.mem_span_pair.mp hq
    refine ⟨p₀ * q₀ * xClass D.u +
        p₀ * qY * ySubClass (conjugateV D.v) +
        pY * q₀ * ySubClass D.v -
        pY * qY * xClass D.w, ?_⟩
    rw [← hpEq, ← hqEq]
    linear_combination pY * qY * ySubClass_mul_conjugate D
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨a, b, c, hbez⟩ := D.bezout
    have huI : xClass D.u ∈ I :=
      xClass_mem_mumfordIdeal D.u D.v
    have huJ : xClass D.u ∈ J :=
      xClass_mem_mumfordIdeal D.u (conjugateV D.v)
    have hvI : ySubClass D.v ∈ I :=
      ySubClass_mem_mumfordIdeal D.u D.v
    have hvJ : ySubClass (conjugateV D.v) ∈ J :=
      ySubClass_mem_mumfordIdeal D.u (conjugateV D.v)
    have hu2 : xClass D.u * xClass D.u ∈ I * J :=
      Ideal.mul_mem_mul huI huJ
    have huv :
        xClass D.u * xClass (2 * D.v + hPoly) ∈ I * J := by
      have hp :
          xClass D.u * ySubClass (conjugateV D.v) ∈ I * J :=
        Ideal.mul_mem_mul huI hvJ
      have hm :
          ySubClass D.v * xClass D.u ∈ I * J :=
        Ideal.mul_mem_mul hvI huJ
      have hd := Ideal.sub_mem (I * J) hp hm
      convert hd using 1
      simp only [ySubClass, conjugateV, xClass_neg, xClass_sub,
        xClass_add, xClass_mul]
      have htwoPoly : (2 : K[X]) = 0 :=
        CharP.cast_eq_zero (K[X]) 2
      have htwoCoord : (2 : CoordinateRing) = 0 := by
        calc
          (2 : CoordinateRing) = xClass (2 : K[X]) :=
            (xClass_natCast 2).symm
          _ = xClass 0 := by rw [htwoPoly]
          _ = 0 := xClass_zero
      rw [htwoPoly, xClass_zero, zero_mul, zero_add]
      have hvadd : xClass D.v + xClass D.v = 0 := by
        rw [← two_mul, htwoCoord, zero_mul]
      calc
        xClass D.u * xClass hPoly =
            xClass D.u * xClass hPoly +
              xClass D.u * (xClass D.v + xClass D.v) := by
          rw [hvadd, mul_zero, add_zero]
        _ = xClass D.u *
              (yClass - (-xClass hPoly - xClass D.v)) -
            (yClass - xClass D.v) * xClass D.u := by ring
    have huw : xClass D.u * xClass D.w ∈ I * J := by
      have hg :
          ySubClass D.v * ySubClass (conjugateV D.v) ∈ I * J :=
        Ideal.mul_mem_mul hvI hvJ
      have hneg := (I * J).neg_mem hg
      rw [ySubClass_mul_conjugate] at hneg
      simpa using hneg
    have ha :
        xClass a * (xClass D.u * xClass D.u) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass a) hu2
    have hb :
        xClass b *
          (xClass D.u * xClass (2 * D.v + hPoly)) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass b) huv
    have hc :
        xClass c * (xClass D.u * xClass D.w) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass c) huw
    have hsum :=
      Ideal.add_mem (I * J) (Ideal.add_mem (I * J) ha hb) hc
    have heq :
        xClass a * (xClass D.u * xClass D.u) +
            xClass b *
              (xClass D.u * xClass (2 * D.v + hPoly)) +
            xClass c * (xClass D.u * xClass D.w) =
          xClass D.u := by
      calc
        _ = xClass D.u *
            xClass
              (a * D.u + b * (2 * D.v + hPoly) + c * D.w) := by
          simp only [xClass_add, xClass_mul]
          ring
        _ = xClass D.u * 1 := by rw [hbez, xClass_one]
        _ = xClass D.u := mul_one _
    rw [heq] at hsum
    exact hsum

theorem mumfordIdeal_mul_conj_fractional (D : SemiMumford) :
    (mumfordIdeal D.u D.v :
        FractionalIdeal CoordinateRing⁰ FunctionField) *
      (mumfordIdeal D.u (conjugateV D.v) :
        FractionalIdeal CoordinateRing⁰ FunctionField) =
      (Ideal.span ({xClass D.u} : Set CoordinateRing) :
        FractionalIdeal CoordinateRing⁰ FunctionField) := by
  rw [← coeIdeal_mul, mumfordIdeal_mul_conj_integral]

/-- Invertible fractional ideals of the special affine coordinate ring. -/
abbrev InvFrac :=
  (FractionalIdeal CoordinateRing⁰ FunctionField)ˣ

/-- A generalized Mumford graph ideal as a unit fractional ideal. -/
def mumfordIdealUnit (D : SemiMumford) : InvFrac :=
  Units.mkOfMulEqOne
    (mumfordIdeal D.u D.v :
      FractionalIdeal CoordinateRing⁰ FunctionField)
    ((mumfordIdeal D.u (conjugateV D.v) :
        FractionalIdeal CoordinateRing⁰ FunctionField) *
      (Ideal.span ({xClass D.u} : Set CoordinateRing) :
        FractionalIdeal CoordinateRing⁰ FunctionField)⁻¹)
    (by
      rw [← mul_assoc, mumfordIdeal_mul_conj_fractional]
      exact FractionalIdeal.coe_ideal_span_singleton_mul_inv
        FunctionField (xClass_ne_zero D.u_monic.ne_zero))

@[simp] theorem coe_mumfordIdealUnit (D : SemiMumford) :
    (mumfordIdealUnit D :
      FractionalIdeal CoordinateRing⁰ FunctionField) =
      mumfordIdeal D.u D.v := rfl

end

end MazurProof.N13GoodCoordinateRingTwo

end
end

-- module FLT.Assumptions.MazurProof.N13GeneralizedMumfordReduction
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GeneralizedMumfordReduction =====
section

/-!
# Reduction of integral N13 Mumford graphs at two

The good integral equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`

has the same coefficients after reduction from `ℤ₂` to `𝔽₂`.  Hence
coefficientwise reduction induces a canonical ring homomorphism between
the two affine coordinate rings.  This file proves that the homomorphism
preserves both coordinates and carries every generalized Mumford graph
ideal exactly to the corresponding special-fibre graph ideal.
-/

open Polynomial

namespace MazurProof.N13GeneralizedMumfordReduction

noncomputable section

abbrev R₂ : Type :=
  N13GeneralizedMumfordIntegral.TwoAdic.R₂

abbrev K : Type :=
  N13GoodCoordinateRingTwo.K

abbrev IntegralRing : Type :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := R₂)

abbrev SpecialRing : Type :=
  N13GoodCoordinateRingTwo.CoordinateRing

/-- Coefficient reduction from the two-adic integers to `𝔽₂`. -/
def reduceBase : R₂ →+* K :=
  PadicInt.toZMod

/-- Coefficientwise reduction of polynomials in the `X` coordinate. -/
def reducePoly : R₂[X] →+* K[X] :=
  Polynomial.mapRingHom reduceBase

@[simp] theorem reducePoly_apply (p : R₂[X]) :
    reducePoly p = p.map reduceBase := rfl

@[simp] theorem reduceBase_two :
    reduceBase (2 : R₂) = 0 := by
  rw [← RingHom.mem_ker, reduceBase, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p]
  exact Ideal.subset_span (by simp)

@[simp] theorem reduce_hPoly :
    reducePoly
        (N13GeneralizedMumfordIntegral.hPoly (R := R₂)) =
      N13GoodCoordinateRingTwo.hPoly := by
  simp [reducePoly, reduceBase,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GoodCoordinateRingTwo.hPoly]

@[simp] theorem reduce_rhsPoly :
    reducePoly
        (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)) =
      N13GoodCoordinateRingTwo.rhsPoly := by
  simp [reducePoly, reduceBase,
    N13GeneralizedMumfordIntegral.rhsPoly,
    N13GoodCoordinateRingTwo.rhsPoly]

theorem reduce_curvePoly :
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).map
        reducePoly =
      N13GoodCoordinateRingTwo.curvePoly := by
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    N13GoodCoordinateRingTwo.curvePoly, Polynomial.map_sub,
    Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_mul]
  change
    X ^ 2 +
          C (reducePoly
            (N13GeneralizedMumfordIntegral.hPoly (R := R₂))) * X -
        C (reducePoly
          (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂))) =
      X ^ 2 + C N13GoodCoordinateRingTwo.hPoly * X -
        C N13GoodCoordinateRingTwo.rhsPoly
  rw [reduce_hPoly, reduce_rhsPoly]

theorem special_curve_dvd :
    N13GoodCoordinateRingTwo.curvePoly ∣
      (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).map
        reducePoly := by
  rw [reduce_curvePoly]

/-- Reduction on the affine coordinate ring of the good equation. -/
def reduceCoordinate : IntegralRing →+* SpecialRing :=
  AdjoinRoot.map reducePoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    N13GoodCoordinateRingTwo.curvePoly
    special_curve_dvd

@[simp] theorem reduce_xClass (p : R₂[X]) :
    reduceCoordinate
        (N13GeneralizedMumfordIntegral.xClass (R := R₂) p) =
      N13GoodCoordinateRingTwo.xClass (reducePoly p) := by
  exact AdjoinRoot.map_of
    reducePoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    N13GoodCoordinateRingTwo.curvePoly
    special_curve_dvd p

@[simp] theorem reduce_yClass :
    reduceCoordinate
        (N13GeneralizedMumfordIntegral.yClass (R := R₂)) =
      N13GoodCoordinateRingTwo.yClass := by
  exact AdjoinRoot.map_root
    reducePoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    N13GoodCoordinateRingTwo.curvePoly
    special_curve_dvd

@[simp] theorem reduce_ySubClass (v : R₂[X]) :
    reduceCoordinate
        (N13GeneralizedMumfordIntegral.ySubClass (R := R₂) v) =
      N13GoodCoordinateRingTwo.ySubClass (reducePoly v) := by
  simp [N13GeneralizedMumfordIntegral.ySubClass,
    N13GoodCoordinateRingTwo.ySubClass]

/-- Coefficientwise reduction of polynomials is onto. -/
theorem reducePoly_surjective :
    Function.Surjective reducePoly :=
  Polynomial.map_surjective
    reduceBase
    (ZMod.ringHom_surjective PadicInt.toZMod)

/-- The integral good-model coordinate ring reduces onto its special fibre.
This follows from the common rank-two normal form, not from a presentation
calculation in the quotient. -/
theorem reduceCoordinate_surjective :
    Function.Surjective reduceCoordinate := by
  intro z
  obtain ⟨p, hp⟩ :=
    reducePoly_surjective
      (N13GoodCoordinateRingTwo.coeff0 z)
  obtain ⟨q, hq⟩ :=
    reducePoly_surjective
      (N13GoodCoordinateRingTwo.coeffY z)
  refine ⟨
    N13GeneralizedMumfordIntegral.xClass p +
      N13GeneralizedMumfordIntegral.xClass q *
        N13GeneralizedMumfordIntegral.yClass,
    ?_⟩
  simp only [map_add, map_mul, reduce_xClass, reduce_yClass,
    hp, hq]
  exact N13GoodCoordinateRingTwo.recompose z

@[simp] theorem reduce_coeff0 (z : IntegralRing) :
    N13GoodCoordinateRingTwo.coeff0 (reduceCoordinate z) =
      reducePoly
        (N13GeneralizedMumfordIntegral.coeff0 z) := by
  calc
    N13GoodCoordinateRingTwo.coeff0 (reduceCoordinate z) =
        N13GoodCoordinateRingTwo.coeff0
          (reduceCoordinate
            (N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeff0 z) +
              N13GeneralizedMumfordIntegral.xClass
                  (N13GeneralizedMumfordIntegral.coeffY z) *
                N13GeneralizedMumfordIntegral.yClass)) := by
          rw [N13GeneralizedMumfordIntegral.recompose]
    _ = reducePoly
          (N13GeneralizedMumfordIntegral.coeff0 z) := by
      simp only [map_add, map_mul, reduce_xClass, reduce_yClass,
        N13GoodCoordinateRingTwo.coeff0_xClass,
        N13GoodCoordinateRingTwo.coeff0_xClass_mul_yClass,
        add_zero]

@[simp] theorem reduce_coeffY (z : IntegralRing) :
    N13GoodCoordinateRingTwo.coeffY (reduceCoordinate z) =
      reducePoly
        (N13GeneralizedMumfordIntegral.coeffY z) := by
  calc
    N13GoodCoordinateRingTwo.coeffY (reduceCoordinate z) =
        N13GoodCoordinateRingTwo.coeffY
          (reduceCoordinate
            (N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeff0 z) +
              N13GeneralizedMumfordIntegral.xClass
                  (N13GeneralizedMumfordIntegral.coeffY z) *
                N13GeneralizedMumfordIntegral.yClass)) := by
          rw [N13GeneralizedMumfordIntegral.recompose]
    _ = reducePoly
          (N13GeneralizedMumfordIntegral.coeffY z) := by
      simp only [map_add, map_mul, reduce_xClass, reduce_yClass,
        N13GoodCoordinateRingTwo.coeffY_xClass,
        N13GoodCoordinateRingTwo.coeffY_xClass_mul_yClass,
        zero_add]

theorem exists_eq_C_two_mul_of_reducePoly_eq_zero
    (p : R₂[X]) (hp : reducePoly p = 0) :
    ∃ q : R₂[X], p = C (2 : R₂) * q := by
  have hmem :
      p ∈ RingHom.ker reducePoly :=
    RingHom.mem_ker.mpr hp
  rw [reducePoly, Polynomial.ker_mapRingHom, reduceBase,
    PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at hmem
  exact hmem

/-- Reduction has exactly the vertical principal ideal `(2)` as kernel.
The proof combines the rank-two normal form with the polynomial-map kernel
theorem and the standard description of the maximal ideal of `ℤ₂`. -/
theorem ker_reduceCoordinate :
    RingHom.ker reduceCoordinate =
      Ideal.span
        ({algebraMap R₂ IntegralRing (2 : R₂)} :
          Set IntegralRing) := by
  apply le_antisymm
  · intro z hz
    have hz0 : reduceCoordinate z = 0 :=
      RingHom.mem_ker.mp hz
    have h0 :
        reducePoly
          (N13GeneralizedMumfordIntegral.coeff0 z) = 0 := by
      rw [← reduce_coeff0 z, hz0]
      simp
    have hY :
        reducePoly
          (N13GeneralizedMumfordIntegral.coeffY z) = 0 := by
      rw [← reduce_coeffY z, hz0]
      simp
    obtain ⟨p, hp⟩ :=
      exists_eq_C_two_mul_of_reducePoly_eq_zero _ h0
    obtain ⟨q, hq⟩ :=
      exists_eq_C_two_mul_of_reducePoly_eq_zero _ hY
    rw [Ideal.mem_span_singleton]
    refine ⟨
      N13GeneralizedMumfordIntegral.xClass p +
        N13GeneralizedMumfordIntegral.xClass q *
          N13GeneralizedMumfordIntegral.yClass,
      ?_⟩
    rw [← N13GeneralizedMumfordIntegral.recompose z, hp, hq]
    calc
      N13GeneralizedMumfordIntegral.xClass (C 2 * p) +
          N13GeneralizedMumfordIntegral.xClass (C 2 * q) *
            N13GeneralizedMumfordIntegral.yClass =
        N13GeneralizedMumfordIntegral.xClass (C 2) *
          (N13GeneralizedMumfordIntegral.xClass p +
            N13GeneralizedMumfordIntegral.xClass q *
              N13GeneralizedMumfordIntegral.yClass) := by
          simp only [mul_add,
            N13GeneralizedMumfordIntegral.xClass_mul]
          ring
      _ = algebraMap R₂ IntegralRing (2 : R₂) *
          (N13GeneralizedMumfordIntegral.xClass p +
            N13GeneralizedMumfordIntegral.xClass q *
              N13GeneralizedMumfordIntegral.yClass) := rfl
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change
      algebraMap R₂ IntegralRing (2 : R₂) ∈
        RingHom.ker reduceCoordinate
    rw [RingHom.mem_ker]
    change reduceCoordinate
      (N13GeneralizedMumfordIntegral.xClass (C (2 : R₂))) = 0
    rw [reduce_xClass]
    simp [reducePoly]

/-- Reduction carries the integral graph ideal onto, rather than merely
into, the graph ideal with reduced coefficients. -/
theorem map_mumfordIdeal (u v : R₂[X]) :
    Ideal.map reduceCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) u v) =
      N13GoodCoordinateRingTwo.mumfordIdeal
        (reducePoly u) (reducePoly v) := by
  rw [N13GeneralizedMumfordIntegral.mumfordIdeal,
    N13GoodCoordinateRingTwo.mumfordIdeal, Ideal.map_span,
    Set.image_pair, reduce_xClass, reduce_ySubClass]

set_option maxHeartbeats 4000000 in
/-- Integral generalized Mumford data carrying the smoothness Bézout
identity.  This is precisely the extra condition needed for the reduced
graph ideal to be invertible. -/
structure SmoothMumford₂ : Type
    extends
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂ where
  bezout :
    ∃ a b c : R₂[X],
      a * u + b * (2 * v +
        N13GeneralizedMumfordIntegral.hPoly (R := R₂)) +
          c * w = 1

/-- Smooth integral Mumford data reduce to the already constructed smooth
special-fibre data. -/
def reduceSmoothMumford
    (D : SmoothMumford₂) :
    N13GoodCoordinateRingTwo.SemiMumford where
  u := reducePoly D.u
  v := reducePoly D.v
  w := reducePoly D.w
  u_monic := D.u_monic.map reduceBase
  curve_eq := by
    have h := congrArg reducePoly D.curve_eq
    simpa only [map_add, map_sub, map_mul, map_pow,
      reduce_hPoly, reduce_rhsPoly] using h
  bezout := by
    obtain ⟨a, b, c, habc⟩ := D.bezout
    refine ⟨reducePoly a, reducePoly b, reducePoly c, ?_⟩
    have h := congrArg reducePoly habc
    simpa only [map_add, map_mul, map_ofNat, map_one,
      reduce_hPoly] using h

@[simp] theorem reduceSmoothMumford_u
    (D : SmoothMumford₂) :
    (reduceSmoothMumford D).u = reducePoly D.u := rfl

@[simp] theorem reduceSmoothMumford_v
    (D : SmoothMumford₂) :
    (reduceSmoothMumford D).v = reducePoly D.v := rfl

/-- The exact ideal reduction theorem, now stated for smooth integral data. -/
theorem map_smoothMumfordIdeal
    (D : SmoothMumford₂) :
    Ideal.map reduceCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) D.u D.v) =
      N13GoodCoordinateRingTwo.mumfordIdeal
        (reduceSmoothMumford D).u
        (reduceSmoothMumford D).v := by
  simpa using map_mumfordIdeal D.u D.v

end

end MazurProof.N13GeneralizedMumfordReduction

end
end

-- module FLT.Assumptions.MazurProof.N13AbelChartBase
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13AbelChartBase =====
section

/-!
# The nonspecial base divisor for the N13 Abel chart

The integral divisor

`(0,0) + (-1,0)`

has generalized Mumford pair `u = X² + X`, `v = 0`.  Its reduction is the
unordered pair of the sheet-zero points over the distinct affine base
coordinates `0` and `1`.  A canonical hyperelliptic fibre contains one
point on each sheet, so this reduced divisor is noncanonical.

The same base pair satisfies a short Bézout identity.  Hence its graph ideal
is one of the smooth integral Mumford ideals already shown to commute with
reduction.
-/

open Polynomial

namespace MazurProof.N13AbelChartBase

noncomputable section

open N13AbelFiberTwoModel
open N13SymmetricSquareTwo

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  ℤ_[2]

abbrev K : Type :=
  N13AbelFiberTwoModel.K

/-- The special-fibre point `(0,0)`. -/
def p00 : N13AbelFiberTwoModel.CurvePoint :=
  curvePointEquiv.symm (Sum.inl 0, 0)

/-- The special-fibre point `(1,0)`, which is the reduction of `(-1,0)`. -/
def p10 : N13AbelFiberTwoModel.CurvePoint :=
  curvePointEquiv.symm (Sum.inl 1, 0)

/-- Reduction of the selected integral degree-two divisor. -/
def specialBaseDivisor :
    N13SymmetricSquareTwo.EffectiveDivisorTwo :=
  s(p00, p10)

def sheet
    (P : N13AbelFiberTwoModel.CurvePoint) : K :=
  (curvePointEquiv P).2

@[simp] private theorem sheet_p00 :
    sheet p00 = 0 := by
  simp [sheet, p00]

@[simp] private theorem sheet_p10 :
    sheet p10 = 0 := by
  simp [sheet, p10]

@[simp] private theorem sheet_canonical_zero
    (b : BasePoint) :
    sheet (curvePointEquiv.symm (b, 0)) = 0 := by
  simp [sheet]

@[simp] private theorem sheet_canonical_one
    (b : BasePoint) :
    sheet (curvePointEquiv.symm (b, 1)) = 1 := by
  simp [sheet]

/-- The base divisor is outside the canonical hyperelliptic pencil.  The
proof only compares sheet coordinates; it does not enumerate curve points. -/
theorem specialBaseDivisor_not_canonical :
    ¬IsCanonical specialBaseDivisor := by
  rintro ⟨b, hb⟩
  change
    s(curvePointEquiv.symm (b, 0),
      curvePointEquiv.symm (b, 1)) =
        s(p00, p10) at hb
  rw [Sym2.eq_iff] at hb
  rcases hb with hb | hb
  · have hs := congrArg sheet hb.2
    simp at hs
  · have hs := congrArg sheet hb.2
    simp at hs

/-- The smooth integral generalized Mumford datum of the selected base
divisor.  The Bézout certificate is

`(X-1)u + h + 2w = 1`.
-/
def baseSmoothMumford :
    N13GeneralizedMumfordReduction.SmoothMumford₂ where
  u := N13FormalAbelLinearization.uBase
  v := 0
  w := -X ^ 3
  u_monic := N13FormalAbelLinearization.uBase_monic
  curve_eq := by
    simp only [N13GeneralizedMumfordIntegral.hPoly,
      N13GeneralizedMumfordIntegral.rhsPoly,
      N13FormalAbelLinearization.uBase]
    ring
  bezout := by
    refine ⟨X - 1, 1, 2, ?_⟩
    simp only [N13FormalAbelLinearization.uBase,
      N13GeneralizedMumfordIntegral.hPoly]
    ring

@[simp] theorem baseSmoothMumford_u :
    baseSmoothMumford.u =
      N13FormalAbelLinearization.uBase := rfl

@[simp] theorem baseSmoothMumford_v :
    baseSmoothMumford.v = 0 := rfl

/-- The integral base graph reduces to the same polynomial pair
`(X²+X,0)` in characteristic two. -/
theorem reduce_baseSmoothMumford_u :
    (N13GeneralizedMumfordReduction.reduceSmoothMumford
      baseSmoothMumford).u =
        (X ^ 2 + X :
          N13GoodCoordinateRingTwo.K[X]) := by
  simp [baseSmoothMumford,
    N13FormalAbelLinearization.uBase,
    N13GeneralizedMumfordReduction.reducePoly,
    N13GeneralizedMumfordReduction.reduceBase]

@[simp] theorem reduce_baseSmoothMumford_v :
    (N13GeneralizedMumfordReduction.reduceSmoothMumford
      baseSmoothMumford).v = 0 := by
  simp [baseSmoothMumford,
    N13GeneralizedMumfordReduction.reducePoly]

end

end MazurProof.N13AbelChartBase

end
end

-- module FLT.Assumptions.MazurProof.SexticMumford
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumford =====
section

/-!
# Balanced Mumford data for a separable monic sextic

This file contains the curve-independent algebra underlying the balanced
Mumford representation for a genus-two curve

`Y² = f(X)`,

where `f` is monic, separable, and has degree six.  Arithmetic for a specific
curve belongs in a separate model instance.

The semantic target is an oriented fractional-ideal quotient of the affine
coordinate ring.  Constructing the order at a chosen point at infinity and
proving the normal-form theorem are deliberately separate later layers.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

set_option maxHeartbeats 4000000 in
/-- A smooth monic degree-six hyperelliptic equation. -/
structure Model (K : Type u) [Field K] where
  f : K[X]
  monic : f.Monic
  natDegree : f.natDegree = 6
  separable : f.Separable
  two_ne_zero : (2 : K) ≠ 0

variable {K : Type u} [Field K]

namespace Model

theorem squarefree (M : Model K) : Squarefree M.f :=
  M.separable.squarefree

theorem ne_zero (M : Model K) : M.f ≠ 0 :=
  M.monic.ne_zero

theorem not_isUnit (M : Model K) : ¬IsUnit M.f :=
  Polynomial.not_isUnit_of_natDegree_pos M.f (by rw [M.natDegree]; norm_num)

end Model

variable (M : Model K)

/-! ## The affine coordinate ring -/

/-- The outer variable is `Y`; its coefficients are polynomials in `X`. -/
def curvePoly : K[X][X] :=
  X ^ 2 - C M.f

theorem curvePoly_monic : (curvePoly M).Monic := by
  unfold curvePoly
  monicity!

theorem curvePoly_natDegree : (curvePoly M).natDegree = 2 := by
  unfold curvePoly
  compute_degree!

theorem curvePoly_not_isRoot (q : K[X]) :
    ¬IsRoot (curvePoly M) q := by
  intro hq
  have hsq : q ^ 2 = M.f := by
    simpa only [IsRoot.def, curvePoly, eval_sub, eval_pow, eval_X, eval_C,
      sub_eq_zero] using hq
  have hqunit : IsUnit q := by
    apply M.squarefree q
    refine ⟨1, ?_⟩
    simpa only [mul_one, pow_two] using hsq.symm
  have hfunit : IsUnit M.f := by
    rw [← hsq]
    exact hqunit.pow 2
  exact M.not_isUnit hfunit

theorem curvePoly_irreducible : Irreducible (curvePoly M) := by
  rw [(curvePoly_monic M).irreducible_iff_roots_eq_zero_of_degree_le_three]
  · apply Multiset.eq_zero_of_forall_notMem
    intro q hq
    exact curvePoly_not_isRoot M q
      ((mem_roots (curvePoly_monic M).ne_zero).mp hq)
  · norm_num [curvePoly_natDegree]
  · norm_num [curvePoly_natDegree]

instance curvePolyIrreducibleFact : Fact (Irreducible (curvePoly M)) :=
  ⟨curvePoly_irreducible M⟩

abbrev CoordinateRing : Type u :=
  AdjoinRoot (curvePoly M)

abbrev FunctionField : Type u :=
  FractionRing (CoordinateRing M)

instance : IsDomain (CoordinateRing M) :=
  AdjoinRoot.isDomain_of_prime (curvePoly_irreducible M).prime

noncomputable instance : Algebra K (CoordinateRing M) :=
  inferInstance

noncomputable instance : Algebra K[X] (CoordinateRing M) :=
  inferInstance

/-- Quotient map to the affine coordinate ring. -/
def mk : K[X][X] →+* CoordinateRing M :=
  AdjoinRoot.mk (curvePoly M)

/-- Embed a polynomial in the `X` coordinate into the coordinate ring. -/
def xClass (p : K[X]) : CoordinateRing M :=
  mk M (C p)

/-- The class of the `Y` coordinate. -/
def yClass : CoordinateRing M :=
  mk M X

@[simp] theorem yClass_sq :
    yClass M ^ 2 = xClass M M.f := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [curvePoly]
  ring

theorem xClass_ne_zero {p : K[X]} (hp : p ≠ 0) :
    xClass M p ≠ 0 := by
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt (curvePoly_monic M)
    (C_ne_zero.mpr hp) (by rw [curvePoly_natDegree, natDegree_C]; norm_num)

/-! ## Balanced triples -/

set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
/-- A balanced Mumford representative for a divisor class on a monic sextic
with two distinguished points at infinity. -/
structure Mumford where
  u : K[X]
  v : K[X]
  nInf : ℕ
  u_monic : u.Monic
  deg_u : u.natDegree ≤ 2
  v_reduced : v % u = v
  curve_dvd : u ∣ M.f - v ^ 2
  infinity_bound : u.natDegree + nInf ≤ 2

set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
/-- The unreduced integral version used during ideal multiplication. -/
structure SemiMumford where
  u : K[X]
  v : K[X]
  nInf : ℤ
  u_monic : u.Monic
  v_reduced : v % u = v
  curve_dvd : u ∣ M.f - v ^ 2

/-- Forget the balancing bounds while retaining the ideal data. -/
def Mumford.toSemi (D : Mumford M) : SemiMumford M where
  u := D.u
  v := D.v
  nInf := D.nInf
  u_monic := D.u_monic
  v_reduced := D.v_reduced
  curve_dvd := D.curve_dvd

@[simp] theorem toSemi_u (D : Mumford M) : D.toSemi.u = D.u := rfl

@[simp] theorem toSemi_v (D : Mumford M) : D.toSemi.v = D.v := rfl

@[simp] theorem toSemi_nInf (D : Mumford M) : D.toSemi.nInf = D.nInf := rfl

/-- The balanced representative of the identity class. -/
def zero : Mumford M where
  u := 1
  v := 0
  nInf := 1
  u_monic := monic_one
  deg_u := by simp
  v_reduced := by simp
  curve_dvd := one_dvd _
  infinity_bound := by simp

@[simp] theorem zero_u : (zero M).u = 1 := rfl

@[simp] theorem zero_v : (zero M).v = 0 := rfl

@[simp] theorem zero_nInf : (zero M).nInf = 1 := rfl

/-! ## Curve points and their balanced representatives -/

/-- The two-infinity projective completion of the affine sextic. -/
inductive CurvePoint where
  | infinityPlus
  | infinityMinus
  | affine (x y : K) (onCurve : y ^ 2 = M.f.eval x)

/-- With `∞₊` as base point, an affine point `(x,y)` is represented by
`(X-x,y,0)`. -/
def affinePointMumford (x y : K) (h : y ^ 2 = M.f.eval x) :
    Mumford M where
  u := X - C x
  v := C y
  nInf := 0
  u_monic := monic_X_sub_C x
  deg_u := by simp
  v_reduced := by
    rw [mod_eq_self_iff (monic_X_sub_C x).ne_zero]
    exact degree_C_le.trans_lt (by rw [degree_X_sub_C]; norm_num)
  curve_dvd := by
    have heval : (M.f - (C y) ^ 2).eval x = 0 := by
      rw [eval_sub, eval_pow, eval_C, ← h, sub_self]
    have hd := X_sub_C_dvd_sub_C_eval (p := M.f - (C y) ^ 2) (a := x)
    simpa only [heval, C_0, sub_zero] using hd
  infinity_bound := by simp

/-- The negative point at infinity is represented by `(1,0,0)`. -/
def infinityMinusMumford : Mumford M where
  u := 1
  v := 0
  nInf := 0
  u_monic := monic_one
  deg_u := by simp
  v_reduced := by simp
  curve_dvd := one_dvd _
  infinity_bound := by simp

/-- The balanced representative attached to a projective curve point. -/
def pointMumford : CurvePoint M → Mumford M
  | .infinityPlus => zero M
  | .infinityMinus => infinityMinusMumford M
  | .affine x y h => affinePointMumford M x y h

theorem X_sub_C_ne_one (x : K) :
    (X - C x : K[X]) ≠ 1 := by
  intro h
  have hc := congrArg (fun p : K[X] ↦ p.coeff 1) h
  rw [coeff_one] at hc
  norm_num at hc

theorem X_sub_C_injective :
    Function.Injective (fun x : K ↦ (X - C x : K[X])) := by
  intro x y h
  have hc := congrArg (fun p : K[X] ↦ p.coeff 0) h
  simpa using congrArg Neg.neg hc

/-- Distinct projective points have distinct balanced representatives. -/
theorem pointMumford_injective :
    Function.Injective (pointMumford M) := by
  intro P Q hPQ
  cases P with
  | infinityPlus =>
      cases Q with
      | infinityPlus => rfl
      | infinityMinus =>
          have hn := congrArg Mumford.nInf hPQ
          norm_num [pointMumford, zero, infinityMinusMumford] at hn
      | affine x y h =>
          have hn := congrArg Mumford.nInf hPQ
          norm_num [pointMumford, zero, affinePointMumford] at hn
  | infinityMinus =>
      cases Q with
      | infinityPlus =>
          have hn := congrArg Mumford.nInf hPQ
          norm_num [pointMumford, zero, infinityMinusMumford] at hn
      | infinityMinus => rfl
      | affine x y h =>
          have hu := congrArg Mumford.u hPQ
          change (1 : K[X]) = X - C x at hu
          exact False.elim (X_sub_C_ne_one x hu.symm)
  | affine x y h =>
      cases Q with
      | infinityPlus =>
          have hn := congrArg Mumford.nInf hPQ
          norm_num [pointMumford, zero, affinePointMumford] at hn
      | infinityMinus =>
          have hu := congrArg Mumford.u hPQ
          change X - C x = (1 : K[X]) at hu
          exact False.elim (X_sub_C_ne_one x hu)
      | affine x' y' h' =>
          have hu := congrArg Mumford.u hPQ
          have hv := congrArg Mumford.v hPQ
          change X - C x = X - C x' at hu
          change C y = C y' at hv
          have hx : x = x' := X_sub_C_injective hu
          have hy : y = y' := C_injective hv
          subst x'
          subst y'
          rfl

/-! ## Mumford ideals -/

def ySubClass (v : K[X]) : CoordinateRing M :=
  yClass M - xClass M v

def mumfordIdeal (u v : K[X]) : Ideal (CoordinateRing M) :=
  Ideal.span {xClass M u, ySubClass M v}

theorem xClass_mem_mumfordIdeal (u v : K[X]) :
    xClass M u ∈ mumfordIdeal M u v := by
  exact Ideal.subset_span (by simp)

/-! ## The oriented fractional-ideal quotient -/

abbrev InvFrac : Type u :=
  (FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))ˣ

abbrev OrientedFrac : Type u :=
  InvFrac M × Multiplicative ℤ

set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
set_option maxHeartbeats 2000000 in
/-- The valuation datum at the chosen positive point at infinity. -/
structure InfinityOrder where
  ordPlus : (FunctionField M)ˣ →* Multiplicative ℤ

def principalOriented (O : InfinityOrder M) :
    (FunctionField M)ˣ →* OrientedFrac M :=
  (toPrincipalIdeal (CoordinateRing M) (FunctionField M)).prod O.ordPlus

abbrev OrientedPic (O : InfinityOrder M) : Type u :=
  Additive (OrientedFrac M ⧸ (principalOriented M O).range)

instance (O : InfinityOrder M) : AddCommGroup (OrientedPic M O) :=
  inferInstance

end

end MazurProof.SexticMumford

end
end

-- module FLT.Assumptions.MazurProof.N13Mumford
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13Mumford =====
section

/-!
# The smooth sextic and Mumford model for `X₁(13)`

This file instantiates the curve-independent balanced Mumford layer with the
standard sextic model of `X₁(13)`.  Smoothness is proved by a short Bézout
identity between the sextic and its derivative.
-/

open Polynomial

namespace MazurProof.N13Mumford

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

/-- The standard sextic over an arbitrary characteristic-zero field. -/
def f : K[X] :=
  X ^ 6 + 4 * X ^ 5 + 6 * X ^ 4 + 2 * X ^ 3 + X ^ 2 + 2 * X + 1

def fQ : ℚ[X] :=
  X ^ 6 + 4 * X ^ 5 + 6 * X ^ 4 + 2 * X ^ 3 + X ^ 2 + 2 * X + 1

omit [CharZero K] in
theorem f_monic : (f K).Monic := by
  unfold f
  monicity!

theorem f_natDegree : (f K).natDegree = 6 := by
  unfold f
  compute_degree!

def bezoutA : ℚ[X] :=
  300 * X ^ 4 + 784 * X ^ 3 + 606 * X ^ 2 - 192 * X + 234

def bezoutB : ℚ[X] :=
  -50 * X ^ 5 - 164 * X ^ 4 - 177 * X ^ 3 + 40 * X ^ 2 - 73 * X - 65

theorem C_nat (n : ℕ) : C (n : ℚ) = (n : ℚ[X]) := by
  exact map_natCast (C : ℚ →+* ℚ[X]) n

theorem fQ_derivative :
    fQ.derivative =
      6 * X ^ 5 + 20 * X ^ 4 + 24 * X ^ 3 + 6 * X ^ 2 + 2 * X + 2 := by
  simp only [fQ, derivative_add, derivative_one, derivative_X, derivative_pow,
    derivative_ofNat, derivative_mul, zero_mul, zero_add, add_zero]
  rw [C_nat 2, C_nat 3, C_nat 4, C_nat 5, C_nat 6]
  ring

/-- A small fixed smoothness certificate for the `X₁(13)` sextic. -/
theorem fQ_bezout_derivative :
    bezoutA * fQ + bezoutB * fQ.derivative = 104 := by
  rw [fQ_derivative]
  simp only [bezoutA, bezoutB, fQ]
  ring

theorem fQ_separable : fQ.Separable := by
  rw [separable_def']
  refine ⟨C (1 / 104 : ℚ) * bezoutA, C (1 / 104 : ℚ) * bezoutB, ?_⟩
  calc
    (C (1 / 104 : ℚ) * bezoutA) * fQ +
        (C (1 / 104 : ℚ) * bezoutB) * fQ.derivative =
      C (1 / 104 : ℚ) * (bezoutA * fQ + bezoutB * fQ.derivative) := by
        ring
    _ = C (1 / 104 : ℚ) * 104 := by rw [fQ_bezout_derivative]
    _ = C (1 / 104 : ℚ) * C 104 := by rw [C_ofNat]
    _ = 1 := by rw [← C_mul]; norm_num

theorem f_eq_map :
    f K = fQ.map (algebraMap ℚ K) := by
  simp [f, fQ]

theorem f_separable : (f K).Separable := by
  rw [f_eq_map]
  exact (separable_map (algebraMap ℚ K)).mpr fQ_separable

/-- The `X₁(13)` instance of the generic smooth monic sextic model. -/
def model : SexticMumford.Model K where
  f := f K
  monic := f_monic K
  natDegree := f_natDegree K
  separable := f_separable K
  two_ne_zero := by norm_num

@[simp] theorem model_f :
    (model K).f = f K := rfl

theorem f_eval_eq_sexticF13 (x : ℚ) :
    (f ℚ).eval x = N13CurveModel.sexticF13 x := by
  simp [f, N13CurveModel.sexticF13]

abbrev CoordinateRing : Type u :=
  SexticMumford.CoordinateRing (model K)

abbrev FunctionField : Type u :=
  SexticMumford.FunctionField (model K)

abbrev Mumford : Type u :=
  SexticMumford.Mumford (model K)

abbrev SemiMumford : Type u :=
  SexticMumford.SemiMumford (model K)

/-! ## The six rational cusps -/

/-- Names for the six rational cusps on the smooth projective curve. -/
inductive Cusp13
  | infinityPlus
  | infinityMinus
  | zeroPlus
  | zeroMinus
  | negOnePlus
  | negOneMinus
  deriving DecidableEq

instance : Fintype Cusp13 where
  elems := {Cusp13.infinityPlus, Cusp13.infinityMinus, Cusp13.zeroPlus, Cusp13.zeroMinus,
    Cusp13.negOnePlus, Cusp13.negOneMinus}
  complete := by intro x; cases x <;> decide

/-- The six cusps as points of the generic two-infinity sextic model. -/
def cuspPoint : Cusp13 → SexticMumford.CurvePoint (model ℚ)
  | .infinityPlus => .infinityPlus
  | .infinityMinus => .infinityMinus
  | .zeroPlus => .affine 0 1 (by norm_num [model, f])
  | .zeroMinus => .affine 0 (-1) (by norm_num [model, f])
  | .negOnePlus => .affine (-1) 1 (by norm_num [model, f])
  | .negOneMinus => .affine (-1) (-1) (by norm_num [model, f])

/-- A scalar point on the sextic gives a point of its projective completion. -/
def affineCurvePoint (X Y : ℚ) (h : N13CurveModel.C13SexticEq X Y) :
    SexticMumford.CurvePoint (model ℚ) :=
  .affine X Y (by
    change Y ^ 2 = (f ℚ).eval X
    rw [f_eval_eq_sexticF13]
    exact h)

end

end MazurProof.N13Mumford

end
end

-- module FLT.Assumptions.MazurProof.N13GoodSexticCoordinateEquiv
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodSexticCoordinateEquiv =====
section

/-!
# Completing the square on the N13 coordinate rings

Over any field of characteristic zero, the good generalized equation

`y² + (X³+X+1)y = X⁵+X⁴`

and the sextic equation already used by the concrete Picard group are
isomorphic by

`Y = 2y + (X³+X+1)`.

This file constructs that isomorphism directly from the two `AdjoinRoot`
presentations and records its action on both coordinates.  It is the
algebraic bridge needed to interpret integral generalized Mumford graph
ideals as classes in the existing oriented sextic Picard group.
-/

open Polynomial

namespace MazurProof.N13GoodSexticCoordinateEquiv

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K]

abbrev M : SexticMumford.Model K :=
  N13Mumford.model K

abbrev GoodRing : Type u :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := K)

abbrev SexticRing : Type u :=
  N13Mumford.CoordinateRing K

def goodXHom : K[X] →+* GoodRing (K := K) :=
  N13GeneralizedMumfordIntegral.xClassHom

def sexticXHom : K[X] →+* SexticRing (K := K) :=
  AdjoinRoot.of (SexticMumford.curvePoly (M (K := K)))

@[simp] theorem goodXHom_apply (p : K[X]) :
    goodXHom (K := K) p =
      N13GeneralizedMumfordIntegral.xClass p := rfl

@[simp] theorem sexticXHom_apply (p : K[X]) :
    sexticXHom (K := K) p =
      SexticMumford.xClass (M (K := K)) p := rfl

abbrev hPoly : K[X] :=
  N13GeneralizedMumfordIntegral.hPoly

abbrev rhsPoly : K[X] :=
  N13GeneralizedMumfordIntegral.rhsPoly

/-- The polynomial identity behind completion of the square. -/
theorem sextic_eq_h_sq_add_four_rhs :
    N13Mumford.f K = hPoly ^ 2 + 4 * rhsPoly := by
  simp only [N13Mumford.f, hPoly, rhsPoly,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly]
  ring

/-- The good `y` coordinate inside the sextic coordinate ring. -/
def goodYInSextic : SexticRing (K := K) :=
  (1 / 2 : K) •
    (SexticMumford.yClass (M (K := K)) -
      sexticXHom (K := K) hPoly)

/-- The sextic `Y` coordinate inside the good coordinate ring. -/
def sexticYInGood : GoodRing (K := K) :=
  2 * N13GeneralizedMumfordIntegral.yClass +
    goodXHom (K := K) hPoly

theorem goodYInSextic_root :
    (N13GeneralizedMumfordIntegral.curvePoly (R := K)).eval₂
      (sexticXHom (K := K)) (goodYInSextic (K := K)) = 0 := by
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
    eval₂_mul]
  have hy := SexticMumford.yClass_sq (M (K := K))
  change
    SexticMumford.yClass (M (K := K)) ^ 2 =
      sexticXHom (K := K) (N13Mumford.f K) at hy
  rw [sextic_eq_h_sq_add_four_rhs (K := K)] at hy
  simp only [map_add, map_mul, map_pow, map_ofNat] at hy
  let a : SexticRing (K := K) :=
    (algebraMap K (SexticRing (K := K))) (1 / 2)
  let Y : SexticRing (K := K) :=
    SexticMumford.yClass (M (K := K))
  let H : SexticRing (K := K) :=
    sexticXHom (K := K) (hPoly (K := K))
  let R : SexticRing (K := K) :=
    sexticXHom (K := K) (rhsPoly (K := K))
  simp only [goodYInSextic, Algebra.smul_def]
  change (a * (Y - H)) ^ 2 + H * (a * (Y - H)) - R = 0
  have hy' : Y ^ 2 = H ^ 2 + 4 * R := hy
  have ha : 2 * a = 1 := by
    dsimp only [a]
    rw [← map_ofNat
      (algebraMap K (SexticRing (K := K))) 2,
      ← map_mul]
    norm_num
  linear_combination
    a ^ 2 * hy' +
      (-a * Y * H + a * H ^ 2 + (2 * a + 1) * R) * ha

theorem good_root_relation :
    N13GeneralizedMumfordIntegral.yClass ^ 2 +
        goodXHom (K := K) (hPoly (K := K)) *
          N13GeneralizedMumfordIntegral.yClass -
      goodXHom (K := K) (rhsPoly (K := K)) = 0 := by
  apply sub_eq_zero.mpr
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [N13GeneralizedMumfordIntegral.curvePoly]
  ring

theorem sexticYInGood_root :
    (SexticMumford.curvePoly (M (K := K))).eval₂
      (goodXHom (K := K)) (sexticYInGood (K := K)) = 0 := by
  simp only [SexticMumford.curvePoly,
    eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change
    sexticYInGood (K := K) ^ 2 -
      goodXHom (K := K) (N13Mumford.f K) = 0
  rw [sextic_eq_h_sq_add_four_rhs (K := K)]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  unfold sexticYInGood
  linear_combination 4 * good_root_relation (K := K)

/-- Completion of the square as a ring homomorphism from the good model to
the sextic model. -/
def toSextic :
    GoodRing (K := K) →+* SexticRing (K := K) :=
  AdjoinRoot.lift (sexticXHom (K := K))
    (goodYInSextic (K := K))
    (goodYInSextic_root (K := K))

/-- The inverse change of variables. -/
def toGood :
    SexticRing (K := K) →+* GoodRing (K := K) :=
  AdjoinRoot.lift (goodXHom (K := K))
    (sexticYInGood (K := K))
    (sexticYInGood_root (K := K))

@[simp] theorem toSextic_xClass (p : K[X]) :
    toSextic (K := K)
        (N13GeneralizedMumfordIntegral.xClass p) =
      SexticMumford.xClass (M (K := K)) p := by
  change
    toSextic (K := K)
        (AdjoinRoot.of
          (N13GeneralizedMumfordIntegral.curvePoly (R := K)) p) =
      sexticXHom (K := K) p
  exact AdjoinRoot.lift_of (goodYInSextic_root (K := K))

@[simp] theorem toSextic_algebraMap (z : K) :
    toSextic (K := K)
        (algebraMap K (GoodRing (K := K)) z) =
      algebraMap K (SexticRing (K := K)) z := by
  change
    toSextic (K := K)
        (N13GeneralizedMumfordIntegral.xClass (C z)) =
      SexticMumford.xClass (M (K := K)) (C z)
  exact toSextic_xClass (K := K) (C z)

@[simp] theorem toSextic_yClass :
    toSextic (K := K)
        N13GeneralizedMumfordIntegral.yClass =
      goodYInSextic (K := K) :=
  AdjoinRoot.lift_root (goodYInSextic_root (K := K))

@[simp] theorem toGood_xClass (p : K[X]) :
    toGood (K := K) (SexticMumford.xClass (M (K := K)) p) =
      N13GeneralizedMumfordIntegral.xClass p := by
  change
    toGood (K := K)
        (AdjoinRoot.of
          (SexticMumford.curvePoly (M (K := K))) p) =
      goodXHom (K := K) p
  exact AdjoinRoot.lift_of (sexticYInGood_root (K := K))

@[simp] theorem toGood_algebraMap (z : K) :
    toGood (K := K)
        (algebraMap K (SexticRing (K := K)) z) =
      algebraMap K (GoodRing (K := K)) z := by
  change
    toGood (K := K)
        (SexticMumford.xClass (M (K := K)) (C z)) =
      N13GeneralizedMumfordIntegral.xClass (C z)
  exact toGood_xClass (K := K) (C z)

@[simp] theorem toGood_yClass :
    toGood (K := K) (SexticMumford.yClass (M (K := K))) =
      sexticYInGood (K := K) :=
  AdjoinRoot.lift_root (sexticYInGood_root (K := K))

theorem invTwo_mul_two_good :
    (algebraMap K (GoodRing (K := K))) (2 : K)⁻¹ *
        (2 : GoodRing (K := K)) = 1 := by
  rw [← map_ofNat
      (algebraMap K (GoodRing (K := K))) 2,
    ← map_mul]
  norm_num

theorem two_mul_invTwo_sextic :
    (2 : SexticRing (K := K)) *
        (algebraMap K (SexticRing (K := K))) (2 : K)⁻¹ = 1 := by
  rw [← map_ofNat
      (algebraMap K (SexticRing (K := K))) 2,
    ← map_mul]
  norm_num

theorem toGood_comp_toSextic :
    (toGood (K := K)).comp (toSextic (K := K)) =
      RingHom.id (GoodRing (K := K)) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext_iff.mpr
    intro p
    change
      toGood (K := K)
          (toSextic (K := K) (goodXHom (K := K) p)) =
        goodXHom (K := K) p
    rw [goodXHom_apply, toSextic_xClass, toGood_xClass]
  · change
      toGood (K := K) (toSextic (K := K)
        N13GeneralizedMumfordIntegral.yClass) =
          N13GeneralizedMumfordIntegral.yClass
    rw [toSextic_yClass (K := K)]
    simp [goodYInSextic, sexticYInGood, Algebra.smul_def]
    rw [← mul_assoc, invTwo_mul_two_good (K := K), one_mul]

theorem toSextic_comp_toGood :
    (toSextic (K := K)).comp (toGood (K := K)) =
      RingHom.id (SexticRing (K := K)) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext_iff.mpr
    intro p
    change
      toSextic (K := K)
          (toGood (K := K) (sexticXHom (K := K) p)) =
        sexticXHom (K := K) p
    rw [sexticXHom_apply, toGood_xClass, toSextic_xClass]
  · change
      toSextic (K := K)
          (toGood (K := K)
            (SexticMumford.yClass (M (K := K)))) =
        SexticMumford.yClass (M (K := K))
    rw [toGood_yClass (K := K)]
    simp [goodYInSextic, sexticYInGood, Algebra.smul_def]
    rw [map_ofNat, ← mul_assoc,
      two_mul_invTwo_sextic (K := K)]
    ring

/-- The coordinate-ring isomorphism induced by completion of the square. -/
def coordinateRingEquiv :
    GoodRing (K := K) ≃+* SexticRing (K := K) where
  toFun := toSextic (K := K)
  invFun := toGood (K := K)
  left_inv z := by
    have h :=
      DFunLike.congr_fun (toGood_comp_toSextic (K := K)) z
    simpa using h
  right_inv z := by
    have h :=
      DFunLike.congr_fun (toSextic_comp_toGood (K := K)) z
    simpa using h
  map_mul' := map_mul (toSextic (K := K))
  map_add' := map_add (toSextic (K := K))

@[simp] theorem coordinateRingEquiv_xClass (p : K[X]) :
    coordinateRingEquiv (K := K)
        (N13GeneralizedMumfordIntegral.xClass p) =
      SexticMumford.xClass (M (K := K)) p :=
  toSextic_xClass (K := K) p

@[simp] theorem coordinateRingEquiv_yClass :
    coordinateRingEquiv (K := K)
        N13GeneralizedMumfordIntegral.yClass =
      goodYInSextic (K := K) :=
  toSextic_yClass (K := K)

end

end MazurProof.N13GoodSexticCoordinateEquiv

end
end

-- module FLT.Assumptions.MazurProof.N13GoodSexticMumfordTransport
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodSexticMumfordTransport =====
section

/-!
# Transporting N13 Mumford graph ideals through completion of the square

The rational change of coordinates

`Y = 2y + (X³ + X + 1)`

does more than identify the two affine coordinate rings.  It sends the
generalized graph ideal `(u, y - v)` exactly to the sextic graph ideal
`(u, Y - (2v + X³ + X + 1))`.  The factor `1 / 2` appearing on the second
generator is a unit in the base field, so it does not change the generated
ideal.
-/

open Polynomial

namespace MazurProof.N13GoodSexticMumfordTransport

noncomputable section

open N13GoodSexticCoordinateEquiv

/-- Multiplying one generator of a two-generated ideal by a unit does not
change the ideal. -/
theorem span_pair_mul_right_unit
    {R : Type*} [CommRing R] (x a y : R) (ha : IsUnit a) :
    Ideal.span {x, a * y} = Ideal.span {x, y} := by
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact Ideal.subset_span (by simp)
    · rw [hz]
      exact Ideal.mul_mem_left _ a (Ideal.subset_span (by simp))
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact Ideal.subset_span (by simp)
    · rw [hz]
      obtain ⟨b, hab⟩ := isUnit_iff_exists_inv.mp ha
      have hba : b * a = 1 := by
        simpa [mul_comm] using hab
      have hay : a * y ∈ Ideal.span {x, a * y} :=
        Ideal.subset_span (by simp)
      have hby : b * (a * y) ∈ Ideal.span {x, a * y} :=
        Ideal.mul_mem_left _ b hay
      simpa [← mul_assoc, hba] using hby

universe u

variable {K : Type u} [Field K] [CharZero K]





/-- The sextic graph polynomial corresponding to a generalized graph
polynomial `v`. -/
def completedGraph (v : K[X]) : K[X] :=
  2 * v + N13GeneralizedMumfordIntegral.hPoly

theorem two_mul_invTwo :
    (2 : (N13GoodSexticCoordinateEquiv.SexticRing (K := K))) *
        (algebraMap K (N13GoodSexticCoordinateEquiv.SexticRing (K := K))) (2 : K)⁻¹ = 1 := by
  rw [← map_ofNat (algebraMap K (N13GoodSexticCoordinateEquiv.SexticRing (K := K))) 2, ← map_mul]
  norm_num

/-- Under completion of the square, the generalized graph generator is
`1 / 2` times the corresponding sextic graph generator. -/
@[simp] theorem toSextic_ySubClass (v : K[X]) :
    (N13GoodSexticCoordinateEquiv.toSextic (K := K))
        (N13GeneralizedMumfordIntegral.ySubClass v) =
      (algebraMap K (N13GoodSexticCoordinateEquiv.SexticRing (K := K))) (2 : K)⁻¹ *
        SexticMumford.ySubClass (N13GoodSexticCoordinateEquiv.M (K := K)) (completedGraph v) := by
  simp only [N13GeneralizedMumfordIntegral.ySubClass, map_sub,
    N13GoodSexticCoordinateEquiv.toSextic_yClass,
    N13GoodSexticCoordinateEquiv.toSextic_xClass,
    N13GoodSexticCoordinateEquiv.goodYInSextic,
    SexticMumford.ySubClass, completedGraph, Algebra.smul_def]
  have hhalf :
      (algebraMap K (N13GoodSexticCoordinateEquiv.SexticRing (K := K))) (1 / 2 : K) =
        (algebraMap K (N13GoodSexticCoordinateEquiv.SexticRing (K := K))) (2 : K)⁻¹ := by
    norm_num
  have hx :
      SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K))
          (2 * v + N13GeneralizedMumfordIntegral.hPoly) =
        2 * SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) v +
          SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K))
            N13GeneralizedMumfordIntegral.hPoly := by
    change (N13GoodSexticCoordinateEquiv.sexticXHom (K := K))
        (2 * v + N13GeneralizedMumfordIntegral.hPoly) =
      2 * (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) v +
        (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) N13GeneralizedMumfordIntegral.hPoly
    rw [map_add, map_mul, map_ofNat]
  rw [hhalf, hx]
  let a : (N13GoodSexticCoordinateEquiv.SexticRing (K := K)) :=
    (algebraMap K (N13GoodSexticCoordinateEquiv.SexticRing (K := K))) (2 : K)⁻¹
  let Y : (N13GoodSexticCoordinateEquiv.SexticRing (K := K)) := SexticMumford.yClass (N13GoodSexticCoordinateEquiv.M (K := K))
  let H : (N13GoodSexticCoordinateEquiv.SexticRing (K := K)) :=
    SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K))
      N13GeneralizedMumfordIntegral.hPoly
  let V : (N13GoodSexticCoordinateEquiv.SexticRing (K := K)) :=
    SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) v
  change a * (Y - H) - V = a * (Y - (2 * V + H))
  have ha : 2 * a = 1 := two_mul_invTwo
  linear_combination V * ha

theorem invTwo_isUnit :
    IsUnit ((algebraMap K (N13GoodSexticCoordinateEquiv.SexticRing (K := K))) (2 : K)⁻¹) := by
  exact
    (isUnit_iff_ne_zero.mpr (by norm_num : (2 : K)⁻¹ ≠ 0)).map
      (algebraMap K (N13GoodSexticCoordinateEquiv.SexticRing (K := K)))

/-- Completion of the square maps each generalized Mumford graph ideal
exactly onto the corresponding sextic Mumford graph ideal. -/
theorem map_mumfordIdeal (u v : K[X]) :
    Ideal.map (N13GoodSexticCoordinateEquiv.toSextic (K := K))
        (N13GeneralizedMumfordIntegral.mumfordIdeal u v) =
      SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u (completedGraph v) := by
  rw [N13GeneralizedMumfordIntegral.mumfordIdeal,
    SexticMumford.mumfordIdeal, Ideal.map_span, Set.image_pair,
    N13GoodSexticCoordinateEquiv.toSextic_xClass,
    toSextic_ySubClass]
  exact span_pair_mul_right_unit _ _ _ invTwo_isUnit

/-- Congruent graph polynomials define the same sextic graph ideal. -/
theorem sextic_mumfordIdeal_eq_of_dvd_sub
    (u v w : K[X]) (hvw : u ∣ v - w) :
    SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u v =
      SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u w := by
  obtain ⟨q, hq⟩ := hvw
  have hxsub :
      SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) (v - w) =
        SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) v -
          SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) w := by
    change (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) (v - w) =
      (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) v - (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) w
    exact map_sub (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) v w
  have hxmul :
      SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) (u * q) =
        SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) u *
          SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) q := by
    change (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) (u * q) =
      (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) u * (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) q
    exact map_mul (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) u q
  have hyw :
      SexticMumford.ySubClass (N13GoodSexticCoordinateEquiv.M (K := K)) w =
        SexticMumford.ySubClass (N13GoodSexticCoordinateEquiv.M (K := K)) v +
          SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) u *
            SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) q := by
    unfold SexticMumford.ySubClass
    rw [← hxmul, ← hq, hxsub]
    ring
  have hyv :
      SexticMumford.ySubClass (N13GoodSexticCoordinateEquiv.M (K := K)) v =
        SexticMumford.ySubClass (N13GoodSexticCoordinateEquiv.M (K := K)) w -
          SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) u *
            SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) q := by
    rw [hyw]
    ring
  have hxv :
      SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) u ∈
        SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u v :=
    SexticMumford.xClass_mem_mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u v
  have hxw :
      SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) u ∈
        SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u w :=
    SexticMumford.xClass_mem_mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u w
  have hyvmem :
      SexticMumford.ySubClass (N13GoodSexticCoordinateEquiv.M (K := K)) v ∈
        SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u v := by
    unfold SexticMumford.mumfordIdeal
    exact Ideal.subset_span (by simp)
  have hywmem :
      SexticMumford.ySubClass (N13GoodSexticCoordinateEquiv.M (K := K)) w ∈
        SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u w := by
    unfold SexticMumford.mumfordIdeal
    exact Ideal.subset_span (by simp)
  have hmulv :
      SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) u *
          SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) q ∈
        SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u v := by
    simpa only [mul_comm] using
      Ideal.mul_mem_left
        (SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u v)
        (SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) q) hxv
  have hmulw :
      SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) u *
          SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) q ∈
        SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u w := by
    simpa only [mul_comm] using
      Ideal.mul_mem_left
        (SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u w)
        (SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) q) hxw
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact hxw
    · rw [hz, hyv]
      exact Ideal.sub_mem
        (SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u w)
        hywmem
        hmulw
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact hxv
    · rw [hz, hyw]
      exact Ideal.add_mem
        (SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u v)
        hyvmem
        hmulv

/-- The reduced sextic graph polynomial attached to generalized data. -/
def reducedCompletedGraph (u v : K[X]) : K[X] :=
  completedGraph v % u

theorem dvd_sub_mod (p u : K[X]) :
    u ∣ p - p % u := by
  refine ⟨p / u, ?_⟩
  have h := EuclideanDomain.mod_add_div p u
  calc
    p - p % u = (p % u + u * (p / u)) - p % u := by
      rw [h]
    _ = u * (p / u) := by ring

/-- The exact transport theorem with the sextic graph polynomial reduced
modulo `u`, as required by the standard Mumford representation. -/
theorem map_mumfordIdeal_reduced (u v : K[X]) :
    Ideal.map (N13GoodSexticCoordinateEquiv.toSextic (K := K))
        (N13GeneralizedMumfordIntegral.mumfordIdeal u v) =
      SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u
        (reducedCompletedGraph u v) := by
  rw [map_mumfordIdeal]
  exact sextic_mumfordIdeal_eq_of_dvd_sub _ _ _
    (dvd_sub_mod (completedGraph v) u)

/-- Completing the square carries the generalized Mumford equation to the
standard sextic equation. -/
theorem completedGraph_curve_eq
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K)) :
    N13Mumford.f K - completedGraph D.v ^ 2 =
      D.u * (-4 * D.w) := by
  rw [N13GoodSexticCoordinateEquiv.sextic_eq_h_sq_add_four_rhs
    (K := K)]
  unfold completedGraph
  linear_combination -4 * D.curve_eq

/-- Reducing the completed graph polynomial modulo `u` preserves the
sextic divisibility relation. -/
theorem reducedCompletedGraph_curve_dvd
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K)) :
    D.u ∣ N13Mumford.f K -
      reducedCompletedGraph D.u D.v ^ 2 := by
  let V : K[X] := completedGraph D.v
  let Vred : K[X] := reducedCompletedGraph D.u D.v
  obtain ⟨q, hq⟩ := dvd_sub_mod V D.u
  change V - Vred = D.u * q at hq
  refine ⟨-4 * D.w + q * (V + Vred), ?_⟩
  calc
    N13Mumford.f K - Vred ^ 2 =
        (N13Mumford.f K - V ^ 2) +
          (V - Vred) * (V + Vred) := by ring
    _ =
        D.u * (-4 * D.w) +
          (D.u * q) * (V + Vred) := by
      rw [completedGraph_curve_eq D, hq]
    _ = D.u * (-4 * D.w + q * (V + Vred)) := by ring

/-- A generalized Mumford representative over a characteristic-zero field,
written as a standard reduced sextic semirepresentative. -/
def toSexticSemi
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    SexticMumford.SemiMumford (N13GoodSexticCoordinateEquiv.M (K := K)) where
  u := D.u
  v := reducedCompletedGraph D.u D.v
  nInf := nInf
  u_monic := D.u_monic
  v_reduced := by
    apply (Polynomial.mod_eq_self_iff D.u_monic.ne_zero).2
    exact Polynomial.degree_mod_lt _ D.u_monic.ne_zero
  curve_dvd := by
    simpa only [N13Mumford.model_f] using
      reducedCompletedGraph_curve_dvd D

@[simp] theorem toSexticSemi_u
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    (toSexticSemi D nInf).u = D.u := rfl

@[simp] theorem toSexticSemi_v
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    (toSexticSemi D nInf).v =
      reducedCompletedGraph D.u D.v := rfl

@[simp] theorem toSexticSemi_nInf
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    (toSexticSemi D nInf).nInf = nInf := rfl

/-- The reduced standard semirepresentative has exactly the transported
generalized graph ideal. -/
theorem map_mumfordIdeal_toSexticSemi
    (D :
      N13GeneralizedMumfordIntegral.SemiMumford (R := K))
    (nInf : ℤ) :
    Ideal.map (N13GoodSexticCoordinateEquiv.toSextic (K := K))
        (N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v) =
      SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K))
        (toSexticSemi D nInf).u
        (toSexticSemi D nInf).v := by
  simpa only [toSexticSemi_u, toSexticSemi_v] using
    map_mumfordIdeal_reduced D.u D.v

end

end MazurProof.N13GoodSexticMumfordTransport

end
end

-- module FLT.Assumptions.MazurProof.N13TwoAdicMumfordTransport
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicMumfordTransport =====
section

/-!
# Transporting integral N13 Mumford data to the two-adic sextic model

Smooth generalized Mumford data over `ℤ₂` first extend coefficientwise to
`ℚ₂`.  Completion of the square then gives a standard reduced sextic
semirepresentative.  This file records that passage without choosing
coordinates or enumerating residue classes.
-/

open Polynomial

namespace MazurProof.N13TwoAdicMumfordTransport

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  ℤ_[2]

abbrev Q₂ : Type :=
  ℚ_[2]

def coeffMap : R₂ →+* Q₂ :=
  algebraMap R₂ Q₂

def mapPoly : R₂[X] →+* Q₂[X] :=
  Polynomial.mapRingHom coeffMap

@[simp] theorem mapPoly_apply (p : R₂[X]) :
    mapPoly p = p.map coeffMap := rfl

@[simp] theorem mapPoly_hPoly :
    mapPoly
        (N13GeneralizedMumfordIntegral.hPoly (R := R₂)) =
      N13GeneralizedMumfordIntegral.hPoly (R := Q₂) := by
  simp [mapPoly, coeffMap,
    N13GeneralizedMumfordIntegral.hPoly]

@[simp] theorem mapPoly_rhsPoly :
    mapPoly
        (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)) =
      N13GeneralizedMumfordIntegral.rhsPoly (R := Q₂) := by
  simp [mapPoly, coeffMap,
    N13GeneralizedMumfordIntegral.rhsPoly]

/-- Coefficient extension does not require the additional special-fibre
smoothness witness. -/
def baseChangeSemi
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂) :
    N13GeneralizedMumfordIntegral.SemiMumford (R := Q₂) where
  u := mapPoly D.u
  v := mapPoly D.v
  w := mapPoly D.w
  u_monic := D.u_monic.map coeffMap
  curve_eq := by
    have h := congrArg mapPoly D.curve_eq
    simpa only [map_add, map_sub, map_mul, map_pow,
      mapPoly_hPoly, mapPoly_rhsPoly] using h

@[simp] theorem baseChangeSemi_u
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂) :
    (baseChangeSemi D).u = mapPoly D.u := rfl

@[simp] theorem baseChangeSemi_v
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂) :
    (baseChangeSemi D).v = mapPoly D.v := rfl

@[simp] theorem baseChangeSemi_w
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂) :
    (baseChangeSemi D).w = mapPoly D.w := rfl

/-- Coefficient extension of an integral generalized Mumford datum. -/
def baseChange
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    N13GeneralizedMumfordIntegral.SemiMumford (R := Q₂) where
  u := mapPoly D.u
  v := mapPoly D.v
  w := mapPoly D.w
  u_monic := D.u_monic.map coeffMap
  curve_eq := by
    have h := congrArg mapPoly D.curve_eq
    simpa only [map_add, map_sub, map_mul, map_pow,
      mapPoly_hPoly, mapPoly_rhsPoly] using h

@[simp] theorem baseChange_u
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    (baseChange D).u = mapPoly D.u := rfl

@[simp] theorem baseChange_v
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    (baseChange D).v = mapPoly D.v := rfl

@[simp] theorem baseChange_w
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    (baseChange D).w = mapPoly D.w := rfl

/-- The standard reduced sextic semirepresentative attached to arbitrary
integral generalized Mumford data. -/
def sexticSemiOfSemi
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    SexticMumford.SemiMumford
      (N13GoodSexticCoordinateEquiv.M (K := Q₂)) :=
  N13GoodSexticMumfordTransport.toSexticSemi
    (baseChangeSemi D) nInf

@[simp] theorem sexticSemiOfSemi_u
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    (sexticSemiOfSemi D nInf).u = mapPoly D.u := rfl

@[simp] theorem sexticSemiOfSemi_v
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    (sexticSemiOfSemi D nInf).v =
      N13GoodSexticMumfordTransport.reducedCompletedGraph
        (mapPoly D.u) (mapPoly D.v) := rfl

@[simp] theorem sexticSemiOfSemi_nInf
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    (sexticSemiOfSemi D nInf).nInf = nInf := rfl

/-- Completion of the square transports every integral generalized graph
ideal, independently of a vertical Bézout witness. -/
theorem map_mumfordIdeal_sexticSemiOfSemi
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    Ideal.map
        (N13GoodSexticCoordinateEquiv.toSextic (K := Q₂))
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (baseChangeSemi D).u (baseChangeSemi D).v) =
      SexticMumford.mumfordIdeal
        (N13GoodSexticCoordinateEquiv.M (K := Q₂))
        (sexticSemiOfSemi D nInf).u
        (sexticSemiOfSemi D nInf).v :=
  N13GoodSexticMumfordTransport.map_mumfordIdeal_toSexticSemi
    (baseChangeSemi D) nInf

/-- The standard reduced sextic semirepresentative over `ℚ₂`. -/
def sexticSemi
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    SexticMumford.SemiMumford
      (N13GoodSexticCoordinateEquiv.M (K := Q₂)) :=
  N13GoodSexticMumfordTransport.toSexticSemi
    (baseChange D) nInf

@[simp] theorem sexticSemi_u
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    (sexticSemi D nInf).u = mapPoly D.u := rfl

@[simp] theorem sexticSemi_v
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    (sexticSemi D nInf).v =
      N13GoodSexticMumfordTransport.reducedCompletedGraph
        (mapPoly D.u) (mapPoly D.v) := rfl

@[simp] theorem sexticSemi_nInf
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    (sexticSemi D nInf).nInf = nInf := rfl

/-- The two-adic sextic graph ideal is exactly the image of the generalized
graph ideal under completion of the square. -/
theorem map_mumfordIdeal_sexticSemi
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    Ideal.map
        (N13GoodSexticCoordinateEquiv.toSextic (K := Q₂))
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (baseChange D).u (baseChange D).v) =
      SexticMumford.mumfordIdeal
        (N13GoodSexticCoordinateEquiv.M (K := Q₂))
        (sexticSemi D nInf).u
        (sexticSemi D nInf).v :=
  N13GoodSexticMumfordTransport.map_mumfordIdeal_toSexticSemi
    (baseChange D) nInf

end

end MazurProof.N13TwoAdicMumfordTransport

end
end

-- module FLT.Assumptions.MazurProof.N13TwoAdicCoordinateBaseChange
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicCoordinateBaseChange =====
section

/-!
# Base change of the N13 integral coordinate ring to `ℚ₂`

Coefficient extension from `ℤ₂` to `ℚ₂` induces a map between the two
generalized-hyperelliptic coordinate rings.  It carries an integral Mumford
graph ideal exactly onto the graph ideal obtained by coefficient extension.
Composing with completion of the square therefore sends the integral graph
directly to the standard sextic Mumford graph over `ℚ₂`.
-/

open Polynomial

namespace MazurProof.N13TwoAdicCoordinateBaseChange

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13TwoAdicMumfordTransport.R₂

abbrev Q₂ : Type :=
  N13TwoAdicMumfordTransport.Q₂

abbrev IntegralRing : Type :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := R₂)

abbrev GoodRing : Type :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := Q₂)

def coeffMap : R₂ →+* Q₂ :=
  N13TwoAdicMumfordTransport.coeffMap

def mapPoly : R₂[X] →+* Q₂[X] :=
  N13TwoAdicMumfordTransport.mapPoly

@[simp] theorem mapPoly_apply (p : R₂[X]) :
    mapPoly p = p.map coeffMap := rfl

/-- Coefficient extension from `ℤ₂[X]` to `ℚ₂[X]` is faithful. -/
theorem mapPoly_injective : Function.Injective mapPoly :=
  Polynomial.map_injective coeffMap
    (IsFractionRing.injective R₂ Q₂)

@[simp] theorem mapPoly_hPoly :
    mapPoly
        (N13GeneralizedMumfordIntegral.hPoly (R := R₂)) =
      N13GeneralizedMumfordIntegral.hPoly (R := Q₂) :=
  N13TwoAdicMumfordTransport.mapPoly_hPoly

@[simp] theorem mapPoly_rhsPoly :
    mapPoly
        (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)) =
      N13GeneralizedMumfordIntegral.rhsPoly (R := Q₂) :=
  N13TwoAdicMumfordTransport.mapPoly_rhsPoly

theorem map_curvePoly :
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).map
        mapPoly =
      N13GeneralizedMumfordIntegral.curvePoly (R := Q₂) := by
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_mul]
  change
    X ^ 2 +
          C (mapPoly
            (N13GeneralizedMumfordIntegral.hPoly (R := R₂))) * X -
        C (mapPoly
          (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂))) =
      X ^ 2 +
          C (N13GeneralizedMumfordIntegral.hPoly (R := Q₂)) * X -
        C (N13GeneralizedMumfordIntegral.rhsPoly (R := Q₂))
  rw [mapPoly_hPoly, mapPoly_rhsPoly]

theorem target_curve_dvd :
    N13GeneralizedMumfordIntegral.curvePoly (R := Q₂) ∣
      (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).map
        mapPoly := by
  rw [map_curvePoly]

/-- Coefficient extension on the affine coordinate ring of the good model. -/
def extendCoordinate : IntegralRing →+* GoodRing :=
  AdjoinRoot.map mapPoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    (N13GeneralizedMumfordIntegral.curvePoly (R := Q₂))
    target_curve_dvd

@[simp] theorem extend_xClass (p : R₂[X]) :
    extendCoordinate
        (N13GeneralizedMumfordIntegral.xClass (R := R₂) p) =
      N13GeneralizedMumfordIntegral.xClass
        (R := Q₂) (mapPoly p) := by
  exact AdjoinRoot.map_of
    mapPoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    (N13GeneralizedMumfordIntegral.curvePoly (R := Q₂))
    target_curve_dvd p

@[simp] theorem extend_yClass :
    extendCoordinate
        (N13GeneralizedMumfordIntegral.yClass (R := R₂)) =
      N13GeneralizedMumfordIntegral.yClass (R := Q₂) := by
  exact AdjoinRoot.map_root
    mapPoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    (N13GeneralizedMumfordIntegral.curvePoly (R := Q₂))
    target_curve_dvd

@[simp] theorem extend_ySubClass (v : R₂[X]) :
    extendCoordinate
        (N13GeneralizedMumfordIntegral.ySubClass (R := R₂) v) =
      N13GeneralizedMumfordIntegral.ySubClass
        (R := Q₂) (mapPoly v) := by
  simp [N13GeneralizedMumfordIntegral.ySubClass]

/-- Coefficient extension preserves the `1`-coordinate in the rank-two
presentation of the generalized coordinate ring. -/
@[simp] theorem coeff0_extendCoordinate (z : IntegralRing) :
    N13GeneralizedMumfordIntegral.coeff0
        (extendCoordinate z) =
      mapPoly (N13GeneralizedMumfordIntegral.coeff0 z) := by
  rw [← N13GeneralizedMumfordIntegral.recompose z]
  simp

/-- Coefficient extension preserves the `Y`-coordinate in the rank-two
presentation of the generalized coordinate ring. -/
@[simp] theorem coeffY_extendCoordinate (z : IntegralRing) :
    N13GeneralizedMumfordIntegral.coeffY
        (extendCoordinate z) =
      mapPoly (N13GeneralizedMumfordIntegral.coeffY z) := by
  rw [← N13GeneralizedMumfordIntegral.recompose z]
  simp

/-- Base change from the integral good model to its generic fibre loses no
functions.  This is the rank-two basis argument, not a localization
calculation in coordinates. -/
theorem extendCoordinate_injective :
    Function.Injective extendCoordinate := by
  intro z w h
  apply
    (N13GeneralizedMumfordIntegral.eq_iff_coeff z w).2
  constructor
  · apply mapPoly_injective
    simpa only [coeff0_extendCoordinate] using congrArg
      N13GeneralizedMumfordIntegral.coeff0 h
  · apply mapPoly_injective
    simpa only [coeffY_extendCoordinate] using congrArg
      N13GeneralizedMumfordIntegral.coeffY h

/-- Coefficient extension maps an integral graph ideal onto the
coefficient-extended graph ideal. -/
theorem map_mumfordIdeal (u v : R₂[X]) :
    Ideal.map extendCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) u v) =
      N13GeneralizedMumfordIntegral.mumfordIdeal
        (R := Q₂) (mapPoly u) (mapPoly v) := by
  rw [N13GeneralizedMumfordIntegral.mumfordIdeal,
    N13GeneralizedMumfordIntegral.mumfordIdeal,
    Ideal.map_span, Set.image_pair, extend_xClass,
    extend_ySubClass]

/-- The full integral-to-sextic coordinate map over `ℚ₂`. -/
def integralToSextic :
    IntegralRing →+*
      N13GoodSexticCoordinateEquiv.SexticRing (K := Q₂) :=
  (N13GoodSexticCoordinateEquiv.toSextic (K := Q₂)).comp
    extendCoordinate

/-- An integral smooth graph ideal becomes exactly the standard reduced
sextic Mumford graph attached by `sexticSemi`. -/
theorem map_mumfordIdeal_sexticSemi
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    Ideal.map integralToSextic
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) D.u D.v) =
      SexticMumford.mumfordIdeal
        (N13GoodSexticCoordinateEquiv.M (K := Q₂))
        (N13TwoAdicMumfordTransport.sexticSemi D nInf).u
        (N13TwoAdicMumfordTransport.sexticSemi D nInf).v := by
  rw [integralToSextic, ← Ideal.map_map,
    map_mumfordIdeal]
  exact
    N13TwoAdicMumfordTransport.map_mumfordIdeal_sexticSemi
      D nInf

/-- The same coordinate transport theorem for arbitrary integral
semigraphs. -/
theorem map_mumfordIdeal_sexticSemiOfSemi
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    Ideal.map integralToSextic
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) D.u D.v) =
      SexticMumford.mumfordIdeal
        (N13GoodSexticCoordinateEquiv.M (K := Q₂))
        (N13TwoAdicMumfordTransport.sexticSemiOfSemi D nInf).u
        (N13TwoAdicMumfordTransport.sexticSemiOfSemi D nInf).v := by
  rw [integralToSextic, ← Ideal.map_map,
    map_mumfordIdeal]
  exact
    N13TwoAdicMumfordTransport.map_mumfordIdeal_sexticSemiOfSemi
      D nInf

end

end MazurProof.N13TwoAdicCoordinateBaseChange

end
end


