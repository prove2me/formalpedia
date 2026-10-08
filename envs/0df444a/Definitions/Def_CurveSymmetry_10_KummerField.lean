-- Prove2me | Definitions.Def_CurveSymmetry_10_KummerField
-- name    : CurveSymmetry_10_KummerField
-- status  : Definition
-- author  : @carlok
-- created : 2026-10-07T12:23:00.060133+00:00
-- url     : https://prove2.me/theorems/69bd61ea-d38b-4a9d-9303-0cdde80ee050
-- title:
--   Kummer covers $y^n=f(x)$, the quartic $X^4+Y^4=2$ with three differentials, and pullbacks along similarities
-- statement:
--   Let $n\in\mathbb N$, $f\in\mathbb C[x]$, and let $\mathbb C(x)$ be the rational function field. Polynomials in $\mathbb C[X,Y]$ are read in the coordinates $X=z$, $Y=\bar z$; for $m\in\mathbb N$ and $\alpha\in\mathbb C$, $P_\alpha=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$ and $h_{m,\alpha}(t)=-t(t^m+1)(\alpha t^m+\bar\alpha)$.
--
--   The file defines the coordinate ring and the function field of the Kummer cover $y^n=f(x)$,
--   $$R_{n,f}=\mathbb C[x][Y]/(Y^n-f),\qquad K_{n,f}=\mathbb C(x)[Y]/(Y^n-f),$$
--   with $y$ the class of $Y$ ($K_{n,f}$ is a field when $Y^n-f$ is irreducible over $\mathbb C(x)$), and specializes them to the quartic $f=2-x^4$, whose field $K_4=K_{4,\,2-x^4}$ is that of $y^4=2-x^4$. It also defines:
--
--   1. The $\mathbb C[x]$-algebra homomorphism $R_{n,f}\to K_{n,f}$ with $Y\mapsto y$, which makes $K_{n,f}$ an $R_{n,f}$-algebra; and, when $Y^n-f$ is irreducible over $\mathbb C(x)$, the element $x\in K_{n,f}$ and the one-element basis $dx$ of $\Omega_{K_{n,f}/\mathbb C}$.
--   2. For the quartic: the coordinates $x,y\in K_4$ and the three differentials $dx/y^3$, $x\,dx/y^3$ and $y\,dx/y^3=dx/y^2$, written as $(N_i/y^3)\,dx$ with numerators $(N_1,N_2,N_3)=(1,x,y)$.
--   3. The Fermat coordinate ring $\mathbb C[X,Y]/(X^d+Y^d-2)$ and its fraction field, for $d\in\mathbb N$.
--   4. For $m\ge1$ and $\alpha\ne\bar\alpha$, the comparison isomorphism of $\mathbb C$-algebras $\mathbb C(t)[W]/(W^2-h_{m,\alpha})\to\operatorname{Frac}\big(\mathbb C[X,Y]/(P_\alpha)\big)$, $t\mapsto x/y$, $W\mapsto t(t^m+1)\,y$, and the underlying ring homomorphism.
--   5. Similarities: for $a,b\in\mathbb C$, the $\mathbb C$-algebra endomorphism of $\mathbb C[X,Y]$ with $X\mapsto aX+b$ and $Y\mapsto\bar aY+\bar b$, the pullback along $z\mapsto az+b$; and, for $a\ne0$, the automorphism it defines, whose inverse is the pullback along the inverse similarity.
--
--   These serve Remark 5 and the genus clause of Lemma 4. In the coordinates $X=z$, $Y=\bar z$ the curve $\operatorname{Re}(z^4)=1$ is $X^4+Y^4=2$, that is, the Kummer cover $y^4=2-x^4$, and the three differentials of item 2 form the basis of its holomorphic differentials behind the genus three of Remark 5. The comparison isomorphism transfers the genus computed on the double cover to the function field of $P_\alpha=0$, and the pullback along a similarity is how a similarity between real loci becomes an isomorphism of function fields.
--
--   **Formalization Note**: The rings are `AdjoinRoot` quotients over $\mathbb C[x]$ and over $\mathbb C(x)$, the latter being `RatFunc ℂ`. The irreducibility of $Y^n-f$ over $\mathbb C(x)$ is a `Fact` instance, provided here for $n=4$ and $f=2-x^4$, and the Fermat coordinate ring is a domain for $d\ne0$. The file also proves that $Y^n-f$ is irreducible over $\mathbb C[x]$ and over $\mathbb C(x)$ when $n\ne0$ and $f$ is squarefree of positive degree, that $R_{n,f}\to K_{n,f}$ is injective for $n\ne0$, and that $K_{n,f}$ is then the fraction field of $R_{n,f}$ when $Y^n-f$ is irreducible over $\mathbb C(x)$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), definitions of the formalization, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean modules FamilyGenus, KummerField, FermatHolomorphic, QuarticComparison in https://github.com/carlok/curve-symmetry-lean/tree/d99bc17a1c397956c05d7417de50f9beed56580f/lean (C. Perassi)

-- Definitions, part 10 of 12, generated from curve-symmetry-lean by skeleton
-- subtraction: the source modules below, in dependency order, each in its own
-- section; only definitions, instances and the theorems they need are kept.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

-- lean/FamilyGenus.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

section Point

variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)

end Point

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

variable (m α) in
/-- G07a's comparison map `ℂ(t)[w]/(w² − h) → Frac(ℂ[X,Y]/(P_α))`, typed on `QuadField`. -/
noncomputable def familyQuadLift : QuadField (familyH m α) →+* FamilyFunctionField m α :=
  familyLift m α

lemma familyQuadLift_bijective : Function.Bijective (familyQuadLift m α) :=
  ⟨familyLift_injective, familyLift_surjective⟩

variable (m α) in
/-- G07a's isomorphism `ℂ(t)[w]/(w² − h) ≅ Frac(ℂ[X,Y]/(P_α))`, as `ℂ`-algebras. -/
noncomputable def familyFunctionFieldAlgEquiv :
    QuadField (familyH m α) ≃ₐ[ℂ] FamilyFunctionField m α :=
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofBijective (familyQuadLift m α) familyQuadLift_bijective)
    fun z => by
      rw [RingEquiv.ofBijective_apply,
        IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) (QuadField (familyH m α)),
        AdjoinRoot.algebraMap_eq]
      exact (familyLift_of _).trans ((familyRatFuncHom m α).commutes z)

@[simp] lemma familyFunctionFieldAlgEquiv_apply (x : QuadField (familyH m α)) :
    familyFunctionFieldAlgEquiv m α x = familyQuadLift m α x :=
  rfl

end CurveSymmetry

end

-- lean/KummerField.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

/-- `Yⁿ − f` over `ℂ[x]`. -/
noncomputable def kummerPoly (n : ℕ) (f : ℂ[X]) : ℂ[X][X] := X ^ n - C f

/-- The affine coordinate ring `ℂ[x][Y]/(Yⁿ − f)` of the Kummer cover. -/
abbrev KummerRing (n : ℕ) (f : ℂ[X]) : Type := AdjoinRoot (kummerPoly n f)

/-- `Yⁿ − f` over `ℂ(x)`. -/
noncomputable def kummerRat (n : ℕ) (f : ℂ[X]) : (RatFunc ℂ)[X] :=
  X ^ n - C (algebraMap ℂ[X] (RatFunc ℂ) f)

/-- The function field `ℂ(x)[Y]/(Yⁿ − f)` of the Kummer cover. -/
abbrev KummerField (n : ℕ) (f : ℂ[X]) : Type := AdjoinRoot (kummerRat n f)

section Polynomials

variable (n : ℕ) (f : ℂ[X])

lemma kummerPoly_monic (hn : n ≠ 0) : (kummerPoly n f).Monic := monic_X_pow_sub_C _ hn

lemma kummerPoly_map :
    (kummerPoly n f).map (algebraMap ℂ[X] (RatFunc ℂ)) = kummerRat n f := by
  simp [kummerPoly, kummerRat, Polynomial.map_sub, Polynomial.map_pow]

/-- **R01c-1**: for squarefree, nonconstant `f`, the polynomial `Yⁿ − f` is irreducible over
`ℂ[x]`, by Eisenstein's criterion at a simple root of `f`. -/
theorem kummerPoly_irreducible (hn : n ≠ 0) (hsq : Squarefree f) (hf : 0 < f.natDegree) :
    Irreducible (kummerPoly n f) := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root f (natDegree_pos_iff_degree_pos.mp hf).ne'
  have hmonic := kummerPoly_monic n f hn
  have hdeg : (kummerPoly n f).natDegree = n := natDegree_X_pow_sub_C
  have hprime : (Ideal.span {X - C c} : Ideal ℂ[X]).IsPrime :=
    (Ideal.span_singleton_prime (X_sub_C_ne_zero c)).mpr (prime_X_sub_C c)
  apply irreducible_of_eisenstein_criterion hprime
  · rw [hmonic.leadingCoeff]
    exact fun h => hprime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  · intro k hk
    have hk' : k < n := by simpa [hdeg] using coe_lt_degree.mp hk
    rw [Ideal.mem_span_singleton]
    simp only [kummerPoly, coeff_sub, coeff_X_pow, coeff_C, if_neg hk'.ne]
    by_cases h0 : k = 0
    · rw [if_pos h0, zero_sub, dvd_neg]
      exact dvd_iff_isRoot.mpr hc
    · rw [if_neg h0, sub_zero]
      exact dvd_zero _
  · exact natDegree_pos_iff_degree_pos.mp (by omega)
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp only [kummerPoly, coeff_sub, coeff_X_pow, coeff_C, if_neg (Ne.symm hn),
      zero_sub, dvd_neg]
    intro hdvd
    exact not_isUnit_X_sub_C c (hsq _ (by rwa [← sq]))
  · exact hmonic.isPrimitive

/-- `Yⁿ − f` stays irreducible over `ℂ(x)` (Gauss's lemma). -/
theorem kummerRat_irreducible (hn : n ≠ 0) (hsq : Squarefree f) (hf : 0 < f.natDegree) :
    Irreducible (kummerRat n f) := by
  rw [← kummerPoly_map]
  exact (kummerPoly_monic n f hn).irreducible_iff_irreducible_map_fraction_map.mp
    (kummerPoly_irreducible n f hn hsq hf)

end Polynomials

section Ring

variable (n : ℕ) (f : ℂ[X])

/-- The comparison map from the coordinate ring to the function field, `Y ↦ y`. -/
noncomputable def kummerRingMap : KummerRing n f →ₐ[ℂ[X]] KummerField n f :=
  AdjoinRoot.liftAlgHom (kummerPoly n f) (Algebra.ofId ℂ[X] (KummerField n f))
    (AdjoinRoot.root (kummerRat n f)) (by
      change eval₂ (algebraMap ℂ[X] (KummerField n f)) _ _ = 0
      rw [← aeval_def, ← Polynomial.aeval_map_algebraMap (RatFunc ℂ), kummerPoly_map,
        AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])

lemma kummerRingMap_mk (g : ℂ[X][X]) :
    kummerRingMap n f (AdjoinRoot.mk (kummerPoly n f) g) =
      AdjoinRoot.mk (kummerRat n f) (g.map (algebraMap ℂ[X] (RatFunc ℂ))) := by
  conv_rhs => rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_map_algebraMap]
  rw [kummerRingMap, AdjoinRoot.liftAlgHom_mk, aeval_def]
  rfl

/-- **R01c-1**: the coordinate ring embeds in the function field. -/
theorem kummerRingMap_injective (hn : n ≠ 0) : Function.Injective (kummerRingMap n f) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using AdjoinRoot.induction_on with
  | ih g =>
    have hmon := kummerPoly_monic n f hn
    rw [kummerRingMap_mk, AdjoinRoot.mk_eq_zero, ← kummerPoly_map,
      ← modByMonic_eq_zero_iff_dvd (hmon.map _), ← map_modByMonic _ hmon] at hx
    rw [AdjoinRoot.mk_eq_zero, ← modByMonic_eq_zero_iff_dvd hmon]
    exact Polynomial.map_injective _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))
      (hx.trans (Polynomial.map_zero _).symm)

end Ring

section Field

variable (n : ℕ) (f : ℂ[X]) [Fact (Irreducible (kummerRat n f))]

instance kummerField_finiteDimensional : FiniteDimensional (RatFunc ℂ) (KummerField n f) :=
  (AdjoinRoot.powerBasis (Fact.out : Irreducible (kummerRat n f)).ne_zero).finite

/-- The coordinate `x` of the base line, inside the function field. -/
noncomputable def kummerX : KummerField n f := algebraMap ℂ[X] (KummerField n f) X

lemma kummerX_eq : kummerX n f = algebraMap (RatFunc ℂ) (KummerField n f) RatFunc.X := by
  rw [kummerX, IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (KummerField n f),
    RatFunc.algebraMap_X]

/-- The defining relation `yⁿ = f(x)`. -/
lemma kummerRoot_pow :
    AdjoinRoot.root (kummerRat n f) ^ n = algebraMap ℂ[X] (KummerField n f) f := by
  have h0 : AdjoinRoot.mk (kummerRat n f)
      (X ^ n - C (algebraMap ℂ[X] (RatFunc ℂ) f)) = 0 := AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h0
  rw [h0, ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

/-- Characteristic zero makes the extension separable, hence formally étale. -/
instance kummerField_formallyEtale : Algebra.FormallyEtale (RatFunc ℂ) (KummerField n f) :=
  Algebra.FormallyEtale.of_isSeparable _ _

/-- **R01c-1**: `Ω[K⁄ℂ]` is free of rank one on `dx`. -/
noncomputable def kummerKaehlerBasis :
    Module.Basis Unit (KummerField n f) Ω[KummerField n f⁄ℂ] :=
  kaehlerBasisOfEtale ℂ (RatFunc ℂ) (KummerField n f) ratFuncKaehlerBasis

end Field

section Quartic

/-- The quartic's branch polynomial `2 − x⁴`: `X⁴ + Y⁴ = 2` is `Y⁴ = 2 − X⁴`. -/
noncomputable def fermatQuartic : ℂ[X] := C 2 - X ^ 4

/-- The nested Fermat polynomial of degree four is the Kummer polynomial of `2 − x⁴`. -/
lemma fermatNested_eq_kummerPoly : fermatNested 4 = kummerPoly 4 fermatQuartic := by
  simp only [fermatNested, kummerPoly, fermatQuartic, map_sub]
  ring

instance fermatQuartic_kummerRat_irreducible : Fact (Irreducible (kummerRat 4 fermatQuartic)) :=
  ⟨by
    rw [← kummerPoly_map]
    refine (kummerPoly_monic 4 fermatQuartic (by norm_num)).irreducible_iff_irreducible_map_fraction_map.mp
      ?_
    rw [← fermatNested_eq_kummerPoly]
    exact fermatNested_irreducible (by norm_num)⟩

end Quartic

end CurveSymmetry

end

-- lean/FermatHolomorphic.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

section ValuationRing

variable {K : Type*} [Field K] (O : ValuationSubring K)

end ValuationRing

section Quartic

local notation "K₄" => KummerField 4 fermatQuartic

instance quarticField_charZero : CharZero K₄ :=
  charZero_of_injective_algebraMap (algebraMap ℂ K₄).injective

/-- The coordinate `x` of the quartic's function field. -/
noncomputable abbrev quarticX : K₄ := kummerX 4 fermatQuartic

/-- The coordinate `y` of the quartic's function field. -/
noncomputable abbrev quarticY : K₄ := AdjoinRoot.root (kummerRat 4 fermatQuartic)

/-- The numerators `1, x, y` of the canonical differentials `P·dx/y³`. -/
noncomputable def quarticHoloNum : Fin 3 → K₄ := ![1, quarticX, quarticY]

/-- The differentials `dx/y³`, `x·dx/y³` and `y·dx/y³ = dx/y²`. -/
noncomputable def quarticHolo (i : Fin 3) : Ω[K₄⁄ℂ] :=
  (quarticHoloNum i * quarticY⁻¹ ^ 3) • KaehlerDifferential.D ℂ K₄ quarticX

end Quartic

end CurveSymmetry

end

-- lean/QuarticComparison.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

section KummerFraction

variable (n : ℕ) (f : ℂ[X])

noncomputable instance kummerRing_algebra : Algebra (KummerRing n f) (KummerField n f) :=
  (kummerRingMap n f).toRingHom.toAlgebra

lemma kummerRing_algebraMap_apply (r : KummerRing n f) :
    algebraMap (KummerRing n f) (KummerField n f) r = kummerRingMap n f r :=
  rfl

instance kummerRing_scalarTower : IsScalarTower ℂ (KummerRing n f) (KummerField n f) :=
  IsScalarTower.of_algebraMap_eq fun z => by
    rw [kummerRing_algebraMap_apply, IsScalarTower.algebraMap_apply ℂ ℂ[X] (KummerRing n f),
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

/-- The Kummer field is the fraction field of the Kummer ring: clearing the denominators of
the coefficients writes every element as a quotient. -/
theorem kummerRing_isFractionRing (hn : n ≠ 0) [Fact (Irreducible (kummerRat n f))] :
    IsFractionRing (KummerRing n f) (KummerField n f) := by
  have : FaithfulSMul (KummerRing n f) (KummerField n f) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (kummerRingMap_injective n f hn)
  refine IsFractionRing.of_field (R := KummerRing n f) (K := KummerField n f) fun z => ?_
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨b, hb, hbp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℂ[X]) p
  have hb0 : algebraMap ℂ[X] (KummerField n f) b ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (KummerField n f)]
    exact (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) (KummerField n f)).injective).mpr
      (RatFunc.algebraMap_ne_zero (nonZeroDivisors.ne_zero hb))
  refine ⟨AdjoinRoot.mk _ (IsLocalization.integerNormalization (nonZeroDivisors ℂ[X]) p),
    algebraMap ℂ[X] (KummerRing n f) b, ?_⟩
  rw [kummerRing_algebraMap_apply, kummerRing_algebraMap_apply, kummerRingMap_mk, hbp,
    AlgHom.commutes, eq_div_iff hb0, Algebra.smul_def, map_mul, Polynomial.algebraMap_apply,
    AdjoinRoot.mk_C, mul_comm]
  congr 1

end KummerFraction

section Fermat

/-- The coordinate ring `ℂ[X, Y]/(X^d + Y^d − 2)` of the Fermat curve. -/
abbrev FermatCoordinateRing (d : ℕ) : Type := BPoly ⧸ Ideal.span {fermatPolynomial d}

/-- The function field of the Fermat curve `X^d + Y^d = 2`. -/
abbrev FermatFunctionField (d : ℕ) : Type := FractionRing (FermatCoordinateRing d)

instance fermatCoordinateRing_isDomain (d : ℕ) [NeZero d] : IsDomain (FermatCoordinateRing d) := by
  have : (Ideal.span {fermatPolynomial d}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp
        (fermat_irreducible (Nat.pos_of_ne_zero (NeZero.ne d))))
  exact Ideal.Quotient.isDomain _

end Fermat

section Similarity

/-- The pullback along the direct similarity `z ↦ az + b`, in the coordinates `X = z`,
`Y = z̄`. -/
noncomputable def simPull (a b : ℂ) : BPoly →ₐ[ℂ] BPoly :=
  MvPolynomial.aeval fun i : Fin 2 =>
    if i = 0 then MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b
    else MvPolynomial.C (star a) * MvPolynomial.X 1 + MvPolynomial.C (star b)

lemma simPull_comp (a b a' b' : ℂ) :
    (simPull a b).comp (simPull a' b') = simPull (a' * a) (a' * b + b') := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [simPull, star_mul, star_add] <;> ring

lemma simPull_one_zero : simPull 1 0 = AlgHom.id ℂ BPoly := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [simPull]

/-- The pullback along a similarity is an automorphism, with the inverse similarity's
pullback as inverse. -/
noncomputable def simPullEquiv (a b : ℂ) (ha : a ≠ 0) : BPoly ≃ₐ[ℂ] BPoly :=
  AlgEquiv.ofAlgHom (simPull a b) (simPull a⁻¹ (-(a⁻¹ * b)))
    (by rw [simPull_comp, inv_mul_cancel₀ ha, show a⁻¹ * b + -(a⁻¹ * b) = 0 by ring,
      simPull_one_zero])
    (by rw [simPull_comp, mul_inv_cancel₀ ha,
      show a * -(a⁻¹ * b) + b = 0 by field_simp; ring, simPull_one_zero])

end Similarity

section Quartic

local notation "K₄" => KummerField 4 fermatQuartic

end Quartic

end CurveSymmetry

end


