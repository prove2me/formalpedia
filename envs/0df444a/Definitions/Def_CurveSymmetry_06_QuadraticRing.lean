-- Prove2me | Definitions.Def_CurveSymmetry_06_QuadraticRing
-- name    : CurveSymmetry_06_QuadraticRing
-- status  : Definition
-- author  : @carlok
-- created : 2026-10-07T12:15:19.106825+00:00
-- url     : https://prove2.me/theorems/bf433ed0-dca1-4c1c-83b2-3c0c6738b8e5
-- title:
--   The double cover $w^2=h(t)$: the extension $\mathbb C(t)[W]/(W^2-h)$, its coordinate ring and evaluation at points
-- statement:
--   Let $h\in\mathbb C[t]$ be a polynomial, $\mathbb C(t)$ the field of rational functions, and write $w$ for the class of the variable $W$ in the quotients below. For the extremal family, $h_{m,\alpha}(t)=-t(t^m+1)(\alpha t^m+\bar\alpha)$ with $m\in\mathbb N$ and $\alpha\in\mathbb C$.
--
--   The file defines the quadratic extension of $\mathbb C(t)$ and the affine coordinate ring of the double cover $w^2=h(t)$,
--   $$L_h=\mathbb C(t)[W]/(W^2-h),\qquad R_h=\mathbb C[t][W]/(W^2-h),$$
--   where $L_h$ is a field when $W^2-h$ is irreducible over $\mathbb C(t)$. It also defines:
--
--   1. The conjugation of $L_h$ over $\mathbb C(t)$: the $\mathbb C(t)$-algebra endomorphism with $w\mapsto-w$, so that $a+bw\mapsto a-bw$ for $a,b\in\mathbb C(t)$.
--   2. The $\mathbb C[t]$-algebra homomorphism $R_h\to L_h$ with $W\mapsto w$.
--   3. For $(c,d)\in\mathbb C^2$ with $d^2=h(c)$, the evaluation homomorphism $R_h\to\mathbb C$ with $t\mapsto c$ and $W\mapsto d$, at the point $(c,d)$ of the curve $w^2=h(t)$.
--
--   For $h=h_{m,\alpha}$ the polynomial $W^2-h$ over $\mathbb C(t)$ is, by definition, the quadratic that presents the function field of $P_\alpha=0$.
--
--   With $h=h_{m,\alpha}$, $L_h$ is the double cover (7) of the proof of Lemma 4, the field in which places and holomorphic differentials are computed for the genus clause of Lemma 4 and for Remark 5, and $R_h$ is its affine coordinate ring; the evaluations at the points $(c,d)$ give the maximal ideals at which the finite places are centered.
--
--   **Formalization Note**: Both rings are `AdjoinRoot` quotients. The irreducibility of $W^2-h$ that makes $L_h$ a field is supplied as a `Fact` instance, derived from $m\ge1$ and $\alpha\ne\bar\alpha$ when $h=h_{m,\alpha}$. The file also proves: for squarefree $h$, an element of $L_h$ is integral over $\mathbb C[t]$ if and only if it equals $a+bw$ with $a,b\in\mathbb C[t]$; the map $R_h\to L_h$ is injective when $h\ne0$, and its image is the integral closure of $\mathbb C[t]$ when $h$ is squarefree; and every maximal ideal of $\mathbb C[t]$ contains some $t-c$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), definitions of the formalization, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean modules QuadraticIntegralClosure, QuadraticDedekind, QuadraticRing in https://github.com/carlok/curve-symmetry-lean/tree/d99bc17a1c397956c05d7417de50f9beed56580f/lean (C. Perassi)

-- Definitions, part 06 of 12, generated from curve-symmetry-lean by skeleton
-- subtraction: the source modules below, in dependency order, each in its own
-- section; only definitions, instances and the theorems they need are kept.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
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
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

-- lean/QuadraticIntegralClosure.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

/-- `W² − h` over `ℂ(t)`. -/
noncomputable def quadRat (h : ℂ[X]) : (RatFunc ℂ)[X] :=
  X ^ 2 - C (algebraMap ℂ[X] (RatFunc ℂ) h)

/-- The quadratic extension `ℂ(t)[W]/(W² − h)`. -/
abbrev QuadField (h : ℂ[X]) : Type := AdjoinRoot (quadRat h)

/-- A rational function whose square times a squarefree polynomial is polynomial
is itself polynomial. -/
lemma ratFunc_polynomial_of_sq_mul {h : ℂ[X]} (hsq : Squarefree h) {b : RatFunc ℂ} {p : ℂ[X]}
    (hb : b ^ 2 * algebraMap ℂ[X] (RatFunc ℂ) h = algebraMap ℂ[X] (RatFunc ℂ) p) :
    ∃ c : ℂ[X], b = algebraMap ℂ[X] (RatFunc ℂ) c := by
  have hd0 := RatFunc.denom_ne_zero b
  have hden : algebraMap ℂ[X] (RatFunc ℂ) b.denom ≠ 0 := RatFunc.algebraMap_ne_zero hd0
  have hpoly : b.num ^ 2 * h = p * b.denom ^ 2 := by
    apply RatFunc.algebraMap_injective ℂ
    rw [← RatFunc.num_div_denom b, div_pow] at hb
    field_simp at hb
    simp only [map_pow, map_mul]
    linear_combination hb
  have hdvd : b.denom * b.denom ∣ h := by
    have hc : IsCoprime (b.denom ^ 2) (b.num ^ 2) :=
      (RatFunc.isCoprime_num_denom b).symm.pow
    rw [← sq]
    exact hc.dvd_of_dvd_mul_left ⟨p, by rw [hpoly, mul_comm]⟩
  have hunit : IsUnit b.denom := hsq _ hdvd
  have hone : b.denom = 1 := (RatFunc.monic_denom b).isUnit_iff.mp hunit
  refine ⟨b.num, ?_⟩
  conv_lhs => rw [← RatFunc.num_div_denom b, hone, map_one, div_one]

section

variable (h : ℂ[X])

lemma quadRat_monic : (quadRat h).Monic := monic_X_pow_sub_C _ two_ne_zero

lemma quadRat_natDegree : (quadRat h).natDegree = 2 := natDegree_X_pow_sub_C

instance quadField_nontrivial : Nontrivial (QuadField h) :=
  AdjoinRoot.nontrivial _ (by
    rw [degree_eq_natDegree (quadRat_monic h).ne_zero, quadRat_natDegree]
    decide)

lemma quadRoot_sq :
    AdjoinRoot.root (quadRat h) ^ 2 =
      algebraMap (RatFunc ℂ) (QuadField h) (algebraMap ℂ[X] (RatFunc ℂ) h) := by
  have h0 : AdjoinRoot.mk (quadRat h) (X ^ 2 - C (algebraMap ℂ[X] (RatFunc ℂ) h)) = 0 :=
    AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h0
  exact h0

/-- Every element is `a + b·w` with rational-function coefficients. -/
lemma quad_exists_eq (x : QuadField h) :
    ∃ a b : RatFunc ℂ, x = algebraMap (RatFunc ℂ) (QuadField h) a +
      algebraMap (RatFunc ℂ) (QuadField h) b * AdjoinRoot.root (quadRat h) := by
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    have hmon := quadRat_monic h
    have hne1 : quadRat h ≠ 1 := by
      intro h1
      have hd := quadRat_natDegree h
      rw [h1, natDegree_one] at hd
      omega
    have hle : (p %ₘ quadRat h).natDegree ≤ 1 := by
      have hlt := natDegree_modByMonic_lt p hmon hne1
      rw [quadRat_natDegree] at hlt
      omega
    have hmk : AdjoinRoot.mk (quadRat h) p = AdjoinRoot.mk (quadRat h) (p %ₘ quadRat h) := by
      rw [AdjoinRoot.mk_eq_mk]
      have hdiv := modByMonic_add_div p (quadRat h)
      exact ⟨p /ₘ quadRat h, by linear_combination -hdiv⟩
    refine ⟨(p %ₘ quadRat h).coeff 0, (p %ₘ quadRat h).coeff 1, ?_⟩
    rw [hmk]
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hle]
    simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    rw [← AdjoinRoot.algebraMap_eq]
    ring

lemma eval₂_quadRat {S : Type*} [CommRing S] (i : RatFunc ℂ →+* S) (x : S) :
    (quadRat h).eval₂ i x = x ^ 2 - i (algebraMap ℂ[X] (RatFunc ℂ) h) := by
  simp [quadRat]

/-- The conjugation `w ↦ −w` over `ℂ(t)`. -/
noncomputable def quadConj : QuadField h →ₐ[RatFunc ℂ] QuadField h :=
  AdjoinRoot.liftAlgHom (quadRat h) (Algebra.ofId (RatFunc ℂ) (QuadField h))
    (-AdjoinRoot.root (quadRat h)) (by
    rw [eval₂_quadRat, neg_sq, sub_eq_zero]
    exact quadRoot_sq h)

lemma quadConj_apply (a b : RatFunc ℂ) :
    quadConj h (algebraMap (RatFunc ℂ) (QuadField h) a +
      algebraMap (RatFunc ℂ) (QuadField h) b * AdjoinRoot.root (quadRat h)) =
    algebraMap (RatFunc ℂ) (QuadField h) a -
      algebraMap (RatFunc ℂ) (QuadField h) b * AdjoinRoot.root (quadRat h) := by
  rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, quadConj, AdjoinRoot.liftAlgHom_root]
  ring

/-- Integrality of an element of `ℂ(t)` viewed in `L` descends to `ℂ[t]`. -/
lemma quad_ratFunc_integral {a : RatFunc ℂ}
    (ha : IsIntegral ℂ[X] (algebraMap (RatFunc ℂ) (QuadField h) a)) :
    ∃ p : ℂ[X], algebraMap ℂ[X] (RatFunc ℂ) p = a := by
  have hinj : Function.Injective
      ((Algebra.ofId (RatFunc ℂ) (QuadField h)).restrictScalars ℂ[X]) :=
    (algebraMap (RatFunc ℂ) (QuadField h)).injective
  have ha' := (isIntegral_algHom_iff _ hinj).mp ha
  exact IsIntegrallyClosed.isIntegral_iff.mp ha'

/-- G07b-1 (generic): the integral closure of `ℂ[t]` in `ℂ(t)[W]/(W² − h)` is
`ℂ[t] ⊕ ℂ[t]·w` when `h` is squarefree. -/
theorem quad_isIntegral_iff (hsq : Squarefree h) (x : QuadField h) :
    IsIntegral ℂ[X] x ↔ ∃ a b : ℂ[X], x = algebraMap ℂ[X] (QuadField h) a +
      algebraMap ℂ[X] (QuadField h) b * AdjoinRoot.root (quadRat h) := by
  have htower (p : ℂ[X]) : algebraMap ℂ[X] (QuadField h) p =
      algebraMap (RatFunc ℂ) (QuadField h) (algebraMap ℂ[X] (RatFunc ℂ) p) :=
    IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h) p
  constructor
  · intro hx
    obtain ⟨a, b, rfl⟩ := quad_exists_eq h x
    have hσ := hx.map ((quadConj h).restrictScalars ℂ[X])
    rw [AlgHom.restrictScalars_apply, quadConj_apply] at hσ
    have htr : IsIntegral ℂ[X] (algebraMap (RatFunc ℂ) (QuadField h) (2 * a)) := by
      have he : algebraMap (RatFunc ℂ) (QuadField h) (2 * a) =
          (algebraMap (RatFunc ℂ) (QuadField h) a +
            algebraMap (RatFunc ℂ) (QuadField h) b * AdjoinRoot.root (quadRat h)) +
          (algebraMap (RatFunc ℂ) (QuadField h) a -
            algebraMap (RatFunc ℂ) (QuadField h) b * AdjoinRoot.root (quadRat h)) := by
        rw [map_mul, map_ofNat]
        ring
      rw [he]
      exact hx.add hσ
    have hnorm : IsIntegral ℂ[X] (algebraMap (RatFunc ℂ) (QuadField h)
        (a ^ 2 - b ^ 2 * algebraMap ℂ[X] (RatFunc ℂ) h)) := by
      have he : algebraMap (RatFunc ℂ) (QuadField h)
          (a ^ 2 - b ^ 2 * algebraMap ℂ[X] (RatFunc ℂ) h) =
          (algebraMap (RatFunc ℂ) (QuadField h) a +
            algebraMap (RatFunc ℂ) (QuadField h) b * AdjoinRoot.root (quadRat h)) *
          (algebraMap (RatFunc ℂ) (QuadField h) a -
            algebraMap (RatFunc ℂ) (QuadField h) b * AdjoinRoot.root (quadRat h)) := by
        rw [map_sub, map_mul, map_pow, map_pow]
        linear_combination (algebraMap (RatFunc ℂ) (QuadField h) b) ^ 2 * quadRoot_sq h
      rw [he]
      exact hx.mul hσ
    obtain ⟨p, hp⟩ := quad_ratFunc_integral h htr
    obtain ⟨q, hq⟩ := quad_ratFunc_integral h hnorm
    have ha : a = algebraMap ℂ[X] (RatFunc ℂ) (C (1 / 2 : ℂ) * p) := by
      rw [map_mul, hp, RatFunc.algebraMap_C]
      simp only [map_div₀, map_one, map_ofNat]
      ring
    have hb : b ^ 2 * algebraMap ℂ[X] (RatFunc ℂ) h =
        algebraMap ℂ[X] (RatFunc ℂ) ((C (1 / 2 : ℂ) * p) ^ 2 - q) := by
      rw [map_sub, map_pow, ← ha, hq]
      ring
    obtain ⟨c, hc⟩ := ratFunc_polynomial_of_sq_mul hsq hb
    exact ⟨C (1 / 2 : ℂ) * p, c, by rw [htower, htower, ← ha, ← hc]⟩
  · rintro ⟨a, b, rfl⟩
    have hroot : IsIntegral ℂ[X] (AdjoinRoot.root (quadRat h)) := by
      refine ⟨X ^ 2 - C h, monic_X_pow_sub_C _ two_ne_zero, ?_⟩
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, htower, quadRoot_sq, sub_self]
    exact isIntegral_algebraMap.add (isIntegral_algebraMap.mul hroot)

end

lemma quadRat_familyH (m : ℕ) (α : ℂ) : quadRat (familyH m α) = familyQuadraticRat m α := rfl

end CurveSymmetry

end

-- lean/QuadraticDedekind.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

section

variable (h : ℂ[X]) [Fact (Irreducible (quadRat h))]

instance quadField_finiteDimensional : FiniteDimensional (RatFunc ℂ) (QuadField h) :=
  (AdjoinRoot.powerBasis (quadRat_monic h).ne_zero).finite

end

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

instance quadRat_familyH_fact : Fact (Irreducible (quadRat (familyH m α))) :=
  ⟨by rw [quadRat_familyH]; exact familyQuadraticRat_irreducible_of hm.out ha.out⟩

end CurveSymmetry

end

-- lean/QuadraticRing.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

/-- `W² − h` over `ℂ[t]`. -/
noncomputable def quadPoly (h : ℂ[X]) : (ℂ[X])[X] := X ^ 2 - C h

/-- The affine coordinate ring `ℂ[t][W]/(W² − h)` of the double cover. -/
abbrev QuadRing (h : ℂ[X]) : Type := AdjoinRoot (quadPoly h)

section

variable (h : ℂ[X])

lemma quadPoly_monic : (quadPoly h).Monic := monic_X_pow_sub_C _ two_ne_zero

lemma eval₂_quadPoly {S : Type*} [CommRing S] (i : ℂ[X] →+* S) (x : S) :
    (quadPoly h).eval₂ i x = x ^ 2 - i h := by
  simp [quadPoly]

instance quadRing_isIntegral : Algebra.IsIntegral ℂ[X] (QuadRing h) :=
  haveI := (AdjoinRoot.powerBasis' (quadPoly_monic h)).finite
  Algebra.IsIntegral.of_finite ℂ[X] (QuadRing h)

/-- The comparison map to the field, `W ↦ w`. -/
noncomputable def quadRingMap : QuadRing h →ₐ[ℂ[X]] QuadField h :=
  AdjoinRoot.liftAlgHom (quadPoly h) (Algebra.ofId ℂ[X] (QuadField h))
    (AdjoinRoot.root (quadRat h)) (by
    rw [eval₂_quadPoly, sub_eq_zero, quadRoot_sq]
    exact (IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h) h).symm)

lemma quadRingMap_root : quadRingMap h (AdjoinRoot.root (quadPoly h)) =
    AdjoinRoot.root (quadRat h) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- `1` and `w` are independent over `ℂ(t)` when `h ≠ 0`. -/
lemma quad_coeff_eq_zero (hh : h ≠ 0) {a b : RatFunc ℂ}
    (hab : algebraMap (RatFunc ℂ) (QuadField h) a +
      algebraMap (RatFunc ℂ) (QuadField h) b * AdjoinRoot.root (quadRat h) = 0) :
    a = 0 ∧ b = 0 := by
  have hc := congrArg (quadConj h) hab
  rw [quadConj_apply, map_zero] at hc
  have h2 : algebraMap (RatFunc ℂ) (QuadField h) (2 * a) = 0 := by
    rw [map_mul, map_ofNat]
    linear_combination hab + hc
  have ha : a = 0 := by
    have := (algebraMap (RatFunc ℂ) (QuadField h)).injective (h2.trans (map_zero _).symm)
    simpa using this
  refine ⟨ha, ?_⟩
  rw [ha, map_zero, zero_add] at hab
  have hb2 : algebraMap (RatFunc ℂ) (QuadField h) (b * algebraMap ℂ[X] (RatFunc ℂ) h) = 0 := by
    rw [map_mul, ← quadRoot_sq]
    linear_combination AdjoinRoot.root (quadRat h) * hab
  have hb3 := (algebraMap (RatFunc ℂ) (QuadField h)).injective (hb2.trans (map_zero _).symm)
  exact (mul_eq_zero.mp hb3).resolve_right (RatFunc.algebraMap_ne_zero hh)

lemma quadRing_exists_eq (x : QuadRing h) :
    ∃ a b : ℂ[X], x = algebraMap ℂ[X] (QuadRing h) a +
      algebraMap ℂ[X] (QuadRing h) b * AdjoinRoot.root (quadPoly h) := by
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    have hmon := quadPoly_monic h
    have hne1 : quadPoly h ≠ 1 := by
      intro h1
      have hd : (quadPoly h).natDegree = 2 := natDegree_X_pow_sub_C
      rw [h1, natDegree_one] at hd
      omega
    have hle : (p %ₘ quadPoly h).natDegree ≤ 1 := by
      have hlt := natDegree_modByMonic_lt p hmon hne1
      rw [show (quadPoly h).natDegree = 2 from natDegree_X_pow_sub_C] at hlt
      omega
    have hmk : AdjoinRoot.mk (quadPoly h) p = AdjoinRoot.mk (quadPoly h) (p %ₘ quadPoly h) := by
      rw [AdjoinRoot.mk_eq_mk]
      have hdiv := modByMonic_add_div p (quadPoly h)
      exact ⟨p /ₘ quadPoly h, by linear_combination -hdiv⟩
    refine ⟨(p %ₘ quadPoly h).coeff 0, (p %ₘ quadPoly h).coeff 1, ?_⟩
    rw [hmk]
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hle]
    simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    rw [← AdjoinRoot.algebraMap_eq]
    ring

lemma quadRingMap_apply (a b : ℂ[X]) :
    quadRingMap h (algebraMap ℂ[X] (QuadRing h) a +
      algebraMap ℂ[X] (QuadRing h) b * AdjoinRoot.root (quadPoly h)) =
    algebraMap ℂ[X] (QuadField h) a +
      algebraMap ℂ[X] (QuadField h) b * AdjoinRoot.root (quadRat h) := by
  rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, quadRingMap_root]

lemma quadRingMap_injective (hh : h ≠ 0) : Function.Injective (quadRingMap h) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, b, rfl⟩ := quadRing_exists_eq h x
  rw [quadRingMap_apply,
    IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h) a,
    IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h) b] at hx
  obtain ⟨ha, hb⟩ := quad_coeff_eq_zero h hh hx
  rw [RatFunc.algebraMap_injective ℂ (ha.trans (map_zero _).symm),
    RatFunc.algebraMap_injective ℂ (hb.trans (map_zero _).symm)]
  simp

/-- G07b-2b (image): for squarefree `h`, `quadRingMap` is injective with image the
integral closure of `ℂ[t]`. -/
theorem quadRingMap_range (hsq : Squarefree h) (x : QuadField h) :
    IsIntegral ℂ[X] x ↔ ∃ y : QuadRing h, quadRingMap h y = x := by
  rw [quad_isIntegral_iff h hsq]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨_, quadRingMap_apply h a b⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨a, b, rfl⟩ := quadRing_exists_eq h y
    exact ⟨a, b, quadRingMap_apply h a b⟩

/-- Evaluation at a point `(c, d)` of the double cover. -/
noncomputable def quadEval (c d : ℂ) (hd : d ^ 2 = h.eval c) : QuadRing h →+* ℂ :=
  AdjoinRoot.lift (evalRingHom c) d (by
    rw [eval₂_quadPoly, coe_evalRingHom, hd, sub_self])

lemma quadEval_of (c d : ℂ) (hd : d ^ 2 = h.eval c) (p : ℂ[X]) :
    quadEval h c d hd (AdjoinRoot.of _ p) = p.eval c :=
  AdjoinRoot.lift_of _

/-- A maximal ideal of `ℂ[t]` contains some `t − c`. -/
lemma exists_X_sub_C_mem {𝔫 : Ideal ℂ[X]} (hmax : 𝔫.IsMaximal) : ∃ c : ℂ, X - C c ∈ 𝔫 := by
  have hbot : ⊥ < 𝔫 := Ideal.bot_lt_of_maximal 𝔫 (Polynomial.not_isField ℂ)
  obtain ⟨p, hp, hp0⟩ := SetLike.exists_of_lt hbot
  have hp0' : p ≠ 0 := by simpa using hp0
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases hd : p.degree = 0
    · exfalso
      have hu : IsUnit p := by
        rw [eq_C_of_degree_eq_zero hd]
        exact (isUnit_iff_ne_zero.mpr (by
          intro h0
          apply hp0'
          rw [eq_C_of_degree_eq_zero hd, h0, map_zero])).map C
      exact hmax.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
    · obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p hd
      have hfac := mul_divByMonic_eq_iff_isRoot.mpr hr
      rw [← hfac] at hp
      rcases hmax.isPrime.mem_or_mem hp with h1 | h2
      · exact ⟨r, h1⟩
      · have hq0 : p /ₘ (X - C r) ≠ 0 := by
          intro hz
          apply hp0'
          rw [← hfac, hz, mul_zero]
        have hpos : 0 < p.natDegree :=
          Nat.pos_of_ne_zero fun h0 => hd (by rw [degree_eq_natDegree hp0', h0]; rfl)
        have hdeg : (p /ₘ (X - C r)).natDegree < n := by
          rw [natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C]
          omega
        exact ih _ hdeg _ h2 (by simpa using hq0) hq0 rfl

end

end CurveSymmetry

end


