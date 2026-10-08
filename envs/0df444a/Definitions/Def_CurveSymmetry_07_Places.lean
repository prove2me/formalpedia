-- Prove2me | Definitions.Def_CurveSymmetry_07_Places
-- name    : CurveSymmetry_07_Places
-- status  : Definition
-- author  : @carlok
-- created : 2026-10-07T12:16:45.669424+00:00
-- url     : https://prove2.me/theorems/3fe7e49b-5c9a-4596-b334-00181446c604
-- title:
--   Places of the double cover $w^2=h(t)$: valuation rings at points, the place over $t=\infty$, and branch points
-- statement:
--   Let $A$ be a Dedekind domain with fraction field $K$. For $h\in\mathbb C[t]$ let $L_h=\mathbb C(t)[W]/(W^2-h)$ and $R_h=\mathbb C[t][W]/(W^2-h)$, with $w$ the class of $W$. For the extremal family let $m\ge1$ and $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$, $h_{m,\alpha}(t)=-t(t^m+1)(\alpha t^m+\bar\alpha)$, and $L_{m,\alpha}=L_{h_{m,\alpha}}$, with $t,w\in L_{m,\alpha}$. Places are represented by valuation subrings.
--
--   The central construction is the chart at infinity of the family, the ring isomorphism
--   $$L_{m,\alpha}\longrightarrow L_{m,\bar\alpha},\qquad t\longmapsto\frac1s,\qquad w\longmapsto\frac{w'}{s^{m+1}},$$
--   where $s$ and $w'$ denote $t$ and $w$ in $L_{m,\bar\alpha}$. It is built from the $\mathbb C$-algebra endomorphism $t\mapsto1/t$ of $\mathbb C(t)$ and is well defined because $h_{m,\alpha}(1/s)=s^{-(2m+2)}h_{m,\bar\alpha}(s)$. The place of $L_{m,\alpha}$ over $t=\infty$ is the preimage under it of the place of $L_{m,\bar\alpha}$ at the point $(0,0)$. The file also defines:
--
--   1. For a prime $\mathfrak p\subseteq A$, the localization $A_{\mathfrak p}$ as a subring of $K$, and, for $\mathfrak p\ne0$, the valuation subring of $K$ it defines. For a valuation subring $O\subseteq K$ containing $A$, its center $\{a\in A : a\in\mathfrak m_O\}$, a prime ideal of $A$.
--   2. The inclusion of $R_h$ in $L_h$ through $W\mapsto w$, and, for $(c,d)\in\mathbb C^2$ with $d^2=h(c)$, the place of $L_h$ at the point $(c,d)$: the localization of $R_h$ at the kernel of the evaluation $t\mapsto c$, $W\mapsto d$.
--   3. For $p\in\mathbb C\cup\{\infty\}$, the places of $L_{m,\alpha}$ over $p$: the valuation subrings $O\ne L_{m,\alpha}$ containing $\mathbb C$ such that $t-c\in O$ and $(t-c)^{-1}\notin O$ if $p=c\in\mathbb C$, and $t\notin O$ if $p=\infty$. A point $p$ is a branch point when fewer than two places lie over it.
--
--   These definitions give the double cover (7) its places. The point places and the place over $t=\infty$ are those at which differentials are tested in the genus computations for Lemma 4 and Remark 5, and the branch points counted in the proof of Lemma 4 are defined by fibres, as points over which fewer than two places lie; ramification indices are not used.
--
--   **Formalization Note**: Places are Mathlib `ValuationSubring`s. The Dedekind, integral-closure and fraction-field structures of $R_h$ are instances under the `Fact` hypotheses that $h$ is squarefree and $W^2-h$ is irreducible, both provided for $h_{m,\alpha}$ when $m\ge1$ and $\alpha\ne\bar\alpha$. The number of places is `Set.ncard`, which is $0$ for an infinite set. The file also proves that $A_{\mathfrak p}$ is a discrete valuation ring for $\mathfrak p\ne0$ and that $t\mapsto1/t$ is surjective.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), definitions of the formalization, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean modules DedekindPlaces, QuadraticPlaces, QuadraticInfinity, FamilyBranchPoints in https://github.com/carlok/curve-symmetry-lean/tree/d99bc17a1c397956c05d7417de50f9beed56580f/lean (C. Perassi)

-- Definitions, part 07 of 12, generated from curve-symmetry-lean by skeleton
-- subtraction: the source modules below, in dependency order, each in its own
-- section; only definitions, instances and the theorems they need are kept.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
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
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic
import Mathlib.Topology.Compactification.OnePoint.Basic

-- lean/DedekindPlaces.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open IsLocalRing

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K]

variable (K) in
/-- The localization at a prime, as a subalgebra of the fraction field. -/
noncomputable abbrev primeLocalization (P : Ideal A) [P.IsPrime] : Subalgebra A K :=
  Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors

lemma primeLocalization_dvr (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    IsDiscreteValuationRing (primeLocalization K P) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP _

variable (K) in
/-- The valuation subring `A_P ⊆ K` of a nonzero prime `P`. -/
noncomputable def primeValuationSubring (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    ValuationSubring K where
  toSubring := (primeLocalization K P).toSubring
  mem_or_inv_mem' x := by
    have := primeLocalization_dvr (K := K) P hP
    rcases ValuationRing.isInteger_or_isInteger (primeLocalization K P) x with
      ⟨y, hy⟩ | ⟨y, hy⟩
    · left
      rw [← hy]
      exact y.2
    · right
      rw [← hy]
      exact y.2

lemma algebraMap_mem_primeValuationSubring {P : Ideal A} [P.IsPrime] (hP : P ≠ ⊥) (a : A) :
    algebraMap A K a ∈ primeValuationSubring K P hP :=
  ⟨a, 1, P.primeCompl.one_mem, by simp⟩

variable (K) in
/-- The center in `A` of a valuation subring containing `A`. -/
noncomputable def placeCenter (O : ValuationSubring K) (hO : ∀ a : A, algebraMap A K a ∈ O) :
    Ideal A :=
  Ideal.comap ((algebraMap A K).codRestrict O hO) (maximalIdeal O)

instance placeCenter_isPrime (O : ValuationSubring K) (hO : ∀ a : A, algebraMap A K a ∈ O) :
    (placeCenter K O hO).IsPrime := by
  unfold placeCenter
  infer_instance

omit [IsDedekindDomain A] [IsFractionRing A K] in
lemma mem_placeCenter (O : ValuationSubring K) (hO : ∀ a : A, algebraMap A K a ∈ O) (a : A) :
    a ∈ placeCenter K O hO ↔ O.valuation (algebraMap A K a) < 1 := by
  rw [placeCenter, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

omit [IsDedekindDomain A] [IsFractionRing A K] in
/-- Outside the center, elements of `A` are invertible in `O`. -/
lemma inv_mem_of_notMem_placeCenter (O : ValuationSubring K) (hO : ∀ a : A, algebraMap A K a ∈ O)
    {a : A} (ha : a ∉ placeCenter K O hO) : (algebraMap A K a)⁻¹ ∈ O := by
  rw [mem_placeCenter] at ha
  have hle := (O.valuation_le_one_iff _).mpr (hO a)
  have heq : O.valuation (algebraMap A K a) = 1 := le_antisymm hle (not_lt.mp ha)
  rw [← O.valuation_le_one_iff, map_inv₀, heq, inv_one]

lemma placeCenter_ne_bot (O : ValuationSubring K) (hO : ∀ a : A, algebraMap A K a ∈ O)
    (htop : O ≠ ⊤) : placeCenter K O hO ≠ ⊥ := by
  intro hbot
  apply htop
  refine top_unique fun x _ => ?_
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsn : s ∉ placeCenter K O hO := by rw [hbot]; simpa using hs0
  rw [div_eq_mul_inv]
  exact mul_mem (hO a) (inv_mem_of_notMem_placeCenter O hO hsn)

end CurveSymmetry

end

-- lean/QuadraticPlaces.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

section

variable (h : ℂ[X])

noncomputable instance quadRingAlgebra : Algebra (QuadRing h) (QuadField h) :=
  (quadRingMap h).toRingHom.toAlgebra

instance quadRing_scalarTower : IsScalarTower ℂ[X] (QuadRing h) (QuadField h) :=
  IsScalarTower.of_algebraMap_eq fun p => ((quadRingMap h).commutes p).symm

/-- The maximal ideal of a point is nonzero: it contains `t − c`. -/
lemma quadEval_ker_ne_bot (c d : ℂ) (hd : d ^ 2 = h.eval c) :
    RingHom.ker (quadEval h c d hd) ≠ ⊥ := by
  intro hb
  have hmem : AdjoinRoot.of (quadPoly h) (X - C c) ∈ RingHom.ker (quadEval h c d hd) := by
    rw [RingHom.mem_ker, quadEval_of, eval_sub, eval_X, eval_C, sub_self]
  rw [hb, Ideal.mem_bot] at hmem
  have hinj := AdjoinRoot.of.injective_of_degree_ne_zero (f := quadPoly h) (by
    rw [degree_eq_natDegree (quadPoly_monic h).ne_zero,
      show (quadPoly h).natDegree = 2 from natDegree_X_pow_sub_C]
    decide)
  exact X_sub_C_ne_zero c (hinj (hmem.trans (map_zero _).symm))

instance quadEval_ker_isPrime (c d : ℂ) (hd : d ^ 2 = h.eval c) :
    (RingHom.ker (quadEval h c d hd)).IsPrime :=
  RingHom.ker_isPrime _

variable [hsq : Fact (Squarefree h)] [hirr : Fact (Irreducible (quadRat h))]

instance quadRing_isDomain : IsDomain (QuadRing h) :=
  Function.Injective.isDomain (quadRingMap h).toRingHom
    (quadRingMap_injective h hsq.out.ne_zero)

instance quadRing_isIntegralClosure : IsIntegralClosure (QuadRing h) ℂ[X] (QuadField h) where
  algebraMap_injective := quadRingMap_injective h hsq.out.ne_zero
  isIntegral_iff {x} := quadRingMap_range h hsq.out x

instance quadRing_isDedekindDomain : IsDedekindDomain (QuadRing h) :=
  IsIntegralClosure.isDedekindDomain ℂ[X] (RatFunc ℂ) (QuadField h) (QuadRing h)

instance quadRing_isFractionRing : IsFractionRing (QuadRing h) (QuadField h) :=
  IsIntegralClosure.isFractionRing_of_finite_extension ℂ[X] (RatFunc ℂ) (QuadField h) (QuadRing h)

/-- The place of `L` at the point `(c, d)` of the affine double cover. -/
noncomputable def quadPlace (c d : ℂ) (hd : d ^ 2 = h.eval c) : ValuationSubring (QuadField h) :=
  primeValuationSubring (QuadField h) (RingHom.ker (quadEval h c d hd))
    (quadEval_ker_ne_bot h c d hd)

end

instance familyH_squarefree_fact {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)] :
    Fact (Squarefree (familyH m α)) :=
  ⟨familyH_squarefree_of hm.out ha.out⟩

end CurveSymmetry

end

-- lean/QuadraticInfinity.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

open scoped nonZeroDivisors

section Generic

variable {A K : Type*} [CommRing A] [Field K] [Algebra A K]

end Generic

lemma ratFunc_aeval_X (p : ℂ[X]) :
    aeval (RatFunc.X : RatFunc ℂ) p = algebraMap ℂ[X] (RatFunc ℂ) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | monomial n a =>
      rw [aeval_monomial, ← C_mul_X_pow_eq_monomial, map_mul, map_pow, RatFunc.algebraMap_C,
        RatFunc.algebraMap_X, RatFunc.algebraMap_eq_C]

lemma ratFunc_X_inv_transcendental : Transcendental ℂ (RatFunc.X : RatFunc ℂ)⁻¹ := by
  have hX : Transcendental ℂ (RatFunc.X : RatFunc ℂ) := by
    rw [transcendental_iff_injective]
    intro p q hpq
    rw [ratFunc_aeval_X, ratFunc_aeval_X] at hpq
    exact RatFunc.algebraMap_injective ℂ hpq
  intro halg
  exact hX (IsAlgebraic.inv_iff.mp halg)

lemma ratInv_hφ : (ℂ[X])⁰ ≤ (RatFunc ℂ)⁰.comap (aeval (R := ℂ) (RatFunc.X : RatFunc ℂ)⁻¹) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (transcendental_iff_injective.mp ratFunc_X_inv_transcendental)

/-- The `ℂ`-algebra endomorphism of `ℂ(t)` sending `t` to `1/t`. -/
noncomputable def ratInv : RatFunc ℂ →ₐ[ℂ] RatFunc ℂ :=
  RatFunc.liftAlgHom (aeval (RatFunc.X : RatFunc ℂ)⁻¹) ratInv_hφ

lemma ratInv_algebraMap (p : ℂ[X]) :
    ratInv (algebraMap ℂ[X] (RatFunc ℂ) p) = aeval (RatFunc.X : RatFunc ℂ)⁻¹ p := by
  have h := RatFunc.liftAlgHom_apply_div (φ := aeval (RatFunc.X : RatFunc ℂ)⁻¹)
    (hφ := ratInv_hφ) p 1
  simp only [map_one, div_one] at h
  exact h

lemma ratInv_X : ratInv (RatFunc.X : RatFunc ℂ) = (RatFunc.X : RatFunc ℂ)⁻¹ := by
  have h := ratInv_algebraMap X
  rwa [aeval_X, RatFunc.algebraMap_X] at h

lemma ratInv_C (c : ℂ) : ratInv (algebraMap ℂ[X] (RatFunc ℂ) (C c)) =
    algebraMap ℂ[X] (RatFunc ℂ) (C c) := by
  rw [ratInv_algebraMap, aeval_C, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]

lemma ratInv_surjective : Function.Surjective ratInv := by
  have hpoly (p : ℂ[X]) : algebraMap ℂ[X] (RatFunc ℂ) p ∈ Set.range ratInv := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        obtain ⟨a, ha⟩ := hp
        obtain ⟨b, hb⟩ := hq
        exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | monomial n c =>
        refine ⟨algebraMap ℂ[X] (RatFunc ℂ) (C c) * ((RatFunc.X : RatFunc ℂ)⁻¹) ^ n, ?_⟩
        rw [map_mul, ratInv_C, map_pow, map_inv₀, ratInv_X, inv_inv, ← C_mul_X_pow_eq_monomial,
          map_mul, map_pow, RatFunc.algebraMap_X]
  intro f
  obtain ⟨a, ha⟩ := hpoly f.num
  obtain ⟨b, hb⟩ := hpoly f.denom
  exact ⟨a / b, by rw [map_div₀, ha, hb, RatFunc.num_div_denom]⟩

/-- `h_α(1/s) = h_{conj α}(s) · s^(-(2m+2))`. -/
lemma familyH_inv_identity (m : ℕ) (α : ℂ) :
    aeval (RatFunc.X : RatFunc ℂ)⁻¹ (familyH m α) =
      algebraMap ℂ[X] (RatFunc ℂ) (familyH m (star α)) *
        ((RatFunc.X : RatFunc ℂ)⁻¹) ^ (2 * m + 2) := by
  have hX := RatFunc.X_ne_zero (K := ℂ)
  simp only [familyH, familyB, familyA, map_neg, map_mul, map_add, map_pow, aeval_X, aeval_C,
    map_one, RatFunc.algebraMap_X, RatFunc.algebraMap_C, star_star, RatFunc.algebraMap_eq_C,
    inv_pow]
  field_simp
  ring

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

instance star_ne_star_star_fact : Fact (star α ≠ star (star α)) :=
  ⟨by simpa only [star_star, ne_comm] using ha.out⟩

omit hm in
lemma familyH_eval_zero (m : ℕ) (α : ℂ) : (familyH m α).eval 0 = 0 := by
  simp [familyH, familyB]

variable (m α) in
/-- `t ↦ 1/s`, `w ↦ w'·s^(-(m+1))`. -/
noncomputable def familyInfinityMap :
    QuadField (familyH m α) →+* QuadField (familyH m (star α)) :=
  AdjoinRoot.lift ((algebraMap (RatFunc ℂ) (QuadField (familyH m (star α)))).comp ratInv.toRingHom)
    (AdjoinRoot.root (quadRat (familyH m (star α))) *
      (algebraMap (RatFunc ℂ) (QuadField (familyH m (star α))) (RatFunc.X : RatFunc ℂ)⁻¹) ^ (m + 1))
    (by
      rw [eval₂_quadRat, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        ratInv_algebraMap, familyH_inv_identity, map_mul, map_pow, mul_pow, quadRoot_sq]
      ring)

lemma familyInfinityMap_of (r : RatFunc ℂ) :
    familyInfinityMap m α (algebraMap (RatFunc ℂ) (QuadField (familyH m α)) r) =
      algebraMap (RatFunc ℂ) (QuadField (familyH m (star α))) (ratInv r) :=
  AdjoinRoot.lift_of _

lemma familyInfinityMap_root :
    familyInfinityMap m α (AdjoinRoot.root (quadRat (familyH m α))) =
      AdjoinRoot.root (quadRat (familyH m (star α))) *
        (algebraMap (RatFunc ℂ) (QuadField (familyH m (star α))) (RatFunc.X : RatFunc ℂ)⁻¹) ^
          (m + 1) :=
  AdjoinRoot.lift_root _

lemma familyInfinityMap_surjective : Function.Surjective (familyInfinityMap m α) := by
  let φ := familyInfinityMap m α
  have hadd {a b : QuadField (familyH m (star α))} (ha' : a ∈ Set.range φ) (hb : b ∈ Set.range φ) :
      a + b ∈ Set.range φ := by
    obtain ⟨x, rfl⟩ := ha'
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x + y, map_add φ x y⟩
  have hmul {a b : QuadField (familyH m (star α))} (ha' : a ∈ Set.range φ) (hb : b ∈ Set.range φ) :
      a * b ∈ Set.range φ := by
    obtain ⟨x, rfl⟩ := ha'
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x * y, map_mul φ x y⟩
  have hof (r : RatFunc ℂ) :
      algebraMap (RatFunc ℂ) (QuadField (familyH m (star α))) r ∈ Set.range φ := by
    obtain ⟨q, rfl⟩ := ratInv_surjective r
    exact ⟨algebraMap (RatFunc ℂ) (QuadField (familyH m α)) q, familyInfinityMap_of q⟩
  have hroot : AdjoinRoot.root (quadRat (familyH m (star α))) ∈ Set.range φ := by
    have hX := RatFunc.X_ne_zero (K := ℂ)
    have he : AdjoinRoot.root (quadRat (familyH m (star α))) =
        φ (AdjoinRoot.root (quadRat (familyH m α))) *
          algebraMap (RatFunc ℂ) (QuadField (familyH m (star α))) (RatFunc.X ^ (m + 1)) := by
      rw [familyInfinityMap_root, mul_assoc, map_pow, ← mul_pow, ← map_mul, inv_mul_cancel₀ hX,
        map_one, one_pow, mul_one]
    rw [he]
    exact hmul ⟨_, rfl⟩ (hof _)
  intro y
  induction y using AdjoinRoot.induction_on with
  | ih p =>
    induction p using Polynomial.induction_on with
    | C a =>
        rw [AdjoinRoot.mk_C]
        exact hof a
    | add p q hp hq =>
        rw [map_add]
        exact hadd hp hq
    | monomial n a hn =>
        rw [pow_succ, ← mul_assoc, map_mul, AdjoinRoot.mk_X]
        exact hmul hn hroot

variable (m α) in
/-- The ring isomorphism with the chart at infinity. -/
noncomputable def familyInfinityEquiv :
    QuadField (familyH m α) ≃+* QuadField (familyH m (star α)) :=
  RingEquiv.ofBijective (familyInfinityMap m α)
    ⟨(familyInfinityMap m α).injective, familyInfinityMap_surjective⟩

lemma familyInfinityMap_polyC (c : ℂ) :
    familyInfinityMap m α (algebraMap ℂ[X] (QuadField (familyH m α)) (C c)) =
      algebraMap ℂ[X] (QuadField (familyH m (star α))) (C c) := by
  rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField (familyH m α)),
    familyInfinityMap_of, ratInv_C,
    ← IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField (familyH m (star α)))]

omit hm ha in
lemma familyH_star_zero_point (m : ℕ) (α : ℂ) : (0 : ℂ) ^ 2 = (familyH m (star α)).eval 0 := by
  rw [familyH_eval_zero]
  ring

variable (m α) in
/-- The place of the function field of `V_α` over `t = ∞`. -/
noncomputable def familyInfinityPlace : ValuationSubring (QuadField (familyH m α)) :=
  (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).comap
    (familyInfinityMap m α)

end CurveSymmetry

end

-- lean/FamilyBranchPoints.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial OnePoint

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

variable (m α) in
/-- The places of the function field lying over a point of the `t`-line. -/
def familyPlacesOver (p : OnePoint ℂ) : Set (ValuationSubring (QuadField (familyH m α))) :=
  {O | O ≠ ⊤ ∧ (∀ c : ℂ, algebraMap ℂ[X] (QuadField (familyH m α)) (C c) ∈ O) ∧
    p.elim (algebraMap ℂ[X] (QuadField (familyH m α)) X ∉ O)
      (fun c => algebraMap ℂ[X] (QuadField (familyH m α)) (X - C c) ∈ O ∧
        (algebraMap ℂ[X] (QuadField (familyH m α)) (X - C c))⁻¹ ∉ O)}

variable (m α) in
/-- The recorded definition: fewer than two places over the point. -/
def IsFamilyBranchPoint (p : OnePoint ℂ) : Prop :=
  (familyPlacesOver m α p).ncard < 2

end CurveSymmetry

end


