-- Prove2me | Definitions.Def_CurveSymmetry_05_FamilyFunctionField
-- name    : CurveSymmetry_05_FamilyFunctionField
-- status  : Definition
-- author  : @carlok
-- created : 2026-10-07T12:14:11.413142+00:00
-- url     : https://prove2.me/theorems/477ab5d2-fe01-45e1-b5b5-fb9bd898c105
-- title:
--   Multiplicity and ordinary points, weight polynomials, and the function field of $P_\alpha=0$ over $\mathbb C(t)$
-- statement:
--   Let $\mathbb C[X,Y]$ be the complex polynomial ring, $m\in\mathbb N$, $\alpha\in\mathbb C$, $P_\alpha=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$, and $A_{m,\alpha}(t)=\alpha t^m+\bar\alpha$, $B_m(t)=t(t^m+1)$ in $\mathbb C[t]$. For a point $(x,y)\in\mathbb C^2$ let $\mathfrak m_{x,y}=(X-x,\,Y-y)$ be its maximal ideal.
--
--   The file defines the function field of the affine curve $P_\alpha=0$, the branch polynomial, and the quadratic over $\mathbb C(t)$ that presents the function field:
--   $$K_{m,\alpha}=\operatorname{Frac}\big(\mathbb C[X,Y]/(P_\alpha)\big),\qquad h_{m,\alpha}(t)=-B_m(t)A_{m,\alpha}(t)=-t(t^m+1)(\alpha t^m+\bar\alpha),\qquad W^2-h_{m,\alpha}(t)\in\mathbb C(t)[W],$$
--   together with the coordinate ring $\mathbb C[X,Y]/(P_\alpha)$ and the classes $x,y\in K_{m,\alpha}$ of $X,Y$. When $m\ge1$ and $\alpha\ne\bar\alpha$ it further defines the elements $t=x/y$ and $w=t(t^m+1)\,y$ of $K_{m,\alpha}$, the $\mathbb C$-algebra embedding $\mathbb C(t)\to K_{m,\alpha}$ sending the variable to $x/y$, and the comparison homomorphism $\mathbb C(t)[W]/(W^2-h_{m,\alpha})\to K_{m,\alpha}$ that extends it with $W\mapsto w$.
--
--   Independently of the family, it defines:
--
--   1. Multiplicity: $P$ has multiplicity $n$ at $(x,y)$ if $P\in\mathfrak m_{x,y}^n$ and $P\notin\mathfrak m_{x,y}^{n+1}$.
--   2. Ordinary $n$-fold point at the origin: $P$ has multiplicity $n$ at $(0,0)$, and its homogeneous component of degree $n$ equals $c\prod_{i=1}^n(\ell_{i0}X+\ell_{i1}Y)$ with $c\ne0$, every $(\ell_{i0},\ell_{i1})\ne(0,0)$, and $\ell_{i0}\ell_{j1}-\ell_{i1}\ell_{j0}\ne0$ for $i\ne j$.
--   3. Weight polynomials: for $P=\sum p_{ab}X^aY^b$, the polynomials $\sum_k p_{k+m,k}\,s^k$ and $\sum_k p_{k,k+m}\,s^k$ in $\mathbb C[s]$, which collect the coefficients of weight $+m$ and $-m$ as polynomials in $s=XY$.
--
--   $K_{m,\alpha}$ is the function field through which the normalization of $V_\alpha$ is read, and $t$, $w$, $h_{m,\alpha}$ present it as the double cover (7) of $\mathbb C(t)$; its genus is the subject of the genus clause of Lemma 4 and enters Remark 5. Multiplicity and ordinary points give a precise meaning to the ordinary $m$-fold points of Lemma 4. The weight polynomials extract the polynomial $A$ of the radial form (5) from the coefficients of $P$.
--
--   **Formalization Note**: The hypotheses $m\ge1$ and $\alpha\ne\bar\alpha$ are `Fact` instances; they make $\mathbb C[X,Y]/(P_\alpha)$ a domain, and $K_{m,\alpha}$ is its `FractionRing`. The tangent cone is Mathlib's homogeneous component of degree $n$. Under these instances the file also proves that $w^2=h_{m,\alpha}(t)$ in $K_{m,\alpha}$, that $h_{m,\alpha}$ is squarefree and $W^2-h_{m,\alpha}$ is irreducible over $\mathbb C(t)$, and that the comparison homomorphism is bijective.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), definitions of the formalization, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean modules OrdinaryMultiplePoints, RadialAntiForm, FamilyFunctionField in https://github.com/carlok/curve-symmetry-lean/tree/d99bc17a1c397956c05d7417de50f9beed56580f/lean (C. Perassi)

-- Definitions, part 05 of 12, generated from curve-symmetry-lean by skeleton
-- subtraction: the source modules below, in dependency order, each in its own
-- section; only definitions, instances and the theorems they need are kept.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

-- lean/OrdinaryMultiplePoints.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

/-- The maximal ideal of polynomials vanishing at the complex point `(x,y)`. -/
noncomputable def pointIdeal (x y : ℂ) : Ideal BPoly :=
  Ideal.span {X 0 - C x, X 1 - C y}

/-- The usual algebraic multiplicity of a plane curve equation at a point:
membership in the `n`th, but not the `(n+1)`st, power of the maximal ideal. -/
def HasMultiplicityAt (P : BPoly) (x y : ℂ) (n : ℕ) : Prop :=
  P ∈ pointIdeal x y ^ n ∧ P ∉ pointIdeal x y ^ (n + 1)

/-- An ordinary `n`-fold point at the origin: multiplicity `n`, and the tangent
cone, the degree-`n` component, is a nonzero multiple of `n` pairwise
nonproportional nonzero linear forms. -/
def OrdinaryAtOrigin (P : BPoly) (n : ℕ) : Prop :=
  HasMultiplicityAt P 0 0 n ∧
    ∃ (c : ℂ) (ℓ : Fin n → Fin 2 → ℂ), c ≠ 0 ∧ (∀ i, ℓ i ≠ 0) ∧
      (∀ i j, i ≠ j → ℓ i 0 * ℓ j 1 - ℓ i 1 * ℓ j 0 ≠ 0) ∧
      homogeneousComponent n P = C c * ∏ i, (C (ℓ i 0) * X 0 + C (ℓ i 1) * X 1)

end CurveSymmetry

end

-- lean/RadialAntiForm.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

/-- The coefficients of weight `+m`, `X^(k+m) Y^k`, as a polynomial in `XY`. -/
noncomputable def weightPolynomial (P : BPoly) (m : ℕ) : Polynomial ℂ :=
  ∑ k ∈ P.support.image (fun s => s 1), Polynomial.monomial k (P.coeff (exponent (k + m) k))

/-- The coefficients of weight `-m`, `X^k Y^(k+m)`, as a polynomial in `XY`. -/
noncomputable def oppositeWeightPolynomial (P : BPoly) (m : ℕ) : Polynomial ℂ :=
  ∑ k ∈ P.support.image (fun s => s 0), Polynomial.monomial k (P.coeff (exponent k (k + m)))

end CurveSymmetry

end

-- lean/FamilyFunctionField.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

/-- Coordinate ring of the affine family curve. -/
abbrev FamilyCoordinateRing (m : ℕ) (α : ℂ) : Type :=
  BPoly ⧸ Ideal.span {familyPolynomial m α}

/-- The function field of the family curve. -/
abbrev FamilyFunctionField (m : ℕ) (α : ℂ) : Type :=
  FractionRing (FamilyCoordinateRing m α)

/-- The coordinate functions `X` and `Y` in the function field. -/
noncomputable def familyPoint (m : ℕ) (α : ℂ) (i : Fin 2) : FamilyFunctionField m α :=
  algebraMap (FamilyCoordinateRing m α) (FamilyFunctionField m α)
    (Ideal.Quotient.mk _ (MvPolynomial.X i))

/-- The branch polynomial `h = −t(t^m+1)(α t^m + conj α)`. -/
noncomputable def familyH (m : ℕ) (α : ℂ) : ℂ[X] := -(familyB m * familyA m α)

/-- The defining quadratic `W² − h` over `ℂ(t)`. -/
noncomputable def familyQuadraticRat (m : ℕ) (α : ℂ) : (RatFunc ℂ)[X] :=
  X ^ 2 - C (algebraMap ℂ[X] (RatFunc ℂ) (familyH m α))

variable {m : ℕ} {α : ℂ}

lemma familyPolynomial_ne_zero (hm : 0 < m) (α : ℂ) : familyPolynomial m α ≠ 0 := by
  intro h
  have hd := family_degree hm α
  rw [h, MvPolynomial.totalDegree_zero] at hd
  omega

lemma family_not_dvd_of_degree_le_one (hm : 0 < m) (α : ℂ) {Q : BPoly} (hQ : Q ≠ 0)
    (hdeg : Q.totalDegree ≤ 1) : ¬ familyPolynomial m α ∣ Q := by
  rintro ⟨R, rfl⟩
  have hR : R ≠ 0 := by rintro rfl; exact hQ (mul_zero _)
  have he := MvPolynomial.totalDegree_mul_of_isDomain (familyPolynomial_ne_zero hm α) hR
  rw [family_degree hm] at he
  omega

lemma algebraMap_mk_eq_aeval (p : BPoly) :
    algebraMap (FamilyCoordinateRing m α) (FamilyFunctionField m α)
      (Ideal.Quotient.mk _ p) = MvPolynomial.aeval (familyPoint m α) p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [MvPolynomial.aeval_C, ← MvPolynomial.algebraMap_eq, ← Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p i hp => rw [map_mul, map_mul, hp, map_mul, MvPolynomial.aeval_X]; rfl

lemma familyA_ne_zero_of (hm : 0 < m) (hα : α ≠ 0) : familyA m α ≠ 0 := by
  intro h
  have he := familyA_zero m hm α
  rw [h, coeff_zero] at he
  exact (star_ne_zero.mpr hα) he.symm

lemma familyA_natDegree (hα : α ≠ 0) : (familyA m α).natDegree = m := by
  rw [familyA, natDegree_add_C, natDegree_C_mul_X_pow m α hα]

lemma familyB_natDegree : (familyB m).natDegree = m + 1 := by
  have h1 : (X ^ m + 1 : ℂ[X]).natDegree = m := by
    simpa using natDegree_X_pow_add_C (n := m) (r := (1 : ℂ))
  have h1' : (X ^ m + 1 : ℂ[X]) ≠ 0 := by
    intro h
    have he := congrArg (eval 1) h
    norm_num at he
  rw [familyB, natDegree_mul X_ne_zero h1', natDegree_X, h1, add_comm]

lemma familyH_natDegree_of (hm : 0 < m) (ha : α ≠ star α) :
    (familyH m α).natDegree = 2 * m + 1 := by
  have hα : α ≠ 0 := by intro h; apply ha; simp [h]
  rw [familyH, natDegree_neg, natDegree_mul (familyB_ne_zero m hm) (familyA_ne_zero_of hm hα),
    familyB_natDegree, familyA_natDegree hα]
  ring

instance familyCoordinateRing_isDomain [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)] :
    IsDomain (FamilyCoordinateRing m α) := by
  have : (Ideal.span {familyPolynomial m α}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp
        (familyPolynomial_irreducible hm.out ha.out))
  exact Ideal.Quotient.isDomain _

section FunctionField

variable [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

variable (m α) in
/-- The double-cover parameter `t = X/Y`. -/
noncomputable def familyT : FamilyFunctionField m α :=
  familyPoint m α 0 / familyPoint m α 1

variable (m α) in
/-- The quadratic generator `w = t(t^m+1)Y`. -/
noncomputable def familyW : FamilyFunctionField m α :=
  aeval (familyT m α) (familyB m) * familyPoint m α 1

omit ha in
lemma algebraMap_mk_ne_zero {Q : BPoly} (hQ : Q ≠ 0) (hdeg : Q.totalDegree ≤ 1) :
    MvPolynomial.aeval (familyPoint m α) Q ≠ 0 := by
  rw [← algebraMap_mk_eq_aeval]
  intro h
  have h0 := IsFractionRing.injective (FamilyCoordinateRing m α) (FamilyFunctionField m α)
    (h.trans (map_zero _).symm)
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
  exact family_not_dvd_of_degree_le_one hm.out α hQ hdeg h0

omit ha in
lemma familyPoint_ne_zero (i : Fin 2) : familyPoint m α i ≠ 0 := by
  have h := algebraMap_mk_ne_zero (m := m) (α := α) (MvPolynomial.X_ne_zero i)
    (by rw [MvPolynomial.totalDegree_X])
  rwa [MvPolynomial.aeval_X] at h

omit hm ha in
lemma family_relation :
    familyPoint m α 0 ^ m * (algebraMap ℂ _ α + familyPoint m α 0 * familyPoint m α 1) +
      familyPoint m α 1 ^ m *
        (algebraMap ℂ _ (star α) + familyPoint m α 0 * familyPoint m α 1) = 0 := by
  have h : MvPolynomial.aeval (familyPoint m α) (familyPolynomial m α) = 0 := by
    rw [← algebraMap_mk_eq_aeval, Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _)), map_zero]
  simpa [familyPolynomial] using h

/-- `t` is not a constant: otherwise `X − cY` would be divisible by `P_α`. -/
lemma familyT_ne_algebraMap (c : ℂ) : familyT m α ≠ algebraMap ℂ _ c := by
  intro h
  have hy := familyPoint_ne_zero (m := m) (α := α) 1
  have hx : familyPoint m α 0 = algebraMap ℂ _ c * familyPoint m α 1 := by
    rw [← h, familyT, div_mul_cancel₀ _ hy]
  have hL : (MvPolynomial.X 0 - MvPolynomial.C c * MvPolynomial.X 1 : BPoly) ≠ 0 := by
    intro hz
    have he := congrArg (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0)) hz
    simp at he
  apply algebraMap_mk_ne_zero (m := m) (α := α) hL (linear_degree_le c)
  simp [hx, MvPolynomial.aeval_X]

/-- `t` is transcendental over `ℂ`. -/
lemma familyT_aeval_eq_zero {q : ℂ[X]} (hq : aeval (familyT m α) q = 0) : q = 0 := by
  induction hn : q.natDegree using Nat.strong_induction_on generalizing q with
  | _ n ih =>
    by_contra hq0
    by_cases hd : q.degree = 0
    · have hC := eq_C_of_degree_eq_zero hd
      rw [hC, aeval_C] at hq
      apply hq0
      rw [hC, (algebraMap ℂ (FamilyFunctionField m α)).injective (hq.trans (map_zero _).symm),
        map_zero]
    · obtain ⟨r, hr⟩ := IsAlgClosed.exists_root q hd
      have hfac := mul_divByMonic_eq_iff_isRoot.mpr hr
      rw [← hfac, map_mul] at hq
      rcases mul_eq_zero.mp hq with h1 | h2
      · apply familyT_ne_algebraMap (m := m) (α := α) r
        simpa [sub_eq_zero] using h1
      · have hpos : 0 < q.natDegree :=
          Nat.pos_of_ne_zero fun h0 => hd (by rw [degree_eq_natDegree hq0, h0]; rfl)
        have hdeg : (q /ₘ (X - C r)).natDegree < n := by
          rw [natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C]
          omega
        have hz := ih _ hdeg h2 rfl
        apply hq0
        rw [← hfac, hz, mul_zero]

lemma familyT_aeval_injective : Function.Injective (aeval (R := ℂ) (familyT m α)) :=
  (injective_iff_map_eq_zero _).mpr fun _ h => familyT_aeval_eq_zero h

variable (m α) in
/-- The embedding `ℂ(t) → K` sending the variable to `t = X/Y`. -/
noncomputable def familyRatFuncHom : RatFunc ℂ →ₐ[ℂ] FamilyFunctionField m α :=
  RatFunc.liftAlgHom (aeval (familyT m α))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ familyT_aeval_injective)

lemma familyRatFuncHom_algebraMap (p : ℂ[X]) :
    familyRatFuncHom m α (algebraMap ℂ[X] (RatFunc ℂ) p) = aeval (familyT m α) p := by
  have h := RatFunc.liftAlgHom_apply_div (φ := aeval (familyT m α))
    (hφ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ familyT_aeval_injective) p 1
  simp only [map_one, div_one] at h
  exact h

lemma familyRatFuncHom_X : familyRatFuncHom m α RatFunc.X = familyT m α := by
  have h := familyRatFuncHom_algebraMap (m := m) (α := α) X
  rwa [aeval_X, RatFunc.algebraMap_X] at h

/-- The strict-transform relation `A(t) + B(t) Y² = 0` in the function field. -/
lemma family_quadratic_relation :
    aeval (familyT m α) (familyA m α) +
      aeval (familyT m α) (familyB m) * familyPoint m α 1 ^ 2 = 0 := by
  have hy := familyPoint_ne_zero (m := m) (α := α) 1
  have hx : familyPoint m α 0 = familyT m α * familyPoint m α 1 := by
    rw [familyT, div_mul_cancel₀ _ hy]
  have hrel := family_relation (m := m) (α := α)
  rw [hx] at hrel
  have hfac : familyPoint m α 1 ^ m * (aeval (familyT m α) (familyA m α) +
      aeval (familyT m α) (familyB m) * familyPoint m α 1 ^ 2) = 0 := by
    simp only [familyA, familyB, map_add, map_mul, map_pow, aeval_C, aeval_X, map_one]
    linear_combination hrel
  exact (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero _ hy)

/-- `w² = h(t)`. -/
theorem familyW_sq : familyW m α ^ 2 = aeval (familyT m α) (familyH m α) := by
  have hq := family_quadratic_relation (m := m) (α := α)
  simp only [familyW, familyH, map_neg, map_mul]
  linear_combination aeval (familyT m α) (familyB m) * hq

omit hm ha in
theorem familyH_squarefree_of (hm : 0 < m) (ha : α ≠ star α) : Squarefree (familyH m α) := by
  have hα : α ≠ 0 := by intro h; apply ha; simp [h]
  have hsX : (X : ℂ[X]).Separable := separable_X
  have hsXm : (X ^ m + 1 : ℂ[X]).Separable := by
    have h := separable_X_pow_sub_C (n := m) (-1 : ℂ) (by exact_mod_cast hm.ne') (by norm_num)
    simpa [sub_eq_add_neg] using h
  have hsA : (familyA m α).Separable := binary_tangent_separable hm hα (star_ne_zero.mpr hα)
  have hcop1 : IsCoprime (X : ℂ[X]) (X ^ m + 1) := by
    rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := ℂ) (K := ℂ)]
    intro a
    by_cases h0 : a = 0
    · right; simp [h0, hm.ne']
    · left; simpa using h0
  have hcop2 : IsCoprime (familyB m) (familyA m α) := by
    rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := ℂ) (K := ℂ)]
    intro a
    by_contra h
    push Not at h
    apply family_coefficients_no_common_root hm ha a
    simpa [aeval_def, eval₂_eq_eval_map] using ⟨h.2, h.1⟩
  have hsep : (familyB m * familyA m α).Separable := (hsX.mul hsXm hcop1).mul hsA hcop2
  have hneg : familyH m α = (familyB m * familyA m α) * C (-1) := by
    simp [familyH]
  rw [hneg]
  exact (hsep.mul_unit (isUnit_C.mpr (by norm_num))).squarefree

omit hm ha in
/-- `h` is not a square in `ℂ(t)`: its degree `2m+1` is odd. -/
theorem familyQuadraticRat_irreducible_of (hm : 0 < m) (ha : α ≠ star α) :
    Irreducible (familyQuadraticRat m α) := by
  have hdeg : (familyQuadraticRat m α).natDegree = 2 := by
    rw [familyQuadraticRat, natDegree_X_pow_sub_C]
  rw [irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
  have hne : familyQuadraticRat m α ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hroot := (mem_roots hne).mp hr
  simp only [familyQuadraticRat, IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hroot
  have hd0 := RatFunc.denom_ne_zero r
  have hh0 : familyH m α ≠ 0 := by
    intro h
    have := familyH_natDegree_of hm ha
    rw [h, natDegree_zero] at this
    omega
  have hpoly : r.num ^ 2 = familyH m α * r.denom ^ 2 := by
    apply RatFunc.algebraMap_injective ℂ
    have hnd := RatFunc.num_div_denom r
    have hden : algebraMap ℂ[X] (RatFunc ℂ) r.denom ≠ 0 := RatFunc.algebraMap_ne_zero hd0
    rw [← hnd, div_pow] at hroot
    field_simp at hroot
    simp only [map_pow, map_mul]
    linear_combination hroot
  have hnum0 : r.num ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at hpoly
    exact (mul_ne_zero hh0 (pow_ne_zero 2 hd0)) hpoly.symm
  have hd := congrArg natDegree hpoly
  rw [natDegree_pow, natDegree_mul hh0 (pow_ne_zero 2 hd0), natDegree_pow,
    familyH_natDegree_of hm ha] at hd
  omega

instance familyQuadraticRat_fact : Fact (Irreducible (familyQuadraticRat m α)) :=
  ⟨familyQuadraticRat_irreducible_of hm.out ha.out⟩

lemma familyT_B_ne_zero : aeval (familyT m α) (familyB m) ≠ 0 :=
  fun h => familyB_ne_zero m hm.out (familyT_aeval_eq_zero h)

lemma familyW_eval : (familyQuadraticRat m α).eval₂ (familyRatFuncHom m α).toRingHom
    (familyW m α) = 0 := by
  simp only [familyQuadraticRat, eval₂_sub, eval₂_X_pow, eval₂_C, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, familyRatFuncHom_algebraMap, familyW_sq, sub_self]

variable (m α) in
/-- The comparison map `ℂ(t)[W]/(W² − h) → K`, `W ↦ w`. -/
noncomputable def familyLift : AdjoinRoot (familyQuadraticRat m α) →+* FamilyFunctionField m α :=
  AdjoinRoot.lift (familyRatFuncHom m α).toRingHom (familyW m α) familyW_eval

lemma familyLift_of (r : RatFunc ℂ) :
    familyLift m α (AdjoinRoot.of _ r) = familyRatFuncHom m α r :=
  AdjoinRoot.lift_of familyW_eval

lemma familyLift_root : familyLift m α (AdjoinRoot.root _) = familyW m α :=
  AdjoinRoot.lift_root familyW_eval

lemma familyLift_injective : Function.Injective (familyLift m α) :=
  (familyLift m α).injective

lemma familyLift_surjective : Function.Surjective (familyLift m α) := by
  let L := familyLift m α
  have hdiv {a b : FamilyFunctionField m α} (ha' : a ∈ Set.range L) (hb : b ∈ Set.range L) :
      a / b ∈ Set.range L := by
    obtain ⟨x, rfl⟩ := ha'
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x / y, map_div₀ L x y⟩
  have hmul {a b : FamilyFunctionField m α} (ha' : a ∈ Set.range L) (hb : b ∈ Set.range L) :
      a * b ∈ Set.range L := by
    obtain ⟨x, rfl⟩ := ha'
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x * y, map_mul L x y⟩
  have hadd {a b : FamilyFunctionField m α} (ha' : a ∈ Set.range L) (hb : b ∈ Set.range L) :
      a + b ∈ Set.range L := by
    obtain ⟨x, rfl⟩ := ha'
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x + y, map_add L x y⟩
  have hφ (r : RatFunc ℂ) : familyRatFuncHom m α r ∈ Set.range L :=
    ⟨AdjoinRoot.of _ r, familyLift_of r⟩
  have hw : familyW m α ∈ Set.range L := ⟨AdjoinRoot.root _, familyLift_root⟩
  have hy : familyPoint m α 1 ∈ Set.range L := by
    have he : familyPoint m α 1 = familyW m α / aeval (familyT m α) (familyB m) := by
      rw [familyW, mul_div_cancel_left₀ _ familyT_B_ne_zero]
    rw [he, ← familyRatFuncHom_algebraMap]
    exact hdiv hw (hφ _)
  have hx : familyPoint m α 0 ∈ Set.range L := by
    have he : familyPoint m α 0 = familyT m α * familyPoint m α 1 := by
      rw [familyT, div_mul_cancel₀ _ (familyPoint_ne_zero 1)]
    rw [he, ← familyRatFuncHom_X]
    exact hmul (hφ _) hy
  have hpoly (p : BPoly) : MvPolynomial.aeval (familyPoint m α) p ∈ Set.range L := by
    induction p using MvPolynomial.induction_on with
    | C c =>
        rw [MvPolynomial.aeval_C, ← (familyRatFuncHom m α).commutes]
        exact hφ _
    | add p q hp hq => rw [map_add]; exact hadd hp hq
    | mul_X p i hp =>
        rw [map_mul, MvPolynomial.aeval_X]
        refine hmul hp ?_
        fin_cases i
        · exact hx
        · exact hy
  intro z
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := FamilyCoordinateRing m α) z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [algebraMap_mk_eq_aeval, algebraMap_mk_eq_aeval]
  exact hdiv (hpoly p) (hpoly q)

end FunctionField

end CurveSymmetry

end


