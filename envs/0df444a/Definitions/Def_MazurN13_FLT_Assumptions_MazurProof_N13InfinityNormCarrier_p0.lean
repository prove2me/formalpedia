-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityNormCarrier_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13InfinityNormCarrier_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:33:39.52129+00:00
-- url     : https://prove2.me/theorems/21216b3b-bb39-49ef-bfef-7dcf65b5e6ab
-- title:
--   FLT.Assumptions.MazurProof.N13InfinityNormCarrier source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13InfinityNormCarrier

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13InfinityNormCarrier
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GeneralizedMumfordIntegral_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13QuotientFiniteness_p0
import Mathlib.Algebra.Polynomial.Reverse

set_option autoImplicit false




/-!
# The explicit N13 norm carrier at infinity

For the integral N13 equation

`y² + h(x)y = r(x)`,

the hyperelliptic conjugate of `P(x) + Q(x)y` is
`P(x) - Q(x)h(x) - Q(x)y`.  Their product is the polynomial

`P² - hPQ - rQ²`

evaluated at `x`.  Thus one affine ideal section whose two normalized
infinity branches are units can later be converted into a monic polynomial
contained in the ideal by inspecting the leading coefficient of this norm.

This file records the equation-level algebra only.  It makes no properness,
Mumford-graph, or branch-unit assumption.
-/

open Polynomial

namespace MazurProof.N13InfinityNormCarrier

noncomputable section

universe u

variable {R : Type u} [CommRing R]

abbrev CoordinateRing : Type u :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := R)

/-- The polynomial norm of the affine normal form `P(x)+Q(x)y`. -/
def normPoly (P Q : R[X]) : R[X] :=
  P ^ 2 -
    N13GeneralizedMumfordIntegral.hPoly * P * Q -
      N13GeneralizedMumfordIntegral.rhsPoly * Q ^ 2

/-- The affine normal form `P(x)+Q(x)y`. -/
def normalElement (P Q : R[X]) : CoordinateRing (R := R) :=
  N13GeneralizedMumfordIntegral.xClass P +
    N13GeneralizedMumfordIntegral.xClass Q *
      N13GeneralizedMumfordIntegral.yClass

/-- Its image under hyperelliptic conjugation. -/
def conjugateElement (P Q : R[X]) : CoordinateRing (R := R) :=
  N13GeneralizedMumfordIntegral.xClass P -
    N13GeneralizedMumfordIntegral.xClass
        (Q * N13GeneralizedMumfordIntegral.hPoly) -
      N13GeneralizedMumfordIntegral.xClass Q *
        N13GeneralizedMumfordIntegral.yClass

/-- The explicit quadratic norm identity in the integral coordinate ring. -/
theorem xClass_normPoly
    (P Q : R[X]) :
    N13GeneralizedMumfordIntegral.xClass (normPoly P Q) =
      normalElement P Q * conjugateElement P Q := by
  rw [show
    N13GeneralizedMumfordIntegral.xClass (normPoly P Q) =
      N13GeneralizedMumfordIntegral.xClass P ^ 2 -
        N13GeneralizedMumfordIntegral.xClass
            N13GeneralizedMumfordIntegral.hPoly *
          N13GeneralizedMumfordIntegral.xClass P *
          N13GeneralizedMumfordIntegral.xClass Q -
        N13GeneralizedMumfordIntegral.xClass
            N13GeneralizedMumfordIntegral.rhsPoly *
          N13GeneralizedMumfordIntegral.xClass Q ^ 2 by
      simp only [normPoly,
        N13GeneralizedMumfordIntegral.xClass_sub,
        N13GeneralizedMumfordIntegral.xClass_mul,
        N13GeneralizedMumfordIntegral.xClass_pow]]
  rw [← N13GeneralizedMumfordIntegral.yClass_relation]
  simp only [normalElement, conjugateElement,
    N13GeneralizedMumfordIntegral.xClass_mul]
  ring

/-- The norm of an affine ideal element remains in the same ideal. -/
theorem xClass_normPoly_mem
    (I : Ideal (CoordinateRing (R := R)))
    (P Q : R[X])
    (hPQ : normalElement P Q ∈ I) :
    N13GeneralizedMumfordIntegral.xClass (normPoly P Q) ∈ I := by
  rw [xClass_normPoly]
  exact I.mul_mem_right _ hPQ

theorem hPoly_natDegree [Nontrivial R] :
    (N13GeneralizedMumfordIntegral.hPoly :
      R[X]).natDegree = 3 := by
  unfold N13GeneralizedMumfordIntegral.hPoly
  compute_degree
  all_goals norm_num

theorem rhsPoly_natDegree [Nontrivial R] :
    (N13GeneralizedMumfordIntegral.rhsPoly :
      R[X]).natDegree = 5 := by
  unfold N13GeneralizedMumfordIntegral.rhsPoly
  compute_degree
  all_goals norm_num

/-- Weighted degree bound for the explicit norm. -/
theorem normPoly_natDegree_le
    [Nontrivial R]
    {N : ℕ} (hN : 3 ≤ N)
    {P Q : R[X]}
    (hP : P.natDegree ≤ N)
    (hQ : Q.natDegree ≤ N - 3) :
    (normPoly P Q).natDegree ≤ 2 * N := by
  have hh :
      (N13GeneralizedMumfordIntegral.hPoly :
        R[X]).natDegree ≤ 3 := by
    rw [hPoly_natDegree]
  have hr :
      (N13GeneralizedMumfordIntegral.rhsPoly :
        R[X]).natDegree ≤ 5 := by
    rw [rhsPoly_natDegree]
  have hP2 : (P ^ 2).natDegree ≤ 2 * N := by
    exact Polynomial.natDegree_pow_le.trans
      (Nat.mul_le_mul_left 2 hP)
  have hHPQ :
      (N13GeneralizedMumfordIntegral.hPoly * P * Q).natDegree ≤
        2 * N := by
    refine Polynomial.natDegree_mul_le.trans ?_
    have hHP :=
      Nat.add_le_add
        (Polynomial.natDegree_mul_le.trans
          (Nat.add_le_add hh hP))
        hQ
    omega
  have hRQ2 :
      (N13GeneralizedMumfordIntegral.rhsPoly * Q ^ 2).natDegree ≤
        2 * N := by
    refine Polynomial.natDegree_mul_le.trans ?_
    have hQ2 :=
      Polynomial.natDegree_pow_le.trans
        (Nat.mul_le_mul_left 2 hQ)
    have hsum := Nat.add_le_add hr hQ2
    omega
  unfold normPoly
  refine (Polynomial.natDegree_sub_le _ _).trans ?_
  rw [max_le_iff]
  constructor
  · refine (Polynomial.natDegree_sub_le _ _).trans ?_
    rw [max_le_iff]
    exact ⟨hP2, hHPQ⟩
  · exact hRQ2

/--
At the weighted pole bound `deg P ≤ N`, `deg Q ≤ N-3`, the coefficient of
degree `2N` in the norm is the product of the two normalized branch
constants.  Reflection turns this into a constant-coefficient calculation,
so the proof does not expand coefficient convolutions.
-/
theorem normPoly_coeff_two_mul
    [Nontrivial R]
    {N : ℕ} (hN : 3 ≤ N)
    {P Q : R[X]}
    (hP : P.natDegree ≤ N)
    (hQ : Q.natDegree ≤ N - 3) :
    (normPoly P Q).coeff (2 * N) =
      P.coeff N * (P.coeff N - Q.coeff (N - 3)) := by
  have hh :
      (N13GeneralizedMumfordIntegral.hPoly :
        R[X]).natDegree ≤ 3 := by
    rw [hPoly_natDegree]
  have hr :
      (N13GeneralizedMumfordIntegral.rhsPoly :
        R[X]).natDegree ≤ 6 := by
    rw [rhsPoly_natDegree]
    omega
  have hhP :
      (N13GeneralizedMumfordIntegral.hPoly * P).natDegree ≤
        3 + N :=
    Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add hh hP)
  have hQQ :
      (Q ^ 2).natDegree ≤
        (N - 3) + (N - 3) := by
    rw [pow_two]
    exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add hQ hQ)
  have hrefP :
      (P ^ 2).reflect (2 * N) =
        P.reflect N * P.reflect N := by
    simpa [pow_two, two_mul] using
      (Polynomial.reflect_mul P P hP hP)
  have hrefHPQ :
      (N13GeneralizedMumfordIntegral.hPoly * P * Q).reflect
          (2 * N) =
        N13GeneralizedMumfordIntegral.hPoly.reflect 3 *
          P.reflect N * Q.reflect (N - 3) := by
    calc
      (N13GeneralizedMumfordIntegral.hPoly * P * Q).reflect
          (2 * N) =
          (N13GeneralizedMumfordIntegral.hPoly * P * Q).reflect
            ((3 + N) + (N - 3)) := by
              congr 2
              omega
      _ =
          (N13GeneralizedMumfordIntegral.hPoly * P).reflect
              (3 + N) *
            Q.reflect (N - 3) :=
        Polynomial.reflect_mul
          (N13GeneralizedMumfordIntegral.hPoly * P) Q hhP hQ
      _ =
          N13GeneralizedMumfordIntegral.hPoly.reflect 3 *
              P.reflect N *
            Q.reflect (N - 3) := by
        rw [Polynomial.reflect_mul
          N13GeneralizedMumfordIntegral.hPoly P hh hP]
  have hrefRQQ :
      (N13GeneralizedMumfordIntegral.rhsPoly * Q ^ 2).reflect
          (2 * N) =
        N13GeneralizedMumfordIntegral.rhsPoly.reflect 6 *
          (Q.reflect (N - 3) * Q.reflect (N - 3)) := by
    calc
      (N13GeneralizedMumfordIntegral.rhsPoly * Q ^ 2).reflect
          (2 * N) =
          (N13GeneralizedMumfordIntegral.rhsPoly * Q ^ 2).reflect
            (6 + ((N - 3) + (N - 3))) := by
              congr 2
              omega
      _ =
          N13GeneralizedMumfordIntegral.rhsPoly.reflect 6 *
            (Q ^ 2).reflect ((N - 3) + (N - 3)) :=
        Polynomial.reflect_mul
          N13GeneralizedMumfordIntegral.rhsPoly (Q ^ 2) hr hQQ
      _ =
          N13GeneralizedMumfordIntegral.rhsPoly.reflect 6 *
            (Q.reflect (N - 3) * Q.reflect (N - 3)) := by
        rw [show Q ^ 2 = Q * Q by ring,
          Polynomial.reflect_mul Q Q hQ hQ]
  have href :
      (normPoly P Q).reflect (2 * N) =
        P.reflect N * P.reflect N -
          (N13GeneralizedMumfordIntegral.hPoly.reflect 3 *
            P.reflect N * Q.reflect (N - 3)) -
          N13GeneralizedMumfordIntegral.rhsPoly.reflect 6 *
            (Q.reflect (N - 3) * Q.reflect (N - 3)) := by
    simp only [normPoly, Polynomial.reflect_sub]
    rw [hrefP, hrefHPQ, hrefRQQ]
  have hc :=
    congrArg (fun f : R[X] => f.coeff 0) href
  have hX3 : (X : R[X]).coeff 3 = 0 := by
    rw [Polynomial.coeff_X]
    norm_num
  have hc' :
      (normPoly P Q).coeff (2 * N) =
        P.coeff N * P.coeff N -
          P.coeff N * Q.coeff (N - 3) := by
    simpa [Polynomial.mul_coeff_zero,
      N13GeneralizedMumfordIntegral.hPoly,
      N13GeneralizedMumfordIntegral.rhsPoly, hX3] using hc
  calc
    (normPoly P Q).coeff (2 * N) =
        P.coeff N * P.coeff N -
          P.coeff N * Q.coeff (N - 3) := hc'
    _ = P.coeff N * (P.coeff N - Q.coeff (N - 3)) := by
      ring

/--
Two unit normalized branch constants manufacture a monic norm polynomial
whose evaluation remains in the affine ideal.
-/
theorem exists_monic_norm_carrier
    [Nontrivial R]
    (I : Ideal (CoordinateRing (R := R)))
    {N : ℕ} (hN : 3 ≤ N)
    (P Q : R[X])
    (hP : P.natDegree ≤ N)
    (hQ : Q.natDegree ≤ N - 3)
    (hPQ : normalElement P Q ∈ I)
    (h0 : IsUnit (P.coeff N))
    (h1 : IsUnit (P.coeff N - Q.coeff (N - 3))) :
    ∃ m : R[X],
      m.Monic ∧
      m.natDegree = 2 * N ∧
      N13GeneralizedMumfordIntegral.xClass m ∈ I := by
  let f : R[X] := normPoly P Q
  have hfCoeff :
      f.coeff (2 * N) =
        P.coeff N * (P.coeff N - Q.coeff (N - 3)) := by
    exact normPoly_coeff_two_mul hN hP hQ
  have hfUnit : IsUnit (f.coeff (2 * N)) := by
    rw [hfCoeff]
    exact h0.mul h1
  have hfDegree : f.natDegree = 2 * N := by
    apply le_antisymm
    · exact normPoly_natDegree_le hN hP hQ
    · exact Polynomial.le_natDegree_of_ne_zero hfUnit.ne_zero
  let c : Rˣ := hfUnit.unit
  let m : R[X] := C ((c⁻¹ : Rˣ) : R) * f
  refine ⟨m, ?_, ?_, ?_⟩
  · change (C ((c⁻¹ : Rˣ) : R) * f).Monic
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    have hlead : f.leadingCoeff = (c : R) := by
      calc
        f.leadingCoeff = f.coeff f.natDegree :=
          Polynomial.coeff_natDegree.symm
        _ = f.coeff (2 * N) := by rw [hfDegree]
        _ = (c : R) := hfUnit.unit_spec.symm
    rw [hlead]
    exact Units.inv_mul c
  · rw [show m = C ((c⁻¹ : Rˣ) : R) * f by rfl,
      Polynomial.natDegree_C_mul_of_isUnit (c⁻¹).isUnit f,
      hfDegree]
  · change
      N13GeneralizedMumfordIntegral.xClass
          (C ((c⁻¹ : Rˣ) : R) * f) ∈ I
    rw [N13GeneralizedMumfordIntegral.xClass_mul]
    exact I.mul_mem_left _
      (by
        change
          N13GeneralizedMumfordIntegral.xClass
              (normPoly P Q) ∈ I
        exact xClass_normPoly_mem I P Q hPQ)

/-- Polynomial evaluation at the affine coordinate agrees with `xClass`. -/
theorem aeval_xCoordinate
    (p : R[X]) :
    aeval
        (N13GeneralizedMumfordIntegral.xClass (X : R[X])) p =
      N13GeneralizedMumfordIntegral.xClass p := by
  let ψ : R[X] →ₐ[R] CoordinateRing (R := R) :=
    IsScalarTower.toAlgHom R R[X] (CoordinateRing (R := R))
  have h :
      aeval
          (N13GeneralizedMumfordIntegral.xClass (X : R[X])) =
        ψ := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    rfl
  calc
    aeval
        (N13GeneralizedMumfordIntegral.xClass (X : R[X])) p =
        ψ p := DFunLike.congr_fun h p
    _ = N13GeneralizedMumfordIntegral.xClass p := rfl

/-- The actual N13 affine coordinate ring has the generic rank-two
polynomial normal form used by the finiteness theorem. -/
theorem rankTwoPolynomialNormalForm
    [Nontrivial R] :
    ∀ z : CoordinateRing (R := R),
      ∃ P Q : R[X],
        z =
          aeval
              (N13GeneralizedMumfordIntegral.xClass (X : R[X])) P +
            aeval
                (N13GeneralizedMumfordIntegral.xClass (X : R[X])) Q *
              N13GeneralizedMumfordIntegral.yClass := by
  intro z
  refine ⟨
    N13GeneralizedMumfordIntegral.coeff0 z,
    N13GeneralizedMumfordIntegral.coeffY z,
    ?_⟩
  rw [aeval_xCoordinate, aeval_xCoordinate]
  exact (N13GeneralizedMumfordIntegral.recompose z).symm

/-- One monic `xClass` relation in an ideal makes the actual N13 affine
quotient finite over the base ring. -/
theorem quotient_finite_of_monic_xClass_mem
    [Nontrivial R]
    (I : Ideal (CoordinateRing (R := R)))
    {m : R[X]}
    (hm : m.Monic)
    (hmI : N13GeneralizedMumfordIntegral.xClass m ∈ I) :
    Module.Finite R (CoordinateRing (R := R) ⧸ I) := by
  apply
    MazurProof.N13QuotientFiniteness.quotient_finite_of_monic_relation_of_rankTwoNormalForm
        (N13GeneralizedMumfordIntegral.xClass (X : R[X]))
        N13GeneralizedMumfordIntegral.yClass
        rankTwoPolynomialNormalForm I hm
  rwa [aeval_xCoordinate]

/--
The complete algebraic no-escape endpoint: a bounded affine ideal section
whose two normalized branch constants are units makes the affine quotient
finite.
-/
theorem quotient_finite_of_two_branch_constants
    [Nontrivial R]
    (I : Ideal (CoordinateRing (R := R)))
    {N : ℕ} (hN : 3 ≤ N)
    (P Q : R[X])
    (hP : P.natDegree ≤ N)
    (hQ : Q.natDegree ≤ N - 3)
    (hPQ : normalElement P Q ∈ I)
    (h0 : IsUnit (P.coeff N))
    (h1 : IsUnit (P.coeff N - Q.coeff (N - 3))) :
    Module.Finite R (CoordinateRing (R := R) ⧸ I) := by
  obtain ⟨m, hm, _, hmI⟩ :=
    exists_monic_norm_carrier I hN P Q hP hQ hPQ h0 h1
  exact quotient_finite_of_monic_xClass_mem I hm hmI

end

end MazurProof.N13InfinityNormCarrier


