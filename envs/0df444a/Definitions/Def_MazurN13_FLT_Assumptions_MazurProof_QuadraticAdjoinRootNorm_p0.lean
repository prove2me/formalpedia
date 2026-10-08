-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_QuadraticAdjoinRootNorm_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_QuadraticAdjoinRootNorm_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:21:40.383974+00:00
-- url     : https://prove2.me/theorems/4fa9b383-1e08-4442-a6cc-79dec50796d0
-- title:
--   FLT.Assumptions.MazurProof.QuadraticAdjoinRootNorm source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.QuadraticAdjoinRootNorm

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.QuadraticAdjoinRootNorm
Original leading source comments and nonproject imports are retained below. -/
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

set_option autoImplicit false




/-!
# Norms in monic quadratic polynomial quotients

For a monic quadratic `u`, multiplication by the class of `x + yX` has
matrix

```
!![x, -u.coeff 0 * y; y, x - u.coeff 1 * y].
```

Its determinant is the fixed-degree resultant of `u` and `x + yX`.
Reducing a cubic representative modulo `u` then identifies its algebra norm
with the resultant padded to formal degrees `(2, 3)`.  This gives a
root-free bridge between quadratic quotient algebras and the fixed-degree
resultants used by Padé identities.
-/

namespace MazurProof.QuadraticAdjoinRootNorm

noncomputable section

open Polynomial

variable {K : Type*} [Field K]

private def quad (a b : K) : K[X] :=
  X ^ 2 + C b * X + C a

private theorem quad_monic (a b : K) :
    (quad a b).Monic :=
  (isMonicOfDegree_add_add_two b a).monic

private theorem quad_natDegree (a b : K) :
    (quad a b).natDegree = 2 :=
  (isMonicOfDegree_add_add_two b a).natDegree_eq

private def linearPoly (x y : K) : K[X] :=
  C x + C y * X

private theorem norm_mk_linear (a b x y : K) :
    Algebra.norm K
        (AdjoinRoot.mk (quad a b) (linearPoly x y)) =
      x ^ 2 - b * x * y + a * y ^ 2 := by
  let hu : (quad a b).Monic := quad_monic a b
  let e : Fin (quad a b).natDegree ≃ Fin 2 :=
    finCongr (quad_natDegree a b)
  let basis :
      Module.Basis (Fin 2) K (AdjoinRoot (quad a b)) :=
    (AdjoinRoot.powerBasisAux' hu).reindex e
  have hb0 : basis (0 : Fin 2) = 1 := by
    dsimp only [basis]
    rw [Module.Basis.reindex_apply]
    change
      (AdjoinRoot.powerBasis' hu).basis (e.symm 0) = 1
    calc
      _ = (AdjoinRoot.powerBasis' hu).gen ^ (e.symm 0).val :=
        (AdjoinRoot.powerBasis' hu).basis_eq_pow _
      _ = 1 := by
        change (AdjoinRoot.root (quad a b)) ^ (0 : ℕ) = 1
        exact pow_zero _
  have hb1 :
      basis (1 : Fin 2) = AdjoinRoot.root (quad a b) := by
    dsimp only [basis]
    rw [Module.Basis.reindex_apply]
    change
      (AdjoinRoot.powerBasis' hu).basis (e.symm 1) =
        AdjoinRoot.root (quad a b)
    calc
      _ = (AdjoinRoot.powerBasis' hu).gen ^ (e.symm 1).val :=
        (AdjoinRoot.powerBasis' hu).basis_eq_pow _
      _ = AdjoinRoot.root (quad a b) := by
        change (AdjoinRoot.root (quad a b)) ^ (1 : ℕ) = _
        exact pow_one _
  have hrepr (z : AdjoinRoot (quad a b)) (i : Fin 2) :
      basis.repr z i =
        (AdjoinRoot.modByMonicHom hu z).coeff i.val := by
    dsimp only [basis]
    rw [Module.Basis.repr_reindex_apply,
      AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
    congr 1
  have hrem0 :
      linearPoly x y %ₘ quad a b = linearPoly x y := by
    apply (modByMonic_eq_self_iff hu).mpr
    have hdegree :
        (quad a b).degree = (2 : WithBot ℕ) := by
      rw [degree_eq_natDegree (quad_monic a b).ne_zero,
        quad_natDegree]
      norm_num
    rw [hdegree]
    change
      (linearPoly x y).degree <
        ((2 : ℕ) : WithBot ℕ)
    rw [degree_lt_iff_coeff_zero]
    intro n hn
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    simp only [linearPoly, coeff_add,
      coeff_C_of_ne_zero hn0, coeff_C_mul_X,
      if_neg hn1, add_zero]
  have hrem1 :
      (linearPoly x y * X) %ₘ quad a b =
        C (-a * y) + C (x - b * y) * X := by
    let r : K[X] :=
      C (-a * y) + C (x - b * y) * X
    have hcongr :
        (linearPoly x y * X) %ₘ quad a b =
          r %ₘ quad a b := by
      apply modByMonic_eq_of_dvd_sub hu
      refine ⟨C y, ?_⟩
      dsimp only [r]
      simp only [quad, linearPoly,
        map_sub, map_mul, map_neg]
      ring
    rw [hcongr]
    apply (modByMonic_eq_self_iff hu).mpr
    have hdegree :
        (quad a b).degree = (2 : WithBot ℕ) := by
      rw [degree_eq_natDegree (quad_monic a b).ne_zero,
        quad_natDegree]
      norm_num
    rw [hdegree]
    change r.degree < ((2 : ℕ) : WithBot ℕ)
    rw [degree_lt_iff_coeff_zero]
    intro n hn
    dsimp only [r]
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    simp only [coeff_add,
      coeff_C_of_ne_zero hn0, coeff_C_mul_X,
      if_neg hn1, add_zero]
  have hmulRoot :
      AdjoinRoot.mk (quad a b) (linearPoly x y) *
          AdjoinRoot.root (quad a b) =
        AdjoinRoot.mk (quad a b) (linearPoly x y * X) := by
    rw [AdjoinRoot.root, map_mul]
  have hmatrix :
      Algebra.leftMulMatrix basis
          (AdjoinRoot.mk (quad a b) (linearPoly x y)) =
        !![x, -a * y; y, x - b * y] := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      rw [Algebra.leftMulMatrix_eq_repr_mul, hrepr]
    · rw [show basis _ = 1 by simpa using hb0,
        mul_one, AdjoinRoot.modByMonicHom_mk, hrem0]
      simp [linearPoly]
    · rw [show basis _ = AdjoinRoot.root (quad a b) by
          simpa using hb1,
        hmulRoot, AdjoinRoot.modByMonicHom_mk, hrem1]
      simp
    · rw [show basis _ = 1 by simpa using hb0,
        mul_one, AdjoinRoot.modByMonicHom_mk, hrem0]
      simp [linearPoly]
    · rw [show basis _ = AdjoinRoot.root (quad a b) by
          simpa using hb1,
        hmulRoot, AdjoinRoot.modByMonicHom_mk, hrem1]
      simp
  rw [Algebra.norm_eq_matrix_det basis, hmatrix]
  rw [Matrix.det_fin_two]
  simp
  ring

private theorem resultant_quad_linear (a b x y : K) :
    Polynomial.resultant
        (quad a b) (linearPoly x y) 2 1 =
      x ^ 2 - b * x * y + a * y ^ 2 := by
  rw [Polynomial.resultant]
  rw [Matrix.det_fin_three]
  simp [Polynomial.sylvester, quad, linearPoly,
    Fin.addCases]
  norm_num [coeff_X]
  ring

/-- In a monic quadratic quotient, the algebra norm of a linear
representative is its fixed-degree resultant. -/
theorem norm_mk_eq_resultant_fixed_one
    (u p : K[X]) (hu : u.Monic)
    (hu2 : u.natDegree = 2)
    (hp : p.natDegree ≤ 1) :
    Algebra.norm K (AdjoinRoot.mk u p) =
      Polynomial.resultant u p 2 1 := by
  have huDegree : IsMonicOfDegree u 2 :=
    ⟨hu2, hu⟩
  obtain ⟨b, a, rfl⟩ :=
    isMonicOfDegree_two_iff.mp huDegree
  have hpShape :
      p = linearPoly (p.coeff 0) (p.coeff 1) := by
    calc
      p = C (p.coeff 1) * X + C (p.coeff 0) :=
        eq_X_add_C_of_natDegree_le_one hp
      _ = linearPoly (p.coeff 0) (p.coeff 1) := by
        simp only [linearPoly]
        ring
  rw [hpShape]
  calc
    Algebra.norm K
          (AdjoinRoot.mk
            (X ^ 2 + C b * X + C a)
            (linearPoly (p.coeff 0) (p.coeff 1))) =
        (p.coeff 0) ^ 2 -
          b * (p.coeff 0) * (p.coeff 1) +
          a * (p.coeff 1) ^ 2 := by
      convert
        norm_mk_linear a b (p.coeff 0) (p.coeff 1)
          using 1 <;> rfl
    _ =
        Polynomial.resultant
          (X ^ 2 + C b * X + C a)
          (linearPoly (p.coeff 0) (p.coeff 1)) 2 1 := by
      symm
      convert
        resultant_quad_linear a b (p.coeff 0) (p.coeff 1)
          using 1 <;> rfl

/-- A cubic representative may be reduced modulo the monic quadratic
without changing either the quotient element or the resultant padded to
formal second degree three. -/
theorem norm_mk_eq_resultant_fixed_three
    (u p : K[X]) (hu : u.Monic)
    (hu2 : u.natDegree = 2)
    (hp : p.natDegree ≤ 3) :
    Algebra.norm K (AdjoinRoot.mk u p) =
      Polynomial.resultant u p 2 3 := by
  let r : K[X] := p %ₘ u
  let d : K[X] := p /ₘ u
  have huNeOne : u ≠ 1 := by
    intro h
    rw [h, natDegree_one] at hu2
    omega
  have hr : r.natDegree ≤ 1 := by
    have hlt := natDegree_modByMonic_lt p hu huNeOne
    dsimp only [r]
    rw [hu2] at hlt
    omega
  have hd : d.natDegree + 2 ≤ 3 := by
    dsimp only [d]
    rw [natDegree_divByMonic p hu, hu2]
    omega
  have huLe : u.natDegree ≤ 2 := hu2.le
  have hdecomp : r + u * d = p :=
    modByMonic_add_div p u
  have hmk :
      AdjoinRoot.mk u r = AdjoinRoot.mk u p := by
    simpa only [r, AdjoinRoot.modByMonicHom_mk] using
      AdjoinRoot.mk_leftInverse hu (AdjoinRoot.mk u p)
  have hcoeff : u.coeff 2 = 1 := by
    simpa only [hu2] using hu.coeff_natDegree
  have hresReduce :
      Polynomial.resultant u p 2 3 =
        Polynomial.resultant u r 2 1 := by
    calc
      Polynomial.resultant u p 2 3 =
          Polynomial.resultant u (r + u * d) 2 3 := by
        rw [hdecomp]
      _ = Polynomial.resultant u r 2 3 :=
        resultant_add_mul_right u r d 2 3 hd huLe
      _ = Polynomial.resultant u r 2 1 := by
        have hpad :=
          resultant_add_right_deg u r 2 1 2 hr
        simpa only [Nat.reduceAdd, hcoeff, one_pow,
          one_mul] using hpad
  calc
    Algebra.norm K (AdjoinRoot.mk u p) =
        Algebra.norm K (AdjoinRoot.mk u r) := by
      rw [hmk]
    _ = Polynomial.resultant u r 2 1 :=
      norm_mk_eq_resultant_fixed_one u r hu hu2 hr
    _ = Polynomial.resultant u p 2 3 :=
      hresReduce.symm

/-- For a reduced representative, the default resultant has the same
formal degrees as the quadratic quotient norm, including the constant
representative case. -/
theorem norm_mk_eq_resultant
    (u p : K[X]) (hu : u.Monic)
    (hu2 : u.natDegree = 2)
    (hp : p.natDegree ≤ 1) :
    Algebra.norm K (AdjoinRoot.mk u p) =
      Polynomial.resultant u p := by
  change
    Algebra.norm K (AdjoinRoot.mk u p) =
      Polynomial.resultant u p u.natDegree p.natDegree
  rw [hu2]
  have hcoeff : u.coeff 2 = 1 := by
    simpa only [hu2] using hu.coeff_natDegree
  have hpad :=
    resultant_add_right_deg
      u p 2 p.natDegree (1 - p.natDegree) le_rfl
  have hadd :
      p.natDegree + (1 - p.natDegree) = 1 := by
    omega
  rw [hadd, hcoeff, one_pow, one_mul] at hpad
  rw [← hpad]
  exact norm_mk_eq_resultant_fixed_one u p hu hu2 hp

/-- A polynomial coprime to the modulus represents a unit in the
polynomial quotient. -/
theorem isUnit_mk_of_isCoprime
    (u p : K[X]) (hcop : IsCoprime u p) :
    IsUnit (AdjoinRoot.mk u p) := by
  obtain ⟨a, b, hab⟩ := hcop
  apply IsUnit.of_mul_eq_one (AdjoinRoot.mk u b)
  calc
    AdjoinRoot.mk u p * AdjoinRoot.mk u b =
        AdjoinRoot.mk u (p * b) := by
      rw [map_mul]
    _ = AdjoinRoot.mk u (a * u + b * p) := by
      rw [map_add, map_mul, map_mul,
        AdjoinRoot.mk_self]
      simp [mul_comm]
    _ = AdjoinRoot.mk u 1 := by
      rw [hab]
    _ = 1 := map_one (AdjoinRoot.mk u)

/-- A nonzero resultant is enough to produce the quotient unit. -/
theorem isUnit_mk_of_resultant_ne_zero
    (u p : K[X]) (hu : u ≠ 0)
    (hres : Polynomial.resultant u p ≠ 0) :
    IsUnit (AdjoinRoot.mk u p) := by
  apply isUnit_mk_of_isCoprime
  by_contra hcop
  apply hres
  exact Polynomial.resultant_eq_zero_iff.mpr
    ⟨Or.inl hu, hcop⟩

/-- The norm of the quotient of a cubic numerator by a reduced denominator
is the corresponding ratio of resultants.  The denominator is packaged as
an actual unit, so this remains valid when the quadratic quotient is not a
domain. -/
theorem exists_mk_unit_norm_mul_inv
    (u l v : K[X]) (hu : u.Monic)
    (hu2 : u.natDegree = 2)
    (hl : l.natDegree ≤ 3)
    (hv : v.natDegree ≤ 1)
    (hres : Polynomial.resultant u v ≠ 0) :
    ∃ V : (AdjoinRoot u)ˣ,
      (V : AdjoinRoot u) = AdjoinRoot.mk u v ∧
      Algebra.norm K
          (AdjoinRoot.mk u l *
            ((V⁻¹ : (AdjoinRoot u)ˣ) : AdjoinRoot u)) =
        Polynomial.resultant u l 2 3 /
          Polynomial.resultant u v := by
  have hvUnit :
      IsUnit (AdjoinRoot.mk u v) :=
    isUnit_mk_of_resultant_ne_zero
      u v hu.ne_zero hres
  let V : (AdjoinRoot u)ˣ := hvUnit.unit
  have hV :
      (V : AdjoinRoot u) = AdjoinRoot.mk u v :=
    hvUnit.unit_spec
  refine ⟨V, hV, ?_⟩
  have hnormL :
      Algebra.norm K (AdjoinRoot.mk u l) =
        Polynomial.resultant u l 2 3 :=
    norm_mk_eq_resultant_fixed_three
      u l hu hu2 hl
  have hnormV :
      Algebra.norm K (V : AdjoinRoot u) =
        Polynomial.resultant u v := by
    rw [hV]
    exact norm_mk_eq_resultant u v hu hu2 hv
  have hnormInv :
      Algebra.norm K
          ((V⁻¹ : (AdjoinRoot u)ˣ) : AdjoinRoot u) =
        (Polynomial.resultant u v)⁻¹ := by
    calc
      Algebra.norm K
            ((V⁻¹ : (AdjoinRoot u)ˣ) : AdjoinRoot u) =
          (((Units.map (Algebra.norm K) V)⁻¹ : Kˣ) : K) := by
            exact
              (Units.coe_map_inv
                (Algebra.norm K) V).symm
      _ = (Algebra.norm K (V : AdjoinRoot u))⁻¹ := by
        rw [Units.val_inv_eq_inv_val, Units.coe_map]
      _ = (Polynomial.resultant u v)⁻¹ := by
        rw [hnormV]
  rw [map_mul, hnormL, hnormInv, div_eq_mul_inv]

end

end MazurProof.QuadraticAdjoinRootNorm


