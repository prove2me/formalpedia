-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_PowerBasisDiscriminant_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_PowerBasisDiscriminant_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:46:31.261355+00:00
-- url     : https://prove2.me/theorems/42f1d720-8810-4ccc-aaf9-792ce1a0c8af
-- title:
--   FLT.Assumptions.MazurProof.PowerBasisDiscriminant source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.PowerBasisDiscriminant

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.PowerBasisDiscriminant
Original leading source comments and nonproject imports are retained below. -/
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Polynomial.Resultant.Basic

set_option autoImplicit false




/-!
# Structural discriminant identities for power bases

This file supplies two small bridges missing from Mathlib's public API:

* the norm of `q(θ)` is the resultant of the minimal polynomial of `θ`
  with `q`;
* the trace discriminant of a power basis is the polynomial discriminant
  of its minimal polynomial.

The norm proof reindexes the canonical product over embeddings by the
canonical multiset of roots.  It does not choose or enumerate roots and it
does not expand a multiplication matrix.
-/

open Polynomial
open scoped Polynomial BigOperators

namespace MazurProof.PowerBasisDiscriminant

noncomputable section

/-- The norm of a polynomial in a power-basis generator is the resultant
with the generator's minimal polynomial. -/
theorem norm_aeval_eq_resultant
    {K L : Type*}
    [Field K] [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (B : PowerBasis K L)
    (q : K[X]) :
    Algebra.norm K (Polynomial.aeval B.gen q) =
      (minpoly K B.gen).resultant q := by
  let E := AlgebraicClosure L
  letI := Classical.decEq E

  have hres :
      algebraMap K E ((minpoly K B.gen).resultant q) =
        (((minpoly K B.gen).aroots E).map
          (fun y => Polynomial.aeval y q)).prod := by
    rw [← Polynomial.resultant_map_map
      (f := minpoly K B.gen)
      (g := q)
      (m := (minpoly K B.gen).natDegree)
      (n := q.natDegree)
      (algebraMap K E)]
    have hr :=
      Polynomial.resultant_eq_prod_eval
        ((minpoly K B.gen).map (algebraMap K E))
        (q.map (algebraMap K E))
        q.natDegree
        Polynomial.natDegree_map_le
        (IsAlgClosed.splits _)
    rw [((minpoly.monic B.isIntegral_gen).map
      (algebraMap K E)).leadingCoeff, one_pow, one_mul] at hr
    simpa only [Polynomial.aroots_def,
      Polynomial.eval_map_algebraMap,
      (minpoly.monic B.isIntegral_gen).natDegree_map] using hr

  apply (algebraMap K E).injective
  rw [Algebra.norm_eq_prod_embeddings K E]
  rw [hres]
  calc
    (∏ σ : L →ₐ[K] E, σ (Polynomial.aeval B.gen q)) =
        ∏ y : {y // y ∈ (minpoly K B.gen).aroots E},
          Polynomial.aeval y.1 q := by
      apply Fintype.prod_equiv B.liftEquiv'
      intro σ
      simp only [PowerBasis.liftEquiv'_apply_coe]
      exact (Polynomial.aeval_algHom_apply σ B.gen q).symm
    _ = (((minpoly K B.gen).aroots E).map
          (fun y => Polynomial.aeval y q)).prod := by
      rw [Finset.prod_mem_multiset,
      Finset.prod_eq_multiset_prod,
      Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr]
      · exact nodup_roots
          (Separable.map
            (Algebra.IsSeparable.isSeparable K B.gen))
      · intro y
        rfl

/-- The trace discriminant of a power basis is the polynomial discriminant
of its minimal polynomial. -/
theorem discr_basis_eq_minpoly_discr
    {K L : Type*}
    [Field K] [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (B : PowerBasis K L) :
    Algebra.discr K B.basis =
      (minpoly K B.gen).discr := by
  rw [Algebra.discr_powerBasis_eq_norm K B]
  rw [norm_aeval_eq_resultant B]
  let f := minpoly K B.gen
  have hfmonic : f.Monic :=
    minpoly.monic B.isIntegral_gen
  have hderiv :
      f.derivative.natDegree ≤ f.natDegree - 1 :=
    Polynomial.natDegree_derivative_le f
  have hpad :
      f.resultant f.derivative =
        f.resultant f.derivative f.natDegree (f.natDegree - 1) := by
    symm
    calc
      f.resultant f.derivative f.natDegree (f.natDegree - 1) =
          f.resultant f.derivative f.natDegree
            (f.derivative.natDegree +
              ((f.natDegree - 1) - f.derivative.natDegree)) := by
        rw [Nat.add_sub_of_le hderiv]
      _ = f.coeff f.natDegree ^
            ((f.natDegree - 1) - f.derivative.natDegree) *
          f.resultant f.derivative f.natDegree
            f.derivative.natDegree := by
        rw [Polynomial.resultant_add_right_deg
          f f.derivative f.natDegree f.derivative.natDegree
          ((f.natDegree - 1) - f.derivative.natDegree) le_rfl]
      _ = f.resultant f.derivative := by
        rw [Polynomial.coeff_natDegree, hfmonic.leadingCoeff]
        simp
  rw [hpad]
  have hdeg : 0 < (minpoly K B.gen).degree := by
    rw [B.degree_minpoly]
    simpa using B.dim_pos
  rw [Polynomial.resultant_deriv hdeg]
  rw [(minpoly.monic B.isIntegral_gen).leadingCoeff, mul_one]
  rw [B.natDegree_minpoly, ← B.finrank]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

/-- Polynomial discriminant commutes with a coefficient map for a
positive-degree monic polynomial. -/
theorem discr_map_of_monic_of_degree_pos
    {R S : Type*}
    [CommRing R] [Field S]
    (φ : R →+* S)
    {f : R[X]}
    (hf : f.Monic)
    (hdeg : 0 < f.degree) :
    (f.map φ).discr = φ f.discr := by
  have hdeg' : 0 < (f.map φ).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos,
      hf.natDegree_map φ,
      Polynomial.natDegree_pos_iff_degree_pos]
    exact hdeg
  have hbase := Polynomial.resultant_deriv hdeg
  have hmap := congrArg φ hbase
  have htarget := Polynomial.resultant_deriv hdeg'
  rw [Polynomial.derivative_map, hf.natDegree_map φ] at htarget
  rw [← Polynomial.resultant_map_map
      (f := f)
      (g := f.derivative)
      (m := f.natDegree)
      (n := f.natDegree - 1)
      φ] at hmap
  have heq :
      (-1 : S) ^
          (f.natDegree * (f.natDegree - 1) / 2) *
        (f.map φ).discr =
      (-1 : S) ^
          (f.natDegree * (f.natDegree - 1) / 2) *
        φ f.discr := by
    simpa [hf.leadingCoeff, (hf.map φ).leadingCoeff]
      using htarget.symm.trans hmap
  exact mul_left_cancel₀
    (pow_ne_zero _
      (neg_ne_zero.mpr one_ne_zero : (-1 : S) ≠ 0))
    heq

/-- For an integral power-basis generator over an integrally closed base,
the basis discriminant is the image of its integral minimal-polynomial
discriminant. -/
theorem powerBasis_discr_eq_map_discr
    {R K L : Type*}
    [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R]
    [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R K L]
    [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (B : PowerBasis K L)
    (hBint : IsIntegral R B.gen)
    (h : R[X])
    (hmin : minpoly R B.gen = h) :
    Algebra.discr K B.basis =
      algebraMap R K h.discr := by
  rw [discr_basis_eq_minpoly_discr B]
  have hminK :
      minpoly K B.gen =
        h.map (algebraMap R K) := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hBint, hmin]
  have hhmonic : h.Monic := by
    rw [← hmin]
    exact minpoly.monic hBint
  have hnat : h.natDegree = B.dim := by
    rw [← hhmonic.natDegree_map (algebraMap R K)]
    rw [← hminK]
    exact B.natDegree_minpoly
  have hdeg : 0 < h.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, hnat]
    exact B.dim_pos
  rw [hminK]
  exact discr_map_of_monic_of_degree_pos
    (algebraMap R K) hhmonic hdeg

/-- Literal rational `AdjoinRoot` specialization of the norm--resultant
identity. -/
theorem norm_aeval_adjoinRoot_eq_resultant
    {f : ℚ[X]}
    (hf : f.Monic)
    (hirr : Irreducible f)
    (q : ℚ[X]) :
    Algebra.norm ℚ
        (Polynomial.aeval (AdjoinRoot.root f) q) =
      f.resultant q := by
  letI : Fact (Irreducible f) := ⟨hirr⟩
  let B : PowerBasis ℚ (AdjoinRoot f) :=
    AdjoinRoot.powerBasis hf.ne_zero
  letI : Module.Finite ℚ (AdjoinRoot f) :=
    B.finite
  have h := norm_aeval_eq_resultant B q
  have hmin : minpoly ℚ B.gen = f := by
    simpa [B] using
      AdjoinRoot.minpoly_powerBasis_gen_of_monic hf
  rw [hmin] at h
  simpa [B] using h

end

end MazurProof.PowerBasisDiscriminant


