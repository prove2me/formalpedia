-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_LinearAdjoinRootScalar_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_LinearAdjoinRootScalar_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:22:00.558216+00:00
-- url     : https://prove2.me/theorems/8b28a3d6-f874-49a2-8830-36f446a7e574
-- title:
--   FLT.Assumptions.MazurProof.LinearAdjoinRootScalar source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.LinearAdjoinRootScalar

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.LinearAdjoinRootScalar
Original leading source comments and nonproject imports are retained below. -/
import Mathlib.RingTheory.AdjoinRoot

set_option autoImplicit false




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


