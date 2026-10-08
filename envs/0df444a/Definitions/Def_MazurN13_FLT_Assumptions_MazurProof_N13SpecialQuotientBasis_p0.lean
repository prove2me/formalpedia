-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialQuotientBasis_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialQuotientBasis_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:07:37.53999+00:00
-- url     : https://prove2.me/theorems/6b9b86de-31b5-48c6-8926-ab7a4264e39d
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialQuotientBasis source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialQuotientBasis

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialQuotientBasis
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13AbelChartBase_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialDualFrame_p0
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.AdjoinRoot

set_option autoImplicit false




/-!
# The literal basis of the fixed N13 special quotient

The selected special divisor has graph ideal `(X²+X,Y)`.  Evaluation on
that graph identifies its affine quotient with
`𝔽₂[X]/(X²+X)`.  The canonical monic power basis on the latter transports
back to the literal quotient basis `{1,x}`.

This file is only the fixed special-fibre endpoint.  It does not assert
that the contraction of an arbitrary generic Picard representative reduces
to this ideal.
-/

open Module
open Polynomial

namespace MazurProof.N13SpecialQuotientBasis

noncomputable section

abbrev k : Type :=
  N13GoodCoordinateRingTwo.K

abbrev A : Type :=
  N13GoodCoordinateRingTwo.CoordinateRing

/-- The fixed reduced smooth Mumford datum. -/
def specialData :
    N13GoodCoordinateRingTwo.SemiMumford :=
  N13GeneralizedMumfordReduction.reduceSmoothMumford
    N13AbelChartBase.baseSmoothMumford

@[simp] theorem specialData_u :
    specialData.u = (X ^ 2 + X : k[X]) :=
  N13AbelChartBase.reduce_baseSmoothMumford_u

@[simp] theorem specialData_v :
    specialData.v = 0 :=
  N13AbelChartBase.reduce_baseSmoothMumford_v

@[simp] theorem specialData_u_natDegree :
    specialData.u.natDegree = 2 := by
  rw [specialData_u]
  (compute_degree; norm_num)

/-- The fixed special graph ideal. -/
abbrev specialIdeal : Ideal A :=
  N13GoodCoordinateRingTwo.mumfordIdeal
    specialData.u specialData.v

theorem specialIdeal_eq_dualFrame :
    specialIdeal = N13SpecialDualFrame.I := by
  simp [specialIdeal, N13SpecialDualFrame.I,
    N13SpecialDualFrame.u]

/-- The monic quotient `k[X]/(u)` has its canonical power basis. -/
def residueBasis :
    Basis (Fin 2) k (AdjoinRoot specialData.u) :=
  (AdjoinRoot.powerBasis' specialData.u_monic).basis.reindex
    (finCongr (by
      change specialData.u.natDegree = 2
      exact specialData_u_natDegree))

theorem residueBasis_apply (i : Fin 2) :
    residueBasis i =
      AdjoinRoot.root specialData.u ^ (i : ℕ) := by
  change
    ((AdjoinRoot.powerBasis' specialData.u_monic).basis.reindex
        (finCongr specialData_u_natDegree)) i =
      AdjoinRoot.root specialData.u ^ (i : ℕ)
  rw [Basis.reindex_apply, PowerBasis.basis_eq_pow,
    AdjoinRoot.powerBasis'_gen]
  rfl

@[simp] theorem residueBasis_zero :
    residueBasis (0 : Fin 2) = 1 := by
  simp [residueBasis_apply]

@[simp] theorem residueBasis_one :
    residueBasis (1 : Fin 2) =
      AdjoinRoot.root specialData.u := by
  simp [residueBasis_apply]

/-- The graph-quotient equivalence respects the coefficient field. -/
def quotientAlgEquiv :
    (A ⧸ specialIdeal) ≃ₐ[k]
      N13GoodCoordinateRingTwo.MumfordResidue specialData :=
  by
    simpa only [A, k, specialIdeal] using
      N13GoodCoordinateRingTwo.mumfordQuotientAlgEquiv specialData

/-- Transport the polynomial quotient basis to the affine graph quotient. -/
def quotientBasis :
    Basis (Fin 2) k (A ⧸ specialIdeal) :=
  residueBasis.map
    quotientAlgEquiv.symm.toLinearEquiv

@[simp] theorem quotientBasis_zero :
    quotientBasis (0 : Fin 2) = 1 := by
  change quotientAlgEquiv.symm (residueBasis 0) = 1
  rw [residueBasis_zero]
  exact map_one quotientAlgEquiv.symm

set_option backward.isDefEq.respectTransparency.types false in
@[simp] theorem quotientBasis_one :
    quotientBasis (1 : Fin 2) =
      Ideal.Quotient.mk specialIdeal
        (N13GoodCoordinateRingTwo.xClass X) := by
  change
    quotientAlgEquiv.symm (residueBasis 1) =
      Ideal.Quotient.mk specialIdeal
        (N13GoodCoordinateRingTwo.xClass X)
  rw [residueBasis_one]
  apply quotientAlgEquiv.injective
  rw [quotientAlgEquiv.apply_symm_apply]
  simp only [quotientAlgEquiv]
  change
    AdjoinRoot.root specialData.u =
      N13GoodCoordinateRingTwo.mumfordEval specialData
        (N13GoodCoordinateRingTwo.xClass X)
  rw [N13GoodCoordinateRingTwo.mumfordEval_xClass]
  rfl

/-- The basis family is literally `{1,x}`. -/
theorem coe_quotientBasis :
    (quotientBasis : Fin 2 → A ⧸ specialIdeal) =
      ![1,
        Ideal.Quotient.mk specialIdeal
          (N13GoodCoordinateRingTwo.xClass X)] := by
  funext i
  fin_cases i <;> simp

end

end MazurProof.N13SpecialQuotientBasis


