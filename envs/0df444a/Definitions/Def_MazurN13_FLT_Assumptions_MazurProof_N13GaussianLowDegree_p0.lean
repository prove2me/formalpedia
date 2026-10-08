-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianLowDegree_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianLowDegree_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:26:46.540488+00:00
-- url     : https://prove2.me/theorems/f0580f03-4c63-403b-8ee7-420c6d89242f
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianLowDegree source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianLowDegree

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianLowDegree
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianOrderTwo_p0

set_option autoImplicit false




/-!
# Low-degree polynomial jets in the N13 Gaussian order

Every integral polynomial in `θ` reduces to a constant dual number: the
coefficients have no infinitesimal part and `θ` reduces to `α`.  If its
coefficient reduction is nonzero of degree at most two, evaluation at
`α` cannot vanish because the residue polynomial of `α` has degree three.

This treats split and nonsplit degree-two support uniformly.  It is a
statement about the explicit Gaussian order and its first quotient; the
global-to-completion and genuine local Kummer comparisons remain separate.
-/

open Polynomial

namespace MazurProof.N13GaussianLowDegree

noncomputable section

open N13GaussianOrderTwo
open N13LocalDlogTwo
open N13LocalDlogRegimes
open TrivSqZeroExt

abbrev Z2 : Type := N13GaussianOrderTwo.Z2
abbrev Order : Type := N13GaussianOrderTwo.Order
abbrev F8 : Type := N13LocalDlogTwo.F8

/-- Coefficientwise reduction of a `2`-adic integral polynomial. -/
def residuePolynomial (U : Z2[X]) : (ZMod 2)[X] :=
  U.map PadicInt.toZMod

/-- Evaluation of the reduced polynomial at the cubic residue generator. -/
def residueEval (U : Z2[X]) : F8 :=
  AdjoinRoot.mk residueCubic (residuePolynomial U)

/-- Evaluation of an integral polynomial at the order generator. -/
def thetaEval (U : Z2[X]) : Order :=
  U.eval₂ (algebraMap Z2 Order) theta

/-- Polynomial evaluation commutes with the exact first-jet reduction.
The resulting jet has no infinitesimal component. -/
theorem reduction_thetaEval (U : Z2[X]) :
    reduction (thetaEval U) = inl (residueEval U) := by
  let residueDualHom : ZMod 2 →+* DualNumber F8 :=
    (algebraMap F8 (DualNumber F8)).comp
      (algebraMap (ZMod 2) F8)
  have hscalar :
      reduction.comp (algebraMap Z2 Order) =
        padicScalarDualHom := by
    apply RingHom.ext
    intro z
    exact reduction_scalar z
  have hcomp :
      residueDualHom.comp PadicInt.toZMod =
        padicScalarDualHom := by
    apply RingHom.ext
    intro z
    rfl
  calc
    reduction (thetaEval U) =
        U.eval₂ padicScalarDualHom thetaDual := by
      rw [thetaEval, Polynomial.hom_eval₂, hscalar,
        reduction_theta]
    _ = (residuePolynomial U).eval₂
          residueDualHom thetaDual := by
      rw [residuePolynomial, Polynomial.eval₂_map, hcomp]
    _ = inl
          ((residuePolynomial U).eval₂
            (algebraMap (ZMod 2) F8) alpha) := by
      simpa [residueDualHom, thetaDual,
        TrivSqZeroExt.algebraMap_eq_inl'] using
        (Polynomial.hom_eval₂
          (residuePolynomial U)
          (algebraMap (ZMod 2) F8)
          (algebraMap F8 (DualNumber F8))
          alpha).symm
    _ = inl (residueEval U) := by
      change inl
          ((residuePolynomial U).eval₂
            (AdjoinRoot.of residueCubic)
            (AdjoinRoot.root residueCubic)) =
        inl (AdjoinRoot.mk residueCubic (residuePolynomial U))
      exact congrArg
        (fun z : AdjoinRoot residueCubic =>
          (inl z : DualNumber F8))
        (by
          simpa only [aeval_def, AdjoinRoot.algebraMap_eq] using
            (AdjoinRoot.aeval_eq (f := residueCubic)
              (residuePolynomial U)))

/-- A nonzero polynomial of degree below three cannot vanish at `α`. -/
theorem residueEval_ne_zero
    (U : Z2[X])
    (hne : residuePolynomial U ≠ 0)
    (hdeg : (residuePolynomial U).natDegree ≤ 2) :
    residueEval U ≠ 0 := by
  apply AdjoinRoot.mk_ne_zero_of_natDegree_lt
    residueCubic_monic hne
  rw [residueCubic_natDegree]
  omega

/-- The constant first jet, packaged as a dual-number unit. -/
def lowDegreeJet
    (U : Z2[X])
    (hne : residuePolynomial U ≠ 0)
    (hdeg : (residuePolynomial U).natDegree ≤ 2) :
    (DualNumber F8)ˣ :=
  RamifiedDlog.unitOf
    (residueEval U) 0
    (residueEval_ne_zero U hne hdeg)

@[simp] theorem lowDegreeJet_val
    (U : Z2[X])
    (hne : residuePolynomial U ≠ 0)
    (hdeg : (residuePolynomial U).natDegree ≤ 2) :
    (lowDegreeJet U hne hdeg : DualNumber F8) =
      reduction (thetaEval U) := by
  rw [reduction_thetaEval]
  ext <;> simp [lowDegreeJet]

/-- Every primitive low-degree integral polynomial has zero first
ramified logarithm at `θ`. -/
theorem dlog_lowDegreeJet
    (U : Z2[X])
    (hne : residuePolynomial U ≠ 0)
    (hdeg : (residuePolynomial U).natDegree ≤ 2) :
    RamifiedDlog.dlog (lowDegreeJet U hne hdeg) = 0 := by
  simp [lowDegreeJet]

end

end MazurProof.N13GaussianLowDegree


