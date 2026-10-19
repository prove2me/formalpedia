-- Prove2me | Definitions.Def_MazurTransfer_Order13InfinityEvaluationMaps
-- name    : MazurTransfer_Order13InfinityEvaluationMaps
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T11:16:01.889577+00:00
-- url     : https://prove2.me/theorems/cc285b54-c73c-4e84-8253-03f332a19ef7
-- title:
--   Evaluation and quotient maps at either literal infinity point
-- statement:
--   Let $R$ be a commutative ring and let $a\in R$ satisfy $a^2=1$. The original reciprocal-chart evaluation sends $z\mapsto0$ and $w\mapsto a$, is an $R$-algebra map, and is surjective. The section ideal and its specified quotient map are $$I_a=(z,w-a),\qquad A\longrightarrow A/I_a,$$ with the original quotient-coordinate equations. These maps supply the exact kernel theorem and the local parameter at either literal infinity point.
-- source:
--   Original complete selected declarations and bodies from MazurTheorem, Apache-2.0, Vas and contributors. 7 complete original closed types and 4 data values are kernel-compared; native, strict and complete frontend checks pass with standard axioms only. Public imports alone replace the original project dependencies. Original polynomial coefficients and upstream attribution are retained. Design boundary and named downstream consumers are explicit in the checked source and original-source preparation manifest.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact evaluation ideal at either literal reciprocal
infinity point, over any commutative base ring. Named downstream consumer:
the local parameter and the principal divisor of the degree-19 Pell function.
This generalizes the checked positive-infinity evaluation calculation.
-/
import Definitions.Def_MazurTransfer_Order13IntegralInfinitySections
noncomputable section
universe u
namespace MazurTransfer.Order13InfinityEvaluationKernel
open Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13IntegralSections
variable (R : Type u) [CommRing R] (a : R) (ha : a ^ 2 = 1)
def evaluation : ReciprocalRing R →+* R := reciprocalInfinityEvaluation R a ha

def evaluationAlgHom : ReciprocalRing R →ₐ[R] R where
  __ := evaluation R a ha
  commutes' r := by
    exact RingHom.congr_fun (reciprocalInfinityEvaluation_comp_algebraMap R a ha) r

def sectionIdeal : Ideal (ReciprocalRing R) :=
  Ideal.span {zCoordinate R, wCoordinate R - algebraMap R (ReciprocalRing R) a}

def quotientMap : ReciprocalRing R →ₐ[R] ReciprocalRing R ⧸ sectionIdeal R a :=
  Ideal.Quotient.mkₐ R (sectionIdeal R a)

theorem quotientMap_z : quotientMap R a (zCoordinate R) = 0 := by
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (by simp))

theorem quotientMap_w : quotientMap R a (wCoordinate R) =
    algebraMap R (ReciprocalRing R ⧸ sectionIdeal R a) a := by
  have h : quotientMap R a (wCoordinate R - algebraMap R (ReciprocalRing R) a) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (by simp))
  rw [map_sub, (quotientMap R a).commutes] at h
  exact sub_eq_zero.mp h

theorem evaluation_surjective : Function.Surjective (evaluation R a ha) := by
  intro r
  refine ⟨algebraMap R (ReciprocalRing R) r, ?_⟩
  exact RingHom.congr_fun (reciprocalInfinityEvaluation_comp_algebraMap R a ha) r
end MazurTransfer.Order13InfinityEvaluationKernel
#print axioms MazurTransfer.Order13InfinityEvaluationKernel.evaluation_surjective


