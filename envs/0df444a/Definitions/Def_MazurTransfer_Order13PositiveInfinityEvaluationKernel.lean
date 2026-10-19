-- Prove2me | Definitions.Def_MazurTransfer_Order13PositiveInfinityEvaluationKernel
-- name    : MazurTransfer_Order13PositiveInfinityEvaluationKernel
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:42:35.679163+00:00
-- url     : https://prove2.me/theorems/94b481bc-c62d-4ad9-9ff6-a8cd8882d118
-- title:
--   The literal positive-infinity evaluation and its exact kernel
-- statement:
--   Let $R$ be a commutative ring. On the actual reciprocal coordinate ring of the order-thirteen curve, the positive-infinity evaluation $\varepsilon$ sends $z$ to $0$ and $w$ to $1$. It is surjective and its kernel is the literal ideal $(z,w-1)$. The retained evaluation, quotient and factorization constructors specify this closed section image over every commutative base.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. Ten original declarations from Order13PositiveInfinityEvaluationKernel.lean, with every declaration body unchanged and only imports replaced by public integral infinity sections and first-chart constructors. All ten original closed types and the four original data constructor values are compared in the kernel. The quotient-factorization and kernel identities are the structural proofs needed by the actual closed-image interface. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: actual first/inverse chart intersection in unchanged integral FiniteMapData.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact kernel and surjectivity of the actual positive
infinity evaluation on the reciprocal chart over every commutative ring.
Named downstream consumer: its closed image and the single-section complement.
No whole-curve complement or global gluing is asserted.
-/
import Definitions.Def_MazurTransfer_Order13IntegralInfinitySections
import Definitions.Def_MazurTransfer_Order13FirstFiniteChartCanonicalOpen

noncomputable section
universe u
namespace MazurTransfer.Order13PositiveInfinityEvaluationKernel
open Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13IntegralSections
variable (R : Type u) [CommRing R]

def evaluation : ReciprocalRing R →+* R := reciprocalInfinityEvaluation R 1 (by simp)
def evaluationAlgHom : ReciprocalRing R →ₐ[R] R where
  __ := evaluation R
  commutes' r := by
    exact RingHom.congr_fun (reciprocalInfinityEvaluation_comp_algebraMap R 1 (by simp)) r

def sectionIdeal : Ideal (ReciprocalRing R) := Ideal.span {zCoordinate R,wCoordinate R - 1}
def quotientMap : ReciprocalRing R →ₐ[R] ReciprocalRing R ⧸ sectionIdeal R :=
  Ideal.Quotient.mkₐ R (sectionIdeal R)

theorem quotientMap_z : quotientMap R (zCoordinate R) = 0 := by
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (by simp))
theorem quotientMap_w : quotientMap R (wCoordinate R) = 1 := by
  have h : quotientMap R (wCoordinate R - 1) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (by simp))
  rw [map_sub,map_one] at h
  exact sub_eq_zero.mp h

theorem quotientMap_factorization : quotientMap R =
    (Algebra.ofId R (ReciprocalRing R ⧸ sectionIdeal R)).comp (evaluationAlgHom R) := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change quotientMap R (zCoordinate R) =
      algebraMap R (ReciprocalRing R ⧸ sectionIdeal R) (reciprocalInfinityEvaluation R 1 (by simp) (zCoordinate R))
    rw [quotientMap_z,reciprocalInfinityEvaluation_z,map_zero]
  · change quotientMap R (wCoordinate R) =
      algebraMap R (ReciprocalRing R ⧸ sectionIdeal R) (reciprocalInfinityEvaluation R 1 (by simp) (wCoordinate R))
    rw [quotientMap_w,reciprocalInfinityEvaluation_w,map_one]

theorem sectionIdeal_le_kernel : sectionIdeal R ≤ RingHom.ker (evaluation R) := by
  apply Ideal.span_le.mpr
  intro b hb
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl
  · change reciprocalInfinityEvaluation R 1 (by simp) (zCoordinate R) = 0
    exact reciprocalInfinityEvaluation_z R 1 (by simp)
  · change evaluation R (wCoordinate R - 1) = 0
    simp only [evaluation,map_sub,map_one,reciprocalInfinityEvaluation_w,sub_self]

theorem evaluation_kernel : RingHom.ker (evaluation R) = sectionIdeal R := by
  apply le_antisymm
  · intro a ha
    change evaluation R a = 0 at ha
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change quotientMap R a = 0
    have h := DFunLike.congr_fun (quotientMap_factorization R) a
    change quotientMap R a = algebraMap R (ReciprocalRing R ⧸ sectionIdeal R) (evaluation R a) at h
    rw [ha,map_zero] at h
    exact h
  · exact sectionIdeal_le_kernel R

theorem evaluation_surjective : Function.Surjective (evaluation R) := by
  intro r
  refine ⟨algebraMap R (ReciprocalRing R) r,?_⟩
  exact RingHom.congr_fun (reciprocalInfinityEvaluation_comp_algebraMap R 1 (by simp)) r

end MazurTransfer.Order13PositiveInfinityEvaluationKernel
#print axioms MazurTransfer.Order13PositiveInfinityEvaluationKernel.evaluation_kernel
#print axioms MazurTransfer.Order13PositiveInfinityEvaluationKernel.evaluation_surjective


