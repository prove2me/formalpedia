-- Prove2me | Definitions.Def_MazurTransfer_OriginalHopfBaseChangeArithmeticPointsData20261020
-- name    : MazurTransfer_OriginalHopfBaseChangeArithmeticPointsData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T01:47:21.370795+00:00
-- url     : https://prove2.me/theorems/7fa0ae22-8886-4e85-a144-9606473b90c0
-- title:
--   Original Hopf scalar base-change point equivalence and coalgebra representation
-- statement:
--   Retain the original arithmetic point restriction, exact point equivalence and scalar base-change coalgebra representation. All three complete original types and three whole data values, together with all generated structural certificates, are independently checked. Evaluation, convolution preservation and naturality are separate theorem interfaces. Named downstream consumer: transport of the actual selected nineteen character quotient to the equivalent rational-subring base.
-- source:
--   MazurTheorem HopfBaseChangeArithmeticPoints by Vas and contributors; complete original types and whole values, preserving Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: arithmetic points of the SAME Hopf algebra under scalar
base change, preserving convolution and every coefficient map.
Named downstream consumer: transport of the actual selected nineteen
character quotient to the proved equivalent rational-subring base.
-/
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.Bialgebra.Convolution

noncomputable section
namespace MazurTransfer.HopfBaseChangeArithmeticPoints
open scoped TensorProduct
variable {R S H K : Type} [CommRing R] [CommRing S] [Algebra R S]
variable [CommRing H] [HopfAlgebra R H]
variable [CommRing K] [Algebra R K] [Algebra S K] [IsScalarTower R S K]

def restrictPoint (f : WithConv (S ⊗[R] H →ₐ[S] K)) : WithConv (H →ₐ[R] K) :=
  .toConv ((AlgHom.liftEquiv R S H K).symm f.ofConv)

def pointEquiv : WithConv (S ⊗[R] H →ₐ[S] K) ≃ WithConv (H →ₐ[R] K) where
  toFun := restrictPoint
  invFun f := .toConv (AlgHom.liftEquiv R S H K f.ofConv)
  left_inv f := congrArg WithConv.toConv ((AlgHom.liftEquiv R S H K).apply_symm_apply f.ofConv)
  right_inv f := congrArg WithConv.toConv ((AlgHom.liftEquiv R S H K).symm_apply_apply f.ofConv)



def baseChangeRepr (h : H) {ι : Type} (d : Coalgebra.Repr R h ι) :
    Coalgebra.Repr S ((1 : S) ⊗ₜ[R] h) ι where
  index := d.index
  left i := 1 ⊗ₜ[R] d.left i
  right i := 1 ⊗ₜ[R] d.right i
  eq := by
    rw [TensorProduct.comul_tmul, ← d.eq]
    simp [TensorProduct.tmul_sum]





end MazurTransfer.HopfBaseChangeArithmeticPoints
#print axioms MazurTransfer.HopfBaseChangeArithmeticPoints.restrictPoint
#print axioms MazurTransfer.HopfBaseChangeArithmeticPoints.pointEquiv
#print axioms MazurTransfer.HopfBaseChangeArithmeticPoints.baseChangeRepr


