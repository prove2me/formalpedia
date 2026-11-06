-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CRTTrace
-- name    : QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CRTTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:42:58.843188+00:00
-- url     : https://prove2.me/theorems/58df157b-a45a-4432-92bf-512a578358fa
-- title:
--   CRTTrace
-- statement:
--   Definitions and structural lemmas for CRTTrace, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/CRTTrace.lean

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_ProdTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceEquivScoped
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
universe u v
variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
noncomputable def quotientMulLinearEquivQuotientProd
    (I J : Ideal S) (hcop : IsCoprime I J) :
    (S ⧸ (I * J)) ≃ₗ[R] (S ⧸ I) × (S ⧸ J) :=
  (Ideal.quotientMulEquivQuotientProd I J hcop).toAddEquiv.toLinearEquiv
    (R := R) (by
      intro r x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hmapI : Ideal.Quotient.factor
          (Ideal.mul_le_left : I * J ≤ I)
          (algebraMap R (S ⧸ (I * J)) r) =
          algebraMap R (S ⧸ I) r := by
        change Ideal.Quotient.factor Ideal.mul_le_left
          (Ideal.Quotient.mk (I * J) (algebraMap R S r)) =
            Ideal.Quotient.mk I (algebraMap R S r)
        exact Ideal.Quotient.factor_mk Ideal.mul_le_left _
      have hmapJ : Ideal.Quotient.factor
          (Ideal.mul_le_right : I * J ≤ J)
          (algebraMap R (S ⧸ (I * J)) r) =
          algebraMap R (S ⧸ J) r := by
        change Ideal.Quotient.factor Ideal.mul_le_right
          (Ideal.Quotient.mk (I * J) (algebraMap R S r)) =
            Ideal.Quotient.mk J (algebraMap R S r)
        exact Ideal.Quotient.factor_mk Ideal.mul_le_right _
      apply Prod.ext <;>
        simp [Ideal.quotientMulEquivQuotientProd_fst,
          Ideal.quotientMulEquivQuotientProd_snd, Algebra.smul_def,
          hmapI, hmapJ])
end QEC.Coding.AlgebraicGeometry


