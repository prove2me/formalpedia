-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimePowerQuotientTrace
-- name    : QEC_Coding_AlgebraicGeometry_Trace_PrimePowerQuotientTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:02:31.27808+00:00
-- url     : https://prove2.me/theorems/6481fb0a-7b26-440a-a6b9-86728813eb86
-- title:
--   Prime Power Quotient Trace
-- statement:
--   Definitions and structural lemmas for Prime Power Quotient Trace, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimePowerQuotientTrace.lean

import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_LinearTraceInvariantQuotient
set_option autoImplicit false
namespace Ideal
universe u v
variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
attribute [-instance] Ideal.Quotient.commSemiring
attribute [local instance]
  Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
namespace Factors
open UniqueFactorizationMonoid
variable [IsDedekindDomain S] [Module.Finite R S]
noncomputable abbrev compatibleQuotientField (p : Ideal R) [p.IsMaximal] :
    Field (R ⧸ p) :=
  Ideal.Quotient.field p
noncomputable abbrev powQuotientSubmodule (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (i : Nat) :
    Submodule (R ⧸ p)
      (S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S)) :=
  Submodule.restrictScalars (R ⧸ p)
    (((P : Ideal S) ^ i).map
      (Ideal.Quotient.mk ((P : Ideal S) ^ ramificationIdx' p (P : Ideal S))))
noncomputable def powQuotientMul (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S) (i : Nat) :
    powQuotientSubmodule p P i →ₗ[R ⧸ p] powQuotientSubmodule p P i :=
  ((Algebra.lmul (R ⧸ p)
      (S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S))
      (Ideal.Quotient.mk _ x)).domRestrict (powQuotientSubmodule p P i)).codRestrict
    (powQuotientSubmodule p P i) fun y => by
      change Ideal.Quotient.mk _ x * (y :
        S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S)) ∈
          ((P : Ideal S) ^ i).map
            (Ideal.Quotient.mk ((P : Ideal S) ^ ramificationIdx' p (P : Ideal S)))
      exact Ideal.mul_mem_left _ _ y.property
noncomputable abbrev powQuotientInclusion (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (i : Nat) :
    powQuotientSubmodule p P (i + 1) →ₗ[R ⧸ p] powQuotientSubmodule p P i :=
  Ideal.powQuotSuccInclusion p (P : Ideal S) i
noncomputable def residueQuotientMul (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S) :
    (S ⧸ (P : Ideal S)) →ₗ[R ⧸ p] (S ⧸ (P : Ideal S)) :=
  Algebra.lmul (R ⧸ p) (S ⧸ (P : Ideal S)) (Ideal.Quotient.mk _ x)
@[simp]
theorem powQuotientMul_apply (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S) (i : Nat)
    (y : powQuotientSubmodule p P i) :
    (powQuotientMul p P x i y :
        S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S)) =
      Ideal.Quotient.mk _ x * (y :
        S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S)) :=
  rfl
@[simp]
theorem powQuotientInclusion_apply (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (i : Nat)
    (y : powQuotientSubmodule p P (i + 1)) :
    (powQuotientInclusion p P i y :
      S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S)) = y :=
  rfl
@[simp]
theorem residueQuotientMul_apply (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S)
    (y : S ⧸ (P : Ideal S)) :
    residueQuotientMul p P x y = Ideal.Quotient.mk _ x * y :=
  rfl
theorem powQuotientInclusion_range_invariant (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S) (i : Nat) :
    LinearMap.range (powQuotientInclusion p P i) ≤
      (LinearMap.range (powQuotientInclusion p P i)).comap
        (powQuotientMul p P x i) := by
  rintro _ ⟨y, rfl⟩
  refine ⟨powQuotientMul p P x (i + 1) y, ?_⟩
  apply Subtype.ext
  rfl
noncomputable def powQuotientGradeMul (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S) (i : Nat) :
    (powQuotientSubmodule p P i ⧸ LinearMap.range (powQuotientInclusion p P i))
      →ₗ[R ⧸ p]
    (powQuotientSubmodule p P i ⧸ LinearMap.range (powQuotientInclusion p P i)) :=
  (LinearMap.range (powQuotientInclusion p P i)).mapQ
    (LinearMap.range (powQuotientInclusion p P i)) (powQuotientMul p P x i)
      (powQuotientInclusion_range_invariant p P x i)
noncomputable def powQuotientGradeEmbedding (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) {i : Nat} {a : S}
    (ha : a ∈ (P : Ideal S) ^ i) :
    (S ⧸ (P : Ideal S)) →ₗ[R ⧸ p]
      (powQuotientSubmodule p P i ⧸ LinearMap.range (powQuotientInclusion p P i)) :=
  Ideal.quotientToQuotientRangePowQuotSucc p (P : Ideal S) ha
end Factors
end Ideal


