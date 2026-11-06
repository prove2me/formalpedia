-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
-- name    : QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:25:24.965196+00:00
-- url     : https://prove2.me/theorems/4e59d72f-55bd-4804-a7c8-08b7408cbd18
-- title:
--   Trace
-- statement:
--   Definitions and structural lemmas for Trace, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/Trace.lean

import Mathlib.LinearAlgebra.Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Grade
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
@[implicit_reducible]
noncomputable def primaryTorsionGradeFinite [IsNoetherianRing R]
    [Module.Finite R M] (p : Ideal R) (i : ℕ) :
    letI := primaryTorsionGradeModule (M := M) p i
    Module.Finite (R ⧸ p) (primaryTorsionGrade p M i) := by
  let h := primaryTorsionGrade_annihilated (M := M) p i
  letI : Module (R ⧸ p) (primaryTorsionGrade p M i) := h.module
  letI : Module.Finite R (primaryTorsionGrade p M i) := inferInstance
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ p)
    (primaryTorsionGrade p M i)
noncomputable def primaryTorsionGradeTrace [IsNoetherianRing R]
    [Module.Finite R M] (p : Ideal R) [p.IsMaximal]
    (f : M →ₗ[R] M) (i : ℕ) : R ⧸ p := by
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI := primaryTorsionGradeModule (M := M) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p M i) :=
    primaryTorsionGradeFinite (M := M) p i
  exact LinearMap.trace (R ⧸ p) (primaryTorsionGrade p M i)
    (primaryTorsionGradeEndomorphism p f i)
noncomputable def primaryTorsionTrace [IsNoetherianRing R]
    [Module.Finite R M] (p : Ideal R) [p.IsMaximal]
    (f : M →ₗ[R] M) (n : ℕ) : R ⧸ p :=
  ∑ i ∈ Finset.range n, primaryTorsionGradeTrace p f i
end QEC.Coding.AlgebraicGeometry


