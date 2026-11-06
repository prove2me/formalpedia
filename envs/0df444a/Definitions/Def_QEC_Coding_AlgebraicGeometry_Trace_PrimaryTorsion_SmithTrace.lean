-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_SmithTrace
-- name    : QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_SmithTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:24:16.671186+00:00
-- url     : https://prove2.me/theorems/3ed042ec-fc95-4a95-a363-fd4e3f3799f3
-- title:
--   Smith Trace
-- statement:
--   Definitions and structural lemmas for Smith Trace, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/SmithTrace.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialSmithMatrix
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PiTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicTraceStabilization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceEquivScoped
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation


set_option autoImplicit false
open scoped Polynomial
namespace QEC.Coding.AlgebraicGeometry
open Module
universe u v
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
noncomputable local instance cokernelModuleFinite [Module.Finite R M]
    (f : M →ₗ[R] M) : Module.Finite R (M ⧸ LinearMap.range f) :=
  Module.Finite.quotient R (LinearMap.range f)
noncomputable local instance cyclicQuotientModuleFinite (a : R) :
    Module.Finite R (R ⧸ Ideal.span {a}) :=
  Module.Finite.quotient R (Ideal.span {a})
theorem range_le_comap_of_commute (f g : M →ₗ[R] M)
    (hcomm : f.comp g = g.comp f) :
    LinearMap.range f ≤ (LinearMap.range f).comap g := by
  rintro _ ⟨x, rfl⟩
  refine ⟨g x, ?_⟩
  exact LinearMap.congr_fun hcomm x
def cokernelEndomorphism (f g : M →ₗ[R] M)
    (hcomm : f.comp g = g.comp f) :
    (M ⧸ LinearMap.range f) →ₗ[R] (M ⧸ LinearMap.range f) :=
  (LinearMap.range f).mapQ (LinearMap.range f) g
    (range_le_comap_of_commute f g hcomm)
@[simp]
theorem cokernelEndomorphism_mk (f g : M →ₗ[R] M)
    (hcomm : f.comp g = g.comp f) (x : M) :
    cokernelEndomorphism f g hcomm
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (g x) :=
  rfl
variable [IsDomain R] [IsPrincipalIdealRing R]
def smithCoordinateSubmodule {n : ℕ} (a : Fin n → R) :
    Submodule R (Fin n → R) :=
  Submodule.pi Set.univ fun i => Ideal.span {a i}
theorem target_repr_apply_eq_mul_of_toMatrix_eq_diagonal
    {n : ℕ} (source target : Basis (Fin n) R M)
    (a : Fin n → R) (f : M →ₗ[R] M)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (x : M) (i : Fin n) :
    target.repr (f x) i = a i * source.repr x i := by
  have h := congrFun
    (LinearMap.toMatrix_mulVec_repr source target f x) i
  rw [hdiag] at h
  simpa [Matrix.mulVec, dotProduct, Matrix.diagonal_apply] using h.symm
theorem range_map_target_equivFun_eq_smithCoordinateSubmodule
    {n : ℕ} (source target : Basis (Fin n) R M)
    (a : Fin n → R) (f : M →ₗ[R] M)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a) :
    (LinearMap.range f).map
        (target.equivFun : M →ₗ[R] Fin n → R) =
      smithCoordinateSubmodule a := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    rw [smithCoordinateSubmodule, Submodule.mem_pi]
    intro i _hi
    rw [Ideal.mem_span_singleton]
    refine ⟨source.repr z i, ?_⟩
    exact target_repr_apply_eq_mul_of_toMatrix_eq_diagonal
      source target a f hdiag z i
  · intro hy
    have hyi : ∀ i, y i ∈ Ideal.span ({a i} : Set R) := by
      intro i
      exact (Submodule.mem_pi.mp hy) i (Set.mem_univ i)
    have hydiv : ∀ i, a i ∣ y i := by
      intro i
      exact Ideal.mem_span_singleton.mp (hyi i)
    choose c hc using hydiv
    let x : M := source.equivFun.symm c
    refine ⟨f x, ⟨x, rfl⟩, ?_⟩
    apply funext
    intro i
    change target.repr (f x) i = y i
    rw [target_repr_apply_eq_mul_of_toMatrix_eq_diagonal
      source target a f hdiag]
    have hxcoord : source.repr x i = c i := by
      exact congrFun (source.equivFun.apply_symm_apply c) i
    rw [hxcoord]
    exact (hc i).symm
noncomputable def smithCokernelEquiv
    {n : ℕ} (source target : Basis (Fin n) R M)
    (a : Fin n → R) (f : M →ₗ[R] M)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a) :
    (M ⧸ LinearMap.range f) ≃ₗ[R]
      ∀ i, R ⧸ Ideal.span ({a i} : Set R) :=
  (Submodule.Quotient.equiv
      (LinearMap.range f) (smithCoordinateSubmodule a)
      target.equivFun
      (range_map_target_equivFun_eq_smithCoordinateSubmodule
        source target a f hdiag)).trans
    (Submodule.quotientPi fun i => Ideal.span ({a i} : Set R))
variable {k : Type*} [Field k] [Finite k]
end QEC.Coding.AlgebraicGeometry


