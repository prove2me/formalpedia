-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DerivationTrace
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_DerivationTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:23:26.271836+00:00
-- url     : https://prove2.me/theorems/132b0d3c-78a5-4423-a667-ecdf7e31c2b3
-- title:
--   Derivation Trace
-- statement:
--   Definitions and structural lemmas for Derivation Trace, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DerivationTrace.lean

import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
namespace FunctionFieldDifferential
open scoped RatFunc
section ConnectionTrace
variable {k K L : Type*} [Field k] [Field K] [Field L]
variable [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
variable [FiniteDimensional K L]
abbrev DerivationExtends (D₀ : Derivation k K K) (D : Derivation k L L) : Prop :=
  ∀ c : K, D (algebraMap K L c) = algebraMap K L (D₀ c)
theorem derivation_smul_of_extends
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hD : DerivationExtends D₀ D) (c : K) (x : L) :
    D (c • x) = D₀ c • x + c • D x := by
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]
  rw [D.leibniz, hD]
  ring
noncomputable def derivationConnection
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hD : DerivationExtends D₀ D) (T : Module.End K L) : Module.End K L where
  toFun x := D (T x) - T (D x)
  map_add' x y := by
    simp only [map_add]
    abel
  map_smul' c x := by
    rw [T.map_smul, derivation_smul_of_extends D₀ D hD,
      derivation_smul_of_extends D₀ D hD, T.map_add, T.map_smul, T.map_smul]
    simp only [smul_sub]
    change
      D₀ c • T x + c • D (T x) - (D₀ c • T x + c • T (D x)) =
        c • D (T x) - c • T (D x)
    abel
end ConnectionTrace
variable {k F : Type*} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
end FunctionFieldDifferential
end QEC.Coding.AlgebraicGeometry


