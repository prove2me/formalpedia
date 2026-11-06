-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
-- name    : OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:09:54.042028+00:00
-- url     : https://prove2.me/theorems/d1b149fa-f69c-4dba-8f14-4662d0f0aa46
-- title:
--   Cubic Normalization
-- statement:
--   Definitions and structural lemmas for Cubic Normalization, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicNormalization.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
namespace ActualEisensteinCubic
section
open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace
end
open EisensteinEmbedding ConcreteTraceCRT
noncomputable def breveGamma2 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood ^ 2)
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)
end ActualEisensteinCubic
namespace ShortDraftLocal
open AddChar MulChar
end ShortDraftLocal
namespace ActualEisensteinCubic
section
open AddChar MulChar
end
open ConcreteTraceCRT PrimitiveTrace
end ActualEisensteinCubic
namespace AnalyticBridge
end AnalyticBridge
namespace JacobiQuadratic
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
def affineDouble (hchar : ringChar F ≠ 2) : F ≃ F where
  toFun x := 2 * x - 1
  invFun t := (t + 1) / 2
  left_inv := by
    intro x
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
    field_simp
    ring
  right_inv := by
    intro t
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
    field_simp
    ring
def oneSub : F ≃ F where
  toFun y := 1 - y
  invFun y := 1 - y
  left_inv := by intro y; ring
  right_inv := by intro y; ring
end JacobiQuadratic
end
end OAI


