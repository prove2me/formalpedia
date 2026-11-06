-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
-- name    : OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:11:51.442249+00:00
-- url     : https://prove2.me/theorems/7c709c9b-5b6a-4a07-be57-5b8f1240caf9
-- title:
--   Sextic Normalization
-- statement:
--   Definitions and structural lemmas for Sextic Normalization, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_product
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftTrace_breveE_period_integer
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


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
noncomputable def breveGamma1 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood)
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)
noncomputable def breveGamma3 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood ^ 3)
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)
end
section
open EisensteinEmbedding ConcreteTraceCRT IdealGaussCRT
theorem breveE_period_O (x : O) :
    ShortDraftTrace.breveE (eisEmbedding x) = 1 := by
  obtain ⟨a, b, hx⟩ := exists_ab x
  rw [hx]
  change ShortDraftTrace.breveE
    (embedding omega3 omega3_sq (a + b * pb.gen : O)) = 1
  rw [embedding_apply_ab]
  change ShortDraftTrace.breveE
    ((a : ℂ) + (b : ℂ) * ShortDraftTrace.ω₃) = 1
  exact ShortDraftTrace.breveE_period_integer a b
noncomputable def eisBreveModChar (p : O) (hp : p ≠ 0) :
    AddChar (O ⧸ Ideal.span {p}) ℂ :=
  traceModChar eisEmbedding ShortDraftTrace.breveE 1 p
    (eisEmbedding_ne_zero hp) one_ne_zero (by
      intro x
      simpa only [div_one] using breveE_period_O x)
end
section
open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace
noncomputable def breveLocalG (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  (canonicalSextic P hgood (Ideal.Quotient.mk P (4 : O)))⁻¹ *
    breveGamma3 P hgood p hP hp
end
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE
noncomputable def breveGamma2Product
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    [haMax : (Ideal.span {a}).IsMaximal]
    [hbMax : (Ideal.span {b}).IsMaximal]
    (hgooda : lambda ∉ Ideal.span {a})
    (hgoodb : lambda ∉ Ideal.span {b}) : ℂ := by
  letI : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) :=
    finite_quotient_product ha hb
  letI : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  let χa := canonicalSextic (Ideal.span {a}) hgooda
  let χb := canonicalSextic (Ideal.span {b}) hgoodb
  exact (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
    (χa ^ 2) (Ideal.Quotient.factor
      (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
    (χb ^ 2) (Ideal.Quotient.factor
      (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
    eisTraceProdChar ShortDraftTrace.breveE breveE_period_coordinates
      a b ha hb x) / (‖eisEmbedding (a * b)‖ : ℂ)
end ActualEisensteinCubic
namespace ConcreteBreveE
open EisensteinEmbedding ConcreteTraceCRT
noncomputable def normalizedTraceGauss
    (a : O) (ha : a ≠ 0) (χ : MulChar (O ⧸ Ideal.span {a}) ℂ) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {a}) := finite_quotient_span ha
  letI : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  exact gaussSum χ (eisTraceModChar ShortDraftTrace.breveE
    breveE_period_coordinates a ha) / (‖eisEmbedding a‖ : ℂ)
noncomputable def normalizedTraceGaussProduct
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (χa : MulChar (O ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (O ⧸ Ideal.span {b}) ℂ) : ℂ := by
  letI : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) :=
    finite_quotient_product ha hb
  letI : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  exact (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
    χa (Ideal.Quotient.factor
      (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
    χb (Ideal.Quotient.factor
      (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
    eisTraceProdChar ShortDraftTrace.breveE breveE_period_coordinates
      a b ha hb x) / (‖eisEmbedding (a * b)‖ : ℂ)
end ConcreteBreveE
namespace FixedRayActiveSet
open scoped BigOperators
end FixedRayActiveSet
namespace CubeInversion
end CubeInversion
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace
noncomputable def breveGammaMinus1 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood)⁻¹
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)
end ActualEisensteinCubic
namespace PowerExtraction
end PowerExtraction
end
end OAI


