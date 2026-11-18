-- Prove2me | Definitions.Def_Kyprianou_Ch09_AppellSource
-- name    : Kyprianou_Ch09_AppellSource
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T15:16:58.453199+00:00
-- url     : https://prove2.me/theorems/a87e31a7-3a01-474c-a72b-7313d90f853c
-- title:
--   Kyprianou (2006) Chapter 9 canonical source owner AppellSource
-- statement:
--   Source Definition 9.5 and mathematical properties of the Appell polynomial construction. This source Definition module provides the actual declarations: IsAppellUpTo, lemma98_appellMeanValue_Statement, appellMeanValue, certificate_result_9_8. The binding scopes, mathematical hypotheses and exact meaning are given by the complete Lean source included here; no published theorem proof is assumed.
-- source:
--   A. E. Kyprianou (2006), first edition, Chapter 9, printed pp. 239–270, physical PDF pp. 247–278; Chapter 3 completed-natural-filtration provider as cited in source imports.

import Mathlib
set_option autoImplicit false
open MeasureTheory
namespace Kyprianou.Ch09.B1
/-- Finite-order version of Definition 9.5, represented on an actual
probability space. Centring is part of the Appell definition and never
asserts the desired translated mean-value identity. -/
def IsAppellUpTo {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (n : ℕ) (Q : ℕ → ℝ → ℝ) : Prop :=
  (∀ x : ℝ, Q 0 x = 1) ∧
  (∀ k : ℕ, k < n → ∀ x : ℝ,
      deriv (Q (k + 1)) x = (k + 1 : ℝ) * Q k x) ∧
  (∀ k : ℕ, 1 ≤ k → k ≤ n →
      Integrable (fun ω => Q k (Y ω)) P ∧
      (∫ ω, Q k (Y ω) ∂P) = 0)

/-- Kyprianou (2006), Lemma 9.8, printed page 251/PDF 259:
the complete translated nth-order Appell mean-value property.
Source-faithful authoring goal; proof remains OPEN, this is not an importable
Prove2Me theorem or proof of the proposition. -/
def lemma98_appellMeanValue_Statement
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] : Prop :=
  ∀ (Y : Ω → ℝ) (hY : Measurable Y)
    (n : ℕ) (hn : 1 ≤ n)
    (hYnonneg : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (hYmoment : Integrable (fun ω => (Y ω) ^ n) P)
    (Q : ℕ → ℝ → ℝ) (hQ : IsAppellUpTo P Y n Q)
    (x : ℝ),
    (∫ ω, Q n (x + Y ω) ∂P) = x ^ n

end Kyprianou.Ch09.B1

namespace Kyprianou.Ch09

universe u

/-- Canonical full source proposition of Lemma 9.8. This declaration has
no proof and has not been published as a Prove2Me theorem. -/
noncomputable def appellMeanValue : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P],
    Kyprianou.Ch09.B1.lemma98_appellMeanValue_Statement P

/-- Logically identical cumulative-goal conjunct, generated from the
canonical parent proposition. No conclusion is inserted as a premise. -/
noncomputable def certificate_result_9_8 : Prop := appellMeanValue.{u}

/-- Kernel-level definitional parity for the sole currently authored parent. -/
theorem certificate_result_9_8_eq :
    certificate_result_9_8.{u} = appellMeanValue.{u} := rfl

end Kyprianou.Ch09


