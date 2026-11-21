-- Prove2me | Definitions.Def_AbsNe
-- name    : AbsNe
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-21T00:51:17.874104+00:00
-- url     : https://prove2.me/theorems/206a6f97-9324-449e-b64c-6e453f41fc4d
-- title:
--   M11 — AbsNe (abstract nonvanishing lemma)
-- statement:
--   M11 of the Alpöge–Claude timeline: AbsNe, the abstract nonvanishing lemma the SchurStep identity rests on. Found while reading the file (bonus item, not in the original tier-2 list). It is the most portable item in this tier — Mathlib measure theory only, no archive-private dependencies. This item is a def : Prop in the archive, NOT a theorem — the name AbsNe is the archive's name for this definition; the wrapper theorem asserting it (AlpoegeClaudeRH.M11d_AbsNe_wrapper) is ours.
--
--   Statement read from the Alpöge archive (alpo.ge, SHA-256 verified). Claim NOT verified — no independent lake build Main + #print axioms has been published. Definition stack must be ported as platform definitions first; the statement alone is not submittable as a proved item.
--
--   Dependencies — Formalpedia check, Nov 20, 2026: Measure, SFinite, Integrable, ENNReal — Mathlib measure-theory names per the extraction, but Formalpedia's title search returned 0 results for 'Measure' and did not show them as Lean definitions on the platform, so not confirmed via Formalpedia — recorded as not checked on the platform. No archive-private names appear in this statement.
-- source:
--   Alpöge archive, Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/SchurStep.lean:183-190 — https://alpo.ge

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Normed.Group.Defs

open MeasureTheory

namespace AlpoegeClaudeRH

def AbsNe : Prop :=
  ∀ (A B C : Type) [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] (μA : Measure A) (μB : Measure B) (μC : Measure C)
  [SFinite μA] [SFinite μB] [SFinite μC] (H : Set B) (K : Set C), MeasurableSet H → MeasurableSet K → μB H ≠ 0 → μB H ≠ ⊤ →
  μC K ≠ ⊤ → ∀ (f : A × B × C → ℂ) (m : A → C → ℂ) (s c₀ : C → ℂ) (κ : ℂ) (r : ℝ) (w : C → ENNReal), κ ≠ 0 → 0 < r →
  Integrable f (μA.prod (μB.prod μC)) → (∀ x b c, b ∉ H → f (x, b, c) = 0) → (∀ x c, ∀ b ∈ H, f (x, b, c) = s c * m x c) →
  (∀ c, ∫ x, m x c ∂μA = κ * c₀ c) → (∀ c ∈ K, s c = 1 ∧ c₀ c = r) → (∀ c, ‖c₀ c‖ ≤ r ∧ ‖s c‖ₑ ≤ w c) →
  ∫⁻ c in Kᶜ, w c ∂μC < μC K → ∫ y, f y ∂(μA.prod (μB.prod μC)) ≠ 0

end AlpoegeClaudeRH


