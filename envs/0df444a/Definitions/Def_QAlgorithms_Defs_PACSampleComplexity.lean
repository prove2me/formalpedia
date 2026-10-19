-- Prove2me | Definitions.Def_QAlgorithms_Defs_PACSampleComplexity
-- name    : QAlgorithms_Defs_PACSampleComplexity
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:52:53.647511+00:00
-- url     : https://prove2.me/theorems/bcf8e693-43b7-44a1-b7ff-8e735b6f483a
-- title:
--   Shattering, VC dimension, PAC learners and PAC sample complexity on a measurable instance space
-- statement:
--   # Shattering, VC dimension, PAC learners and PAC sample complexity on a measurable instance space
--   (shared definition layer)
--
--   S. Hanneke, *The optimal sample complexity of PAC learning* (arXiv:1507.00473v4), cited
--   "Hanneke p.N" (PDF pages), §2.
--
--   Conventions. The instance space is an arbitrary measurable space `X`; the label space
--   `Y = {−1, +1}` is `Bool`; a classifier is `h : X → Bool` (measurable where the source requires it);
--   a concept class is a `Set (X → Bool)`. Probabilities of events are Mathlib measures in `ℝ≥0∞`.
--   -/
--
--   namespace QAlgorithms.Learning
--
--   open MeasureTheory
--   open scoped ENNReal
--
--   /-- Hanneke §2 (p.2): `C` shatters the finite point set `s`: every labelling of `s` is realized
--   by some classifier of `C`.
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\PACSampleComplexity.lean

import Definitions.Def_QAlgorithms_Defs_LearningSeparation
/-!
# Shattering, VC dimension, PAC learners and PAC sample complexity on a measurable instance space
(shared definition layer)

S. Hanneke, *The optimal sample complexity of PAC learning* (arXiv:1507.00473v4), cited
"Hanneke p.N" (PDF pages), §2.

Conventions. The instance space is an arbitrary measurable space `X`; the label space
`Y = {−1, +1}` is `Bool`; a classifier is `h : X → Bool` (measurable where the source requires it);
a concept class is a `Set (X → Bool)`. Probabilities of events are Mathlib measures in `ℝ≥0∞`.
-/

namespace QAlgorithms.Learning

open MeasureTheory
open scoped ENNReal

/-- Hanneke §2 (p.2): `C` shatters the finite point set `s`: every labelling of `s` is realized
by some classifier of `C`. -/
def ShattersSet {X : Type*} (C : Set (X → Bool)) (s : Finset X) : Prop :=
  ∀ y : s → Bool, ∃ h ∈ C, ∀ x : s, h x = y x

/-- Hanneke §2 (p.2): the VC dimension of `C`, the largest size of a shattered set, `⊤` when there
is no largest one (the source's `d = ∞`). -/
noncomputable def vcDimSet {X : Type*} (C : Set (X → Bool)) : ℕ∞ :=
  ⨆ (s : Finset X) (_ : ShattersSet C s), (s.card : ℕ∞)

/-- Hanneke §2 (p.2): the error rate `er_P(h; f⋆) = P(x : h(x) ≠ f⋆(x))`. -/
noncomputable def errRate {X : Type*} [MeasurableSpace X] (P : Measure X) (h f : X → Bool) : ℝ≥0∞ :=
  P {x | h x ≠ f x}

/-- Hanneke Definition 1 with footnote 2 (p.2): `A` is an `(ε, δ)`-PAC learner for `C` from `m`
examples: a randomized algorithm (internal randomness `ω ∼ ρ`, independent of the data) mapping
`m` labelled examples to a measurable classifier, such that for every data distribution `P` and
every target `f⋆ ∈ C`, `P(er_P(ĥ; f⋆) ≤ ε) ≥ 1 − δ` for `ĥ = A((X_{1:m}, f⋆(X_{1:m})))`, the
`X_i` i.i.d. `P`. Stated as: the (outer) measure of the failure event is at most `δ`. -/
def IsMeasPACLearner {X : Type*} [MeasurableSpace X] (C : Set (X → Bool)) (ε δ : ℝ) (m : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (A : (Fin m → X × Bool) → Ω → X → Bool) : Prop :=
  (∀ s ω, Measurable (A s ω)) ∧
    ∀ (P : Measure X) [IsProbabilityMeasure P], ∀ f ∈ C,
      ((Measure.pi fun _ : Fin m => P).prod ρ)
        {q | ENNReal.ofReal ε < errRate P (A (fun i => (q.1 i, f (q.1 i))) q.2) f} ≤
        ENNReal.ofReal δ

/-- Hanneke Definition 1 (p.2): the sample complexity `M(ε, δ)` of `(ε, δ)`-PAC learning `C`, the
smallest `m` admitting an `(ε, δ)`-PAC learner from `m` examples (`⊤` if there is none). -/
noncomputable def pacSampleComplexity {X : Type*} [MeasurableSpace X] (C : Set (X → Bool))
    (ε δ : ℝ) : ℕ∞ :=
  sInf {k : ℕ∞ | ∃ m : ℕ, k = m ∧ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (ρ : Measure Ω)
    (_ : IsProbabilityMeasure ρ) (A : (Fin m → X × Bool) → Ω → X → Bool),
    IsMeasPACLearner C ε δ m ρ A}

/-- Hanneke §2 (p.3): `Log(z) = ln(max{z, e})`. -/
noncomputable def logE (z : ℝ) : ℝ :=
  Real.log (max z (Real.exp 1))

/-- Hanneke §2 (p.3), the standing assumption "the events appearing in probability claims below
are indeed measurable", at the events where it is used (Lemma 4, p.8): for every distribution, target
and sample size, the event "some classifier of `C` consistent with the sample has error rate above
`r`" is measurable. -/
def ConsistentEventsMeasurable {X : Type*} [MeasurableSpace X] (C : Set (X → Bool)) : Prop :=
  ∀ (P : Measure X) [IsProbabilityMeasure P], ∀ f ∈ C, ∀ (m : ℕ) (r : ℝ),
    MeasurableSet {xs : Fin m → X | ∃ h ∈ C, (∀ i, h (xs i) = f (xs i)) ∧
      ENNReal.ofReal r < errRate P h f}

/-! ### Sanity tests -/

example {X : Type*} (C : Set (X → Bool)) (h : C.Nonempty) : ShattersSet C ∅ := by
  obtain ⟨c, hc⟩ := h
  exact fun _ => ⟨c, hc, fun x => absurd x.2 (Finset.notMem_empty _)⟩

example {X : Type*} : vcDimSet (∅ : Set (X → Bool)) = 0 := by
  refine le_antisymm (iSup₂_le fun s hs => ?_) bot_le
  obtain ⟨h, hh, -⟩ := hs fun _ => true
  exact absurd hh (Set.notMem_empty h)

example {X : Type*} [MeasurableSpace X] (P : Measure X) (h : X → Bool) : errRate P h h = 0 := by
  simp [errRate]

example : logE 0 = 1 := by
  rw [logE, max_eq_right (Real.exp_pos 1).le, Real.log_exp]

example {X : Type*} [MeasurableSpace X] (C : Set (X → Bool)) (ε δ : ℝ) (m : ℕ) {Ω : Type}
    [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (A : (Fin m → X × Bool) → Ω → X → Bool) (hA : IsMeasPACLearner C ε δ m ρ A) :
    pacSampleComplexity C ε δ ≤ m :=
  sInf_le ⟨m, rfl, Ω, inferInstance, ρ, inferInstance, A, hA⟩

end QAlgorithms.Learning


