-- Prove2me | Definitions.Def_FuzzyExtractors_ImprovedJSFull_Refinement
-- name    : FuzzyExtractors_ImprovedJSFull_Refinement
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:35:12.558565+00:00
-- url     : https://prove2.me/theorems/207e8164-02a8-470e-ad6a-6d052b3d12b2
-- title:
--   Construction 5 program refinement, failure behavior and field-symbol storage
-- statement:
--   The published coefficient sketch, high polynomial and Step 3 predicate are reused. A duplicate-free input list represents an $s$-element set regardless of order. The decoder relation searches for a polynomial of degree less than $s-t$, including zero, with doubled agreement count at least $2s-t$. It returns the distinct roots of the high polynomial minus that polynomial. If no decoding polynomial exists, or the root set has a different cardinality, the total interface returns the received set.
--
--   An executable recovery output must encode a duplicate-free list of the resulting set, satisfy the decoder relation, and agree with the published semantic recovery. These are output requirements to prove. The implementation predicate requires exact coefficient output for sketch generation and this recovery relation for every well-formed input and every $t$-symbol sketch, together with almost-sure termination and the uniform expected-time bound.
--
--   $$|F^t|=|F|^t,\qquad \log_2|F^t|\le t\log_2|F|.$$
--
--   Storage also records exactly $t$ field symbols, the binary digit encoding length, and the existence of an injective packed encoding of length $\lceil t\log_2|F|\rceil$. This distinguishes algebraic helper capacity from physical binary allocation and connects the old semantic model to the new operational model without assuming any implementation.
-- source:
--   Dodis, Ostrovsky, Reyzin and Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, arXiv:cs/0602007v4 (1 Apr 2008), https://arxiv.org/abs/cs/0602007v4, Construction 5, printed p.21 / PDF p.22; Definition 3, printed p.11 / PDF p.12; Theorem 6.1, printed p.22 / PDF p.23; storage convention also Appendix D, printed p.42 / PDF p.43

import Mathlib
import Definitions.Def_FuzzyExtractors_ImprovedJS_Basic
import Definitions.Def_FuzzyExtractors_ImprovedJSFull_Presentation

namespace FuzzyExtractors.ImprovedJSFull

open FuzzyExtractors.ImprovedJS

/-! Decoder and roots refinement for Construction 5, arXiv:cs/0602007v4,
printed p.21 / PDF 22. All cost conclusions are obligations of the goal;
none is a field of the representation or an assumed algorithm interface. -/

/-- Duplicate-free input lists represent every s-element set, in any order. -/
def Represents {F : Type} [DecidableEq F] {s : ℕ}
    (xs : List F) (w : SDifS F s) : Prop :=
  xs.Nodup ∧ xs.toFinset = w.val

/-- Full Step 3/Step 4 relation, including failure on arbitrary sketches.
The published Step3Cond uses degree < s-t (including zero), doubled agreement
threshold 2s-t, and the published pHigh. On failure or wrong root cardinality
return the received set, as in the published total semantic kernel. -/
noncomputable def DecoderRoots {F : Type} [Field F] [DecidableEq F]
    (s t : ℕ) (a : Fin t → F) (received result : SDifS F s) : Prop :=
  (¬ (∃ low, Step3Cond s t a received.val low)) ∧ result = received ∨
  ∃ low : Polynomial F, Step3Cond s t a received.val low ∧
    let roots := (pHigh s t a - low).roots.toFinset
    (roots.card = s ∧ result.val = roots) ∨ (roots.card ≠ s ∧ result = received)

/-- Exact output specification for the executable recovery. The list can be
in any order. Both the decoder relation and its connection to the existing
semantic recovery must be established, even on a mismatched sketch. -/
noncomputable def RecoveryOutput {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (P : Presentation F) (s t : ℕ) (received : SDifS F s) (a : Fin t → F)
    (out : Bits) : Prop :=
  ∃ result : SDifS F s, ∃ xs : List F,
    Represents xs result ∧ out = P.encodeList xs ∧
    DecoderRoots s t a received result ∧
    recover s t received a = PMF.pure result

/-- Algebraic capacity of exactly t field symbols. Literal binary allocation
is kept separate: a packed vector needs ceil(t log₂ n) bits, while digitwise
encoding takes t*k*ceil(log₂ p) bits. -/
noncomputable def Storage {F : Type} [Field F] [Fintype F]
    (P : Presentation F) (t : ℕ) : Prop :=
  Fintype.card (Fin t → F) = (Fintype.card F) ^ t ∧
  Real.logb 2 (Fintype.card (Fin t → F)) ≤ t * Real.logb 2 (Fintype.card F) ∧
  (∀ a : Fin t → F, (List.ofFn a).length = t ∧
    (P.encodeSketch a).length = t * P.k * P.digitWidth) ∧
  ∃ packed : (Fin t → F) → Bits,
    Function.Injective packed ∧
    ∀ a, (packed a).length = ⌈(t : ℝ) * Real.logb 2 (Fintype.card F)⌉₊

/-- Realization and cost are imposed for every well-formed received set and
all t-symbol sketches, not just honestly generated or close instances. -/
noncomputable def Implements {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (SS Rec : Program) (P : Presentation F) (C : ℝ) (d s t : ℕ) : Prop :=
  (∀ w : SDifS F s, ∀ xs : List F, Represents xs w →
    Realizes SS (P.sketchInput s t xs)
      (fun out => out = P.encodeSketch (sketchCoeffs s t w.val)) ∧
    expectedSteps SS (P.sketchInput s t xs) ≤ timeBound C d s t P.universeBits) ∧
  (∀ received : SDifS F s, ∀ xs : List F, Represents xs received →
    ∀ a : Fin t → F,
      Realizes Rec (P.recoveryInput s t xs a) (RecoveryOutput P s t received a) ∧
      expectedSteps Rec (P.recoveryInput s t xs a) ≤ timeBound C d s t P.universeBits)

end FuzzyExtractors.ImprovedJSFull


