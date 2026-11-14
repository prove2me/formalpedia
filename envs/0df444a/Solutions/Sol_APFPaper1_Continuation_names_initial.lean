-- Prove2me | solution 1 for APFPaper1.Continuation.names_initial
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:50:54.381205+00:00
-- url     : https://prove2.me/submissions/3be40909-b5d5-4468-8583-b320d933e5c5

/-
APF Foundation Ledger — theorem node. DRAFT for author and cold review. Not gated, not released, not uploaded.
name: APFPaper1.Continuation.names_laws
title: Naming laws with names equal to words
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:3188-3194 (continuation word). Author direction 4c of 2026-10-04.
consumes: no declared input.
statement: Output typing, uniqueness, the empty name, the single-fragment name and the initial-segment law, for the relation in which a word names itself.
label: BY DEFINITION OF names.
-/
import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
namespace APFPaper1.Continuation

universe uC uF uX uR
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

/-- A named process ends in the end context of its name. -/
theorem names_output {g h : Context} (word : Word Frag g h) (p : WordFrom Frag g)
    (hp : names word p) : p.1 = h := by
  have hp' : p = ⟨h, word⟩ := hp
  rw [hp']

/-- A word names at most one process. -/
theorem names_unique {g h : Context} (word : Word Frag g h) (p q : WordFrom Frag g)
    (hp : names word p) (hq : names word q) : p = q := by
  have hp' : p = ⟨h, word⟩ := hp
  have hq' : q = ⟨h, word⟩ := hq
  rw [hp', hq']

/-- The empty word names the empty process and nothing else. -/
theorem names_empty (g : Context) (p : WordFrom Frag g) :
    names (Word.nil g) p ↔ p = nullWord g := Iff.rfl

/-- A one-fragment word names the one-fragment process and nothing else. -/
theorem names_single {g h : Context} (f : Frag g h) (p : WordFrom Frag g) :
    names (Word.single f) p ↔ p = ⟨h, Word.single f⟩ := Iff.rfl

/-- The process named by a concatenation has, as an initial segment, the process named by its first part. -/
theorem names_initial {g h k : Context} (word : Word Frag g h) (v : Word Frag h k)
    (q : WordFrom Frag g) (hq : names (word.append v) q) :
    ∃ p : WordFrom Frag g, names word p ∧ IsPrefix p q := by
  have hq' : q = ⟨k, word.append v⟩ := hq
  refine ⟨⟨h, word⟩, rfl, ?_⟩
  rw [hq']
  exact ⟨v, rfl⟩

end APFPaper1.Continuation


universe uC uF
theorem solution :
∀ {Context : Type uC} {Frag : Context → Context → Type uF} {g h k : Context}
  (word : APFPaper1.Continuation.Word.{uC, uF} Frag g h) (v : APFPaper1.Continuation.Word.{uC, uF} Frag h k)
  (q : APFPaper1.Continuation.WordFrom.{uC, uF} Frag g),
  APFPaper1.Continuation.names.{uC, uF} (APFPaper1.Continuation.Word.append.{uC, uF} word v) q →
    ∃ p, APFPaper1.Continuation.names.{uC, uF} word p ∧ APFPaper1.Continuation.IsPrefix.{uC, uF} p q := by
  exact @APFPaper1.Continuation.names_initial
