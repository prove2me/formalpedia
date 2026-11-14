-- Prove2me | Definitions.Def_BuhaiPapers_Background_Encoding
-- name    : BuhaiPapers_Background_Encoding
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:06.309045+00:00
-- url     : https://prove2.me/theorems/872c8e2e-687f-4bdd-aaac-33180e81d26b
-- title:
--   Background.Encoding — Encodings as bit strings
-- statement:
--   This is module `Background.Encoding`, shared background material of the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0), published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) uses it.
--
--   Injective encodings of the data that algorithms read and write, for stating results about Turing
--   machines (CSLib's `Turing.MultiTapeTM.ComputableInTimeAndSpace` takes encodings `α ↪ List Bool`).
--
--   * `Encoding.frame`: a self-delimiting copy of a bit string.
--   * `Encoding.encPair`, `Encoding.encList`: pairs and lists.
--   * `Encoding.encNat`, `Encoding.encUnary`, `Encoding.encInt`, `Encoding.encRat`,
--     `Encoding.encBool`, `Encoding.encBits`: numbers (in binary and in unary), bits and bit
--     strings.
--
--   The definitions of frames, pairs, lists, natural numbers and bits are adapted from complexitylib's
--   independent comparator statements, `ComplexityComparator.SAT.Statements` (Apache-2.0; authors
--   Christian Reitwiessner, Samuel Schlesinger).
--
--   **Contents.** The module is published as a whole: 14 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BuhaiPapers_Background_Encoding`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Background/Encoding.lean

module

public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Rat.Defs

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `Background.Encoding` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Encodings as bit strings

Injective encodings of the data that algorithms read and write, for stating results about Turing
machines (CSLib's `Turing.MultiTapeTM.ComputableInTimeAndSpace` takes encodings `α ↪ List Bool`).

* `Encoding.frame`: a self-delimiting copy of a bit string.
* `Encoding.encPair`, `Encoding.encList`: pairs and lists.
* `Encoding.encNat`, `Encoding.encUnary`, `Encoding.encInt`, `Encoding.encRat`,
  `Encoding.encBool`, `Encoding.encBits`: numbers (in binary and in unary), bits and bit
  strings.

The definitions of frames, pairs, lists, natural numbers and bits are adapted from complexitylib's
independent comparator statements, `ComplexityComparator.SAT.Statements` (Apache-2.0; authors
Christian Reitwiessner, Samuel Schlesinger).
-/

@[expose] public section

namespace Encoding

/-- A self-delimiting copy of a bit string: each bit `b` becomes `true, b`, then `false` ends the
frame. -/
def frame (w : List Bool) : List Bool := w.flatMap (fun b ↦ [true, b]) ++ [false]

/-- The bits of a frame at the start of a string. -/
def unframe : List Bool → List Bool
  | true :: b :: v => b :: unframe v
  | _ => []

/-- What follows a frame at the start of a string. -/
def dropFrame : List Bool → List Bool
  | true :: _ :: v => dropFrame v
  | false :: v => v
  | _ => []

theorem unframe_frame_append (w u : List Bool) : unframe (frame w ++ u) = w := by
  induction w <;> simp_all [frame, unframe]

theorem dropFrame_frame_append (w u : List Bool) : dropFrame (frame w ++ u) = u := by
  induction w <;> simp_all [frame, dropFrame]

theorem frame_append_inj {w w' u u' : List Bool} (h : frame w ++ u = frame w' ++ u') :
    w = w' ∧ u = u' :=
  ⟨by simpa [unframe_frame_append] using congrArg unframe h,
    by simpa [dropFrame_frame_append] using congrArg dropFrame h⟩

/-- A pair: the first component framed, followed by the second. -/
def encPair {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) : α × β ↪ List Bool :=
  ⟨fun p ↦ frame (a p.1) ++ b p.2, fun _ _ h ↦
    Prod.ext (a.injective (frame_append_inj h).1) (b.injective (frame_append_inj h).2)⟩

/-- A list: its elements, each framed, one after the other. -/
def encList {α : Type} (enc : α ↪ List Bool) : List α ↪ List Bool :=
  ⟨fun l ↦ l.flatMap (frame ∘ enc), fun l l' h ↦ by
    induction l generalizing l' with
    | nil => cases l' <;> simp_all [frame]
    | cons a l ih =>
      cases l' with
      | nil => simp [frame] at h
      | cons a' l' =>
        simp only [List.flatMap_cons, Function.comp_apply] at h
        rw [enc.injective (frame_append_inj h).1, ih _ (frame_append_inj h).2]⟩

/-- A natural number in binary, least significant bit first. -/
def encNat : ℕ ↪ List Bool :=
  ⟨Nat.bits, fun m n h ↦ Nat.eq_of_testBit_eq fun i ↦ by simp [Nat.testBit_eq_inth, h]⟩

/-- A natural number in unary: `n` ones. Its length is `n`, so an algorithm reading it may take
time polynomial in `n`. -/
def encUnary : ℕ ↪ List Bool :=
  ⟨fun n ↦ List.replicate n true, fun m n h ↦ by simpa using congrArg List.length h⟩

/-- An integer: its sign (`true` for negative), then its absolute value in binary. -/
def encInt : ℤ ↪ List Bool :=
  ⟨fun z ↦ decide (z < 0) :: encNat z.natAbs, fun a b h ↦ by
    simp only [List.cons.injEq, decide_eq_decide] at h
    have hn : a.natAbs = b.natAbs := encNat.injective h.2
    rcases Int.natAbs_eq_natAbs_iff.1 hn with h' | h'
    · exact h'
    · have := h.1
      omega⟩

/-- A rational number in lowest terms: its numerator, framed, then its denominator. -/
def encRat : ℚ ↪ List Bool :=
  ⟨fun q ↦ encPair encInt encNat (q.num, q.den), fun a b h ↦ by
    have := (encPair encInt encNat).injective h
    simp only [Prod.mk.injEq] at this
    exact Rat.ext this.1 this.2⟩

/-- A bit. -/
def encBool : Bool ↪ List Bool := ⟨fun b ↦ [b], fun _ _ h ↦ by injection h⟩

/-- A bit string, as itself. -/
def encBits : List Bool ↪ List Bool := Function.Embedding.refl _

end Encoding


