-- Prove2me | Definitions.Def_FixpReciprocal_frame
-- name    : FixpReciprocal_frame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:45:29.114359+00:00
-- url     : https://prove2.me/theorems/3429162b-1cac-4bef-8db5-f9788854e042
-- title:
--   Self-delimiting binary encodings of naturals, rationals and lists
-- statement:
--   This item fixes how nested instance data is written as a word over the four-letter alphabet $\mathrm{Sym}$. A word $w$ is **framed** by replacing each symbol $s$ with the pair $3,s$ and appending the end marker $0$. A natural number is framed from its binary expansion, a rational from its binary reduced numerator and denominator, and a list is written as its framed length followed by its items.
--
--   The file proves that these encodings are **prefix-free**, so a concatenation decodes uniquely and every encoded instance determines the instance. Numbers stay in binary, and framing multiplies lengths by $2$ at each of the constantly many nesting levels, so an input's length is proportional to its bit length as the paper measures it.
--
--   **Formalization Note** This is a Lean convention needed to read "polynomial time" as Mathlib's `Turing.TM2ComputableInPolyTime`. The separate framing is required because `encNat 0` is the empty word.
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), §3, p.10 (PDF p.12): "Rational inputs use binary numerators and denominators; input size is the total bit length of the instance description."

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat

namespace FixpReciprocal

open OnlineCRS.Combine

/-- **Self-delimiting framing of a word over `Sym`.** Each symbol `s` becomes `3, s`; the symbol `0`
ends the word. Doubling the length this way is what lets nested data (lists of rows of rationals)
be written in the fixed four-letter alphabet, since `encNat 0` is the empty word.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), §3, p.10: "Rational inputs use binary numerators and denominators; input size is the total
bit length of the instance description."

**Formalization Note.** The instance encodings of this mission are a Lean convention of the reading
of "polynomial time" as Mathlib's `Turing.TM2ComputableInPolyTime`. Numbers stay binary, and framing
multiplies lengths by a constant at each of the constantly many nesting levels. -/
def frame (w : List Sym) : List Sym := w.flatMap (fun s => [3, s]) ++ [0]

theorem frame_append_inj {a b s t : List Sym} (h : frame a ++ s = frame b ++ t) :
    a = b ∧ s = t := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simpa [frame] using h
    | cons y b => simp [frame] at h
  | cons x a ih =>
    cases b with
    | nil => simp [frame] at h
    | cons y b =>
      simp only [frame, List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc,
        List.cons.injEq, true_and] at h
      obtain ⟨rfl, h⟩ := h
      have := ih (b := b) (by simpa [frame, List.append_assoc] using h)
      exact ⟨by rw [this.1], this.2⟩

/-- An encoding no value of which is a proper prefix of another's: concatenations decode uniquely. -/
def PrefixFree {α : Type} (e : α → List Sym) : Prop :=
  ∀ ⦃a b : α⦄ ⦃s t : List Sym⦄, e a ++ s = e b ++ t → a = b ∧ s = t

theorem PrefixFree.injective {α : Type} {e : α → List Sym} (h : PrefixFree e) :
    Function.Injective e := fun _ _ hab =>
  (@h _ _ [] [] (by simpa using hab)).1

theorem PrefixFree.comp_injective {α β : Type} {e : β → List Sym} (h : PrefixFree e) {f : α → β}
    (hf : Function.Injective f) : PrefixFree (fun a => e (f a)) := fun _ _ _ _ hh => by
  obtain ⟨h1, h2⟩ := h hh
  exact ⟨hf h1, h2⟩

theorem encNat_injective : Function.Injective encNat := by
  intro a b h
  have hbit : Function.Injective bit := by
    intro x y hxy
    cases x <;> cases y <;> first | rfl | (simp [bit] at hxy)
  have h' := List.map_injective_iff.mpr hbit h
  have := congrArg Computability.decodeNat h'
  simpa using this

theorem encInt_injective : Function.Injective encInt := by
  intro a b h
  simp only [encInt, List.cons.injEq] at h
  have h2 := encNat_injective h.2
  have h1 : decide (a < 0) = decide (b < 0) := by
    have := h.1
    revert this
    cases decide (a < 0) <;> cases decide (b < 0) <;> simp [bit]
  have h1' : a < 0 ↔ b < 0 := by simpa using h1
  omega

theorem two_notMem_encNat (n : ℕ) : (2 : Sym) ∉ encNat n := by
  simp only [encNat, List.mem_map, not_exists, not_and]
  intro b _
  cases b <;> simp [bit]

theorem two_notMem_encInt (z : ℤ) : (2 : Sym) ∉ encInt z := by
  simp only [encInt, List.mem_cons, not_or]
  refine ⟨?_, two_notMem_encNat _⟩
  cases h : decide (z < 0) <;> simp [bit]

theorem split_at_two {u v s t : List Sym} (hu : (2 : Sym) ∉ u) (hv : (2 : Sym) ∉ v)
    (h : u ++ 2 :: s = v ++ 2 :: t) : u = v ∧ s = t := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => simpa using h
    | cons y v =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hv
  | cons x u ih =>
    cases v with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hu
    | cons y v =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have := ih (fun m => hu (List.mem_cons_of_mem _ m)) (fun m => hv (List.mem_cons_of_mem _ m)) h
      exact ⟨by rw [this.1], this.2⟩

theorem encRat_injective : Function.Injective encRat := by
  intro a b h
  simp only [encRat, List.append_assoc, List.cons_append, List.nil_append] at h
  obtain ⟨h1, h2⟩ := split_at_two (two_notMem_encInt _) (two_notMem_encInt _) h
  exact Rat.ext (encInt_injective h1) (encNat_injective h2)

/-- A framed binary natural number. -/
def fNat (n : ℕ) : List Sym := frame (encNat n)

/-- A framed rational, with binary reduced numerator and denominator (`encRat`). -/
def fRat (q : ℚ) : List Sym := frame (encRat q)

/-- A list: its framed length, then the items. -/
def fList {α : Type} (e : α → List Sym) (l : List α) : List Sym :=
  fNat l.length ++ l.flatMap e

theorem fNat_prefixFree : PrefixFree fNat := fun _ _ _ _ h => by
  obtain ⟨h1, h2⟩ := frame_append_inj h
  exact ⟨encNat_injective h1, h2⟩

theorem fRat_prefixFree : PrefixFree fRat := fun _ _ _ _ h => by
  obtain ⟨h1, h2⟩ := frame_append_inj h
  exact ⟨encRat_injective h1, h2⟩

theorem PrefixFree.fList {α : Type} {e : α → List Sym} (he : PrefixFree e) :
    PrefixFree (FixpReciprocal.fList e) := by
  have aux : ∀ (l l' : List α) (s t : List Sym), l.length = l'.length →
      l.flatMap e ++ s = l'.flatMap e ++ t → l = l' ∧ s = t := by
    intro l
    induction l with
    | nil =>
      intro l' s t hlen h
      cases l' with
      | nil => simpa using h
      | cons _ _ => simp at hlen
    | cons x l ih =>
      intro l' s t hlen h
      cases l' with
      | nil => simp at hlen
      | cons y l' =>
        simp only [List.flatMap_cons, List.append_assoc] at h
        obtain ⟨rfl, h'⟩ := he h
        have := ih l' s t (by simpa using hlen) h'
        exact ⟨by rw [this.1], this.2⟩
  intro l l' s t h
  simp only [FixpReciprocal.fList, List.append_assoc] at h
  obtain ⟨hlen, h⟩ := fNat_prefixFree h
  exact aux l l' s t hlen h

end FixpReciprocal


