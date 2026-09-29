-- Prove2me | Definitions.Def_mme_CW_fourth_literal_support_words
-- name    : mme_CW_fourth_literal_support_words
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T19:34:19.590507+00:00
-- url     : https://prove2.me/theorems/f34d8f75-78d2-4043-9ed2-9238f3c2c99e
-- title:
--   Literal CW terms and their fourth-power addresses
-- statement:
--   This definition package gives a parameter-uniform enumeration of the literal summands of the Coppersmith--Winograd tensor $CW_q$, their three basis coordinates, and the grouped basis address of four such summands in $CW_q^{\otimes 4}$. It also chooses representatives of the six support patterns using an arbitrary middle coordinate. The package connects the abstract six-pattern combinatorics to the literal fourth tensor and is designed for reuse at both $q=6$ (Davie--Stothers) and $q=5$ (DWZ).
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Royal Soc. Edinburgh 143A (2013), Section 5, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173.

import Definitions.Def_mme_stothers_fourth_data

open MME TensorProduct PiTensorProduct

universe u

namespace MME.StothersFourth

set_option autoImplicit false

abbrev CWLiteralTerm (q : ℕ) := (Fin q × Fin 3) ⊕ Fin 3

def cwZeroIndex (q : ℕ) : Fin (q + 2) := ⟨0, by omega⟩

def cwMiddleIndex (q : ℕ) (i : Fin q) : Fin (q + 2) :=
  ⟨i.val + 1, by omega⟩

def cwTopIndex (q : ℕ) : Fin (q + 2) := ⟨q + 1, by omega⟩

def cwLiteralTermTriple (q : ℕ) :
    CWLiteralTerm q → Fin 3 → Fin (q + 2)
  | Sum.inl (_i, ⟨0, _⟩), ⟨0, _⟩ => cwZeroIndex q
  | Sum.inl (i, ⟨0, _⟩), ⟨1, _⟩ => cwMiddleIndex q i
  | Sum.inl (i, ⟨0, _⟩), ⟨2, _⟩ => cwMiddleIndex q i
  | Sum.inl (i, ⟨1, _⟩), ⟨0, _⟩ => cwMiddleIndex q i
  | Sum.inl (_i, ⟨1, _⟩), ⟨1, _⟩ => cwZeroIndex q
  | Sum.inl (i, ⟨1, _⟩), ⟨2, _⟩ => cwMiddleIndex q i
  | Sum.inl (i, ⟨2, _⟩), ⟨0, _⟩ => cwMiddleIndex q i
  | Sum.inl (i, ⟨2, _⟩), ⟨1, _⟩ => cwMiddleIndex q i
  | Sum.inl (_i, ⟨2, _⟩), ⟨2, _⟩ => cwZeroIndex q
  | Sum.inr ⟨0, _⟩, ⟨0, _⟩ => cwZeroIndex q
  | Sum.inr ⟨0, _⟩, ⟨1, _⟩ => cwZeroIndex q
  | Sum.inr ⟨0, _⟩, ⟨2, _⟩ => cwTopIndex q
  | Sum.inr ⟨1, _⟩, ⟨0, _⟩ => cwZeroIndex q
  | Sum.inr ⟨1, _⟩, ⟨1, _⟩ => cwTopIndex q
  | Sum.inr ⟨1, _⟩, ⟨2, _⟩ => cwZeroIndex q
  | Sum.inr ⟨2, _⟩, ⟨0, _⟩ => cwTopIndex q
  | Sum.inr ⟨2, _⟩, ⟨1, _⟩ => cwZeroIndex q
  | Sum.inr ⟨2, _⟩, ⟨2, _⟩ => cwZeroIndex q

noncomputable def cwLiteralTermMonomial
    (K : Type u) [Field K] (q : ℕ) (t : CWLiteralTerm q) :
    PiTensorProduct K (CWSpace K q) :=
  CWMonom K q (cwLiteralTermTriple q t 0)
    (cwLiteralTermTriple q t 1) (cwLiteralTermTriple q t 2)

def cwFourthIndexOfLiteralTerms (q : ℕ)
    (t₁ t₂ t₃ t₄ : CWLiteralTerm q) (s : Fin 3) :
    (Fin (q + 2) × Fin (q + 2)) ×
      (Fin (q + 2) × Fin (q + 2)) :=
  ((cwLiteralTermTriple q t₁ s, cwLiteralTermTriple q t₂ s),
   (cwLiteralTermTriple q t₃ s, cwLiteralTermTriple q t₄ s))

def cwCanonicalSupportTerm (q : ℕ) (i : Fin q) :
    Fin 6 → CWLiteralTerm q :=
  ![Sum.inl (i, 0), Sum.inl (i, 1), Sum.inl (i, 2),
    Sum.inr 0, Sum.inr 1, Sum.inr 2]

def cwCanonicalFourLiteralAddress (q : ℕ) (i : Fin q)
    (r : Fin 4 → Fin 6) (s : Fin 3) : Fin 9 :=
  cwFourthPairGrade q
    (cwFourthIndexOfLiteralTerms q
      (cwCanonicalSupportTerm q i (r 0))
      (cwCanonicalSupportTerm q i (r 1))
      (cwCanonicalSupportTerm q i (r 2))
      (cwCanonicalSupportTerm q i (r 3)) s)

end MME.StothersFourth


