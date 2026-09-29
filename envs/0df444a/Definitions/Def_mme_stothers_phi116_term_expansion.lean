-- Prove2me | Definitions.Def_mme_stothers_phi116_term_expansion
-- name    : mme_stothers_phi116_term_expansion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T19:45:35.575896+00:00
-- url     : https://prove2.me/theorems/827fca6b-a0ee-42d1-a6a4-bca37216b919
-- title:
--   Canonical finite-term expansion data for the phi_116 support proof
-- statement:
--   Index the $3q+3$ canonical rank-one monomials of the Coppersmith--Winograd tensor $CW_q$ by the finite type $(\{0,\ldots,q-1\}\times\{0,1,2\})\sqcup\{0,1,2\}$. For each index, record its three coordinate labels and the corresponding pure tensor.
--
--   The first $3q$ labels represent the three cyclic placements of the middle coordinates; the last three represent the exceptional $(0,0,q+1)$ terms and their cyclic rotations. This explicit finite indexing is used to expand $CW_6^{\otimes4}$ term by term and verify the support of the literal $\varphi_{116}$ outer grading.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions (1990), definition of the basic tensor, journal p. 254, https://www.sciencedirect.com/science/article/pii/S0747717108800132; A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi116_outer_grading

open MME

universe u

namespace MME.StothersFourth.Phi116

set_option autoImplicit false

def cwO (q : ℕ) : Fin (q + 2) := ⟨0, by omega⟩

def cwM (q : ℕ) (i : Fin q) : Fin (q + 2) := ⟨i.val + 1, by omega⟩

def cwT (q : ℕ) : Fin (q + 2) := ⟨q + 1, by omega⟩

/-- Coordinate triples occurring in one canonical CW rank-one monomial. -/
def cwSupportedTriple (q : ℕ)
    (a b c : Fin (q + 2)) : Prop :=
  (∃ i : Fin q, a = cwO q ∧ b = cwM q i ∧ c = cwM q i) ∨
  (∃ i : Fin q, a = cwM q i ∧ b = cwO q ∧ c = cwM q i) ∨
  (∃ i : Fin q, a = cwM q i ∧ b = cwM q i ∧ c = cwO q) ∨
  (a = cwO q ∧ b = cwO q ∧ c = cwT q) ∨
  (a = cwO q ∧ b = cwT q ∧ c = cwO q) ∨
  (a = cwT q ∧ b = cwO q ∧ c = cwO q)

/-- Finite labels for the $3q+3$ canonical terms of `CW_q`. -/
abbrev CWTerm (q : ℕ) := (Fin q × Fin 3) ⊕ Fin 3

/-- The three coordinate labels of one canonical CW term. -/
def cwTermTriple (q : ℕ) : CWTerm q → Fin 3 → Fin (q + 2)
  | Sum.inl (_i, ⟨0, _⟩), ⟨0, _⟩ => cwO q
  | Sum.inl (i, ⟨0, _⟩), ⟨1, _⟩ => cwM q i
  | Sum.inl (i, ⟨0, _⟩), ⟨2, _⟩ => cwM q i
  | Sum.inl (i, ⟨1, _⟩), ⟨0, _⟩ => cwM q i
  | Sum.inl (_i, ⟨1, _⟩), ⟨1, _⟩ => cwO q
  | Sum.inl (i, ⟨1, _⟩), ⟨2, _⟩ => cwM q i
  | Sum.inl (i, ⟨2, _⟩), ⟨0, _⟩ => cwM q i
  | Sum.inl (i, ⟨2, _⟩), ⟨1, _⟩ => cwM q i
  | Sum.inl (_i, ⟨2, _⟩), ⟨2, _⟩ => cwO q
  | Sum.inr ⟨0, _⟩, ⟨0, _⟩ => cwO q
  | Sum.inr ⟨0, _⟩, ⟨1, _⟩ => cwO q
  | Sum.inr ⟨0, _⟩, ⟨2, _⟩ => cwT q
  | Sum.inr ⟨1, _⟩, ⟨0, _⟩ => cwO q
  | Sum.inr ⟨1, _⟩, ⟨1, _⟩ => cwT q
  | Sum.inr ⟨1, _⟩, ⟨2, _⟩ => cwO q
  | Sum.inr ⟨2, _⟩, ⟨0, _⟩ => cwT q
  | Sum.inr ⟨2, _⟩, ⟨1, _⟩ => cwO q
  | Sum.inr ⟨2, _⟩, ⟨2, _⟩ => cwO q

/-- The canonical rank-one monomial indexed by a `CWTerm`. -/
noncomputable def cwTermMonom
    (K : Type u) [Field K] (q : ℕ) (t : CWTerm q) :
    PiTensorProduct K (CWSpace K q) :=
  CWMonom K q (cwTermTriple q t 0) (cwTermTriple q t 1)
    (cwTermTriple q t 2)

end MME.StothersFourth.Phi116


