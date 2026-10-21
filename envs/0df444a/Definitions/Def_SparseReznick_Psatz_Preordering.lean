-- Prove2me | Definitions.Def_SparseReznick_Psatz_Preordering
-- name    : SparseReznick_Psatz_Preordering
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:08.916867+00:00
-- url     : https://prove2.me/theorems/6b016cfb-f5fb-4808-a461-a239a9cbf639
-- title:
--   Preordering, Sper and arithmetic boundedness, p. 9
-- statement:
--   For a commutative ring $A$, a preordering $T$ contains every square and is closed under addition and multiplication. Its real spectrum here is the set of ring homomorphisms $A\to\mathbb R$ that take nonnegative values on $T$. Arithmetic boundedness means that every $h\in A$ admits a natural number $K$ for which both $K+h$ and $K-h$ belong to $T$.
--
--   $$\operatorname{Sper}_T A=\{\varphi:A\to\mathbb R:\varphi(T)\subseteq\mathbb R_{\ge0}\},\qquad A=H'(A).$$
--
--   These notions state Lemma 3.1 in its ring-wide setting. The preordering definition permits the whole ring as a preordering, as in the source.
-- source:
--   Mai, Magron & Lasserre, A sparse version of Reznick’s Positivstellensatz, arXiv:2002.05101v2, p. 9, preordering, Sper_T A, and H′(A)

import Mathlib

namespace SparseReznick.Psatz

structure Preordering (A : Type*) [CommRing A] where
  carrier : Set A
  sq_mem : ∀ a : A, a * a ∈ carrier
  add_mem : ∀ {a b : A}, a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  mul_mem : ∀ {a b : A}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier

def Sper {A : Type*} [CommRing A] (T : Preordering A) : Set (A →+* ℝ) :=
  {φ | ∀ t ∈ T.carrier, 0 ≤ φ t}

def IsArithBounded {A : Type*} [CommRing A] (T : Preordering A) : Prop :=
  ∀ h : A, ∃ K : ℕ, (K : A) + h ∈ T.carrier ∧ (K : A) - h ∈ T.carrier

end SparseReznick.Psatz


