-- Prove2me | Definitions.Def_lemma_2_1_data
-- name    : lemma_2_1_data
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-12T19:38:53.606265+00:00
-- url     : https://prove2.me/theorems/826ec7a0-0a55-403c-be5a-215d90def758
-- title:
--   Lemma 2.1 data: the diagonal/second-factor subgroups of G×G and their swap isomorphism
-- statement:
--   Supporting data for the preprint's Lemma 2.1: the diagonal subgroup $A = \{(g,g) : g \in G\}$ and second-factor subgroup $B = \{(1,g) : g \in G\}$ of $G \times G$, together with the isomorphism $\varphi : A \to B$, $(g,g) \mapsto (1,g)$, used to form the HNN extension $\hat G = \mathrm{HNN}(G \times G, A, B, \varphi)$.
-- source:
--   OpenAI, *Finite algebraic envelopes and the Boone–Higman conjecture*, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026/paper.pdf, Lemma 2.1, p. 3.

import Mathlib

namespace OAI
namespace FiniteAlgebraicEnvelopes

universe u

variable (G : Type u) [Group G]

/-- The diagonal subgroup `{(g,g) : g ∈ G}` of `G × G`, called `A` in Lemma 2.1. -/
def diagonalSubgroup : Subgroup (G × G) where
  carrier := {p | p.1 = p.2}
  one_mem' := rfl
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *; rw [Prod.fst_mul, Prod.snd_mul, ha, hb]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *; rw [Prod.fst_inv, Prod.snd_inv, ha]

/-- The second-factor subgroup `{(1,g) : g ∈ G}` of `G × G`, called `B` in Lemma 2.1. -/
def secondFactorSubgroup : Subgroup (G × G) where
  carrier := {p | p.1 = 1}
  one_mem' := rfl
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *; rw [Prod.fst_mul, ha, hb, one_mul]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *; rw [Prod.fst_inv, ha, inv_one]

@[simp] theorem mem_diagonalSubgroup (p : G × G) : p ∈ diagonalSubgroup G ↔ p.1 = p.2 := Iff.rfl

@[simp] theorem mem_secondFactorSubgroup (p : G × G) : p ∈ secondFactorSubgroup G ↔ p.1 = 1 :=
  Iff.rfl

/-- The isomorphism `A ≃* B` from Lemma 2.1, sending `(g,g) ↦ (1,g)`. -/
def diagonalEquivSecondFactor : diagonalSubgroup G ≃* secondFactorSubgroup G where
  toFun x := ⟨(1, x.1.2), by simp⟩
  invFun y := ⟨(y.1.2, y.1.2), by simp⟩
  left_inv x := by
    ext
    · exact x.2.symm
    · rfl
  right_inv y := by
    ext
    · exact y.2.symm
    · rfl
  map_mul' x y := by
    ext
    · simp
    · rfl

theorem diagonalEquivSecondFactor_apply (g : G) :
    (diagonalEquivSecondFactor G ⟨(g, g), rfl⟩ : G × G) = (1, g) := rfl

end FiniteAlgebraicEnvelopes
end OAI


