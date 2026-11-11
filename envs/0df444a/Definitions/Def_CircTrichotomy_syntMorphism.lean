-- Prove2me | Definitions.Def_CircTrichotomy_syntMorphism
-- name    : CircTrichotomy_syntMorphism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:36.825505+00:00
-- url     : https://prove2.me/theorems/eb2c15e9-f543-4a73-a774-9366e856b448
-- title:
--   Syntactic congruence, syntactic semigroup $S(L)$ and syntactic morphism $\eta_L$
-- statement:
--   For a language $L\subseteq\Sigma^+$, the **syntactic congruence** $\sim_L$ on $\Sigma^+$ is
--   $$u\sim_L v\iff \bigl(xuy\in L\Leftrightarrow xvy\in L\ \text{ for all } x,y\in\Sigma^*\bigr).$$
--   The **syntactic semigroup** is $S(L)=\Sigma^+/{\sim_L}$, and the **syntactic morphism** $\eta_L:\Sigma^+\to S(L)$ is the canonical quotient map. For each $x\in S(L)$, $\eta_L^{-1}(x)\subseteq\Sigma^+$ is the fibre of $\eta_L$ over $x$, viewed as a language.
--
--   For regular $L$, $S(L)$ is finite and $\eta_L$ is a stamp; algebraic properties of $\eta_L$ classify the circuit complexity of $L$.
--
--   **Formalization Note** $\sim_L$ is a Mathlib `Con` on `FreeSemigroup α` and $\eta_L$ its quotient `MulHom`; finiteness of $S(L)$ for regular $L$ is a theorem, not part of the definition.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.2, p.17

import Mathlib
import Definitions.Def_CircTrichotomy_wordToList

set_option autoImplicit false

namespace CircTrichotomy

/-- **Syntactic congruence `∼_L`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.2, p.17): "the syntactic congruence ∼_L on Σ⁺ is given
by u ∼_L v if xuy ∈ L ⇔ xvy ∈ L for each x, y ∈ Σ*." -/
def syntCon {α : Type} (L : Language α) : Con (FreeSemigroup α) where
  r u v := ∀ x y : List α, x ++ wordToList u ++ y ∈ L ↔ x ++ wordToList v ++ y ∈ L
  iseqv := ⟨fun _ _ _ => Iff.rfl, fun h x y => (h x y).symm,
    fun h1 h2 x y => (h1 x y).trans (h2 x y)⟩
  mul' := by
    intro u1 v1 u2 v2 h1 h2 x y
    have e1 := h1 x (wordToList u2 ++ y)
    have e2 := h2 (x ++ wordToList v1) y
    simp only [wordToList_mul, List.append_assoc] at e1 e2 ⊢
    exact e1.trans e2

/-- **Syntactic semigroup `S(L) = Σ⁺/∼_L`** (p.17). -/
abbrev SyntSemigroup {α : Type} (L : Language α) : Type := (syntCon L).Quotient

/-- **Syntactic morphism `η_L : Σ⁺ → S(L)`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.2, p.17): "The corresponding semigroup
Σ⁺/∼_L is called the syntactic semigroup, denoted by S(L) and the canonical morphism
η_L : Σ⁺ → S(L) is called the syntactic morphism of L."

**Formalization Note** `η_L` is the quotient map of the free semigroup `FreeSemigroup α` (= α⁺)
by `∼_L`, as a semigroup morphism (`MulHom`). For a regular language `S(L)` is finite and `η_L` is
a stamp; that is a theorem, not part of the definition. -/
def syntMorphism {α : Type} (L : Language α) : FreeSemigroup α →ₙ* SyntSemigroup L where
  toFun u := (u : (syntCon L).Quotient)
  map_mul' _ _ := rfl

/-- The fibre `η_L⁻¹(x) ⊆ Σ⁺` of the syntactic morphism over `x ∈ S(L)`, as a language (p.19,
Lemma A.3). -/
def syntPreimage {α : Type} (L : Language α) (x : SyntSemigroup L) : Language α :=
  {u | ∃ z : FreeSemigroup α, wordToList z = u ∧ syntMorphism L z = x}

end CircTrichotomy


