-- Prove2me | Definitions.Def_CircTrichotomy_L1Form
-- name    : CircTrichotomy_L1Form
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:01:30.011021+00:00
-- url     : https://prove2.me/theorems/89627f68-7ab9-438d-87b5-e103e6af26bc
-- title:
--   The Lindström one-variable fragment $\mathcal L^1[\mathcal Q,\tau]$ and definability
-- statement:
--   A $k$-ary numerical **Lindström quantifier** $Q$ is given by its denotations $Q^n$, sets of $k$-ary relations on $[0,n-1]$, one for each word length $n$. The formula $Q\,x_0\cdots x_{k-1}[\phi_0,\dots,\phi_{k-1}]$ holds on $w$ iff
--   $$\phi_0^{w}\times\cdots\times\phi_{k-1}^{w}\in Q^{|w|},$$
--   where $\phi_i^w$ is the set of positions satisfying $\phi_i$. The **one-variable fragment** $\mathcal L^1[\mathcal Q,\tau]$ consists of the atomic formulas over $\tau$ with at most one variable, the quantified formulas $Q\,x_0\cdots x_{k-1}[\phi_0,\dots,\phi_{k-1}]$ with $Q\in\mathcal Q$ and each $\phi_i$ having free variables among $\{x_i\}$, and their Boolean combinations with at most one free variable. Every quantified formula is a sentence.
--
--   **Formalization Note** All formulas are written in one variable $x$; the quantifier binds $x$ in its $i$-th argument as $x_i$ (renaming bound variables changes nothing).
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition B.14 and (66), p.27

import Mathlib
import Definitions.Def_CircTrichotomy_FO1Form

set_option autoImplicit false

namespace CircTrichotomy

/-- Formulas of the **Lindström one-variable fragment `L¹[𝒬, τ]`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition B.14, p.27):
"The one-variable fragment of L[𝒬, τ], denoted by L¹[𝒬, τ], is the smallest set of formulas
satisfying the following conditions:
• Every atomic formula over τ using at most one variable belongs to L¹[𝒬, τ].
• Let {x₀, …, x_{k−1}} be a set of pairwise distinct variables and let ϕ₀, …, ϕ_{k−1} ∈ L¹[𝒬, τ] be
  such that the set of free variables of ϕ_i is a subset of {x_i} for i ∈ [0, k − 1]. If Q ∈ 𝒬 is a
  k-ary quantifier then Q x₀ … x_{k−1} [ϕ₀, …, ϕ_{k−1}] ∈ L¹[𝒬, τ].
• If ϕ, ψ are in L¹[𝒬, τ] and the resulting formula has at most one free variable, then ¬ϕ, ϕ ∨ ψ
  and ϕ ∧ ψ are in L¹[𝒬, τ]."

A `k`-ary numerical Lindström quantifier is given by its denotations `Q n`, a set of `k`-ary
relations on `[0, n − 1]` for each word length `n` (p.27: "A Lindström quantifier Q is numerical if
its denotation Q^w on a word w depends only on the length of the word w").

**Formalization Note** Every formula has at most one free variable, so all argument formulas are
written in the one variable `x`; the quantifier `quant k Q args` binds `x` in the `i`-th argument as
its `x_i`. Renaming bound variables changes no semantics. Atoms are `P_a(t)`, `R(t₀, …)` and `t = t′`
with terms `x` or constants. -/
inductive L1Form (α : Type) where
  /-- the letter predicate `P_a(t)` -/
  | letter (a : α) (t : NTerm)
  /-- a numerical predicate applied to terms -/
  | rel (R : Σ r : ℕ, ℕ → (Fin r → ℕ) → Prop) (args : Fin R.1 → NTerm)
  /-- equality of terms -/
  | eq (t t' : NTerm)
  /-- `Q x₀ … x_{k−1} [ϕ₀, …, ϕ_{k−1}]` for a `k`-ary numerical quantifier with denotations `Q n` -/
  | quant (k : ℕ) (Q : ℕ → Set (Set (Fin k → ℕ))) (args : Fin k → L1Form α)
  | neg (φ : L1Form α)
  | or (φ ψ : L1Form α)
  | and (φ ψ : L1Form α)

/-- Satisfaction (§A.5, p.20; (66), p.27): "w, I ⊨ φ iff ∏_{i=0}^{k−1} ϕ_i^{w,I} ∈ Q^{w,I}", where
`ϕ_i^w ⊆ [0, |w| − 1]` is the set of positions satisfying `ϕ_i` and the product is the `k`-ary relation
`ϕ₀^w × ⋯ × ϕ_{k−1}^w`. -/
def L1Form.Sat {α : Type} (w : List α) : L1Form α → ℕ → Prop
  | letter a t, x => w[t.eval w.length x]? = some a
  | rel R args, x => R.2 w.length (fun i => (args i).eval w.length x)
  | eq t t', x => t.eval w.length x = t'.eval w.length x
  | quant k Q args, _ =>
      {p : Fin k → ℕ | ∀ i, p i < w.length ∧ (args i).Sat w (p i)} ∈ Q w.length
  | neg φ, x => ¬ φ.Sat w x
  | or φ ψ, x => φ.Sat w x ∨ ψ.Sat w x
  | and φ ψ, x => φ.Sat w x ∧ ψ.Sat w x

/-- `φ` is a sentence: the variable `x` has no free occurrence (a quantified formula is a sentence,
p.27). -/
def L1Form.IsSentence {α : Type} : L1Form α → Prop
  | letter _ t => t.IsClosed
  | rel _ args => ∀ i, (args i).IsClosed
  | eq t t' => t.IsClosed ∧ t'.IsClosed
  | quant _ _ _ => True
  | neg φ => φ.IsSentence
  | or φ ψ => φ.IsSentence ∧ ψ.IsSentence
  | and φ ψ => φ.IsSentence ∧ ψ.IsSentence

/-- `φ ∈ L¹[𝒬, Σ, V]`: every constant and predicate of `φ` is in `V` and every `k`-ary quantifier of `φ`
is in `Qs k`. -/
def L1Form.InFragment {α : Type} (V : Vocab)
    (Qs : (k : ℕ) → Set (ℕ → Set (Set (Fin k → ℕ)))) : L1Form α → Prop
  | letter _ t => t.InVocab V
  | rel R args => R ∈ V.rels ∧ ∀ i, (args i).InVocab V
  | eq t t' => t.InVocab V ∧ t'.InVocab V
  | quant k Q args => Q ∈ Qs k ∧ ∀ i, (args i).InFragment V Qs
  | neg φ => φ.InFragment V Qs
  | or φ ψ => φ.InFragment V Qs ∧ ψ.InFragment V Qs
  | and φ ψ => φ.InFragment V Qs ∧ ψ.InFragment V Qs

/-- The language `L(φ) = {w ∈ Σ⁺ | w ⊨ φ}` of a sentence (p.20). -/
def L1Lang {α : Type} (φ : L1Form α) : Language α := {w | w ≠ [] ∧ φ.Sat w 0}

/-- **`L` is definable in `L¹[𝒬, Σ, V]`** (p.20): some sentence `φ` of the fragment has `L(φ) = L`. -/
def L1Definable {α : Type} (V : Vocab) (Qs : (k : ℕ) → Set (ℕ → Set (Set (Fin k → ℕ))))
    (L : Language α) : Prop :=
  ∃ φ : L1Form α, φ.IsSentence ∧ φ.InFragment V Qs ∧ L1Lang φ = L

end CircTrichotomy


