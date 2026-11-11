-- Prove2me | Definitions.Def_CircTrichotomy_QFForm
-- name    : CircTrichotomy_QFForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:07.773205+00:00
-- url     : https://prove2.me/theorems/18d5132f-c586-45bf-bb2d-ad8d808eb57d
-- title:
--   Quantifier-free formulas $\varphi(x_0,\dots,x_{k-1})$ over numerical predicates
-- statement:
--   Quantifier-free formulas in the variables $x_0,\dots,x_{k-1}$ over a vocabulary of numerical predicates: atoms $R(x_{i_0},\dots,x_{i_{r-1}})$ and $x_i=x_j$, closed under $\neg,\wedge,\vee$. They define the bounded quantifiers $\mathcal B_\tau$.
--
--   **Formalization Note** The predicates used with them ($<$, $+j$, and the circuit-computable predicates of $\mathrm{num}[O(f),O(g)]$) are relations on $\mathbb N$ that do not depend on the word length.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition B.16, p.28

import Mathlib

set_option autoImplicit false

namespace CircTrichotomy

/-- **Quantifier-free formulas `φ(x₀, …, x_{k−1})` over a vocabulary of numerical predicates**
(Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition B.16, p.28): atoms `R(x_{i₀}, …, x_{i_{r−1}})` and `x_i = x_j`, closed under `¬, ∧, ∨`.
A predicate is a length-independent relation `R : (Fin r → ℕ) → Prop` on positions, packaged with
its arity (the vocabularies `<, +ω` and `num[O(f), O(g)]` used with Definition B.16 are of this
kind, Definition B.18, p.29). -/
inductive QFForm (k : ℕ) where
  | rel (R : Σ r : ℕ, (Fin r → ℕ) → Prop) (args : Fin R.1 → Fin k)
  | eq (i j : Fin k)
  | neg (φ : QFForm k)
  | and (φ ψ : QFForm k)
  | or (φ ψ : QFForm k)

/-- Truth of `φ` at the tuple `a = (a₀, …, a_{k−1})`. -/
def QFForm.Sat {k : ℕ} (a : Fin k → ℕ) : QFForm k → Prop
  | rel R args => R.2 (fun i => a (args i))
  | eq i j => a i = a j
  | neg φ => ¬ φ.Sat a
  | and φ ψ => φ.Sat a ∧ ψ.Sat a
  | or φ ψ => φ.Sat a ∨ ψ.Sat a

/-- Every predicate of `φ` belongs to the vocabulary `Rs`. -/
def QFForm.InVocab {k : ℕ} (Rs : Set (Σ r : ℕ, (Fin r → ℕ) → Prop)) : QFForm k → Prop
  | rel R _ => R ∈ Rs
  | eq _ _ => True
  | neg φ => φ.InVocab Rs
  | and φ ψ => φ.InVocab Rs ∧ ψ.InVocab Rs
  | or φ ψ => φ.InVocab Rs ∧ ψ.InVocab Rs

end CircTrichotomy


