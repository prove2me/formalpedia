-- Prove2me | Definitions.Def_AehligSchwichtenberg2002_Bounds
-- name    : AehligSchwichtenberg2002_Bounds
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-30T01:56:09.471707+00:00
-- url     : https://prove2.me/theorems/84cd66c7-2b4e-44e6-9c44-483bc81fd640
-- title:
--   Sections 3-4: Weight `μ(r)`, Iteration Depth `d(r)`, and Syntactic Valuation `|r|_ξ`
-- statement:
--   Formalizes Sections 3 and 4 of Aehlig and Schwichtenberg (2002): iteration depth `d(r)` (Definition 3.1), the weight measure `μ(r)` weighting subterms under `d_i` and `it` by `2` (Definition 3.2), the `d`-graded syntactic size valuation `|r|_ξ` with environment `ξ` (Definition 4.1), environment compatibility `CompatEnv`, and polynomial-time Turing computability.
-- source:
--   Klaus Aehlig and Helmut Schwichtenberg, 'A syntactical analysis of non-size-increasing polynomial time computation', ACM Transactions on Computational Logic 3(3), 2002, pp. 383-401 (LICS 2000, pp. 84-91; doi:10.1145/507382.507386). Sections 3-4, pp. 391-398.

import Definitions.Def_AehligSchwichtenberg2002_Syntax

/-!
# Term Length and Polynomial Step Bounds for Aehlig–Schwichtenberg (2002, Section 4)

Source: Klaus Aehlig and Helmut Schwichtenberg,
"A syntactical analysis of non-size-increasing polynomial time computation",
*ACM Transactions on Computational Logic* 3(3), 2002, pp. 383–401 (arXiv:cs/0011037v2),
Section 4 (pp. 9–14).

This module formalizes:
- Definition 4.1: Term length `|t|` (`termLength`, p. 10), with `|{t}| = 0`.
- Definition 4.5: Polynomial bound `ϑ(t) ∈ N^{poly}` (`theta t : Nat → Nat`, p. 11),
  pointwise order `PolyLe` (`f ≼ g`), and polynomial boundedness (`IsPolyBounded`).
- Input list representations for Corollary 4.4 (Non-size-increasing property, p. 11) and
  Corollary 4.9 (Polynomial-time computability of closed terms of type `L(B) ⊸ ⋯ ⊸ L(B) ⊸ L(B)`, p. 14).
-/

namespace AehligSchwichtenberg2002

/-- Definition 4.1 (Length `|t|`, p. 10):
- `|c| := |x| := 1`
- `|t s| := |t| + |s|`
- `|λx^τ. s| := |s| + 1`
- `|⟨t, s⟩| := max {|t|, |s|} + 1`
- `|{t}| := 0`. -/
def termLength : Term → Nat
  | .var _ => 1
  | .const _ => 1
  | .app t s => termLength t + termLength s
  | .lam _ s => termLength s + 1
  | .pair t s => Nat.max (termLength t) (termLength s) + 1
  | .brace _ => 0

/-- Section 4 (p. 11): `X_n(m) = min {n, m}`. -/
def truncId (n m : Nat) : Nat :=
  Nat.min n m

/-- Pointwise order `f ≼ g` on functions `Nat → Nat` (Section 4, p. 11). -/
def PolyLe (f g : Nat → Nat) : Prop :=
  ∀ m : Nat, f m ≤ g m

/-- Definition 4.5 (Polynomial bound `ϑ(t)` of a term, p. 11):
For each (not necessarily typed) term `t` and input parameter `m : Nat`, `theta t m`
evaluates the polynomial bound `ϑ(t)(m)`:
- `ϑ(x) := ϑ(c) := 0`
- `ϑ(t s) := ϑ(t) + X_n · ϑ(h) + X_n · |h|` if `t` is a list with `n` entries and `s = {h}`,
  and `ϑ(t) + ϑ(s)` otherwise
- `ϑ(λx^τ. t) := ϑ(t)`
- `ϑ(⟨t, s⟩) := sup_{≼} {ϑ(t), ϑ(s)}`
- `ϑ({h}) := X · ϑ(h) + X · |h|`. -/
def theta : Term → Nat → Nat
  | .var _, _ => 0
  | .const _, _ => 0
  | .app t (.brace h), m =>
      match listEntryCount t with
      | some n =>
          theta t m + truncId n m * theta h m + truncId n m * termLength h
      | none =>
          theta t m + (m * theta h m + m * termLength h)
  | .app t s, m => theta t m + theta s m
  | .lam _ t, m => theta t m
  | .pair t s, m => Nat.max (theta t m) (theta s m)
  | .brace h, m => m * theta h m + m * termLength h

/-- Combined measure `ϑ(t)(N) + |t|` appearing in Theorem 4.8 (p. 12). -/
def stepMeasure (t : Term) (N : Nat) : Nat :=
  theta t N + termLength t

/-- Brace-nesting depth of a term `t` (Section 2, p. 4: "the degree of the bounding polynomial
is the nesting depth of braces"). -/
def braceDepth : Term → Nat
  | .var _ => 0
  | .const _ => 0
  | .lam _ t => braceDepth t
  | .pair t s => Nat.max (braceDepth t) (braceDepth s)
  | .app t s => Nat.max (braceDepth t) (braceDepth s)
  | .brace h => braceDepth h + 1

/-- A function `B : Nat → Nat` is bounded by a polynomial of degree at most `d`
if there exist `c₀, c₁ : Nat` such that `B n ≤ c₀ * (n + 1)^d + c₁` for all `n`. -/
def IsPolyBoundedOfDegree (B : Nat → Nat) (d : Nat) : Prop :=
  ∃ c₀ c₁ : Nat, ∀ n : Nat, B n ≤ c₀ * (n + 1) ^ d + c₁

/-- A function `B : Nat → Nat` is polynomially bounded (`B ∈ N^{poly}`, p. 11). -/
def IsPolyBounded (B : Nat → Nat) : Prop :=
  ∃ d : Nat, IsPolyBoundedOfDegree B d

/-- An almost closed normal list of type `L(τ)` with `n` entries (used as canonical list input
in Corollary 4.4, p. 11 & Corollary 4.9, p. 14). -/
def IsCanonicalListInput (τ : Ty) (l : Term) (n : Nat) : Prop :=
  ∃ Γ : Context,
    (∀ v ∈ Γ, v.ty = .diamond) ∧
    HasType Γ l (.list τ) ∧
    IsNormal l ∧
    listEntryCount l = some n

/-- A tuple of canonical binary-list inputs `ls = [l₁, ..., lₖ]` of type `L(B)` with pairwise
disjoint contexts `Γ₁, ..., Γₖ` (Corollary 4.9, p. 14). -/
inductive ValidBinListInputs : Context → List Term → List Nat → Prop where
  | nil : ValidBinListInputs [] [] []
  | cons {Γ_acc Γ_l Γ_new : Context} {l : Term} {n : Nat} {ls : List Term} {ns : List Nat} :
      (∀ v ∈ Γ_l, v.ty = .diamond) →
      HasType Γ_l l Ty.bin →
      IsNormal l →
      listEntryCount l = some n →
      IsDisjointCtxUnion Γ_acc Γ_l Γ_new →
      ValidBinListInputs Γ_acc ls ns →
      ValidBinListInputs Γ_new (l :: ls) (n :: ns)

/-- Sum of list lengths `n₁ + ⋯ + nₖ` for a tuple of list inputs. -/
def sumListLengths : List Nat → Nat
  | [] => 0
  | n :: ns => n + sumListLengths ns

end AehligSchwichtenberg2002


