-- Prove2me | Definitions.Def_LeanPool_Parikh_Construction
-- name    : LeanPool_Parikh_Construction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T09:51:06.55086+00:00
-- url     : https://prove2.me/theorems/550045c9-908b-4565-bd83-1faca3bdcbe6
-- title:
--   Construction
-- statement:
--   Definitions and structural lemmas for Construction, from Umang Mathur; LeanPool contributors's pinned Parikh's theorem and a certified semilinear grammar compiler development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Construction.lean

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Mathlib.Data.Nat.Log
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Definitions.Def_LeanPool_Parikh_FiniteWitness
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace Parikh
structure GrammarSize where
  /-- Number of available nonterminal labels. -/
  nonterminals : ℕ
  /-- Number of terminal letters. -/
  terminals : ℕ
  /-- Number of distinct production rules. -/
  productions : ℕ
  /-- Upper bound on the length of a production output. -/
  branching : ℕ
  deriving Repr
@[expose] def GrammarSize.positions (s : GrammarSize) : ℕ :=
  ∑ i ∈ Finset.range (s.nonterminals + 2), s.branching ^ i
@[expose] def GrammarSize.records (s : GrammarSize) : ℕ :=
  1 + s.terminals + s.nonterminals + s.productions
@[expose] def GrammarSize.trees (s : GrammarSize) : ℕ := s.records ^ s.positions
@[expose] noncomputable def grammarSize {T : Type*} [Fintype T] (g : ContextFreeGrammar T) :
  GrammarSize :=
  ⟨(activeNonterminals g).card, Fintype.card T, g.rules.card,
    max 1 (g.rules.sup fun r => r.output.length)⟩
@[expose] def norm {T : Type*} [Fintype T] (v : Vector T) : ℕ := ∑ a, v a
@[expose] def WithinBounds {T : Type*} [Fintype T] (s : GrammarSize) (W : Witness T) : Prop :=
  W.length ≤ s.trees * 2 ^ s.trees ∧
    ∀ c ∈ W, c.periods.length ≤ s.trees ∧
      norm c.base ≤ (s.trees + 1) * s.positions ∧
      ∀ p ∈ c.periods, norm p ≤ s.positions
@[expose] def GrammarSize.coordinateBits (s : GrammarSize) : ℕ :=
  max 1 (Nat.clog 2 ((s.trees + 1) * s.positions + 1))
@[expose] def GrammarSize.vectorBits (s : GrammarSize) : ℕ :=
  s.trees * 2 ^ s.trees * (s.trees + 1) * s.terminals * s.coordinateBits
@[expose] def entryBits {T : Type*} [Fintype T] (s : GrammarSize) (W : Witness T) : ℕ :=
  (W.map fun c => (c.periods.length + 1) * Fintype.card T * s.coordinateBits).sum
structure EncodedGrammar where
  /-- Size of the declared terminal alphabet. -/
  terminalCount : ℕ
  /-- Number of nonterminal labels beyond the always-present initial label. -/
  extraNonterminalCount : ℕ
  /-- Starting nonterminal of the grammar. -/
  initial : Fin (extraNonterminalCount + 1)
  /-- Finite list of productions; duplicate rules are allowed. -/
  rules : List (ContextFreeRule (Fin terminalCount) (Fin (extraNonterminalCount + 1)))
@[expose] def EncodedGrammar.decode (g : EncodedGrammar) : ContextFreeGrammar (Fin
  g.terminalCount) :=
  ⟨Fin (g.extraNonterminalCount + 1), g.initial, g.rules.toFinset⟩
@[expose] def EncodedGrammar.size (g : EncodedGrammar) : GrammarSize :=
  ⟨g.extraNonterminalCount + 1, g.terminalCount, g.rules.toFinset.card,
    max 1 ((g.rules.map fun r => r.output.length).foldl max 0)⟩
structure BoundedEnumeration where
  /-- List every valid open tree within the requested height bound. -/
  enumerate : (g : EncodedGrammar) → ℕ →
    List (ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1)))
  correct : ∀ g H t, t ∈ enumerate g H ↔ Valid g.decode t ∧ t.height ≤ H
structure Compiler where
  /-- Compute a finite semilinear representation from numeric grammar syntax. -/
  compile : (g : EncodedGrammar) → Witness (Fin g.terminalCount)
  correct : ∀ g, (compile g).denotation = image g.decode.language
  bounded : ∀ g, WithinBounds g.size (compile g)
end Parikh


