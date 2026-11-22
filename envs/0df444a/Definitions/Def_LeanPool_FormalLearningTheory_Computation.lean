-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Computation
-- name    : LeanPool_FormalLearningTheory_Computation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:32:06.643813+00:00
-- url     : https://prove2.me/theorems/3fdcb4c6-276a-4dc3-a0df-b5fcec3f0aa4
-- title:
--   Computation
-- statement:
--   Definitions and structural lemmas for Computation, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Computation.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Basic
public import Mathlib.Computability.PartrecCode
public import Mathlib.Algebra.Group.End
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
class Alphabet (Sym : Type*) where
  /-- The alphabet is finite. -/
  [toFintype : Fintype Sym]
  /-- Symbols have decidable equality. -/
  [toDecidableEq : DecidableEq Sym]
abbrev Word (Sym : Type*) := List Sym
def FormalLanguage (Sym : Type*) := Set (Word Sym)
structure DFA' (Sym : Type*) (Q : Type*) [Fintype Q] [DecidableEq Q] where
  /-- Transition function -/
  step : Q → Sym → Q
  /-- Start state -/
  start : Q
  /-- Accept states -/
  accept : Set Q
def DFA'.accepts {Sym : Type*} {Q : Type*} [Fintype Q] [DecidableEq Q]
    (M : DFA' Sym Q) : FormalLanguage Sym :=
  { w | List.foldl M.step M.start w ∈ M.accept }
structure NFA' (Sym : Type*) (Q : Type*) [Fintype Q] where
  /-- Transition relation from a state and input symbol. -/
  step : Q → Sym → Set Q
  /-- Initial states. -/
  start : Set Q
  /-- Accepting states. -/
  accept : Set Q
def IsRegularLang (Sym : Type*) (L : FormalLanguage Sym) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (M : DFA' Sym Q), M.accepts = L
structure CFG (Sym : Type*) where
  /-- Nonterminal symbols -/
  Variable : Type
  /-- Production rules: Variable → list of (Variable ⊕ Terminal) -/
  productions : Variable → Set (List (Variable ⊕ Sym))
  /-- Start symbol -/
  start : Variable
def CFG.DerivesStep {Sym : Type*} (G : CFG Sym)
    (sf1 sf2 : List (G.Variable ⊕ Sym)) : Prop :=
  ∃ (pre suf : List (G.Variable ⊕ Sym)) (v : G.Variable)
    (p : List (G.Variable ⊕ Sym)),
    p ∈ G.productions v ∧
    sf1 = pre ++ [Sum.inl v] ++ suf ∧
    sf2 = pre ++ p ++ suf
def CFG.Derives {Sym : Type*} (G : CFG Sym) :
    List (G.Variable ⊕ Sym) → List (G.Variable ⊕ Sym) → Prop :=
  Relation.ReflTransGen G.DerivesStep
def CFG.Language {Sym : Type*} (G : CFG Sym) : FormalLanguage Sym :=
  { w | G.Derives [Sum.inl G.start] (w.map Sum.inr) }
def IsContextFree (Sym : Type*) (L : FormalLanguage Sym) : Prop :=
  ∃ (G : CFG Sym), G.Language = L
structure PDA (Sym : Type*) (Q : Type*) (Γ : Type*) where
  /-- Transition relation using an optional input symbol and top stack symbol. -/
  step : Q → Option Sym → Γ → Set (Q × List Γ)
  /-- Initial control state. -/
  start : Q
  /-- Initial stack symbol. -/
  startStack : Γ
  /-- Accepting control states. -/
  accept : Set Q
structure TuringMachine where
  /-- Opaque representation; we work with the computability predicate, not the machine. -/
  index : ℕ
def GodelNumbering (α : Type*) := α ≃ ℕ
def PartialComputable (α β : Type*) [Encodable α] [Encodable β] :=
  { f : α →. β // ∃ g : ℕ →. ℕ, Nat.Partrec g ∧
    ∀ a : α, (f a).map Encodable.encode = g (Encodable.encode a) }
def RESet (α : Type*) :=
  { S : Set α // ∃ f : ℕ → Option α, S = { a | ∃ n, f n = some a } }
def LimitingRecursive (α β : Type*) :=
  { f : α → β // ∃ g : α → ℕ → β, (∀ x, ∃ s₀, ∀ s ≥ s₀, g x s = f x) }
def Delta02Class (α : Type*) :=
  { S : Set α // ∃ f : α → ℕ → Bool, ∀ x, (x ∈ S ↔ ∃ s₀, ∀ s ≥ s₀, f x s = true) }
noncomputable def KolmogorovComplexity (α : Type*) [Encodable α] (x : α) : ℕ :=
  sInf { Encodable.encode p | (p : Nat.Partrec.Code)
    (_ : Nat.Partrec.Code.eval p 0 = Part.some (Encodable.encode x)) }
def DescriptionLength (α : Type*) := α → ℕ
structure MDLPrinciple (X : Type u) (Y : Type v) [Inhabited (Concept X Y)] where
  /-- Description language for hypotheses -/
  hypothesisLength : Concept X Y → ℕ
  /-- Description language for data given hypothesis -/
  dataLength : Concept X Y → List (X × Y) → ℕ
  /-- MDL selection: minimize total description length.
      Uses Classical.epsilon to select an h ∈ H minimizing hypothesisLength h + dataLength h data.
      Inhabited provides the Nonempty witness for epsilon. -/
  select (data : List (X × Y)) (H : Set (Concept X Y)) : Concept X Y :=
    Classical.epsilon (fun h => h ∈ H ∧
      ∀ h' ∈ H, hypothesisLength h + dataLength h data ≤ hypothesisLength h' + dataLength h' data)
structure MMLPrinciple (X : Type u) (Y : Type v) [Inhabited (Concept X Y)] where
  /-- Description length of a hypothesis. -/
  hypothesisLength : Concept X Y → ℝ
  /-- Data-fit cost of a hypothesis on observations. -/
  dataFit : Concept X Y → List (X × Y) → ℝ
  /-- MML selection: minimize total message length (hypothesisLength + dataFit).
      Inhabited provides the Nonempty witness for epsilon. -/
  select (data : List (X × Y)) (H : Set (Concept X Y)) : Concept X Y :=
    Classical.epsilon (fun h => h ∈ H ∧
      ∀ h' ∈ H, hypothesisLength h + dataFit h data ≤ hypothesisLength h' + dataFit h' data)
noncomputable def AlgorithmicProbability (α : Type*) [Encodable α] (x : α) : ℝ :=
  haveI : DecidableEq (Part ℕ) := Classical.decEq _
  ∑' (p : Nat.Partrec.Code),
    if Nat.Partrec.Code.eval p 0 = Part.some (Encodable.encode x)
    then (2 : ℝ) ^ (-(Encodable.encode p : ℤ))
    else 0
structure SRM (X : Type u) (Y : Type v) [DecidableEq Y] [Inhabited (Concept X Y)] where
  /-- Nested hypothesis classes of increasing complexity -/
  levels : ℕ → Set (Concept X Y)
  /-- Monotonicity: larger index = richer class -/
  mono : ∀ n, levels n ⊆ levels (n + 1)
  /-- Empirical risk: fraction of training errors -/
  empiricalRisk : Concept X Y → List (X × Y) → ℝ
  /-- Complexity penalty: regularizer per level -/
  penalty : ℕ → ℝ
  /-- SRM selection: minimize empiricalRisk(h, data) + penalty(n) over (n, h ∈ levels n).
      Uses Classical.epsilon for the argmin; Inhabited provides the witness. -/
  select (data : List (X × Y)) : ℕ × Concept X Y :=
    Classical.epsilon (fun (pair : ℕ × Concept X Y) =>
      pair.2 ∈ levels pair.1 ∧
        ∀ n (h : Concept X Y), h ∈ levels n →
          empiricalRisk pair.2 data + penalty pair.1 ≤
            empiricalRisk h data + penalty n)
def ExecutionTrace (X : Type u) (Y : Type v) := ℕ → Concept X Y
def PartialTrace (X : Type u) (Y : Type v) := ℕ → Option (Concept X Y)


