-- Prove2me | Definitions.Def_ApproxCountRwPHP_Unprovability_Game
-- name    : ApproxCountRwPHP_Unprovability_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:57:36.710004+00:00
-- url     : https://prove2.me/theorems/6a77c1e2-1a46-486c-85cc-5109baa0891a
-- title:
--   Partial structures and the adaptive inspector–adversary game
-- statement:
--   A partial structure returns an optional value for each table-entry query, with constants as arity-zero queries. A quantifier-free formula is witnessed only if all of its terms are defined and the formula is true. The published generic decision-tree type is specialized to these queries and answers in [N]. Height counts every branch. Randomized trees are PMFs with every supported tree of height at most h; over the finite query and answer sets this also gives finite support.
--
--   In each of m rounds an adaptive inspector supplies such a PMF and the adversary replies in [0,1]. The adversary then supplies a partial structure. It wins exactly when that structure is not witnessing, every singleton query's answer agrees with its determined leaf bit, and every queried half-mixture satisfies
--
--   $$|p_1-p_2/2-p_3/2|\le\varepsilon.$$
--
--   Both winning predicates quantify over actual history-dependent strategies, using the same recursively computed play. The inspector's terminal condition is the negation of the adversary's condition.
-- source:
--   Oliver Korten, Jiatu Li, Igor Oliveira, Hanlin Ren, STOC 2027 submission #1023 (October 2026), Definitions 6.1–6.2, printed p. 34–35, PDF p. 36–37; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1023.pdf#page=36–37

import Definitions.Def_ApproxCountRwPHP_Unprovability_Circuits
import Definitions.Def_QAlgorithms_Defs_Classical

open FirstOrder

namespace ApproxCountRwPHP.Unprovability

/-- Queries include constants as arity-zero table entries. -/
abbrev TableQuery (S : Signature) (N : ℕ) := (s : Fin S.count) × (Fin (S.arity s) → Fin N)
abbrev PartialStructure (S : Signature) (N : ℕ) := TableQuery S N → Option (Fin N)

def optionVector {α : Type} : {n : ℕ} → (Fin n → Option α) → Option (Fin n → α)
  | 0, _ => some Fin.elim0
  | _ + 1, xs => do
      let x ← xs 0
      let rest ← optionVector (fun i => xs i.succ)
      pure (Fin.cons x rest)

/-- Strict partial evaluation; there is no default value for an undefined term. -/
def partialTerm {S : Signature} {N : ℕ} {α : Type}
    (ρ : PartialStructure S N) (assignment : α → Fin N) : (S.language).Term α → Option (Fin N)
  | .var i => some (assignment i)
  | .func ⟨s, hs⟩ ts => do
      let values ← optionVector (fun i => partialTerm ρ assignment (ts i))
      ρ ⟨s, fun i => values (Fin.cast hs i)⟩

/-- Both operands of every connective must have defined terms, including
operands whose truth value would be irrelevant to a short-circuit evaluator.
Quantified formulas are outside the domain used by the game. -/
def partialFormula {S : Signature} {N : ℕ} (ρ : PartialStructure S N) :
    {k : ℕ} → (S.language).BoundedFormula Empty k → (Fin k → Fin N) → Option Bool
  | _, .falsum, _ => some false
  | _, .equal t u, xs => do
      let x ← partialTerm ρ (Sum.elim Empty.elim xs) t
      let y ← partialTerm ρ (Sum.elim Empty.elim xs) u
      pure (x == y)
  | _, .rel r _, _ => Empty.elim r
  | _, .imp φ ψ, xs => do
      let b ← partialFormula ρ φ xs
      let c ← partialFormula ρ ψ xs
      pure (!b || c)
  | _, .all _, _ => none

def witnessing {S : Signature} {N k : ℕ} (φ : S.language.BoundedFormula Empty k)
    (ρ : PartialStructure S N) : Prop := ∃ xs, partialFormula ρ φ xs = some true

abbrev DecisionTree (S : Signature) (N : ℕ) :=
  QAlgorithms.DecisionTree (TableQuery S N) (Fin N) Bool

/-- Structural height counts every branch, even mutually inconsistent repeated
queries. This deliberately does not reuse `MakesAtMost` from the reference,
which measures only paths followed by a total oracle. -/
def treeHeight {S : Signature} {N : ℕ} : DecisionTree S N → ℕ
  | .leaf _ => 0
  | .node _ next => 1 + Finset.univ.sup (fun i => treeHeight (next i))

def treeCompose {S : Signature} {N : ℕ} : DecisionTree S N → DecisionTree S N → DecisionTree S N
  | .leaf _, T => T
  | .node q next, T => .node q (fun i => treeCompose (next i) T)

def determinedOutput {S : Signature} {N : ℕ} (ρ : PartialStructure S N) : DecisionTree S N → Option Bool
  | .leaf b => some b
  | .node q next => do
      let x ← ρ q
      determinedOutput ρ (next x)

abbrev RDT (S : Signature) (N : ℕ) := PMF (DecisionTree S N)

def legalRDT (S : Signature) (N h : ℕ) :=
  {μ : RDT S N // ∀ T ∈ μ.support, treeHeight T ≤ h}

noncomputable def halfMixture {S : Signature} {N : ℕ} (μ ν : RDT S N) : RDT S N :=
  (PMF.bernoulli (1/2) (by norm_num)).bind (fun b => if b then μ else ν)

abbrev Response := Set.Icc (0 : ℝ) 1
abbrev GameHistory (S : Signature) (N h : ℕ) := List (legalRDT S N h × Response)
abbrev Inspector (S : Signature) (N h : ℕ) := GameHistory S N h → legalRDT S N h

structure Adversary (S : Signature) (N h : ℕ) where
  answer : GameHistory S N h → legalRDT S N h → Response
  final : GameHistory S N h → PartialStructure S N

def play {S : Signature} {N h : ℕ} (I : Inspector S N h) (A : Adversary S N h) :
    ℕ → GameHistory S N h
  | 0 => []
  | t + 1 =>
      let history := play I A t
      let T := I history
      history ++ [(T, A.answer history T)]

/-- Definition 6.2, all three win conditions, with exact PMF equality for mixtures. -/
def adversaryWin {S : Signature} {N h k : ℕ}
    (φ : S.language.BoundedFormula Empty k) (ε : ℝ)
    (history : GameHistory S N h) (ρ : PartialStructure S N) : Prop :=
  ¬ witnessing φ ρ ∧
  (∀ Tp ∈ history, ∀ T, Tp.1.val = PMF.pure T →
    ∃ b : Bool, determinedOutput ρ T = some b ∧ (b.toNat : ℝ) = Tp.2.val) ∧
  (∀ Tp₁ ∈ history, ∀ Tp₂ ∈ history, ∀ Tp₃ ∈ history,
    Tp₁.1.val = halfMixture Tp₂.1.val Tp₃.1.val →
    |Tp₁.2.val - Tp₂.2.val/2 - Tp₃.2.val/2| ≤ ε)

def adversaryWins {S : Signature} {N h k : ℕ}
    (φ : S.language.BoundedFormula Empty k) (m : ℕ) (ε : ℝ) : Prop :=
  ∃ A : Adversary S N h, ∀ I : Inspector S N h,
    adversaryWin φ ε (play I A m) (A.final (play I A m))

def inspectorWins {S : Signature} {N h k : ℕ}
    (φ : S.language.BoundedFormula Empty k) (m : ℕ) (ε : ℝ) : Prop :=
  ∃ I : Inspector S N h, ∀ A : Adversary S N h,
    ¬ adversaryWin φ ε (play I A m) (A.final (play I A m))

end ApproxCountRwPHP.Unprovability


