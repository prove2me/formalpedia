-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Logic_Syntax
-- name    : LeanPool_DeciSigma1_Logic_Syntax
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:32:48.415803+00:00
-- url     : https://prove2.me/theorems/090abf35-c4c5-4535-8d08-c82de608ff44
-- title:
--   Syntax
-- statement:
--   Definitions and structural lemmas for Syntax, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Syntax.lean

module
public import Mathlib.Data.Nat.Notation
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Logic
structure Interpretation (T : Type → Type) (D : Type) where
  /-- The value of a term when its variables have the values `ρ`. -/
  eval {V : Type} : (V → D) → T V → D
  /-- The relation interpreting `≤`. -/
  le : D → D → Prop
def Interpretation.TermClosed {T : Type → Type} {D : Type} (I : Interpretation T D)
    (C : D → Prop) : Prop :=
  ∀ {V : Type} (ρ : V → D) (t : T V), (∀ v, C (ρ v)) → C (I.eval ρ t)
variable {T : Type → Type} {D V : Type}
inductive QuantifierFreeFormula (T : Type → Type) (V : Type) where
  /-- The inequality `s ≤ t`. -/
  | le (s t : T V)
  /-- The true formula. -/
  | tt
  /-- The false formula. -/
  | ff
  /-- Negation. -/
  | not (φ : QuantifierFreeFormula T V)
  /-- Conjunction. -/
  | and (φ ψ : QuantifierFreeFormula T V)
  /-- Disjunction. -/
  | or (φ ψ : QuantifierFreeFormula T V)
def QuantifierFreeFormula.eq (s t : T V) : QuantifierFreeFormula T V := .and (.le s t) (.le t s)
def QuantifierFreeFormula.Holds (I : Interpretation T D) (ρ : V → D) :
    QuantifierFreeFormula T V → Prop
  | .le s t => I.le (I.eval ρ s) (I.eval ρ t)
  | .tt => True
  | .ff => False
  | .not φ => ¬ φ.Holds I ρ
  | .and φ ψ => φ.Holds I ρ ∧ ψ.Holds I ρ
  | .or φ ψ => φ.Holds I ρ ∨ ψ.Holds I ρ
structure Sigma1 (T : Type → Type) where
  /-- The number of bound variables. -/
  variableCount : ℕ
  /-- The quantifier-free body. -/
  body : QuantifierFreeFormula T (Fin variableCount)
def Sigma1.HoldsIn (I : Interpretation T D) (C : D → Prop) (s : Sigma1 T) : Prop :=
  ∃ ρ : Fin s.variableCount → D, (∀ v, C (ρ v)) ∧ s.body.Holds I ρ
inductive BooleanSentence (T : Type → Type) where
  /-- The existential sentence `∃ x₀ … x_{m-1}, φ`. -/
  | ex (s : Sigma1 T)
  /-- The universal sentence `∀ x₀ … x_{m-1}, φ`, for `s = ⟨m, φ⟩`. -/
  | all (s : Sigma1 T)
  /-- Negation. -/
  | not (φ : BooleanSentence T)
  /-- Conjunction. -/
  | and (φ ψ : BooleanSentence T)
  /-- Disjunction. -/
  | or (φ ψ : BooleanSentence T)
def BooleanSentence.HoldsIn (I : Interpretation T D) (C : D → Prop) :
    BooleanSentence T → Prop
  | .ex s => s.HoldsIn I C
  | .all s => ∀ ρ : Fin s.variableCount → D, (∀ v, C (ρ v)) → s.body.Holds I ρ
  | .not φ => ¬ φ.HoldsIn I C
  | .and φ ψ => φ.HoldsIn I C ∧ ψ.HoldsIn I C
  | .or φ ψ => φ.HoldsIn I C ∨ ψ.HoldsIn I C
end DeciSigma1.Logic


