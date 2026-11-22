-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Logic_Flatten
-- name    : LeanPool_DeciSigma1_Logic_Flatten
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:34:00.213917+00:00
-- url     : https://prove2.me/theorems/07cc7984-551c-4367-9846-93c009c46ec0
-- title:
--   Flatten
-- statement:
--   Definitions and structural lemmas for Flatten, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Flatten.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Syntax
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Logic
variable {T : Type → Type} {D V : Type} {I : Interpretation T D}
structure ConjunctiveClause (T : Type → Type) (V : Type) where
  /-- The inequalities. -/
  positive : List (T V × T V)
  /-- The negated inequalities. -/
  negative : List (T V × T V)
def ConjunctiveClause.Holds (I : Interpretation T D) (ρ : V → D) (c : ConjunctiveClause T V) :
    Prop :=
  (∀ p ∈ c.positive, I.le (I.eval ρ p.1) (I.eval ρ p.2)) ∧
  (∀ p ∈ c.negative, ¬ I.le (I.eval ρ p.1) (I.eval ρ p.2))
def ConjunctiveClause.append (c d : ConjunctiveClause T V) : ConjunctiveClause T V :=
  ⟨c.positive ++ d.positive, c.negative ++ d.negative⟩
def ConjunctiveClause.cross (cs ds : List (ConjunctiveClause T V)) : List (ConjunctiveClause T V) :=
  cs.flatMap fun c => ds.map c.append
def QuantifierFreeFormula.dnfWithPolarity :
    QuantifierFreeFormula T V → Bool → List (ConjunctiveClause T V)
  | .le s t, true => [⟨[(s, t)], []⟩]
  | .le s t, false => [⟨[], [(s, t)]⟩]
  | .tt, true | .ff, false => [⟨[], []⟩]
  | .tt, false | .ff, true => []
  | .not φ, b => φ.dnfWithPolarity (!b)
  | .and φ ψ, true => ConjunctiveClause.cross (φ.dnfWithPolarity true) (ψ.dnfWithPolarity true)
  | .or φ ψ, false => ConjunctiveClause.cross (φ.dnfWithPolarity false) (ψ.dnfWithPolarity false)
  | .and φ ψ, false => φ.dnfWithPolarity false ++ ψ.dnfWithPolarity false
  | .or φ ψ, true => φ.dnfWithPolarity true ++ ψ.dnfWithPolarity true
def QuantifierFreeFormula.dnf (φ : QuantifierFreeFormula T V) :
    List (ConjunctiveClause T V) := φ.dnfWithPolarity true
structure Flattening (I : Interpretation T D) where
  /-- Flat literals with variables in `W`. -/
  Lit : Type → Type
  /-- Satisfaction of a flat literal by an assignment. -/
  Holds {W : Type} : (W → D) → Lit W → Prop
  /-- The flat literal `x ≤ y`. -/
  leLit {W : Type} : W → W → Lit W
  holds_leLit {W : Type} (σ : W → D) (x y : W) : Holds σ (leLit x y) ↔ I.le (σ x) (σ y)
  /-- The subterms of a term, including the term itself. -/
  subterms {V : Type} : T V → List (T V)
  mem_subterms {V : Type} (t : T V) : t ∈ subterms t
  subterms_trans {V : Type} {s t u : T V} : s ∈ subterms t → u ∈ subterms s → u ∈ subterms t
  /-- A term without variables, which names the values not used by a clause. -/
  bot {V : Type} : T V
  /-- Literals defining `name t`, given the names `var v` of the variables and `name s` of the
  other subterms of `t`. -/
  defs {V W : Type} : (V → W) → (T V → W) → T V → List (Lit W)
  /-- If every subterm is named by its value, the defining literals hold. -/
  holds_defs {V W : Type} (var : V → W) (name : T V → W) (σ : W → D) (t : T V) :
    (∀ s ∈ subterms t, σ (name s) = I.eval (σ ∘ var) s) → ∀ l ∈ defs var name t, Holds σ l
  /-- If the defining literals of all subterms hold, `t` is named by its value. -/
  eval_of_holds_defs {V W : Type} (var : V → W) (name : T V → W) (σ : W → D) (t : T V) :
    (∀ s ∈ subterms t, ∀ l ∈ defs var name s, Holds σ l) → σ (name t) = I.eval (σ ∘ var) t
namespace Flattening
variable (F : Flattening I)
def DisjEntailsIn {W : Type} {k : ℕ} (C : D → Prop) (Γ : List (F.Lit W))
    (q : Fin k → W × W) : Prop :=
  ∀ σ : W → D, (∀ w, C (σ w)) → (∀ l ∈ Γ, F.Holds σ l) → ∃ i, I.le (σ (q i).1) (σ (q i).2)
end Flattening
namespace ConjunctiveClause
variable (F : Flattening I) {m : ℕ} (c : ConjunctiveClause T (Fin m))
def terms : List (T (Fin m)) :=
  (c.positive ++ c.negative).flatMap fun p => F.subterms p.1 ++ F.subterms p.2
abbrev Names : Type := Fin m ⊕ Fin ((c.terms F).length + 1)
def extend (ρ : Fin m → D) : c.Names F → D :=
  Sum.elim ρ fun i => I.eval ρ (((c.terms F)[i.val]?).getD F.bot)
variable [DecidableEq (T (Fin m))]
def name (t : T (Fin m)) : c.Names F :=
  .inr ⟨(c.terms F).idxOf t, Nat.lt_succ_of_le List.idxOf_le_length⟩
def constraints : List (F.Lit (c.Names F)) :=
  (c.terms F).flatMap (F.defs .inl (c.name F)) ++
    c.positive.map fun p => F.leLit (c.name F p.1) (c.name F p.2)
def queries (i : Fin c.negative.length) : c.Names F × c.Names F :=
  (c.name F c.negative[i].1, c.name F c.negative[i].2)
end ConjunctiveClause
end DeciSigma1.Logic


