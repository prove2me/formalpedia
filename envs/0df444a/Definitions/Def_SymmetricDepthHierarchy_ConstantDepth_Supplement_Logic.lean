-- Prove2me | Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Logic
-- name    : SymmetricDepthHierarchy_ConstantDepth_Supplement_Logic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:57:11.92285+00:00
-- url     : https://prove2.me/theorems/4e2c8918-1a96-4b90-82dd-736783386587
-- title:
--   Counting logic, labelled hosts, weighted padding, and incidence structures
-- statement:
--   A finite positive-arity relational vocabulary specifies relation symbols and their arities; a finite structure specifies its universe and each relation. First-order counting formulas have equality, relation atoms, Boolean operations, and finite-threshold quantifiers $\exists^{\ge t}x$. They use a fixed reusable register set of size $K$. Quantifier rank increases by one at each counting quantifier. Closed-sentence semantics is defined recursively, including empty universes, and
--   $$A\equiv_{C_K^q}B$$
--   means equality of truth values for every sentence of rank at most $q$ in these $K$ variables. This is independent of homomorphism counts and circuit computations.
--
--   A labelled bipartite graph has finite sides and one binary relation per label. Homomorphisms respect sides and every relation. One-label-per-pair is a separate host predicate, and is not imposed on source patterns. Injective row and column indexing defines the zero-padded weighted matrix with entry $\omega_\sigma$ on relation $\sigma$.
--
--   The incidence graph of $D$ has left universe $U$ and right tagged tuples of all lengths $1\le s\le m$, with colours $(s,J,S)$. Here $J$ is the exact nonempty set of tuple positions equal to the left vertex, and $S$ is the exact set of arity-$s$ relations containing that tuple. All repeated tuples, all multiplicities of positions, and all isolated vertices are retained. Positive arities follow the source's $s\in[m]$ vocabulary convention. Empty vocabularies are allowed. These definitions provide actual syntax, satisfaction, and the specified incidence construction, rather than theorem-shaped predicates.
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 43–46 (PDF p. 46–49), §§C.3.1–C.3.2; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Paths

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement


/-- Finite relational vocabulary; relation symbols have positive arity (C.3.1 convention). -/
structure Vocabulary where
  R : Type
  [finiteR : Fintype R]
  arity : R → ℕ
  positive : ∀ R, 0 < arity R
attribute [instance] Vocabulary.finiteR

structure RelStructure (τ : Vocabulary) where
  U : Type
  [finiteU : Fintype U]
  relation : (R : τ.R) → (Fin (τ.arity R) → U) → Prop
attribute [instance] RelStructure.finiteU

/-- Finite-variable first-order counting syntax. Variables are reusable registers. -/
inductive CountingFormula (τ : Vocabulary) (k : ℕ)
  | truth
  | equal (i j : Fin k)
  | atom (R : τ.R) (args : Fin (τ.arity R) → Fin k)
  | neg (φ : CountingFormula τ k)
  | conj (φ ψ : CountingFormula τ k)
  | count (i : Fin k) (threshold : ℕ) (φ : CountingFormula τ k)
namespace CountingFormula
variable {τ : Vocabulary} {k : ℕ}
def rank : CountingFormula τ k → ℕ
  | .truth | .equal _ _ | .atom _ _ => 0
  | .neg φ => φ.rank
  | .conj φ ψ => max φ.rank ψ.rank
  | .count _ _ φ => φ.rank + 1

def freeVars : CountingFormula τ k → Finset (Fin k)
  | .truth => ∅
  | .equal i j => {i,j}
  | .atom _ args => Finset.univ.image args
  | .neg φ => φ.freeVars
  | .conj φ ψ => φ.freeVars ∪ ψ.freeVars
  | .count i _ φ => φ.freeVars.erase i

/-- Option-valued environments also give the correct closed-sentence semantics on empty universes. -/
def holds (D : RelStructure τ) : CountingFormula τ k → (Fin k → Option D.U) → Prop
  | .truth, _ => True
  | .equal i j, e => ∃ u, e i = some u ∧ e j = some u
  | .atom R args, e => ∃ a : Fin (τ.arity R) → D.U,
      (∀ j, e (args j) = some (a j)) ∧ D.relation R a
  | .neg φ, e => ¬ φ.holds D e
  | .conj φ ψ, e => φ.holds D e ∧ ψ.holds D e
  | .count i t φ, e => t ≤ (Finset.univ.filter fun u =>
      φ.holds D (Function.update e i (some u))).card
end CountingFormula

/-- Same sentences of counting rank at most q using at most k reusable variables. -/
def countingEquiv {τ : Vocabulary} (A B : RelStructure τ) (k q : ℕ) : Prop :=
  ∀ φ : CountingFormula τ k, φ.freeVars = ∅ → φ.rank ≤ q →
    (φ.holds A (fun _ => none) ↔ φ.holds B (fun _ => none))

/-- The unbounded-rank fragment C_k. -/
def countingEquivAll {τ : Vocabulary} (A B : RelStructure τ) (k : ℕ) : Prop :=
  ∀ q, countingEquiv A B k q

/-- Labelled bipartite graphs, including several labels on a pair and isolated vertices. -/
structure LabelledHost (SLabel : Type) where
  A : Type
  B : Type
  [finiteA : Fintype A]
  [finiteB : Fintype B]
  edge : SLabel → A → B → Prop
attribute [instance] LabelledHost.finiteA LabelledHost.finiteB
namespace LabelledHost
variable {SLabel : Type} [Fintype SLabel]
def oneLabel (G : LabelledHost SLabel) : Prop :=
  ∀ s t a b, G.edge s a b → G.edge t a b → s = t

def homCount (L G : LabelledHost SLabel) : ℕ :=
  (Finset.univ.filter fun h : (L.A → G.A) × (L.B → G.B) =>
    ∀ s a b, L.edge s a b → G.edge s (h.1 a) (h.2 b)).card

def graph (L : LabelledHost SLabel) : SimpleGraph (L.A ⊕ L.B) :=
  SimpleGraph.fromRel fun x y => match x,y with
    | .inl a, .inr b => ∃ s, L.edge s a b
    | _, _ => False

inductive RelationSymbol (SLabel : Type)
  | leftSide | rightSide | edge (s : SLabel)
  deriving Fintype, DecidableEq

def vocabulary (SLabel : Type) [Fintype SLabel] : Vocabulary where
  R := RelationSymbol SLabel
  arity r := match r with | .edge _ => 2 | _ => 1
  positive r := by cases r <;> exact Nat.zero_lt_succ _

def structureOf (G : LabelledHost SLabel) : RelStructure (vocabulary SLabel) where
  U := G.A ⊕ G.B
  relation := by
    intro r
    cases r with
    | leftSide =>
      change (Fin 1 → G.A ⊕ G.B) → Prop
      exact fun a => ∃ x, a 0 = Sum.inl x
    | rightSide =>
      change (Fin 1 → G.A ⊕ G.B) → Prop
      exact fun a => ∃ x, a 0 = Sum.inr x
    | edge s =>
      change (Fin 2 → G.A ⊕ G.B) → Prop
      exact fun a => ∃ x y, a 0 = Sum.inl x ∧ a 1 = Sum.inr y ∧ G.edge s x y

/-- Explicit injections make zero padding and indexing choices fully determined. -/
def weightedMatrix {K : Type} [Field K] {N : ℕ} (G : LabelledHost SLabel)
    (iA : G.A ↪ Fin N) (iB : G.B ↪ Fin N) (ω : SLabel → K) : Matrix (Fin N) (Fin N) K :=
  fun i j => ∑ s, if ∃ a b, iA a = i ∧ iB b = j ∧ G.edge s a b then ω s else 0
end LabelledHost

/-- Incidence colours (s,J,S), including every nonempty equality-position set J. -/
structure IncColour (τ : Vocabulary) (m : ℕ) where
  s : Fin (m+1)
  positive : 0 < s.val
  positions : Finset (Fin s.val)
  nonempty : positions.Nonempty
  symbols : Finset {R : τ.R // τ.arity R = s.val}
  deriving Fintype

/-- Tagged tuples of all positive arities through m; repeats are retained. -/
abbrev IncTuple {τ : Vocabulary} (D : RelStructure τ) (m : ℕ) :=
  (s : {s : Fin (m+1) // 0 < s.val}) × (Fin s.val.val → D.U)

instance {τ : Vocabulary} (D : RelStructure τ) (m : ℕ) : Fintype (IncTuple D m) :=
  inferInstance

/-- C.3.2: the source-constructed incidence graph, independently of counting equivalence. -/
def incidence {τ : Vocabulary} (D : RelStructure τ) (m : ℕ) : LabelledHost (IncColour τ m) where
  A := D.U
  B := IncTuple D m
  edge col u t := ∃ h : col.s.val = t.1.val.val,
    (∀ j : Fin col.s.val, j ∈ col.positions ↔ t.2 (Fin.cast h j) = u) ∧
    (∀ R : {R : τ.R // τ.arity R = col.s.val}, R ∈ col.symbols ↔
      D.relation R.val (fun j => t.2 (Fin.cast (R.property.trans h) j)))

end SymmetricDepthHierarchy.ConstantDepth.Supplement


