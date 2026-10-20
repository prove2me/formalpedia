-- Prove2me | Definitions.Def_Bagaria_arena
-- name    : Bagaria_arena
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-19T23:05:23.842152+00:00
-- url     : https://prove2.me/theorems/4303b6bc-02c5-4b73-a74f-84420c575634
-- title:
--   Formulas, elementary embeddings, and the universe of set theory
-- statement:
--   The arena of the large cardinal hierarchies beyond Choice. A first-order formula of set theory is built from membership and equality between de Bruijn-indexed variables by negation, disjunction, and existential quantification, and satisfaction is Tarski's: an existential quantifier binds index zero and shifts the remaining indices. A map between two membership structures is elementary when it preserves the satisfaction of every formula under every assignment. The universe of set theory is an abstract structure: a carrier with a membership relation, a rank function into the ordinals, and a system of ordinal codes, obeying that membership strictly decreases rank, that membership between ordinal codes agrees with the ordinal order, and that the code of an ordinal carries that ordinal as its rank. The rank segment below an ordinal α is the collection of elements of rank smaller than α, with membership inherited from the universe; the two-step rank segment below the double successor of l is the analogue of V_{l+2}. The structure satisfies ZF when the semantic first-order axioms hold: extensionality, pairing, union, infinity, power set, foundation, and the separation and replacement schemes over all formulas and assignments, with no form of Choice. The critical point of a self-embedding of the universe, or of a rank segment, is the least ordinal whose code the embedding moves.
-- source:
--   Bagaria (2017), Large Cardinals beyond Choice, AILA XXVI slides, pp. 8-16, background definitions; satisfaction and ZF after Tarski

import Mathlib

universe u v

/-!
# Large cardinals beyond Choice: the arena

First-order formulas of set theory with Tarski satisfaction, elementary maps
between membership structures, the semantic first-order ZF axioms without
Choice, and an abstract universe of set theory with rank segments, ordinal
codes, and critical points of self-embeddings. This is the arena in which
the Reinhardt and Berkeley hierarchies of the source live.
-/

namespace Bagaria

/-- An abstract universe of set theory: a carrier with a membership
relation, a rank function into the ordinals, and a system of ordinal
codes. The fields assert that membership strictly decreases rank
(mem_rank), that membership between ordinal codes agrees with the ordinal
order (mem_ord), and that the code of an ordinal carries that ordinal as
its rank (rank_ord). The intended model is the class V of all sets, read
at one universe level. -/
structure Universe where
  carrier : Type (v + 1)
  mem : carrier → carrier → Prop
  rank : carrier → Ordinal.{v}
  ord : Ordinal.{v} → carrier
  mem_rank : ∀ (x y : carrier), mem x y → rank x < rank y
  mem_ord : ∀ (α β : Ordinal.{v}), mem (ord α) (ord β) ↔ α < β
  rank_ord : ∀ (α : Ordinal.{v}), rank (ord α) = α

namespace Universe

/-- A first-order formula in the language of set theory, with variables
indexed by de Bruijn indices. -/
inductive SetFormula : Type
  | mem : ℕ → ℕ → SetFormula
  | eq : ℕ → ℕ → SetFormula
  | not : SetFormula → SetFormula
  | or : SetFormula → SetFormula → SetFormula
  | ex : SetFormula → SetFormula

/-- Tarski satisfaction of a formula under a membership relation and an
assignment of elements to variable indices. The existential quantifier
binds de Bruijn index 0, shifting the remaining indices by one. -/
def holds {α : Type u} (mem : α → α → Prop) (s : ℕ → α) : SetFormula → Prop
  | .mem i j => mem (s i) (s j)
  | .eq i j => s i = s j
  | .not f => ¬ holds mem s f
  | .or f g => holds mem s f ∨ holds mem s g
  | .ex f => ∃ x : α, holds mem (fun n => if n = 0 then x else s (n - 1)) f

/-- A map between two membership structures is elementary when it
preserves the satisfaction of every formula under every assignment. -/
def IsElementaryOf {α β : Type u} (memA : α → α → Prop) (memB : β → β → Prop)
    (j : α → β) : Prop :=
  ∀ (φ : SetFormula) (s : ℕ → α),
    holds memA s φ ↔ holds memB (fun n => j (s n)) φ

/-- The semantic first-order ZF axioms without Choice for a membership
structure: extensionality, pairing, union, infinity, power set, and
foundation, together with the separation and replacement schemes over all
formulas and assignments. No form of Choice is assumed. -/
def SatisfiesZF {α : Type u} (mem : α → α → Prop) : Prop :=
  (∀ x y : α, (∀ z : α, mem z x ↔ mem z y) → x = y) ∧
  (∀ x y : α, ∃ p : α, ∀ z : α, mem z p ↔ (z = x ∨ z = y)) ∧
  (∀ x : α, ∃ u : α, ∀ z : α, mem z u ↔ ∃ y : α, mem y x ∧ mem z y) ∧
  (∃ i : α, ∃ z : α, mem z i ∧
    ∀ x : α, mem x i → ∃ y : α, mem y i ∧ mem x y ∧
      ∀ w : α, mem w x → mem w y) ∧
  (∀ x : α, ∃ p : α, ∀ z : α, mem z p ↔ ∀ w : α, mem w z → mem w x) ∧
  (∀ x : α, (∃ z : α, mem z x) →
    ∃ m : α, mem m x ∧ ∀ w : α, mem w x → ¬ mem w m) ∧
  (∀ (φ : SetFormula) (s : ℕ → α) (a : α),
    ∃ b : α, ∀ x : α, mem x b ↔
      (mem x a ∧ holds mem (fun n => if n = 0 then x else s (n - 1)) φ)) ∧
  (∀ (φ : SetFormula) (s : ℕ → α) (a : α),
    (∀ x : α, mem x a → ∃! y : α,
      holds mem (fun n => if n = 0 then x else if n = 1 then y else s (n - 2)) φ) →
    ∃ b : α, ∀ y : α, mem y b ↔ ∃ x : α, mem x a ∧
      holds mem (fun n => if n = 0 then x else if n = 1 then y else s (n - 2)) φ)

/-! ## Rank segments, ordinal codes, and critical points -/

variable (U : Universe.{v})

/-- The rank segment below an ordinal: the elements of the universe whose
rank is smaller than the ordinal, with membership inherited from the
universe. This is the abstract analogue of the cumulative hierarchy set
V_α. -/
def segment (α : Ordinal.{v}) : Type (v + 1) :=
  {x : U.carrier // U.rank x < α}

/-- Membership restricted to the rank segment below α. -/
def segmentMem (α : Ordinal.{v}) :
    U.segment α → U.segment α → Prop :=
  fun x y => U.mem x.val y.val

/-- The ordinal successor, self-contained: the ordinal α + 1. The
universe is taken as an explicit argument so that the successor is
reachable by field notation on a universe; the argument is unused in the
body. -/
noncomputable def succ (_Univ : Universe.{v}) (α : Ordinal.{v}) : Ordinal.{v} :=
  α + 1

/-- The two-step rank segment below the double successor of an ordinal:
the abstract analogue of the set V_{l+2}. -/
abbrev segmentOfSuccSucc (l : Ordinal.{v}) : Type (v + 1) :=
  U.segment (U.succ (U.succ l))

/-- The code of the ordinal β, as a member of the rank segment below α.
The argument h certifies that β lies below α. -/
def segOrd (α β : Ordinal.{v}) (h : β < α) : U.segment α :=
  ⟨U.ord β, by rw [U.rank_ord]; exact h⟩

/-- The critical point of a self-embedding of the universe: the least
ordinal whose code the embedding moves, fixing the code of every smaller
ordinal. -/
def critIs (j : U.carrier → U.carrier) (κ : Ordinal.{v}) : Prop :=
  j (U.ord κ) ≠ U.ord κ ∧
    ∀ α : Ordinal.{v}, α < κ → j (U.ord α) = U.ord α

/-- The critical point of a self-embedding of a rank segment: the least
ordinal whose code inside the segment the embedding moves, fixing the
code of every smaller ordinal inside the segment. -/
def critIsIn (α : Ordinal.{v}) (j : U.segment α → U.segment α)
    (κ : Ordinal.{v}) : Prop :=
  ∃ hκ : κ < α,
    (j (U.segOrd α κ hκ)).val ≠ U.ord κ ∧
    ∀ β : Ordinal.{v}, β < κ → ∀ hβ : β < α,
      (j (U.segOrd α β hβ)).val = U.ord β

end Universe

end Bagaria


