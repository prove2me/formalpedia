-- Prove2me | Definitions.Def_LeanPool_PureNock_Agreement
-- name    : LeanPool_PureNock_Agreement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:59:45.661282+00:00
-- url     : https://prove2.me/theorems/fe1a583b-ecaf-4de6-90e6-3c07bf7b2402
-- title:
--   Agreement
-- statement:
--   Definitions and structural lemmas for Agreement, from Pure Nock formalization contributors; LeanPool contributors's pinned Pure Nock semantics, trace certificates, and polynomial fingerprints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Nock
namespace Verb
open Noun
def den : Nat → Verb → Option Noun
  | _,        .leaf k       => some (.atom k)
  | 0,        .node _ _ _   => none
  | fuel + 1, .node act l r =>
      match act with
      | .null  =>
          match den fuel l, den fuel r with
          | some a, some b => some (.cell a b)
          | _, _           => none
      | .star  =>
          match den fuel l, den fuel r with
          | some a, some b => evalN fuel a b
          | _, _           => none
      | .slot  =>
          match den fuel l, den fuel r with
          | some (.atom ax), some b => Noun.slot ax b
          | _, _                    => none
      | .equal =>
          match den fuel l, den fuel r with
          | some a, some b => some (Noun.tis a b)
          | _, _           => none
      | .minus =>
          match den fuel l, den fuel r with
          | some (.atom 3), some b => some (Noun.wut b)
          | some (.atom 4), some b => Noun.lus b
          | _, _                   => none
      | .edit  =>
          match r with
          | .node _ nw od =>
              match den fuel l, den fuel nw, den fuel od with
              | some (.atom ax), some n, some o => Noun.edit ax n o
              | _, _, _                          => none
          | .leaf _ => none
      | .wut   => none
def Den (v : Verb) (x : Noun) : Prop := ∃ fuel, den fuel v = some x
def Ev (a b x : Noun) : Prop := ∃ fuel, evalN fuel a b = some x
def editOk : Verb → Bool
  | .leaf _ => true
  | .node a l r =>
      (match a with | .edit => !r.isPending | _ => true) && editOk l && editOk r
inductive Rel : Verb → Verb → Prop where
  | leaf {k} : Rel (.leaf k) (.leaf k)
  | base {v w} : v.isPending = true → (∀ x, Den v x ↔ Den w x) → Rel v w
  | cong {a l l' r r'} : Rel l l' → Rel r r' → Rel (.node a l r) (.node a l' r')
def siblingAxis (ax : Nat) : Nat := if ax % 2 == 0 then ax + 1 else ax - 1
inductive SiblingOf : Nat → Nat → Prop where
  | immediate (a : Nat) : SiblingOf (a + 2) (siblingAxis (a + 2))
  | ancestor (a : Nat) {sib : Nat} : SiblingOf ((a + 2) / 2) sib → SiblingOf (a + 2) sib
end Verb
end Nock


