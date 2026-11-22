-- Prove2me | Definitions.Def_LeanPool_PureNock_Reference
-- name    : LeanPool_PureNock_Reference
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:59:08.912039+00:00
-- url     : https://prove2.me/theorems/63581a9c-8c82-40c7-aa85-ee2ca82fc9ef
-- title:
--   Reference
-- statement:
--   Definitions and structural lemmas for Reference, from Pure Nock formalization contributors; LeanPool contributors's pinned Pure Nock semantics, trace certificates, and polynomial fingerprints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Reference.lean

module
public import Definitions.Def_LeanPool_PureNock_Tree
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Nock
namespace Noun
def wut : Noun → Noun
  | .cell _ _ => .atom 0
  | .atom _   => .atom 1
def lus : Noun → Option Noun
  | .atom n   => some (.atom (n + 1))
  | .cell _ _ => none
def tis (a b : Noun) : Noun :=
  if a = b then .atom 0 else .atom 1
def slot : Nat → Noun → Option Noun
  | 0, _ => none
  | 1, n => some n
  | (a+2), n =>
    match slot ((a+2) / 2) n with
    | some (.cell l r) => some (if (a+2) % 2 == 0 then l else r)
    | _ => none
  termination_by a => a
  decreasing_by omega
def edit : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | 1, new, _ => some new
  | (a+2), new, old =>
    let sibAxis := if (a+2) % 2 == 0 then (a+2) + 1 else (a+2) - 1
    match slot sibAxis old with
    | some sib =>
      let paired := if (a+2) % 2 == 0 then Noun.cell new sib else Noun.cell sib new
      edit ((a+2) / 2) paired old
    | none => none
  termination_by a => a
  decreasing_by omega
end Noun
open Noun
def evalN : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | fuel + 1, subj, .cell (.cell b c) d =>
      -- autocons: the head of the formula is itself a formula ⇒ distribute (Nock's [b c] rule)
      match evalN fuel subj (.cell b c), evalN fuel subj d with
      | some l, some r => some (.cell l r)
      | _, _ => none
  | fuel + 1, subj, .cell (.atom op) tail =>
    match op with
    | 0 => match tail with               -- *[a 0 b] = /[b a]
           | .atom ax => slot ax subj
           | _ => none
    | 1 => some tail                      -- *[a 1 b] = b
    | 2 => match tail with               -- *[a 2 b c] = *[*[a b] *[a c]]
           | .cell b c =>
             match evalN fuel subj b, evalN fuel subj c with
             | some sb, some sc => evalN fuel sb sc
             | _, _ => none
           | _ => none
    | 3 => (evalN fuel subj tail).map wut               -- *[a 3 b] = ?*[a b]
    | 4 => (evalN fuel subj tail).bind lus              -- *[a 4 b] = +*[a b]
    | 5 => match tail with               -- *[a 5 b c] = =[*[a b] *[a c]]
           | .cell b c =>
             match evalN fuel subj b, evalN fuel subj c with
             | some sb, some sc => some (tis sb sc)
             | _, _ => none
           | _ => none
    | 6 => match tail with               -- *[a 6 b c d]  (if b then c else d)
           | .cell b (.cell c d) =>
             match evalN fuel subj b with
             | some (.atom 0) => evalN fuel subj c
             | some (.atom 1) => evalN fuel subj d
             | _ => none
           | _ => none
    | 7 => match tail with               -- *[a 7 b c] = *[*[a b] c]
           | .cell b c =>
             match evalN fuel subj b with
             | some sb => evalN fuel sb c
             | none => none
           | _ => none
    | 8 => match tail with               -- *[a 8 b c] = *[[*[a b] a] c]
           | .cell b c =>
             match evalN fuel subj b with
             | some sb => evalN fuel (.cell sb subj) c
             | none => none
           | _ => none
    | 9 => match tail with               -- *[a 9 b c] = *[*[a c] 2 [0 1] 0 b]
           | .cell (.atom ax) c =>       --   ≡ fetch arm at axis b of core *[a c], run core against
             -- it
             match evalN fuel subj c with
             | some core =>
               match slot ax core with
               | some arm => evalN fuel core arm
               | none => none
             | none => none
           | _ => none
    | 10 => match tail with              -- *[a 10 [b c] d] = #[b *[a c] *[a d]]
            | .cell (.cell (.atom ax) c) d =>
              match evalN fuel subj c, evalN fuel subj d with
              | some new, some old => edit ax new old
              | _, _ => none
            | _ => none
    | 11 => match tail with              -- *[a 11 [b c] d] (dynamic) / *[a 11 b c] (static) — hints
            | .cell (.cell _ clue) body =>
              match evalN fuel subj clue with
              | some _ => evalN fuel subj body
              | none => none
            | .cell (.atom _) body => evalN fuel subj body
            | _ => none
    | _ => none
end Nock


