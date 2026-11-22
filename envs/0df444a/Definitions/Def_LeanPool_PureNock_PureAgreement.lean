-- Prove2me | Definitions.Def_LeanPool_PureNock_PureAgreement
-- name    : LeanPool_PureNock_PureAgreement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:00:03.940699+00:00
-- url     : https://prove2.me/theorems/743678e4-1796-41d0-82f7-1f1b51b11871
-- title:
--   Pure Agreement
-- statement:
--   Definitions and structural lemmas for Pure Agreement, from Pure Nock formalization contributors; LeanPool contributors's pinned Pure Nock semantics, trace certificates, and polynomial fingerprints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Nock
namespace Verb
open Noun
def denP : Nat → Verb → Option Noun
  | _,        .leaf k       => some (.atom k)
  | 0,        .node _ _ _   => none
  | fuel + 1, .node act l r =>
      match act with
      | .null  =>
          match denP fuel l, denP fuel r with
          | some a, some b => some (.cell a b)
          | _, _           => none
      | .star  =>
          match denP fuel l, denP fuel r with
          | some a, some b => evalPaper fuel a b
          | _, _           => none
      | .slot  =>
          match denP fuel l, denP fuel r with
          | some (.atom ax), some b => Noun.slot ax b
          | _, _                    => none
      | .equal =>
          match denP fuel l, denP fuel r with
          | some a, some b => some (Noun.tis a b)
          | _, _           => none
      | .minus =>
          match denP fuel l, denP fuel r with
          | some (.atom 3), some b => some (Noun.wut b)
          | some (.atom 4), some b => Noun.lus b
          | _, _                   => none
      | .edit  =>
          match r with
          | .node _ nw od =>
              match denP fuel l, denP fuel nw, denP fuel od with
              | some (.atom ax), some n, some o => Noun.edit ax n o
              | _, _, _                          => none
          | .leaf _ => none
      | .wut   => none
def DenP (v : Verb) (x : Noun) : Prop := ∃ fuel, denP fuel v = some x
def EvP (a b x : Noun) : Prop := ∃ fuel, evalPaper fuel a b = some x
def isHintRedex : Verb → Bool
  | .node .star n1 (.node ra (.leaf 11) (.node rn h b)) =>
      isTerminal n1 && ra.isNull && isTerminal (.node rn h b)
  | _ => false
def hintExpand : Verb → Option Verb
  | .node .star n1 (.node ra (.leaf 11) n2) =>
      if isTerminal n1 && ra.isNull && isTerminal n2 then
        match n2 with
        | .node _ (.node _ _ clue) body =>            -- dynamic: [11 [t c] d]
            some (.node .star n1
              (.node .null (.leaf 8)
                (.node .null clue
                  (.node .null (.leaf 7)
                    (.node .null (.node .null (.leaf 0) (.leaf 3)) body)))))
        | .node _ (.leaf _) body =>                   -- static: [11 t d]
            some (.node .star n1 body)
        | _ => none
      else none
  | _ => none
def redexHint (v : Verb) : Option Verb :=
  match hintExpand v with
  | some v' => some v'
  | none    => reduce v
def inDomainHint (v : Verb) : Bool := inDomain v || isHintRedex v
def nextHint (v : Verb) : Option Verb :=
  match getIndex v with
  | none   => none
  | some i =>
      match map i v with
      | none     => none
      | some sub =>
          if inDomainHint sub then
            match redexHint sub with
            | some r => some (replaceAt i v r)
            | none   => none
          else none
def runHint : Nat → Verb → Option Noun
  | 0,        _ => none
  | fuel + 1, v =>
      match nextHint v with
      | some v' => runHint fuel v'
      | none    => result v
def runHintProgram (fuel : Nat) (subject formula : Noun) : Option Noun :=
  runHint fuel (program subject formula)
def hintProgStatic : Noun := .cell (.atom 11) (.cell (.atom 33) (.cell (.atom 0) (.atom 1)))
def hintProgDyn : Noun :=
  .cell (.atom 11)
    (.cell (.cell (.atom 1) (.cell (.atom 1) (.atom 33)))
      (.cell (.atom 0) (.atom 1)))
def hintProgInc : Noun :=
  .cell (.atom 11)
    (.cell (.cell (.atom 1) (.cell (.atom 1) (.atom 33)))
      (.cell (.atom 4) (.cell (.atom 0) (.atom 1))))
def HintComplete : Prop :=
  ∀ s f r : Noun, (∃ fuel, evalN fuel s f = some r) → (∃ fuel, runHintProgram fuel s f = some r)
def PaperComplete : Prop :=
  ∀ s f r : Noun, (∃ fuel, evalPaper fuel s f = some r) → (∃ fuel, runProgram fuel s f = some r)
def PaperSound : Prop :=
  ∀ s f r : Noun, (∃ fuel, runProgram fuel s f = some r) → (∃ fuel, evalPaper fuel s f = some r)
inductive RelP : Verb → Verb → Prop where
  | leaf {k} : RelP (.leaf k) (.leaf k)
  | base {v w} : v.isPending = true → (∀ x, DenP v x ↔ DenP w x) → RelP v w
  | cong {a l l' r r'} : RelP l l' → RelP r r' → RelP (.node a l r) (.node a l' r')
def pcost : Nat → Noun → Noun → Nat
  | 0, _, _ => 0
  | _ + 1, _, .atom _ => 0
  | f + 1, subj, .cell (.cell b c) d =>
      1 + pcost f subj (.cell b c) + pcost f subj d
  | f + 1, subj, .cell (.atom op) tail =>
    match op with
    | 0 => 2
    | 1 => 1
    | 2 =>
        match tail with
        | .cell b c =>
            let inner := match evalPaper f subj b, evalPaper f subj c with
                         | some sb, some sc => pcost f sb sc
                         | _, _ => 0
            1 + pcost f subj b + pcost f subj c + inner
        | _ => 0
    | 3 => 2 + pcost f subj tail
    | 4 => 2 + pcost f subj tail
    | 5 =>
        match tail with
        | .cell b c => 2 + pcost f subj b + pcost f subj c
        | _ => 0
    | 6 =>
        match tail with
        | .cell b (.cell c d) =>
            let inner := match evalPaper f subj b with
                         | some (.atom 0) => pcost f subj c
                         | some (.atom 1) => pcost f subj d
                         | _ => 0
            100 + pcost f subj b + inner
        | _ => 0
    | 7 =>
        match tail with
        | .cell b c =>
            let inner := match evalPaper f subj b with
                         | some sb => pcost f sb c
                         | _ => 0
            1 + pcost f subj b + inner
        | _ => 0
    | 8 =>
        match tail with
        | .cell b c =>
            let inner := match evalPaper f subj b with
                         | some sb => pcost f (.cell sb subj) c
                         | _ => 0
            1 + pcost f subj b + inner
        | _ => 0
    | 9 =>
        match tail with
        | .cell (.atom ax) c =>
            let inner := match evalPaper f subj c with
                         | some core =>
                             match Noun.slot ax core with
                             | some arm => pcost f core arm
                             | _ => 0
                         | _ => 0
            20 + pcost f subj c + inner
        | _ => 0
    | 10 =>
        match tail with
        | .cell (.cell (.atom _) c) d => 2 + pcost f subj c + pcost f subj d
        | _ => 0
    | _ => 0
def vcost (F : Nat) : Verb → Nat
  | .leaf _ => 0
  | .node a l r =>
      (match a with
       | .star => match denP F l, denP F r with
                  | some sa, some fo => pcost F sa fo
                  | _, _ => 0
       | .slot => 1
       | .equal => 1
       | .minus => 1
       | .edit => 1
       | .null => 0
       | .wut => 0) + vcost F l + vcost F r
end Verb
end Nock


