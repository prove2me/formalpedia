-- Prove2me | Definitions.Def_LeanPool_PureNock_Verb
-- name    : LeanPool_PureNock_Verb
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:59:27.066509+00:00
-- url     : https://prove2.me/theorems/69bb22ed-3964-4b9c-87a4-d62bb55b0312
-- title:
--   Verb
-- statement:
--   Definitions and structural lemmas for Verb, from Pure Nock formalization contributors; LeanPool contributors's pinned Pure Nock semantics, trace certificates, and polynomial fingerprints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Nock
inductive Action where
  | null    -- ⊥
  | star    -- *
  | wut     -- ?
  | equal   -- =
  | slot    -- /
  | edit    -- #
  | minus   -- -
deriving Repr, DecidableEq, Inhabited
def Action.isNull : Action → Bool
  | .null => true
  | _     => false
def Action.isOperator : Action → Bool
  | .null => false
  | .star => false
  | _     => true
inductive Verb where
  | leaf : Nat → Verb
  | node : Action → Verb → Verb → Verb
deriving Repr, DecidableEq, Inhabited
namespace Verb
def noun : Verb → Noun
  | .leaf n     => .atom n
  | .node _ l r => .cell l.noun r.noun
def leaves : Verb → Nat
  | .leaf _     => 1
  | .node _ l r => l.leaves + r.leaves
def isCell : Verb → Bool
  | .node _ _ _ => true
  | .leaf _     => false
def rootAction : Verb → Option Action
  | .node a _ _ => some a
  | .leaf _     => none
def isStar : Verb → Bool
  | .node .star _ _ => true
  | _               => false
def isPending : Verb → Bool
  | .node a _ _ => !a.isNull
  | .leaf _     => false
def isTerminal : Verb → Bool
  | .leaf _     => true
  | .node a l r => a.isNull && isTerminal l && isTerminal r
def enum : Verb → Nat → Nat × List (Nat × Verb)
  | .leaf _,     c => (c, [])
  | .node a l r, c =>
      let e1 := enum l (c + 1)
      let e2 := enum r e1.1
      (e2.1, (c, .node a l r) :: (e1.2 ++ e2.2))
def nodes (v : Verb) : List (Nat × Verb) := (enum v 0).2
def findAt : Nat → List (Nat × Verb) → Option Verb
  | _, []          => none
  | i, (j, v) :: t => if i = j then some v else findAt i t
def map (i : Nat) (v : Verb) : Option Verb := findAt i (nodes v)
def maximumPendingIndex : List (Nat × Verb) → Option Nat
  | []          => none
  | (i, v) :: t =>
      let rest := maximumPendingIndex t
      if v.isPending then
        some (match rest with | none => i | some j => Nat.max i j)
      else rest
def getIndex (v : Verb) : Option Nat := maximumPendingIndex (nodes v)
def replaceAux (i : Nat) (new : Verb) : Verb → Nat → Nat × Verb
  | .leaf n,     c => (c, .leaf n)
  | .node a l r, c =>
      let e1 := replaceAux i new l (c + 1)
      let e2 := replaceAux i new r e1.1
      (e2.1, if c = i then new else .node a e1.2 e2.2)
def replaceAt (i : Nat) (v new : Verb) : Verb := (replaceAux i new v 0).2
def opHeadOk : Verb → Bool
  | .leaf k     => k < 11
  | .node _ _ _ => true
def inOpcodeDomain : Verb → Bool
  | .node .star n1 (.node ra i n2) =>
      isTerminal n1
        && ra.isNull
        && isTerminal i && isTerminal n2 && opHeadOk i
  | _ => false
def opReady : Verb → Bool
  | .node a l r => a.isOperator && isTerminal l && isTerminal r
  | .leaf _     => false
def inDomain (v : Verb) : Bool := inOpcodeDomain v || opReady v
def redex : Verb → Option Verb
  | .node .star n1 (.node _ i n2) =>
      match i with
      | .node _ _ _ =>                                  -- main.tex:1075  cons (type(i)=cell)
          some (.node .null (.node .star n1 i) (.node .star n1 n2))
      | .leaf op =>
          match op with
          | 0 =>                                        -- main.tex:1061  OP₀ : → /(n₂,n₁)
              some (.node .slot n2 n1)
          | 1 => some n2                                -- main.tex:1062  OP₁ : → n₂
          | 2 => match n2 with                          -- main.tex:1063  OP₂ : → *[*[n₁,h],*[n₁,t]]
                 | .node _ b c =>
                     some (.node .star (.node .star n1 b) (.node .star n1 c))
                 | _ => none
          | 3 =>                                        -- main.tex:1064  OP₃ : → -[3, *[n₁,n₂]] =
            -- ?(*[n₁,n₂])
              some (.node .minus (.leaf 3) (.node .star n1 n2))
          | 4 =>                                        -- main.tex:1065  OP₄ : → -[4, *[n₁,n₂]] =
            -- +(*[n₁,n₂])
              some (.node .minus (.leaf 4) (.node .star n1 n2))
          | 5 => match n2 with                          -- main.tex:1066  OP₅ : → =(*[n₁,h],*[n₁,t])
                 | .node _ b c =>
                     some (.node .equal (.node .star n1 b) (.node .star n1 c))
                 | _ => none
          | 6 => match n2 with                          -- main.tex:1067  OP₆ (if-then-else macro)
                 | .node _ b c =>
                     -- b = head(n₂), c = tail(n₂);
                     -- → *[n₁, *[c, [0, *[[2,3], [0, *[n₁,[4,[4,b]]]]]]]]
                     let inner := Verb.node .star n1
                                    (.node .null (.leaf 4) (.node .null (.leaf 4) b))
                     let d0    := Verb.node .null (.leaf 0) inner
                     let c0    := Verb.node .star (.node .null (.leaf 2) (.leaf 3)) d0
                     let b0    := Verb.node .null (.leaf 0) c0
                     let a0    := Verb.node .star c b0
                     some (.node .star n1 a0)
                 | _ => none
          | 7 => match n2 with                          -- main.tex:1068  OP₇ : → *[*[n₁,h],t]
                 | .node _ b c => some (.node .star (.node .star n1 b) c)
                 | _ => none
          | 8 => match n2 with                          -- main.tex:1069  OP₈ : → *[[*[n₁,h],n₁],t]
                 | .node _ b c =>
                     some (.node .star (.node .null (.node .star n1 b) n1) c)
                 | _ => none
          | 9 => match n2 with                          -- main.tex:1070  OP₉ : → *[*[n₁,t], 2,
            -- [[0,1],0,h]]
                 | .node _ b c =>
                     -- b = head(n₂), c = tail(n₂)
                     let core := Verb.node .star n1 c
                     let f01  := Verb.node .null (.leaf 0) (.leaf 1)
                     let f0h  := Verb.node .null (.leaf 0) b
                     let form := Verb.node .null (.leaf 2) (.node .null f01 f0h)
                     some (.node .star core form)
                 | _ => none
          | 10 => match n2 with                         -- main.tex:1071  OP₁₀ : → #[hh(n₂),
            -- *[n₁,th(n₂)], *[n₁,t(n₂)]]
                  | .node _ hd d =>
                      match hd with
                      | .node _ ax c =>
                          some (.node .edit ax
                                  (.node .null (.node .star n1 c) (.node .star n1 d)))
                      | _ => none
                  | _ => none
          | _ => none                                   -- i ∉ [11] ⇒ crash
  | _ => none
def ofNoun : Noun → Verb
  | .atom k   => .leaf k
  | .cell l r => .node .null (ofNoun l) (ofNoun r)
def reduce : Verb → Option Verb
  | .node .star n1 t     => redex (.node .star n1 t)                    -- opcode step
  | .node .equal l r     => some (ofNoun (Noun.tis l.noun r.noun))      -- main.tex:1525  =
  | .node .slot l r      =>                                             -- main.tex:1537  /
      match l.noun with
      | .atom ax => (Noun.slot ax r.noun).map ofNoun
      | _        => none
  | .node .edit l r      =>                                             -- main.tex:1587  #
      match l.noun, r with
      | .atom ax, .node _ nw od => (Noun.edit ax nw.noun od.noun).map ofNoun
      | _,        _             => none
  | .node .minus l r     =>                                             -- main.tex:1618  -
      match l.noun with
      | .atom 3 => some (ofNoun (Noun.wut r.noun))                      --   -[3,·] = ?(·)
      | .atom 4 => (Noun.lus r.noun).map ofNoun                         --   -[4,·] = +(·)
      | _       => none
  | .node .wut _ _       => none                                        -- unreachable, see note 2a
  | .node .null _ _      => none
  | .leaf _              => none
def next (v : Verb) : Option Verb :=
  match getIndex v with
  | none   => none
  | some i =>
      match map i v with
      | none     => none
      | some sub =>
          if inDomain sub then
            match reduce sub with
            | some r => some (replaceAt i v r)
            | none   => none
          else none
def program (subject formula : Noun) : Verb :=
  .node .star (ofNoun subject) (ofNoun formula)
def result (v : Verb) : Option Noun :=
  if v.isTerminal then some v.noun else none
def run : Nat → Verb → Option Noun
  | 0,        _ => none
  | fuel + 1, v =>
      match next v with
      | some v' => run fuel v'
      | none    => result v
def runProgram (fuel : Nat) (subject formula : Noun) : Option Noun :=
  run fuel (program subject formula)
structure StrictSelect (lt : Nat → Nat → Prop) : Prop where
  irrefl : ∀ i, ¬ lt i i
  trans  : ∀ {i j k}, lt i j → lt j k → lt i k
  total  : ∀ {i j}, i ≠ j → lt i j ∨ lt j i
def IsPendingIdx (a : Verb) (i : Nat) : Prop :=
  ∃ v, map i a = some v ∧ v.isPending = true
def IsMaxPending (lt : Nat → Nat → Prop) (a : Verb) (i : Nat) : Prop :=
  IsPendingIdx a i ∧ ∀ j, IsPendingIdx a j → ¬ lt i j
def SelStep (lt : Nat → Nat → Prop) (a b : Verb) : Prop :=
  ∃ i sub r, IsMaxPending lt a i ∧ map i a = some sub ∧ inDomain sub = true
             ∧ reduce sub = some r ∧ b = replaceAt i a r
abbrev dfsLt : Nat → Nat → Prop := (· < ·)
def emptyLt : Nat → Nat → Prop := fun _ _ => False
def twoRedex : Verb :=
  .node .null
    (.node .star (.leaf 0) (.node .null (.leaf 1) (.leaf 5)))
    (.node .star (.leaf 0) (.node .null (.leaf 1) (.leaf 5)))
def reduceROM : Verb → Option Verb
  | .node .star _ (.node _ (.leaf 10) _) => none   -- (i) OP₁₀ opcode excluded (main.tex:1160)
  | .node .edit _ _                      => none   -- (ii) the `#`/edit write step excluded
  | v => reduce v
def nextROM (v : Verb) : Option Verb :=
  match getIndex v with
  | none   => none
  | some i =>
      match map i v with
      | none     => none
      | some sub =>
          if inDomain sub then
            match reduceROM sub with
            | some r => some (replaceAt i v r)
            | none   => none
          else none
def NockCheck (Ti : Verb) (Tnext : Option Verb) : Bool :=
  match getIndex Ti with
  | none   => false                                        -- terminal `Ti`: no transition
  | some i =>
      match map i Ti with
      | none    => false                                   -- (unreachable: `getIndex ⇒ node`)
      | some Fi =>
          match inDomain Fi, reduce Fi with
          -- main.tex:1642,1653,1657  genuine step: frame-preserving splice of the rewrite
          | true,  some Fnext => decide (Tnext = some (replaceAt i Ti Fnext))
          -- main.tex:1644,1650    crash: selected redex reduces to ⊥
          | true,  none       => decide (Tnext = none)
          -- main.tex:1643,1649    crash: selected `Fᵢ` is a non-redex / out of domain
          | false, _          => decide (Tnext = none)
def Crashes (Ti : Verb) : Prop := getIndex Ti ≠ none ∧ next Ti = none
def FrameAgree (i : Nat) (Ti Tj : Verb) : Prop := ∃ Fj, Tj = replaceAt i Ti Fj
inductive Outcome
  | value (n : Noun)   -- terminal reached: the paper's `*[s f] = n`
  | crash              -- stuck, non-terminal reached: the paper's `*[s f] = ⊥` (main.tex:1124)
  | timeout            -- fuel exhausted while the state was still steppable
  deriving Repr, DecidableEq, Inhabited
def haltOutcome (v : Verb) : Outcome :=
  if v.isTerminal then .value v.noun else .crash
def eval : Nat → Verb → Outcome
  | 0,        _ => .timeout
  | fuel + 1, v =>
      match next v with
      | some v' => eval fuel v'
      | none    => haltOutcome v
def evalProgram (fuel : Nat) (subject formula : Noun) : Outcome :=
  eval fuel (program subject formula)
end Verb
end Nock


