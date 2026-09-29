-- Prove2me | Definitions.Def_Freiman_lowerHistoryModel
-- name    : Freiman_lowerHistoryModel
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T11:51:26.399759+00:00
-- url     : https://prove2.me/theorems/7da71778-770c-4871-876d-bdd30ff3cae2
-- title:
--   Freiman.lowerHistoryModel
-- statement:
--   Permanent physical-side replay, incoming normalization, marked suffix origins and the complete source-preserving seven-step grammar. Source: Freiman's Hall ray: Proof report and corrected English text (8 September 2026); history_certificates.tex app:all-suffix-histories, global_selection.tex lem:global-suffix-targets; initial_bridges.tex lem:H-entry-bridges; certificates/target_selection/all_suffix_histories_printed.json.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Appendix app:all-suffix-histories and its exact arithmetic/certificate guide.

import Definitions.Def_Freiman_lowerHistoryAlgebra

namespace Freiman

inductive LowerHistoryCatalog where
  | left | right | mixed | rightMixed | initial
  deriving DecidableEq, Inhabited

structure LowerHistoryPath where
  catalog : LowerHistoryCatalog
  id : ℕ
  context : List ℕ+
  entry : LowerLabel
  initialWider : Bool
  steps : List (LowerLabel × Bool)
  finalSuffixes : LowerPair
  finalParity : Bool × Bool
  finalWider : Bool
  row : ℕ
  rectangle : CertRectangle
  alternatives : ℕ
  deriving DecidableEq

structure LowerHistoryRecord where
  catalog : LowerHistoryCatalog
  pathId : ℕ
  alternative : ℕ
  endpointBranch : ℤ
  survivor : Bool
  premiseId : ℕ
  witnessId : ℕ
  deriving DecidableEq, Inhabited

def lowerHistoryHazard (row : ℕ) (p : LowerPair) : Prop :=
  match row with
  | 1 => ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerLStar p
  | 2 => ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ lowerRStar p
  | 3 => lowerMixed p ∧ ¬ lowerH p 2 ∧ ¬ lowerH p 5 ∧ lowerLStar p
  | 4 => lowerMixed p ∧ ¬ lowerH p 2 ∧ ¬ lowerH p 5 ∧ lowerRStar p
  | _ => False

def lowerHistoryTarget (row : ℕ) (p : LowerPair) (t : ℝ) : Prop :=
  match row with
  | 1 => lowerLocalLower p ([2],[1]) ≤ lowerLocalCoordinate p t
  | 2 => lowerLocalLower p ([2],[2]) ≤ lowerLocalCoordinate p t
  | 3 => lowerLocalLower p ([2],[2]) ≤ lowerLocalCoordinate p t
  | _ => False

def lowerHistoryOrient (p : LowerPair) (flip : Bool) : LowerPair :=
  if flip then (p.2,p.1) else p

def lowerHistoryRawStep (p : LowerPair) (wider : Bool) (l : LowerLabel) : LowerPair :=
  if wider then (p.1 ++ l.2,p.2 ++ l.1.reverse)
  else (p.1 ++ l.1.reverse,p.2 ++ l.2)

def lowerHistoryReplay (base : LowerPair) (path : LowerHistoryPath) (n : ℕ) : LowerPair × Bool :=
  (path.steps.take n).foldl (fun s step =>
    (lowerHistoryRawStep s.1 s.2 step.1, if step.2 then !s.2 else s.2))
    (lowerHistoryRawStep base false path.entry,path.initialWider)

def lowerHistoryWiderCompatible (p : LowerPair) (wider : Bool) : Prop :=
  if wider then lowerWidth p.1 ≤ lowerWidth p.2 else lowerWidth p.2 ≤ lowerWidth p.1

def lowerHistorySuffixContext (w ctx : List ℕ+) : Prop :=
  lowerEnds w ctx ∧ (lowerEnds w [3] ↔ lowerEnds ctx [3]) ∧
    (lowerEnds w [3,1] ↔ lowerEnds ctx [3,1])

def lowerHistoryRealizes (h : ℕ → LowerPair) (start : ℕ) (base : LowerPair)
    (flip : Bool) (path : LowerHistoryPath) : Prop :=
  lowerHistorySuffixContext base.1 path.context ∧
  (if path.catalog = .initial then lowerEnds base.2 [3,1,3]
    else lowerEnds base.2 [3,1] ∧ ¬ lowerEnds base.2 [3,1,3,1]) ∧
  base.1.length % 2 = base.2.length % 2 ∧
  ∀ j : ℕ, j ≤ path.steps.length →
    lowerHistoryOrient (lowerPhysicalPath h (start+j)) flip = (lowerHistoryReplay base path j).1 ∧
    lowerHistoryWiderCompatible (lowerHistoryReplay base path j).1 (lowerHistoryReplay base path j).2 ∧
    lowerNormalize (h (start+j)) = lowerHistoryOrient
      (lowerHistoryReplay base path j).1 (lowerHistoryReplay base path j).2

def lowerHistoryReached (t : ℝ) (h : ℕ → LowerPair) (n : ℕ)
    (base : LowerPair) (path : LowerHistoryPath) : Prop :=
  ∃ start : ℕ, ∃ flip : Bool, start + path.steps.length = n ∧
    lowerHistoryRealizes h start base flip path ∧
    (if path.catalog = .initial then start = 0 ∧
      ∃ (f : LowerInitialFamily) (a k p : ℕ),
        ((f = .A ∧ k = 0) ∨ (f = .B ∧ k = 0) ∨ (f = .C ∧ p = 0)) ∧
        lowerInitialBaseSelected t f a k p ∧
        base = lowerNormalize (lowerFamilyPair f a k p) ∧
        h 0 = lowerChild (lowerFamilyPair f a k p) path.entry
     else 0 < start ∧ base = lowerNormalize (h (start-1)) ∧
       lowerHistoryOrient (lowerPhysicalPath h (start-1)) flip = base ∧
       path.entry = ([2],[3]))

def lowerHistoryContextWords : List (List ℕ+) := [[1],[2],[3],[3,1],[3,1,3],[3,1,3,1]]
def lowerHistoryLabels : List LowerLabel :=
  [([1],[]),([2],[]),([3],[]),([],[1]),([2],[1]),([3],[1])]

structure LowerHistoryState where
  context : LowerHistoryContext
  wider : Bool
  markedDone : Bool
  previous : Option (Bool × LowerLabel × Bool)
  deriving DecidableEq

def lowerHistoryInitialState (p : LowerHistoryPath) : LowerHistoryState :=
  let base : LowerPair := (p.context,if p.catalog = .initial then [3,1,3] else [3,1])
  ⟨⟨lowerHistoryRawStep base false p.entry,
    (decide (p.entry.1.length % 2 = 1),decide (p.entry.2.length % 2 = 1))⟩,
    p.initialWider,decide (p.catalog = .initial ∧ p.entry.2 ≠ []),none⟩

def lowerHistoryAdvance (s : LowerHistoryState) (l : LowerLabel) (reflect : Bool) : LowerHistoryState :=
  let extra := lowerHistoryRawStep ([],[]) s.wider l
  ⟨⟨lowerHistoryRawStep s.context.words s.wider l,
    (xor s.context.parity.1 (decide (extra.1.length % 2 = 1)),
     xor s.context.parity.2 (decide (extra.2.length % 2 = 1)))⟩,
    xor s.wider reflect,s.markedDone || decide (extra.2 ≠ []),some (s.wider,l,reflect)⟩

def lowerHistoryForbidden (w : List ℕ+) : Bool :=
  (List.range (w.length+1)).any fun n => decide ((w.drop n).take 5 = [3,1,3,1,3])

def lowerHistoryStepLegal (s : LowerHistoryState) (l : LowerLabel) (reflect : Bool) : Prop :=
  let extra := lowerHistoryRawStep ([],[]) s.wider l
  let next := lowerHistoryAdvance s l reflect
  l ∈ lowerHistoryLabels ∧
  (l.1 = [] → s.context.parity.1 ≠ s.context.parity.2) ∧
  (l.1 = [3] → ¬ lowerEnds (lowerHistoryPick s.context.words s.wider) [3,1]) ∧
  (extra.2 = [] ∨ extra.2 = [1]) ∧ (s.markedDone = true → extra.2 = []) ∧
  lowerHistoryForbidden next.context.words.1 = false ∧
  lowerHistoryForbidden next.context.words.2 = false ∧
  (l.1 = [] → reflect = false) ∧
  (l.2 = [] → l.1 = [2] ∨ l.1 = [3] → reflect = true) ∧
  (s.wider = false → extra.2 = [] → l = ([1],[]) →
    s.previous = some (false,([1],[]),false) → next.wider = true)

set_option synthInstance.maxSize 256 in
instance (s : LowerHistoryState) (l : LowerLabel) (r : Bool) :
    Decidable (lowerHistoryStepLegal s l r) := by
  unfold lowerHistoryStepLegal lowerEnds
  dsimp only
  infer_instance

def lowerHistoryLegalSteps : LowerHistoryState → List (LowerLabel × Bool) → Prop
  | _, [] => True
  | s, (l,r)::tail => lowerHistoryStepLegal s l r ∧
    lowerHistoryLegalSteps (lowerHistoryAdvance s l r) tail
def lowerHistoryFinalState (p : LowerHistoryPath) : LowerHistoryState :=
  p.steps.foldl (fun s step => lowerHistoryAdvance s step.1 step.2) (lowerHistoryInitialState p)
def lowerHistoryPathKey (p : LowerHistoryPath) :
    LowerHistoryCatalog × List ℕ+ × LowerLabel × Bool × List (LowerLabel × Bool) :=
  (p.catalog,p.context,p.entry,p.initialWider,p.steps)
def lowerHistoryStructural (p : LowerHistoryPath) : Prop :=
  p.steps.length ≤ 7 ∧
  (if p.catalog = .initial then p.context ∈ [[2],[3]] ∧
    p.entry ∈ [([1],[]),([2],[1]),([3],[1])]
   else p.context ∈ lowerHistoryContextWords ∧ p.entry = ([2],[3])) ∧
  lowerHistoryLegalSteps (lowerHistoryInitialState p) p.steps ∧
  (let s := lowerHistoryFinalState p
   s.markedDone = true ∧ s.context.words = p.finalSuffixes ∧
   s.context.parity = p.finalParity ∧ s.wider = p.finalWider) ∧
  (if p.catalog = .initial then
    (p.row = (if p.finalParity.1 = p.finalParity.2 then
      if p.finalWider then 1 else 2 else if p.finalWider then 3 else 4))
   else
    (p.catalog = .left ∧ p.row = 1 ∧ p.finalParity = (false,false) ∧ p.finalWider = true) ∨
    (p.catalog = .right ∧ p.row = 2 ∧ p.finalParity = (false,false) ∧ p.finalWider = false) ∨
    (p.catalog = .mixed ∧ p.row = 3 ∧ p.finalParity = (true,false) ∧ p.finalWider = true) ∨
    (p.catalog = .rightMixed ∧ p.row = 4 ∧ p.finalParity = (true,false) ∧ p.finalWider = false))

abbrev LowerHistoryKey :=
  LowerHistoryCatalog × List ℕ+ × LowerLabel × Bool × List (LowerLabel × Bool)
def lowerHistoryTerminal (cat : LowerHistoryCatalog) (s : LowerHistoryState) : Bool :=
  s.markedDone && match cat with
    | .initial => true
    | .left => decide (s.context.parity = (false,false)) && s.wider
    | .right => decide (s.context.parity = (false,false)) && !s.wider
    | .mixed => decide (s.context.parity = (true,false)) && s.wider
    | .rightMixed => decide (s.context.parity = (true,false)) && !s.wider
def lowerHistoryWalkKeys (cat : LowerHistoryCatalog) (ctx : List ℕ+) (entry : LowerLabel)
    (wide : Bool) (s : LowerHistoryState) (steps : List (LowerLabel × Bool)) : ℕ → List LowerHistoryKey
  | 0 => if lowerHistoryTerminal cat s then [(cat,ctx,entry,wide,steps)] else []
  | k+1 =>
    (if lowerHistoryTerminal cat s then [(cat,ctx,entry,wide,steps)] else []) ++
    lowerHistoryLabels.flatMap fun l => [false,true].flatMap fun r =>
      if lowerHistoryStepLegal s l r then
        lowerHistoryWalkKeys cat ctx entry wide (lowerHistoryAdvance s l r) (steps++[(l,r)]) k
      else []
def lowerHistoryGeneratedKeys (cat : LowerHistoryCatalog) : List LowerHistoryKey :=
  let contexts := if cat = .initial then [[2],[3]] else lowerHistoryContextWords
  let entries : List LowerLabel := if cat = .initial then [([1],[]),([2],[1]),([3],[1])] else [([2],[3])]
  contexts.flatMap fun ctx => entries.flatMap fun entry => [false,true].flatMap fun wide =>
    let p : LowerHistoryPath := ⟨cat,0,ctx,entry,wide,[],([],[]),(false,false),false,0,⟨0,1,0,1⟩,0⟩
    lowerHistoryWalkKeys cat ctx entry wide (lowerHistoryInitialState p) [] 7

end Freiman


