-- Prove2me | Definitions.Def_Freiman_lowerWordGuards
-- name    : Freiman_lowerWordGuards
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:21:01.656238+00:00
-- url     : https://prove2.me/theorems/341b1a82-1e81-4517-8444-31e9181823bc
-- title:
--   Freiman guarded word selection: lowerWordGuards
-- statement:
--   Finite source guard cases, exact boundary checks and their bridge to the existing offered words. No numerical or language completeness theorem is assumed.
-- source:
--   Freiman report, 'The complete boundary table for selected words', Appendix app:selection-words, report/source/staging/parts/word_certificates.tex; global_selection.tex admissibility argument; certificates/word_selection/selection_words_printed.json, word_guards.json and source_bindings.json; verification/families/word_selection/verify_word_guards.py.

import Definitions.Def_Freiman_lowerCertificates
namespace Freiman
def lowerGuardStates : List (List ℕ+) := [[1],[2],[3],[3,1],[3,1,3],[3,1,3,1]]
def lowerGuardSuffix (w u : List ℕ+) : Bool :=
  decide (u.length ≤ w.length) && decide (w.drop (w.length-u.length) = u)
def lowerGuardState (w : List ℕ+) : List ℕ+ :=
  if lowerGuardSuffix w [3,1,3,1] then [3,1,3,1] else
  if lowerGuardSuffix w [3,1,3] then [3,1,3] else
  if lowerGuardSuffix w [3,1] then [3,1] else
  if lowerGuardSuffix w [3] then [3] else w.drop (w.length-1)
def lowerGuardSafe (w : List ℕ+) : Bool :=
  !((List.range (w.length+1)).any fun i => decide ((w.drop i).take 5 = [3,1,3,1,3]))
def lowerGuardShortLabels : List LowerLabel := [([1],[]),([2],[]),([3],[]),([],[1]),([2],[1]),([3],[1])]
structure LowerGuardCase where
  mixed : Bool
  before : LowerPair
  branch : String
  labels : List LowerLabel
  reason : String
  run : Bool
  deriving DecidableEq
structure LowerGuardPrinted where
  id : ℕ
  contexts : List LowerPair
  mixed : Bool
  branch : String
  labels : List LowerLabel
  reason : String
  run : Bool
  deriving DecidableEq
def lowerGuardExpand (r : LowerGuardPrinted) : List LowerGuardCase :=
  r.contexts.map fun c => ⟨r.mixed,c,r.branch,r.labels,r.reason,r.run⟩
def lowerGuardCaseValid (c : LowerGuardCase) : Prop :=
  c.before.1 ∈ lowerGuardStates ∧ c.before.2 ∈ lowerGuardStates ∧
  (∀ l ∈ c.labels,
    (∀ d ∈ l.1++l.2, (d:ℕ) ≤ 3) ∧ (l.1 ≠ [] ∨ l.2 ≠ []) ∧
    lowerGuardSafe (c.before.1++l.1.reverse) = true ∧
    lowerGuardSafe (c.before.2++l.2) = true ∧
    (∀ right : Bool,
      let old := lowerSide c.before right
      let ext := if right then l.2 else l.1.reverse
      (lowerGuardState (old++ext) = [3,1,3] → ext ≠ [] →
        c.mixed = false ∧ l = ([2],[3]) ∧ right = true ∧ lowerGuardSuffix old [3,1] = true) ∧
      (lowerGuardState (old++ext) = [3,1,3,1] → ext ≠ [] → old = [3,1,3] ∧ ext = [1]) ∧
      (old ∈ [[3,1,3],[3,1,3,1]] → lowerGuardState (old++ext) ∈ [[3,1,3],[3,1,3,1]] →
        l ∈ lowerGuardShortLabels))) ∧
  (c.run = true → lowerGuardSuffix c.before.1 [3,1] = false ∧
    lowerGuardSuffix c.before.2 [3,1] = false ∧
    lowerGuardSafe (c.before.1++[3,3]) = true ∧ lowerGuardSafe (c.before.2++[3,3]) = true)
noncomputable def lowerGuardBranch (b : String) (p : LowerPair) : Prop :=
  let M := lowerMixed p
  let E9 := ¬M ∧ ¬lowerA p 3 ∧ lowerA p 9
  let EN := ¬M ∧ ¬lowerA p 3 ∧ ¬lowerA p 9
  let M5 := M ∧ ¬lowerH p 2 ∧ lowerH p 5
  let MN := M ∧ ¬lowerH p 2 ∧ ¬lowerH p 5
  match b with
  | "M/H2" => M ∧ lowerH p 2
  | "M/H5/left31" => M5 ∧ lowerL p
  | "M/H5/H6/H7" => M5 ∧ ¬lowerL p ∧ lowerH p 6 ∧ lowerH p 7
  | "M/H5/notH6" => M5 ∧ ¬lowerL p ∧ ¬lowerH p 6
  | "M/H5/H6/notH7" => M5 ∧ ¬lowerL p ∧ lowerH p 6 ∧ ¬lowerH p 7
  | "M/notH5/right3131" => MN ∧ lowerRStar p
  | "M/notH5/H21/H17" => MN ∧ ¬lowerRStar p ∧ lowerH p 21 ∧ lowerH p 17
  | "M/notH5/H21/notH17" => MN ∧ ¬lowerRStar p ∧ lowerH p 21 ∧ ¬lowerH p 17
  | "M/notH5/notH21/chain" => MN ∧ ¬lowerRStar p ∧ ¬lowerH p 21 ∧
      (lowerEnds (lowerNormalize p).2 [3] ∨ ¬lowerH p 23)
  | "M/notH5/notH21/H23" => MN ∧ ¬lowerRStar p ∧ ¬lowerH p 21 ∧
      ¬lowerEnds (lowerNormalize p).2 [3] ∧ lowerH p 23
  | "E/H3" => ¬M ∧ lowerA p 3
  | "E/H9/left31" => E9 ∧ lowerL p
  | "E/H9/H16" => E9 ∧ ¬lowerL p ∧ lowerR p ∧ lowerA p 16
  | "E/H9/notH16" => E9 ∧ ¬lowerL p ∧ lowerR p ∧ ¬lowerA p 16
  | "E/H9/NNFalse" => E9 ∧ ¬lowerL p ∧ ¬lowerR p ∧ ¬lowerRunOffered p
  | "E/H9/NNTrue" => E9 ∧ ¬lowerL p ∧ ¬lowerR p ∧ lowerRunOffered p
  | "E/notH9/left3131" => EN ∧ lowerLStar p
  | "E/notH9/left31" => EN ∧ lowerL p ∧ ¬lowerLStar p
  | "E/notH9/DFalse/NNFalse" => EN ∧ ¬lowerL p ∧ ¬lowerA p 20 ∧ ¬lowerRunOffered p
  | "E/notH9/DTrue/NNFalse" => EN ∧ ¬lowerL p ∧ lowerA p 20 ∧ ¬lowerRunOffered p
  | "E/notH9/DFalse/NNTrue" => EN ∧ ¬lowerL p ∧ ¬lowerA p 20 ∧ lowerRunOffered p
  | "E/notH9/DTrue/NNTrue" => EN ∧ ¬lowerL p ∧ lowerA p 20 ∧ lowerRunOffered p
  | _ => False
noncomputable def lowerGuardFits (c : LowerGuardCase) (p : LowerPair) : Prop :=
  c.before = (lowerGuardState (lowerNormalize p).1, lowerGuardState (lowerNormalize p).2) ∧
  (c.mixed = true ↔ lowerMixed p) ∧ lowerGuardBranch c.branch p
def LowerGuardBoundaryLaw : Prop :=
  ∀ w u s : List ℕ+, lowerGuardState w = s → s ∈ lowerGuardStates →
    ¬ ([3,1,3,1,3] : List ℕ+).IsInfix w → lowerGuardSafe (s++u) = true →
    ¬ ([3,1,3,1,3] : List ℕ+).IsInfix (w++u)
noncomputable def lowerGuardExtensionData (p : LowerPair) (l : LowerLabel) : Prop :=
  lowerExtends (lowerNormalize p) (lowerChild p l) ∧
  lowerPrefixSize p < lowerPrefixSize (lowerChild p l) ∧
  ¬ ([3,1,3,1,3] : List ℕ+).IsInfix ((lowerChild p l).1.reverse++[4]++(lowerChild p l).2)
end Freiman


