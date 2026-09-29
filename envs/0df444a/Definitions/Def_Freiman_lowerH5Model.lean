-- Prove2me | Definitions.Def_Freiman_lowerH5Model
-- name    : Freiman_lowerH5Model
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:34:15.564409+00:00
-- url     : https://prove2.me/theorems/8a9c3294-1c5a-4966-9148-7ba7117f4218
-- title:
--   Freiman p97 predecessor certificates: lowerH5Model
-- statement:
--   Actual source predecessor cases, exact Q(sqrt3,sqrt7) bound-pair witnesses, reconstructed endpoint residuals and earlier-depth priority events.
-- source:
--   Freiman report, 'The carried target in the shortened-left case of Section 14', sec:h5-source-target, Lemma lem:h5-original-two (source printed p. 97), report/source/staging/parts/h5_target.tex; global_selection.tex priority rule; certificates/target_selection/h5_cases.json and h5_original_appendix_printed.json; verification/families/target_selection/verify_h5_original_independent.py.

import Definitions.Def_Freiman_lowerHistoryVerification
import Definitions.Def_Freiman_lowerWordGuardData
namespace Freiman
inductive LowerH5Kind where
  | a | b1 | b2h3 | b2h9h16 | b2h9not | cLarge | cShort
  deriving DecidableEq
structure LowerH5Case where
  id : ℕ
  name : String
  kind : LowerH5Kind
  context : LowerHistoryContext
  words : LowerPair
  reflect : Bool
  rectangle : CertRectangle
  oldCuts : List CertBound
  automatic : ℕ
  deriving DecidableEq
structure LowerH5Record where
  caseId : ℕ
  branch : ℕ
  bounds : List ℕ
  witness : ℕ
  deriving DecidableEq
def lowerH5H18 : CertBound := ⟨false,false,lowerHistoryThreshold (lowerHistoryRat (183/250))
  (lowerHistoryTheta 25,lowerHistoryCF [2,1,3] lowerHistoryTau)
  (lowerHistoryTheta 36,lowerHistoryTheta 63)⟩
def lowerH5ExpectedCuts : LowerH5Kind → List CertBound
  | .a | .b1 => []
  | .b2h3 => [lowerHistoryComplement lowerHistoryH7]
  | .b2h9h16 => [lowerHistoryH7,lowerHistoryH9,lowerHistoryComplement lowerH5H18]
  | .b2h9not => [lowerHistoryH7,lowerHistoryH9,lowerH5H18]
  | .cLarge => [lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5]
  | .cShort => [lowerHistoryComplement lowerHistoryH2,lowerHistoryH5]
def lowerH5ExpectedWords : LowerH5Kind → LowerPair
  | .a | .b1 => ([1],[])
  | .b2h3 | .b2h9h16 | .b2h9not => ([2],[])
  | .cLarge | .cShort => ([2],[1])
def lowerH5ExpectedParity : LowerH5Kind → Bool × Bool
  | .a => (true,true)
  | .b1 | .b2h3 | .b2h9h16 | .b2h9not => (false,false)
  | .cLarge | .cShort => (false,true)
def lowerH5Exceptional (c : LowerH5Case) : Prop :=
  c.kind = .b2h9not ∧ c.context.words.1 ∈ [[1],[2],[3]]
def lowerH5GoalWords (c : LowerH5Case) : LowerPair :=
  if c.reflect then (c.words.1,c.words.2++[2]) else (c.words.1++[2],c.words.2)
def lowerH5Comparisons (c : LowerH5Case) : List (List CertBound × LowerHistoryComparison) :=
  lowerHistoryComparisons c.context c.words (lowerH5GoalWords c) false false
def lowerH5Premises (c : LowerH5Case) : List CertBound :=
  [lowerHistoryZero,lowerHistoryHN] ++ c.oldCuts ++
  (lowerHistoryRelaxedGoodness c.context).getD [] ++
  [lowerHistoryHN,lowerHistoryComplement lowerHistoryH2,lowerHistoryH5].map
    (fun b => lowerHistoryPull b c.words c.reflect)
def lowerH5Residual (c : LowerH5Case) (branch : ℕ) : List CertBound :=
  let cg := (lowerH5Comparisons c)[branch]?.getD ([],.automatic)
  (lowerH5Premises c ++ cg.1 ++ (match cg.2 with
    | .bound b => [lowerHistoryComplement b]
    | _ => [])).eraseDups
def lowerH5ContextBox (w : List ℕ+) : ℚ × ℚ :=
  let v := w.foldl (fun (z : ℚ × ℚ) a => (1/((a:ℕ)+z.2),1/((a:ℕ)+z.1))) (0,1)
  (max (1/4) v.1,min (4/5) v.2)
def lowerH5ExpectedKeys : List (LowerH5Kind × LowerPair) :=
  [(.a,([3],[1])),(.a,([3],[2]))] ++
  ([[1],[2],[3],[3,1]] : List (List ℕ+)).flatMap fun l =>
    [(.b1,(l,[3,1])),(.b2h3,(l,[3,1])),(.b2h9h16,(l,[3,1])),(.b2h9not,(l,[3,1])),(.cLarge,(l,[3]))] ++
    (if l = [3,1] then [(.cShort,(l,[3]))] else [])
def lowerH5CaseShape (c : LowerH5Case) : Prop :=
  c.words = lowerH5ExpectedWords c.kind ∧ c.context.parity = lowerH5ExpectedParity c.kind ∧
  c.reflect = decide (c.kind ≠ .a) ∧ c.oldCuts.toFinset = (lowerH5ExpectedCuts c.kind).toFinset ∧
  c.rectangle = ⟨(lowerH5ContextBox c.context.words.1).1,(lowerH5ContextBox c.context.words.1).2,
    (lowerH5ContextBox c.context.words.2).1,(lowerH5ContextBox c.context.words.2).2⟩ ∧
  (lowerHistoryRelaxedGoodness c.context).isSome = true
noncomputable def lowerH5Active (p : LowerPair) : Prop :=
  lowerMixed p ∧ ¬lowerH p 2 ∧ lowerH p 5 ∧ lowerL p
noncomputable def lowerH5LowerBound (p : LowerPair) (t : ℝ) : Prop :=
  lowerLocalLower p ([2],[]) ≤ lowerLocalCoordinate p t
noncomputable def lowerH5LocalUpper (p : LowerPair) (l : LowerLabel) : ℝ :=
  if (lowerNormalize p).1.length % 2 = 0 then lowerEndpoint (lowerChild p l) true
  else -lowerEndpoint (lowerChild p l) false
noncomputable def lowerH5ParentLower (p : LowerPair) : ℝ :=
  if (lowerNormalize p).1.length % 2 = 0 then lowerEndpoint p false else -lowerEndpoint p true
noncomputable def lowerH5Immediate (h : ℕ → LowerPair) (n : ℕ) (c : LowerH5Case) : Prop :=
  ∃ m : ℕ, m+1=n ∧
    let base := lowerNormalize (h m)
    lowerHistoryContextFits base c.context ∧
    h n = lowerHistoryAppend base c.words ∧
    lowerNormalize (h n) = lowerHistoryOrient (h n) c.reflect ∧
    lowerHistoryAtBase base c.oldCuts
noncomputable def lowerH5ReachedPremises (h : ℕ → LowerPair) (n : ℕ) (c : LowerH5Case) : Prop :=
  ∃ m : ℕ, m+1=n ∧
    certRectangleMem c.rectangle (lowerRatio (lowerNormalize (h m)).1) (lowerRatio (lowerNormalize (h m)).2) ∧
    lowerHistoryAtBase (lowerNormalize (h m)) (lowerH5Premises c)
structure LowerH5PriorityEvent (t : ℝ) (h : ℕ → LowerPair) (n m : ℕ) : Prop where
  earlier : m < n
  next : m+1=n
  branch : ¬lowerMixed (h m) ∧ ¬lowerA (h m) 3 ∧ lowerA (h m) 9 ∧
    ¬lowerL (h m) ∧ lowerR (h m) ∧ ¬lowerA (h m) 16
  selected : h n = lowerChild (h m) ([2],[])
  priority : lowerPriority t (h m) ([2],[])
end Freiman


