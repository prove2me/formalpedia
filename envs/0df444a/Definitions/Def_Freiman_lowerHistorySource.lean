-- Prove2me | Definitions.Def_Freiman_lowerHistorySource
-- name    : Freiman_lowerHistorySource
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T11:54:13.889173+00:00
-- url     : https://prove2.me/theorems/0485644d-a0b1-49a0-b756-8ac481ca0507
-- title:
--   Freiman.lowerHistorySource
-- statement:
--   Pure reconstruction of source A/H choices, necessary goodness, inherited premise DNF and generic endpoint comparisons. Source: Freiman's Hall ray: Proof report and corrected English text (8 September 2026); history_certificates.tex app:all-suffix-histories, global_selection.tex lem:global-suffix-targets; initial_bridges.tex lem:H-entry-bridges; certificates/target_selection/all_suffix_histories_printed.json.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Appendix app:all-suffix-histories and its exact arithmetic/certificate guide.

import Definitions.Def_Freiman_lowerHistoryModel

namespace Freiman

def lowerHistoryTheta : ℕ → CertField
  | 3 => lowerHistoryCF [3] lowerHistoryTau
  | 20 => lowerHistoryCF [3,2,1,3] lowerHistoryTau
  | 22 => lowerHistoryCF [3,3] lowerHistoryAlpha
  | 25 => lowerHistoryCF [3,3] lowerHistoryTau
  | 28 => lowerHistoryCF [3] lowerHistoryAlpha
  | 35 => lowerHistoryCF [2,1,2,1,3] lowerHistoryTau
  | 36 => certFieldScale (1/2) lowerHistoryTau
  | 63 => lowerHistoryCF [2,3] lowerHistoryTau
  | 65 => lowerHistoryCF [1] lowerHistoryBeta
  | 66 => lowerHistoryCF [1,1,3] lowerHistoryTau
  | 68 => lowerHistoryCF [1,1,3] lowerHistoryAlpha
  | 70 => lowerHistoryCF [1,1,2,1,3] lowerHistoryTau
  | 90 => lowerHistoryCF [1,2,1,3] lowerHistoryTau
  | 94 => lowerHistoryCF [1,3] lowerHistoryTau
  | _ => lowerHistoryRat 0
def lowerHistoryPB (c : CertField) (i j k l : ℕ) (lo strict : Bool) : CertBound :=
  ⟨lo,strict,lowerHistoryThreshold c (lowerHistoryTheta i,lowerHistoryTheta k)
    (lowerHistoryTheta j,lowerHistoryTheta l)⟩
def lowerHistoryHN : CertBound := ⟨false,false,lowerHistoryWH ([],[])⟩
def lowerHistoryZero : CertBound := ⟨true,true,lowerHistoryThreshold (lowerHistoryRat 0)
  (lowerHistoryRat 0,lowerHistoryRat 0) (lowerHistoryRat 0,lowerHistoryRat 0)⟩
def lowerHistoryH2 : CertBound := lowerHistoryPB (lowerHistoryRat (37/50)) 63 70 66 90 true true
def lowerHistoryH5 : CertBound := lowerHistoryPB (lowerHistoryRat (279/500)) 35 63 63 70 false true
def lowerHistoryH6 : CertBound := lowerHistoryPB (lowerHistoryRat (69/200)) 22 65 28 68 false true
def lowerHistoryH7 : CertBound := lowerHistoryPB (lowerHistoryRat (31/100)) 3 63 25 66 true false
def lowerHistoryH7Mixed : CertBound := lowerHistoryPB (lowerHistoryRat (161/500)) 3 63 25 66 false true
def lowerHistoryH9 : CertBound := lowerHistoryPB ⟨3/2,-1/2,0,0⟩ 36 63 63 66 false false
def lowerHistoryH21 : CertBound := lowerHistoryPB (lowerHistoryAbs (lowerHistoryDiv
  (certFieldSub (lowerHistoryTheta 63) (lowerHistoryTheta 3))
  (certFieldSub (lowerHistoryTheta 20) (lowerHistoryTheta 66)))) 3 20 63 66 false true
def lowerHistoryH23 : CertBound := lowerHistoryPB (lowerHistoryRat (139/250)) 63 70 66 94 true true
def lowerHistoryConstantBound (q : ℚ) (lo strict : Bool) : CertBound :=
  ⟨lo,strict,lowerHistoryThreshold (lowerHistoryRat q)
    (lowerHistoryRat 0,lowerHistoryRat 0) (lowerHistoryRat 0,lowerHistoryRat 0)⟩

def lowerHistorySourceChoices (s : LowerHistoryState) (l : LowerLabel) : List (List CertBound) :=
  if l = ([1],[]) then [[]] else
  if s.context.parity.1 = s.context.parity.2 then
    if l = ([2],[]) then [[lowerHistoryComplement lowerHistoryH7],[lowerHistoryH7,lowerHistoryH9]]
    else if l = ([3],[]) then [[lowerHistoryComplement lowerHistoryH7]]
    else if l = ([2],[1]) ∨ l = ([3],[1]) then [[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9]]
    else []
  else
    if l = ([2],[]) then [[lowerHistoryComplement lowerHistoryH2,lowerHistoryH5]]
    else if l = ([3],[]) then [[lowerHistoryComplement lowerHistoryH2,lowerHistoryH5,lowerHistoryH6,lowerHistoryH7Mixed]]
    else if l = ([],[1]) then [[lowerHistoryH2]] ++
      (if ([3] : List ℕ+).IsSuffix (lowerHistoryPick s.context.words (!s.wider)) then [] else
        [[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,
          lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]])
    else if l = ([2],[1]) then [[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5]]
    else if l = ([3],[1]) then
      [[lowerHistoryComplement lowerHistoryH2,lowerHistoryH5,lowerHistoryComplement lowerHistoryH6],
       [lowerHistoryComplement lowerHistoryH2,lowerHistoryH5,lowerHistoryH6,lowerHistoryComplement lowerHistoryH7Mixed]] ++
       (if ([3,1] : List ℕ+).IsSuffix (lowerHistoryPick s.context.words s.wider) then [] else
         [[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5]])
    else []

def lowerHistoryExtreme (maximum : Bool) (zs : List CertField) : CertField :=
  zs.foldl (fun a b => if (decide (0 < lowerHistorySign (certFieldSub b a))) = maximum then b else a)
    (zs.headD (lowerHistoryRat 0))
def lowerHistoryRelaxedGoodness (C : LowerHistoryContext) : Option (List CertBound) := Id.run do
  let mut bounds := []
  for (u,v) in [((([1],[]) : LowerPair),(([2],[]) : LowerPair)),
                ((([2],[]) : LowerPair),(([1],[]) : LowerPair))] do
    let hi := lowerHistoryEndpointCases C u true
    let lo := lowerHistoryEndpointCases C v false
    let x := (lowerHistoryExtreme (!C.parity.1) (hi.map (fun z => z.1.1)),
      lowerHistoryExtreme (!C.parity.2) (hi.map (fun z => z.1.2)))
    let y := (lowerHistoryExtreme C.parity.1 (lo.map (fun z => z.1.1)),
      lowerHistoryExtreme C.parity.2 (lo.map (fun z => z.1.2)))
    match lowerHistoryGreater C x y with
    | .automatic => pure ()
    | .impossible => return none
    | .bound b => bounds := bounds ++ [b]
  return some bounds
def lowerHistoryNecessary (s : LowerHistoryState) (words : LowerPair) : Option (List CertBound) :=
  let C : LowerHistoryContext := ⟨lowerHistoryOrient s.context.words s.wider,
    if s.wider then (s.context.parity.2,s.context.parity.1) else s.context.parity⟩
  (lowerHistoryRelaxedGoodness C).map fun bs => bs.map (fun b => lowerHistoryPull b words s.wider)
def lowerHistoryNormalization (words : LowerPair) (wider strict : Bool) : CertBound :=
  ⟨wider,strict,lowerHistoryWH words⟩
def lowerHistoryFinalCuts (row : ℕ) : List CertBound :=
  if row = 1 then [lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,lowerHistoryHN]
  else if row = 2 then [lowerHistoryH7,lowerHistoryHN]
  else [lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryHN]

-- This is the independently reconstructed DNF of necessary source conditions;
-- the packet's premise rows are compared to these expressions, not trusted.
def lowerHistorySourcePremises (p : LowerHistoryPath) : List (List CertBound) := Id.run do
  let base : LowerPair := (p.context,if p.catalog = .initial then [3,1,3] else [3,1])
  let mut alternatives : List (List CertBound) := []
  if p.catalog = .initial then
    alternatives := [[lowerHistoryZero,lowerHistoryHN,
      lowerHistoryConstantBound (729/1024) true true,
      lowerHistoryConstantBound (225/289) false true]]
  else
    match lowerHistoryRelaxedGoodness ⟨base,(false,false)⟩ with
    | none => return []
    | some good => alternatives := [[lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,
        lowerHistoryComplement lowerHistoryH9] ++ good]
  let mut words := lowerHistoryRawStep ([],[]) false p.entry
  let mut s := lowerHistoryInitialState p
  alternatives := alternatives.map fun cs => cs ++ [lowerHistoryNormalization words s.wider false]
  for (l,reflect) in p.steps do
    match lowerHistoryNecessary s words with
    | none => return []
    | some good =>
      alternatives := alternatives.flatMap fun cs =>
        (lowerHistorySourceChoices s l).map fun ch =>
          cs ++ good ++ ch.map (fun b => lowerHistoryPull b words s.wider)
    words := lowerHistoryRawStep words s.wider l
    s := lowerHistoryAdvance s l reflect
    let forced := decide (l ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])])
    alternatives := alternatives.map fun cs => cs ++ [lowerHistoryNormalization words s.wider forced]
  match lowerHistoryNecessary s words with
  | none => return []
  | some good =>
    let final := good ++ (lowerHistoryFinalCuts p.row).map (fun b => lowerHistoryPull b words s.wider)
    return alternatives.map fun cs => (cs ++ final).eraseDups

def lowerHistoryFinalWords (p : LowerHistoryPath) : LowerPair :=
  (lowerHistoryReplay ([],[]) p p.steps.length).1
def lowerHistoryEndpointComparisons (p : LowerHistoryPath) : List (List CertBound × LowerHistoryComparison) :=
  let base : LowerPair := (p.context,[3,1])
  let ancestor : LowerPair := if ([3,1] : List ℕ+).IsSuffix p.context then ([],[]) else ([3],[2])
  let upper := decide (¬ ([3,1] : List ℕ+).IsSuffix p.context)
  let w := lowerHistoryFinalWords p
  let goal := (w.1 ++ (if p.row = 1 then [1] else [2]),
    w.2 ++ (if p.row = 4 then [1] else [2]))
  lowerHistoryComparisons ⟨base,(false,false)⟩ ancestor goal upper false

def lowerHistoryResidual (p : LowerHistoryPath) (alternative : ℕ) (branch : ℤ) : List CertBound :=
  let cs := (lowerHistorySourcePremises p)[alternative]?.getD []
  if branch < 0 then cs else
    let comp := (lowerHistoryEndpointComparisons p)[branch.toNat]?.getD ([],.automatic)
    (cs ++ comp.1 ++ (match comp.2 with
      | .bound b => [lowerHistoryComplement b]
      | _ => [])).eraseDups

end Freiman


