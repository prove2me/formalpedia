-- Prove2me | Definitions.Def_Freiman_middleRepairCertificates
-- name    : Freiman_middleRepairCertificates
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:21:29.323207+00:00
-- url     : https://prove2.me/theorems/16abf498-99ae-40c5-91c1-f566f75107f3
-- title:
--   Freiman report-normalized middle model: middleRepairCertificates
-- statement:
--   Definitions only: normalized child and cumulative physical reflection, exact incoming-order endpoint cases, or the 146 explicit redirects to unchanged source polynomial witnesses. No theorem or axiom is declared.
-- source:
--   Active report m2b_body.tex lines 46–48, §§2,8–9,11; REPORT_MODE_BINDING.json.

import Definitions.Def_Freiman_middleRepair
import Definitions.Def_Freiman_middleCertData

namespace Freiman

def middleRepairCertNormals (w : LowerPair) (incoming : Bool) : List (Bool × CertBound) :=
  [(false,⟨false,incoming,lowerHistoryWH w⟩),(true,⟨true,!incoming,lowerHistoryWH w⟩)]
def middleRepairCertEqualCases (w : LowerPair) (upper parity incoming : Bool) : List LowerHistoryEndCase :=
  (middleRepairCertNormals w incoming).flatMap fun (wide,norm) =>
    let e3 := xor (!upper) (middleCertOdd w parity wide)
    let su : List ℕ+ := if e3 then [3] else [1,3]
    let sv : List ℕ+ := if e3 then [2] else [1,2]
    let aux := lowerHistoryWH (w.1++su,w.2++su)
    let cut : CertBound := if wide then ⟨false,false,lowerHistoryScaleThreshold (7/5) aux⟩
      else ⟨true,false,lowerHistoryScaleThreshold (5/7) aux⟩
    [true,false].map fun short =>
      let a := if short then lowerHistoryCF (lowerHistoryPick w wide++su) lowerHistoryTau
        else lowerHistoryCF (lowerHistoryPick w wide) (if e3 then lowerHistoryAlpha else lowerHistoryBeta)
      let b := if short then lowerHistoryCF (lowerHistoryPick w (!wide)++sv) lowerHistoryBeta
        else lowerHistoryCF (lowerHistoryPick w (!wide)++su) lowerHistoryTau
      ((if wide then (b,a) else (a,b)),[norm,if short then cut else lowerHistoryComplement cut])
def middleRepairCertEndpointCases (w : LowerPair) (upper parity incoming : Bool) : List LowerHistoryEndCase :=
  if middleCertOdd w parity false = middleCertOdd w parity true then
    middleRepairCertEqualCases w upper parity incoming
  else (middleRepairCertNormals w incoming).flatMap fun (wide,norm) =>
    let side := if (!upper) = middleCertOdd w parity wide then wide else !wide
    let nw := lowerHistorySet w side (lowerHistoryPick w side++[1])
    (middleRepairCertEqualCases nw upper parity wide).map fun (v,cs) => (v,norm::cs)
def middleRepairCertCompare (w v : LowerPair) (a b parity incoming : Bool) :
    List (List CertBound × LowerHistoryComparison) :=
  (middleRepairCertEndpointCases w a parity incoming).flatMap fun (x,cx) =>
    (middleRepairCertEndpointCases v b parity incoming).map fun (y,cy) => (cx++cy,middleCertGreater parity x y)
def middleRepairCertParents (parity : Bool) : List (List CertBound) :=
  (middleRepairCertNormals ([],[]) false).flatMap fun (wide,norm) =>
    let one : LowerPair := if wide then ([],[1]) else ([1],[])
    let two : LowerPair := if wide then ([],[2]) else ([2],[])
    let ordered := if middleCertOdd ([],[]) parity wide then (one,two) else (two,one)
    (middleRepairCertCompare ordered.1 ordered.2 true false parity wide).filterMap fun (cs,v) =>
      match v with | .impossible => none | .automatic => some (norm::cs) | .bound b => some (b::norm::cs)
def middleRepairCertIncoming : MiddleCertRole → Bool
  | .good _ side => side | _ => false
def middleRepairCertGoalBranches (C : MiddleCertCatalog) (g : MiddleCertGoal) :
    List (List CertBound × LowerHistoryComparison) :=
  let a := middleCertEndpoint C g.first
  let b := middleCertEndpoint C g.second
  middleRepairCertCompare a.words b.words a.upper b.upper (middleCertParity g.family) (middleRepairCertIncoming g.role)
def middleRepairCertBranch (C : MiddleCertCatalog) (g : MiddleCertGoal) (j : ℕ) :
    List CertBound × LowerHistoryComparison := (middleRepairCertGoalBranches C g)[j]?.getD ([],.impossible)
def middleRepairCertConditions (C : MiddleCertCatalog) (rec : MiddleCertRecord) (parent : ℤ) : List CertBound :=
  let g := middleCertGoal C rec.goal
  let b := middleRepairCertBranch C g rec.branch
  middleCertBounds C g.hypotheses ++ b.1 ++
    (if parent<0 then [] else (middleRepairCertParents (middleCertParity g.family))[parent.toNat]?.getD []) ++
    (match b.2 with | .bound t => [lowerHistoryComplement t] | _ => [])

structure MiddleRepairRedirect where
  goal : ℕ
  branch : ℕ
  parent : ℤ
  originalProof : ℕ
  pair : MiddleCertPair
  deriving DecidableEq
def middleRepairRedirectMatches (a : MiddleRepairRedirect) (rec : MiddleCertRecord) (parent : ℤ) : Bool :=
  decide (a.goal=rec.goal ∧ a.branch=rec.branch ∧ a.parent=parent ∧ a.originalProof=rec.proof)
def middleRepairStrengthen (C : MiddleCertCatalog) (cs : List CertBound) (b : MiddleCertBoundRef) : MiddleCertBoundRef :=
  ⟨b.lower,cs.any (fun x => x.lower==b.lower && x.strict && decide (x.threshold=middleCertThreshold C b.threshold)),b.threshold⟩
def middleRepairAdaptPair (C : MiddleCertCatalog) (cs : List CertBound) (p : MiddleCertPair) : MiddleCertPair :=
  ⟨middleRepairStrengthen C cs p.lowerBound,middleRepairStrengthen C cs p.upperBound,p.witness⟩
def middleRepairEffectiveProof (C : MiddleCertCatalog) (redirects : List MiddleRepairRedirect)
    (rec : MiddleCertRecord) (parent : ℤ) : MiddleCertProof :=
  match redirects.find? (fun a => middleRepairRedirectMatches a rec parent) with
  | some a => .pair a.pair
  | none =>
    let cs := middleRepairCertConditions C rec parent
    match middleCertProof C rec.proof with
    | .pair p => .pair (middleRepairAdaptPair C cs p)
    | .diagonal a b => .diagonal (middleRepairAdaptPair C cs a) (middleRepairAdaptPair C cs b)
def middleRepairRecordValid (C : MiddleCertCatalog) (redirects : List MiddleRepairRedirect)
    (rec : MiddleCertRecord) (parent : ℤ) : Prop :=
  middleCertProofValid C (middleRepairEffectiveProof C redirects rec parent) ∧
  ∀ p ∈ middleCertProofPairs (middleRepairEffectiveProof C redirects rec parent),
    middleCertBound C p.lowerBound ∈ middleRepairCertConditions C rec parent ∧
    middleCertBound C p.upperBound ∈ middleRepairCertConditions C rec parent
def middleRepairLedgerValid (C : MiddleCertCatalog) (redirects : List MiddleRepairRedirect) : Prop :=
  (∀ a ∈ redirects, ∃ rec ∈ C.records, a.goal=rec.goal ∧ a.branch=rec.branch ∧
    a.parent∈rec.parents ∧ a.originalProof=rec.proof) ∧
  ∀ rec ∈ C.records, ∀ parent ∈ rec.parents, middleRepairRecordValid C redirects rec parent
def middleRepairBranchIdentity (C : MiddleCertCatalog) : Prop :=
  (∀ g ∈ C.goals, (middleRepairCertGoalBranches C g).map Prod.snd =
    (middleCertGoalBranches C g).map Prod.snd) ∧
  ∀ parity : Bool, (middleRepairCertParents parity).length = (C.parents parity).length
noncomputable def middleRepairCertParentHolds (f : ℕ) (r s q : ℝ) : Prop :=
  if f<9 then ∃ bs ∈ middleRepairCertParents (middleCertParity f), middleCertHolds bs r s q else True
noncomputable def middleRepairCertFamilySound (C : MiddleCertCatalog) (f : ℕ) : Prop :=
  ∀ i ∈ List.range C.goals.length, (middleCertGoal C (i+1)).family=f →
  ∀ r s q : ℝ, certRectangleMem middleCertRectangle r s → 0<q → middleRepairCertParentHolds f r s q →
    middleCertHolds (middleCertBounds C (middleCertGoal C (i+1)).hypotheses) r s q →
  ∀ j ∈ List.range (middleRepairCertGoalBranches C (middleCertGoal C (i+1))).length,
    middleCertHolds (middleRepairCertBranch C (middleCertGoal C (i+1)) j).1 r s q →
    middleCertComparisonHolds (middleRepairCertBranch C (middleCertGoal C (i+1)) j).2 r s q

noncomputable def middleRepairCertDomain (c : MiddleCore) (f : ℕ) : Prop :=
  middleRegular c ∧ if f<9 then middleRepairGood c ∧ middleRowCondition c (middleCertRow f)
    else middleRatio c < (19/5:ℝ) ∧
      decide ((middleNormalized c).left.length%2 ≠ (middleNormalized c).right.length%2) = middleCertParity f
noncomputable def middleRepairCertEndpoint (c : MiddleCore) (w : LowerPair) (upper incoming : Bool) : ℝ :=
  let d := middleNormalized c
  let e := middleBounds (middleRepairAct incoming ⟨d.left++w.1,d.right++w.2⟩)
  if d.left.length%2=0 then (if upper then e.2 else e.1) else -(if upper then e.1 else e.2)
noncomputable def middleRepairCertSpecHolds (c : MiddleCore) (sp : MiddleCertSpec) : Prop :=
  middleCertHolds sp.extra (middleParameter (middleNormalized c).left)
    (middleParameter (middleNormalized c).right) (middleQ c) →
  middleRepairCertEndpoint c sp.second sp.secondUpper (middleRepairCertIncoming sp.role) ≤
    middleRepairCertEndpoint c sp.first sp.firstUpper (middleRepairCertIncoming sp.role)
noncomputable def middleRepairCertActualFamily (c : MiddleCore) (f : ℕ) : Prop :=
  ∀ sp ∈ middleCertSpecs f, middleRepairCertSpecHolds c sp

end Freiman


