-- Prove2me | Definitions.Def_Freiman_middleCertModel
-- name    : Freiman_middleCertModel
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:05:44.632271+00:00
-- url     : https://prove2.me/theorems/1e5f1292-a193-41c9-ab94-dad3fd0801d7
-- title:
--   Freiman M2B: middleCertModel
-- statement:
--   Exact source model, finite certificate validator, or lossless data. Definitions only; no new axioms or theorem declarations.
-- source:
--   Freiman report (8 September 2026), M2B §§8–9 and complete middle-interval certificate appendix; m2b_readable_model.json, SHA256 a5ac6d3c8e0148e2e3137e8cfa09a2715de6a993dd6ab01eda4842a96bba4cdf.

import Definitions.Def_Freiman_certDiagonal
import Definitions.Def_Freiman_lowerHistoryAlgebra
import Definitions.Def_Freiman_middleRoots

namespace Freiman

structure MiddleCertBoundRef where
  lower : Bool
  strict : Bool
  threshold : ℕ
  deriving DecidableEq
structure MiddleCertEndCase where
  x : ℕ
  y : ℕ
  conditions : List MiddleCertBoundRef
  deriving DecidableEq
structure MiddleCertEndpoint where
  words : LowerPair
  upper : Bool
  parity : Bool
  alternatives : List MiddleCertEndCase
  deriving DecidableEq
inductive MiddleCertRole where
  | outerLow | outerHigh | valid (child : ℕ) | good (child : ℕ) (side : Bool)
  | contact (child : ℕ) (forward : Bool) | anchor (forward : Bool) | uniform
  deriving DecidableEq
structure MiddleCertGoal where
  family : ℕ
  role : MiddleCertRole
  first : ℕ
  second : ℕ
  hypotheses : List MiddleCertBoundRef
  automatic : List ℕ
  deriving DecidableEq
structure MiddleCertPair where
  lowerBound : MiddleCertBoundRef
  upperBound : MiddleCertBoundRef
  witness : ℕ
  deriving DecidableEq
inductive MiddleCertProof where
  | pair (p : MiddleCertPair)
  | diagonal (positive negative : MiddleCertPair)
  deriving DecidableEq
structure MiddleCertWitness where
  first : ℕ
  second : ℕ
  direction : ℤ
  values : List CertField
  lowerNumerator : ℕ
  deriving DecidableEq
structure MiddleCertRecord where
  goal : ℕ
  branch : ℕ
  parents : List ℤ
  proof : ℕ
  deriving DecidableEq
structure MiddleCertSpec where
  role : MiddleCertRole
  first : LowerPair
  firstUpper : Bool
  second : LowerPair
  secondUpper : Bool
  extra : List CertBound
  deriving DecidableEq
structure MiddleCertCatalog where
  tails : List CertField
  thresholds : List CertThreshold
  endpoints : List MiddleCertEndpoint
  parents : Bool → List (List MiddleCertBoundRef)
  goals : List MiddleCertGoal
  proofs : List MiddleCertProof
  witnesses : List MiddleCertWitness
  records : List MiddleCertRecord

def middleCertRectangle : CertRectangle := ⟨1/4,4/5,1/4,4/5⟩
def middleCertThreshold (C : MiddleCertCatalog) (i : ℕ) : CertThreshold :=
  C.thresholds[i-1]?.getD ⟨certDiagonalZero,certDiagonalZero,certDiagonalZero,certDiagonalZero,certDiagonalZero⟩
def middleCertTail (C : MiddleCertCatalog) (i : ℕ) : CertField := C.tails[i-1]?.getD certDiagonalZero
def middleCertBound (C : MiddleCertCatalog) (b : MiddleCertBoundRef) : CertBound :=
  ⟨b.lower,b.strict,middleCertThreshold C b.threshold⟩
def middleCertBounds (C : MiddleCertCatalog) (bs : List MiddleCertBoundRef) : List CertBound :=
  bs.map (middleCertBound C)
def middleCertEndpoint (C : MiddleCertCatalog) (i : ℕ) : MiddleCertEndpoint :=
  C.endpoints[i-1]?.getD ⟨([],[]),false,false,[]⟩
def middleCertGoal (C : MiddleCertCatalog) (i : ℕ) : MiddleCertGoal :=
  C.goals[i-1]?.getD ⟨0,.uniform,0,0,[],[]⟩
def middleCertWitness (C : MiddleCertCatalog) (i : ℕ) : MiddleCertWitness :=
  C.witnesses[i-1]?.getD ⟨0,0,0,[],0⟩
def middleCertProof (C : MiddleCertCatalog) (i : ℕ) : MiddleCertProof :=
  C.proofs[i-1]?.getD (.pair ⟨⟨true,false,0⟩,⟨false,false,0⟩,0⟩)
def middleCertParity (family : ℕ) : Bool := decide (family < 3 ∨ family = 10)
def middleCertRow : ℕ → MiddleRow
  | 0 => .mixedA | 1 => .mixedB | 2 => .mixedC | 3 => .equalIShort | 4 => .equalIJ
  | 5 => .equalIIa | 6 => .equalIIbNormal | 7 => .equalIIbShort | _ => .equalIIbJ
def middleCertChildren : ℕ → List LowerPair
  | 0 => [([],[1]),([1],[])]
  | 1 | 5 => [([3],[]),([2],[]),([1],[])]
  | 2 => [([3],[1]),([2],[]),([1],[])]
  | 3 | 4 => [([3],[2]),([2],[3]),([2],[2]),([],[1])]
  | 6 => [([3],[3]),([3],[2]),([2],[]),([1],[])]
  | _ => [([3],[2]),([2],[]),([1],[])]
def middleCertOdd (w : LowerPair) (parity side : Bool) : Bool :=
  xor (parity && side) (decide ((lowerHistoryPick w side).length % 2 = 1))
def middleCertNormals (w : LowerPair) : List (Bool × CertBound) :=
  [(false,⟨false,false,lowerHistoryWH w⟩),(true,⟨true,true,lowerHistoryWH w⟩)]
def middleCertEqualCases (w : LowerPair) (upper parity : Bool) : List LowerHistoryEndCase :=
  (middleCertNormals w).flatMap fun (wide,norm) =>
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
def middleCertEndpointCases (w : LowerPair) (upper parity : Bool) : List LowerHistoryEndCase :=
  if middleCertOdd w parity false = middleCertOdd w parity true then middleCertEqualCases w upper parity
  else (middleCertNormals w).flatMap fun (wide,norm) =>
    let side := if (!upper) = middleCertOdd w parity wide then wide else !wide
    let nw := lowerHistorySet w side (lowerHistoryPick w side++[1])
    (middleCertEqualCases nw upper parity).map fun (v,cs) => (v,norm::cs)
def middleCertGreater (parity : Bool) (x y : CertField × CertField) : LowerHistoryComparison :=
  lowerHistoryGreater ⟨([],[]),(false,parity)⟩ x y
def middleCertCompare (w v : LowerPair) (a b parity : Bool) :
    List (List CertBound × LowerHistoryComparison) :=
  (middleCertEndpointCases w a parity).flatMap fun (x,cx) =>
    (middleCertEndpointCases v b parity).map fun (y,cy) => (cx++cy,middleCertGreater parity x y)
def middleCertExpectedParents (parity : Bool) : List (List CertBound) :=
  (middleCertNormals ([],[])).flatMap fun (wide,norm) =>
    let one : LowerPair := if wide then ([],[1]) else ([1],[])
    let two : LowerPair := if wide then ([],[2]) else ([2],[])
    let ordered := if middleCertOdd ([],[]) parity wide then (one,two) else (two,one)
    (middleCertCompare ordered.1 ordered.2 true false parity).filterMap fun (cs,v) =>
      match v with | .impossible => none | .automatic => some (norm::cs) | .bound b => some (b::norm::cs)
def middleCertA (q : ℚ) : CertThreshold := lowerHistoryThreshold (lowerHistoryRat q)
  (lowerHistoryCF [2,3] lowerHistoryTau,lowerHistoryCF [1,1,3] lowerHistoryTau)
  (lowerHistoryCF [1,1,2] lowerHistoryBeta,lowerHistoryBeta)
def middleCertB (q : ℚ) : CertThreshold := lowerHistoryThreshold (lowerHistoryRat q)
  (lowerHistoryCF [3,1,2] lowerHistoryBeta,lowerHistoryCF [3] lowerHistoryAlpha)
  (lowerHistoryCF [2,3] lowerHistoryTau,lowerHistoryCF [1,1,3] lowerHistoryTau)
def middleCertFamilyHyp (f : ℕ) : List CertBound :=
  let norm : CertBound := ⟨false,false,lowerHistoryWH ([],[])⟩
  let a : CertBound := ⟨true,true,middleCertA (if f<3 then 55/100 else 549/1000)⟩
  let b : CertBound := ⟨false,true,middleCertB (if f<3 then 328/1000 else 313/1000)⟩
  let s : CertBound := ⟨true,false,lowerHistoryScaleThreshold (5/7) (lowerHistoryWH ([3],[3]))⟩
  let t : CertBound := ⟨true,false,lowerHistoryScaleThreshold (5/7) (lowerHistoryWH ([3,3],[3,3]))⟩
  norm :: (match f with
    | 0 => [a] | 1 => [lowerHistoryComplement a,b] | 2 => [lowerHistoryComplement a,lowerHistoryComplement b]
    | 3 => [a,s] | 4 => [a,lowerHistoryComplement s] | 5 => [lowerHistoryComplement a,b]
    | 6 => [lowerHistoryComplement a,lowerHistoryComplement b,lowerHistoryComplement t]
    | 7 => [lowerHistoryComplement a,lowerHistoryComplement b,t,s]
    | 8 => [lowerHistoryComplement a,lowerHistoryComplement b,t,lowerHistoryComplement s]
    | _ => [⟨true,true,lowerHistoryScaleThreshold (5/19) (lowerHistoryWH ([],[]))⟩])
def middleCertSpecs (f : ℕ) : List MiddleCertSpec :=
  if 9 ≤ f then [⟨.uniform,([2],[]),true,([1],[]),false,[]⟩] else
  let ws := middleCertChildren f
  let hasJ := f=4 ∨ f=8
  [⟨.outerLow,([],[]),false,(if hasJ then ([3],[3]) else ws.headD ([],[])),false,[]⟩,
   ⟨.outerHigh,ws.getLastD ([],[]),true,([],[]),true,[]⟩] ++
  (ws.zipIdx.flatMap fun (w,k) =>
    ⟨.valid k,w,true,w,false,[]⟩ :: (middleCertNormals w).map fun (side,norm) =>
      let one := lowerHistorySet w side (lowerHistoryPick w side++[1])
      let two := lowerHistorySet w side (lowerHistoryPick w side++[2])
      let ordered := if middleCertOdd w (middleCertParity f) side then (one,two) else (two,one)
      ⟨.good k side,ordered.1,true,ordered.2,false,[norm]⟩) ++
  ((ws.zip ws.tail).zipIdx.flatMap fun ((w,v),k) =>
    [⟨.contact k true,w,true,v,false,[]⟩,⟨.contact k false,v,true,w,false,[]⟩]) ++
  (if hasJ then [⟨.anchor true,([3,3],[3,3]),true,([3],[2]),false,[]⟩,
    ⟨.anchor false,([3],[2]),true,([3,3],[3,3]),false,[]⟩] else [])

def middleCertActualCases (C : MiddleCertCatalog) (e : MiddleCertEndpoint) : List LowerHistoryEndCase :=
  e.alternatives.map fun a => ((middleCertTail C a.x,middleCertTail C a.y),middleCertBounds C a.conditions)
def middleCertEndSet (es : List LowerHistoryEndCase) : Finset ((CertField × CertField) × Finset CertBound) :=
  (es.map fun (v,cs) => (v,cs.toFinset)).toFinset
def middleCertEndpointValid (C : MiddleCertCatalog) (e : MiddleCertEndpoint) : Prop :=
  middleCertEndSet (middleCertActualCases C e) = middleCertEndSet (middleCertEndpointCases e.words e.upper e.parity)
def middleCertGoalSpec (C : MiddleCertCatalog) (g : MiddleCertGoal) : MiddleCertSpec :=
  let a := middleCertEndpoint C g.first
  let b := middleCertEndpoint C g.second
  ⟨g.role,a.words,a.upper,b.words,b.upper,[]⟩
def middleCertGoalMatches (C : MiddleCertCatalog) (g : MiddleCertGoal) (sp : MiddleCertSpec) : Prop :=
  0 < g.first ∧ g.first ≤ C.endpoints.length ∧ 0 < g.second ∧ g.second ≤ C.endpoints.length ∧
  g.role = sp.role ∧ (middleCertEndpoint C g.first).words = sp.first ∧
  (middleCertEndpoint C g.first).upper = sp.firstUpper ∧ (middleCertEndpoint C g.second).words = sp.second ∧
  (middleCertEndpoint C g.second).upper = sp.secondUpper ∧
  (middleCertEndpoint C g.first).parity = middleCertParity g.family ∧
  (middleCertEndpoint C g.second).parity = middleCertParity g.family ∧
  (middleCertBounds C g.hypotheses).toFinset = (middleCertFamilyHyp g.family++sp.extra).toFinset
def middleCertGoalBranches (C : MiddleCertCatalog) (g : MiddleCertGoal) :
    List (List CertBound × LowerHistoryComparison) :=
  (middleCertActualCases C (middleCertEndpoint C g.first)).flatMap fun (x,cx) =>
    (middleCertActualCases C (middleCertEndpoint C g.second)).map fun (y,cy) =>
      (cx++cy,middleCertGreater (middleCertParity g.family) x y)
def middleCertBranch (C : MiddleCertCatalog) (g : MiddleCertGoal) (i : ℕ) :
    List CertBound × LowerHistoryComparison := (middleCertGoalBranches C g)[i]?.getD ([],.impossible)
def middleCertRecordConditions (C : MiddleCertCatalog) (r : MiddleCertRecord) (parent : ℤ) : List CertBound :=
  let g := middleCertGoal C r.goal
  let v := middleCertBranch C g r.branch
  middleCertBounds C g.hypotheses ++ v.1 ++
    (if parent < 0 then [] else middleCertBounds C ((C.parents (middleCertParity g.family))[parent.toNat]?.getD [])) ++
    (match v.2 with | .bound b => [lowerHistoryComplement b] | _ => [])
def middleCertWitnessLower (w : MiddleCertWitness) : ℚ := (w.lowerNumerator:ℚ)/(2*10^24)
def middleCertPairWitness (C : MiddleCertCatalog) (p : MiddleCertPair) : CertWitness :=
  let w := middleCertWitness C p.witness
  ⟨middleCertBound C p.lowerBound,middleCertBound C p.upperBound,middleCertRectangle,
    fun i j => w.values.getD (i.val+3*j.val) certDiagonalZero,fun _ _ => middleCertWitnessLower w⟩
def middleCertDiagonalWitness (C : MiddleCertCatalog) (w : MiddleCertWitness) : CertDiagonalData :=
  let l := middleCertThreshold C w.first
  let u := middleCertThreshold C w.second
  let P := certCrossPolynomial l u
  ⟨l,u,middleCertRectangle,decide (w.direction = 1),P 1 0,P 2 0,P 2 1,
    fun i j => w.values.getD (2*i.val+j.val) certDiagonalZero,fun _ _ => middleCertWitnessLower w⟩
def middleCertWitnessValid (C : MiddleCertCatalog) (w : MiddleCertWitness) : Prop :=
  0 < w.first ∧ w.first ≤ C.thresholds.length ∧ 0 < w.second ∧ w.second ≤ C.thresholds.length ∧
  certThresholdDataValid (middleCertThreshold C w.first) ∧ certThresholdDataValid (middleCertThreshold C w.second) ∧
  (if w.direction = 0 then w.values.length = 9 ∧
    (∀ i j : Fin 3, w.values.getD (i.val+3*j.val) certDiagonalZero =
      certBernsteinCoefficients (certCrossPolynomial (middleCertThreshold C w.first)
        (middleCertThreshold C w.second)) middleCertRectangle i j) ∧
    ∀ i j : Fin 3, certCoefficientBoundValid (w.values.getD (i.val+3*j.val) certDiagonalZero) (middleCertWitnessLower w)
   else (w.direction = 1 ∨ w.direction = -1) ∧ w.values.length = 4 ∧
    certDiagonalDataValid (middleCertDiagonalWitness C w))
def middleCertPairValid (C : MiddleCertCatalog) (p : MiddleCertPair) (direction : ℤ) : Prop :=
  0 < p.witness ∧ p.witness ≤ C.witnesses.length ∧
  p.lowerBound.lower = true ∧ p.upperBound.lower = false ∧
  p.lowerBound.threshold = (middleCertWitness C p.witness).first ∧
  p.upperBound.threshold = (middleCertWitness C p.witness).second ∧
  (middleCertWitness C p.witness).direction = direction ∧
  (if direction = 0 then 0 < (middleCertWitness C p.witness).lowerNumerator ∨
    p.lowerBound.strict = true ∨ p.upperBound.strict = true
   else p.lowerBound.strict = true ∨ p.upperBound.strict = true)
def middleCertProofPairs : MiddleCertProof → List MiddleCertPair
  | .pair p => [p] | .diagonal a b => [a,b]
def middleCertProofValid (C : MiddleCertCatalog) : MiddleCertProof → Prop
  | .pair p => middleCertPairValid C p 0
  | .diagonal a b => middleCertPairValid C a 1 ∧ middleCertPairValid C b (-1)
def middleCertRecordValid (C : MiddleCertCatalog) (r : MiddleCertRecord) : Prop :=
  0 < r.goal ∧ r.goal ≤ C.goals.length ∧ 0 < r.proof ∧ r.proof ≤ C.proofs.length ∧
  r.branch < (middleCertGoalBranches C (middleCertGoal C r.goal)).length ∧
  (middleCertBranch C (middleCertGoal C r.goal) r.branch).2 ≠ .automatic ∧
  middleCertProofValid C (middleCertProof C r.proof) ∧
  ∀ parent ∈ r.parents, (parent = -1 ∨ (0 ≤ parent ∧ parent.toNat < (C.parents (middleCertParity (middleCertGoal C r.goal).family)).length)) ∧
    ∀ p ∈ middleCertProofPairs (middleCertProof C r.proof),
      middleCertBound C p.lowerBound ∈ middleCertRecordConditions C r parent ∧
      middleCertBound C p.upperBound ∈ middleCertRecordConditions C r parent
def middleCertRecorded (C : MiddleCertCatalog) (goal branch : ℕ) (parent : ℤ) : Prop :=
  ∃ r ∈ C.records, r.goal = goal ∧ r.branch = branch ∧ parent ∈ r.parents
def middleCertFamilyValid (C : MiddleCertCatalog) (f : ℕ) : Prop :=
  (∀ sp ∈ middleCertSpecs f, ∃ i ∈ List.range C.goals.length,
    let g := middleCertGoal C (i+1)
    g.family = f ∧ middleCertGoalMatches C g sp) ∧
  (∀ r ∈ C.records, (middleCertGoal C r.goal).family = f → middleCertRecordValid C r) ∧
  ∀ i ∈ List.range C.goals.length, (middleCertGoal C (i+1)).family = f →
    ∀ j ∈ List.range (middleCertGoalBranches C (middleCertGoal C (i+1))).length,
      (middleCertBranch C (middleCertGoal C (i+1)) j).2 = .automatic ∨
      middleCertRecorded C (i+1) j (-1) ∨
      (f < 9 ∧ ∀ k ∈ List.range (C.parents (middleCertParity f)).length, middleCertRecorded C (i+1) j k)
noncomputable def middleCertHolds (bs : List CertBound) (r s q : ℝ) : Prop :=
  ∀ b ∈ bs, certBoundHolds b r s q
noncomputable def middleCertComparisonHolds (v : LowerHistoryComparison) (r s q : ℝ) : Prop :=
  match v with | .automatic => True | .impossible => False | .bound b => certBoundHolds b r s q
noncomputable def middleCertParentHolds (C : MiddleCertCatalog) (f : ℕ) (r s q : ℝ) : Prop :=
  if f < 9 then ∃ bs ∈ C.parents (middleCertParity f), middleCertHolds (middleCertBounds C bs) r s q else True
noncomputable def middleCertRecordSound (C : MiddleCertCatalog) (r : MiddleCertRecord) : Prop :=
  ∀ parent ∈ r.parents, ∀ x y q : ℝ, certRectangleMem middleCertRectangle x y →
    ¬ middleCertHolds (middleCertRecordConditions C r parent) x y q
noncomputable def middleCertFamilySound (C : MiddleCertCatalog) (f : ℕ) : Prop :=
  ∀ i ∈ List.range C.goals.length, (middleCertGoal C (i+1)).family = f →
  ∀ r s q : ℝ, certRectangleMem middleCertRectangle r s → 0 < q → middleCertParentHolds C f r s q →
    middleCertHolds (middleCertBounds C (middleCertGoal C (i+1)).hypotheses) r s q →
  ∀ j ∈ List.range (middleCertGoalBranches C (middleCertGoal C (i+1))).length,
    middleCertHolds (middleCertBranch C (middleCertGoal C (i+1)) j).1 r s q →
    middleCertComparisonHolds (middleCertBranch C (middleCertGoal C (i+1)) j).2 r s q
noncomputable def middleCertLocalEndpoint (c : MiddleCore) (w : LowerPair) (upper : Bool) : ℝ :=
  let d := middleNormalized c
  let e := middleBounds ⟨d.left++w.1,d.right++w.2⟩
  if d.left.length % 2 = 0 then (if upper then e.2 else e.1) else -(if upper then e.1 else e.2)
noncomputable def middleCertActualSpec (c : MiddleCore) (sp : MiddleCertSpec) : Prop :=
  middleCertHolds sp.extra (middleParameter (middleNormalized c).left)
    (middleParameter (middleNormalized c).right) (middleQ c) →
    middleCertLocalEndpoint c sp.second sp.secondUpper ≤ middleCertLocalEndpoint c sp.first sp.firstUpper
noncomputable def middleCertActualFamily (c : MiddleCore) (f : ℕ) : Prop :=
  ∀ sp ∈ middleCertSpecs f, middleCertActualSpec c sp

def middleCertEndpointsValid (C : MiddleCertCatalog) : Prop :=
  ∀ e ∈ C.endpoints, middleCertEndpointValid C e
def middleCertParentsValid (C : MiddleCertCatalog) : Prop :=
  ∀ parity : Bool,
    ((C.parents parity).map fun bs => (middleCertBounds C bs).toFinset).toFinset =
    ((middleCertExpectedParents parity).map List.toFinset).toFinset
def middleCertWitnessesValid (C : MiddleCertCatalog) : Prop :=
  ∀ w ∈ C.witnesses, middleCertWitnessValid C w
noncomputable def middleCertProofSound (C : MiddleCertCatalog) (p : MiddleCertProof) : Prop :=
  ∀ r s q : ℝ, certRectangleMem middleCertRectangle r s →
    ¬ (∀ pair ∈ middleCertProofPairs p,
      certBoundHolds (middleCertBound C pair.lowerBound) r s q ∧
      certBoundHolds (middleCertBound C pair.upperBound) r s q)
noncomputable def middleCertDomain (c : MiddleCore) (f : ℕ) : Prop :=
  middleRegular c ∧
    if f < 9 then middleGood c ∧ middleRowCondition c (middleCertRow f)
    else middleRatio c < (19/5:ℝ) ∧
      decide ((middleNormalized c).left.length % 2 ≠ (middleNormalized c).right.length % 2) = middleCertParity f
noncomputable def middleCertActualComparison (c : MiddleCore) (a b : CertField × CertField) : Prop :=
  let d := middleNormalized c
  let sign : ℝ := if d.left.length % 2 = 0 then 1 else -1
  sign * (prefixEval d.left (certFieldVal b.1) + prefixEval d.right (certFieldVal b.2)) ≤
  sign * (prefixEval d.left (certFieldVal a.1) + prefixEval d.right (certFieldVal a.2))
def middleCertUsedWords (f : ℕ) : List LowerPair :=
  (middleCertSpecs f).flatMap (fun sp => [sp.first,sp.second]) ++ middleCertChildren f

end Freiman


