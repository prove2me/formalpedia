-- Prove2me | Definitions.Def_Freiman_trunkModel
-- name    : Freiman_trunkModel
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:05:07.242646+00:00
-- url     : https://prove2.me/theorems/e80eba46-3b26-4372-ade7-68fe03c7798d
-- title:
--   trunkModel
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_section14Model
import Definitions.Def_Freiman_lowerHistoryVerification

namespace Freiman

structure TrunkPlan where
  cuts : List CertBound
  labels : List LowerLabel
  holes : List (LowerLabel × LowerLabel)
  deriving DecidableEq

def trunkH18 : CertBound := ⟨false,false,lowerHistoryThreshold (lowerHistoryRat (183/250))
  (lowerHistoryTheta 25,lowerHistoryCF [2,1,3] lowerHistoryTau)
  (lowerHistoryTheta 36,lowerHistoryTheta 63)⟩
def trunkH20 : CertBound := ⟨false,true,lowerHistoryThreshold ⟨-171/255,0,0,76/255⟩
  (lowerHistoryAlpha,lowerHistoryTheta 28)
  (lowerHistoryTheta 65,lowerHistoryBeta)⟩
def trunkShorten : CertBound := ⟨true,false,
  lowerHistoryScaleThreshold (5/7) (lowerHistoryWH ([3],[3]))⟩
def trunkSourcePlans (C : LowerHistoryContext) : List TrunkPlan := Id.run do
  let L := decide (([3,1] : List ℕ+).IsSuffix C.words.1)
  let R := decide (([3,1] : List ℕ+).IsSuffix C.words.2)
  let initial : List LowerLabel := [([1],[]),([2],[])]
  let runs : List LowerLabel := [([3,3],[3,3]),([3],[3])]
  let runHole : List (LowerLabel × LowerLabel) := [((([3,3],[3,3]) : LowerLabel),([3],[3]))]
  let mut plans : List TrunkPlan := [⟨[lowerHistoryComplement lowerHistoryH7],
    initial ++ (if L then [] else [([3],[])]),[]⟩]
  let small := [lowerHistoryH7,lowerHistoryH9]
  if L then plans := plans ++ [⟨small,initial,[]⟩]
  else if R then
    plans := plans ++ [⟨small++[lowerHistoryComplement trunkH18],initial++[([3],[2])],[]⟩,
      ⟨small++[trunkH18],initial++[([2],[2]),([3],[2])],[((([2],[2]) : LowerLabel),([3],[2]))]⟩]
  else
    for shortened in [true,false] do
      plans := plans ++ [⟨small++[if shortened then trunkShorten else lowerHistoryComplement trunkShorten],
        initial++[([3],[2])]++(if shortened then [] else runs),if shortened then [] else runHole⟩]
  let large := [lowerHistoryH7,lowerHistoryComplement lowerHistoryH9]
  if L then
    plans := plans ++ [⟨large,[([1],[]),([2],[1]),([2],[2]),([2],[3])],
      [((([2],[1]) : LowerLabel),([2],[2]))]⟩]
  else
    for first in [true,false] do
      for shortened in (if R then [true] else [true,false]) do
        let cuts := large++[if first then trunkH20 else lowerHistoryComplement trunkH20]++
          (if R then [] else [if shortened then trunkShorten else lowerHistoryComplement trunkShorten])
        let chain : List LowerLabel := [([1],[]),([2],[1]),
          (if first then ([3],[1]) else ([3],[1,1])),([2],[2]),([2],[3]),([3],[2])]
        plans := plans ++ [⟨cuts,chain++(if shortened then [] else runs),if shortened then [] else runHole⟩]
  return plans

def trunkNormalCases (w : LowerPair) (incoming : Bool) : List (Bool × CertBound) :=
  [(false,⟨false,incoming,lowerHistoryWH w⟩),(true,⟨true,!incoming,lowerHistoryWH w⟩)]
def trunkEqualCases (C : LowerHistoryContext) (w : LowerPair) (upper incoming : Bool) : List LowerHistoryEndCase :=
  let n := (lowerHistoryNatural C w upper false,lowerHistoryNatural C w upper true)
  if n.1 || n.2 then
    [((lowerHistoryEndVal C w upper false n.1,lowerHistoryEndVal C w upper true n.2),[])]
  else
    let e : List ℕ+ := if xor (!upper) (lowerHistoryWordParity C w false) then [3] else [1,3]
    let aux := lowerHistoryWH (w.1++e,w.2++e)
    (trunkNormalCases w incoming).flatMap fun (wide,norm) =>
      let cut : CertBound := if wide then ⟨false,false,lowerHistoryScaleThreshold (7/5) aux⟩
        else ⟨true,false,lowerHistoryScaleThreshold (5/7) aux⟩
      [false,true].map fun shortened =>
        ((lowerHistoryEndVal C w upper false (shortened && wide),
          lowerHistoryEndVal C w upper true (shortened && !wide)),
          [norm,if shortened then cut else lowerHistoryComplement cut])
def trunkEndpointCases (C : LowerHistoryContext) (w : LowerPair) (upper incoming : Bool) : List LowerHistoryEndCase :=
  if lowerHistoryWordParity C w false = lowerHistoryWordParity C w true then trunkEqualCases C w upper incoming
  else (trunkNormalCases w incoming).flatMap fun (wide,norm) =>
    let vs := if upper = !(lowerHistoryWordParity C w wide) then
      trunkEqualCases C (lowerHistorySet w wide (lowerHistoryPick w wide ++ [1])) upper incoming
    else [((lowerHistoryEndVal C w upper false (lowerHistoryNatural C w upper false),
            lowerHistoryEndVal C w upper true (lowerHistoryNatural C w upper true)),[])]
    vs.map fun (v,cs) => (v,norm::cs)
def trunkSpecIncoming (s : Section14Spec) : Bool :=
  (s.extra.head?.map CertBound.lower).getD false

def trunkGreater (C : LowerHistoryContext) (x y : CertField × CertField)
    (strict : Bool) : LowerHistoryComparison :=
  match lowerHistoryGreater C x y with
  | .automatic => if strict && decide (x = y) then .impossible else .automatic
  | .impossible => .impossible
  | .bound b => .bound { b with strict := strict }
def trunkBranches (C : LowerHistoryContext) (s : Section14Spec) :
    List (List CertBound × LowerHistoryComparison) :=
  (trunkEndpointCases C s.first s.firstUpper (trunkSpecIncoming s)).flatMap fun (x,cx) =>
    (trunkEndpointCases C s.second s.secondUpper (trunkSpecIncoming s)).map fun (y,cy) =>
      (s.extra++cx++cy,trunkGreater C x y s.strict)
def trunkParents (C : LowerHistoryContext) : List (List CertBound) :=
  let a := trunkBranches C ⟨([2],[]),true,([1],[]),false,false,[]⟩
  let b := trunkBranches C ⟨([1],[]),true,([2],[]),false,false,[]⟩
  let raw := a.flatMap fun (ca,ga) => b.filterMap fun (cb,gb) =>
    let base := ca++cb++[lowerHistoryHN,lowerHistoryZero]
    match ga,gb with
    | .impossible,_ | _,.impossible => none
    | .automatic,.automatic => some base
    | .bound g,.automatic | .automatic,.bound g => some (g::base)
    | .bound g,.bound h => some (g::h::base)
  raw.foldl (fun acc bs => if acc.any (fun cs => decide (cs.toFinset = bs.toFinset))
    then acc else acc++[bs]) []
def trunkSpecs (p : TrunkPlan) : List Section14Spec :=
  let inside := p.labels.flatMap fun l =>
    let w := section14LabelWords l
    ⟨w,true,w,false,false,[]⟩ :: (section14NormalCases w).flatMap fun (wide,norm) =>
      let one := lowerHistorySet w wide (lowerHistoryPick w wide ++ [1])
      let two := lowerHistorySet w wide (lowerHistoryPick w wide ++ [2])
      [⟨one,true,two,false,true,[norm]⟩,⟨two,true,one,false,true,[norm]⟩]
  let contact := (p.labels.zip p.labels.tail).flatMap fun (l,m) =>
    if (l,m) ∈ p.holes then [] else
    [⟨section14LabelWords l,true,section14LabelWords m,false,false,[]⟩,
      ⟨section14LabelWords m,true,section14LabelWords l,false,false,[]⟩]
  inside++contact++
    (p.labels.head?.toList.map fun l => ⟨section14LabelWords l,true,([],[]),true,false,[]⟩)++
    (p.labels.getLast?.toList.map fun l => ⟨([],[]),false,section14LabelWords l,false,false,[]⟩)

structure TrunkWitness where
  lowerId : ℕ
  upperId : ℕ
  rectangle : CertRectangle
  diagonal : ℤ
  margin : ℚ
  deriving DecidableEq
inductive TrunkTree where
  | pair (witness : ℕ)
  | split (sAxis : Bool) (left right : TrunkTree)
  | diagonal (negative positive : ℕ)
  | boundary
  deriving DecidableEq
structure TrunkGroup where
  plan : ℕ
  parents : List ℕ
  goal : ℕ
  branches : List (ℤ × TrunkTree)
  deriving DecidableEq
structure TrunkState where
  context : LowerHistoryContext
  rectangle : CertRectangle
  groups : List TrunkGroup
  deriving DecidableEq
structure TrunkCatalog where
  bounds : Array CertBound
  witnesses : Array TrunkWitness
  states : Fin 16 → TrunkState

def trunkBound (C : TrunkCatalog) (id : ℕ) : CertBound := C.bounds[id-1]?.getD lowerHistoryZero
def trunkWitness (C : TrunkCatalog) (id : ℕ) : TrunkWitness :=
  C.witnesses[id-1]?.getD ⟨0,0,⟨0,1,0,1⟩,0,0⟩
def trunkPolynomial (C : TrunkCatalog) (w : TrunkWitness) : CertPoly22 :=
  certCrossPolynomial (trunkBound C w.lowerId).threshold (trunkBound C w.upperId).threshold
def trunkPairWitness (C : TrunkCatalog) (w : TrunkWitness) : CertWitness :=
  ⟨trunkBound C w.lowerId,trunkBound C w.upperId,w.rectangle,
    certBernsteinCoefficients (trunkPolynomial C w) w.rectangle,fun _ _ => w.margin/2⟩
def trunkCorner (a b : ℚ) (i : Fin 2) : ℚ := if i = 0 then a else b
def trunkDiagonalCoefficient (C : TrunkCatalog) (w : TrunkWitness) (i j : Fin 2) : CertField :=
  let r := trunkCorner w.rectangle.r0 w.rectangle.r1 i
  let s := trunkCorner w.rectangle.s0 w.rectangle.s1 j
  let P := trunkPolynomial C w
  certFieldScale w.diagonal (certFieldAdd (P 1 0)
    (certFieldAdd (certFieldScale (r+s) (P 2 0)) (certFieldScale (r*s) (P 2 1))))
def trunkWitnessValid (C : TrunkCatalog) (w : TrunkWitness) : Prop :=
  0 < w.lowerId ∧ w.lowerId ≤ C.bounds.size ∧ 0 < w.upperId ∧ w.upperId ≤ C.bounds.size ∧
  if w.diagonal = 0 then certWitnessValid (trunkPairWitness C w) else
    (w.diagonal = -1 ∨ w.diagonal = 1) ∧ certRectangleValid w.rectangle ∧ 0 ≤ w.rectangle.r0 ∧
    (trunkBound C w.lowerId).lower = true ∧ (trunkBound C w.upperId).lower = false ∧
    certThresholdDataValid (trunkBound C w.lowerId).threshold ∧
    certThresholdDataValid (trunkBound C w.upperId).threshold ∧
    ((trunkBound C w.lowerId).strict = true ∨ (trunkBound C w.upperId).strict = true) ∧
    (∀ i j : Fin 3, trunkPolynomial C w i j = certFieldScale (-1) (trunkPolynomial C w j i)) ∧
    0 < w.margin ∧ ∀ i j : Fin 2, w.margin/2 < certFieldLower (trunkDiagonalCoefficient C w i j)
def trunkRectangleHalf (R : CertRectangle) (sAxis upper : Bool) : CertRectangle :=
  if sAxis then
    if upper then ⟨R.r0,R.r1,(R.s0+R.s1)/2,R.s1⟩ else ⟨R.r0,R.r1,R.s0,(R.s0+R.s1)/2⟩
  else if upper then ⟨(R.r0+R.r1)/2,R.r1,R.s0,R.s1⟩ else ⟨R.r0,(R.r0+R.r1)/2,R.s0,R.s1⟩
def trunkUseBounds (C : TrunkCatalog) (w : TrunkWitness) (l u : CertBound) : Prop :=
  l.lower = true ∧ u.lower = false ∧
  l.threshold = (trunkBound C w.lowerId).threshold ∧
  u.threshold = (trunkBound C w.upperId).threshold ∧
  ((w.diagonal = 0 ∧ 0 < w.margin) ∨ l.strict = true ∨ u.strict = true)
def trunkLeafBound (C : TrunkCatalog) (R : CertRectangle) (bs : List CertBound)
    (id : ℕ) (sign : ℤ) : Prop :=
  0 < id ∧ id ≤ C.witnesses.size ∧
  (trunkWitness C id).diagonal = sign ∧
  section14RectangleContains (trunkWitness C id).rectangle R ∧
  ∃ l ∈ bs, ∃ u ∈ bs, trunkUseBounds C (trunkWitness C id) l u

def trunkBoundaryPolynomial : CertPoly22 :=
  certCrossPolynomial (lowerHistoryWH ([1],[1])) (lowerHistoryWH ([],[]))
def trunkBoundaryCertificateValid : Prop :=
  (∀ i j : Fin 3, trunkBoundaryPolynomial i j = certFieldScale (-1) (trunkBoundaryPolynomial j i)) ∧
  trunkBoundaryPolynomial 1 0 = ⟨-3/5,0,0,1/15⟩ ∧
  trunkBoundaryPolynomial 2 0 = ⟨8/5,0,0,-2/5⟩ ∧
  trunkBoundaryPolynomial 2 1 = ⟨-33/5,0,0,7/5⟩ ∧
  0 < certFieldLower (certFieldScale (-1) (trunkBoundaryPolynomial 1 0)) ∧
  0 < certFieldLower (certFieldScale (-1) (trunkBoundaryPolynomial 2 0)) ∧
  0 < certFieldLower (certFieldScale (-1) (trunkBoundaryPolynomial 2 1)) ∧
  certThresholdDataValid (lowerHistoryWH ([1],[1])) ∧
  certThresholdDataValid (lowerHistoryWH ([],[]))
def trunkThresholdOneDifference (t : CertThreshold) (a : ℚ) : CertField :=
  let factor := fun x => certFieldAdd (lowerHistoryRat 1) (certFieldScale a x)
  certFieldSub (certFieldMul t.c (certFieldMul (factor t.y0) (factor t.y1)))
    (certFieldMul (factor t.x0) (factor t.x1))
def trunkBoundaryBound (R : CertRectangle) (bs : List CertBound) : Prop :=
  0 ≤ R.r0 ∧ 0 ≤ R.s0 ∧ R.r1 = R.s0 ∧
  (∃ l ∈ bs, l.lower = true ∧ l.threshold = lowerHistoryWH ([1],[1])) ∧
  (∃ u ∈ bs, u.lower = false ∧ u.threshold = lowerHistoryWH ([],[])) ∧
  ∃ b ∈ bs, b.lower = true ∧ certThresholdDataValid b.threshold ∧
    0 < certFieldLower (trunkThresholdOneDifference b.threshold R.r1)
def trunkTreeBound (C : TrunkCatalog) (R : CertRectangle) (bs : List CertBound) : TrunkTree → Prop
  | .pair id => trunkLeafBound C R bs id 0
  | .split axis left right =>
    trunkTreeBound C (trunkRectangleHalf R axis false) bs left ∧
    trunkTreeBound C (trunkRectangleHalf R axis true) bs right
  | .diagonal negative positive => trunkLeafBound C R bs negative (-1) ∧ trunkLeafBound C R bs positive 1
  | .boundary => trunkBoundaryBound R bs

def trunkPlanAt (S : TrunkState) (pi : ℕ) : TrunkPlan :=
  (trunkSourcePlans S.context)[pi]?.getD ⟨[],[],[]⟩
def trunkBaseConditions (S : TrunkState) (plan parent : ℕ) : List CertBound :=
  (trunkPlanAt S plan).cuts ++ (trunkParents S.context)[parent]?.getD []
def trunkGoalBranches (S : TrunkState) (plan goal : ℕ) : List (List CertBound × LowerHistoryComparison) :=
  if goal = 0 then [([],.impossible)] else
    trunkBranches S.context ((trunkSpecs (trunkPlanAt S plan))[goal-1]?.getD ⟨([],[]),false,([],[]),false,false,[]⟩)
def trunkBranch (S : TrunkState) (plan goal : ℕ) (branch : ℤ) : List CertBound × LowerHistoryComparison :=
  (trunkGoalBranches S plan goal)[branch.toNat]?.getD ([],.impossible)
def trunkResidual (S : TrunkState) (plan parent goal : ℕ) (branch : ℤ) : List CertBound :=
  let b := trunkBranch S plan goal branch
  trunkBaseConditions S plan parent ++ b.1 ++
    match b.2 with | .bound a => [lowerHistoryComplement a] | _ => []
def trunkGroupValid (C : TrunkCatalog) (k : Fin 16) (g : TrunkGroup) : Prop :=
  let S := C.states k
  g.plan < (trunkSourcePlans S.context).length ∧ g.goal ≤ (trunkSpecs (trunkPlanAt S g.plan)).length ∧
  (∀ p ∈ g.parents, p < (trunkParents S.context).length) ∧
  ∀ bt ∈ g.branches,
    ((g.goal = 0 ∧ bt.1 = -1) ∨ (0 < g.goal ∧ 0 ≤ bt.1 ∧ bt.1.toNat < (trunkGoalBranches S g.plan g.goal).length)) ∧
    (trunkBranch S g.plan g.goal bt.1).2 ≠ .automatic ∧
    ∀ p ∈ g.parents, trunkTreeBound C S.rectangle (trunkResidual S g.plan p g.goal bt.1) bt.2
def trunkRecorded (C : TrunkCatalog) (k : Fin 16) (plan parent goal : ℕ) (branch : ℤ) : Prop :=
  ∃ g ∈ (C.states k).groups, g.plan = plan ∧ parent ∈ g.parents ∧ g.goal = goal ∧
    ∃ tree, (branch,tree) ∈ g.branches
def trunkCoverage (C : TrunkCatalog) (k : Fin 16) : Prop :=
  let S := C.states k
  certRectangleValid S.rectangle ∧ 0 ≤ S.rectangle.r0 ∧
  ∀ pi : ℕ, pi < (trunkSourcePlans S.context).length →
  ∀ par : ℕ, par < (trunkParents S.context).length →
    trunkRecorded C k pi par 0 (-1) ∨
    ∀ goal : ℕ, 0 < goal → goal ≤ (trunkSpecs (trunkPlanAt S pi)).length →
    ∀ bi : ℕ, bi < (trunkGoalBranches S pi goal).length →
      (trunkBranch S pi goal bi).2 = .automatic ∨ trunkRecorded C k pi par goal bi
def trunkAllWitnesses (C : TrunkCatalog) : Prop :=
  ∀ id : ℕ, 0 < id → id ≤ C.witnesses.size → trunkWitnessValid C (trunkWitness C id)
def trunkAllBindings (C : TrunkCatalog) : Prop :=
  ∀ k : Fin 16, (∀ g ∈ (C.states k).groups, trunkGroupValid C k g) ∧ trunkCoverage C k
def trunkHolds (bs : List CertBound) (r s q : ℝ) : Prop := ∀ b ∈ bs, certBoundHolds b r s q
def trunkStateSound (C : TrunkCatalog) (k : Fin 16) : Prop :=
  let S := C.states k
  ∀ pi par : ℕ, pi < (trunkSourcePlans S.context).length → par < (trunkParents S.context).length →
  ∀ r s q : ℝ, certRectangleMem S.rectangle r s → trunkHolds (trunkBaseConditions S pi par) r s q →
  ∀ goal : ℕ, 0 < goal → goal ≤ (trunkSpecs (trunkPlanAt S pi)).length →
  ∀ bi : ℕ, bi < (trunkGoalBranches S pi goal).length →
    trunkHolds (trunkBranch S pi goal bi).1 r s q →
    lowerHistoryComparisonHolds (trunkBranch S pi goal bi).2 r s q

end Freiman


