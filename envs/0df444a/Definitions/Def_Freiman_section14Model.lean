-- Prove2me | Definitions.Def_Freiman_section14Model
-- name    : Freiman_section14Model
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T11:51:13.677709+00:00
-- url     : https://prove2.me/theorems/4b557469-4b9f-4d12-b50d-4e39a4eb5022
-- title:
--   Freiman §14: section14Model
-- statement:
--   Exact §14 source model, finite verifier or lossless report data; no theorem or axiom declarations.
-- source:
--   Freiman report, active §14; Appendix Complete finite certificates for the scalar geometry of §14; full_readable_model.json.

import Definitions.Def_Freiman_lowerHistoryAlgebra

namespace Freiman

structure Section14BoundRef where
  lower : Bool
  strict : Bool
  threshold : ℕ
  deriving DecidableEq
structure Section14Endpoint where
  family : ℕ
  branch : ℕ
  x : ℕ
  y : ℕ
  conditions : List Section14BoundRef
  deriving DecidableEq
structure Section14Parent where
  family : ℕ
  branch : ℕ
  conditions : List Section14BoundRef
  deriving DecidableEq
structure Section14Goal where
  caseId : ℕ
  first : ℕ
  second : ℕ
  strict : Bool
  extra : List Section14BoundRef
  automatic : List ℕ
  deriving DecidableEq
structure Section14Proof where
  lowerBound : Section14BoundRef
  upperBound : Section14BoundRef
  deriving DecidableEq
structure Section14Witness where
  firstThreshold : ℕ
  secondThreshold : ℕ
  rectangle : CertRectangle
  lowerNumerator : ℕ
  deriving DecidableEq
structure Section14Assignment where
  proofId : ℕ
  states : List ℕ
  witnessId : ℕ
  deriving DecidableEq
structure Section14Record where
  goal : ℕ
  branch : ℤ
  states : List ℕ
  parents : List ℕ
  proofId : ℕ
  deriving DecidableEq
structure Section14Spec where
  first : LowerPair
  firstUpper : Bool
  second : LowerPair
  secondUpper : Bool
  strict : Bool
  extra : List CertBound
  deriving DecidableEq
structure Section14Plan where
  caseId : ℕ
  excludedGoal : ℕ
  labels : List LowerLabel
  targetLower : Bool
  specs : List (ℕ × Section14Spec)
  deriving DecidableEq
structure Section14State where
  context : LowerHistoryContext
  rectangle : CertRectangle
  parentFamily : ℕ
  plans : List Section14Plan
  deriving DecidableEq
structure Section14Catalog where
  tails : List CertField
  thresholds : List CertThreshold
  endpoints : List Section14Endpoint
  parents : List Section14Parent
  cases : List (List Section14BoundRef)
  goals : List Section14Goal
  proofs : List Section14Proof
  witnesses : List Section14Witness
  assignments : List Section14Assignment
  records : List Section14Record
  states : List Section14State

def section14Zero : CertField := ⟨0,0,0,0⟩
def section14Threshold (C : Section14Catalog) (i : ℕ) : CertThreshold :=
  C.thresholds[i-1]?.getD ⟨section14Zero,section14Zero,section14Zero,section14Zero,section14Zero⟩
def section14Tail (C : Section14Catalog) (i : ℕ) : CertField :=
  C.tails[i-1]?.getD section14Zero
def section14Bound (C : Section14Catalog) (b : Section14BoundRef) : CertBound :=
  ⟨b.lower,b.strict,section14Threshold C b.threshold⟩
def section14Bounds (C : Section14Catalog) (bs : List Section14BoundRef) : List CertBound :=
  bs.map (section14Bound C)
def section14Endpoints (C : Section14Catalog) (i : ℕ) : List LowerHistoryEndCase :=
  (C.endpoints.filter (fun e => e.family == i)).map fun e =>
    ((section14Tail C e.x,section14Tail C e.y),section14Bounds C e.conditions)
def section14Goal (C : Section14Catalog) (i : ℕ) : Section14Goal :=
  C.goals[i-1]?.getD ⟨0,0,0,false,[],[]⟩
def section14Case (C : Section14Catalog) (i : ℕ) : List CertBound :=
  section14Bounds C (C.cases[i-1]?.getD [])
def section14Parents (C : Section14Catalog) (S : Section14State) : List Section14Parent :=
  C.parents.filter (fun p => p.family == S.parentFamily)
def section14Proof (C : Section14Catalog) (i : ℕ) : Section14Proof :=
  C.proofs[i-1]?.getD ⟨⟨true,false,0⟩,⟨false,false,0⟩⟩
def section14Witness (C : Section14Catalog) (i : ℕ) : Section14Witness :=
  C.witnesses[i-1]?.getD ⟨0,0,⟨0,0,0,0⟩,0⟩
def section14State (C : Section14Catalog) (i : ℕ) : Section14State :=
  C.states[i-1]?.getD ⟨⟨([],[]),(false,true)⟩,⟨0,0,0,0⟩,0,[]⟩
def section14PairWitness (C : Section14Catalog) (p : Section14Proof)
    (w : Section14Witness) : CertWitness :=
  let l := section14Bound C p.lowerBound
  let u := section14Bound C p.upperBound
  ⟨l,u,w.rectangle,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) w.rectangle,
    fun _ _ => (w.lowerNumerator : ℚ)/(2*10^24)⟩

-- Unlike the history over-approximation, the scalar appendix retains the
-- first side at a full-width tie: its second normalization branch is strict.
def section14NormalCases (w : LowerPair) : List (Bool × CertBound) :=
  [(false,⟨false,false,lowerHistoryWH w⟩),(true,⟨true,true,lowerHistoryWH w⟩)]
def section14EqualCases (C : LowerHistoryContext) (w : LowerPair) (upper : Bool) : List LowerHistoryEndCase :=
  let n := (lowerHistoryNatural C w upper false,lowerHistoryNatural C w upper true)
  if n.1 || n.2 then
    [((lowerHistoryEndVal C w upper false n.1,lowerHistoryEndVal C w upper true n.2),[])]
  else
    let e : List ℕ+ := if xor (!upper) (lowerHistoryWordParity C w false) then [3] else [1,3]
    let aux := lowerHistoryWH (w.1++e,w.2++e)
    (section14NormalCases w).flatMap fun (wide,norm) =>
      let cut : CertBound := if wide then ⟨false,false,lowerHistoryScaleThreshold (7/5) aux⟩
        else ⟨true,false,lowerHistoryScaleThreshold (5/7) aux⟩
      [false,true].map fun shortened =>
        ((lowerHistoryEndVal C w upper false (shortened && wide),
          lowerHistoryEndVal C w upper true (shortened && !wide)),
          [norm,if shortened then cut else lowerHistoryComplement cut])
def section14EndpointCases (C : LowerHistoryContext) (w : LowerPair) (upper : Bool) : List LowerHistoryEndCase :=
  if lowerHistoryWordParity C w false = lowerHistoryWordParity C w true then section14EqualCases C w upper
  else (section14NormalCases w).flatMap fun (wide,norm) =>
    let vs := if upper = !(lowerHistoryWordParity C w wide) then
      section14EqualCases C (lowerHistorySet w wide (lowerHistoryPick w wide ++ [1])) upper
    else [((lowerHistoryEndVal C w upper false (lowerHistoryNatural C w upper false),
            lowerHistoryEndVal C w upper true (lowerHistoryNatural C w upper true)),[])]
    vs.map fun (v,cs) => (v,norm::cs)
def section14Greater (x y : CertField × CertField) (strict : Bool) : LowerHistoryComparison :=
  match lowerHistoryGreater ⟨([],[]),(false,true)⟩ x y with
  | .automatic => if strict && decide (x = y) then .impossible else .automatic
  | .impossible => .impossible
  | .bound b => .bound { b with strict := strict }
def section14ComparisonBranches (C : LowerHistoryContext) (s : Section14Spec) :
    List (List CertBound × LowerHistoryComparison) :=
  (section14EndpointCases C s.first s.firstUpper).flatMap fun (x,cx) =>
    (section14EndpointCases C s.second s.secondUpper).map fun (y,cy) =>
      (s.extra++cx++cy,section14Greater x y s.strict)
def section14ExpectedParents (C : LowerHistoryContext) : List (List CertBound) :=
  let a := section14ComparisonBranches C ⟨([2],[]),true,([1],[]),false,false,[]⟩
  let b := section14ComparisonBranches C ⟨([1],[]),true,([2],[]),false,false,[]⟩
  a.flatMap fun (ca,ga) => b.filterMap fun (cb,gb) =>
    let base := ca++cb++[⟨false,false,lowerHistoryWH ([],[])⟩,
      ⟨true,true,⟨section14Zero,section14Zero,section14Zero,section14Zero,section14Zero⟩⟩]
    match ga,gb with
    | .impossible,_ | _,.impossible => none
    | .automatic,.automatic => some base
    | .bound g,.automatic | .automatic,.bound g => some (g::base)
    | .bound g,.bound h => some (g::h::base)
def section14LabelWords (l : LowerLabel) : LowerPair := (l.1.reverse,l.2)
def section14ExpectedSpecs (ls : List LowerLabel) (targetLower : Bool) : List Section14Spec :=
  let inside := ls.flatMap fun l =>
    let w := section14LabelWords l
    ⟨w,true,w,false,false,[]⟩ :: (section14NormalCases w).flatMap fun (wide,norm) =>
      let one := lowerHistorySet w wide (lowerHistoryPick w wide ++ [1])
      let two := lowerHistorySet w wide (lowerHistoryPick w wide ++ [2])
      [⟨one,true,two,false,true,[norm]⟩,⟨two,true,one,false,true,[norm]⟩]
  let contact := (ls.zip ls.tail).flatMap fun (l,m) =>
    [⟨section14LabelWords l,true,section14LabelWords m,false,false,[]⟩,
     ⟨section14LabelWords m,true,section14LabelWords l,false,false,[]⟩]
  inside ++ contact ++
    (ls.head?.toList.map fun l => ⟨section14LabelWords l,true,([],[]),true,false,[]⟩) ++
    (if targetLower then [] else
      ls.getLast?.toList.map fun l => ⟨([],[]),false,section14LabelWords l,false,false,[]⟩)
def section14EndSet (es : List LowerHistoryEndCase) : Finset ((CertField × CertField) × Finset CertBound) :=
  (es.map fun (v,cs) => (v,cs.toFinset)).toFinset
def section14SpecValid (C : Section14Catalog) (S : Section14State) (caseId : ℕ)
    (gs : ℕ × Section14Spec) : Prop :=
  let g := section14Goal C gs.1
  g.caseId = caseId ∧ 0 < g.first ∧ 0 < g.second ∧ g.strict = gs.2.strict ∧
  (section14Bounds C g.extra).toFinset = gs.2.extra.toFinset ∧
  section14EndSet (section14Endpoints C g.first) =
    section14EndSet (section14EndpointCases S.context gs.2.first gs.2.firstUpper) ∧
  section14EndSet (section14Endpoints C g.second) =
    section14EndSet (section14EndpointCases S.context gs.2.second gs.2.secondUpper)
def section14PlanValid (C : Section14Catalog) (S : Section14State) (p : Section14Plan) : Prop :=
  p.labels ≠ [] ∧
  (section14Goal C p.excludedGoal).first = 0 ∧
  (section14Goal C p.excludedGoal).second = 0 ∧
  (section14Goal C p.excludedGoal).caseId = p.caseId ∧
  (section14Goal C p.excludedGoal).extra = [] ∧
  (p.specs.map Prod.snd).toFinset = (section14ExpectedSpecs p.labels p.targetLower).toFinset ∧
  ∀ gs ∈ p.specs, section14SpecValid C S p.caseId gs
def section14GoalBranches (C : Section14Catalog) (g : Section14Goal) :
    List (List CertBound × LowerHistoryComparison) :=
  if g.first = 0 then [([], .impossible)] else
    (section14Endpoints C g.first).flatMap fun (x,cx) =>
      (section14Endpoints C g.second).map fun (y,cy) =>
        (section14Bounds C g.extra++cx++cy,section14Greater x y g.strict)
def section14Branch (C : Section14Catalog) (g : Section14Goal) (b : ℤ) :
    List CertBound × LowerHistoryComparison :=
  (section14GoalBranches C g)[b.toNat]?.getD ([],.impossible)
def section14NegatedConditions (bs : List CertBound) (v : LowerHistoryComparison) : List CertBound :=
  match v with | .bound b => lowerHistoryComplement b :: bs | _ => bs
def section14RecordConditions (C : Section14Catalog) (r : Section14Record) (p : Section14Parent) : List CertBound :=
  let g := section14Goal C r.goal
  let v := section14Branch C g r.branch
  section14Case C g.caseId ++ section14Bounds C p.conditions ++ section14NegatedConditions v.1 v.2
def section14RectangleContains (outer inner : CertRectangle) : Prop :=
  outer.r0 ≤ inner.r0 ∧ inner.r1 ≤ outer.r1 ∧ outer.s0 ≤ inner.s0 ∧ inner.s1 ≤ outer.s1
def section14RecordValid (C : Section14Catalog) (si : ℕ) (r : Section14Record) : Prop :=
  let S := section14State C si
  let p := section14Proof C r.proofId
  0 < r.goal ∧ r.goal ≤ C.goals.length ∧ 0 < r.proofId ∧ r.proofId ≤ C.proofs.length ∧
  (section14Branch C (section14Goal C r.goal) r.branch).2 ≠ .automatic ∧
  (∀ b ∈ section14Parents C S, b.branch ∈ r.parents →
    section14Bound C p.lowerBound ∈ section14RecordConditions C r b ∧
    section14Bound C p.upperBound ∈ section14RecordConditions C r b) ∧
  ∃ a ∈ C.assignments, a.proofId = r.proofId ∧ si ∈ a.states ∧
    0 < a.witnessId ∧ a.witnessId ≤ C.witnesses.length ∧
    let w := section14Witness C a.witnessId
    w.firstThreshold = p.lowerBound.threshold ∧ w.secondThreshold = p.upperBound.threshold ∧
    section14RectangleContains w.rectangle S.rectangle ∧ certWitnessValid (section14PairWitness C p w)
def section14Recorded (C : Section14Catalog) (si parent goal : ℕ) (branch : ℤ) : Prop :=
  ∃ r ∈ C.records, si ∈ r.states ∧ parent ∈ r.parents ∧ r.goal = goal ∧ r.branch = branch
def section14Coverage (C : Section14Catalog) (si : ℕ) : Prop :=
  let S := section14State C si
  ∀ pl ∈ S.plans, ∀ b ∈ section14Parents C S,
    section14Recorded C si b.branch pl.excludedGoal (-1) ∨
    ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches C (section14Goal C gs.1)).length,
      (section14Branch C (section14Goal C gs.1) j).2 = .automatic ∨
      section14Recorded C si b.branch gs.1 j
def section14StateValid (C : Section14Catalog) (si : ℕ) : Prop :=
  let S := section14State C si
  certRectangleValid S.rectangle ∧ 0 ≤ S.rectangle.r0 ∧ 0 ≤ S.rectangle.s0 ∧
  ((section14Parents C S).map fun p => (section14Bounds C p.conditions).toFinset).toFinset =
    ((section14ExpectedParents S.context).map List.toFinset).toFinset ∧
  (∀ pl ∈ S.plans, section14PlanValid C S pl) ∧
  (∀ r ∈ C.records, si ∈ r.states → section14RecordValid C si r) ∧ section14Coverage C si

noncomputable def section14Holds (bs : List CertBound) (r s q : ℝ) : Prop :=
  ∀ b ∈ bs, certBoundHolds b r s q
noncomputable def section14ComparisonHolds (v : LowerHistoryComparison) (r s q : ℝ) : Prop :=
  match v with | .automatic => True | .impossible => False | .bound b => certBoundHolds b r s q
noncomputable def section14RecordSound (C : Section14Catalog) (si : ℕ) (rec : Section14Record) : Prop :=
  ∀ p ∈ section14Parents C (section14State C si), p.branch ∈ rec.parents →
  ∀ r s q : ℝ, certRectangleMem (section14State C si).rectangle r s →
    ¬ section14Holds (section14RecordConditions C rec p) r s q
noncomputable def section14StateSound (C : Section14Catalog) (si : ℕ) : Prop :=
  let S := section14State C si
  ∀ pl ∈ S.plans, ∀ p ∈ section14Parents C S, ∀ r s q : ℝ,
    certRectangleMem S.rectangle r s →
    section14Holds (section14Case C pl.caseId ++ section14Bounds C p.conditions) r s q →
    ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches C (section14Goal C gs.1)).length,
      section14Holds (section14Branch C (section14Goal C gs.1) j).1 r s q →
      section14ComparisonHolds (section14Branch C (section14Goal C gs.1) j).2 r s q

end Freiman


