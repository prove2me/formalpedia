-- Prove2me | Definitions.Def_Freiman_lowerEarlyTerminalModel
-- name    : Freiman_lowerEarlyTerminalModel
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:20:56.945526+00:00
-- url     : https://prove2.me/theorems/2b1c38bc-ad30-44a2-a8bd-043ce90d3c15
-- title:
--   Freiman.lowerEarlyTerminalModel
-- statement:
--   Range-checked source goal, premise and pair records; strict endpoint and final triple-endpoint branch evaluator; exact finite validity predicates. Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/{residual_geometry_certificate,extension_1,extension_2}.json and certificates/section15_terminal/geometry_certificate.json; PROOF_GUIDE.md; verification/families/section15_early/{independent_residual,independent_extensions}.py and section15_terminal/verify_independent.py.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/{residual_geometry_certificate,extension_1,extension_2}.json and certificates/section15_terminal/geometry_certificate.json; PROOF_GUIDE.md; verification/families/section15_early/{independent_residual,independent_extensions}.py and section15_terminal/verify_independent.py. Lean module: Definitions.Def_Freiman_lowerEarlyTerminalModel.

import Definitions.Def_Freiman_section14Model
import Definitions.Def_Freiman_lowerHistoryVerification

namespace Freiman

inductive LowerEarlyTerminalKind where
  | compare (first : LowerPair) (firstUpper : Bool) (second : LowerPair)
      (secondUpper strict : Bool)
  | scalar (boundId : ℕ)
  | unionCase (branch : ℕ)
  | normalCase (branch : ℕ)
  deriving DecidableEq
structure LowerEarlyTerminalGoal where
  premises : List ℕ
  kind : LowerEarlyTerminalKind
  deriving DecidableEq
structure LowerEarlyTerminalPair where
  lowerId : ℕ
  upperId : ℕ
  coefficientLower : ℚ
  deriving DecidableEq
structure LowerEarlyTerminalRecord where
  goal : ℕ
  branch : ℕ
  premises : List ℕ
  pairId : ℕ
  deriving DecidableEq
structure LowerEarlyTerminalCatalog where
  leftContext : List ℕ+
  rectangle : CertRectangle
  bounds : List CertBound
  goals : List LowerEarlyTerminalGoal
  pairs : List LowerEarlyTerminalPair
  records : List LowerEarlyTerminalRecord

def lowerEarlyTerminalContext (C : LowerEarlyTerminalCatalog) : LowerHistoryContext :=
  ⟨(C.leftContext,[3,1]),(false,false)⟩
def lowerEarlyTerminalBound (C : LowerEarlyTerminalCatalog) (id : ℕ) : CertBound :=
  C.bounds[id-1]?.getD ⟨true,true,⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩
def lowerEarlyTerminalBoundsAt (C : LowerEarlyTerminalCatalog) (ids : List ℕ) : List CertBound :=
  ids.map (lowerEarlyTerminalBound C)
def lowerEarlyTerminalGoal (C : LowerEarlyTerminalCatalog) (id : ℕ) : LowerEarlyTerminalGoal :=
  C.goals[id]?.getD ⟨[],.scalar 0⟩
def lowerEarlyTerminalPair (C : LowerEarlyTerminalCatalog) (id : ℕ) : LowerEarlyTerminalPair :=
  C.pairs[id]?.getD ⟨0,0,0⟩
def lowerEarlyTerminalGreater (x y : CertField × CertField) (strict : Bool) : LowerHistoryComparison :=
  match lowerHistoryGreater ⟨([],[]),(false,false)⟩ x y with
  | .automatic => if strict && decide (x=y) then .impossible else .automatic
  | .impossible => .impossible
  | .bound b => .bound { b with strict := strict }
def lowerEarlyTerminalCompare (C : LowerEarlyTerminalCatalog) (u : LowerPair) (hi : Bool)
    (v : LowerPair) (hj strict : Bool) : List (List CertBound × LowerHistoryComparison) :=
  (section14EndpointCases (lowerEarlyTerminalContext C) u hi).flatMap fun (x,cx) =>
    (section14EndpointCases (lowerEarlyTerminalContext C) v hj).map fun (y,cy) =>
      (cx++cy,lowerEarlyTerminalGreater x y strict)
def lowerEarlyTerminalUnionCases (C : LowerEarlyTerminalCatalog) :
    List (List CertBound × LowerHistoryComparison) :=
  (section14EndpointCases (lowerEarlyTerminalContext C) ([2,1,1,2],[3,3]) true).flatMap fun (a,ca) =>
    (section14EndpointCases (lowerEarlyTerminalContext C) ([2,1,1,3],[3,3]) false).flatMap fun (b,cb) =>
      (section14EndpointCases (lowerEarlyTerminalContext C) ([2],[2]) false).map fun (c,cc) =>
        let cs := ca++cb++cc
        match lowerEarlyTerminalGreater a b false,lowerEarlyTerminalGreater a c false with
        | .automatic,_ | _,.automatic => (cs,.automatic)
        | .impossible,g | g,.impossible => (cs,g)
        | .bound f,.bound g => (lowerHistoryComplement f::cs,.bound g)
def lowerEarlyTerminalBranches (C : LowerEarlyTerminalCatalog) (k : LowerEarlyTerminalKind) :
    List (List CertBound × LowerHistoryComparison) :=
  match k with
  | .compare u a v b s => lowerEarlyTerminalCompare C u a v b s
  | .scalar id => [([],.bound (lowerEarlyTerminalBound C id))]
  | .unionCase j => [(lowerEarlyTerminalUnionCases C)[j]?.getD ([],.impossible)]
  | .normalCase j =>
    [(((section14EndpointCases (lowerEarlyTerminalContext C) ([2,1,1,1],[3,1,1]) true)[j]?.getD
      ((⟨0,0,0,0⟩,⟨0,0,0,0⟩),[])).2,.impossible)]
def lowerEarlyTerminalResidual (C : LowerEarlyTerminalCatalog) (g : LowerEarlyTerminalGoal)
    (j : ℕ) : List CertBound :=
  let b := (lowerEarlyTerminalBranches C g.kind)[j]?.getD ([],.impossible)
  lowerEarlyTerminalBoundsAt C g.premises ++ b.1 ++
    (match b.2 with | .bound h => [lowerHistoryComplement h] | _ => [])
def lowerEarlyTerminalWitness (C : LowerEarlyTerminalCatalog) (p : LowerEarlyTerminalPair) : CertWitness :=
  let l := lowerEarlyTerminalBound C p.lowerId
  let u := lowerEarlyTerminalBound C p.upperId
  ⟨l,u,C.rectangle,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) C.rectangle,
    fun _ _ => p.coefficientLower⟩
def lowerEarlyTerminalGoalValid (C : LowerEarlyTerminalCatalog) (g : LowerEarlyTerminalGoal) : Prop :=
  (∀ id ∈ g.premises, 0 < id ∧ id ≤ C.bounds.length) ∧
  match g.kind with
  | .scalar id => 0 < id ∧ id ≤ C.bounds.length
  | .unionCase j => j < (lowerEarlyTerminalUnionCases C).length
  | .normalCase j => j < (section14EndpointCases (lowerEarlyTerminalContext C) ([2,1,1,1],[3,1,1]) true).length
  | .compare _ _ _ _ _ => True
def lowerEarlyTerminalPairValid (C : LowerEarlyTerminalCatalog) (p : LowerEarlyTerminalPair) : Prop :=
  0 < p.lowerId ∧ p.lowerId ≤ C.bounds.length ∧
  0 < p.upperId ∧ p.upperId ≤ C.bounds.length ∧
  certWitnessValid (lowerEarlyTerminalWitness C p)
def lowerEarlyTerminalRecordValid (C : LowerEarlyTerminalCatalog) (r : LowerEarlyTerminalRecord) : Prop :=
  r.goal < C.goals.length ∧ r.pairId < C.pairs.length ∧
  (∀ id ∈ r.premises, 0 < id ∧ id ≤ C.bounds.length) ∧
  r.branch < (lowerEarlyTerminalBranches C (lowerEarlyTerminalGoal C r.goal).kind).length ∧
  (lowerEarlyTerminalBoundsAt C r.premises).toFinset =
    (lowerEarlyTerminalResidual C (lowerEarlyTerminalGoal C r.goal) r.branch).toFinset ∧
  (lowerEarlyTerminalPair C r.pairId).lowerId ∈ r.premises ∧
  (lowerEarlyTerminalPair C r.pairId).upperId ∈ r.premises
def lowerEarlyTerminalCoverage (C : LowerEarlyTerminalCatalog) : Prop :=
  ∀ g ∈ List.range C.goals.length,
    ∀ j ∈ List.range (lowerEarlyTerminalBranches C (lowerEarlyTerminalGoal C g).kind).length,
      ((lowerEarlyTerminalBranches C (lowerEarlyTerminalGoal C g).kind)[j]?.getD ([],.impossible)).2 = .automatic ∨
        ∃ r ∈ C.records, r.goal = g ∧ r.branch = j
def lowerEarlyTerminalFiniteValid (C : LowerEarlyTerminalCatalog) : Prop :=
  (∀ g ∈ C.goals, lowerEarlyTerminalGoalValid C g) ∧
  (∀ p ∈ C.pairs, lowerEarlyTerminalPairValid C p) ∧
  (∀ r ∈ C.records, lowerEarlyTerminalRecordValid C r) ∧ lowerEarlyTerminalCoverage C
noncomputable def lowerEarlyTerminalGoalsSound (C : LowerEarlyTerminalCatalog) : Prop :=
  ∀ r s q : ℝ, certRectangleMem C.rectangle r s →
    ∀ g ∈ C.goals, section14Holds (lowerEarlyTerminalBoundsAt C g.premises) r s q →
      ∀ b ∈ lowerEarlyTerminalBranches C g.kind, section14Holds b.1 r s q →
        section14ComparisonHolds b.2 r s q

end Freiman


