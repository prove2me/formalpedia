-- Prove2me | Definitions.Def_Freiman_lateModel
-- name    : Freiman_lateModel
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:20:59.990357+00:00
-- url     : https://prove2.me/theorems/5c35409e-e514-4c34-b9be-3cac5ee274d2
-- title:
--   Freiman late: lateModel
-- statement:
--   Exact source late decision catalogue, shared-kernel finite validator or actual-cover interface; no theorem/axiom declarations.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lowerHistoryAlgebra
import Mathlib.Data.Finset.Basic

namespace Freiman

-- The late appendix keeps the strict reflected normalization branch.
def lateContext (right3 : Bool) : LowerHistoryContext :=
  ⟨([3,1],if right3 then [3] else [3,1]),(false,false)⟩
def lateNormals (w : LowerPair) : List (Bool × CertBound) :=
  [(false,⟨false,false,lowerHistoryWH w⟩),(true,⟨true,true,lowerHistoryWH w⟩)]
def lateEqualCases (C : LowerHistoryContext) (w : LowerPair) (upper : Bool) : List LowerHistoryEndCase :=
  let n := (lowerHistoryNatural C w upper false,lowerHistoryNatural C w upper true)
  if n.1 || n.2 then
    [((lowerHistoryEndVal C w upper false n.1,lowerHistoryEndVal C w upper true n.2),[])]
  else
    let e : List ℕ+ := if xor (!upper) (lowerHistoryWordParity C w false) then [3] else [1,3]
    let aux := lowerHistoryWH (w.1++e,w.2++e)
    (lateNormals w).flatMap fun (wide,norm) =>
      let cut : CertBound := if wide then ⟨false,false,lowerHistoryScaleThreshold (7/5) aux⟩
        else ⟨true,false,lowerHistoryScaleThreshold (5/7) aux⟩
      [false,true].map fun shortened =>
        ((lowerHistoryEndVal C w upper false (shortened && wide),
          lowerHistoryEndVal C w upper true (shortened && !wide)),
          [norm,if shortened then cut else lowerHistoryComplement cut])
def lateEndpointCases (right3 : Bool) (w : LowerPair) (upper : Bool) : List LowerHistoryEndCase :=
  let C := lateContext right3
  if lowerHistoryWordParity C w false = lowerHistoryWordParity C w true then
    lateEqualCases C w upper
  else (lateNormals w).flatMap fun (wide,norm) =>
    let vs := if upper = !(lowerHistoryWordParity C w wide) then
      lateEqualCases C (lowerHistorySet w wide (lowerHistoryPick w wide ++ [1])) upper
    else [((lowerHistoryEndVal C w upper false (lowerHistoryNatural C w upper false),
            lowerHistoryEndVal C w upper true (lowerHistoryNatural C w upper true)),[])]
    vs.map fun (v,cs) => (v,norm::cs)
def lateGreater (x y : CertField × CertField) (strict : Bool) : LowerHistoryComparison :=
  match lowerHistoryGreater (lateContext false) x y with
  | .automatic => if strict && decide (x = y) then .impossible else .automatic
  | .impossible => .impossible
  | .bound b => .bound {b with strict := strict}

structure LateEndpoint where
  right3 : Bool
  words : LowerPair
  upper : Bool
  value : CertField × CertField
  modes : List (List ℕ)
structure LateCheck where
  a : ℕ
  b : ℕ
  strict : Bool
structure LateNormalization where
  label : LowerLabel
  wide : Bool
  bound : ℕ
structure LatePath where
  right3 : Bool
  route : List LowerLabel
  required : List ℕ
  incoming : List ℕ
  checks : List LateCheck
  normalizations : List LateNormalization
  implications : List (ℕ × Option ℕ)
structure LateWitnessRow where
  lower : ℕ
  upper : ℕ
  rectangle : ℕ
  lowerBounds : Fin 3 → Fin 3 → ℚ
inductive LateProofNode where
  | pair (witness : ℕ)
  | split (secondAxis : Bool) (left right : ℕ)
inductive LateDecisionTree where
  | cut (bound : ℕ) (left right : LateDecisionTree)
  | split (secondAxis : Bool) (left right : LateDecisionTree)
  | empty (proof : ℕ)
  | path (path : ℕ)
structure LateCatalog where
  bounds : Array CertBound
  rectangles : Array CertRectangle
  witnesses : Array LateWitnessRow
  proofs : Array LateProofNode
  endpoints : Array LateEndpoint
  paths : Array LatePath

def lateZeroBound : CertBound := ⟨true,true,⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩
def lateBound (C : LateCatalog) (i : ℕ) : CertBound := C.bounds[i-1]?.getD lateZeroBound
def lateBounds (C : LateCatalog) (is : List ℕ) : List CertBound := is.map (lateBound C)
def lateRectangle (C : LateCatalog) (i : ℕ) : CertRectangle := C.rectangles[i-1]?.getD ⟨0,0,0,0⟩
def lateWitnessRow (C : LateCatalog) (i : ℕ) : LateWitnessRow :=
  C.witnesses[i-1]?.getD ⟨0,0,0,fun _ _ => 0⟩
def lateWitness (C : LateCatalog) (i : ℕ) : CertWitness :=
  let w := lateWitnessRow C i
  let l := lateBound C w.lower
  let u := lateBound C w.upper
  let R := lateRectangle C w.rectangle
  ⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R,w.lowerBounds⟩
def lateEndpoint (C : LateCatalog) (i : ℕ) : LateEndpoint :=
  C.endpoints[i-1]?.getD ⟨false,([],[]),false,(⟨0,0,0,0⟩,⟨0,0,0,0⟩),[]⟩
def latePath (C : LateCatalog) (i : ℕ) : LatePath :=
  C.paths[i-1]?.getD ⟨false,[],[],[],[],[],[]⟩
def lateIndex (i n : ℕ) : Prop := 0 < i ∧ i ≤ n
def lateIndices (C : LateCatalog) (is : List ℕ) : Prop := ∀ i ∈ is, lateIndex i C.bounds.size
def lateSubrect (R : CertRectangle) (secondAxis right : Bool) : CertRectangle :=
  if secondAxis then
    if right then {R with s0 := (R.s0+R.s1)/2} else {R with s1 := (R.s0+R.s1)/2}
  else if right then {R with r0 := (R.r0+R.r1)/2} else {R with r1 := (R.r0+R.r1)/2}
def lateHolds (bs : List CertBound) (r s q : ℝ) : Prop := ∀ b ∈ bs, certBoundHolds b r s q
def lateProofValid (C : LateCatalog) : ℕ → List CertBound → CertRectangle → ℕ → Prop
  | 0,_,_,_ => False
  | fuel+1,bs,R,id => lateIndex id C.proofs.size ∧
      match C.proofs[id-1]?.getD (.pair 0) with
      | .pair w => lateIndex w C.witnesses.size ∧
          (lateWitness C w).lowerBound ∈ bs ∧ (lateWitness C w).upperBound ∈ bs ∧
          (lateWitness C w).rectangle = R
      | .split axis l r =>
          lateProofValid C fuel bs (lateSubrect R axis false) l ∧
          lateProofValid C fuel bs (lateSubrect R axis true) r
def lateEndpointValid (C : LateCatalog) (e : LateEndpoint) : Prop :=
  e.modes ≠ [] ∧ 0 ≤ certFieldLower e.value.1 ∧ 0 ≤ certFieldLower e.value.2 ∧
  ∀ ids ∈ e.modes, lateIndices C ids ∧
    ∃ cs, (e.value,cs) ∈ lateEndpointCases e.right3 e.words e.upper ∧
      cs.toFinset = (lateBounds C ids).toFinset

-- Each expected check carries actual outward words and endpoint direction.
abbrev LateSpec := LowerPair × Bool × LowerPair × Bool × Bool
def lateWords (l : LowerLabel) : LowerPair := (l.1.reverse,l.2)
def lateForkWords (n : LateNormalization) (d : ℕ+) : LowerPair :=
  let w := lateWords n.label
  lowerHistorySet w n.wide (lowerHistoryPick w n.wide ++ [d])
def lateExpectedSpecs (p : LatePath) : List LateSpec :=
  p.route.map (fun l => (lateWords l,true,lateWords l,false,false)) ++
  p.normalizations.flatMap (fun n =>
    [(lateForkWords n 1,true,lateForkWords n 2,false,true),
     (lateForkWords n 2,true,lateForkWords n 1,false,true)]) ++
  (p.route.zip p.route.tail).flatMap (fun (l,m) =>
    [(lateWords l,true,lateWords m,false,false),(lateWords m,true,lateWords l,false,false)])
def lateCheckSpec (C : LateCatalog) (c : LateCheck) : LateSpec :=
  let a := lateEndpoint C c.a
  let b := lateEndpoint C c.b
  (a.words,a.upper,b.words,b.upper,c.strict)
def lateCheckValid (C : LateCatalog) (p : LatePath) (c : LateCheck) : Prop :=
  lateIndex c.a C.endpoints.size ∧ lateIndex c.b C.endpoints.size ∧
  (lateEndpoint C c.a).right3 = p.right3 ∧ (lateEndpoint C c.b).right3 = p.right3 ∧
  (∃ ids ∈ (lateEndpoint C c.a).modes, ∀ i ∈ ids, i ∈ p.required) ∧
  (∃ ids ∈ (lateEndpoint C c.b).modes, ∀ i ∈ ids, i ∈ p.required) ∧
  match lateGreater (lateEndpoint C c.a).value (lateEndpoint C c.b).value c.strict with
  | .automatic => True
  | .impossible => False
  | .bound b => b ∈ lateBounds C p.required
def latePathValid (C : LateCatalog) (p : LatePath) : Prop :=
  2 ≤ p.route.length ∧ p.route.length ≤ lowerLateCandidates.length ∧ p.route.Nodup ∧
  p.route.head? = some ([2],[2]) ∧ p.route.getLast? = some ([2],[1]) ∧
  (∀ l ∈ p.route, l ∈ lowerLateCandidates) ∧
  lateIndices C p.required ∧ lateIndices C p.incoming ∧
  p.normalizations.map LateNormalization.label = p.route.tail.dropLast ∧
  (∀ n ∈ p.normalizations, n.bound ∈ p.required ∧
    (n.wide,lateBound C n.bound) ∈ lateNormals (lateWords n.label)) ∧
  p.checks.map (lateCheckSpec C) = lateExpectedSpecs p ∧
  (∀ c ∈ p.checks, lateCheckValid C p c) ∧
  (p.implications.map Prod.fst).toFinset = p.required.toFinset
def lateImplicationsValid (C : LateCatalog) (p : LatePath) (bs : List CertBound) (R : CertRectangle) : Prop :=
  (p.implications.map Prod.fst).toFinset = p.required.toFinset ∧
  ∀ imp ∈ p.implications,
    match imp.2 with
    | none => lateBound C imp.1 ∈ bs
    | some id => lateProofValid C 1500 (lowerHistoryComplement (lateBound C imp.1)::bs) R id
def lateDecisionValid (C : LateCatalog) (right3 : Bool) : List CertBound → CertRectangle → LateDecisionTree → Prop
  | bs,R,.cut id l r => lateIndex id C.bounds.size ∧
      lateDecisionValid C right3 (lateBound C id::bs) R l ∧
      lateDecisionValid C right3 (lowerHistoryComplement (lateBound C id)::bs) R r
  | bs,R,.split axis l r =>
      lateDecisionValid C right3 bs (lateSubrect R axis false) l ∧
      lateDecisionValid C right3 bs (lateSubrect R axis true) r
  | bs,R,.empty id => lateProofValid C 1500 bs R id
  | bs,R,.path id => lateIndex id C.paths.size ∧ (latePath C id).right3 = right3 ∧
      (lateBounds C (latePath C id).incoming).toFinset = bs.toFinset ∧
      lateImplicationsValid C (latePath C id) bs R
def lateAllWitnesses (C : LateCatalog) : Prop :=
  ∀ i, lateIndex i C.witnesses.size → certWitnessValid (lateWitness C i)
def lateAllEndpoints (C : LateCatalog) : Prop :=
  ∀ i, lateIndex i C.endpoints.size → lateEndpointValid C (lateEndpoint C i)
def lateAllPaths (C : LateCatalog) : Prop :=
  ∀ i, lateIndex i C.paths.size → latePathValid C (latePath C i)
def lateDecisionSound (C : LateCatalog) (right3 : Bool) (bs : List CertBound) (R : CertRectangle) : Prop :=
  ∀ r s q : ℝ, certRectangleMem R r s → lateHolds bs r s q →
    ∃ i, lateIndex i C.paths.size ∧ (latePath C i).right3 = right3 ∧
      lateHolds (lateBounds C (latePath C i).required) r s q

end Freiman


