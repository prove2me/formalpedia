-- Prove2me | Definitions.Def_IntegerMatrixMortality_FixedImage_ConcreteModules
-- name    : IntegerMatrixMortality_FixedImage_ConcreteModules
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:31:39.253736+00:00
-- url     : https://prove2.me/theorems/14fbe11e-2ae7-434a-a230-1d27ef4a27e2
-- title:
--   The explicit increment, test, division, contraction and padding tables
-- statement:
--   Define the actual finite edge lists in the source tables for Inc, Test(d,A), Div₂, Div₃, the five-scan comparison, one- and two-block removal, and recovery with m scans. The final division maps combine auxiliary factors within the last generator. The contractions join two-block removal to recovery with m=2, and one-block removal to recovery with m=3. All nonboundary labels are fresh, and the recovery join has precisely its recovery edges.
--
--   $$\#\mathrm{Inc}=4,\quad\#\mathrm{Div}_2=10,\quad\#\mathrm{Div}_3=14,\quad\#\mathrm{Con}_2=30,\quad\#\mathrm{Con}_3=32.$$
--
--   These are listed-generator counts, stated as subsequent theorems. Allocate a private copy to every instruction of the concrete reversed program. Let N be a finite upper bound on its phase labels. Form the set of the resulting matrices and add the deficit to 5798 from B_d=C_dD₀C_d⁻¹ at previously unused indices N,…,N+5797. The choice of p is made only after reserving these indices. The definition alone does not assume that padding is harmless or that the desired count is attained.
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), (C.1) and (C.2), PDF pp. 20–21 / printed pp. 18–19; (C.10) and (C.11), PDF p. 24 / printed p. 22; (D.2)–(D.4), PDF p. 26 / printed p. 24; (D.8), PDF p. 29 / printed p. 27; (E.1), PDF pp. 31–32 / printed pp. 29–30

import Mathlib
import Definitions.Def_IntegerMatrixMortality_FixedImage_ModuleGraphs
import Definitions.Def_IntegerMatrixMortality_FixedImage_FixedProgram

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage


/-- Convenient source-table constructor; zero pre-parameter is the identity. -/
def GE (q r : ℕ) (e : ℤ) (pre : ℕ → ℤ := fun _ => 0)
    (neg : Bool := false) (post : ℕ → ℤ := fun _ => 0) : GeneratorEdge :=
  ⟨q,r,e,pre,neg,post⟩

/-- Local labels 0,1 are the boundaries; labels ≥2 are private. -/
def incrementModule : InstructionModule := ⟨0,1,[
  GE 0 2 0 (fun p => 1-(p : ℤ)), GE 0 1 1 (fun p => 1-(p : ℤ)),
  GE 2 2 0, GE 2 1 1]⟩

def testModule (d : ℕ) (A : Finset ℕ) : InstructionModule := ⟨0,1,
  [GE 0 (2 + 1 % d) 0] ++
  (List.range d).map (fun j => GE (2+j) (2+(j+1)%d) 0) ++
  (A.sort (· ≤ ·)).map (fun j => GE (2+j) 1 1) ++
  (if 0 ∈ A then [GE 0 1 1] else [])⟩

/-- Guessed positive prefix followed by k marker-one scans and a marker-two scan.
    Labels: 0 entry, 1 output, 2 guessing, 3..k+2 marker-one states, k+3 marker-two. -/
def comparisonModule (k : ℕ) (postNeg : Bool) (postH : ℕ → ℤ) : InstructionModule := ⟨0,1,
  [GE 0 2 0, GE 0 3 0 (fun _ => 0) false (fun _ => -1),
   GE 2 2 0, GE 2 3 0 (fun _ => 0) false (fun _ => -1)] ++
  (List.range k).flatMap (fun i => [GE (3+i) (3+i) 0,
    GE (3+i) (if i+1 < k then 4+i else k+3) 1 (fun _ => 0) false
      (fun _ => if i+1 < k then 0 else 1)]) ++
  [GE (k+3) (k+3) 0, GE (k+3) 1 2 (fun _ => 0) postNeg postH]⟩

/-- Pure comparison with the final negation, Lemma C.3. -/
def pureComparison (k : ℕ) := comparisonModule k true (fun _ => 0)

/-- Division by two combines T² Neg with the last digit deletion. -/
def div2Module := comparisonModule 2 true (fun _ => 2)

/-- Rename both boundaries and every private state of a local graph. -/
def renameModule (M : InstructionModule) (f : ℕ → ℕ) : InstructionModule :=
  ⟨f M.entry, f M.exit, M.edges.map (fun e => {e with source := f e.source, target := f e.target})⟩

/-- Division by three: label 1 is a private join; label 8 is the final boundary. -/
def div3Module : InstructionModule := ⟨0,8,
  (comparisonModule 3 true (fun _ => 1)).edges ++
    [GE 1 1 0, GE 1 8 1 (fun _ => 0) false (fun _ => -1)]⟩

def contractionComparison := comparisonModule 5 true (fun _ => 1)

/-- One or two blocks are removed; 1 and 10 are private joins, 11 the output. -/
def blockRemoval (two : Bool) : InstructionModule := ⟨0,11,
  contractionComparison.edges ++
  (if two then [GE 1 1 0, GE 1 10 1, GE 10 10 0,
    GE 10 11 1 (fun _ => 0) false (fun _ => 1)]
   else [GE 1 1 0, GE 1 11 1 (fun _ => 0) false (fun _ => 1)])⟩

/-- Recovery table (D.8). 0 entry, 1 exit, 2..m guessing, m+1 ell,
    m+2..2m+1 validation states. -/
def recoveryModule (m : ℕ) : InstructionModule := ⟨0,1,
  [GE 0 0 0, GE 0 2 1] ++
  (List.range (m-1)).flatMap (fun i => [GE (2+i) (2+i) 0,
    GE (2+i) (3+i) 0 (fun _ => 0) false (fun _ => 1)]) ++
  [GE (m+1) (m+1) 0, GE (m+1) (m+2) (-1) (fun _ => 0) false (fun _ => -2)] ++
  (List.range m).flatMap (fun i => [GE (m+2+i) (m+2+i) 0,
    GE (m+2+i) (if i+1 < m then m+3+i else 1) 1])⟩

def contractionModule (m : ℕ) : InstructionModule := ⟨0,1,
  (renameModule (blockRemoval (m = 2)) (fun s => if s = 1 then 12 else s)).edges ++
  (renameModule (recoveryModule m) (fun s => if s = 0 then 11 else if s = 1 then 1 else 20+s)).edges⟩

def concreteModule : ArithmeticInstruction → InstructionModule
  | .inc => incrementModule
  | .test d A => testModule d A
  | .div2 => div2Module
  | .div3 => div3Module
  | .con2 => contractionModule 2
  | .con3 => contractionModule 3

def privateSize (M : InstructionModule) : ℕ :=
  1 + (M.edges.flatMap (fun e => [e.source,e.target])).foldl max 0

/-- Allocate after all 278 source labels. No phase or matrix depends on the numerical input. -/
def allocateFixedModules : List InstructionEdge → ℕ → List InstructionModule
  | [], _ => []
  | e :: es, offset =>
    let M := concreteModule e.instruction
    renameModule M (fun s => if s = M.entry then e.source
      else if s = M.exit then e.target else offset+s) ::
      allocateFixedModules es (offset+privateSize M)

def fixedModules := allocateFixedModules fixedInstructionEdges 279

def fixedPhaseBound := 279 + (fixedInstructionEdges.map
  (fun e => privateSize (concreteModule e.instruction))).sum

def originalGenerators (p : ℕ) := allocatedGenerators p fixedModules

def paddingMatrix (p d : ℕ) : ZMat := edgeMatrix p (GE d d 0)

/-- Reserve 5798 phases before p is selected, then add precisely the deficit of distinct matrices. -/
def paddedGenerators (p : ℕ) : Finset ZMat :=
  originalGenerators p ∪ ((Finset.range (5798-(originalGenerators p).card)).image
    (fun j => paddingMatrix p (fixedPhaseBound+j)))


end IntegerMatrixMortality.FixedImage


