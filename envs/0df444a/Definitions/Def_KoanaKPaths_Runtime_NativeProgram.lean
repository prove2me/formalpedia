-- Prove2me | Definitions.Def_KoanaKPaths_Runtime_NativeProgram
-- name    : KoanaKPaths_Runtime_NativeProgram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T07:59:00.497966+00:00
-- url     : https://prove2.me/theorems/95ef2ae7-3e9d-4608-9487-780cd14bbb49
-- title:
--   Native executable graph estimator on binary integer stacks
-- statement:
--   This module defines the executable program for directed-path estimation and its register representations. The program parses a graph and tolerance controls, caches shared random signs, evaluates recursive exterior arrays, sums trials using binary carries, selects an exact median, and writes a rational. A zero-vertex input has a separate zero-output branch. All arithmetic programs act on binary integer stacks.
--
--   $$\operatorname{program}=\operatorname{readGraph};\operatorname{branch}_{n=0}(\operatorname{writeZero},\operatorname{estimateAndWrite}).$$
--
--   The definitions include executable subroutines, reference states, and explicit native cost expressions. Semantic correctness, probabilistic accuracy, and running-time bounds are separate theorem interfaces; this module supplies their common program and data representations.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Definitions/Def_KoanaKPaths_Runtime_NativeProgram.lean; source snapshot SHA-256 447379a36321ddb6b06b6af6da4bdfa4b86bd606f5ea8aa55d4ffb442913cc71.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_MedianOfMeans
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Definitions.Def_KoanaKPaths_TapeSampling
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_finite_stack_compilation
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
import Theorems.Thm_NLogN_compile_correct
import Theorems.Thm_NLogN_smul_runs
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine

variable {S : ℕ}

/-- Move a unary block of markers, stopping at its first non-marker item. -/
def moveMarks (src dst : Fin S) : IStmt S 0 :=
  .loop src (fun c => decide (c=Cls.mark))
    (.seq (.op (.unmark src)) (.op (.mark dst)))









/-- Consume a unary marker block and put two markers per input marker on another stack. -/
def duplicateMoveMarks (src dst : Fin S) : IStmt S 0 :=
  .loop src (fun c => decide (c=Cls.mark))
    (.seq (.op (.unmark src)) (.seq (.op (.mark dst)) (.op (.mark dst))))



def doubleMarks (src tmp : Fin S) : IStmt S 0 :=
  .seq (duplicateMoveMarks src tmp) (moveMarks tmp src)




/-- Consume a marker block and copy it to two other stacks. -/
def copyMoveMarks (src dst tmp : Fin S) : IStmt S 0 :=
  .loop src (fun c => decide (c=Cls.mark))
    (.seq (.op (.unmark src)) (.seq (.op (.mark dst)) (.op (.mark tmp))))



def copyMarks (src dst tmp : Fin S) : IStmt S 0 :=
  .seq (copyMoveMarks src dst tmp) (moveMarks tmp src)



end KoanaKPaths.Machine

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}

/-- Reverse a delimited array of integer items onto another stack. -/
def moveInts (src dst : Fin S) : IStmt S 0 :=
  .loop src (fun c => decide (c = Cls.zero ∨ c = Cls.pos ∨ c = Cls.neg))
    (.op (.mv src dst))

def moveIntsCost (xs : List ℤ) : ℕ :=
  (xs.map (fun z => 2 * moveCost (zsz z) + 49)).sum + 30







/-- Copy an integer array in reverse order while returning the source array intact. -/
def copyReverseInts (src dst tmp : Fin S) : IStmt S 0 :=
  .seq (.loop src (fun c => decide (c = Cls.zero ∨ c = Cls.pos ∨ c = Cls.neg))
    (.seq (.op (.dup src dst)) (.op (.mv src tmp)))) (moveInts tmp src)

def duplicateMoveInts (src dst tmp : Fin S) : IStmt S 0 :=
  .loop src (fun c => decide (c = Cls.zero ∨ c = Cls.pos ∨ c = Cls.neg))
    (.seq (.op (.dup src dst)) (.op (.mv src tmp)))

def duplicateMoveIntsCost (xs : List ℤ) : ℕ :=
  (xs.map (fun z => dupCost (zsz z) + 17 + (2*moveCost (zsz z)+19)+30)).sum+30






/-- Consume two equally long arrays and prepend their pointwise sum in reverse order. -/
def zipAddInts (src dst out : Fin S) : IStmt S 0 :=
  .loop src (fun c => decide (c = Cls.zero ∨ c = Cls.pos ∨ c = Cls.neg))
    (.op (.add src dst out))

def zipAddIntsCost (xs ys : List ℤ) : ℕ :=
  (List.zipWith (fun x y => addIntCost (zsz x+zsz y)+30) xs ys).sum+30




/-- Split an array at a unary count, making two reversed copies of the selected prefix. -/
def duplicateTakeInts (count src dst tmp : Fin S) : IStmt S 0 :=
  .loop count (fun c => decide (c=Cls.mark))
    (.seq (.op (.unmark count)) (.seq (.op (.dup src dst)) (.op (.mv src tmp))))

def duplicateTakeIntsCost (xs : List ℤ) : ℕ :=
  (xs.map (fun z => dupCost (zsz z)+17+(2*moveCost (zsz z)+19)+31)).sum+30




/-- Negate and reverse a delimited array onto another stack. -/
def negMoveInts (src dst : Fin S) : IStmt S 0 :=
  .loop src (fun c => decide (c = Cls.zero ∨ c = Cls.pos ∨ c = Cls.neg))
    (.seq (.op (.neg src)) (.op (.mv src dst)))





end KoanaKPaths.Machine

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}

def growMarks (control count tmp : Fin S) : IStmt S 0 :=
  .loop control (fun c => decide (c=Cls.mark))
    (.seq (.op (.unmark control)) (doubleMarks count tmp))

def growMarksCost : ℕ → ℕ → ℕ
  | m, 0 => 30
  | m, d+1 => 97*m+91+growMarksCost (2*m) d







/-- Build a unary power of two while preserving a unary exponent. -/
def powerMarks (depth count control tmp : Fin S) : IStmt S 0 :=
  .seq (.op (.mark count))
    (.seq (copyMarks depth control tmp) (growMarks control count tmp))






end KoanaKPaths.Machine

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

open NLogN
namespace KoanaKPaths.Machine.Wedge

abbrev NS := 128
abbrev A : Fin NS := 0
abbrev R : Fin NS := 1
abbrev V : Fin NS := 2
abbrev D : Fin NS := 3
abbrev C0 : Fin NS := 4
abbrev H0 : Fin NS := 5
abbrev H1 : Fin NS := 6
abbrev W0 : Fin NS := 7
abbrev U : Fin NS := 8
abbrev VS : Fin NS := 9
abbrev HC : Fin NS := 10
abbrev DC : Fin NS := 11
abbrev Aux : Fin NS := 12
abbrev Z : Fin NS := 13

def seqs (ps : List (IStmt NS 1)) : IStmt NS 1 := ps.foldr .seq .skip

def move (src dst : Fin NS) : IStmt NS 1 := liftClosed (moveInts src dst)

/-- Negate a delimited array, returning it in its original order. -/
def negate (src : Fin NS) : IStmt NS 1 := seqs [
  .op (.mark Z), liftClosed (negMoveInts src Z), move Z src, .op (.unmark Z)]

/-- Base case consumes the unique input coordinate and returns the zero exterior product. -/
def base : IStmt NS 1 := seqs [
  .op (.drop A), .op (.unmark A), .op (.mark R), .op (.const R 0)]

/-- The two recursive calls implement the lower and upper subset blocks. Each saved array
has its own marker, so recursive uses of the same finite registers preserve its tail. -/
def prepare : IStmt NS 1 := seqs [
  .op (.unmark D), .op (.mv V VS),
  .op (.mark C0), .op (.mark H0),
  liftClosed (powerMarks D HC DC Aux),
  liftClosed (duplicateTakeInts HC A C0 H0),
  .op (.mark H1), move A H1, .op (.unmark A),
  .op (.mark A), move H0 A, .op (.unmark H0)]

def between : IStmt NS 1 := seqs [
  .op (.mark W0), move R W0, .op (.unmark R),
  .op (.mark A), move H1 A, .op (.unmark H1)]

def finish : IStmt NS 1 := seqs [
  .op (.mark A), move C0 A, .op (.unmark C0),
  .op (.mv VS V),
  .ite V (fun c => decide (c=Cls.neg)) (negate A) .skip,
  negate R,
  .op (.mark U), liftClosed (zipAddInts A R U),
  .op (.unmark A), .op (.unmark R),
  .op (.mark R), move U R, .op (.unmark U),
  move W0 R, .op (.unmark W0), .op (.mark D)]

def step : IStmt NS 1 :=
  .seq prepare (.seq (.call 0) (.seq between (.seq (.call 0) finish)))

/-- One fixed recursive procedure for right multiplication by a sign vector. -/
def body : IStmt NS 1 := .ite D (fun c => decide (c=Cls.mark)) step base

def prog : Fin 1 → IStmt NS 1 := fun _ => body

end KoanaKPaths.Machine.Wedge

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.SignLookup
abbrev NS := Wedge.NS
abbrev DB : Fin NS := 24
abbrev Out : Fin NS := 25
abbrev Cache : Fin NS := 26
abbrev Count : Fin NS := 27
abbrev Back : Fin NS := 28
abbrev Tmp : Fin NS := 29
attribute [local simp] DB Out Cache Count Back Tmp

/-- Arrays are separated by markers; their entries have ordinary integer encodings. -/
def frames (arrays : List (List ℤ)) : List Item :=
  arrays.flatMap (fun a => a.map Item.int ++ [.mark])

def reverseFrames (arrays : List (List ℤ)) : List Item :=
  frames (arrays.reverse.map List.reverse)

def seqs (ps : List (IStmt NS 0)) : IStmt NS 0 := ps.foldr .seq .skip

/-- Move the selected pre to a temporary stack without examining the remaining arrays. -/
def forward : IStmt NS 0 :=
  .loop Count (fun c => decide (c=Cls.mark)) (seqs [
    .op (.unmark Count), .op (.mark Back), .op (.mark Cache),
    moveInts DB Cache, .op (.unmark DB)])

/-- Restore the pre in its original order. -/
def backward : IStmt NS 0 :=
  .loop Back (fun c => decide (c=Cls.mark)) (seqs [
    .op (.unmark Back), .op (.mark Count), .op (.mark DB),
    moveInts Cache DB, .op (.unmark Cache)])

/-- Return the selected array in reverse order and restore the database and index. -/
def program : IStmt NS 0 :=
  .seq forward (.seq (copyReverseInts DB Out Tmp) backward)

def forwardCost (arrays : List (List ℤ)) : ℕ :=
  (arrays.map (fun a => moveIntsCost a+35)).sum+30

def backwardCost (arrays : List (List ℤ)) : ℕ :=
  (arrays.map (fun a => moveIntsCost a.reverse+35)).sum+30

















def lookupCost (pre : List (List ℤ)) (target : List ℤ) : ℕ :=
  forwardCost pre+duplicateMoveIntsCost target+moveIntsCost target.reverse+backwardCost pre










end KoanaKPaths.Machine.SignLookup

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
namespace KoanaKPaths.ExteriorCoordinates

/-- The same block recursion, with the vector stored in decreasing row order. -/
def wedgeReverse : List ℤ → List ℤ → List ℤ
  | [], _ => [0]
  | z::vs, A =>
    let A0 := A.take (2^vs.length)
    let A1 := A.drop (2^vs.length)
    wedgeReverse vs A0 ++ List.zipWith (fun x y => z*x-y) A0 (wedgeReverse vs A1)







end KoanaKPaths.ExteriorCoordinates

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge











def signedList (z : ℤ) (xs : List ℤ) : List ℤ := if z<0 then xs.map (fun x => -x) else xs





end KoanaKPaths.Machine.Wedge

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open NLogN
namespace KoanaKPaths.Machine.Wedge
attribute [local simp] A R V D C0 H0 H1 W0 U VS HC DC Aux Z

def prepared (s : IState NS) (d : ℕ) (z : ℤ) (vs xs ys : List ℤ)
    (ta td tv : List Item) : IState NS :=
  ((((((s.upd D (List.replicate d .mark ++ td)).upd V (vs.map Item.int ++ tv)).upd VS
    (.int z::s.G VS)).upd C0 (xs.reverse.map Item.int ++ .mark::s.G C0)).upd H1
    (ys.reverse.map Item.int ++ .mark::s.G H1)).upd A (xs.map Item.int ++ .mark::ta))

def prepareCost (d : ℕ) (z : ℤ) (xs ys : List ℤ) : ℕ :=
  [1, 2*moveCost (zsz z)+19, 1, 1,
    1+(65*d+60)+growMarksCost 1 d, duplicateTakeIntsCost xs,
    1, moveIntsCost ys, 1, 1, moveIntsCost xs.reverse, 1].sum+1



end KoanaKPaths.Machine.Wedge

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge
attribute [local simp] A R V D C0 H0 H1 W0 U VS HC DC Aux Z

def betweenState (s : IState NS) (lower next : List ℤ) (ta tr th : List Item) : IState NS :=
  (((s.upd W0 (lower.reverse.map Item.int ++ .mark::s.G W0)).upd R tr).upd A
    (next.map Item.int ++ .mark::ta)).upd H1 th



end KoanaKPaths.Machine.Wedge

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open NLogN
namespace KoanaKPaths.Machine.Wedge
attribute [local simp] A R V D C0 H0 H1 W0 U VS HC DC Aux Z

def finished (s : IState NS) (z : ℤ) (xs lower upper : List ℤ)
    (tr tc tw tvs : List Item) : IState NS :=
  (((((s.upd R ((lower++List.zipWith (fun x y => z*x-y) xs upper).map Item.int ++ .mark::tr)).upd
    C0 tc).upd W0 tw).upd VS tvs).upd V (.int z::s.G V)).upd D (.mark::s.G D)

def finishCost (z : ℤ) (xs lower upper : List ℤ) : ℕ :=
  let signed := signedList z xs
  let negUpper := upper.map (fun x => -x)
  let block := List.zipWith (·+·) signed negUpper
  [1, moveIntsCost (xs.reverse), 1, 2*moveCost (zsz z)+19, (if z<0 then 2*moveIntsCost xs+20*xs.length+3 else 1)+25, 2*moveIntsCost upper+20*upper.length+3, 1, zipAddIntsCost signed negUpper, 1, 1, 1, moveIntsCost (block.reverse), 1, moveIntsCost (lower.reverse), 1, 1].sum+1



end KoanaKPaths.Machine.Wedge

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open NLogN
namespace KoanaKPaths.Machine.Wedge
open KoanaKPaths.ExteriorCoordinates
attribute [local simp] A R V D C0 H0 H1 W0 U VS HC DC Aux Z

/-- Exact charged cost of the recursive exterior procedure. -/
def wedgeCost : List ℤ → List ℤ → ℕ
  | [], xs => 2*zsz (xs.headD 0)+34
  | z::vs, xs =>
    let x0 := xs.take (2^vs.length)
    let x1 := xs.drop (2^vs.length)
    let lower := wedgeReverse vs x0
    let upper := wedgeReverse vs x1
    prepareCost vs.length z x0 x1 + wedgeCost vs x0 +
      (moveIntsCost lower+moveIntsCost x1.reverse+5) + wedgeCost vs x1 +
      finishCost z x0 lower upper+27



end KoanaKPaths.Machine.Wedge

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S P : ℕ}

def readCountedMarks (cnt dst : Fin S) : Stmt S P :=
  .loop cnt (fun o => decide (o=some hdMark)) (.seq (.pop cnt) (.inRd dst))




def signWord (b : Bool) : List Sym := [if b then hdPos else hdNeg,1]



def pushSigns (src dst : Fin S) : Stmt S P :=
  .loop src isBitT (.ite src (fun o => decide (o=some 1))
    (.seq (.pop src) (.seq (.push dst 1) (.push dst hdPos)))
    (.seq (.pop src) (.seq (.push dst 1) (.push dst hdNeg))))













def bulkSigns (counter coins : Fin S) : Stmt (S+4) P :=
  .seq (readCountedMarks (ι counter) (NLogN.sq S)) (pushSigns (NLogN.sq S) (ι coins))



end KoanaKPaths.Machine

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S P : ℕ}

/-- Read one self-delimiting natural number into a native integer-item stack. -/
def parseItem (dst : Fin S) : Stmt (S+4) P :=
  parseNat (NLogN.sq S) (NLogN.s1 S) (NLogN.s2 S) (ι dst)








end KoanaKPaths.Machine

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
abbrev NS := Wedge.NS
abbrev Coins : Fin NS := 52
abbrev SignDB : Fin NS := SignLookup.DB
abbrev SignTemplate : Fin NS := 44
abbrev SignCounter : Fin NS := 67
abbrev SignTmp : Fin NS := 68
attribute [local simp] Coins SignDB SignLookup.DB SignTemplate SignCounter SignTmp

def signItems (xs : List ℤ) : List Item := xs.reverse.flatMap (fun x => [.int x,.mark])

def loadLoop : IStmt NS 0 :=
  .loop SignCounter (fun c => decide (c=Cls.mark))
    (.seq (.op (.unmark SignCounter)) (.seq (.op (.mark SignDB)) (.op (.mv Coins SignDB))))

def loadCost (xs : List ℤ) : ℕ :=
  (xs.map (fun x => 2*moveCost (zsz x)+51)).sum+30



/-- Materialize one contiguous random block as scalar records for indexed reuse. -/
def loadSigns : IStmt NS 0 :=
  .seq (copyMarks SignTemplate SignCounter SignTmp) loadLoop





end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Square
abbrev NS := Wedge.NS
abbrev Value : Fin NS := 70
abbrev Arg : Fin NS := 71
abbrev X : Fin NS := 72
abbrev Y : Fin NS := 73
abbrev W : Fin NS := 74
abbrev Q : Fin NS := 75
abbrev R : Fin NS := 76
abbrev T : Fin NS := 77
attribute [local simp] Value Arg X Y W Q R T



/-- Square one signed integer, preserving every auxiliary stack. -/
def program : IStmt NS 0 :=
  .seq (.op (.dup Value Arg)) (.seq (.op (.mv Value Arg))
    (.seq (smul Arg X Y W Q R T) (.op (.mv Arg Value))))



end KoanaKPaths.Machine.Square

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Square
attribute [local simp] Arg X Y W Q R T

/-- Multiply two saved integers without consuming either source. -/
def multiplyCopy (i j dst : Fin NS) : IStmt NS 0 :=
  .seq (.op (.dup i Arg)) (.seq (.op (.dup j Arg))
    (.seq (smul Arg X Y W Q R T) (.op (.mv Arg dst))))



end KoanaKPaths.Machine.Square

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Square
abbrev Eval : Fin NS := Value
attribute [local simp] Eval Value Arg X Y W Q R T

def binaryAdd : IStmt NS 0 := .seq (.op (.mv Eval Arg)) (.op (.add Eval Arg Eval))
def binaryMul : IStmt NS 0 :=
  .seq (.op (.mv Eval Arg)) (.seq (.op (.mv Eval Arg))
    (.seq (smul Arg X Y W Q R T) (.op (.mv Arg Eval))))







end KoanaKPaths.Machine.Square

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Arithmetic
open Square
variable {v : ℕ}

inductive Expr (v : ℕ) where
  | constant (n : ℕ)
  | input (i : Fin v)
  | add (x y : Expr v)
  | mul (x y : Expr v)

def Expr.eval (values : Fin v→ℕ) : Expr v→ℕ
  | .constant n => n
  | .input i => values i
  | .add x y => x.eval values+y.eval values
  | .mul x y => x.eval values*y.eval values

def Expr.size : Expr v→ℕ
  | .constant _ => 1
  | .input _ => 1
  | .add x y | .mul x y => x.size+y.size+1

def Expr.width (values : Fin v→ℕ) (e : Expr v) : ℕ :=
  max (zsz (e.eval values : ℤ)) (match e with
    | .constant _ | .input _ => 0
    | .add x y | .mul x y => max (x.width values) (y.width values))

def Expr.compile (reg : Fin v→Fin Square.NS) : Expr v→IStmt Square.NS 0
  | .constant n => .op (.const Eval (n : ℤ))
  | .input i => .op (.dup (reg i) Eval)
  | .add x y => .seq (x.compile reg) (.seq (y.compile reg) binaryAdd)
  | .mul x y => .seq (x.compile reg) (.seq (y.compile reg) binaryMul)





end KoanaKPaths.Machine.Arithmetic

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Square
attribute [local simp] Eval Value Arg

def binarySub : IStmt NS 0 :=
  .seq (.op (.mv Eval Arg)) (.seq (.op (.neg Arg)) (.op (.add Eval Arg Eval)))





end KoanaKPaths.Machine.Square

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Square
attribute [local simp] Eval Value Arg

def predCopy (src dst : Fin NS) : IStmt NS 0 :=
  .seq (.op (.dup src Eval))
    (.seq (.ite Eval (fun c => decide (c=Cls.zero)) .skip
      (.seq (.op (.const Eval (-1))) binaryAdd)) (.op (.mv Eval dst)))



end KoanaKPaths.Machine.Square

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.BitCounter
abbrev NS := Wedge.NS
abbrev Source : Fin NS := 36
abbrev Ruler : Fin NS := 37
abbrev Rem : Fin NS := 38
abbrev Bits : Fin NS := 39
abbrev Count : Fin NS := 40
abbrev Tmp : Fin NS := 41
attribute [local simp] Source Ruler Rem Bits Count Tmp

def bitInt (b : Bool) : ℤ := if b then 1 else 0

def bitValue : ℕ → List Bool → ℕ
  | m, [] => m
  | m, b::bs => bitValue (2*m+b.toNat) bs

def buildLoop : IStmt NS 0 :=
  .loop Bits (fun c => decide (c=Cls.zero ∨ c=Cls.pos))
    (.seq (doubleMarks Count Tmp) (.seq
      (.ite Bits (fun c => decide (c=Cls.pos)) (.op (.mark Count)) .skip)
      (.op (.drop Bits))))

def buildCost : ℕ → List Bool → ℕ
  | _, [] => 30
  | m, b::bs => 97*m+118+2*b.toNat+buildCost (2*m+b.toNat) bs















def extractLoop : IStmt NS 0 :=
  .loop Source (fun c => decide (c=Cls.pos))
    (.seq (.op (.split Source Ruler Rem)) (.op (.mv Rem Bits)))




/-- Convert a nonnegative binary integer item into a unary marker block. -/
def toMarks : IStmt NS 0 :=
  .seq (.op (.mark Bits)) (.seq (.op (.const Ruler 2)) (.seq extractLoop
    (.seq (.op (.drop Source)) (.seq buildLoop (.seq (.op (.unmark Bits)) (.op (.drop Ruler)))))))



end KoanaKPaths.Machine.BitCounter

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic Square
abbrev Total : Fin NS := 63
abbrev Base : Fin NS := 69
attribute [local simp] Total Base Square.Eval Square.Value BitCounter.Source
variable {v : ℕ}

def signAddress (reg : Fin v→Fin NS) (e : Expr v) : IStmt NS 0 :=
  .seq (predCopy Total Base) (.seq (.op (.mv Base Eval))
    (.seq (e.compile reg) (.seq binarySub (.op (.mv Eval BitCounter.Source)))))



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}

def clearMarks (src : Fin S) : IStmt S 0 :=
  .loop src (fun c => decide (c=Cls.mark)) (.op (.unmark src))



def clearInts (src : Fin S) : IStmt S 0 :=
  .loop src (fun c => decide (c=Cls.zero ∨ c=Cls.pos ∨ c=Cls.neg)) (.op (.drop src))

def clearIntsCost (xs : List ℤ) : ℕ := (xs.map (fun x => 2*zsz x+32)).sum+30



def clearItems (src : Fin S) : IStmt S 0 :=
  .loop src (fun c => decide (c≠Cls.none))
    (.ite src (fun c => decide (c=Cls.mark)) (.op (.unmark src)) (.op (.drop src)))

def itemClearCost : Item→ℕ
  | .mark => 56
  | .int x => 2*zsz x+57

def clearItemsCost (xs : List Item) : ℕ := (xs.map itemClearCost).sum+30



end KoanaKPaths.Machine

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.ArrayLookup
abbrev NS := Wedge.NS
abbrev DB : Fin NS := 14
abbrev Out : Fin NS := 15
abbrev Cache : Fin NS := 16
abbrev Count : Fin NS := 17
abbrev Back : Fin NS := 18
abbrev Tmp : Fin NS := 19
attribute [local simp] DB Out Cache Count Back Tmp

/-- Arrays are separated by markers; their entries have ordinary integer encodings. -/
def frames (arrays : List (List ℤ)) : List Item :=
  arrays.flatMap (fun a => a.map Item.int ++ [.mark])

def reverseFrames (arrays : List (List ℤ)) : List Item :=
  frames (arrays.reverse.map List.reverse)

def seqs (ps : List (IStmt NS 0)) : IStmt NS 0 := ps.foldr .seq .skip

/-- Move the selected pre to a temporary stack without examining the remaining arrays. -/
def forward : IStmt NS 0 :=
  .loop Count (fun c => decide (c=Cls.mark)) (seqs [
    .op (.unmark Count), .op (.mark Back), .op (.mark Cache),
    moveInts DB Cache, .op (.unmark DB)])

/-- Restore the pre in its original order. -/
def backward : IStmt NS 0 :=
  .loop Back (fun c => decide (c=Cls.mark)) (seqs [
    .op (.unmark Back), .op (.mark Count), .op (.mark DB),
    moveInts Cache DB, .op (.unmark Cache)])

/-- Return the selected array in reverse order and restore the database and index. -/
def program : IStmt NS 0 :=
  .seq forward (.seq (copyReverseInts DB Out Tmp) backward)

def forwardCost (arrays : List (List ℤ)) : ℕ :=
  (arrays.map (fun a => moveIntsCost a+35)).sum+30

def backwardCost (arrays : List (List ℤ)) : ℕ :=
  (arrays.map (fun a => moveIntsCost a.reverse+35)).sum+30

















def lookupCost (pre : List (List ℤ)) (target : List ℤ) : ℕ :=
  forwardCost pre+duplicateMoveIntsCost target+moveIntsCost target.reverse+backwardCost pre










end KoanaKPaths.Machine.ArrayLookup

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
attribute [local simp] SignDB SignLookup.DB SignLookup.Out SignLookup.Count SignLookup.Back SignLookup.Tmp
  BitCounter.Source BitCounter.Count BitCounter.Tmp



/-- Query a cached sign, charging the unary address construction and restoring that address bank. -/
def querySign : IStmt NS 0 :=
  .seq BitCounter.toMarks (.seq (moveMarks BitCounter.Count SignLookup.Count)
    (.seq SignLookup.program (clearMarks SignLookup.Count)))







end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic Square
attribute [local simp] SignDB SignLookup.DB SignLookup.Out SignLookup.Count SignLookup.Back SignLookup.Tmp
  BitCounter.Source BitCounter.Count BitCounter.Tmp Total
variable {v : ℕ}

def readSign (reg : Fin v→Fin NS) (e : Expr v) : IStmt NS 0 := .seq (signAddress reg e) querySign



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Square
attribute [local simp] Eval Value

def increment (i : Fin NS) : IStmt NS 0 :=
  .seq (.op (.dup i Eval)) (.seq (.op (.const Eval 1))
    (.seq binaryAdd (.seq (.op (.drop i)) (.op (.mv Eval i)))))



end KoanaKPaths.Machine.Square

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic Square
abbrev Vertex : Fin NS := 81
abbrev Row : Fin NS := 82
abbrev LabelCounter : Fin NS := 88
abbrev LabelTmp : Fin NS := 89
attribute [local simp] Vertex Row Wedge.V SignLookup.Out

def labelRegs : Fin 3→Fin NS := ![54,81,82]
def labelValues (k v r : ℕ) : Fin 3→ℕ := ![k,v,r]
def labelExpr : Expr 3 := .add (.mul (.input 1) (.input 0)) (.input 2)
def labelBody : IStmt NS 0 :=
  .seq (readSign labelRegs labelExpr) (.seq (.op (.mv SignLookup.Out Wedge.V)) (increment Row))






end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
attribute [local simp] Vertex Row LabelCounter LabelTmp Wedge.V SignDB SignLookup.DB SignLookup.Count
  SignLookup.Back SignLookup.Tmp BitCounter.Count BitCounter.Tmp Total

def labelBlock (xs : List ℤ) (k v : ℕ) : ℕ→ℕ→List ℤ
  | _,0 => []
  | r,m+1 => xs.getD (v*k+r) 1::labelBlock xs k v (r+1) m

def labelLoop : IStmt NS 0 :=
  .loop LabelCounter (fun c => decide (c=Cls.mark)) (.seq (.op (.unmark LabelCounter)) labelBody)

def labelIterationCost (xs : List ℤ) (w : ℕ) : ℕ :=
  500000*(w+1)^2+10000*(xs.length+1)+31



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
attribute [local simp] Vertex Row LabelCounter LabelTmp Wedge.V Wedge.D SignDB SignLookup.DB SignLookup.Count
  SignLookup.Back SignLookup.Tmp BitCounter.Count BitCounter.Tmp Total

def loadVector : IStmt NS 0 :=
  .seq (.op (.mark Wedge.V)) (.seq (.op (.const Row 0))
    (.seq (copyMarks Wedge.D LabelCounter LabelTmp) (.seq labelLoop (.op (.drop Row)))))



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}

/-- Consume a unary count and prepend that many copies of an integer. -/
def repeatInts (count dst : Fin S) (z : ℤ) : IStmt S 0 :=
  .loop count (fun c => decide (c=Cls.mark))
    (.seq (.op (.unmark count)) (.op (.const dst z)))



end KoanaKPaths.Machine

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge
attribute [local simp] A D HC DC Aux

/-- Initialize the full coordinate array of the exterior unit without expanding any words. -/
def initializeUnit : IStmt NS 0 :=
  .seq (.op (.mark A)) (.seq (powerMarks D HC DC Aux) (.seq (.op (.unmark HC))
    (.seq (repeatInts HC A 0) (.op (.const A 1)))))





end KoanaKPaths.Machine.Wedge

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
open Wedge

def scaleBySign (sign src : Fin Wedge.NS) : IStmt Wedge.NS 1 :=
  .seq (.ite sign (fun c => decide (c=Cls.neg)) (negate src) .skip) (.op (.drop sign))





end KoanaKPaths.Machine

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}



/-- Transfer one marked array in forward coordinate order. -/
def transferArray (src dst tmp : Fin S) : IStmt S 0 :=
  .seq (.op (.mark tmp)) (.seq (moveInts src tmp) (.seq (.op (.unmark src))
    (.seq (.op (.mark dst)) (.seq (moveInts tmp dst) (.op (.unmark tmp))))))



end KoanaKPaths.Machine

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.GraphArray
open KoanaKPaths.ExteriorCoordinates
abbrev NS := Wedge.NS
abbrev Current : Fin NS := 22
abbrev Tmp : Fin NS := 23
abbrev Sign : Fin NS := 25
attribute [local simp] Current Tmp Sign Wedge.A Wedge.R Wedge.D Wedge.V Wedge.HC Wedge.DC Wedge.Aux

def unitArray (d : ℕ) : List ℤ := 1::List.replicate (2^d-1) 0

def firstArray : IStmt NS 1 :=
  .seq (liftClosed Wedge.initializeUnit) (.seq (.call 0)
    (.seq (scaleBySign Sign Wedge.R) (liftClosed (transferArray Wedge.R Current Tmp))))







end KoanaKPaths.Machine.GraphArray

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic Square
open KoanaKPaths.ExteriorCoordinates
abbrev StateIndex : Fin NS := 83
attribute [local simp] Vertex StateIndex GraphArray.Sign GraphArray.Current Total SignDB SignLookup.DB
  SignLookup.Count SignLookup.Back SignLookup.Tmp BitCounter.Count BitCounter.Tmp
  Wedge.D Wedge.V Wedge.HC Wedge.DC Wedge.Aux

def firstRegs : Fin 4→Fin NS := ![53,54,81,83]
def firstValues (n k v a : ℕ) : Fin 4→ℕ := ![n,k,v,a]
def firstExpr : Expr 4 := .add (.mul (.input 0) (.input 1))
  (.add (.mul (.input 3) (.input 0)) (.input 2))
def firstCell : IStmt NS 1 :=
  .seq (liftClosed (readSign firstRegs firstExpr))
    (.seq GraphArray.firstArray (liftClosed (increment StateIndex)))






end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

noncomputable section
namespace KoanaKPaths.Main
open ExteriorCoordinates

/-- Sum equal-length arrays by successive sequential additions. -/
def arraySum (k : ℕ) (arrays : List (List ℤ)) : List ℤ :=
  arrays.foldl (List.zipWith (·+·)) (List.replicate (2^k) 0)

def labelList {n k : ℕ} (σ : Labels n k) (v : Fin n) : List ℤ :=
  (List.finRange k).map (fun r => sgn (σ v r))

/-- Fully sequential version of the vertex/state dynamic program. -/
def denseLayer {n k ℓ : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k ℓ) : ℕ → Fin n → Fin ℓ → List ℤ
  | 0 => fun _ _ => List.replicate (2^k) 0
  | 1 => fun v a => (wedgeList k (1::List.replicate (2^k-1) 0) (labelList σ v)).map
      (fun x => sgn (R.1 a v)*x)
  | i+2 => fun v a => if h : i<k-1 then
      wedgeList k (arraySum k ((List.finRange n).flatMap (fun u =>
        (List.finRange ℓ).map (fun b => (denseLayer arcs σ R (i+1) u b).map
          (fun x => (if (u,v)∈arcs.toFinset then sgn (R.2 ⟨i,h⟩ a (b,v)) else 0)*x)))))
        (labelList σ v)
    else List.replicate (2^k) 0


/-- Sum the terminal-vertex arrays in one sketch state. -/
def denseOutput {n k ℓ : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k ℓ) (a : Fin ℓ) : List ℤ :=
  arraySum k ((List.finRange n).map (fun v => denseLayer arcs σ R k v a))

/-- Unnormalized nonnegative trial numerator, computed from the full-set coordinates. -/
def denseTrial {n k ℓ : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k ℓ) : ℕ :=
  (((List.finRange ℓ).map (fun a => ((denseOutput arcs σ R a).getLast?.getD 0)^2)).sum : ℤ).toNat

end KoanaKPaths.Main

end
end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main

def signsOf {n k : ℕ} (ω : Fin (trialBits n k)→Bool) : List ℤ :=
  List.ofFn (fun j => sgn (ω j))

lemma signsOf_length {n k : ℕ} (ω : Fin (trialBits n k)→Bool) :
    (signsOf ω).length=trialBits n k := by simp [signsOf]











end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Arithmetic
open Square
variable {v : ℕ}
attribute [local simp] Square.Eval Square.Value BitCounter.Source BitCounter.Count BitCounter.Tmp

def storeExpr (reg : Fin v→Fin Square.NS) (e : Expr v) (dst : Fin Square.NS) : IStmt Square.NS 0 :=
  .seq (e.compile reg) (.op (.mv Eval dst))



/-- Evaluate a count in binary, then produce its unary loop template. -/
def countExpr (reg : Fin v→Fin Square.NS) (e : Expr v) (dst : Fin Square.NS) : IStmt Square.NS 0 :=
  .seq (storeExpr reg e BitCounter.Source)
    (.seq BitCounter.toMarks (moveMarks BitCounter.Count dst))



end KoanaKPaths.Machine.Arithmetic

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Arithmetic
variable {v : ℕ}

abbrev CountPlan (v : ℕ) := Expr v × Fin Square.NS

def countPlans (reg : Fin v→Fin Square.NS) : List (CountPlan v)→IStmt Square.NS 0
  | [] => .skip
  | (e,d)::plans => .seq (countExpr reg e d) (countPlans reg plans)

def applyCounts (values : Fin v→ℕ) (s : IState Square.NS) : List (CountPlan v)→IState Square.NS
  | [] => s
  | (e,d)::plans => applyCounts values
      (s.upd d (List.replicate (e.eval values) .mark ++ s.G d)) plans

def countPlansCost (values : Fin v→ℕ) (w : ℕ) : List (CountPlan v)→ℕ
  | [] => 1
  | (e,_)::plans => 11000*(e.size+1)*(w+1)^2+1100*(e.eval values+1)+countPlansCost values w plans





end KoanaKPaths.Machine.Arithmetic

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Controls
abbrev NS := Wedge.NS
abbrev PowerCount : Fin NS := 47
abbrev PowerRuler : Fin NS := 48
abbrev PowerOut : Fin NS := 60
attribute [local simp] PowerCount PowerRuler PowerOut

def powerLoop : IStmt NS 0 :=
  .loop PowerCount (fun c => decide (c=Cls.mark))
    (.seq (.op (.unmark PowerCount)) (.op (.shl PowerOut PowerRuler)))



def powerFour : IStmt NS 0 :=
  .seq (.op (.const PowerRuler 4)) (.seq (.op (.const PowerOut 1))
    (.seq powerLoop (.op (.drop PowerRuler))))





end KoanaKPaths.Machine.Controls

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Arithmetic
variable {v : ℕ}

def Expr.atomWidth (values : Fin v→ℕ) : Expr v→ℕ
  | .constant n => zsz (n : ℤ)
  | .input i => zsz (values i : ℤ)
  | .add x y | .mul x y => max (x.atomWidth values) (y.atomWidth values)



end KoanaKPaths.Machine.Arithmetic

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates







def layerRadius (n k ℓ : ℕ) : ℕ := 1+k*(n*ℓ+1)












end KoanaKPaths.Main

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Norm
abbrev NS := Wedge.NS
abbrev Src : Fin NS := Wedge.R
abbrev Value : Fin NS := Square.Value
abbrev Tmp : Fin NS := 78
attribute [local simp] Src Value Tmp Wedge.R Square.Value

/-- Consume a coordinate array and retain its final, full-set coordinate as a scalar. -/
def takeTop : IStmt NS 0 :=
  .seq (.op (.mark Tmp)) (.seq (moveInts Src Tmp) (.seq (.op (.unmark Src))
    (.seq (.op (.mv Tmp Value)) (.seq (clearInts Tmp) (.op (.unmark Tmp))))))



end KoanaKPaths.Machine.Norm

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
open scoped BigOperators
namespace KoanaKPaths.Main

def outputExponent (n k ℓ : ℕ) : ℕ := n+(n+k+ℓ+3)*k

def trialWidth (n k ℓ : ℕ) : ℕ := ℓ+2*outputExponent n k ℓ+1











end KoanaKPaths.Main

namespace KoanaKPaths.Machine.Norm




end KoanaKPaths.Machine.Norm

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
open scoped BigOperators
namespace KoanaKPaths.Main

def medianWidth (n k a : ℕ) : ℕ := 100*(1+n+k)^2+2*a













end KoanaKPaths.Main

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Controls
open Arithmetic

def inputRegs : Fin 7→Fin NS := ![53,54,55,56,57,60,66]
def inputValues (n k a b m : ℕ) : Fin 7→ℕ := ![n,k,a,b,m,4^a,k-1]

def exprN : Expr 7 := .input 0
def exprK : Expr 7 := .input 1
def exprA : Expr 7 := .input 2
def exprB : Expr 7 := .input 3
def exprArcCount : Expr 7 := .input 4
def exprPower : Expr 7 := .input 5
def exprKMinus : Expr 7 := .input 6
def exprM : Expr 7 := .mul (.mul (.constant 1024) (.mul (.mul exprK exprK) exprK)) exprPower
def exprQ : Expr 7 := .add (.mul (.constant 2) exprB) (.constant 1)
def exprTrial : Expr 7 := .add (.mul exprN exprK)
  (.add (.mul exprK exprN) (.mul exprKMinus (.mul exprK (.mul exprK exprN))))
def exprSample : Expr 7 := .mul (.mul exprQ exprM) exprTrial
def exprNK : Expr 7 := .mul exprN exprK
def exprWidth : Expr 7 := .add
  (.mul (.constant 100) (.mul (.add (.add (.constant 1) exprN) exprK)
    (.add (.add (.constant 1) exprN) exprK))) (.mul (.constant 2) exprA)
def exprThreshold : Expr 7 := .add exprB (.constant 1)

def plans : List (CountPlan 7) :=
  [(exprN,59),(exprK,3),(exprM,42),(exprQ,43),(exprTrial,44),
    (exprNK,45),(exprArcCount,46),(exprWidth,124),(exprSample,51),(exprThreshold,115)]

def program : IStmt NS 0 := countPlans inputRegs plans






















end KoanaKPaths.Machine.Controls

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Controls

def controlWidth (n k a b m : ℕ) : ℕ := 11+n+k+m+2*a+b.size














end KoanaKPaths.Machine.Controls

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic KoanaKPaths.Main

def wordWidth (n k : ℕ) : ℕ := 100*(1+n+k)^2













end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] LabelCounter StateIndex GraphArray.Current Vertex Wedge.D Wedge.V
  Wedge.HC Wedge.DC Wedge.Aux Total SignDB SignLookup.DB SignLookup.Count SignLookup.Back SignLookup.Tmp
  BitCounter.Count BitCounter.Tmp

def firstCellCost (n k : ℕ) : ℕ :=
  10000000*(wordWidth n k+k+2)^2*2^k+10000*(trialBits n k+1)

def firstRow : IStmt NS 1 :=
  .loop LabelCounter (fun c => decide (c=Cls.mark)) (.seq (.op (.unmark LabelCounter)) firstCell)

def firstRowState {k : ℕ} (s : IState NS) (F : Fin k→List ℤ) (i : ℕ) (atail : List Item) : IState NS :=
  ((s.upd LabelCounter (List.replicate (k-i) .mark)).upd StateIndex (.int (i : ℤ)::atail)).upd GraphArray.Current
    (ArrayLookup.frames ((List.ofFn F).take i).reverse ++ s.G GraphArray.Current)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] LabelCounter LabelTmp StateIndex Vertex GraphArray.Current Wedge.V Wedge.D Wedge.HC Wedge.DC Wedge.Aux
  Total SignDB SignLookup.DB SignLookup.Count SignLookup.Back SignLookup.Tmp BitCounter.Count BitCounter.Tmp

def firstVertex : IStmt NS 1 :=
  .seq (liftClosed loadVector) (.seq (.op (.const StateIndex 0))
    (.seq (liftClosed (copyMarks Wedge.D LabelCounter LabelTmp)) (.seq firstRow
      (.seq (.op (.drop StateIndex)) (.seq (liftClosed (clearInts Wedge.V))
        (.seq (.op (.unmark Wedge.V)) (liftClosed (Square.increment Vertex))))))))

def firstVertexCost (n k : ℕ) : ℕ :=
  (500000*(wordWidth n k+1)^2+10000*(trialBits n k+1)+firstCellCost n k+1000)*(k+1)+
    100000*(wordWidth n k+1)^2



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace KoanaKPaths.Main

noncomputable def matrixArrays {n k : ℕ} (F : Fin n→Fin k→List ℤ) : List (List ℤ) :=
  List.ofFn (fun j : Fin (n*k) => F (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)









end KoanaKPaths.Main

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
abbrev VerticesCounter : Fin NS := 87
abbrev VerticesTemplate : Fin NS := 59
attribute [local simp] VerticesCounter VerticesTemplate Vertex GraphArray.Current StateIndex LabelCounter LabelTmp
  Wedge.D Wedge.V Wedge.HC Wedge.DC Wedge.Aux Total SignDB SignLookup.DB SignLookup.Count SignLookup.Back
  SignLookup.Tmp BitCounter.Count BitCounter.Tmp

def firstVertices : IStmt NS 1 :=
  .loop VerticesCounter (fun c => decide (c=Cls.mark)) (.seq (.op (.unmark VerticesCounter)) firstVertex)

def firstVerticesState {n k : ℕ} (s : IState NS) (F : Fin n→Fin k→List ℤ) (i : ℕ) (vt : List Item) : IState NS :=
  ((s.upd VerticesCounter (List.replicate (n-i) .mark)).upd Vertex (.int (i : ℤ)::vt)).upd GraphArray.Current
    (ArrayLookup.frames (((List.ofFn (fun v => List.ofFn (F v))).take i).flatten.reverse) ++ s.G GraphArray.Current)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Matrix
abbrev NS := Wedge.NS
abbrev Prev : Fin NS := ArrayLookup.DB
abbrev Current : Fin NS := 22
abbrev Tmp : Fin NS := 23
abbrev Template : Fin NS := 45
abbrev Counter : Fin NS := 67
abbrev CopyTmp : Fin NS := 68
attribute [local simp] Prev ArrayLookup.DB Current Tmp Template Counter CopyTmp

def transferLoop : IStmt NS 0 :=
  .loop Counter (fun c => decide (c=Cls.mark))
    (.seq (.op (.unmark Counter)) (transferArray Current Prev Tmp))

def transferCost : List (List ℤ)→ℕ
  | [] => 30
  | a::arrays => 2*moveIntsCost a+35+transferCost arrays



/-- Reverse the list of arrays while preserving each array's coordinate order. -/
def transfer : IStmt NS 0 := .seq (copyMarks Template Counter CopyTmp) transferLoop





end KoanaKPaths.Machine.Matrix

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] VerticesCounter VerticesTemplate Vertex LabelCounter LabelTmp GraphArray.Current
  Matrix.Current Matrix.Prev Matrix.Template Matrix.Counter Matrix.CopyTmp
  Wedge.D Wedge.HC Wedge.DC Wedge.Aux Total SignDB SignLookup.DB SignLookup.Count SignLookup.Back
  SignLookup.Tmp BitCounter.Count BitCounter.Tmp ArrayLookup.DB

def firstLayer : IStmt NS 1 :=
  .seq (.op (.const Vertex 0)) (.seq (liftClosed (copyMarks VerticesTemplate VerticesCounter LabelTmp))
    (.seq firstVertices (.seq (.op (.drop Vertex)) (liftClosed Matrix.transfer))))

def firstLayerCost (n k : ℕ) : ℕ := (firstVertexCost n k+31)*n+
  1000*(wordWidth n k+1)*(n+1)+2000*(wordWidth n k+1)*2^k*(n*k+1)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Matrix
attribute [local simp] ArrayLookup.DB ArrayLookup.Out ArrayLookup.Count ArrayLookup.Back ArrayLookup.Tmp
  BitCounter.Source BitCounter.Count BitCounter.Tmp Wedge.A

def queryArray : IStmt NS 0 :=
  .seq BitCounter.toMarks (.seq (moveMarks BitCounter.Count ArrayLookup.Count)
    (.seq (.op (.mark ArrayLookup.Out)) (.seq ArrayLookup.program
      (.seq (.op (.mark Wedge.A)) (.seq (moveInts ArrayLookup.Out Wedge.A)
        (.seq (.op (.unmark ArrayLookup.Out)) (clearMarks ArrayLookup.Count)))))))





end KoanaKPaths.Machine.Matrix

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Matrix
open Arithmetic Square
attribute [local simp] ArrayLookup.DB ArrayLookup.Count ArrayLookup.Back ArrayLookup.Tmp
  BitCounter.Source BitCounter.Count BitCounter.Tmp Wedge.A
variable {v : ℕ}

def readArray (reg : Fin v→Fin NS) (e : Expr v) : IStmt NS 0 :=
  .seq (storeExpr reg e BitCounter.Source) queryArray



end KoanaKPaths.Machine.Matrix

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Accumulate
abbrev NS := Wedge.NS
abbrev Src : Fin NS := Wedge.A
abbrev Acc : Fin NS := 20
abbrev Tmp : Fin NS := 21
attribute [local simp] Src Acc Tmp Wedge.A

/-- Consume an array and add it to a persistent accumulator array. -/
def program : IStmt NS 0 :=
  .seq (.op (.mark Tmp)) (.seq (zipAddInts Src Acc Tmp) (.seq (.op (.unmark Src))
    (.seq (.op (.unmark Acc)) (.seq (.op (.mark Acc)) (.seq (moveInts Tmp Acc) (.op (.unmark Tmp)))))))



end KoanaKPaths.Machine.Accumulate

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.GraphArray
open KoanaKPaths.ExteriorCoordinates
attribute [local simp] Sign Wedge.A Accumulate.Src Accumulate.Acc

/-- Add a retrieved predecessor array with its shared sketch sign. -/
def weightedAdd : IStmt NS 1 :=
  .seq (scaleBySign Sign Wedge.A) (liftClosed Accumulate.program)



end KoanaKPaths.Machine.GraphArray

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic Square
abbrev Predecessor : Fin NS := 80
abbrev LayerIndex : Fin NS := 84
abbrev PreviousState : Fin NS := 85
attribute [local simp] Predecessor LayerIndex PreviousState Vertex StateIndex GraphArray.Sign
  Wedge.A Accumulate.Acc Total SignDB SignLookup.DB SignLookup.Count SignLookup.Back SignLookup.Tmp
  SignLookup.Out ArrayLookup.DB ArrayLookup.Count ArrayLookup.Back ArrayLookup.Tmp BitCounter.Count BitCounter.Tmp

def predRegs : Fin 3→Fin NS := ![54,80,85]
def predValues (k u b : ℕ) : Fin 3→ℕ := ![k,u,b]
def predExpr : Expr 3 := .add (.mul (.input 1) (.input 0)) (.input 2)
def laterRegs : Fin 6→Fin NS := ![53,54,81,83,84,85]
def laterValues (n k v a i b : ℕ) : Fin 6→ℕ := ![n,k,v,a,i,b]
def laterExpr : Expr 6 := .add (.mul (.input 0) (.input 1))
  (.add (.mul (.input 1) (.input 0))
    (.add (.mul (.input 4) (.mul (.input 1) (.mul (.input 1) (.input 0))))
      (.add (.mul (.input 3) (.mul (.input 1) (.input 0)))
        (.add (.mul (.input 5) (.input 0)) (.input 2)))))

def laterIndex (n k v a i b : ℕ) : ℕ := n*k+k*n+i*(k*(k*n))+a*(k*n)+b*n+v

def predecessorCell : IStmt NS 1 :=
  .seq (liftClosed (Matrix.readArray predRegs predExpr))
    (.seq (liftClosed (readSign laterRegs laterExpr))
      (.seq GraphArray.weightedAdd (liftClosed (increment PreviousState))))






def predecessorCellCost (matrixSize signCount k w : ℕ) : ℕ :=
  1000000*(w+1)^2+10000*(w+1)*2^k*(matrixSize+1)+
    10000*(w+2)*(2^k+1)+10000*(signCount+1)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}

/-- Preserve two integers and prepend one marker exactly when the first is at most the second. -/
def compareLE (i j tmp work dst : Fin S) : IStmt S 0 :=
  .seq (.op (.dup i tmp)) (.seq (.op (.dup j work))
    (.seq (.op (.neg work)) (.seq (.op (.add tmp work tmp))
      (.seq (.ite tmp (fun c => decide (c=Cls.pos)) .skip (.op (.mark dst)))
        (.op (.drop tmp))))))

def compareCost (x y : ℤ) : ℕ := dupCost (zsz x)+17+dupCost (zsz y)+17+20+
  addIntCost (zsz x+zsz (-y))+26+(2*zsz (x-y)+2)





end KoanaKPaths.Machine

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}

/-- Preserve two integers and mark exactly when they are equal. -/
def compareEq (i j tmp work dst : Fin S) : IStmt S 0 :=
  .seq (.op (.dup i tmp)) (.seq (.op (.dup j work))
    (.seq (.op (.neg work)) (.seq (.op (.add tmp work tmp))
      (.seq (.ite tmp (fun c => decide (c=Cls.zero)) (.op (.mark dst)) .skip)
        (.op (.drop tmp))))))



end KoanaKPaths.Machine

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median
abbrev NS := Wedge.NS
abbrev Records : Fin NS := 107
abbrev Lo : Fin NS := 108
abbrev Hi : Fin NS := 109
abbrev Mid : Fin NS := 110
abbrev Value : Fin NS := 111
abbrev Tmp : Fin NS := 112
abbrev Work : Fin NS := 113
abbrev Count : Fin NS := 114
abbrev Threshold : Fin NS := 115
abbrev Back : Fin NS := 116
attribute [local simp] Records Lo Hi Mid Value Tmp Work Count Threshold Back

def intClass (c : Cls) : Bool := decide (c=Cls.zero ∨ c=Cls.pos ∨ c=Cls.neg)


/-- Sequentially inspect all group numerators, counting those at most the trial midpoint. -/
def scan : IStmt NS 0 :=
  .loop Records intClass
    (.seq (.op (.mv Records Value))
      (.seq (compareLE Value Mid Tmp Work Count) (.op (.mv Value Back))))

def scanCost (mid : ℤ) : List ℤ→ℕ
  | [] => 30
  | x::xs => 4*moveCost (zsz x)+compareCost x mid+68+scanCost mid xs

def countLE (mid : ℤ) (xs : List ℤ) : ℕ := (xs.filter (fun x => decide (x≤ mid))).length





end KoanaKPaths.Machine.Median

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.ArcMember
abbrev NS := Wedge.NS
abbrev DB : Fin NS := 30
abbrev Back : Fin NS := 67
abbrev U : Fin NS := 68
abbrev V : Fin NS := 69
abbrev QueryU : Fin NS := 80
abbrev QueryV : Fin NS := 81
abbrev Found : Fin NS := 86
abbrev FlagU : Fin NS := 108
abbrev FlagV : Fin NS := 109
abbrev Tmp : Fin NS := 110
abbrev Work : Fin NS := 111
attribute [local simp] DB Back U V QueryU QueryV Found FlagU FlagV Tmp Work

def records (ps : List (ℤ×ℤ)) : List Item :=
  ps.flatMap (fun p => [.int p.2,.int p.1,.mark])

def takeRecord (src : Fin NS) : IStmt NS 0 :=
  .seq (.op (.mv src V)) (.seq (.op (.mv src U)) (.op (.unmark src)))

def pushRecord (dst : Fin NS) : IStmt NS 0 :=
  .seq (.op (.mark dst)) (.seq (.op (.mv U dst)) (.op (.mv V dst)))

def recordCost (u v : ℤ) : ℕ := 2*moveCost (zsz u)+2*moveCost (zsz v)+39





end KoanaKPaths.Machine.ArcMember

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.ArcMember
attribute [local simp] FlagU FlagV Found

def markFound : IStmt NS 0 := .seq (.op (.drop Found)) (.op (.const Found 1))
def flagDecision : IStmt NS 0 :=
  .ite FlagU (fun c => decide (c=Cls.mark))
    (.ite FlagV (fun c => decide (c=Cls.mark)) markFound .skip) .skip

def flags (b : Bool) : List Item := if b then [.mark] else []
def nextFound (u v f : Bool) : Bool := (u && v) || f





def mergeFlags : IStmt NS 0 :=
  .seq flagDecision (.seq (clearMarks FlagU) (clearMarks FlagV))



end KoanaKPaths.Machine.ArcMember

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.ArcMember
attribute [local simp] DB Back U V QueryU QueryV Found FlagU FlagV Tmp Work

def inspectRecord : IStmt NS 0 :=
  .seq (takeRecord DB) (.seq (compareEq U QueryU Tmp Work FlagU)
    (.seq (compareEq V QueryV Tmp Work FlagV) (.seq mergeFlags (pushRecord Back))))





end KoanaKPaths.Machine.ArcMember

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.ArcMember
attribute [local simp] U V

def transferRecords (src dst : Fin NS) : IStmt NS 0 :=
  .loop src Median.intClass (.seq (takeRecord src) (pushRecord dst))

def transferCost : List (ℤ×ℤ)→ℕ
  | [] => 30
  | (u,v)::ps => 2*recordCost u v+30+transferCost ps





end KoanaKPaths.Machine.ArcMember

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.ArcMember
attribute [local simp] DB Back QueryU QueryV Found FlagU FlagV

def arcMatch (qu qv : ℤ) (p : ℤ×ℤ) : Bool := decide (p.1=qu) && decide (p.2=qv)
def scanFound (qu qv : ℤ) (ps : List (ℤ×ℤ)) (f : Bool) : Bool :=
  ps.foldl (fun f p => arcMatch qu qv p || f) f

def scan : IStmt NS 0 := .loop DB Median.intClass inspectRecord

def scanCost (qu qv : ℤ) : List (ℤ×ℤ)→ℕ
  | [] => 30
  | (u,v)::ps => 2*recordCost u v+compareCost u qu+compareCost v qv+230+scanCost qu qv ps









end KoanaKPaths.Machine.ArcMember

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S P : ℕ}

def parseFields : List (Fin S)→Stmt (S+4) P
  | [] => .skip
  | d::ds => .seq (parseItem d) (parseFields ds)

def fieldSymbols (fields : List (Fin S × ℕ)) : List Sym :=
  fields.flatMap (fun p => (HypergraphUnreliability.FPRAS.natCode p.2).map codeBit)

def fieldCost (fields : List (Fin S × ℕ)) : ℕ :=
  (fields.map (fun p => 11*p.2.bits.length+6)).sum+1

def storeFields : IState S→List (Fin S × ℕ)→IState S
  | s, [] => s
  | s, (d,n)::fs => storeFields {s.upd d (.int (n : ℤ)::s.G d) with
      ip := s.ip+(HypergraphUnreliability.FPRAS.natCode n).length} fs








end KoanaKPaths.Machine

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
open NLogN
namespace KoanaKPaths.Machine.Input
abbrev NS := Wedge.NS
abbrev Counter : Fin NS := 58
abbrev DB : Fin NS := 30
attribute [local simp] Counter DB
variable {P : ℕ}

def arcSymbols : List (ℕ×ℕ)→List Sym
  | [] => []
  | (u,v)::arcs => (HypergraphUnreliability.FPRAS.natCode u).map codeBit ++
      (HypergraphUnreliability.FPRAS.natCode v).map codeBit ++ arcSymbols arcs

def arcItems : List (ℕ×ℕ)→List Item
  | [] => []
  | (u,v)::arcs => arcItems arcs ++ [.int (v : ℤ),.int (u : ℤ),.mark]

def arcCost : List (ℕ×ℕ)→ℕ
  | [] => 1
  | (u,v)::arcs => 11*u.bits.length+11*v.bits.length+15+arcCost arcs

/-- Read a unary-counted list of arc endpoints into two-integer array records. -/
def readArcs : Stmt (NS+4) P :=
  .loop (ι Counter) (fun o => decide (o=some hdMark))
    (.seq (.pop (ι Counter)) (.seq (.push (ι DB) hdMark) (.seq (parseItem DB) (parseItem DB))))



end KoanaKPaths.Machine.Input

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
open NLogN
namespace KoanaKPaths.Machine.Input
abbrev VertexField : Fin NS := 53
abbrev PathField : Fin NS := 54
abbrev AccuracyField : Fin NS := 55
abbrev ConfidenceField : Fin NS := 56
abbrev ArcCountField : Fin NS := 57
attribute [local simp] VertexField PathField AccuracyField ConfidenceField ArcCountField Counter
attribute [local simp] BitCounter.Source BitCounter.Count BitCounter.Tmp

def headerFields (n k a b m : ℕ) : List (Fin NS × ℕ) :=
  [(VertexField,n),(PathField,k),(AccuracyField,a),(ConfidenceField,b),(ArcCountField,m)]

def readHeader {P : ℕ} : Stmt (NS+4) P :=
  parseFields [VertexField,PathField,AccuracyField,ConfidenceField,ArcCountField]

def prepareArcCount : IStmt NS 0 :=
  .seq (.op (.dup ArcCountField BitCounter.Source))
    (.seq BitCounter.toMarks (moveMarks BitCounter.Count Counter))





end KoanaKPaths.Machine.Input

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
open NLogN
namespace KoanaKPaths.Machine.Input
attribute [local simp] VertexField PathField AccuracyField ConfidenceField ArcCountField Counter DB
attribute [local simp] BitCounter.Count BitCounter.Tmp
variable {P : ℕ}

def arcValues {n : ℕ} (arcs : List (Fin n × Fin n)) : List (ℕ×ℕ) :=
  arcs.map (fun p => (p.1.val,p.2.val))







def initial : IState NS := ⟨fun _ => [],0,[]⟩

def parsedState (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) : IState NS :=
  let h := storeFields initial (headerFields n k a b arcs.length)
  {h.upd DB (arcItems (arcValues arcs)) with ip := (KoanaKPaths.Main.graphInputControls n arcs k a b).length}

/-- Fixed graph-input front end: five header fields, a binary-to-unary arc count, then arcs. -/
def readGraph : Stmt (NS+4) P :=
  .seq readHeader (.seq (compile (liftClosed prepareArcCount)) readArcs)

def graphReadCost (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) : ℕ :=
  fieldCost (headerFields n k a b arcs.length)+2000*(arcs.length+1)+arcCost (arcValues arcs)



end KoanaKPaths.Machine.Input

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.ArcMember
attribute [local simp] DB Back QueryU QueryV Found FlagU FlagV

/-- Scan the native arc list and restore it, leaving one membership bit. -/
def queryArc : IStmt NS 0 :=
  .seq (.op (.const Found 0)) (.seq scan (transferRecords Back DB))





def ofArcs {n : ℕ} (arcs : List (Fin n × Fin n)) : List (ℤ×ℤ) :=
  arcs.reverse.map (fun p => ((p.1.val : ℤ),(p.2.val : ℤ)))





end KoanaKPaths.Machine.ArcMember

namespace KoanaKPaths.Machine.ArcMember
open NLogN

end KoanaKPaths.Machine.ArcMember

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main

def coreRegisters : List (Fin NS) := [53,54,63,24,14,30,3,59,45,40,41,17,18,19,27,28,29,67,68,108,109,89,10,11,12]
noncomputable def coreStack {n k : ℕ} (ω : Fin (trialBits n k)→Bool)
    (arcs : List (Fin n × Fin n)) (p : ℕ) (j : Fin NS) : List Item :=
  match j.val with
  | 53 => [.int (n : ℤ)]
  | 54 => [.int (k : ℤ)]
  | 63 => [.int (trialBits n k : ℤ)]
  | 24 => signItems (signsOf ω)
  | 14 => ArrayLookup.frames (matrixArrays (denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p))
  | 30 => Input.arcItems (Input.arcValues arcs)
  | 3 => List.replicate k .mark
  | 59 => List.replicate n .mark
  | 45 => List.replicate (n*k) .mark
  | _ => []

def Core {n k : ℕ} (s : IState NS) (ω : Fin (trialBits n k)→Bool)
    (arcs : List (Fin n × Fin n)) (p : ℕ) : Prop :=
  ∀ j∈coreRegisters, s.G j=coreStack ω arcs p j





end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates

def predecessorTerm {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (i : Fin (k-1)) (a : Fin k) (v : Fin n)
    (q : Fin n × Fin k) : Coordinates k :=
  if (q.1,v)∈arcs.toFinset then sgn (R.2 i a (q.2,v)) • graphLayer arcs σ R p q.1 q.2 else 0









end KoanaKPaths.Main

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
open scoped BigOperators
namespace KoanaKPaths.Main
universe u
variable {M : Type u} [AddCommMonoid M] {m : ℕ}

def finPrefix (f : Fin m→M) (i : ℕ) : M :=
  ∑ j∈Finset.univ.filter (fun j : Fin m => j.val< i), f j







end KoanaKPaths.Main

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates

def predSet (n k u b : ℕ) : Finset (Fin n × Fin k) :=
  Finset.univ.filter (fun q => q.1.val< u ∨ q.1.val=u ∧ q.2.val< b)







def predSum {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (i : Fin (k-1)) (a : Fin k) (v : Fin n) (u b : ℕ) : Coordinates k :=
  ∑ q∈predSet n k u b, predecessorTerm arcs σ R p i a v q






end KoanaKPaths.Main

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic Square KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates
abbrev Found : Fin NS := 86
attribute [local simp] Found PreviousState Accumulate.Acc

def predecessorStep : IStmt NS 1 :=
  .ite Found (fun c => decide (c=Cls.pos)) predecessorCell (liftClosed (increment PreviousState))



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates
abbrev PreviousCounter : Fin NS := 92
attribute [local simp] PreviousCounter PreviousState Accumulate.Acc Vertex StateIndex LayerIndex Predecessor Found

def predecessorRow : IStmt NS 1 :=
  .loop PreviousCounter (fun c => decide (c=Cls.mark))
    (.seq (.op (.unmark PreviousCounter)) predecessorStep)

noncomputable def predecessorRowState {n k : ℕ} (s : IState NS) (ω : Fin (trialBits n k)→Bool)
    (arcs : List (Fin n × Fin n)) (p : ℕ) (i : Fin (k-1)) (a : Fin k) (v u : Fin n)
    (b : ℕ) (bt accTail : List Item) : IState NS :=
  ((s.upd PreviousCounter (List.replicate (k-b) .mark)).upd PreviousState (.int (b : ℤ)::bt)).upd Accumulate.Acc
    ((coefficientList (predSum arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p i a v u.val b)).map Item.int ++ .mark::accTail)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates
attribute [local simp] PreviousCounter PreviousState Accumulate.Acc Vertex StateIndex LayerIndex Predecessor Found
  Wedge.D LabelTmp ArcMember.Found ArcMember.DB ArcMember.Back ArcMember.FlagU ArcMember.FlagV

/-- Add the previous-layer contributions from one predecessor vertex. -/
def predecessorVertex : IStmt NS 1 :=
  .seq (liftClosed ArcMember.queryArc) (.seq (.op (.const PreviousState 0))
    (.seq (liftClosed (copyMarks Wedge.D PreviousCounter LabelTmp)) (.seq predecessorRow
      (.seq (.op (.drop PreviousState)) (.seq (.op (.drop Found)) (liftClosed (Square.increment Predecessor)))))))

def predecessorVertexCost (n k m : ℕ) : ℕ :=
  (predecessorCellCost (n*k) (trialBits n k) k (wordWidth n k)+56)*k+
    7000*(n+1)*(m+1)+15000*(wordWidth n k+1)^2+1000*(k+1)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates
abbrev PredecessorCounter : Fin NS := 91
attribute [local simp] PredecessorCounter PreviousCounter Predecessor Accumulate.Acc Vertex StateIndex LayerIndex

def predecessors : IStmt NS 1 :=
  .loop PredecessorCounter (fun c => decide (c=Cls.mark))
    (.seq (.op (.unmark PredecessorCounter)) predecessorVertex)

noncomputable def predecessorsState {n k : ℕ} (s : IState NS) (ω : Fin (trialBits n k)→Bool)
    (arcs : List (Fin n × Fin n)) (p : ℕ) (i : Fin (k-1)) (a : Fin k) (v : Fin n)
    (u : ℕ) (ut accTail : List Item) : IState NS :=
  ((s.upd PredecessorCounter (List.replicate (n-u) .mark)).upd Predecessor (.int (u : ℤ)::ut)).upd Accumulate.Acc
    ((coefficientList (predSum arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p i a v u 0)).map Item.int ++ .mark::accTail)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.GraphArray
open KoanaKPaths.ExteriorCoordinates
attribute [local simp] Current Tmp Accumulate.Acc Wedge.A Wedge.R Wedge.D Wedge.V Wedge.HC Wedge.DC Wedge.Aux

/-- Apply the vertex label vector after summing all signed predecessor arrays. -/
def laterArray : IStmt NS 1 :=
  .seq (liftClosed (transferArray Accumulate.Acc Wedge.A Tmp))
    (.seq (.call 0) (liftClosed (transferArray Wedge.R Current Tmp)))



end KoanaKPaths.Machine.GraphArray

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge
attribute [local simp] D HC DC Aux

def zeroArray (dst : Fin NS) : IStmt NS 0 :=
  .seq (.op (.mark dst)) (.seq (powerMarks D HC DC Aux) (repeatInts HC dst 0))





end KoanaKPaths.Machine.Wedge

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates
attribute [local simp] PredecessorCounter PreviousCounter Predecessor Accumulate.Acc Vertex StateIndex LayerIndex
  VerticesTemplate LabelTmp Wedge.D Wedge.V Wedge.HC Wedge.DC Wedge.Aux GraphArray.Current

def laterCell : IStmt NS 1 :=
  .seq (liftClosed (Wedge.zeroArray Accumulate.Acc)) (.seq (.op (.const Predecessor 0))
    (.seq (liftClosed (copyMarks VerticesTemplate PredecessorCounter LabelTmp)) (.seq predecessors
      (.seq (.op (.drop Predecessor)) (.seq GraphArray.laterArray (liftClosed (Square.increment StateIndex)))))))

def laterCellCost (n k m : ℕ) : ℕ :=
  (predecessorVertexCost n k m+31)*n+
    2000000*(k+2)^2*(wordWidth n k+k+2)*2^k+20000*(wordWidth n k+1)^2+1000*(n+1)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] PredecessorCounter PreviousCounter LayerIndex LabelCounter StateIndex GraphArray.Current Vertex Wedge.D Wedge.V
  Wedge.HC Wedge.DC Wedge.Aux Total SignDB SignLookup.DB SignLookup.Count SignLookup.Back SignLookup.Tmp
  BitCounter.Count BitCounter.Tmp

def laterRow : IStmt NS 1 :=
  .loop LabelCounter (fun c => decide (c=Cls.mark)) (.seq (.op (.unmark LabelCounter)) laterCell)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] PredecessorCounter PreviousCounter LayerIndex LabelCounter LabelTmp StateIndex Vertex GraphArray.Current Wedge.V Wedge.D Wedge.HC Wedge.DC Wedge.Aux
  Total SignDB SignLookup.DB SignLookup.Count SignLookup.Back SignLookup.Tmp BitCounter.Count BitCounter.Tmp

def laterVertex : IStmt NS 1 :=
  .seq (liftClosed loadVector) (.seq (.op (.const StateIndex 0))
    (.seq (liftClosed (copyMarks Wedge.D LabelCounter LabelTmp)) (.seq laterRow
      (.seq (.op (.drop StateIndex)) (.seq (liftClosed (clearInts Wedge.V))
        (.seq (.op (.unmark Wedge.V)) (liftClosed (Square.increment Vertex))))))))

def laterVertexCost (n k m : ℕ) : ℕ :=
  (500000*(wordWidth n k+1)^2+10000*(trialBits n k+1)+laterCellCost n k m+1000)*(k+1)+
    100000*(wordWidth n k+1)^2



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] PredecessorCounter PreviousCounter LayerIndex VerticesCounter VerticesTemplate Vertex GraphArray.Current StateIndex LabelCounter LabelTmp
  Wedge.D Wedge.V Wedge.HC Wedge.DC Wedge.Aux Total SignDB SignLookup.DB SignLookup.Count SignLookup.Back
  SignLookup.Tmp BitCounter.Count BitCounter.Tmp

def laterVertices : IStmt NS 1 :=
  .loop VerticesCounter (fun c => decide (c=Cls.mark)) (.seq (.op (.unmark VerticesCounter)) laterVertex)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] PredecessorCounter PreviousCounter LayerIndex VerticesCounter VerticesTemplate Vertex LabelCounter LabelTmp GraphArray.Current
  Matrix.Current Matrix.Prev Matrix.Template Matrix.Counter Matrix.CopyTmp ArrayLookup.DB

def laterLayer : IStmt NS 1 :=
  .seq (.op (.const Vertex 0)) (.seq (liftClosed (copyMarks VerticesTemplate VerticesCounter LabelTmp))
    (.seq laterVertices (.seq (.op (.drop Vertex))
      (.seq (liftClosed (clearItems Matrix.Prev)) (liftClosed Matrix.transfer)))))

def laterLayerCost (n k m : ℕ) : ℕ := (laterVertexCost n k m+31)*n+
  1000*(wordWidth n k+1)*(n+1)+(2*wordWidth n k+57)*(2^k+1)*(n*k)+100+
    2000*(wordWidth n k+1)*2^k*(n*k+1)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
abbrev LayersCounter : Fin NS := 93
attribute [local simp] LayersCounter LayerIndex VerticesCounter LabelCounter PredecessorCounter PreviousCounter Matrix.Prev ArrayLookup.DB

def layerLoop : IStmt NS 1 :=
  .loop LayersCounter (fun c => decide (c=Cls.mark))
    (.seq (.op (.unmark LayersCounter)) (.seq laterLayer (liftClosed (Square.increment LayerIndex))))

noncomputable def layerLoopState {n k : ℕ} (s : IState NS) (ω : Fin (trialBits n k)→Bool)
    (arcs : List (Fin n × Fin n)) (i : ℕ) (it : List Item) : IState NS :=
  ((s.upd LayersCounter (List.replicate (k-1-i) .mark)).upd LayerIndex (.int (i : ℤ)::it)).upd Matrix.Prev
    (ArrayLookup.frames (matrixArrays (denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 (i+1))))



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic KoanaKPaths.Main
attribute [local simp] LayersCounter LayerIndex VerticesCounter LabelCounter PredecessorCounter PreviousCounter Matrix.Prev ArrayLookup.DB BitCounter.Count BitCounter.Tmp

def layerDriver : IStmt NS 1 :=
  .seq (.op (.const LayerIndex 0))
    (.seq (liftClosed (countExpr (fun _ : Fin 1 => 66) (.input 0) LayersCounter))
      (.seq layerLoop (.op (.drop LayerIndex))))

def layerDriverCost (n k m : ℕ) : ℕ :=
  (laterLayerCost n k m+13000*(wordWidth n k+1)^2+31)*(k-1)+
    25000*(wordWidth n k+1)^2+1200*(k+1)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main

def readyRegisters : List (Fin NS) := coreRegisters++[44,66,87,88,91,92,93]

def readyStack (n k : ℕ) (arcs : List (Fin n × Fin n)) (j : Fin NS) : List Item :=
  match j.val with
  | 53 => [.int (n : ℤ)]
  | 54 => [.int (k : ℤ)]
  | 30 => Input.arcItems (Input.arcValues arcs)
  | 3 => List.replicate k .mark
  | 59 => List.replicate n .mark
  | 45 => List.replicate (n*k) .mark
  | 44 => List.replicate (trialBits n k) .mark
  | 66 => [.int ((k-1 : ℕ) : ℤ)]
  | _ => []

def Ready {n k : ℕ} (s : IState NS) (arcs : List (Fin n × Fin n)) : Prop :=
  ∀ j∈readyRegisters, s.G j=readyStack n k arcs j







end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] Total SignDB SignLookup.DB SignLookup.Count SignLookup.Back SignLookup.Tmp BitCounter.Count BitCounter.Tmp
  VerticesTemplate VerticesCounter LabelCounter LabelTmp PredecessorCounter PreviousCounter LayersCounter
  Matrix.Template Matrix.Counter Matrix.CopyTmp Matrix.Prev ArrayLookup.DB Wedge.D Wedge.HC Wedge.DC Wedge.Aux

def graphLayers : IStmt NS 1 := .seq firstLayer layerDriver

def labeledState {n k : ℕ} (base : IState NS) (ω : Fin (trialBits n k)→Bool) : IState NS :=
  (base.upd Total [.int (trialBits n k : ℤ)]).upd SignDB (signItems (signsOf ω))



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates

def terminalPrefix {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (a : Fin k) (u : ℕ) : Coordinates k :=
  finPrefix (fun v => graphLayer arcs σ R k v a) u





def normPrefix {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (i : ℕ) : ℤ :=
  finPrefix (fun a => (graphOutput arcs σ R a Finset.univ)^2) i



end KoanaKPaths.Main

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates
attribute [local simp] Predecessor StateIndex Vertex Accumulate.Acc Accumulate.Src Wedge.A

def terminalRegs : Fin 3→Fin NS := ![54,80,83]


def terminalCell : IStmt NS 1 :=
  .seq (liftClosed (Matrix.readArray terminalRegs predExpr))
    (.seq (liftClosed Accumulate.program) (liftClosed (Square.increment Predecessor)))

def terminalCellCost (n k : ℕ) : ℕ :=
  100000*(wordWidth n k+1)^2+10000*(wordWidth n k+1)*2^k*(n*k+1)+
    10000*(wordWidth n k+2)*(2^k+1)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates
attribute [local simp] PredecessorCounter PreviousCounter Predecessor Accumulate.Acc Vertex StateIndex LayerIndex

def terminalLoop : IStmt NS 1 :=
  .loop PredecessorCounter (fun c => decide (c=Cls.mark))
    (.seq (.op (.unmark PredecessorCounter)) terminalCell)

noncomputable def terminalLoopState {n k : ℕ} (s : IState NS) (ω : Fin (trialBits n k)→Bool)
    (arcs : List (Fin n × Fin n)) (a : Fin k) (u : ℕ) (ut accTail : List Item) : IState NS :=
  ((s.upd PredecessorCounter (List.replicate (n-u) .mark)).upd Predecessor (.int (u : ℤ)::ut)).upd Accumulate.Acc
    ((coefficientList (terminalPrefix arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 a u)).map Item.int ++ .mark::accTail)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Norm
abbrev Sum : Fin NS := 79
abbrev TransferTmp : Fin NS := 23
attribute [local simp] Wedge.R Sum TransferTmp Src Value Square.Value Accumulate.Acc

def addArray : IStmt NS 0 :=
  .seq (transferArray Accumulate.Acc Src TransferTmp)
    (.seq takeTop (.seq Square.program (.op (.add Value Sum Sum))))



end KoanaKPaths.Machine.Norm

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates
attribute [local simp] PredecessorCounter Predecessor StateIndex Accumulate.Acc VerticesTemplate LabelTmp
  Wedge.D Wedge.HC Wedge.DC Wedge.Aux Norm.Sum

def normState : IStmt NS 1 :=
  .seq (liftClosed (Wedge.zeroArray Accumulate.Acc)) (.seq (.op (.const Predecessor 0))
    (.seq (liftClosed (copyMarks VerticesTemplate PredecessorCounter LabelTmp)) (.seq terminalLoop
      (.seq (.op (.drop Predecessor)) (.seq (liftClosed Norm.addArray) (liftClosed (Square.increment StateIndex)))))))

def normStateCost (n k : ℕ) : ℕ :=
  (terminalCellCost n k+31)*n+50000*(wordWidth n k+1)^2*(2^k+1)+1000*(n+1)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates
attribute [local simp] LabelCounter StateIndex Norm.Sum PredecessorCounter Vertex StateIndex LayerIndex Predecessor Found

def normLoop : IStmt NS 1 :=
  .loop LabelCounter (fun c => decide (c=Cls.mark))
    (.seq (.op (.unmark LabelCounter)) normState)

noncomputable def normLoopState {n k : ℕ} (s : IState NS) (ω : Fin (trialBits n k)→Bool)
    (arcs : List (Fin n × Fin n)) (a : ℕ) (atail sumTail : List Item) : IState NS :=
  ((s.upd LabelCounter (List.replicate (k-a) .mark)).upd StateIndex (.int (a : ℤ)::atail)).upd Norm.Sum
    (.int (normPrefix arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 a)::sumTail)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] LabelCounter LabelTmp StateIndex PredecessorCounter Norm.Sum Wedge.D

def normDriver : IStmt NS 1 :=
  .seq (.op (.const Norm.Sum 0)) (.seq (.op (.const StateIndex 0))
    (.seq (liftClosed (copyMarks Wedge.D LabelCounter LabelTmp)) (.seq normLoop (.op (.drop StateIndex)))))

def normDriverCost (n k : ℕ) : ℕ := (normStateCost n k+31)*k+3000*(wordWidth n k+1)*(k+1)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic KoanaKPaths.Main

def totalRegs : Fin 3→Fin NS := ![53,54,66]
def totalValues (n k : ℕ) : Fin 3→ℕ := ![n,k,k-1]
def totalExpr : Expr 3 := .add (.mul (.input 0) (.input 1))
  (.add (.mul (.input 1) (.input 0))
    (.mul (.input 2) (.mul (.input 1) (.mul (.input 1) (.input 0)))))

def storeTotal : IStmt NS 0 := storeExpr totalRegs totalExpr Total







end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] SignLookup.DB Coins SignDB SignTemplate SignCounter SignTmp Total Matrix.Prev ArrayLookup.DB Norm.Sum
  LabelCounter PredecessorCounter

def nativeTrial : IStmt NS 1 :=
  .seq (liftClosed storeTotal) (.seq (liftClosed loadSigns) (.seq graphLayers (.seq normDriver
    (.seq (liftClosed (clearItems Matrix.Prev))
      (.seq (liftClosed (clearItems SignDB)) (.op (.drop Total)))))))

def nativeTrialCost (n k m : ℕ) : ℕ :=
  180000*(wordWidth n k+1)^2+500*(trialBits n k+1)+firstLayerCost n k+
    layerDriverCost n k m+normDriverCost n k+(2*wordWidth n k+57)*(2^k+1)*(n*k)+100



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Balanced

abbrev Chunk := ℕ×ℤ

/-- Merge equal-size blocks, as in carrying in a binary counter. -/
def carryInsert : ℕ→ℤ→List Chunk→List Chunk
  | l,x,[] => [(l,x)]
  | l,x,(j,y)::cs => if j=l then carryInsert (l+1) (x+y) cs else (l,x)::(j,y)::cs

/-- Charged work of the carry loop, including its counter-bit restoration and final move. -/
def carryCharge : ℕ→ℤ→List Chunk→ℕ
  | _,x,[] => 2*moveCost (zsz x)+109
  | l,x,(j,y)::cs => if j=l then
      addIntCost (zsz x+zsz y)+68+carryCharge (l+1) (x+y) cs
    else 2*moveCost (zsz x)+109

def potential (w : ℕ) (cs : List Chunk) : ℕ :=
  5000*(cs.map (fun c => w+c.1+2)).sum









def chunkCount (cs : List Chunk) : ℕ := (cs.map (fun c => 2^c.1)).sum



def accumulate : List Chunk→List ℤ→List Chunk
  | cs,[] => cs
  | cs,x::xs => accumulate (carryInsert 0 x cs) xs

def accumulateCharge : List Chunk→List ℤ→ℕ
  | _,[] => 0
  | cs,x::xs => carryCharge 0 x cs+accumulateCharge (carryInsert 0 x cs) xs










def foldCharge : ℤ→List Chunk→ℕ
  | _,[] => 30
  | x,(_,y)::cs => addIntCost (zsz x+zsz y)+30+foldCharge (x+y) cs









end KoanaKPaths.Machine.Balanced

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
open NLogN
namespace KoanaKPaths.Machine.Balanced
abbrev NS := Wedge.NS
abbrev Partials : Fin NS := 102
abbrev Bits : Fin NS := 103
abbrev Carry : Fin NS := 104
abbrev Restore : Fin NS := 105
abbrev Sum : Fin NS := 106
attribute [local simp] Partials Bits Carry Restore Sum

/-- Merge exactly the low binary-counter positions that currently contain ones. -/
def mergeOnes : IStmt NS 0 :=
  .loop Bits (fun c => decide (c=Cls.pos))
    (.seq (.op (.drop Bits)) (.seq (.op (.mark Restore)) (.op (.add Carry Partials Carry))))

def mergeCost : ℤ→List ℤ→ℕ
  | _,[] => 30
  | x,y::ys => addIntCost (zsz x+zsz y)+35+mergeCost (x+y) ys



/-- Insert a fresh trial value, incrementing the binary occupancy counter. -/
def insert : IStmt NS 0 :=
  .seq mergeOnes
    (.seq (.ite Bits (fun c => decide (c=Cls.zero)) (.op (.drop Bits)) .skip)
      (.seq (.op (.const Bits 1))
        (.seq (repeatInts Restore Bits 0) (.op (.mv Carry Partials)))))

def stopBits (zero : Bool) (tail : List Item) : List Item :=
  (if zero then Item.int 0 else Item.mark)::tail

def nextBits (zero : Bool) (tail : List Item) : List Item :=
  if zero then tail else Item.mark::tail

def insertCost (x : ℤ) (ys : List ℤ) (zero : Bool) : ℕ :=
  mergeCost x ys+(if zero then 27 else 26)+3+33*ys.length+30+
    (2*moveCost (zsz (x+ys.sum))+19)



end KoanaKPaths.Machine.Balanced

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Balanced

def counterCode (l : ℕ) : List Chunk → List Item
  | [] => [.mark]
  | (j,_)::cs => List.replicate (j-l) (.int 0) ++ .int 1::counterCode (j+1) cs









end KoanaKPaths.Machine.Balanced

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Balanced
attribute [local simp] Partials Bits Carry Restore Sum



/-- Collapse the remaining occupied blocks, in increasing order of block size. -/
def foldPartials : IStmt NS 0 :=
  .loop Partials (fun c => decide (c=Cls.zero ∨ c=Cls.pos ∨ c=Cls.neg))
    (.op (.add Sum Partials Sum))



end KoanaKPaths.Machine.Balanced

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main Balanced
abbrev TrialCounter : Fin NS := 101
attribute [local simp] TrialCounter Coins Norm.Sum Balanced.Carry Balanced.Bits Balanced.Partials Balanced.Restore

def trialFold : IStmt NS 1 :=
  .loop TrialCounter (fun c => decide (c=Cls.mark))
    (.seq (.op (.unmark TrialCounter)) (.seq nativeTrial
      (.seq (.op (.mv Norm.Sum Balanced.Carry)) (liftClosed Balanced.insert))))

def trialStream {n k : ℕ} (os : List (Fin (trialBits n k)→Bool)) : List Item :=
  (os.flatMap signsOf).map Item.int
noncomputable def numerators {n k : ℕ} (arcs : List (Fin n × Fin n))
    (os : List (Fin (trialBits n k)→Bool)) : List ℤ :=
  os.map (fun ω => (trialNumerator (walkTensor n arcs k) (trialEquiv n k ω) : ℤ))

noncomputable def trialFoldState {n k : ℕ} (s : IState NS) (arcs : List (Fin n × Fin n))
    (os : List (Fin (trialBits n k)→Bool)) (cs : List Chunk) (tail bt pt : List Item) : IState NS :=
  (((s.upd TrialCounter []).upd Coins tail).upd Balanced.Bits
    (counterCode 0 (accumulate cs (numerators arcs os))++bt)).upd Balanced.Partials
      (((accumulate cs (numerators arcs os)).map Prod.snd).map Item.int ++ pt)

def trialFoldBaseCost (n k m : ℕ) : ℕ := nativeTrialCost n k m+1000*(wordWidth n k+1)+31



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Balanced

def counterDigits (l : ℕ) : List Chunk→List ℤ
  | [] => []
  | (j,_)::cs => List.replicate (j-l) 0 ++ 1::counterDigits (j+1) cs









end KoanaKPaths.Machine.Balanced

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Balanced
abbrev Records : Fin NS := 107
attribute [local simp] Partials Bits Sum Records

def finishGroup : IStmt NS 0 :=
  .seq (.op (.const Sum 0)) (.seq foldPartials (.seq (.op (.unmark Partials))
    (.seq (clearInts Bits) (.seq (.op (.unmark Bits)) (.op (.mv Sum Records))))))



end KoanaKPaths.Machine.Balanced

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
abbrev TrialTemplate : Fin NS := 42
abbrev GroupCopyTmp : Fin NS := 61
attribute [local simp] TrialCounter TrialTemplate GroupCopyTmp Coins Balanced.Partials Balanced.Bits Balanced.Restore Balanced.Records

def groupNative : IStmt NS 1 :=
  .seq (.op (.mark Balanced.Partials)) (.seq (.op (.mark Balanced.Bits))
    (.seq (liftClosed (copyMarks TrialTemplate TrialCounter GroupCopyTmp))
      (.seq trialFold (liftClosed Balanced.finishGroup))))

def groupNativeCost (n k m trials : ℕ) : ℕ :=
  trialFoldBaseCost n k m*trials+10000*(wordWidth n k+2)*(trials+1)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
abbrev GroupCounter : Fin NS := 100
attribute [local simp] GroupCounter TrialTemplate TrialCounter GroupCopyTmp Coins Balanced.Restore Balanced.Records

def groupFold : IStmt NS 1 :=
  .loop GroupCounter (fun c => decide (c=Cls.mark)) (.seq (.op (.unmark GroupCounter)) groupNative)

def groupsStream {n k : ℕ} (oss : List (List (Fin (trialBits n k)→Bool))) : List Item :=
  oss.flatMap trialStream
noncomputable def groupSums {n k : ℕ} (arcs : List (Fin n × Fin n))
    (oss : List (List (Fin (trialBits n k)→Bool))) : List ℤ :=
  oss.map (fun os => (numerators arcs os).sum)

noncomputable def groupFoldState {n k : ℕ} (s : IState NS) (arcs : List (Fin n × Fin n))
    (oss : List (List (Fin (trialBits n k)→Bool))) (tail : List Item) : IState NS :=
  ((s.upd GroupCounter []).upd Coins tail).upd Balanced.Records
    ((groupSums arcs oss).reverse.map Item.int ++ s.G Balanced.Records)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}

/-- Reverse one delimited integer array in place using three linear passes. -/
def reverseArray (src tmp aux : Fin S) : IStmt S 0 :=
  .seq (transferArray src tmp aux) (.seq (.op (.mark src))
    (.seq (moveInts tmp src) (.op (.unmark tmp))))





end KoanaKPaths.Machine

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
abbrev GroupTemplate : Fin NS := 43
abbrev OuterCopyTmp : Fin NS := 62
attribute [local simp] GroupTemplate OuterCopyTmp GroupCounter TrialCounter TrialTemplate GroupCopyTmp Coins Balanced.Records Balanced.Restore

def groupDriver : IStmt NS 1 :=
  .seq (.op (.mark Balanced.Records))
    (.seq (liftClosed (copyMarks GroupTemplate GroupCounter OuterCopyTmp))
      (.seq groupFold (liftClosed (reverseArray Balanced.Records GroupCopyTmp OuterCopyTmp))))

def groupDriverCost (n k m trials groups : ℕ) : ℕ :=
  (groupNativeCost n k m trials+3000*(wordWidth n k+trials+1))*(groups+1)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median
abbrev Saved : Fin NS := 117
abbrev Flag : Fin NS := 119
attribute [local simp] Count Threshold Saved Flag

/-- Consume the observed count while retaining a restorable prefix of the threshold. -/
def peelCount : IStmt NS 0 :=
  .loop Count (fun c => decide (c=Cls.mark))
    (.seq (.op (.unmark Count))
      (.ite Threshold (fun c => decide (c=Cls.mark))
        (.seq (.op (.unmark Threshold)) (.op (.mark Saved))) .skip))



/-- Test the quantile threshold using unary counts, with no confidence-word arithmetic. -/
def compareCounts : IStmt NS 0 :=
  .seq peelCount
    (.seq (.ite Threshold (fun c => decide (c=Cls.mark)) .skip (.op (.mark Flag)))
      (moveMarks Saved Threshold))



end KoanaKPaths.Machine.Median

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median
attribute [local simp] Records Mid Value Tmp Work Count Threshold Back Saved Flag

/-- Inspect all group sums and restore their original order. -/
def countRecords : IStmt NS 0 :=
  .seq (.op (.mark Back)) (.seq scan (.seq (moveInts Back Records) (.op (.unmark Back))))





/-- Set the upper-half decision flag, retaining the threshold and all group sums. -/
def quantileTest : IStmt NS 0 := .seq countRecords compareCounts



end KoanaKPaths.Machine.Median

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median
abbrev Ruler : Fin NS := 118
abbrev Rem : Fin NS := 120
attribute [local simp] Lo Hi Mid Tmp Work Ruler Rem

/-- Compute the midpoint with a one-bit split, retaining both interval endpoints. -/
def midpoint : IStmt NS 0 :=
  .seq (.op (.dup Lo Tmp)) (.seq (.op (.dup Hi Work))
    (.seq (.op (.add Tmp Work Mid))
      (.seq (.op (.split Mid Ruler Rem)) (.op (.drop Rem)))))

def midpointCost (lo hi : ℕ) : ℕ :=
  dupCost (zsz (lo : ℤ))+17+dupCost (zsz (hi : ℤ))+17+
    addIntCost (zsz (lo : ℤ)+zsz (hi : ℤ))+321+
      (2*zsz (((lo+hi)%2 : ℕ) : ℤ)+2)





end KoanaKPaths.Machine.Median

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median
attribute [local simp] Lo Hi Mid Work Flag

def updateInterval : IStmt NS 0 :=
  .ite Flag (fun c => decide (c=Cls.mark))
    (.seq (.op (.unmark Flag)) (.seq (.op (.drop Hi)) (.op (.mv Mid Hi))))
    (.seq (.op (.drop Lo)) (.seq (.op (.const Work 1)) (.op (.add Mid Work Lo))))









end KoanaKPaths.Machine.Median

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace KoanaKPaths.Sampling



/-- Bounded-round binary search for the middle order statistic. -/
def medianSearch (b : ℕ) (x : Fin (2*b+1)→ℕ) : ℕ→ℕ→ℕ→ℕ
  | 0, lo, _ => lo
  | L+1, lo, hi =>
    if lo< hi then
      let mid := (lo+hi)/2
      if b+1≤(Finset.univ.filter (fun i => x i≤ mid)).card then
        medianSearch b x L lo mid
      else medianSearch b x L (mid+1) hi
    else lo





end KoanaKPaths.Sampling

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace KoanaKPaths.Machine.Median

def searchBounds (test : ℕ→Prop) [DecidablePred test] : ℕ→ℕ→ℕ→ℕ×ℕ
  | 0,lo,hi => (lo,hi)
  | L+1,lo,hi =>
    let mid := (lo+hi)/2
    if test mid then searchBounds test L lo mid else searchBounds test L (mid+1) hi









end KoanaKPaths.Machine.Median

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median
attribute [local simp] Records Lo Hi Mid Ruler Rem Count Threshold Saved Flag

def nextBounds (xs : List ℤ) (t lo hi : ℕ) : ℕ×ℕ :=
  if t≤ countLE (((lo+hi)/2 : ℕ) : ℤ) xs then (lo,(lo+hi)/2) else ((lo+hi)/2+1,hi)

def round : IStmt NS 0 := .seq midpoint (.seq quantileTest updateInterval)







end KoanaKPaths.Machine.Median

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median
abbrev Fuel : Fin NS := 123
attribute [local simp] Fuel Records Lo Hi Mid Ruler Count Threshold Saved Flag

def loop : IStmt NS 0 :=
  .loop Fuel (fun c => decide (c=Cls.mark)) (.seq (.op (.unmark Fuel)) round)

def boundsState (s : IState NS) (fuel : ℕ) (bounds : ℕ×ℕ) (lt ht : List Item) : IState NS :=
  ((s.upd Fuel (List.replicate fuel .mark)).upd Lo (.int (bounds.1 : ℤ)::lt)).upd Hi
    (.int (bounds.2 : ℤ)::ht)





end KoanaKPaths.Machine.Median

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median
abbrev Template : Fin NS := 124
abbrev CopyTmp : Fin NS := 125
abbrev Output : Fin NS := 126
attribute [local simp] Template CopyTmp Output Fuel Hi Ruler Work Lo

def shiftLoop : IStmt NS 0 :=
  .loop Fuel (fun c => decide (c=Cls.mark))
    (.seq (.op (.unmark Fuel)) (.op (.shl Hi Ruler)))



/-- Construct the binary upper endpoint without enumerating its numerical value. -/
def initializeInterval : IStmt NS 0 :=
  .seq (.op (.const Ruler 2)) (.seq (.op (.const Hi 1)) (.seq (.op (.const Lo 0))
    (.seq (copyMarks Template Fuel CopyTmp) (.seq shiftLoop
      (.seq (.op (.const Work (-1))) (.seq (.op (.add Hi Work Hi))
        (copyMarks Template Fuel CopyTmp)))))))





end KoanaKPaths.Machine.Median

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median
attribute [local simp] Lo Hi Ruler Output

def finishMedian : IStmt NS 0 :=
  .seq (.op (.drop Hi)) (.seq (.op (.mv Lo Output)) (.op (.drop Ruler)))





end KoanaKPaths.Machine.Median

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median
attribute [local simp] Template CopyTmp Output Fuel Records Lo Hi Mid Ruler Count Threshold Saved Flag

def program : IStmt NS 0 := .seq initializeInterval (.seq loop finishMedian)





end KoanaKPaths.Machine.Median

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main

def estimatorRegisters : List (Fin NS) := [42,43,55,56,57,60,61,62,100,101,105,110,114,115,117,119,123,124,125,126,127]
def estimatorStack (n k a b m : ℕ) (j : Fin NS) : List Item :=
  match j.val with
  | 42 => List.replicate (groupTrials k a) .mark
  | 43 => List.replicate (2*b+1) .mark
  | 55 => [.int (a : ℤ)]
  | 56 => [.int (b : ℤ)]
  | 57 => [.int (m : ℤ)]
  | 60 => [.int ((4^a : ℕ) : ℤ)]
  | 115 => List.replicate (b+1) .mark
  | 124 => List.replicate (medianWidth n k a) .mark
  | _ => []

def EstimatorReady {n : ℕ} (s : IState NS) (k a b : ℕ) (arcs : List (Fin n × Fin n)) : Prop :=
  Ready (k := k) s arcs ∧ ∀ j∈estimatorRegisters, s.G j=estimatorStack n k a b arcs.length j



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open NLogN
open scoped BigOperators
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] GroupTemplate GroupCounter TrialTemplate TrialCounter GroupCopyTmp OuterCopyTmp Coins Balanced.Records Balanced.Restore
  Median.Records Median.Template Median.CopyTmp Median.Output Median.Fuel Median.Mid Median.Count Median.Threshold Median.Saved Median.Flag

def nativeNumerator : IStmt NS 1 := .seq groupDriver (liftClosed Median.program)

def numeratorCost (n k a b m : ℕ) : ℕ := groupDriverCost n k m (groupTrials k a) (2*b+1)+
  30000*(medianWidth n k a+1)^2*(2*b+2)



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Main

def partialDenominator (k a i : ℕ) : ℕ := groupTrials k a*k^i*i.factorial








end KoanaKPaths.Main

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Arithmetic
open Square
variable {v : ℕ}
attribute [local simp] Eval Value

def replaceExpr (reg : Fin v→Fin Square.NS) (e : Expr v) (dst : Fin Square.NS) : IStmt Square.NS 0 :=
  .seq (e.compile reg) (.seq (.op (.drop dst)) (.op (.mv Eval dst)))



end KoanaKPaths.Machine.Arithmetic

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Denominator
open Arithmetic KoanaKPaths.Main
abbrev NS := Trial.NS
abbrev Den : Fin NS := 127
abbrev Index : Fin NS := Trial.StateIndex
attribute [local simp] Den Index Trial.StateIndex

def regs : Fin 3→Fin NS := ![127,54,83]
def values (k a j : ℕ) : Fin 3→ℕ := ![partialDenominator k a j,k,j]
def expr : Expr 3 := .mul (.mul (.input 0) (.input 1)) (.add (.input 2) (.constant 1))
def step : IStmt NS 0 := .seq (replaceExpr regs expr Den) (Square.increment Index)





end KoanaKPaths.Machine.Denominator

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Denominator
open Arithmetic KoanaKPaths.Main

def initRegs : Fin 2→Fin NS := ![54,60]
def initValues (k a : ℕ) : Fin 2→ℕ := ![k,4^a]
def initExpr : Expr 2 := .mul
  (.mul (.constant 1024) (.mul (.mul (.input 0) (.input 0)) (.input 0))) (.input 1)
def initDen : IStmt NS 0 := storeExpr initRegs initExpr Den





end KoanaKPaths.Machine.Denominator

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Denominator
open KoanaKPaths.Main
abbrev Counter : Fin NS := Trial.LabelCounter
attribute [local simp] Counter Trial.LabelCounter Den Index Trial.StateIndex

def loop : IStmt NS 0 := .loop Counter (fun c => decide (c=Cls.mark)) (.seq (.op (.unmark Counter)) step)
def loopState (s : IState NS) (k a j : ℕ) (dt jt : List Item) : IState NS :=
  ((s.upd Counter (List.replicate (k-j) .mark)).upd Index (.int (j : ℤ)::jt)).upd Den
    (.int (partialDenominator k a j : ℤ)::dt)



end KoanaKPaths.Machine.Denominator

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Denominator
open KoanaKPaths.Main
attribute [local simp] Den Index Counter Trial.StateIndex Trial.LabelCounter Trial.LabelTmp Wedge.D

def program : IStmt NS 0 :=
  .seq initDen (.seq (.op (.const Index 0))
    (.seq (copyMarks Wedge.D Counter Trial.LabelTmp) (.seq loop (.op (.drop Index)))))

def driverCost (n k a : ℕ) : ℕ := 40000000*(medianWidth n k a+1)^2*(k+1)



end KoanaKPaths.Machine.Denominator

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main

def sampleTrials {n k a b : ℕ} (ω : Fin (sampleBits n k a b)→Bool) :
    Fin (2*b+1)→Fin (groupTrials k a)→Fin (trialBits n k)→Bool :=
  fun i j t => ω (finProdFinEquiv (finProdFinEquiv (i,j),t))












end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open NLogN
open scoped BigOperators
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] Coins Balanced.Records Median.Output Denominator.Den Denominator.Index Denominator.Counter
  StateIndex LabelCounter LabelTmp Wedge.D

def nativeEstimator : IStmt NS 1 := .seq nativeNumerator (liftClosed Denominator.program)
def estimatorCost (n k a b m : ℕ) : ℕ := numeratorCost n k a b m+Denominator.driverCost n k a



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Controls
open Arithmetic
abbrev FieldK : Fin NS := 54
abbrev FieldA : Fin NS := 55
abbrev KMinus : Fin NS := 66
attribute [local simp] FieldK FieldA KMinus PowerCount PowerOut BitCounter.Count BitCounter.Tmp Square.Eval Square.Value

def prepareBinary : IStmt NS 0 :=
  .seq (countExpr (fun _ : Fin 1 => FieldA) (.input 0) PowerCount)
    (.seq powerFour (Square.predCopy FieldK KMinus))



end KoanaKPaths.Machine.Controls

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Controls
open Arithmetic
attribute [local simp] FieldK FieldA KMinus PowerOut PowerCount BitCounter.Count BitCounter.Tmp

def setup : IStmt NS 0 := .seq prepareBinary program

def setupState (s : IState NS) (n k a b m : ℕ) : IState NS :=
  applyCounts (inputValues n k a b m)
    ((s.upd PowerOut (.int ((4^a : ℕ) : ℤ)::s.G PowerOut)).upd KMinus
      (.int ((k-1 : ℕ) : ℤ)::s.G KMinus)) plans

def setupCost (n k a b m : ℕ) : ℕ :=
  (22000*(zsz (a : ℤ)+1)^2+1600*(a+1)+12000*(zsz (k : ℤ)+2)^2)+
    countPlansCost (inputValues n k a b m) (100*(controlWidth n k a b m+1)) plans







end KoanaKPaths.Machine.Controls

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 4000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] Input.VertexField Input.PathField Input.AccuracyField Input.ConfidenceField Input.ArcCountField

def preparedState (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) : IState NS :=
  Controls.setupState (Input.parsedState n arcs k a b) n k a b arcs.length








end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S P : ℕ}

def skipInput : Stmt (S+4) P := .seq (.inRd (NLogN.sq S)) (.pop (NLogN.sq S))



end KoanaKPaths.Machine

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S P : ℕ}

/-- Emit the unary length prefix and reverse the stored payload into a scratch stack. -/
def countWriteBits (src dst : Fin S) : Stmt S P :=
  .loop src isBitT
    (.seq (.ite src (fun o => decide (o=some 0))
      (.seq (.pop src) (.push dst 0)) (.seq (.pop src) (.push dst 1))) (.out true))

def writeBits (src : Fin S) : Stmt S P :=
  .loop src isBitT (.seq (.ite src (fun o => decide (o=some 0)) (.out false) (.out true)) (.pop src))

def writeNat (src tmp : Fin S) : Stmt S P :=
  .seq (.pop src) (.seq (countWriteBits src tmp)
    (.seq (.out false) (.seq (transferBits tmp src) (writeBits src))))










end KoanaKPaths.Machine

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
open HypergraphUnreliability.FPRAS
variable {P : ℕ}

def writeFraction : Stmt (128+4) P :=
  .seq (writeNat (ι (126 : Fin 128)) (NLogN.sq 128))
    (writeNat (ι (127 : Fin 128)) (NLogN.sq 128))



end KoanaKPaths.Machine

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main HypergraphUnreliability.FPRAS
attribute [local simp] Coins

def rawProg : Fin 1→Stmt (NS+4) 1 := fun _ => compile Wedge.body


def positiveRaw : Stmt (NS+4) 1 :=
  .seq (compile (liftClosed Controls.setup)) (.seq skipInput (.seq (bulkSigns 51 Coins)
    (.seq (compile nativeEstimator) writeFraction)))

def writtenCost (f : Frac) : ℕ := 13*(Nat.bits f.num).length+13*(Nat.bits f.den).length+10

def positiveCost (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) (tape : List Bool) : ℕ :=
  Controls.setupCost n k a b arcs.length+2+(8*sampleBits n k a b+2)+
    estimatorCost n k a b arcs.length+writtenCost (estimateFraction (walkTensor n arcs k) a b (tapeSamples n k a b tape))



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {P : ℕ}





def zeroFraction : Stmt (128+4) P := .seq (.out false) (.seq (.out true) (.seq (.out false) (.out true)))









end KoanaKPaths.Machine

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main HypergraphUnreliability.FPRAS

def graphRoot : Stmt (NS+4) 1 := .seq Input.readGraph
  (.seq (.pop (ι (53 : Fin NS)))
    (.ite (ι (53 : Fin NS)) isBitT (.seq (.push (ι (53 : Fin NS)) hdPos) positiveRaw) zeroFraction))

def rootCost (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) (tape : List Bool) : ℕ :=
  Input.graphReadCost n arcs k a b+if n=0 then 6 else positiveCost n arcs k a b tape+3



end KoanaKPaths.Machine.Trial

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine

variable {S : ℕ}

def closedCode (p : Stmt S 0) (pc : ℕ) : Instr S :=
  (p.instrAt Fin.elim0 0 p.size pc).getD .ret

















end KoanaKPaths.Machine

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S P : ℕ}











/-- A recursive auxiliary procedure followed by a separate main program. -/
def oneProcCode (proc root : Stmt S 1) (x : ℕ) : Instr S :=
  if x < proc.size then (proc.instrAt (fun _ => 0) 0 proc.size x).getD .ret
  else if x = proc.size then .ret
  else (root.instrAt (fun _ => 0) (proc.size+1) (proc.size+1+root.size) x).getD .ret











end KoanaKPaths.Machine

end

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main

def costEnvelope (C W M Q L2 K : ℕ) : ℕ :=
  ((C+1000*(W+1)+31)*M+10000*(W+2)*(M+1)+3000*(W+M+1))*(2*Q)+
    60000*L2*Q+40000000*L2*K







end KoanaKPaths.Machine.Trial

end


