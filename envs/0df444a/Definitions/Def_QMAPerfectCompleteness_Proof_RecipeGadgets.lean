-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RecipeGadgets
-- name    : QMAPerfectCompleteness_Proof_RecipeGadgets
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:05:52.443101+00:00
-- url     : https://prove2.me/theorems/b52b4ec6-5d6d-4343-8863-93a92c9009ae
-- title:
--   Finite recipes for reversible circuit gadgets
-- statement:
--   Defines bounded-loop recipes for conjunction, controlled flips, normalization, equality, comparison, addition, clock increment and paired Hadamards. Address substitution and reusable arithmetic steps give finite descriptions of the raw gadget families.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RecipeGadgets.lean, retained declaration span lines 11–424.

/- Generated from Solutions.RecipeGadgets by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanFraming
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitRecipe
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawArithmeticGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RawControlGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawG2Gadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeNormalization
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding



/-! Finite recipes realizing the linear reversible circuit templates. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QMAPerfectCompleteness.Main.CircuitRecipe

namespace Expr
/-- Substitute the current address in an address expression. -/
def plug (e v : Expr) : Expr :=
  match e with
  | .lit n => .lit n | .param p => .param p | .bound j => .bound j
  | .addr => v | .add a b => .add (a.plug v) (b.plug v)
  | .sub a b => .sub (a.plug v) (b.plug v) | .half a => .half (a.plug v)
  | .scale n a => .scale n (a.plug v)
  | .ifLt a b y n => .ifLt (a.plug v) (b.plug v) (y.plug v) (n.plug v)

end Expr

namespace Gadgets
open RawG2 RawEncoding
instance : Add Expr := ⟨Expr.add⟩
instance : Sub Expr := ⟨Expr.sub⟩
instance (n : ℕ) : OfNat Expr n := ⟨Expr.lit n⟩
instance : Append Recipe := ⟨Recipe.append⟩




def x (a : Expr) := Recipe.emit 0 [a]
def cn (a b : Expr) := Recipe.emit 1 [a,b]
def tof (a b c : Expr) := Recipe.emit 2 [a,b,c]
def hh (a b : Expr) := Recipe.emit 3 [a,b]
def conj (a b c : Expr) :=
  Recipe.ifLt a b (tof a b c) (Recipe.ifLt b a (tof a b c) (cn a c))










def andCompute (r control flags : Expr) : Recipe :=
  x (flags.plug 0) ++ Recipe.forUp r
    (tof (flags.lift.plug (.bound 0)) (control.lift.plug (.bound 0))
      (flags.lift.plug (.bound 0+1)))

def useUncompute (a b : Recipe) := (a ++ b) ++ a.reverse

def multiX (r control flags target : Expr) : Recipe :=
  useUncompute (andCompute r control flags) (cn (flags.plug r) target)

def normalize (r control bit : Expr) : Recipe :=
  Recipe.forUp r (Recipe.ifLt (bit.lift.plug (.bound 0)) 1
    (x (control.lift.plug (.bound 0))) .nil)

def patternX (r control flags bit target : Expr) : Recipe :=
  useUncompute (normalize r control bit) (multiX r control flags target)














/-- One symbolic borrow step; all temporary uses are XOR commands. -/
def borrowStep (a b carry next temp : Expr) : Recipe :=
  cn a temp ++ cn b temp ++ x temp ++ x a ++ conj a b next ++ x a ++
    conj temp carry next ++ x temp ++ cn b temp ++ cn a temp

def borrowCompute (r a b carry temp : Expr) := Recipe.forUp r
  (borrowStep (a.lift.plug (.bound 0)) (b.lift.plug (.bound 0))
    (carry.lift.plug (.bound 0)) (carry.lift.plug (.bound 0+1)) temp.lift)

def comparator (r a b carry temp target : Expr) :=
  useUncompute (borrowCompute r a b carry temp) (cn (carry.plug r) target)









def equality (r a b carry temp target : Expr) :=
  comparator r a b carry temp target ++ comparator r b a carry temp target ++ x target




/-- Carry computation for a binary ripple adder. -/
def carryStep (a b carry next temp : Expr) :=
  conj a b next ++ cn a temp ++ cn b temp ++ conj temp carry next ++ cn b temp ++ cn a temp

def carryCompute (r a b carry temp : Expr) := Recipe.forUp r
  (carryStep (a.lift.plug (.bound 0)) (b.lift.plug (.bound 0))
    (carry.lift.plug (.bound 0)) (carry.lift.plug (.bound 0+1)) temp.lift)

def sumCompute (r a b carry output : Expr) := Recipe.forUp r
  (cn (a.lift.plug (.bound 0)) (output.lift.plug (.bound 0)) ++
    cn (b.lift.plug (.bound 0)) (output.lift.plug (.bound 0)) ++
    cn (carry.lift.plug (.bound 0)) (output.lift.plug (.bound 0)))

def addition (r a b carry output temp : Expr) :=
  useUncompute (carryCompute r a b carry temp) (sumCompute r a b carry output)












/-- Binary comparison with a symbolic threshold bit function. No exponentially large
threshold is written to a unary register. -/
def compareBits (r control flags bits target : Expr) : Recipe := Recipe.forUp r
  (Recipe.ifLt 0 (bits.lift.plug (r.lift-1-.bound 0))
    (patternX (.bound 0+1) (control.lift.plug ((r.plug 0).lift-1-.addr)) flags.lift
      (.ifLt .addr (.bound 0) (bits.lift.plug ((r.plug 0).lift-1-.addr)) 0) target.lift) .nil)





def increment (r control flags : Expr) := Recipe.forDown r
  (multiX (.bound 0+1) control.lift flags.lift (control.lift.plug (.bound 0+1)))





def pairedH (r wire : Expr) := Recipe.forUp (.half r)
  (hh (wire.lift.plug (.scale 2 (.bound 0))) (wire.lift.plug (.scale 2 (.bound 0)+1)))




end Gadgets
end QMAPerfectCompleteness.Main.CircuitRecipe


