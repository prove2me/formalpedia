-- Prove2me | Definitions.Def_Monodromy_FormalCompilation
-- name    : Monodromy_FormalCompilation
-- status  : Definition
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:21:57.460797+00:00
-- url     : https://prove2.me/theorems/8e15d200-da98-4a81-8650-5059fb4b279f
-- title:
--   Finite Turing Compilation and Reversible Native Universality
-- statement:
--   Connects Mathlib’s partial-recursive stack evaluator to finite Turing tables, finite counter compilers and actual native continuation programs. Defines ordinary and history-recording encodings, marked source-step macros, reversible prime compression, forward and inverse native tables, and the complete result, halting, divergence and actual-cover-lift universality contracts.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/FormalCompilation.lean (file SHA-256 c07335814044367fc4605d1e494fe82a30c684f754d58d55aaa7514b94c37122):
--   Monodromy.FormalCompilation.Stack at L27-L27 [UTF-8 828:859].
--   Monodromy.FormalCompilation.Symbol at L28-L28 [UTF-8 860:893].
--   Monodromy.FormalCompilation.Store at L29-L29 [UTF-8 894:923].
--   Monodromy.FormalCompilation.Label2 at L30-L30 [UTF-8 924:957].
--   Monodromy.FormalCompilation.Alphabet at L31-L31 [UTF-8 958:1011].
--   Monodromy.FormalCompilation.stackFintype at L33-L35 [UTF-8 1013:1146].
--   Monodromy.FormalCompilation.Control1 at L37-L40 [UTF-8 1148:1355].
--   Monodromy.FormalCompilation.control1Inhabited at L44-L45 [UTF-8 1393:1533].
--   Monodromy.FormalCompilation.machine1 at L47-L48 [UTF-8 1535:1642].
--   Monodromy.FormalCompilation.Control0 at L50-L50 [UTF-8 1644:1695].
--   Monodromy.FormalCompilation.control0Inhabited at L52-L53 [UTF-8 1697:1817].
--   Monodromy.FormalCompilation.machine0 at L55-L55 [UTF-8 1819:1903].
--   Monodromy.FormalCompilation.labels1 at L57-L58 [UTF-8 1905:2047].
--   Monodromy.FormalCompilation.supports1 at L60-L63 [UTF-8 2049:2316].
--   Monodromy.FormalCompilation.labels0 at L65-L65 [UTF-8 2318:2423].
--   Monodromy.FormalCompilation.supports0 at L67-L68 [UTF-8 2425:2577].
--   Monodromy.FormalCompilation.finiteSupport at L70-L71 [UTF-8 2579:2696].
--   Monodromy.FormalCompilation.tapeData at L73-L76 [UTF-8 2698:2921].
--   Monodromy.FormalCompilation.halt1 at L121-L122 [UTF-8 4978:5146].
--   Monodromy.FormalCompilation.halt0 at L156-L157 [UTF-8 6818:6942].
--   Monodromy.NativeTuring.source3 at L210-L212 [UTF-8 9247:9404].
--   Monodromy.NativeTuring.source2 at L214-L216 [UTF-8 9406:9585].
--   Monodromy.NativeTuring.source3_nonempty at L218-L220 [UTF-8 9587:9750].
--   Monodromy.NativeTuring.source2_nonempty at L222-L226 [UTF-8 9752:10031].
--   Monodromy.NativeTuring.program at L228-L231 [UTF-8 10033:10306].
--   Monodromy.NativeTuring.iota at L233-L236 [UTF-8 10308:10614].
--   Monodromy.NativeTuring.finiteProgram at L362-L364 [UTF-8 17540:17767].
--   Monodromy.NativeTuring.finiteIota at L366-L368 [UTF-8 17769:17963].
--   Monodromy.NativeTuring.markTable at L412-L415 [UTF-8 19595:19831].
--   Monodromy.NativeTuring.markedProgram at L417-L419 [UTF-8 19833:20074].
--   Monodromy.NativeTuring.MarkedBoundary at L421-L423 [UTF-8 20076:20314].
--   Monodromy.NativeTuring.CounterMarked at L498-L503 [UTF-8 24097:24481].
--   Monodromy.NativeTuring.counterMark at L505-L507 [UTF-8 24483:24699].
--   Monodromy.NativeTuring.boundaryProgram at L509-L511 [UTF-8 24701:24894].
--   Monodromy.NativeTuring.Boundary at L513-L515 [UTF-8 24896:25107].
--   Monodromy.NativeTuring.CounterInternalStep at L546-L549 [UTF-8 26723:27064].
--   Monodromy.NativeTuring.CounterInternalReaches at L551-L552 [UTF-8 27066:27196].
--   Monodromy.NativeTuring.InternalStep at L598-L600 [UTF-8 29876:30145].
--   Monodromy.NativeTuring.InternalReaches at L602-L603 [UTF-8 30147:30263].
--   Monodromy.NativeTuring.FirstReturn at L625-L627 [UTF-8 31563:31841].
--   Monodromy.NativeTuring.macroStep at L662-L667 [UTF-8 33725:34152].
--   Monodromy.NativeTuring.finiteMacro at L690-L692 [UTF-8 35202:35452].
--   Monodromy.RecordedTuring.size at L737-L738 [UTF-8 37279:37401].
--   Monodromy.RecordedTuring.counterEncode at L740-L743 [UTF-8 37403:37656].
--   Monodromy.ReversibleTuring.table at L769-L774 [UTF-8 38528:38944].
--   Monodromy.ReversibleTuring.encode at L776-L780 [UTF-8 38946:39257].
--   Monodromy.ReversibleTuring.Boundary at L813-L817 [UTF-8 41246:41591].
--   Monodromy.ReversibleTuring.boundary_decidable at L819-L824 [UTF-8 41593:41863].
--   Monodromy.ReversibleTuring.boundaryTransition at L882-L886 [UTF-8 45422:45771].
--   Monodromy.ReversibleTuring.macroStep at L910-L918 [UTF-8 46932:47503].
--   Monodromy.ReversibleTuring.Related at L960-L964 [UTF-8 49792:50076].
--   Monodromy.ReversibleTuring.Compression.basis at L1036-L1042 [UTF-8 53589:53884].
--   Monodromy.ReversibleTuring.Compression.source_deterministic at L1046-L1048 [UTF-8 53930:54119].
--   Monodromy.ReversibleTuring.Compression.source_targetCompatible at L1050-L1052 [UTF-8 54121:54319].
--   Monodromy.ReversibleTuring.Compression.size at L1054-L1056 [UTF-8 54321:54525].
--   Monodromy.ReversibleTuring.Compression.edges at L1058-L1059 [UTF-8 54527:54659].
--   Monodromy.ReversibleTuring.Compression.table at L1061-L1064 [UTF-8 54661:55003].
--   Monodromy.ReversibleTuring.Compression.encode at L1066-L1071 [UTF-8 55005:55453].
--   Monodromy.ReversibleTuring.Compression.deterministic at L1073-L1076 [UTF-8 55455:55712].
--   Monodromy.ReversibleTuring.Compression.targetCompatible at L1078-L1081 [UTF-8 55714:55980].
--   Monodromy.ReversibleTuring.Compression.sourceMark at L1109-L1113 [UTF-8 57568:57891].
--   Monodromy.ReversibleTuring.Compression.Boundary at L1129-L1134 [UTF-8 58738:59098].
--   Monodromy.ReversibleTuring.Compression.boundary_decidable at L1136-L1143 [UTF-8 59100:59531].
--   Monodromy.ReversibleTuring.Compression.mark at L1145-L1147 [UTF-8 59533:59756].
--   Monodromy.ReversibleTuring.Compression.Related at L1254-L1256 [UTF-8 66167:66371].
--   Monodromy.ReversibleNativeTuring.size_nonzero at L1326-L1330 [UTF-8 69678:69909].
--   Monodromy.ReversibleNativeTuring.program at L1332-L1336 [UTF-8 69911:70295].
--   Monodromy.ReversibleNativeTuring.iota at L1338-L1341 [UTF-8 70297:70614].
--   Monodromy.ReversibleNativeTuring.boundaryProgram at L1350-L1355 [UTF-8 70920:71338].
--   Monodromy.ReversibleNativeTuring.Boundary at L1357-L1358 [UTF-8 71340:71472].
--   Monodromy.ReversibleNativeTuring.FirstReturn at L1368-L1371 [UTF-8 71983:72277].
--   Monodromy.ReversibleNativeTuring.Related at L1419-L1421 [UTF-8 75286:75464].
--   Monodromy.ReversibleNativeTuring.reverseProgram at L1464-L1468 [UTF-8 77789:78192].
--   Monodromy.ReversibleNativeTuring.executionEquiv at L1480-L1482 [UTF-8 78896:79135].
--   Monodromy.ReversibleNativeTuring.macroStep at L1502-L1506 [UTF-8 80230:80613].
--   Monodromy.ReversibleNativeTuring.reverseMacro at L1508-L1510 [UTF-8 80615:80889].

-- Generated by Lean-fact skeleton subtraction; original source is frozen in imports/monodromy/source.
module
public import Definitions.Def_Monodromy_Counter
public import Definitions.Def_Monodromy_FiniteSupport
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Computability.TuringMachine.ToPartrec
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section


/-!
# Finite Turing tables and native continuation

Mathlib's stack evaluator is translated to a Post–Turing table and restricted
to its finite support. The source code fixes the table; its numeric arguments
are supplied through an explicit finite input word.

The native simulation composes the actual finite counter compilers with
fixed geometric Word execution. It preserves full configurations, complete
partial results, halting and divergence. Source steps are causal first returns
marked by finite analytic root observations. Finite executions are realized
by the two matching covering-space lifts.
-/

@[expose] public section

namespace Monodromy.FormalCompilation

open Turing

abbrev Stack := PartrecToTM2.K'
abbrev Symbol := PartrecToTM2.Γ'
abbrev Store := Option Symbol
abbrev Label2 := PartrecToTM2.Λ'
abbrev Alphabet := TM2to1.Γ' Stack (fun _ => Symbol)

instance stackFintype : Fintype Stack where
  elems := {.main, .rev, .aux, .stack}
  complete := by intro value; cases value <;> simp

/-- The parameter fixes the distinguished initial label of the compiled table. -/
@[nolint unusedArguments]
def Control1 (_source : ToPartrec.Code) : Type :=
  TM2to1.Λ' Stack (fun _ => Symbol) Label2 Store

variable (source : ToPartrec.Code)

instance control1Inhabited : Inhabited (Control1 source) :=
  ⟨TM2to1.Λ'.normal (PartrecToTM2.trNormal source PartrecToTM2.Cont'.halt)⟩

def machine1 : Control1 source → TM1.Stmt Alphabet (Control1 source) Store :=
  TM2to1.tr PartrecToTM2.tr

def Control0 : Type := TM1to0.Λ' (machine1 source)

instance control0Inhabited : Inhabited (Control0 source) :=
  inferInstanceAs (Inhabited (TM1to0.Λ' (machine1 source)))

def machine0 : TM0.Machine Alphabet (Control0 source) := TM1to0.tr (machine1 source)

noncomputable def labels1 : Finset (Control1 source) :=
  TM2to1.trSupp PartrecToTM2.tr (PartrecToTM2.codeSupp source PartrecToTM2.Cont'.halt)

theorem supports1 : TM1.Supports (machine1 source) (labels1 source) := by
  let _ : Inhabited Label2 := ⟨PartrecToTM2.trNormal source PartrecToTM2.Cont'.halt⟩
  exact TM2to1.tr_supports PartrecToTM2.tr
    (PartrecToTM2.tr_supports source PartrecToTM2.Cont'.halt)

noncomputable def labels0 : Finset (Control0 source) := TM1to0.trStmts (machine1 source) (labels1 source)

theorem supports0 : TM0.Supports (machine0 source) (labels0 source : Set (Control0 source)) :=
  TM1to0.tr_supports (machine1 source) (supports1 source)

noncomputable def finiteSupport : FiniteSupport.Support (machine0 source) :=
  ⟨labels0 source, supports0 source⟩

omit source in
/-- Every list of numeric arguments has an explicit word over the finite tape alphabet. -/
def tapeData (values : List ℕ) : List Alphabet :=
  TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList values)







def halt1 (values : List ℕ) : TM1.Cfg Alphabet (Control1 source) Store :=
  { (TM1.init (tapeData values) : TM1.Cfg Alphabet (Control1 source) Store) with l := none }





def halt0 (values : List ℕ) : TM0.Cfg Alphabet (Control0 source) :=
  TM1to0.trCfg (machine1 source) (halt1 source values)











end Monodromy.FormalCompilation

noncomputable section

namespace Monodromy.NativeTuring

open Turing CoupledContinuation

variable (a q : ℕ) [NeZero a] [NeZero q]

def source3 (machine : TM0.Machine (Fin a) (Fin q)) :
    Counter.Program 3 (Counter.TuringCompiler.size a q) :=
  Counter.TuringCompiler.program a q machine

def source2 (machine : TM0.Machine (Fin a) (Fin q)) :
    Counter.Program 2 (Counter.Compression.size (source3 a q machine)) :=
  Counter.Compression.program (source3 a q machine)

instance source3_nonempty : NeZero (Counter.TuringCompiler.size a q) := by
  have bound := (Counter.TuringCompiler.dispatch a q (0, 0)).isLt
  exact ⟨by omega⟩

instance source2_nonempty (machine : TM0.Machine (Fin a) (Fin q)) :
    NeZero (Counter.Compression.size (source3 a q machine)) := by
  have bound := (Counter.Compression.dispatch (source3 a q machine)
    (Counter.TuringCompiler.dispatch a q (0, 0))).isLt
  exact ⟨by omega⟩

/-- The only runtime is the existing finite native Word/Program interpreter. -/
def program (machine : TM0.Machine (Fin a) (Fin q)) :
    CoupledContinuation.Program (Counter.Compression.size (source3 a q machine) * 3) :=
  CounterContinuation.compile (source2 a q machine)

/-- Initialization composes the three already verified, faithful source encodings. -/
def iota (machine : TM0.Machine (Fin a) (Fin q)) (state : TM0.Cfg (Fin a) (Fin q)) : Memory :=
  CounterContinuation.encode
    (Counter.Compression.encode (source3 a q machine) (Counter.TuringCompiler.encode a q state))

























section FiniteTypes

variable {Γ Q : Type} [Fintype Γ] [Inhabited Γ] [Fintype Q] [Inhabited Q]

/-- Pointed finite enumeration changes only the presentation of the source alphabet and control. -/
def finiteProgram (machine : TM0.Machine Γ Q) :=
  program (Fintype.card Γ) (Fintype.card Q) (FiniteRenaming.machine machine)

def finiteIota (machine : TM0.Machine Γ Q) (state : TM0.Cfg Γ Q) : Memory :=
  iota (Fintype.card Γ) (Fintype.card Q) (FiniteRenaming.machine machine)
    (FiniteRenaming.configuration state)











end FiniteTypes

end Monodromy.NativeTuring

namespace Monodromy.NativeTuring

open Turing CoupledContinuation

section Marking

variable {m : ℕ} [NeZero m]

/-- A static finite table marks selected phase-zero source addresses. -/
def markTable (mark : Fin m → Bool) (index : Fin (m * 3)) : Bool :=
  let address := finProdFinEquiv.symm index
  if address.2 = 0 then mark address.1 else false

/-- Only the stopping table changes; every actual geometric word is retained. -/
def markedProgram (source : Counter.Program 2 m) (mark : Fin m → Bool) : Program (m * 3) :=
  ⟨(CounterContinuation.compile source).table, markTable mark⟩

/-- The boundary is an actual analytic finite-root observation of the native state. -/
def MarkedBoundary (source : Counter.Program 2 m) (mark : Fin m → Bool) (state : Memory) : Prop :=
  (markedProgram source mark).haltSignal state = 1













end Marking

variable (a q : ℕ) [NeZero a] [NeZero q]

/-- This finite PC flag marks exactly nested source dispatch cells, independently of storage. -/
def CounterMarked (machine : TM0.Machine (Fin a) (Fin q))
    (cell : Fin (Counter.Compression.size (source3 a q machine))) : Prop :=
  ∃ row : Counter.TuringCompiler.Row a q,
    cell = Counter.Compression.dispatch (source3 a q machine)
      (Counter.TuringCompiler.dispatch a q row)

def counterMark (machine : TM0.Machine (Fin a) (Fin q))
    (cell : Fin (Counter.Compression.size (source3 a q machine))) : Bool :=
  @decide (CounterMarked a q machine cell) (by unfold CounterMarked; infer_instance)

def boundaryProgram (machine : TM0.Machine (Fin a) (Fin q)) :
    Program (Counter.Compression.size (source3 a q machine) * 3) :=
  markedProgram (source2 a q machine) (counterMark a q machine)

/-- No integer labels or memory tests enter the native boundary definition. -/
def Boundary (machine : TM0.Machine (Fin a) (Fin q)) (state : Memory) : Prop :=
  (boundaryProgram a q machine).haltSignal state = 1









/-- Proof-side interior relation for the already defined two-counter table. -/
def CounterInternalStep (machine : TM0.Machine (Fin a) (Fin q))
    (first last : Counter.Configuration 2 (Counter.Compression.size (source3 a q machine))) : Prop :=
  Counter.step (source2 a q machine) first = some last ∧ ¬ CounterMarked a q machine first.pc

abbrev CounterInternalReaches (machine : TM0.Machine (Fin a) (Fin q)) :=
  Relation.ReflTransGen (CounterInternalStep a q machine)









/-- The native words execute unchanged; only the geometric boundary mark is excluded internally. -/
def InternalStep (machine : TM0.Machine (Fin a) (Fin q)) (first last : Memory) : Prop :=
  (program a q machine).step first = some last ∧ ¬ Boundary a q machine first

abbrev InternalReaches (machine : TM0.Machine (Fin a) (Fin q)) :=
  Relation.ReflTransGen (InternalStep a q machine)





/-- One actual native step, followed only by actual steps whose sources are unmarked. -/
def FirstReturn (machine : TM0.Machine (Fin a) (Fin q)) (first last : Memory) : Prop :=
  ∃ after, (program a q machine).step first = some after ∧ InternalReaches a q machine after last









/-- Leave the current return once, then execute the same words until the next internal root mark.
Its inputs contain no target state, decoded integer labels, or source transition oracle. -/
def macroStep (machine : TM0.Machine (Fin a) (Fin q)) (state : Memory) : Part (Option Memory) :=
  match (program a q machine).step state with
  | none => Part.some none
  | some next => ((boundaryProgram a q machine).eval next).map some




section FiniteTypes

variable {Γ Q : Type} [Fintype Γ] [Inhabited Γ] [Fintype Q] [Inhabited Q]

/-- The same first-return execution under pointed finite source renaming. -/
def finiteMacro (machine : TM0.Machine Γ Q) (state : Memory) : Part (Option Memory) :=
  macroStep (Fintype.card Γ) (Fintype.card Q) (FiniteRenaming.machine machine) state



end FiniteTypes



end Monodromy.NativeTuring

/-!
## Universal simulation with recoverable history

The ordinary two-counter compilation supplies only the source to be made
reversible. A fixed finite recording graph executes it, retaining the complete
configuration and history. Its four source registers are a proof intermediate;
reversibility-preserving compression to two native memory roots is separate.
-/

namespace Monodromy.RecordedTuring

open Turing

noncomputable section

variable (a q : ℕ) [NeZero a] [NeZero q]

abbrev size (machine : TM0.Machine (Fin a) (Fin q)) : ℕ :=
  Counter.Compression.size (NativeTuring.source3 a q machine)

def counterEncode (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) : Counter.Configuration 2 (size a q machine) :=
  Counter.Compression.encode (NativeTuring.source3 a q machine)
    (Counter.TuringCompiler.encode a q state)





end

end Monodromy.RecordedTuring

namespace Monodromy.ReversibleTuring

open Turing

noncomputable section

variable (a q : ℕ) [NeZero a] [NeZero q]

/-- A fixed finite reversible graph realizes the source; its four registers are an intermediate code. -/
def table (machine : TM0.Machine (Fin a) (Fin q)) :
    Counter.Reversible.Table 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine))
      (Counter.Reversible.Recording.edges (NativeTuring.source2 a q machine)) :=
  Counter.Reversible.Recording.table (NativeTuring.source2 a q machine)

def encode (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine)) :=
  Counter.Reversible.Recording.encode (RecordedTuring.counterEncode a q machine state) history







/-- The compiled machine's finite dispatch marks are lifted to recording ports. -/
def Boundary (machine : TM0.Machine (Fin a) (Fin q))
    (state : Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine))) : Prop :=
  Counter.Reversible.Recording.Marked (NativeTuring.counterMark a q machine) state

instance boundary_decidable (machine : TM0.Machine (Fin a) (Fin q))
    (state : Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine))) :
    Decidable (Boundary a q machine state) := by
  unfold Boundary
  infer_instance











/-- The same graph is stopped at the chosen finite dispatch marks. -/
def boundaryTransition (machine : TM0.Machine (Fin a) (Fin q))
    (state : Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine))) :=
  if Boundary a q machine state then none else Counter.Reversible.step (table a q machine) state





/-- Execute the fixed graph once, then stop it at a finite control mark or a graph dead end. -/
def macroStep (machine : TM0.Machine (Fin a) (Fin q))
    (state : Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine))) :
    Part (Option (Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine)))) :=
  match Counter.Reversible.step (table a q machine) state with
  | none => Part.some none
  | some next => (StateTransition.eval (boundaryTransition a q machine) next).map some







def Related (machine : TM0.Machine (Fin a) (Fin q))
    (original : TM0.Cfg (Fin a) (Fin q))
    (compiled : Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine))) : Prop :=
  ∃ history, encode a q machine original history = compiled











end

end Monodromy.ReversibleTuring

/-!
## Recoverable-history simulation on two counters
-/

noncomputable section

namespace Monodromy.ReversibleTuring.Compression

open Turing Counter.Reversible

/-- Four source registers use one instance of the uniform finite prime code. -/
def basis : PrimeCode.Basis 4 where
  prime := ![2, 3, 5, 7]
  isPrime := by intro index; fin_cases index <;> decide
  distinct := by
    intro first second same
    fin_cases first <;> fin_cases second <;> simp_all

variable (a q : ℕ) [NeZero a] [NeZero q]

theorem source_deterministic (machine : TM0.Machine (Fin a) (Fin q)) :
    Deterministic (ReversibleTuring.table a q machine) :=
  Recording.deterministic (NativeTuring.source2 a q machine)

theorem source_targetCompatible (machine : TM0.Machine (Fin a) (Fin q)) :
    TargetCompatible (ReversibleTuring.table a q machine) :=
  Recording.targetCompatible (NativeTuring.source2 a q machine)

abbrev size (machine : TM0.Machine (Fin a) (Fin q)) : ℕ :=
  PrimeCompression.size basis (ReversibleTuring.table a q machine)
    (source_deterministic a q machine) (source_targetCompatible a q machine)

abbrev edges (machine : TM0.Machine (Fin a) (Fin q)) : ℕ :=
  PrimeCompression.rawEdges basis (ReversibleTuring.table a q machine)

/-- A fixed finite graph on two counters, with no source-step interpreter in its definition. -/
def table (machine : TM0.Machine (Fin a) (Fin q)) : Table 2 (size a q machine) (edges a q machine) :=
  PrimeCompression.table basis (ReversibleTuring.table a q machine)
    (source_deterministic a q machine) (source_targetCompatible a q machine)

/-- The entire source configuration and its recoverable history are retained. -/
def encode (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) : State 2 (size a q machine) :=
  PrimeCompression.encode basis (ReversibleTuring.table a q machine)
    (source_deterministic a q machine) (source_targetCompatible a q machine)
    (PrimeCompression.toNatural (ReversibleTuring.encode a q machine state history))

theorem deterministic (machine : TM0.Machine (Fin a) (Fin q)) :
    Deterministic (table a q machine) :=
  PrimeCompression.deterministic basis (ReversibleTuring.table a q machine)
    (source_deterministic a q machine) (source_targetCompatible a q machine)

theorem targetCompatible (machine : TM0.Machine (Fin a) (Fin q)) :
    TargetCompatible (table a q machine) :=
  PrimeCompression.targetCompatible basis (ReversibleTuring.table a q machine)
    (source_deterministic a q machine) (source_targetCompatible a q machine)







/-- The original recording boundary depends only on its finite control position. -/
def sourceMark (machine : TM0.Machine (Fin a) (Fin q))
    (position : Fin (Recording.size (RecordedTuring.size a q machine))) : Bool :=
  decide (Recording.Marked (n := 2) (NativeTuring.counterMark a q machine)
    (position, fun _ => 0))





/-- Marked source boundaries inside the actual compressed control graph. -/
def Boundary (machine : TM0.Machine (Fin a) (Fin q))
    (state : State 2 (size a q machine)) : Prop :=
  PrimeCompression.Marked basis (ReversibleTuring.table a q machine)
    (source_deterministic a q machine) (source_targetCompatible a q machine)
    (sourceMark a q machine) state

instance boundary_decidable (machine : TM0.Machine (Fin a) (Fin q))
    (state : State 2 (size a q machine)) : Decidable (Boundary a q machine state) := by
  unfold Boundary PrimeCompression.Marked
  refine @Fintype.decidableExistsFintype
    (Fin (Recording.size (RecordedTuring.size a q machine))) _ ?_ inferInstance
  intro position
  dsimp only
  exact @instDecidableAnd _ _ (instDecidableEqFin _ _ _) (instDecidableEqBool _ _)

/-- The marker used by a native finite-root table has no memory input. -/
def mark (machine : TM0.Machine (Fin a) (Fin q)) (position : Fin (size a q machine)) : Bool :=
  decide (Boundary a q machine (position, fun _ => 0))



















def Related (machine : TM0.Machine (Fin a) (Fin q))
    (original : TM0.Cfg (Fin a) (Fin q)) (compiled : State 2 (size a q machine)) : Prop :=
  ∃ history, encode a q machine original history = compiled











end Monodromy.ReversibleTuring.Compression

end

/-!
## Reversible universality by actual path lifting
-/

noncomputable section

namespace Monodromy.ReversibleNativeTuring

open Turing CoupledContinuation ReversibleTuring

variable (a q : ℕ) [NeZero a] [NeZero q]

instance size_nonzero (machine : TM0.Machine (Fin a) (Fin q)) :
    NeZero (Compression.size a q machine) := by
  constructor
  have bound := (Compression.encode a q machine (TM0.init [] : TM0.Cfg (Fin a) (Fin q)) 0).1.isLt
  omega

/-- The same five geometric primitives execute the complete compressed finite table. -/
def program (machine : TM0.Machine (Fin a) (Fin q)) :
    Program (11 * (Compression.size a q machine + Compression.edges a q machine)) :=
  ReversibleCompilation.haltingProgram (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)

/-- Complete source configurations and histories occupy the original three-root fiber. -/
def iota (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) : Memory :=
  ReversibleCompilation.iota (e := Compression.edges a q machine) (Compression.encode a q machine state history)



/-- The same native words, with finite root marks for complete Turing steps. -/
def boundaryProgram (machine : TM0.Machine (Fin a) (Fin q)) :
    Program (11 * (Compression.size a q machine + Compression.edges a q machine)) :=
  ReversibleCompilation.markedProgram (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)
    (Compression.mark a q machine)

def Boundary (machine : TM0.Machine (Fin a) (Fin q)) (state : Memory) : Prop :=
  (boundaryProgram a q machine).haltSignal state = 1



def FirstReturn (machine : TM0.Machine (Fin a) (Fin q)) (first last : Memory) : Prop :=
  ReversibleCompilation.NativeFirstReturn (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)
    (Compression.mark a q machine) first last







def Related (machine : TM0.Machine (Fin a) (Fin q))
    (original : TM0.Cfg (Fin a) (Fin q)) (native : Memory) : Prop :=
  ∃ history, iota a q machine original history = native









/-- The inverse is another fixed word table on the same fiber and with the same five primitives. -/
def reverseProgram (machine : TM0.Machine (Fin a) (Fin q)) :
    Program (11 * (Compression.size a q machine + Compression.edges a q machine)) :=
  ReversibleCompilation.reverseProgram (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)





def executionEquiv (machine : TM0.Machine (Fin a) (Fin q)) : Memory ≃ Memory :=
  ReversibleCompilation.executionEquiv (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)





/-- Native execution determines both departure and the next internal stopping boundary. -/
def macroStep (machine : TM0.Machine (Fin a) (Fin q)) (state : Memory) : Part (Option Memory) :=
  ReversibleCompilation.nativeMacro (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)
    (Compression.mark a q machine) state

/-- The inverse executes its own fixed word table and the same finite boundary observation. -/
def reverseMacro (machine : TM0.Machine (Fin a) (Fin q)) (state : Memory) : Part Memory :=
  Program.reverseReturn (reverseProgram a q machine) (boundaryProgram a q machine) state




















end Monodromy.ReversibleNativeTuring

end


