-- Prove2me | Definitions.Def_NearLinearRSP_TwoResources_Implementation_Foundations
-- name    : NearLinearRSP_TwoResources_Implementation_Foundations
-- status  : Definition
-- author  : @k-variant
-- created : 2026-11-15T18:21:43.489718+00:00
-- url     : https://prove2.me/theorems/f6ad531f-3ecb-45b2-a289-305cfabe0cb1
-- title:
--   RSP implementation data, commands and representation predicates
-- statement:
--   The implementation data and representation predicates for the deterministic two-resource restricted shortest-path algorithm: structured machine commands, tournament records, active-vertex indexing, shortest-tree and dynamic-table layouts, Poisson expectation state, output records, and retrieval state. Quantified property predicates specify the initialization and expectation correctness interface. The supporting constructor lemmas establish capacity, active-vertex, positive-length and address bounds needed to construct these data; they introduce no unproved assumptions.
-- source:
--   A Deterministic Near-Linear Time Approximation Algorithm for Restricted Shortest Paths in Directed Graphs, Theorem 1 (p. 3), Section 4 (pp. 6–8), and Observation A.1 (p. 14). Derived initialization, implementation and expectation lemmas for the two-resource formalization: https://prove2.me/missions/A_Deterministic_Near-Linear_Time_Approximation_Algorithm_for_Restricted_Shortest_Paths_in_Directed_Graphs

import Definitions.Def_NearLinearRSP_TwoResources_Inner
import Definitions.Def_NearLinearRSP_TwoResources_Instance
import Definitions.Def_NearLinearRSP_TwoResources_Machine
import Definitions.Def_NearLinearRSP_TwoResources_Outer
import Definitions.Def_NearLinearRSP_TwoResources_RAM
import Definitions.Def_NearLinearRSP_TwoResources_Retrieval
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

universe u_1

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources
namespace Mission

def countdownProgram : Program :=
  [ .inputReal 0 0,
    .realConst 1 4,
    .realOp .div 0 0 1,
    .realOp .mul 0 0 0,
    .realConst 1 512,
    .realOp .div 0 1 0,
    .realConst 1 1,
    .realConst 2 0,
    .natConst 1 1,
    .natConst 2 0,
    .realBranch .lt 2 0 11 14,
    .realOp .add 2 2 1,
    .natOp .add 2 2 1,
    .jump 10,
    .natConst 0 0,
    .storeNat 0 2,
    .halt ]

noncomputable def countdownLoopState (x : ℝ) (k : ℕ) : RAMState where
  pc := 10
  halted := false
  nr := Function.update (Function.update (fun _ => 0) 1 1) 2 k
  rr := Function.update (Function.update (Function.update (fun _ => 0) 0 x) 1 1) 2 k
  nm := fun _ => 0
  rm := fun _ => 0

noncomputable def countdownFinalState (x : ℝ) : RAMState :=
  { countdownLoopState x (Nat.ceil x) with
    pc := 16
    halted := true
    nr := Function.update (countdownLoopState x (Nat.ceil x)).nr 0 0
    nm := Function.update (fun _ => 0) 0 (Nat.ceil x) }

end Mission
end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission
namespace Structured

structure Store where
  nr : ℕ → ℕ
  rr : ℕ → ℝ
  nm : ℕ → ℕ
  rm : ℕ → ℝ

def Store.at (s : Store) (pc : ℕ) : RAMState :=
  ⟨pc, false, s.nr, s.rr, s.nm, s.rm⟩

def Store.ofRAM (s : RAMState) : Store := ⟨s.nr, s.rr, s.nm, s.rm⟩

def initialStore : Store := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

noncomputable def queryStore (snapshot : RAMState) (target : ℕ) : Store :=
  ⟨Function.update (fun _ => 0) 0 target, fun _ => 0, snapshot.nm, snapshot.rm⟩

def IsAtom : RAMInstr → Prop
  | .realBranch .. | .natBranch .. | .jump .. | .halt => False
  | _ => True

abbrev Atom := { i : RAMInstr // IsAtom i }

noncomputable def Atom.eval (a : Atom) (input : RAMInput) (s : Store) : Store :=
  Store.ofRAM (ramStep [a.val] input (s.at 0))

inductive Guard where
  | real (test : Test) (lhs rhs : ℕ)
  | nat (test : Test) (lhs rhs : ℕ)

noncomputable def Guard.eval (g : Guard) (s : Store) : Bool :=
  match g with
  | .real test a b => realTest test (s.rr a) (s.rr b)
  | .nat test a b => natTest test (s.nr a) (s.nr b)

def Guard.instr (g : Guard) (yes no : ℕ) : RAMInstr :=
  match g with
  | .real test a b => .realBranch test a b yes no
  | .nat test a b => .natBranch test a b yes no

inductive Cmd where
  | skip
  | atom (a : Atom)
  | seq (a b : Cmd)
  | branch (g : Guard) (a b : Cmd)
  | loop (g : Guard) (body : Cmd)

def Cmd.size : Cmd → ℕ
  | .skip => 0
  | .atom _ => 1
  | .seq a b => a.size + b.size
  | .branch _ a b => 1 + a.size + 1 + b.size
  | .loop _ a => 1 + a.size + 1

def Cmd.compile : Cmd → ℕ → Program
  | .skip, _ => []
  | .atom a, _ => [a.val]
  | .seq a b, base => a.compile base ++ b.compile (base + a.size)
  | .branch g a b, base =>
      [g.instr (base + 1) (base + 1 + a.size + 1)] ++
        a.compile (base + 1) ++
        [.jump (base + (1 + a.size + 1 + b.size))] ++
        b.compile (base + 1 + a.size + 1)
  | .loop g body, base =>
      [g.instr (base + 1) (base + (1 + body.size + 1))] ++
        body.compile (base + 1) ++ [.jump base]

inductive Run (input : RAMInput) : Cmd → Store → Store → ℕ → Prop
  | skip (s : Store) : Run input .skip s s 0
  | atom (a : Atom) (s : Store) : Run input (.atom a) s (a.eval input s) 1
  | seq {a b : Cmd} {s u t : Store} {n m : ℕ} :
      Run input a s u n → Run input b u t m → Run input (.seq a b) s t (n + m)
  | branchTrue {g : Guard} {a b : Cmd} {s t : Store} {n : ℕ} :
      g.eval s = true → Run input a s t n → Run input (.branch g a b) s t (1 + n + 1)
  | branchFalse {g : Guard} {a b : Cmd} {s t : Store} {n : ℕ} :
      g.eval s = false → Run input b s t n → Run input (.branch g a b) s t (1 + n)
  | loopFalse {g : Guard} {body : Cmd} {s : Store} :
      g.eval s = false → Run input (.loop g body) s s 1
  | loopTrue {g : Guard} {body : Cmd} {s u t : Store} {n m : ℕ} :
      g.eval s = true → Run input body s u n → Run input (.loop g body) u t m →
      Run input (.loop g body) s t (1 + n + 1 + m)

def loopCost (bodyCost : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => 1 + bodyCost (k + 1) + 1 + loopCost bodyCost k

def CodeAt (p : Program) (base : ℕ) (code : Program) : Prop :=
  ∀ i < code.length, p[base + i]? = code[i]?

def Cmd.program (c : Cmd) : Program := c.compile 0 ++ [.halt]

end Structured
end NearLinearRSP.TwoResources.Mission
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Queue

noncomputable def choose {α : Type} (key : α → ℝ) : Option α → Option α → Option α
  | none, b => b
  | a, none => a
  | some a, some b => if key b < key a then some b else some a

noncomputable def winner {α : Type} (key : α → ℝ) (xs : List α) : Option α :=
  xs.foldl (fun a b => choose key a (some b)) none

inductive Tree (α : Type) : ℕ → Type where
  | leaf (value : Option α) : Tree α 0
  | node {h : ℕ} (left right : Tree α h) : Tree α (h + 1)

def Tree.leaves {α : Type} : {h : ℕ} → Tree α h → List α
  | _, .leaf x => x.toList
  | _, .node l r => l.leaves ++ r.leaves

noncomputable def Tree.champion {α : Type} (key : α → ℝ) : {h : ℕ} → Tree α h → Option α
  | _, .leaf x => x
  | _, .node l r => choose key (l.champion key) (r.champion key)

inductive Path : ℕ → Type where
  | done : Path 0
  | left {h : ℕ} : Path h → Path (h + 1)
  | right {h : ℕ} : Path h → Path (h + 1)

def Tree.replace {α : Type} : {h : ℕ} → Tree α h → Path h → Option α → Tree α h
  | _, .leaf _, .done, x => .leaf x
  | _, .node l r, .left p, x => .node (l.replace p x) r
  | _, .node l r, .right p, x => .node l (r.replace p x)

def Path.index : {h : ℕ} → Path h → ℕ
  | _, .done => 0
  | _, .left p => p.index
  | h + 1, .right p => 2 ^ h + p.index

theorem capacity_bounds (n : ℕ) (hn : 0 < n) :
    n ≤ 2 ^ Nat.clog 2 n ∧ 2 ^ Nat.clog 2 n < 2 * n := by
  constructor
  · exact Nat.le_pow_clog (by decide) n
  · by_cases hn1 : n = 1
    · subst n; simp
    · have hc : 0 < Nat.clog 2 n := Nat.clog_pos (by decide) (by omega)
      have hp : 2 ^ (Nat.clog 2 n - 1) < n :=
        (Nat.lt_clog_iff_pow_lt (by decide)).mp (by omega)
      have he : Nat.clog 2 n = Nat.clog 2 n - 1 + 1 := by omega
      rw [he, pow_succ]
      omega

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Queue
open Structured

def atoms : List Atom → Cmd
  | [] => .skip
  | a :: as => .seq (.atom a) (atoms as)

noncomputable def evalAtoms (input : RAMInput) (as : List Atom) (s : Store) : Store :=
  as.foldl (fun t a => a.eval input t) s

structure Record where
  token : ℕ
  key : ℝ

noncomputable def merge (a b : Record) : Record :=
  if b.token = 0 then a else if a.token = 0 then b else if b.key < a.key then b else a

def Record.decode (a : Record) : Option Record := if a.token = 0 then none else some a

def readRecord (s : Store) (address : ℕ) : Record := ⟨s.nm address, s.rm address⟩

def writeRecord (s : Store) (address : ℕ) (r : Record) : Store :=
  { s with
    nm := Function.update s.nm address r.token
    rm := Function.update s.rm address r.key }

def loadChildren : List Atom :=
  [ ⟨.natOp .add 5 0 0, by trivial⟩,
    ⟨.natOp .add 6 5 4, by trivial⟩,
    ⟨.natOp .add 7 1 5, by trivial⟩,
    ⟨.loadNat 8 7, by trivial⟩,
    ⟨.loadReal 0 7, by trivial⟩,
    ⟨.natOp .add 7 1 6, by trivial⟩,
    ⟨.loadNat 9 7, by trivial⟩,
    ⟨.loadReal 1 7, by trivial⟩,
    ⟨.natOp .add 7 1 0, by trivial⟩ ]

def storeLeft : List Atom :=
  [⟨.storeNat 7 8, by trivial⟩, ⟨.storeReal 7 0, by trivial⟩]

def storeRight : List Atom :=
  [⟨.storeNat 7 9, by trivial⟩, ⟨.storeReal 7 1, by trivial⟩]

def selectChild : Cmd :=
  .branch (.nat .eq 9 3) (atoms storeLeft)
    (.branch (.nat .eq 8 3) (atoms storeRight)
      (.branch (.real .lt 1 0) (atoms storeRight) (atoms storeLeft)))

def refreshNode : Cmd := .seq (atoms loadChildren) selectChild

noncomputable def loaded (s : Store) : Store :=
  let left := s.nr 1 + (s.nr 0 + s.nr 0)
  let right := s.nr 1 + (s.nr 0 + s.nr 0 + s.nr 4)
  { s with
    nr := Function.update (Function.update (Function.update (Function.update
      (Function.update s.nr 5 (s.nr 0 + s.nr 0)) 6 (s.nr 0 + s.nr 0 + s.nr 4))
      8 (s.nm left)) 9 (s.nm right)) 7 (s.nr 1 + s.nr 0)
    rr := Function.update (Function.update s.rr 0 (s.rm left)) 1 (s.rm right) }

noncomputable def refreshed (s : Store) : Store :=
  writeRecord (loaded s) (s.nr 1 + s.nr 0)
    (merge (readRecord s (s.nr 1 + (s.nr 0 + s.nr 0)))
      (readRecord s (s.nr 1 + (s.nr 0 + s.nr 0 + s.nr 4))))

def parentHop : List Atom :=
  [⟨.natOp .add 7 2 0, by trivial⟩, ⟨.loadNat 0 7, by trivial⟩]

noncomputable def advanced (s : Store) : Store :=
  { s with
    nr := Function.update
      (Function.update s.nr 7 (s.nr 2 + s.nr 0)) 0 (s.nm (s.nr 2 + s.nr 0)) }

def repairBody : Cmd := .seq refreshNode (atoms parentHop)

def repairAncestors : Cmd := .loop (.nat .lt 3 0) repairBody

noncomputable def repairStep (s : Store) : Store := advanced (refreshed s)

def hops (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else hops (n / 2) + 1
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

def ParentLayout (capacity : ℕ) (s : Store) : Prop :=
  s.nr 0 < capacity ∧ s.nr 1 + capacity ≤ s.nr 2 ∧ s.nr 3 = 0 ∧
    ∀ u < capacity, s.nm (s.nr 2 + u) = u / 2

def ancestors (n : ℕ) : List ℕ :=
  if h : n = 0 then [] else n :: ancestors (n / 2)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

def Ready (capacity : ℕ) (truth : ℕ → Record) (s : Store) : Prop :=
  ∀ v < capacity, v ∉ ancestors (s.nr 0) → readRecord s (s.nr 1 + v) = truth v

def Coherent (capacity : ℕ) (truth : ℕ → Record) : Prop :=
  ∀ u, 0 < u → u + u + 1 < capacity →
    truth u = merge (truth (u + u)) (truth (u + u + 1))

def writeLeaf : List Atom :=
  [⟨.natOp .add 7 1 0, by trivial⟩,
    ⟨.storeNat 7 10, by trivial⟩,
    ⟨.storeReal 7 2, by trivial⟩]

noncomputable def leafWritten (s : Store) : Store :=
  writeRecord { s with nr := Function.update s.nr 7 (s.nr 1 + s.nr 0) }
    (s.nr 1 + s.nr 0) ⟨s.nr 10, s.rr 2⟩

noncomputable def updateStart (s : Store) : Store := advanced (leafWritten s)

def updateLeaf : Cmd :=
  .seq (atoms writeLeaf) (.seq (atoms parentHop) repairAncestors)

def WinnerFrame (W capacity : ℕ) (s out : Store) : Prop :=
  ∀ a, a < W ∨ W + capacity ≤ a → out.nm a = s.nm a ∧ out.rm a = s.rm a

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Structured

def Cmd.atoms : List Atom → Cmd
  | [] => .skip
  | a :: as => .seq (.atom a) (Cmd.atoms as)

noncomputable def evalAtoms (input : RAMInput) : List Atom → Store → Store
  | [], s => s
  | a :: as, s => evalAtoms input as (a.eval input s)

end NearLinearRSP.TwoResources.Mission.Structured
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def treeLeafAtoms : List Atom :=
  [ ⟨.natOp .add 175 171 172, trivial⟩,
    ⟨.loadNat 175 175, trivial⟩,
    ⟨.natOp .add 0 170 172, trivial⟩,
    ⟨.natOp .add 10 172 4, trivial⟩,
    ⟨.natOp .add 176 175 175, trivial⟩,
    ⟨.natOp .add 176 176 176, trivial⟩,
    ⟨.natConst 177 16, trivial⟩,
    ⟨.natOp .add 174 177 176, trivial⟩,
    ⟨.natOp .add 174 174 173, trivial⟩,
    ⟨.storeNat 174 3, trivial⟩ ]

def treeLeafKey : Cmd :=
  .branch (.nat .eq 175 123) (.atom ⟨.realConst 2 0, trivial⟩)
    (.atom ⟨.realCopy 2 170, trivial⟩)

def treeLeafPrepare : Cmd := .seq (Cmd.atoms treeLeafAtoms) treeLeafKey

def treeInitializeLeaf : Cmd := .seq treeLeafPrepare Queue.updateLeaf

def treeLeafPrepared (s : Store) : Store :=
  let v := s.nm (s.nr 171 + s.nr 172)
  let addr := targetAddress v + s.nr 173
  { s with
    nr := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update s.nr 175 v) 0 (s.nr 170 + s.nr 172))
      10 (s.nr 172 + s.nr 4)) 176 (4 * v)) 177 16) 174 addr
    nm := Function.update s.nm addr (s.nr 3) }

noncomputable def treeLeafReady (s : Store) : Store :=
  { treeLeafPrepared s with
    rr := Function.update s.rr 2
      (if s.nm (s.nr 171 + s.nr 172) = s.nr 123 then 0 else s.rr 170) }

def treeSeedWrite : List Atom :=
  [ ⟨.natOp .add 178 13 172, trivial⟩,
    ⟨.storeReal 178 2, trivial⟩,
    ⟨.natOp .add 172 172 4, trivial⟩ ]

def treeSeedBody : Cmd := .seq treeLeafPrepare (.atoms treeSeedWrite)

def treeSeed : Cmd :=
  .seq (.atom ⟨.natConst 172 0, trivial⟩) (.loop (.nat .lt 172 12) treeSeedBody)

noncomputable def treeSeedStep (input : RAMInput) (s : Store) : Store :=
  evalAtoms input treeSeedWrite (treeLeafReady s)

noncomputable def treeSeedSteps (input : RAMInput) : ℕ → Store → Store
  | 0, s => s
  | n + 1, s => treeSeedSteps input n (treeSeedStep input s)

def treeSeedStart (s : Store) : Store := { s with nr := Function.update s.nr 172 0 }

structure TreeSeedInv (xs : List ℕ) (A R source off : ℕ) (top : ℝ)
    (k : ℕ) (s : Store) : Prop where
  count_bound : k ≤ xs.length
  counter : s.nr 172 = k
  length_reg : s.nr 12 = xs.length
  array_reg : s.nr 171 = A
  key_reg : s.nr 13 = R
  source_reg : s.nr 123 = source
  offset_reg : s.nr 173 = off
  zero_reg : s.nr 3 = 0
  one_reg : s.nr 4 = 1
  top_reg : s.rr 170 = top
  array : ∀ j v, xs[j]? = some v → s.nm (A + j) = v
  key : ∀ j v, xs[j]? = some v → j < k →
    s.rm (R + j) = if v = source then 0 else top
  parent : ∀ j v, xs[j]? = some v → j < k → s.nm (targetAddress v + off) = 0

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Structured

def Atom.natWrites (a : Atom) : Finset ℕ :=
  match a.val with
  | .natConst d _ | .natCopy d _ | .natOp _ d _ _ | .loadNat d _ | .inputNat d _ => {d}
  | _ => ∅

def Atom.realWrites (a : Atom) : Finset ℕ :=
  match a.val with
  | .realConst d _ | .realCopy d _ | .realOp _ d _ _ | .exp d _ |
      .loadReal d _ | .inputReal d _ => {d}
  | _ => ∅

def Atom.writesNatMemory (a : Atom) : Bool :=
  match a.val with | .storeNat .. => true | _ => false

def Atom.writesRealMemory (a : Atom) : Bool :=
  match a.val with | .storeReal .. => true | _ => false

def Cmd.natWrites : Cmd → Finset ℕ
  | .skip => ∅
  | .atom a => a.natWrites
  | .seq a b | .branch _ a b => a.natWrites ∪ b.natWrites
  | .loop _ body => body.natWrites

def Cmd.realWrites : Cmd → Finset ℕ
  | .skip => ∅
  | .atom a => a.realWrites
  | .seq a b | .branch _ a b => a.realWrites ∪ b.realWrites
  | .loop _ body => body.realWrites

def Cmd.writesNatMemory : Cmd → Bool
  | .skip => false
  | .atom a => a.writesNatMemory
  | .seq a b | .branch _ a b => a.writesNatMemory || b.writesNatMemory
  | .loop _ body => body.writesNatMemory

def Cmd.writesRealMemory : Cmd → Bool
  | .skip => false
  | .atom a => a.writesRealMemory
  | .seq a b | .branch _ a b => a.writesRealMemory || b.writesRealMemory
  | .loop _ body => body.writesRealMemory

end NearLinearRSP.TwoResources.Mission.Structured
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Queue

noncomputable def heapTruth (B : ℕ) (leaf : ℕ → Record) (v : ℕ) : Record :=
  if h : 0 < v ∧ v < B then
    merge (heapTruth B leaf (v + v)) (heapTruth B leaf (v + v + 1))
  else leaf v
termination_by B - v
decreasing_by all_goals omega

def leafRecords (leaf : ℕ → Record) (start count : ℕ) : List Record :=
  ((List.range count).map (fun i => leaf (start + i))).filterMap Record.decode

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory
namespace RSP.Tails

noncomputable def mass (r : ℝ≥0) (n : ℕ) : ℝ :=
  Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)

noncomputable def countdown (k : ℕ) (ε : ℝ) : ℕ :=
  ⌈128 * (k : ℝ) / ε ^ 2⌉₊

end RSP.Tails
end

set_option autoImplicit false
section
namespace NearLinearRSP.TwoResources
open scoped BigOperators

def TableRange (T : Table) : Prop :=
  ∀ v i j, 0 ≤ (T v i j).value ∧ (T v i j).value ≤ 1

def LayerRange (S : LayerState) : Prop :=
  TableRange S.table ∧ ∀ v, 0 ≤ S.keys v ∧ S.keys v ≤ 1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem activeVertices_source_mem (I : Instance) : I.source ∈ activeVertices I := by
  simp [activeVertices]

theorem standalone_Mission_QueueStructure__eraseDups_nat_nodup (xs : List ℕ) : xs.eraseDups.Nodup := by
  have hloop : ∀ ys acc : List ℕ, acc.Nodup →
      (List.eraseDupsBy.loop (· == ·) ys acc).Nodup := by
    intro ys
    induction ys with
    | nil => intro acc h; simpa [List.eraseDupsBy.loop] using h
    | cons y ys ih =>
        intro acc h
        unfold List.eraseDupsBy.loop
        split
        · exact ih acc h
        · rename_i hn
          apply ih
          rw [List.nodup_cons]
          refine ⟨?_, h⟩
          intro hm
          have ha : acc.any (fun x => y == x) = true := by
            apply List.any_eq_true.mpr
            exact ⟨y, hm, by simp⟩
          simp [ha] at hn
  exact hloop xs [] (by simp)

theorem activeVertices_nodup (I : Instance) : (activeVertices I).Nodup := by
  exact standalone_Mission_QueueStructure__eraseDups_nat_nodup _

noncomputable def relaxAll (A : InnerInput) (i j u : ℕ) (S : LayerState) : LayerState :=
  A.I.graph.edges.foldl (relaxEdge A i j u) S

noncomputable def queueRun (A : InnerInput) (i j n : ℕ) (S : LayerState) : LayerState :=
  (List.range n).foldl (fun U _ => popLayer A i j U) S

def PoppedSync (A : InnerInput) (i j : ℕ) (S : LayerState) : Prop :=
  ∀ v ∈ activeVertices A.I, v ∉ S.queue → (S.table v i j).value = S.keys v

def LayerFutureBound (A : InnerInput) (i j : ℕ) (S : LayerState) : Prop :=
  ∀ v ∈ S.queue, ∀ a b : ℕ, a ≠ 0 ∨ b ≠ 0 →
    S.keys v ≤ dpValue A S.table v (i + a) (j + b)

noncomputable def settleState (S : LayerState) (i j u : ℕ) : LayerState :=
  { S with
    table := putCell S.table u i j ⟨S.keys u, S.parents u, S.nextRank⟩
    queue := S.queue.erase u
    nextRank := S.nextRank + 1 }

noncomputable def pickedVertex (S : LayerState) : ℕ :=
  firstMin S.keys S.queue (S.queue.headD 0)

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

structure PathReduction (P Q : List ℕ) : Prop where
  head : Q.head? = P.head?
  last : Q.getLast? = P.getLast?
  nodup : Q.Nodup
  subset : Q ⊆ P
  chain : ∀ R : ℕ → ℕ → Prop, P.IsChain R → Q.IsChain R
  weight : ∀ w : ℕ → ℕ → ℝ≥0, pathWeight w Q ≤ pathWeight w P

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

noncomputable def optionDist : Option ℝ → WithTop ℝ
  | none => ⊤
  | some d => (d : WithTop ℝ)

noncomputable def treeDist (T : ShortestTree) (v : ℕ) : WithTop ℝ :=
  optionDist (T v).distance

noncomputable def treePick (S : TreeQueue) : ℕ :=
  S.queue.foldl (fun x y =>
    if distanceLess (S.tree y).distance (S.tree x).distance then y else x)
    (S.queue.headD 0)

noncomputable def treeRelaxAll (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) : TreeQueue :=
  I.graph.edges.foldl (treeRelax I allow w u) S

noncomputable def treeSettle (S : TreeQueue) (u : ℕ) : TreeQueue :=
  { tree := Function.update S.tree u { S.tree u with rank := S.rank }
    queue := S.queue.erase u
    rank := S.rank + 1 }

noncomputable def treeRun (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (n : ℕ) (S : TreeQueue) : TreeQueue :=
  (List.range n).foldl (fun U _ => treePop I allow w U) S

noncomputable def treeInitial (I : Instance) : TreeQueue :=
  { tree := fun v => ⟨if v = I.source then some 0 else none, none, 0⟩
    queue := activeVertices I
    rank := 0 }

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

structure TreePolicy (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) : Prop where
  active : ∀ v d, (S.tree v).distance = some d → v ∈ activeVertices I
  settled : ∀ v ∈ activeVertices I, v ∉ S.queue → (S.tree v).rank < S.rank
  finite : ∀ v d, (S.tree v).distance = some d → v = I.source ∨
    ∃ u a, (S.tree v).parent = some u ∧ (S.tree u).distance = some a ∧
      d = a + w u v ∧ (u,v) ∈ I.graph.edges ∧ allow u v = true ∧
      u ∉ S.queue ∧ (S.tree u).rank < S.rank ∧
      (v ∉ S.queue → (S.tree u).rank < (S.tree v).rank)
  balance : S.rank + S.queue.length = (activeVertices I).length

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

def TreeSeparation (I : Instance) (S : TreeQueue) : Prop :=
  ∀ u ∈ activeVertices I, u ∉ S.queue →
    ∀ v ∈ S.queue, treeDist S.tree u ≤ treeDist S.tree v

def TreeBellman (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) : Prop :=
  ∀ u ∈ activeVertices I, u ∉ S.queue →
    ∀ v, (u,v) ∈ I.graph.edges → allow u v = true →
      treeDist S.tree v ≤ treeDist S.tree u + (w u v : WithTop ℝ)

theorem activeVertices_valid (I : Instance) (v : ℕ) (hv : v ∈ activeVertices I) :
    v < I.graph.n := by
  simp only [activeVertices, List.mem_eraseDups, List.mem_cons, List.mem_flatMap] at hv
  rcases hv with rfl | ⟨e, he, hv⟩
  · exact I.source_valid
  · have h := I.graph.endpoints e he
    simp at hv
    rcases hv with rfl | rfl
    · exact h.1
    · exact h.2

theorem activeVertices_length_le_vertices (I : Instance) :
    (activeVertices I).length ≤ I.graph.n := by
  have hsub : activeVertices I ⊆ List.range I.graph.n := by
    intro v hv
    exact List.mem_range.mpr (activeVertices_valid I v hv)
  simpa using (activeVertices_nodup I).length_le_of_subset hsub

theorem activeVertices_length_pos (I : Instance) : 0 < (activeVertices I).length := by
  exact List.length_pos_of_mem (activeVertices_source_mem I)

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

noncomputable def edgeWeightSum (I : Instance) (w : ℕ → ℕ → ℝ≥0) : ℝ :=
  (I.graph.edges.map (fun e => (w e.1 e.2 : ℝ))).sum

noncomputable def sentinelKey (top : ℝ) (T : ShortestTree) (v : ℕ) : ℝ :=
  (T v).distance.getD top

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Queue

noncomputable def activeLeaf (xs queued : List ℕ) (key : ℕ → ℝ) (B node : ℕ) : Record :=
  if B ≤ node ∧ node < B+xs.length then
    let k := node-B
    let v := xs[k]?.getD 0
    ⟨if v ∈ queued then k+1 else 0, key v⟩
  else ⟨0,0⟩

def slotVertex (xs : List ℕ) (k : ℕ) : ℕ := xs[k]?.getD 0

noncomputable def vertexRecord (xs : List ℕ) (key : ℕ → ℝ) (v : ℕ) : Record :=
  ⟨xs.idxOf v+1,key v⟩

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Queue
open Structured

def initPrefix : List Atom :=
  [⟨.realConst 0 0, by trivial⟩,
    ⟨.natCopy 7 1, by trivial⟩,
    ⟨.storeNat 7 3, by trivial⟩, ⟨.storeReal 7 0, by trivial⟩,
    ⟨.natOp .add 7 1 4, by trivial⟩,
    ⟨.storeNat 7 3, by trivial⟩, ⟨.storeReal 7 0, by trivial⟩,
    ⟨.natCopy 7 2, by trivial⟩, ⟨.storeNat 7 3, by trivial⟩,
    ⟨.natOp .add 7 2 4, by trivial⟩, ⟨.storeNat 7 3, by trivial⟩]

def initPair : List Atom :=
  [⟨.natOp .add 5 0 0, by trivial⟩,
    ⟨.natOp .add 6 5 4, by trivial⟩,
    ⟨.natOp .add 7 1 5, by trivial⟩,
    ⟨.storeNat 7 3, by trivial⟩, ⟨.storeReal 7 0, by trivial⟩,
    ⟨.natOp .add 7 1 6, by trivial⟩,
    ⟨.storeNat 7 3, by trivial⟩, ⟨.storeReal 7 0, by trivial⟩,
    ⟨.natOp .add 7 2 5, by trivial⟩, ⟨.storeNat 7 0, by trivial⟩,
    ⟨.natOp .add 7 2 6, by trivial⟩, ⟨.storeNat 7 0, by trivial⟩,
    ⟨.natOp .sub 0 0 4, by trivial⟩]

def initializeEmpty : Cmd :=
  .seq (atoms initPrefix) (.loop (.nat .lt 3 0) (atoms initPair))

noncomputable def prefixed (s : Store) : Store :=
  { s with
    nr := Function.update s.nr 7 (s.nr 2 + s.nr 4)
    rr := Function.update s.rr 0 0
    nm := Function.update (Function.update (Function.update (Function.update s.nm
      (s.nr 1) (s.nr 3)) (s.nr 1 + s.nr 4) (s.nr 3)) (s.nr 2) (s.nr 3))
      (s.nr 2 + s.nr 4) (s.nr 3)
    rm := Function.update (Function.update s.rm (s.nr 1) 0) (s.nr 1 + s.nr 4) 0 }

noncomputable def paired (s : Store) : Store :=
  let l := s.nr 0 + s.nr 0
  let r := l + s.nr 4
  { s with
    nr := Function.update (Function.update (Function.update (Function.update s.nr
      5 l) 6 r) 7 (s.nr 2 + r)) 0 (s.nr 0 - s.nr 4)
    nm := Function.update (Function.update (Function.update (Function.update s.nm
      (s.nr 1 + l) (s.nr 3)) (s.nr 1 + r) (s.nr 3)) (s.nr 2 + l) (s.nr 0))
      (s.nr 2 + r) (s.nr 0)
    rm := Function.update (Function.update s.rm (s.nr 1 + l) (s.rr 0))
      (s.nr 1 + r) (s.rr 0) }

def InitInv (W P B k : ℕ) (s : Store) : Prop :=
  s.nr 0 = k ∧ s.nr 1 = W ∧ s.nr 2 = P ∧ s.nr 3 = 0 ∧ s.nr 4 = 1 ∧ s.rr 0 = 0 ∧
    ∀ v < 2 * B, v < 2 ∨ 2 * (k + 1) ≤ v →
      s.nm (W + v) = 0 ∧ s.rm (W + v) = 0 ∧ s.nm (P + v) = v / 2

def InitFrame (W P B : ℕ) (s out : Store) : Prop :=
  (∀ a, (a < W ∨ W + 2 * B ≤ a) → (a < P ∨ P + 2 * B ≤ a) →
    out.nm a = s.nm a) ∧
  ∀ a, (a < W ∨ W + 2 * B ≤ a) → out.rm a = s.rm a

def Represents (B W : ℕ) (leaf : ℕ → Record) (s : Store) : Prop :=
  ∀ v < 2 * B, readRecord s (W + v) = heapTruth B leaf v

noncomputable def prefixLeaf (B : ℕ) (key : ℕ → ℝ) (count v : ℕ) : Record :=
  if B ≤ v ∧ v < B + count then ⟨v - B + 1, key (v - B)⟩ else ⟨0, 0⟩

def buildSetup : List Atom :=
  [⟨.natOp .sub 0 11 4, by trivial⟩, ⟨.natConst 14 0, by trivial⟩]

noncomputable def buildSetupState (s : Store) : Store :=
  { s with nr := Function.update (Function.update s.nr 0 (s.nr 11 - s.nr 4)) 14 0 }

def prepareInsert : List Atom :=
  [⟨.natOp .add 16 13 14, by trivial⟩, ⟨.loadReal 2 16, by trivial⟩,
    ⟨.natOp .add 0 11 14, by trivial⟩, ⟨.natOp .add 10 14 4, by trivial⟩]

noncomputable def preparedInsert (s : Store) : Store :=
  { s with
    nr := Function.update (Function.update (Function.update s.nr 16 (s.nr 13 + s.nr 14))
      0 (s.nr 11 + s.nr 14)) 10 (s.nr 14 + s.nr 4)
    rr := Function.update s.rr 2 (s.rm (s.nr 13 + s.nr 14)) }

def insertIncrement : Atom := ⟨.natOp .add 14 14 4, by trivial⟩

noncomputable def inserted (s : Store) : Store :=
  { s with nr := Function.update s.nr 14 (s.nr 14 + s.nr 4) }

def insertBody : Cmd :=
  .seq (atoms prepareInsert) (.seq updateLeaf (.atom insertIncrement))

def buildQueue : Cmd :=
  .seq (atoms buildSetup) (.seq initializeEmpty (.loop (.nat .lt 14 12) insertBody))

structure BuildInv (B N W P R : ℕ) (initial : Store) (k : ℕ) (s : Store) : Prop where
  hW : s.nr 1 = W
  hP : s.nr 2 = P
  hzero : s.nr 3 = 0
  hone : s.nr 4 = 1
  hB : s.nr 11 = B
  hN : s.nr 12 = N
  hR : s.nr 13 = R
  hk : s.nr 14 = k
  parents : ParentLayout (2 * B) s
  represents : Represents B W (prefixLeaf B (fun i => initial.rm (R + i)) k) s
  frame : InitFrame W P B initial s

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def treeInitializeQueue : Cmd := .seq treeSeed Queue.buildQueue

def activeProbe : List Atom :=
  [⟨.natOp .add 144 141 140, trivial⟩, ⟨.loadNat 145 144, trivial⟩]

def activeAppend : List Atom :=
  [ ⟨.natOp .add 146 142 143, trivial⟩,
    ⟨.storeNat 146 140, trivial⟩,
    ⟨.natOp .add 143 143 126, trivial⟩,
    ⟨.storeNat 144 143, trivial⟩ ]

def activeInsert : Cmd :=
  .seq (Cmd.atoms activeProbe)
    (.branch (.nat .eq 145 125) (Cmd.atoms activeAppend) .skip)

def activeProbed (s : Store) : Store :=
  { s with
    nr := Function.update (Function.update s.nr 144 (s.nr 141 + s.nr 140))
      145 (s.nm (s.nr 141 + s.nr 140)) }

def activeAppended (s : Store) : Store :=
  { s with
    nr := Function.update (Function.update s.nr 146 (s.nr 142 + s.nr 143))
      143 (s.nr 143 + s.nr 126)
    nm := Function.update (Function.update s.nm (s.nr 142 + s.nr 143) (s.nr 140))
      (s.nr 144) (s.nr 143 + s.nr 126) }

def activeResult (s : Store) : Store :=
  if s.nm (s.nr 141 + s.nr 140) = 0 then activeAppended (activeProbed s)
  else activeProbed s

def stableInsert (xs : List ℕ) (v : ℕ) : List ℕ :=
  if v ∈ xs then xs else xs ++ [v]

structure ActiveRep (n base array : ℕ) (xs : List ℕ) (s : Store) : Prop where
  nodup : xs.Nodup
  valid : ∀ v ∈ xs, v < n
  base_reg : s.nr 141 = base
  array_reg : s.nr 142 = array
  count_reg : s.nr 143 = xs.length
  separation : base + n ≤ array
  absent : ∀ v < n, v ∉ xs → s.nm (base + v) = 0
  index : ∀ k v, xs[k]? = some v → s.nm (base + v) = k + 1
  value : ∀ k v, xs[k]? = some v → s.nm (array + k) = v

structure TreeMemoryRep (I : Instance) (B W P map array off : ℕ) (top : ℝ)
    (S : TreeQueue) (s : Store) : Prop where
  active : ActiveRep I.graph.n map array (activeVertices I) s
  queued : S.queue.Sublist (activeVertices I)
  heap : Queue.Represents B W
    (Queue.activeLeaf (activeVertices I) S.queue (sentinelKey top S.tree) B) s
  links : ∀ node < 2 * B, s.nm (P + node) = node / 2
  parents : ∀ v ∈ activeVertices I,
    s.nm (targetAddress v + off) = ((S.tree v).parent.map (· + 1)).getD 0
  settled : ∀ v ∈ activeVertices I, v ∉ S.queue →
    s.rm (targetAddress v + off) = sentinelKey top S.tree v

structure TreeRegisters (I : Instance) (B W P R map arrayBase heads links off mode : ℕ)
    (top : ℝ) (s : Store) : Prop where
  winner : s.nr 1 = W
  parent : s.nr 2 = P
  zero : s.nr 3 = 0
  one : s.nr 4 = 1
  capacity : s.nr 11 = B
  count : s.nr 12 = (activeVertices I).length
  keys : s.nr 13 = R
  source : s.nr 123 = I.source
  heads : s.nr 137 = heads
  links : s.nr 139 = links
  map : s.nr 141 = map
  array : s.nr 142 = arrayBase
  active_count : s.nr 143 = (activeVertices I).length
  saved_capacity : s.nr 170 = B
  saved_array : s.nr 171 = arrayBase
  offset : s.nr 173 = off
  mode : s.nr 264 = mode
  sentinel : s.rr 170 = top

structure TreeAllocation (I : Instance) where
  B : ℕ
  height : ℕ
  W : ℕ
  P : ℕ
  R : ℕ
  map : ℕ
  array : ℕ
  heads : ℕ
  links : ℕ
  capacity : B = 2 ^ height
  fit : (activeVertices I).length ≤ B
  target_map : 16 + 4 * I.graph.n ≤ map
  map_heads : map + I.graph.n ≤ heads
  heads_array : heads + I.graph.n ≤ array
  array_links : array + I.graph.n ≤ links
  links_winner : links + I.graph.edges.length ≤ W
  winner_parent : W + 2 * B ≤ P
  parent_temp : P + 2 * B ≤ R

inductive TreeMode where
  | zeroLength
  | zeroBudget
  deriving DecidableEq

def TreeMode.tag : TreeMode → ℕ
  | .zeroLength => 0
  | .zeroBudget => 1

def TreeMode.offset : TreeMode → ℕ
  | .zeroLength => 2
  | .zeroBudget => 3

noncomputable def TreeMode.allow (mode : TreeMode) (I : Instance) : ℕ → ℕ → Bool :=
  match mode with
  | .zeroLength => fun u v => decide (I.length u v = 0)
  | .zeroBudget => fun u v => decide (I.cost u v = 0)

def TreeMode.resource (mode : TreeMode) (I : Instance) :=
  match mode with
  | .zeroLength => I.cost
  | .zeroBudget => I.length

noncomputable def TreeMode.weight (mode : TreeMode) (I : Instance) (u v : ℕ) : ℝ :=
  mode.resource I u v

noncomputable def TreeMode.top (mode : TreeMode) (I : Instance) : ℝ :=
  ((I.graph.n : ℝ) + 1) * (1 + edgeWeightSum I (mode.resource I))

noncomputable abbrev TreeAllocation.Memory {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) (S : TreeQueue) (s : Store) : Prop :=
  TreeMemoryRep I E.B E.W E.P E.map E.array mode.offset (mode.top I) S s

noncomputable abbrev TreeAllocation.Registers {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) (s : Store) : Prop :=
  TreeRegisters I E.B E.W E.P E.R E.map E.array E.heads E.links mode.offset mode.tag (mode.top I) s

def treeNatConstants : Finset ℕ :=
  {1,2,3,4,11,12,13,123,137,139,141,142,143,170,171,173,264}

def treeExtractAtoms : List Atom :=
  [ ⟨.natOp .add 7 1 4, trivial⟩,
    ⟨.loadNat 260 7, trivial⟩,
    ⟨.loadReal 260 7, trivial⟩,
    ⟨.natOp .sub 261 260 4, trivial⟩,
    ⟨.natOp .add 262 171 261, trivial⟩,
    ⟨.loadNat 262 262, trivial⟩,
    ⟨.natOp .add 0 170 261, trivial⟩,
    ⟨.natConst 10 0, trivial⟩,
    ⟨.realCopy 2 260, trivial⟩ ]

def treeExtract : Cmd := .seq (.atoms treeExtractAtoms) Queue.updateLeaf

def treeExtractPrepared (s : Store) : Store :=
  let root := s.nr 1 + s.nr 4
  let token := s.nm root
  let index := token - s.nr 4
  let vertex := s.nm (s.nr 171 + index)
  { s with
    nr := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update s.nr 7 root) 260 token) 261 index)
      262 vertex) 0 (s.nr 170 + index)) 10 0
    rr := Function.update (Function.update s.rr 260 (s.rm root)) 2 (s.rm root) }

def treeRecordDistanceAtoms : List Atom :=
  [ ⟨.natOp .add 275 262 262, trivial⟩,
    ⟨.natOp .add 275 275 275, trivial⟩,
    ⟨.natConst 276 16, trivial⟩,
    ⟨.natOp .add 275 276 275, trivial⟩,
    ⟨.natOp .add 275 275 173, trivial⟩,
    ⟨.storeReal 275 260, trivial⟩ ]

def treeRecordedDistance (s : Store) : Store :=
  { s with
    nr := Function.update (Function.update s.nr 276 16)
      275 (targetAddress (s.nr 262) + s.nr 173)
    rm := Function.update s.rm (targetAddress (s.nr 262) + s.nr 173) (s.rr 260) }

def treeEdgeAtoms : List Atom :=
  [ ⟨.natOp .add 266 265 265, trivial⟩,
    ⟨.natConst 267 4, trivial⟩,
    ⟨.natOp .add 267 267 266, trivial⟩,
    ⟨.inputNat 268 267, trivial⟩,
    ⟨.natConst 267 2, trivial⟩,
    ⟨.natOp .add 267 267 266, trivial⟩,
    ⟨.inputReal 261 267, trivial⟩,
    ⟨.natOp .add 267 267 4, trivial⟩,
    ⟨.inputReal 262 267, trivial⟩,
    ⟨.realConst 263 0, trivial⟩ ]

def treeEdgeLoaded (input : RAMInput) (s : Store) : Store :=
  { s with
    nr := Function.update (Function.update (Function.update s.nr 266 (2 * s.nr 265))
      268 (input.naturals (4 + 2 * s.nr 265))) 267 (2 + 2 * s.nr 265 + s.nr 4)
    rr := Function.update (Function.update (Function.update s.rr
      261 (input.reals (2 + 2 * s.nr 265)))
      262 (input.reals (2 + 2 * s.nr 265 + s.nr 4))) 263 0 }

def treeTargetAtoms : List Atom :=
  [ ⟨.natOp .add 270 141 268, trivial⟩,
    ⟨.loadNat 271 270, trivial⟩,
    ⟨.natOp .sub 271 271 4, trivial⟩,
    ⟨.natOp .add 0 170 271, trivial⟩,
    ⟨.natOp .add 7 1 0, trivial⟩,
    ⟨.loadNat 10 7, trivial⟩,
    ⟨.loadReal 265 7, trivial⟩ ]

def treeTargetLoaded (s : Store) : Store :=
  let index := s.nm (s.nr 141 + s.nr 268) - s.nr 4
  let node := s.nr 170 + index
  let address := s.nr 1 + node
  { s with
    nr := Function.update (Function.update (Function.update (Function.update
      (Function.update s.nr 270 (s.nr 141 + s.nr 268)) 271 index) 0 node) 7 address)
      10 (s.nm address)
    rr := Function.update s.rr 265 (s.rm address) }

def treeDecreaseAtoms : List Atom :=
  [ ⟨.realCopy 2 264, trivial⟩,
    ⟨.natOp .add 272 268 268, trivial⟩,
    ⟨.natOp .add 272 272 272, trivial⟩,
    ⟨.natConst 273 16, trivial⟩,
    ⟨.natOp .add 272 273 272, trivial⟩,
    ⟨.natOp .add 272 272 173, trivial⟩,
    ⟨.natOp .add 274 262 4, trivial⟩,
    ⟨.storeNat 272 274, trivial⟩ ]

def treeDecreased (s : Store) : Store :=
  { s with
    nr := Function.update (Function.update (Function.update s.nr
      272 (targetAddress (s.nr 268) + s.nr 173)) 273 16) 274 (s.nr 262 + s.nr 4)
    rr := Function.update s.rr 2 (s.rr 264)
    nm := Function.update s.nm (targetAddress (s.nr 268) + s.nr 173) (s.nr 262 + s.nr 4) }

def treeApplyDecrease : Cmd := .seq (.atoms treeDecreaseAtoms) Queue.updateLeaf

def treeCheckTarget : Cmd :=
  .seq (.atoms treeTargetAtoms)
    (.branch (.nat .eq 10 3) .skip
      (.branch (.real .lt 264 265) treeApplyDecrease .skip))

def treeRelaxLoaded : Cmd :=
  .branch (.nat .eq 264 3)
    (.branch (.real .eq 261 263)
      (.seq (.atom ⟨.realOp .add 264 260 262, trivial⟩) treeCheckTarget) .skip)
    (.branch (.real .eq 262 263)
      (.seq (.atom ⟨.realOp .add 264 260 261, trivial⟩) treeCheckTarget) .skip)

def treeRelaxEdgeCmd : Cmd := .seq (.atoms treeEdgeAtoms) treeRelaxLoaded

def treeAdjacencyPrepare : List Atom :=
  [ ⟨.natOp .sub 265 278 4, trivial⟩,
    ⟨.natOp .add 279 139 265, trivial⟩,
    ⟨.loadNat 279 279, trivial⟩ ]

def treeAdjacencyBody : Cmd :=
  .seq (.atoms treeAdjacencyPrepare)
    (.seq treeRelaxEdgeCmd (.atom ⟨.natCopy 278 279, trivial⟩))

def treeAdjacencyLoop : Cmd := .loop (.nat .lt 3 278) treeAdjacencyBody

def treeAdjacencyHead : List Atom :=
  [ ⟨.natOp .add 278 137 262, trivial⟩, ⟨.loadNat 278 278, trivial⟩ ]

def treePopCmd : Cmd :=
  .seq treeExtract (.seq (.atoms treeRecordDistanceAtoms)
    (.seq (.atoms treeAdjacencyHead) (.seq treeAdjacencyLoop
      (.atom ⟨.natOp .add 277 277 4, trivial⟩))))

def treeCmd : Cmd :=
  .seq treeSeed (.seq Queue.buildQueue
    (.seq (.atom ⟨.natConst 277 0, trivial⟩) (.loop (.nat .lt 277 12) treePopCmd)))

def zeroLengthSetup : List Atom :=
  [ ⟨.natConst 264 0, trivial⟩, ⟨.natConst 173 2, trivial⟩,
    ⟨.realCopy 170 280, trivial⟩ ]

def zeroBudgetSetup : List Atom :=
  [ ⟨.natConst 264 1, trivial⟩, ⟨.natConst 173 3, trivial⟩,
    ⟨.realCopy 170 281, trivial⟩ ]

def zeroTreesCmd : Cmd :=
  .seq (.atoms zeroLengthSetup) (.seq treeCmd (.seq (.atoms zeroBudgetSetup) treeCmd))

def adjacencyAtoms : List Atom :=
  [ ⟨.natOp .add 165 163 161, trivial⟩,
    ⟨.loadNat 166 165, trivial⟩,
    ⟨.natOp .add 167 164 160, trivial⟩,
    ⟨.storeNat 167 166, trivial⟩,
    ⟨.natOp .add 168 160 126, trivial⟩,
    ⟨.storeNat 165 168, trivial⟩ ]

def adjacencyInsert : Cmd := Cmd.atoms adjacencyAtoms

def adjacencyResult (s : Store) : Store :=
  { s with
    nr := Function.update (Function.update (Function.update (Function.update s.nr
      165 (s.nr 163 + s.nr 161)) 166 (s.nm (s.nr 163 + s.nr 161)))
      167 (s.nr 164 + s.nr 160)) 168 (s.nr 160 + s.nr 126)
    nm := Function.update
      (Function.update s.nm (s.nr 164 + s.nr 160) (s.nm (s.nr 163 + s.nr 161)))
      (s.nr 163 + s.nr 161) (s.nr 160 + s.nr 126) }

inductive AdjacencyChain (mem : ℕ → ℕ) (links : ℕ) : ℕ → List ℕ → Prop
  | nil : AdjacencyChain mem links 0 []
  | cons {e next : ℕ} {es : List ℕ} :
      mem (links + e) = next → AdjacencyChain mem links next es →
      AdjacencyChain mem links (e + 1) (e :: es)

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def TreeIteratorScratch (s t : Store) : Prop :=
  t.rr = s.rr ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
    ∀ r, r ≠ 265 → r ≠ 278 → r ≠ 279 → t.nr r = s.nr r

noncomputable def treeAdjacencyPrepared (input : RAMInput) (s : Store) : Store :=
  evalAtoms input treeAdjacencyPrepare s

noncomputable def treeAdjacencyAdvanced (input : RAMInput) (s : Store) : Store :=
  Atom.eval (⟨.natCopy 278 279,trivial⟩ : Atom) input s

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

noncomputable def treeCheckedLeaf (leaf : ℕ → Queue.Record) (s : Store) : ℕ → Queue.Record :=
  if s.nr 10 ≠ 0 ∧ s.rr 264 < s.rr 265 then
    Function.update leaf (s.nr 0) ⟨s.nr 10, s.rr 264⟩
  else leaf

noncomputable def treeCheckedNatMemory (s : Store) : ℕ → ℕ :=
  if s.nr 10 ≠ 0 ∧ s.rr 264 < s.rr 265 then
    Function.update s.nm (targetAddress (s.nr 268) + s.nr 173) (s.nr 262 + s.nr 4)
  else s.nm

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

noncomputable def treeUpdated (S : TreeQueue) (u v : ℕ) (d : ℝ) : TreeQueue :=
  { S with
    tree := Function.update S.tree v ⟨some d,some u,0⟩ }

noncomputable def treeTargetState (top : ℝ) (S : TreeQueue) (u v : ℕ) (d : ℝ) : TreeQueue :=
  if v ∈ S.queue ∧ d < sentinelKey top S.tree v then treeUpdated S u v d else S

def TreeEdgeFrame (W B parentAddress : ℕ) (s t : Store) : Prop :=
  ∀ a, (a < W ∨ W + 2*B ≤ a) → a ≠ parentAddress →
    t.nm a = s.nm a ∧ t.rm a = s.rm a

def standalone_Mission_RAMTreeEdge__candidateAtom : TreeMode → Atom
  | .zeroLength => ⟨.realOp .add 264 260 262,trivial⟩
  | .zeroBudget => ⟨.realOp .add 264 260 261,trivial⟩

def standalone_Mission_RAMTreeEdge__edgeGuard : TreeMode → Guard
  | .zeroLength => .real .eq 261 263
  | .zeroBudget => .real .eq 262 263

def standalone_Mission_RAMTreeEdge__modeBody (mode : TreeMode) : Cmd :=
  .branch (standalone_Mission_RAMTreeEdge__edgeGuard mode) (.seq (.atom (standalone_Mission_RAMTreeEdge__candidateAtom mode)) treeCheckTarget) .skip

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

structure TreeScanMath (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) : Prop where
  policy : TreePolicy I allow w S
  nonnegative : ∀ v, 0 ≤ treeDist S.tree v
  source_zero : (S.tree I.source).distance = some 0
  removed : u ∉ S.queue
  rank_bound : (S.tree u).rank < S.rank

def outgoingEdges (I : Instance) (u : ℕ) : List (ℕ × ℕ) :=
  I.graph.edges.filter (fun e => e.1 == u)

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def adjacencyScanBody : Cmd :=
  .seq (.atom ⟨.inputNat 161 162, trivial⟩)
    (.seq adjacencyInsert
      (Cmd.atoms [⟨.natOp .add 160 160 126, trivial⟩,
        ⟨.natOp .add 162 162 127, trivial⟩]))

def adjacencyScanLoop : Cmd := .loop (.nat .lt 160 122) adjacencyScanBody

def adjacencyScanCmd : Cmd :=
  .seq (Cmd.atoms [⟨.natConst 160 0, trivial⟩,⟨.natConst 162 3, trivial⟩]) adjacencyScanLoop

def adjacencyLoaded (input : RAMInput) (s : Store) : Store :=
  { s with nr := Function.update s.nr 161 (input.naturals (s.nr 162)) }

def adjacencyStep (input : RAMInput) (s : Store) : Store :=
  { adjacencyResult (adjacencyLoaded input s) with
    nr := Function.update (Function.update (adjacencyResult (adjacencyLoaded input s)).nr
      160 (s.nr 160 + 1)) 162 (s.nr 162 + 2) }

def adjacencyScanResult (input : RAMInput) : ℕ → Store → Store
  | 0, s => s
  | k+1, s => adjacencyScanResult input k (adjacencyStep input s)

def adjacencyPrepared (s : Store) : Store :=
  { s with nr := Function.update (Function.update s.nr 160 0) 162 3 }

def edgeAt (I : Instance) (e : ℕ) : ℕ × ℕ := I.graph.edges[e]?.getD (0,0)

def outgoingIndices (I : Instance) (count v : ℕ) : List ℕ :=
  ((List.range count).filter (fun e => (edgeAt I e).1 == v)).reverse

def AdjacencyPrefix (I : Instance) (count heads links : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ v < I.graph.n, AdjacencyChain mem links (mem (heads+v)) (outgoingIndices I count v)

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def TreeProtected {I : Instance} (E : TreeAllocation I) (mode : TreeMode) (a : ℕ) : Prop :=
  (a < E.W ∨ E.W+2*E.B ≤ a) ∧
    ∀ v ∈ activeVertices I, a ≠ targetAddress v + mode.offset

structure TreeScanInvariant {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (u : ℕ) (S : TreeQueue) (s : Store) : Prop where
  memory : E.Memory mode S s
  registers : E.Registers mode s
  math : TreeScanMath I (mode.allow I) (mode.weight I) u S
  vertex : s.nr 262 = u
  key : s.rr 260 = sentinelKey (mode.top I) S.tree u

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def treeSettleCmd : Cmd := .seq treeExtract (.atoms treeRecordDistanceAtoms)

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources

def outgoingWork (I : Instance) (vertices : List ℕ) : ℕ :=
  (vertices.map (fun u => (outgoingEdges I u).length)).sum

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

noncomputable def treeHeadStore (input : RAMInput) (s : Store) : Store :=
  evalAtoms input treeAdjacencyHead s

noncomputable def treePopIncremented (input : RAMInput) (s : Store) : Store :=
  Atom.eval (⟨.natOp .add 277 277 4,trivial⟩ : Atom) input s

noncomputable def treeState (I : Instance) (mode : TreeMode) (k : ℕ) : TreeQueue :=
  treeRun I (mode.allow I) (mode.weight I) k (treeInitial I)

def treeLoopCmd : Cmd := .loop (.nat .lt 277 12) treePopCmd

def TreeWholeProtected {I : Instance} (E : TreeAllocation I) (mode : TreeMode) (a : ℕ) : Prop :=
  TreeProtected E mode a ∧ (a < E.P ∨ E.P+2*E.B ≤ a) ∧
    (a < E.R ∨ E.R+(activeVertices I).length ≤ a)

def TreeMode.sentinelRegister : TreeMode → ℕ
  | .zeroLength => 280
  | .zeroBudget => 281

def zeroTreeSetup : TreeMode → Cmd
  | .zeroLength => .atoms zeroLengthSetup
  | .zeroBudget => .atoms zeroBudgetSetup

def zeroTreePrepared (mode : TreeMode) (s : Store) : Store :=
  { s with
    nr := Function.update (Function.update s.nr 264 mode.tag) 173 mode.offset
    rr := Function.update s.rr 170 (s.rr mode.sentinelRegister) }

structure ZeroTreeMemory (I : Instance) (s : Store) : Prop where
  length_parent : ∀ v ∈ activeVertices I,
    s.nm (targetAddress v+2)=((zeroLengthTree I v).parent.map (·+1)).getD 0
  budget_parent : ∀ v ∈ activeVertices I,
    s.nm (targetAddress v+3)=((zeroBudgetTree I v).parent.map (·+1)).getD 0
  length_distance : ∀ v ∈ activeVertices I,
    s.rm (targetAddress v+2)=sentinelKey (TreeMode.zeroLength.top I) (zeroLengthTree I) v
  budget_distance : ∀ v ∈ activeVertices I,
    s.rm (targetAddress v+3)=sentinelKey (TreeMode.zeroBudget.top I) (zeroBudgetTree I) v

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem standalone_Mission_Guesses__min_fold_pos (xs : List ℝ) (a : ℝ) (ha : 0 < a)
    (hx : ∀ x ∈ xs, 0 < x) : 0 < xs.foldl min a := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
      apply ih
      · exact lt_min ha (hx x (by simp))
      · intro y hy
        exact hx y (by simp [hy])

theorem positiveLengths_member_pos (I : Instance) (x : ℝ)
    (hx : x ∈ positiveLengths I) : 0 < x := by
  simpa [positiveLengths] using (List.mem_filter.mp hx).2

theorem firstPositiveLength_pos (I : Instance) : 0 < firstPositiveLength I := by
  unfold firstPositiveLength
  apply standalone_Mission_Guesses__min_fold_pos
  · cases he : positiveLengths I with
    | nil => norm_num
    | cons x xs =>
        exact positiveLengths_member_pos I x (by simp [he])
  · exact positiveLengths_member_pos I

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.GuessLoop
open Structured

def stepOps : List Atom :=
  [⟨.realOp .mul 73 73 71,trivial⟩,⟨.natOp .add 70 70 71,trivial⟩]

def loopCmd : Cmd := .loop (.real .lt 73 72) (.atoms stepOps)

def initOps : List Atom :=
  [⟨.natConst 70 0,trivial⟩,⟨.natConst 71 1,trivial⟩,⟨.realCopy 73 70,trivial⟩]

def crossingCmd : Cmd := .seq (.atoms initOps) loopCmd

def gridState (s : Store) (k : ℕ) : Store :=
  { s with nr := Function.update (Function.update s.nr 70 k) 71 1
           rr := Function.update s.rr 73 (s.rr 70 * s.rr 71 ^ k) }

end NearLinearRSP.TwoResources.Mission.GuessLoop
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources
attribute [local instance] Classical.propDecidable

noncomputable def acceptedIndex (I : Instance) (ε : ℝ) (t : ℕ) : Option ℕ :=
  (List.range (outerInputs I ε).length).find?
    (fun r => ((outerInputs I ε)[r]?).any (fun A => decide (accepted A t)))

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

noncomputable def gridInput (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : 0 < (I.budget : ℝ)) (r : ℕ) : InnerInput where
  I := I
  δ := ε / 4
  accuracy_pos := by linarith
  accuracy_lt_one := by linarith
  L := firstPositiveLength I * (1 + ε/4)^r
  length_pos := mul_pos (firstPositiveLength_pos I) (pow_pos (by linarith) r)
  budget_pos := hC

theorem outerInputs_eq_grid (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : 0 < (I.budget : ℝ)) :
    outerInputs I ε = if (positiveLengths I).isEmpty then [] else
      (List.range (firstCrossing (firstPositiveLength I) (1+ε/4)
        (I.graph.n * largestLength I)+1)).map (gridInput I ε hε hε1 hC) := by
  have hh : 0 < ε ∧ ε < 1 ∧ 0 < (I.budget : ℝ) := ⟨hε,hε1,hC⟩
  simp only [outerInputs,dif_pos hh,geometricGuesses]
  split
  · rfl
  · rw [List.filterMap_map]
    apply List.filterMap_eq_map_iff_forall_eq_some.mpr
    intro r hr
    have hp : 0 < firstPositiveLength I * (1+ε/4)^r :=
      mul_pos (firstPositiveLength_pos I) (pow_pos (by linarith) r)
    simp [hp,gridInput]

theorem outerInputs_get_grid (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (r : ℕ) (hr : r < (outerInputs I ε).length) :
    ∃ hC : 0 < (I.budget : ℝ),
      (outerInputs I ε)[r]? = some (gridInput I ε hε hε1 hC r) := by
  have hC : 0 < (I.budget : ℝ) := by
    by_contra h
    have hn : I.budget = 0 := by
      apply Subtype.ext
      change (I.budget : ℝ) = 0
      exact le_antisymm (le_of_not_gt h) I.budget.coe_nonneg
    simp [outerInputs,hn] at hr
  refine ⟨hC,?_⟩
  rw [outerInputs_eq_grid I ε hε hε1 hC] at hr ⊢
  split at hr
  · simp at hr
  · rename_i he
    simp only [he,if_false,List.length_map,List.length_range] at hr ⊢
    simp [hr]

theorem outerInputs_get_parameters (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (r : ℕ) (A : InnerInput) (hA : (outerInputs I ε)[r]? = some A) :
    A.I = I ∧ A.δ = ε/4 ∧ A.L = firstPositiveLength I * (1+ε/4)^r ∧
    tickLimit A = outerQ ε := by
  have hr := (List.getElem?_eq_some_iff.mp hA).1
  obtain ⟨hC,hgrid⟩ := outerInputs_get_grid I ε hε hε1 r hr
  have he : A = gridInput I ε hε hε1 hC r := Option.some.inj (hA.symm.trans hgrid)
  subst A
  exact ⟨rfl,rfl,rfl,rfl⟩

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def countPrepare : List Atom :=
  [⟨.natConst 132 0,trivial⟩,⟨.realConst 74 0,trivial⟩]

def countPositivePrepare : List Atom :=
  [⟨.realCopy 70 150,trivial⟩,⟨.realCopy 71 123,trivial⟩,
   ⟨.realOp .mul 72 129 151,trivial⟩]

def countPositive : Cmd :=
  .seq (.atoms countPositivePrepare)
    (.seq GuessLoop.crossingCmd (.atom ⟨.natOp .add 132 70 126,trivial⟩))

def countCases : Cmd :=
  .branch (.nat .eq 150 125) .skip
    (.branch (.real .lt 74 121) countPositive .skip)

def countCmd : Cmd := .seq (.atoms countPrepare) countCases

structure CountReady (I : Instance) (ε : ℝ) (s : Store) : Prop where
  zero : s.nr 125 = 0
  one : s.nr 126 = 1
  found : s.nr 150 = if (positiveLengths I).isEmpty then 0 else 1
  budget : s.rr 121 = (I.budget : ℝ)
  ratio : s.rr 123 = 1+ε/4
  vertices : s.rr 129 = I.graph.n
  minimum : s.rr 150 = firstPositiveLength I
  maximum : s.rr 151 = largestLength I

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission
namespace Preprocess
open Structured

def headerAtoms : List Atom :=
  [ ⟨.natConst 120 0, trivial⟩,
    ⟨.inputNat 121 120, trivial⟩,
    ⟨.inputReal 120 120, trivial⟩,
    ⟨.natConst 120 1, trivial⟩,
    ⟨.inputNat 122 120, trivial⟩,
    ⟨.inputReal 121 120, trivial⟩,
    ⟨.natConst 120 2, trivial⟩,
    ⟨.inputNat 123 120, trivial⟩,
    ⟨.natConst 124 0, trivial⟩,
    ⟨.natConst 125 0, trivial⟩,
    ⟨.natConst 126 1, trivial⟩,
    ⟨.natConst 127 2, trivial⟩,
    ⟨.natConst 128 3, trivial⟩,
    ⟨.natOp .add 129 121 121, trivial⟩,
    ⟨.natOp .add 129 129 129, trivial⟩,
    ⟨.natConst 130 16, trivial⟩,
    ⟨.natOp .add 130 130 129, trivial⟩,
    ⟨.realConst 125 1, trivial⟩,
    ⟨.realConst 126 4, trivial⟩,
    ⟨.realOp .div 122 120 126, trivial⟩,
    ⟨.realOp .add 123 125 122, trivial⟩,
    ⟨.realOp .mul 124 122 122, trivial⟩,
    ⟨.realConst 126 512, trivial⟩,
    ⟨.realOp .div 124 126 124, trivial⟩,
    ⟨.realConst 127 0, trivial⟩,
    ⟨.realConst 126 8, trivial⟩,
    ⟨.realOp .div 128 120 126, trivial⟩,
    ⟨.realOp .add 128 125 128, trivial⟩,
    ⟨.realOp .div 128 128 123, trivial⟩ ]

noncomputable def headerPrepared (input : RAMInput) (s : Store) : Store :=
  evalAtoms input headerAtoms s

def headerLoopStore (s : Store) (k : ℕ) : Store :=
  { s with
    nr := Function.update s.nr 124 k
    rr := Function.update s.rr 127 (k : ℝ) }

def headerBody : Cmd :=
  .seq (.atom ⟨.natOp .add 124 124 126, trivial⟩)
    (.atom ⟨.realOp .add 127 127 125, trivial⟩)

def headerLoop : Cmd := .loop (.real .lt 127 124) headerBody

def headerStores : List Atom :=
  [ ⟨.natConst 120 0, trivial⟩,
    ⟨.storeNat 120 124, trivial⟩,
    ⟨.storeReal 120 128, trivial⟩,
    ⟨.natConst 120 1, trivial⟩,
    ⟨.storeNat 120 123, trivial⟩,
    ⟨.natConst 120 2, trivial⟩,
    ⟨.storeNat 120 121, trivial⟩ ]

def headerCmd : Cmd :=
  .seq (Cmd.atoms headerAtoms) (.seq headerLoop (Cmd.atoms headerStores))

noncomputable def headerResult (input : RAMInput) (s : Store) : Store :=
  evalAtoms input headerStores
    (headerLoopStore (headerPrepared input s) (Nat.ceil (512 / (input.reals 0 / 4) ^ 2)))

end Preprocess
end NearLinearRSP.TwoResources.Mission
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.NatToReal
open Structured

def atoms : List Atom → Cmd
  | [] => .skip
  | a :: as => .seq (.atom a) (atoms as)

noncomputable def evalAtoms (input : RAMInput) (as : List Atom) (s : Store) : Store :=
  as.foldl (fun s a => a.eval input s) s

def powerOps : List Atom :=
  [⟨.natCopy 62 63, trivial⟩,
   ⟨.realOp .add 61 61 61, trivial⟩,
   ⟨.natOp .add 63 63 63, trivial⟩]

def powerBody : Cmd := atoms powerOps

def powerLoop : Cmd := .loop (.nat .lt 63 66) powerBody

def powerState (s : Store) (k : ℕ) : Store :=
  { s with nr := Function.update (Function.update s.nr 62 (2 ^ k)) 63 (2 ^ (k+1))
           rr := Function.update s.rr 61 ((2 : ℝ) ^ k) }

def prepare : List Atom :=
  [⟨.natConst 62 1, trivial⟩, ⟨.natConst 63 2, trivial⟩,
   ⟨.realConst 61 1, trivial⟩, ⟨.natOp .add 66 61 65, trivial⟩]

def finish : List Atom :=
  [⟨.natOp .sub 61 61 62, trivial⟩, ⟨.realOp .add 60 60 61, trivial⟩]

def convertBody : Cmd := .seq (atoms prepare) (.seq powerLoop (atoms finish))

def convertLoop : Cmd := .loop (.nat .lt 64 61) convertBody

def prepared (s : Store) : Store := { s with nr := Function.update s.nr 66 (s.nr 61+1) }

def bodyResult (s : Store) (k : ℕ) : Store :=
  let t := powerState (prepared s) k
  { t with nr := Function.update t.nr 61 (s.nr 61 - 2 ^ k)
           rr := Function.update t.rr 60 (s.rr 60 + (2 : ℝ) ^ k) }

def Frame (s t : Store) : Prop :=
  (∀ r, r < 61 ∨ 66 < r → t.nr r = s.nr r) ∧
  (∀ r, r ≠ 60 → r ≠ 61 → t.rr r = s.rr r) ∧ t.nm = s.nm ∧ t.rm = s.rm

def initOps : List Atom :=
  [⟨.natCopy 61 60,trivial⟩, ⟨.natConst 64 0,trivial⟩,
   ⟨.natConst 65 1,trivial⟩, ⟨.realConst 60 0,trivial⟩]

def convertCmd : Cmd := .seq (atoms initOps) convertLoop

end NearLinearRSP.TwoResources.Mission.NatToReal
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Scan

structure Summary where
  found : Bool
  minimum : ℝ
  maximum : ℝ
  sumLength : ℝ
  sumCost : ℝ

noncomputable def positives (xs : List (ℝ × ℝ)) : List ℝ :=
  (xs.map Prod.fst).filter (0 < ·)

noncomputable def summarize (xs : List (ℝ × ℝ)) : Summary where
  found := !(positives xs).isEmpty
  minimum := (positives xs).foldl min ((positives xs).headD 1)
  maximum := (xs.map Prod.fst).foldl max 0
  sumLength := (xs.map Prod.fst).sum
  sumCost := (xs.map Prod.snd).sum

noncomputable def addSample (s : Summary) (x : ℝ × ℝ) : Summary where
  found := if 0 < x.1 then true else s.found
  minimum := if 0 < x.1 then if s.found then min s.minimum x.1 else x.1 else s.minimum
  maximum := max s.maximum x.1
  sumLength := s.sumLength+x.1
  sumCost := s.sumCost+x.2

noncomputable def sample (input : RAMInput) (k : ℕ) : ℝ × ℝ :=
  (input.reals (2+2*k),input.reals (2+2*k+1))

noncomputable def prefixSummary (input : RAMInput) (k : ℕ) : Summary :=
  summarize ((List.range k).map (sample input))

noncomputable def edgeSamples (I : Instance) : List (ℝ × ℝ) :=
  I.graph.edges.map (fun e => ((I.length e.1 e.2 : ℝ),(I.cost e.1 e.2 : ℝ)))

end NearLinearRSP.TwoResources.Mission.Scan
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.Scan
open Structured

def minCmd (dst src : ℕ) : Cmd :=
  .branch (.real .lt src dst) (.atom ⟨.realCopy dst src,trivial⟩) .skip

def maxCmd (dst src : ℕ) : Cmd :=
  .branch (.real .lt dst src) (.atom ⟨.realCopy dst src,trivial⟩) .skip

noncomputable def minResult (s : Store) (dst src : ℕ) : Store :=
  { s with rr := Function.update s.rr dst (min (s.rr dst) (s.rr src)) }

noncomputable def maxResult (s : Store) (dst src : ℕ) : Store :=
  { s with rr := Function.update s.rr dst (max (s.rr dst) (s.rr src)) }

def firstPositiveOps : List Atom :=
  [⟨.realCopy 150 154,trivial⟩,⟨.natConst 150 1,trivial⟩]

def positiveCmd : Cmd :=
  .branch (.real .lt 156 154)
    (.branch (.nat .eq 150 153) (.atoms firstPositiveOps) (minCmd 150 154)) .skip

noncomputable def positiveResult (input : RAMInput) (s : Store) : Store :=
  if 0 < s.rr 154 then
    if s.nr 150 = 0 then evalAtoms input firstPositiveOps s else minResult s 150 154
  else s

def loadSampleOps : List Atom :=
  [⟨.inputReal 154 151,trivial⟩,⟨.natOp .add 151 151 154,trivial⟩,
   ⟨.inputReal 155 151,trivial⟩,⟨.natOp .add 151 151 154,trivial⟩,
   ⟨.realOp .add 152 152 154,trivial⟩,⟨.realOp .add 153 153 155,trivial⟩]

def incrementCmd : Cmd := .atom ⟨.natOp .add 152 152 154,trivial⟩

def scanBody : Cmd := .seq (.atoms loadSampleOps)
  (.seq positiveCmd (.seq (maxCmd 151 154) incrementCmd))

noncomputable def scanBodyResult (input : RAMInput) (s : Store) : Store :=
  let a := evalAtoms input loadSampleOps s
  let b := positiveResult input a
  let c := maxResult b 151 154
  { c with nr := Function.update c.nr 152 (c.nr 152+c.nr 154) }

def scanInitOps : List Atom :=
  [⟨.natConst 158 1,trivial⟩,⟨.inputNat 159 158,trivial⟩,
   ⟨.natConst 150 0,trivial⟩,⟨.natConst 151 2,trivial⟩,
   ⟨.natConst 152 0,trivial⟩,⟨.natConst 153 0,trivial⟩,⟨.natConst 154 1,trivial⟩,
   ⟨.realConst 150 1,trivial⟩,⟨.realConst 151 0,trivial⟩,
   ⟨.realConst 152 0,trivial⟩,⟨.realConst 153 0,trivial⟩,⟨.realConst 156 0,trivial⟩]

def scanLoop : Cmd := .loop (.nat .lt 152 159) scanBody

def scanCmd : Cmd := .seq (.atoms scanInitOps) scanLoop

structure ScanRep (input : RAMInput) (m k : ℕ) (s : Store) : Prop where
  index : s.nr 152 = k
  pointer : s.nr 151 = 2+2*k
  bound : s.nr 159 = m
  zero : s.nr 153 = 0
  one : s.nr 154 = 1
  realZero : s.rr 156 = 0
  found : s.nr 150 = if (prefixSummary input k).found then 1 else 0
  minimum : s.rr 150 = (prefixSummary input k).minimum
  maximum : s.rr 151 = (prefixSummary input k).maximum
  lengthSum : s.rr 152 = (prefixSummary input k).sumLength
  costSum : s.rr 153 = (prefixSummary input k).sumCost

end NearLinearRSP.TwoResources.Mission.Scan
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

structure CoreRegs (I : Instance) (ε : ℝ) (s : Store) : Prop where
  vertices : s.nr 121 = I.graph.n
  edges : s.nr 122 = I.graph.edges.length
  source : s.nr 123 = I.source
  q : s.nr 124 = outerQ ε
  zero : s.nr 125 = 0
  one : s.nr 126 = 1
  two : s.nr 127 = 2
  vertexStride : s.nr 129 = 4*I.graph.n
  targetEnd : s.nr 130 = 16+4*I.graph.n
  budget : s.rr 121 = (I.budget : ℝ)
  ratio : s.rr 123 = 1+ε/4
  realOne : s.rr 125 = 1
  realQ : s.rr 127 = (outerQ ε : ℝ)
  z : s.rr 128 = (1+ε/8)/(1+ε/4)

structure ScalarReady (I : Instance) (ε : ℝ) (s : Store) : Prop extends CoreRegs I ε s where
  realVertices : s.rr 129 = I.graph.n
  minimum : s.rr 150 = firstPositiveLength I
  maximum : s.rr 151 = largestLength I
  lengthSum : s.rr 152 = (I.graph.edges.map (fun e => (I.length e.1 e.2 : ℝ))).sum
  costSum : s.rr 153 = (I.graph.edges.map (fun e => (I.cost e.1 e.2 : ℝ))).sum
  found : s.nr 150 = if (positiveLengths I).isEmpty then 0 else 1
  count : s.nr 132 = (outerInputs I ε).length
  headerQ : s.nm 0 = outerQ ε
  headerSource : s.nm 1 = I.source
  headerVertices : s.nm 2 = I.graph.n
  headerZ : s.rm 0 = (1+ε/8)/(1+ε/4)
  naturalZero : ∀a, 3 ≤ a → s.nm a = 0
  realZero : ∀a, 1 ≤ a → s.rm a = 0

def scalarCopyN : Atom := ⟨.natCopy 60 121,trivial⟩

def scalarKeepN : Atom := ⟨.realCopy 129 60,trivial⟩

def scalarCmd : Cmd := .seq headerCmd (.seq (.atom scalarCopyN)
  (.seq NatToReal.convertCmd (.seq (.atom scalarKeepN) (.seq Scan.scanCmd countCmd))))

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission
namespace Address
open Structured

def addressBody : Cmd :=
  .seq (.atom ⟨.natOp .add 44 44 41, trivial⟩)
    (.atom ⟨.natOp .sub 46 46 47, trivial⟩)

def addressLoop : Cmd := .loop (.nat .lt 48 46) addressBody

def addressCmd : Cmd :=
  .seq (.atom ⟨.natCopy 44 40, trivial⟩)
  (.seq (.atom ⟨.natCopy 46 42, trivial⟩)
  (.seq (.atom ⟨.natConst 47 1, trivial⟩)
  (.seq (.atom ⟨.natConst 48 0, trivial⟩)
  (.seq (.atom ⟨.natOp .add 45 43 43, trivial⟩)
  (.seq (.atom ⟨.natOp .add 45 45 45, trivial⟩)
  (.seq (.atom ⟨.natOp .add 44 44 45, trivial⟩) addressLoop))))))

def loopStore (s : Store) (addr remaining : ℕ) : Store :=
  { s with nr := Function.update (Function.update s.nr 44 addr) 46 remaining }

def preparedStore (s : Store) : Store :=
  { s with nr := Function.update (Function.update (Function.update s.nr 45 (4 * s.nr 43)) 47 1) 48 0 }

def addressResult (s : Store) : Store :=
  loopStore (preparedStore s) (s.nr 40 + 4 * s.nr 43 + s.nr 41 * s.nr 42) 0

end Address
end NearLinearRSP.TwoResources.Mission
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def layoutFirst : List Atom :=
  [ ⟨.natConst 40 0, trivial⟩, ⟨.natCopy 41 129, trivial⟩,
    ⟨.natCopy 42 124, trivial⟩, ⟨.natConst 43 0, trivial⟩ ]

def layoutSecond : List Atom :=
  [ ⟨.natCopy 138 44, trivial⟩, ⟨.natConst 40 0, trivial⟩,
    ⟨.natCopy 41 138, trivial⟩, ⟨.natCopy 42 124, trivial⟩,
    ⟨.natConst 43 0, trivial⟩ ]

def layoutThird : List Atom :=
  [ ⟨.natCopy 133 44, trivial⟩, ⟨.natCopy 40 130, trivial⟩,
    ⟨.natCopy 41 133, trivial⟩, ⟨.natCopy 42 132, trivial⟩,
    ⟨.natConst 43 0, trivial⟩ ]

def layoutFinish : List Atom :=
  [ ⟨.natCopy 134 44, trivial⟩,
    ⟨.natCopy 135 44, trivial⟩,
    ⟨.natConst 136 64, trivial⟩,
    ⟨.natOp .add 136 136 124, trivial⟩,
    ⟨.natOp .add 136 136 134, trivial⟩,
    ⟨.natCopy 141 136, trivial⟩,
    ⟨.natOp .add 137 136 121, trivial⟩,
    ⟨.natOp .add 142 137 121, trivial⟩,
    ⟨.natOp .add 139 142 121, trivial⟩,
    ⟨.natConst 120 4, trivial⟩,
    ⟨.storeNat 120 129, trivial⟩,
    ⟨.natConst 120 5, trivial⟩,
    ⟨.storeNat 120 138, trivial⟩,
    ⟨.natConst 120 6, trivial⟩,
    ⟨.storeNat 120 135, trivial⟩,
    ⟨.natConst 120 7, trivial⟩,
    ⟨.storeNat 120 136, trivial⟩ ]

def layoutCmd : Cmd :=
  .seq (.atoms layoutFirst) (.seq Address.addressCmd
    (.seq (.atoms layoutSecond) (.seq Address.addressCmd
      (.seq (.atoms layoutThird) (.seq Address.addressCmd (.atoms layoutFinish))))))

def layoutFirstResult (s : Store) : Store :=
  { s with nr := Function.update (Function.update (Function.update (Function.update
      s.nr 40 0) 41 (s.nr 129)) 42 (s.nr 124)) 43 0 }

def layoutSecondResult (s : Store) : Store :=
  { s with nr := Function.update (Function.update (Function.update (Function.update
      (Function.update s.nr 138 (s.nr 44)) 40 0) 41 (s.nr 44)) 42 (s.nr 124)) 43 0 }

def layoutThirdResult (s : Store) : Store :=
  { s with nr := Function.update (Function.update (Function.update (Function.update
      (Function.update s.nr 133 (s.nr 44)) 40 (s.nr 130)) 41 (s.nr 44)) 42 (s.nr 132)) 43 0 }

def layoutFinishResult (s : Store) : Store :=
  let scratch := s.nr 44 + s.nr 124 + 64
  { s with
    nr := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update s.nr
        134 (s.nr 44)) 135 (s.nr 44)) 136 scratch) 141 scratch)
        137 (scratch + s.nr 121)) 142 (scratch + 2 * s.nr 121))
        139 (scratch + 3 * s.nr 121)) 120 7
    nm := Function.update (Function.update (Function.update (Function.update s.nm
      4 (s.nr 129)) 5 (s.nr 138)) 6 (s.nr 44)) 7 scratch }

def layoutState1 (_input : RAMInput) (s : Store) : Store := layoutFirstResult s

def layoutState2 (input : RAMInput) (s : Store) : Store :=
  layoutSecondResult (Address.addressResult (layoutState1 input s))

def layoutState3 (input : RAMInput) (s : Store) : Store :=
  layoutThirdResult (Address.addressResult (layoutState2 input s))

def layoutResult (input : RAMInput) (s : Store) : Store :=
  layoutFinishResult (Address.addressResult (layoutState3 input s))

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def powerCacheInit : List Atom :=
  [⟨.natConst 240 0,trivial⟩,⟨.natCopy 241 135,trivial⟩,
   ⟨.natConst 242 1,trivial⟩,⟨.realConst 240 1,trivial⟩]

def powerCacheBodyOps : List Atom :=
  [⟨.storeReal 241 240,trivial⟩,⟨.realOp .mul 240 240 128,trivial⟩,
   ⟨.natOp .add 241 241 242,trivial⟩,⟨.natOp .add 240 240 242,trivial⟩]

def powerCacheLoop : Cmd := .loop (.nat .lt 240 124) (.atoms powerCacheBodyOps)

def powerCacheCmd : Cmd := .seq (.atoms powerCacheInit) powerCacheLoop

noncomputable def powerCacheState (s : Store) (k : ℕ) : Store :=
  { s with
    nr := Function.update (Function.update (Function.update s.nr 240 k) 241 (s.nr 135+k)) 242 1
    rr := Function.update s.rr 240 (s.rr 128^k)
    rm := fun a => if s.nr 135 ≤ a ∧ a < s.nr 135+k then s.rr 128^(a-s.nr 135) else s.rm a }

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Query
open Structured

def prependAtoms : List Atom := [
  ⟨.natOp .sub 3 3 31, trivial⟩,
  ⟨.storeNat 3 0, trivial⟩,
  ⟨.natOp .add 2 2 31, trivial⟩]

def prependCmd : Cmd := .atoms prependAtoms

def prependResult (s : Store) : Store :=
  { s with
    nr := Function.update (Function.update s.nr 3 (s.nr 3 - 1)) 2 (s.nr 2 + 1)
    nm := Function.update s.nm (s.nr 3 - 1) (s.nr 0) }

def StoresList (mem : ℕ → ℕ) (base : ℕ) (xs : List ℕ) : Prop :=
  ∀ k (hk : k < xs.length), mem (base + k) = xs[k]

def scoreAtoms : List Atom := [
  ⟨.natOp .add 39 21 16, trivial⟩,
  ⟨.loadReal 7 39, trivial⟩,
  ⟨.natOp .add 39 21 17, trivial⟩,
  ⟨.loadReal 8 39, trivial⟩,
  ⟨.loadReal 9 27, trivial⟩,
  ⟨.realConst 10 1, trivial⟩,
  ⟨.realOp .sub 9 10 9, trivial⟩,
  ⟨.realOp .mul 13 7 1, trivial⟩,
  ⟨.realOp .div 13 13 3, trivial⟩,
  ⟨.realOp .mul 14 8 2, trivial⟩,
  ⟨.realOp .div 14 14 4, trivial⟩,
  ⟨.realOp .add 5 9 13, trivial⟩,
  ⟨.realOp .add 5 5 14, trivial⟩]

def scoreCmd : Cmd := .atoms scoreAtoms

noncomputable def scoreResult (input : RAMInput) (s : Store) : Store :=
  evalAtoms input scoreAtoms s

def chooseAtoms : List Atom := [
  ⟨.realCopy 6 5, trivial⟩,
  ⟨.natCopy 18 16, trivial⟩,
  ⟨.natCopy 19 17, trivial⟩,
  ⟨.natCopy 49 27, trivial⟩]

def chooseCmd : Cmd := .branch (.real .lt 5 6) (.atoms chooseAtoms) .skip

noncomputable def chooseResult (input : RAMInput) (s : Store) : Store :=
  if s.rr 5 < s.rr 6 then evalAtoms input chooseAtoms s else s

noncomputable def chooseCost (s : Store) : ℕ := if s.rr 5 < s.rr 6 then 6 else 1

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Query

noncomputable def outputEnd (I : Instance) (ε : ℝ) : ℕ :=
  16 + 4 * I.graph.n + 4 * I.graph.n * outerQ ε ^ 2 * (outerInputs I ε).length

noncomputable def QueryReady (I : Instance) (ε : ℝ) (snapshot : RAMState) : Prop :=
  EncodesOutput I ε snapshot ∧
  snapshot.nm 3 = (activeVertices I).length ∧
  snapshot.nm 4 = 4 * I.graph.n ∧
  snapshot.nm 5 = 4 * I.graph.n * outerQ ε ∧
  outputEnd I ε ≤ snapshot.nm 7 ∧
  ∀ a < outerQ ε, snapshot.rm (snapshot.nm 6 + a) = ((1 + ε / 8) / (1 + ε / 4)) ^ a

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

structure NumericRegs (I : Instance) (ε : ℝ) (s : Store) : Prop extends CoreRegs I ε s where
  realVertices : s.rr 129 = I.graph.n
  minimum : s.rr 150 = firstPositiveLength I
  maximum : s.rr 151 = largestLength I
  lengthSum : s.rr 152 = (I.graph.edges.map (fun e => (I.length e.1 e.2 : ℝ))).sum
  costSum : s.rr 153 = (I.graph.edges.map (fun e => (I.cost e.1 e.2 : ℝ))).sum
  found : s.nr 150 = if (positiveLengths I).isEmpty then 0 else 1
  count : s.nr 132 = (outerInputs I ε).length

noncomputable def graphBase (I : Instance) (ε : ℝ) : ℕ := Query.outputEnd I ε + outerQ ε + 64

noncomputable def headsBase (I : Instance) (ε : ℝ) : ℕ := graphBase I ε + I.graph.n

noncomputable def arrayBase (I : Instance) (ε : ℝ) : ℕ := graphBase I ε + 2*I.graph.n

noncomputable def linksBase (I : Instance) (ε : ℝ) : ℕ := graphBase I ε + 3*I.graph.n

structure LayoutRegs (I : Instance) (ε : ℝ) (s : Store) : Prop where
  span : s.nr 133 = 4*I.graph.n*outerQ ε^2
  outputEnd : s.nr 134 = Query.outputEnd I ε
  powerBase : s.nr 135 = Query.outputEnd I ε
  rowStride : s.nr 138 = 4*I.graph.n*outerQ ε
  map : s.nr 141 = graphBase I ε
  heads : s.nr 137 = headsBase I ε
  array : s.nr 142 = arrayBase I ε
  links : s.nr 139 = linksBase I ε

structure OutputHeaders (I : Instance) (ε : ℝ) (s : Store) : Prop where
  q : s.nm 0 = outerQ ε
  source : s.nm 1 = I.source
  vertices : s.nm 2 = I.graph.n
  vertexStride : s.nm 4 = 4*I.graph.n
  rowStride : s.nm 5 = 4*I.graph.n*outerQ ε
  powerBase : s.nm 6 = Query.outputEnd I ε
  map : s.nm 7 = graphBase I ε
  z : s.rm 0 = (1+ε/8)/(1+ε/4)

structure LayoutReady (I : Instance) (ε : ℝ) (s : Store) : Prop where
  numeric : NumericRegs I ε s
  layout : LayoutRegs I ε s
  headers : OutputHeaders I ε s
  powers : ∀a<outerQ ε, s.rm (Query.outputEnd I ε+a) = ((1+ε/8)/(1+ε/4))^a
  naturalZero : ∀a, 8 ≤ a → s.nm a = 0
  realZero : ∀a, 1 ≤ a → (a < Query.outputEnd I ε ∨ Query.outputEnd I ε+outerQ ε ≤ a) →
    s.rm a = 0

def layoutCacheCmd : Cmd := .seq layoutCmd powerCacheCmd

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def activeScanBody : Cmd :=
  .seq (.atom ⟨.inputNat 140 147, trivial⟩)
    (.seq activeInsert (.atom ⟨.natOp .add 147 147 126, trivial⟩))

def activeScan : Cmd := .loop (.nat .lt 147 148) activeScanBody

def activeLoaded (input : RAMInput) (s : Store) : Store :=
  { s with nr := Function.update s.nr 140 (input.naturals (s.nr 147)) }

def activeStep (input : RAMInput) (s : Store) : Store :=
  { activeResult (activeLoaded input s) with
    nr := Function.update (activeResult (activeLoaded input s)).nr 147 (s.nr 147 + 1) }

def activeScanResult (input : RAMInput) : ℕ → Store → Store
  | 0, s => s
  | k + 1, s => activeScanResult input k (activeStep input s)

def scannedVertices (input : RAMInput) : ℕ → ℕ → List ℕ
  | _, 0 => []
  | start, count + 1 => input.naturals start :: scannedVertices input (start + 1) count

def activeInitAtoms : List Atom :=
  [ ⟨.natConst 143 0, trivial⟩,
    ⟨.natCopy 140 123, trivial⟩,
    ⟨.natConst 147 3, trivial⟩,
    ⟨.natOp .add 148 122 122, trivial⟩,
    ⟨.natOp .add 148 148 147, trivial⟩ ]

def activeInit : Cmd :=
  .seq (Cmd.atoms activeInitAtoms) (.seq activeInsert activeScan)

def activeInitPrepared (s : Store) : Store :=
  { s with
    nr := Function.update (Function.update (Function.update (Function.update s.nr
      143 0) 140 (s.nr 123)) 147 3) 148 (2 * s.nr 122 + 3) }

def activeInitResult (input : RAMInput) (s : Store) : Store :=
  activeScanResult input (2 * s.nr 122) (activeResult (activeInitPrepared s))

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

structure GraphReady (I : Instance) (ε : ℝ) (s : Store) : Prop where
  numeric : NumericRegs I ε s
  layout : LayoutRegs I ε s
  headers : OutputHeaders I ε s
  activeCount : s.nm 3 = (activeVertices I).length
  active : ActiveRep I.graph.n (graphBase I ε) (arrayBase I ε) (activeVertices I) s
  adjacency : AdjacencyPrefix I I.graph.edges.length (headsBase I ε) (linksBase I ε) s.nm
  powers : ∀a<outerQ ε, s.rm (Query.outputEnd I ε+a) = ((1+ε/8)/(1+ε/4))^a
  naturalZero : ∀a, 8 ≤ a → a<graphBase I ε → s.nm a = 0
  realZero : ∀a, 1 ≤ a → (a<Query.outputEnd I ε ∨ Query.outputEnd I ε+outerQ ε≤a) → s.rm a=0

def graphAdjPrepare : List Atom :=
  [⟨.natConst 120 3,trivial⟩,⟨.storeNat 120 143,trivial⟩,
   ⟨.natCopy 163 137,trivial⟩,⟨.natCopy 164 139,trivial⟩]

def graphCmd : Cmd := .seq activeInit (.seq (.atoms graphAdjPrepare) adjacencyScanCmd)

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Queue
open Structured

def capacityDouble : Atom := ⟨.natOp .add 11 11 11, by trivial⟩

def capacityStart : Atom := ⟨.natConst 11 1, by trivial⟩

def chooseCapacity : Cmd :=
  .seq (.atom capacityStart) (.loop (.nat .lt 11 10) (.atom capacityDouble))

def capacityState (s : Store) (k : ℕ) : Store :=
  { s with nr := Function.update s.nr 11 (2 ^ k) }

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

noncomputable def queueCapacity (I : Instance) : ℕ := 2^Nat.clog 2 (activeVertices I).length

noncomputable def queueWinnerBase (I : Instance) (ε : ℝ) : ℕ :=
  linksBase I ε+I.graph.edges.length+16

noncomputable def queueParentBase (I : Instance) (ε : ℝ) : ℕ :=
  queueWinnerBase I ε+2*queueCapacity I

noncomputable def queueTempBase (I : Instance) (ε : ℝ) : ℕ :=
  queueParentBase I ε+2*queueCapacity I

structure SetupReady (I : Instance) (ε : ℝ) (s : Store) : Prop where
  graph : GraphReady I ε s
  capacity : s.nr 11 = queueCapacity I
  winner : s.nr 1 = queueWinnerBase I ε
  parents : s.nr 2 = queueParentBase I ε
  temporary : s.nr 13 = queueTempBase I ε
  activeCount : s.nr 12 = (activeVertices I).length
  zero : s.nr 3 = 0
  one : s.nr 4 = 1
  treeCapacity : s.nr 170 = queueCapacity I
  treeArray : s.nr 171 = arrayBase I ε
  costSentinel : s.rr 280 = ((I.graph.n:ℝ)+1)*
    (1+(I.graph.edges.map (fun e => (I.cost e.1 e.2 : ℝ))).sum)
  lengthSentinel : s.rr 281 = ((I.graph.n:ℝ)+1)*
    (1+(I.graph.edges.map (fun e => (I.length e.1 e.2 : ℝ))).sum)

def heapFinish : List Atom :=
  [⟨.natConst 172 16,trivial⟩,
   ⟨.natOp .add 1 139 122,trivial⟩,⟨.natOp .add 1 1 172,trivial⟩,
   ⟨.natOp .add 2 11 11,trivial⟩,⟨.natOp .add 2 1 2,trivial⟩,
   ⟨.natOp .add 13 11 11,trivial⟩,⟨.natOp .add 13 2 13,trivial⟩,
   ⟨.natCopy 12 143,trivial⟩,⟨.natConst 3 0,trivial⟩,⟨.natConst 4 1,trivial⟩,
   ⟨.natCopy 170 11,trivial⟩,⟨.natCopy 171 142,trivial⟩,
   ⟨.realOp .add 280 129 125,trivial⟩,⟨.realOp .add 282 153 125,trivial⟩,
   ⟨.realOp .mul 280 280 282,trivial⟩,
   ⟨.realOp .add 281 129 125,trivial⟩,⟨.realOp .add 282 152 125,trivial⟩,
   ⟨.realOp .mul 281 281 282,trivial⟩]

def heapCmd : Cmd := .seq (.atom ⟨.natCopy 10 143,trivial⟩)
  (.seq Queue.chooseCapacity (.atoms heapFinish))

def setupCmd : Cmd := .seq scalarCmd (.seq layoutCacheCmd (.seq graphCmd heapCmd))

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

structure RuntimeReady (I : Instance) (ε : ℝ) (s : Store) : Prop where
  numeric : NumericRegs I ε s
  layout : LayoutRegs I ε s
  headers : OutputHeaders I ε s
  activeCount : s.nm 3=(activeVertices I).length
  active : ActiveRep I.graph.n (graphBase I ε) (arrayBase I ε) (activeVertices I) s
  adjacency : AdjacencyPrefix I I.graph.edges.length (headsBase I ε) (linksBase I ε) s.nm
  powers : ∀a<outerQ ε, s.rm (Query.outputEnd I ε+a)=((1+ε/8)/(1+ε/4))^a

noncomputable def treeAllocation (I : Instance) (ε : ℝ) : TreeAllocation I where
  B := queueCapacity I
  height := Nat.clog 2 (activeVertices I).length
  W := queueWinnerBase I ε
  P := queueParentBase I ε
  R := queueTempBase I ε
  map := graphBase I ε
  array := arrayBase I ε
  heads := headsBase I ε
  links := linksBase I ε
  capacity := rfl
  fit := (Queue.capacity_bounds _ (activeVertices_length_pos I)).1
  target_map := by unfold graphBase Query.outputEnd; omega
  map_heads := le_rfl
  heads_array := by unfold headsBase arrayBase; omega
  array_links := by unfold arrayBase linksBase; omega
  links_winner := by unfold queueWinnerBase; omega
  winner_parent := le_rfl
  parent_temp := le_rfl

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Structured

def Cmd.acyclic : Cmd → Bool
  | .skip | .atom _ => true
  | .seq a b | .branch _ a b => a.acyclic && b.acyclic
  | .loop _ _ => false

noncomputable def Cmd.evalAcyclic (input : RAMInput) : Cmd → Store → Store
  | .skip, s => s
  | .atom a, s => a.eval input s
  | .seq a b, s => b.evalAcyclic input (a.evalAcyclic input s)
  | .branch g a b, s => if g.eval s then a.evalAcyclic input s else b.evalAcyclic input s
  | .loop _ _, s => s

end NearLinearRSP.TwoResources.Mission.Structured
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources
attribute [local instance] Classical.propDecidable

def branchFromIndex : Option ℕ → AnswerBranch
  | some r => .inner r
  | none => .absent

def markAccepted (p : ℕ → Bool) (b : AnswerBranch) (r : ℕ) : AnswerBranch :=
  if b = .absent then if p r then .inner r else .absent else b

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured

def seedInit : List Atom :=
  [⟨.natConst 302 0,trivial⟩,⟨.realConst 302 0,trivial⟩]

def writeLength : Cmd := .atoms
  [⟨.natConst 304 1,trivial⟩,⟨.storeNat 300 304,trivial⟩,
   ⟨.storeReal 300 302,trivial⟩]

def writeBudget : Cmd := .atoms
  [⟨.natConst 304 2,trivial⟩,⟨.storeNat 300 304,trivial⟩,
   ⟨.storeReal 300 301,trivial⟩]

def writeAbsent : Cmd := .atom ⟨.storeNat 300 302,trivial⟩

def budgetChoice : Cmd := .branch (.real .eq 121 302)
  (.branch (.real .lt 301 281) writeBudget writeAbsent) writeAbsent

def seedChoice : Cmd := .branch (.nat .eq 307 123) writeLength
  (.branch (.real .lt 300 280)
    (.branch (.real .lt 121 300) budgetChoice writeLength) budgetChoice)

def seedCmd : Cmd := .seq (.atoms seedInit) seedChoice

noncomputable def seedResult (input : RAMInput) (s : Store) : Store :=
  seedCmd.evalAcyclic input s

noncomputable def seedTag (s : Store) : ℕ :=
  if s.nr 307 = s.nr 123 then 1
  else if s.rr 300 < s.rr 280 ∧ s.rr 300 ≤ s.rr 121 then 1
  else if s.rr 121 = 0 ∧ s.rr 301 < s.rr 281 then 2 else 0

def markInit : List Atom :=
  [⟨.natConst 302 0,trivial⟩,⟨.natConst 303 1,trivial⟩,
   ⟨.realConst 303 3,trivial⟩,⟨.realConst 306 4,trivial⟩,
   ⟨.realOp .div 303 303 306,trivial⟩,⟨.loadNat 304 300,trivial⟩]

def markWrite : List Atom :=
  [⟨.natConst 304 3,trivial⟩,⟨.storeNat 300 304,trivial⟩,
   ⟨.natOp .add 306 300 303,trivial⟩,⟨.storeNat 306 301,trivial⟩,
   ⟨.storeReal 300 304,trivial⟩]

def markCmd : Cmd := .seq (.atoms markInit)
  (.branch (.nat .eq 304 302)
    (.branch (.real .lt 305 303) .skip (.atoms markWrite)) .skip)

noncomputable def markResult (input : RAMInput) (s : Store) : Store :=
  markCmd.evalAcyclic input s

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured

def LabelRep (d : Option ℝ) (sentinel value : ℝ) : Prop :=
  value = d.getD sentinel ∧ ∀ x, d = some x → x < sentinel

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured
attribute [local instance] Classical.propDecidable

noncomputable def selectedDistance (I : Instance) (ε : ℝ) (v : ℕ) : AnswerBranch → Option ℝ
  | .absent => none
  | .zeroLength => some 0
  | .zeroBudget => (zeroBudgetTree I v).distance
  | .inner r => ((outerInputs I ε)[r]?).map (fun A => (1+A.δ)*A.L)

noncomputable def RecordRep (I : Instance) (ε : ℝ) (v : ℕ) (b : AnswerBranch)
    (s : Store) : Prop :=
  s.nm (targetAddress v) = branchTag b ∧
  (∀ d, selectedDistance I ε v b = some d → s.rm (targetAddress v) = d) ∧
  (∀ r, b = .inner r → s.nm (targetAddress v+1) = tableBase I ε r)

noncomputable def branchesAfter (I : Instance) (ε : ℝ) (k v : ℕ) : AnswerBranch :=
  (List.range k).foldl
    (markAccepted (fun r => ((outerInputs I ε)[r]?).any (fun A => decide (accepted A v))))
    (answerBranch I 0 v)

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured
attribute [local instance] Classical.propDecidable

def seedLoadOps : List Atom :=
  [⟨.natConst 308 2,trivial⟩,⟨.natOp .add 309 300 308,trivial⟩,
   ⟨.loadReal 300 309,trivial⟩,⟨.natConst 308 1,trivial⟩,
   ⟨.natOp .add 309 309 308,trivial⟩,⟨.loadReal 301 309,trivial⟩]

def seedVisitor : Cmd := .seq (.atoms seedLoadOps) seedCmd

noncomputable def seedVisitorResult (input : RAMInput) (s : Store) : Store :=
  seedResult input (evalAtoms input seedLoadOps s)

def markLoadOps : List Atom :=
  [⟨.natOp .add 308 307 307,trivial⟩,⟨.natOp .add 308 308 308,trivial⟩,
   ⟨.natOp .add 309 301 308,trivial⟩,⟨.loadReal 305 309,trivial⟩]

def markVisitor : Cmd := .seq (.atoms markLoadOps) markCmd

noncomputable def markVisitorResult (input : RAMInput) (s : Store) : Store :=
  markResult input (evalAtoms input markLoadOps s)

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.ActiveIterator
open Structured

def setupAtoms : List Atom :=
  [⟨.natConst 320 0,trivial⟩,⟨.natConst 324 16,trivial⟩,⟨.natConst 325 1,trivial⟩]

def prepareAtoms : List Atom :=
  [⟨.natOp .add 321 142 320,trivial⟩,⟨.loadNat 307 321,trivial⟩,
   ⟨.natOp .add 322 307 307,trivial⟩,⟨.natOp .add 323 322 322,trivial⟩,
   ⟨.natOp .add 300 324 323,trivial⟩]

def incrementAtom : Atom := ⟨.natOp .add 320 320 325,trivial⟩

def body (visitor : Cmd) : Cmd :=
  .seq (.atoms prepareAtoms) (.seq visitor (.atom incrementAtom))

def command (visitor : Cmd) : Cmd :=
  .seq (.atoms setupAtoms) (.loop (.nat .lt 320 143) (body visitor))

def setup (s : Store) : Store :=
  {s with nr := Function.update (Function.update (Function.update s.nr 320 0) 324 16) 325 1}

def prepared (s : Store) : Store :=
  let addr := s.nr 142+s.nr 320
  let v := s.nm addr
  {s with nr := Function.update (Function.update (Function.update
    (Function.update (Function.update s.nr 321 addr) 307 v) 322 (v+v))
    323 ((v+v)+(v+v))) 300 (s.nr 324+((v+v)+(v+v)))}

def advanced (s : Store) : Store :=
  {s with nr := Function.update s.nr 320 (s.nr 320+s.nr 325)}

def Frame (array : ℕ) (xs : List ℕ) (s out : Store) : Prop :=
  (∀ r, r∈[142,143,320,324,325] → out.nr r=s.nr r) ∧
  ∀ k<xs.length, out.nm (array+k)=s.nm (array+k)

def State (array : ℕ) (xs : List ℕ) (k : ℕ) (s : Store) : Prop :=
  s.nr 142=array ∧ s.nr 143=xs.length ∧ s.nr 320=k ∧ s.nr 324=16 ∧ s.nr 325=1 ∧
  ∀ j (hj : j < xs.length), s.nm (array+j)=xs[j]'hj

def prefixFold {α : Type} (step : α→ℕ→α) (initial : α) (xs : List ℕ) (k : ℕ) : α :=
  (xs.take k).foldl step initial

end NearLinearRSP.TwoResources.Mission.ActiveIterator
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

noncomputable def buildRow (A : InnerInput) (T : Table) (i : ℕ) : Table :=
  ((List.range (tickLimit A)).reverse).foldl (fun U j => buildLayer A U i j) T

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured
attribute [local instance] Classical.propDecidable

structure TargetFrame (I : Instance) (s t : Store) : Prop where
  nat : ∀ a, (∀ v < I.graph.n, a ≠ targetAddress v ∧ a ≠ targetAddress v+1) → t.nm a = s.nm a
  real : ∀ a, (∀ v < I.graph.n, a ≠ targetAddress v) → t.rm a = s.rm a

def setAnswer (value : ℕ → AnswerBranch) (f : ℕ → AnswerBranch) (v : ℕ) : ℕ → AnswerBranch :=
  Function.update f v (value v)

def updateAnswer (change : ℕ → AnswerBranch → AnswerBranch)
    (f : ℕ → AnswerBranch) (v : ℕ) : ℕ → AnswerBranch :=
  Function.update f v (change v (f v))

noncomputable def RecordMap (I : Instance) (ε : ℝ) (f : ℕ → AnswerBranch) (s : Store) : Prop :=
  ∀ v < I.graph.n, RecordRep I ε v (f v) s

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured

structure SeedWorld (I : Instance) (s : Store) : Prop where
  source : s.nr 123 = I.source
  budget : s.rr 121 = I.budget
  labels : ∀ v ∈ activeVertices I,
    LabelRep (zeroLengthTree I v).distance (s.rr 280) (s.rm (targetAddress v+2)) ∧
    LabelRep (zeroBudgetTree I v).distance (s.rr 281) (s.rm (targetAddress v+3))

def seedRecordsCmd : Cmd := ActiveIterator.command seedVisitor

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def OutputParents (I : Instance) (s : Store) : Prop :=
  ∀ v ∈ activeVertices I,
    s.nm (targetAddress v+2) = ((zeroLengthTree I v).parent.map (·+1)).getD 0 ∧
    s.nm (targetAddress v+3) = ((zeroBudgetTree I v).parent.map (·+1)).getD 0

noncomputable def OutputTable (I : Instance) (ε : ℝ) (r : ℕ) (A : InnerInput) (s : Store) : Prop :=
  ∀ v ∈ activeVertices I, ∀ i < tickLimit A, ∀ j < tickLimit A,
    let addr := tableAddress I ε r v i j
    let c := buildTable A v i j
    s.rm addr = 1-c.value ∧ s.nm addr = parentTag c.parent ∧
    s.nm (addr+1) = parentVertex c.parent ∧ s.nm (addr+2) = c.rank ∧
    (∀ u, c.parent = .edge u → s.rm (addr+1) = lengthPGF A u v ∧
      s.rm (addr+2) = costPGF A u v)

noncomputable def CompletedTables (I : Instance) (ε : ℝ) (k : ℕ) (s : Store) : Prop :=
  ∀ r < k, ∀ A, (outerInputs I ε)[r]? = some A → OutputTable I ε r A s

noncomputable def FutureZero (I : Instance) (ε : ℝ) (k : ℕ) (s : Store) : Prop :=
  ∀ a, tableBase I ε k ≤ a → a < Query.outputEnd I ε → s.rm a = 0

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured
attribute [local instance] Classical.propDecidable

structure MarkWorld (I : Instance) (ε : ℝ) (r : ℕ) (A : InnerInput) (s : Store) : Prop where
  base : s.nr 301 = tableBase I ε r
  estimate : s.rr 304 = (1+A.δ)*A.L
  mass : ∀ v ∈ activeVertices I,
    s.rm (tableBase I ε r+4*v) = 1-dpValue A (buildTable A) v 0 0

def markRecordsCmd : Cmd := ActiveIterator.command markVisitor

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Outer
open Structured

def initOps : List Atom :=
  [⟨.natConst 243 0,trivial⟩,⟨.natCopy 244 130,trivial⟩,
   ⟨.natConst 245 16,trivial⟩,⟨.natOp .add 246 11 11,trivial⟩,
   ⟨.natOp .add 247 139 122,trivial⟩,⟨.natOp .add 247 247 245,trivial⟩,
   ⟨.natOp .add 248 247 246,trivial⟩,⟨.natCopy 249 11,trivial⟩,
   ⟨.natOp .add 250 248 246,trivial⟩,
   ⟨.realCopy 243 150,trivial⟩,⟨.realOp .add 244 123 125,trivial⟩,
   ⟨.realConst 246 2,trivial⟩,⟨.realOp .div 244 244 246,trivial⟩,
   ⟨.realOp .mul 245 244 121,trivial⟩,⟨.realOp .div 245 127 245,trivial⟩]

def prepareOps : List Atom :=
  [⟨.natCopy 200 244,trivial⟩,⟨.natCopy 201 124,trivial⟩,
   ⟨.natCopy 202 125,trivial⟩,⟨.natOp .add 203 244 133,trivial⟩,
   ⟨.natCopy 204 143,trivial⟩,⟨.natCopy 205 247,trivial⟩,
   ⟨.natCopy 206 248,trivial⟩,⟨.natCopy 207 249,trivial⟩,
   ⟨.natCopy 208 250,trivial⟩,⟨.natCopy 209 138,trivial⟩,
   ⟨.realOp .mul 200 244 243,trivial⟩,⟨.realOp .div 200 127 200,trivial⟩,
   ⟨.realCopy 201 245,trivial⟩,⟨.realCopy 202 128,trivial⟩]

def markOps : List Atom :=
  [⟨.natCopy 301 244,trivial⟩,⟨.realOp .mul 304 123 243,trivial⟩]

def advanceOps : List Atom :=
  [⟨.natOp .add 243 243 126,trivial⟩,⟨.natOp .add 244 244 133,trivial⟩,
   ⟨.realOp .mul 243 243 123,trivial⟩]

def body (table : Cmd) : Cmd := .seq (.atoms prepareOps)
  (.seq table (.seq (.atoms markOps) (.seq TargetRecords.markRecordsCmd (.atoms advanceOps))))

def loopCmd (table : Cmd) : Cmd := .loop (.nat .lt 243 132) (body table)

def command (table : Cmd) : Cmd := .seq (.atoms initOps) (loopCmd table)

noncomputable def initialized (input : RAMInput) (s : Store) : Store := evalAtoms input initOps s

noncomputable def prepared (input : RAMInput) (s : Store) : Store := evalAtoms input prepareOps s

noncomputable def markPrepared (input : RAMInput) (s : Store) : Store := evalAtoms input markOps s

noncomputable def advanced (input : RAMInput) (s : Store) : Store := evalAtoms input advanceOps s

end NearLinearRSP.TwoResources.Mission.Outer
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources
namespace Mission

def poissonProgram : Program :=
  [ .inputNat 0 0,
    .natConst 1 0,
    .inputReal 0 1,
    .realConst 1 0,
    .realOp .sub 1 1 0,
    .exp 2 1,
    .realConst 1 0,
    .realConst 3 1,
    .natConst 1 0,
    .natConst 2 1,
    .natBranch .lt 1 0 11 16,
    .natOp .add 1 1 2,
    .realOp .add 1 1 3,
    .realOp .mul 2 2 0,
    .realOp .div 2 2 1,
    .jump 10,
    .natConst 1 0,
    .storeReal 1 2,
    .halt ]

noncomputable def poissonLoopState (μ : ℝ) (n k : ℕ) : RAMState where
  pc := 10
  halted := false
  nr := Function.update (Function.update (Function.update (fun _ => 0) 0 n) 1 k) 2 1
  rr := Function.update (Function.update (Function.update
    (Function.update (fun _ => 0) 0 μ) 1 k) 2
      (ActuarialValuation.poissonCountMass μ k)) 3 1
  nm := fun _ => 0
  rm := fun _ => 0

noncomputable def poissonFinalState (μ : ℝ) (n : ℕ) : RAMState :=
  { poissonLoopState μ n n with
    pc := 18
    halted := true
    nr := Function.update (poissonLoopState μ n n).nr 1 0
    rm := Function.update (fun _ => 0) 0 (ActuarialValuation.poissonCountMass μ n) }

end Mission
end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped BigOperators
namespace NearLinearRSP.TwoResources.Mission.Expectation
open Structured

def atoms : List Atom → Cmd
  | [] => .skip
  | a :: rest => .seq (.atom a) (atoms rest)

noncomputable def evalAtoms (input : RAMInput) (as : List Atom) (s : Store) : Store :=
  as.foldl (fun t a => Atom.eval a input t) s

structure Frame (s t : Store) : Prop where
  natural : ∀ r, r < 86 ∨ 96 < r → t.nr r = s.nr r
  real : ∀ r, r < 82 ∨ 92 < r → t.rr r = s.rr r
  naturalMemory : t.nm = s.nm
  realMemory : t.rm = s.rm

noncomputable abbrev mass := ActuarialValuation.poissonCountMass

def columnAtoms : List Atom :=
  [⟨.loadReal 91 94, trivial⟩,
   ⟨.realOp .mul 92 83 84, trivial⟩,
   ⟨.realOp .mul 92 92 91, trivial⟩,
   ⟨.realOp .add 82 82 92, trivial⟩,
   ⟨.natOp .add 94 94 89, trivial⟩,
   ⟨.natOp .add 92 92 96, trivial⟩,
   ⟨.realOp .add 86 86 87, trivial⟩,
   ⟨.realOp .mul 84 84 81, trivial⟩,
   ⟨.realOp .div 84 84 86, trivial⟩]

def columnBody : Cmd := atoms columnAtoms

def columnLoop : Cmd := .loop (.nat .lt 92 87) columnBody

structure ColumnContext where
  count : ℕ
  mean : ℝ
  rowMass : ℝ
  base : ℕ
  stride : ℕ
  memory : ℕ → ℝ

noncomputable def ColumnContext.term (c : ColumnContext) (k : ℕ) : ℝ :=
  c.rowMass * mass c.mean k * c.memory (c.base + c.stride * k)

structure ColumnInv (c : ColumnContext) (k : ℕ) (total : ℝ) (s : Store) : Prop where
  count : s.nr 87 = c.count
  stride : s.nr 89 = c.stride
  oneNat : s.nr 96 = 1
  index : s.nr 92 = k
  address : s.nr 94 = c.base + c.stride * k
  mean : s.rr 81 = c.mean
  rowMass : s.rr 83 = c.rowMass
  oneReal : s.rr 87 = 1
  coefficient : s.rr 84 = mass c.mean k
  realIndex : s.rr 86 = (k : ℝ)
  sum : s.rr 82 = total
  memory : s.rm = c.memory

structure ColumnFrame (s t : Store) : Prop where
  natural : ∀ r, r ≠ 92 → r ≠ 94 → t.nr r = s.nr r
  real : ∀ r, r ≠ 82 → r ≠ 84 → r ≠ 86 → r ≠ 91 → r ≠ 92 → t.rr r = s.rr r
  naturalMemory : t.nm = s.nm
  realMemory : t.rm = s.rm

structure RectangleContext where
  rows : ℕ
  cols : ℕ
  lengthMean : ℝ
  costMean : ℝ
  base : ℕ
  stride : ℕ
  rowStride : ℕ
  memory : ℕ → ℝ

noncomputable def RectangleContext.column (c : RectangleContext) (a : ℕ) : ColumnContext :=
  ⟨c.cols, c.costMean, mass c.lengthMean a, c.base + c.rowStride * a,
    c.stride, c.memory⟩

noncomputable def RectangleContext.row (c : RectangleContext) (a : ℕ) : ℝ :=
  ∑ b ∈ Finset.range c.cols, (c.column a).term b

structure RowInv (c : RectangleContext) (a : ℕ) (total : ℝ) (s : Store) : Prop where
  rows : s.nr 86 = c.rows
  cols : s.nr 87 = c.cols
  stride : s.nr 89 = c.stride
  rowStride : s.nr 90 = c.rowStride
  oneNat : s.nr 96 = 1
  index : s.nr 91 = a
  address : s.nr 93 = c.base + c.rowStride * a
  lengthMean : s.rr 80 = c.lengthMean
  costMean : s.rr 81 = c.costMean
  oneReal : s.rr 87 = 1
  coefficient : s.rr 83 = mass c.lengthMean a
  realIndex : s.rr 85 = (a : ℝ)
  costInitial : s.rr 89 = mass c.costMean 0
  sum : s.rr 82 = total
  memory : s.rm = c.memory

def rowPrepare : List Atom :=
  [⟨.natConst 92 0, trivial⟩,
   ⟨.natCopy 94 93, trivial⟩,
   ⟨.realCopy 84 89, trivial⟩,
   ⟨.realConst 86 0, trivial⟩]

def rowFinish : List Atom :=
  [⟨.natOp .add 93 93 90, trivial⟩,
   ⟨.natOp .add 91 91 96, trivial⟩,
   ⟨.realOp .add 85 85 87, trivial⟩,
   ⟨.realOp .mul 83 83 80, trivial⟩,
   ⟨.realOp .div 83 83 85, trivial⟩]

def rowBody : Cmd := .seq (atoms rowPrepare) (.seq columnLoop (atoms rowFinish))

def rowLoop : Cmd := .loop (.nat .lt 91 86) rowBody

def corePrepare : List Atom :=
  [⟨.natConst 91 0, trivial⟩,
   ⟨.natCopy 93 88, trivial⟩,
   ⟨.natConst 96 1, trivial⟩,
   ⟨.realConst 82 0, trivial⟩,
   ⟨.realConst 85 0, trivial⟩,
   ⟨.realConst 87 1, trivial⟩,
   ⟨.realConst 88 0, trivial⟩,
   ⟨.realOp .sub 90 88 80, trivial⟩,
   ⟨.exp 83 90, trivial⟩,
   ⟨.realOp .sub 90 88 81, trivial⟩,
   ⟨.exp 89 90, trivial⟩]

def coreFinish : List Atom := [⟨.realOp .sub 82 87 82, trivial⟩]

def coreCmd : Cmd := .seq (atoms corePrepare) (.seq rowLoop (atoms coreFinish))

def contextOf (s : Store) : RectangleContext :=
  ⟨s.nr 86, s.nr 87, s.rr 80, s.rr 81, s.nr 88, s.nr 89, s.nr 90, s.rm⟩

def prepareIndex : List Atom :=
  [⟨.natCopy 40 82, trivial⟩, ⟨.natCopy 41 80, trivial⟩,
   ⟨.natCopy 42 81, trivial⟩, ⟨.natConst 43 0, trivial⟩]

def prepareCell : List Atom :=
  [⟨.natCopy 42 44, trivial⟩, ⟨.natCopy 40 84, trivial⟩,
   ⟨.natCopy 41 85, trivial⟩, ⟨.natCopy 43 83, trivial⟩]

def prepareStride : List Atom :=
  [⟨.natCopy 88 44, trivial⟩, ⟨.natConst 40 0, trivial⟩,
   ⟨.natCopy 41 85, trivial⟩, ⟨.natCopy 42 80, trivial⟩, ⟨.natConst 43 0, trivial⟩]

def prepareDimensions : List Atom :=
  [⟨.natCopy 90 44, trivial⟩, ⟨.natOp .sub 86 80 81, trivial⟩,
   ⟨.natOp .sub 87 80 82, trivial⟩, ⟨.natCopy 89 85, trivial⟩]

def setupCmd : Cmd :=
  .seq (atoms prepareIndex) (.seq Address.addressCmd
  (.seq (atoms prepareCell) (.seq Address.addressCmd
  (.seq (atoms prepareStride) (.seq Address.addressCmd (atoms prepareDimensions))))))

noncomputable def indexPrepared (input : RAMInput) (s : Store) : Store :=
  evalAtoms input prepareIndex s

noncomputable def indexResult (input : RAMInput) (s : Store) : Store :=
  Address.addressResult (indexPrepared input s)

noncomputable def cellPrepared (input : RAMInput) (s : Store) : Store :=
  evalAtoms input prepareCell (indexResult input s)

noncomputable def cellResult (input : RAMInput) (s : Store) : Store :=
  Address.addressResult (cellPrepared input s)

noncomputable def stridePrepared (input : RAMInput) (s : Store) : Store :=
  evalAtoms input prepareStride (cellResult input s)

noncomputable def strideResult (input : RAMInput) (s : Store) : Store :=
  Address.addressResult (stridePrepared input s)

noncomputable def setupResult (input : RAMInput) (s : Store) : Store :=
  evalAtoms input prepareDimensions (strideResult input s)

structure FullFrame (s t : Store) : Prop where
  natural : ∀ r, (r < 40 ∨ 48 < r) → (r < 86 ∨ 96 < r) → t.nr r = s.nr r
  real : ∀ r, r < 82 ∨ 92 < r → t.rr r = s.rr r
  naturalMemory : t.nm = s.nm
  realMemory : t.rm = s.rm

def nonsaturatedCmd : Cmd := .seq setupCmd coreCmd

def saturatedCmd : Cmd := .atom ⟨.realConst 82 1, trivial⟩

def expectationCmd : Cmd :=
  .branch (.nat .lt 81 80)
    (.branch (.nat .lt 82 80) nonsaturatedCmd saturatedCmd) saturatedCmd

noncomputable def expectedResult (s : Store) : ℝ :=
  if s.nr 80 ≤ s.nr 81 ∨ s.nr 80 ≤ s.nr 82 then 1 else
    1 - ∑ a ∈ Finset.range (s.nr 80 - s.nr 81),
      ∑ b ∈ Finset.range (s.nr 80 - s.nr 82),
        mass (s.rr 80) a * mass (s.rr 81) b *
          s.rm (s.nr 84 + s.nr 85 * ((s.nr 81 + a) * s.nr 80 + (s.nr 82 + b)) + 4 * s.nr 83)

end NearLinearRSP.TwoResources.Mission.Expectation
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

structure Layout (A : InnerInput) where
  base : ℕ
  winner : ℕ
  parent : ℕ
  capacity : ℕ
  height : ℕ
  temp : ℕ
  ordinalMap : ℕ
  activeArray : ℕ
  heads : ℕ
  links : ℕ
  capacity_eq : capacity = 2 ^ height
  active_fit : (activeVertices A.I).length ≤ capacity
  table_before_map : base + 4 * A.I.graph.n * tickLimit A ^ 2 ≤ ordinalMap
  table_before_array : base + 4 * A.I.graph.n * tickLimit A ^ 2 ≤ activeArray
  table_before_heads : base + 4 * A.I.graph.n * tickLimit A ^ 2 ≤ heads
  table_before_links : base + 4 * A.I.graph.n * tickLimit A ^ 2 ≤ links
  map_before_winner : ordinalMap + A.I.graph.n ≤ winner
  array_before_winner : activeArray + (activeVertices A.I).length ≤ winner
  heads_before_winner : heads + A.I.graph.n ≤ winner
  links_before_winner : links + A.I.graph.edges.length ≤ winner
  winner_before_parent : winner + 2 * capacity ≤ parent
  parent_before_temp : parent + 2 * capacity ≤ temp

noncomputable def Layout.address {A : InnerInput} (E : Layout A) (v i j : ℕ) : ℕ :=
  E.base + 4 * ((i * tickLimit A + j) * A.I.graph.n + v)

noncomputable def Constants {A : InnerInput} (E : Layout A) (i j : ℕ) (s : Store) : Prop :=
  s.nr 121 = A.I.graph.n ∧ s.nr 123 = A.I.source ∧ s.nr 124 = tickLimit A ∧
  s.nr 125 = 0 ∧ s.nr 126 = 1 ∧ s.nr 129 = 4 * A.I.graph.n ∧
  s.nr 137 = E.heads ∧ s.nr 139 = E.links ∧ s.nr 141 = E.ordinalMap ∧
  s.nr 142 = E.activeArray ∧
  s.nr 200 = E.base ∧ s.nr 201 = i ∧ s.nr 202 = j ∧
  s.nr 203 = E.address 0 i j ∧ s.nr 204 = (activeVertices A.I).length ∧
  s.nr 205 = E.winner ∧ s.nr 206 = E.parent ∧ s.nr 207 = E.capacity ∧
  s.nr 208 = E.temp ∧ s.nr 209 = 4 * A.I.graph.n * tickLimit A ∧
  s.rr 200 = lengthRate A ∧ s.rr 201 = costRate A ∧ s.rr 202 = zValue A

def GraphMemory {A : InnerInput} (E : Layout A) (s : Store) : Prop :=
  ∀ k v, (activeVertices A.I)[k]? = some v →
    s.nm (E.ordinalMap + v) = k + 1 ∧ s.nm (E.activeArray + k) = v

noncomputable def layerLeaf {A : InnerInput} (E : Layout A) (S : LayerState)
    (node : ℕ) : Queue.Record :=
  if E.capacity ≤ node ∧ node < E.capacity + (activeVertices A.I).length then
    let k := node - E.capacity
    let v := (activeVertices A.I)[k]?.getD 0
    ⟨if v ∈ S.queue then k + 1 else 0, S.keys v⟩
  else ⟨0, 0⟩

noncomputable def Heap {A : InnerInput} (E : Layout A) (S : LayerState) (s : Store) : Prop :=
  Queue.Represents E.capacity E.winner (layerLeaf E S) s ∧
  ∀ u < 2 * E.capacity, s.nm (E.parent + u) = u / 2

noncomputable def Arrays {A : InnerInput} (E : Layout A) (S : LayerState) (s : Store) : Prop :=
  ∀ k v, (activeVertices A.I)[k]? = some v →
    s.rm (E.temp + k) = S.keys v ∧
    s.nm (E.temp + k) = parentTag (S.parents v) ∧
    s.nm (E.temp + (activeVertices A.I).length + k) = parentVertex (S.parents v) ∧
    ∀ u, S.parents v = .edge u →
      s.rm (E.temp + (activeVertices A.I).length + k) = lengthPGF A u v ∧
      s.rm (E.temp + 2 * (activeVertices A.I).length + k) = costPGF A u v

noncomputable def TableValues {A : InnerInput} (E : Layout A) (T : Table) (s : Store) : Prop :=
  ∀ v ∈ activeVertices A.I, ∀ i < tickLimit A, ∀ j < tickLimit A,
    s.rm (E.address v i j) = 1 - (T v i j).value

noncomputable def StoredCell {A : InnerInput} (E : Layout A) (T : Table)
    (v i j : ℕ) (s : Store) : Prop :=
  let addr := E.address v i j
  let c := T v i j
  s.rm addr = 1 - c.value ∧ s.nm addr = parentTag c.parent ∧
  s.nm (addr + 1) = parentVertex c.parent ∧ s.nm (addr + 2) = c.rank ∧
  ∀ u, c.parent = .edge u → s.rm (addr + 1) = lengthPGF A u v ∧
    s.rm (addr + 2) = costPGF A u v

noncomputable def LayerRep {A : InnerInput} (E : Layout A) (i j : ℕ)
    (S : LayerState) (s : Store) : Prop :=
  Constants E i j s ∧ GraphMemory E s ∧ Heap E S s ∧ Arrays E S s ∧
  TableValues E S.table s ∧ S.queue.Sublist (activeVertices A.I) ∧
  s.nr 210 = S.nextRank

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem tableEnd_le_outputEnd (I : Instance) (ε : ℝ) (r : ℕ)
    (hr : r<(outerInputs I ε).length) :
    tableBase I ε r+4*I.graph.n*outerQ ε^2≤Query.outputEnd I ε := by
  have h := Nat.mul_le_mul_left (4*I.graph.n*outerQ ε^2)
    (show r+1≤(outerInputs I ε).length by omega)
  simp only [Nat.mul_add,Nat.mul_one] at h
  unfold tableBase Query.outputEnd
  omega

noncomputable def outerLayout (I : Instance) (ε : ℝ) (hε : 0<ε) (hε1 : ε<1)
    (r : ℕ) (A : InnerInput) (hA : (outerInputs I ε)[r]?=some A) : DP.Layout A := by
  have hp := outerInputs_get_parameters I ε hε hε1 r A hA
  have hI := hp.1
  have hq := hp.2.2.2
  have hr := (List.getElem?_eq_some_iff.mp hA).1
  have ht := tableEnd_le_outputEnd I ε r hr
  have hN := activeVertices_length_le_vertices I
  refine {
    base := tableBase I ε r
    winner := queueWinnerBase I ε
    parent := queueParentBase I ε
    capacity := queueCapacity I
    height := Nat.clog 2 (activeVertices I).length
    temp := queueTempBase I ε
    ordinalMap := graphBase I ε
    activeArray := arrayBase I ε
    heads := headsBase I ε
    links := linksBase I ε
    capacity_eq := rfl
    active_fit := ?_
    table_before_map := ?_
    table_before_array := ?_
    table_before_heads := ?_
    table_before_links := ?_
    map_before_winner := ?_
    array_before_winner := ?_
    heads_before_winner := ?_
    links_before_winner := ?_
    winner_before_parent := le_rfl
    parent_before_temp := le_rfl }
  · rw [hI]
    exact (Queue.capacity_bounds _ (activeVertices_length_pos I)).1
  · rw [hI,hq]; unfold graphBase; omega
  · rw [hI,hq]; unfold arrayBase graphBase; omega
  · rw [hI,hq]; unfold headsBase graphBase; omega
  · rw [hI,hq]; unfold linksBase graphBase; omega
  · rw [hI]; unfold queueWinnerBase linksBase; omega
  · rw [hI]; unfold queueWinnerBase linksBase arrayBase; omega
  · rw [hI]; unfold queueWinnerBase linksBase headsBase; omega
  · rw [hI]; unfold queueWinnerBase; omega

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Outer
open Structured Preprocess

structure Registers (I : Instance) (ε : ℝ) (k : ℕ) (s : Store) : Prop where
  index : s.nr 243 = k
  table : s.nr 244 = tableBase I ε k
  winner : s.nr 247 = queueWinnerBase I ε
  parent : s.nr 248 = queueParentBase I ε
  capacity : s.nr 249 = queueCapacity I
  temporary : s.nr 250 = queueTempBase I ε
  length : s.rr 243 = firstPositiveLength I*(1+ε/4)^k
  factor : s.rr 244 = 1+ε/8
  costRate : s.rr 245 = (outerQ ε : ℝ)/((1+ε/8)*I.budget)

end NearLinearRSP.TwoResources.Mission.Outer
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

def constantNatRegisters : Finset ℕ :=
  {121,123,124,125,126,129,137,139,141,142,200,201,202,203,204,205,206,207,208,209}

def constantRealRegisters : Finset ℕ := {200,201,202}

def BelowFrame (cutoff : ℕ) (s t : Store) : Prop :=
  ∀ a < cutoff, t.nm a = s.nm a ∧ t.rm a = s.rm a

def OutsideTableFrame {A : InnerInput} (E : Layout A) (s t : Store) : Prop :=
  ∀ a < E.winner, a < E.base ∨ E.base+4*A.I.graph.n*tickLimit A^2 ≤ a →
    t.nm a = s.nm a ∧ t.rm a = s.rm a

def LayerContract {A : InnerInput} (E : Layout A) (ε : ℝ) (layerCmd : Cmd) (bound : ℕ) : Prop :=
  ∀ (T : Table) (i j : ℕ) (s : Store), i < tickLimit A → j < tickLimit A →
    Constants E i j s → GraphMemory E s → TableValues E T s →
    Preprocess.AdjacencyPrefix A.I A.I.graph.edges.length E.heads E.links s.nm →
    ∃ t n, Run (encodeInput A.I ε) layerCmd s t n ∧ n ≤ bound ∧
      Constants E i j t ∧ GraphMemory E t ∧ TableValues E (buildLayer A T i j) t ∧
      (∀ v ∈ activeVertices A.I, StoredCell E (buildLayer A T i j) v i j t) ∧
      OutsideTableFrame E s t ∧
      (∀ v ∈ activeVertices A.I, ∀ a < tickLimit A, ∀ b < tickLimit A,
        (a ≠ i ∨ b ≠ j) → StoredCell E T v a b s →
          StoredCell E (buildLayer A T i j) v a b t)

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def OuterTableFrame (I : Instance) (ε : ℝ) (r : ℕ) (s t : Store) : Prop :=
  ∀a<queueWinnerBase I ε, a<tableBase I ε r ∨ tableBase I ε (r+1)≤a →
    t.nm a=s.nm a ∧ t.rm a=s.rm a

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Outer
open Structured Preprocess TargetRecords

structure Invariant (I : Instance) (ε : ℝ) (k : ℕ) (s : Store) : Prop where
  runtime : RuntimeReady I ε s
  registers : Registers I ε k s
  parents : OutputParents I s
  records : RecordMap I ε (branchesAfter I ε k) s
  tables : CompletedTables I ε k s
  future : FutureZero I ε k s

end NearLinearRSP.TwoResources.Mission.Outer
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured

def persistentRegisters : Finset ℕ := Finset.Icc 121 153 ∪ Finset.Icc 243 259

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

def tableColumnPrepare : List Atom :=
  [⟨.natOp .sub 202 202 126,trivial⟩,⟨.natOp .sub 203 203 129,trivial⟩]

def tableRowPrepare : List Atom :=
  [⟨.natOp .sub 201 201 126,trivial⟩,⟨.natCopy 202 124,trivial⟩]

def tableRowCmd (layer : Cmd) : Cmd :=
  .loop (.nat .lt 125 202) (.seq (.atoms tableColumnPrepare) layer)

def tableCmd (layer : Cmd) : Cmd :=
  .loop (.nat .lt 125 201) (.seq (.atoms tableRowPrepare) (tableRowCmd layer))

noncomputable def tableColumnStore (input : RAMInput) (s : Store) : Store :=
  evalAtoms input tableColumnPrepare s

noncomputable def tableRowStore (input : RAMInput) (s : Store) : Store :=
  evalAtoms input tableRowPrepare s

noncomputable def rowTable (A : InnerInput) (T : Table) (i count : ℕ) : Table :=
  ((List.range count).reverse).foldl (fun U j => buildLayer A U i j) T

noncomputable def rowsTable (A : InnerInput) (T : Table) (count : ℕ) : Table :=
  ((List.range count).reverse).foldl (fun U i => rowTable A U i (tickLimit A)) T

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

structure RowResult {A : InnerInput} (E : Layout A) (T R : Table) (i count : ℕ)
    (initial out : Store) : Prop where
  constants : Constants E i 0 out
  graph : GraphMemory E out
  table : TableValues E R out
  adjacency : Preprocess.AdjacencyPrefix A.I A.I.graph.edges.length E.heads E.links out.nm
  stored : ∀ v ∈ activeVertices A.I, ∀ b < count, StoredCell E R v i b out
  frame : OutsideTableFrame E initial out
  kept : ∀ v ∈ activeVertices A.I, ∀ a < tickLimit A, ∀ b < tickLimit A,
    (a ≠ i ∨ count ≤ b) → StoredCell E T v a b initial → StoredCell E R v a b out

structure RowsResult {A : InnerInput} (E : Layout A) (T R : Table) (count : ℕ)
    (initial out : Store) : Prop where
  constants : Constants E 0 0 out
  graph : GraphMemory E out
  table : TableValues E R out
  adjacency : Preprocess.AdjacencyPrefix A.I A.I.graph.edges.length E.heads E.links out.nm
  stored : ∀ v ∈ activeVertices A.I, ∀ a < count, ∀ b < tickLimit A, StoredCell E R v a b out
  frame : OutsideTableFrame E initial out
  kept : ∀ v ∈ activeVertices A.I, ∀ a < tickLimit A, ∀ b < tickLimit A,
    count ≤ a → StoredCell E T v a b initial → StoredCell E R v a b out

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

def writeCellAtoms : List Atom := [
  ⟨.realConst 239 1, trivial⟩,
  ⟨.realOp .sub 239 239 230, trivial⟩,
  ⟨.storeReal 230 239, trivial⟩,
  ⟨.storeNat 230 231, trivial⟩,
  ⟨.natConst 239 1, trivial⟩,
  ⟨.natOp .add 239 230 239, trivial⟩,
  ⟨.storeNat 239 232, trivial⟩,
  ⟨.storeReal 239 231, trivial⟩,
  ⟨.natConst 239 2, trivial⟩,
  ⟨.natOp .add 239 230 239, trivial⟩,
  ⟨.storeNat 239 233, trivial⟩,
  ⟨.storeReal 239 232, trivial⟩]

def writeCellCmd : Cmd := .atoms writeCellAtoms

noncomputable def writtenCell (input : RAMInput) (s : Store) : Store :=
  evalAtoms input writeCellAtoms s

def popLoadAtoms : List Atom := [
  ⟨.natOp .add 239 205 126, trivial⟩,
  ⟨.loadNat 212 239, trivial⟩,
  ⟨.loadReal 230 239, trivial⟩,
  ⟨.natOp .sub 224 212 126, trivial⟩,
  ⟨.natOp .add 239 142 224, trivial⟩,
  ⟨.loadNat 211 239, trivial⟩,
  ⟨.natOp .add 230 211 211, trivial⟩,
  ⟨.natOp .add 230 230 230, trivial⟩,
  ⟨.natOp .add 230 203 230, trivial⟩,
  ⟨.natOp .add 239 208 224, trivial⟩,
  ⟨.loadNat 231 239, trivial⟩,
  ⟨.natOp .add 239 239 204, trivial⟩,
  ⟨.loadNat 232 239, trivial⟩,
  ⟨.loadReal 231 239, trivial⟩,
  ⟨.natOp .add 239 239 204, trivial⟩,
  ⟨.loadReal 232 239, trivial⟩,
  ⟨.natCopy 233 210, trivial⟩]

def deletePrepareAtoms : List Atom := [
  ⟨.natOp .add 0 207 224, trivial⟩,
  ⟨.natCopy 1 205, trivial⟩,
  ⟨.natCopy 2 206, trivial⟩,
  ⟨.natConst 3 0, trivial⟩,
  ⟨.natConst 4 1, trivial⟩,
  ⟨.natConst 10 0, trivial⟩,
  ⟨.realCopy 2 230, trivial⟩]

def popFinish : Atom := ⟨.natOp .add 210 210 126, trivial⟩

def popCmd : Cmd := .seq (.atoms popLoadAtoms)
  (.seq writeCellCmd (.seq (.atoms deletePrepareAtoms)
    (.seq Queue.updateLeaf (.atom popFinish))))

noncomputable def popLoaded (input : RAMInput) (s : Store) : Store :=
  evalAtoms input popLoadAtoms s

def relaxOrdinalOps : List Atom :=
  [⟨.natOp .add 331 141 330,trivial⟩,
   ⟨.loadNat 331 331,trivial⟩,
   ⟨.natOp .sub 332 331 126,trivial⟩,
   ⟨.natOp .add 333 207 332,trivial⟩,
   ⟨.natOp .add 334 205 333,trivial⟩,
   ⟨.loadNat 338 334,trivial⟩]

def relaxExpectationOps : List Atom :=
  [⟨.natCopy 80 124,trivial⟩,⟨.natCopy 81 201,trivial⟩,
   ⟨.natCopy 82 202,trivial⟩,⟨.natCopy 83 211,trivial⟩,
   ⟨.natCopy 84 200,trivial⟩,⟨.natCopy 85 129,trivial⟩,
   ⟨.realOp .mul 80 200 330,trivial⟩,⟨.realOp .mul 81 201 331,trivial⟩]

def relaxOldKeyOps : List Atom :=
  [⟨.natOp .add 335 208 332,trivial⟩,⟨.loadReal 332 335,trivial⟩]

def relaxCommitOps : List Atom :=
  [⟨.realConst 335 1,trivial⟩,
   ⟨.realOp .sub 335 202 335,trivial⟩,
   ⟨.realOp .mul 336 80 335,trivial⟩,⟨.exp 336 336,trivial⟩,
   ⟨.realOp .mul 337 81 335,trivial⟩,⟨.exp 337 337,trivial⟩,
   ⟨.natConst 339 3,trivial⟩,
   ⟨.storeNat 335 339,trivial⟩,⟨.storeReal 335 82,trivial⟩,
   ⟨.natOp .add 336 208 204,trivial⟩,
   ⟨.natOp .add 336 336 332,trivial⟩,
   ⟨.storeNat 336 211,trivial⟩,⟨.storeReal 336 336,trivial⟩,
   ⟨.natOp .add 337 336 204,trivial⟩,⟨.storeReal 337 337,trivial⟩,
   ⟨.natCopy 0 333,trivial⟩,⟨.natCopy 1 205,trivial⟩,
   ⟨.natCopy 2 206,trivial⟩,⟨.natCopy 3 125,trivial⟩,
   ⟨.natCopy 4 126,trivial⟩,⟨.natCopy 10 331,trivial⟩,
   ⟨.realCopy 2 82,trivial⟩]

def relaxCommitCmd : Cmd := .seq (.atoms relaxCommitOps) Queue.updateLeaf

def relaxComputeCmd : Cmd :=
  .seq (.atoms relaxExpectationOps) (.seq Expectation.expectationCmd (.atoms relaxOldKeyOps))

def relaxPresentCmd : Cmd :=
  .seq relaxComputeCmd (.branch (.real .lt 82 332) relaxCommitCmd .skip)

def relaxNonselfCmd : Cmd := .seq (.atoms relaxOrdinalOps)
  (.branch (.nat .eq 338 125) .skip relaxPresentCmd)

def relaxCmd : Cmd := .branch (.nat .eq 330 211) .skip relaxNonselfCmd

noncomputable def relaxOrdinalResult (input : RAMInput) (s : Store) : Store :=
  evalAtoms input relaxOrdinalOps s

noncomputable def relaxExpectationPrepared (input : RAMInput) (s : Store) : Store :=
  evalAtoms input relaxExpectationOps s

noncomputable def relaxOldKeyResult (input : RAMInput) (s : Store) : Store :=
  evalAtoms input relaxOldKeyOps s

noncomputable def relaxCommitPrepared (input : RAMInput) (s : Store) : Store :=
  evalAtoms input relaxCommitOps s

noncomputable def updatedLayer (S : LayerState) (u v : ℕ) (value : ℝ) : LayerState :=
  { S with
    keys := Function.update S.keys v value
    parents := Function.update S.parents v (.edge u) }

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

def outgoingLoadAtoms : List Atom := [
  ⟨.natOp .sub 224 213 126, trivial⟩,
  ⟨.natOp .add 239 224 224, trivial⟩,
  ⟨.natConst 222 4, trivial⟩,
  ⟨.natOp .add 239 239 222, trivial⟩,
  ⟨.inputNat 330 239, trivial⟩,
  ⟨.natConst 222 2, trivial⟩,
  ⟨.natOp .sub 239 239 222, trivial⟩,
  ⟨.inputReal 330 239, trivial⟩,
  ⟨.natOp .add 239 239 126, trivial⟩,
  ⟨.inputReal 331 239, trivial⟩]

def outgoingNextAtoms : List Atom := [
  ⟨.natOp .add 239 139 224, trivial⟩,
  ⟨.loadNat 213 239, trivial⟩]

def outgoingBody : Cmd := .seq (.atoms outgoingLoadAtoms)
  (.seq relaxCmd (.atoms outgoingNextAtoms))

def outgoingLoop : Cmd := .loop (.nat .lt 125 213) outgoingBody

def outgoingStartAtoms : List Atom := [
  ⟨.natOp .add 239 137 211, trivial⟩,
  ⟨.loadNat 213 239, trivial⟩]

def outgoingCmd : Cmd := .seq (.atoms outgoingStartAtoms) outgoingLoop

noncomputable def outgoingLoaded (input : RAMInput) (s : Store) : Store :=
  evalAtoms input outgoingLoadAtoms s

noncomputable def outgoingCost (A : InnerInput) (E : Layout A) : ℕ :=
  100 * (tickLimit A + 1) ^ 2 + 19 * Nat.clog 2 (2 * E.capacity) + 74

noncomputable def poppedCells {A : InnerInput} (E : Layout A) (i j : ℕ)
    (S : LayerState) (s : Store) : Prop :=
  ∀ v ∈ activeVertices A.I, v ∉ S.queue → StoredCell E S.table v i j s

def layerStep : Cmd := .seq popCmd outgoingCmd

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def dpLengthPrepare : List Atom :=
  [⟨.natOp .add 185 181 126,trivial⟩,⟨.realConst 190 0,trivial⟩]

def dpLengthLoad : List Atom :=
  [⟨.natOp .add 186 180 183,trivial⟩,⟨.loadReal 190 186,trivial⟩]

def dpCostPrepare : List Atom :=
  [⟨.natOp .add 185 182 126,trivial⟩,⟨.realConst 191 0,trivial⟩]

def dpCostLoad : List Atom :=
  [⟨.natOp .add 186 180 129,trivial⟩,⟨.loadReal 191 186,trivial⟩]

def dpLengthCmd : Cmd := .seq (.atoms dpLengthPrepare)
  (.branch (.nat .lt 185 124) (.atoms dpLengthLoad) .skip)

def dpCostCmd : Cmd := .seq (.atoms dpCostPrepare)
  (.branch (.nat .lt 185 124) (.atoms dpCostLoad) .skip)

noncomputable def dpLengthResult (input : RAMInput) (s : Store) : Store :=
  let t := evalAtoms input dpLengthPrepare s
  if s.nr 181+s.nr 126 < s.nr 124 then evalAtoms input dpLengthLoad t else t

noncomputable def dpCostResult (input : RAMInput) (s : Store) : Store :=
  let t := evalAtoms input dpCostPrepare s
  if s.nr 182+s.nr 126 < s.nr 124 then evalAtoms input dpCostLoad t else t

def dpChooseLengthOps : List Atom :=
  [⟨.realConst 192 1,trivial⟩,⟨.realOp .sub 2 192 190,trivial⟩,⟨.natConst 184 1,trivial⟩]

def dpChooseCostOps : List Atom :=
  [⟨.realConst 192 1,trivial⟩,⟨.realOp .sub 2 192 191,trivial⟩,⟨.natConst 184 2,trivial⟩]

def dpChooseCmd : Cmd := .branch (.real .lt 190 191) (.atoms dpChooseCostOps) (.atoms dpChooseLengthOps)

noncomputable def dpChooseResult (input : RAMInput) (s : Store) : Store :=
  if s.rr 190 < s.rr 191 then evalAtoms input dpChooseCostOps s
  else evalAtoms input dpChooseLengthOps s

def dpSourceOps : List Atom := [⟨.realConst 2 0,trivial⟩,⟨.natConst 184 0,trivial⟩]

def dpLeafCmd : Cmd := .branch (.nat .eq 175 123) (.atoms dpSourceOps)
  (.seq dpLengthCmd (.seq dpCostCmd dpChooseCmd))

noncomputable def dpLeafResult (input : RAMInput) (s : Store) : Store :=
  if s.nr 175 = s.nr 123 then evalAtoms input dpSourceOps s
  else dpChooseResult input (dpCostResult input (dpLengthResult input s))

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured Preprocess

def fillPrepareAtoms : List Atom := [
  ⟨.natOp .add 226 142 225,trivial⟩,
  ⟨.loadNat 175 226,trivial⟩,
  ⟨.natOp .add 227 175 175,trivial⟩,
  ⟨.natOp .add 227 227 227,trivial⟩,
  ⟨.natOp .add 180 203 227,trivial⟩,
  ⟨.natCopy 181 201,trivial⟩,
  ⟨.natCopy 182 202,trivial⟩,
  ⟨.natCopy 183 209,trivial⟩]

def fillEvalCmd : Cmd := .seq (.atoms fillPrepareAtoms) dpLeafCmd

def fillStoreAtoms : List Atom := [
  ⟨.natOp .add 226 208 225,trivial⟩,
  ⟨.storeReal 226 2,trivial⟩,
  ⟨.storeNat 226 184,trivial⟩,
  ⟨.natOp .add 228 226 204,trivial⟩,
  ⟨.storeNat 228 125,trivial⟩,
  ⟨.natOp .add 225 225 126,trivial⟩]

def fillBody : Cmd := .seq fillEvalCmd (.atoms fillStoreAtoms)

def fillLoop : Cmd := .loop (.nat .lt 225 204) fillBody

def fillInitialKeys : Cmd := .seq (.atom ⟨.natConst 225 0,trivial⟩) fillLoop

noncomputable def fillPrepared (input : RAMInput) (s : Store) : Store :=
  evalAtoms input fillPrepareAtoms s

noncomputable def fillStored (input : RAMInput) (s : Store) : Store :=
  evalAtoms input fillStoreAtoms s

structure FillLayout (A : InnerInput) (T : Table) (i j array base R lengthStride costStride : ℕ)
    (initial : Store) : Prop where
  active : ∀ k v, (activeVertices A.I)[k]? = some v → initial.nm (array+k) = v
  activeBelow : ∀ k < (activeVertices A.I).length, array+k < R
  lengthBelow : ∀ v ∈ activeVertices A.I, i+1 < tickLimit A → base+4*v+lengthStride < R
  lengthValue : ∀ v ∈ activeVertices A.I, i+1 < tickLimit A →
    initial.rm (base+4*v+lengthStride) = 1-dpValue A T v (i+1) j
  costBelow : ∀ v ∈ activeVertices A.I, j+1 < tickLimit A → base+4*v+costStride < R
  costValue : ∀ v ∈ activeVertices A.I, j+1 < tickLimit A →
    initial.rm (base+4*v+costStride) = 1-dpValue A T v i (j+1)

structure FillRegisters (A : InnerInput) (i j array base R lengthStride costStride : ℕ)
    (s : Store) : Prop where
  source : s.nr 123 = A.I.source
  limit : s.nr 124 = tickLimit A
  zero : s.nr 125 = 0
  one : s.nr 126 = 1
  costStride_eq : s.nr 129 = costStride
  array_eq : s.nr 142 = array
  i_eq : s.nr 201 = i
  j_eq : s.nr 202 = j
  base_eq : s.nr 203 = base
  count_eq : s.nr 204 = (activeVertices A.I).length
  keyBase_eq : s.nr 208 = R
  lengthStride_eq : s.nr 209 = lengthStride

structure FillInvariant (A : InnerInput) (T : Table)
    (i j array base R lengthStride costStride : ℕ) (initial : Store) (k : ℕ) (s : Store) : Prop where
  registers : FillRegisters A i j array base R lengthStride costStride s
  counter : s.nr 225 = k
  key : ∀ a v, a < k → (activeVertices A.I)[a]? = some v →
    s.rm (R+a) = (initLayer A T i j).keys v
  tag : ∀ a v, a < k → (activeVertices A.I)[a]? = some v →
    s.nm (R+a) = parentTag ((initLayer A T i j).parents v)
  parent : ∀ a < k, s.nm (R+(activeVertices A.I).length+a) = 0
  naturalFrame : ∀ a, a < R ∨ R+2*(activeVertices A.I).length ≤ a → s.nm a = initial.nm a
  realFrame : ∀ a, a < R ∨ R+(activeVertices A.I).length ≤ a → s.rm a = initial.rm a

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

def initialQueueSetup : List Atom := [
  ⟨.natCopy 1 205,trivial⟩, ⟨.natCopy 2 206,trivial⟩,
  ⟨.natConst 3 0,trivial⟩, ⟨.natConst 4 1,trivial⟩,
  ⟨.natCopy 11 207,trivial⟩, ⟨.natCopy 12 204,trivial⟩,
  ⟨.natCopy 13 208,trivial⟩, ⟨.natConst 210 0,trivial⟩]

def initializeLayer : Cmd :=
  .seq fillInitialKeys (.seq (.atoms initialQueueSetup) Queue.buildQueue)

noncomputable def initialQueueStore (input : RAMInput) (s : Store) : Store :=
  evalAtoms input initialQueueSetup s

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

def layerLoop : Cmd := .loop (.nat .lt 210 204) layerStep

def layerCmd : Cmd := .seq initializeLayer layerLoop

noncomputable def layerCost {A : InnerInput} (E : Layout A) : ℕ :=
  15*E.capacity + (38*Nat.clog 2 (2*E.capacity)+100)*(activeVertices A.I).length +
    outgoingCost A E * A.I.graph.edges.length + 20

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

def buildTableCmd : Cmd := tableCmd layerCmd

noncomputable def tableCost {A : InnerInput} (E : Layout A) : ℕ :=
  ((layerCost E+4)*tickLimit A+5)*tickLimit A+1

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

def outerPersistentRegisters : Finset ℕ := Finset.Icc 121 153 ∪ Finset.Icc 243 259

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.Outer
open Structured Preprocess TargetRecords

noncomputable def iterationBound (I : Instance) (ε : ℝ) : ℕ :=
  1000*((activeVertices I).length+I.graph.edges.length+1)*
    (Nat.clog 2 (2*queueCapacity I)+1)*(outerQ ε+1)^4

def outerCmd : Cmd := command DP.buildTableCmd

end NearLinearRSP.TwoResources.Mission.Outer
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured TargetRecords

def afterTreesCmd : Cmd := .seq seedRecordsCmd Outer.outerCmd

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess

noncomputable def preprocessingInstructionBound (I : Instance) (ε : ℝ) : ℕ :=
  let N := (activeVertices I).length
  let m := I.graph.edges.length
  let B := queueCapacity I
  let H := Nat.clog 2 (2*B)
  let q := outerQ ε
  let G := (outerInputs I ε).length
  (18*q+14*(Nat.log 2 I.graph.n+1)^2+55*m+8*G+3*Nat.clog 2 N+182) +
    (2*(15*B+(38*H+58)*N+(19*H+46)*m+7)+6) + (54*N+4) +
    (1000*(N+m+1)*(H+1)*(q+1)^4*(G+1)+16) + 1

noncomputable def preprocessingConstant : ℝ := 14876397639696436800061

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def preprocessingCmd : Cmd := .seq setupCmd (.seq zeroTreesCmd afterTreesCmd)

def preprocessingProgram : Program := preprocessingCmd.program

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Query
open Structured

structure RectParams where
  base : ℕ
  powerBase : ℕ
  rowStride : ℕ
  colStride : ℕ
  rows : ℕ
  cols : ℕ
  Hlength : ℝ
  Hcost : ℝ
  Mlength : ℝ
  Mcost : ℝ
  memory : ℕ → ℝ

def RectParams.address (E : RectParams) (a b : ℕ) : ℕ :=
  E.base + E.rowStride * a + E.colStride * b

noncomputable def RectParams.score (E : RectParams) (ab : ℕ × ℕ) : ℝ :=
  (1 - E.memory (E.address ab.1 ab.2)) +
    E.memory (E.powerBase + ab.1) * E.Hlength / E.Mlength +
    E.memory (E.powerBase + ab.2) * E.Hcost / E.Mcost

noncomputable def RectParams.choose (E : RectParams) (best candidate : ℕ × ℕ) : ℕ × ℕ :=
  if E.score candidate < E.score best then candidate else best

def RectConstants (E : RectParams) (s : Store) : Prop :=
  s.nr 21 = E.powerBase ∧ s.nr 24 = E.colStride ∧ s.nr 25 = E.rowStride ∧
  s.nr 28 = E.rows ∧ s.nr 29 = E.cols ∧ s.nr 31 = 1 ∧
  s.rr 1 = E.Hlength ∧ s.rr 2 = E.Hcost ∧ s.rr 3 = E.Mlength ∧
  s.rr 4 = E.Mcost ∧ s.rm = E.memory

noncomputable def RectBest (E : RectParams) (best : ℕ × ℕ) (s : Store) : Prop :=
  s.nr 18 = best.1 ∧ s.nr 19 = best.2 ∧
  s.nr 49 = E.address best.1 best.2 ∧ s.rr 6 = E.score best

noncomputable def RectCell (E : RectParams) (a b : ℕ) (best : ℕ × ℕ) (s : Store) : Prop :=
  RectConstants E s ∧ RectBest E best s ∧ s.nr 16 = a ∧ s.nr 17 = b ∧
    s.nr 26 = E.base + E.rowStride * a ∧ s.nr 27 = E.address a b

noncomputable def RectRow (E : RectParams) (a : ℕ) (best : ℕ × ℕ) (s : Store) : Prop :=
  RectConstants E s ∧ RectBest E best s ∧ s.nr 16 = a ∧
    s.nr 26 = E.base + E.rowStride * a

def cellAdvanceAtoms : List Atom := [
  ⟨.natOp .add 17 17 31, trivial⟩,
  ⟨.natOp .add 27 27 24, trivial⟩]

def cellCmd : Cmd := .seq scoreCmd (.seq chooseCmd (.atoms cellAdvanceAtoms))

def rowSetupAtoms : List Atom := [
  ⟨.natConst 17 0, trivial⟩,
  ⟨.natCopy 27 26, trivial⟩]

def rowAdvanceAtoms : List Atom := [
  ⟨.natOp .add 16 16 31, trivial⟩,
  ⟨.natOp .add 26 26 25, trivial⟩]

def rowCmd : Cmd :=
  .seq (.atoms rowSetupAtoms)
    (.seq (.loop (.nat .lt 17 29) cellCmd) (.atoms rowAdvanceAtoms))

def rectangleSetupAtoms : List Atom := [
  ⟨.natConst 16 0, trivial⟩,
  ⟨.natConst 17 0, trivial⟩,
  ⟨.natCopy 26 27, trivial⟩]

def rectangleCmd : Cmd :=
  .seq (.atoms rectangleSetupAtoms)
    (.seq scoreCmd (.seq (.atoms chooseAtoms) (.loop (.nat .lt 16 28) rowCmd)))

noncomputable def rowWinner (E : RectParams) (a b : ℕ) (best : ℕ × ℕ) : ℕ × ℕ :=
  (List.range b).foldl (fun w j => E.choose w (a, j)) best

noncomputable def rowsWinner (E : RectParams) (rows : ℕ) (best : ℕ × ℕ) : ℕ × ℕ :=
  (List.range rows).foldl (fun w a => rowWinner E a E.cols w) best

def rectanglePairs (rows cols : ℕ) : List (ℕ × ℕ) :=
  (List.range rows).flatMap (fun a => (List.range cols).map (fun b => (a, b)))

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace RSP

def retrievalRank (cap width spent rank : ℕ) : ℕ :=
  (cap - spent) * width + rank

end RSP
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

def RetrievalConsistent (A : InnerInput) (S : RetrievalState) : Prop :=
  S.path.head? = some S.front ∧
  S.Hlength = zValue A ^ S.i /
    (8 * ((S.path.zip S.path.tail).map (fun e => lengthPGF A e.1 e.2)).prod) ∧
  S.Hcost = zValue A ^ S.j /
    (8 * ((S.path.zip S.path.tail).map (fun e => costPGF A e.1 e.2)).prod)

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

def ParentSupported (A : InnerInput) (v : ℕ) (p : Parent) : Prop :=
  match p with
  | .none => v = A.I.source
  | .edge u => (u,v) ∈ A.I.graph.edges
  | .lengthTick | .costTick => True

def TableParentsSupported (A : InnerInput) (T : Table) : Prop :=
  ∀ v i j, ParentSupported A v (T v i j).parent

def LayerParentsSupported (A : InnerInput) (S : LayerState) : Prop :=
  TableParentsSupported A S.table ∧ ∀ v, ParentSupported A v (S.parents v)

def RetrievalTerminal (A : InnerInput) (S : RetrievalState) : Prop :=
  S.front = A.I.source ∧ S.i < tickLimit A ∧ S.j < tickLimit A

noncomputable def actualRetrievalRank (A : InnerInput) (S : RetrievalState) : ℕ :=
  RSP.retrievalRank (2 * tickLimit A) ((activeVertices A.I).length + 1)
    (S.i + S.j) (buildTable A S.front S.i S.j).rank

def TickConsistency (A : InnerInput) (i j : ℕ) (S : LayerState) : Prop :=
  ∀ v, (S.parents v = .lengthTick → S.keys v = dpValue A S.table v (i + 1) j) ∧
    (S.parents v = .costTick → S.keys v = dpValue A S.table v i (j + 1))

def EdgeConsistency (A : InnerInput) (i j : ℕ) (S : LayerState) : Prop :=
  ∀ v u, S.parents v = .edge u →
    u ∉ S.queue ∧ S.keys v = edgeExpectation A S.table u v i j

def PoppedParentSync (A : InnerInput) (i j : ℕ) (S : LayerState) : Prop :=
  ∀ v ∈ activeVertices A.I, v ∉ S.queue → (S.table v i j).parent = S.parents v

def layerBefore (x y : ℕ × ℕ) : Prop :=
  y.1 < x.1 ∨ y.1 = x.1 ∧ y.2 < x.2

noncomputable def layerSchedule (A : InnerInput) : List (ℕ × ℕ) :=
  (List.range (tickLimit A)).reverse.flatMap fun i =>
    (List.range (tickLimit A)).reverse.map fun j => (i, j)

noncomputable def runLayers (A : InnerInput) (layers : List (ℕ × ℕ)) (T : Table) : Table :=
  layers.foldl (fun U p => buildLayer A U p.1 p.2) T

structure LayerRanks (A : InnerInput) (i j : ℕ) (S : LayerState) : Prop where
  settled : ∀ v ∈ activeVertices A.I, v ∉ S.queue →
    (S.table v i j).rank < S.nextRank
  pending : ∀ v u, S.parents v = .edge u →
    u ∉ S.queue ∧ (S.table u i j).rank < S.nextRank
  edge : ∀ v ∈ activeVertices A.I, v ∉ S.queue → ∀ u,
    (S.table v i j).parent = .edge u →
      u ∉ S.queue ∧ (S.table u i j).rank < (S.table v i j).rank

def TableRankBound (T : Table) (n : ℕ) : Prop := ∀ v i j, (T v i j).rank ≤ n

def LayerRankBound (S : LayerState) (n : ℕ) : Prop :=
  TableRankBound S.table n ∧ S.nextRank + S.queue.length = n

noncomputable def artificialTickCharge (A : InnerInput) (S : RetrievalState) : ℕ :=
  match (buildTable A S.front S.i S.j).parent with
  | .lengthTick | .costTick => 1
  | _ => 0

noncomputable def graphEdgeCharge (A : InnerInput) (S : RetrievalState) : ℕ :=
  match (buildTable A S.front S.i S.j).parent with
  | .edge _ => 1
  | _ => 0

inductive RetrievalTrace (A : InnerInput) : RetrievalState → RetrievalState → ℕ → ℕ → Prop
  | refl (S : RetrievalState) : RetrievalTrace A S S 0 0
  | step (S T U : RetrievalState) (ticks edges : ℕ)
      (hstep : retrievalStep A S = some T)
      (tail : RetrievalTrace A T U ticks edges) :
      RetrievalTrace A S U (artificialTickCharge A S + ticks) (graphEdgeCharge A S + edges)

inductive ActiveRetrievalTrace (A : InnerInput) : RetrievalState → RetrievalState → ℕ → ℕ → Prop
  | done (S : RetrievalState) (terminal : RetrievalTerminal A S) :
      ActiveRetrievalTrace A S S 0 0
  | step (S T U : RetrievalState) (ticks edges : ℕ)
      (nonsource : S.front ≠ A.I.source) (lengthUnsaturated : S.i < tickLimit A)
      (costUnsaturated : S.j < tickLimit A) (step_eq : retrievalStep A S = some T)
      (tail : ActiveRetrievalTrace A T U ticks edges) :
      ActiveRetrievalTrace A S U (artificialTickCharge A S + ticks) (graphEdgeCharge A S + edges)

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Query
open Structured

def lengthTickAtoms : List Atom := [
  ⟨.natOp .add 9 9 31, trivial⟩,
  ⟨.realOp .mul 1 0 1, trivial⟩,
  ⟨.natOp .add 13 13 25, trivial⟩]

def costTickAtoms : List Atom := [
  ⟨.natOp .add 10 10 31, trivial⟩,
  ⟨.realOp .mul 2 0 2, trivial⟩,
  ⟨.natOp .add 13 13 24, trivial⟩]

def edgeSetupAtoms : List Atom := [
  ⟨.natOp .add 39 13 31, trivial⟩,
  ⟨.loadNat 15 39, trivial⟩,
  ⟨.loadReal 3 39, trivial⟩,
  ⟨.natOp .add 39 39 31, trivial⟩,
  ⟨.loadReal 4 39, trivial⟩,
  ⟨.natOp .sub 28 4 9, trivial⟩,
  ⟨.natOp .sub 29 4 10, trivial⟩,
  ⟨.natCopy 27 13, trivial⟩,
  ⟨.natOp .add 39 0 0, trivial⟩,
  ⟨.natOp .add 39 39 39, trivial⟩,
  ⟨.natOp .sub 27 27 39, trivial⟩,
  ⟨.natOp .add 39 15 15, trivial⟩,
  ⟨.natOp .add 39 39 39, trivial⟩,
  ⟨.natOp .add 27 27 39, trivial⟩]

def edgeFinishAtoms : List Atom := [
  ⟨.natOp .add 9 9 18, trivial⟩,
  ⟨.natOp .add 10 10 19, trivial⟩,
  ⟨.natCopy 0 15, trivial⟩,
  ⟨.natCopy 13 49, trivial⟩,
  ⟨.natOp .add 39 21 18, trivial⟩,
  ⟨.loadReal 7 39, trivial⟩,
  ⟨.realOp .mul 1 7 1, trivial⟩,
  ⟨.realOp .div 1 1 3, trivial⟩,
  ⟨.natOp .add 39 21 19, trivial⟩,
  ⟨.loadReal 8 39, trivial⟩,
  ⟨.realOp .mul 2 8 2, trivial⟩,
  ⟨.realOp .div 2 2 4, trivial⟩]

def edgeCmd : Cmd := .seq (.atoms edgeSetupAtoms)
  (.seq rectangleCmd (.seq (.atoms edgeFinishAtoms) prependCmd))

def innerStepCmd : Cmd := .seq (.atom ⟨.loadNat 14 13, trivial⟩)
  (.branch (.nat .eq 14 31) (.atoms lengthTickAtoms)
    (.branch (.nat .eq 14 32) (.atoms costTickAtoms) edgeCmd))

def innerStopAtoms : List Atom := [
  ⟨.natConst 1 1, trivial⟩,
  ⟨.natConst 50 0, trivial⟩]

def innerBodyCmd : Cmd :=
  .branch (.nat .eq 0 5) (.atoms innerStopAtoms) innerStepCmd

def innerLoopCmd : Cmd := .loop (.nat .lt 30 50) innerBodyCmd

def innerFuelAtoms : List Atom := [
  ⟨.natConst 40 0, trivial⟩,
  ⟨.natOp .add 41 7 31, trivial⟩,
  ⟨.natOp .add 42 4 4, trivial⟩,
  ⟨.natOp .add 42 42 31, trivial⟩,
  ⟨.natConst 43 0, trivial⟩]

noncomputable def innerInitAtoms : List Atom := [
  ⟨.natCopy 11 44, trivial⟩,
  ⟨.natOp .add 3 22 44, trivial⟩,
  ⟨.natConst 2 1, trivial⟩,
  ⟨.storeNat 3 0, trivial⟩,
  ⟨.natConst 9 0, trivial⟩,
  ⟨.natConst 10 0, trivial⟩,
  ⟨.realConst 1 (1 / 8), trivial⟩,
  ⟨.realConst 2 (1 / 8), trivial⟩,
  ⟨.natConst 50 1, trivial⟩,
  ⟨.natOp .add 39 36 31, trivial⟩,
  ⟨.loadNat 8 39, trivial⟩,
  ⟨.natOp .add 39 0 0, trivial⟩,
  ⟨.natOp .add 39 39 39, trivial⟩,
  ⟨.natOp .add 13 8 39, trivial⟩]

noncomputable def innerInitCmd : Cmd := .seq (.atoms innerFuelAtoms)
  (.seq Address.addressCmd (.atoms innerInitAtoms))

noncomputable def innerQueryCmd : Cmd := .seq innerInitCmd innerLoopCmd

structure InnerEnv (A : InnerInput) where
  base : ℕ
  powerBase : ℕ
  scratchBase : ℕ
  naturalMemory : ℕ → ℕ
  realMemory : ℕ → ℝ

noncomputable def InnerEnv.address {A : InnerInput} (E : InnerEnv A) (v i j : ℕ) : ℕ :=
  E.base + 4 * ((i * tickLimit A + j) * A.I.graph.n + v)

noncomputable def InnerLayout {A : InnerInput} (E : InnerEnv A) : Prop :=
  (∀ a < tickLimit A, E.realMemory (E.powerBase + a) = zValue A ^ a) ∧
  (∀ v ∈ activeVertices A.I, ∀ i < tickLimit A, ∀ j < tickLimit A,
    let addr := E.address v i j
    let c := buildTable A v i j
    addr + 2 < E.scratchBase ∧
    E.realMemory addr = 1 - c.value ∧ E.naturalMemory addr = parentTag c.parent ∧
    E.naturalMemory (addr + 1) = parentVertex c.parent ∧
    (∀ u, c.parent = .edge u →
      E.realMemory (addr + 1) = lengthPGF A u v ∧
      E.realMemory (addr + 2) = costPGF A u v))

noncomputable def InnerConstants {A : InnerInput} (E : InnerEnv A) (s : Store) : Prop :=
  s.nr 4 = tickLimit A ∧ s.nr 5 = A.I.source ∧ s.nr 21 = E.powerBase ∧
  s.nr 24 = 4 * A.I.graph.n ∧ s.nr 25 = 4 * A.I.graph.n * tickLimit A ∧
  s.nr 30 = 0 ∧ s.nr 31 = 1 ∧ s.nr 32 = 2 ∧
  s.rr 0 = zValue A ∧ s.rm = E.realMemory

noncomputable def InnerCore {A : InnerInput} (E : InnerEnv A) (S : RetrievalState) (s : Store) : Prop :=
  s.nr 0 = S.front ∧ s.nr 9 = S.i ∧ s.nr 10 = S.j ∧
  s.nr 13 = E.address S.front S.i S.j ∧ s.rr 1 = S.Hlength ∧ s.rr 2 = S.Hcost

def InnerMemory {A : InnerInput} (E : InnerEnv A) (s : Store) : Prop :=
  ∀ a < E.scratchBase, s.nm a = E.naturalMemory a

def InnerPath {A : InnerInput} (E : InnerEnv A) (S : RetrievalState) (s : Store) : Prop :=
  s.nr 2 = S.path.length ∧ StoresList s.nm (s.nr 3) S.path ∧ E.scratchBase ≤ s.nr 3

noncomputable def InnerState {A : InnerInput} (E : InnerEnv A) (S : RetrievalState) (s : Store) : Prop :=
  InnerConstants E s ∧ InnerCore E S s ∧ InnerMemory E s ∧
  InnerPath E S s ∧ s.nr 50 = 1

noncomputable def parentLoaded (input : RAMInput) (s : Store) : Store :=
  Atom.eval (⟨.loadNat 14 13, trivial⟩ : Atom) input s

noncomputable def stopped (input : RAMInput) (s : Store) : Store :=
  evalAtoms input innerStopAtoms s

noncomputable def edgeParams {A : InnerInput} (E : InnerEnv A)
    (S : RetrievalState) (u : ℕ) : RectParams :=
  ⟨E.address u S.i S.j, E.powerBase, 4 * A.I.graph.n * tickLimit A,
    4 * A.I.graph.n, tickLimit A - S.i, tickLimit A - S.j,
    S.Hlength, S.Hcost, lengthPGF A u S.front, costPGF A u S.front, E.realMemory⟩

noncomputable def edgeSetupResult (input : RAMInput) (s : Store) : Store :=
  evalAtoms input edgeSetupAtoms s

noncomputable def edgeFinishResult (input : RAMInput) (s : Store) : Store :=
  evalAtoms input edgeFinishAtoms s

def edgeMoveCmd : Cmd := .seq (.atoms edgeSetupAtoms)
  (.seq rectangleCmd (.atoms edgeFinishAtoms))

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.Query
open Structured

def queryHeaderOps : List Atom :=
  [⟨.natConst 30 0,trivial⟩,⟨.natConst 31 1,trivial⟩,
   ⟨.natConst 32 2,trivial⟩,⟨.natConst 33 3,trivial⟩,⟨.natConst 1 0,trivial⟩,
   ⟨.loadNat 4 30,trivial⟩,⟨.loadReal 0 30,trivial⟩,
   ⟨.loadNat 5 31,trivial⟩,⟨.loadNat 6 32,trivial⟩,
   ⟨.natConst 39 3,trivial⟩,⟨.loadNat 7 39,trivial⟩,
   ⟨.natConst 39 4,trivial⟩,⟨.loadNat 24 39,trivial⟩,
   ⟨.natConst 39 5,trivial⟩,⟨.loadNat 25 39,trivial⟩,
   ⟨.natConst 39 6,trivial⟩,⟨.loadNat 21 39,trivial⟩,
   ⟨.natConst 39 7,trivial⟩,⟨.loadNat 22 39,trivial⟩,
   ⟨.natOp .add 36 0 0,trivial⟩,⟨.natOp .add 36 36 36,trivial⟩,
   ⟨.natConst 39 16,trivial⟩,⟨.natOp .add 36 36 39,trivial⟩,
   ⟨.loadNat 35 36,trivial⟩]

def queryHeaderCmd : Cmd := .atoms queryHeaderOps

noncomputable def queryHeaderResult (input : RAMInput) (s : Store) : Store :=
  evalAtoms input queryHeaderOps s

structure ReadyRegisters (I : Instance) (ε : ℝ) (target : ℕ) (s : Store) : Prop where
  memory : QueryReady I ε (s.at 0)
  front : s.nr 0 = target
  absentFlag : s.nr 1 = 0
  limit : s.nr 4 = outerQ ε
  source : s.nr 5 = I.source
  vertices : s.nr 6 = I.graph.n
  active : s.nr 7 = (activeVertices I).length
  costStride : s.nr 24 = 4*I.graph.n
  lengthStride : s.nr 25 = 4*I.graph.n*outerQ ε
  powers : s.nr 21 = s.nm 6
  scratch : s.nr 22 = s.nm 7
  zero : s.nr 30 = 0
  one : s.nr 31 = 1
  two : s.nr 32 = 2
  three : s.nr 33 = 3
  targetAddr : s.nr 36 = targetAddress target
  branch : s.nr 35 = branchTag (answerBranch I ε target)
  ratio : s.rr 0 = (1+ε/8)/(1+ε/4)

def innerPrepareCmd : Cmd := .seq (.atoms innerFuelAtoms) Address.addressCmd

noncomputable def innerFuelResult (input : RAMInput) (s : Store) : Store :=
  evalAtoms input innerFuelAtoms s

noncomputable def innerPreparedStore (input : RAMInput) (s : Store) : Store :=
  Address.addressResult (innerFuelResult input s)

noncomputable def innerInitialStore (input : RAMInput) (s : Store) : Store :=
  evalAtoms input innerInitAtoms (innerPreparedStore input s)

noncomputable def selectedInnerEnv (I : Instance) (ε : ℝ) (r : ℕ)
    (A : InnerInput) (s : Store) : InnerEnv A :=
  ⟨tableBase I ε r,s.nr 21,s.nr 22,s.nm,s.rm⟩

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Query
open Structured

def treeReadAtoms : List Atom := [
  ⟨.natOp .add 36 0 0, trivial⟩,
  ⟨.natOp .add 36 36 36, trivial⟩,
  ⟨.natConst 37 16, trivial⟩,
  ⟨.natOp .add 36 36 37, trivial⟩,
  ⟨.natOp .add 36 36 35, trivial⟩,
  ⟨.natOp .add 36 36 31, trivial⟩,
  ⟨.loadNat 0 36, trivial⟩,
  ⟨.natOp .sub 0 0 31, trivial⟩,
  ⟨.natOp .sub 7 7 31, trivial⟩]

def treeAdvanceCmd : Cmd := .seq (.atoms treeReadAtoms) prependCmd

def treeStopCmd : Cmd := .atom ⟨.natConst 7 0, trivial⟩

def treeBody : Cmd := .branch (.nat .eq 0 5) treeStopCmd treeAdvanceCmd

def treeLoop : Cmd := .loop (.nat .lt 30 7) treeBody

def treeInitAtoms : List Atom := [
  ⟨.natConst 31 1, trivial⟩,
  ⟨.natConst 30 0, trivial⟩,
  ⟨.natConst 2 1, trivial⟩,
  ⟨.natOp .add 3 22 7, trivial⟩,
  ⟨.storeNat 3 0, trivial⟩]

def treeQueryCmd : Cmd := .seq (.atoms treeInitAtoms)
  (.seq treeLoop (.atom ⟨.natConst 1 1, trivial⟩))

def treeReadResult (s : Store) (u k slot : ℕ) : Store :=
  { s with nr := Function.update (Function.update (Function.update
      (Function.update s.nr 36 (targetAddress (s.nr 0) + slot)) 37 16) 0 u) 7 k }

def treeAdvanceResult (s : Store) (u k slot : ℕ) : Store :=
  prependResult (treeReadResult s u k slot)

def treeStopResult (s : Store) : Store := { s with nr := Function.update s.nr 7 0 }

def treeInitResult (s : Store) : Store :=
  { s with
    nr := Function.update (Function.update (Function.update
      (Function.update s.nr 31 1) 30 0) 2 1) 3 (s.nr 22 + s.nr 7)
    nm := Function.update s.nm (s.nr 22 + s.nr 7) (s.nr 0) }

def TreeParentMemory (I : Instance) (T : ShortestTree) (slot : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ v ∈ activeVertices I, mem (targetAddress v + slot) = ((T v).parent.map (· + 1)).getD 0

structure TreeLoopState (I : Instance) (T : ShortestTree) (slot scratch fuel v : ℕ)
    (P : List ℕ) (s : Store) : Prop where
  front : s.nr 0 = v
  source : s.nr 5 = I.source
  fuel_eq : s.nr 7 = fuel
  slot_eq : s.nr 35 + 1 = slot
  zero : s.nr 30 = 0
  one : s.nr 31 = 1
  space : scratch + fuel ≤ s.nr 3
  length_eq : s.nr 2 = P.length
  path : StoresList s.nm (s.nr 3) P
  parents : TreeParentMemory I T slot s.nm

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.Query
open Structured

noncomputable def queryDispatchCmd : Cmd :=
  .branch (.nat .eq 35 30) .skip
    (.branch (.nat .lt 35 33) treeQueryCmd innerQueryCmd)

noncomputable def queryCmd : Cmd := .seq queryHeaderCmd queryDispatchCmd

noncomputable def queryProgram : Program := queryCmd.program

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal BigOperators
namespace NearLinearRSP.TwoResources.Completeness

noncomputable def quadratic (q M i r : ℝ) : ℝ :=
  (r + (i + r - M) ^ 2) / (q - M) ^ 2

end NearLinearRSP.TwoResources.Completeness
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

def SettledSeparation (A : InnerInput) (S : LayerState) : Prop :=
  ∀ u ∈ activeVertices A.I, u ∉ S.queue →
    ∀ v ∈ S.queue, S.keys u ≤ S.keys v

def SettledBellman (A : InnerInput) (i j : ℕ) (S : LayerState) : Prop :=
  ∀ u ∈ activeVertices A.I, u ∉ S.queue →
    ∀ v, (u, v) ∈ A.I.graph.edges →
      S.keys v ≤ edgeExpectation A S.table u v i j

def StandaloneMissionGoal : Prop :=
    ∃ preprocessing retrieval : Program, ∃ K : ℝ, 0 < K ∧
      ∀ (I : Instance) (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (steps : ℕ) (snapshot : RAMState),
          Execution preprocessing (encodeInput I ε) initialState snapshot steps ∧
          (steps : ℝ) ≤ K * preprocessingScale I ε ∧ EncodesOutput I ε snapshot ∧
          ∀ t : ℕ, t < I.graph.n →
            readDistance snapshot t = answerDistance I ε t ∧
            (∃ (querySteps : ℕ) (out : RAMState),
              Execution retrieval (encodeInput I ε) (queryStart snapshot t) out querySteps ∧
              queryPath out = answerPath I ε t ∧
              (querySteps : ℝ) ≤ K * retrievalScale ε (answerPath I ε t)) ∧
            (∀ d : ℝ, readDistance snapshot t = some d →
              ∃ P : List ℕ, answerPath I ε t = some P ∧
                IsPath I.graph I.source t P ∧ pathWeight I.length P ≤ d ∧
                pathWeight I.cost P ≤ (1 + ε) * I.budget ∧
                ∀ R : List ℕ, Feasible I t R → d ≤ (1 + ε) * pathWeight I.length R) ∧
            ((∃ R : List ℕ, Feasible I t R) → (readDistance snapshot t).isSome = true) ∧
            (∀ P : List ℕ, answerPath I ε t = some P →
              IsPath I.graph I.source t P ∧ pathWeight I.cost P ≤ (1 + ε) * I.budget)

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

def ramStep_of_halted_contract_statement : Prop :=
  ∀ (p : Program) (input : RAMInput) (S : RAMState)
    (h : S.halted = true),
  ramStep p input S = S

def execute_add_contract_statement : Prop :=
  ∀ (p : Program) (input : RAMInput) (a b : ℕ) (S : RAMState),
  execute p input (a + b) S = execute p input b (execute p input a S)

def execute_of_halted_contract_statement : Prop :=
  ∀ (p : Program) (input : RAMInput) (k : ℕ) (S : RAMState)
    (h : S.halted = true),
  execute p input k S = S

def Execution.steps_pos_contract_statement : Prop :=
  ∀ {p : Program} {input : RAMInput}
    {initial final : RAMState} {k : ℕ} (h : Execution p input initial final k)
    (hi : initial.halted = false),
  0 < k

def Execution.steps_unique_contract_statement : Prop :=
  ∀ {p : Program} {input : RAMInput}
    {initial final₁ final₂ : RAMState} {k₁ k₂ : ℕ}
    (h₁ : Execution p input initial final₁ k₁)
    (h₂ : Execution p input initial final₂ k₂),
  k₁ = k₂

def Execution.deterministic_contract_statement : Prop :=
  ∀ {p : Program} {input : RAMInput}
    {initial final₁ final₂ : RAMState} {k₁ k₂ : ℕ}
    (h₁ : Execution p input initial final₁ k₁)
    (h₂ : Execution p input initial final₂ k₂),
  k₁ = k₂ ∧ final₁ = final₂

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources
namespace Mission

def countdown_prefix_contract_statement : Prop :=
  ∀ (input : RAMInput),
  execute countdownProgram input 10 initialState =
      countdownLoopState (512 / (input.reals 0 / 4) ^ 2) 0

def countdown_iteration_contract_statement : Prop :=
  ∀ (input : RAMInput) (x : ℝ) (k : ℕ)
    (hk : (k : ℝ) < x),
  execute countdownProgram input 4 (countdownLoopState x k) =
      countdownLoopState x (k + 1)

def countdown_iterations_contract_statement : Prop :=
  ∀ (input : RAMInput) (x : ℝ) (k : ℕ)
    (hk : k ≤ Nat.ceil x),
  execute countdownProgram input (4 * k) (countdownLoopState x 0) =
      countdownLoopState x k

def countdown_exit_contract_statement : Prop :=
  ∀ (input : RAMInput) (x : ℝ),
  execute countdownProgram input 4 (countdownLoopState x (Nat.ceil x)) =
      countdownFinalState x

def countdown_evaluation_contract_statement : Prop :=
  ∀ (input : RAMInput),
  execute countdownProgram input
      (14 + 4 * Nat.ceil (512 / (input.reals 0 / 4) ^ 2)) initialState =
      countdownFinalState (512 / (input.reals 0 / 4) ^ 2)

def execution_of_bounded_halt_contract_statement : Prop :=
  ∀ (p : Program) (input : RAMInput)
    (initial : RAMState) (n : ℕ)
    (hh : (execute p input n initial).halted = true),
  ∃ steps ≤ n, Execution p input initial (execute p input n initial) steps

def countdownProgram_correct_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ),
  ∃ (steps : ℕ) (out : RAMState),
      Execution countdownProgram (encodeInput I ε) initialState out steps ∧
      steps ≤ 14 + 4 * outerQ ε ∧ out.nm 0 = outerQ ε

def countdownProgram_cost_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1),
  ∃ (steps : ℕ) (out : RAMState),
      Execution countdownProgram (encodeInput I ε) initialState out steps ∧
      (steps : ℝ) ≤ 32786 / ε ^ 2 ∧ out.nm 0 = outerQ ε

end Mission
end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission
namespace Structured

def initialStore_at_contract_statement : Prop :=
  initialStore.at 0 = initialState

def queryStore_at_contract_statement : Prop :=
  ∀ (snapshot : RAMState) (target : ℕ),
  (queryStore snapshot target).at 0 = queryStart snapshot target

def Cmd.compile_length_contract_statement : Prop :=
  ∀ (c : Cmd) (base : ℕ),
  (c.compile base).length = c.size

def run_countdown_loop_contract_statement : Prop :=
  ∀ (input : RAMInput) (g : Guard) (body : Cmd)
    (state : ℕ → Store) (bodyCost : ℕ → ℕ)
    (hexit : g.eval (state 0) = false)
    (hguard : ∀ k, g.eval (state (k + 1)) = true)
    (hbody : ∀ k, Run input body (state (k + 1)) (state k) (bodyCost (k + 1)))
    (k : ℕ),
  Run input (.loop g body) (state k) (state 0) (loopCost bodyCost k)

def loopCost_le_contract_statement : Prop :=
  ∀ (bodyCost : ℕ → ℕ) (bound k : ℕ)
    (h : ∀ j, 1 ≤ j → j ≤ k → bodyCost j ≤ bound),
  loopCost bodyCost k ≤ (bound + 2) * k + 1

def CodeAt.left_contract_statement : Prop :=
  ∀ {p a b : Program} {base : ℕ} (h : CodeAt p base (a ++ b)),
  CodeAt p base a

def CodeAt.right_contract_statement : Prop :=
  ∀ {p a b : Program} {base : ℕ} (h : CodeAt p base (a ++ b)),
  CodeAt p (base + a.length) b

def CodeAt.head_contract_statement : Prop :=
  ∀ {p : Program} {base : ℕ} {i : RAMInstr} {code : Program}
    (h : CodeAt p base (i :: code)),
  p[base]?.getD .halt = i

def codeAt_prefix_contract_statement : Prop :=
  ∀ (pre code post : Program),
  CodeAt (pre ++ code ++ post) pre.length code

def atom_step_contract_statement : Prop :=
  ∀ (a : Atom) (input : RAMInput) (s : Store) (pc : ℕ) (p : Program)
    (h : p[pc]?.getD .halt = a.val),
  ramStep p input (s.at pc) = (a.eval input s).at (pc + 1)

def guard_step_contract_statement : Prop :=
  ∀ (g : Guard) (input : RAMInput) (s : Store)
    (pc yes no : ℕ) (p : Program) (h : p[pc]?.getD .halt = g.instr yes no),
  ramStep p input (s.at pc) = s.at (if g.eval s then yes else no)

def jump_step_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (pc target : ℕ) (p : Program)
    (h : p[pc]?.getD .halt = .jump target),
  ramStep p input (s.at pc) = s.at target

def compile_correct_contract_statement : Prop :=
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (hrun : Run input c s t n),
  ∀ (p : Program) (base : ℕ), CodeAt p base (c.compile base) →
      execute p input n (s.at base) = t.at (base + c.size)

def compiled_execution_contract_statement : Prop :=
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n),
  ∃ (steps : ℕ) (out : RAMState),
      Execution c.program input (s.at 0) out steps ∧ steps ≤ n + 1 ∧
      Store.ofRAM out = t

def compiled_preprocessing_contract_statement : Prop :=
  ∀ {input : RAMInput} {c : Cmd} {t : Store} {n : ℕ}
    (h : Run input c initialStore t n),
  ∃ (steps : ℕ) (out : RAMState),
      Execution c.program input initialState out steps ∧ steps ≤ n + 1 ∧
      Store.ofRAM out = t

def compiled_query_contract_statement : Prop :=
  ∀ {input : RAMInput} {c : Cmd} {t : Store} {n : ℕ}
    (snapshot : RAMState) (target : ℕ)
    (h : Run input c (queryStore snapshot target) t n),
  ∃ (steps : ℕ) (out : RAMState),
      Execution c.program input (queryStart snapshot target) out steps ∧
      steps ≤ n + 1 ∧ Store.ofRAM out = t

end Structured
end NearLinearRSP.TwoResources.Mission
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

def standalone_RSP_FirstMin__fold_choice_le_seed_contract_statement : Prop :=
  ∀ {α : Type} (f : α → ℝ) (xs : List α) (x : α),
  f (xs.foldl (fun a b => if f b < f a then b else a) x) ≤ f x

def standalone_RSP_FirstMin__fold_choice_le_member_contract_statement : Prop :=
  ∀ {α : Type} (f : α → ℝ) (xs : List α)
    (x y : α) (hy : y ∈ xs),
  f (xs.foldl (fun a b => if f b < f a then b else a) x) ≤ f y

def firstMin_le_of_mem_contract_statement : Prop :=
  ∀ {α : Type} (f : α → ℝ) (xs : List α)
    (fallback y : α) (hy : y ∈ xs),
  f (firstMin f xs fallback) ≤ f y

def standalone_RSP_FirstMin__fold_choice_pred_contract_statement : Prop :=
  ∀ {α : Type} (f : α → ℝ) (xs : List α)
    (P : α → Prop) (x : α) (hx : P x) (hall : ∀ y ∈ xs, P y),
  P (xs.foldl (fun a b => if f b < f a then b else a) x)

def firstMin_mem_contract_statement : Prop :=
  ∀ {α : Type} (f : α → ℝ) (xs : List α) (fallback : α)
    (h : xs ≠ []),
  firstMin f xs fallback ∈ xs

def dp_faithfulness_saturated_contract_statement : Prop :=
  ∀ (A : InnerInput) (T : Table) (u v i j : ℕ)
    (h : tickLimit A ≤ i ∨ tickLimit A ≤ j),
  dpValue A T v i j = edgeExpectation A T u v i j

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Queue

def choose_none_left_contract_statement : Prop :=
  ∀ {α : Type} (key : α → ℝ) (x : Option α),
  choose key none x = x

def choose_none_right_contract_statement : Prop :=
  ∀ {α : Type} (key : α → ℝ) (x : Option α),
  choose key x none = x

def choose_assoc_contract_statement : Prop :=
  ∀ {α : Type} (key : α → ℝ) (a b c : Option α),
  choose key (choose key a b) c = choose key a (choose key b c)

def fold_choose_contract_statement : Prop :=
  ∀ {α : Type} (key : α → ℝ) (xs : List α) (a : Option α),
  xs.foldl (fun a b => choose key a (some b)) a = choose key a (winner key xs)

def winner_append_contract_statement : Prop :=
  ∀ {α : Type} (key : α → ℝ) (xs ys : List α),
  winner key (xs ++ ys) = choose key (winner key xs) (winner key ys)

def winner_nil_contract_statement : Prop :=
  ∀ {α : Type} (key : α → ℝ),
  winner key [] = none

def winner_singleton_contract_statement : Prop :=
  ∀ {α : Type} (key : α → ℝ) (x : α),
  winner key [x] = some x

def fold_some_contract_statement : Prop :=
  ∀ {α : Type} (key : α → ℝ) (xs : List α) (x : α),
  xs.foldl (fun a b => choose key a (some b)) (some x) =
      some (xs.foldl (fun a b => if key b < key a then b else a) x)

def winner_eq_firstMin_contract_statement : Prop :=
  ∀ {α : Type} (key : α → ℝ) (xs : List α)
    (fallback : α) (hne : xs ≠ []),
  winner key xs = some (firstMin key xs fallback)

def Tree.champion_eq_winner_contract_statement : Prop :=
  ∀ {α : Type} (key : α → ℝ) {h : ℕ} (t : Tree α h),
  t.champion key = winner key t.leaves

def Tree.champion_eq_firstMin_contract_statement : Prop :=
  ∀ {α : Type} (key : α → ℝ) {h : ℕ}
    (t : Tree α h) (fallback : α) (hne : t.leaves ≠ []),
  t.champion key = some (firstMin key t.leaves fallback)

def Path.index_lt_contract_statement : Prop :=
  ∀ {h : ℕ} (p : Path h),
  p.index < 2 ^ h

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Queue
open Structured

def store_ext_contract_statement : Prop :=
  ∀ (s t : Store)
    (hnr : ∀ a, s.nr a = t.nr a) (hrr : ∀ a, s.rr a = t.rr a)
    (hnm : ∀ a, s.nm a = t.nm a) (hrm : ∀ a, s.rm a = t.rm a),
  s = t

def run_atoms_contract_statement : Prop :=
  ∀ (input : RAMInput) (as : List Atom) (s : Store),
  Run input (atoms as) s (evalAtoms input as s) as.length

def merge_decode_contract_statement : Prop :=
  ∀ (a b : Record),
  (merge a b).decode = choose Record.key a.decode b.decode

def loadChildren_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input loadChildren s = loaded s

def storeLeft_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input storeLeft s = writeRecord s (s.nr 7) ⟨s.nr 8, s.rr 0⟩

def storeRight_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input storeRight s = writeRecord s (s.nr 7) ⟨s.nr 9, s.rr 1⟩

def selectChild_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (hz : s.nr 3 = 0),
  ∃ k ≤ 6, Run input selectChild s
      (writeRecord s (s.nr 7) (merge ⟨s.nr 8, s.rr 0⟩ ⟨s.nr 9, s.rr 1⟩)) k

def refreshNode_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (hz : s.nr 3 = 0),
  ∃ k ≤ 15, Run input refreshNode s (refreshed s) k

def refreshed_record_contract_statement : Prop :=
  ∀ (s : Store),
  readRecord (refreshed s) (s.nr 1 + s.nr 0) =
      merge (readRecord s (s.nr 1 + (s.nr 0 + s.nr 0)))
        (readRecord s (s.nr 1 + (s.nr 0 + s.nr 0 + s.nr 4)))

def refreshed_other_contract_statement : Prop :=
  ∀ (s : Store) (a : ℕ) (ha : a ≠ s.nr 1 + s.nr 0),
  (refreshed s).nm a = s.nm a ∧ (refreshed s).rm a = s.rm a

def refreshed_header_contract_statement : Prop :=
  ∀ (s : Store) (a : ℕ) (ha : a < 5),
  (refreshed s).nr a = s.nr a

def parentHop_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input parentHop s = advanced s

def repairBody_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (hz : s.nr 3 = 0),
  ∃ k ≤ 17, Run input repairBody s (repairStep s) k

def hops_zero_contract_statement : Prop :=
  hops 0 = 0

def hops_pos_contract_statement : Prop :=
  ∀ (n : ℕ) (hn : 0 < n),
  hops n = hops (n / 2) + 1

def hops_le_of_lt_pow_contract_statement : Prop :=
  ∀ (n h : ℕ) (hn : n < 2 ^ h),
  hops n ≤ h

def hops_le_clog_contract_statement : Prop :=
  ∀ (n capacity : ℕ) (hn : n < capacity),
  hops n ≤ Nat.clog 2 capacity

def repairStep_header_contract_statement : Prop :=
  ∀ (s : Store) (a : ℕ) (ha : 0 < a) (ha' : a < 5),
  (repairStep s).nr a = s.nr a

def repairStep_parent_contract_statement : Prop :=
  ∀ (capacity : ℕ) (s : Store) (h : ParentLayout capacity s),
  (repairStep s).nr 0 = s.nr 0 / 2

def repairStep_layout_contract_statement : Prop :=
  ∀ (capacity : ℕ) (s : Store) (h : ParentLayout capacity s),
  ParentLayout capacity (repairStep s)

def repairAncestors_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (capacity : ℕ) (s : Store)
    (h : ParentLayout capacity s),
  ∃ out k, Run input repairAncestors s out k ∧
      k ≤ 19 * hops (s.nr 0) + 1 ∧ out.nr 0 = 0 ∧ ParentLayout capacity out

def repairAncestors_logarithmic_contract_statement : Prop :=
  ∀ (input : RAMInput) (capacity : ℕ) (s : Store)
    (h : ParentLayout capacity s),
  ∃ out k, Run input repairAncestors s out k ∧
      k ≤ 19 * Nat.clog 2 capacity + 1 ∧ out.nr 0 = 0 ∧ ParentLayout capacity out

def ancestors_zero_contract_statement : Prop :=
  ancestors 0 = []

def ancestors_pos_contract_statement : Prop :=
  ∀ (n : ℕ) (hn : 0 < n),
  ancestors n = n :: ancestors (n / 2)

def le_of_mem_ancestors_contract_statement : Prop :=
  ∀ (n v : ℕ) (hv : v ∈ ancestors n),
  v ≤ n

def repairStep_record_other_contract_statement : Prop :=
  ∀ (s : Store) (v : ℕ) (hv : v ≠ s.nr 0),
  readRecord (repairStep s) (s.nr 1 + v) = readRecord s (s.nr 1 + v)

def repairStep_ready_contract_statement : Prop :=
  ∀ (capacity : ℕ) (truth : ℕ → Record) (s : Store)
    (h : ParentLayout capacity s) (hone : s.nr 4 = 1)
    (hpositive : 0 < s.nr 0) (hinternal : s.nr 0 + s.nr 0 + 1 < capacity)
    (hc : Coherent capacity truth) (hr : Ready capacity truth s),
  Ready capacity truth (repairStep s)

def repairAncestors_correct_contract_statement : Prop :=
  ∀ (input : RAMInput) (capacity : ℕ)
    (truth : ℕ → Record) (s : Store) (h : ParentLayout capacity s)
    (hone : s.nr 4 = 1) (hinternal : s.nr 0 + s.nr 0 + 1 < capacity)
    (hc : Coherent capacity truth) (hr : Ready capacity truth s),
  ∃ out k, Run input repairAncestors s out k ∧
      k ≤ 19 * hops (s.nr 0) + 1 ∧ out.nr 0 = 0 ∧
      (∀ a, 0 < a → a < 5 → out.nr a = s.nr a) ∧
      ParentLayout capacity out ∧
      ∀ v < capacity, readRecord out (s.nr 1 + v) = truth v

def writeLeaf_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input writeLeaf s = leafWritten s

def leafWritten_header_contract_statement : Prop :=
  ∀ (s : Store) (a : ℕ) (ha : a ≠ 7),
  (leafWritten s).nr a = s.nr a

def updateStart_header_contract_statement : Prop :=
  ∀ (s : Store) (a : ℕ) (ha : 0 < a) (ha' : a < 5),
  (updateStart s).nr a = s.nr a

def leafWritten_other_contract_statement : Prop :=
  ∀ (s : Store) (a : ℕ) (ha : a ≠ s.nr 1 + s.nr 0),
  (leafWritten s).nm a = s.nm a ∧ (leafWritten s).rm a = s.rm a

def updateStart_parent_contract_statement : Prop :=
  ∀ (capacity : ℕ) (s : Store) (h : ParentLayout capacity s),
  (updateStart s).nr 0 = s.nr 0 / 2

def updateStart_layout_contract_statement : Prop :=
  ∀ (capacity : ℕ) (s : Store) (h : ParentLayout capacity s),
  ParentLayout capacity (updateStart s)

def updateStart_ready_contract_statement : Prop :=
  ∀ (capacity : ℕ) (truth : ℕ → Record) (s : Store)
    (h : ParentLayout capacity s) (hpositive : 0 < s.nr 0)
    (hr : Ready capacity truth s) (hnew : truth (s.nr 0) = ⟨s.nr 10, s.rr 2⟩),
  Ready capacity truth (updateStart s)

def updateLeaf_correct_contract_statement : Prop :=
  ∀ (input : RAMInput) (leaves : ℕ)
    (truth : ℕ → Record) (s : Store) (h : ParentLayout (2 * leaves) s)
    (hone : s.nr 4 = 1) (hpositive : 0 < s.nr 0)
    (hc : Coherent (2 * leaves) truth) (hr : Ready (2 * leaves) truth s)
    (hnew : truth (s.nr 0) = ⟨s.nr 10, s.rr 2⟩),
  ∃ out k, Run input updateLeaf s out k ∧
      k ≤ 19 * Nat.clog 2 (2 * leaves) + 6 ∧ out.nr 0 = 0 ∧
      (∀ a, 0 < a → a < 5 → out.nr a = s.nr a) ∧
      ParentLayout (2 * leaves) out ∧
      ∀ v < 2 * leaves, readRecord out (s.nr 1 + v) = truth v

def run_final_unique_contract_statement : Prop :=
  ∀ {input : RAMInput} {c : Cmd} {s t u : Store} {n m : ℕ}
    (h : Run input c s t n) (h' : Run input c s u m),
  t = u

def WinnerFrame.refl_contract_statement : Prop :=
  ∀ (W capacity : ℕ) (s : Store),
  WinnerFrame W capacity s s

def WinnerFrame.trans_contract_statement : Prop :=
  ∀ (W capacity : ℕ) (s u t : Store)
    (h : WinnerFrame W capacity s u) (h' : WinnerFrame W capacity u t),
  WinnerFrame W capacity s t

def repairStep_frame_contract_statement : Prop :=
  ∀ (capacity : ℕ) (s : Store) (hn : s.nr 0 < capacity),
  WinnerFrame (s.nr 1) capacity s (repairStep s)

def repairAncestors_run_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (capacity : ℕ) (s : Store)
    (h : ParentLayout capacity s),
  ∃ out k, Run input repairAncestors s out k ∧ WinnerFrame (s.nr 1) capacity s out

def repairAncestors_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (capacity : ℕ) (s out : Store) (k : ℕ)
    (h : ParentLayout capacity s) (hrun : Run input repairAncestors s out k),
  WinnerFrame (s.nr 1) capacity s out

def updateStart_frame_contract_statement : Prop :=
  ∀ (capacity : ℕ) (s : Store) (hn : s.nr 0 < capacity),
  WinnerFrame (s.nr 1) capacity s (updateStart s)

def updateLeaf_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (capacity : ℕ) (s out : Store) (k : ℕ)
    (h : ParentLayout capacity s) (hrun : Run input updateLeaf s out k),
  WinnerFrame (s.nr 1) capacity s out

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Structured

def run_atoms_contract_statement : Prop :=
  ∀ (input : RAMInput) (as : List Atom) (s : Store),
  Run input (Cmd.atoms as) s (evalAtoms input as s) as.length

def Cmd.atoms_size_contract_statement : Prop :=
  ∀ (as : List Atom),
  (Cmd.atoms as).size = as.length

def Store.ext_contract_statement : Prop :=
  ∀ {s t : Store} (hnr : s.nr = t.nr)
    (hrr : s.rr = t.rr) (hnm : s.nm = t.nm) (hrm : s.rm = t.rm),
  s = t

def run_atoms_append_contract_statement : Prop :=
  ∀ (input : RAMInput) (as bs : List Atom) (s : Store),
  evalAtoms input (as ++ bs) s = evalAtoms input bs (evalAtoms input as s)

def run_bounded_loop_contract_statement : Prop :=
  ∀ (input : RAMInput) (g : Guard) (body : Cmd)
    (limit bound : ℕ) (P : ℕ → Store → Prop)
    (hguard : ∀ k s, k ≤ limit → P k s → g.eval s = decide (k < limit))
    (hstep : ∀ k s, k < limit → P k s →
      ∃ t n, Run input body s t n ∧ P (k + 1) t ∧ n ≤ bound)
    (k : ℕ) (s : Store) (hk : k ≤ limit) (hs : P k s),
  ∃ t n, Run input (.loop g body) s t n ∧ P limit t ∧
      n ≤ (bound + 2) * (limit - k) + 1

end NearLinearRSP.TwoResources.Mission.Structured
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def treeLeafAtoms_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input treeLeafAtoms s = treeLeafPrepared s

def treeLeafPrepare_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  ∃ steps ≤ 13, Run input treeLeafPrepare s (treeLeafReady s) steps

def treeLeafReady_values_contract_statement : Prop :=
  ∀ (s : Store) (hz : s.nr 3 = 0) (hone : s.nr 4 = 1),
  (treeLeafReady s).nr 0 = s.nr 170 + s.nr 172 ∧
    (treeLeafReady s).nr 10 = s.nr 172 + 1 ∧
    (treeLeafReady s).nr 175 = s.nm (s.nr 171 + s.nr 172) ∧
    (treeLeafReady s).nm (targetAddress (s.nm (s.nr 171 + s.nr 172)) + s.nr 173) = 0 ∧
    (treeLeafReady s).rr 2 =
      (if s.nm (s.nr 171 + s.nr 172) = s.nr 123 then 0 else s.rr 170)

def treeLeafReady_queue_header_contract_statement : Prop :=
  ∀ (s : Store) (r : ℕ) (hr : 0 < r) (hr' : r < 5),
  (treeLeafReady s).nr r = s.nr r

def treeInitializeLeaf_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (B : ℕ)
    (truth : ℕ → Queue.Record) (s : Store)
    (hp : Queue.ParentLayout (2 * B) (treeLeafReady s))
    (hone : s.nr 4 = 1) (hpositive : 0 < s.nr 170 + s.nr 172)
    (hc : Queue.Coherent (2 * B) truth)
    (hr : Queue.Ready (2 * B) truth (treeLeafReady s))
    (hnew : truth (s.nr 170 + s.nr 172) =
      ⟨s.nr 172 + 1, if s.nm (s.nr 171 + s.nr 172) = s.nr 123 then 0 else s.rr 170⟩),
  ∃ out steps, Run input treeInitializeLeaf s out steps ∧
      steps ≤ 19 * Nat.clog 2 (2 * B) + 19 ∧
      Queue.ParentLayout (2 * B) out ∧
      ∀ v < 2 * B, Queue.readRecord out (s.nr 1 + v) = truth v

def treeSeedBody_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  ∃ steps ≤ 16, Run input treeSeedBody s (treeSeedStep input s) steps

def treeSeedStep_counter_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (treeSeedStep input s).nr 172 = s.nr 172 + s.nr 4

def treeSeedStep_fixed_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (treeSeedStep input s).nr 4 = s.nr 4 ∧
    (treeSeedStep input s).nr 12 = s.nr 12

def treeSeedStep_memory_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (treeSeedStep input s).nm =
      Function.update s.nm (targetAddress (s.nm (s.nr 171 + s.nr 172)) + s.nr 173) (s.nr 3) ∧
    (treeSeedStep input s).rm = Function.update s.rm (s.nr 13 + s.nr 172)
      (if s.nm (s.nr 171 + s.nr 172) = s.nr 123 then 0 else s.rr 170)

def treeSeedLoop_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (remaining : ℕ) (s : Store)
    (hone : s.nr 4 = 1) (hend : s.nr 172 + remaining = s.nr 12),
  ∃ steps ≤ 18 * remaining + 1,
      Run input (.loop (.nat .lt 172 12) treeSeedBody) s
        (treeSeedSteps input remaining s) steps

def treeSeed_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (hone : s.nr 4 = 1),
  ∃ steps ≤ 18 * s.nr 12 + 2,
      Run input treeSeed s (treeSeedSteps input (s.nr 12) (treeSeedStart s)) steps

def treeSeedStep_nr_fixed_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (r : ℕ)
    (hr : r ∈ [3,4,12,13,123,171,173]),
  (treeSeedStep input s).nr r = s.nr r

def treeSeedStep_top_fixed_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (treeSeedStep input s).rr 170 = s.rr 170

def TreeSeedInv.step_contract_statement : Prop :=
  ∀ {xs : List ℕ} {A R source off k : ℕ} {top : ℝ} {s : Store}
    (h : TreeSeedInv xs A R source off top k s) (input : RAMInput)
    (hk : k < xs.length)
    (hspace : ∀ v ∈ xs, targetAddress v + off < A),
  TreeSeedInv xs A R source off top (k + 1) (treeSeedStep input s)

def TreeSeedInv.steps_contract_statement : Prop :=
  ∀ {xs : List ℕ} {A R source off k : ℕ} {top : ℝ} {s : Store}
    (h : TreeSeedInv xs A R source off top k s) (input : RAMInput)
    (remaining : ℕ) (hend : k + remaining = xs.length)
    (hspace : ∀ v ∈ xs, targetAddress v + off < A),
  TreeSeedInv xs A R source off top xs.length (treeSeedSteps input remaining s)

def treeSeed_correct_contract_statement : Prop :=
  ∀ (input : RAMInput) (xs : List ℕ) (A R source off : ℕ) (top : ℝ)
    (s : Store) (hlen : s.nr 12 = xs.length) (hA : s.nr 171 = A)
    (hR : s.nr 13 = R) (hsource : s.nr 123 = source) (hoff : s.nr 173 = off)
    (hz : s.nr 3 = 0) (hone : s.nr 4 = 1) (htop : s.rr 170 = top)
    (harray : ∀ j v, xs[j]? = some v → s.nm (A + j) = v)
    (hspace : ∀ v ∈ xs, targetAddress v + off < A),
  ∃ out steps, Run input treeSeed s out steps ∧ steps ≤ 18 * xs.length + 2 ∧
      TreeSeedInv xs A R source off top xs.length out

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Structured

def Atom.nat_frame_contract_statement : Prop :=
  ∀ (a : Atom) (input : RAMInput) (s : Store) (r : ℕ)
    (h : r ∉ a.natWrites),
  (a.eval input s).nr r = s.nr r

def Atom.real_frame_contract_statement : Prop :=
  ∀ (a : Atom) (input : RAMInput) (s : Store) (r : ℕ)
    (h : r ∉ a.realWrites),
  (a.eval input s).rr r = s.rr r

def Atom.natMemory_frame_contract_statement : Prop :=
  ∀ (a : Atom) (input : RAMInput) (s : Store)
    (h : a.writesNatMemory = false),
  (a.eval input s).nm = s.nm

def Atom.realMemory_frame_contract_statement : Prop :=
  ∀ (a : Atom) (input : RAMInput) (s : Store)
    (h : a.writesRealMemory = false),
  (a.eval input s).rm = s.rm

def Run.nat_frame_contract_statement : Prop :=
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (r : ℕ) (hr : r ∉ c.natWrites),
  t.nr r = s.nr r

def Run.real_frame_contract_statement : Prop :=
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (r : ℕ) (hr : r ∉ c.realWrites),
  t.rr r = s.rr r

def Run.natMemory_frame_contract_statement : Prop :=
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (hw : c.writesNatMemory = false),
  t.nm = s.nm

def Run.realMemory_frame_contract_statement : Prop :=
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (hw : c.writesRealMemory = false),
  t.rm = s.rm

end NearLinearRSP.TwoResources.Mission.Structured
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def TreeSeedInv.step_memory_frame_contract_statement : Prop :=
  ∀ {xs : List ℕ} {A R source off k : ℕ} {top : ℝ}
    {s : Store} (h : TreeSeedInv xs A R source off top k s) (input : RAMInput)
    (hk : k < xs.length) (a : ℕ)
    (hn : ∀ v ∈ xs, a ≠ targetAddress v + off)
    (hr : a < R ∨ R + xs.length ≤ a),
  (treeSeedStep input s).nm a = s.nm a ∧ (treeSeedStep input s).rm a = s.rm a

def TreeSeedInv.steps_memory_frame_contract_statement : Prop :=
  ∀ {xs : List ℕ} {A R source off k : ℕ} {top : ℝ}
    {s : Store} (h : TreeSeedInv xs A R source off top k s) (input : RAMInput)
    (remaining : ℕ) (hend : k + remaining = xs.length)
    (hspace : ∀ v ∈ xs, targetAddress v + off < A) (a : ℕ)
    (hn : ∀ v ∈ xs, a ≠ targetAddress v + off)
    (hr : a < R ∨ R + xs.length ≤ a),
  (treeSeedSteps input remaining s).nm a = s.nm a ∧
      (treeSeedSteps input remaining s).rm a = s.rm a

def treeSeed_register_frame_contract_statement : Prop :=
  ∀ {input : RAMInput} {s out : Store} {steps r : ℕ}
    (h : Run input treeSeed s out steps)
    (hr : r ∉ ({0,10,172,174,175,176,177,178} : Finset ℕ)),
  out.nr r = s.nr r

def treeSeed_real_register_frame_contract_statement : Prop :=
  ∀ {input : RAMInput} {s out : Store} {steps r : ℕ}
    (h : Run input treeSeed s out steps) (hr : r ≠ 2),
  out.rr r = s.rr r

def treeSeedStart_inv_contract_statement : Prop :=
  ∀ (xs : List ℕ) (A R source off : ℕ) (top : ℝ) (s : Store)
    (hlen : s.nr 12 = xs.length) (hA : s.nr 171 = A) (hR : s.nr 13 = R)
    (hsource : s.nr 123 = source) (hoff : s.nr 173 = off)
    (hz : s.nr 3 = 0) (hone : s.nr 4 = 1) (htop : s.rr 170 = top)
    (harray : ∀ j v, xs[j]? = some v → s.nm (A + j) = v),
  TreeSeedInv xs A R source off top 0 (treeSeedStart s)

def treeSeed_framed_contract_statement : Prop :=
  ∀ (input : RAMInput) (xs : List ℕ) (A R source off : ℕ) (top : ℝ)
    (s : Store) (hlen : s.nr 12 = xs.length) (hA : s.nr 171 = A)
    (hR : s.nr 13 = R) (hsource : s.nr 123 = source) (hoff : s.nr 173 = off)
    (hz : s.nr 3 = 0) (hone : s.nr 4 = 1) (htop : s.rr 170 = top)
    (harray : ∀ j v, xs[j]? = some v → s.nm (A + j) = v)
    (hspace : ∀ v ∈ xs, targetAddress v + off < A),
  ∃ out steps, Run input treeSeed s out steps ∧ steps ≤ 18 * xs.length + 2 ∧
      TreeSeedInv xs A R source off top xs.length out ∧
      (∀ a, (∀ v ∈ xs, a ≠ targetAddress v + off) →
        (a < R ∨ R + xs.length ≤ a) → out.nm a = s.nm a ∧ out.rm a = s.rm a)

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Queue

def heapTruth_internal_contract_statement : Prop :=
  ∀ (B : ℕ) (leaf : ℕ → Record) (v : ℕ)
    (hv : 0 < v) (hB : v < B),
  heapTruth B leaf v = merge (heapTruth B leaf (v + v)) (heapTruth B leaf (v + v + 1))

def heapTruth_leaf_contract_statement : Prop :=
  ∀ (B : ℕ) (leaf : ℕ → Record) (v : ℕ)
    (hv : B ≤ v),
  heapTruth B leaf v = leaf v

def heapTruth_coherent_contract_statement : Prop :=
  ∀ (B : ℕ) (leaf : ℕ → Record),
  Coherent (2 * B) (heapTruth B leaf)

def merge_self_contract_statement : Prop :=
  ∀ (r : Record),
  merge r r = r

def heapTruth_const_contract_statement : Prop :=
  ∀ (B : ℕ) (r : Record) (v : ℕ),
  heapTruth B (fun _ => r) v = r

def mem_ancestors_self_contract_statement : Prop :=
  ∀ (n : ℕ) (hn : 0 < n),
  n ∈ ancestors n

def parent_mem_ancestors_contract_statement : Prop :=
  ∀ (n v : ℕ) (hv : v ∈ ancestors n) (hp : 0 < v / 2),
  v / 2 ∈ ancestors n

def child_not_mem_ancestors_contract_statement : Prop :=
  ∀ (k v : ℕ) (hv : 0 < v) (hk : v ∉ ancestors k),
  v + v ∉ ancestors k ∧ v + v + 1 ∉ ancestors k

def heapTruth_frame_contract_statement : Prop :=
  ∀ (B : ℕ) (leaf leaf' : ℕ → Record) (k : ℕ)
    (hk : 0 < k) (hchange : ∀ v, v ≠ k → leaf' v = leaf v),
  ∀ v, v ∉ ancestors k → heapTruth B leaf' v = heapTruth B leaf v

def leafRecords_add_contract_statement : Prop :=
  ∀ (leaf : ℕ → Record) (start a b : ℕ),
  leafRecords leaf start (a+b) =
      leafRecords leaf start a ++ leafRecords leaf (start+a) b

def heapTruth_decode_subtree_contract_statement : Prop :=
  ∀ (B : ℕ) (leaf : ℕ → Record) (h v : ℕ)
    (hv : 0 < v) (hlo : B ≤ v * 2^h) (hhi : (v+1)*2^h ≤ 2*B),
  (heapTruth B leaf v).decode =
      winner Record.key (leafRecords leaf (v * 2^h) (2^h))

def heapTruth_root_contract_statement : Prop :=
  ∀ (h : ℕ) (leaf : ℕ → Record),
  (heapTruth (2^h) leaf 1).decode = winner Record.key (leafRecords leaf (2^h) (2^h))

def choose_map_contract_statement : Prop :=
  ∀ {α β : Type} (key : β → ℝ) (f : α → β) (a b : Option α),
  choose key (a.map f) (b.map f) = (choose (key ∘ f) a b).map f

def winner_map_contract_statement : Prop :=
  ∀ {α β : Type} (key : β → ℝ) (f : α → β) (xs : List α),
  winner key (xs.map f) = (winner (key ∘ f) xs).map f

def heapTruth_firstMin_contract_statement : Prop :=
  ∀ (h : ℕ) (leaf : ℕ → Record) (xs : List ℕ)
    (encode : ℕ → Record) (hslots : leafRecords leaf (2^h) (2^h) = xs.map encode)
    (fallback : ℕ) (hne : xs ≠ []),
  (heapTruth (2^h) leaf 1).decode =
      some (encode (firstMin (fun v => (encode v).key) xs fallback))

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory
namespace RSP.Tails

def mass_nonneg_contract_statement : Prop :=
  ∀ (r : ℝ≥0) (n : ℕ),
  0 ≤ mass r n

def mass_succ_mul_contract_statement : Prop :=
  ∀ (r : ℝ≥0) (n : ℕ),
  mass r (n + 1) * (n + 1 : ℝ) = (r : ℝ) * mass r n

def mass_hasSum_contract_statement : Prop :=
  ∀ (r : ℝ≥0),
  HasSum (mass r) 1

def poisson_pgf_hasSum_contract_statement : Prop :=
  ∀ (r : ℝ≥0) (z : ℝ),
  HasSum (fun n : ℕ => mass r n * z ^ n) (Real.exp ((r : ℝ) * (z - 1)))

def poisson_pgf_contract_statement : Prop :=
  ∀ (r : ℝ≥0) (z : ℝ),
  (∫ n : ℕ, z ^ n ∂poissonMeasure r) = Real.exp ((r : ℝ) * (z - 1))

def firstMoment_hasSum_contract_statement : Prop :=
  ∀ (r : ℝ≥0),
  HasSum (fun n : ℕ => mass r n * (n : ℝ)) (r : ℝ)

def factorialMoment_two_hasSum_contract_statement : Prop :=
  ∀ (r : ℝ≥0),
  HasSum (fun n : ℕ => mass r n * ((n : ℝ) * ((n : ℝ) - 1))) ((r : ℝ) ^ 2)

def secondMoment_hasSum_contract_statement : Prop :=
  ∀ (r : ℝ≥0),
  HasSum (fun n : ℕ => mass r n * (n : ℝ) ^ 2) ((r : ℝ) ^ 2 + (r : ℝ))

def poisson_integrable_sq_contract_statement : Prop :=
  ∀ (r : ℝ≥0),
  Integrable (fun n : ℕ => (n : ℝ) ^ 2) (poissonMeasure r)

def poisson_memLp_two_contract_statement : Prop :=
  ∀ (r : ℝ≥0),
  MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonMeasure r)

def poisson_mean_contract_statement : Prop :=
  ∀ (r : ℝ≥0),
  (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = (r : ℝ)

def poisson_secondMoment_contract_statement : Prop :=
  ∀ (r : ℝ≥0),
  (∫ n : ℕ, (n : ℝ) ^ 2 ∂poissonMeasure r) = (r : ℝ) ^ 2 + (r : ℝ)

def poisson_variance_contract_statement : Prop :=
  ∀ (r : ℝ≥0),
  variance (fun n : ℕ => (n : ℝ)) (poissonMeasure r) = (r : ℝ)

def poisson_upper_tail_contract_statement : Prop :=
  ∀ (r : ℝ≥0) (a : ℝ) (ha : (r : ℝ) < a),
  poissonMeasure r {n : ℕ | a ≤ (n : ℝ)} ≤
      ENNReal.ofReal ((r : ℝ) / (a - (r : ℝ)) ^ 2)

def poisson_lower_tail_contract_statement : Prop :=
  ∀ (r : ℝ≥0) (a : ℝ) (ha : a < (r : ℝ)),
  poissonMeasure r {n : ℕ | (n : ℝ) ≤ a} ≤
      ENNReal.ofReal ((r : ℝ) / ((r : ℝ) - a) ^ 2)

def completeness_ratio_contract_statement : Prop :=
  ∀ (q ε : ℝ) (hq : 0 < q) (hε : 0 < ε),
  (q / (1 + ε / 2)) / (q - q / (1 + ε / 2)) ^ 2 =
      (4 + 2 * ε) / (q * ε ^ 2)

def soundness_ratio_contract_statement : Prop :=
  ∀ (q ε : ℝ) (hq : 0 < q) (hε : 0 < ε),
  (q * (1 + ε) / (1 + ε / 2)) /
        (q * (1 + ε) / (1 + ε / 2) - q) ^ 2 =
      (4 + 6 * ε + 2 * ε ^ 2) / (q * ε ^ 2)

def completeness_ratio_le_contract_statement : Prop :=
  ∀ (q ε : ℝ) (k : ℕ) (hk : 0 < k)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2),
  (q / (1 + ε / 2)) / (q - q / (1 + ε / 2)) ^ 2 ≤
      1 / (8 * (k : ℝ))

def soundness_ratio_le_contract_statement : Prop :=
  ∀ (q ε : ℝ) (k : ℕ) (hk : 0 < k)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2),
  (q * (1 + ε) / (1 + ε / 2)) /
        (q * (1 + ε) / (1 + ε / 2) - q) ^ 2 ≤
      1 / (8 * (k : ℝ))

def poisson_completeness_tail_contract_statement : Prop :=
  ∀ (r : ℝ≥0) (q ε : ℝ) (k : ℕ) (hk : 0 < k)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2) (hr : (r : ℝ) = q / (1 + ε / 2)),
  (poissonMeasure r).real {n : ℕ | q ≤ (n : ℝ)} ≤ 1 / (8 * (k : ℝ))

def poisson_completeness_tail_of_le_contract_statement : Prop :=
  ∀ (r : ℝ≥0) (q ε : ℝ) (k : ℕ) (hk : 0 < k)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2) (hr : (r : ℝ) ≤ q / (1 + ε / 2)),
  (poissonMeasure r).real {n : ℕ | q ≤ (n : ℝ)} ≤ 1 / (8 * (k : ℝ))

def poisson_soundness_tail_contract_statement : Prop :=
  ∀ (r : ℝ≥0) (q ε : ℝ) (k : ℕ) (hk : 0 < k)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2)
    (hr : (r : ℝ) = q * (1 + ε) / (1 + ε / 2)),
  (poissonMeasure r).real {n : ℕ | (n : ℝ) < q} ≤ 1 / (8 * (k : ℝ))

def resource_union_bound_contract_statement : Prop :=
  ∀ {Ω : Type u_1} [MeasurableSpace Ω]
    (μ : Measure Ω) (k : ℕ) (hk : 0 < k) (events : Fin k → Set Ω)
    (h : ∀ i, μ.real (events i) ≤ 1 / (8 * (k : ℝ))),
  μ.real (⋃ i, events i) ≤ 1 / 8

def poisson_completeness_union_contract_statement : Prop :=
  ∀ {Ω : Type u_1} [MeasurableSpace Ω]
    (μ : Measure Ω) (k : ℕ) (hk : 0 < k) (q ε : ℝ)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2)
    (r : ℝ≥0) (hr : (r : ℝ) = q / (1 + ε / 2))
    (X : Fin k → Ω → ℕ) (hX : ∀ i, HasLaw (X i) (poissonMeasure r) μ),
  μ.real (⋃ i, {ω | q ≤ (X i ω : ℝ)}) ≤ 1 / 8

def poisson_completeness_union_of_le_contract_statement : Prop :=
  ∀ {Ω : Type u_1} [MeasurableSpace Ω]
    (μ : Measure Ω) (k : ℕ) (hk : 0 < k) (q ε : ℝ)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2)
    (r : Fin k → ℝ≥0) (hr : ∀ i, (r i : ℝ) ≤ q / (1 + ε / 2))
    (X : Fin k → Ω → ℕ) (hX : ∀ i, HasLaw (X i) (poissonMeasure (r i)) μ),
  μ.real (⋃ i, {ω | q ≤ (X i ω : ℝ)}) ≤ 1 / 8

def countdown_pos_contract_statement : Prop :=
  ∀ (k : ℕ) (ε : ℝ) (hk : 0 < k) (hε : 0 < ε),
  0 < countdown k ε

def countdown_sufficient_contract_statement : Prop :=
  ∀ (k : ℕ) (ε : ℝ) (hε : 0 < ε),
  128 * (k : ℝ) ≤ (countdown k ε : ℝ) * ε ^ 2

def poisson_soundness_union_contract_statement : Prop :=
  ∀ {Ω : Type u_1} [MeasurableSpace Ω]
    (μ : Measure Ω) (k : ℕ) (hk : 0 < k) (q ε : ℝ)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2)
    (r : ℝ≥0) (hr : (r : ℝ) = q * (1 + ε) / (1 + ε / 2))
    (X : Fin k → Ω → ℕ) (hX : ∀ i, HasLaw (X i) (poissonMeasure r) μ),
  μ.real (⋃ i, {ω | (X i ω : ℝ) < q}) ≤ 1 / 8

end RSP.Tails
end

set_option autoImplicit false
section
set_option autoImplicit false
open NearLinearRSP.TwoResources
namespace RSP.PoissonBridge

def lengthRate_nonneg_contract_statement : Prop :=
  ∀ (A : InnerInput),
  0 ≤ lengthRate A

def costRate_nonneg_contract_statement : Prop :=
  ∀ (A : InnerInput),
  0 ≤ costRate A

def poissonCountMass_nonneg_contract_statement : Prop :=
  ∀ (r : ℝ) (hr : 0 ≤ r) (n : ℕ),
  0 ≤ ActuarialValuation.poissonCountMass r n

def poissonCountMass_hasSum_contract_statement : Prop :=
  ∀ (r : ℝ) (hr : 0 ≤ r),
  HasSum (ActuarialValuation.poissonCountMass r) 1

def poissonCountMass_sum_le_one_contract_statement : Prop :=
  ∀ (r : ℝ) (hr : 0 ≤ r) (n : ℕ),
  (∑ a ∈ Finset.range n, ActuarialValuation.poissonCountMass r a) ≤ 1

def edgeMass_nonneg_contract_statement : Prop :=
  ∀ (A : InnerInput) (u v a b : ℕ),
  0 ≤ edgeMass A u v a b

def edgeMass_rectangle_eq_contract_statement : Prop :=
  ∀ (A : InnerInput) (u v na nb : ℕ),
  (∑ a ∈ Finset.range na, ∑ b ∈ Finset.range nb, edgeMass A u v a b) =
      (∑ a ∈ Finset.range na,
        ActuarialValuation.poissonCountMass (lengthRate A * A.I.length u v) a) *
      (∑ b ∈ Finset.range nb,
        ActuarialValuation.poissonCountMass (costRate A * A.I.cost u v) b)

def edgeMass_rectangle_nonneg_contract_statement : Prop :=
  ∀ (A : InnerInput) (u v na nb : ℕ),
  0 ≤ ∑ a ∈ Finset.range na, ∑ b ∈ Finset.range nb, edgeMass A u v a b

def edgeMass_rectangle_le_one_contract_statement : Prop :=
  ∀ (A : InnerInput) (u v na nb : ℕ),
  (∑ a ∈ Finset.range na, ∑ b ∈ Finset.range nb, edgeMass A u v a b) ≤ 1

def edgeMass_sum_le_one_contract_statement : Prop :=
  ∀ (A : InnerInput) (u v i j : ℕ),
  (∑ a ∈ Finset.range (tickLimit A - i),
      ∑ b ∈ Finset.range (tickLimit A - j), edgeMass A u v a b) ≤ 1

end RSP.PoissonBridge
end

set_option autoImplicit false
section
namespace NearLinearRSP.TwoResources
open scoped BigOperators

def standalone_RSP_TableBounds__foldl_invariant_contract_statement : Prop :=
  ∀ {α β : Type u_1} (f : β → α → β) (P : β → Prop)
    (xs : List α) (b : β) (hb : P b)
    (hf : ∀ b a, P b → P (f b a)),
  P (xs.foldl f b)

def putCell_range_contract_statement : Prop :=
  ∀ (T : Table) (v i j : ℕ) (c : Cell)
    (hT : TableRange T) (hc : 0 ≤ c.value ∧ c.value ≤ 1),
  TableRange (putCell T v i j c)

def dpValue_range_contract_statement : Prop :=
  ∀ (A : InnerInput) (T : Table) (hT : TableRange T)
    (v i j : ℕ),
  0 ≤ dpValue A T v i j ∧ dpValue A T v i j ≤ 1

def edgeExpectation_range_contract_statement : Prop :=
  ∀ (A : InnerInput) (T : Table) (hT : TableRange T)
    (u v i j : ℕ),
  0 ≤ edgeExpectation A T u v i j ∧ edgeExpectation A T u v i j ≤ 1

def initLayer_range_contract_statement : Prop :=
  ∀ (A : InnerInput) (T : Table) (hT : TableRange T)
    (i j : ℕ),
  LayerRange (initLayer A T i j)

def relaxEdge_range_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hS : LayerRange S),
  LayerRange (relaxEdge A i j u S e)

def popLayer_range_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hS : LayerRange S),
  LayerRange (popLayer A i j S)

def buildLayer_range_contract_statement : Prop :=
  ∀ (A : InnerInput) (T : Table) (hT : TableRange T)
    (i j : ℕ),
  TableRange (buildLayer A T i j)

def buildTable_range_contract_statement : Prop :=
  ∀ (A : InnerInput),
  TableRange (buildTable A)

def dpValue_buildTable_nonneg_contract_statement : Prop :=
  ∀ (A : InnerInput) (v i j : ℕ),
  0 ≤ dpValue A (buildTable A) v i j

def dpValue_buildTable_le_one_contract_statement : Prop :=
  ∀ (A : InnerInput) (v i j : ℕ),
  dpValue A (buildTable A) v i j ≤ 1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

def activeVertices_edge_left_contract_statement : Prop :=
  ∀ (I : Instance) (u v : ℕ)
    (h : (u,v) ∈ I.graph.edges),
  u ∈ activeVertices I

def activeVertices_edge_right_contract_statement : Prop :=
  ∀ (I : Instance) (u v : ℕ)
    (h : (u,v) ∈ I.graph.edges),
  v ∈ activeVertices I

def putCell_same_contract_statement : Prop :=
  ∀ (T : Table) (v i j : ℕ) (c : Cell),
  putCell T v i j c v i j = c

def putCell_other_vertex_contract_statement : Prop :=
  ∀ (T : Table) (v w i j : ℕ) (c : Cell) (h : w ≠ v),
  putCell T v i j c w i j = T w i j

def putCell_other_layer_contract_statement : Prop :=
  ∀ (T : Table) (v w i j a b : ℕ) (c : Cell)
    (h : a ≠ i ∨ b ≠ j),
  putCell T v i j c w a b = T w a b

def relaxEdge_table_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ),
  (relaxEdge A i j u S e).table = S.table

def relaxEdge_queue_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ),
  (relaxEdge A i j u S e).queue = S.queue

def relaxEdge_nextRank_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ),
  (relaxEdge A i j u S e).nextRank = S.nextRank

def relaxEdge_keys_outside_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hv : v ∉ S.queue),
  (relaxEdge A i j u S e).keys v = S.keys v

def relaxEdge_parents_outside_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hv : v ∉ S.queue),
  (relaxEdge A i j u S e).parents v = S.parents v

def relaxEdge_keys_le_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (e : ℕ × ℕ),
  (relaxEdge A i j u S e).keys v ≤ S.keys v

def standalone_Mission_QueueStructure__fold_preserves_contract_statement : Prop :=
  ∀ {α β γ : Type u_1} (f : β → α → β) (p : β → γ)
    (hf : ∀ s a, p (f s a) = p s) (xs : List α) (s : β),
  p (xs.foldl f s) = p s

def relaxAll_table_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState),
  (relaxAll A i j u S).table = S.table

def relaxAll_queue_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState),
  (relaxAll A i j u S).queue = S.queue

def relaxAll_nextRank_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState),
  (relaxAll A i j u S).nextRank = S.nextRank

def relaxAll_keys_outside_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (hv : v ∉ S.queue),
  (relaxAll A i j u S).keys v = S.keys v

def relaxAll_parents_outside_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (hv : v ∉ S.queue),
  (relaxAll A i j u S).parents v = S.parents v

def popLayer_queue_length_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState),
  (popLayer A i j S).queue.length = S.queue.length - 1

def popLayer_queue_subset_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState),
  (popLayer A i j S).queue ⊆ S.queue

def popLayer_other_layer_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (v a b : ℕ) (h : a ≠ i ∨ b ≠ j),
  (popLayer A i j S).table v a b = S.table v a b

def queueRun_zero_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState),
  queueRun A i j 0 S = S

def queueRun_succ_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState),
  queueRun A i j (n + 1) S = popLayer A i j (queueRun A i j n S)

def queueRun_queue_length_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState),
  (queueRun A i j n S).queue.length = S.queue.length - n

def queueRun_queue_subset_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState),
  (queueRun A i j n S).queue ⊆ S.queue

def queueRun_other_layer_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (v a b : ℕ) (h : a ≠ i ∨ b ≠ j),
  (queueRun A i j n S).table v a b = S.table v a b

def buildLayer_other_layer_contract_statement : Prop :=
  ∀ (A : InnerInput) (T : Table) (i j v a b : ℕ)
    (h : a ≠ i ∨ b ≠ j),
  buildLayer A T i j v a b = T v a b

def buildLayer_queue_exhausted_contract_statement : Prop :=
  ∀ (A : InnerInput) (T : Table) (i j : ℕ),
  (queueRun A i j (activeVertices A.I).length (initLayer A T i j)).queue = []

def popLayer_queue_nodup_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (h : S.queue.Nodup),
  (popLayer A i j S).queue.Nodup

def queueRun_queue_nodup_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (h : S.queue.Nodup),
  (queueRun A i j n S).queue.Nodup

def popLayer_sync_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hdup : S.queue.Nodup) (hS : PoppedSync A i j S),
  PoppedSync A i j (popLayer A i j S)

def queueRun_sync_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hdup : S.queue.Nodup) (hS : PoppedSync A i j S),
  PoppedSync A i j (queueRun A i j n S)

def relaxEdge_zero_key_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hS : LayerRange S) (hz : S.keys v = 0),
  (relaxEdge A i j u S e).keys v = 0

def relaxAll_zero_key_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (hS : LayerRange S) (hz : S.keys v = 0),
  (relaxAll A i j u S).keys v = 0

def popLayer_zero_key_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j v : ℕ) (S : LayerState)
    (hS : LayerRange S) (hz : S.keys v = 0),
  (popLayer A i j S).keys v = 0

def queueRun_range_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hS : LayerRange S),
  LayerRange (queueRun A i j n S)

def queueRun_zero_key_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j n v : ℕ) (S : LayerState)
    (hS : LayerRange S) (hz : S.keys v = 0),
  (queueRun A i j n S).keys v = 0

def buildLayer_source_zero_contract_statement : Prop :=
  ∀ (A : InnerInput) (T : Table) (i j : ℕ)
    (hT : TableRange T),
  (buildLayer A T i j A.I.source i j).value = 0

def edgeExpectation_congr_contract_statement : Prop :=
  ∀ (A : InnerInput) (T U : Table) (u v i j : ℕ)
    (h : ∀ a ∈ Finset.range (tickLimit A - i),
      ∀ b ∈ Finset.range (tickLimit A - j),
        dpValue A T u (i + a) (j + b) = dpValue A U u (i + a) (j + b)),
  edgeExpectation A T u v i j = edgeExpectation A U u v i j

def edgeExpectation_mono_contract_statement : Prop :=
  ∀ (A : InnerInput) (T U : Table) (u v i j : ℕ)
    (h : ∀ a ∈ Finset.range (tickLimit A - i),
      ∀ b ∈ Finset.range (tickLimit A - j),
        dpValue A T u (i + a) (j + b) ≤ dpValue A U u (i + a) (j + b)),
  edgeExpectation A T u v i j ≤ edgeExpectation A U u v i j

def edgeExpectation_extensive_contract_statement : Prop :=
  ∀ (A : InnerInput) (T : Table) (u v i j : ℕ)
    (baseline : ℝ) (hb : baseline ≤ 1)
    (h : ∀ a ∈ Finset.range (tickLimit A - i),
      ∀ b ∈ Finset.range (tickLimit A - j),
        baseline ≤ dpValue A T u (i + a) (j + b)),
  baseline ≤ edgeExpectation A T u v i j

def dpValue_congr_at_contract_statement : Prop :=
  ∀ (A : InnerInput) (T U : Table) (v i j : ℕ)
    (h : T v i j = U v i j),
  dpValue A T v i j = dpValue A U v i j

def relaxEdge_futureBound_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hS : LayerFutureBound A i j S),
  LayerFutureBound A i j (relaxEdge A i j u S e)

def relaxAll_keys_le_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u v : ℕ) (S : LayerState),
  (relaxAll A i j u S).keys v ≤ S.keys v

def relaxAll_futureBound_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (hS : LayerFutureBound A i j S),
  LayerFutureBound A i j (relaxAll A i j u S)

def popLayer_keys_le_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j v : ℕ) (S : LayerState),
  (popLayer A i j S).keys v ≤ S.keys v

def popLayer_future_dpValue_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (v a b : ℕ) (hab : a ≠ 0 ∨ b ≠ 0),
  dpValue A (popLayer A i j S).table v (i + a) (j + b) =
      dpValue A S.table v (i + a) (j + b)

def popLayer_futureBound_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hS : LayerFutureBound A i j S),
  LayerFutureBound A i j (popLayer A i j S)

def queueRun_futureBound_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hS : LayerFutureBound A i j S),
  LayerFutureBound A i j (queueRun A i j n S)

def settleState_expectation_ge_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hu : u ∈ S.queue)
    (hS : LayerRange S) (hfuture : LayerFutureBound A i j S) (v : ℕ),
  S.keys u ≤ edgeExpectation A (settleState S i j u).table u v i j

def relaxEdge_keys_ge_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (baseline : ℝ)
    (hkeys : ∀ v ∈ S.queue, baseline ≤ S.keys v)
    (hexpect : ∀ v, baseline ≤ edgeExpectation A S.table u v i j),
  ∀ v ∈ (relaxEdge A i j u S e).queue,
      baseline ≤ (relaxEdge A i j u S e).keys v

def relaxAll_keys_ge_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (baseline : ℝ) (hkeys : ∀ v ∈ S.queue, baseline ≤ S.keys v)
    (hexpect : ∀ v, baseline ≤ edgeExpectation A S.table u v i j),
  ∀ v ∈ (relaxAll A i j u S).queue, baseline ≤ (relaxAll A i j u S).keys v

def pickedVertex_mem_contract_statement : Prop :=
  ∀ (S : LayerState) (hne : S.queue ≠ []),
  pickedVertex S ∈ S.queue

def pickedVertex_le_contract_statement : Prop :=
  ∀ (S : LayerState) (v : ℕ) (hv : v ∈ S.queue),
  S.keys (pickedVertex S) ≤ S.keys v

def popLayer_eq_relaxAll_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hne : S.queue ≠ []),
  popLayer A i j S =
      relaxAll A i j (pickedVertex S) (settleState S i j (pickedVertex S))

def popLayer_keys_ge_picked_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hne : S.queue ≠ [])
    (hS : LayerRange S) (hfuture : LayerFutureBound A i j S),
  ∀ v ∈ (popLayer A i j S).queue,
      S.keys (pickedVertex S) ≤ (popLayer A i j S).keys v

def popLayer_picked_key_mono_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hne : S.queue ≠ [])
    (hnext : (popLayer A i j S).queue ≠ [])
    (hS : LayerRange S) (hfuture : LayerFutureBound A i j S),
  S.keys (pickedVertex S) ≤ (popLayer A i j S).keys (pickedVertex (popLayer A i j S))

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

def pathWeight_cons_cons_contract_statement : Prop :=
  ∀ (w : ℕ → ℕ → ℝ≥0) (a b : ℕ) (P : List ℕ),
  pathWeight w (a :: b :: P) = (w a b : ℝ) + pathWeight w (b :: P)

def pathWeight_nonneg_contract_statement : Prop :=
  ∀ (w : ℕ → ℕ → ℝ≥0) (P : List ℕ),
  0 ≤ pathWeight w P

def pathWeight_tail_le_contract_statement : Prop :=
  ∀ (w : ℕ → ℕ → ℝ≥0) (a : ℕ) (P : List ℕ),
  pathWeight w P ≤ pathWeight w (a :: P)

def pathWeight_suffix_le_contract_statement : Prop :=
  ∀ (w : ℕ → ℕ → ℝ≥0) (pre post : List ℕ),
  pathWeight w post ≤ pathWeight w (pre ++ post)

def exists_pathReduction_contract_statement : Prop :=
  ∀ (P : List ℕ),
  ∃ Q, PathReduction P Q

def isChain_vertices_lt_contract_statement : Prop :=
  ∀ (G : Digraph) (P : List ℕ)
    (hchain : P.IsChain (fun u v => (u, v) ∈ G.edges))
    (hhead : ∀ v ∈ P.head?, v < G.n),
  ∀ v ∈ P, v < G.n

def IsPath.vertices_lt_contract_statement : Prop :=
  ∀ (G : Digraph) (s t : ℕ) (P : List ℕ)
    (hP : IsPath G s t P) (hs : s < G.n),
  ∀ v ∈ P, v < G.n

def IsPath.length_le_of_nodup_contract_statement : Prop :=
  ∀ (G : Digraph) (s t : ℕ) (P : List ℕ)
    (hP : IsPath G s t P) (hs : s < G.n) (hnd : P.Nodup),
  P.length ≤ G.n

def IsPath.exists_simple_contract_statement : Prop :=
  ∀ (G : Digraph) (s t : ℕ) (P : List ℕ)
    (hP : IsPath G s t P) (hs : s < G.n),
  ∃ Q : List ℕ, IsPath G s t Q ∧ Q.Nodup ∧ Q.length ≤ G.n ∧
      Q ⊆ P ∧ ∀ w : ℕ → ℕ → ℝ≥0, pathWeight w Q ≤ pathWeight w P

def Feasible.exists_simple_contract_statement : Prop :=
  ∀ (I : Instance) (t : ℕ) (P : List ℕ)
    (hP : Feasible I t P),
  ∃ Q : List ℕ, Feasible I t Q ∧ Q.Nodup ∧ Q.length ≤ I.graph.n ∧
      pathWeight I.length Q ≤ pathWeight I.length P

def pathWeight_le_length_mul_contract_statement : Prop :=
  ∀ (G : Digraph) (w : ℕ → ℕ → ℝ≥0)
    (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ u v, (u, v) ∈ G.edges → (w u v : ℝ) ≤ M)
    (P : List ℕ) (hP : P.IsChain (fun u v => (u, v) ∈ G.edges)),
  pathWeight w P ≤ (P.length : ℝ) * M

def IsPath.weight_le_n_mul_contract_statement : Prop :=
  ∀ (G : Digraph) (s t : ℕ) (P : List ℕ)
    (hP : IsPath G s t P) (hs : s < G.n) (hnd : P.Nodup)
    (w : ℕ → ℕ → ℝ≥0) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ u v, (u, v) ∈ G.edges → (w u v : ℝ) ≤ M),
  pathWeight w P ≤ (G.n : ℝ) * M

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

def distanceLess_iff_contract_statement : Prop :=
  ∀ (x y : Option ℝ),
  distanceLess x y = true ↔ optionDist x < optionDist y

def standalone_Mission_ShortestTreeStructure__treeFold_mem_contract_statement : Prop :=
  ∀ (T : ShortestTree) (xs : List ℕ) (P : ℕ → Prop)
    (x : ℕ) (hx : P x) (hall : ∀ y ∈ xs, P y),
  P (xs.foldl (fun x y =>
      if distanceLess (T y).distance (T x).distance then y else x) x)

def treePick_mem_contract_statement : Prop :=
  ∀ (S : TreeQueue) (hne : S.queue ≠ []),
  treePick S ∈ S.queue

def standalone_Mission_ShortestTreeStructure__treeFold_le_seed_contract_statement : Prop :=
  ∀ (T : ShortestTree) (xs : List ℕ) (x : ℕ),
  treeDist T (xs.foldl (fun x y =>
      if distanceLess (T y).distance (T x).distance then y else x) x) ≤ treeDist T x

def standalone_Mission_ShortestTreeStructure__treeFold_le_mem_contract_statement : Prop :=
  ∀ (T : ShortestTree) (xs : List ℕ) (x y : ℕ)
    (hy : y ∈ xs),
  treeDist T (xs.foldl (fun x y =>
      if distanceLess (T y).distance (T x).distance then y else x) x) ≤ treeDist T y

def treePick_le_contract_statement : Prop :=
  ∀ (S : TreeQueue) (v : ℕ) (hv : v ∈ S.queue),
  treeDist S.tree (treePick S) ≤ treeDist S.tree v

def treeRelax_queue_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e : ℕ × ℕ),
  (treeRelax I allow w u S e).queue = S.queue

def treeRelax_rank_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e : ℕ × ℕ),
  (treeRelax I allow w u S e).rank = S.rank

def treeRelax_outside_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue) (e : ℕ × ℕ)
    (hv : v ∉ S.queue),
  (treeRelax I allow w u S e).tree v = S.tree v

def treeRelax_dist_le_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue) (e : ℕ × ℕ),
  treeDist (treeRelax I allow w u S e).tree v ≤ treeDist S.tree v

def standalone_Mission_ShortestTreeStructure__treeFold_preserves_contract_statement : Prop :=
  ∀ {α β γ : Type u_1} (f : β → α → β) (p : β → γ)
    (hf : ∀ s a, p (f s a) = p s) (xs : List α) (s : β),
  p (xs.foldl f s) = p s

def treeRelaxAll_queue_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue),
  (treeRelaxAll I allow w u S).queue = S.queue

def treeRelaxAll_rank_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue),
  (treeRelaxAll I allow w u S).rank = S.rank

def treeRelaxFold_outside_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue) (es : List (ℕ × ℕ))
    (hv : v ∉ S.queue),
  (es.foldl (treeRelax I allow w u) S).tree v = S.tree v

def treeRelaxAll_outside_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue) (hv : v ∉ S.queue),
  (treeRelaxAll I allow w u S).tree v = S.tree v

def treeRelaxFold_dist_le_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue) (es : List (ℕ × ℕ)),
  treeDist (es.foldl (treeRelax I allow w u) S).tree v ≤ treeDist S.tree v

def treeRelaxAll_dist_le_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue),
  treeDist (treeRelaxAll I allow w u S).tree v ≤ treeDist S.tree v

def treeSettle_dist_contract_statement : Prop :=
  ∀ (S : TreeQueue) (u v : ℕ),
  treeDist (treeSettle S u).tree v = treeDist S.tree v

def treePop_eq_relaxAll_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (hne : S.queue ≠ []),
  treePop I allow w S = treeRelaxAll I allow w (treePick S) (treeSettle S (treePick S))

def treePop_queue_length_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue),
  (treePop I allow w S).queue.length = S.queue.length - 1

def treePop_queue_subset_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue),
  (treePop I allow w S).queue ⊆ S.queue

def treePop_queue_nodup_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (hS : S.queue.Nodup),
  (treePop I allow w S).queue.Nodup

def treeRun_zero_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue),
  treeRun I allow w 0 S = S

def treeRun_succ_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (n : ℕ) (S : TreeQueue),
  treeRun I allow w (n + 1) S = treePop I allow w (treeRun I allow w n S)

def treeRun_queue_length_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (n : ℕ) (S : TreeQueue),
  (treeRun I allow w n S).queue.length = S.queue.length - n

def treeRun_queue_nodup_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (n : ℕ) (S : TreeQueue) (hS : S.queue.Nodup),
  (treeRun I allow w n S).queue.Nodup

def shortestTree_eq_treeRun_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ),
  shortestTree I allow w = (treeRun I allow w (activeVertices I).length (treeInitial I)).tree

def shortestTree_queue_exhausted_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ),
  (treeRun I allow w (activeVertices I).length (treeInitial I)).queue = []

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

def treeInitial_policy_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ),
  TreePolicy I allow w (treeInitial I)

def treeSettle_policy_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (u : ℕ) (hu : u ∈ S.queue)
    (h : TreePolicy I allow w S),
  TreePolicy I allow w (treeSettle S u)

def treeRelax_policy_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e : ℕ × ℕ)
    (he : e ∈ I.graph.edges) (hu : u ∉ S.queue)
    (hur : (S.tree u).rank < S.rank) (h : TreePolicy I allow w S),
  TreePolicy I allow w (treeRelax I allow w u S e)

def treeRelaxFold_policy_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (es : List (ℕ × ℕ))
    (hes : ∀ e ∈ es, e ∈ I.graph.edges) (hu : u ∉ S.queue)
    (hur : (S.tree u).rank < S.rank) (h : TreePolicy I allow w S),
  TreePolicy I allow w (es.foldl (treeRelax I allow w u) S)

def treePop_policy_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (hdup : S.queue.Nodup)
    (h : TreePolicy I allow w S),
  TreePolicy I allow w (treePop I allow w S)

def treeRun_policy_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (n : ℕ) (S : TreeQueue) (hdup : S.queue.Nodup)
    (h : TreePolicy I allow w S),
  TreePolicy I allow w (treeRun I allow w n S)

def shortestTree_finite_rank_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (v : ℕ) (d : ℝ)
    (hd : (shortestTree I allow w v).distance = some d),
  (shortestTree I allow w v).rank < (activeVertices I).length

def shortestTree_finite_parent_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (v : ℕ) (d : ℝ) (hv : v ≠ I.source)
    (hd : (shortestTree I allow w v).distance = some d),
  ∃ u a, (shortestTree I allow w v).parent = some u ∧
      (shortestTree I allow w u).distance = some a ∧ d = a + w u v ∧
      (u,v) ∈ I.graph.edges ∧ allow u v = true ∧
      (shortestTree I allow w u).rank < (shortestTree I allow w v).rank

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

def treePop_dist_le_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (v : ℕ),
  treeDist (treePop I allow w S).tree v ≤ treeDist S.tree v

def treePop_outside_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (v : ℕ) (hv : v ∉ S.queue),
  (treePop I allow w S).tree v = S.tree v

def treePop_dist_picked_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (hne : S.queue ≠ [])
    (hdup : S.queue.Nodup),
  treeDist (treePop I allow w S).tree (treePick S) = treeDist S.tree (treePick S)

def treeRelax_dist_ge_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e : ℕ × ℕ)
    (baseline : WithTop ℝ) (hkeys : ∀ v ∈ S.queue, baseline ≤ treeDist S.tree v)
    (hu : baseline ≤ treeDist S.tree u) (hw : 0 ≤ w e.1 e.2),
  ∀ v ∈ (treeRelax I allow w u S e).queue,
      baseline ≤ treeDist (treeRelax I allow w u S e).tree v

def treeRelaxFold_dist_ge_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (u : ℕ)
    (S : TreeQueue) (es : List (ℕ × ℕ)) (baseline : WithTop ℝ)
    (hkeys : ∀ v ∈ S.queue, baseline ≤ treeDist S.tree v)
    (hu : baseline ≤ treeDist S.tree u) (huq : u ∉ S.queue),
  ∀ v ∈ (es.foldl (treeRelax I allow w u) S).queue,
      baseline ≤ treeDist (es.foldl (treeRelax I allow w u) S).tree v

def treePop_dist_ge_picked_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (S : TreeQueue)
    (hne : S.queue ≠ []) (hdup : S.queue.Nodup),
  ∀ v ∈ (treePop I allow w S).queue,
      treeDist S.tree (treePick S) ≤ treeDist (treePop I allow w S).tree v

def treeRelax_edge_bound_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue)
    (huv : u ≠ v) (hv : v ∈ S.queue) (ha : allow u v = true),
  treeDist (treeRelax I allow w u S (u,v)).tree v ≤
      treeDist S.tree u + (w u v : WithTop ℝ)

def treeRelaxAll_edge_bound_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue)
    (huv : u ≠ v) (hv : v ∈ S.queue) (hu : u ∉ S.queue)
    (ha : allow u v = true) (hedge : (u,v) ∈ I.graph.edges),
  treeDist (treeRelaxAll I allow w u S).tree v ≤
      treeDist S.tree u + (w u v : WithTop ℝ)

def treePop_separation_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (S : TreeQueue)
    (hdup : S.queue.Nodup) (hsep : TreeSeparation I S),
  TreeSeparation I (treePop I allow w S)

def treePop_bellman_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (S : TreeQueue)
    (hdup : S.queue.Nodup) (hsep : TreeSeparation I S)
    (hbell : TreeBellman I allow w S),
  TreeBellman I allow w (treePop I allow w S)

def treeRun_bellman_separation_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (n : ℕ) (S : TreeQueue)
    (hdup : S.queue.Nodup) (hsep : TreeSeparation I S) (hbell : TreeBellman I allow w S),
  TreeSeparation I (treeRun I allow w n S) ∧ TreeBellman I allow w (treeRun I allow w n S)

def shortestTree_bellman_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (u v : ℕ)
    (he : (u,v) ∈ I.graph.edges) (ha : allow u v = true),
  treeDist (shortestTree I allow w) v ≤
      treeDist (shortestTree I allow w) u + (w u v : WithTop ℝ)

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

def treeRelax_dist_nonneg_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (u : ℕ)
    (S : TreeQueue) (hS : ∀ v, 0 ≤ treeDist S.tree v) (e : ℕ × ℕ),
  ∀ v, 0 ≤ treeDist (treeRelax I allow w u S e).tree v

def treeRelaxAll_dist_nonneg_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (u : ℕ)
    (S : TreeQueue) (hS : ∀ v, 0 ≤ treeDist S.tree v),
  ∀ v, 0 ≤ treeDist (treeRelaxAll I allow w u S).tree v

def treePop_dist_nonneg_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v)
    (S : TreeQueue) (hS : ∀ v, 0 ≤ treeDist S.tree v),
  ∀ v, 0 ≤ treeDist (treePop I allow w S).tree v

def treeRun_dist_nonneg_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (n : ℕ)
    (S : TreeQueue) (hS : ∀ v, 0 ≤ treeDist S.tree v),
  ∀ v, 0 ≤ treeDist (treeRun I allow w n S).tree v

def treeRun_dist_le_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (n : ℕ) (S : TreeQueue) (v : ℕ),
  treeDist (treeRun I allow w n S).tree v ≤ treeDist S.tree v

def shortestTree_dist_nonneg_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (v : ℕ),
  0 ≤ treeDist (shortestTree I allow w) v

def shortestTree_source_zero_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v),
  (shortestTree I allow w I.source).distance = some 0

def shortestTree_distance_nonneg_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (v : ℕ) (d : ℝ)
    (hd : (shortestTree I allow w v).distance = some d),
  0 ≤ d

def treeDist_chain_bound_contract_statement : Prop :=
  ∀ (I : Instance) (T : ShortestTree)
    (allow : ℕ → ℕ → Bool) (w : ℕ → ℕ → ℝ≥0)
    (hbell : ∀ u v, (u,v) ∈ I.graph.edges → allow u v = true →
      treeDist T v ≤ treeDist T u + ((w u v : ℝ) : WithTop ℝ))
    (P : List ℕ) (s t : ℕ) (hp : IsPath I.graph s t P)
    (ha : P.IsChain (fun u v => allow u v = true)),
  treeDist T t ≤ treeDist T s + ((pathWeight w P : ℝ) : WithTop ℝ)

def shortestTree_path_bound_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ≥0) (P : List ℕ) (t : ℕ)
    (hp : IsPath I.graph I.source t P)
    (ha : P.IsChain (fun u v => allow u v = true)),
  ∃ d : ℝ, (shortestTree I allow (fun u v => w u v) t).distance = some d ∧
      d ≤ pathWeight w P

def pathWeight_zero_chain_contract_statement : Prop :=
  ∀ (w : ℕ → ℕ → ℝ≥0) (P : List ℕ)
    (h : pathWeight w P = 0),
  P.IsChain (fun u v => w u v = 0)

def zeroLengthTree_path_bound_contract_statement : Prop :=
  ∀ (I : Instance) (P : List ℕ) (t : ℕ)
    (hp : IsPath I.graph I.source t P) (hz : pathWeight I.length P = 0),
  ∃ d : ℝ, (zeroLengthTree I t).distance = some d ∧ d ≤ pathWeight I.cost P

def zeroBudgetTree_path_bound_contract_statement : Prop :=
  ∀ (I : Instance) (P : List ℕ) (t : ℕ)
    (hp : IsPath I.graph I.source t P) (hz : pathWeight I.cost P = 0),
  ∃ d : ℝ, (zeroBudgetTree I t).distance = some d ∧ d ≤ pathWeight I.length P

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

def activeVertices_length_le_edges_contract_statement : Prop :=
  ∀ (I : Instance),
  (activeVertices I).length ≤ 2 * I.graph.edges.length + 1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

def edgeWeightSum_nonneg_contract_statement : Prop :=
  ∀ (I : Instance) (w : ℕ → ℕ → ℝ≥0),
  0 ≤ edgeWeightSum I w

def weight_le_edgeWeightSum_contract_statement : Prop :=
  ∀ (I : Instance) (w : ℕ → ℕ → ℝ≥0) (u v : ℕ)
    (he : (u,v) ∈ I.graph.edges),
  (w u v : ℝ) ≤ edgeWeightSum I w

def treePolicy_distance_bound_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (h : TreePolicy I allow w S)
    (hs : (S.tree I.source).distance = some 0) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∀ u v, (u,v) ∈ I.graph.edges → w u v ≤ W)
    (v : ℕ) (d : ℝ) (hd : (S.tree v).distance = some d),
  d ≤ (S.rank : ℝ) * W

def treeRun_source_zero_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (k : ℕ),
  ((treeRun I allow w k (treeInitial I)).tree I.source).distance = some 0

def treeRun_sentinel_bound_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ≥0) (k v : ℕ) (d : ℝ)
    (hd : ((treeRun I allow (fun u v => (w u v : ℝ)) k (treeInitial I)).tree v).distance = some d),
  d < ((I.graph.n : ℝ) + 1) * (1 + edgeWeightSum I w)

def distanceLess_eq_sentinel_contract_statement : Prop :=
  ∀ (top : ℝ) (x y : Option ℝ)
    (hx : ∀ d, x = some d → d < top) (hy : ∀ d, y = some d → d < top),
  distanceLess x y = decide (x.getD top < y.getD top)

def treePick_eq_sentinel_firstMin_contract_statement : Prop :=
  ∀ (top : ℝ) (S : TreeQueue)
    (hfinite : ∀ v d, (S.tree v).distance = some d → d < top),
  treePick S = firstMin (sentinelKey top S.tree) S.queue 0

def treeRun_pick_sentinel_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ≥0) (k : ℕ),
  let S := treeRun I allow (fun u v => (w u v : ℝ)) k (treeInitial I)
  treePick S = firstMin
    (sentinelKey (((I.graph.n : ℝ)+1)*(1+edgeWeightSum I w)) S.tree) S.queue 0

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Queue

def activeLeaf_at_contract_statement : Prop :=
  ∀ (xs q : List ℕ) (key : ℕ → ℝ) (B k : ℕ)
    (hk : k<xs.length),
  activeLeaf xs q key B (B+k) =
      ⟨if slotVertex xs k∈q then k+1 else 0,key (slotVertex xs k)⟩

def activeLeaf_outside_contract_statement : Prop :=
  ∀ (xs q : List ℕ) (key : ℕ → ℝ) (B node : ℕ)
    (h : node<B ∨ B+xs.length≤node),
  activeLeaf xs q key B node=⟨0,0⟩

def slotVertex_injective_contract_statement : Prop :=
  ∀ (xs : List ℕ) (hxs : xs.Nodup) (i j : ℕ)
    (hi : i<xs.length) (hj : j<xs.length),
  slotVertex xs i=slotVertex xs j ↔ i=j

def slotVertex_idxOf_contract_statement : Prop :=
  ∀ (xs : List ℕ) (hxs : xs.Nodup) (k : ℕ) (hk : k<xs.length),
  xs.idxOf (slotVertex xs k)=k

def activeLeaf_single_change_contract_statement : Prop :=
  ∀ (xs q q' : List ℕ) (key key' : ℕ → ℝ)
    (B k : ℕ) (hxs : xs.Nodup) (hk : k<xs.length)
    (hkey : ∀ v, v≠slotVertex xs k → key' v=key v)
    (hq : ∀ v, v≠slotVertex xs k → (v∈q' ↔ v∈q)),
  activeLeaf xs q' key' B = Function.update (activeLeaf xs q key B) (B+k)
      ⟨if slotVertex xs k∈q' then k+1 else 0,key' (slotVertex xs k)⟩

def activeLeaf_delete_contract_statement : Prop :=
  ∀ (xs q : List ℕ) (key : ℕ → ℝ) (B k : ℕ)
    (hxs : xs.Nodup) (hq : q.Nodup) (hk : k<xs.length),
  activeLeaf xs (q.erase (slotVertex xs k)) key B =
      Function.update (activeLeaf xs q key B) (B+k) ⟨0,key (slotVertex xs k)⟩

def activeLeaf_update_key_contract_statement : Prop :=
  ∀ (xs q : List ℕ) (key : ℕ → ℝ) (B k : ℕ) (value : ℝ)
    (hxs : xs.Nodup) (hk : k<xs.length) (hq : slotVertex xs k∈q),
  activeLeaf xs q (Function.update key (slotVertex xs k) value) B =
      Function.update (activeLeaf xs q key B) (B+k) ⟨k+1,value⟩

def slotVertex_idxOf_eq_contract_statement : Prop :=
  ∀ (xs : List ℕ) (u : ℕ) (hu : u∈xs),
  slotVertex xs (xs.idxOf u)=u

def activeLeaf_delete_vertex_contract_statement : Prop :=
  ∀ (xs q : List ℕ) (key : ℕ→ℝ) (B u : ℕ)
    (hxs : xs.Nodup) (hq : q.Nodup) (hu : u∈xs),
  activeLeaf xs (q.erase u) key B =
      Function.update (activeLeaf xs q key B) (B+xs.idxOf u) ⟨0,key u⟩

def activeLeaf_update_vertex_contract_statement : Prop :=
  ∀ (xs q : List ℕ) (key : ℕ→ℝ) (B u : ℕ) (value : ℝ)
    (hxs : xs.Nodup) (hu : u∈xs) (huq : u∈q),
  activeLeaf xs q (Function.update key u value) B =
      Function.update (activeLeaf xs q key B) (B+xs.idxOf u) ⟨xs.idxOf u+1,value⟩

def standalone_Mission_QueueLeaves__getD_map_range_contract_statement : Prop :=
  ∀ (xs : List ℕ),
  (List.range xs.length).map (slotVertex xs)=xs

def standalone_Mission_QueueLeaves__filterMap_live_contract_statement : Prop :=
  ∀ (xs q : List ℕ) (f : ℕ→Record),
  xs.filterMap (fun v=>if v∈q then some (f v) else none) =
      (xs.filter (fun v=>decide (v∈q))).map f

def filter_sublist_members_contract_statement : Prop :=
  ∀ (xs q : List ℕ) (hxs : xs.Nodup) (hq : q.Sublist xs),
  xs.filter (fun v=>decide (v∈q))=q

def activeLeaf_records_contract_statement : Prop :=
  ∀ (xs q : List ℕ) (key : ℕ→ℝ) (B : ℕ)
    (hxs : xs.Nodup) (hq : q.Sublist xs) (hB : xs.length≤B),
  leafRecords (activeLeaf xs q key B) B B = q.map (vertexRecord xs key)

def activeLeaf_firstMin_contract_statement : Prop :=
  ∀ (xs q : List ℕ) (key : ℕ→ℝ) (height : ℕ)
    (hxs : xs.Nodup) (hq : q.Sublist xs) (hB : xs.length≤2^height)
    (fallback : ℕ) (hne : q≠[]),
  (heapTruth (2^height) (activeLeaf xs q key (2^height)) 1).decode =
      some (vertexRecord xs key (firstMin key q fallback))

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources

def popLayer_queue_sublist_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState),
  (popLayer A i j S).queue.Sublist S.queue

def queueRun_queue_sublist_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState),
  (queueRun A i j n S).queue.Sublist S.queue

def treePop_queue_sublist_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ→ℕ→Bool)
    (w : ℕ→ℕ→ℝ) (S : TreeQueue),
  (treePop I allow w S).queue.Sublist S.queue

def treeRun_queue_sublist_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ→ℕ→Bool)
    (w : ℕ→ℕ→ℝ) (n : ℕ) (S : TreeQueue),
  (treeRun I allow w n S).queue.Sublist S.queue

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Queue
open Structured

def initPrefix_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input initPrefix s = prefixed s

def initPair_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input initPair s = paired s

def empty_coherent_contract_statement : Prop :=
  ∀ (capacity : ℕ),
  Coherent capacity (fun _ => (⟨0, 0⟩ : Record))

def prefixed_inv_contract_statement : Prop :=
  ∀ (W P B : ℕ) (s : Store) (hB : 0 < B) (hspace : W + 2 * B ≤ P)
    (h0 : s.nr 0 = B - 1) (h1 : s.nr 1 = W) (h2 : s.nr 2 = P)
    (h3 : s.nr 3 = 0) (h4 : s.nr 4 = 1),
  InitInv W P B (B - 1) (prefixed s)

def paired_inv_contract_statement : Prop :=
  ∀ (W P B k : ℕ) (s : Store) (hspace : W + 2 * B ≤ P)
    (hk : 0 < k) (hkB : k < B) (h : InitInv W P B k s),
  InitInv W P B (k - 1) (paired s)

def initLoop_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (W P B k : ℕ) (s : Store)
    (hspace : W + 2 * B ≤ P) (hkB : k < B) (h : InitInv W P B k s),
  ∃ out, Run input (.loop (.nat .lt 3 0) (atoms initPair)) s out (15 * k + 1) ∧
      InitInv W P B 0 out

def initializeEmpty_correct_contract_statement : Prop :=
  ∀ (input : RAMInput) (W P B : ℕ) (s : Store)
    (hB : 0 < B) (hspace : W + 2 * B ≤ P)
    (h0 : s.nr 0 = B - 1) (h1 : s.nr 1 = W) (h2 : s.nr 2 = P)
    (h3 : s.nr 3 = 0) (h4 : s.nr 4 = 1),
  ∃ out k, Run input initializeEmpty s out k ∧ k ≤ 15 * B ∧
      out.nr 0 = 0 ∧ out.nr 1 = W ∧ out.nr 2 = P ∧ out.nr 3 = 0 ∧ out.nr 4 = 1 ∧
      ParentLayout (2 * B) out ∧
      ∀ v < 2 * B, readRecord out (W + v) = ⟨0, 0⟩

def InitFrame.refl_contract_statement : Prop :=
  ∀ (W P B : ℕ) (s : Store),
  InitFrame W P B s s

def InitFrame.trans_contract_statement : Prop :=
  ∀ (W P B : ℕ) (s u t : Store)
    (h : InitFrame W P B s u) (h' : InitFrame W P B u t),
  InitFrame W P B s t

def prefixed_frame_contract_statement : Prop :=
  ∀ (W P B : ℕ) (s : Store) (hB : 0 < B)
    (h1 : s.nr 1 = W) (h2 : s.nr 2 = P) (h4 : s.nr 4 = 1),
  InitFrame W P B s (prefixed s)

def paired_frame_contract_statement : Prop :=
  ∀ (W P B k : ℕ) (s : Store) (hkB : k < B)
    (h0 : s.nr 0 = k) (h1 : s.nr 1 = W) (h2 : s.nr 2 = P) (h4 : s.nr 4 = 1),
  InitFrame W P B s (paired s)

def initLoop_run_framed_contract_statement : Prop :=
  ∀ (input : RAMInput) (W P B k : ℕ) (s : Store)
    (hspace : W + 2 * B ≤ P) (hkB : k < B) (h : InitInv W P B k s),
  ∃ out, Run input (.loop (.nat .lt 3 0) (atoms initPair)) s out (15 * k + 1) ∧
      InitInv W P B 0 out ∧ InitFrame W P B s out

def initializeEmpty_framed_contract_statement : Prop :=
  ∀ (input : RAMInput) (W P B : ℕ) (s : Store)
    (hB : 0 < B) (hspace : W + 2 * B ≤ P)
    (h0 : s.nr 0 = B - 1) (h1 : s.nr 1 = W) (h2 : s.nr 2 = P)
    (h3 : s.nr 3 = 0) (h4 : s.nr 4 = 1),
  ∃ out k, Run input initializeEmpty s out k ∧ k ≤ 15 * B ∧
      InitInv W P B 0 out ∧ InitFrame W P B s out

def updateLeaf_refines_contract_statement : Prop :=
  ∀ (input : RAMInput) (B : ℕ) (leaf : ℕ → Record) (s : Store)
    (hparent : ParentLayout (2 * B) s) (hone : s.nr 4 = 1)
    (hpositive : 0 < s.nr 0) (hleaf : B ≤ s.nr 0)
    (hrep : Represents B (s.nr 1) leaf s),
  ∃ out k, Run input updateLeaf s out k ∧ k ≤ 19 * Nat.clog 2 (2 * B) + 6 ∧
      out.nr 0 = 0 ∧ (∀ a, 0 < a → a < 5 → out.nr a = s.nr a) ∧
      ParentLayout (2 * B) out ∧
      Represents B (s.nr 1) (Function.update leaf (s.nr 0) ⟨s.nr 10, s.rr 2⟩) out ∧
      WinnerFrame (s.nr 1) (2 * B) s out

def initializeEmpty_represents_contract_statement : Prop :=
  ∀ (input : RAMInput) (W P B : ℕ) (s : Store)
    (hB : 0 < B) (hspace : W + 2 * B ≤ P)
    (h0 : s.nr 0 = B - 1) (h1 : s.nr 1 = W) (h2 : s.nr 2 = P)
    (h3 : s.nr 3 = 0) (h4 : s.nr 4 = 1),
  ∃ out k, Run input initializeEmpty s out k ∧ k ≤ 15 * B ∧
      InitInv W P B 0 out ∧ Represents B W (fun _ => ⟨0, 0⟩) out ∧ InitFrame W P B s out

def represented_root_firstMin_contract_statement : Prop :=
  ∀ (h W : ℕ) (leaf : ℕ → Record) (s : Store)
    (hrep : Represents (2 ^ h) W leaf s) (xs : List ℕ) (encode : ℕ → Record)
    (hslots : leafRecords leaf (2 ^ h) (2 ^ h) = xs.map encode)
    (fallback : ℕ) (hne : xs ≠ []),
  (readRecord s (W + 1)).decode =
      some (encode (firstMin (fun v => (encode v).key) xs fallback))

def prefixLeaf_zero_contract_statement : Prop :=
  ∀ (B : ℕ) (key : ℕ → ℝ),
  prefixLeaf B key 0 = fun _ => ⟨0, 0⟩

def prefixLeaf_succ_contract_statement : Prop :=
  ∀ (B k : ℕ) (key : ℕ → ℝ),
  Function.update (prefixLeaf B key k) (B + k) ⟨k + 1, key k⟩ = prefixLeaf B key (k + 1)

def buildSetup_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  Queue.evalAtoms input buildSetup s = buildSetupState s

def prepareInsert_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  Queue.evalAtoms input prepareInsert s = preparedInsert s

def insertIncrement_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  insertIncrement.eval input s = inserted s

def initializeEmpty_high_register_contract_statement : Prop :=
  ∀ {input : RAMInput} {s t : Store} {k r : ℕ}
    (h : Run input initializeEmpty s t k) (hr : 10 ≤ r),
  t.nr r = s.nr r

def updateLeaf_high_register_contract_statement : Prop :=
  ∀ {input : RAMInput} {s t : Store} {k r : ℕ}
    (h : Run input updateLeaf s t k) (hr : 10 ≤ r),
  t.nr r = s.nr r

def WinnerFrame.initFrame_contract_statement : Prop :=
  ∀ (W P B : ℕ) (s t : Store)
    (h : WinnerFrame W (2 * B) s t),
  InitFrame W P B s t

def insertBody_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (B N W P R k : ℕ) (initial s : Store)
    (hB : 0 < B) (hN : N ≤ B) (hk : k < N)
    (hkeys : ∀ i < N, R + i < W ∨ W + 2 * B ≤ R + i)
    (h : BuildInv B N W P R initial k s),
  ∃ out cost, Run input insertBody s out cost ∧ BuildInv B N W P R initial (k + 1) out ∧
      cost ≤ 19 * Nat.clog 2 (2 * B) + 11

def buildQueue_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (B N W P R : ℕ) (s : Store)
    (hB : 0 < B) (hN : N ≤ B) (hspace : W + 2 * B ≤ P)
    (hkeys : ∀ i < N, R + i < W ∨ W + 2 * B ≤ R + i)
    (h1 : s.nr 1 = W) (h2 : s.nr 2 = P) (h3 : s.nr 3 = 0) (h4 : s.nr 4 = 1)
    (h11 : s.nr 11 = B) (h12 : s.nr 12 = N) (h13 : s.nr 13 = R),
  ∃ out cost, Run input buildQueue s out cost ∧ BuildInv B N W P R s N out ∧
      cost ≤ 15 * B + (19 * Nat.clog 2 (2 * B) + 13) * N + 3

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Queue

def activeLeaf_initial_contract_statement : Prop :=
  ∀ (xs : List ℕ) (key : ℕ → ℝ) (B : ℕ),
  activeLeaf xs xs key B =
      prefixLeaf B (fun k => key (slotVertex xs k)) xs.length

def prefixLeaf_records_contract_statement : Prop :=
  ∀ (B N : ℕ) (key : ℕ → ℝ) (hN : N ≤ B),
  leafRecords (prefixLeaf B key N) B B =
      (List.range N).map (fun k => (⟨k+1,key k⟩ : Record))

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def seed_prefixLeaf_contract_statement : Prop :=
  ∀ (xs : List ℕ) (A R source off B : ℕ) (top : ℝ) (s : Store)
    (h : TreeSeedInv xs A R source off top xs.length s),
  Queue.prefixLeaf B (fun k => s.rm (R+k)) xs.length =
      Queue.activeLeaf xs xs (fun v => if v=source then 0 else top) B

def treeInitializeQueue_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (xs : List ℕ)
    (A R source off B W P : ℕ) (top : ℝ) (s : Store)
    (hB : 0 < B) (hfit : xs.length ≤ B) (hWP : W+2*B ≤ P) (hPR : P+2*B ≤ R)
    (hAW : A+xs.length ≤ W)
    (hW : s.nr 1 = W) (hP : s.nr 2 = P) (hz : s.nr 3 = 0) (hone : s.nr 4 = 1)
    (hcapacity : s.nr 11 = B) (hlen : s.nr 12 = xs.length)
    (hA : s.nr 171 = A) (hR : s.nr 13 = R) (hsource : s.nr 123 = source)
    (hoff : s.nr 173 = off) (htop : s.rr 170 = top)
    (harray : ∀ j v, xs[j]? = some v → s.nm (A+j) = v)
    (hspace : ∀ v ∈ xs, targetAddress v + off < A),
  ∃ out steps, Run input treeInitializeQueue s out steps ∧
      steps ≤ 15*B + (19*Nat.clog 2 (2*B)+31)*xs.length + 5 ∧
      TreeSeedInv xs A R source off top xs.length out ∧
      Queue.ParentLayout (2*B) out ∧
      Queue.Represents B W
        (Queue.activeLeaf xs xs (fun v => if v=source then 0 else top) B) out ∧
      (∀ a, (∀ v ∈ xs, a ≠ targetAddress v + off) →
        (a < R ∨ R+xs.length ≤ a) →
        (a < W ∨ W+2*B ≤ a) → (a < P ∨ P+2*B ≤ a) →
        out.nm a = s.nm a ∧ out.rm a = s.rm a)

def activeProbe_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input activeProbe s = activeProbed s

def activeAppend_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input activeAppend s = activeAppended s

def activeInsert_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (hz : s.nr 125 = 0),
  ∃ steps ≤ 8, Run input activeInsert s (activeResult s) steps

def activeResult_frame_register_contract_statement : Prop :=
  ∀ (s : Store) (r : ℕ)
    (h143 : r ≠ 143) (h144 : r ≠ 144) (h145 : r ≠ 145) (h146 : r ≠ 146),
  (activeResult s).nr r = s.nr r

def activeResult_frame_memory_contract_statement : Prop :=
  ∀ (s : Store) (a : ℕ)
    (hflag : a ≠ s.nr 141 + s.nr 140) (hlist : a ≠ s.nr 142 + s.nr 143),
  (activeResult s).nm a = s.nm a

def activeResult_frame_reals_contract_statement : Prop :=
  ∀ (s : Store),
  (activeResult s).rr = s.rr ∧ (activeResult s).rm = s.rm

def activeResult_present_contract_statement : Prop :=
  ∀ (s : Store) (hm : s.nm (s.nr 141 + s.nr 140) ≠ 0),
  (activeResult s).nm = s.nm ∧ (activeResult s).nr 143 = s.nr 143

def activeResult_absent_contract_statement : Prop :=
  ∀ (s : Store) (hm : s.nm (s.nr 141 + s.nr 140) = 0)
    (hone : s.nr 126 = 1)
    (hsep : s.nr 141 + s.nr 140 ≠ s.nr 142 + s.nr 143),
  (activeResult s).nr 143 = s.nr 143 + 1 ∧
    (activeResult s).nm (s.nr 141 + s.nr 140) = s.nr 143 + 1 ∧
    (activeResult s).nm (s.nr 142 + s.nr 143) = s.nr 140

def active_regions_disjoint_contract_statement : Prop :=
  ∀ (base n v count : ℕ) (hv : v < n),
  base + v ≠ (base + 2 * n) + count

def stableInsert_mem_contract_statement : Prop :=
  ∀ (xs : List ℕ) (v x : ℕ),
  x ∈ stableInsert xs v ↔ x ∈ xs ∨ x = v

def stableInsert_nodup_contract_statement : Prop :=
  ∀ (xs : List ℕ) (v : ℕ) (hx : xs.Nodup),
  (stableInsert xs v).Nodup

def standalone_Mission_RAMActiveList__stableFold_loop_contract_statement : Prop :=
  ∀ (xs acc : List ℕ),
  xs.foldl stableInsert acc.reverse = List.eraseDupsBy.loop (· == ·) xs acc

def stableFold_eq_eraseDups_contract_statement : Prop :=
  ∀ (xs : List ℕ),
  xs.foldl stableInsert [] = xs.eraseDups

def activeVertices_eq_stableFold_contract_statement : Prop :=
  ∀ (I : Instance),
  activeVertices I = (I.source :: I.graph.edges.flatMap (fun e => [e.1,e.2])).foldl
      stableInsert []

def ActiveRep.flag_zero_iff_contract_statement : Prop :=
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (v : ℕ) (hv : v < n),
  s.nm (base + v) = 0 ↔ v ∉ xs

def ActiveRep.empty_contract_statement : Prop :=
  ∀ (n base array : ℕ) (s : Store)
    (hb : s.nr 141 = base) (ha : s.nr 142 = array) (hc : s.nr 143 = 0)
    (hsep : base + n ≤ array) (hz : ∀ v < n, s.nm (base + v) = 0),
  ActiveRep n base array [] s

def ActiveRep.insert_contract_statement : Prop :=
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (hv : s.nr 140 < n) (hone : s.nr 126 = 1),
  ActiveRep n base array (stableInsert xs (s.nr 140)) (activeResult s)

def ActiveRep.indexOf_contract_statement : Prop :=
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (v : ℕ) (hv : v ∈ xs),
  s.nm (base + v) = xs.idxOf v + 1

def ActiveRep.index_bounds_contract_statement : Prop :=
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (v : ℕ) (hv : v ∈ xs),
  0 < s.nm (base + v) ∧ s.nm (base + v) ≤ xs.length

def ActiveRep.inverse_contract_statement : Prop :=
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (v : ℕ) (hv : v ∈ xs),
  s.nm (array + (s.nm (base + v) - 1)) = v

def ActiveRep.vertex_at_contract_statement : Prop :=
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (k : ℕ) (hk : k < xs.length),
  s.nm (array + k) = xs[k]?.getD 0

def ActiveRep.length_le_contract_statement : Prop :=
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s),
  xs.length ≤ n

def ActiveRep.congr_contract_statement : Prop :=
  ∀ {n base array : ℕ} {xs : List ℕ} {s t : Store}
    (h : ActiveRep n base array xs s)
    (hb : t.nr 141 = s.nr 141) (ha : t.nr 142 = s.nr 142) (hc : t.nr 143 = s.nr 143)
    (hmap : ∀ v < n, t.nm (base + v) = s.nm (base + v))
    (harray : ∀ k < xs.length, t.nm (array + k) = s.nm (array + k)),
  ActiveRep n base array xs t

def TreeMode.weight_nonneg_contract_statement : Prop :=
  ∀ (mode : TreeMode) (I : Instance) (u v : ℕ),
  0 ≤ mode.weight I u v

def TreeMode.top_pos_contract_statement : Prop :=
  ∀ (mode : TreeMode) (I : Instance),
  0 < mode.top I

def TreeMode.offset_lt_four_contract_statement : Prop :=
  ∀ (mode : TreeMode),
  mode.offset < 4

def TreeAllocation.capacity_pos_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I),
  0 < E.B

def TreeAllocation.target_lt_map_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) (v : ℕ) (hv : v < I.graph.n),
  targetAddress v + mode.offset < E.map

def TreeAllocation.map_le_array_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I),
  E.map ≤ E.array

def TreeAllocation.array_end_le_winner_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I),
  E.array + I.graph.n ≤ E.W

def TreeAllocation.target_lt_winner_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) (v : ℕ) (hv : v < I.graph.n),
  targetAddress v + mode.offset < E.W

def TreeRegisters.transfer_contract_statement : Prop :=
  ∀ {I : Instance} {B W P R map array heads links off mode : ℕ}
    {top : ℝ} {s t : Store} (h : TreeRegisters I B W P R map array heads links off mode top s)
    (hn : ∀ r ∈ treeNatConstants, t.nr r = s.nr r) (hr : t.rr 170 = s.rr 170),
  TreeRegisters I B W P R map array heads links off mode top t

def TreeRegisters.after_run_contract_statement : Prop :=
  ∀ {I : Instance} {B W P R map array heads links off mode : ℕ}
    {top : ℝ} {s t : Store} (h : TreeRegisters I B W P R map array heads links off mode top s)
    {input : RAMInput} {cmd : Cmd} {steps : ℕ} (hrun : Run input cmd s t steps)
    (hn : Disjoint treeNatConstants cmd.natWrites) (hr : 170 ∉ cmd.realWrites),
  TreeRegisters I B W P R map array heads links off mode top t

def treeInitializeQueue_rep_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (input : RAMInput) (s : Store) (hr : E.Registers mode s)
    (ha : ActiveRep I.graph.n E.map E.array (activeVertices I) s),
  ∃ out steps, Run input treeInitializeQueue s out steps ∧
      E.Registers mode out ∧ E.Memory mode (treeInitial I) out ∧
      steps ≤ 15*E.B + (19*Nat.clog 2 (2*E.B)+31)*(activeVertices I).length + 5 ∧
      (∀ a, (∀ v ∈ activeVertices I, a ≠ targetAddress v + mode.offset) →
        (a < E.R ∨ E.R+(activeVertices I).length ≤ a) →
        (a < E.W ∨ E.W+2*E.B ≤ a) → (a < E.P ∨ E.P+2*E.B ≤ a) →
        out.nm a = s.nm a ∧ out.rm a = s.rm a)

def treeExtractAtoms_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input treeExtractAtoms s = treeExtractPrepared s

def treeExtractPrepared_values_contract_statement : Prop :=
  ∀ (s : Store) (hone : s.nr 4 = 1),
  (treeExtractPrepared s).nr 0 = s.nr 170 + (s.nm (s.nr 1 + 1) - 1) ∧
    (treeExtractPrepared s).nr 10 = 0 ∧
    (treeExtractPrepared s).nr 260 = s.nm (s.nr 1 + 1) ∧
    (treeExtractPrepared s).nr 261 = s.nm (s.nr 1 + 1) - 1 ∧
    (treeExtractPrepared s).nr 262 = s.nm (s.nr 171 + (s.nm (s.nr 1 + 1) - 1)) ∧
    (treeExtractPrepared s).rr 260 = s.rm (s.nr 1 + 1) ∧
    (treeExtractPrepared s).rr 2 = s.rm (s.nr 1 + 1)

def treeExtractPrepared_header_contract_statement : Prop :=
  ∀ (s : Store) (r : ℕ) (hr : 0 < r) (hr' : r < 5),
  (treeExtractPrepared s).nr r = s.nr r

def standalone_Mission_RAMTreeExtract__updateLeaf_nat_frame_contract_statement : Prop :=
  ∀ {input : RAMInput} {s out : Store} {steps r : ℕ}
    (h : Run input Queue.updateLeaf s out steps) (hr : 11 ≤ r),
  out.nr r = s.nr r

def standalone_Mission_RAMTreeExtract__updateLeaf_real_frame_contract_statement : Prop :=
  ∀ {input : RAMInput} {s out : Store} {steps r : ℕ}
    (h : Run input Queue.updateLeaf s out steps) (hr : 2 ≤ r),
  out.rr r = s.rr r

def treeExtract_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (B : ℕ)
    (truth : ℕ → Queue.Record) (s : Store)
    (hp : Queue.ParentLayout (2 * B) (treeExtractPrepared s))
    (hone : s.nr 4 = 1)
    (hpositive : 0 < s.nr 170 + (s.nm (s.nr 1 + 1) - 1))
    (hc : Queue.Coherent (2 * B) truth)
    (hr : Queue.Ready (2 * B) truth (treeExtractPrepared s))
    (hnew : truth (s.nr 170 + (s.nm (s.nr 1 + 1) - 1)) = ⟨0, s.rm (s.nr 1 + 1)⟩),
  ∃ out steps, Run input treeExtract s out steps ∧
      steps ≤ 19 * Nat.clog 2 (2 * B) + 15 ∧
      Queue.ParentLayout (2 * B) out ∧
      (∀ v < 2 * B, Queue.readRecord out (s.nr 1 + v) = truth v) ∧
      out.nr 260 = s.nm (s.nr 1 + 1) ∧
      out.nr 261 = s.nm (s.nr 1 + 1) - 1 ∧
      out.nr 262 = s.nm (s.nr 171 + (s.nm (s.nr 1 + 1) - 1)) ∧
      out.rr 260 = s.rm (s.nr 1 + 1)

def treeRecordDistance_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  Run input (.atoms treeRecordDistanceAtoms) s (treeRecordedDistance s) 6

def treeRecordedDistance_value_contract_statement : Prop :=
  ∀ (s : Store),
  (treeRecordedDistance s).rm (targetAddress (s.nr 262) + s.nr 173) = s.rr 260

def treeRecordedDistance_frame_contract_statement : Prop :=
  ∀ (s : Store) (a : ℕ)
    (ha : a ≠ targetAddress (s.nr 262) + s.nr 173),
  (treeRecordedDistance s).nm = s.nm ∧ (treeRecordedDistance s).rm a = s.rm a

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

def encodeInput_edge_left_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (k : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[k]? = some e),
  (encodeInput I ε).naturals (3+2*k) = e.1

def encodeInput_edge_right_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (k : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[k]? = some e),
  (encodeInput I ε).naturals (3+2*k+1) = e.2

def encodeInput_length_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (k : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[k]? = some e),
  (encodeInput I ε).reals (2+2*k) = (I.length e.1 e.2 : ℝ)

def encodeInput_cost_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (k : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[k]? = some e),
  (encodeInput I ε).reals (2+2*k+1) = (I.cost e.1 e.2 : ℝ)

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def treeEdgeAtoms_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input treeEdgeAtoms s = treeEdgeLoaded input s

def treeEdgeLoaded_values_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (s : Store) (e : ℕ × ℕ)
    (he : I.graph.edges[s.nr 265]? = some e) (hone : s.nr 4 = 1),
  (treeEdgeLoaded (encodeInput I ε) s).nr 268 = e.2 ∧
    (treeEdgeLoaded (encodeInput I ε) s).rr 261 = (I.length e.1 e.2 : ℝ) ∧
    (treeEdgeLoaded (encodeInput I ε) s).rr 262 = (I.cost e.1 e.2 : ℝ)

def treeTargetAtoms_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input treeTargetAtoms s = treeTargetLoaded s

def treeDecreaseAtoms_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input treeDecreaseAtoms s = treeDecreased s

def treeDecreased_header_contract_statement : Prop :=
  ∀ (s : Store) (r : ℕ) (hr : r < 11),
  (treeDecreased s).nr r = s.nr r

def treeApplyDecrease_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (B : ℕ)
    (truth : ℕ → Queue.Record) (s : Store)
    (hp : Queue.ParentLayout (2 * B) (treeDecreased s)) (hone : s.nr 4 = 1)
    (hpositive : 0 < s.nr 0) (hc : Queue.Coherent (2 * B) truth)
    (hr : Queue.Ready (2 * B) truth (treeDecreased s))
    (hnew : truth (s.nr 0) = ⟨s.nr 10, s.rr 264⟩),
  ∃ out steps, Run input treeApplyDecrease s out steps ∧
      steps ≤ 19 * Nat.clog 2 (2 * B) + 14 ∧
      Queue.ParentLayout (2 * B) out ∧
      ∀ v < 2 * B, Queue.readRecord out (s.nr 1 + v) = truth v

def adjacencyAtoms_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input adjacencyAtoms s = adjacencyResult s

def adjacencyInsert_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  Run input adjacencyInsert s (adjacencyResult s) 6

def adjacencyResult_head_contract_statement : Prop :=
  ∀ (s : Store) (hone : s.nr 126 = 1),
  (adjacencyResult s).nm (s.nr 163 + s.nr 161) = s.nr 160 + 1

def adjacencyResult_link_contract_statement : Prop :=
  ∀ (s : Store)
    (hsep : s.nr 164 + s.nr 160 ≠ s.nr 163 + s.nr 161),
  (adjacencyResult s).nm (s.nr 164 + s.nr 160) = s.nm (s.nr 163 + s.nr 161)

def adjacencyResult_memory_frame_contract_statement : Prop :=
  ∀ (s : Store) (a : ℕ)
    (hh : a ≠ s.nr 163 + s.nr 161) (hl : a ≠ s.nr 164 + s.nr 160),
  (adjacencyResult s).nm a = s.nm a

def adjacencyResult_register_frame_contract_statement : Prop :=
  ∀ (s : Store) (r : ℕ)
    (h165 : r ≠ 165) (h166 : r ≠ 166) (h167 : r ≠ 167) (h168 : r ≠ 168),
  (adjacencyResult s).nr r = s.nr r

def adjacencyResult_real_frame_contract_statement : Prop :=
  ∀ (s : Store),
  (adjacencyResult s).rr = s.rr ∧ (adjacencyResult s).rm = s.rm

def AdjacencyChain.frame_contract_statement : Prop :=
  ∀ {mem mem' : ℕ → ℕ} {links token : ℕ} {es : List ℕ}
    (h : AdjacencyChain mem links token es)
    (hf : ∀ e ∈ es, mem' (links + e) = mem (links + e)),
  AdjacencyChain mem' links token es

def adjacencyInsert_chain_contract_statement : Prop :=
  ∀ (s : Store) (es : List ℕ)
    (hone : s.nr 126 = 1)
    (hold : AdjacencyChain s.nm (s.nr 164) (s.nm (s.nr 163 + s.nr 161)) es)
    (hfresh : s.nr 160 ∉ es)
    (hsep : ∀ e, s.nr 164 + e ≠ s.nr 163 + s.nr 161),
  AdjacencyChain (adjacencyResult s).nm (s.nr 164)
      ((adjacencyResult s).nm (s.nr 163 + s.nr 161)) (s.nr 160 :: es)

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def treeAdjacencyPrepared_scratch_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  TreeIteratorScratch s (treeAdjacencyPrepared input s)

def treeAdjacencyAdvanced_scratch_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  TreeIteratorScratch s (treeAdjacencyAdvanced input s)

def treeAdjacencyPrepared_values_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (treeAdjacencyPrepared input s).nr 265 = s.nr 278-s.nr 4 ∧
    (treeAdjacencyPrepared input s).nr 279 = s.nm (s.nr 139+(s.nr 278-s.nr 4))

def treeAdjacencyLoop_run_of_edge_contract_contract_statement : Prop :=
  ∀ {α : Type u_1}
    (input : RAMInput) (links C : ℕ) (valid protect : ℕ → Prop)
    (step : α → ℕ → α) (Inv : α → Store → Prop)
    (htransfer : ∀ S s t, Inv S s → TreeIteratorScratch s t → Inv S t)
    (hedge : ∀ S e s, valid e → Inv S s → s.nr 265 = e →
      ∃ t n, Run input treeRelaxEdgeCmd s t n ∧ Inv (step S e) t ∧ n ≤ C ∧
        (∀ k, valid k → t.nm (links+k) = s.nm (links+k)) ∧
        (∀ a, protect a → t.nm a = s.nm a ∧ t.rm a = s.rm a))
    (es : List ℕ) (S : α) (s : Store) (token : ℕ)
    (hchain : AdjacencyChain s.nm links token es)
    (hvalid : ∀ e ∈ es, valid e) (hInv : Inv S s)
    (hz : s.nr 3 = 0) (ho : s.nr 4 = 1) (hl : s.nr 139 = links)
    (htoken : s.nr 278 = token),
  ∃ out n, Run input treeAdjacencyLoop s out n ∧ Inv (es.foldl step S) out ∧
      out.nr 278 = 0 ∧ n ≤ (C+6)*es.length+1 ∧
      (∀ a, protect a → out.nm a = s.nm a ∧ out.rm a = s.rm a)

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def treeCheckTarget_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (B : ℕ) (leaf : ℕ → Queue.Record)
    (s : Store)
    (hp : Queue.ParentLayout (2 * B) (treeTargetLoaded s)) (hone : s.nr 4 = 1)
    (hpositive : 0 < (treeTargetLoaded s).nr 0) (hleaf : B ≤ (treeTargetLoaded s).nr 0)
    (hrep : Queue.Represents B ((treeTargetLoaded s).nr 1) leaf (treeTargetLoaded s))
    (hparent : targetAddress ((treeTargetLoaded s).nr 268) + (treeTargetLoaded s).nr 173 < (treeTargetLoaded s).nr 1),
  ∃ out steps, Run input treeCheckTarget s out steps ∧
      steps ≤ 19 * Nat.clog 2 (2 * B) + 25 ∧
      Queue.ParentLayout (2 * B) out ∧
      Queue.Represents B ((treeTargetLoaded s).nr 1) (treeCheckedLeaf leaf (treeTargetLoaded s)) out ∧
      (∀ a, a < (treeTargetLoaded s).nr 1 ∨ (treeTargetLoaded s).nr 1 + 2 * B ≤ a →
        out.nm a = treeCheckedNatMemory (treeTargetLoaded s) a ∧ out.rm a = (treeTargetLoaded s).rm a)

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
open scoped NNReal
namespace NearLinearRSP.TwoResources

def treePolicy_candidate_sentinel_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ→ℕ→Bool)
    (w : ℕ→ℕ→ℝ≥0) (S : TreeQueue)
    (h : TreePolicy I allow (fun u v=>(w u v:ℝ)) S)
    (hs : (S.tree I.source).distance=some 0) (u v : ℕ) (d : ℝ)
    (hd : (S.tree u).distance=some d) (he : (u,v)∈I.graph.edges),
  d+(w u v:ℝ) < ((I.graph.n:ℝ)+1)*(1+edgeWeightSum I w)

def sentinelKey_le_contract_statement : Prop :=
  ∀ (top : ℝ) (T : ShortestTree) (v : ℕ)
    (h : ∀ d, (T v).distance=some d → d<top),
  sentinelKey top T v≤top

def sentinel_source_none_no_decrease_contract_statement : Prop :=
  ∀ (top : ℝ) (T : ShortestTree) (u v : ℕ)
    (hu : (T u).distance=none) (weight : ℝ) (hw : 0≤weight)
    (hv : ∀ d, (T v).distance=some d → d<top),
  ¬ sentinelKey top T u+weight < sentinelKey top T v

def sentinel_finite_candidate_comparison_contract_statement : Prop :=
  ∀ (top : ℝ) (T : ShortestTree) (v : ℕ)
    (candidate : ℝ) (hc : candidate<top)
    (hv : ∀ d, (T v).distance=some d → d<top),
  distanceLess (some candidate) (T v).distance = decide (candidate<sentinelKey top T v)

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

def treeRelax_eq_real_test_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (u v : ℕ) (top : ℝ)
    (hu : u ∉ S.queue) (hw : 0 ≤ w u v)
    (hfinite : ∀ x d, (S.tree x).distance = some d → d < top)
    (hcandidate : ∀ d, (S.tree u).distance = some d → d + w u v < top),
  treeRelax I allow w u S (u,v) =
      if v ∈ S.queue ∧ allow u v = true ∧
          sentinelKey top S.tree u + w u v < sentinelKey top S.tree v then
        { S with tree := Function.update S.tree v ⟨some (sentinelKey top S.tree u + w u v), some u, 0⟩ }
      else S

def sentinelKey_update_contract_statement : Prop :=
  ∀ (top : ℝ) (T : ShortestTree) (v : ℕ) (d : ℝ)
    (parent rank : ℕ),
  sentinelKey top (Function.update T v ⟨some d, some parent, rank⟩) =
      Function.update (sentinelKey top T) v d

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def TreeMemoryRep.congr_contract_statement : Prop :=
  ∀ {I : Instance} {B W P map array off : ℕ} {top : ℝ}
    {S : TreeQueue} {s t : Store} (h : TreeMemoryRep I B W P map array off top S s)
    (hmap : t.nr 141 = s.nr 141) (harray : t.nr 142 = s.nr 142)
    (hcount : t.nr 143 = s.nr 143) (hn : t.nm = s.nm) (hr : t.rm = s.rm),
  TreeMemoryRep I B W P map array off top S t

def TreeMemoryRep.after_readonly_contract_statement : Prop :=
  ∀ {I : Instance} {B W P map array off : ℕ} {top : ℝ}
    {S : TreeQueue} {s t : Store} (h : TreeMemoryRep I B W P map array off top S s)
    {input : RAMInput} {cmd : Cmd} {steps : ℕ} (hrun : Run input cmd s t steps)
    (h141 : 141 ∉ cmd.natWrites) (h142 : 142 ∉ cmd.natWrites) (h143 : 143 ∉ cmd.natWrites)
    (hn : cmd.writesNatMemory = false) (hr : cmd.writesRealMemory = false),
  TreeMemoryRep I B W P map array off top S t

def treeTarget_values_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (S : TreeQueue) (s : Store) (v : ℕ) (hm : E.Memory mode S s)
    (hr : E.Registers mode s) (hv : v ∈ activeVertices I) (hhead : s.nr 268 = v),
  let k := (activeVertices I).idxOf v
  let p := treeTargetLoaded s
  p.nr 0 = E.B+k ∧ p.nr 10 = (if v ∈ S.queue then k+1 else 0) ∧
  p.rr 265 = sentinelKey (mode.top I) S.tree v

def treeTarget_correct_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (S : TreeQueue) (input : RAMInput) (s : Store) (u v : ℕ) (d : ℝ)
    (hm : E.Memory mode S s) (hr : E.Registers mode s)
    (hv : v ∈ activeVertices I) (hu : s.nr 262 = u) (hhead : s.nr 268 = v)
    (hd : s.rr 264 = d),
  ∃ out steps, Run input treeCheckTarget s out steps ∧
      steps ≤ 19*Nat.clog 2 (2*E.B)+25 ∧
      E.Memory mode (treeTargetState (mode.top I) S u v d) out ∧
      E.Registers mode out ∧ TreeEdgeFrame E.W E.B (targetAddress v+mode.offset) s out

def TreeMode.sentinel_bounds_contract_statement : Prop :=
  ∀ (mode : TreeMode) (I : Instance) (S : TreeQueue)
    (h : TreePolicy I (mode.allow I) (mode.weight I) S)
    (hs : (S.tree I.source).distance = some 0) (u v : ℕ) (he : (u,v) ∈ I.graph.edges),
  (∀ x d, (S.tree x).distance = some d → d < mode.top I) ∧
    (∀ d, (S.tree u).distance = some d → d + mode.weight I u v < mode.top I)

def standalone_Mission_RAMTreeEdge__edgeGuard_value_contract_statement : Prop :=
  ∀ (I : Instance) (mode : TreeMode) (s : Store) (u v : ℕ)
    (hL : s.rr 261 = I.length u v) (hC : s.rr 262 = I.cost u v) (hz : s.rr 263 = 0),
  (standalone_Mission_RAMTreeEdge__edgeGuard mode).eval s = mode.allow I u v

def standalone_Mission_RAMTreeEdge__candidate_value_contract_statement : Prop :=
  ∀ (I : Instance) (mode : TreeMode) (input : RAMInput)
    (s : Store) (u v : ℕ) (key : ℝ) (hkey : s.rr 260 = key)
    (hL : s.rr 261 = I.length u v) (hC : s.rr 262 = I.cost u v),
  ((standalone_Mission_RAMTreeEdge__candidateAtom mode).eval input s).rr 264 = key + mode.weight I u v

def standalone_Mission_RAMTreeEdge__modeBody_correct_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (S : TreeQueue) (input : RAMInput) (s : Store) (u v : ℕ)
    (hm : E.Memory mode S s) (hr : E.Registers mode s)
    (he : (u,v) ∈ I.graph.edges) (huq : u ∉ S.queue)
    (hpolicy : TreePolicy I (mode.allow I) (mode.weight I) S)
    (hs : (S.tree I.source).distance = some 0)
    (hu : s.nr 262 = u) (hv : s.nr 268 = v)
    (hkey : s.rr 260 = sentinelKey (mode.top I) S.tree u)
    (hL : s.rr 261 = I.length u v) (hC : s.rr 262 = I.cost u v) (hz : s.rr 263 = 0),
  ∃ out steps, Run input (standalone_Mission_RAMTreeEdge__modeBody mode) s out steps ∧
      steps ≤ 19*Nat.clog 2 (2*E.B)+28 ∧
      E.Memory mode (treeRelax I (mode.allow I) (mode.weight I) u S (u,v)) out ∧
      E.Registers mode out ∧ TreeEdgeFrame E.W E.B (targetAddress v+mode.offset) s out

def treeEdge_correct_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (S : TreeQueue) (ε : ℝ) (s : Store) (u v : ℕ)
    (hm : E.Memory mode S s) (hr : E.Registers mode s)
    (he : I.graph.edges[s.nr 265]? = some (u,v)) (huq : u ∉ S.queue)
    (hpolicy : TreePolicy I (mode.allow I) (mode.weight I) S)
    (hs : (S.tree I.source).distance = some 0)
    (hu : s.nr 262 = u) (hkey : s.rr 260 = sentinelKey (mode.top I) S.tree u),
  ∃ out steps, Run (encodeInput I ε) treeRelaxEdgeCmd s out steps ∧
      steps ≤ 19*Nat.clog 2 (2*E.B)+40 ∧
      E.Memory mode (treeRelax I (mode.allow I) (mode.weight I) u S (u,v)) out ∧
      E.Registers mode out ∧ TreeEdgeFrame E.W E.B (targetAddress v+mode.offset) s out

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

def treeRelax_source_zero_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (u : ℕ) (S : TreeQueue)
    (hn : ∀ v, 0 ≤ treeDist S.tree v) (hs : (S.tree I.source).distance = some 0)
    (e : ℕ × ℕ),
  ((treeRelax I allow w u S e).tree I.source).distance = some 0

def TreeScanMath.step_contract_statement : Prop :=
  ∀ {I : Instance} {allow : ℕ → ℕ → Bool} {w : ℕ → ℕ → ℝ}
    {u : ℕ} {S : TreeQueue} (h : TreeScanMath I allow w u S)
    (hw : ∀ u v, 0 ≤ w u v) (e : ℕ × ℕ) (he : e ∈ I.graph.edges),
  TreeScanMath I allow w u (treeRelax I allow w u S e)

def TreeScanMath.start_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool) (w : ℕ → ℕ → ℝ)
    (S : TreeQueue) (u : ℕ) (hu : u ∈ S.queue) (hq : S.queue.Nodup)
    (hp : TreePolicy I allow w S) (hn : ∀ v, 0 ≤ treeDist S.tree v)
    (hs : (S.tree I.source).distance = some 0),
  TreeScanMath I allow w u (treeSettle S u)

def relaxEdge_nonoutgoing_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (he : e.1 ≠ u),
  relaxEdge A i j u S e = S

def relaxFold_filter_outgoing_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (es : List (ℕ × ℕ)),
  (es.filter (fun e => e.1 == u)).foldl (relaxEdge A i j u) S =
      es.foldl (relaxEdge A i j u) S

def relaxAll_eq_outgoingFold_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState),
  relaxAll A i j u S = (outgoingEdges A.I u).foldl (relaxEdge A i j u) S

def treeRelax_nonoutgoing_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e : ℕ × ℕ)
    (he : e.1 ≠ u),
  treeRelax I allow w u S e = S

def treeRelaxFold_filter_outgoing_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (es : List (ℕ × ℕ)),
  (es.filter (fun e => e.1 == u)).foldl (treeRelax I allow w u) S =
      es.foldl (treeRelax I allow w u) S

def treeRelaxAll_eq_outgoingFold_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue),
  treeRelaxAll I allow w u S =
      (outgoingEdges I u).foldl (treeRelax I allow w u) S

def relaxEdge_disabled_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (he : ¬ (e.1 = u ∧ e.1 ≠ e.2 ∧ e.2 ∈ S.queue)),
  relaxEdge A i j u S e = S

def treeRelax_disabled_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e : ℕ × ℕ)
    (he : ¬ (e.1 = u ∧ e.1 ≠ e.2 ∧ e.2 ∈ S.queue ∧ allow e.1 e.2 = true)),
  treeRelax I allow w u S e = S

def relaxEdge_comm_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e f : ℕ × ℕ),
  relaxEdge A i j u (relaxEdge A i j u S e) f =
      relaxEdge A i j u (relaxEdge A i j u S f) e

def relaxFold_perm_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (es fs : List (ℕ × ℕ)) (h : es.Perm fs),
  es.foldl (relaxEdge A i j u) S = fs.foldl (relaxEdge A i j u) S

def relaxAll_eq_reversedOutgoingFold_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState),
  relaxAll A i j u S = (outgoingEdges A.I u).reverse.foldl (relaxEdge A i j u) S

def treeRelax_comm_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (weight : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e f : ℕ × ℕ),
  treeRelax I allow weight u (treeRelax I allow weight u S e) f =
      treeRelax I allow weight u (treeRelax I allow weight u S f) e

def treeRelaxFold_perm_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue)
    (es fs : List (ℕ × ℕ)) (h : es.Perm fs),
  es.foldl (treeRelax I allow w u) S = fs.foldl (treeRelax I allow w u) S

def treeRelaxAll_eq_reversedOutgoingFold_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue),
  treeRelaxAll I allow w u S =
      (outgoingEdges I u).reverse.foldl (treeRelax I allow w u) S

def popLayer_reversed_refinement_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hne : S.queue ≠ []),
  popLayer A i j S = (outgoingEdges A.I (pickedVertex S)).reverse.foldl
      (relaxEdge A i j (pickedVertex S)) (settleState S i j (pickedVertex S))

def treePop_reversed_refinement_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (hne : S.queue ≠ []),
  treePop I allow w S = (outgoingEdges I (treePick S)).reverse.foldl
      (treeRelax I allow w (treePick S)) (treeSettle S (treePick S))

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def adjacencyStep_index_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (adjacencyStep input s).nr 160 = s.nr 160 + 1

def adjacencyStep_inputPointer_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (adjacencyStep input s).nr 162 = s.nr 162 + 2

def adjacencyStep_register_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (r : ℕ)
    (h160 : r ≠ 160) (h161 : r ≠ 161) (h162 : r ≠ 162)
    (h165 : r ≠ 165) (h166 : r ≠ 166) (h167 : r ≠ 167) (h168 : r ≠ 168),
  (adjacencyStep input s).nr r = s.nr r

def adjacencyScanBody_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store)
    (hone : s.nr 126 = 1) (htwo : s.nr 127 = 2),
  Run input adjacencyScanBody s (adjacencyStep input s) 9

def adjacencyScanLoop_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (remaining : ℕ) (s : Store)
    (hone : s.nr 126 = 1) (htwo : s.nr 127 = 2)
    (hend : s.nr 160 + remaining = s.nr 122),
  Run input adjacencyScanLoop s (adjacencyScanResult input remaining s) (11*remaining+1)

def adjacencyScanCmd_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store)
    (hone : s.nr 126 = 1) (htwo : s.nr 127 = 2),
  Run input adjacencyScanCmd s
      (adjacencyScanResult input (s.nr 122) (adjacencyPrepared s)) (11*s.nr 122+3)

def outgoingIndices_lt_contract_statement : Prop :=
  ∀ (I : Instance) (count v e : ℕ)
    (he : e ∈ outgoingIndices I count v),
  e < count

def outgoingIndices_succ_contract_statement : Prop :=
  ∀ (I : Instance) (count v : ℕ),
  outgoingIndices I (count+1) v =
      if (edgeAt I count).1 = v then count :: outgoingIndices I count v
      else outgoingIndices I count v

def adjacencyPrefix_zero_contract_statement : Prop :=
  ∀ (I : Instance) (heads links : ℕ) (mem : ℕ → ℕ)
    (hz : ∀ v<I.graph.n, mem (heads+v)=0),
  AdjacencyPrefix I 0 heads links mem

def edgeAt_valid_contract_statement : Prop :=
  ∀ (I : Instance) (e : ℕ) (he : e < I.graph.edges.length),
  (edgeAt I e).1 < I.graph.n ∧ (edgeAt I e).2 < I.graph.n

def adjacencyStep_prefix_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (s : Store) (count heads links : ℕ)
    (hone : s.nr 126=1) (hcount : s.nr 160=count) (hp : s.nr 162=3+2*count)
    (hh : s.nr 163=heads) (hl : s.nr 164=links) (hvalid : count<I.graph.edges.length)
    (hsep : heads+I.graph.n ≤ links) (h : AdjacencyPrefix I count heads links s.nm),
  AdjacencyPrefix I (count+1) heads links (adjacencyStep (encodeInput I ε) s).nm

def adjacencyScanResult_register_contract_statement : Prop :=
  ∀ (input : RAMInput) (n : ℕ) (s : Store) (r : ℕ)
    (h160 : r ≠ 160) (h161 : r ≠ 161) (h162 : r ≠ 162)
    (h165 : r ≠ 165) (h166 : r ≠ 166) (h167 : r ≠ 167) (h168 : r ≠ 168),
  (adjacencyScanResult input n s).nr r = s.nr r

def adjacencyScanResult_reals_contract_statement : Prop :=
  ∀ (input : RAMInput) (n : ℕ) (s : Store),
  (adjacencyScanResult input n s).rr = s.rr ∧
      (adjacencyScanResult input n s).rm = s.rm

def adjacencyScanResult_prefix_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (remaining : ℕ)
    (s : Store) (count heads links : ℕ)
    (hone : s.nr 126=1) (hcount : s.nr 160=count) (hp : s.nr 162=3+2*count)
    (hh : s.nr 163=heads) (hl : s.nr 164=links)
    (hvalid : count+remaining≤I.graph.edges.length)
    (hsep : heads+I.graph.n≤links) (h : AdjacencyPrefix I count heads links s.nm),
  AdjacencyPrefix I (count+remaining) heads links
      (adjacencyScanResult (encodeInput I ε) remaining s).nm

def adjacencyStep_memory_outside_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (s : Store)
    (count heads links a : ℕ) (hcount : s.nr 160=count) (hp : s.nr 162=3+2*count)
    (hh : s.nr 163=heads) (hl : s.nr 164=links) (hk : count<I.graph.edges.length)
    (hahead : a<heads ∨ heads+I.graph.n≤a)
    (halink : a<links ∨ links+I.graph.edges.length≤a),
  (adjacencyStep (encodeInput I ε) s).nm a = s.nm a

def adjacencyScanResult_memory_outside_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (remaining : ℕ)
    (s : Store) (count heads links a : ℕ)
    (hcount : s.nr 160=count) (hp : s.nr 162=3+2*count)
    (hh : s.nr 163=heads) (hl : s.nr 164=links)
    (hvalid : count+remaining≤I.graph.edges.length)
    (hahead : a<heads ∨ heads+I.graph.n≤a)
    (halink : a<links ∨ links+I.graph.edges.length≤a),
  (adjacencyScanResult (encodeInput I ε) remaining s).nm a = s.nm a

def adjacencyScanCmd_correct_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (s : Store) (heads links : ℕ)
    (hm : s.nr 122=I.graph.edges.length) (hone : s.nr 126=1) (htwo : s.nr 127=2)
    (hh : s.nr 163=heads) (hl : s.nr 164=links) (hsep : heads+I.graph.n≤links)
    (hzero : ∀ v<I.graph.n, s.nm (heads+v)=0),
  ∃ out, Run (encodeInput I ε) adjacencyScanCmd s out (11*I.graph.edges.length+3) ∧
      AdjacencyPrefix I I.graph.edges.length heads links out.nm ∧
      out.rr=s.rr ∧ out.rm=s.rm ∧
      (∀ a, (a<heads ∨ heads+I.graph.n≤a) →
        (a<links ∨ links+I.graph.edges.length≤a) → out.nm a=s.nm a) ∧
      (∀ r, r≠160 → r≠161 → r≠162 → r≠165 → r≠166 → r≠167 → r≠168 → out.nr r=s.nr r)

def standalone_Mission_RAMAdjacencyScan__map_filter_compat_contract_statement : Prop :=
  ∀ {α β : Type} (f : α→β) (p : β→Bool) (xs : List α),
  (xs.filter (fun x=>p (f x))).map f = (xs.map f).filter p

def edgeAt_map_range_contract_statement : Prop :=
  ∀ (I : Instance),
  (List.range I.graph.edges.length).map (edgeAt I) = I.graph.edges

def outgoingIndices_edges_contract_statement : Prop :=
  ∀ (I : Instance) (v : ℕ),
  (outgoingIndices I I.graph.edges.length v).map (edgeAt I) = (outgoingEdges I v).reverse

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def TreeScanInvariant.transfer_contract_statement : Prop :=
  ∀ {I : Instance} {E : TreeAllocation I} {mode : TreeMode}
    {u : ℕ} {S : TreeQueue} {s t : Store} (h : TreeScanInvariant E mode u S s)
    (hf : TreeIteratorScratch s t),
  TreeScanInvariant E mode u S t

def TreeAllocation.link_protected_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) (k : ℕ) (hk : k < I.graph.edges.length),
  TreeProtected E mode (E.links+k)

def TreeAllocation.graph_protected_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) (a : ℕ) (hlo : E.map ≤ a) (hhi : a < E.W),
  TreeProtected E mode a

def AdjacencyPrefix.protected_frame_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) {s t : Store}
    (h : AdjacencyPrefix I I.graph.edges.length E.heads E.links s.nm)
    (hf : ∀ a, TreeProtected E mode a → t.nm a = s.nm a),
  AdjacencyPrefix I I.graph.edges.length E.heads E.links t.nm

def outgoingIndices_valid_contract_statement : Prop :=
  ∀ (I : Instance) (u e : ℕ)
    (he : e ∈ outgoingIndices I I.graph.edges.length u),
  ∃ v, I.graph.edges[e]? = some (u,v)

def treeScan_run_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (ε : ℝ) (u : ℕ) (S : TreeQueue) (s : Store) (es : List ℕ) (token : ℕ)
    (hchain : AdjacencyChain s.nm E.links token es)
    (hvalid : ∀ e ∈ es, ∃ v, I.graph.edges[e]? = some (u,v))
    (hInv : TreeScanInvariant E mode u S s) (htoken : s.nr 278 = token),
  ∃ out steps, Run (encodeInput I ε) treeAdjacencyLoop s out steps ∧
      TreeScanInvariant E mode u
        (es.foldl (fun T e => treeRelax I (mode.allow I) (mode.weight I) u T (edgeAt I e)) S) out ∧
      out.nr 278 = 0 ∧ steps ≤ (19*Nat.clog 2 (2*E.B)+46)*es.length+1 ∧
      (∀ a, TreeProtected E mode a → out.nm a = s.nm a ∧ out.rm a = s.rm a)

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured Queue

def standalone_Mission_RAMTreeExtractRefinement__queue_update_nat_high_contract_statement : Prop :=
  ∀ {input : RAMInput} {s out : Store} {steps r : ℕ}
    (h : Run input updateLeaf s out steps) (hr : 11 ≤ r),
  out.nr r=s.nr r

def standalone_Mission_RAMTreeExtractRefinement__queue_update_real_high_contract_statement : Prop :=
  ∀ {input : RAMInput} {s out : Store} {steps r : ℕ}
    (h : Run input updateLeaf s out steps) (hr : 2 ≤ r),
  out.rr r=s.rr r

def treeExtract_refines_contract_statement : Prop :=
  ∀ (input : RAMInput) (B height : ℕ)
    (xs q : List ℕ) (key : ℕ→ℝ) (s : Store)
    (hB : B=2^height) (hfit : xs.length ≤ B)
    (hxs : xs.Nodup) (hq : q.Sublist xs) (hne : q ≠ [])
    (hp : s.nr 1+2*B ≤ s.nr 2 ∧ s.nr 3=0 ∧
      ∀ node < 2*B,s.nm (s.nr 2+node)=node/2)
    (hone : s.nr 4=1) (hbase : s.nr 170=B)
    (harray : ∀ k v, xs[k]?=some v → s.nm (s.nr 171+k)=v)
    (hrep : Represents B (s.nr 1) (activeLeaf xs q key B) s),
  let u := firstMin key q 0
  ∃ out cost, Run input treeExtract s out cost ∧
    cost ≤ 19*Nat.clog 2 (2*B)+15 ∧ ParentLayout (2*B) out ∧
    Represents B (s.nr 1) (activeLeaf xs (q.erase u) key B) out ∧
    WinnerFrame (s.nr 1) (2*B) s out ∧
    out.nr 0=0 ∧ (∀ r,0 < r → r < 5 → out.nr r=s.nr r) ∧
    out.nr 260=xs.idxOf u+1 ∧ out.nr 261=xs.idxOf u ∧
    out.nr 262=u ∧ out.rr 260=key u

def treeExtract_high_register_contract_statement : Prop :=
  ∀ (input : RAMInput) (s out : Store) (cost r : ℕ)
    (h : Run input treeExtract s out cost) (hr : 11 ≤ r)
    (h260 : r ≠ 260) (h261 : r ≠ 261) (h262 : r ≠ 262),
  out.nr r=s.nr r

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def sentinelKey_treeSettle_contract_statement : Prop :=
  ∀ (top : ℝ) (S : TreeQueue) (u : ℕ),
  sentinelKey top (treeSettle S u).tree=sentinelKey top S.tree

def treeSettle_parent_unchanged_contract_statement : Prop :=
  ∀ (S : TreeQueue) (u v : ℕ),
  ((treeSettle S u).tree v).parent=(S.tree v).parent

def treeExtract_registers_contract_statement : Prop :=
  ∀ (I : Instance) (E : TreeAllocation I) (mode : TreeMode)
    (input : RAMInput) (s out : Store) (cost : ℕ)
    (hR : E.Registers mode s) (h : Run input treeExtract s out cost),
  E.Registers mode out

def treeSettle_registers_contract_statement : Prop :=
  ∀ (I : Instance) (E : TreeAllocation I) (mode : TreeMode)
    (input : RAMInput) (s out : Store) (cost : ℕ)
    (hR : E.Registers mode s) (h : Run input treeSettleCmd s out cost),
  E.Registers mode out

def treeSettle_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (I : Instance) (E : TreeAllocation I)
    (mode : TreeMode) (S : TreeQueue) (s : Store)
    (hM : E.Memory mode S s) (hR : E.Registers mode s) (hne : S.queue ≠ [])
    (hfinite : ∀ v d,(S.tree v).distance=some d → d < mode.top I),
  ∃ out cost, Run input treeSettleCmd s out cost ∧
      cost ≤ 19*Nat.clog 2 (2*E.B)+21 ∧
      E.Memory mode (treeSettle S (treePick S)) out ∧ E.Registers mode out ∧
      out.nr 262=treePick S ∧ out.rr 260=sentinelKey (mode.top I) S.tree (treePick S) ∧
      (∀ a,(a < E.W ∨ E.W+2*E.B ≤ a) → out.nm a=s.nm a) ∧
      (∀ a,(a < E.W ∨ E.W+2*E.B ≤ a) →
        a ≠ targetAddress (treePick S)+mode.offset → out.rm a=s.rm a)

def treeSettle_counter277_contract_statement : Prop :=
  ∀ (input : RAMInput) (s out : Store) (cost : ℕ)
    (h : Run input treeSettleCmd s out cost),
  out.nr 277=s.nr 277

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources

def outgoingWork_erase_contract_statement : Prop :=
  ∀ (I : Instance) (vertices : List ℕ) (u : ℕ) (hu : u ∈ vertices),
  (outgoingEdges I u).length + outgoingWork I (vertices.erase u) = outgoingWork I vertices

def standalone_Mission_OutgoingWork__indicator_sum_contract_statement : Prop :=
  ∀ (xs : List ℕ) (u : ℕ),
  (xs.map (fun v => if u = v then 1 else 0)).sum = xs.count u

def standalone_Mission_OutgoingWork__outgoing_filter_count_contract_statement : Prop :=
  ∀ (edges : List (ℕ × ℕ)) (vertices : List ℕ)
    (hnd : vertices.Nodup) (hs : ∀ e ∈ edges, e.1 ∈ vertices),
  (vertices.map (fun u => (edges.filter (fun e => e.1 == u)).length)).sum = edges.length

def outgoingWork_active_contract_statement : Prop :=
  ∀ (I : Instance),
  outgoingWork I (activeVertices I) = I.graph.edges.length

def outgoingWork_settle_contract_statement : Prop :=
  ∀ (I : Instance) (S : LayerState) (i j u : ℕ) (hu : u ∈ S.queue),
  (outgoingEdges I u).length + outgoingWork I (settleState S i j u).queue =
      outgoingWork I S.queue

def queueRun_succ_front_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState),
  queueRun A i j (n+1) S = queueRun A i j n (popLayer A i j S)

def popLayer_nextRank_of_ne_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hne : S.queue≠[]),
  (popLayer A i j S).nextRank=S.nextRank+1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def standalone_Mission_RAMTreePop__seq_attach_contract_statement : Prop :=
  ∀ {input : RAMInput} {a b c : Cmd} {s t out : Store} {n m : ℕ}
    (hab : Run input (.seq a b) s t n) (hc : Run input c t out m),
  Run input (.seq a (.seq b c)) s out (n+m)

def treeHeadStore_token_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (treeHeadStore input s).nr 278 = s.nm (s.nr 137+s.nr 262)

def treePopCmd_run_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (ε : ℝ) (S : TreeQueue) (s : Store)
    (hm : E.Memory mode S s) (hr : E.Registers mode s) (hne : S.queue ≠ [])
    (hp : TreePolicy I (mode.allow I) (mode.weight I) S)
    (hn : ∀ v, 0 ≤ treeDist S.tree v) (hs : (S.tree I.source).distance = some 0)
    (hfinite : ∀ v d, (S.tree v).distance=some d → d < mode.top I)
    (hAdj : AdjacencyPrefix I I.graph.edges.length E.heads E.links s.nm),
  ∃ out steps, Run (encodeInput I ε) treePopCmd s out steps ∧
      E.Memory mode (treePop I (mode.allow I) (mode.weight I) S) out ∧
      E.Registers mode out ∧ out.nr 277 = s.nr 277+1 ∧
      steps ≤ 19*Nat.clog 2 (2*E.B)+25 +
        (19*Nat.clog 2 (2*E.B)+46)*(outgoingEdges I (treePick S)).length ∧
      AdjacencyPrefix I I.graph.edges.length E.heads E.links out.nm ∧
      (∀ a, TreeProtected E mode a → out.nm a=s.nm a ∧ out.rm a=s.rm a)

def treePop_outgoingWork_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (hne : S.queue ≠ []),
  (outgoingEdges I (treePick S)).length + outgoingWork I (treePop I allow w S).queue =
      outgoingWork I S.queue

def treeLoop_run_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (ε : ℝ) (remaining k : ℕ) (s : Store)
    (hend : k+remaining=(activeVertices I).length)
    (hm : E.Memory mode (treeState I mode k) s) (hr : E.Registers mode s)
    (hcounter : s.nr 277=k)
    (hAdj : AdjacencyPrefix I I.graph.edges.length E.heads E.links s.nm),
  ∃ out steps, Run (encodeInput I ε) treeLoopCmd s out steps ∧
      E.Memory mode (treeState I mode (activeVertices I).length) out ∧
      E.Registers mode out ∧ out.nr 277=(activeVertices I).length ∧
      steps ≤ (19*Nat.clog 2 (2*E.B)+27)*remaining +
        (19*Nat.clog 2 (2*E.B)+46)*outgoingWork I (treeState I mode k).queue+1 ∧
      AdjacencyPrefix I I.graph.edges.length E.heads E.links out.nm ∧
      (∀ a, TreeProtected E mode a → out.nm a=s.nm a ∧ out.rm a=s.rm a)

def standalone_Mission_RAMTreeRun__seq_attach_contract_statement : Prop :=
  ∀ {input : RAMInput} {a b c : Cmd} {s t out : Store} {n m : ℕ}
    (hab : Run input (.seq a b) s t n) (hc : Run input c t out m),
  Run input (.seq a (.seq b c)) s out (n+m)

def treeCmd_run_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (ε : ℝ) (s : Store) (hr : E.Registers mode s)
    (ha : ActiveRep I.graph.n E.map E.array (activeVertices I) s)
    (hAdj : AdjacencyPrefix I I.graph.edges.length E.heads E.links s.nm),
  ∃ out steps, Run (encodeInput I ε) treeCmd s out steps ∧
      E.Memory mode (treeState I mode (activeVertices I).length) out ∧
      E.Registers mode out ∧
      steps ≤ 15*E.B+(38*Nat.clog 2 (2*E.B)+58)*(activeVertices I).length+
        (19*Nat.clog 2 (2*E.B)+46)*I.graph.edges.length+7 ∧
      AdjacencyPrefix I I.graph.edges.length E.heads E.links out.nm ∧
      (∀ a, TreeWholeProtected E mode a → out.nm a=s.nm a ∧ out.rm a=s.rm a)

def treeState_final_tree_contract_statement : Prop :=
  ∀ (I : Instance) (mode : TreeMode),
  (treeState I mode (activeVertices I).length).tree =
      shortestTree I (mode.allow I) (mode.weight I)

def treeState_final_queue_contract_statement : Prop :=
  ∀ (I : Instance) (mode : TreeMode),
  (treeState I mode (activeVertices I).length).queue=[]

def TreeMemoryRep.final_distances_contract_statement : Prop :=
  ∀ {I : Instance} {E : TreeAllocation I} {mode : TreeMode}
    {s : Store} (h : E.Memory mode (treeState I mode (activeVertices I).length) s)
    (v : ℕ) (hv : v ∈ activeVertices I),
  s.rm (targetAddress v+mode.offset) =
      sentinelKey (mode.top I) (shortestTree I (mode.allow I) (mode.weight I)) v

def TreeMemoryRep.final_parents_contract_statement : Prop :=
  ∀ {I : Instance} {E : TreeAllocation I} {mode : TreeMode}
    {s : Store} (h : E.Memory mode (treeState I mode (activeVertices I).length) s)
    (v : ℕ) (hv : v ∈ activeVertices I),
  s.nm (targetAddress v+mode.offset) =
      (((shortestTree I (mode.allow I) (mode.weight I)) v).parent.map (·+1)).getD 0

def zeroTreeSetup_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (mode : TreeMode) (s : Store),
  Run input (zeroTreeSetup mode) s (zeroTreePrepared mode s) 3

def TreeRegisters.prepare_contract_statement : Prop :=
  ∀ {I : Instance} {E : TreeAllocation I} {old : TreeMode}
    {s : Store} (h : E.Registers old s) (mode : TreeMode)
    (hs : s.rr mode.sentinelRegister=mode.top I),
  E.Registers mode (zeroTreePrepared mode s)

def TreeAllocation.length_field_protected_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I)
    (v : ℕ) (hv : v < I.graph.n),
  TreeWholeProtected E .zeroBudget (targetAddress v+2)

def TreeMode.zeroLength_tree_contract_statement : Prop :=
  ∀ (I : Instance),
  shortestTree I (TreeMode.zeroLength.allow I) (TreeMode.zeroLength.weight I) = zeroLengthTree I

def TreeMode.zeroBudget_tree_contract_statement : Prop :=
  ∀ (I : Instance),
  shortestTree I (TreeMode.zeroBudget.allow I) (TreeMode.zeroBudget.weight I) = zeroBudgetTree I

def zeroTreesCmd_run_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I) (ε : ℝ) (s : Store)
    (hstart : E.Registers .zeroLength (zeroTreePrepared .zeroLength s))
    (hsentinel : s.rr 281=TreeMode.zeroBudget.top I)
    (ha : ActiveRep I.graph.n E.map E.array (activeVertices I) s)
    (hAdj : AdjacencyPrefix I I.graph.edges.length E.heads E.links s.nm),
  ∃ out steps, Run (encodeInput I ε) zeroTreesCmd s out steps ∧
      ZeroTreeMemory I out ∧ E.Registers .zeroBudget out ∧
      AdjacencyPrefix I I.graph.edges.length E.heads E.links out.nm ∧
      steps ≤ 2*(15*E.B+(38*Nat.clog 2 (2*E.B)+58)*(activeVertices I).length+
        (19*Nat.clog 2 (2*E.B)+46)*I.graph.edges.length+7)+6 ∧
      (∀ a, TreeWholeProtected E .zeroLength a → TreeWholeProtected E .zeroBudget a →
        out.nm a=s.nm a ∧ out.rm a=s.rm a)

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

def standalone_Mission_Guesses__min_fold_le_seed_contract_statement : Prop :=
  ∀ (xs : List ℝ) (a : ℝ),
  xs.foldl min a ≤ a

def standalone_Mission_Guesses__min_fold_le_member_contract_statement : Prop :=
  ∀ (xs : List ℝ) (a x : ℝ) (hx : x ∈ xs),
  xs.foldl min a ≤ x

def standalone_Mission_Guesses__seed_le_max_fold_contract_statement : Prop :=
  ∀ (xs : List ℝ) (a : ℝ),
  a ≤ xs.foldl max a

def standalone_Mission_Guesses__member_le_max_fold_contract_statement : Prop :=
  ∀ (xs : List ℝ) (a x : ℝ) (hx : x ∈ xs),
  x ≤ xs.foldl max a

def firstPositiveLength_le_member_contract_statement : Prop :=
  ∀ (I : Instance) (x : ℝ)
    (hx : x ∈ positiveLengths I),
  firstPositiveLength I ≤ x

def member_le_largestLength_contract_statement : Prop :=
  ∀ (I : Instance) (x : ℝ)
    (hx : x ∈ positiveLengths I),
  x ≤ largestLength I

def largestLength_nonneg_contract_statement : Prop :=
  ∀ (I : Instance),
  0 ≤ largestLength I

def firstPositiveLength_le_largestLength_contract_statement : Prop :=
  ∀ (I : Instance)
    (h : positiveLengths I ≠ []),
  firstPositiveLength I ≤ largestLength I

def largestLength_pos_contract_statement : Prop :=
  ∀ (I : Instance) (h : positiveLengths I ≠ []),
  0 < largestLength I

def one_le_aspectRatio_contract_statement : Prop :=
  ∀ (I : Instance),
  1 ≤ aspectRatio I

def crossing_exists_contract_statement : Prop :=
  ∀ (a r top : ℝ) (ha : 0 < a) (hr : 1 < r),
  ∃ k : ℕ, top ≤ a * r ^ k

def firstCrossing_spec_contract_statement : Prop :=
  ∀ (a r top : ℝ) (ha : 0 < a) (hr : 1 < r),
  top ≤ a * r ^ firstCrossing a r top

def firstCrossing_minimal_contract_statement : Prop :=
  ∀ (a r top : ℝ) (ha : 0 < a) (hr : 1 < r)
    (i : ℕ) (hi : i < firstCrossing a r top),
  a * r ^ i < top

def firstCrossing_le_contract_statement : Prop :=
  ∀ (a r top : ℝ) (ha : 0 < a) (hr : 1 < r)
    (i : ℕ) (hi : top ≤ a * r ^ i),
  firstCrossing a r top ≤ i

def firstCrossing_mono_top_contract_statement : Prop :=
  ∀ (a r x y : ℝ) (ha : 0 < a) (hr : 1 < r)
    (hxy : x ≤ y),
  firstCrossing a r x ≤ firstCrossing a r y

def firstCrossing_approx_contract_statement : Prop :=
  ∀ (a r x : ℝ) (ha : 0 < a) (hr : 1 < r)
    (hax : a ≤ x),
  a * r ^ firstCrossing a r x ≤ r * x

def geometricGuesses_cover_contract_statement : Prop :=
  ∀ (I : Instance) (ε x : ℝ)
    (hε : 0 < ε) (hne : positiveLengths I ≠ [])
    (hlo : firstPositiveLength I ≤ x)
    (hhi : x ≤ I.graph.n * largestLength I),
  ∃ L ∈ geometricGuesses I ε, x ≤ L ∧ L ≤ (1 + ε / 4) * x

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.GuessLoop
open Structured

def step_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (k : ℕ),
  Run input (.atoms stepOps) (gridState s k) (gridState s (k+1)) 2

def loop_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store)
    (ha : 0 < s.rr 70) (hr : 1 < s.rr 71) (j d : ℕ)
    (hk : j+d = firstCrossing (s.rr 70) (s.rr 71) (s.rr 72)),
  Run input loopCmd (gridState s j) (gridState s (j+d)) (4*d+1)

def crossingCmd_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store)
    (ha : 0 < s.rr 70) (hr : 1 < s.rr 71),
  Run input crossingCmd s
      (gridState s (firstCrossing (s.rr 70) (s.rr 71) (s.rr 72)))
      (4*firstCrossing (s.rr 70) (s.rr 71) (s.rr 72)+4)

def crossing_result_contract_statement : Prop :=
  ∀ (s : Store) (k : ℕ),
  (gridState s k).nr 70 = k ∧ (gridState s k).rr 73 = s.rr 70*s.rr 71^k

def crossing_frame_contract_statement : Prop :=
  ∀ (s : Store) (k : ℕ),
  (∀ r, r ≠ 70 → r ≠ 71 → (gridState s k).nr r = s.nr r) ∧
    (∀ r, r ≠ 73 → (gridState s k).rr r = s.rr r) ∧
    (gridState s k).nm = s.nm ∧ (gridState s k).rm = s.rm

end NearLinearRSP.TwoResources.Mission.GuessLoop
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources
attribute [local instance] Classical.propDecidable

def acceptedIndex_spec_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (t r : ℕ)
    (h : acceptedIndex I ε t = some r),
  ∃ A, (outerInputs I ε)[r]? = some A ∧ accepted A t

def acceptedIndex_le_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (t r s : ℕ) (A : InnerInput)
    (hr : acceptedIndex I ε t = some r)
    (hs : (outerInputs I ε)[s]? = some A) (ha : accepted A t),
  r ≤ s

def acceptedIndex_exists_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (t : ℕ) (A : InnerInput)
    (hA : A ∈ outerInputs I ε) (ha : accepted A t),
  ∃ r, acceptedIndex I ε t = some r

def answerBranch_inner_iff_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (t r : ℕ),
  answerBranch I ε t = .inner r ↔
      t ≠ I.source ∧
      (∀ d, (zeroLengthTree I t).distance = some d → (I.budget : ℝ) < d) ∧
      I.budget ≠ 0 ∧ acceptedIndex I ε t = some r

def answerBranch_inner_input_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (t r : ℕ)
    (h : answerBranch I ε t = .inner r),
  ∃ A, (outerInputs I ε)[r]? = some A ∧ accepted A t

def answerBranch_zeroLength_spec_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (t : ℕ)
    (h : answerBranch I ε t = .zeroLength),
  t = I.source ∨ ∃ d, (zeroLengthTree I t).distance = some d ∧ d ≤ I.budget

def answerBranch_zeroBudget_spec_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (t : ℕ)
    (h : answerBranch I ε t = .zeroBudget),
  I.budget = 0 ∧ (zeroBudgetTree I t).distance.isSome = true

def outerInputs_mem_fields_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (A : InnerInput)
    (hA : A ∈ outerInputs I ε),
  A.I = I ∧ A.δ = ε / 4 ∧ A.L ∈ geometricGuesses I ε

def geometricGuesses_ordered_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (hε : 0 ≤ ε),
  (geometricGuesses I ε).Pairwise (· ≤ ·)

def outerInputs_ordered_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (hε : 0 ≤ ε),
  (outerInputs I ε).Pairwise (fun A B => A.L ≤ B.L)

def outerInputs_get_length_le_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (hε : 0 ≤ ε)
    (r s : ℕ) (A B : InnerInput) (hr : (outerInputs I ε)[r]? = some A)
    (hs : (outerInputs I ε)[s]? = some B) (hrs : r ≤ s),
  A.L ≤ B.L

def answerDistance_eq_none_iff_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (t : ℕ),
  answerDistance I ε t = none ↔ answerBranch I ε t = .absent

def EncodesOutput.readDistance_eq_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (S : RAMState)
    (h : EncodesOutput I ε S) (t : ℕ) (ht : t < I.graph.n),
  readDistance S t = answerDistance I ε t

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

def outerInputs_length_exact_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1),
  (outerInputs I ε).length = if (positiveLengths I).isEmpty ∨ I.budget = 0 then 0
      else firstCrossing (firstPositiveLength I) (1+ε/4) (I.graph.n * largestLength I)+1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def countCmd_run_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (s : Store) (hs : CountReady I ε s),
  ∃ out steps, Run (encodeInput I ε) countCmd s out steps ∧
      out.nr 132 = (outerInputs I ε).length ∧
      steps ≤ 4*(outerInputs I ε).length+13

def countCmd_nat_frame_contract_statement : Prop :=
  ∀ {input : RAMInput} {s out : Store} {k : ℕ}
    (h : Run input countCmd s out k) (r : ℕ)
    (h70 : r ≠ 70) (h71 : r ≠ 71) (h132 : r ≠ 132),
  out.nr r = s.nr r

def countCmd_real_frame_contract_statement : Prop :=
  ∀ {input : RAMInput} {s out : Store} {k : ℕ}
    (h : Run input countCmd s out k) (r : ℕ) (hr : r < 70 ∨ 74 < r),
  out.rr r = s.rr r

def countCmd_memory_frame_contract_statement : Prop :=
  ∀ {input : RAMInput} {s out : Store} {k : ℕ}
    (h : Run input countCmd s out k),
  out.nm = s.nm ∧ out.rm = s.rm

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission
namespace Preprocess
open Structured

def headerPrepared_values_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (headerPrepared input s).nr 121 = input.naturals 0 ∧
    (headerPrepared input s).nr 122 = input.naturals 1 ∧
    (headerPrepared input s).nr 123 = input.naturals 2 ∧
    (headerPrepared input s).nr 124 = 0 ∧
    (headerPrepared input s).nr 126 = 1 ∧
    (headerPrepared input s).nr 129 = 4 * input.naturals 0 ∧
    (headerPrepared input s).nr 130 = 16 + 4 * input.naturals 0 ∧
    (headerPrepared input s).rr 120 = input.reals 0 ∧
    (headerPrepared input s).rr 121 = input.reals 1 ∧
    (headerPrepared input s).rr 123 = 1 + input.reals 0 / 4 ∧
    (headerPrepared input s).rr 124 = 512 / (input.reals 0 / 4) ^ 2 ∧
    (headerPrepared input s).rr 125 = 1 ∧
    (headerPrepared input s).rr 127 = 0 ∧
    (headerPrepared input s).rr 128 = (1 + input.reals 0 / 8) / (1 + input.reals 0 / 4)

def headerLoopStore_zero_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  headerLoopStore (headerPrepared input s) 0 = headerPrepared input s

def headerBody_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (k : ℕ)
    (hone : s.nr 126 = 1) (hrone : s.rr 125 = 1),
  Run input headerBody (headerLoopStore s k) (headerLoopStore s (k + 1)) 2

def headerLoop_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (x : ℝ)
    (hone : s.nr 126 = 1) (hrone : s.rr 125 = 1) (hx : s.rr 124 = x)
    (k remaining : ℕ) (hcount : k + remaining = Nat.ceil x),
  Run input headerLoop (headerLoopStore s k)
      (headerLoopStore s (Nat.ceil x)) (4 * remaining + 1)

def headerCmd_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  Run input headerCmd s (headerResult input s)
      (37 + 4 * Nat.ceil (512 / (input.reals 0 / 4) ^ 2))

def headerResult_header_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (s : Store),
  (headerResult (encodeInput I ε) s).nm 0 = outerQ ε ∧
    (headerResult (encodeInput I ε) s).nm 1 = I.source ∧
    (headerResult (encodeInput I ε) s).nm 2 = I.graph.n ∧
    (headerResult (encodeInput I ε) s).rm 0 = (1 + ε / 8) / (1 + ε / 4)

def headerResult_memory_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (a : ℕ)
    (h0 : a ≠ 0) (h1 : a ≠ 1) (h2 : a ≠ 2),
  (headerResult input s).nm a = s.nm a ∧ (headerResult input s).rm a = s.rm a

end Preprocess
end NearLinearRSP.TwoResources.Mission
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.NatToReal
open Structured

def run_atoms_contract_statement : Prop :=
  ∀ (input : RAMInput) (as : List Atom) (s : Store),
  Run input (atoms as) s (evalAtoms input as s) as.length

def powerBody_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (k : ℕ),
  Run input powerBody (powerState s k) (powerState s (k+1)) 3

def powerLoop_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (n k d : ℕ)
    (hn : s.nr 66 = n+1) (hlo : 2 ^ (k+d) ≤ n) (hhi : n < 2 ^ (k+d+1)),
  Run input powerLoop (powerState s k) (powerState s (k+d)) (5*d+1)

def convertBody_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (hone : s.nr 65 = 1)
    (hpos : 0 < s.nr 61),
  Run input convertBody s (bodyResult s (Nat.log 2 (s.nr 61)))
      (7 + 5 * Nat.log 2 (s.nr 61))

def Frame.refl_contract_statement : Prop :=
  ∀ (s : Store),
  Frame s s

def Frame.trans_contract_statement : Prop :=
  ∀ {s t u : Store} (h : Frame s t) (h' : Frame t u),
  Frame s u

def bodyResult_frame_contract_statement : Prop :=
  ∀ (s : Store) (k : ℕ),
  Frame s (bodyResult s k)

def convertLoop_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (h : ℕ) (s : Store)
    (hz : s.nr 64 = 0) (hone : s.nr 65 = 1) (hb : s.nr 61 < 2 ^ h),
  ∃ (t : Store) (steps : ℕ), Run input convertLoop s t steps ∧
      t.nr 61 = 0 ∧ t.rr 60 = s.rr 60 + s.nr 61 ∧
      steps ≤ 14 * h ^ 2 + 1 ∧ Frame s t

def convertCmd_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  ∃ (t : Store) (steps : ℕ), Run input convertCmd s t steps ∧
      t.rr 60 = (s.nr 60 : ℝ) ∧
      steps ≤ 14 * (Nat.log 2 (s.nr 60) + 1) ^ 2 + 5 ∧ Frame s t

end NearLinearRSP.TwoResources.Mission.NatToReal
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Scan

def positives_append_contract_statement : Prop :=
  ∀ (xs ys : List (ℝ × ℝ)),
  positives (xs++ys) = positives xs ++ positives ys

def minimum_append_contract_statement : Prop :=
  ∀ (xs : List ℝ) (x : ℝ),
  (xs++[x]).foldl min ((xs++[x]).headD 1) =
      if xs.isEmpty then x else min (xs.foldl min (xs.headD 1)) x

def addSample_summarize_contract_statement : Prop :=
  ∀ (xs : List (ℝ × ℝ)) (x : ℝ × ℝ),
  addSample (summarize xs) x = summarize (xs++[x])

def prefixSummary_succ_contract_statement : Prop :=
  ∀ (input : RAMInput) (k : ℕ),
  prefixSummary input (k+1) = addSample (prefixSummary input k) (sample input k)

def encoded_samples_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ),
  (List.range I.graph.edges.length).map (sample (encodeInput I ε)) = edgeSamples I

def max_fold_filter_positive_contract_statement : Prop :=
  ∀ (xs : List ℝ) (a : ℝ) (ha : 0 ≤ a),
  xs.foldl max a = (xs.filter (0 < ·)).foldl max a

def summarize_edgeSamples_contract_statement : Prop :=
  ∀ (I : Instance),
  (summarize (edgeSamples I)).found = !(positiveLengths I).isEmpty ∧
    (summarize (edgeSamples I)).minimum = firstPositiveLength I ∧
    (summarize (edgeSamples I)).maximum = largestLength I ∧
    (summarize (edgeSamples I)).sumLength =
      (I.graph.edges.map (fun e => (I.length e.1 e.2 : ℝ))).sum ∧
    (summarize (edgeSamples I)).sumCost =
      (I.graph.edges.map (fun e => (I.cost e.1 e.2 : ℝ))).sum

end NearLinearRSP.TwoResources.Mission.Scan
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.Scan
open Structured

def minCmd_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (dst src : ℕ),
  ∃ n ≤ 3, Run input (minCmd dst src) s (minResult s dst src) n

def maxCmd_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (dst src : ℕ),
  ∃ n ≤ 3, Run input (maxCmd dst src) s (maxResult s dst src) n

def positiveCmd_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store)
    (hz : s.nr 153 = 0) (hrz : s.rr 156 = 0),
  ∃ n ≤ 6, Run input positiveCmd s (positiveResult input s) n

def scanBody_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store)
    (hz : s.nr 153 = 0) (hrz : s.rr 156 = 0),
  ∃ n ≤ 16, Run input scanBody s (scanBodyResult input s) n

def scanBody_values_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (hone : s.nr 154 = 1)
    (hflag : s.nr 150 = 0 ∨ s.nr 150 = 1),
  let t := scanBodyResult input s
  let l := input.reals (s.nr 151)
  let c := input.reals (s.nr 151+1)
  t.nr 151 = s.nr 151+2 ∧ t.nr 152 = s.nr 152+1 ∧
  t.nr 150 = (if 0 < l then 1 else s.nr 150) ∧
  t.rr 150 = (if 0 < l then if s.nr 150 = 0 then l else min (s.rr 150) l else s.rr 150) ∧
  t.rr 151 = max (s.rr 151) l ∧ t.rr 152 = s.rr 152+l ∧ t.rr 153 = s.rr 153+c

def scan_init_rep_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  ScanRep input (input.naturals 1) 0 (evalAtoms input scanInitOps s)

def scan_step_rep_contract_statement : Prop :=
  ∀ (input : RAMInput) (m k : ℕ) (s : Store)
    (h : ScanRep input m k s),
  ∃ n ≤ 16, Run input scanBody s (scanBodyResult input s) n ∧
      ScanRep input m (k+1) (scanBodyResult input s)

def scanCmd_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  ∃ out steps, Run input scanCmd s out steps ∧
      ScanRep input (input.naturals 1) (input.naturals 1) out ∧
      steps ≤ 18*input.naturals 1+13 ∧ out.nm = s.nm ∧ out.rm = s.rm

def scan_encoded_correct_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (s : Store),
  ∃ out steps, Run (encodeInput I ε) scanCmd s out steps ∧
      out.rr 150 = firstPositiveLength I ∧ out.rr 151 = largestLength I ∧
      out.rr 152 = (I.graph.edges.map (fun e => (I.length e.1 e.2 : ℝ))).sum ∧
      out.rr 153 = (I.graph.edges.map (fun e => (I.cost e.1 e.2 : ℝ))).sum ∧
      out.nr 150 = (if (positiveLengths I).isEmpty then 0 else 1) ∧
      steps ≤ 20*(I.graph.edges.length+1) ∧ out.nm = s.nm ∧ out.rm = s.rm

end NearLinearRSP.TwoResources.Mission.Scan
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Scan
open Structured

def scan_nat_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s t : Store) (steps r : ℕ)
    (h : Run input scanCmd s t steps) (hr : r < 150 ∨ 159 < r),
  t.nr r = s.nr r

def scan_real_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s t : Store) (steps r : ℕ)
    (h : Run input scanCmd s t steps) (hr : r < 150 ∨ 156 < r),
  t.rr r = s.rr r

end NearLinearRSP.TwoResources.Mission.Scan
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def CoreRegs.transfer_contract_statement : Prop :=
  ∀ {I : Instance} {ε : ℝ} {s t : Store} (h : CoreRegs I ε s)
    (hn : ∀r, 121 ≤ r → r ≤ 130 → t.nr r = s.nr r)
    (hr : ∀r, 121 ≤ r → r ≤ 128 → t.rr r = s.rr r),
  CoreRegs I ε t

def headerResult_core_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (s : Store),
  CoreRegs I ε (headerResult (encodeInput I ε) s)

def scalarCmd_run_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1),
  ∃ out steps, Run (encodeInput I ε) scalarCmd initialStore out steps ∧
      ScalarReady I ε out ∧
      steps ≤ 4*outerQ ε + 14*(Nat.log 2 I.graph.n+1)^2 +
        20*I.graph.edges.length + 4*(outerInputs I ε).length + 80

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission
namespace Address
open Structured

def standalone_Mission_RAMAddress__store_eq_contract_statement : Prop :=
  ∀ (s t : Store) (hnr : s.nr = t.nr)
    (hrr : s.rr = t.rr) (hnm : s.nm = t.nm) (hrm : s.rm = t.rm),
  s = t

def standalone_Mission_RAMAddress__body_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (addr k : ℕ)
    (hone : s.nr 47 = 1),
  Run input addressBody (loopStore s addr (k + 1))
      (loopStore s (addr + s.nr 41) k) 2

def loop_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (addr k : ℕ)
    (hone : s.nr 47 = 1) (hzero : s.nr 48 = 0),
  Run input addressLoop (loopStore s addr k)
      (loopStore s (addr + s.nr 41 * k) 0) (4 * k + 1)

def addressCmd_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  Run input addressCmd s (addressResult s) (8 + 4 * s.nr 42)

def addressResult_value_contract_statement : Prop :=
  ∀ (s : Store),
  (addressResult s).nr 44 = s.nr 40 + s.nr 41 * s.nr 42 + 4 * s.nr 43

def addressResult_frame_contract_statement : Prop :=
  ∀ (s : Store) (r : ℕ)
    (h44 : r ≠ 44) (h45 : r ≠ 45) (h46 : r ≠ 46)
    (h47 : r ≠ 47) (h48 : r ≠ 48),
  (addressResult s).nr r = s.nr r

def addressResult_memory_contract_statement : Prop :=
  ∀ (s : Store),
  (addressResult s).rr = s.rr ∧ (addressResult s).nm = s.nm ∧
      (addressResult s).rm = s.rm

def rectangle_index_lt_contract_statement : Prop :=
  ∀ (q i j : ℕ) (hi : i < q) (hj : j < q),
  i * q + j < q ^ 2

def address_cost_le_rectangle_contract_statement : Prop :=
  ∀ (q i j : ℕ) (hi : i < q) (hj : j < q),
  8 + 4 * (i * q + j) ≤ 8 + 4 * q ^ 2

def tableAddress_stride_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (r v i j : ℕ),
  tableAddress I ε r v i j = tableBase I ε r +
      (4 * I.graph.n) * (i * outerQ ε + j) + 4 * v

def tableAddress_next_cost_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (r v i j : ℕ),
  tableAddress I ε r v i (j + 1) = tableAddress I ε r v i j + 4 * I.graph.n

def tableAddress_next_length_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (r v i j : ℕ),
  tableAddress I ε r v (i + 1) j = tableAddress I ε r v i j +
      4 * I.graph.n * outerQ ε

def tableAddress_change_vertex_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (r v u i j : ℕ),
  tableAddress I ε r v i j - 4 * v + 4 * u = tableAddress I ε r u i j

end Address
end NearLinearRSP.TwoResources.Mission
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def layoutFirst_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input layoutFirst s = layoutFirstResult s

def layoutSecond_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input layoutSecond s = layoutSecondResult s

def layoutThird_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input layoutThird s = layoutThirdResult s

def layoutFinish_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input layoutFinish s = layoutFinishResult s

def layout_counts_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (layoutState1 input s).nr 42 = s.nr 124 ∧
    (layoutState2 input s).nr 42 = s.nr 124 ∧
    (layoutState3 input s).nr 42 = s.nr 132

def layoutCmd_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  Run input layoutCmd s (layoutResult input s)
      (55 + 8 * s.nr 124 + 4 * s.nr 132)

def layoutResult_values_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (layoutResult input s).nr 133 = s.nr 129 * s.nr 124 ^ 2 ∧
    (layoutResult input s).nr 134 = s.nr 130 + s.nr 129 * s.nr 124 ^ 2 * s.nr 132 ∧
    (layoutResult input s).nr 135 = (layoutResult input s).nr 134 ∧
    (layoutResult input s).nr 141 = (layoutResult input s).nr 134 + s.nr 124 + 64 ∧
    (layoutResult input s).nr 137 = (layoutResult input s).nr 141 + s.nr 121 ∧
    (layoutResult input s).nr 142 = (layoutResult input s).nr 141 + 2 * s.nr 121 ∧
    (layoutResult input s).nr 139 = (layoutResult input s).nr 141 + 3 * s.nr 121 ∧
    (layoutResult input s).nm 6 = (layoutResult input s).nr 135 ∧
    (layoutResult input s).nm 7 = (layoutResult input s).nr 141

def layoutResult_headers_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (layoutResult input s).nr 138 = s.nr 129 * s.nr 124 ∧
    (layoutResult input s).nm 4 = s.nr 129 ∧
    (layoutResult input s).nm 5 = s.nr 129 * s.nr 124

def layoutResult_memory_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (a : ℕ)
    (h4 : a ≠ 4) (h5 : a ≠ 5) (h6 : a ≠ 6) (h7 : a ≠ 7),
  (layoutResult input s).nm a = s.nm a ∧ (layoutResult input s).rm a = s.rm a

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def powerCacheBody_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (k : ℕ),
  evalAtoms input powerCacheBodyOps (powerCacheState s k) = powerCacheState s (k+1)

def powerCacheBody_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (k : ℕ),
  Run input (.atoms powerCacheBodyOps) (powerCacheState s k) (powerCacheState s (k+1)) 4

def powerCacheLoop_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (k d : ℕ)
    (he : k+d = s.nr 124),
  Run input powerCacheLoop (powerCacheState s k) (powerCacheState s (k+d)) (6*d+1)

def powerCacheCmd_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  Run input powerCacheCmd s (powerCacheState s (s.nr 124)) (6*s.nr 124+5)

def powerCache_values_contract_statement : Prop :=
  ∀ (s : Store) (a : ℕ) (ha : a < s.nr 124),
  (powerCacheState s (s.nr 124)).rm (s.nr 135+a) = s.rr 128^a

def powerCache_frame_contract_statement : Prop :=
  ∀ (s : Store) (a : ℕ)
    (ha : a < s.nr 135 ∨ s.nr 135+s.nr 124 ≤ a),
  (powerCacheState s (s.nr 124)).rm a = s.rm a

def powerCache_natMemory_contract_statement : Prop :=
  ∀ (s : Store),
  (powerCacheState s (s.nr 124)).nm = s.nm

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Query
open Structured

def prepend_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (hone : s.nr 31 = 1),
  Run input prependCmd s (prependResult s) 3

def storesList_cons_contract_statement : Prop :=
  ∀ (mem : ℕ → ℕ) (base u : ℕ) (xs : List ℕ)
    (hb : 0 < base) (h : StoresList mem base xs),
  StoresList (Function.update mem (base - 1) u) (base - 1) (u :: xs)

def storesList_map_contract_statement : Prop :=
  ∀ (mem : ℕ → ℕ) (base : ℕ) (xs : List ℕ)
    (h : StoresList mem base xs),
  (List.range xs.length).map (fun k => mem (base + k)) = xs

def prepend_stores_contract_statement : Prop :=
  ∀ (s : Store) (xs : List ℕ)
    (hlen : s.nr 2 = xs.length) (hbase : 0 < s.nr 3)
    (hmem : StoresList s.nm (s.nr 3) xs),
  (prependResult s).nr 2 = (s.nr 0 :: xs).length ∧
    StoresList (prependResult s).nm ((prependResult s).nr 3) (s.nr 0 :: xs)

def prepend_memory_frame_contract_statement : Prop :=
  ∀ (s : Store) (a : ℕ) (ha : a < s.nr 3 - 1),
  (prependResult s).nm a = s.nm a

def score_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  Run input scoreCmd s (scoreResult input s) 13

def score_value_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (scoreResult input s).rr 5 =
      (1 - s.rm (s.nr 27)) +
        s.rm (s.nr 21 + s.nr 16) * s.rr 1 / s.rr 3 +
        s.rm (s.nr 21 + s.nr 17) * s.rr 2 / s.rr 4

def score_nat_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (r : ℕ) (h : r ≠ 39),
  (scoreResult input s).nr r = s.nr r

def score_real_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (r : ℕ)
    (h5 : r ≠ 5) (h7 : r ≠ 7) (h8 : r ≠ 8) (h9 : r ≠ 9)
    (h10 : r ≠ 10) (h13 : r ≠ 13) (h14 : r ≠ 14),
  (scoreResult input s).rr r = s.rr r

def score_memory_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (scoreResult input s).nm = s.nm ∧ (scoreResult input s).rm = s.rm

def choose_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  Run input chooseCmd s (chooseResult input s) (chooseCost s)

def choose_cost_le_contract_statement : Prop :=
  ∀ (s : Store),
  chooseCost s ≤ 6

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Query

def header_lt_outputEnd_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (a : ℕ) (ha : a < 16),
  a < outputEnd I ε

def target_lt_outputEnd_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (v off : ℕ)
    (hv : v < I.graph.n) (hoff : off < 4),
  targetAddress v + off < outputEnd I ε

def table_lt_outputEnd_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (r v i j off : ℕ)
    (hr : r < (outerInputs I ε).length) (hv : v < I.graph.n)
    (hi : i < outerQ ε) (hj : j < outerQ ε) (hoff : off < 4),
  tableAddress I ε r v i j + off < outputEnd I ε

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def ScalarReady.numeric_contract_statement : Prop :=
  ∀ {I : Instance} {ε : ℝ} {s : Store}
    (h : ScalarReady I ε s),
  NumericRegs I ε s

def NumericRegs.transfer_contract_statement : Prop :=
  ∀ {I : Instance} {ε : ℝ} {s t : Store} (h : NumericRegs I ε s)
    (hn : ∀r, (121 ≤ r ∧ r ≤ 132) ∨ r = 150 → t.nr r = s.nr r)
    (hr : ∀r, 121 ≤ r → r ≤ 153 → t.rr r = s.rr r),
  NumericRegs I ε t

def layoutResult_numeric_contract_statement : Prop :=
  ∀ {I : Instance} {ε : ℝ} {s : Store} (h : NumericRegs I ε s),
  NumericRegs I ε (layoutResult (encodeInput I ε) s)

def layoutResult_layout_contract_statement : Prop :=
  ∀ {I : Instance} {ε : ℝ} {s : Store} (h : NumericRegs I ε s),
  LayoutRegs I ε (layoutResult (encodeInput I ε) s)

def layoutCacheCmd_run_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (s : Store) (hs : ScalarReady I ε s),
  ∃ out steps, Run (encodeInput I ε) layoutCacheCmd s out steps ∧
      LayoutReady I ε out ∧ steps = 60+14*outerQ ε+4*(outerInputs I ε).length

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def activeStep_register_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (r : ℕ)
    (h140 : r ≠ 140) (h143 : r ≠ 143) (h144 : r ≠ 144)
    (h145 : r ≠ 145) (h146 : r ≠ 146) (h147 : r ≠ 147),
  (activeStep input s).nr r = s.nr r

def activeStep_pointer_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (activeStep input s).nr 147 = s.nr 147 + 1

def activeScanBody_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store)
    (hz : s.nr 125 = 0) (hone : s.nr 126 = 1),
  ∃ steps ≤ 10, Run input activeScanBody s (activeStep input s) steps

def activeScan_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (remaining : ℕ) (s : Store)
    (hz : s.nr 125 = 0) (hone : s.nr 126 = 1)
    (hend : s.nr 147 + remaining = s.nr 148),
  ∃ steps ≤ 12 * remaining + 1,
      Run input activeScan s (activeScanResult input remaining s) steps

def ActiveRep.loaded_contract_statement : Prop :=
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (input : RAMInput),
  ActiveRep n base array xs (activeLoaded input s)

def ActiveRep.step_contract_statement : Prop :=
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (input : RAMInput)
    (hv : input.naturals (s.nr 147) < n) (hone : s.nr 126 = 1),
  ActiveRep n base array (stableInsert xs (input.naturals (s.nr 147))) (activeStep input s)

def activeScan_rep_contract_statement : Prop :=
  ∀ (input : RAMInput) (remaining : ℕ) (s : Store)
    (n base array : ℕ) (xs : List ℕ) (h : ActiveRep n base array xs s)
    (hone : s.nr 126 = 1)
    (hv : ∀ v ∈ scannedVertices input (s.nr 147) remaining, v < n),
  ActiveRep n base array
      ((scannedVertices input (s.nr 147) remaining).foldl stableInsert xs)
      (activeScanResult input remaining s)

def scannedVertices_pairs_contract_statement : Prop :=
  ∀ (input : RAMInput) (start : ℕ) (edges : List (ℕ × ℕ))
    (hinput : ∀ k e, edges[k]? = some e →
      input.naturals (start + 2 * k) = e.1 ∧ input.naturals (start + 2 * k + 1) = e.2),
  scannedVertices input start (2 * edges.length) = edges.flatMap (fun e => [e.1,e.2])

def encoded_scannedVertices_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ),
  scannedVertices (encodeInput I ε) 3 (2 * I.graph.edges.length) =
      I.graph.edges.flatMap (fun e => [e.1,e.2])

def activeInitAtoms_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input activeInitAtoms s = activeInitPrepared s

def activeInit_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store)
    (hz : s.nr 125 = 0) (hone : s.nr 126 = 1),
  ∃ steps ≤ 24 * s.nr 122 + 14,
      Run input activeInit s (activeInitResult input s) steps

def activeInit_rep_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (s : Store) (base array : ℕ)
    (hm : s.nr 122 = I.graph.edges.length) (hsource : s.nr 123 = I.source)
    (hbase : s.nr 141 = base) (harray : s.nr 142 = array)
    (hsep : base + I.graph.n ≤ array) (hone : s.nr 126 = 1)
    (hzero : ∀ v < I.graph.n, s.nm (base + v) = 0),
  ActiveRep I.graph.n base array (activeVertices I)
      (activeInitResult (encodeInput I ε) s)

def ActiveRep.insert_memory_frame_contract_statement : Prop :=
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (hv : s.nr 140 < n) (hone : s.nr 126 = 1)
    (a : ℕ) (hb : a < base ∨ base + n ≤ a) (ha : a < array ∨ array + n ≤ a),
  (activeResult s).nm a = s.nm a

def activeScan_memory_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (remaining : ℕ) (s : Store)
    (n base array : ℕ) (xs : List ℕ) (h : ActiveRep n base array xs s)
    (hone : s.nr 126 = 1)
    (hv : ∀ v ∈ scannedVertices input (s.nr 147) remaining, v < n)
    (a : ℕ) (hb : a < base ∨ base + n ≤ a) (ha : a < array ∨ array + n ≤ a),
  (activeScanResult input remaining s).nm a = s.nm a

def activeInit_memory_frame_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (s : Store) (base array : ℕ)
    (hm : s.nr 122 = I.graph.edges.length) (hsource : s.nr 123 = I.source)
    (hbase : s.nr 141 = base) (harray : s.nr 142 = array)
    (hsep : base + I.graph.n ≤ array) (hone : s.nr 126 = 1)
    (hzero : ∀ v < I.graph.n, s.nm (base + v) = 0)
    (a : ℕ) (hb : a < base ∨ base + I.graph.n ≤ a)
    (ha : a < array ∨ array + I.graph.n ≤ a),
  (activeInitResult (encodeInput I ε) s).nm a = s.nm a

def activeInit_register_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store)
    (hz : s.nr 125 = 0) (hone : s.nr 126 = 1) (r : ℕ)
    (hr : r ∉ ({140, 143, 144, 145, 146, 147, 148} : Finset ℕ)),
  (activeInitResult input s).nr r = s.nr r

def activeInit_real_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store)
    (hz : s.nr 125 = 0) (hone : s.nr 126 = 1),
  (activeInitResult input s).rr = s.rr ∧ (activeInitResult input s).rm = s.rm

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def LayoutRegs.transfer_contract_statement : Prop :=
  ∀ {I : Instance} {ε : ℝ} {s t : Store} (h : LayoutRegs I ε s)
    (hn : ∀r, r ∈ ({133,134,135,137,138,139,141,142} : Finset ℕ) → t.nr r=s.nr r),
  LayoutRegs I ε t

def OutputHeaders.transfer_contract_statement : Prop :=
  ∀ {I : Instance} {ε : ℝ} {s t : Store} (h : OutputHeaders I ε s)
    (hn : ∀a, a<8 → a≠3 → t.nm a=s.nm a) (hr : t.rm 0=s.rm 0),
  OutputHeaders I ε t

def graphCmd_run_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (s : Store) (hs : LayoutReady I ε s),
  ∃ out steps, Run (encodeInput I ε) graphCmd s out steps ∧
      GraphReady I ε out ∧ steps ≤ 35*I.graph.edges.length+21

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Queue
open Structured

def capacityStart_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  capacityStart.eval input s = capacityState s 0

def capacityDouble_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (k : ℕ),
  capacityDouble.eval input (capacityState s k) = capacityState s (k + 1)

def chooseCapacity_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  ∃ k ≤ 3 * Nat.clog 2 (s.nr 10) + 2,
      Run input chooseCapacity s (capacityState s (Nat.clog 2 (s.nr 10))) k

def chooseCapacity_bounds_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (hn : 0 < s.nr 10),
  ∃ out k, Run input chooseCapacity s out k ∧ k ≤ 3 * Nat.clog 2 (s.nr 10) + 2 ∧
      s.nr 10 ≤ out.nr 11 ∧ out.nr 11 < 2 * s.nr 10 ∧
      out.nm = s.nm ∧ out.rm = s.rm ∧ out.rr = s.rr ∧
      ∀ a, a ≠ 11 → out.nr a = s.nr a

def chooseCapacity_exact_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  ∃ out k, Run input chooseCapacity s out k ∧ k ≤ 3 * Nat.clog 2 (s.nr 10) + 2 ∧
      out.nr 11 = 2 ^ Nat.clog 2 (s.nr 10) ∧
      out.nm = s.nm ∧ out.rm = s.rm ∧ out.rr = s.rr ∧
      ∀ a, a ≠ 11 → out.nr a = s.nr a

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def GraphReady.transfer_contract_statement : Prop :=
  ∀ {I : Instance} {ε : ℝ} {s t : Store} (h : GraphReady I ε s)
    (hn : ∀r, 121≤r → r≤153 → t.nr r=s.nr r)
    (hr : ∀r, 121≤r → r≤153 → t.rr r=s.rr r)
    (hm : t.nm=s.nm) (hrm : t.rm=s.rm),
  GraphReady I ε t

def heapCmd_run_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (s : Store) (hs : GraphReady I ε s),
  ∃ out steps, Run (encodeInput I ε) heapCmd s out steps ∧ SetupReady I ε out ∧
      steps≤3*Nat.clog 2 (activeVertices I).length+21

def setupCmd_run_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (hε : 0<ε) (hε1 : ε<1),
  ∃ out steps, Run (encodeInput I ε) setupCmd initialStore out steps ∧ SetupReady I ε out ∧
      steps≤18*outerQ ε+14*(Nat.log 2 I.graph.n+1)^2+55*I.graph.edges.length+
        8*(outerInputs I ε).length+3*Nat.clog 2 (activeVertices I).length+182

def SetupReady.capacity_bounds_contract_statement : Prop :=
  ∀ {I : Instance} {ε : ℝ} {s : Store} (h : SetupReady I ε s),
  (activeVertices I).length ≤ s.nr 11 ∧ s.nr 11 < 2*(activeVertices I).length

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def GraphReady.runtime_contract_statement : Prop :=
  ∀ {I : Instance} {ε : ℝ} {s : Store} (h : GraphReady I ε s),
  RuntimeReady I ε s

def SetupReady.runtime_contract_statement : Prop :=
  ∀ {I : Instance} {ε : ℝ} {s : Store} (h : SetupReady I ε s),
  RuntimeReady I ε s

def RuntimeReady.transfer_contract_statement : Prop :=
  ∀ {I : Instance} {ε : ℝ} {s t : Store} (h : RuntimeReady I ε s)
    (hn : ∀r, 121≤r → r≤153 → t.nr r=s.nr r)
    (hr : ∀r, 121≤r → r≤153 → t.rr r=s.rr r)
    (hhead : ∀a, a<8 → t.nm a=s.nm a)
    (hgraph : ∀a, graphBase I ε≤a → a<linksBase I ε+I.graph.edges.length → t.nm a=s.nm a)
    (hz : t.rm 0=s.rm 0)
    (hcache : ∀a<outerQ ε, t.rm (Query.outputEnd I ε+a)=s.rm (Query.outputEnd I ε+a)),
  RuntimeReady I ε t

def SetupReady.costSentinel_mode_contract_statement : Prop :=
  ∀ {I : Instance} {ε : ℝ} {s : Store}
    (h : SetupReady I ε s),
  s.rr 280=TreeMode.zeroLength.top I

def SetupReady.lengthSentinel_mode_contract_statement : Prop :=
  ∀ {I : Instance} {ε : ℝ} {s : Store}
    (h : SetupReady I ε s),
  s.rr 281=TreeMode.zeroBudget.top I

def RuntimeReady.treeActive_contract_statement : Prop :=
  ∀ {I : Instance} {ε : ℝ} {s : Store}
    (h : RuntimeReady I ε s),
  ActiveRep I.graph.n (treeAllocation I ε).map (treeAllocation I ε).array (activeVertices I) s

def RuntimeReady.treeAdjacency_contract_statement : Prop :=
  ∀ {I : Instance} {ε : ℝ} {s : Store}
    (h : RuntimeReady I ε s),
  AdjacencyPrefix I I.graph.edges.length (treeAllocation I ε).heads
      (treeAllocation I ε).links s.nm

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Structured

def run_acyclic_contract_statement : Prop :=
  ∀ (input : RAMInput) (c : Cmd) (h : c.acyclic = true) (s : Store),
  ∃ n ≤ c.size, Run input c s (c.evalAcyclic input s) n

def Cmd.atoms_evalAcyclic_contract_statement : Prop :=
  ∀ (input : RAMInput) (as : List Atom) (s : Store),
  (Cmd.atoms as).evalAcyclic input s = evalAtoms input as s

def Cmd.atoms_acyclic_contract_statement : Prop :=
  ∀ (as : List Atom),
  (Cmd.atoms as).acyclic = true

end NearLinearRSP.TwoResources.Mission.Structured
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources
attribute [local instance] Classical.propDecidable

def markAccepted_fold_contract_statement : Prop :=
  ∀ (p : ℕ → Bool) (xs : List ℕ) (b : AnswerBranch),
  xs.foldl (markAccepted p) b =
      if b = .absent then branchFromIndex (xs.find? p) else b

def acceptedIndex_zero_budget_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (t : ℕ)
    (hC : I.budget = 0),
  acceptedIndex I ε t = none

def acceptedIndex_zero_accuracy_contract_statement : Prop :=
  ∀ (I : Instance) (t : ℕ),
  acceptedIndex I 0 t = none

def answerBranch_seed_find_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (t : ℕ),
  answerBranch I ε t =
      if answerBranch I 0 t = .absent then branchFromIndex (acceptedIndex I ε t)
      else answerBranch I 0 t

def answerBranch_incremental_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (t : ℕ),
  (List.range (outerInputs I ε).length).foldl
      (markAccepted (fun r => ((outerInputs I ε)[r]?).any (fun A => decide (accepted A t))))
      (answerBranch I 0 t) = answerBranch I ε t

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured

def seedCmd_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  ∃ n ≤ 40, Run input seedCmd s (seedResult input s) n

def seedResult_values_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (seedResult input s).nm (s.nr 300) = seedTag s ∧
    (seedTag s = 1 → (seedResult input s).rm (s.nr 300) = 0) ∧
    (seedTag s = 2 → (seedResult input s).rm (s.nr 300) = s.rr 301) ∧
    (∀ a, a ≠ s.nr 300 → (seedResult input s).nm a = s.nm a ∧
      (seedResult input s).rm a = s.rm a)

def markCmd_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  ∃ n ≤ 15, Run input markCmd s (markResult input s) n

def markResult_values_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (markResult input s).nm (s.nr 300) =
      (if s.nm (s.nr 300) = 0 ∧ (3/4 : ℝ) ≤ s.rr 305 then 3 else s.nm (s.nr 300)) ∧
    (s.nm (s.nr 300) = 0 → (3/4 : ℝ) ≤ s.rr 305 →
      (markResult input s).nm (s.nr 300+1) = s.nr 301 ∧
      (markResult input s).rm (s.nr 300) = s.rr 304) ∧
    (∀ a, a ≠ s.nr 300 → a ≠ s.nr 300+1 →
      (markResult input s).nm a = s.nm a) ∧
    (∀ a, a ≠ s.nr 300 → (markResult input s).rm a = s.rm a)

def markResult_unchanged_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store)
    (h : s.nm (s.nr 300) ≠ 0 ∨ s.rr 305 < (3/4 : ℝ)),
  (markResult input s).nm = s.nm ∧ (markResult input s).rm = s.rm

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured

def LabelRep.finite_iff_contract_statement : Prop :=
  ∀ {d : Option ℝ} {sentinel value : ℝ}
    (h : LabelRep d sentinel value),
  value < sentinel ↔ d.isSome = true

def seedTag_correct_contract_statement : Prop :=
  ∀ (I : Instance) (v : ℕ) (s : Store)
    (hv : s.nr 307 = v) (hsource : s.nr 123 = I.source)
    (hbudget : s.rr 121 = I.budget)
    (hL : LabelRep (zeroLengthTree I v).distance (s.rr 280) (s.rr 300))
    (hC : LabelRep (zeroBudgetTree I v).distance (s.rr 281) (s.rr 301)),
  seedTag s = branchTag (answerBranch I 0 v)

def seedResult_correct_contract_statement : Prop :=
  ∀ (input : RAMInput) (I : Instance) (v : ℕ) (s : Store)
    (hv : s.nr 307 = v) (hsource : s.nr 123 = I.source)
    (hbudget : s.rr 121 = I.budget)
    (hL : LabelRep (zeroLengthTree I v).distance (s.rr 280) (s.rr 300))
    (hC : LabelRep (zeroBudgetTree I v).distance (s.rr 281) (s.rr 301)),
  (seedResult input s).nm (s.nr 300) = branchTag (answerBranch I 0 v) ∧
    (∀ d, answerDistance I 0 v = some d → (seedResult input s).rm (s.nr 300) = d)

def mark_acceptance_contract_statement : Prop :=
  ∀ (A : InnerInput) (v : ℕ) (s : Store)
    (h : s.rr 305 = 1 - dpValue A (buildTable A) v 0 0),
  (3/4 : ℝ) ≤ s.rr 305 ↔ accepted A v

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured
attribute [local instance] Classical.propDecidable

def selectedDistance_answer_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (v : ℕ),
  selectedDistance I ε v (answerBranch I ε v) = answerDistance I ε v

def selectedDistance_seed_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (v : ℕ),
  selectedDistance I ε v (answerBranch I 0 v) = answerDistance I 0 v

def seed_record_contract_statement : Prop :=
  ∀ (input : RAMInput) (I : Instance) (ε : ℝ) (v : ℕ) (s : Store)
    (hv : s.nr 307 = v) (ha : s.nr 300 = targetAddress v)
    (hsource : s.nr 123 = I.source) (hbudget : s.rr 121 = I.budget)
    (hL : LabelRep (zeroLengthTree I v).distance (s.rr 280) (s.rr 300))
    (hC : LabelRep (zeroBudgetTree I v).distance (s.rr 281) (s.rr 301)),
  RecordRep I ε v (answerBranch I 0 v) (seedResult input s)

def mark_record_contract_statement : Prop :=
  ∀ (input : RAMInput) (I : Instance) (ε : ℝ) (v r : ℕ)
    (A : InnerInput) (b : AnswerBranch) (s : Store)
    (hrec : RecordRep I ε v b s)
    (ha : s.nr 300 = targetAddress v) (hbase : s.nr 301 = tableBase I ε r)
    (hd : s.rr 304 = (1+A.δ)*A.L)
    (hsuccess : (3/4 : ℝ) ≤ s.rr 305 ↔ accepted A v)
    (hA : (outerInputs I ε)[r]? = some A),
  RecordRep I ε v
      (markAccepted (fun j => ((outerInputs I ε)[j]?).any (fun B => decide (accepted B v))) b r)
      (markResult input s)

def branchesAfter_zero_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (v : ℕ),
  branchesAfter I ε 0 v = answerBranch I 0 v

def branchesAfter_succ_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (k v : ℕ),
  branchesAfter I ε (k+1) v =
      markAccepted (fun r => ((outerInputs I ε)[r]?).any (fun A => decide (accepted A v)))
        (branchesAfter I ε k v) k

def branchesAfter_end_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (v : ℕ),
  branchesAfter I ε (outerInputs I ε).length v = answerBranch I ε v

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured
attribute [local instance] Classical.propDecidable

def seedVisitor_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  ∃ n ≤ 46, Run input seedVisitor s (seedVisitorResult input s) n

def seedVisitor_correct_contract_statement : Prop :=
  ∀ (input : RAMInput) (I : Instance) (ε : ℝ) (v : ℕ) (s : Store)
    (hv : s.nr 307 = v) (ha : s.nr 300 = targetAddress v)
    (hsource : s.nr 123 = I.source) (hbudget : s.rr 121 = I.budget)
    (hL : LabelRep (zeroLengthTree I v).distance (s.rr 280) (s.rm (targetAddress v+2)))
    (hC : LabelRep (zeroBudgetTree I v).distance (s.rr 281) (s.rm (targetAddress v+3))),
  RecordRep I ε v (answerBranch I 0 v) (seedVisitorResult input s)

def seedVisitor_memory_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (a : ℕ)
    (ha : a ≠ s.nr 300),
  (seedVisitorResult input s).nm a = s.nm a ∧
    (seedVisitorResult input s).rm a = s.rm a

def markVisitor_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  ∃ n ≤ 19, Run input markVisitor s (markVisitorResult input s) n

def markVisitor_correct_contract_statement : Prop :=
  ∀ (input : RAMInput) (I : Instance) (ε : ℝ) (v r : ℕ)
    (A : InnerInput) (b : AnswerBranch) (s : Store)
    (hrec : RecordRep I ε v b s) (hv : s.nr 307 = v)
    (ha : s.nr 300 = targetAddress v) (hbase : s.nr 301 = tableBase I ε r)
    (hd : s.rr 304 = (1+A.δ)*A.L)
    (hmass : s.rm (tableBase I ε r+4*v) = 1-dpValue A (buildTable A) v 0 0)
    (hA : (outerInputs I ε)[r]? = some A),
  RecordRep I ε v
      (markAccepted (fun j => ((outerInputs I ε)[j]?).any (fun B => decide (accepted B v))) b r)
      (markVisitorResult input s)

def markVisitor_memory_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (a : ℕ)
    (ha : a ≠ s.nr 300) (ha1 : a ≠ s.nr 300+1),
  (markVisitorResult input s).nm a = s.nm a ∧
    (markVisitorResult input s).rm a = s.rm a

def RecordRep.memory_congr_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (v : ℕ) (b : AnswerBranch)
    (s t : Store) (htag : t.nm (targetAddress v) = s.nm (targetAddress v))
    (hbase : t.nm (targetAddress v+1) = s.nm (targetAddress v+1))
    (hd : t.rm (targetAddress v) = s.rm (targetAddress v))
    (h : RecordRep I ε v b s),
  RecordRep I ε v b t

def target_record_separate_contract_statement : Prop :=
  ∀ (v w a b : ℕ) (hvw : v ≠ w) (ha : a < 4) (hb : b < 4),
  targetAddress v+a ≠ targetAddress w+b

def seedVisitor_nat_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (r : ℕ)
    (hr : r ∉ [302,304,308,309]),
  (seedVisitorResult input s).nr r = s.nr r

def seedVisitor_real_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (r : ℕ)
    (hr : r ∉ [300,301,302]),
  (seedVisitorResult input s).rr r = s.rr r

def markVisitor_nat_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (r : ℕ)
    (hr : r ∉ [302,303,304,306,308,309]),
  (markVisitorResult input s).nr r = s.nr r

def markVisitor_real_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store) (r : ℕ)
    (hr : r ∉ [303,305,306]),
  (markVisitorResult input s).rr r = s.rr r

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.ActiveIterator
open Structured

def setup_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input setupAtoms s=setup s

def prepared_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input prepareAtoms s=prepared s

def advanced_eval_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  incrementAtom.eval input s=advanced s

def setup_state_contract_statement : Prop :=
  ∀ (array : ℕ) (xs : List ℕ) (s : Store)
    (ha : s.nr 142=array) (hn : s.nr 143=xs.length)
    (hmem : ∀ j (hj : j < xs.length),s.nm (array+j)=xs[j]'hj),
  State array xs 0 (setup s)

def prepared_state_contract_statement : Prop :=
  ∀ (array : ℕ) (xs : List ℕ) (k : ℕ) (s : Store)
    (h : State array xs k s),
  State array xs k (prepared s)

def prepared_values_contract_statement : Prop :=
  ∀ (array : ℕ) (xs : List ℕ) (k : ℕ) (s : Store)
    (h : State array xs k s) (hk : k<xs.length),
  (prepared s).nr 307=xs[k] ∧ (prepared s).nr 300=16+4*xs[k]

def advanced_state_contract_statement : Prop :=
  ∀ (array : ℕ) (xs : List ℕ) (k : ℕ) (s out : Store)
    (h : State array xs k s) (hf : Frame array xs s out),
  State array xs (k+1) (advanced out)

def command_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (visitor : Cmd) (array : ℕ) (xs : List ℕ)
    (bound : ℕ) (P : ℕ → Store → Prop) (s : Store)
    (ha : s.nr 142=array) (hn : s.nr 143=xs.length)
    (hmem : ∀ j (hj : j < xs.length),s.nm (array+j)=xs[j]'hj)
    (hstart : P 0 (setup s))
    (hvisit : ∀ k t, k<xs.length → State array xs k t → P k t →
      ∃ out cost, Run input visitor (prepared t) out cost ∧ cost≤bound ∧
        Frame array xs (prepared t) out ∧ P (k+1) (advanced out)),
  ∃ out cost, Run input (command visitor) s out cost ∧
      State array xs xs.length out ∧ P xs.length out ∧
      cost≤(bound+8)*xs.length+4

def prefixFold_succ_contract_statement : Prop :=
  ∀ {α : Type} (step : α→ℕ→α) (initial : α)
    (xs : List ℕ) (k : ℕ) (hk : k<xs.length),
  prefixFold step initial xs (k+1)=step (prefixFold step initial xs k) xs[k]

def command_fold_contract_statement : Prop :=
  ∀ {α : Type} (input : RAMInput) (visitor : Cmd) (array : ℕ)
    (xs : List ℕ) (bound : ℕ) (step : α→ℕ→α) (initial : α)
    (Rep : α→Store→Prop) (s : Store)
    (ha : s.nr 142=array) (hn : s.nr 143=xs.length)
    (hmem : ∀ j (hj : j < xs.length),s.nm (array+j)=xs[j]'hj)
    (hstart : Rep initial (setup s))
    (hvisit : ∀ k t (hk : k<xs.length), State array xs k t →
      Rep (prefixFold step initial xs k) t →
      ∃ out cost, Run input visitor (prepared t) out cost ∧ cost≤bound ∧
        Frame array xs (prepared t) out ∧
        Rep (step (prefixFold step initial xs k) xs[k]) (advanced out)),
  ∃ out cost, Run input (command visitor) s out cost ∧
      State array xs xs.length out ∧ Rep (xs.foldl step initial) out ∧
      cost≤(bound+8)*xs.length+4

def command_nat_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (visitor : Cmd) (s out : Store) (cost r : ℕ)
    (h : Run input (command visitor) s out cost)
    (hv : r∉visitor.natWrites)
    (hr : r∉[300,307,320,321,322,323,324,325]),
  out.nr r=s.nr r

def command_real_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (visitor : Cmd) (s out : Store) (cost r : ℕ)
    (h : Run input (command visitor) s out cost)
    (hv : r∉visitor.realWrites),
  out.rr r=s.rr r

end NearLinearRSP.TwoResources.Mission.ActiveIterator
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

def standalone_Mission_QueueSource__fold_keeps_contract_statement : Prop :=
  ∀ {α β : Type u_1} (f : β → α → β) (Inv : β → Prop)
    (xs : List α) (s : β) (hs : Inv s) (hstep : ∀ s a, Inv s → Inv (f s a)),
  Inv (xs.foldl f s)

def standalone_Mission_QueueSource__fold_sets_contract_statement : Prop :=
  ∀ {α β : Type u_1} (f : β → α → β) (Inv P : β → Prop)
    (xs : List α) (a : α) (ha : a ∈ xs) (s : β) (hs : Inv s)
    (hInv : ∀ s b, Inv s → Inv (f s b))
    (hset : ∀ s, Inv s → P (f s a))
    (hkeep : ∀ s b, Inv s → P s → P (f s b)),
  P (xs.foldl f s)

def buildRow_range_contract_statement : Prop :=
  ∀ (A : InnerInput) (T : Table) (i : ℕ) (hT : TableRange T),
  TableRange (buildRow A T i)

def buildRow_other_row_contract_statement : Prop :=
  ∀ (A : InnerInput) (T : Table) (i v a b : ℕ)
    (h : a ≠ i),
  buildRow A T i v a b = T v a b

def buildRow_source_zero_contract_statement : Prop :=
  ∀ (A : InnerInput) (T : Table) (i j : ℕ)
    (hj : j < tickLimit A) (hT : TableRange T),
  (buildRow A T i A.I.source i j).value = 0

def buildTable_source_value_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j : ℕ)
    (hi : i < tickLimit A) (hj : j < tickLimit A),
  (buildTable A A.I.source i j).value = 0

def dpValue_buildTable_source_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j : ℕ)
    (hi : i < tickLimit A) (hj : j < tickLimit A),
  dpValue A (buildTable A) A.I.source i j = 0

def popLayer_inactive_frame_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hsub : S.queue ⊆ activeVertices A.I) (v a b : ℕ) (hv : v ∉ activeVertices A.I),
  (popLayer A i j S).table v a b = S.table v a b

def queueRun_inactive_frame_contract_statement : Prop :=
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hsub : S.queue ⊆ activeVertices A.I) (v a b : ℕ) (hv : v ∉ activeVertices A.I),
  (queueRun A i j n S).table v a b = S.table v a b

def buildLayer_inactive_frame_contract_statement : Prop :=
  ∀ (A : InnerInput) (T : Table) (i j v a b : ℕ)
    (hv : v ∉ activeVertices A.I),
  buildLayer A T i j v a b = T v a b

def standalone_Mission_QueueInactive__fold_const_contract_statement : Prop :=
  ∀ {α β γ : Type u_1} (f : β → α → β) (p : β → γ)
    (xs : List α) (s : β) (h : ∀ s a, p (f s a) = p s),
  p (xs.foldl f s) = p s

def buildRow_inactive_frame_contract_statement : Prop :=
  ∀ (A : InnerInput) (T : Table) (i v a b : ℕ)
    (hv : v ∉ activeVertices A.I),
  buildRow A T i v a b = T v a b

def buildTable_inactive_contract_statement : Prop :=
  ∀ (A : InnerInput) (v i j : ℕ) (hv : v ∉ activeVertices A.I),
  buildTable A v i j = ⟨1, .lengthTick, 0⟩

def dpValue_buildTable_inactive_contract_statement : Prop :=
  ∀ (A : InnerInput) (v i j : ℕ)
    (hv : v ∉ activeVertices A.I),
  dpValue A (buildTable A) v i j = 1

def accepted_active_contract_statement : Prop :=
  ∀ (A : InnerInput) (v : ℕ) (h : accepted A v),
  v ∈ activeVertices A.I

def shortestTree_finite_active_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (v : ℕ) (d : ℝ)
    (hd : (shortestTree I allow w v).distance = some d),
  v ∈ activeVertices I

def shortestTree_inactive_distance_contract_statement : Prop :=
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (v : ℕ) (hv : v ∉ activeVertices I),
  (shortestTree I allow w v).distance = none

def answerBranch_active_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (t : ℕ)
    (h : answerBranch I ε t ≠ .absent),
  t ∈ activeVertices I

def answerBranch_inactive_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (t : ℕ)
    (ht : t ∉ activeVertices I),
  answerBranch I ε t = .absent

def answerDistance_inactive_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (t : ℕ)
    (ht : t ∉ activeVertices I),
  answerDistance I ε t = none

def answerPath_inactive_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (t : ℕ)
    (ht : t ∉ activeVertices I),
  answerPath I ε t = none

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured
attribute [local instance] Classical.propDecidable

def TargetFrame.refl_contract_statement : Prop :=
  ∀ (I : Instance) (s : Store),
  TargetFrame I s s

def TargetFrame.trans_contract_statement : Prop :=
  ∀ {I : Instance} {s t u : Store}
    (h : TargetFrame I s t) (h' : TargetFrame I t u),
  TargetFrame I s u

def TargetFrame.outside_contract_statement : Prop :=
  ∀ {I : Instance} {s t : Store} (h : TargetFrame I s t)
    (a : ℕ) (ha : a < 16 ∨ 16+4*I.graph.n ≤ a),
  t.nm a = s.nm a ∧ t.rm a = s.rm a

def TargetFrame.treeParents_contract_statement : Prop :=
  ∀ {I : Instance} {s t : Store} (h : TargetFrame I s t)
    (v : ℕ),
  t.nm (targetAddress v+2) = s.nm (targetAddress v+2) ∧
      t.nm (targetAddress v+3) = s.nm (targetAddress v+3)

def seedVisitor_targetFrame_contract_statement : Prop :=
  ∀ (input : RAMInput) (I : Instance) (s : Store) (v : ℕ)
    (hv : v < I.graph.n) (ha : s.nr 300 = targetAddress v),
  TargetFrame I s (seedVisitorResult input s)

def markVisitor_targetFrame_contract_statement : Prop :=
  ∀ (input : RAMInput) (I : Instance) (s : Store) (v : ℕ)
    (hv : v < I.graph.n) (ha : s.nr 300 = targetAddress v),
  TargetFrame I s (markVisitorResult input s)

def setAnswer_fold_apply_contract_statement : Prop :=
  ∀ (xs : List ℕ) (f value : ℕ → AnswerBranch) (v : ℕ),
  (xs.foldl (setAnswer value) f) v = if v ∈ xs then value v else f v

def updateAnswer_fold_apply_contract_statement : Prop :=
  ∀ (xs : List ℕ) (hxs : xs.Nodup)
    (f : ℕ → AnswerBranch) (change : ℕ → AnswerBranch → AnswerBranch) (v : ℕ),
  (xs.foldl (updateAnswer change) f) v = if v ∈ xs then change v (f v) else f v

def RecordMap.initial_absent_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (s : Store)
    (h : ∀ v < I.graph.n, s.nm (targetAddress v) = 0),
  RecordMap I ε (fun _ => .absent) s

def RecordMap.seed_step_contract_statement : Prop :=
  ∀ (input : RAMInput) (I : Instance) (ε : ℝ) (f : ℕ → AnswerBranch)
    (v : ℕ) (s : Store) (ha : s.nr 300 = targetAddress v)
    (h : RecordMap I ε f s)
    (hnew : RecordRep I ε v (answerBranch I 0 v) (seedVisitorResult input s)),
  RecordMap I ε (setAnswer (answerBranch I 0) f v) (seedVisitorResult input s)

def RecordMap.mark_step_contract_statement : Prop :=
  ∀ (input : RAMInput) (I : Instance) (ε : ℝ) (f : ℕ → AnswerBranch)
    (v : ℕ) (change : ℕ → AnswerBranch → AnswerBranch) (s : Store)
    (ha : s.nr 300 = targetAddress v) (h : RecordMap I ε f s)
    (hnew : RecordRep I ε v (change v (f v)) (markVisitorResult input s)),
  RecordMap I ε (updateAnswer change f v) (markVisitorResult input s)

def seed_fold_exact_contract_statement : Prop :=
  ∀ (I : Instance) (v : ℕ),
  ((activeVertices I).foldl (setAnswer (answerBranch I 0)) (fun _ => .absent)) v =
      answerBranch I 0 v

def mark_fold_exact_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (r v : ℕ),
  ((activeVertices I).foldl
      (updateAnswer (fun w b => markAccepted
        (fun j => ((outerInputs I ε)[j]?).any (fun A => decide (accepted A w))) b r))
      (branchesAfter I ε r)) v = branchesAfter I ε (r+1) v

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured

def seedVisitor_world_contract_statement : Prop :=
  ∀ (input : RAMInput) (I : Instance) (s : Store) (v : ℕ)
    (ha : s.nr 300 = targetAddress v) (h : SeedWorld I s),
  SeedWorld I (seedVisitorResult input s)

def seedVisitor_iteratorFrame_contract_statement : Prop :=
  ∀ (input : RAMInput) (I : Instance) (array : ℕ) (s : Store)
    (v : ℕ) (hv : v < I.graph.n) (ha : s.nr 300 = targetAddress v)
    (hspace : 16+4*I.graph.n ≤ array),
  ActiveIterator.Frame array (activeVertices I) s (seedVisitorResult input s)

def seedRecords_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (I : Instance) (ε : ℝ) (array : ℕ) (s : Store)
    (hworld : SeedWorld I s)
    (ha : s.nr 142 = array) (hn : s.nr 143 = (activeVertices I).length)
    (hmem : ∀ k (hk : k < (activeVertices I).length), s.nm (array+k) = (activeVertices I)[k])
    (hspace : 16+4*I.graph.n ≤ array)
    (hzero : ∀ v < I.graph.n, s.nm (targetAddress v) = 0),
  ∃ out cost, Run input seedRecordsCmd s out cost ∧
      SeedWorld I out ∧ RecordMap I ε (answerBranch I 0) out ∧
      TargetFrame I s out ∧ cost ≤ 54*(activeVertices I).length+4

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def runtime_outputs_queryReady_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (s : Store)
    (h : RuntimeReady I ε s) (hp : OutputParents I s)
    (hr : TargetRecords.RecordMap I ε (answerBranch I ε) s)
    (ht : CompletedTables I ε (outerInputs I ε).length s) (pc : ℕ),
  Query.QueryReady I ε (s.at pc)

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

def SetupReady.treeStart_contract_statement : Prop :=
  ∀ {I : Instance} {ε : ℝ} {s : Store}
    (h : SetupReady I ε s),
  (treeAllocation I ε).Registers .zeroLength (zeroTreePrepared .zeroLength s)

def TreeAllocation.protected_before_winner_contract_statement : Prop :=
  ∀ {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) (a : ℕ) (ha : a < E.W)
    (hfields : ∀ v ∈ activeVertices I,a ≠ targetAddress v+mode.offset),
  TreeWholeProtected E mode a

def treeAllocation_protected_before_map_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (mode : TreeMode)
    (a : ℕ) (ha : a < graphBase I ε)
    (hfields : ∀ v ∈ activeVertices I,a ≠ targetAddress v+mode.offset),
  TreeWholeProtected (treeAllocation I ε) mode a

def treeAllocation_header_protected_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (mode : TreeMode)
    (a : ℕ) (ha : a < 8),
  TreeWholeProtected (treeAllocation I ε) mode a

def treeAllocation_graph_protected_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (mode : TreeMode)
    (a : ℕ) (hlo : graphBase I ε ≤ a)
    (hhi : a < linksBase I ε+I.graph.edges.length),
  TreeWholeProtected (treeAllocation I ε) mode a

def treeAllocation_post_targets_protected_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (mode : TreeMode)
    (a : ℕ) (hlo : 16+4*I.graph.n ≤ a) (hhi : a < graphBase I ε),
  TreeWholeProtected (treeAllocation I ε) mode a

def treeAllocation_cache_protected_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (mode : TreeMode)
    (a : ℕ) (ha : a < outerQ ε),
  TreeWholeProtected (treeAllocation I ε) mode (Query.outputEnd I ε+a)

def treeAllocation_tag_protected_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (mode : TreeMode)
    (v : ℕ) (hv : v < I.graph.n),
  TreeWholeProtected (treeAllocation I ε) mode (targetAddress v)

def zeroTrees_nat_scalar_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s out : Store) (cost r : ℕ)
    (h : Run input zeroTreesCmd s out cost) (hlo : 121 ≤ r) (hhi : r ≤ 153),
  out.nr r=s.nr r

def zeroTrees_real_scalar_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s out : Store) (cost r : ℕ)
    (h : Run input zeroTreesCmd s out cost) (hlo : 121 ≤ r) (hhi : r ≤ 153),
  out.rr r=s.rr r

def ZeroTreeMemory.seedWorld_contract_statement : Prop :=
  ∀ (I : Instance) (s : Store) (h : ZeroTreeMemory I s)
    (hs : s.nr 123=I.source) (hb : s.rr 121=I.budget)
    (hL : s.rr 280=TreeMode.zeroLength.top I)
    (hC : s.rr 281=TreeMode.zeroBudget.top I),
  TargetRecords.SeedWorld I s

def zeroTrees_ready_contract_statement : Prop :=
  ∀ (I : Instance) (ε : ℝ) (s : Store) (hSetup : SetupReady I ε s),
  ∃ out steps, Run (encodeInput I ε) zeroTreesCmd s out steps ∧
      RuntimeReady I ε out ∧ OutputParents I out ∧ TargetRecords.SeedWorld I out ∧
      FutureZero I ε 0 out ∧
      (∀ v < I.graph.n,out.nm (targetAddress v)=0) ∧ out.nr 11=queueCapacity I ∧
      steps ≤ 2*(15*queueCapacity I+
        (38*Nat.clog 2 (2*queueCapacity I)+58)*(activeVertices I).length+
        (19*Nat.clog 2 (2*queueCapacity I)+46)*I.graph.edges.length+7)+6

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured
attribute [local instance] Classical.propDecidable

def markVisitor_world_contract_statement : Prop :=
  ∀ (input : RAMInput) (I : Instance) (ε : ℝ) (r : ℕ)
    (A : InnerInput) (s : Store) (v : ℕ) (hv : v < I.graph.n)
    (ha : s.nr 300 = targetAddress v) (h : MarkWorld I ε r A s),
  MarkWorld I ε r A (markVisitorResult input s)

def markVisitor_iteratorFrame_contract_statement : Prop :=
  ∀ (input : RAMInput) (I : Instance) (array : ℕ) (s : Store)
    (v : ℕ) (hv : v < I.graph.n) (ha : s.nr 300 = targetAddress v)
    (hspace : 16+4*I.graph.n ≤ array),
  ActiveIterator.Frame array (activeVertices I) s (markVisitorResult input s)

def markRecords_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (I : Instance) (ε : ℝ) (r : ℕ) (A : InnerInput)
    (hA : (outerInputs I ε)[r]? = some A) (array : ℕ) (s : Store)
    (hworld : MarkWorld I ε r A s) (hrecords : RecordMap I ε (branchesAfter I ε r) s)
    (ha : s.nr 142 = array) (hn : s.nr 143 = (activeVertices I).length)
    (hmem : ∀ k (hk : k < (activeVertices I).length), s.nm (array+k) = (activeVertices I)[k])
    (hspace : 16+4*I.graph.n ≤ array),
  ∃ out cost, Run input markRecordsCmd s out cost ∧ MarkWorld I ε r A out ∧
      RecordMap I ε (branchesAfter I ε (r+1)) out ∧ TargetFrame I s out ∧
      cost ≤ 27*(activeVertices I).length+4

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Outer
open Structured

def prepared_values_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (prepared input s).nr 200 = s.nr 244 ∧ (prepared input s).nr 201 = s.nr 124 ∧
    (prepared input s).nr 202 = s.nr 125 ∧ (prepared input s).nr 203 = s.nr 244+s.nr 133 ∧
    (prepared input s).nr 204 = s.nr 143 ∧ (prepared input s).nr 205 = s.nr 247 ∧
    (prepared input s).nr 206 = s.nr 248 ∧ (prepared input s).nr 207 = s.nr 249 ∧
    (prepared input s).nr 208 = s.nr 250 ∧ (prepared input s).nr 209 = s.nr 138 ∧
    (prepared input s).rr 200 = s.rr 127/(s.rr 244*s.rr 243) ∧
    (prepared input s).rr 201 = s.rr 245 ∧ (prepared input s).rr 202 = s.rr 128

def markPrepared_values_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (markPrepared input s).nr 301 = s.nr 244 ∧
    (markPrepared input s).rr 304 = s.rr 123*s.rr 243

def advanced_values_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (advanced input s).nr 243 = s.nr 243+s.nr 126 ∧
    (advanced input s).nr 244 = s.nr 244+s.nr 133 ∧
    (advanced input s).rr 243 = s.rr 243*s.rr 123

end NearLinearRSP.TwoResources.Mission.Outer
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources
namespace Mission

def poissonCountMass_recurrence_contract_statement : Prop :=
  ∀ (μ : ℝ) (k : ℕ),
  ActuarialValuation.poissonCountMass μ (k + 1) =
      ActuarialValuation.poissonCountMass μ k * μ / ((k : ℝ) + 1)

def poisson_prefix_contract_statement : Prop :=
  ∀ (input : RAMInput),
  execute poissonProgram input 10 initialState =
      poissonLoopState (input.reals 0) (input.naturals 0) 0

def poisson_iteration_contract_statement : Prop :=
  ∀ (input : RAMInput) (μ : ℝ) (n k : ℕ)
    (hk : k < n),
  execute poissonProgram input 6 (poissonLoopState μ n k) =
      poissonLoopState μ n (k + 1)

def poisson_iterations_contract_statement : Prop :=
  ∀ (input : RAMInput) (μ : ℝ) (n k : ℕ)
    (hk : k ≤ n),
  execute poissonProgram input (6 * k) (poissonLoopState μ n 0) =
      poissonLoopState μ n k

def poisson_exit_contract_statement : Prop :=
  ∀ (input : RAMInput) (μ : ℝ) (n : ℕ),
  execute poissonProgram input 4 (poissonLoopState μ n n) =
      poissonFinalState μ n

def poisson_evaluation_contract_statement : Prop :=
  ∀ (input : RAMInput),
  execute poissonProgram input (14 + 6 * input.naturals 0) initialState =
      poissonFinalState (input.reals 0) (input.naturals 0)

def poissonProgram_correct_contract_statement : Prop :=
  ∀ (input : RAMInput),
  ∃ (steps : ℕ) (out : RAMState),
      Execution poissonProgram input initialState out steps ∧
      steps ≤ 14 + 6 * input.naturals 0 ∧
      out.rm 0 = ActuarialValuation.poissonCountMass (input.reals 0) (input.naturals 0)

end Mission
end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped BigOperators
namespace NearLinearRSP.TwoResources.Mission.Expectation
open Structured

def run_atoms_contract_statement : Prop :=
  ∀ (input : RAMInput) (as : List Atom) (s : Store),
  Run input (atoms as) s (evalAtoms input as s) as.length

def Frame.refl_contract_statement : Prop :=
  ∀ (s : Store),
  Frame s s

def Frame.trans_contract_statement : Prop :=
  ∀ {s t u : Store} (h : Frame s t) (g : Frame t u),
  Frame s u

def ColumnFrame.refl_contract_statement : Prop :=
  ∀ (s : Store),
  ColumnFrame s s

def ColumnFrame.trans_contract_statement : Prop :=
  ∀ {s t u : Store} (h : ColumnFrame s t)
    (g : ColumnFrame t u),
  ColumnFrame s u

def ColumnFrame.frame_contract_statement : Prop :=
  ∀ {s t : Store} (h : ColumnFrame s t),
  Frame s t

def columnBody_inv_contract_statement : Prop :=
  ∀ (input : RAMInput) (c : ColumnContext) (k : ℕ)
    (total : ℝ) (s : Store) (h : ColumnInv c k total s),
  ColumnInv c (k + 1) (total + c.term k) (evalAtoms input columnAtoms s)

def columnBody_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  ColumnFrame s (evalAtoms input columnAtoms s)

def columnLoop_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (c : ColumnContext) (k d : ℕ)
    (total : ℝ) (s : Store) (h : ColumnInv c k total s) (hend : c.count = k + d),
  ∃ t : Store, Run input columnLoop s t (11 * d + 1) ∧
      ColumnInv c (k + d) (total + ∑ b ∈ Finset.range d, c.term (k + b)) t ∧
      ColumnFrame s t

def rowPrepare_inv_contract_statement : Prop :=
  ∀ (input : RAMInput) (c : RectangleContext) (a : ℕ)
    (total : ℝ) (s : Store) (h : RowInv c a total s),
  ColumnInv (c.column a) 0 total (evalAtoms input rowPrepare s)

def rowPrepare_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  ColumnFrame s (evalAtoms input rowPrepare s)

def RowInv.afterColumn_contract_statement : Prop :=
  ∀ (c : RectangleContext) (a : ℕ) (total next : ℝ)
    (s t : Store) (h : RowInv c a total s) (hf : ColumnFrame s t)
    (htotal : t.rr 82 = next),
  RowInv c a next t

def rowFinish_inv_contract_statement : Prop :=
  ∀ (input : RAMInput) (c : RectangleContext) (a : ℕ)
    (total : ℝ) (s : Store) (h : RowInv c a total s),
  RowInv c (a + 1) total (evalAtoms input rowFinish s)

def rowFinish_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  Frame s (evalAtoms input rowFinish s)

def rowBody_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (c : RectangleContext) (a : ℕ)
    (total : ℝ) (s : Store) (h : RowInv c a total s),
  ∃ t : Store, Run input rowBody s t (10 + 11 * c.cols) ∧
      RowInv c (a + 1) (total + c.row a) t ∧ Frame s t

def rowLoop_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (c : RectangleContext) (a d : ℕ)
    (total : ℝ) (s : Store) (h : RowInv c a total s) (hend : c.rows = a + d),
  ∃ t : Store, Run input rowLoop s t ((12 + 11 * c.cols) * d + 1) ∧
      RowInv c (a + d) (total + ∑ k ∈ Finset.range d, c.row (a + k)) t ∧ Frame s t

def corePrepare_inv_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  RowInv (contextOf s) 0 0 (evalAtoms input corePrepare s)

def corePrepare_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  Frame s (evalAtoms input corePrepare s)

def coreFinish_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  Frame s (evalAtoms input coreFinish s)

def coreCmd_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  ∃ t : Store, Run input coreCmd s t (13 + (12 + 11 * s.nr 87) * s.nr 86) ∧
      t.rr 82 = 1 - ∑ a ∈ Finset.range (s.nr 86),
        ∑ b ∈ Finset.range (s.nr 87),
          mass (s.rr 80) a * mass (s.rr 81) b *
            s.rm (s.nr 88 + s.nr 90 * a + s.nr 89 * b) ∧ Frame s t

def setupCmd_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  Run input setupCmd s (setupResult input s)
      (41 + 4 * s.nr 81 + 4 * (s.nr 81 * s.nr 80 + s.nr 82) + 4 * s.nr 80)

def setupResult_values_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  (setupResult input s).nr 86 = s.nr 80 - s.nr 81 ∧
    (setupResult input s).nr 87 = s.nr 80 - s.nr 82 ∧
    (setupResult input s).nr 88 = s.nr 84 + s.nr 85 * (s.nr 81 * s.nr 80 + s.nr 82) + 4 * s.nr 83 ∧
    (setupResult input s).nr 89 = s.nr 85 ∧
    (setupResult input s).nr 90 = s.nr 85 * s.nr 80

def FullFrame.refl_contract_statement : Prop :=
  ∀ (s : Store),
  FullFrame s s

def FullFrame.trans_contract_statement : Prop :=
  ∀ {s t u : Store} (h : FullFrame s t) (g : FullFrame t u),
  FullFrame s u

def Frame.full_contract_statement : Prop :=
  ∀ {s t : Store} (h : Frame s t),
  FullFrame s t

def setupResult_frame_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  FullFrame s (setupResult input s)

def nonsaturatedCmd_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store)
    (hi : s.nr 81 < s.nr 80) (hj : s.nr 82 < s.nr 80),
  ∃ t : Store, Run input nonsaturatedCmd s t
      (54 + 4 * s.nr 81 + 4 * (s.nr 81 * s.nr 80 + s.nr 82) + 4 * s.nr 80 +
        (12 + 11 * (s.nr 80 - s.nr 82)) * (s.nr 80 - s.nr 81)) ∧
      t.rr 82 = expectedResult s ∧ FullFrame s t

def expectationCmd_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (s : Store),
  ∃ (t : Store) (steps : ℕ), Run input expectationCmd s t steps ∧
      steps ≤ 100 * (s.nr 80 + 1) ^ 2 ∧
      t.rr 82 = expectedResult s ∧ FullFrame s t

def expectedResult_eq_edgeExpectation_contract_statement : Prop :=
  ∀ (A : InnerInput) (T : Table)
    (u v i j : ℕ) (s : Store)
    (hq : s.nr 80 = tickLimit A) (hi : s.nr 81 = i) (hj : s.nr 82 = j)
    (hμ : s.rr 80 = lengthRate A * A.I.length u v)
    (hν : s.rr 81 = costRate A * A.I.cost u v)
    (hmem : ∀ a < tickLimit A - i, ∀ b < tickLimit A - j,
      s.rm (s.nr 84 + s.nr 85 * ((i + a) * tickLimit A + (j + b)) + 4 * s.nr 83) =
        1 - (T u (i + a) (j + b)).value),
  expectedResult s = edgeExpectation A T u v i j

def edgeExpectation_run_contract_statement : Prop :=
  ∀ (input : RAMInput) (A : InnerInput) (T : Table)
    (u v i j : ℕ) (s : Store)
    (hq : s.nr 80 = tickLimit A) (hi : s.nr 81 = i) (hj : s.nr 82 = j)
    (hμ : s.rr 80 = lengthRate A * A.I.length u v)
    (hν : s.rr 81 = costRate A * A.I.cost u v)
    (hmem : ∀ a < tickLimit A - i, ∀ b < tickLimit A - j,
      s.rm (s.nr 84 + s.nr 85 * ((i + a) * tickLimit A + (j + b)) + 4 * s.nr 83) =
        1 - (T u (i + a) (j + b)).value),
  ∃ (t : Store) (steps : ℕ), Run input expectationCmd s t steps ∧
      steps ≤ 100 * (tickLimit A + 1) ^ 2 ∧
      t.rr 82 = edgeExpectation A T u v i j ∧ FullFrame s t

end NearLinearRSP.TwoResources.Mission.Expectation
end


