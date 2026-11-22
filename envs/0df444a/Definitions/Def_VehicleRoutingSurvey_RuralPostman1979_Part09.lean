-- Prove2me | Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part09
-- name    : VehicleRoutingSurvey_RuralPostman1979_Part09
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T14:19:50.788755+00:00
-- url     : https://prove2.me/theorems/9cb43036-84c7-4a14-878d-0d1ed77da1a5
-- title:
--   Rural postman algorithm — Cycle-record allocation and alternating-forest growth
-- statement:
--   This module supplies the Lean definitions and checked auxiliary results for cycle-record allocation and alternating-forest growth in the Table 3 proof. It uses the mission’s rural-run and arithmetic-RAM model.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.Chain
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part01
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part05
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part07
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part08

/-! matching/MatchingCycleRecordRAM.lean -/
section RppSource_MatchingCycleRecordRAM
namespace VehicleRoutingSurvey.Routing

/-- One child in the cyclic list and the original edge leading to the next child. -/
structure MatchingCycleChild where
  representative : ℕ
  node : ℕ
  endpointA : ℕ
  endpointB : ℕ

def MatchingCycleChild.words (child : MatchingCycleChild) : List ℕ :=
  [child.representative, child.node, child.endpointA, child.endpointB]

def writeMatchingCycleChild (memory : ℕ → ℕ) (address : ℕ) (child : MatchingCycleChild) : ℕ → ℕ :=
  Function.update
    (Function.update (Function.update (Function.update memory address child.representative)
      (address + 1) child.node) (address + 2) child.endpointA) (address + 3) child.endpointB

theorem writeMatchingCycleChild_lower (memory : ℕ → ℕ) (address : ℕ) (child : MatchingCycleChild)
    (a : ℕ) (low : a < address) : writeMatchingCycleChild memory address child a = memory a := by
  simp (disch := omega) [writeMatchingCycleChild, Function.update_of_ne]

theorem writeMatchingCycleChild_words (memory : ℕ → ℕ) (address : ℕ) (child : MatchingCycleChild)
    (i : ℕ) (inside : i < 4) :
    writeMatchingCycleChild memory address child (address + i) = child.words[i]?.getD 0 := by
  interval_cases i <;> simp (disch := omega) [writeMatchingCycleChild, MatchingCycleChild.words, Function.update_of_ne]

def currentMatchingCycleChild (s : ArithmeticState) : MatchingCycleChild :=
  ⟨s.nr 15, s.nm (s.nr 74 + s.nr 15), s.nr 16, s.nr 17⟩

/-- Append a child record at the live registry cursor. Its old node identifier is
loaded before any writes, making existing nested blossoms available to later expansions. -/
def appendMatchingCycleChild : List ArithmeticInstruction :=
  [.natAdd 6 74 15, .natLoad 10 6,
   .natStore 68 15, .natAdd 68 68 9, .natStore 68 10, .natAdd 68 68 9,
   .natStore 68 16, .natAdd 68 68 9, .natStore 68 17, .natAdd 68 68 9]

theorem appendMatchingCycleChild_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns appendMatchingCycleChild 10 s t ∧ t.halted = false ∧
      t.nr 68 = s.nr 68 + 4 ∧ t.nm = writeMatchingCycleChild s.nm (s.nr 68) (currentMatchingCycleChild s) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 10, 68] → t.nr r = s.nr r := by
  let t := (arithmeticStep appendMatchingCycleChild)^[10] s
  have effect : t.pc = appendMatchingCycleChild.length ∧ t.halted = false ∧ t.nr 68 = s.nr 68 + 4 ∧
      t.nm = writeMatchingCycleChild s.nm (s.nr 68) (currentMatchingCycleChild s) ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    have plusTwo : s.nr 68 + 1 + 1 = s.nr 68 + 2 := by omega
    have plusThree : s.nr 68 + 1 + 1 + 1 = s.nr 68 + 3 := by omega
    have plusFour : s.nr 68 + 1 + 1 + 1 + 1 = s.nr 68 + 4 := by omega
    simp [t, arithmeticStep, appendMatchingCycleChild, entry, running, one, Function.iterate_succ_apply',
      writeMatchingCycleChild, currentMatchingCycleChild, plusTwo, plusThree, plusFour]
  refine ⟨t, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1,
    effect.2.2.1, effect.2.2.2.1, effect.2.2.2.2.1, effect.2.2.2.2.2, ?_⟩
  intro r away
  apply arithmeticRun_keeps_register
  simp [appendMatchingCycleChild, naturalDestination] at away ⊢ <;> omega

def matchingCycleChildCount (s : ArithmeticState) : ℕ := s.nr 13 + s.nr 14 + 1

/-- Register the new cycle at zero dual value. Its record will start at the current
cursor and contain the two exclusive trace legs and the common base. -/
def startMatchingCycleRecord : List ArithmeticInstruction :=
  [.natAdd 6 77 76, .natStore 6 68, .natAdd 6 78 76,
   .natAdd 10 13 14, .natAdd 10 10 9, .natStore 6 10,
   .natAdd 6 75 76, .realConst 0 0, .realStore 6 0]

def startMatchingCycleNat (s : ArithmeticState) : ℕ → ℕ :=
  Function.update (Function.update s.nm (s.nr 77 + s.nr 76) (s.nr 68))
    (s.nr 78 + s.nr 76) (matchingCycleChildCount s)

def startMatchingCycleReal (s : ArithmeticState) : ℕ → ℝ :=
  Function.update s.rm (s.nr 75 + s.nr 76) 0

theorem startMatchingCycleRecord_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns startMatchingCycleRecord 9 s t ∧ t.halted = false ∧
      t.nm = startMatchingCycleNat s ∧ t.rm = startMatchingCycleReal s ∧
      ∀ r, r ∉ [0, 6, 10] → t.nr r = s.nr r := by
  let t := (arithmeticStep startMatchingCycleRecord)^[9] s
  have effect : t.pc = startMatchingCycleRecord.length ∧ t.halted = false ∧
      t.nm = startMatchingCycleNat s ∧ t.rm = startMatchingCycleReal s := by
    simp [t, arithmeticStep, startMatchingCycleRecord, entry, running, one, Function.iterate_succ_apply',
      startMatchingCycleNat, startMatchingCycleReal, matchingCycleChildCount]
  refine ⟨t, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1,
    effect.2.2.1, effect.2.2.2, ?_⟩
  intro r away
  apply arithmeticRun_keeps_register
  simp [startMatchingCycleRecord, naturalDestination] at away ⊢ <;> omega

def matchingCycleChildAt (memory : ℕ → ℕ) (address : ℕ) : MatchingCycleChild :=
  ⟨memory address, memory (address + 1), memory (address + 2), memory (address + 3)⟩

theorem matchingCycleChildAt_write (memory : ℕ → ℕ) (address : ℕ) (child : MatchingCycleChild) :
    matchingCycleChildAt (writeMatchingCycleChild memory address child) address = child := by
  cases child
  simp (disch := omega) [matchingCycleChildAt, writeMatchingCycleChild, Function.update_of_ne]

/-- Read a stored cycle header using its node identifier in register 22. -/
def readMatchingCycleHeader : List ArithmeticInstruction :=
  [.natAdd 6 77 22, .natLoad 18 6, .natAdd 6 78 22, .natLoad 19 6]

theorem readMatchingCycleHeader_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    ∃ t, BlockRuns readMatchingCycleHeader 4 s t ∧ t.halted = false ∧
      t.nr 18 = s.nm (s.nr 77 + s.nr 22) ∧ t.nr 19 = s.nm (s.nr 78 + s.nr 22) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 18, 19] → t.nr r = s.nr r := by
  let t := (arithmeticStep readMatchingCycleHeader)^[4] s
  have effect : t.pc = readMatchingCycleHeader.length ∧ t.halted = false ∧
      t.nr 18 = s.nm (s.nr 77 + s.nr 22) ∧ t.nr 19 = s.nm (s.nr 78 + s.nr 22) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, readMatchingCycleHeader, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1,
    effect.2.2.1, effect.2.2.2.1, effect.2.2.2.2.1, effect.2.2.2.2.2.1, effect.2.2.2.2.2.2, ?_⟩
  intro r away
  exact arithmeticRun_keeps_from_destination_list [0, 6, 18, 19] (by decide) away s 4

/-- Read a single child record at index 7 in the cycle starting at register 18. -/
def readMatchingCycleChild : List ArithmeticInstruction :=
  [.natAdd 6 7 7, .natAdd 6 6 6, .natAdd 6 18 6, .natLoad 15 6,
    .natAdd 6 6 9, .natLoad 25 6, .natAdd 6 6 9, .natLoad 16 6,
    .natAdd 6 6 9, .natLoad 17 6]

def readMatchingCycleChildValue (s : ArithmeticState) : MatchingCycleChild :=
  ⟨s.nr 15, s.nr 25, s.nr 16, s.nr 17⟩

theorem readMatchingCycleChild_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns readMatchingCycleChild 10 s t ∧ t.halted = false ∧
      readMatchingCycleChildValue t = matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 15, 16, 17, 25] → t.nr r = s.nr r := by
  let t := (arithmeticStep readMatchingCycleChild)^[10] s
  have effect : t.pc = readMatchingCycleChild.length ∧ t.halted = false ∧
      readMatchingCycleChildValue t = matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    have quad : s.nr 7 + s.nr 7 + (s.nr 7 + s.nr 7) = 4 * s.nr 7 := by omega
    have two : s.nr 18 + 4 * s.nr 7 + 1 + 1 = s.nr 18 + 4 * s.nr 7 + 2 := by omega
    have three : s.nr 18 + 4 * s.nr 7 + 1 + 1 + 1 = s.nr 18 + 4 * s.nr 7 + 3 := by omega
    simp [t, readMatchingCycleChild, arithmeticStep, entry, running, one, Function.iterate_succ_apply',
      readMatchingCycleChildValue, matchingCycleChildAt, quad, two, three]
  refine ⟨t, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1,
    effect.2.2.1, effect.2.2.2.1, effect.2.2.2.2.1, effect.2.2.2.2.2, ?_⟩
  intro r away
  exact arithmeticRun_keeps_from_destination_list [0, 6, 15, 16, 17, 25] (by decide) away s 10

end VehicleRoutingSurvey.Routing
end RppSource_MatchingCycleRecordRAM

/-! matching/MatchingCycleMembersRAM.lean -/
section RppSource_MatchingCycleMembersRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

def matchingCycleStackAddress (s : ArithmeticState) (i : ℕ) : ℕ := s.nr 80 + 3 * i

def pushedMatchingCycleMember (s : ArithmeticState) : ℕ → ℕ :=
  let addr := matchingCycleStackAddress s (s.nr 87)
  Function.update (Function.update (Function.update s.nm addr (s.nr 15)) (addr + 1) (s.nr 25))
    (addr + 2) (s.nr 26)

/-- Push a representative, child node ID, and its immediate child of the expanded
blossom onto the depth-first traversal stack. -/
def pushMatchingCycleMember : List ArithmeticInstruction :=
  [.natAdd 6 87 87, .natAdd 6 6 87, .natAdd 6 80 6, .natStore 6 15,
    .natAdd 6 6 9, .natStore 6 25, .natAdd 6 6 9, .natStore 6 26, .natAdd 87 87 9]

theorem pushMatchingCycleMember_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns pushMatchingCycleMember 9 s t ∧ t.halted = false ∧
      t.nr 87 = s.nr 87 + 1 ∧ t.nm = pushedMatchingCycleMember s ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 87] → t.nr r = s.nr r := by
  let t := (arithmeticStep pushMatchingCycleMember)^[9] s
  have address : s.nr 87 + s.nr 87 + s.nr 87 = 3 * s.nr 87 := by omega
  have extra : s.nr 80 + 3 * s.nr 87 + 1 + 1 = s.nr 80 + 3 * s.nr 87 + 2 := by omega
  have effect : t.pc = pushMatchingCycleMember.length ∧ t.halted = false ∧
      t.nr 87 = s.nr 87 + 1 ∧ t.nm = pushedMatchingCycleMember s ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, pushMatchingCycleMember, arithmeticStep, entry, running, one, Function.iterate_succ_apply',
      pushedMatchingCycleMember, matchingCycleStackAddress, address, extra]
  refine ⟨t, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1, effect.2.2.1,
    effect.2.2.2.1, effect.2.2.2.2.1, effect.2.2.2.2.2, ?_⟩
  intro r away
  exact arithmeticRun_keeps_from_destination_list [0, 6, 87] (by decide) away s 9

def popMatchingCycleMember : List ArithmeticInstruction :=
  [.natSub 87 87 9, .natAdd 6 87 87, .natAdd 6 6 87, .natAdd 6 80 6,
    .natLoad 15 6, .natAdd 6 6 9, .natLoad 22 6, .natAdd 6 6 9, .natLoad 26 6]

theorem popMatchingCycleMember_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns popMatchingCycleMember 9 s t ∧ t.halted = false ∧ t.nr 87 = s.nr 87 - 1 ∧
      t.nr 15 = s.nm (matchingCycleStackAddress s (s.nr 87 - 1)) ∧
      t.nr 22 = s.nm (matchingCycleStackAddress s (s.nr 87 - 1) + 1) ∧
      t.nr 26 = s.nm (matchingCycleStackAddress s (s.nr 87 - 1) + 2) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 15, 22, 26, 87] → t.nr r = s.nr r := by
  let t := (arithmeticStep popMatchingCycleMember)^[9] s
  let i := s.nr 87 - 1
  have address : i + i + i = 3 * i := by omega
  have extra : s.nr 80 + 3 * i + 1 + 1 = s.nr 80 + 3 * i + 2 := by omega
  have effect : t.pc = popMatchingCycleMember.length ∧ t.halted = false ∧ t.nr 87 = s.nr 87 - 1 ∧
      t.nr 15 = s.nm (matchingCycleStackAddress s (s.nr 87 - 1)) ∧
      t.nr 22 = s.nm (matchingCycleStackAddress s (s.nr 87 - 1) + 1) ∧
      t.nr 26 = s.nm (matchingCycleStackAddress s (s.nr 87 - 1) + 2) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    have rewriteIndex : s.nr 87 - 1 = i := rfl
    simp [t, popMatchingCycleMember, arithmeticStep, entry, running, one, Function.iterate_succ_apply',
      matchingCycleStackAddress, rewriteIndex, address, extra]
  obtain ⟨exit, live, count, rep, node, root, natural, real, registers⟩ := effect
  refine ⟨t, BlockRuns.of_running_exit rfl live exit, live, count, rep, node, root, natural, real, registers, ?_⟩
  intro r away
  exact arithmeticRun_keeps_from_destination_list [0, 6, 15, 22, 26, 87] (by decide) away s 9

def preserveTopCycleChild : List ArithmeticInstruction := [.natAdd 26 15 23]

def writeCycleMemberLeaf : List ArithmeticInstruction :=
  [.natAdd 6 79 15, .natStore 6 26]

def pushTopCycleChild : List ArithmeticInstruction :=
  appendBlock readMatchingCycleChild (appendBlock preserveTopCycleChild pushMatchingCycleMember)

def pushNestedCycleChild : List ArithmeticInstruction :=
  appendBlock readMatchingCycleChild pushMatchingCycleMember

def visitCycleMemberNode : List ArithmeticInstruction :=
  appendBlock popMatchingCycleMember (branchOnAtMost 22 23 writeCycleMemberLeaf
    (appendBlock readMatchingCycleHeader (countedLoopFromZero 9 7 19 pushNestedCycleChild)))

def clearCycleMemberMapCell : List ArithmeticInstruction :=
  [.natAdd 6 79 7, .natStore 6 55]

/-- Recover the immediate-child map of the nontrivial node given in register 22.
Each original leaf receives the representative of its immediate child. Registers
79 and 80 hold disjoint map and stack scratch arrays. -/
def mapMatchingCycleNodeMembers : List ArithmeticInstruction :=
  appendBlock [.natConst 23 0, .natConst 87 0, .natAdd 28 55 55]
    (appendBlock (countedLoopFromZero 9 7 55 clearCycleMemberMapCell)
      (appendBlock readMatchingCycleHeader
        (appendBlock (countedLoopFromZero 9 7 19 pushTopCycleChild)
          (countedLoopFromZero 9 24 28 (branchOnUnequal 87 23 visitCycleMemberNode)))))

/-- Recover the child map for the current top-level representative in register 97. -/
def mapMatchingCycleMembers : List ArithmeticInstruction :=
  appendBlock [.natAdd 6 74 97, .natLoad 22 6] mapMatchingCycleNodeMembers

theorem mapMatchingCycleNodeMembers_keeps_register {s t : ArithmeticState} {steps r : ℕ}
    (run : BlockRuns mapMatchingCycleNodeMembers steps s t)
    (away : r ∉ [0, 6, 7, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 28, 87]) : t.nr r = s.nr r := by
  rw [← run.run]
  exact arithmeticRun_keeps_from_destination_list [0, 6, 7, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 28, 87]
    (by decide) away s steps

private def onlyReadsReals : ArithmeticInstruction → Bool
  | .realConst _ _ | .realAdd _ _ _ | .realSub _ _ _ | .realMul _ _ _ | .realDiv _ _ _
  | .realLoad _ _ | .realStore _ _ => false
  | _ => true

private theorem arithmeticStep_keeps_reals {p : List ArithmeticInstruction} (readOnly : p.all onlyReadsReals = true)
    (s : ArithmeticState) : (arithmeticStep p s).rr = s.rr ∧ (arithmeticStep p s).rm = s.rm := by
  by_cases stopped : s.halted = true
  · simp [arithmeticStep, stopped]
  cases fetched : p[s.pc]? with
  | none => simp [arithmeticStep, stopped, fetched]
  | some ins =>
    have reads := List.all_eq_true.mp readOnly ins (List.mem_of_getElem? fetched)
    cases ins <;> simp [arithmeticStep, stopped, fetched, onlyReadsReals] at reads ⊢

private theorem arithmeticRun_keeps_reals {p : List ArithmeticInstruction} (readOnly : p.all onlyReadsReals = true)
    (s : ArithmeticState) (ticks : ℕ) :
    ((arithmeticStep p)^[ticks] s).rr = s.rr ∧ ((arithmeticStep p)^[ticks] s).rm = s.rm := by
  induction ticks with
  | zero => exact ⟨rfl, rfl⟩
  | succ ticks ih =>
    rw [Function.iterate_succ_apply']
    have step := arithmeticStep_keeps_reals readOnly ((arithmeticStep p)^[ticks] s)
    exact ⟨step.1.trans ih.1, step.2.trans ih.2⟩

theorem mapMatchingCycleNodeMembers_keeps_reals {s t : ArithmeticState} {steps : ℕ}
    (run : BlockRuns mapMatchingCycleNodeMembers steps s t) : t.rr = s.rr ∧ t.rm = s.rm := by
  rw [← run.run]
  exact arithmeticRun_keeps_reals (by decide) s steps

end VehicleRoutingSurvey.Routing
end RppSource_MatchingCycleMembersRAM

/-! matching/MatchingMemberTree.lean -/
section RppSource_MatchingMemberTree
namespace VehicleRoutingSurvey.Routing

/-- The live descendant records of a blossom. A nontrivial record owns an ordered
cycle of children and a singleton has no registry node. The final argument of each
nonempty constructor is the list of siblings. -/
inductive MatchingMemberTree where
  | nil
  | leaf (vertex : ℕ) (siblings : MatchingMemberTree)
  | blossom (representative node : ℕ) (children siblings : MatchingMemberTree)

namespace MatchingMemberTree

def arity : MatchingMemberTree → ℕ
  | .nil => 0
  | .leaf _ siblings | .blossom _ _ _ siblings => 1 + siblings.arity

def nodes : MatchingMemberTree → ℕ
  | .nil => 0
  | .leaf _ siblings => 1 + siblings.nodes
  | .blossom _ _ children siblings => 1 + children.nodes + siblings.nodes

def leaves : MatchingMemberTree → List ℕ
  | .nil => []
  | .leaf v siblings => v :: siblings.leaves
  | .blossom _ _ children siblings => children.leaves ++ siblings.leaves

/-- Two or more children suffice for the accounting bound. Actual blossom cycles
have odd length at least three. -/
def proper : MatchingMemberTree → Prop
  | .nil => True
  | .leaf _ siblings => siblings.proper
  | .blossom _ node children siblings =>
    0 < node ∧ 2 ≤ children.arity ∧ children.proper ∧ siblings.proper

theorem nodes_add_arity_le (tree : MatchingMemberTree) (properTree : tree.proper) :
    tree.nodes + tree.arity ≤ 2 * tree.leaves.length := by
  induction tree with
  | nil => simp [nodes, arity, leaves]
  | leaf v siblings ih =>
    have bound := ih properTree
    simp only [nodes, arity, leaves, List.length_cons]
    omega
  | blossom representative node children siblings ihChildren ihSiblings =>
    obtain ⟨_, branching, childrenWellFormed, siblingsWellFormed⟩ := properTree
    have childrenBound := ihChildren childrenWellFormed
    have siblingsBound := ihSiblings siblingsWellFormed
    simp only [nodes, arity, leaves, List.length_append]
    omega

theorem arity_le_nodes (tree : MatchingMemberTree) : tree.arity ≤ tree.nodes := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih => simp only [arity, nodes]; omega
  | blossom representative node children siblings _ ih => simp only [arity, nodes]; omega

/-- Registry words used by the membership traversal at one child entry. -/
def rootKey (representative node : ℕ) : ℕ × ℕ := (representative, node)

def rootKeys : MatchingMemberTree → List (ℕ × ℕ)
  | .nil => []
  | .leaf v siblings => rootKey v 0 :: siblings.rootKeys
  | .blossom r node _ siblings => rootKey r node :: siblings.rootKeys

@[simp] theorem rootKeys_length (tree : MatchingMemberTree) : tree.rootKeys.length = tree.arity := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih => simp [rootKeys, arity, ih, Nat.add_comm]
  | blossom r node children siblings _ ih => simp [rootKeys, arity, ih, Nat.add_comm]

/-- Interpret the descendants using exactly the cycle headers and child keys read by
the RAM routine. The two endpoint words of an entry are not used in this traversal. -/
def encoded (memory : ℕ → ℕ) (startBase countBase : ℕ) : MatchingMemberTree → Prop
  | .nil => True
  | .leaf _ siblings => siblings.encoded memory startBase countBase
  | .blossom _ node children siblings =>
    memory (countBase + node) = children.arity ∧
    (∀ i (h : i < children.rootKeys.length),
      let cell := matchingCycleChildAt memory (memory (startBase + node) + 4 * i)
      rootKey cell.representative cell.node = children.rootKeys[i]) ∧
    children.encoded memory startBase countBase ∧ siblings.encoded memory startBase countBase

/-- Areas which must remain unchanged while the scratch map and DFS stack are written. -/
def readable (memory : ℕ → ℕ) (startBase countBase : ℕ) (untouched : ℕ → Prop) :
    MatchingMemberTree → Prop
  | .nil => True
  | .leaf _ siblings => siblings.readable memory startBase countBase untouched
  | .blossom _ node children siblings =>
    untouched (startBase + node) ∧ untouched (countBase + node) ∧
    (∀ i < children.arity, ∀ w < 4, untouched (memory (startBase + node) + 4 * i + w)) ∧
    children.readable memory startBase countBase untouched ∧ siblings.readable memory startBase countBase untouched

theorem encoded_congr {tree : MatchingMemberTree} {before after : ℕ → ℕ} {startBase countBase : ℕ}
    {untouched : ℕ → Prop} (input : tree.encoded before startBase countBase)
    (frame : tree.readable before startBase countBase untouched)
    (keeps : ∀ a, untouched a → after a = before a) : tree.encoded after startBase countBase := by
  induction tree with
  | nil => trivial
  | leaf v siblings ih => exact ih input frame
  | blossom r node children siblings ihChildren ihSiblings =>
    obtain ⟨count, records, childInput, siblingInput⟩ := input
    obtain ⟨header, total, region, childFrame, siblingFrame⟩ := frame
    refine ⟨(keeps _ total).trans count, ?_, ihChildren childInput childFrame, ihSiblings siblingInput siblingFrame⟩
    intro i hi
    have index : i < children.arity := by simpa using hi
    have zero : untouched (before (startBase + node) + 4 * i) := by simpa using region i index 0 (by decide)
    have one := region i index 1 (by decide)
    have restored := records i hi
    simpa only [keeps _ header, rootKey, matchingCycleChildAt, keeps _ zero, keeps _ one] using restored

/-- The dynamic cycle records start past the statically allocated scratch arrays.
Unlike the cycle records, header cells may be below the scratch arrays. -/
def recordsAbove (memory : ℕ → ℕ) (startBase lower : ℕ) : MatchingMemberTree → Prop
  | .nil => True
  | .leaf _ siblings => siblings.recordsAbove memory startBase lower
  | .blossom _ node children siblings =>
    lower ≤ memory (startBase + node) ∧ children.recordsAbove memory startBase lower ∧
      siblings.recordsAbove memory startBase lower

end MatchingMemberTree

end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberTree

/-! matching/MatchingMemberStack.lean -/
section RppSource_MatchingMemberStack
namespace VehicleRoutingSurvey.Routing

/-- A pending visit keeps the immediate child of the original root even when it
travels down to a nested blossom. The first three fields are the RAM stack words. -/
structure MatchingMemberJob where
  representative : ℕ
  node : ℕ
  owner : ℕ
  children : Option MatchingMemberTree

namespace MatchingMemberJob

def assignments (job : MatchingMemberJob) : List (ℕ × ℕ) :=
  match job.children with
  | none => [(job.representative, job.owner)]
  | some children => children.leaves.map fun v => (v, job.owner)

def visits (job : MatchingMemberJob) : ℕ := 1 + (job.children.map MatchingMemberTree.nodes).getD 0

def proper (job : MatchingMemberJob) : Prop :=
  match job.children with
  | none => job.node = 0
  | some children => 0 < job.node ∧ 2 ≤ children.arity ∧ children.proper

def tree (job : MatchingMemberJob) : MatchingMemberTree :=
  match job.children with
  | none => .leaf job.representative .nil
  | some children => .blossom job.representative job.node children .nil

def frontier (stack : List MatchingMemberJob) : List (ℕ × ℕ) := stack.flatMap assignments

def work (stack : List MatchingMemberJob) : ℕ := (stack.map visits).sum

theorem work_append (left right : List MatchingMemberJob) : work (left ++ right) = work left + work right := by
  simp [work, List.sum_append]

theorem work_reverse (stack : List MatchingMemberJob) : work stack.reverse = work stack := by
  simp [work, List.sum_reverse_nat]

theorem frontier_reverse (stack : List MatchingMemberJob) : (frontier stack.reverse).Perm (frontier stack) :=
  (List.reverse_perm stack).flatMap_right assignments

end MatchingMemberJob

namespace MatchingMemberTree

/-- Order before the RAM puts these records on its LIFO stack. At the first level
each child is its own owner, and every deeper level inherits its parent's owner. -/
def jobs (owner : Option ℕ) : MatchingMemberTree → List MatchingMemberJob
  | .nil => []
  | .leaf v siblings => ⟨v, 0, owner.getD v, none⟩ :: siblings.jobs owner
  | .blossom r node children siblings => ⟨r, node, owner.getD r, some children⟩ :: siblings.jobs owner

theorem jobs_length (tree : MatchingMemberTree) (owner : Option ℕ) : (tree.jobs owner).length = tree.arity := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih => simp [jobs, arity, ih, Nat.add_comm]
  | blossom r node children siblings _ ih => simp [jobs, arity, ih, Nat.add_comm]

theorem jobs_rootKeys (tree : MatchingMemberTree) (owner : Option ℕ) :
    (tree.jobs owner).map (fun job => rootKey job.representative job.node) = tree.rootKeys := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih => simp [jobs, rootKeys, ih]
  | blossom r node children siblings _ ih => simp [jobs, rootKeys, ih]

theorem jobs_owner (tree : MatchingMemberTree) (owner : Option ℕ) :
    ∀ job ∈ tree.jobs owner, job.owner = owner.getD job.representative := by
  induction tree with
  | nil => simp [jobs]
  | leaf v siblings ih =>
    intro job present
    simp only [jobs, List.mem_cons] at present
    rcases present with rfl | present
    · rfl
    · exact ih job present
  | blossom r node children siblings _ ih =>
    intro job present
    simp only [jobs, List.mem_cons] at present
    rcases present with rfl | present
    · rfl
    · exact ih job present

theorem jobs_proper (tree : MatchingMemberTree) (owner : Option ℕ) (properTree : tree.proper) :
    ∀ job ∈ tree.jobs owner, job.proper := by
  induction tree with
  | nil => simp [jobs]
  | leaf v siblings ih =>
    intro job found
    simp only [jobs, List.mem_cons] at found
    rcases found with rfl | found
    · rfl
    · exact ih properTree job found
  | blossom r node children siblings ihChildren ihSiblings =>
    obtain ⟨identifier, branching, validChildren, validSiblings⟩ := properTree
    intro job found
    simp only [jobs, List.mem_cons] at found
    rcases found with rfl | found
    · exact ⟨identifier, branching, validChildren⟩
    · exact ihSiblings validSiblings job found

theorem jobs_work (tree : MatchingMemberTree) (owner : Option ℕ) :
    MatchingMemberJob.work (tree.jobs owner) = tree.nodes := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih =>
    change 1 + MatchingMemberJob.work (siblings.jobs owner) = 1 + siblings.nodes
    rw [ih]
  | blossom r node children siblings _ ih =>
    change 1 + children.nodes + MatchingMemberJob.work (siblings.jobs owner) = 1 + children.nodes + siblings.nodes
    rw [ih]

theorem jobs_inheritedFrontier (tree : MatchingMemberTree) (owner : ℕ) :
    MatchingMemberJob.frontier (tree.jobs (some owner)) = tree.leaves.map (fun v => (v, owner)) := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih =>
    simpa [jobs, leaves, MatchingMemberJob.frontier, MatchingMemberJob.assignments] using congrArg ((v, owner) :: ·) ih
  | blossom r node children siblings _ ih =>
    simpa [jobs, leaves, MatchingMemberJob.frontier, MatchingMemberJob.assignments] using
      congrArg (children.leaves.map (fun v => (v, owner)) ++ ·) ih

theorem jobs_frontier_vertices (tree : MatchingMemberTree) (owner : Option ℕ) :
    (MatchingMemberJob.frontier (tree.jobs owner)).map Prod.fst = tree.leaves := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih =>
    simpa [jobs, leaves, MatchingMemberJob.frontier, MatchingMemberJob.assignments] using congrArg (v :: ·) ih
  | blossom r node children siblings _ ih =>
    simpa [jobs, leaves, MatchingMemberJob.frontier, MatchingMemberJob.assignments, List.map_map, Function.comp_def] using
      congrArg (children.leaves ++ ·) ih

theorem jobs_encoded (tree : MatchingMemberTree) (owner : Option ℕ) (memory : ℕ → ℕ)
    (startBase countBase lower : ℕ) (untouched : ℕ → Prop)
    (encodedTree : tree.encoded memory startBase countBase)
    (readableTree : tree.readable memory startBase countBase untouched)
    (recordSpace : tree.recordsAbove memory startBase lower) :
    ∀ job ∈ tree.jobs owner, job.tree.encoded memory startBase countBase ∧
      job.tree.readable memory startBase countBase untouched ∧ job.tree.recordsAbove memory startBase lower := by
  induction tree with
  | nil => simp [jobs]
  | leaf v siblings ih =>
    intro job found
    simp only [jobs, List.mem_cons] at found
    rcases found with rfl | found
    · exact ⟨trivial, trivial, trivial⟩
    · exact ih encodedTree readableTree recordSpace job found
  | blossom r node children siblings _ ih =>
    obtain ⟨size, rows, childEncoding, siblingEncoding⟩ := encodedTree
    obtain ⟨header, total, cell, childReadable, siblingReadable⟩ := readableTree
    obtain ⟨space, childSpace, siblingSpace⟩ := recordSpace
    intro job found
    simp only [jobs, List.mem_cons] at found
    rcases found with rfl | found
    · exact ⟨⟨size, rows, childEncoding, trivial⟩, ⟨header, total, cell, childReadable, trivial⟩,
        ⟨space, childSpace, trivial⟩⟩
    · exact ih siblingEncoding siblingReadable siblingSpace job found

end MatchingMemberTree

namespace MatchingMemberJob

theorem pushChildren_frontier (head : MatchingMemberJob) (rest : List MatchingMemberJob)
    (children : MatchingMemberTree) (nested : head.children = some children) :
    (frontier ((children.jobs (some head.owner)).reverse ++ rest)).Perm (frontier (head :: rest)) := by
  have swapped := (frontier_reverse (children.jobs (some head.owner))).append_right (frontier rest)
  simpa [frontier, assignments, nested, ← children.jobs_inheritedFrontier head.owner] using swapped

theorem pushChildren_work (head : MatchingMemberJob) (rest : List MatchingMemberJob)
    (children : MatchingMemberTree) (nested : head.children = some children) :
    work ((children.jobs (some head.owner)).reverse ++ rest) + 1 = work (head :: rest) := by
  rw [work_append, work_reverse, children.jobs_work]
  simp [work, visits, nested]
  omega

theorem visits_pos (job : MatchingMemberJob) : 0 < job.visits := by
  simp [visits]

theorem length_le_work (stack : List MatchingMemberJob) : stack.length ≤ work stack := by
  induction stack with
  | nil => rfl
  | cons head rest ih =>
    have pos := head.visits_pos
    simp only [List.length_cons, work, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem assignments_nonempty (job : MatchingMemberJob) (good : job.proper) : 0 < job.assignments.length := by
  cases owned : job.children with
  | none => simp [assignments, owned]
  | some children =>
    rw [proper, owned] at good
    obtain ⟨_, many, childrenGood⟩ := good
    have count := children.nodes_add_arity_le childrenGood
    simp only [assignments, owned, List.length_map]
    omega

theorem length_le_frontier (stack : List MatchingMemberJob) (good : ∀ job ∈ stack, job.proper) :
    stack.length ≤ (frontier stack).length := by
  induction stack with
  | nil => rfl
  | cons head rest ih =>
    have positive := head.assignments_nonempty (good head (by simp))
    have below := ih (fun job h => good job (List.mem_cons_of_mem _ h))
    simp only [frontier, List.flatMap_cons, List.length_append, List.length_cons] at below ⊢
    omega

theorem frontier_append (first second : List MatchingMemberJob) :
    frontier (first ++ second) = frontier first ++ frontier second := by simp [frontier]

theorem appendChildren_frontier (earlier : List MatchingMemberJob) (job : MatchingMemberJob)
    (children : MatchingMemberTree) (nested : job.children = some children) :
    frontier (earlier ++ children.jobs (some job.owner)) = frontier (earlier ++ [job]) := by
  rw [frontier_append, frontier_append, children.jobs_inheritedFrontier]
  simp [frontier, assignments, nested]

theorem appendChildren_work (earlier : List MatchingMemberJob) (job : MatchingMemberJob)
    (children : MatchingMemberTree) (nested : job.children = some children) :
    work (earlier ++ children.jobs (some job.owner)) + 1 = work (earlier ++ [job]) := by
  rw [work_append, work_append, children.jobs_work]
  simp [work, visits, nested] <;> omega

theorem frontier_length_le {stack : List MatchingMemberJob} {done all : List (ℕ × ℕ)}
    (same : (done ++ frontier stack).Perm all) : (frontier stack).length ≤ all.length := by
  have length := same.length_eq
  simp only [List.length_append] at length
  omega

theorem boundedAssignments_length (assignments : List (ℕ × ℕ)) (k : ℕ)
    (unique : (assignments.map Prod.fst).Nodup) (inside : ∀ p ∈ assignments, p.1 < k) :
    assignments.length ≤ k := by
  let vertices := assignments.map Prod.fst
  have values : vertices.toFinset ⊆ Finset.range k := by
    intro v found
    have inList := List.mem_toFinset.mp found
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp inList
    exact Finset.mem_range.mpr (inside p hp)
  simpa [List.toFinset_card_of_nodup unique, vertices] using Finset.card_le_card values

end MatchingMemberJob

end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberStack

/-! matching/MatchingMemberVisitRAM.lean -/
section RppSource_MatchingMemberVisitRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

def matchingMemberJobWords (job : MatchingMemberJob) : ℕ × ℕ × ℕ :=
  (job.representative, job.node, job.owner)

def matchingMemberStackWords (memory : ℕ → ℕ) (address : ℕ) : ℕ × ℕ × ℕ :=
  (memory address, memory (address + 1), memory (address + 2))

def matchingMemberStackWrite (memory : ℕ → ℕ) (address : ℕ) (words : ℕ × ℕ × ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update memory address words.1) (address + 1) words.2.1)
    (address + 2) words.2.2

theorem matchingMemberStackWrite_words (memory : ℕ → ℕ) (address : ℕ) (words : ℕ × ℕ × ℕ) :
    matchingMemberStackWords (matchingMemberStackWrite memory address words) address = words := by
  rcases words with ⟨representative, node, owner⟩
  simp (disch := omega) [matchingMemberStackWrite, matchingMemberStackWords, Function.update_of_ne]

theorem matchingMemberStackWrite_unchanged (memory : ℕ → ℕ) (address : ℕ) (words : ℕ × ℕ × ℕ)
    (a : ℕ) (outside : a < address ∨ address + 3 ≤ a) : matchingMemberStackWrite memory address words a = memory a := by
  simp (disch := omega) [matchingMemberStackWrite, Function.update_of_ne]

theorem writeCycleMemberLeaf_spec (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns writeCycleMemberLeaf 2 s t ∧ t.halted = false ∧
      t.nm = Function.update s.nm (s.nr 79 + s.nr 15) (s.nr 26) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6] → t.nr r = s.nr r := by
  let t := (arithmeticStep writeCycleMemberLeaf)^[2] s
  have effect : t.pc = writeCycleMemberLeaf.length ∧ t.halted = false ∧
      t.nm = Function.update s.nm (s.nr 79 + s.nr 15) (s.nr 26) ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, writeCycleMemberLeaf, entry, running, arithmeticStep, Function.iterate_succ_apply']
  exact ⟨t, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1, effect.2.2.1,
    effect.2.2.2.1, effect.2.2.2.2, fun _ safe =>
      arithmeticRun_keeps_from_destination_list _ (by decide) safe s 2⟩

theorem clearCycleMemberMapCell_spec (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns clearCycleMemberMapCell 2 s t ∧ t.halted = false ∧
      t.nm = Function.update s.nm (s.nr 79 + s.nr 7) (s.nr 55) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6] → t.nr r = s.nr r := by
  let t := (arithmeticStep clearCycleMemberMapCell)^[2] s
  have effect : t.pc = clearCycleMemberMapCell.length ∧ t.halted = false ∧
      t.nm = Function.update s.nm (s.nr 79 + s.nr 7) (s.nr 55) ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, clearCycleMemberMapCell, entry, running, arithmeticStep, Function.iterate_succ_apply']
  exact ⟨t, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1, effect.2.2.1,
    effect.2.2.2.1, effect.2.2.2.2, fun _ safe =>
      arithmeticRun_keeps_from_destination_list _ (by decide) safe s 2⟩

private structure ClearedMatchingMemberMap (s : ArithmeticState) (i : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  running : m.halted = false
  index : m.nr 7 = i
  registers : ∀ r, r ∉ [0, 6, 7] → m.nr r = s.nr r
  natural : ∀ a, m.nm a = if s.nr 79 ≤ a ∧ a < s.nr 79 + i then s.nr 55 else s.nm a
  real : m.rm = s.rm
  realRegisters : m.rr = s.rr

theorem clearCycleMemberMap_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ 5 * s.nr 55 + 2 ∧
      BlockRuns (countedLoopFromZero 9 7 55 clearCycleMemberMapCell) steps s t ∧ t.halted = false ∧
      (∀ a, t.nm a = if s.nr 79 ≤ a ∧ a < s.nr 79 + s.nr 55 then s.nr 55 else s.nm a) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 7] → t.nr r = s.nr r := by
  have initial : ClearedMatchingMemberMap s 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, ?_, rfl, rfl⟩
    · intro r safe
      exact Function.update_of_ne (by simp at safe; omega) _ _
    · intro a
      have no : ¬(s.nr 79 ≤ a ∧ a < s.nr 79 + 0) := by omega
      simp [no]
  have iteration (i : ℕ) (_ : i < s.nr 55) (m : ArithmeticState) (inv : ClearedMatchingMemberMap s i m) :
      ∃ t steps, steps ≤ 2 ∧ BlockRuns clearCycleMemberMapCell steps m t ∧ t.halted = false ∧
        ClearedMatchingMemberMap s (i+1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    obtain ⟨t, run, live, natural, real, rr, keeps⟩ := clearCycleMemberMapCell_spec m inv.entry inv.running
    have oneAt : m.nr 9 = 1 := (inv.registers 9 (by decide)).trans one
    refine ⟨t, 2, le_rfl, run, live, rfl, live, ?_, ?_, ?_, real.trans inv.real, rr.trans inv.realRegisters⟩
    · simp [keeps 7 (by decide), keeps 9 (by decide), inv.index, oneAt]
    · intro r away
      have safe : r ∉ [0, 6] := by simp at away ⊢; omega
      exact (Function.update_of_ne (by simp at away; omega) _ _).trans ((keeps r safe).trans (inv.registers r away))
    · intro a
      change t.nm a = _
      rw [natural, inv.registers 79 (by decide), inv.index, inv.registers 55 (by decide)]
      by_cases atEnd : a = s.nr 79 + i
      · have inside : s.nr 79 ≤ a ∧ a < s.nr 79 + (i+1) := by omega
        simp [atEnd, if_pos (by omega : s.nr 79 ≤ s.nr 79 + i ∧ s.nr 79 + i < s.nr 79 + (i+1))]
      · have same : (s.nr 79 ≤ a ∧ a < s.nr 79 + (i+1)) ↔ s.nr 79 ≤ a ∧ a < s.nr 79 + i := by omega
        simp [Function.update_of_ne atEnd, inv.natural, same]
  obtain ⟨t, ticks, done, budget, run⟩ := countedLoopFromZero_bounded 9 7 55 (s.nr 55) 2
    clearCycleMemberMapCell (ClearedMatchingMemberMap s) (s := s) entry running initial
    (fun _ _ inv => ⟨inv.entry, inv.running, inv.index, inv.registers 55 (by decide)⟩) iteration
  exact ⟨_, ticks, by omega, run, done.running, done.natural, done.real, done.realRegisters, done.registers⟩

def pushMatchingMemberFromCycle (newOwner : Bool) : List ArithmeticInstruction :=
  if newOwner then pushTopCycleChild else pushNestedCycleChild

theorem pushMatchingMemberFromCycle_spec (newOwner : Bool) (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0) :
    let record := matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7)
    let owner := if newOwner then record.representative else s.nr 26
    ∃ t steps, steps ≤ 20 ∧ BlockRuns (pushMatchingMemberFromCycle newOwner) steps s t ∧ t.halted = false ∧
      t.nr 87 = s.nr 87 + 1 ∧ t.nm = matchingMemberStackWrite s.nm (matchingCycleStackAddress s (s.nr 87))
        (record.representative, record.node, owner) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 15, 16, 17, 25, 26, 87] → t.nr r = s.nr r := by
  intro record owner
  obtain ⟨read, readRun, readLive, fields, sameNat, sameReal, sameRR, keeps⟩ :=
    readMatchingCycleChild_spec s entry running one
  let a := {read with pc := 0}
  have aOne : a.nr 9 = 1 := (keeps 9 (by decide)).trans one
  have aZero : a.nr 23 = 0 := (keeps 23 (by decide)).trans zero
  have rep : a.nr 15 = record.representative := congrArg MatchingCycleChild.representative fields
  have node : a.nr 25 = record.node := congrArg MatchingCycleChild.node fields
  have count : a.nr 87 = s.nr 87 := keeps 87 (by decide)
  have stackBase : a.nr 80 = s.nr 80 := keeps 80 (by decide)
  have previousOwner : a.nr 26 = s.nr 26 := keeps 26 (by decide)
  have aNat : a.nm = s.nm := sameNat
  cases newOwner
  · obtain ⟨t, write, ready, more, written, real, realRegs, _⟩ := pushMatchingCycleMember_spec a rfl readLive aOne
    have combined : BlockRuns (pushMatchingMemberFromCycle false) (10 + 9) s _ := readRun.append write
    refine ⟨_, 19, by decide, combined, ready, more.trans (congrArg (· + 1) count), ?_,
      real.trans sameReal, realRegs.trans sameRR, ?_⟩
    · change t.nm = _
      rw [written]
      simp [pushedMatchingCycleMember, matchingMemberStackWrite, matchingCycleStackAddress, aNat, count,
        stackBase, rep, node, previousOwner, owner]
    · intro r safe
      rw [← combined.run]
      exact arithmeticRun_keeps_from_destination_list [0, 6, 15, 16, 17, 25, 26, 87] (by decide) safe s 19
  · let b := {a with pc := 1, nr := Function.update a.nr 26 (a.nr 15)}
    have readZero : read.nr 23 = 0 := aZero
    have save : BlockRuns preserveTopCycleChild 1 a b := by
      apply BlockRuns.of_running_exit
      · simp [b, preserveTopCycleChild, arithmeticStep, a, readLive, readZero]
      · exact readLive
      · rfl
    let c := {b with pc := 0}
    have cOne : c.nr 9 = 1 := by simpa [c, b] using aOne
    obtain ⟨t, write, ready, more, written, real, realRegs, _⟩ := pushMatchingCycleMember_spec c rfl readLive cOne
    have combined : BlockRuns (pushMatchingMemberFromCycle true) (10 + (1 + 9)) s _ := readRun.append (save.append write)
    have cCount : c.nr 87 = s.nr 87 := by simpa [c, b] using count
    have cBase : c.nr 80 = s.nr 80 := by simpa [c, b] using stackBase
    have cRep : c.nr 15 = record.representative := by simpa [c, b] using rep
    have cNode : c.nr 25 = record.node := by simpa [c, b] using node
    have cOwner : c.nr 26 = record.representative := by simpa [c, b] using rep
    have cNat : c.nm = s.nm := sameNat
    refine ⟨_, 20, le_rfl, combined, ready, more.trans (congrArg (· + 1) cCount), ?_,
      real.trans sameReal, realRegs.trans sameRR, ?_⟩
    · change t.nm = _
      rw [written]
      simp [pushedMatchingCycleMember, matchingMemberStackWrite, matchingCycleStackAddress, cNat, cCount,
        cBase, cRep, cNode, cOwner, owner]
    · intro r safe
      rw [← combined.run]
      exact arithmeticRun_keeps_from_destination_list [0, 6, 15, 16, 17, 25, 26, 87] (by decide) safe s 20

theorem pushMatchingMemberFromCycle_keeps_inherited {s t : ArithmeticState} {steps : ℕ}
    (run : BlockRuns (pushMatchingMemberFromCycle false) steps s t) : t.nr 26 = s.nr 26 := by
  rw [← run.run]
  exact arithmeticRun_keeps_from_destination_list [0, 6, 15, 16, 17, 25, 87] (by decide) (by decide) s steps

def matchingMemberChildPushCount (s : ArithmeticState) (i : ℕ) : ℕ := s.nr 80 + 3 * (s.nr 87 + i)

/-- The stack initially contains an untouched prefix. The child scan appends the
cycle records in increasing physical order, leaving later pushes to use LIFO order. -/
structure MatchingMemberChildPush (s : ArithmeticState) (newOwner : Bool) (jobs : List MatchingMemberJob)
    (i : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  running : m.halted = false
  index : m.nr 7 = i
  count : m.nr 87 = s.nr 87 + i
  registers : ∀ r, r ∉ [0, 6, 7, 15, 16, 17, 25, 26, 87] → m.nr r = s.nr r
  inherited : newOwner = false → m.nr 26 = s.nr 26
  stack : ∀ j (hj : j < i) (inside : j < jobs.length),
    matchingMemberStackWords m.nm (matchingMemberChildPushCount s j) = matchingMemberJobWords jobs[j]
  natural : ∀ a, (a < matchingMemberChildPushCount s 0 ∨ matchingMemberChildPushCount s i ≤ a) → m.nm a = s.nm a
  real : m.rm = s.rm
  realRegisters : m.rr = s.rr

theorem pushMatchingMemberChildren_spec (newOwner : Bool) (s : ArithmeticState) (jobs : List MatchingMemberJob)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0)
    (count : s.nr 19 = jobs.length) (space : matchingMemberChildPushCount s jobs.length ≤ s.nr 18)
    (read : ∀ i (hi : i < jobs.length),
      let record := matchingCycleChildAt s.nm (s.nr 18 + 4 * i)
      let job := jobs[i]
      (record.representative, record.node) = (job.representative, job.node) ∧
      job.owner = (if newOwner then job.representative else s.nr 26)) :
    ∃ t steps, steps ≤ 23 * jobs.length + 2 ∧
      BlockRuns (countedLoopFromZero 9 7 19 (pushMatchingMemberFromCycle newOwner)) steps s t ∧
      MatchingMemberChildPush s newOwner jobs jobs.length {t with pc := 0} := by
  have initial : MatchingMemberChildPush s newOwner jobs 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, by simp, ?_, by simp, ?_, fun _ _ => rfl, rfl, rfl⟩
    · intro r safe
      have other : r ≠ 7 := by simp at safe; omega
      exact Function.update_of_ne other _ _
    · intro j hj
      omega
  have step (i : ℕ) (hi : i < jobs.length) (m : ArithmeticState)
      (inv : MatchingMemberChildPush s newOwner jobs i m) :
      ∃ t steps, steps ≤ 20 ∧ BlockRuns (pushMatchingMemberFromCycle newOwner) steps m t ∧ t.halted = false ∧
        MatchingMemberChildPush s newOwner jobs (i+1)
          {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    have oneAt : m.nr 9 = 1 := (inv.registers 9 (by decide)).trans one
    have zeroAt : m.nr 23 = 0 := (inv.registers 23 (by decide)).trans zero
    obtain ⟨t, steps, budget, run, live, more, memory, real, realRegisters, kept⟩ :=
      pushMatchingMemberFromCycle_spec newOwner m inv.entry inv.running oneAt zeroAt
    have atCycle : m.nr 18 = s.nr 18 := inv.registers 18 (by decide)
    have recordEq : matchingCycleChildAt m.nm (m.nr 18 + 4 * m.nr 7) =
        matchingCycleChildAt s.nm (s.nr 18 + 4 * i) := by
      rw [atCycle, inv.index]
      have addresses (w : ℕ) : m.nm (s.nr 18 + 4 * i + w) = s.nm (s.nr 18 + 4 * i + w) := by
        apply inv.natural
        right
        unfold matchingMemberChildPushCount at space ⊢
        omega
      have first := addresses 0
      simp only [Nat.add_zero] at first
      simp only [matchingCycleChildAt, first, addresses 1, addresses 2, addresses 3]
    have whereAt : matchingCycleStackAddress m (m.nr 87) = matchingMemberChildPushCount s i := by
      rw [matchingCycleStackAddress, matchingMemberChildPushCount, inv.registers 80 (by decide), inv.count]
    have ownerAt : (if newOwner then jobs[i].representative else m.nr 26) = jobs[i].owner := by
      cases h : newOwner
      · simpa [h, inv.inherited h] using (read i hi).2.symm
      · simpa [h] using (read i hi).2.symm
    have effect : t.nm = matchingMemberStackWrite m.nm (matchingMemberChildPushCount s i)
        (matchingMemberJobWords jobs[i]) := by
      rw [memory, recordEq, whereAt]
      have rp : (matchingCycleChildAt s.nm (s.nr 18 + 4 * i)).representative = jobs[i].representative :=
        congrArg Prod.fst (read i hi).1
      have nd : (matchingCycleChildAt s.nm (s.nr 18 + 4 * i)).node = jobs[i].node := congrArg Prod.snd (read i hi).1
      rw [rp, nd, ownerAt]
      rfl
    refine ⟨t, steps, budget, run, live, rfl, live, ?_, ?_, ?_, ?_, ?_, ?_,
      real.trans inv.real, realRegisters.trans inv.realRegisters⟩
    · simp [kept 7 (by decide), kept 9 (by decide), inv.index, oneAt]
    · change t.nr 87 = _
      rw [more, inv.count]
      omega
    · intro r safe
      have different : r ≠ 7 := by simp at safe; omega
      have outside : r ∉ [0, 6, 15, 16, 17, 25, 26, 87] := by simp at safe ⊢; omega
      exact (Function.update_of_ne different _ _).trans ((kept r outside).trans (inv.registers r safe))
    · intro inherited
      subst newOwner
      change t.nr 26 = s.nr 26
      exact (pushMatchingMemberFromCycle_keeps_inherited run).trans (inv.inherited rfl)
    · intro j hj inJobs
      change matchingMemberStackWords t.nm (matchingMemberChildPushCount s j) = _
      rw [effect]
      obtain before | equal := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)
      · have same (w : ℕ) (hw : w < 3) : matchingMemberStackWrite m.nm (matchingMemberChildPushCount s i)
            (matchingMemberJobWords jobs[i]) (matchingMemberChildPushCount s j + w) =
            m.nm (matchingMemberChildPushCount s j + w) := by
          apply matchingMemberStackWrite_unchanged
          left
          unfold matchingMemberChildPushCount
          omega
        have first := same 0 (by decide)
        simp only [Nat.add_zero] at first
        simpa only [matchingMemberStackWords, first, same 1 (by decide), same 2 (by decide)] using inv.stack j before inJobs
      · subst j
        exact matchingMemberStackWrite_words _ _ _
    · intro a far
      change t.nm a = s.nm a
      have previous : a < matchingMemberChildPushCount s 0 ∨ matchingMemberChildPushCount s i ≤ a := by
        unfold matchingMemberChildPushCount at far ⊢
        omega
      have skips : a < matchingMemberChildPushCount s i ∨ matchingMemberChildPushCount s i + 3 ≤ a := by
        unfold matchingMemberChildPushCount at far ⊢
        omega
      exact (congrFun effect a).trans ((matchingMemberStackWrite_unchanged _ _ _ a skips).trans (inv.natural a previous))
  obtain ⟨t, steps, completed, budget, run⟩ := countedLoopFromZero_bounded 9 7 19 jobs.length 20
    (pushMatchingMemberFromCycle newOwner) (MatchingMemberChildPush s newOwner jobs) (s := s)
    entry running initial (fun _ _ inv => ⟨inv.entry, inv.running, inv.index,
      (inv.registers 19 (by decide)).trans count⟩) step
  exact ⟨_, steps, by omega, run, rfl, completed.running, completed.index, completed.count,
    completed.registers, completed.inherited, completed.stack, completed.natural, completed.real, completed.realRegisters⟩

/-- The leaf branch pops one record, writes the recorded owner, and leaves the
remaining stack words unchanged. -/
theorem visitCycleMemberLeaf_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0) (v owner : ℕ)
    (top : matchingMemberStackWords s.nm (matchingCycleStackAddress s (s.nr 87 - 1)) = (v, 0, owner)) :
    ∃ t, BlockRuns visitCycleMemberNode 13 s t ∧ t.halted = false ∧ t.nr 87 = s.nr 87 - 1 ∧
      t.nm = Function.update s.nm (s.nr 79 + v) owner ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 15, 22, 26, 87] → t.nr r = s.nr r := by
  obtain ⟨p, pop, pLive, pCount, rep, node, tag, pNat, pReal, pRR, pKeeps⟩ :=
    popMatchingCycleMember_spec s entry running one
  let a := {p with pc := 0}
  have vertex : a.nr 15 = v := rep.trans (congrArg Prod.fst top)
  have identifier : a.nr 22 = 0 := node.trans (congrArg (fun w : ℕ × ℕ × ℕ => w.2.1) top)
  have ownerAt : a.nr 26 = owner := tag.trans (congrArg (fun w : ℕ × ℕ × ℕ => w.2.2) top)
  have zeroAt : a.nr 23 = 0 := (pKeeps 23 (by decide)).trans zero
  have mapAt : a.nr 79 = s.nr 79 := pKeeps 79 (by decide)
  obtain ⟨t, write, tLive, natural, real, rr, kept⟩ := writeCycleMemberLeaf_spec a rfl pLive
  have branch := branchOnAtMost_left 22 23 writeCycleMemberLeaf
    (appendBlock readMatchingCycleHeader (countedLoopFromZero 9 7 19 pushNestedCycleChild)) (s := a) rfl pLive
    (by simp [identifier, zeroAt]) write tLive
  have run : BlockRuns visitCycleMemberNode 13 s _ := pop.append branch
  refine ⟨_, run, tLive, (kept 87 (by decide)).trans pCount, ?_, real.trans pReal, rr.trans pRR, ?_⟩
  · change t.nm = _
    rw [natural, mapAt, vertex, ownerAt]
    change Function.update p.nm _ _ = _
    rw [pNat]
  · intro r safe
    exact (kept r (by simp at safe ⊢; omega)).trans (pKeeps r safe)

/-- The nontrivial branch pops one node and pushes exactly its ordered children.
Only the appended stack area is written. -/
theorem visitCycleMemberBlossom_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0)
    (representative node owner : ℕ) (positive : 0 < node) (jobs : List MatchingMemberJob)
    (top : matchingMemberStackWords s.nm (matchingCycleStackAddress s (s.nr 87 - 1)) = (representative, node, owner))
    (headerCount : s.nm (s.nr 78 + node) = jobs.length)
    (space : s.nr 80 + 3 * (s.nr 87 - 1 + jobs.length) ≤ s.nm (s.nr 77 + node))
    (read : ∀ i (hi : i < jobs.length),
      let cell := matchingCycleChildAt s.nm (s.nm (s.nr 77 + node) + 4 * i)
      (cell.representative, cell.node) = (jobs[i].representative, jobs[i].node) ∧ jobs[i].owner = owner) :
    ∃ t steps, steps ≤ 23 * jobs.length + 16 ∧ BlockRuns visitCycleMemberNode steps s t ∧ t.halted = false ∧
      t.nr 87 = s.nr 87 - 1 + jobs.length ∧
      (∀ i (hi : i < jobs.length), matchingMemberStackWords t.nm (s.nr 80 + 3 * (s.nr 87 - 1 + i)) =
        matchingMemberJobWords jobs[i]) ∧
      (∀ a, a < s.nr 80 + 3 * (s.nr 87 - 1) ∨ s.nr 80 + 3 * (s.nr 87 - 1 + jobs.length) ≤ a → t.nm a = s.nm a) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 7, 15, 16, 17, 18, 19, 22, 25, 26, 87] → t.nr r = s.nr r := by
  obtain ⟨p, pop, pLive, pCount, _, pNode, tag, pNat, pReal, pRR, pKeeps⟩ :=
    popMatchingCycleMember_spec s entry running one
  let a := {p with pc := 0}
  have nodeAt : a.nr 22 = node := pNode.trans (congrArg (fun w : ℕ × ℕ × ℕ => w.2.1) top)
  have ownerAt : a.nr 26 = owner := tag.trans (congrArg (fun w : ℕ × ℕ × ℕ => w.2.2) top)
  have zeroAt : a.nr 23 = 0 := (pKeeps 23 (by decide)).trans zero
  have countAt : a.nr 87 = s.nr 87 - 1 := pCount
  have natAt : a.nm = s.nm := pNat
  have ahead : a.nr 23 < a.nr 22 := by rwa [zeroAt, nodeAt]
  obtain ⟨h, header, hLive, oldStart, oldCount, hNat, hReal, hRR, hKeeps⟩ :=
    readMatchingCycleHeader_spec a rfl pLive
  let b := {h with pc := 0}
  have bNat : b.nm = s.nm := hNat.trans natAt
  have bOne : b.nr 9 = 1 := (hKeeps 9 (by decide)).trans ((pKeeps 9 (by decide)).trans one)
  have bZero : b.nr 23 = 0 := (hKeeps 23 (by decide)).trans zeroAt
  have bCount : b.nr 87 = s.nr 87 - 1 := (hKeeps 87 (by decide)).trans countAt
  have bStack : b.nr 80 = s.nr 80 := (hKeeps 80 (by decide)).trans (pKeeps 80 (by decide))
  have bOwner : b.nr 26 = owner := (hKeeps 26 (by decide)).trans ownerAt
  have bStart : b.nr 18 = s.nm (s.nr 77 + node) := by
    change h.nr 18 = _
    rw [oldStart, natAt, nodeAt, show a.nr 77 = s.nr 77 from pKeeps 77 (by decide)]
  have bLength : b.nr 19 = jobs.length := by
    change h.nr 19 = _
    rw [oldCount, natAt, nodeAt, show a.nr 78 = s.nr 78 from pKeeps 78 (by decide), headerCount]
  have room : matchingMemberChildPushCount b jobs.length ≤ b.nr 18 := by
    simpa [matchingMemberChildPushCount, bStack, bCount, bStart] using space
  have rows (i : ℕ) (hi : i < jobs.length) :
      let cell := matchingCycleChildAt b.nm (b.nr 18 + 4 * i)
      (cell.representative, cell.node) = (jobs[i].representative, jobs[i].node) ∧
        jobs[i].owner = (if false then jobs[i].representative else b.nr 26) := by
    simpa [bNat, bStart, bOwner] using read i hi
  obtain ⟨t, ticks, budget, push, result⟩ :=
    pushMatchingMemberChildren_spec false b jobs rfl hLive bOne bZero bLength room rows
  have branch := branchOnAtMost_right 22 23 writeCycleMemberLeaf _ (s := a) rfl pLive ahead (header.append push) result.running
  have run : BlockRuns visitCycleMemberNode (9 + (1 + (4 + ticks))) s _ := pop.append branch
  refine ⟨_, _, by omega, run, result.running, ?_, ?_, ?_, result.real.trans (hReal.trans pReal),
    result.realRegisters.trans (hRR.trans pRR), ?_⟩
  · have out : t.nr 87 = b.nr 87 + jobs.length := result.count
    change t.nr 87 = _
    exact out.trans (congrArg (· + jobs.length) bCount)
  · intro i hi
    change matchingMemberStackWords t.nm _ = _
    simpa [matchingMemberChildPushCount, bStack, bCount] using result.stack i hi hi
  · intro address untouched
    have safe : address < matchingMemberChildPushCount b 0 ∨ matchingMemberChildPushCount b jobs.length ≤ address := by
      simpa [matchingMemberChildPushCount, bStack, bCount] using untouched
    change t.nm address = _
    exact (result.natural address safe).trans (congrFun bNat address)
  · intro r safe
    exact (result.registers r (by simp at safe ⊢; omega)).trans
      ((hKeeps r (by simp at safe ⊢; omega)).trans (pKeeps r (by simp at safe ⊢; omega)))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberVisitRAM

/-! matching/MatchingMemberWalkRAM.lean -/
section RppSource_MatchingMemberWalkRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

/-- Neither the leaf map nor the encoded DFS stack may overlap a live header or record. -/
def outsideMatchingMemberScratch (s : ArithmeticState) (a : ℕ) : Prop :=
  (a < s.nr 79 ∨ s.nr 79 + s.nr 55 ≤ a) ∧ (a < s.nr 80 ∨ s.nr 80 + 3 * s.nr 55 ≤ a)

def matchingMemberJobValid (s : ArithmeticState) (job : MatchingMemberJob) : Prop :=
  job.proper ∧ job.tree.encoded s.nm (s.nr 77) (s.nr 78) ∧
    job.tree.readable s.nm (s.nr 77) (s.nr 78) (outsideMatchingMemberScratch s) ∧
    job.tree.recordsAbove s.nm (s.nr 77) (s.nr 80 + 3 * s.nr 55)

/-- Logical and physical correspondence of a traversal prefix. The encoded stack
is in increasing address order, with the next task at its highest address. -/
structure MatchingMemberWalk (s : ArithmeticState) (assignments done : List (ℕ × ℕ))
    (jobs : List MatchingMemberJob) (i : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  running : m.halted = false
  registers : ∀ r ∈ [9, 55, 77, 78, 79, 80], m.nr r = s.nr r
  zero : m.nr 23 = 0
  index : m.nr 24 = i
  watch : m.nr 28 = 2 * s.nr 55
  count : m.nr 87 = jobs.length
  pending : jobs ≠ [] → i + MatchingMemberJob.work jobs ≤ 2 * s.nr 55
  tasks : ∀ job ∈ jobs, matchingMemberJobValid s job
  remaining : (done ++ MatchingMemberJob.frontier jobs).Perm assignments
  slots : ∀ j (inStack : j < jobs.length),
    matchingMemberStackWords m.nm (s.nr 80 + 3 * j) = matchingMemberJobWords jobs[j]
  placed : ∀ x ∈ done, m.nm (s.nr 79 + x.1) = x.2
  stillEmpty : ∀ v < s.nr 55, v ∉ done.map Prod.fst → m.nm (s.nr 79 + v) = s.nr 55
  natural : ∀ a, outsideMatchingMemberScratch s a → m.nm a = s.nm a

theorem MatchingMemberWalk.stackCapacity {s m : ArithmeticState} {assignments done : List (ℕ × ℕ)}
    {jobs : List MatchingMemberJob} {i : ℕ} (inv : MatchingMemberWalk s assignments done jobs i m)
    (bound : assignments.length ≤ s.nr 55) : jobs.length ≤ s.nr 55 :=
  (MatchingMemberJob.length_le_frontier jobs fun j hj => (inv.tasks j hj).1).trans
    ((MatchingMemberJob.frontier_length_le inv.remaining).trans bound)

def matchingMemberWalkCredit (s : ArithmeticState) (m : ArithmeticState) : ℕ :=
  23 * (2 * s.nr 55 - m.nr 24 - m.nr 87)

private theorem visitMatchingMember_preservesLoopRegisters {s m t : ArithmeticState}
    (one : s.nr 9 = 1) {i : ℕ}
    (atIndex : m.nr 24 = i)
    (registers : ∀ r ∈ [9, 55, 77, 78, 79, 80], m.nr r = s.nr r)
    (keeps : ∀ r ∈ [9, 23, 24, 28, 55, 77, 78, 79, 80], t.nr r = m.nr r) :
    let next := {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)}
    next.nr 24 = i + 1 ∧
      (∀ r ∈ [9, 55, 77, 78, 79, 80], next.nr r = s.nr r) ∧
      next.nr 23 = m.nr 23 ∧ next.nr 28 = m.nr 28 := by
  intro next
  have atOne := (keeps 9 (by decide)).trans ((registers 9 (by decide)).trans one)
  refine ⟨by simp [next, atOne, keeps 24 (by decide), atIndex], ?_, ?_, ?_⟩
  · intro r known
    have safe : r ≠ 24 := by simp at known; omega
    have listed : r ∈ [9, 23, 24, 28, 55, 77, 78, 79, 80] := by simp at known ⊢; omega
    exact (Function.update_of_ne safe _ _).trans ((keeps r listed).trans (registers r known))
  · simpa [next] using keeps 23 (by decide)
  · simpa [next] using keeps 28 (by decide)

theorem matchingMemberJobRows {children : MatchingMemberTree} {owner : Option ℕ}
    {memory : ℕ → ℕ} {start : ℕ}
    (saved : ∀ i (hi : i < children.rootKeys.length),
      let cell := matchingCycleChildAt memory (start + 4 * i)
      MatchingMemberTree.rootKey cell.representative cell.node = children.rootKeys[i]) :
    ∀ i (hi : i < (children.jobs owner).length),
      let cell := matchingCycleChildAt memory (start + 4 * i)
      let job := (children.jobs owner)[i]
      (cell.representative, cell.node) = (job.representative, job.node) ∧
        job.owner = owner.getD job.representative := by
  intro i hi
  have hiKeys : i < children.rootKeys.length := by simpa [children.jobs_length owner] using hi
  have keys := congrArg (fun rows : List (ℕ × ℕ) => rows[i]?) (children.jobs_rootKeys owner)
  have typed : MatchingMemberTree.rootKey (children.jobs owner)[i].representative (children.jobs owner)[i].node =
      children.rootKeys[i] := by
    simpa only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiKeys, Option.map_some,
      Option.some.injEq] using keys
  exact ⟨(saved i hiKeys).trans typed.symm, children.jobs_owner owner _ (List.getElem_mem hi)⟩

private theorem matchingMember_popLeaf {s m : ArithmeticState} {assignments done : List (ℕ × ℕ)}
    {jobs : List MatchingMemberJob} {i : ℕ} {job : MatchingMemberJob}
    (inv : MatchingMemberWalk s assignments done (jobs ++ [job]) i m)
    (one : s.nr 9 = 1) (unique : (assignments.map Prod.fst).Nodup)
    (validLeaves : ∀ p ∈ assignments, p.1 < s.nr 55)
    (separated : s.nr 79 + s.nr 55 ≤ s.nr 80) (singleton : job.children = none) :
    ∃ t, BlockRuns visitCycleMemberNode 13 m t ∧ t.halted = false ∧
      let next := {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)}
      MatchingMemberWalk s assignments ((job.representative, job.owner) :: done) jobs (i+1) next ∧
        matchingMemberWalkCredit s next = matchingMemberWalkCredit s m := by
  let pair := (job.representative, job.owner)
  have appears : job ∈ jobs ++ [job] := by simp
  have isLeaf : job.node = 0 := by simpa [MatchingMemberJob.proper, singleton] using (inv.tasks job appears).1
  have oneAt : m.nr 9 = 1 := (inv.registers 9 (by decide)).trans one
  have count : m.nr 87 = jobs.length + 1 := by simpa using inv.count
  have here : jobs.length < (jobs ++ [job]).length := by simp
  have atTop := inv.slots jobs.length here
  have lastJob : (jobs ++ [job])[jobs.length] = job := by simp
  rw [lastJob] at atTop
  have top : matchingMemberStackWords m.nm (matchingCycleStackAddress m (m.nr 87 - 1)) =
      (job.representative, 0, job.owner) := by
    simpa [matchingCycleStackAddress, inv.registers 80 (by decide), count, matchingMemberJobWords, isLeaf] using atTop
  obtain ⟨t, run, live, popCount, memory, _, _, kept⟩ :=
    visitCycleMemberLeaf_spec m inv.entry inv.running oneAt inv.zero job.representative job.owner top
  have same : ((pair :: done) ++ MatchingMemberJob.frontier jobs).Perm assignments := by
    have reorder : ([pair] ++ (done ++ MatchingMemberJob.frontier jobs)).Perm
        ((done ++ MatchingMemberJob.frontier jobs) ++ [pair]) := List.perm_append_comm
    have oldOrder : (done ++ (MatchingMemberJob.frontier jobs ++ [pair])).Perm assignments := by
      simpa [MatchingMemberJob.frontier_append, MatchingMemberJob.frontier, MatchingMemberJob.assignments,
        singleton, pair, List.append_assoc] using inv.remaining
    exact reorder.trans (by simpa [List.append_assoc] using oldOrder)
  have inLeaves : pair ∈ assignments := same.mem_iff.mp (by simp)
  have leafBound : job.representative < s.nr 55 := validLeaves pair inLeaves
  have noRepeat : job.representative ∉ done.map Prod.fst := by
    have nd := (same.map Prod.fst).nodup_iff.mpr unique
    simp only [List.cons_append, List.map_cons, List.nodup_cons, pair] at nd
    intro h
    apply nd.1
    rw [List.map_append]
    exact List.mem_append_left _ h
  have locality : t.nm = Function.update m.nm (s.nr 79 + job.representative) job.owner := by
    simpa [inv.registers 79 (by decide)] using memory
  have control := visitMatchingMember_preservesLoopRegisters one inv.index inv.registers
    (t := t) (fun r list => kept r (by simp at list ⊢; omega))
  have popped : t.nr 87 = jobs.length := by simpa [count] using popCount
  have remains : i + MatchingMemberJob.work (jobs ++ [job]) ≤ 2 * s.nr 55 := inv.pending (by simp)
  have decreases : MatchingMemberJob.work (jobs ++ [job]) = MatchingMemberJob.work jobs + 1 := by
    rw [MatchingMemberJob.work_append]
    simp [MatchingMemberJob.work, MatchingMemberJob.visits, singleton]
  refine ⟨t, run, live, ⟨rfl, live, control.2.1, control.2.2.1.trans inv.zero, control.1,
    control.2.2.2.trans inv.watch, popped, ?_, ?_, same, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro _
    omega
  · intro nested present
    exact inv.tasks nested (List.mem_append_left _ present)
  · intro j hj
    change matchingMemberStackWords t.nm (s.nr 80 + 3 * j) = _
    have idx : j < (jobs ++ [job]).length := by simp; omega
    have earlier : (jobs ++ [job])[j] = jobs[j] := List.getElem_append_left hj
    have untouched (w : ℕ) : s.nr 80 + 3 * j + w ≠ s.nr 79 + job.representative := by omega
    have first : s.nr 80 + 3 * j ≠ s.nr 79 + job.representative := by omega
    simpa [matchingMemberStackWords, locality, Function.update_of_ne first, Function.update_of_ne (untouched 1),
      Function.update_of_ne (untouched 2), earlier] using inv.slots j idx
  · intro other did
    change t.nm (s.nr 79 + other.1) = other.2
    simp only [List.mem_cons] at did
    rcases did with rfl | old
    · simp [locality, pair]
    · have different : other.1 ≠ job.representative := fun equal =>
        noRepeat (equal ▸ List.mem_map_of_mem (f := Prod.fst) old)
      rw [locality, Function.update_of_ne (by omega : s.nr 79 + other.1 ≠ s.nr 79 + job.representative)]
      exact inv.placed other old
  · intro v bound missing
    change t.nm (s.nr 79 + v) = _
    have old : v ∉ done.map Prod.fst := fun h => missing (by simp [h])
    have different : v ≠ job.representative := fun eq => missing (by simp [eq])
    rw [locality, Function.update_of_ne (by omega : s.nr 79 + v ≠ s.nr 79 + job.representative)]
    exact inv.stillEmpty v bound old
  · intro a safe
    change t.nm a = s.nm a
    have away : a ≠ s.nr 79 + job.representative := by rcases safe.1 with low | high <;> omega
    rw [locality, Function.update_of_ne away]
    exact inv.natural a safe
  · unfold matchingMemberWalkCredit
    have freshIndex := control.1
    have freshCount : ({t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)} : ArithmeticState).nr 87 =
        jobs.length := popped
    rw [freshIndex, freshCount, inv.index, count]
    omega

private theorem matchingMember_expandJob {s m : ArithmeticState} {assignments done : List (ℕ × ℕ)}
    {jobs : List MatchingMemberJob} {i : ℕ} {job : MatchingMemberJob} {children : MatchingMemberTree}
    (inv : MatchingMemberWalk s assignments done (jobs ++ [job]) i m) (one : s.nr 9 = 1)
    (assigned : assignments.length ≤ s.nr 55) (validLeaves : ∀ p ∈ assignments, p.1 < s.nr 55)
    (separated : s.nr 79 + s.nr 55 ≤ s.nr 80)
    (nested : job.children = some children) :
    let pushed := children.jobs (some job.owner)
    ∃ t steps, steps ≤ 23 * pushed.length + 16 ∧ BlockRuns visitCycleMemberNode steps m t ∧
      t.halted = false ∧
      let next := {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)}
      MatchingMemberWalk s assignments done (jobs ++ pushed) (i+1) next ∧
        matchingMemberWalkCredit s next + 23 * pushed.length = matchingMemberWalkCredit s m := by
  intro pushed
  have present : job ∈ jobs ++ [job] := by simp
  obtain ⟨proper, oldEncoding, readable, above⟩ := inv.tasks job present
  rw [MatchingMemberJob.proper, nested] at proper
  obtain ⟨positive, _, validChildren⟩ := proper
  have localEncoding := MatchingMemberTree.encoded_congr oldEncoding readable inv.natural
  rw [MatchingMemberJob.tree, nested] at localEncoding oldEncoding readable above
  obtain ⟨headerCount, storedChildren, _, _⟩ := localEncoding
  obtain ⟨headerSafe, _, _, childReadable, _⟩ := readable
  have higher : s.nr 80 + 3 * s.nr 55 ≤ m.nm (s.nr 77 + job.node) := by
    rw [inv.natural _ headerSafe]
    exact above.1
  have same : (done ++ MatchingMemberJob.frontier (jobs ++ pushed)).Perm assignments := by
    rw [show MatchingMemberJob.frontier (jobs ++ pushed) = MatchingMemberJob.frontier (jobs ++ [job]) from
      MatchingMemberJob.appendChildren_frontier jobs job children nested]
    exact inv.remaining
  have correct (j : MatchingMemberJob) (found : j ∈ jobs ++ pushed) : matchingMemberJobValid s j := by
    rcases List.mem_append.mp found with prior | new
    · exact inv.tasks j (List.mem_append_left _ prior)
    · exact ⟨children.jobs_proper (some job.owner) validChildren j new,
        children.jobs_encoded (some job.owner) s.nm (s.nr 77) (s.nr 78) (s.nr 80 + 3 * s.nr 55)
          (outsideMatchingMemberScratch s) oldEncoding.2.2.1 childReadable above.2.1 j new⟩
  have capacity : jobs.length + pushed.length ≤ s.nr 55 := by
    simpa only [List.length_append] using (MatchingMemberJob.length_le_frontier (jobs ++ pushed)
      (fun j there => (correct j there).1)).trans ((MatchingMemberJob.frontier_length_le same).trans assigned)
  have count : m.nr 87 = jobs.length + 1 := by simpa using inv.count
  have atTop := inv.slots jobs.length (by simp)
  have lastJob : (jobs ++ [job])[jobs.length] = job := by simp
  rw [lastJob] at atTop
  have top : matchingMemberStackWords m.nm (matchingCycleStackAddress m (m.nr 87 - 1)) =
      (job.representative, job.node, job.owner) := by
    simpa [matchingCycleStackAddress, inv.registers 80 (by decide), count, matchingMemberJobWords] using atTop
  have room : m.nr 80 + 3 * (m.nr 87 - 1 + pushed.length) ≤ m.nm (m.nr 77 + job.node) := by
    rw [inv.registers 77 (by decide), inv.registers 80 (by decide), count]
    omega
  have size : m.nm (m.nr 78 + job.node) = pushed.length := by
    rw [inv.registers 78 (by decide), headerCount]
    exact (children.jobs_length _).symm
  have rows (j : ℕ) (hj : j < pushed.length) :
      let cell := matchingCycleChildAt m.nm (m.nm (m.nr 77 + job.node) + 4 * j)
      (cell.representative, cell.node) = (pushed[j].representative, pushed[j].node) ∧ pushed[j].owner = job.owner := by
    have matchingRows := matchingMemberJobRows (owner := some job.owner) storedChildren j hj
    simpa [inv.registers 77 (by decide), pushed] using matchingRows
  obtain ⟨t, steps, cost, run, live, appended, written, effect, _, _, kept⟩ :=
    visitCycleMemberBlossom_spec m inv.entry inv.running ((inv.registers 9 (by decide)).trans one)
      inv.zero job.representative job.node job.owner positive pushed top size room rows
  have control := visitMatchingMember_preservesLoopRegisters one inv.index inv.registers
    (t := t) (fun r list => kept r (by simp at list ⊢; omega))
  have grew : t.nr 87 = jobs.length + pushed.length := by simpa only [count, Nat.add_sub_cancel] using appended
  have unchanged (a : ℕ) (there : a < s.nr 80 + 3 * jobs.length ∨ s.nr 80 + 3 * (jobs.length + pushed.length) ≤ a) :
      t.nm a = m.nm a := effect a (by simpa [count, inv.registers 80 (by decide)] using there)
  have potential := inv.pending (by simp)
  have visited := MatchingMemberJob.appendChildren_work jobs job children nested
  have still : (i + 1) + MatchingMemberJob.work (jobs ++ pushed) ≤ 2 * s.nr 55 := by
    change MatchingMemberJob.work (jobs ++ pushed) + 1 = _ at visited
    omega
  have workGe := MatchingMemberJob.length_le_work (jobs ++ pushed)
  have physicalBudget : (i + 1) + jobs.length + pushed.length ≤ 2 * s.nr 55 := by
    simp only [List.length_append] at workGe
    omega
  refine ⟨t, steps, cost, run, live, ⟨rfl, live, control.2.1, control.2.2.1.trans inv.zero, control.1,
    control.2.2.2.trans inv.watch, by simpa using grew, fun _ => still, correct, same, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j hj
    change matchingMemberStackWords t.nm (s.nr 80 + 3 * j) = _
    by_cases earlier : j < jobs.length
    · have old : j < (jobs ++ [job]).length := by simp; omega
      have readBefore := inv.slots j old
      rw [List.getElem_append_left earlier] at readBefore ⊢
      have safe (w : ℕ) (word : w < 3) : t.nm (s.nr 80 + 3 * j + w) = m.nm (s.nr 80 + 3 * j + w) :=
        unchanged _ (.inl (by omega))
      have first := safe 0 (by decide)
      simp only [Nat.add_zero] at first
      simpa only [matchingMemberStackWords, first, safe 1 (by decide), safe 2 (by decide)] using readBefore
    · have past : jobs.length ≤ j := Nat.le_of_not_gt earlier
      have index : j - jobs.length < pushed.length := by simp at hj; omega
      have loc : jobs.length + (j - jobs.length) = j := by omega
      rw [List.getElem_append_right past]
      simpa [inv.registers 80 (by decide), count, loc] using written (j - jobs.length) index
  · intro x hx
    change t.nm (s.nr 79 + x.1) = x.2
    have inAll : x ∈ assignments := same.mem_iff.mp (List.mem_append_left _ hx)
    have outside : s.nr 79 + x.1 < s.nr 80 + 3 * jobs.length := by
      have xBound := validLeaves x inAll
      omega
    exact (unchanged _ (.inl outside)).trans (inv.placed x hx)
  · intro v bound untouched
    change t.nm (s.nr 79 + v) = _
    exact (unchanged _ (.inl (by omega))).trans (inv.stillEmpty v bound untouched)
  · intro a safe
    change t.nm a = s.nm a
    exact (unchanged _ (by rcases safe.2 with before | after <;> omega)).trans (inv.natural a safe)
  · unfold matchingMemberWalkCredit
    have tIndex := control.1
    have tCount : ({t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)} : ArithmeticState).nr 87 =
        jobs.length + pushed.length := grew
    rw [tIndex, tCount, inv.index, count]
    omega

theorem matchingMemberWalk_loop {s start : ArithmeticState} {assignments : List (ℕ × ℕ)}
    (one : s.nr 9 = 1) (unique : (assignments.map Prod.fst).Nodup)
    (validLeaves : ∀ p ∈ assignments, p.1 < s.nr 55)
    (separated : s.nr 79 + s.nr 55 ≤ s.nr 80)
    (entry : start.pc = 0) (running : start.halted = false)
    {initial : List MatchingMemberJob}
    (initialState : MatchingMemberWalk s assignments [] initial 0
      {start with pc := 0, nr := Function.update start.nr 24 0}) :
    ∃ t steps, steps ≤ 42 * s.nr 55 + 23 * (2 * s.nr 55 - initial.length) + 2 ∧
      BlockRuns (countedLoopFromZero 9 24 28 (branchOnUnequal 87 23 visitCycleMemberNode)) steps start t ∧
      t.halted = false ∧ t.nr 87 = 0 ∧ t.nr 23 = 0 ∧
      (∀ p ∈ assignments, t.nm (s.nr 79 + p.1) = p.2) ∧
      (∀ v < s.nr 55, v ∉ assignments.map Prod.fst → t.nm (s.nr 79 + v) = s.nr 55) ∧
      ∀ a, outsideMatchingMemberScratch s a → t.nm a = s.nm a := by
  let inv (i : ℕ) (m : ArithmeticState) := ∃ done jobs, MatchingMemberWalk s assignments done jobs i m
  have assigned := MatchingMemberJob.boundedAssignments_length assignments (s.nr 55) unique validLeaves
  let body := branchOnUnequal 87 23 visitCycleMemberNode
  have step : ∀ i < 2 * s.nr 55, ∀ m, inv i m → ∃ t steps,
      let next := {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)}
      BlockRuns body steps m t ∧ t.halted = false ∧ inv (i + 1) next ∧
        steps + matchingMemberWalkCredit s next ≤ 18 + matchingMemberWalkCredit s m := by
    intro i hi m hm
    obtain ⟨done, jobs, walk⟩ := hm
    cases reverse : jobs.reverse with
    | nil =>
      have empty : jobs = [] := List.reverse_eq_nil_iff.mp reverse
      subst jobs
      have count : m.nr 87 = 0 := walk.count
      have skip := branchOnUnequal_skip 87 23 visitCycleMemberNode m walk.entry walk.running (count.trans walk.zero.symm)
      let t := {m with pc := body.length}
      have run : BlockRuns body 2 m t := skip
      have keeps (r : ℕ) (_ : r ∈ [9, 23, 24, 28, 55, 77, 78, 79, 80]) : t.nr r = m.nr r := rfl
      have ctl := visitMatchingMember_preservesLoopRegisters one walk.index walk.registers keeps
      refine ⟨t, 2, run, walk.running, ⟨done, [], rfl, walk.running, ctl.2.1, ctl.2.2.1.trans walk.zero,
        ctl.1, ctl.2.2.2.trans walk.watch, count, by simp, by simp, walk.remaining, by simp, walk.placed,
        walk.stillEmpty, walk.natural⟩, ?_⟩
      change 2 + 23 * (2 * s.nr 55 - (m.nr 24 + m.nr 9) - m.nr 87) ≤
        18 + 23 * (2 * s.nr 55 - m.nr 24 - m.nr 87)
      rw [walk.index, count, (walk.registers 9 (by decide)).trans one]
      omega
    | cons job earlierReversed =>
      have decomposed : jobs = earlierReversed.reverse ++ [job] := by
        have unfoldReverse := congrArg List.reverse reverse
        simpa only [List.reverse_reverse, List.reverse_cons] using unfoldReverse
      subst jobs
      have unequal : m.nr 87 ≠ m.nr 23 := by simp [walk.count, walk.zero]
      cases subtree : job.children with
      | none =>
        obtain ⟨t, run, live, after, cost⟩ := matchingMember_popLeaf walk one unique validLeaves separated subtree
        have visited := branchOnUnequal_take 87 23 visitCycleMemberNode walk.entry walk.running unequal run
        refine ⟨_, 2 + 13, visited, live, ⟨_, _, after⟩, ?_⟩
        change 2 + 13 + matchingMemberWalkCredit s {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)} ≤
          18 + matchingMemberWalkCredit s m
        rw [cost]
        omega
      | some children =>
        obtain ⟨t, ticks, bound, run, live, after, cost⟩ :=
          matchingMember_expandJob walk one assigned validLeaves separated subtree
        have visited := branchOnUnequal_take 87 23 visitCycleMemberNode walk.entry walk.running unequal run
        refine ⟨_, 2 + ticks, visited, live, ⟨_, _, after⟩, ?_⟩
        change 2 + ticks + matchingMemberWalkCredit s {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)} ≤
          18 + matchingMemberWalkCredit s m
        omega
  obtain ⟨last, steps, stopped, bound, run⟩ := countedLoopFromZero_amortized 9 24 28 (2 * s.nr 55) 18 body
    inv (matchingMemberWalkCredit s) (s := start) entry running ⟨[], initial, initialState⟩
    (fun _ _ ⟨_, _, w⟩ => ⟨w.entry, w.running, w.index, w.watch⟩) step
  obtain ⟨done, pending, final⟩ := stopped
  have empty : pending = [] := by
    by_contra present
    have total := final.pending present
    have nonzero : 0 < pending.length := by
      by_contra h
      exact present (List.eq_nil_of_length_eq_zero (by omega))
    have work := MatchingMemberJob.length_le_work pending
    omega
  subst pending
  have placed : done.Perm assignments := by simpa [MatchingMemberJob.frontier] using final.remaining
  have seededCredit : matchingMemberWalkCredit s {start with pc := 0, nr := Function.update start.nr 24 0} =
      23 * (2 * s.nr 55 - initial.length) := by
    unfold matchingMemberWalkCredit
    rw [initialState.index, initialState.count]
    omega
  refine ⟨_, steps, ?_, run, final.running, final.count, final.zero, ?_, ?_, final.natural⟩
  · rw [seededCredit] at bound
    omega
  · intro p present
    exact final.placed p (placed.mem_iff.mpr present)
  · intro v below missing
    exact final.stillEmpty v below (fun seen => missing ((placed.map Prod.fst).mem_iff.mp seen))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberWalkRAM

/-! matching/MatchingMemberMapRAM.lean -/
section RppSource_MatchingMemberMapRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

/-- The registry entry in register 22 denotes an actual nontrivial live blossom.
The finite subtree identifies all original leaves, their immediate-child owners,
and the immutable cycle data needed to reach them. -/
structure MatchingMemberRoot (s : ArithmeticState) (children : MatchingMemberTree) : Prop where
  proper : (MatchingMemberTree.blossom 0 (s.nr 22) children .nil).proper
  encoded : (MatchingMemberTree.blossom 0 (s.nr 22) children .nil).encoded s.nm (s.nr 77) (s.nr 78)
  readable : (MatchingMemberTree.blossom 0 (s.nr 22) children .nil).readable s.nm (s.nr 77) (s.nr 78)
    (outsideMatchingMemberScratch s)
  above : (MatchingMemberTree.blossom 0 (s.nr 22) children .nil).recordsAbove s.nm (s.nr 77)
    (s.nr 80 + 3 * s.nr 55)
  unique : children.leaves.Nodup
  valid : ∀ v ∈ children.leaves, v < s.nr 55
  separated : s.nr 79 + s.nr 55 ≤ s.nr 80

def matchingMemberAssignments (children : MatchingMemberTree) : List (ℕ × ℕ) :=
  MatchingMemberJob.frontier (children.jobs none)

/-- The actual DFS produces the immediate-child representative for every leaf,
leaves the sentinel on other originals, and confines natural writes to its map
and traversal stack. Work is linear in the compact original-vertex dimension. -/
theorem mapMatchingCycleNodeMembers_spec (s : ArithmeticState) (children : MatchingMemberTree)
    (root : MatchingMemberRoot s children) (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ 93 * s.nr 55 + 13 ∧ BlockRuns mapMatchingCycleNodeMembers steps s t ∧
      t.halted = false ∧ t.nr 87 = 0 ∧ t.nr 23 = 0 ∧
      (∀ p ∈ matchingMemberAssignments children, t.nm (s.nr 79 + p.1) = p.2) ∧
      (∀ v < s.nr 55, v ∉ children.leaves → t.nm (s.nr 79 + v) = s.nr 55) ∧
      (∀ a, outsideMatchingMemberScratch s a → t.nm a = s.nm a) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 7, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 28, 87] → t.nr r = s.nr r := by
  let seedCode : List ArithmeticInstruction := [.natConst 23 0, .natConst 87 0, .natAdd 28 55 55]
  let seeded := { s with
    pc := 3
    nr := Function.update (Function.update (Function.update s.nr 23 0) 87 0) 28 (2 * s.nr 55) }
  have seed : BlockRuns seedCode 3 s seeded := by
    apply BlockRuns.of_running_exit
    · have twice : s.nr 55 + s.nr 55 = 2 * s.nr 55 := by omega
      simp [seedCode, seeded, entry, running, arithmeticStep, twice, Function.iterate_succ_apply']
    · exact running
    · rfl
  have frameSeed (r : ℕ) (safe : r ∉ [23, 28, 87]) : seeded.nr r = s.nr r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at safe
    obtain ⟨a, b, c⟩ := safe
    simp [seeded, Function.update_of_ne a, Function.update_of_ne b, Function.update_of_ne c]
  let a := {seeded with pc := 0}
  have aOne : a.nr 9 = 1 := (frameSeed 9 (by decide)).trans one
  have aSize : a.nr 55 = s.nr 55 := frameSeed 55 (by decide)
  have aMap : a.nr 79 = s.nr 79 := frameSeed 79 (by decide)
  have aNat : a.nm = s.nm := rfl
  obtain ⟨cleared, clearTicks, clearCost, clear, clearLive, clearedMap, _, _, clearFrame⟩ :=
    clearCycleMemberMap_spec a rfl running aOne
  let b := {cleared with pc := 0}
  have clearedOutside (x : ℕ) (safe : x < s.nr 79 ∨ s.nr 79 + s.nr 55 ≤ x) : b.nm x = s.nm x := by
    have away : ¬(s.nr 79 ≤ x ∧ x < s.nr 79 + s.nr 55) := by omega
    exact (clearedMap x).trans (by simp [aMap, aSize, away, aNat])
  have clearedLeaves (v : ℕ) (inside : v < s.nr 55) : b.nm (s.nr 79 + v) = s.nr 55 := by
    have used : s.nr 79 ≤ s.nr 79 + v ∧ s.nr 79 + v < s.nr 79 + s.nr 55 := by omega
    exact (clearedMap (s.nr 79 + v)).trans (by simp [aMap, aSize, used])
  have bFrame (r : ℕ) (safe : r ∉ [0, 6, 7]) : b.nr r = seeded.nr r := clearFrame r safe
  obtain ⟨header, read, headerLive, headerStart, headerLength, headerNat, _, _, headerFrame⟩ :=
    readMatchingCycleHeader_spec b rfl clearLive
  let c := {header with pc := 0}
  have fromSeed (r : ℕ) (safe : r ∉ [0, 6, 7, 18, 19]) : c.nr r = seeded.nr r :=
    (headerFrame r (by simp at safe ⊢; omega)).trans (bFrame r (by simp at safe ⊢; omega))
  have cOne : c.nr 9 = 1 := (fromSeed 9 (by decide)).trans aOne
  have cZero : c.nr 23 = 0 := (fromSeed 23 (by decide)).trans (by simp [seeded])
  have cStack : c.nr 80 = s.nr 80 := (fromSeed 80 (by decide)).trans (frameSeed 80 (by decide))
  have cCount : c.nr 87 = 0 := (fromSeed 87 (by decide)).trans (by simp [seeded])
  have cNat : c.nm = b.nm := headerNat
  have bStartBase : b.nr 77 = s.nr 77 := (bFrame 77 (by decide)).trans (frameSeed 77 (by decide))
  have bCountBase : b.nr 78 = s.nr 78 := (bFrame 78 (by decide)).trans (frameSeed 78 (by decide))
  have node : b.nr 22 = s.nr 22 := (bFrame 22 (by decide)).trans (frameSeed 22 (by decide))
  have ready := MatchingMemberTree.encoded_congr root.encoded root.readable (fun addr safe => clearedOutside addr safe.1)
  let jobs := children.jobs none
  let assignments := matchingMemberAssignments children
  have vertices : assignments.map Prod.fst = children.leaves := children.jobs_frontier_vertices none
  have unique : (assignments.map Prod.fst).Nodup := vertices.symm ▸ root.unique
  have inside (p : ℕ × ℕ) (present : p ∈ assignments) : p.1 < s.nr 55 := by
    apply root.valid
    rw [← vertices]
    exact List.mem_map_of_mem (f := Prod.fst) present
  have typedJobs (j : MatchingMemberJob) (present : j ∈ jobs) : matchingMemberJobValid s j :=
    ⟨children.jobs_proper none root.proper.2.2.1 j present,
      children.jobs_encoded none s.nm (s.nr 77) (s.nr 78) (s.nr 80 + 3 * s.nr 55)
        (outsideMatchingMemberScratch s) root.encoded.2.2.1 root.readable.2.2.2.1 root.above.2.1 j present⟩
  have capacity : jobs.length ≤ s.nr 55 :=
    (MatchingMemberJob.length_le_frontier jobs (fun j hj => (typedJobs j hj).1)).trans
      (MatchingMemberJob.boundedAssignments_length assignments (s.nr 55) unique inside)
  have cStart : c.nr 18 = b.nm (s.nr 77 + s.nr 22) := by
    change header.nr 18 = _
    rw [headerStart, bStartBase, node]
  have cLength : c.nr 19 = jobs.length := by
    change header.nr 19 = _
    rw [headerLength, bCountBase, node, ready.1, children.jobs_length none]
  have room : matchingMemberChildPushCount c jobs.length ≤ c.nr 18 := by
    rw [matchingMemberChildPushCount, cStack, cCount, cStart, clearedOutside _ root.readable.1.1]
    have dynamic := root.above.1
    omega
  have rows (j : ℕ) (hj : j < jobs.length) :
      let row := matchingCycleChildAt c.nm (c.nr 18 + 4 * j)
      (row.representative, row.node) = (jobs[j].representative, jobs[j].node) ∧
        jobs[j].owner = (if true then jobs[j].representative else c.nr 26) := by
    simpa [cStart, cNat, jobs] using matchingMemberJobRows (owner := none) ready.2.1 j hj
  obtain ⟨prepared, pushTicks, pushCost, push, pushed⟩ :=
    pushMatchingMemberChildren_spec true c jobs rfl headerLive cOne cZero cLength room rows
  let start := {prepared with pc := 0}
  have startMove (r : ℕ) (safe : r ∉ [0, 6, 7, 15, 16, 17, 18, 19, 25, 26, 87]) :
      start.nr r = seeded.nr r :=
    (pushed.registers r (by simp at safe ⊢; omega)).trans (fromSeed r (by simp at safe ⊢; omega))
  have sameEarlier (addr : ℕ) (outside : addr < s.nr 80 ∨ s.nr 80 + 3 * jobs.length ≤ addr) :
      start.nm addr = b.nm addr :=
    (pushed.natural addr (by simpa [matchingMemberChildPushCount, cStack, cCount] using outside)).trans (congrFun cNat addr)
  have initial : MatchingMemberWalk s assignments [] jobs 0 {start with pc := 0, nr := Function.update start.nr 24 0} := by
    refine ⟨rfl, pushed.running, ?_, ?_, by simp, ?_, ?_, ?_, typedJobs, .refl _, ?_, by simp, ?_, ?_⟩
    · intro r inList
      have no : r ≠ 24 := by simp at inList; omega
      exact (Function.update_of_ne no _ _).trans ((startMove r (by simp at inList ⊢; omega)).trans
        (frameSeed r (by simp at inList ⊢; omega)))
    · have zero := (startMove 23 (by decide)).trans (show seeded.nr 23 = 0 by simp [seeded])
      simpa [start] using zero
    · have watch := (startMove 28 (by decide)).trans (show seeded.nr 28 = 2 * s.nr 55 by simp [seeded])
      simpa [start] using watch
    · change start.nr 87 = jobs.length
      exact pushed.count.trans (by rw [cCount, Nat.zero_add])
    · intro _
      rw [Nat.zero_add, children.jobs_work none]
      have treeBound := children.nodes_add_arity_le root.proper.2.2.1
      have leafCount : children.leaves.length = assignments.length := by rw [← vertices, List.length_map]
      have card := MatchingMemberJob.boundedAssignments_length assignments (s.nr 55) unique inside
      omega
    · intro j hj
      change matchingMemberStackWords start.nm _ = _
      simpa [matchingMemberChildPushCount, cStack, cCount] using pushed.stack j hj hj
    · intro v bound _
      exact (sameEarlier _ (.inl (by have sep := root.separated; omega))).trans (clearedLeaves v bound)
    · intro address safe
      exact (sameEarlier address (by rcases safe.2 with low | high <;> omega)).trans (clearedOutside address safe.1)
  obtain ⟨t, walkTicks, walkCost, walk, runningNow, empty, zero, values, sentinel, preserved⟩ :=
    matchingMemberWalk_loop one unique inside root.separated rfl pushed.running initial
  have run : BlockRuns mapMatchingCycleNodeMembers (3 + (clearTicks + (4 + (pushTicks + walkTicks)))) s _ :=
    seed.append (clear.append (read.append (push.append walk)))
  have cost : 3 + (clearTicks + (4 + (pushTicks + walkTicks))) ≤ 93 * s.nr 55 + 13 := by
    rw [aSize] at clearCost
    omega
  have reals := mapMatchingCycleNodeMembers_keeps_reals run
  refine ⟨_, _, cost, run, runningNow, empty, zero, values, ?_, preserved, reals.2, reals.1, ?_⟩
  · intro v bound outside
    exact sentinel v bound (by rwa [vertices])
  · intro r safe
    exact mapMatchingCycleNodeMembers_keeps_register run safe

end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberMapRAM

/-! matching/MatchingMemberTopRAM.lean -/
section RppSource_MatchingMemberTopRAM
namespace VehicleRoutingSurvey.Routing

def topMatchingMemberNodeInput (s : ArithmeticState) : ArithmeticState :=
  let address := s.nr 74 + s.nr 97
  {s with pc := 0, nr := Function.update (Function.update s.nr 6 address) 22 (s.nm address)}

/-- Entry point used by blossom expansion. The selected top representative names
its node in the registry table, then the same verified traversal runs unchanged. -/
theorem mapMatchingCycleMembers_spec (s : ArithmeticState) (children : MatchingMemberTree)
    (root : MatchingMemberRoot (topMatchingMemberNodeInput s) children) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ 93 * s.nr 55 + 15 ∧ BlockRuns mapMatchingCycleMembers steps s t ∧
      t.halted = false ∧ t.nr 87 = 0 ∧ t.nr 23 = 0 ∧
      (∀ p ∈ matchingMemberAssignments children, t.nm (s.nr 79 + p.1) = p.2) ∧
      (∀ v < s.nr 55, v ∉ children.leaves → t.nm (s.nr 79 + v) = s.nr 55) ∧
      (∀ a, outsideMatchingMemberScratch s a → t.nm a = s.nm a) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 7, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 28, 87] → t.nr r = s.nr r := by
  let input := topMatchingMemberNodeInput s
  let loaded := {input with pc := 2}
  have load : BlockRuns [.natAdd 6 74 97, .natLoad 22 6] 2 s loaded := by
    apply BlockRuns.of_running_exit
    · simp [loaded, input, topMatchingMemberNodeInput, arithmeticStep, entry, running, Function.iterate_succ_apply']
    · exact running
    · rfl
  have unchanged (r : ℕ) (six : r ≠ 6 := by decide) (node : r ≠ 22 := by decide) : input.nr r = s.nr r := by
    simp [input, topMatchingMemberNodeInput, Function.update_of_ne six, Function.update_of_ne node]
  obtain ⟨t, steps, bound, scan, live, count, zero, assignments, absent, natural, reals, registers, kept⟩ :=
    mapMatchingCycleNodeMembers_spec input children root rfl running ((unchanged 9).trans one)
  have budget : 2 + steps ≤ 93 * s.nr 55 + 15 := by rw [unchanged 55] at bound; omega
  refine ⟨_, 2 + steps, budget, load.append scan, live, count, zero, ?_, ?_, ?_, reals, registers, ?_⟩
  · intro p assigned
    change t.nm (s.nr 79 + p.1) = p.2
    simpa only [unchanged 79] using assignments p assigned
  · intro v below missing
    change t.nm (s.nr 79 + v) = s.nr 55
    simpa only [unchanged 79, unchanged 55] using absent v (by rwa [unchanged 55]) missing
  · intro a untouched
    exact natural a (by simpa only [outsideMatchingMemberScratch, unchanged 79, unchanged 80, unchanged 55] using untouched)
  · intro r safe
    exact (kept r safe).trans (unchanged r (by simp at safe; omega) (by simp at safe; omega))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberTopRAM

/-! matching/MatchingExpansionDirectionRAM.lean -/
section RppSource_MatchingExpansionDirectionRAM
namespace VehicleRoutingSurvey.Routing

private def halveExpansionDistanceCell : List ArithmeticInstruction :=
  [.natBranch 49 47 1 4, .natSub 47 47 49, .natAdd 95 95 9, .jump 4]

private theorem halveExpansionDistanceCell_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (two : s.nr 49 = 2) :
    ∃ t ticks, ticks ≤ 4 ∧ BlockRuns halveExpansionDistanceCell ticks s t ∧ t.halted = false ∧
      t.nr 47 = (if 2 ≤ s.nr 47 then s.nr 47 - 2 else s.nr 47) ∧
      t.nr 95 = s.nr 95 + (if 2 ≤ s.nr 47 then 1 else 0) ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
  by_cases more : 2 ≤ s.nr 47
  · let t := (arithmeticStep halveExpansionDistanceCell)^[4] s
    have result : t.pc = halveExpansionDistanceCell.length ∧ t.halted = false ∧
        t.nr 47 = (if 2 ≤ s.nr 47 then s.nr 47 - 2 else s.nr 47) ∧
        t.nr 95 = s.nr 95 + (if 2 ≤ s.nr 47 then 1 else 0) ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
      simp [t, halveExpansionDistanceCell, arithmeticStep, entry, running, one, two, more, Function.iterate_succ_apply']
    exact ⟨t, 4, le_rfl, BlockRuns.of_running_exit rfl result.2.1 result.1, result.2⟩
  · let t := arithmeticStep halveExpansionDistanceCell s
    have result : t.pc = halveExpansionDistanceCell.length ∧ t.halted = false ∧
        t.nr 47 = (if 2 ≤ s.nr 47 then s.nr 47 - 2 else s.nr 47) ∧
        t.nr 95 = s.nr 95 + (if 2 ≤ s.nr 47 then 1 else 0) ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
      simp [t, halveExpansionDistanceCell, arithmeticStep, entry, running, two, more]
    exact ⟨t, 1, by decide, BlockRuns.of_running_exit rfl result.2.1 result.1, result.2⟩

private def initializeExpansionHalving : List ArithmeticInstruction :=
  [.natConst 49 2, .natAdd 47 46 23, .natConst 95 0]

/-- Compute quotient and remainder by two on a path length bounded by the compact
dimension. The real RAM has addition and subtraction on natural registers. -/
def halveExpansionDistance : List ArithmeticInstruction :=
  appendBlock initializeExpansionHalving (countedLoopFromZero 9 24 55 halveExpansionDistanceCell)

private structure ExpansionHalving (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 24 = i
  registeredTwo : s.nr 49 = 2
  preserved : ∀ r, r ∉ [0, 24, 47, 49, 95] → s.nr r = initial.nr r
  balance : s.nr 47 + 2 * s.nr 95 = initial.nr 46
  progress : 2 ≤ s.nr 47 → i ≤ s.nr 95
  natural : s.nm = initial.nm
  real : s.rm = initial.rm
  realRegisters : s.rr = initial.rr

theorem halveExpansionDistance_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0)
    (bounded : s.nr 46 ≤ s.nr 55) :
    ∃ t steps, steps ≤ 7 * s.nr 55 + 5 ∧ BlockRuns halveExpansionDistance steps s t ∧ t.halted = false ∧
      t.nr 47 + 2 * t.nr 95 = s.nr 46 ∧ t.nr 47 ≤ 1 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 24, 47, 49, 95] → t.nr r = s.nr r := by
  let seeded := { s with
    pc := 3
    nr := Function.update (Function.update (Function.update s.nr 49 2) 47 (s.nr 46)) 95 0 }
  have seed : BlockRuns initializeExpansionHalving 3 s seeded := by
    apply BlockRuns.of_running_exit
    · simp [seeded, initializeExpansionHalving, arithmeticStep, entry, running, zero, Function.iterate_succ_apply']
    · exact running
    · rfl
  let start := {seeded with pc := 0}
  have init : ExpansionHalving s 0 {start with pc := 0, nr := Function.update start.nr 24 0} := by
    refine ⟨rfl, running, by simp, by simp [start, seeded], ?_, by simp [start, seeded], ?_, rfl, rfl, rfl⟩
    · intro r outside
      have a : r ≠ 24 := by simp at outside; omega
      have b : r ≠ 47 := by simp at outside; omega
      have c : r ≠ 49 := by simp at outside; omega
      have d : r ≠ 95 := by simp at outside; omega
      simp [start, seeded, Function.update_of_ne a, Function.update_of_ne b, Function.update_of_ne c, Function.update_of_ne d]
    · intro _
      exact Nat.zero_le _
  have iteration (i : ℕ) (_ : i < s.nr 55) (m : ArithmeticState) (before : ExpansionHalving s i m) :
      ∃ t ticks, ticks ≤ 4 ∧ BlockRuns halveExpansionDistanceCell ticks m t ∧ t.halted = false ∧
        ExpansionHalving s (i + 1) {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)} := by
    have mOne : m.nr 9 = 1 := (before.preserved 9 (by decide)).trans one
    obtain ⟨t, ticks, cost, run, live, residual, count, natural, real, regs⟩ :=
      halveExpansionDistanceCell_spec m before.entry before.running mOne before.registeredTwo
    have keeps (r : ℕ) (outside : r ∉ [0, 47, 95]) : t.nr r = m.nr r := by
      rw [← run.run]
      exact arithmeticRun_keeps_from_destination_list [0, 47, 95] (by decide) outside m ticks
    refine ⟨t, ticks, cost, run, live, rfl, live, ?_, ?_, ?_, ?_, ?_, natural.trans before.natural,
      real.trans before.real, regs.trans before.realRegisters⟩
    · simp [keeps 24 (by decide), keeps 9 (by decide), before.index, mOne]
    · exact (keeps 49 (by decide)).trans before.registeredTwo
    · intro r outside
      have a : r ≠ 24 := by simp at outside; omega
      have b : r ∉ [0, 47, 95] := by simp at outside ⊢; omega
      exact (Function.update_of_ne a _ _).trans ((keeps r b).trans (before.preserved r outside))
    · change t.nr 47 + 2 * t.nr 95 = s.nr 46
      rw [residual, count]
      by_cases more : 2 ≤ m.nr 47 <;> simp [more] <;> have h := before.balance <;> omega
    · change 2 ≤ t.nr 47 → i + 1 ≤ t.nr 95
      rw [residual, count]
      by_cases more : 2 ≤ m.nr 47
      · have prev := before.progress more
        simp [more] <;> omega
      · simp [more]
  obtain ⟨last, ticks, done, cost, complete⟩ := countedLoopFromZero_bounded 9 24 55 (s.nr 55) 4
    halveExpansionDistanceCell (ExpansionHalving s) (s := start) rfl running init
    (fun _ _ h => ⟨h.entry, h.running, h.index, h.preserved 55 (by decide)⟩) iteration
  have small : last.nr 47 ≤ 1 := by
    by_contra big
    have more : 2 ≤ last.nr 47 := by omega
    have count := done.progress more
    have balance := done.balance
    omega
  exact ⟨_, 3 + ticks, by omega, seed.append complete, done.running, done.balance, small, done.natural, done.real,
    done.realRegisters, done.preserved⟩

private def chooseForwardExpansionDistance : List ArithmeticInstruction :=
  branchOnAtMost 81 82 [.natSub 46 82 81] [.natSub 6 81 82, .natSub 46 19 6]

def expansionForwardDistance (s : ArithmeticState) : ℕ :=
  if s.nr 81 ≤ s.nr 82 then s.nr 82 - s.nr 81 else s.nr 19 - (s.nr 81 - s.nr 82)

private theorem chooseForwardExpansionDistance_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    ∃ t, BlockRuns chooseForwardExpansionDistance 3 s t ∧ t.halted = false ∧
      t.nr 46 = expansionForwardDistance s ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 46] → t.nr r = s.nr r := by
  have fixed {t : ArithmeticState} (run : BlockRuns chooseForwardExpansionDistance 3 s t)
      (r : ℕ) (outside : r ∉ [0, 6, 46]) : t.nr r = s.nr r := by
    rw [← run.run]
    exact arithmeticRun_keeps_from_destination_list [0, 6, 46] (by decide) outside s 3
  by_cases forward : s.nr 81 ≤ s.nr 82
  · let t := {s with pc := 1, nr := Function.update s.nr 46 (s.nr 82 - s.nr 81)}
    have run : BlockRuns [.natSub 46 82 81] 1 s t := by
      apply BlockRuns.of_running_exit
      · simp [t, arithmeticStep, entry, running]
      · exact running
      · rfl
    have routed := branchOnAtMost_left 81 82 [.natSub 46 82 81] [.natSub 6 81 82, .natSub 46 19 6]
      entry running forward run running
    refine ⟨_, routed, running, ?_, rfl, rfl, rfl, fixed routed⟩
    change t.nr 46 = expansionForwardDistance s
    simp [t, expansionForwardDistance, forward]
  · let t := { s with
      pc := 2
      nr := Function.update (Function.update s.nr 6 (s.nr 81 - s.nr 82)) 46 (s.nr 19 - (s.nr 81 - s.nr 82)) }
    have run : BlockRuns [.natSub 6 81 82, .natSub 46 19 6] 2 s t := by
      apply BlockRuns.of_running_exit
      · simp [t, arithmeticStep, entry, running, Function.iterate_succ_apply']
      · exact running
      · rfl
    have routed := branchOnAtMost_right 81 82 [.natSub 46 82 81] [.natSub 6 81 82, .natSub 46 19 6]
      entry running (Nat.lt_of_not_ge forward) run running
    refine ⟨_, routed, running, ?_, rfl, rfl, rfl, fixed routed⟩
    change t.nr 46 = expansionForwardDistance s
    simp [t, expansionForwardDistance, forward]

private def chooseEvenExpansionDirection : List ArithmeticInstruction :=
  branchOnAtMost 47 23 [.natConst 45 0]
    (appendBlock [.natConst 45 1, .natSub 46 19 46] halveExpansionDistance)

/-- Of the two arcs between entry and base, use the even-length one. Register 45
selects the direction, 46 is its edge count, and 95 is its pair count. -/
def chooseMatchingExpansionDirection : List ArithmeticInstruction :=
  appendBlock chooseForwardExpansionDistance (appendBlock halveExpansionDistance chooseEvenExpansionDirection)

theorem chooseMatchingExpansionDirection_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0)
    (entryIndex : s.nr 81 < s.nr 19) (baseIndex : s.nr 82 < s.nr 19)
    (oddLength : Odd (s.nr 19)) (smallCycle : s.nr 19 ≤ s.nr 55) :
    ∃ t steps, steps ≤ 14 * s.nr 55 + 16 ∧ BlockRuns chooseMatchingExpansionDirection steps s t ∧ t.halted = false ∧
      t.nr 45 = (if Even (expansionForwardDistance s) then 0 else 1) ∧
      t.nr 46 = (if Even (expansionForwardDistance s) then expansionForwardDistance s else s.nr 19 - expansionForwardDistance s) ∧
      t.nr 46 = 2 * t.nr 95 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
  let d := expansionForwardDistance s
  have dBound : d < s.nr 19 := by
    by_cases order : s.nr 81 ≤ s.nr 82 <;> simp [d, expansionForwardDistance, order] <;> omega
  obtain ⟨first, firstRun, live, forward, natOne, realOne, rrOne, firstKeeps⟩ :=
    chooseForwardExpansionDistance_spec s entry running
  let a := {first with pc := 0}
  have aOne : a.nr 9 = 1 := (firstKeeps 9 (by decide)).trans one
  have aZero : a.nr 23 = 0 := (firstKeeps 23 (by decide)).trans zero
  have aDim : a.nr 55 = s.nr 55 := firstKeeps 55 (by decide)
  have aDist : a.nr 46 = d := forward
  obtain ⟨half, halfSteps, halfBudget, halfRun, halfLive, halfBalance, halfSmall, halfNat, halfReal, halfRR, halfKeeps⟩ :=
    halveExpansionDistance_spec a rfl live aOne aZero (by rw [aDim, aDist]; omega)
  let b := {half with pc := 0}
  have bEntry : b.pc = 0 := rfl
  have bLive : b.halted = false := halfLive
  have bDist : b.nr 46 = d := (halfKeeps 46 (by decide)).trans aDist
  have bZero : b.nr 23 = 0 := (halfKeeps 23 (by decide)).trans aZero
  have bOne : b.nr 9 = 1 := (halfKeeps 9 (by decide)).trans aOne
  have bDim : b.nr 55 = s.nr 55 := (halfKeeps 55 (by decide)).trans aDim
  have bSize : b.nr 19 = s.nr 19 := (halfKeeps 19 (by decide)).trans (firstKeeps 19 (by decide))
  have representation : b.nr 47 + 2 * b.nr 95 = d := halfBalance.trans aDist
  have remBound : b.nr 47 ≤ 1 := halfSmall
  rw [aDim] at halfBudget
  by_cases even : b.nr 47 = 0
  · let t := {b with pc := 1, nr := Function.update b.nr 45 0}
    have step : BlockRuns [.natConst 45 0] 1 b t := by
      apply BlockRuns.of_running_exit
      · simp [t, arithmeticStep, bEntry, bLive]
      · exact bLive
      · rfl
    have ran := branchOnAtMost_left 47 23 [.natConst 45 0]
      (appendBlock [.natConst 45 1, .natSub 46 19 46] halveExpansionDistance) (s := b) rfl halfLive
      (by rw [even, bZero]) step halfLive
    have dEven : Even (expansionForwardDistance s) := ⟨b.nr 95, by change d = _; omega⟩
    refine ⟨_, 3 + (halfSteps + 3), by omega, firstRun.append (halfRun.append ran), halfLive,
      ?_, ?_, ?_, halfNat.trans natOne, halfReal.trans realOne, halfRR.trans rrOne⟩
    · change t.nr 45 = _
      simp [t, dEven]
    · change t.nr 46 = _
      rw [if_pos dEven]
      exact bDist
    · change t.nr 46 = 2 * t.nr 95
      change b.nr 46 = 2 * b.nr 95
      omega
  · have oneLeft : b.nr 47 = 1 := by omega
    have dOdd : ¬Even (expansionForwardDistance s) := by
      rintro ⟨q, eq⟩
      change d = q + q at eq
      omega
    let rev := s.nr 19 - d
    let reversed := { b with
      pc := 2
      nr := Function.update (Function.update b.nr 45 1) 46 rev }
    have turn : BlockRuns [.natConst 45 1, .natSub 46 19 46] 2 b reversed := by
      apply BlockRuns.of_running_exit
      · simp [reversed, rev, arithmeticStep, bEntry, bLive, bSize, bDist, Function.iterate_succ_apply']
      · exact bLive
      · rfl
    let aRev := {reversed with pc := 0}
    have dim : aRev.nr 55 = s.nr 55 := bDim
    have amount : aRev.nr 46 = rev := by simp [aRev, reversed]
    obtain ⟨t, revSteps, revBudget, revRun, revLive, revBalance, revSmall, revNat, revReal, revRR, revKeeps⟩ :=
      halveExpansionDistance_spec aRev rfl halfLive bOne bZero (by rw [amount, dim]; dsimp [rev]; omega)
    have selected := branchOnAtMost_right 47 23 [.natConst 45 0]
      (appendBlock [.natConst 45 1, .natSub 46 19 46] halveExpansionDistance) (s := b) rfl halfLive
      (by rw [oneLeft, bZero] <;> decide) (turn.append revRun) revLive
    have revEven : rev % 2 = 0 := by
      have odd := Nat.odd_iff.mp oddLength
      dsimp [rev]
      omega
    have remain : t.nr 47 = 0 := by omega
    rw [dim] at revBudget
    refine ⟨_, 3 + (halfSteps + (1 + (2 + revSteps))), by omega,
      firstRun.append (halfRun.append selected), revLive, ?_, ?_, ?_,
      revNat.trans (halfNat.trans natOne), revReal.trans (halfReal.trans realOne), revRR.trans (halfRR.trans rrOne)⟩
    · change t.nr 45 = _
      rw [if_neg dOdd, revKeeps 45 (by decide)]
      simp [aRev, reversed]
    · change t.nr 46 = _
      rw [if_neg dOdd, revKeeps 46 (by decide), amount]
    · change t.nr 46 = 2 * t.nr 95
      have counted := revBalance.trans amount
      rw [revKeeps 46 (by decide), amount]
      omega

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionDirectionRAM

/-! matching/MatchingForestWitnessRAM.lean -/
section RppSource_MatchingForestWitnessRAM
namespace VehicleRoutingSurvey.Routing

def forestWitnessAddress (base child : ℕ) : ℕ := base + (child + child)

def matchingForestWitnessAt (memory : ℕ → ℕ) (base child : ℕ) : ℕ × ℕ :=
  let addr := forestWitnessAddress base child
  (memory addr, memory (addr + 1))

def writeMatchingForestWitness (memory : ℕ → ℕ) (base child : ℕ) (edge : ℕ × ℕ) : ℕ → ℕ :=
  let addr := forestWitnessAddress base child
  Function.update (Function.update memory addr edge.1) (addr + 1) edge.2

theorem matchingForestWitnessAt_write_same (memory : ℕ → ℕ) (base child : ℕ) (edge : ℕ × ℕ) :
    matchingForestWitnessAt (writeMatchingForestWitness memory base child edge) base child = edge := by
  rcases edge with ⟨u, v⟩
  simp (disch := omega) [matchingForestWitnessAt, writeMatchingForestWitness, forestWitnessAddress,
    Function.update_of_ne]

theorem matchingForestWitnessAt_write_other (memory : ℕ → ℕ) (base child other : ℕ)
    (edge : ℕ × ℕ) (distinct : other ≠ child) :
    matchingForestWitnessAt (writeMatchingForestWitness memory base child edge) base other =
      matchingForestWitnessAt memory base other := by
  simp (disch := omega) [matchingForestWitnessAt, writeMatchingForestWitness, forestWitnessAddress,
    Function.update_of_ne]

/-- Reserve a parent-edge witness pair for each compact representative.
Root entries are ignored and need no initialization. -/
def allocateMatchingForestWitnessArray : List ArithmeticInstruction :=
  [.natAdd 90 68 14, .natAdd 68 68 55, .natAdd 68 68 55]

theorem allocateMatchingForestWitnessArray_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 14 = 0) :
    ∃ t, BlockRuns allocateMatchingForestWitnessArray 3 s t ∧ t.halted = false ∧
      t.nr 90 = s.nr 68 ∧ t.nr 68 = s.nr 68 + 2 * s.nr 55 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
  let t := (arithmeticStep allocateMatchingForestWitnessArray)^[3] s
  have exit : t.pc = allocateMatchingForestWitnessArray.length ∧ t.halted = false := by
    simp [t, allocateMatchingForestWitnessArray, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl exit.2 exit.1, exit.2, ?_⟩
  simp [t, allocateMatchingForestWitnessArray, arithmeticStep, entry, running, zero, Function.iterate_succ_apply',
    Nat.two_mul, Nat.add_assoc]

def matchingOriginalGrowthEvent (s : ArithmeticState) : ℕ × ℕ :=
  let slot := s.nr 1 - 1
  let addr := s.nr 54 + (slot + slot)
  (s.nm addr, s.nm (addr + 1))

/-- Save both original endpoints before growth can replace the selected candidate row. -/
def saveMatchingGrowthOriginalEdge : List ArithmeticInstruction :=
  [.natSub 6 1 9, .natAdd 6 6 6, .natAdd 6 54 6, .natLoad 22 6, .natAdd 6 6 9, .natLoad 23 6]

theorem saveMatchingGrowthOriginalEdge_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns saveMatchingGrowthOriginalEdge 6 s t ∧ t.halted = false ∧
      (t.nr 22, t.nr 23) = matchingOriginalGrowthEvent s ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ r, r ∉ [0, 6, 22, 23] → t.nr r = s.nr r) := by
  let t := (arithmeticStep saveMatchingGrowthOriginalEdge)^[6] s
  have exit : t.pc = saveMatchingGrowthOriginalEdge.length ∧ t.halted = false ∧
      (t.nr 22, t.nr 23) = matchingOriginalGrowthEvent s ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, saveMatchingGrowthOriginalEdge, matchingOriginalGrowthEvent, arithmeticStep, entry, running,
      one, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl exit.2.1 exit.1,
    exit.2.1, exit.2.2.1, exit.2.2.2.1, exit.2.2.2.2.1, exit.2.2.2.2.2, ?_⟩
  intro r away
  apply arithmeticRun_keeps_register
  simp [saveMatchingGrowthOriginalEdge, naturalDestination] at away ⊢ <;> omega

def matchingSavedGrowthEvent (s : ArithmeticState) : ℕ × ℕ := (s.nr 22, s.nr 23)

/-- Use the saved original endpoint pair to write the new inner node's link. The matched
parent edge of the new outer node connects its base and the inner base. -/
def storeMatchingGrowthWitnesses : List ArithmeticInstruction :=
  [.natAdd 6 28 28, .natAdd 6 90 6, .natStore 6 22, .natAdd 6 6 9, .natStore 6 23,
   .natAdd 6 26 26, .natAdd 6 90 6, .natStore 6 28, .natAdd 6 6 9, .natStore 6 26]

def matchingGrowthWitnessStored (s : ArithmeticState) : ℕ → ℕ :=
  writeMatchingForestWitness
    (writeMatchingForestWitness s.nm (s.nr 90) (s.nr 28) (matchingSavedGrowthEvent s))
    (s.nr 90) (s.nr 26) (s.nr 28, s.nr 26)

set_option maxRecDepth 4096 in
theorem storeMatchingGrowthWitnesses_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns storeMatchingGrowthWitnesses 10 s t ∧ t.halted = false ∧
      t.nm = matchingGrowthWitnessStored s ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ r, r ∉ [0, 6] → t.nr r = s.nr r) := by
  let t := (arithmeticStep storeMatchingGrowthWitnesses)^[10] s
  have computed : t.pc = storeMatchingGrowthWitnesses.length ∧ t.halted = false ∧
      t.nm = matchingGrowthWitnessStored s ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, storeMatchingGrowthWitnesses, arithmeticStep, Function.iterate_succ_apply', entry, running,
      one, matchingGrowthWitnessStored, writeMatchingForestWitness, forestWitnessAddress, matchingSavedGrowthEvent]
  refine ⟨t, BlockRuns.of_running_exit rfl computed.2.1 computed.1,
    computed.2.1, computed.2.2.1, computed.2.2.2.1, computed.2.2.2.2, ?_⟩
  intro r away
  apply arithmeticRun_keeps_register
  simp [storeMatchingGrowthWitnesses, naturalDestination] at away ⊢ <;> omega

theorem matchingGrowthWitnessStored_at_inner (s : ArithmeticState) (distinct : s.nr 28 ≠ s.nr 26) :
    matchingForestWitnessAt (matchingGrowthWitnessStored s) (s.nr 90) (s.nr 28) = matchingSavedGrowthEvent s := by
  simp [matchingGrowthWitnessStored, matchingForestWitnessAt_write_other _ _ _ _ _ distinct,
    matchingForestWitnessAt_write_same]

theorem matchingGrowthWitnessStored_at_outer (s : ArithmeticState) :
    matchingForestWitnessAt (matchingGrowthWitnessStored s) (s.nr 90) (s.nr 26) = (s.nr 28, s.nr 26) := by
  exact matchingForestWitnessAt_write_same _ _ _ _

def orientedMatchingGrowthEdge (s : ArithmeticState) : ℕ × ℕ :=
  if s.nm (s.nr 57 + s.nr 22) = s.nr 28 then (s.nr 23, s.nr 22) else (s.nr 22, s.nr 23)

private def orientMatchingGrowthEdge : List ArithmeticInstruction :=
  [.natAdd 6 57 22, .natLoad 10 6, .natBranch 10 28 3 8, .natBranch 28 10 4 8,
   .natConst 14 0, .natAdd 6 22 14, .natAdd 22 23 14, .natAdd 23 6 14]

private theorem orientMatchingGrowthEdge_spec (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t steps, steps ≤ 8 ∧ BlockRuns orientMatchingGrowthEdge steps s t ∧ t.halted = false ∧
      (t.nr 22, t.nr 23) = orientedMatchingGrowthEdge s ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 10, 14, 22, 23] → t.nr r = s.nr r := by
  have build (steps : ℕ) (cost : steps ≤ 8)
      (computed : let t := (arithmeticStep orientMatchingGrowthEdge)^[steps] s
        t.pc = orientMatchingGrowthEdge.length ∧ t.halted = false ∧
        (t.nr 22, t.nr 23) = orientedMatchingGrowthEdge s ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr) :
      ∃ t steps, steps ≤ 8 ∧ BlockRuns orientMatchingGrowthEdge steps s t ∧ t.halted = false ∧
        (t.nr 22, t.nr 23) = orientedMatchingGrowthEdge s ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
        ∀ r, r ∉ [0, 6, 10, 14, 22, 23] → t.nr r = s.nr r := by
    obtain ⟨exit, live, edge, natural, real, rr⟩ := computed
    exact ⟨_, steps, cost, BlockRuns.of_running_exit rfl live exit, live, edge, natural, real, rr,
      fun _ away => arithmeticRun_keeps_from_destination_list [0, 6, 10, 14, 22, 23] (by decide) away s steps⟩
  rcases lt_trichotomy (s.nm (s.nr 57 + s.nr 22)) (s.nr 28) with before | equal | after
  · apply build 4 (by decide)
    simp [orientMatchingGrowthEdge, orientedMatchingGrowthEdge, arithmeticStep, entry, running,
      before.le, before.ne, not_le.mpr before, Function.iterate_succ_apply']
  · apply build 8 le_rfl
    simp [orientMatchingGrowthEdge, orientedMatchingGrowthEdge, arithmeticStep, entry, running, equal,
      Function.iterate_succ_apply']
  · apply build 3 (by decide)
    simp [orientMatchingGrowthEdge, orientedMatchingGrowthEdge, arithmeticStep, entry, running,
      after.ne', not_le.mpr after, Function.iterate_succ_apply']

/-- Both resulting witness pairs point from the forest parent to its child. -/
def storeOrientedMatchingGrowthWitnesses : List ArithmeticInstruction :=
  appendBlock orientMatchingGrowthEdge storeMatchingGrowthWitnesses

theorem storeOrientedMatchingGrowthWitnesses_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ 18 ∧ BlockRuns storeOrientedMatchingGrowthWitnesses steps s t ∧ t.halted = false ∧
      t.nm = writeMatchingForestWitness
        (writeMatchingForestWitness s.nm (s.nr 90) (s.nr 28) (orientedMatchingGrowthEdge s))
        (s.nr 90) (s.nr 26) (s.nr 28, s.nr 26) ∧ t.rm = s.rm ∧ t.rr = s.rr := by
  obtain ⟨middle, ticks, short, first, live, edge, natural, real, rr, keep⟩ :=
    orientMatchingGrowthEdge_spec s entry running
  let ready := {middle with pc := 0}
  have unit : ready.nr 9 = 1 := (keep 9 (by decide)).trans one
  obtain ⟨t, second, tLive, packed, tReal, tRR, _⟩ := storeMatchingGrowthWitnesses_spec ready rfl live unit
  refine ⟨_, ticks + 10, by omega, first.append second, tLive, ?_, tReal.trans real, tRR.trans rr⟩
  change t.nm = _
  have saved : matchingSavedGrowthEvent ready = orientedMatchingGrowthEdge s := edge
  rw [packed]
  unfold matchingGrowthWitnessStored
  rw [show ready.nm = s.nm from natural, show ready.nr 90 = s.nr 90 from keep 90 (by decide),
    show ready.nr 28 = s.nr 28 from keep 28 (by decide), show ready.nr 26 = s.nr 26 from keep 26 (by decide), saved]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingForestWitnessRAM

/-! matching/MatchingExpansionSearchRAM.lean -/
section RppSource_MatchingExpansionSearchRAM
namespace VehicleRoutingSurvey.Routing

def expansionOldParentWitness (s : ArithmeticState) : ℕ × ℕ :=
  matchingForestWitnessAt s.nm (s.nr 90) (s.nr 97)

def expansionEntryOriginal (s : ArithmeticState) : ℕ :=
  let edge := expansionOldParentWitness s
  if s.nm (s.nr 57 + edge.1) = s.nr 97 then edge.1 else edge.2

def expansionEntryChild (s : ArithmeticState) : ℕ := s.nm (s.nr 79 + expansionEntryOriginal s)

private def fetchExpansionParentWitness : List ArithmeticInstruction :=
  [.natConst 23 0, .natAdd 6 52 97, .natLoad 96 6, .natAdd 6 50 97, .natLoad 98 6,
   .natAdd 6 97 97, .natAdd 6 90 6, .natLoad 43 6, .natAdd 6 6 9, .natLoad 44 6,
   .natAdd 6 57 43, .natLoad 10 6]

private def chooseExpansionEntryChild (original : ℕ) : List ArithmeticInstruction :=
  [.natAdd 6 79 original, .natLoad 27 6]

/-- Recover the decomposed inner blossom's entry child from the original parent witness.
Registers 43/44 save that witness, 96 the outside forest parent, and 98 the mate. -/
def findExpansionEntryChild : List ArithmeticInstruction :=
  appendBlock fetchExpansionParentWitness (branchOnAtMost 10 97
    (branchOnAtMost 97 10 (chooseExpansionEntryChild 43) (chooseExpansionEntryChild 44))
    (chooseExpansionEntryChild 44))

def readExpansionHeader : List ArithmeticInstruction :=
  appendBlock [.natAdd 6 74 97, .natLoad 22 6, .natAdd 81 55 23, .natAdd 82 55 23]
    readMatchingCycleHeader

def readExpansionRepresentative : List ArithmeticInstruction :=
  [.natAdd 6 7 7, .natAdd 6 6 6, .natAdd 6 18 6, .natLoad 15 6]

def rememberExpansionIndex (representative output : ℕ) : List ArithmeticInstruction :=
  branchOnAtMost 15 representative
    (branchOnAtMost representative 15 [.natAdd output 7 23] []) []

def considerExpansionIndex : List ArithmeticInstruction :=
  appendBlock readExpansionRepresentative (appendBlock (rememberExpansionIndex 27 81) (rememberExpansionIndex 97 82))

/-- Locate the entry and old base in the stored cycle. The cycle base and length end
in registers 18 and 19, and the two positions in 81 and 82. -/
def locateMatchingExpansionEndpoints : List ArithmeticInstruction :=
  appendBlock findExpansionEntryChild
    (appendBlock readExpansionHeader (countedLoopFromZero 9 7 19 considerExpansionIndex))

private def expansionWitnessReadState (s : ArithmeticState) : ArithmeticState :=
  let edge := expansionOldParentWitness s
  let zero := Function.update s.nr 23 0
  let parent := Function.update zero 96 (s.nm (s.nr 52 + s.nr 97))
  let mate := Function.update parent 98 (s.nm (s.nr 50 + s.nr 97))
  let witness := Function.update (Function.update mate 43 edge.1) 44 edge.2
  { s with
    pc := 12
    nr := Function.update (Function.update witness 6 (s.nr 57 + edge.1)) 10 (s.nm (s.nr 57 + edge.1)) }

private theorem fetchExpansionParentWitness_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    BlockRuns fetchExpansionParentWitness 12 s (expansionWitnessReadState s) := by
  apply BlockRuns.of_running_exit
  · simp [expansionWitnessReadState, fetchExpansionParentWitness, arithmeticStep, entry, running, one,
      expansionOldParentWitness, matchingForestWitnessAt, forestWitnessAddress, Function.iterate_succ_apply',
      Function.update_idem]
    funext r
    by_cases scratch : r = 6 <;> simp [Function.update_apply, scratch]
  · exact running
  · rfl

private theorem chooseExpansionEntryChild_spec (original : ℕ) (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    let t := { s with
      pc := 2
      nr := Function.update (Function.update s.nr 6 (s.nr 79 + s.nr original)) 27 (s.nm (s.nr 79 + s.nr original)) }
    BlockRuns (chooseExpansionEntryChild original) 2 s t := by
  dsimp only
  apply BlockRuns.of_running_exit
  · simp [chooseExpansionEntryChild, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · exact running
  · rfl

theorem findExpansionEntryChild_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ 18 ∧ BlockRuns findExpansionEntryChild steps s t ∧ t.halted = false ∧
      t.nr 27 = expansionEntryChild s ∧ t.nr 96 = s.nm (s.nr 52 + s.nr 97) ∧
      t.nr 98 = s.nm (s.nr 50 + s.nr 97) ∧ (t.nr 43, t.nr 44) = expansionOldParentWitness s ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧ t.nr 23 = 0 := by
  let p := {expansionWitnessReadState s with pc := 0}
  have fetch := fetchExpansionParentWitness_spec s entry running one
  have readRole : p.nr 10 = s.nm (s.nr 57 + (expansionOldParentWitness s).1) := by simp [p, expansionWitnessReadState]
  have base : p.nr 97 = s.nr 97 := by simp [p, expansionWitnessReadState]
  have parent : p.nr 96 = s.nm (s.nr 52 + s.nr 97) := by simp [p, expansionWitnessReadState]
  have mate : p.nr 98 = s.nm (s.nr 50 + s.nr 97) := by simp [p, expansionWitnessReadState]
  have edge : (p.nr 43, p.nr 44) = expansionOldParentWitness s := by simp [p, expansionWitnessReadState]
  have map : p.nr 79 = s.nr 79 := by simp [p, expansionWitnessReadState]
  have left := chooseExpansionEntryChild_spec 43 p rfl running
  have right := chooseExpansionEntryChild_spec 44 p rfl running
  rcases lt_trichotomy (p.nr 10) (p.nr 97) with below | equal | above
  · have branch := branchOnAtMost_right 97 10 (chooseExpansionEntryChild 43) (chooseExpansionEntryChild 44)
      (s := p) rfl running below right running
    have routed := branchOnAtMost_left 10 97 _ (chooseExpansionEntryChild 44) (s := p) rfl running below.le branch running
    have outside : s.nm (s.nr 57 + (expansionOldParentWitness s).1) ≠ s.nr 97 := by
      simpa only [readRole, base] using below.ne
    refine ⟨_, 12 + (1 + (1 + 2) + 1), by decide, fetch.append routed, running, ?_, parent, mate, edge, rfl, rfl, rfl, rfl⟩
    change p.nm (p.nr 79 + p.nr 44) = expansionEntryChild s
    have rightEdge : p.nr 44 = (expansionOldParentWitness s).2 := congrArg Prod.snd edge
    rw [expansionEntryChild, expansionEntryOriginal, if_neg outside, map, rightEdge] <;> rfl
  · have branch := branchOnAtMost_left 97 10 (chooseExpansionEntryChild 43) (chooseExpansionEntryChild 44)
      (s := p) rfl running equal.ge left running
    have routed := branchOnAtMost_left 10 97 _ (chooseExpansionEntryChild 44) (s := p) rfl running equal.le branch running
    have inside : s.nm (s.nr 57 + (expansionOldParentWitness s).1) = s.nr 97 := by
      simpa only [readRole, base] using equal
    refine ⟨_, 18, le_rfl, fetch.append routed, running, ?_, parent, mate, edge, rfl, rfl, rfl, rfl⟩
    change p.nm (p.nr 79 + p.nr 43) = expansionEntryChild s
    have leftEdge : p.nr 43 = (expansionOldParentWitness s).1 := congrArg Prod.fst edge
    rw [expansionEntryChild, expansionEntryOriginal, if_pos inside, map, leftEdge] <;> rfl
  · have routed := branchOnAtMost_right 10 97 (branchOnAtMost 97 10
      (chooseExpansionEntryChild 43) (chooseExpansionEntryChild 44)) (chooseExpansionEntryChild 44)
      (s := p) rfl running above right running
    have outside : s.nm (s.nr 57 + (expansionOldParentWitness s).1) ≠ s.nr 97 := by
      simpa only [readRole, base] using above.ne'
    refine ⟨_, 15, by decide, fetch.append routed, running, ?_, parent, mate, edge, rfl, rfl, rfl, rfl⟩
    change p.nm (p.nr 79 + p.nr 44) = expansionEntryChild s
    have rightEdge : p.nr 44 = (expansionOldParentWitness s).2 := congrArg Prod.snd edge
    rw [expansionEntryChild, expansionEntryOriginal, if_neg outside, map, rightEdge] <;> rfl

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionSearchRAM

/-! matching/MatchingRebasePair.lean -/
section RppSource_MatchingRebasePair
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- Advance the cycle index in register 7, wrapping at the count in register 19. -/
def advanceMatchingCycleIndexBlock : List ArithmeticInstruction :=
  [.natAdd 7 7 9, .natBranch 19 7 2 3, .natConst 7 0]

theorem advanceMatchingCycleIndexBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (inside : s.nr 7 < s.nr 19) :
    let index := (s.nr 7 + 1) % s.nr 19
    let t := {s with pc := 3, nr := Function.update s.nr 7 index}
    ∃ steps ≤ 3, BlockRuns advanceMatchingCycleIndexBlock steps s t := by
  intro index t
  by_cases wraps : s.nr 19 ≤ s.nr 7 + 1
  · have atEnd : s.nr 7 + 1 = s.nr 19 := by omega
    have indexEq : index = 0 := by simp [index, atEnd]
    refine ⟨3, le_rfl, BlockRuns.of_running_exit ?_ (show t.halted = false from running) rfl⟩
    simp [t, advanceMatchingCycleIndexBlock, arithmeticStep, entry, running, one,
      wraps, indexEq, Function.iterate_succ_apply', Function.update_idem]
  · have indexEq : index = s.nr 7 + 1 := Nat.mod_eq_of_lt (lt_of_not_ge wraps)
    refine ⟨2, by decide, BlockRuns.of_running_exit ?_ (show t.halted = false from running) rfl⟩
    simp [t, advanceMatchingCycleIndexBlock, arithmeticStep, entry, running, one,
      wraps, indexEq, Function.iterate_succ_apply']

private def saveRebasePairLeft : List ArithmeticInstruction :=
  [.natAdd 10 15 14, .natAdd 11 25 14, .natAdd 12 16 14, .natAdd 13 17 14]

private def rebasePairLeftSaved (s : ArithmeticState) : ArithmeticState :=
  {s with
    pc := 4
    nr := Function.update (Function.update (Function.update (Function.update s.nr 10 (s.nr 15))
      11 (s.nr 25)) 12 (s.nr 16)) 13 (s.nr 17)}

private theorem saveRebasePairLeft_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (zero : s.nr 14 = 0) :
    BlockRuns saveRebasePairLeft 4 s (rebasePairLeftSaved s) := by
  refine BlockRuns.of_running_exit ?_ (show (rebasePairLeftSaved s).halted = false from running) rfl
  simp [saveRebasePairLeft, rebasePairLeftSaved, arithmeticStep, entry, running, zero,
    Function.iterate_succ_apply']

private def orientRebasePairPorts : List ArithmeticInstruction :=
  [.natAdd 6 79 12, .natLoad 6 6, .natBranch 6 10 3 4, .natBranch 10 6 7 4,
   .natAdd 6 12 14, .natAdd 12 13 14, .natAdd 13 6 14]

def matchingRebasePorts (memory : ℕ → ℕ) (mapBase : ℕ) (left : MatchingCycleChild) : ℕ × ℕ :=
  if memory (mapBase + left.endpointA) = left.representative then (left.endpointA, left.endpointB)
  else (left.endpointB, left.endpointA)

private theorem orientRebasePairPorts_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (zero : s.nr 14 = 0) :
    ∃ t steps, steps ≤ 7 ∧ BlockRuns orientRebasePairPorts steps s t ∧ t.halted = false ∧
      (t.nr 12, t.nr 13) = matchingRebasePorts s.nm (s.nr 79) ⟨s.nr 10, s.nr 11, s.nr 12, s.nr 13⟩ ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 12, 13] → t.nr r = s.nr r := by
  have build (steps : ℕ) (budget : steps ≤ 7)
      (effect : let t := (arithmeticStep orientRebasePairPorts)^[steps] s
       t.pc = orientRebasePairPorts.length ∧ t.halted = false ∧
         (t.nr 12, t.nr 13) = matchingRebasePorts s.nm (s.nr 79) ⟨s.nr 10, s.nr 11, s.nr 12, s.nr 13⟩ ∧
         t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr) :
      ∃ t steps, steps ≤ 7 ∧ BlockRuns orientRebasePairPorts steps s t ∧ t.halted = false ∧
        (t.nr 12, t.nr 13) = matchingRebasePorts s.nm (s.nr 79) ⟨s.nr 10, s.nr 11, s.nr 12, s.nr 13⟩ ∧
        t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 12, 13] → t.nr r = s.nr r := by
    obtain ⟨exit, live, ports, natural, real, rr⟩ := effect
    exact ⟨_, steps, budget, BlockRuns.of_running_exit rfl live exit, live, ports, natural, real, rr,
      fun _ safe => arithmeticRun_keeps_from_destination_list _ (by decide) safe s steps⟩
  rcases lt_trichotomy (s.nm (s.nr 79 + s.nr 12)) (s.nr 10) with below | equal | above
  · apply build 7 le_rfl
    simp [orientRebasePairPorts, matchingRebasePorts, arithmeticStep, entry, running, zero,
      below.le, not_le.mpr below, below.ne, Function.iterate_succ_apply']
  · apply build 4 (by decide)
    simp [orientRebasePairPorts, matchingRebasePorts, arithmeticStep, entry, running, equal,
      Function.iterate_succ_apply']
  · apply build 6 (by decide)
    simp [orientRebasePairPorts, matchingRebasePorts, arithmeticStep, entry, running, zero,
      not_le.mpr above, above.ne', Function.iterate_succ_apply']

/-- Read adjacent child records and orient the saved original edge using the membership map.
The right child is the cyclic successor, including when the edge crosses the array boundary. -/
def readRebasedCyclePairBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock (appendBlock (appendBlock readMatchingCycleChild saveRebasePairLeft)
    advanceMatchingCycleIndexBlock) readMatchingCycleChild) orientRebasePairPorts

set_option maxRecDepth 4096 in
theorem readRebasedCyclePairBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (inside : s.nr 7 < s.nr 19) :
    let next := (s.nr 7 + 1) % s.nr 19
    let left := matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7)
    let right := matchingCycleChildAt s.nm (s.nr 18 + 4 * next)
    ∃ t steps, steps ≤ 34 ∧ BlockRuns readRebasedCyclePairBlock steps s t ∧ t.halted = false ∧
      t.nr 7 = next ∧ (t.nr 10, t.nr 11) = (left.representative, left.node) ∧
      (t.nr 15, t.nr 25) = (right.representative, right.node) ∧
      (t.nr 12, t.nr 13) = matchingRebasePorts s.nm (s.nr 79) left ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 7, 10, 11, 12, 13, 15, 16, 17, 25] → t.nr r = s.nr r := by
  intro next left right
  obtain ⟨a, readLeft, aReady, leftRead, aNat, aReal, aRR, aGet⟩ := readMatchingCycleChild_spec s entry running one
  let aInput := {a with pc := 0}
  have aZero : aInput.nr 14 = 0 := (aGet 14 (by decide)).trans zero
  have saved := saveRebasePairLeft_correct (s := aInput) rfl aReady aZero
  let beforeAdvance := {relocateState readMatchingCycleChild.length (rebasePairLeftSaved aInput) with pc := 0}
  have carry (r : ℕ) (safe : r ∉ [10, 11, 12, 13] := by decide) : beforeAdvance.nr r = a.nr r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at safe
    obtain ⟨h10, h11, h12, h13⟩ := safe
    simp [beforeAdvance, rebasePairLeftSaved, aInput, relocateState, h10, h11, h12, h13]
  have oneAt : beforeAdvance.nr 9 = 1 := (carry 9).trans ((aGet 9 (by decide)).trans one)
  have indexAt : beforeAdvance.nr 7 = s.nr 7 := (carry 7).trans (aGet 7 (by decide))
  have countAt : beforeAdvance.nr 19 = s.nr 19 := (carry 19).trans (aGet 19 (by decide))
  obtain ⟨advanceSteps, advanceBound, advance⟩ := advanceMatchingCycleIndexBlock_correct
    (s := beforeAdvance) rfl aReady oneAt (by rwa [indexAt, countAt])
  let advanced := {beforeAdvance with pc := 3, nr := Function.update beforeAdvance.nr 7 next}
  have advancedRun : BlockRuns advanceMatchingCycleIndexBlock advanceSteps beforeAdvance advanced := by
    simpa only [advanced, indexAt, countAt, next] using advance
  let prefixCode := appendBlock (appendBlock readMatchingCycleChild saveRebasePairLeft) advanceMatchingCycleIndexBlock
  let readInput := {relocateState (appendBlock readMatchingCycleChild saveRebasePairLeft).length advanced with pc := 0}
  have keep (r : ℕ) (safe : r ≠ 7 := by decide) : readInput.nr r = beforeAdvance.nr r := by
    simp [readInput, advanced, relocateState, safe]
  have readOne : readInput.nr 9 = 1 := (keep 9).trans oneAt
  obtain ⟨d, readRight, dReady, rightRead, dNat, dReal, dRR, dGet⟩ := readMatchingCycleChild_spec readInput rfl aReady readOne
  have rightRead' : readMatchingCycleChildValue d = right := by
    have fixed := (keep 18).trans ((carry 18).trans (aGet 18 (by decide)))
    have idx : readInput.nr 7 = next := by simp [readInput, advanced, relocateState]
    simpa only [fixed, idx, show readInput.nm = s.nm from aNat, right] using rightRead
  let orientInput := {relocateState prefixCode.length d with pc := 0}
  have orientFixed (r : ℕ) (safe : r ∉ [0, 6, 15, 16, 17, 25] := by decide) :
      orientInput.nr r = readInput.nr r := dGet r safe
  have orientZero : orientInput.nr 14 = 0 :=
    (orientFixed 14).trans ((keep 14).trans ((carry 14).trans aZero))
  obtain ⟨e, orientSteps, orientBound, oriented, live, ports, eNat, eReal, eRR, eGet⟩ :=
    orientRebasePairPorts_correct (s := orientInput) rfl dReady orientZero
  let t := relocateState (appendBlock prefixCode readMatchingCycleChild).length e
  have joined : BlockRuns readRebasedCyclePairBlock (10 + 4 + advanceSteps + 10 + orientSteps) s t :=
    (((readLeft.append saved).append advancedRun).append readRight).append oriented
  have leftBytes : (⟨orientInput.nr 10, orientInput.nr 11, orientInput.nr 12, orientInput.nr 13⟩ : MatchingCycleChild) = left := by
    simpa [orientFixed 10, orientFixed 11, orientFixed 12, orientFixed 13, keep 10, keep 11, keep 12, keep 13,
      beforeAdvance, rebasePairLeftSaved, aInput, relocateState, readMatchingCycleChildValue] using leftRead
  refine ⟨t, _, by omega, joined, live, ?_, ?_, ?_, ?_, eNat.trans (dNat.trans aNat),
    eReal.trans (dReal.trans aReal), eRR.trans (dRR.trans aRR), ?_⟩
  · change e.nr 7 = next
    rw [eGet 7 (by decide), orientFixed 7]
    simp [readInput, advanced, relocateState]
  · change (e.nr 10, e.nr 11) = _
    rw [eGet 10 (by decide), eGet 11 (by decide)]
    exact Prod.ext (congrArg MatchingCycleChild.representative leftBytes) (congrArg MatchingCycleChild.node leftBytes)
  · change (e.nr 15, e.nr 25) = _
    rw [eGet 15 (by decide), eGet 25 (by decide)]
    exact Prod.ext (congrArg MatchingCycleChild.representative rightRead') (congrArg MatchingCycleChild.node rightRead')
  · change (e.nr 12, e.nr 13) = _
    have mapBase : orientInput.nr 79 = s.nr 79 :=
      (orientFixed 79).trans ((keep 79).trans ((carry 79).trans (aGet 79 (by decide))))
    simpa only [leftBytes, mapBase, show orientInput.nm = s.nm from dNat.trans aNat] using ports
  · intro r safe
    rw [← joined.run]
    exact arithmeticRun_keeps_from_destination_list _ (by decide) safe s _


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebasePair

/-! matching/MatchingExpansionEmitRAM.lean -/
section RppSource_MatchingExpansionEmitRAM
namespace VehicleRoutingSurvey.Routing

/-- Move to the previous cycle record, wrapping zero to the last index. -/
def retreatMatchingCycleIndexBlock : List ArithmeticInstruction :=
  [.natBranch 7 23 3 1, .natSub 7 7 9, .jump 4, .natSub 7 19 9]

theorem retreatMatchingCycleIndexBlock_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0) :
    let index := if s.nr 7 = 0 then s.nr 19 - 1 else s.nr 7 - 1
    let t := {s with pc := 4, nr := Function.update s.nr 7 index}
    ∃ steps ≤ 3, BlockRuns retreatMatchingCycleIndexBlock steps s t := by
  intro index t
  by_cases wraps : s.nr 7 = 0
  · refine ⟨2, by decide, BlockRuns.of_running_exit ?_ (show t.halted = false from running) rfl⟩
    simp [t, index, retreatMatchingCycleIndexBlock, arithmeticStep, entry, running, wraps, one, zero,
      Function.iterate_succ_apply']
  · refine ⟨3, le_rfl, BlockRuns.of_running_exit ?_ (show t.halted = false from running) rfl⟩
    simp [t, index, retreatMatchingCycleIndexBlock, arithmeticStep, entry, running, wraps, one, zero,
      Function.iterate_succ_apply']

def expansionPathTripleMemory (s : ArithmeticState) : ℕ → ℕ :=
  let cursor := s.nr 47
  Function.update (Function.update (Function.update s.nm cursor (s.nr 15)) (cursor + 1) (s.nr 16))
    (cursor + 2) (s.nr 17)

/-- Append a child representative and its original parent-edge pair to the path output. -/
def writeMatchingExpansionPathTriple : List ArithmeticInstruction :=
  [.natStore 47 15, .natAdd 47 47 9, .natStore 47 16, .natAdd 47 47 9,
    .natStore 47 17, .natAdd 47 47 9]

theorem writeMatchingExpansionPathTriple_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns writeMatchingExpansionPathTriple 6 s t ∧ t.halted = false ∧
      t.nr 47 = s.nr 47 + 3 ∧ t.nm = expansionPathTripleMemory s ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 47] → t.nr r = s.nr r := by
  let t := (arithmeticStep writeMatchingExpansionPathTriple)^[6] s
  have two : s.nr 47 + 1 + 1 = s.nr 47 + 2 := by omega
  have three : s.nr 47 + 1 + 1 + 1 = s.nr 47 + 3 := by omega
  have effect : t.pc = writeMatchingExpansionPathTriple.length ∧ t.halted = false ∧
      t.nr 47 = s.nr 47 + 3 ∧ t.nm = expansionPathTripleMemory s ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, writeMatchingExpansionPathTriple, expansionPathTripleMemory, arithmeticStep, entry, running, one,
      two, three, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1, effect.2.2.1,
    effect.2.2.2.1, effect.2.2.2.2.1, effect.2.2.2.2.2, ?_⟩
  intro r outside
  exact arithmeticRun_keeps_from_destination_list [0, 47] (by decide) outside s 6

def prepareExpansionPathFirst : List ArithmeticInstruction :=
  [.natAdd 94 86 23, .natAdd 47 86 23, .natAdd 7 81 23, .natAdd 16 43 23, .natAdd 17 44 23]

def writeExpansionPathForward : List ArithmeticInstruction :=
  appendBlock readMatchingCycleChild
    (appendBlock advanceMatchingCycleIndexBlock (appendBlock readExpansionRepresentative writeMatchingExpansionPathTriple))

def writeExpansionPathBackward : List ArithmeticInstruction :=
  appendBlock retreatMatchingCycleIndexBlock (appendBlock readMatchingCycleChild
    (appendBlock [.natAdd 6 16 23, .natAdd 16 17 23, .natAdd 17 6 23] writeMatchingExpansionPathTriple))

/-- The first record uses the blossom's old outer-parent witness. Following records use
the cycle edge just traversed, in either direction. The selected arc has an even edge count. -/
def emitMatchingExpansionPath : List ArithmeticInstruction :=
  appendBlock prepareExpansionPathFirst
    (appendBlock readExpansionRepresentative
      (appendBlock writeMatchingExpansionPathTriple
        (countedLoopFromZero 9 24 46 (branchOnAtMost 45 23 writeExpansionPathForward writeExpansionPathBackward))))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionEmitRAM

/-! matching/ExpansionRepresentativeRAM.lean -/
section RppSource_ExpansionRepresentativeRAM
namespace VehicleRoutingSurvey.Routing

private def publishExpansionRepresentativeCell : List ArithmeticInstruction :=
  [.natAdd 6 79 7, .natLoad 10 6, .natBranch 55 10 6 3,
    .natAdd 6 57 7, .natStore 6 10, .jump 9, .jump 7, .jump 8, .jump 9]

def publishExpansionRepresentatives : List ArithmeticInstruction :=
  countedLoopFromZero 9 7 55 publishExpansionRepresentativeCell

def expandedRepresentativeMemory (s : ArithmeticState) (processed : ℕ) : ℕ → ℕ :=
  fun a => if s.nr 57 ≤ a ∧ a < s.nr 57 + processed then
    let child := s.nm (s.nr 79 + (a - s.nr 57))
    if child < s.nr 55 then child else s.nm a
  else s.nm a

private theorem publishExpansionRepresentativeCell_spec {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    let child := s.nm (s.nr 79 + s.nr 7)
    ∃ t, BlockRuns publishExpansionRepresentativeCell 6 s t ∧ t.halted = false ∧
      t.nm = (if child < s.nr 55 then Function.update s.nm (s.nr 57 + s.nr 7) child else s.nm) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ≠ 6 → r ≠ 10 → t.nr r = s.nr r := by
  intro child
  let t := (arithmeticStep publishExpansionRepresentativeCell)^[6] s
  have ran : t.pc = publishExpansionRepresentativeCell.length ∧ t.halted = false ∧
      t.nm = (if child < s.nr 55 then Function.update s.nm (s.nr 57 + s.nr 7) child else s.nm) ∧
      t.rm = s.rm ∧ t.rr = s.rr := by
    by_cases skip : s.nr 55 ≤ s.nm (s.nr 79 + s.nr 7)
    · simp [t, child, publishExpansionRepresentativeCell, arithmeticStep, entry, running,
        skip, Nat.not_lt_of_ge skip, Function.iterate_succ_apply']
    · simp [t, child, publishExpansionRepresentativeCell, arithmeticStep, entry, running,
        skip, Nat.lt_of_not_ge skip, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ran.2.1 ran.1, ran.2.1, ran.2.2.1,
    ran.2.2.2.1, ran.2.2.2.2, ?_⟩
  intro r except6 except10
  by_cases skip : s.nr 55 ≤ s.nm (s.nr 79 + s.nr 7) <;>
    simp [t, publishExpansionRepresentativeCell, arithmeticStep, entry, running, skip,
      Function.iterate_succ_apply', Function.update_of_ne except6, Function.update_of_ne except10]

private theorem expandedRepresentativeMemory_step (s : ArithmeticState) (i : ℕ)
    (within : i < s.nr 55) (disjoint : s.nr 57 + s.nr 55 ≤ s.nr 79) :
    let memory := expandedRepresentativeMemory s i
    let child := memory (s.nr 79 + i)
    (if child < s.nr 55 then Function.update memory (s.nr 57 + i) child else memory) =
      expandedRepresentativeMemory s (i + 1) := by
  intro memory child
  have originalChild : child = s.nm (s.nr 79 + i) := by
    change expandedRepresentativeMemory s i (s.nr 79 + i) = _
    rw [expandedRepresentativeMemory, if_neg (by omega)]
  funext a
  by_cases current : a = s.nr 57 + i
  · subst a
    have new : s.nr 57 ≤ s.nr 57 + i ∧ s.nr 57 + i < s.nr 57 + (i + 1) := by omega
    have same : s.nr 57 + i - s.nr 57 = i := by omega
    by_cases member : s.nm (s.nr 79 + i) < s.nr 55
    · simp [originalChild, member, expandedRepresentativeMemory, new, same]
    · have old : ¬(s.nr 57 ≤ s.nr 57 + i ∧ s.nr 57 + i < s.nr 57 + i) := by omega
      simp [originalChild, member, memory, expandedRepresentativeMemory, new, old, same]
  · have unaffected : (s.nr 57 ≤ a ∧ a < s.nr 57 + i) ↔ (s.nr 57 ≤ a ∧ a < s.nr 57 + (i + 1)) := by omega
    by_cases member : child < s.nr 55 <;>
      simp [member, memory, expandedRepresentativeMemory, unaffected, Function.update_of_ne current]

private structure ExpansionRepresentativeScan (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  ready : s.halted = false
  index : s.nr 7 = i
  fixed : ∀ r, r ∉ [6, 7, 10] → s.nr r = initial.nr r
  memory : s.nm = expandedRepresentativeMemory initial i
  real : s.rm = initial.rm
  realRegisters : s.rr = initial.rr

/-- The DFS leaves a child representative in range for a vertex inside the
expanded blossom and a sentinel elsewhere. Publish exactly the in-range entries. -/
theorem publishExpansionRepresentatives_spec {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (disjoint : s.nr 57 + s.nr 55 ≤ s.nr 79) :
    ∃ t, BlockRuns publishExpansionRepresentatives (9 * s.nr 55 + 2) s t ∧ t.halted = false ∧
      t.nm = expandedRepresentativeMemory s (s.nr 55) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [6, 7, 10] → t.nr r = s.nr r := by
  let inv := ExpansionRepresentativeScan s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, ?_, rfl, rfl⟩
    · intro r outside
      have safe : r ≠ 7 := fun eq => outside (eq.symm ▸ (by decide : (7 : ℕ) ∈ [6, 7, 10]))
      exact Function.update_of_ne safe _ _
    · funext a
      change s.nm a = expandedRepresentativeMemory s 0 a
      rw [expandedRepresentativeMemory, if_neg (by omega)]
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 55 = s.nr 55 :=
    ⟨h.entry, h.ready, h.index, h.fixed 55 (by decide)⟩
  have next (i : ℕ) (within : i < s.nr 55) (m : ArithmeticState) (h : inv i m) :
      ∃ t, BlockRuns publishExpansionRepresentativeCell 6 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    obtain ⟨t, run, ready, natural, real, realRegisters, fixed⟩ := publishExpansionRepresentativeCell_spec h.entry h.ready
    refine ⟨t, run, ready, rfl, ready, ?_, ?_, ?_, real.trans h.real, realRegisters.trans h.realRegisters⟩
    · simp [fixed 7 (by decide) (by decide), h.index, fixed 9 (by decide) (by decide), h.fixed 9 (by decide), one]
    · intro r safe
      have outside (j : ℕ) (used : j ∈ ([6, 7, 10] : List ℕ)) : r ≠ j := fun eq => safe (eq.symm ▸ used)
      change Function.update t.nr 7 (t.nr 7 + t.nr 9) r = s.nr r
      rw [Function.update_of_ne (outside 7 (by decide))]
      exact (fixed r (outside 6 (by decide)) (outside 10 (by decide))).trans (h.fixed r safe)
    · change t.nm = _
      rw [natural, h.memory, h.fixed 55 (by decide), h.fixed 57 (by decide), h.fixed 79 (by decide), h.index]
      exact expandedRepresentativeMemory_step s i within disjoint
  obtain ⟨_, final, run⟩ := countedLoopFromZero_correct 9 7 55 (s.nr 55) 6
    publishExpansionRepresentativeCell inv (s := s) entry running initial control next
  have steps : 1 + (s.nr 55 * (6 + 3) + 1) = 9 * s.nr 55 + 2 := by omega
  rw [steps] at run
  exact ⟨_, run, final.ready, final.memory, final.real, final.realRegisters, final.fixed⟩

theorem expandedRepresentativeMemory_at (s : ArithmeticState) {v : ℕ} (within : v < s.nr 55) :
    expandedRepresentativeMemory s (s.nr 55) (s.nr 57 + v) =
      if s.nm (s.nr 79 + v) < s.nr 55 then s.nm (s.nr 79 + v) else s.nm (s.nr 57 + v) := by
  rw [expandedRepresentativeMemory, if_pos (by omega), show s.nr 57 + v - s.nr 57 = v by omega]

theorem expandedRepresentativeMemory_outside (s : ArithmeticState) {a : ℕ}
    (outside : a < s.nr 57 ∨ s.nr 57 + s.nr 55 ≤ a) :
    expandedRepresentativeMemory s (s.nr 55) a = s.nm a := by
  rw [expandedRepresentativeMemory, if_neg (by omega)]

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionRepresentativeRAM

/-! matching/ExpansionRegistryRAM.lean -/
section RppSource_ExpansionRegistryRAM
namespace VehicleRoutingSurvey.Routing

def expansionCycleRow (s : ArithmeticState) (i : ℕ) : MatchingCycleChild :=
  matchingCycleChildAt s.nm (s.nr 18 + 4 * i)

private def storeExpansionNode : List ArithmeticInstruction :=
  [.natAdd 6 74 15, .natStore 6 25]

private def publishExpansionNodeCell : List ArithmeticInstruction :=
  appendBlock readMatchingCycleChild storeExpansionNode

private theorem storeExpansionNode_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) :
    ∃ t, BlockRuns storeExpansionNode 2 s t ∧ t.halted = false ∧
      t.nm = Function.update s.nm (s.nr 74 + s.nr 15) (s.nr 25) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ≠ 6 → t.nr r = s.nr r := by
  let t := (arithmeticStep storeExpansionNode)^[2] s
  have ready : t.halted = false := by
    simp [t, storeExpansionNode, arithmeticStep, Function.iterate_succ_apply', entry, running]
  have exit : t.pc = storeExpansionNode.length := by
    simp [t, storeExpansionNode, arithmeticStep, Function.iterate_succ_apply', entry, running]
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_⟩
  all_goals first
  | intro r safe
    simp [t, storeExpansionNode, arithmeticStep, Function.iterate_succ_apply', entry, running,
      Function.update_of_ne safe]
  | simp [t, storeExpansionNode, arithmeticStep, Function.iterate_succ_apply', entry, running]

private theorem publishExpansionNodeCell_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns publishExpansionNodeCell 12 s t ∧ t.halted = false ∧
      t.nm = Function.update s.nm (s.nr 74 + (expansionCycleRow s (s.nr 7)).representative)
        (expansionCycleRow s (s.nr 7)).node ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 15, 16, 17, 25] → t.nr r = s.nr r := by
  obtain ⟨m, reads, live, value, nat, real, rr, fixed⟩ := readMatchingCycleChild_spec s entry running one
  let ready := {m with pc := 0}
  obtain ⟨t, writes, stillLive, output, finalReal, finalRr, finalFixed⟩ :=
    storeExpansionNode_spec (s := ready) rfl live
  have owner : m.nr 15 = (expansionCycleRow s (s.nr 7)).representative :=
    congrArg MatchingCycleChild.representative value
  have node : m.nr 25 = (expansionCycleRow s (s.nr 7)).node := congrArg MatchingCycleChild.node value
  refine ⟨_, reads.append writes, stillLive, ?_, finalReal.trans real, finalRr.trans rr, ?_⟩
  · change t.nm = _
    rw [output]
    change Function.update m.nm (m.nr 74 + m.nr 15) (m.nr 25) = _
    rw [nat, fixed 74 (by decide), owner, node]
  · intro r safe
    exact (finalFixed r (by simp at safe; omega)).trans (fixed r safe)

private def expansionNodeScratch : List ℕ := [0, 6, 7, 15, 16, 17, 25]

private structure ExpansionNodeScan (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  ready : s.halted = false
  index : s.nr 7 = i
  fixed : ∀ r, r ∉ expansionNodeScratch → s.nr r = initial.nr r
  records : ∀ j < i, s.nm (initial.nr 74 + (expansionCycleRow initial j).representative) =
    (expansionCycleRow initial j).node
  kept : ∀ a, (∀ j < i, a ≠ initial.nr 74 + (expansionCycleRow initial j).representative) →
    s.nm a = initial.nm a
  real : s.rm = initial.rm
  realRegisters : s.rr = initial.rr

def publishExpansionNodes : List ArithmeticInstruction := countedLoopFromZero 9 7 19 publishExpansionNodeCell

/-- Restore the direct child node ids in the top-level registry. The
persisted cycle remains available for later descent and keeps its orientation. -/
theorem publishExpansionNodes_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (recordAfter : s.nr 74 + s.nr 55 ≤ s.nr 18)
    (inRange : ∀ i < s.nr 19, (expansionCycleRow s i).representative < s.nr 55)
    (distinct : ∀ i < s.nr 19, ∀ j < s.nr 19,
      (expansionCycleRow s i).representative = (expansionCycleRow s j).representative → i = j) :
    ∃ t, BlockRuns publishExpansionNodes (15 * s.nr 19 + 2) s t ∧ t.halted = false ∧
      (∀ j < s.nr 19, t.nm (s.nr 74 + (expansionCycleRow s j).representative) = (expansionCycleRow s j).node) ∧
      (∀ a, (∀ j < s.nr 19, a ≠ s.nr 74 + (expansionCycleRow s j).representative) → t.nm a = s.nm a) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ expansionNodeScratch → t.nr r = s.nr r := by
  let inv := ExpansionNodeScan s
  have first : inv 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, fun i hi => (Nat.not_lt_zero i hi).elim, fun _ _ => rfl, rfl, rfl⟩
    intro r safe
    have notIndex : r ≠ 7 := fun eq => safe (eq.symm ▸ (by decide : (7 : ℕ) ∈ expansionNodeScratch))
    exact Function.update_of_ne notIndex _ _
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 19 = s.nr 19 :=
    ⟨h.entry, h.ready, h.index, h.fixed 19 (by decide)⟩
  have next (i : ℕ) (within : i < s.nr 19) (m : ArithmeticState) (h : inv i m) :
      ∃ t, BlockRuns publishExpansionNodeCell 12 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    obtain ⟨t, run, ready, natural, real, rr, fixed⟩ :=
      publishExpansionNodeCell_spec h.entry h.ready ((h.fixed 9 (by decide)).trans one)
    have cycleRead (a : ℕ) (above : s.nr 18 ≤ a) : m.nm a = s.nm a := by
      apply h.kept a
      intro j earlier
      have bounded := inRange j (earlier.trans within)
      omega
    have row : expansionCycleRow m (m.nr 7) = expansionCycleRow s i := by
      rw [h.index]
      unfold expansionCycleRow matchingCycleChildAt
      rw [h.fixed 18 (by decide), cycleRead (s.nr 18 + 4 * i) (by omega),
        cycleRead (s.nr 18 + 4 * i + 1) (by omega), cycleRead (s.nr 18 + 4 * i + 2) (by omega),
        cycleRead (s.nr 18 + 4 * i + 3) (by omega)]
    have effect : t.nm = Function.update m.nm (s.nr 74 + (expansionCycleRow s i).representative)
        (expansionCycleRow s i).node := by rw [natural, h.fixed 74 (by decide), row]
    refine ⟨t, run, ready, rfl, ready, ?_, ?_, ?_, ?_, real.trans h.real, rr.trans h.realRegisters⟩
    · simp [fixed 7 (by decide), h.index, fixed 9 (by decide), h.fixed 9 (by decide), one]
    · intro r safe
      have outside : r ≠ 7 := fun eq => safe (eq.symm ▸ (by decide : (7 : ℕ) ∈ expansionNodeScratch))
      change Function.update t.nr 7 (t.nr 7 + t.nr 9) r = s.nr r
      rw [Function.update_of_ne outside]
      exact (fixed r (by simp [expansionNodeScratch] at safe ⊢; omega)).trans (h.fixed r safe)
    · intro j below
      change t.nm _ = _
      rw [effect]
      by_cases current : j = i
      · subst j
        exact Function.update_self _ _ _
      · have earlier : j < i := by omega
        have different : (expansionCycleRow s j).representative ≠ (expansionCycleRow s i).representative :=
          fun eq => current (distinct j (earlier.trans within) i within eq)
        rw [Function.update_of_ne (by omega)]
        exact h.records j earlier
    · intro address away
      change t.nm address = _
      rw [effect, Function.update_of_ne (away i (by omega))]
      exact h.kept address (fun j hj => away j (by omega))
  obtain ⟨_, final, run⟩ := countedLoopFromZero_correct 9 7 19 (s.nr 19) 12
    publishExpansionNodeCell inv (s := s) entry running first control next
  have steps : 1 + (s.nr 19 * (12 + 3) + 1) = 15 * s.nr 19 + 2 := by omega
  rw [steps] at run
  exact ⟨_, run, final.ready, final.records, final.kept, final.real, final.realRegisters, final.fixed⟩

def publishExpansionSplit : List ArithmeticInstruction :=
  appendBlock publishExpansionRepresentatives publishExpansionNodes

theorem publishExpansionSplit_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (globalBelowScratch : s.nr 57 + s.nr 55 ≤ s.nr 79)
    (globalBelowRegistry : s.nr 57 + s.nr 55 ≤ s.nr 74) (registryBelowCycle : s.nr 74 + s.nr 55 ≤ s.nr 18)
    (inRange : ∀ i < s.nr 19, (expansionCycleRow s i).representative < s.nr 55)
    (distinct : ∀ i < s.nr 19, ∀ j < s.nr 19,
      (expansionCycleRow s i).representative = (expansionCycleRow s j).representative → i = j) :
    ∃ t, BlockRuns publishExpansionSplit (9 * s.nr 55 + 15 * s.nr 19 + 4) s t ∧ t.halted = false ∧
      (∀ v < s.nr 55, t.nm (s.nr 57 + v) =
        if s.nm (s.nr 79 + v) < s.nr 55 then s.nm (s.nr 79 + v) else s.nm (s.nr 57 + v)) ∧
      (∀ j < s.nr 19, t.nm (s.nr 74 + (expansionCycleRow s j).representative) = (expansionCycleRow s j).node) ∧
      (∀ a, (a < s.nr 57 ∨ s.nr 57 + s.nr 55 ≤ a) →
        (∀ j < s.nr 19, a ≠ s.nr 74 + (expansionCycleRow s j).representative) → t.nm a = s.nm a) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 7, 10, 15, 16, 17, 25] → t.nr r = s.nr r := by
  obtain ⟨m, first, live, natural, real, rr, fixed⟩ :=
    publishExpansionRepresentatives_spec entry running one globalBelowScratch
  let seed := {m with pc := 0}
  have memoryOutside (a : ℕ) (away : a < s.nr 57 ∨ s.nr 57 + s.nr 55 ≤ a) : m.nm a = s.nm a :=
    (congrFun natural a).trans (expandedRepresentativeMemory_outside s away)
  have sameRow (j : ℕ) : expansionCycleRow seed j = expansionCycleRow s j := by
    unfold expansionCycleRow matchingCycleChildAt
    change MatchingCycleChild.mk (m.nm (m.nr 18 + 4 * j)) (m.nm (m.nr 18 + 4 * j + 1))
      (m.nm (m.nr 18 + 4 * j + 2)) (m.nm (m.nr 18 + 4 * j + 3)) = _
    rw [fixed 18 (by decide), memoryOutside (s.nr 18 + 4 * j) (Or.inr (by omega)),
      memoryOutside (s.nr 18 + 4 * j + 1) (Or.inr (by omega)),
      memoryOutside (s.nr 18 + 4 * j + 2) (Or.inr (by omega)),
      memoryOutside (s.nr 18 + 4 * j + 3) (Or.inr (by omega))]
  have lengthEq : seed.nr 19 = s.nr 19 := fixed 19 (by decide)
  have sizeEq : seed.nr 55 = s.nr 55 := fixed 55 (by decide)
  have registryEq : seed.nr 74 = s.nr 74 := fixed 74 (by decide)
  obtain ⟨t, nodes, ready, records, kept, lastReal, lastRr, lastFixed⟩ := publishExpansionNodes_spec
    (s := seed) rfl live ((fixed 9 (by decide)).trans one)
    (by rw [sizeEq, registryEq, show seed.nr 18 = _ from fixed 18 (by decide)]; exact registryBelowCycle)
    (fun j hj => by rw [sameRow, sizeEq]; exact inRange j (lengthEq ▸ hj))
    (fun i hi j hj eq => distinct i (lengthEq ▸ hi) j (lengthEq ▸ hj) (by simpa only [sameRow] using eq))
  have time : (9 * s.nr 55 + 2) + (15 * seed.nr 19 + 2) = 9 * s.nr 55 + 15 * s.nr 19 + 4 := by
    rw [lengthEq]
    omega
  have composed := first.append nodes
  rw [time] at composed
  refine ⟨_, composed, ready, ?_, ?_, ?_, lastReal.trans real, lastRr.trans rr, ?_⟩
  · intro v bounded
    change t.nm (s.nr 57 + v) = _
    rw [kept _ (fun j _ => by rw [registryEq]; omega), natural]
    exact expandedRepresentativeMemory_at s bounded
  · intro j within
    change t.nm (s.nr 74 + (expansionCycleRow s j).representative) = (expansionCycleRow s j).node
    have word := records j (lengthEq.symm ▸ within)
    simpa only [registryEq, sameRow] using word
  · intro a away notWritten
    exact (kept a (fun j hj => by rw [registryEq, sameRow]; exact notWritten j (lengthEq ▸ hj))).trans (memoryOutside a away)
  · intro r untouched
    exact (lastFixed r (by simp [expansionNodeScratch] at untouched ⊢; omega)).trans
      (fixed r (by simp at untouched ⊢; omega))

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionRegistryRAM

/-! matching/AlternatingForestGrowPairs.lean -/
section RppSource_AlternatingForestGrowPairs
namespace VehicleRoutingSurvey.Routing

/-- Restore the inner/outer pairs along the selected blossom expansion route. The
last vertex returned is the outer predecessor of the restored blossom base. -/
def AlternatingForestState.growPairs {α : Type*} [DecidableEq α] (state : AlternatingForestState α)
    (source : α) : List α → AlternatingForestState α × α
  | inner :: outer :: rest => (state.grow source inner outer).growPairs outer rest
  | _ => (state, source)

theorem AlternatingForestState.growPairs_preserves {α : Type*} [DecidableEq α]
    {state : AlternatingForestState α} {source x : α} (vertices : List α) (outside : x ∉ vertices) :
    let result := state.growPairs source vertices
    result.1.role x = state.role x ∧ result.1.depth x = state.depth x := by
  induction vertices using List.twoStepInduction generalizing state source with
  | nil => exact ⟨rfl, rfl⟩
  | singleton _ => exact ⟨rfl, rfl⟩
  | cons_cons inner outer rest ih _ =>
    simp only [List.mem_cons, not_or] at outside
    have unaffected := ih (state := state.grow source inner outer) (source := outer) outside.2.2
    simpa [growPairs, grow, outside.1, outside.2.1] using unaffected

theorem AlternatingForestState.growPairs_valid {α : Type*} [DecidableEq α]
    {state : AlternatingForestState α} {mate : α → Option α} {tight : α → α → Prop} {source : α}
    (valid : state.valid mate tight) (sourceOuter : ∃ parent, state.role source = .outer parent)
    (vertices : List α) (distinct : vertices.Nodup) (even : vertices.length % 2 = 0)
    (unlabelled : ∀ v ∈ vertices, state.role v = .unlabelled)
    (path : (source :: vertices).IsChain tight)
    (oldPairs : ∀ a b, s(a, b) ∈ alternatingEdges vertices → mate a = some b ∧ mate b = some a) :
    let result := state.growPairs source vertices
    result.1.valid mate tight ∧ (∃ parent, result.1.role result.2 = .outer parent) ∧
      result.1.depth result.2 = state.depth source + vertices.length ∧
      (source :: vertices).getLast? = some result.2 := by
  induction vertices using List.twoStepInduction generalizing state source with
  | nil => exact ⟨valid, sourceOuter, by simp [growPairs], rfl⟩
  | singleton a => simp at even
  | cons_cons inner outer rest ih _ =>
    obtain ⟨⟨different, noInner⟩, noOuter, restDistinct⟩ :
        (inner ≠ outer ∧ inner ∉ rest) ∧ outer ∉ rest ∧ rest.Nodup := by
      simpa only [List.nodup_cons, List.mem_cons, not_or] using distinct
    obtain ⟨parent, fromOuter⟩ := sourceOuter
    have incoming := List.isChain_cons_cons.mp path
    have pairPath := List.isChain_cons_cons.mp incoming.2
    have pairMates := oldPairs inner outer List.mem_cons_self
    let grown := state.grow source inner outer
    have grownValid : grown.valid mate tight := grow_valid valid fromOuter
      (unlabelled inner List.mem_cons_self) (unlabelled outer (List.mem_cons_of_mem _ List.mem_cons_self))
      different pairMates.1 pairMates.2 incoming.1 pairPath.1
    have grownOuter : ∃ p, grown.role outer = .outer p := ⟨some inner, by simp [grown, grow, different.symm]⟩
    have restEven : rest.length % 2 = 0 := by
      simp only [List.length_cons] at even
      omega
    have restDormant : ∀ v ∈ rest, grown.role v = .unlabelled := by
      intro v hv
      have notInner : v ≠ inner := fun eq => noInner (eq ▸ hv)
      have notOuter : v ≠ outer := fun eq => noOuter (eq ▸ hv)
      simpa [grown, grow, notInner, notOuter] using
        unlabelled v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv))
    have restPairs : ∀ a b, s(a, b) ∈ alternatingEdges rest → mate a = some b ∧ mate b = some a :=
      fun a b h => oldPairs a b (List.mem_cons_of_mem _ h)
    obtain ⟨newValid, newOuter, depthEq, endAt⟩ := ih (state := grown) (source := outer) grownValid
      grownOuter restDistinct restEven restDormant pairPath.2 restPairs
    change let result := grown.growPairs outer rest
      result.1.valid mate tight ∧ (∃ parent, result.1.role result.2 = .outer parent) ∧
        result.1.depth result.2 = state.depth source + (inner :: outer :: rest).length ∧
        (source :: inner :: outer :: rest).getLast? = some result.2
    refine ⟨newValid, newOuter, ?_, ?_⟩
    · have secondDepth : grown.depth outer = state.depth source + 2 := by
        simp [grown, grow, different.symm]
      rw [depthEq, secondDepth]
      simp only [List.length_cons]
      omega
    · simpa only [List.getLast?_cons_cons] using endAt

end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestGrowPairs


