-- Prove2me | Definitions.Def_OAIQ18Pg001
-- name    : OAIQ18Pg001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T15:53:54.277695+00:00
-- url     : https://prove2.me/theorems/0b849064-25cd-43b4-959b-39577989729f
-- title:
--   Definitions bundle OAIQ18Pg001 of the split of OpenAI, An infinite finitely presented periodic group
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SourceBurnside.thm_main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented periodic group*, OpenAI Math Release, September 23, 2026, result family 247, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 588 declarations of OpenAI's Lean: 254 definitions, 25 inductive types or structures, 5 instances and 304 theorems. The definitions and types are `OAI.SourceBurnside.CompactInit.K`, `OAI.SourceBurnside.CompactInit.layout`, `OAI.SourceBurnside.CompactInit.pairs`, `OAI.SourceBurnside.CompactProgram.bootTime`, `OAI.SourceBurnside.CompactStacks.State`, `OAI.SourceBurnside.CompactStacks.block`, `OAI.SourceBurnside.CompactStacks.clock`, `OAI.SourceBurnside.CompactStacks.config`, `OAI.SourceBurnside.CompactStacks.encode`, `OAI.SourceBurnside.CompactStacks.machine`, `OAI.SourceBurnside.CompactStacks.operation`, `OAI.SourceBurnside.CompactStacks.pred`, `OAI.SourceBurnside.CompactStacks.registers`, `OAI.SourceBurnside.CompactStacks.seeking`, `OAI.SourceBurnside.CompactStacks.ticks`, `OAI.SourceBurnside.CompactStacks.words`, `OAI.SourceBurnside.ConcreteSource.dilation`, `OAI.SourceBurnside.CountLength.K`, `OAI.SourceBurnside.CountLength.countBits`, `OAI.SourceBurnside.CountLength.slots`, `OAI.SourceBurnside.CutReduction.candidates`, `OAI.SourceBurnside.CutReduction.chunkSum`, `OAI.SourceBurnside.CutReduction.eval`, `OAI.SourceBurnside.CutReduction.join`, `OAI.SourceBurnside.CutReduction.language`, `OAI.SourceBurnside.CutReduction.letterSum`, `OAI.SourceBurnside.Cuts.Interval`, `OAI.SourceBurnside.Cuts.NoCut`, `OAI.SourceBurnside.Cuts.parse`, `OAI.SourceBurnside.DirectCancellation.EligibleInterval`, `OAI.SourceBurnside.DirectCancellation.candidates`, `OAI.SourceBurnside.DirectCancellation.eval`, `OAI.SourceBurnside.DirectCancellation.firstLongRun`, `OAI.SourceBurnside.DirectCancellation.spell`, `OAI.SourceBurnside.DropPadding.K`, `OAI.SourceBurnside.Elementary.e`, `OAI.SourceBurnside.Elementary.representation`, `OAI.SourceBurnside.FiniteCode.config`, `OAI.SourceBurnside.FiniteCode.enumeration`, `OAI.SourceBurnside.FiniteCode.program` and 239 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory/PeriodicGroups, in whole or in part: `PeriodicGroups_Algebra_DirectCancellation`, `PeriodicGroups_Algebra_HierarchyGrowth`, `PeriodicGroups_Algebra_MatrixTests`, `PeriodicGroups_Algebra_PacketIntervals`, `PeriodicGroups_Algebra_WordAlgebra`, `PeriodicGroups_Formulas_BooleanCircuits`, `PeriodicGroups_Formulas_PredicateCompilation`, `PeriodicGroups_Homology_RelativeHomology`, `PeriodicGroups_Machines_ArithmeticDevices`, `PeriodicGroups_Machines_BinaryRegisters`, `PeriodicGroups_Machines_Compilation`, `PeriodicGroups_Machines_InputEncoding`, `PeriodicGroups_Machines_ProgramAssembly`, `PeriodicGroups_Machines_ProgramFixedPoint`, `PeriodicGroups_Machines_RegisterLoops`, `PeriodicGroups_Machines_RegisterOperators`, `PeriodicGroups_Machines_StackCompression`, `PeriodicGroups_Machines_TapePrograms`, `PeriodicGroups_Machines_TimedExecution`, `PeriodicGroups_Machines_UniversalInput`, `PeriodicGroups_Machines_UniversalStack`, `PeriodicGroups_Rules_GeometricRelations`, `PeriodicGroups_Rules_Recognizer`, `PeriodicGroups_Rules_Transactions`, `PeriodicGroups_Steinberg_BlockEmbeddings`, `PeriodicGroups_Steinberg_CoefficientQuotients`, `PeriodicGroups_Steinberg_KernelRelations`, `PeriodicGroups_Steinberg_MonomialPresentation`, `PeriodicGroups_Steinberg_PresentationModel`.
--
--   **Imports.** It imports the published bundle `Def_PeriodicGroup`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ18Pg005`, `OAIQ18Pg006`, `OAIQ18Pg007`, `OAIQ18Pg008` and `OAIQ18Pg010`.
-- source:
--   OpenAI, An infinite finitely presented periodic group, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 247; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/PeriodicGroups at commit adc7f12

import Mathlib
import Definitions.Def_PeriodicGroup

section
-- module Solutions.OAIQ18_PG.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Homology_RelativeHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SourceBurnside.Stability
noncomputable section
open Classical CategoryTheory
namespace RationalBar
variable (G : Type) [Group G]
abbrev C1 := G →₀ ℚ

end RationalBar
end
end SourceBurnside.Stability

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_Transactions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
variable {q : ℕ}
  [NeZero q]
  {d : ℕ}

section LocalEdits
variable {N : ℕ} {α : Type*}
lemma ofFn_take_congr (f g : Fin N → α) (i : ℕ)
    (h : ∀ j, j.val < i → f j = g j) : (List.ofFn f).take i = (List.ofFn g).take i := by
  apply List.ext_getElem (by simp)
  intro j hj hk
  simp only [List.getElem_take,List.getElem_ofFn]
  apply h
  simp only [List.length_take,List.length_ofFn] at hj
  change j < i
  omega

lemma ofFn_drop_congr (f g : Fin N → α) (i : ℕ)
    (h : ∀ j, i ≤ j.val → f j = g j) : (List.ofFn f).drop i = (List.ofFn g).drop i := by
  apply List.ext_getElem (by simp)
  intro j hj hk
  simp only [List.getElem_drop,List.getElem_ofFn]
  apply h
  change i ≤ i+j
  omega

lemma ofFn_split_one (f : Fin N → α) (i : Fin N) :
    List.ofFn f = (List.ofFn f).take i.val ++ [f i] ++ (List.ofFn f).drop (i.val+1) := by
  conv_lhs => rw [←List.take_append_drop i.val (List.ofFn f)]
  rw [List.drop_eq_getElem_cons (by simp)]
  simp

lemma ofFn_split_two (f : Fin N → α) (i j : Fin N) (hij : i.val+1=j.val) :
    List.ofFn f = (List.ofFn f).take i.val ++ [f i,f j] ++ (List.ofFn f).drop (j.val+1) := by
  have ht : (List.ofFn f).drop (i.val+1) = f j :: (List.ofFn f).drop (j.val+1) := by
    rw [hij,List.drop_eq_getElem_cons (by simp)]
    simp
  conv_lhs => rw [ofFn_split_one f i]
  rw [ht]
  simp

end LocalEdits

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_TapePrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.OneTape

inductive Move | left | stay | right
  deriving DecidableEq

def Move.shift : Move → ℤ | .left => -1 | .stay => 0 | .right => 1

structure Command (Γ Q : Type*) where
  write : Γ
  next : Q
  move : Move

structure Config (Γ Q : Type*) where
  position : ℤ
  state : Q
  tape : ℤ → Γ

structure Label (Γ Q : Type*) where
  symbol : Γ
  origin : Bool
  head : Option Q
  deriving DecidableEq, Fintype

variable {Γ Q : Type*}

def Config.cell (C : Config Γ Q) (j : ℤ) : Label Γ Q :=
  ⟨C.tape j,decide (j=0),if j=C.position then some C.state else none⟩

def step (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) : Config Γ Q :=
  let cmd := δ C.state (C.tape C.position)
  ⟨C.position+cmd.move.shift,cmd.next,Function.update C.tape C.position cmd.write⟩

def localStep (δ : Q → Γ → Command Γ Q) (left center right : Label Γ Q) : Label Γ Q :=
  let entered := match left.head with
    | some q => let c := δ q left.symbol
                if c.move=Move.right then some c.next else none
    | none => none
  let enteredRight := match right.head with
    | some q => let c := δ q right.symbol
                if c.move=Move.left then some c.next else none
    | none => none
  match center.head with
  | some q => let c := δ q center.symbol
              ⟨c.write,center.origin,if c.move=Move.stay then some c.next else none⟩
  | none => ⟨center.symbol,center.origin,entered.or enteredRight⟩

theorem local_cell (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) (j : ℤ) :
    localStep δ (C.cell (j-1)) (C.cell j) (C.cell (j+1))=(step δ C).cell j := by
  by_cases h0 : j=C.position
  · subst j
    cases he : (δ C.state (C.tape C.position)).move <;>
      simp [localStep,Config.cell,step,Move.shift,he]
  · by_cases hm : j-1=C.position
    · have hp : j+1≠C.position := by omega
      cases he : (δ C.state (C.tape C.position)).move <;>
        simp_all [localStep,Config.cell,step,Move.shift,Function.update] <;> omega
    · by_cases hp : j+1=C.position
      · cases he : (δ C.state (C.tape C.position)).move <;>
          simp_all [localStep,Config.cell,step,Move.shift,Function.update] <;> omega
      · have hml : j≠C.position-1 := by omega
        have hpr : j≠C.position+1 := by omega
        cases he : (δ C.state (C.tape C.position)).move <;>
          simp_all [localStep,Config.cell,step,Move.shift,Function.update]
        omega

def run (δ : Q → Γ → Command Γ Q) (initial : Config Γ Q) : ℕ → Config Γ Q
  | 0 => initial
  | t+1 => step δ (run δ initial t)

lemma step_position_bound (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) :
    C.position-1≤(step δ C).position ∧ (step δ C).position≤C.position+1 := by
  unfold step
  cases he : (δ C.state (C.tape C.position)).move <;> simp [Move.shift,he]
  omega

lemma run_position_bound (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) (t : ℕ) :
    C.position-(t:ℤ)≤(run δ C t).position ∧ (run δ C t).position≤C.position+(t:ℤ) := by
  induction t with
  | zero => simp [run]
  | succ t ih =>
    have hh := step_position_bound δ (run δ C t)
    simp only [run,Nat.cast_add,Nat.cast_one]
    omega

lemma run_tape_untouched (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) (t : ℕ) (j : ℤ)
    (h : ∀ s<t, (run δ C s).position≠j) : (run δ C t).tape j=C.tape j := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change Function.update (run δ C t).tape (run δ C t).position _ j=C.tape j
    rw [Function.update_of_ne (h t (Nat.lt_succ_self t)).symm]
    exact ih (fun s hs => h s (Nat.lt_succ_of_lt hs))

end SourceBurnside.OneTape

namespace SourceBurnside.OneTape
variable {Γ Q : Type*}
lemma run_from (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) (s t : ℕ) :
    run δ C (s+t)=run δ (run δ C s) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change step δ (run δ C (s+t)) = step δ (run δ (run δ C s) t)
    exact congrArg (step δ) ih
lemma run_succ_start (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) (t : ℕ) :
    run δ C (t+1)=run δ (step δ C) t := by
  simpa [run,Nat.add_comm] using run_from δ C 1 t
end SourceBurnside.OneTape

namespace SourceBurnside.StackMachine
open OneTape
noncomputable section
local instance tapeProgramsDecidableEq (α : Sort*) : DecidableEq α :=
  Classical.typeDecidableEq α

inductive Instr (K Γ Q : Type*)
  | push (k : K) (a : Γ) (next : Q)
  | pop (k : K) (next : Option Γ → Q)
  | halt
  deriving Fintype

structure Config (K Γ Q : Type*) where
  state : Q
  store : K → List Γ

variable {K Γ Q : Type*} [DecidableEq K]

def next (P : Q → Instr K Γ Q) (C : Config K Γ Q) : Config K Γ Q :=
  match P C.state with
  | .push k a q => ⟨q,Function.update C.store k (C.store k++[a])⟩
  | .pop k q => ⟨q (C.store k).getLast?,Function.update C.store k (C.store k).dropLast⟩
  | .halt => C

def ticks (P : Q → Instr K Γ Q) (C : Config K Γ Q) : ℕ :=
  match P C.state with
  | .push k _ _ | .pop k _ => 2*(C.store k).length+3
  | .halt => 0

structure Symbol (K Γ : Type*) where
  origin : Bool
  track : K → Option Γ
  deriving Fintype

inductive State (K Γ Q : Type*)
  | ready (q : Q)
  | pushFind (k : K) (a : Γ) (q : Q)
  | popFind (k : K) (q : Option Γ → Q)
  | popRead (k : K) (q : Option Γ → Q)
  | back (q : Q)
  deriving Fintype

def compile (P : Q → Instr K Γ Q) : State K Γ Q → Symbol K Γ →
    OneTape.Command (Symbol K Γ) (State K Γ Q)
  | .ready q,s => match P q with
    | .push k a q' => ⟨s,.pushFind k a q',.right⟩
    | .pop k q' => ⟨s,.popFind k q',.right⟩
    | .halt => ⟨s,.ready q,.stay⟩
  | .pushFind k a q,s => if (s.track k).isSome then ⟨s,.pushFind k a q,.right⟩
      else ⟨⟨s.origin,Function.update s.track k (some a)⟩,.back q,.left⟩
  | .popFind k q,s => if (s.track k).isSome then ⟨s,.popFind k q,.right⟩
      else ⟨s,.popRead k q,.left⟩
  | .popRead k q,s => if s.origin then ⟨s,.ready (q none),.stay⟩
      else ⟨⟨s.origin,Function.update s.track k none⟩,.back (q (s.track k)),.left⟩
  | .back q,s => if s.origin then ⟨s,.ready q,.stay⟩ else ⟨s,.back q,.left⟩

def tape (s : K → List Γ) (j : ℤ) : Symbol K Γ :=
  ⟨decide (j=0),fun k => if 0<j then (s k)[j.toNat-1]? else none⟩
def place (s : K → List Γ) (q : State K Γ Q) (j : ℤ) :
    OneTape.Config (Symbol K Γ) (State K Γ Q) := ⟨j,q,tape s⟩
def encode (C : Config K Γ Q) : OneTape.Config (Symbol K Γ) (State K Γ Q) :=
  place C.store (.ready C.state) 0

omit [DecidableEq K] in
@[simp] lemma tape_origin (s : K → List Γ) (j : ℤ) : (tape s j).origin=decide (j=0) := rfl
omit [DecidableEq K] in
@[simp] lemma tape_track_succ (s : K → List Γ) (k : K) (n : ℕ) :
    (tape s ((n:ℤ)+1)).track k=(s k)[n]? := by simp [tape]
omit [DecidableEq K] in
@[simp] lemma tape_track_zero (s : K → List Γ) (k : K) : (tape s 0).track k=none := by
  simp [tape]

lemma step_back_zero (P : Q → Instr K Γ Q) (s : K → List Γ) (q : Q) :
    OneTape.step (compile P) (place s (.back q) 0)=place s (.ready q) 0 := by
  simp [OneTape.step,compile,place,OneTape.Move.shift]

lemma step_back_succ (P : Q → Instr K Γ Q) (s : K → List Γ) (q : Q) (n : ℕ) :
    OneTape.step (compile P) (place s (.back q) ((n:ℤ)+1))=place s (.back q) n := by
  have hn : (n:ℤ)+1≠0 := by omega
  simp [OneTape.step,compile,place,OneTape.Move.shift,hn]

lemma run_back (P : Q → Instr K Γ Q) (s : K → List Γ) (q : Q) (n : ℕ) :
    OneTape.run (compile P) (place s (.back q) n) (n+1)=place s (.ready q) 0 := by
  induction n with
  | zero => exact step_back_zero P s q
  | succ n ih =>
    rw [OneTape.run_succ_start]
    simpa only [Nat.cast_add,Nat.cast_one,step_back_succ] using ih

lemma step_push_scan (P : Q → Instr K Γ Q) (s : K → List Γ) (k : K) (a : Γ)
    (q : Q) (n : ℕ) (hn : n<(s k).length) :
    OneTape.step (compile P) (place s (.pushFind k a q) ((n:ℤ)+1))=
      place s (.pushFind k a q) ((n:ℤ)+2) := by
  have ht : ((s k)[n]?).isSome = true := by simpa using hn
  simp [OneTape.step,compile,place,tape_track_succ,ht,OneTape.Move.shift,add_assoc]

lemma step_pop_scan (P : Q → Instr K Γ Q) (s : K → List Γ) (k : K)
    (q : Option Γ → Q) (n : ℕ) (hn : n<(s k).length) :
    OneTape.step (compile P) (place s (.popFind k q) ((n:ℤ)+1))=
      place s (.popFind k q) ((n:ℤ)+2) := by
  have ht : ((s k)[n]?).isSome = true := by simpa using hn
  simp [OneTape.step,compile,place,tape_track_succ,ht,OneTape.Move.shift,add_assoc]

lemma run_push_scan (P : Q → Instr K Γ Q) (s : K → List Γ) (k : K) (a : Γ)
    (q : Q) (n : ℕ) (hn : n≤(s k).length) :
    OneTape.run (compile P) (place s (.pushFind k a q) 1) n=
      place s (.pushFind k a q) ((n:ℤ)+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [OneTape.run,ih (by omega),step_push_scan P s k a q n (by omega)]
    congr 1

lemma run_pop_scan (P : Q → Instr K Γ Q) (s : K → List Γ) (k : K)
    (q : Option Γ → Q) (n : ℕ) (hn : n≤(s k).length) :
    OneTape.run (compile P) (place s (.popFind k q) 1) n=
      place s (.popFind k q) ((n:ℤ)+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [OneTape.run,ih (by omega),step_pop_scan P s k q n (by omega)]
    congr 1

lemma step_pop_turn (P : Q → Instr K Γ Q) (s : K → List Γ) (k : K)
    (q : Option Γ → Q) :
    OneTape.step (compile P) (place s (.popFind k q) ((s k).length+1))=
      place s (.popRead k q) (s k).length := by
  simp [OneTape.step,compile,place,tape_track_succ,OneTape.Move.shift]

lemma step_pop_empty (P : Q → Instr K Γ Q) (s : K → List Γ) (k : K)
    (q : Option Γ → Q) :
    OneTape.step (compile P) (place s (.popRead k q) 0)=place s (.ready (q none)) 0 := by
  simp [OneTape.step,compile,place,OneTape.Move.shift]

def exec (P : Q → Instr K Γ Q) (C : Config K Γ Q) : ℕ → Config K Γ Q
  | 0 => C
  | n+1 => next P (exec P C n)
def clock (P : Q → Instr K Γ Q) (C : Config K Γ Q) : ℕ → ℕ
  | 0 => 0
  | n+1 => clock P C n + ticks P (exec P C n)

lemma next_length (P : Q → Instr K Γ Q) (C : Config K Γ Q) (k : K) :
    ((next P C).store k).length≤(C.store k).length+1 := by
  cases h : P C.state with
  | halt => simp [next,h]
  | push i a q =>
    by_cases hi : k=i
    · subst k; simp [next,h]
    · simp [next,h,Function.update_of_ne hi]
  | pop i q =>
    by_cases hi : k=i
    · subst k; simp [next,h]; omega
    · simp [next,h,Function.update_of_ne hi]

lemma exec_length (P : Q → Instr K Γ Q) (C : Config K Γ Q) (n : ℕ) (k : K) :
    ((exec P C n).store k).length≤(C.store k).length+n := by
  induction n with
  | zero => simp [exec]
  | succ n ih =>
    have hh := next_length P (exec P C n) k
    simp only [exec]
    omega

omit [DecidableEq K] in
lemma ticks_bound (P : Q → Instr K Γ Q) (C : Config K Γ Q) (m : ℕ)
    (h : ∀ k, (C.store k).length ≤ m) : ticks P C≤2*m+3 := by
  cases he : P C.state with
  | halt => simp [ticks,he]
  | push i a q => simpa [ticks,he] using Nat.add_le_add_right (Nat.mul_le_mul_left 2 (h i)) 3
  | pop i q => simpa [ticks,he] using Nat.add_le_add_right (Nat.mul_le_mul_left 2 (h i)) 3

theorem clock_bound (P : Q → Instr K Γ Q) (C : Config K Γ Q) (m n : ℕ)
    (h : ∀ k, (C.store k).length ≤ m) : clock P C n ≤ n*(2*(m+n)+3) := by
  induction n with
  | zero => simp [clock]
  | succ n ih =>
    have hb : ticks P (exec P C n)≤2*(m+n)+3 :=
      ticks_bound P (exec P C n) (m+n) (fun k =>
        (exec_length P C n k).trans (Nat.add_le_add_right (h k) n))
    simp only [clock]
    nlinarith

lemma halt_step (P : Q → Instr K Γ Q) (C : Config K Γ Q) (h : P C.state=.halt) :
    OneTape.step (compile P) (encode C)=encode C := by
  simp [OneTape.step,compile,encode,place,h,OneTape.Move.shift]

lemma halt_run (P : Q → Instr K Γ Q) (C : Config K Γ Q) (h : P C.state=.halt) (n : ℕ) :
    OneTape.run (compile P) (encode C) n=encode C := by
  induction n with
  | zero => rfl
  | succ n ih => rw [OneTape.run,ih,halt_step P C h]

end
end SourceBurnside.StackMachine

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_UniversalStack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.UniversalStack
open StackMachine
noncomputable section
variable {K : Type*} [DecidableEq K]

inductive Instruction (K : Type*)
  | push (k : K) (b : Bool) (go : ℕ)
  | pop (k : K) (zeroTarget one empty : ℕ)
  | halt (result : Bool)
  deriving DecidableEq

inductive Token (K : Type*)
  | push (k : K) (b : Bool)
  | pop (k : K)
  | halt (result : Bool)
  | bit (b : Bool)
  | tick | sep | stop
  deriving DecidableEq, Fintype

inductive Stack (K : Type*)
  | reg (k : K) | front | back | pc
  deriving DecidableEq, Fintype

inductive Target
  | beforeTwo | beforeOne | during | after
  deriving DecidableEq
instance instFintypeTarget : Fintype Target := Fintype.ofList [.beforeTwo,.beforeOne,.during,.after]
  (by intro x; cases x <;> simp)
inductive Mode
  | skip | opcode | target (t : Target)
  deriving DecidableEq, Fintype
inductive State (K : Type*)
  | reset | restore (a : Token K) | pick
  | read (m : Mode) | remember (m : Mode) (a : Token K)
  | push (k : K) (b : Bool) | pop (k : K) | saveTarget
  | stopped (result : Bool)
  deriving DecidableEq, Fintype

def afterToken : Mode → Token K → State K
  | .skip,.stop => .pick
  | .skip,_ => .read .skip
  | .opcode,.push k b => .push k b
  | .opcode,.pop k => .pop k
  | .opcode,.halt b => .stopped b
  | .opcode,_ => .stopped false
  | .target _,.stop => .reset
  | .target .beforeTwo,.sep => .read (.target .beforeOne)
  | .target .beforeOne,.sep => .read (.target .during)
  | .target .during,.sep | .target .after,.sep => .read (.target .after)
  | .target .during,.tick => .saveTarget
  | .target t,.tick => .read (.target t)
  | .target _,_ => .stopped false

def interpreter : State K → StackMachine.Instr (Stack K) (Token K) (State K)
  | .reset => .pop .back (fun a => match a with | none => .pick | some a => .restore a)
  | .restore a => .push .front a .reset
  | .pick => .pop .pc (fun a => if a.isSome then .read .skip else .read .opcode)
  | .read m => .pop .front (fun a => match a with | none => .stopped false | some a => .remember m a)
  | .remember m a => .push .back a (afterToken m a)
  | .push k b => .push (.reg k) (.bit b) (.read (.target .during))
  | .pop k => .pop (.reg k) (fun a => .read (.target (match a with
      | some (.bit false) => .during | some (.bit true) => .beforeOne | _ => .beforeTwo)))
  | .saveTarget => .push .pc .tick (.read (.target .during))
  | .stopped _ => .halt

def encodeInstruction : Instruction K → List (Token K)
  | .push k b j => [.push k b] ++ List.replicate j .tick ++ [.stop]
  | .pop k z o e => [.pop k] ++ List.replicate z .tick ++ [.sep] ++
      List.replicate o .tick ++ [.sep] ++ List.replicate e .tick ++ [.stop]
  | .halt b => [.halt b,.stop]
def encodeProgram (P : List (Instruction K)) : List (Token K) := P.flatMap encodeInstruction

def config (s : State K) (regs : K → List Bool) (front back : List (Token K)) (pc : ℕ) :
    StackMachine.Config (Stack K) (Token K) (State K) :=
  ⟨s, fun k => match k with
    | .reg k => (regs k).map Token.bit
    | .front => front.reverse | .back => back | .pc => List.replicate pc .tick⟩

omit [DecidableEq K] in
@[simp] lemma config_state (s : State K) (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    (config s r f b pc).state=s := rfl

lemma exec_from {A Γ Q : Type*} [DecidableEq A] (P : Q → StackMachine.Instr A Γ Q)
    (C : StackMachine.Config A Γ Q) (n m : ℕ) :
    exec P C (n+m)=exec P (exec P C n) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change next P (exec P C (n+m))=next P (exec P (exec P C n) m)
    exact congrArg (next P) ih
lemma exec_start {A Γ Q : Type*} [DecidableEq A] (P : Q → StackMachine.Instr A Γ Q)
    (C : StackMachine.Config A Γ Q) (n : ℕ) :
    exec P C (n+1)=exec P (next P C) n := by
  rw [Nat.add_comm]
  exact exec_from P C 1 n

lemma config_ext {A Γ Q : Type*} {C D : StackMachine.Config A Γ Q}
    (hs : C.state=D.state) (hk : C.store=D.store) : C=D := by
  cases C; cases D
  cases hs; cases hk
  rfl

lemma read_token (m : Mode) (a : Token K) (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read m) r (a::f) b pc) 2 =
      config (afterToken m a) r f (b++[a]) pc := by
  apply config_ext
  · simp [exec,next,interpreter,config,List.getLast?_reverse]
  · funext k
    cases k <;> simp [exec,next,interpreter,config,List.reverse_cons]

lemma save_target (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    next interpreter (config .saveTarget r f b pc)=
      config (.read (.target .during)) r f b (pc+1) := by
  apply config_ext
  · rfl
  · funext k
    cases k <;> simp [next,interpreter,config,List.replicate_succ']

lemma reset_token (a : Token K) (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config .reset r f (b++[a]) pc) 2 =
      config .reset r (a::f) b pc := by
  apply config_ext
  · simp [exec,next,interpreter,config]
  · funext k
    cases k <;> simp [exec,next,interpreter,config,List.reverse_cons]

lemma reset_empty (r : K → List Bool) (f : List (Token K)) (pc : ℕ) :
    next interpreter (config .reset r f [] pc)=config .pick r f [] pc := by
  apply config_ext
  · rfl
  · funext k
    cases k <;> simp [next,interpreter,config]

lemma reset_all (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config .reset r f b pc) (2*b.length+1)=
      config .pick r (b++f) [] pc := by
  induction b using List.reverseRecOn generalizing f with
  | nil => simpa [exec] using reset_empty r f pc
  | append_singleton b a ih =>
    rw [List.length_append,List.length_singleton,
      show 2*(b.length+1)+1=2+(2*b.length+1) by omega,
      exec_from,reset_token,ih]
    simp

lemma pick_zero (r : K → List Bool) (f b : List (Token K)) :
    next interpreter (config .pick r f b 0)=config (.read .opcode) r f b 0 := by
  apply config_ext
  · rfl
  · funext k
    cases k <;> simp [next,interpreter,config]
lemma pick_succ (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    next interpreter (config .pick r f b (pc+1))=config (.read .skip) r f b pc := by
  apply config_ext
  · simp [next,interpreter,config,List.replicate_succ]
  · funext k
    cases k <;> simp [next,interpreter,config,List.replicate_succ]

omit [DecidableEq K] in
lemma after_skip (a : Token K) (ha : a≠.stop) : afterToken .skip a=.read .skip := by
  cases a <;> simp_all [afterToken]

lemma skip_fragment (v : List (Token K)) (hv : ∀a∈v,a≠.stop)
    (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read .skip) r (v++f) b pc) (2*v.length)=
      config (.read .skip) r f (b++v) pc := by
  induction v generalizing b with
  | nil => simp [exec]
  | cons a v ih =>
    rw [List.length_cons,show 2*(v.length+1)=2+2*v.length by omega,
      exec_from,List.cons_append,read_token,after_skip a (hv a (by simp)),
      ih (fun a ha => hv a (by simp [ha]))]
    simp [List.append_assoc]

def codePrefix : Instruction K → List (Token K)
  | .push k b j => [.push k b] ++ List.replicate j .tick
  | .pop k z o e => [.pop k] ++ List.replicate z .tick ++ [.sep] ++
      List.replicate o .tick ++ [.sep] ++ List.replicate e .tick
  | .halt b => [.halt b]
omit [DecidableEq K] in
lemma encode_end (i : Instruction K) : encodeInstruction i=codePrefix i++[.stop] := by
  cases i <;> rfl
omit [DecidableEq K] in
lemma codePrefix_no_stop (i : Instruction K) : ∀a∈codePrefix i,a≠.stop := by
  cases i <;> simp [codePrefix,List.mem_replicate]
  aesop

lemma skip_instruction (i : Instruction K) (r : K → List Bool)
    (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read .skip) r (encodeInstruction i++f) b pc)
      (2*(encodeInstruction i).length) = config .pick r f (b++encodeInstruction i) pc := by
  rw [encode_end,List.length_append,List.length_singleton,
    show 2*((codePrefix i).length+1)=2*(codePrefix i).length+2 by omega,
    exec_from,List.append_assoc,skip_fragment _ (codePrefix_no_stop i)]
  simpa [afterToken,List.append_assoc] using
    read_token .skip .stop r f (b++codePrefix i) pc

lemma skip_instructions (v : List (Instruction K)) (r : K → List Bool)
    (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config .pick r (encodeProgram v++f) b (v.length+pc))
      (v.length+2*(encodeProgram v).length)=
      config .pick r f (b++encodeProgram v) pc := by
  induction v generalizing b with
  | nil => simp [encodeProgram,exec]
  | cons a v ih =>
    have ht : (a::v).length+2*(encodeProgram (a::v)).length=
        1+(2*(encodeInstruction a).length+(v.length+2*(encodeProgram v).length)) := by
      simp [encodeProgram]
      omega
    rw [ht,exec_from]
    have he : encodeProgram (a::v)=encodeInstruction a++encodeProgram v := rfl
    rw [he,List.append_assoc,List.length_cons,
      show v.length+1+pc=(v.length+pc)+1 by omega]
    change exec interpreter (next interpreter (config .pick r
      (encodeInstruction a++(encodeProgram v++f)) b ((v.length+pc)+1))) _ = _
    rw [pick_succ,exec_from,skip_instruction,ih]
    simp [List.append_assoc]

lemma fetch (v : List (Instruction K)) (r : K → List Bool)
    (f : List (Token K)) :
    exec interpreter (config .pick r (encodeProgram v++f) [] v.length)
      (v.length+2*(encodeProgram v).length+1)=
      config (.read .opcode) r f (encodeProgram v) 0 := by
  rw [exec_from]
  have hh := skip_instructions v r f [] 0
  simp only [Nat.add_zero,List.nil_append] at hh
  rw [hh]
  exact pick_zero r f (encodeProgram v)

omit [DecidableEq K] in
lemma after_target_tick (t : Target) (ht : t≠.during) :
    afterToken (K:=K) (.target t) .tick=.read (.target t) := by
  cases t <;> simp_all [afterToken]

lemma skip_ticks (t : Target) (ht : t≠.during) (n : ℕ)
    (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read (.target t)) r (List.replicate n .tick++f) b pc) (2*n)=
      config (.read (.target t)) r f (b++List.replicate n .tick) pc := by
  induction n generalizing b with
  | zero => simp [exec]
  | succ n ih =>
    rw [show 2*(n+1)=2+2*n by omega,exec_from,List.replicate_succ,List.cons_append,
      read_token,after_target_tick t ht,ih]
    simp [List.append_assoc]

lemma one_target_tick (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read (.target .during)) r (.tick::f) b pc) 3=
      config (.read (.target .during)) r f (b++[.tick]) (pc+1) := by
  change exec interpreter _ (2+1)=_
  rw [exec_from,read_token]
  exact save_target r f (b++[.tick]) pc

lemma read_ticks (n : ℕ) (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read (.target .during)) r (List.replicate n .tick++f) b pc) (3*n)=
      config (.read (.target .during)) r f (b++List.replicate n .tick) (pc+n) := by
  induction n generalizing b pc with
  | zero => simp [exec]
  | succ n ih =>
    rw [show 3*(n+1)=3+3*n by omega,exec_from,List.replicate_succ,List.cons_append,
      one_target_tick,ih]
    simp [List.append_assoc,Nat.add_comm,Nat.add_left_comm]

lemma push_register (k : K) (a : Bool) (r : K → List Bool)
    (f b : List (Token K)) (pc : ℕ) :
    next interpreter (config (.push k a) r f b pc)=
      config (.read (.target .during)) (Function.update r k (r k++[a])) f b pc := by
  apply config_ext
  · rfl
  · funext j
    cases j with
    | reg j => by_cases h : j=k <;> simp [next,interpreter,config,Function.update_apply,h]
    | front => simp [next,interpreter,config]
    | back => simp [next,interpreter,config]
    | pc => simp [next,interpreter,config]

lemma pop_empty (k : K) (r : K → List Bool) (hr : r k=[])
    (f b : List (Token K)) (pc : ℕ) :
    next interpreter (config (.pop k) r f b pc)=
      config (.read (.target .beforeTwo)) r f b pc := by
  apply config_ext
  · simp [next,interpreter,config,hr]
  · funext j
    cases j with
    | reg j => by_cases h : j=k <;> simp [next,interpreter,config,h,hr]
    | front => simp [next,interpreter,config]
    | back => simp [next,interpreter,config]
    | pc => simp [next,interpreter,config]

lemma pop_snoc (k : K) (a : Bool) (r : K → List Bool) (v : List Bool) (hr : r k=v++[a])
    (f b : List (Token K)) (pc : ℕ) :
    next interpreter (config (.pop k) r f b pc)=
      config (.read (.target (if a then .beforeOne else .during)))
        (Function.update r k v) f b pc := by
  apply config_ext
  · cases a <;> simp [next,interpreter,config,hr]
  · funext j
    cases j with
    | reg j => by_cases h : j=k <;> simp [next,interpreter,config,Function.update_apply,h,hr]
    | front => simp [next,interpreter,config]
    | back => simp [next,interpreter,config]
    | pc => simp [next,interpreter,config]

lemma stop_target (t : Target) (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read (.target t)) r (.stop::f) b pc) 2=
      config .reset r f (b++[.stop]) pc := by
  simpa [afterToken] using read_token (.target t) .stop r f b pc

lemma sep_during (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read (.target .during)) r (.sep::f) b pc) 2=
      config (.read (.target .after)) r f (b++[.sep]) pc := by
  exact read_token (.target .during) .sep r f b pc
lemma sep_after (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read (.target .after)) r (.sep::f) b pc) 2=
      config (.read (.target .after)) r f (b++[.sep]) pc := by
  exact read_token (.target .after) .sep r f b pc
lemma sep_beforeOne (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read (.target .beforeOne)) r (.sep::f) b pc) 2=
      config (.read (.target .during)) r f (b++[.sep]) pc := by
  exact read_token (.target .beforeOne) .sep r f b pc
lemma sep_beforeTwo (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read (.target .beforeTwo)) r (.sep::f) b pc) 2=
      config (.read (.target .beforeOne)) r f (b++[.sep]) pc := by
  exact read_token (.target .beforeTwo) .sep r f b pc

def popBody (z o e : ℕ) : List (Token K) :=
  List.replicate z .tick ++ [.sep] ++ List.replicate o .tick ++ [.sep] ++
  List.replicate e .tick ++ [.stop]

def selected : Target → ℕ → ℕ → ℕ → ℕ
  | .during,z,_,_ => z | .beforeOne,_,o,_ => o | .beforeTwo,_,_,e => e | .after,_,_,_ => 0

lemma pop_body (t : Target) (z o e : ℕ) (r : K → List Bool) (f b : List (Token K)) (pc : ℕ) :
    exec interpreter (config (.read (.target t)) r (popBody z o e++f) b pc)
      (2*(z+o+e+3)+selected t z o e)=
      config .reset r f (b++popBody z o e) (pc+selected t z o e) := by
  cases t with
  | during =>
    rw [show 2*(z+o+e+3)+selected .during z o e=3*z+(2+(2*o+(2+(2*e+2)))) by simp [selected]; omega]
    simp only [popBody,List.append_assoc,List.cons_append,List.nil_append]
    rw [exec_from,read_ticks,exec_from,sep_during,exec_from,skip_ticks .after (by decide),
      exec_from,sep_after,exec_from,skip_ticks .after (by decide),stop_target]
    simp [selected,List.append_assoc]
  | beforeOne =>
    rw [show 2*(z+o+e+3)+selected .beforeOne z o e=2*z+(2+(3*o+(2+(2*e+2)))) by simp [selected]; omega]
    simp only [popBody,List.append_assoc,List.cons_append,List.nil_append]
    rw [exec_from,skip_ticks .beforeOne (by decide),exec_from,sep_beforeOne,exec_from,read_ticks,
      exec_from,sep_during,exec_from,skip_ticks .after (by decide),stop_target]
    simp [selected,List.append_assoc]
  | beforeTwo =>
    rw [show 2*(z+o+e+3)+selected .beforeTwo z o e=2*z+(2+(2*o+(2+(3*e+2)))) by simp [selected]; omega]
    simp only [popBody,List.append_assoc,List.cons_append,List.nil_append]
    rw [exec_from,skip_ticks .beforeTwo (by decide),exec_from,sep_beforeTwo,exec_from,
      skip_ticks .beforeOne (by decide),exec_from,sep_beforeOne,exec_from,read_ticks,stop_target]
    simp [selected,List.append_assoc]
  | after =>
    rw [show 2*(z+o+e+3)+selected .after z o e=2*z+(2+(2*o+(2+(2*e+2)))) by simp [selected]; omega]
    simp only [popBody,List.append_assoc,List.cons_append,List.nil_append]
    rw [exec_from,skip_ticks .after (by decide),exec_from,sep_after,exec_from,
      skip_ticks .after (by decide),exec_from,sep_after,exec_from,
      skip_ticks .after (by decide),stop_target]
    simp [selected,List.append_assoc]

lemma opcode_push (k : K) (a : Bool) (j : ℕ) (r : K → List Bool)
    (f b : List (Token K)) :
    exec interpreter (config (.read .opcode) r (encodeInstruction (.push k a j)++f) b 0)
      (3*j+5)=
      config .reset (Function.update r k (r k++[a])) f (b++encodeInstruction (.push k a j)) j := by
  rw [show 3*j+5=2+(1+(3*j+2)) by omega]
  simp only [encodeInstruction,List.append_assoc,List.cons_append,List.nil_append]
  rw [exec_from,read_token]
  change exec interpreter (config (.push k a) r _ _ 0) (1+(3*j+2))=_
  rw [exec_from]
  change exec interpreter (next interpreter (config (.push k a) r _ _ 0)) _=_
  rw [push_register,exec_from,read_ticks,stop_target]
  simp [List.append_assoc]

lemma opcode_pop_empty (k : K) (z o e : ℕ) (r : K → List Bool) (hr : r k=[])
    (f b : List (Token K)) :
    exec interpreter (config (.read .opcode) r (encodeInstruction (.pop k z o e)++f) b 0)
      (2*(z+o+e)+e+9)=
      config .reset r f (b++encodeInstruction (.pop k z o e)) e := by
  have he : encodeInstruction (.pop k z o e)=.pop k :: popBody z o e := by
    simp [encodeInstruction,popBody,List.append_assoc]
  rw [he,List.cons_append,show 2*(z+o+e)+e+9=2+(1+(2*(z+o+e+3)+selected .beforeTwo z o e)) by
    simp [selected];omega,exec_from,read_token,exec_from]
  change exec interpreter (next interpreter (config (.pop k) r _ _ 0)) _=_
  rw [pop_empty k r hr,pop_body]
  simp [selected,List.append_assoc]

lemma opcode_pop_snoc (k : K) (a : Bool) (z o e : ℕ) (r : K → List Bool) (v : List Bool)
    (hr : r k=v++[a]) (f b : List (Token K)) :
    exec interpreter (config (.read .opcode) r (encodeInstruction (.pop k z o e)++f) b 0)
      (2*(z+o+e)+(if a then o else z)+9)=
      config .reset (Function.update r k v) f (b++encodeInstruction (.pop k z o e))
        (if a then o else z) := by
  have he : encodeInstruction (.pop k z o e)=.pop k :: popBody z o e := by
    simp [encodeInstruction,popBody,List.append_assoc]
  have ht : 2*(z+o+e)+(if a then o else z)+9=
      2+(1+(2*(z+o+e+3)+selected (if a then .beforeOne else .during) z o e)) := by
    cases a <;> simp [selected] <;> omega
  rw [he,List.cons_append,ht,exec_from,read_token,exec_from]
  change exec interpreter (next interpreter (config (.pop k) r _ _ 0)) _=_
  rw [pop_snoc k a r v hr,pop_body]
  cases a <;> simp [selected,List.append_assoc]

inductive Transfer : Instruction K → (K → List Bool) → (K → List Bool) → ℕ → Prop
  | push (k : K) (a : Bool) (j : ℕ) (r : K → List Bool) :
      Transfer (.push k a j) r (Function.update r k (r k++[a])) j
  | pop_empty (k : K) (z o e : ℕ) (r : K → List Bool) (hr : r k=[]) :
      Transfer (.pop k z o e) r r e
  | pop_snoc (k : K) (a : Bool) (z o e : ℕ) (r : K → List Bool) (v : List Bool)
      (hr : r k=v++[a]) :
      Transfer (.pop k z o e) r (Function.update r k v) (if a then o else z)

lemma opcode_transfer {i : Instruction K} {r r' : K → List Bool} {j : ℕ}
    (h : Transfer i r r' j) (f b : List (Token K)) :
    exec interpreter (config (.read .opcode) r (encodeInstruction i++f) b 0)
      (2*(encodeInstruction i).length+1+j)=
      config .reset r' f (b++encodeInstruction i) j := by
  cases h with
  | push k a j r =>
    convert opcode_push k a j r f b using 1
    all_goals try with_reducible_and_instances rfl
    simp [encodeInstruction]
    congr 1
    omega
  | pop_empty k z o e r hr =>
    convert opcode_pop_empty k z o j r hr f b using 1
    all_goals try with_reducible_and_instances rfl
    simp [encodeInstruction]
    congr 1
    omega
  | pop_snoc k a z o e r v hr =>
    convert opcode_pop_snoc k a z o e r v hr f b using 1
    all_goals try with_reducible_and_instances rfl
    simp [encodeInstruction]
    congr 1
    omega

lemma transfer_jump_le {i : Instruction K} {r r' : K → List Bool} {j : ℕ}
    (h : Transfer i r r' j) : j≤(encodeInstruction i).length := by
  cases h with
  | push k a j r => simp [encodeInstruction];omega
  | pop_empty k z o e r hr => simp [encodeInstruction];omega
  | pop_snoc k a z o e r v hr => cases a <;> simp [encodeInstruction] <;> omega
omit [DecidableEq K] in
lemma instruction_length_pos (i : Instruction K) : 0<(encodeInstruction i).length := by
  cases i <;> simp [encodeInstruction]
omit [DecidableEq K] in
lemma program_length (P : List (Instruction K)) : P.length≤(encodeProgram P).length := by
  induction P with
  | nil => simp [encodeProgram]
  | cons i P ih =>
    change P.length+1≤(encodeInstruction i++encodeProgram P).length
    rw [List.length_append]
    have hi := instruction_length_pos i
    omega

lemma program_step (v w : List (Instruction K)) {i : Instruction K}
    {r r' : K → List Bool} {j : ℕ} (h : Transfer i r r' j) :
    exec interpreter (config .pick r (encodeProgram (v++i::w)) [] v.length)
      (v.length+4*(encodeProgram v).length+4*(encodeInstruction i).length+j+3)=
      config .pick r' (encodeProgram (v++i::w)) [] j := by
  have he : encodeProgram (v++i::w)=encodeProgram v++(encodeInstruction i++encodeProgram w) := by
    simp [encodeProgram]
  rw [he,show v.length+4*(encodeProgram v).length+4*(encodeInstruction i).length+j+3=
      (v.length+2*(encodeProgram v).length+1)+
        ((2*(encodeInstruction i).length+1+j)+
          (2*(encodeProgram v++encodeInstruction i).length+1)) by simp;omega,
    exec_from,fetch,exec_from,opcode_transfer h,reset_all]
  simp [List.append_assoc]

lemma step_clock_le (v w : List (Instruction K)) {i : Instruction K}
    {r r' : K → List Bool} {j : ℕ} (h : Transfer i r r' j) :
    v.length+4*(encodeProgram v).length+4*(encodeInstruction i).length+j+3 ≤
      5*(encodeProgram (v++i::w)).length+3 := by
  have hj := transfer_jump_le h
  have hv := program_length v
  have he : (encodeProgram (v++i::w)).length=
      (encodeProgram v).length+(encodeInstruction i).length+(encodeProgram w).length := by
    simp [encodeProgram,Nat.add_assoc]
  rw [he]
  omega

inductive Run (P : List (Instruction K)) : ℕ → ℕ → (K → List Bool) → ℕ → (K → List Bool) → Prop
  | refl (pc : ℕ) (r : K → List Bool) : Run P 0 pc r pc r
  | step (v w : List (Instruction K)) (i : Instruction K) (hp : P=v++i::w)
      (r r' r'' : K → List Bool) (j last n : ℕ)
      (hi : Transfer i r r' j) (tail : Run P n j r' last r'') :
      Run P (n+1) v.length r last r''

theorem simulate_run (P : List (Instruction K)) {n first last : ℕ} {r s : K → List Bool}
    (h : Run P n first r last s) :
    ∃ N, N≤n*(5*(encodeProgram P).length+3) ∧
      exec interpreter (config .pick r (encodeProgram P) [] first) N =
        config .pick s (encodeProgram P) [] last := by
  induction h with
  | refl pc r => exact ⟨0,by simp,rfl⟩
  | step v w i hp r r' r'' j last n hi tail ih =>
    obtain ⟨N,hN,eN⟩ := ih
    let t := v.length+4*(encodeProgram v).length+4*(encodeInstruction i).length+j+3
    have ht : t≤5*(encodeProgram P).length+3 := by
      rw [hp];exact step_clock_le v w hi
    refine ⟨t+N,?_,?_⟩
    · nlinarith
    · rw [exec_from,hp,program_step v w hi,←hp,eN]

lemma opcode_halt (a : Bool) (r : K → List Bool) (f b : List (Token K)) :
    exec interpreter (config (.read .opcode) r (encodeInstruction (.halt a)++f) b 0) 2=
      config (.stopped a) r (.stop::f) (b++[.halt a]) 0 := by
  exact read_token .opcode (.halt a) r (.stop::f) b 0

lemma program_halt (v w : List (Instruction K)) (a : Bool) (r : K → List Bool) :
    exec interpreter (config .pick r (encodeProgram (v++.halt a::w)) [] v.length)
      (v.length+2*(encodeProgram v).length+3)=
      config (.stopped a) r (.stop::encodeProgram w) (encodeProgram v++[.halt a]) 0 := by
  have he : encodeProgram (v++.halt a::w)=
      encodeProgram v++(encodeInstruction (.halt a)++encodeProgram w) := by
    simp [encodeProgram]
  rw [he,show v.length+2*(encodeProgram v).length+3=
      (v.length+2*(encodeProgram v).length+1)+2 by omega,exec_from,fetch,opcode_halt]

omit [DecidableEq K] in
lemma halt_clock_le (v w : List (Instruction K)) (a : Bool) :
    v.length+2*(encodeProgram v).length+3≤5*(encodeProgram (v++.halt a::w)).length+3 := by
  have hv := program_length v
  have he : (encodeProgram (v++.halt a::w)).length=
      (encodeProgram v).length+2+(encodeProgram w).length := by simp [encodeProgram,encodeInstruction];omega
  rw [he];omega

theorem simulate_halt (P : List (Instruction K)) {n first : ℕ} {r s : K → List Bool}
    (v w : List (Instruction K)) (a : Bool) (hp : P=v++.halt a::w)
    (h : Run P n first r v.length s) :
    ∃ N, N≤(n+1)*(5*(encodeProgram P).length+3) ∧
      exec interpreter (config .pick r (encodeProgram P) [] first) N =
        config (.stopped a) s (.stop::encodeProgram w) (encodeProgram v++[.halt a]) 0 := by
  obtain ⟨N,hN,eN⟩ := simulate_run P h
  refine ⟨N+(v.length+2*(encodeProgram v).length+3),?_,?_⟩
  · have ht := halt_clock_le v w a
    rw [←hp] at ht
    nlinarith
  · rw [exec_from,eN,hp,program_halt]

section FiniteControl
variable {m : ℕ}

def instructionOf (P : Fin m → StackMachine.Instr K Bool (Fin m)) (result : Fin m → Bool)
    (q : Fin m) : Instruction K := match P q with
  | .halt => .halt (result q)
  | .push k a j => .push k a j.val
  | .pop k f => .pop k (f (some false)).val (f (some true)).val (f none).val

def programOf (P : Fin m → StackMachine.Instr K Bool (Fin m)) (result : Fin m → Bool) :
    List (Instruction K) := List.ofFn (instructionOf P result)

omit [DecidableEq K] in
lemma programOf_split (P : Fin m → StackMachine.Instr K Bool (Fin m)) (result : Fin m → Bool)
    (q : Fin m) :
    programOf P result=(programOf P result).take q.val ++
      instructionOf P result q :: (programOf P result).drop (q.val+1) := by
  have hq : q.val<(programOf P result).length := by simp [programOf]
  conv_lhs => rw [←List.take_append_drop q.val (programOf P result)]
  rw [List.drop_eq_getElem_cons hq]
  simp [programOf]
omit [DecidableEq K] in
lemma programOf_prefix_length (P : Fin m → StackMachine.Instr K Bool (Fin m))
    (result : Fin m → Bool) (q : Fin m) : ((programOf P result).take q.val).length=q.val := by
  simp [List.length_take,programOf]

lemma instructionOf_transfer (P : Fin m → StackMachine.Instr K Bool (Fin m))
    (result : Fin m → Bool) (C : StackMachine.Config K Bool (Fin m))
    (h : P C.state≠.halt) :
    Transfer (instructionOf P result C.state) C.store (next P C).store (next P C).state.val := by
  cases he : P C.state with
  | halt => exact False.elim (h he)
  | push k a j =>
    simpa [instructionOf,next,he] using Transfer.push k a j.val C.store
  | pop k f =>
    have hl : C.store k=[] ∨ ∃v a,C.store k=v++[a] := by
      induction C.store k using List.reverseRecOn with
      | nil => exact Or.inl rfl
      | append_singleton v a _ => exact Or.inr ⟨v,a,rfl⟩
    rcases hl with hl|⟨v,a,hl⟩
    · have hu : Function.update C.store k []=C.store := by
        simpa only [hl] using Function.update_eq_self k C.store
      simpa [instructionOf,next,he,hl,hu] using
        Transfer.pop_empty k (f (some false)).val (f (some true)).val (f none).val C.store hl
    · have hh := Transfer.pop_snoc k a (f (some false)).val (f (some true)).val
        (f none).val C.store v hl
      cases a <;> simpa [instructionOf,next,he,hl] using hh

lemma finite_control_run (P : Fin m → StackMachine.Instr K Bool (Fin m))
    (result : Fin m → Bool) (C : StackMachine.Config K Bool (Fin m)) (n : ℕ)
    (hn : ∀ t, t<n → P (exec P C t).state≠.halt) :
    Run (programOf P result) n C.state.val C.store (exec P C n).state.val (exec P C n).store := by
  induction n generalizing C with
  | zero => exact Run.refl _ _
  | succ n ih =>
    have hC : P C.state≠.halt := hn 0 (by omega)
    have htail : ∀t,t<n → P (exec P (next P C) t).state≠.halt := by
      intro t ht
      rw [←exec_start]
      exact hn (t+1) (by omega)
    have ht := instructionOf_transfer P result C hC
    have hh := Run.step ((programOf P result).take C.state.val)
      ((programOf P result).drop (C.state.val+1)) (instructionOf P result C.state)
      (programOf_split P result C.state) C.store (next P C).store
      (exec P (next P C) n).store (next P C).state.val (exec P (next P C) n).state.val n ht
      (ih (next P C) htail)
    simpa only [programOf_prefix_length,exec_start] using hh

end FiniteControl

end
end SourceBurnside.UniversalStack

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_UniversalInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.UniversalInput
open StackMachine UniversalStack
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K]

abbrev Packet (K : Type*) := Option (UniversalStack.Token K)
abbrev width (K : Type*) [Fintype K] := Fintype.card (Packet K)
omit [DecidableEq K] in
lemma width_pos : 0<width K := Fintype.card_pos

def packetBits (p : Packet K) : Fin (width K) → Bool :=
  fun i => decide (i=(Fintype.equivFin (Packet K)) p)
lemma packetBits_injective : Function.Injective (packetBits (K:=K)) := by
  intro a b h
  have he := congrFun h ((Fintype.equivFin (Packet K)) a)
  simp [packetBits] at he
  exact he

def packetDecode (v : Fin (width K) → Bool) : Packet K := Function.invFun packetBits v
lemma packetDecode_bits (p : Packet K) : packetDecode (packetBits p)=p :=
  Function.leftInverse_invFun packetBits_injective p

def packetWord (p : Packet K) : List Bool := List.ofFn (packetBits p)
def binaryCode (P : List (UniversalStack.Token K)) : List Bool :=
  (P.map some++[none]).flatMap packetWord

def header (bits : List Bool) : List Bool := List.replicate bits.length true++false::bits

inductive State (K : Type*) [Fintype K]
  | reverse | reversePut (b : Bool) | header | headerTick | skipPick | skipRead
  | collect (i : Fin (width K)) (v : Fin (width K) → Bool)
  | emit (a : UniversalStack.Token K)
  | universal (s : UniversalStack.State K)
  deriving Fintype

def first : State K := .collect ⟨0,width_pos⟩ (fun _ => false)
def collectNext (i : Fin (width K)) (v : Fin (width K) → Bool) (bit : Bool) : State K :=
  let v' := Function.update v i bit
  if hi : i.val+1<width K then .collect ⟨i.val+1,hi⟩ v' else
    match packetDecode v' with
    | some a => .emit a
    | none => .universal .reset

def machine (src dst : K) : State K → StackMachine.Instr (UniversalStack.Stack K)
    (UniversalStack.Token K) (State K)
  | .reverse => .pop (.reg src) (fun a => match a with
      | none => .header | some (.bit b) => .reversePut b | _ => .universal (.stopped false))
  | .reversePut b => .push (.reg dst) (.bit b) .reverse
  | .header => .pop (.reg dst) (fun a => match a with
      | some (.bit true) => .headerTick | some (.bit false) => .skipPick
      | _ => .universal (.stopped false))
  | .headerTick => .push .pc .tick .header
  | .skipPick => .pop .pc (fun a => if a.isSome then .skipRead else first)
  | .skipRead => .pop (.reg dst) (fun _ => .skipPick)
  | .collect i v => .pop (.reg dst) (fun a => match a with
      | some (.bit b) => collectNext i v b | _ => .universal (.stopped false))
  | .emit a => .push .back a first
  | .universal s => match UniversalStack.interpreter s with
      | .halt => .halt
      | .push k a q => .push k a (.universal q)
      | .pop k f => .pop k (fun a => .universal (f a))

def inputRegs (src dst : K) (u todo : List Bool) : K → List Bool := fun k =>
  if k=src then u else if k=dst then todo.reverse else []
def config (src dst : K) (s : State K) (u todo : List Bool)
    (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    StackMachine.Config (UniversalStack.Stack K) (UniversalStack.Token K) (State K) :=
  ⟨s,(UniversalStack.config .pick (inputRegs src dst u todo) f b pc).store⟩

lemma exec_one (P : State K → StackMachine.Instr (UniversalStack.Stack K)
    (UniversalStack.Token K) (State K)) (C : StackMachine.Config
    (UniversalStack.Stack K) (UniversalStack.Token K) (State K)) :
    exec P C 1=next P C := rfl

variable (src dst : K) (hne : src≠dst)
include hne

lemma config_pop_dst (P : State K → StackMachine.Instr (UniversalStack.Stack K)
    (UniversalStack.Token K) (State K)) (s : State K) (g : Option (UniversalStack.Token K) → State K)
    (he : P s=.pop (.reg dst) g) (u todo : List Bool) (a : Bool)
    (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next P (config src dst s u (a::todo) f b pc)=
      config src dst (g (some (.bit a))) u todo f b pc := by
  apply config_ext
  · simp [next,config,he,UniversalStack.config,inputRegs,Ne.symm hne,List.getLast?_reverse]
  · funext k
    cases k with
    | reg k =>
      by_cases h1 : k=src
      · subst k; simp [next,config,he,UniversalStack.config,inputRegs,hne,Ne.symm hne]
      · by_cases h2 : k=dst
        · subst k; simp [next,config,he,UniversalStack.config,inputRegs,Ne.symm hne]
        · simp [next,config,he,UniversalStack.config,inputRegs,h1,h2,Ne.symm hne]
    | front => simp [next,config,he,UniversalStack.config,inputRegs]
    | back => simp [next,config,he,UniversalStack.config,inputRegs]
    | pc => simp [next,config,he,UniversalStack.config,inputRegs]

lemma collect_bit (i : Fin (width K)) (v : Fin (width K) → Bool) (u todo : List Bool) (a : Bool)
    (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst (.collect i v) u (a::todo) f b pc)=
      config src dst (collectNext i v a) u todo f b pc := by
  exact config_pop_dst src dst hne (machine src dst) (.collect i v) _ rfl u todo a f b pc

def packetState : Packet K → State K
  | none => .universal .reset | some a => .emit a

omit hne in
lemma collect_complete (i : Fin (width K)) (v : Fin (width K) → Bool) (p : Packet K)
    (hv : ∀ j, j.val < i.val → v j=packetBits p j) (hi : ¬i.val+1<width K) :
    collectNext i v (packetBits p i)=packetState p := by
  have hh : Function.update v i (packetBits p i)=packetBits p := by
    funext j
    by_cases he : j=i
    · subst j;simp
    · rw [Function.update_of_ne he]
      exact hv j (by have := j.isLt; have := i.isLt; have hji : j.val ≠ i.val := fun e => he (Fin.ext e);omega)
  rw [collectNext,dite_eq_right hi,hh,packetDecode_bits]; cases p <;> rfl

omit hne [DecidableEq K] in
lemma collect_prefix (i : Fin (width K)) (v : Fin (width K) → Bool) (p : Packet K)
    (hv : ∀ j, j.val < i.val → v j=packetBits p j) :
    ∀j,j.val < i.val+1 → (Function.update v i (packetBits p i)) j=packetBits p j := by
  intro j hj
  by_cases he : j=i
  · subst j;simp
  · rw [Function.update_of_ne he]
    exact hv j (by have hji : j.val ≠ i.val := fun e => he (Fin.ext e);omega)

omit hne in
lemma emit_token (a : UniversalStack.Token K) (u todo : List Bool)
    (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst (.emit a) u todo f b pc)=
      config src dst first u todo f (b++[a]) pc := by
  apply config_ext
  · rfl
  · funext k; cases k <;> simp [next,machine,config,UniversalStack.config]

def liftConfig (C : StackMachine.Config (UniversalStack.Stack K) (UniversalStack.Token K)
    (UniversalStack.State K)) : StackMachine.Config (UniversalStack.Stack K)
    (UniversalStack.Token K) (State K) := ⟨.universal C.state,C.store⟩

omit hne in
lemma lift_next (C : StackMachine.Config (UniversalStack.Stack K) (UniversalStack.Token K)
    (UniversalStack.State K)) : next (machine src dst) (liftConfig C)=
      liftConfig (next UniversalStack.interpreter C) := by
  cases C with
  | mk s r =>
    cases he : UniversalStack.interpreter s <;> simp [next,machine,liftConfig,he]

omit hne in
lemma lift_exec (C : StackMachine.Config (UniversalStack.Stack K) (UniversalStack.Token K)
    (UniversalStack.State K)) (n : ℕ) : exec (machine src dst) (liftConfig C) n=
      liftConfig (exec UniversalStack.interpreter C n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [exec,ih,lift_next src dst]

omit hne in
lemma reset_code (P : List (UniversalStack.Token K)) (u todo : List Bool) :
    exec (machine src dst) (config src dst (.universal .reset) u todo [] P 0)
      (2*P.length+1)=config src dst (.universal .pick) u todo P [] 0 := by
  change exec (machine src dst)
    (liftConfig (UniversalStack.config .reset (inputRegs src dst u todo) [] P 0)) _=_
  rw [lift_exec src dst,reset_all,List.append_nil]
  rfl

end
end SourceBurnside.UniversalInput

namespace SourceBurnside.Structured
noncomputable section
open StackMachine UniversalStack

namespace Program
variable {K : Type*}

def mapInstr {A Γ Q Q' : Type*} (f : Q → Q') : StackMachine.Instr A Γ Q → StackMachine.Instr A Γ Q'
  | .halt => .halt
  | .push k a q => .push k a (f q)
  | .pop k g => .pop k (fun a => f (g a))

lemma mapInstr_comp {A Γ Q Q' Q'' : Type*} (f : Q → Q') (g : Q' → Q'')
    (i : StackMachine.Instr A Γ Q) : mapInstr g (mapInstr f i)=mapInstr (g ∘ f) i := by
  cases i <;> rfl

def done {A B : Type*} (f : A → B) (last : B) : Option A → B
  | none => last | some a => f a

end Program
open Program

end
end SourceBurnside.Structured

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_BinaryRegisters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.Structured.Binary.Add
open Program
abbrev K := Fin 4

def low (a b c : Bool) := (a ^^ b) ^^ c
def high (a b c : Bool) := (a && b) || (a && c) || (b && c)

def scan : List Bool → List Bool → Bool → List Bool × List Bool × Bool
  | [],ys,c => ([],ys,c)
  | a::xs,ys,c =>
    let t := scan xs ys.tail (high a (ys.head?.getD false) c)
    (low a (ys.head?.getD false) c::t.1,t.2)

lemma scan_length (xs ys : List Bool) (c : Bool) : (scan xs ys c).1.length=xs.length := by
  induction xs generalizing ys c with
  | nil => rfl
  | cons a xs ih => simp [scan,ih]

lemma scan_remaining (xs ys : List Bool) (c : Bool) : (scan xs ys c).2.1=ys.drop xs.length := by
  induction xs generalizing ys c with
  | nil => simp [scan]
  | cons a xs ih => cases ys <;> simp [scan,ih,List.drop_succ_cons]

end SourceBurnside.Structured.Binary.Add

namespace SourceBurnside.Structured.Binary
open Program
variable {K : Type*} [DecidableEq K]

namespace Add

def double (xs : List Bool) := false::xs.dropLast
lemma double_length (xs : List Bool) (hx : xs≠[]) : (double xs).length=xs.length := by
  have hn := List.length_pos_iff.mpr hx
  simp [double,List.length_dropLast];omega
lemma double_reverse (xs : List Bool) : (double xs).reverse=xs.reverse.tail++[false] := by
  simp [double,List.reverse_cons]

end Add
end SourceBurnside.Structured.Binary

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_ArithmeticDevices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.Structured.Binary.Multiply
open Program
abbrev K := Fin 6

def regs : Fin 4 → K := ![0,3,4,5]
lemma regs_injective : Function.Injective regs := by decide

def plusIf (b : Bool) (acc x : List Bool) : List Bool := if b then (Add.scan acc x false).1 else acc

def scan : List Bool → List Bool → List Bool → List Bool × List Bool
  | acc,x,[] => (acc,x)
  | acc,x,b::ys => scan (plusIf b acc x) (Add.double x) ys

lemma plusIf_length (b : Bool) (acc x : List Bool) : (plusIf b acc x).length=acc.length := by
  cases b <;> simp [plusIf,Add.scan_length]

lemma scan_length (acc x y : List Bool) (hx : x≠[]) (hlen : acc.length=x.length) :
    (scan acc x y).1.length=acc.length ∧ (scan acc x y).2.length=x.length := by
  induction y generalizing acc x with
  | nil => exact ⟨rfl,rfl⟩
  | cons b y ih =>
    have hp := plusIf_length b acc x
    have hd := Add.double_length x hx
    obtain ⟨h1,h2⟩ := ih (plusIf b acc x) (Add.double x) (by simp [Add.double]) (by omega)
    change (scan (plusIf b acc x) (Add.double x) y).1.length=acc.length ∧
      (scan (plusIf b acc x) (Add.double x) y).2.length=x.length
    exact ⟨h1.trans hp,h2.trans hd⟩

end SourceBurnside.Structured.Binary.Multiply

namespace SourceBurnside.Structured.Binary
open Program

def rollBits (b : Bool) (xs : List Bool) := b::xs.dropLast
lemma rollBits_length (b : Bool) (xs : List Bool) (hx : xs≠[]) : (rollBits b xs).length=xs.length := by
  have hn := List.length_pos_iff.mpr hx
  simp [rollBits,List.length_dropLast];omega
lemma rollBits_reverse (b : Bool) (xs : List Bool) : (rollBits b xs).reverse=xs.reverse.tail++[b] := by
  simp [rollBits,List.reverse_cons]

namespace Divide
abbrev K := Fin 8

def regs : Fin 4 → K := ![4,5,6,7]
lemma regs_injective : Function.Injective regs := by decide

def chooseTime (c : Bool) (n : ℕ) : ℕ := if c then 13*n+6 else 6*n+4

def trial (r d : List Bool) := Add.scan r (d.map not) true
def carry (r d : List Bool) := (trial r d).2.2

def oneStep (b : Bool) (q r d : List Bool) : List Bool × List Bool :=
  let r' := rollBits b r
  let c := carry r' d
  (rollBits c q, if c then (trial r' d).1 else r')
def stepTime (b : Bool) (r d : List Bool) : ℕ :=
  25*r.length+12+chooseTime (carry (rollBits b r) d) r.length

lemma oneStep_lengths (b : Bool) (q r d : List Bool) (hqr : q.length=r.length) (hr : r≠[]) :
    (oneStep b q r d).1.length=q.length ∧ (oneStep b q r d).2.length=r.length := by
  have hqn : q≠[] := by intro he;have hn := List.length_pos_iff.mpr hr;simp [he] at hqr;omega
  have hr' := rollBits_length b r hr
  constructor
  · exact rollBits_length _ q hqn
  · unfold oneStep;simp only
    split <;> simp only [trial,Add.scan_length,hr']

end Divide
end SourceBurnside.Structured.Binary

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_RegisterOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w

namespace SourceBurnside.Structured.Device
section
open Program Binary
variable {ι : Type} [DecidableEq ι]
namespace Constant
abbrev L (ι : Type) := ι ⊕ Fin 2

end Constant

end

section
open Program Binary

namespace AddOperator
abbrev L := Fin 2 ⊕ Fin 4

end AddOperator

end

section
open Program Binary

namespace SubOperator
abbrev L := Fin 2 ⊕ Fin 4

end SubOperator

end

section
open Program Binary
namespace CompareOperator
abbrev L := Fin 2 ⊕ Fin 4

def padded (n : ℕ) (b : Bool) : List Bool := List.replicate (n-1) false++[b]
lemma padded_length (n : ℕ) (hn : 0<n) (b : Bool) : (padded n b).length=n := by simp [-Sum.update_elim_inr,-Sum.elim_update_right,padded];omega
end CompareOperator

end

section
open Program Binary
namespace MultiplyOperator
abbrev L := Fin 2 ⊕ Fin 6

end MultiplyOperator

end

open Program Binary
namespace DivideOperator
abbrev L := Fin 2 ⊕ Fin 8

def chosen (rem : Bool) : Fin 8 := if rem then 1 else 0
def other (rem : Bool) : Fin 8 := if rem then 0 else 1
end DivideOperator

end SourceBurnside.Structured.Device

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_RegisterLoops
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.Structured.Binary.Decrement
open Program
abbrev K := Fin 3

def low (a b : Bool) := a ^^ b
def borrow (a b : Bool) := (!a) && b
def scan : List Bool → Bool → List Bool × Bool
  | [],b => ([],b)
  | a::xs,b => let t := scan xs (borrow a b); (low a b::t.1,t.2)

lemma scan_length (xs : List Bool) (b : Bool) : (scan xs b).1.length=xs.length := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih => simpa only [scan,List.length_cons] using congrArg Nat.succ (ih (borrow a b))

end SourceBurnside.Structured.Binary.Decrement

namespace SourceBurnside.Structured.Binary.Power
open Program
abbrev K := Fin 6

def regs : Fin 3 → K := ![0,2,3]
lemma regs_injective : Function.Injective regs := by decide

def oneStep (cnt acc : List Bool) : List Bool × List Bool :=
  let t := Decrement.scan cnt true
  if t.2 then (List.replicate cnt.length false,acc) else (t.1,Add.double acc)

def iter : ℕ → List Bool → List Bool → List Bool × List Bool
  | 0,cnt,acc => (cnt,acc)
  | m+1,cnt,acc => let t := oneStep cnt acc; iter m t.1 t.2

lemma oneStep_lengths (cnt acc : List Bool) (ha : acc≠[]) :
    (oneStep cnt acc).1.length=cnt.length ∧ (oneStep cnt acc).2.length=acc.length := by
  dsimp only [oneStep]
  split
  · simp
  · simp [Decrement.scan_length,Add.double_length acc ha]

lemma iter_lengths (m : ℕ) (cnt acc : List Bool) (ha : acc≠[]) :
    (iter m cnt acc).1.length=cnt.length ∧ (iter m cnt acc).2.length=acc.length := by
  induction m generalizing cnt acc with
  | zero => exact ⟨rfl,rfl⟩
  | succ m ih =>
    have h := oneStep_lengths cnt acc ha
    have hn : (oneStep cnt acc).2≠[] := by intro he;have hp := List.length_pos_iff.mpr ha;rw [he] at h;simp at h;omega
    have hh := ih (oneStep cnt acc).1 (oneStep cnt acc).2 hn
    exact ⟨hh.1.trans h.1,hh.2.trans h.2⟩

end SourceBurnside.Structured.Binary.Power

namespace SourceBurnside.Structured.Device
open Program Binary
namespace PowerOperator
abbrev L := Fin 1 ⊕ Fin 6

end PowerOperator

end SourceBurnside.Structured.Device

namespace SourceBurnside.Structured.Binary.Increment
open Program
abbrev K := Fin 3

def low (a b : Bool) := a ^^ b
def carry (a b : Bool) := a && b
def scan : List Bool → Bool → List Bool × Bool
  | [],b => ([],b)
  | a::xs,b => let t := scan xs (carry a b); (low a b::t.1,t.2)

lemma scan_length (xs : List Bool) (b : Bool) : (scan xs b).1.length=xs.length := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih => simpa only [scan,List.length_cons] using congrArg Nat.succ (ih (carry a b))
end SourceBurnside.Structured.Binary.Increment

namespace SourceBurnside.Structured.Binary.BitSize
open Program
abbrev K := Fin 5

def regs : Fin 3 → K := ![1,3,4]
lemma regs_injective : Function.Injective regs := by decide

def oneStep (a : Bool) (cnt len : List Bool) : List Bool × List Bool :=
  let c := (Increment.scan cnt true).1
  (c,if a then c else len)
def iter : List Bool → List Bool → List Bool → List Bool × List Bool
  | [],cnt,len => (cnt,len)
  | a::xs,cnt,len => let t := oneStep a cnt len;iter xs t.1 t.2

def measure : List Bool → ℕ → ℕ → ℕ
  | [],_,r => r
  | a::xs,p,r => measure xs (p+1) (if a then p+1 else r)

lemma oneStep_lengths (a : Bool) (cnt len : List Bool) (h : cnt.length=len.length) :
    (oneStep a cnt len).1.length=cnt.length ∧ (oneStep a cnt len).2.length=len.length := by
  cases a <;> simp [oneStep,Increment.scan_length,h]
lemma iter_lengths (xs cnt len : List Bool) (h : cnt.length=len.length) :
    (iter xs cnt len).1.length=cnt.length ∧ (iter xs cnt len).2.length=len.length := by
  induction xs generalizing cnt len with
  | nil => exact ⟨rfl,rfl⟩
  | cons a xs ih =>
    have hh := oneStep_lengths a cnt len h
    have hi := ih (oneStep a cnt len).1 (oneStep a cnt len).2 (hh.1.trans (h.trans hh.2.symm))
    exact ⟨hi.1.trans hh.1,hi.2.trans hh.2⟩

end SourceBurnside.Structured.Binary.BitSize

namespace SourceBurnside.Structured.Device
open Program Binary
namespace SizeOperator
abbrev L := Fin 1 ⊕ Fin 5

end SizeOperator

end SourceBurnside.Structured.Device

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_Recognizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w

namespace SourceBurnside.FiniteTable.Codec

section

def InRange (q : ℕ) (v : Fin 32 → ℕ) : Prop :=
  (v 0<3 ∧ v 1<q ∧ (v 0=2 → v 1=0)) ∧ v 2<5 ∧
  v 3<10 ∧ v 4≤v 3 ∧ (v 5<3 ∧ v 6<q ∧ (v 5=0 → v 6=0)) ∧
  v 7<q ∧ v 8<9

end

lemma zero_window (n offset width : ℕ) :
    (n/2^offset)%2^width=0 ↔ ∀i,width>i → n.testBit (i+offset)=false := by
  constructor
  · intro h i hi
    have H := congrArg (fun n : ℕ => n.testBit i) h
    simpa [Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow,hi] using H
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
    by_cases hi : i<width
    · simp [hi,h i hi]
    · simp [hi]

lemma zero_high (n offset : ℕ) : n/2^offset=0 ↔ ∀i,n.testBit (i+offset)=false := by
  constructor
  · intro h i
    have H := congrArg (fun n : ℕ => n.testBit i) h
    simpa [Nat.testBit_div_two_pow] using H
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simpa [Nat.testBit_div_two_pow] using h i

end SourceBurnside.FiniteTable.Codec

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Formulas_BooleanCircuits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w

namespace SourceBurnside.RawFormula
open Structured.Device FiniteTable.Codec
instance instDecidableInRange (q : ℕ) (v : Fin 32 → ℕ) : Decidable (InRange q v) := by unfold InRange;infer_instance

end SourceBurnside.RawFormula

namespace SourceBurnside.Structured.Device.Formula
end SourceBurnside.Structured.Device.Formula

namespace SourceBurnside.Structured.Device.Formula
end SourceBurnside.Structured.Device.Formula

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Formulas_PredicateCompilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w

namespace SourceBurnside.Structured.Device.Formula

section
variable {ι : Type}
lemma bound_pow_mono {a b n : ℕ} (ha : a<2^b) (hb : b≤n) : a<2^n :=
  ha.trans_le (Nat.pow_le_pow_right (by omega) hb)
lemma binary_value_bound {a b A B N : ℕ} (ha : a<2^A) (hb : b<2^B) (hN : A+B+1≤N) :
    a+b<2^N ∧ a*b<2^N ∧ 2*b≤2^N := by
  have ha' : a<2^(A+B) := bound_pow_mono ha (by omega)
  have hb' : b<2^(A+B) := bound_pow_mono hb (by omega)
  have hs : a+b<2^(A+B+1) := by rw [Nat.pow_succ];omega
  have hm : a*b<2^(A+B) := by
    rw [Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt ha hb
  have hd : 2*b≤2^(B+1) := by rw [Nat.pow_succ];omega
  exact ⟨bound_pow_mono hs hN,bound_pow_mono hm (by omega),hd.trans (Nat.pow_le_pow_right (by omega) (by omega))⟩

end

end SourceBurnside.Structured.Device.Formula

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_Compilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.LocalBody
open FiniteTable FiniteTable.Codec Structured Structured.Device Structured.Device.Formula

abbrev Registers := Fin 9

def exponentLimit (D h n : ℕ) : ℕ := 10000*(D+1)*(h+1)+n+32
lemma limit_height (D h n : ℕ) : 64*h+8≤exponentLimit D h n := by unfold exponentLimit;nlinarith
lemma limit_code (D h n : ℕ) : n≤exponentLimit D h n := by unfold exponentLimit;omega
lemma limit_next (D h n : ℕ) : D*h≤exponentLimit D h n := by unfold exponentLimit;nlinarith
end SourceBurnside.LocalBody

namespace SourceBurnside.HeaderProgram
open Structured Structured.Program Structured.Binary
abbrev K := Fin 4

end SourceBurnside.HeaderProgram

namespace SourceBurnside.RawHeader
open Structured Structured.Program Structured.Binary
abbrev K := Fin 6
def heightSlots : Fin 4 → K := ![0,1,2,3]
def aritySlots : Fin 4 → K := ![0,1,4,3]
lemma heightSlots_injective : Function.Injective heightSlots := by decide
lemma aritySlots_injective : Function.Injective aritySlots := by decide
end SourceBurnside.RawHeader

namespace SourceBurnside.DropPadding
open Structured Structured.Program Structured.Binary
abbrev K := Fin 2
end SourceBurnside.DropPadding

namespace SourceBurnside.PadRegister
open Structured Structured.Program Structured.Binary
abbrev K := Fin 5
def dropSlots : Fin 2 → K := ![4,2]
lemma dropSlots_injective : Function.Injective dropSlots := by decide
lemma result_length (xs : List Bool) (n : ℕ) (hn : xs.length≤n) :
    (List.replicate (n-xs.length) false++xs).length=n := by simp;omega
end SourceBurnside.PadRegister

namespace SourceBurnside.WrappedInput
open StackMachine UniversalStack
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K]

def plain (P : List (UniversalStack.Token K)) : List Bool := false::UniversalInput.binaryCode P
inductive State (K : Type*) [Fintype K]
  | reverse | reversePut (b : Bool) | header | headerTick | skipPick | skipRead | marker
  | inner (s : UniversalInput.State K)
  deriving Fintype

def machine (src dst : K) : State K → Instr (UniversalStack.Stack K) (UniversalStack.Token K) (State K)
  | .reverse => .pop (.reg src) (fun a => match a with
      | none => .header | some (.bit b) => .reversePut b | _ => .inner (.universal (.stopped false)))
  | .reversePut b => .push (.reg dst) (.bit b) .reverse
  | .header => .pop (.reg dst) (fun a => match a with
      | some (.bit true) => .headerTick | some (.bit false) => .skipPick
      | _ => .inner (.universal (.stopped false)))
  | .headerTick => .push .pc .tick .header
  | .skipPick => .pop .pc (fun a => if a.isSome then .skipRead else .marker)
  | .skipRead => .pop (.reg dst) (fun _ => .skipPick)
  | .marker => .pop (.reg dst) (fun a => match a with
      | some (.bit true) => .header | some (.bit false) => .inner UniversalInput.first
      | _ => .inner (.universal (.stopped false)))
  | .inner s => match UniversalInput.machine src dst s with
      | .halt => .halt
      | .push k a q => .push k a (.inner q)
      | .pop k f => .pop k (fun a => .inner (f a))

def config (src dst : K) (s : State K) (u todo : List Bool)
    (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    Config (UniversalStack.Stack K) (UniversalStack.Token K) (State K) :=
  ⟨s,(UniversalStack.config .pick (UniversalInput.inputRegs src dst u todo) f b pc).store⟩
lemma exec_one (P : State K → Instr (UniversalStack.Stack K) (UniversalStack.Token K) (State K))
    (C : Config (UniversalStack.Stack K) (UniversalStack.Token K) (State K)) : exec P C 1=next P C := rfl
variable (src dst : K) (hne : src≠dst)
include hne
lemma reverse_token (u todo : List Bool) (a : Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    exec (machine src dst) (config src dst .reverse (u++[a]) todo f b pc) 2=
      config src dst .reverse u (a::todo) f b pc := by
  apply config_ext
  · simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne]
  · funext k
    cases k with
    | reg k =>
      by_cases h1 : k=src
      · subst k; simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,hne]
      · by_cases h2 : k=dst
        · subst k
          simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne,List.reverse_cons]
        · simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,h1,h2]
    | front => simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne]
    | back => simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne]
    | pc => simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne]

omit hne in
lemma reverse_empty (todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst .reverse [] todo f b pc)=
      config src dst .header [] todo f b pc := by
  apply config_ext
  · simp [next,machine,config,UniversalStack.config,UniversalInput.inputRegs]
  · funext k
    cases k with
    | reg k => by_cases h : k=src <;> simp [next,machine,config,UniversalStack.config,UniversalInput.inputRegs,h]
    | front => simp [next,machine,config,UniversalStack.config,UniversalInput.inputRegs]
    | back => simp [next,machine,config,UniversalStack.config,UniversalInput.inputRegs]
    | pc => simp [next,machine,config,UniversalStack.config,UniversalInput.inputRegs]

lemma reverse_all (u todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    exec (machine src dst) (config src dst .reverse u todo f b pc) (2*u.length+1)=
      config src dst .header [] (u++todo) f b pc := by
  induction u using List.reverseRecOn generalizing todo with
  | nil => simpa [exec] using reverse_empty src dst todo f b pc
  | append_singleton u a ih =>
    rw [List.length_append,List.length_singleton,show 2*(u.length+1)+1=2+(2*u.length+1) by omega,
      exec_from,reverse_token src dst hne,ih]
    simp

lemma header_true (u todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    exec (machine src dst) (config src dst .header u (true::todo) f b pc) 2=
      config src dst .header u todo f b (pc+1) := by
  apply config_ext
  · simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne,List.getLast?_reverse]
  · funext k
    cases k with
    | reg k =>
      by_cases h1 : k=src
      · subst k; simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,hne,Ne.symm hne]
      · by_cases h2 : k=dst
        · subst k; simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne]
        · simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,h1,h2,Ne.symm hne]
    | front => simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne]
    | back => simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne]
    | pc => simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne,List.replicate_succ']

lemma config_pop_dst (P : State K → StackMachine.Instr (UniversalStack.Stack K)
    (UniversalStack.Token K) (State K)) (s : State K) (g : Option (UniversalStack.Token K) → State K)
    (he : P s=.pop (.reg dst) g) (u todo : List Bool) (a : Bool)
    (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next P (config src dst s u (a::todo) f b pc)=
      config src dst (g (some (.bit a))) u todo f b pc := by
  apply config_ext
  · simp [next,config,he,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne,List.getLast?_reverse]
  · funext k
    cases k with
    | reg k =>
      by_cases h1 : k=src
      · subst k; simp [next,config,he,UniversalStack.config,UniversalInput.inputRegs,hne,Ne.symm hne]
      · by_cases h2 : k=dst
        · subst k; simp [next,config,he,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne]
        · simp [next,config,he,UniversalStack.config,UniversalInput.inputRegs,h1,h2,Ne.symm hne]
    | front => simp [next,config,he,UniversalStack.config,UniversalInput.inputRegs]
    | back => simp [next,config,he,UniversalStack.config,UniversalInput.inputRegs]
    | pc => simp [next,config,he,UniversalStack.config,UniversalInput.inputRegs]

lemma header_false (u todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst .header u (false::todo) f b pc)=
      config src dst .skipPick u todo f b pc := by
  exact config_pop_dst src dst hne (machine src dst) .header _ rfl u todo false f b pc

omit hne in
lemma skip_pick_zero (u todo : List Bool) (f b : List (UniversalStack.Token K)) :
    next (machine src dst) (config src dst .skipPick u todo f b 0)=
      config src dst .marker u todo f b 0 := by
  apply config_ext
  · rfl
  · funext k
    cases k <;> simp [next,machine,config,UniversalStack.config]

omit hne in
lemma skip_pick_succ (u todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst .skipPick u todo f b (pc+1))=
      config src dst .skipRead u todo f b pc := by
  apply config_ext
  · simp [next,machine,config,UniversalStack.config,List.replicate_succ]
  · funext k
    cases k <;> simp [next,machine,config,UniversalStack.config,List.replicate_succ]

lemma skip_read (u todo : List Bool) (a : Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst .skipRead u (a::todo) f b pc)=
      config src dst .skipPick u todo f b pc := by
  exact config_pop_dst src dst hne (machine src dst) .skipRead _ rfl u todo a f b pc

lemma header_ones (n : ℕ) (u todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    exec (machine src dst) (config src dst .header u (List.replicate n true++todo) f b pc) (2*n)=
      config src dst .header u todo f b (pc+n) := by
  induction n generalizing pc with
  | zero => simp [exec]
  | succ n ih =>
    rw [show 2*(n+1)=2+2*n by omega,List.replicate_succ,List.cons_append,
      exec_from,header_true src dst hne,ih]
    simp [Nat.add_comm,Nat.add_left_comm]

lemma skip_bits (bits u todo : List Bool) (f b : List (UniversalStack.Token K)) :
    exec (machine src dst) (config src dst .skipPick u (bits++todo) f b bits.length)
      (2*bits.length+1)=config src dst .marker u todo f b 0 := by
  induction bits with
  | nil => simpa [exec] using skip_pick_zero src dst u todo f b
  | cons a bits ih =>
    rw [List.length_cons,List.cons_append,
      show 2*(bits.length+1)+1=1+(1+(2*bits.length+1)) by omega,exec_from]
    rw [exec_one]
    rw [skip_pick_succ src dst,exec_from]
    rw [exec_one]
    rw [skip_read src dst hne,ih]

lemma header_all (bits u todo : List Bool) (f b : List (UniversalStack.Token K)) :
    exec (machine src dst) (config src dst .header u (UniversalInput.header bits++todo) f b 0)
      (4*bits.length+2)=config src dst .marker u todo f b 0 := by
  rw [show 4*bits.length+2=2*bits.length+(1+(2*bits.length+1)) by omega]
  simp only [UniversalInput.header,List.append_assoc,List.cons_append]
  rw [exec_from,header_ones src dst hne,Nat.zero_add,exec_from]
  rw [exec_one]
  rw [header_false src dst hne,skip_bits src dst hne]

lemma marker_true (u todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst .marker u (true::todo) f b pc)=
      config src dst .header u todo f b pc :=
  config_pop_dst src dst hne (machine src dst) .marker _ rfl u todo true f b pc
lemma marker_false (u todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst .marker u (false::todo) f b pc)=
      config src dst (.inner UniversalInput.first) u todo f b pc :=
  config_pop_dst src dst hne (machine src dst) .marker _ rfl u todo false f b pc

omit hne in
def liftConfig (C : Config (UniversalStack.Stack K) (UniversalStack.Token K) (UniversalInput.State K)) :
    Config (UniversalStack.Stack K) (UniversalStack.Token K) (State K) := ⟨.inner C.state,C.store⟩
omit hne in
lemma lift_next (C : Config (UniversalStack.Stack K) (UniversalStack.Token K) (UniversalInput.State K)) :
    next (machine src dst) (liftConfig C)=liftConfig (next (UniversalInput.machine src dst) C) := by
  rcases C with ⟨s,r⟩
  cases he : UniversalInput.machine src dst s <;> simp [next,machine,liftConfig,he]
omit hne in
lemma lift_exec (C : Config (UniversalStack.Stack K) (UniversalStack.Token K) (UniversalInput.State K)) (n : ℕ) :
    exec (machine src dst) (liftConfig C) n=liftConfig (exec (UniversalInput.machine src dst) C n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [exec,ih,lift_next]

end
end SourceBurnside.WrappedInput

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_InputEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.RawLocalBody
open FiniteTable FiniteTable.Codec Structured Structured.Device Structured.Device.Formula

abbrev Registers := Fin 7
def limit (D h n : ℕ) := 10000*(D+20)*(h+1)+n+32
end SourceBurnside.RawLocalBody

namespace SourceBurnside.TakePrefix
open Structured Structured.Program
abbrev K := Fin 3
end SourceBurnside.TakePrefix

namespace SourceBurnside.TwoInputQuote
open Structured Structured.Program Structured.Binary
abbrev K := Fin 7

def headerSlots : Fin 4 → K := ![0,3,1,4]
def unarySlots : Fin 4 → K := ![2,3,4,5]
def takeSlots : Fin 3 → K := ![0,3,2]
lemma headerSlots_injective : Function.Injective headerSlots := by decide
lemma unarySlots_injective : Function.Injective unarySlots := by decide
lemma takeSlots_injective : Function.Injective takeSlots := by decide
end SourceBurnside.TwoInputQuote

namespace SourceBurnside.RawPadSeed
open Structured Structured.Program Structured.Binary
abbrev K (r : ℕ) := Fin r ⊕ Fin 3
end SourceBurnside.RawPadSeed

namespace SourceBurnside.CountLength
open Structured Structured.Program Structured.Binary
abbrev K := Fin 7
def slots : Fin 5 → K := ![4,2,3,5,6]
lemma slots_injective : Function.Injective slots := by decide
def countBits (xs : List Bool) (n : ℕ) : List Bool :=
  (BitSize.iter xs.reverse (List.replicate n false) (List.replicate n false)).1.reverse
lemma countBits_length (xs : List Bool) (n : ℕ) : (countBits xs n).length=n := by
  simpa only [countBits,List.length_reverse,List.length_replicate] using
    (BitSize.iter_lengths xs.reverse (List.replicate n false) (List.replicate n false) rfl).1
end SourceBurnside.CountLength

namespace SourceBurnside.PackFamily
open Structured Structured.Program
abbrev K (r : ℕ) := (Fin r ⊕ Fin r) ⊕ Fin 3

def slots {r : ℕ} (i : Fin r) : Fin 5 → K r :=
  ![.inl (.inl i),.inr 0,.inl (.inr i),.inr 1,.inr 2]
lemma slots_injective {r : ℕ} (i : Fin r) : Function.Injective (slots i) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [slots] at h ⊢
def pad (xs : List Bool) (n : ℕ) := List.replicate (n-xs.length) false++xs
def outputs {r : ℕ} (v out : Fin r → List Bool) (n : ℕ) (items : List (Fin r)) : Fin r → List Bool :=
  fun i => if i∈items then pad (v i) n else out i
end SourceBurnside.PackFamily

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_ProgramAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.RawNumberPrep
open Structured Structured.Program Structured.Binary
abbrev K := Fin 6 ⊕ Fin 7

def before (code input : List Bool) : Fin 6 → List Bool := ![code.reverse,[],[],[],input.reverse,[]]
def headerSlots : Fin 6 → K := ![.inl 4,.inr 5,.inl 1,.inr 6,.inl 2,.inl 3]
def unarySlots : Fin 4 → K := ![.inr 3,.inl 5,.inr 5,.inr 6]
def seedSlots : RawPadSeed.K 6 → K
  | .inl i => .inl i
  | .inr 0 => .inr 0
  | .inr 1 => .inr 5
  | .inr _ => .inr 6
lemma headerSlots_injective : Function.Injective headerSlots := by decide
lemma unarySlots_injective : Function.Injective unarySlots := by decide
lemma seedSlots_injective : Function.Injective seedSlots := by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => simpa [seedSlots] using h
    | inr b => fin_cases b <;> simp [seedSlots] at h
  | inr a => cases b with
    | inl b => fin_cases a <;> simp [seedSlots] at h
    | inr b => fin_cases a <;> fin_cases b <;> simp [seedSlots] at h ⊢

def items (W D : ℕ) : List (Fin 6 × ℕ) := [(5,W*(10000*(D+20))),(0,W),(4,W),(2,W)]
def offset (W D : ℕ) := W*(10000*(D+20)+33)
def width (W D h : ℕ) (code data bits : List Bool) : ℕ :=
  W*(RawLocalBody.limit D h code.length+data.length+bits.length+1)

def countSlots (b : Bool) : Fin 7 → K :=
  ![.inl (if b then 4 else 0),.inr 0,.inr (if b then 2 else 1),.inr 3,.inr 4,.inr 5,.inr 6]
lemma countSlots_injective (b : Bool) : Function.Injective (countSlots b) := by cases b <;> decide
end SourceBurnside.RawNumberPrep

namespace SourceBurnside.RawPreparedInputs
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
open FiniteTable.Codec
abbrev I := Fin 7
def fields : I → RawNumberPrep.K := ![.inl 0,.inr 1,.inl 1,.inl 2,.inl 3,.inl 4,.inr 2]
end SourceBurnside.RawPreparedInputs

namespace SourceBurnside.RawAssembler
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
abbrev K := RawNumberPrep.K ⊕ Fin 7
def packSlots : PackFamily.K 7 → K
  | .inl (.inl i) => .inl (RawPreparedInputs.fields i)
  | .inl (.inr i) => .inr i
  | .inr 0 => .inl (.inr 0)
  | .inr 1 => .inl (.inr 5)
  | .inr _ => .inl (.inr 6)
lemma packSlots_injective : Function.Injective packSlots := by decide
end SourceBurnside.RawAssembler

namespace SourceBurnside.RawPolynomial
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
def factor (W D : ℕ) : ℕ := W*(10000*(D+20)+33)
lemma squash {a b B C : ℕ} (ha : a ≤ C*B) (hb : b ≤ B) : a*b ≤ C*B^2 := by
  calc a*b ≤ (C*B)*B := Nat.mul_le_mul ha hb
       _ = C*B^2 := by ring
lemma linear_square {a B C : ℕ} (hB : 1 ≤ B) (ha : a ≤ C*B) : a ≤ C*B^2 := by
  have hs : B ≤ B^2 := by nlinarith
  exact ha.trans (Nat.mul_le_mul_left C hs)
end SourceBurnside.RawPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_StackCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.CompactStacks
open StackMachine
variable {m : ℕ} {Q : Type}

inductive State (m : ℕ) (Q : Type)
  | start (q : Q)
  | seek (q : Q) (k : Fin (m+1))
  | saveTag (q : Q) (k : Fin (m+1)) (a : Option Bool)
  | readData (q : Q) (k : Fin (m+1))
  | saveData (q : Q) (k : Fin (m+1)) (a : Option Bool)
  | insertTag (q : Q)
  | popTag (q : Q) (a : Option Bool)
  | restore (q : Q)
  | putBack (q : Q) (b : Bool)
  deriving DecidableEq, Fintype

def pred (k : Fin (m+1)) : Fin (m+1) := ⟨k.val-1,by have := k.isLt;omega⟩
def operation (P : Q → Instr (Fin m) Bool Q) (q : Q) : Instr (Fin 2) Bool (State m Q) :=
  match P q with
  | .halt => .halt
  | .push _ b q' => .push 0 b (.insertTag q')
  | .pop _ _ => .pop 0 (fun b => .popTag q b)
def seeking (P : Q → Instr (Fin m) Bool Q) (q : Q) (k : Fin (m+1)) : Instr (Fin 2) Bool (State m Q) :=
  if k.val=0 then operation P q else .pop 0 (fun a => .saveTag q k a)
def machine (P : Q → Instr (Fin m) Bool Q) : State m Q → Instr (Fin 2) Bool (State m Q)
  | .start q => match P q with
    | .halt => .halt
    | .push k _ _ | .pop k _ => seeking P q k.castSucc
  | .seek q k => seeking P q k
  | .saveTag q k a => match a with
    | none => .halt
    | some true => .push 1 true (.readData q k)
    | some false => .push 1 false (.seek q (pred k))
  | .readData q k => .pop 0 (fun a => .saveData q k a)
  | .saveData q k a => match a with
    | none => .halt
    | some b => .push 1 b (.seek q k)
  | .insertTag q' => .push 0 true (.restore q')
  | .popTag q a => match P q,a with
    | .pop _ f,some true => .pop 0 (fun b => .restore (f b))
    | .pop _ f,some false => .push 0 false (.restore (f none))
    | _,_ => .halt
  | .restore q => .pop 1 (fun b => match b with | none => .start q | some b => .putBack q b)
  | .putBack q b => .push 0 b (.restore q)

def block (bs : List Bool) : List Bool := bs.flatMap (fun b => [true,b])++[false]
def words (ss : List (List Bool)) : List Bool := ss.flatMap block
@[simp] lemma block_length (bs : List Bool) : (block bs).length=2*bs.length+1 := by
  simp [block,Nat.mul_comm]
@[simp] lemma block_cons (b : Bool) (bs : List Bool) : block (b::bs)=true::b::block bs := by simp [block]
@[simp] lemma block_nil : block []=[false] := rfl
@[simp] lemma words_nil : words []=[] := rfl
@[simp] lemma words_cons (b : List Bool) (bs : List (List Bool)) : words (b::bs)=block b++words bs := by simp [words]

def config (s : State m Q) (front back : List Bool) : Config (Fin 2) Bool (State m Q) :=
  ⟨s,![front.reverse,back]⟩

lemma skip_bit (P : Q → Instr (Fin m) Bool Q) (q : Q) (k : Fin (m+1)) (hk : k.val≠0)
    (b : Bool) (xs acc : List Bool) :
    exec (machine P) (config (.seek q k) (true::b::xs) acc) 4 =
      config (.seek q k) xs (acc++[true,b]) := by
  simp [exec,next,machine,seeking,hk,config,List.reverse_cons,List.append_assoc]
  funext i;fin_cases i <;> simp
lemma skip_end (P : Q → Instr (Fin m) Bool Q) (q : Q) (k : Fin (m+1)) (hk : k.val≠0)
    (xs acc : List Bool) :
    exec (machine P) (config (.seek q k) (false::xs) acc) 2 =
      config (.seek q (pred k)) xs (acc++[false]) := by
  simp [exec,next,machine,seeking,hk,config,List.reverse_cons]
  funext i;fin_cases i <;> simp

lemma skip_block (P : Q → Instr (Fin m) Bool Q) (q : Q) (k : Fin (m+1)) (hk : k.val≠0)
    (bs xs acc : List Bool) :
    exec (machine P) (config (.seek q k) (block bs++xs) acc) (2*(block bs).length) =
      config (.seek q (pred k)) xs (acc++block bs) := by
  induction bs generalizing acc with
  | nil => simpa using skip_end P q k hk xs acc
  | cons a bs ih =>
    rw [block_cons,List.cons_append,List.cons_append]
    have he : 2*(true::a::block bs).length=4+2*(block bs).length := by simp;omega
    rw [he,UniversalStack.exec_from,skip_bit P q k hk a (block bs++xs) acc,ih]
    all_goals simp [List.append_assoc]

lemma skip_words (P : Q → Instr (Fin m) Bool Q) (q : Q)
    (ss : List (List Bool)) (k : Fin (m+1)) (hk : ss.length≤k.val) (xs acc : List Bool) :
    exec (machine P) (config (.seek q k) (words ss++xs) acc) (2*(words ss).length) =
      config (.seek q ⟨k.val-ss.length,by have := k.isLt;omega⟩) xs (acc++words ss) := by
  induction ss generalizing k acc with
  | nil => simp [exec]
  | cons b ss ih =>
    have hn : k.val≠0 := by simp only [List.length_cons] at hk;omega
    have ht : ss.length≤(pred k).val := by simp only [List.length_cons] at hk;dsimp [pred];omega
    rw [words_cons,List.append_assoc,show 2*(block b++words ss).length=2*(block b).length+2*(words ss).length by simp;omega]
    rw [UniversalStack.exec_from,skip_block P q k hn b (words ss++xs) acc,ih (pred k) ht]
    congr 1
    · congr 1;apply Fin.ext;dsimp [pred];omega
    · simp [List.append_assoc]

lemma restore (P : Q → Instr (Fin m) Bool Q) (q : Q) (xs acc : List Bool) :
    exec (machine P) (config (.restore q) xs acc) (2*acc.length+1)=config (.start q) (acc++xs) [] := by
  induction acc using List.reverseRecOn generalizing xs with
  | nil => simp [exec,next,machine,config]
  | append_singleton acc b ih =>
    have H : exec (machine P) (config (.restore q) xs (acc++[b])) 2=config (.restore q) (b::xs) acc := by
      simp [exec,next,machine,config,List.reverse_cons]
      funext i;fin_cases i <;> simp
    rw [show 2*(acc++[b]).length+1=2+(2*acc.length+1) by simp;omega,UniversalStack.exec_from,H,ih]
    all_goals simp [List.append_assoc]

lemma at_push (P : Q → Instr (Fin m) Bool Q) (q q' : Q) (k : Fin m) (b : Bool)
    (hp : P q=.push k b q') (bs xs acc : List Bool) :
    exec (machine P) (config (.seek q 0) (block bs++xs) acc) 2=
      config (.restore q') (block (b::bs)++xs) acc := by
  simp [exec,next,machine,seeking,operation,hp,config,List.reverse_cons,
    List.reverse_append,List.append_assoc]
  funext i;fin_cases i <;> simp

lemma at_pop_cons (P : Q → Instr (Fin m) Bool Q) (q : Q) (k : Fin m)
    (f : Option Bool → Q) (hp : P q=.pop k f) (b : Bool) (bs xs acc : List Bool) :
    exec (machine P) (config (.seek q 0) (block (b::bs)++xs) acc) 2=
      config (.restore (f (some b))) (block bs++xs) acc := by
  simp [exec,next,machine,seeking,operation,hp,config,List.reverse_cons,List.reverse_append]
  funext i;fin_cases i <;> simp

lemma at_pop_nil (P : Q → Instr (Fin m) Bool Q) (q : Q) (k : Fin m)
    (f : Option Bool → Q) (hp : P q=.pop k f) (xs acc : List Bool) :
    exec (machine P) (config (.seek q 0) (block []++xs) acc) 2=
      config (.restore (f none)) (block []++xs) acc := by
  simp [exec,next,machine,seeking,operation,hp,config,List.reverse_cons]

lemma start_push (P : Q → Instr (Fin m) Bool Q) (q q' : Q) (k : Fin m) (b : Bool)
    (hp : P q=.push k b q') (xs acc : List Bool) (n : ℕ) (hn : 0<n) :
    exec (machine P) (config (.start q) xs acc) n=
      exec (machine P) (config (.seek q k.castSucc) xs acc) n := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  rw [UniversalStack.exec_start,UniversalStack.exec_start]
  congr 1
  by_cases hk : k.val=0 <;> simp [next,machine,hp,config,seeking,operation,hk]

lemma start_pop (P : Q → Instr (Fin m) Bool Q) (q : Q) (k : Fin m)
    (f : Option Bool → Q) (hp : P q=.pop k f) (xs acc : List Bool) (n : ℕ) (hn : 0<n) :
    exec (machine P) (config (.start q) xs acc) n=
      exec (machine P) (config (.seek q k.castSucc) xs acc) n := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  rw [UniversalStack.exec_start,UniversalStack.exec_start]
  congr 1
  by_cases hk : k.val=0 <;> simp [next,machine,hp,config,seeking,operation,hk]

@[simp] lemma words_append (a b : List (List Bool)) : words (a++b)=words a++words b := by
  simp [words]

def registers (r : Fin m → List Bool) : List (List Bool) := List.ofFn (fun k => (r k).reverse)
@[simp] lemma registers_length (r : Fin m → List Bool) : (registers r).length=m := by simp [registers]
@[simp] lemma registers_getElem (r : Fin m → List Bool) (i : ℕ) (hi : i<(registers r).length) :
    (registers r)[i]=(r ⟨i,by simpa using hi⟩).reverse := by simp [registers]

lemma registers_update (r : Fin m → List Bool) (k : Fin m) (bs : List Bool) :
    registers (Function.update r k bs)=(registers r).set k.val bs.reverse := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [registers_length] at hi
  by_cases he : i=k.val
  · subst i;simp
  · have hn : (⟨i,hi⟩ : Fin m)≠k := by intro h;exact he (congrArg Fin.val h)
    simp [Ne.symm he,hn,registers]

lemma registers_split (r : Fin m → List Bool) (k : Fin m) :
    registers r=(registers r).take k.val ++ (r k).reverse::(registers r).drop (k.val+1) := by
  conv_lhs => rw [←List.take_append_drop k.val (registers r)]
  rw [List.drop_eq_getElem_cons (by simp)]
  simp

lemma full_push (P : Q → Instr (Fin m) Bool Q) (q q' : Q) (k : Fin m) (b : Bool)
    (hp : P q=.push k b q') (pre : List (List Bool)) (bs xs : List Bool) (hk : pre.length=k.val) :
    exec (machine P) (config (.start q) (words pre++block bs++xs) []) (4*(words pre).length+3)=
      config (.start q') (words pre++block (b::bs)++xs) [] := by
  rw [start_push P q q' k b hp _ _ _ (by omega)]
  rw [show 4*(words pre).length+3=2*(words pre).length+(2+(2*(words pre).length+1)) by omega,
    UniversalStack.exec_from _ _ (2*(words pre).length) (2+(2*(words pre).length+1)),List.append_assoc,
    skip_words P q pre k.castSucc (by simp [hk])]
  simp only [Fin.val_castSucc,hk,Nat.sub_self,List.nil_append,Fin.mk_zero]
  rw [UniversalStack.exec_from _ _ 2 _,at_push P q q' k b hp,restore]
  all_goals simp [List.append_assoc]

lemma full_pop_cons (P : Q → Instr (Fin m) Bool Q) (q : Q) (k : Fin m)
    (f : Option Bool → Q) (hp : P q=.pop k f) (pre : List (List Bool)) (b : Bool)
    (bs xs : List Bool) (hk : pre.length=k.val) :
    exec (machine P) (config (.start q) (words pre++block (b::bs)++xs) []) (4*(words pre).length+3)=
      config (.start (f (some b))) (words pre++block bs++xs) [] := by
  rw [start_pop P q k f hp _ _ _ (by omega)]
  rw [show 4*(words pre).length+3=2*(words pre).length+(2+(2*(words pre).length+1)) by omega,
    UniversalStack.exec_from _ _ (2*(words pre).length) (2+(2*(words pre).length+1)),List.append_assoc,
    skip_words P q pre k.castSucc (by simp [hk])]
  simp only [Fin.val_castSucc,hk,Nat.sub_self,List.nil_append,Fin.mk_zero]
  rw [UniversalStack.exec_from _ _ 2 _,at_pop_cons P q k f hp,restore]
  all_goals simp [List.append_assoc]

lemma full_pop_nil (P : Q → Instr (Fin m) Bool Q) (q : Q) (k : Fin m)
    (f : Option Bool → Q) (hp : P q=.pop k f) (pre : List (List Bool))
    (xs : List Bool) (hk : pre.length=k.val) :
    exec (machine P) (config (.start q) (words pre++block []++xs) []) (4*(words pre).length+3)=
      config (.start (f none)) (words pre++block []++xs) [] := by
  rw [start_pop P q k f hp _ _ _ (by omega)]
  rw [show 4*(words pre).length+3=2*(words pre).length+(2+(2*(words pre).length+1)) by omega,
    UniversalStack.exec_from _ _ (2*(words pre).length) (2+(2*(words pre).length+1)),List.append_assoc,
    skip_words P q pre k.castSucc (by simp [hk])]
  simp only [Fin.val_castSucc,hk,Nat.sub_self,List.nil_append,Fin.mk_zero]
  rw [UniversalStack.exec_from _ _ 2 _,at_pop_nil P q k f hp,restore]

def encode (C : Config (Fin m) Bool Q) : Config (Fin 2) Bool (State m Q) :=
  config (.start C.state) (words (registers C.store)) []

def ticks (P : Q → Instr (Fin m) Bool Q) (C : Config (Fin m) Bool Q) : ℕ :=
  match P C.state with
  | .halt => 0
  | .push k _ _ | .pop k _ => 4*(words ((registers C.store).take k.val)).length+3

def clock (P : Q → Instr (Fin m) Bool Q) (C : Config (Fin m) Bool Q) : ℕ → ℕ
  | 0 => 0
  | n+1 => clock P C n+ticks P (exec P C n)

lemma words_length_le (ss : List (List Bool)) (B : ℕ) (h : ∀bs∈ss,bs.length≤B) :
    (words ss).length≤ ss.length*(2*B+1) := by
  induction ss with
  | nil => simp
  | cons bs ss ih =>
    have hb := h bs (by simp)
    have ht := ih (fun t ht => h t (by simp [ht]))
    simp only [words_cons,List.length_append,block_length,List.length_cons]
    nlinarith

lemma words_registers_length_le (r : Fin m → List Bool) (B : ℕ) (h : ∀k,(r k).length≤B) :
    (words (registers r)).length≤ m*(2*B+1) := by
  have H := words_length_le (registers r) B (by
    intro bs hb
    simp only [registers,List.mem_ofFn] at hb
    obtain ⟨k,rfl⟩ := hb
    simpa using h k)
  simpa using H

lemma words_take_length_le (ss : List (List Bool)) (k : ℕ) :
    (words (ss.take k)).length≤(words ss).length := by
  have h := congrArg (fun ts => (words ts).length) (List.take_append_drop k ss)
  simp only [words_append,List.length_append] at h
  omega

lemma ticks_bound (P : Q → Instr (Fin m) Bool Q) (C : Config (Fin m) Bool Q)
    (B : ℕ) (h : ∀k,(C.store k).length≤B) : ticks P C≤4*m*(2*B+1)+3 := by
  have H := words_registers_length_le C.store B h
  cases hp : P C.state with
  | halt => simp [ticks,hp]
  | push k b q =>
    have ht := words_take_length_le (registers C.store) k.val
    simp only [ticks,hp];nlinarith
  | pop k f =>
    have ht := words_take_length_le (registers C.store) k.val
    simp only [ticks,hp];nlinarith

theorem clock_bound (P : Q → Instr (Fin m) Bool Q) (C : Config (Fin m) Bool Q)
    (B : ℕ) (h : ∀k,(C.store k).length≤B) (n : ℕ) :
    clock P C n≤n*(4*m*(2*(B+n)+1)+3) := by
  induction n with
  | zero => simp [clock]
  | succ n ih =>
    have H := ticks_bound P (exec P C n) (B+n) (fun k =>
      (StackMachine.exec_length P C n k).trans (Nat.add_le_add_right (h k) n))
    rw [clock]
    have ht := Nat.add_le_add ih H
    nlinarith

end SourceBurnside.CompactStacks

namespace SourceBurnside.CompactInit
open Structured Structured.Program Structured.Binary
abbrev K := Fin 2
def pairs (x : List Bool) : List Bool := x.flatMap (fun b => [true,b])
lemma packet_length (x : List Bool) : (pairs x).length=2*x.length := by
  simp [pairs,Nat.mul_comm]
def layout (m j : ℕ) (x : List Bool) : List Bool :=
  List.replicate j false++pairs x++List.replicate (m-j) false
lemma layout_length {m j : ℕ} (hj : j ≤ m) (x : List Bool) : (layout m j x).length=m+2*x.length := by
  simp [layout,packet_length];omega
lemma program_time_le {m j : ℕ} (hj : j ≤ m) (x : List Bool) :
    (j+1)+(3*x.length+1)+((m-j+1)+(2*(layout m j x).length+1)) ≤ 3*m+7*x.length+4 := by
  rw [layout_length hj];omega
lemma words_empty (m : ℕ) : CompactStacks.words (List.replicate m [])=List.replicate m false := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ,ih]
lemma words_single (m : ℕ) (j : Fin m) (x : List Bool) :
    CompactStacks.words (List.ofFn (Function.update (fun _ : Fin m => []) j x))=
      List.replicate j.val false++CompactStacks.block x++List.replicate (m-j.val-1) false := by
  induction m with
  | zero => exact Fin.elim0 j
  | succ m ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · have h0 : (Function.update (fun _ : Fin (m+1) => []) 0 x) 0=x := by simp
      have ht : (fun i : Fin m => (Function.update (fun _ : Fin (m+1) => []) 0 x) i.succ)=(fun _ => []) := by
        funext i;simp
      rw [List.ofFn_succ,h0,ht]
      simp only [Fin.val_zero,Nat.sub_zero,List.replicate_zero,List.nil_append,List.ofFn_const,CompactStacks.words_cons,words_empty,Nat.add_sub_cancel]
    · have h0 : (Function.update (fun _ : Fin (m+1) => []) k.succ x) 0=[] := by
        exact Function.update_of_ne (Fin.succ_ne_zero k).symm _ _
      have ht : (fun i : Fin m => (Function.update (fun _ : Fin (m+1) => []) k.succ x) i.succ)=
          Function.update (fun _ : Fin m => []) k x := by
        funext i;by_cases h : i=k <;> simp [h]
      rw [List.ofFn_succ,h0,ht,CompactStacks.words_cons,ih]
      simp only [CompactStacks.block_nil,Fin.val_succ,List.replicate_succ,List.cons_append]
      have he : m+1-(k.val+1)-1=m-k.val-1 := by omega
      rw [he,List.nil_append]
lemma layout_eq_words {m : ℕ} (j : Fin m) (x : List Bool) :
    layout m j.val x=CompactStacks.words (CompactStacks.registers (Function.update (fun _ : Fin m => []) j x.reverse)) := by
  have he : (fun k => (Function.update (fun _ : Fin m => []) j x.reverse k).reverse)=
      Function.update (fun _ : Fin m => []) j x := by
    funext k;by_cases h : k=j <;> simp [h]
  rw [CompactStacks.registers,he,words_single]
  have hj : m-j.val=(m-j.val-1)+1 := by have := j.isLt;omega
  unfold layout CompactStacks.block
  change List.replicate j.val false++pairs x++List.replicate (m-j.val) false =
    List.replicate j.val false++(pairs x++[false])++List.replicate (m-j.val-1) false
  conv_lhs => rw [hj,List.replicate_succ]
  simp only [List.append_assoc,List.singleton_append]
end SourceBurnside.CompactInit

namespace SourceBurnside.FixedArity
noncomputable section
open StackMachine Structured Structured.Program Structured.Binary
variable {A B Q Q' : Type*} [DecidableEq A] [DecidableEq B]
def renameInstr (e : A ≃ B) : Instr A Bool Q → Instr B Bool Q
  | .halt => .halt
  | .push k b q => .push (e k) b q
  | .pop k f => .pop (e k) f
def renameConfig (e : A ≃ B) (C : Config A Bool Q) : Config B Bool Q := ⟨C.state,C.store ∘ e.symm⟩
def rename (e : A ≃ B) (P : Q → Instr A Bool Q) : Q → Instr B Bool Q := fun q => renameInstr e (P q)
lemma update_comp (e : A ≃ B) (r : A → List Bool) (k : A) (v : List Bool) :
    (Function.update r k v) ∘ e.symm=Function.update (r ∘ e.symm) (e k) v := by
  funext j
  by_cases h : j=e k
  · subst j;simp
  · have h' : e.symm j≠k := by intro H;apply h;rw [←H,Equiv.apply_symm_apply]
    simp [h,h']
lemma rename_next (e : A ≃ B) (P : Q → Instr A Bool Q) (C : Config A Bool Q) :
    next (rename e P) (renameConfig e C)=renameConfig e (next P C) := by
  cases h : P C.state <;> simp [next,rename,renameConfig,renameInstr,h,update_comp]
lemma rename_exec (e : A ≃ B) (P : Q → Instr A Bool Q) (C : Config A Bool Q) (n : ℕ) :
    exec (rename e P) (renameConfig e C) n=renameConfig e (exec P C n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [exec,ih,rename_next]
def liftInstr (f : Q → Q') : Instr A Bool Q → Instr (Option A) Bool Q'
  | .halt => .halt
  | .push k b q => .push (some k) b (f q)
  | .pop k g => .pop (some k) (fun b => f (g b))
end
end SourceBurnside.FixedArity

namespace SourceBurnside.CompactProgram
noncomputable section
open StackMachine Structured Structured.Program FixedArity
variable {A : Type*} [DecidableEq A] {m : ℕ}
def bootTime (e : Option A ≃ Fin m) (j : A) (x : List Bool) :=
  ((e (some j)).val+1)+(3*x.length+1)+((m-(e (some j)).val+1)+
    (2*(CompactInit.layout m (e (some j)).val x).length+1))
end
end SourceBurnside.CompactProgram

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_ProgramFixedPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteCode
noncomputable section
open StackMachine Structured.Program UniversalStack
variable {K Q R : Type*} [DecidableEq K]
def rename (e : Q ≃ R) (P : Q → StackMachine.Instr K Bool Q) : R → StackMachine.Instr K Bool R :=
  fun q => mapInstr e (P (e.symm q))
def config (e : Q ≃ R) (C : StackMachine.Config K Bool Q) : StackMachine.Config K Bool R := ⟨e C.state,C.store⟩
lemma rename_next (e : Q ≃ R) (P : Q → StackMachine.Instr K Bool Q) (C : StackMachine.Config K Bool Q) :
    next (rename e P) (config e C)=config e (next P C) := by
  cases h : P C.state <;> simp [next,rename,config,mapInstr,h]
lemma rename_exec (e : Q ≃ R) (P : Q → StackMachine.Instr K Bool Q) (C : StackMachine.Config K Bool Q) (n : ℕ) :
    exec (rename e P) (config e C) n=config e (exec P C n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [exec,ih,rename_next];rfl
lemma exec_halt (P : Q → StackMachine.Instr K Bool Q) (C : StackMachine.Config K Bool Q)
    (h : P C.state=.halt) (n : ℕ) : exec P C n=C := by
  induction n with
  | zero => rfl
  | succ n ih => simp [exec,ih,next,h]
lemma after_halt (P : Q → StackMachine.Instr K Bool Q) (C : StackMachine.Config K Bool Q)
    {k n : ℕ} (hkn : k ≤ n) (h : P (exec P C k).state=.halt) : exec P C n=exec P C k := by
  rw [←Nat.add_sub_of_le hkn,exec_from,exec_halt P _ h]
lemma first_halt (P : Q → StackMachine.Instr K Bool Q) (C : StackMachine.Config K Bool Q)
    (n : ℕ) (h : P (exec P C n).state=.halt) :
    ∃ k, k ≤ n ∧ (∀t,t<k → P (exec P C t).state≠.halt) ∧
      P (exec P C k).state=.halt ∧ exec P C k=exec P C n := by
  classical
  have hh : ∃ k,P (exec P C k).state=.halt := ⟨n,h⟩
  let k := Nat.find hh
  have hk : k ≤ n := Nat.find_min' hh h
  have hs : P (exec P C k).state=.halt := Nat.find_spec hh
  exact ⟨k,hk,(fun t ht => Nat.find_min hh ht),hs,(after_halt P C hk hs).symm⟩
def enumeration [Fintype Q] (q : Q) : Q ≃ Fin (Fintype.card Q) :=
  (Fintype.equivFin Q).trans (Equiv.swap ((Fintype.equivFin Q) q) ⟨0,Fintype.card_pos_iff.mpr ⟨q⟩⟩)
lemma enumeration_zero [Fintype Q] (q : Q) : (enumeration q q).val=0 := by simp [enumeration]
def program [Fintype Q] (P : Q → StackMachine.Instr K Bool Q) (q : Q) (result : Q → Bool) :
    List (Instruction K) := programOf (rename (enumeration q) P) (result ∘ (enumeration q).symm)
lemma first_program_trace {m : ℕ} (P : Fin m → StackMachine.Instr K Bool (Fin m))
    (result : Fin m → Bool) (C : StackMachine.Config K Bool (Fin m)) (n : ℕ) (b : Bool)
    (h : P (exec P C n).state=.halt) (hb : result (exec P C n).state=b) :
    ∃ t s front back,t ≤ (n+1)*(5*(encodeProgram (programOf P result)).length+3) ∧
      exec interpreter (UniversalStack.config .pick C.store (encodeProgram (programOf P result)) [] C.state.val) t=
        UniversalStack.config (.stopped b) s front back 0 := by
  obtain ⟨k,hkn,hpre,hs,he⟩ := first_halt P C n h
  have hr := finite_control_run P result C k hpre
  let q := (exec P C k).state
  have hq : P q=.halt := hs
  have hspl := programOf_split P result q
  simp only [instructionOf,hq] at hspl
  have hR : UniversalStack.Run (programOf P result) k C.state.val C.store
      ((programOf P result).take q.val).length (exec P C k).store := by
    simpa only [programOf_prefix_length] using hr
  obtain ⟨t,ht,H⟩ := simulate_halt (programOf P result)
    ((programOf P result).take q.val) ((programOf P result).drop (q.val+1)) (result q) hspl hR
  have hqb : result q=b := by simpa only [q,he] using hb
  rw [hqb] at H
  exact ⟨t,_,_,_,ht.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hkn 1)),H⟩
lemma program_trace [Fintype Q] (P : Q → StackMachine.Instr K Bool Q) (q : Q) (result : Q → Bool)
    (r : K → List Bool) (n : ℕ) (b : Bool) (h : P (exec P ⟨q,r⟩ n).state=.halt)
    (hb : result (exec P ⟨q,r⟩ n).state=b) :
    ∃ t s front back,t ≤ (n+1)*(5*(encodeProgram (program P q result)).length+3) ∧
      exec interpreter (UniversalStack.config .pick r (encodeProgram (program P q result)) [] 0) t=
        UniversalStack.config (.stopped b) s front back 0 := by
  let e := enumeration q
  have hE := rename_exec e P ⟨q,r⟩ n
  have hs : rename e P (exec (rename e P) (config e ⟨q,r⟩) n).state=.halt := by
    rw [hE];simp [rename,config,h,mapInstr]
  have hR : (result ∘ e.symm) (exec (rename e P) (config e ⟨q,r⟩) n).state=b := by
    rw [hE];simpa [config] using hb
  have H := first_program_trace (rename e P) (result ∘ e.symm) (config e ⟨q,r⟩) n b hs hR
  simpa only [program,config,e,enumeration_zero] using H
end
end SourceBurnside.FiniteCode

namespace SourceBurnside.LiteralCompiler
noncomputable section
open StackMachine Structured Structured.Program FixedArity
abbrev K := Option (Fin 2)
def src : K := some 1
def dst : K := some 0
lemma distinct : src≠dst := by decide
end
end SourceBurnside.LiteralCompiler

namespace SourceBurnside.PolynomialAccounting
open Structured Structured.Binary
lemma powers (S : ℕ) (hS : 1 ≤ S) : 1 ≤ S^2 ∧ S ≤ S^2 ∧ 1 ≤ S^4 ∧ S^2 ≤ S^4 ∧ S ≤ S^4 := by
  have h2 : S ≤ S^2 := by nlinarith
  have h4 : S^2 ≤ S^4 := by nlinarith [sq_nonneg (S^2-S)]
  omega
def compactCoefficient (m c d : ℕ) := 3*m+7*d+4+(c+1)*(4*m*(2*(d+c+1)+1)+3)
lemma compact_bound (m c d L n S : ℕ) (hS : 1 ≤ S) (hL : L ≤ d*S) (hn : n ≤ c*S^2) :
    3*m+7*L+4+(n+1)*(4*m*(2*(L+(n+1))+1)+3) ≤ compactCoefficient m c d*S^4 := by
  obtain ⟨hs2,hsq,hs4,hs24,hs14⟩ := powers S hS
  have hl2 : L ≤ d*S^2 := hL.trans (Nat.mul_le_mul_left d hsq)
  have hl4 : L ≤ d*S^4 := hL.trans (Nat.mul_le_mul_left d hs14)
  have hboot : 3*m+7*L+4 ≤ (3*m+7*d+4)*S^4 := by
    have H := Nat.mul_le_mul_left (3*m+4) hs4
    nlinarith
  have hn1 : n+1 ≤ (c+1)*S^2 := by nlinarith
  have hln : L+(n+1) ≤ (d+c+1)*S^2 := by nlinarith
  have hi0 : 2*(L+(n+1))+1 ≤ (2*(d+c+1)+1)*S^2 := by nlinarith
  have hi1 := Nat.mul_le_mul_left (4*m) hi0
  have hi : 4*m*(2*(L+(n+1))+1)+3 ≤ (4*m*(2*(d+c+1)+1)+3)*S^2 := by nlinarith
  have hm := Nat.mul_le_mul hn1 hi
  unfold compactCoefficient
  nlinarith
lemma interpreter_bound (a b c S : ℕ) (hS : 1 ≤ S) (ha : a ≤ b*S^4) :
    (a+1)*c ≤ (b+1)*c*S^4 := by
  have hs4 := (powers S hS).2.2.1
  have H : a+1 ≤ (b+1)*S^4 := by nlinarith
  have := Nat.mul_le_mul_right c H
  nlinarith
lemma oneTape_bound (L N C d S : ℕ) (hS : 1 ≤ S) (hL : L ≤ d*S) (hN : N ≤ C*S^4) :
    N*(2*(L+N)+3) ≤ C*(2*(d+C)+3)*S^8 := by
  have hs4 := (powers S hS).2.2.1
  have hs14 := (powers S hS).2.2.2.2
  have hl4 := hL.trans (Nat.mul_le_mul_left d hs14)
  have hsum : 2*(L+N)+3 ≤ (2*(d+C)+3)*S^4 := by nlinarith
  have H := Nat.mul_le_mul hN hsum
  nlinarith
end SourceBurnside.PolynomialAccounting

namespace SourceBurnside.RawTimeBound
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
open PolynomialAccounting
def size (h l : ℕ) (data : List Bool) := h+l+data.length+1
lemma positive (h l : ℕ) (data : List Bool) : 1 ≤ size h l data := by unfold size;omega
end SourceBurnside.RawTimeBound

namespace SourceBurnside.TimedTape
noncomputable section
open StackMachine Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
abbrev K := LiteralCompiler.K
abbrev SK := UniversalStack.Stack K
abbrev TK := UniversalStack.Token K
abbrev SQ := WrappedInput.State K
abbrev Γ := StackMachine.Symbol SK TK
abbrev Q := StackMachine.State SK TK SQ
def machine := WrappedInput.machine LiteralCompiler.src LiteralCompiler.dst
def δ := StackMachine.compile machine
def start (x : List Bool) : StackMachine.Config SK TK SQ :=
  WrappedInput.config LiteralCompiler.src LiteralCompiler.dst .reverse x [] [] [] 0
def finish (b : Bool) (r : K → List Bool) (front back : List TK) : StackMachine.Config SK TK SQ :=
  WrappedInput.liftConfig (UniversalInput.liftConfig (UniversalStack.config (.stopped b) r front back 0))
def blank : Γ := ⟨false,fun _ => none⟩
def origin : Γ := ⟨true,fun _ => none⟩
def bitSymbol (b : Bool) : Γ := ⟨false,fun k => if k=.reg LiteralCompiler.src then some (.bit b) else none⟩
def initialState : Q := .ready .reverse
def finalState (b : Bool) : Q := .ready (.inner (.universal (.stopped b)))
def output (b : Bool) : OneTape.Label Γ Q := ⟨origin,true,some (finalState b)⟩
lemma start_length (x : List Bool) (k : SK) : ((start x).store k).length ≤ x.length := by
  cases k with
  | reg k =>
    simp only [start,WrappedInput.config,UniversalStack.config,UniversalInput.inputRegs]
    split_ifs <;> simp
  | front => simp [start,WrappedInput.config,UniversalStack.config]
  | back => simp [start,WrappedInput.config,UniversalStack.config]
  | pc => simp [start,WrappedInput.config,UniversalStack.config]
lemma finish_halt (b : Bool) (r : K → List Bool) (front back : List TK) :
    machine (finish b r front back).state=.halt := rfl
lemma origin_tape (r : SK → List TK) : StackMachine.tape r 0=origin := by
  rfl
lemma finish_output (b : Bool) (r : K → List Bool) (front back : List TK) :
    (StackMachine.encode (finish b r front back)).cell 0=output b := by
  simp [StackMachine.encode,StackMachine.place,OneTape.Config.cell,finish,output,
    finalState,WrappedInput.liftConfig,UniversalInput.liftConfig,UniversalStack.config,origin_tape]
lemma output_injective : Function.Injective output := by
  intro b c h
  have H := congrArg OneTape.Label.head h
  simpa [output,finalState] using H
end
end SourceBurnside.TimedTape

namespace SourceBurnside.Tableau

inductive Formula (n : ℕ)
  | constant (b : Bool)
  | input (i : Fin n)
  | nand (a b : Formula n)

end SourceBurnside.Tableau

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_TimedExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.OneTape
open Tableau
variable {Γ Q : Type*}

structure Coding (Γ Q : Type*) where
  bits : ℕ
  positive : 0<bits
  encode : Label Γ Q → (Fin bits → Bool)
  decode : (Fin bits → Bool) → Label Γ Q
  decode_encode : ∀ a, decode (encode a)=a

namespace Coding
section
variable [Fintype Γ] [Fintype Q]
noncomputable def oneHotEncode (a : Label Γ Q) : Fin (Fintype.card (Label Γ Q)) → Bool :=
  fun i => decide (Fintype.equivFin (Label Γ Q) a=i)

lemma oneHotEncode_injective : Function.Injective (oneHotEncode (Γ:=Γ) (Q:=Q)) := by
  intro a b he
  have hh := congrFun he (Fintype.equivFin (Label Γ Q) a)
  have hb : Fintype.equivFin (Label Γ Q) b=Fintype.equivFin (Label Γ Q) a := by
    exact of_decide_eq_true (by simpa only [oneHotEncode,decide_true] using hh.symm)
  exact ((Fintype.equivFin (Label Γ Q)).injective hb).symm

end

variable (K : Coding Γ Q)
lemma encode_injective : Function.Injective K.encode := Function.LeftInverse.injective K.decode_encode

def transition (δ : Q → Γ → Command Γ Q) (v : Fin (3*K.bits) → Bool) : Fin K.bits → Bool :=
  let extract := fun b : Fin 3 => K.decode (fun r => v (finProdFinEquiv (b,r)))
  K.encode (localStep δ (extract 0) (extract 1) (extract 2))

def trace (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) (origin : ℕ)
    (t j : ℕ) : Fin K.bits → Bool := K.encode ((run δ C t).cell ((j:ℤ)-(origin:ℤ)))

end Coding

lemma far_cell (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) (blank : Γ)
    (hp : C.position=0) (t : ℕ) (j : ℤ) (hj : j< -(t:ℤ) ∨ (t:ℤ)<j)
    (hb : C.tape j=blank) : (run δ C t).cell j=⟨blank,false,none⟩ := by
  have hpos := run_position_bound δ C t
  rw [hp] at hpos
  have h0 : j≠0 := by omega
  have hne : j≠(run δ C t).position := by omega
  have htape : (run δ C t).tape j=C.tape j := run_tape_untouched δ C t j (by
    intro s hs
    have hh := run_position_bound δ C s
    rw [hp] at hh
    omega)
  simp [Config.cell,htape,hb,h0,hne]

namespace Coding
variable (K : Coding Γ Q)

lemma boundary_trace (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) (blank : Γ)
    (T : ℕ) (hT : 0<T) (hp : C.position=0)
    (hl : C.tape (-(2*(T:ℤ)))=blank) (hr : C.tape (2*(T:ℤ)-1)=blank)
    (t : ℕ) (ht : t<T) (j : ℕ) (hj : j=0 ∨ j+1=4*T) :
    K.trace δ C (2*T) t j=K.encode ⟨blank,false,none⟩ := by
  unfold trace
  apply congrArg K.encode
  rcases hj with rfl|hj
  · apply far_cell δ C blank hp t _
    · left; push_cast; omega
    · simpa using hl
  · have he : (j:ℤ)-((2*T:ℕ):ℤ)=2*(T:ℤ)-1 := by push_cast; omega
    rw [he]
    exact far_cell δ C blank hp t _ (Or.inr (by omega)) hr

end Coding
end SourceBurnside.OneTape

namespace SourceBurnside.ExponentialThreshold
open Filter Asymptotics
lemma polynomial_lt (C k : ℕ) : ∃n0 : ℕ, ∀n≥n0,C*n^k < 2^n := by
  have H : (fun n : ℕ => (C:ℝ)*(n:ℝ)^k) =o[atTop] (fun n => (2:ℝ)^n) :=
    (isLittleO_pow_const_const_pow_of_one_lt (R:=ℝ) k (by norm_num : (1:ℝ)<2)).const_mul_left C
  have he := H.eventuallyLT_norm_of_eventually_pos (Filter.Eventually.of_forall (fun n => norm_pos_iff.mpr (pow_ne_zero n (by norm_num : (2:ℝ)≠0))))
  obtain ⟨n0,h0⟩ := Filter.eventually_atTop.mp he
  refine ⟨n0,?_⟩
  intro n hn
  have HH := h0 n hn
  simp only [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤(C:ℝ)*(n:ℝ)^k),
    abs_of_nonneg (by positivity : 0≤(2:ℝ)^n)] at HH
  exact_mod_cast HH
lemma scaled (C k a : ℕ) (ha : 0<a) : ∃h0 : ℕ, ∀h≥h0,C*h^k < 2^(h/a) := by
  obtain ⟨n0,h0⟩ := polynomial_lt (C*(2*a)^k) k
  refine ⟨a*(n0+1),?_⟩
  intro h hh
  have hd : n0+1 ≤ h/a := (Nat.le_div_iff_mul_le ha).mpr (by simpa [Nat.mul_comm] using hh)
  have hbound : h ≤ 2*a*(h/a) := by
    have hr := Nat.mod_lt h ha
    have hre := Nat.mod_add_div h a
    have hf : a ≤ a*(h/a) := Nat.le_mul_of_pos_right a (by omega)
    nlinarith
  calc
    C*h^k ≤ C*(2*a*(h/a))^k := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbound k)
    _ = C*(2*a)^k*(h/a)^k := by ring
    _ < 2^(h/a) := h0 _ (by omega)
end SourceBurnside.ExponentialThreshold

namespace SourceBurnside.TimedTape
noncomputable section
variable {q : ℕ}
lemma initial_store (x : List Bool) (k : SK) :
    (start x).store k=if k=.reg LiteralCompiler.src then x.map UniversalStack.Token.bit else [] := by
  cases k with
  | reg k =>
    by_cases hh : k=LiteralCompiler.src
    · subst k;simp [start,WrappedInput.config,UniversalStack.config,UniversalInput.inputRegs]
    · simp [start,WrappedInput.config,UniversalStack.config,UniversalInput.inputRegs,hh]
  | front => rfl
  | back => rfl
  | pc => rfl
lemma raw_symbol_zero (x : List Bool) : StackMachine.tape (start x).store 0=origin := rfl
end
end SourceBurnside.TimedTape

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_GeometricRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable
namespace Rigid
variable {q d n : ℕ} [NeZero q]

def width (q : ℕ) := 2*q+1
omit [NeZero q] in
lemma width_pos : 0<width q := by simp [width]

def coord (i : Fin (n*width q)) : Fin (width q) :=
  ⟨i.val%width q,Nat.mod_lt _ width_pos⟩
def block (i : Fin (n*width q)) : Fin n :=
  ⟨i.val/width q,(Nat.div_lt_iff_lt_mul width_pos).mpr i.isLt⟩

end Rigid
end SourceBurnside.FiniteTable

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_WordAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.WordAlgebra

noncomputable section
open Classical

abbrev Word (α : Type u) := FreeMonoid α
abbrev Polynomial (K : Type v) (α : Type u) [Semiring K] := MonoidAlgebra K (Word α)

structure Table (α : Type u) where
  rep : Word α → Word α → Prop
  zero : Set (Word α)

variable {α : Type u} {K : Type v} [Ring K]

noncomputable def monomial (w : Word α) : Polynomial K α := MonoidAlgebra.single w 1

@[simp] theorem monomial_one : monomial (K := K) (1 : Word α) = 1 := rfl
@[simp] theorem monomial_mul (u v : Word α) :
    monomial (K := K) (u * v) = monomial u * monomial v := by
  simp [monomial, MonoidAlgebra.single_mul_single]

namespace Table

variable (T : Table α)

abbrev Reach : Word α → Word α → Prop := conGen T.rep

def relations : Set (Polynomial K α) :=
  {f | (∃ v w, T.rep v w ∧ f = monomial v - monomial w) ∨
    (∃ z ∈ T.zero, f = monomial z)}

abbrev ideal : TwoSidedIdeal (Polynomial K α) := TwoSidedIdeal.span T.relations

abbrev Algebra := (T.ideal (K := K)).ringCon.Quotient

noncomputable abbrev quotient : Polynomial K α →+* T.Algebra (K := K) :=
  (T.ideal (K := K)).ringCon.mk'

noncomputable def word (w : Word α) : T.Algebra (K := K) := T.quotient (monomial w)

@[simp] theorem word_one : T.word (K := K) 1 = 1 := map_one T.quotient

@[simp] theorem word_mul (v w : Word α) :
    T.word (K := K) (v * w) = T.word v * T.word w := by
  rw [word, monomial_mul, map_mul]; rfl

lemma word_rep {v w : Word α} (h : T.rep v w) : T.word (K := K) v = T.word w := by
  apply ((T.ideal (K := K)).ringCon.eq).mpr
  apply ((T.ideal (K := K)).rel_iff _ _).mpr
  exact TwoSidedIdeal.subset_span (Or.inl ⟨v, w, h, rfl⟩)

lemma word_zero {z : Word α} (hz : z ∈ T.zero) : T.word (K := K) z = 0 := by
  apply ((T.ideal (K := K)).ringCon.eq).mpr
  exact TwoSidedIdeal.subset_span (Or.inr ⟨z, hz, rfl⟩)

noncomputable def detect (target : Word α) : Polynomial K α →+ K := by
  classical
  exact (Finsupp.liftAddHom (fun w : Word α =>
    if T.Reach target w then AddMonoidHom.id K else 0)).comp
      MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

@[simp] lemma detect_single (target w : Word α) (a : K) :
    T.detect target (MonoidAlgebra.single w a) = if T.Reach target w then a else 0 := by
  classical
  change (Finsupp.liftAddHom (fun v : Word α =>
    if T.Reach target v then AddMonoidHom.id K else 0)) (Finsupp.single w a) = _
  rw [Finsupp.liftAddHom_apply_single]
  split <;> simp_all

end Table

end

end SourceBurnside.WordAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_PacketIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.PacketIntervals
variable {Γ : Type*}

def total (len : Γ → ℕ) (s : List Γ) : ℕ := (s.map len).sum

@[simp] lemma total_nil (len : Γ → ℕ) : total len [] = 0 := rfl
@[simp] lemma total_cons (len : Γ → ℕ) (c : Γ) (s : List Γ) :
    total len (c::s) = len c + total len s := rfl
@[simp] lemma total_append (len : Γ → ℕ) (s t : List Γ) :
    total len (s ++ t) = total len s + total len t := by simp [total]

def floorSplit (len : Γ → ℕ) : List Γ → ℕ → List Γ × List Γ
  | [], _ => ([],[])
  | c::s, N => if len c ≤ N then
      let p := floorSplit len s (N-len c)
      (c::p.1,p.2)
    else ([],c::s)

def ceilSplit (len : Γ → ℕ) : List Γ → ℕ → List Γ × List Γ
  | [], _ => ([],[])
  | c::s, N => if N=0 then ([],c::s) else if N ≤ len c then ([c],s) else
      let p := ceilSplit len s (N-len c)
      (c::p.1,p.2)

structure Selection (Γ : Type*) where
  before : List Γ
  inside : List Γ
  after : List Γ
  deriving DecidableEq

def select (len : Γ → ℕ) (s : List Γ) (a e : ℕ) : Selection Γ :=
  let p := ceilSplit len s a
  let q := floorSplit len p.2 (e-total len p.1)
  ⟨p.1,q.1,q.2⟩

end SourceBurnside.PacketIntervals

namespace SourceBurnside.DirectCancellation
open scoped BigOperators
open Classical
noncomputable section

variable {Γ α T A : Type*}

def spell (label : Γ → List α) (s : List Γ) : List α := s.flatMap label

@[simp] lemma spell_append (label : Γ → List α) (s t : List Γ) :
    spell label (s++t) = spell label s ++ spell label t := by simp [spell]

variable [Monoid A]

def eval (f : α → A) (s : List α) : A := (s.map f).prod

@[simp] lemma eval_append (f : α → A) (s t : List α) :
    eval f (s++t) = eval f s * eval f t := by simp [eval]

end
end SourceBurnside.DirectCancellation

namespace SourceBurnside.DirectCancellation
open scoped BigOperators
open Classical
noncomputable section

variable {Γ α T K A : Type*} [Fintype Γ] [CommRing K] [CharP K 2]
  [Ring A] [Algebra K A]

def candidates (Γ : Type*) [Fintype Γ] (n : ℕ) : Finset (List Γ) :=
  Finset.univ.image (fun s : Σ r : Fin (n+1), Fin r.val → Γ => List.ofFn s.2)

end
end SourceBurnside.DirectCancellation

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_DirectCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.DirectCancellation
open scoped BigOperators
open Classical
noncomputable section

variable {α T A : Type*} [Ring A]

def EligibleInterval (eligible : T → Prop) (q : ℕ) (v : List T) (a e : ℕ) : Prop :=
  a < e ∧ e ≤ v.length ∧ q ≤ 100*(e-a) ∧
    ∃ t, eligible t ∧ ((v.drop a).take (e-a) = List.replicate (e-a) t) ∧
      (v.take a).getLast? ≠ some t ∧ (v.drop e).head? ≠ some t

def firstLongRun (eligible : T → Prop) (q : ℕ) (v : List T) : ℕ × ℕ :=
  if h : ∃ a, ∃ e, EligibleInterval eligible q v a e then
    let a := Nat.find h
    (a, Nat.find (Nat.find_spec h))
  else (0,0)

end
end SourceBurnside.DirectCancellation

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_HierarchyGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.Cuts
open Classical
noncomputable section
variable {α : Type*}

def parse (cut : α → Prop) : List α → List α × List (List α)
  | [] => ([],[])
  | a::w =>
    let p := parse cut w
    if cut a then ([],(a::p.1)::p.2) else (a::p.1,p.2)

def NoCut (cut : α → Prop) (w : List α) : Prop := ∀ a ∈ w, ¬ cut a

def Interval (cut : α → Prop) (w : List α) : Prop :=
  ∃ a t, w=a::t ∧ cut a ∧ NoCut cut t

end
end SourceBurnside.Cuts
namespace SourceBurnside.FiniteTable
noncomputable section
open Classical Cuts
variable {q : ℕ}
  [NeZero q]
  {d : ℕ}

def fragmentBound (q : ℕ) := 12*(17*q+3)
end
end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_MatrixTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.CutReduction
open scoped BigOperators
open Classical
noncomputable section
variable {α Γ R : Type*} [Fintype α] [Fintype Γ] [Semiring R]

def candidates (α : Type*) [Fintype α] (n : ℕ) : Finset (List α) :=
  Finset.univ.image (fun s : Σ r : Fin (n+1), Fin r.val → α => List.ofFn s.2)

def eval (f : α → R) (w : List α) : R := (w.map f).prod
omit [Fintype α] [Fintype Γ] in
@[simp] lemma eval_append (f : α → R) (u v : List α) :
    eval f (u++v) = eval f u * eval f v := by simp [eval]

def chunkSum (len : Γ → ℕ) (weight : Γ → R) (m : ℕ) : R :=
  ∑ gs ∈ (candidates Γ m).filter (fun gs => (gs.map len).sum=m), eval weight gs

def letterSum (f : α → R) (n : ℕ) : R :=
  ∑ w ∈ (candidates α n).filter (fun w => w.length=n), eval f w

def join (token : Γ → List α) (x : List α × List α × List Γ) : List α :=
  x.1 ++ x.2.2.flatMap token ++ x.2.1

def language (token : Γ → List α) (ps ss : Finset (List α)) (n : ℕ) :
    Finset (List α × List α × List Γ) :=
  (ps.product (ss.product (candidates Γ n))).filter (fun x => (join token x).length=n)

end
end SourceBurnside.CutReduction

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_PresentationModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside

@[simp] theorem map_bracket {G : Type u} {H : Type v} [Group G] [Group H]
    (f : G →* H) (a b : G) : f (bracket a b) = bracket (f a) (f b) := by
  simp [bracket]

theorem bracket_eq_one_iff {G : Type u} [Group G] (a b : G) :
    bracket a b = 1 ↔ Commute a b := by
  simp only [bracket, mul_inv_eq_iff_eq_mul, one_mul]
  rfl

namespace Steinberg

variable {n : ℕ} {R : Type u} [Ring R]

def x (p : Root n) (a : R) : Steinberg n R := PresentedGroup.of (p, a)

@[simp] theorem x_add (p : Root n) (a b : R) : x p (a + b) = x p a * x p b := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (SteinbergRel.add p a b)

@[simp] theorem x_zero (p : Root n) : x p (0 : R) = 1 := by
  have h := x_add p (0 : R) 0
  simp only [zero_add] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

@[simp] theorem x_neg (p : Root n) (a : R) : x p (-a) = (x p a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← x_add, add_neg_cancel, x_zero]

theorem x_commute (p q : Root n) (h₁ : p.col ≠ q.row) (h₂ : p.row ≠ q.col)
    (a b : R) : Commute (x p a) (x q b) := by
  apply (bracket_eq_one_iff _ _).mp
  have h := PresentedGroup.one_of_mem (SteinbergRel.commute p q h₁ h₂ a b)
  simp only [bracket, map_mul] at h
  exact h

theorem x_mul (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) :
    bracket (x ⟨i, j, hij⟩ a) (x ⟨j, k, hjk⟩ b) = x ⟨i, k, hik⟩ (a * b) := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (SteinbergRel.mul i j k hij hjk hik a b)
  simp only [bracket, map_mul] at h
  exact h

def lift {G : Type v} [Group G] (f : Root n → R → G)
    (ha : ∀ p a b, f p (a + b) = f p a * f p b)
    (hc : ∀ p q, p.col ≠ q.row → p.row ≠ q.col → ∀ a b, Commute (f p a) (f q b))
    (hm : ∀ i j k hij hjk hik a b,
      bracket (f ⟨i, j, hij⟩ a) (f ⟨j, k, hjk⟩ b) = f ⟨i, k, hik⟩ (a * b)) :
    Steinberg n R →* G :=
  PresentedGroup.toGroup (f := fun g => f g.1 g.2) (by
    intro r hr
    cases hr with
    | add p a b => simp [letter, ha]
    | commute p q h₁ h₂ a b =>
      simpa [letter] using (bracket_eq_one_iff _ _).mpr (hc p q h₁ h₂ a b)
    | mul i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_bracket, letter, FreeGroup.lift_apply_of]
      rw [hm i j k hij hjk hik a b, mul_inv_cancel])

@[simp] theorem lift_x {G : Type v} [Group G] (f : Root n → R → G) ha hc hm
    (p : Root n) (a : R) : lift f ha hc hm (x p a) = f p a :=
  PresentedGroup.toGroup.of _

@[ext] theorem hom_ext {G : Type v} [Group G] {f g : Steinberg n R →* G}
    (h : ∀ p a, f (x p a) = g (x p a)) : f = g := by
  apply PresentedGroup.ext
  rintro ⟨p, a⟩
  exact h p a

def map {S : Type v} [Ring S] (f : R →+* S) : Steinberg n R →* Steinberg n S :=
  lift (fun p a => x p (f a)) (by simp) (by intros; apply x_commute <;> assumption)
    (by intros; simpa using x_mul _ _ _ _ _ _ _ _)

@[simp] theorem map_x {S : Type v} [Ring S] (f : R →+* S) (p : Root n) (a : R) :
    map f (x p a) = x p (f a) := lift_x _ _ _ _ _ _

end Steinberg

end SourceBurnside

namespace SourceBurnside

namespace Elementary

variable {n : ℕ} {R : Type u} [Ring R]

def e (p : Root n) (a : R) : (Matrix (Fin n) (Fin n) R)ˣ where
  val := 1 + Matrix.single p.row p.col a
  inv := 1 + Matrix.single p.row p.col (-a)
  val_inv := by simp [add_mul, mul_add, p.ne.symm, ← Matrix.single_neg, add_assoc]
  inv_val := by simp [add_mul, mul_add, p.ne.symm, ← Matrix.single_neg, add_assoc]

@[simp] theorem coe_e (p : Root n) (a : R) :
    ↑(e p a) = 1 + Matrix.single p.row p.col a := rfl

@[simp] theorem e_add (p : Root n) (a b : R) : e p (a + b) = e p a * e p b := by
  apply Units.ext
  simp [coe_e, add_mul, mul_add, p.ne.symm, Matrix.single_add, add_assoc]

@[simp] theorem e_zero (p : Root n) : e p (0 : R) = 1 := by
  apply Units.ext
  simp

@[simp] theorem e_inv (p : Root n) (a : R) : (e p a)⁻¹ = e p (-a) := by
  apply Units.ext
  rfl

theorem e_commute (p q : Root n) (h₁ : p.col ≠ q.row) (h₂ : p.row ≠ q.col)
    (a b : R) : Commute (e p a) (e q b) := by
  change e p a * e q b = e q b * e p a
  apply Units.ext
  simp only [Units.val_mul, coe_e, add_mul, mul_add, one_mul, mul_one,
    Matrix.single_mul_single_of_ne _ _ _ _ h₁,
    Matrix.single_mul_single_of_ne _ _ _ _ h₂.symm]
  abel

theorem e_mul (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) :
    bracket (e ⟨i, j, hij⟩ a) (e ⟨j, k, hjk⟩ b) = e ⟨i, k, hik⟩ (a * b) := by
  apply Units.ext
  simp only [bracket, e_inv, Units.val_mul, coe_e]
  simp only [add_mul, mul_add, one_mul, mul_one]
  simp [hij.symm, hjk.symm, hik.symm, ← Matrix.single_neg]
  abel

def representation : Steinberg n R →* (Matrix (Fin n) (Fin n) R)ˣ :=
  Steinberg.lift e e_add e_commute e_mul

@[simp] theorem representation_x (p : Root n) (a : R) :
    representation (Steinberg.x p a) = e p a := Steinberg.lift_x _ _ _ _ _ _

end Elementary

end SourceBurnside

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_MonomialPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside

namespace CommutatorCalculus

variable {G : Type u} [Group G]

 theorem commute_bracket_right {x a b : G} (ha : Commute x a) (hb : Commute x b) :
    Commute x (bracket a b) :=
  ((ha.mul_right hb).mul_right ha.inv_right).mul_right hb.inv_right

 theorem commute_bracket_left {a b x : G} (ha : Commute a x) (hb : Commute b x) :
    Commute (bracket a b) x := (commute_bracket_right ha.symm hb.symm).symm

 theorem mul_left (a b c : G) :
    bracket (a * b) c = a * bracket b c * a⁻¹ * bracket a c := by
  simp [bracket, mul_assoc]

 theorem mul_right (a b c : G) :
    bracket a (b * c) = bracket a b * b * bracket a c * b⁻¹ := by
  simp [bracket, mul_assoc]

 theorem conj_of_commute {a b : G} (h : Commute a b) : a * b * a⁻¹ = b := by
  rw [h.eq, mul_inv_cancel_right]

 theorem separated (a b c d : G)
    (hac : Commute a c) (had : Commute a d)
    (hbc : Commute b c) (hbd : Commute b d) :
    bracket (a * c) (b * d) = bracket a b * bracket c d := by
  have hAD := commute_bracket_right hac had
  have hBD := commute_bracket_right hbc hbd
  rw [mul_left, mul_right, mul_right,
    (bracket_eq_one_iff _ _).mpr hbc.symm,
    (bracket_eq_one_iff _ _).mpr had]
  simp only [one_mul, mul_one, mul_inv_cancel_right]
  rw [conj_of_commute hBD, conj_of_commute hAD]
  exact (commute_bracket_left hAD hBD).symm.eq

 theorem three_factor (X Y Z : G)
    (hAX : Commute (bracket X Y) X) (_hAY : Commute (bracket X Y) Y)
    (_hBY : Commute (bracket Y Z) Y) (hBZ : Commute (bracket Y Z) Z)
    (hAB : Commute (bracket X Y) (bracket Y Z)) (hXZ : Commute X Z) :
    bracket (bracket X Y) Z = bracket X (bracket Y Z) ∧
    Commute (bracket (bracket X Y) Z) (bracket X Y) ∧
    Commute (bracket (bracket X Y) Z) Z ∧
    Commute (bracket (bracket X Y) Z) X ∧
    Commute (bracket (bracket X Y) Z) (bracket Y Z) := by
  let A := bracket X Y
  let B := bracket Y Z
  let C := bracket A⁻¹ Z
  let D := bracket X B
  have hconjX : Y * X * Y⁻¹ = A⁻¹ * X := by simp [A, bracket, mul_assoc]
  have hconjZ : Y * Z * Y⁻¹ = B * Z := by simp [B, bracket, mul_assoc]
  have hc : Commute (A⁻¹ * X) (Z * B) := by
    have hBZeq : B * Z = Z * B := hBZ.eq
    simpa only [hconjX, hconjZ, hBZeq] using hXZ.conj Y
  have hCD : C * D = 1 := by
    rw [← separated A⁻¹ Z X B hAX.inv_left hAB.inv_left hXZ.symm hBZ.symm]
    exact (bracket_eq_one_iff _ _).mpr hc
  have hC : C = D⁻¹ := eq_inv_of_mul_eq_one_left hCD
  have hDA : Commute D A := commute_bracket_left hAX.symm hAB.symm
  have hDZ : Commute D Z := commute_bracket_left hXZ hBZ
  have hCX : Commute C X := commute_bracket_left hAX.inv_left hXZ.symm
  have hCB : Commute C B := commute_bracket_left hAB.inv_left hBZ.symm
  have hCA : Commute C A := hC ▸ hDA.inv_left
  have hmain : bracket A Z = D := by
    apply inv_injective
    calc
      (bracket A Z)⁻¹ = A * C * A⁻¹ := by simp [C, bracket, mul_assoc]
      _ = C := conj_of_commute hCA.symm
      _ = D⁻¹ := hC
  refine ⟨hmain, ?_, ?_, ?_, ?_⟩
  · exact hmain ▸ hDA
  · exact hmain ▸ hDZ
  · rw [hmain]
    exact (Commute.inv_left_iff.mp (hC ▸ hCX))
  · rw [hmain]
    exact (Commute.inv_left_iff.mp (hC ▸ hCB))

end CommutatorCalculus

theorem exists_fresh {n : ℕ} (hn : 5 ≤ n) (i j k l : Fin n) :
    ∃ a : Fin n, a ≠ i ∧ a ≠ j ∧ a ≠ k ∧ a ≠ l := by
  have hcard : ({i, j, k, l} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    have := (Finset.card_le_four : ({i, j, k, l} : Finset (Fin n)).card ≤ 4)
    simpa using (lt_of_le_of_lt this (show 4 < n by omega))
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨a, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ha⟩

namespace MonomialCompletion

variable {n : ℕ} {α : Type u} {G : Type v} [Group G]

structure Seed (n : ℕ) (α : Type u) (G : Type v) [Group G] where
  g : Root n → List α → G
  square : ∀ p w, w.length ≤ 2 → g p w ^ 2 = 1
  commute : ∀ p q u v, u.length ≤ 2 → v.length ≤ 2 →
    p.col ≠ q.row → p.row ≠ q.col → Commute (g p u) (g q v)
  product : ∀ (i j k : Fin n) hij hjk hik (u v : List α),
    u.length + v.length ≤ 2 →
    bracket (g ⟨i, j, hij⟩ u) (g ⟨j, k, hjk⟩ v) = g ⟨i, k, hik⟩ (u ++ v)

noncomputable def middle (hn : 5 ≤ n) (p : Root n) : Fin n :=
  (exists_fresh hn p.row p.col p.row p.col).choose

theorem middle_ne_row (hn : 5 ≤ n) (p : Root n) : middle hn p ≠ p.row :=
  (exists_fresh hn p.row p.col p.row p.col).choose_spec.1

theorem middle_ne_col (hn : 5 ≤ n) (p : Root n) : middle hn p ≠ p.col :=
  (exists_fresh hn p.row p.col p.row p.col).choose_spec.2.1

noncomputable def word (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) : List α → G
  | [] => s.g p []
  | [a] => s.g p [a]
  | [a, b] => s.g p [a, b]
  | a :: b :: c :: w =>
    bracket (s.g ⟨p.row, middle hn p, (middle_ne_row hn p).symm⟩ [a])
      (word s hn ⟨middle hn p, p.col, middle_ne_col hn p⟩ (b :: c :: w))

 theorem word_short (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) (w : List α)
    (hw : w.length ≤ 2) : word s hn p w = s.g p w := by
  match w with
  | [] | [_] | [_, _] => rfl
  | _ :: _ :: _ :: _ => simp only [List.length_cons] at hw; omega

 theorem word_long (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) (a : α) (v : List α)
    (hv : 2 ≤ v.length) :
    word s hn p (a :: v) =
      bracket (word s hn ⟨p.row, middle hn p, (middle_ne_row hn p).symm⟩ [a])
        (word s hn ⟨middle hn p, p.col, middle_ne_col hn p⟩ v) := by
  match v with
  | [] | [_] => simp only [List.length_cons, List.length_nil] at hv; omega
  | _ :: _ :: _ => rfl

abbrev RootWords (n : ℕ) (α : Type u) (G : Type v) := Root n → List α → G

def ProductUpTo (y : RootWords n α G) (N : ℕ) : Prop :=
  ∀ (i j k : Fin n) hij hjk hik (u v : List α), u.length + v.length ≤ N →
    bracket (y ⟨i, j, hij⟩ u) (y ⟨j, k, hjk⟩ v) = y ⟨i, k, hik⟩ (u ++ v)

def CommuteUpTo (y : RootWords n α G) (N : ℕ) : Prop :=
  ∀ p q u v, u.length ≤ N → v.length ≤ N → p.col ≠ q.row → p.row ≠ q.col →
    Commute (y p u) (y q v)

def SquaresUpTo (y : RootWords n α G) (N : ℕ) : Prop :=
  ∀ p w, w.length ≤ N → y p w ^ 2 = 1

def Good (y : RootWords n α G) (N : ℕ) : Prop :=
  ProductUpTo y N ∧ CommuteUpTo y N ∧ SquaresUpTo y N

 theorem base_good (s : Seed n α G) (hn : 5 ≤ n) (N : ℕ) (hN : N ≤ 2) :
    Good (word s hn) N := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j k hij hjk hik u v huv
    rw [word_short _ _ _ _ (by omega), word_short _ _ _ _ (by omega),
      word_short _ _ _ _ (by simp only [List.length_append]; omega)]
    exact s.product i j k hij hjk hik u v (by omega)
  · intro p q u v hu hv h₁ h₂
    rw [word_short _ _ _ _ (by omega), word_short _ _ _ _ (by omega)]
    exact s.commute p q u v (by omega) (by omega) h₁ h₂
  · intro p w hw
    rw [word_short _ _ _ _ (by omega)]
    exact s.square p w (by omega)

 theorem reassociate_of (y : RootWords n α G) {M : ℕ}
    (hc : CommuteUpTo y M)
    (i a b j : Fin n) (hia : i ≠ a) (hib : i ≠ b) (hij : i ≠ j)
    (hab : a ≠ b) (haj : a ≠ j) (hbj : b ≠ j)
    (u v z : List α) (huv : u.length + v.length ≤ M) (hvz : v.length + z.length ≤ M)
    (hA : bracket (y ⟨i, a, hia⟩ u) (y ⟨a, b, hab⟩ v) = y ⟨i, b, hib⟩ (u ++ v))
    (hB : bracket (y ⟨a, b, hab⟩ v) (y ⟨b, j, hbj⟩ z) = y ⟨a, j, haj⟩ (v ++ z)) :
    bracket (y ⟨i, b, hib⟩ (u ++ v)) (y ⟨b, j, hbj⟩ z) =
      bracket (y ⟨i, a, hia⟩ u) (y ⟨a, j, haj⟩ (v ++ z)) := by
  have h := CommutatorCalculus.three_factor
    (y ⟨i, a, hia⟩ u) (y ⟨a, b, hab⟩ v) (y ⟨b, j, hbj⟩ z)
    (by rw [hA]; exact hc _ _ _ _ (by simp only [List.length_append]; omega) (by omega) hib.symm hia)
    (by rw [hA]; exact hc _ _ _ _ (by simp only [List.length_append]; omega) (by omega) hab.symm hib)
    (by rw [hB]; exact hc _ _ _ _ (by simp only [List.length_append]; omega) (by omega) haj.symm hab)
    (by rw [hB]; exact hc _ _ _ _ (by simp only [List.length_append]; omega) (by omega) hbj.symm haj)
    (by
      rw [hA, hB]
      exact hc _ _ _ _ (by simp only [List.length_append]; omega)
        (by simp only [List.length_append]; omega) hab.symm hij)
    (hc _ _ _ _ (by omega) (by omega) hab hij)
  simpa only [hA, hB] using h.1

 theorem reassociate (y : RootWords n α G) {M : ℕ}
    (hp : ProductUpTo y M) (hc : CommuteUpTo y M)
    (i a b j : Fin n) (hia : i ≠ a) (hib : i ≠ b) (hij : i ≠ j)
    (hab : a ≠ b) (haj : a ≠ j) (hbj : b ≠ j)
    (u v z : List α) (huv : u.length + v.length ≤ M) (hvz : v.length + z.length ≤ M) :
    bracket (y ⟨i, b, hib⟩ (u ++ v)) (y ⟨b, j, hbj⟩ z) =
      bracket (y ⟨i, a, hia⟩ u) (y ⟨a, j, haj⟩ (v ++ z)) :=
  reassociate_of y hc i a b j hia hib hij hab haj hbj u v z huv hvz
    (hp i a b hia hab hib u v huv) (hp a b j hab hbj haj v z hvz)

 theorem first_cut_independent (y : RootWords n α G) (hn : 5 ≤ n) {M : ℕ}
    (hp : ProductUpTo y M) (hc : CommuteUpTo y M)
    (i j h h' : Fin n) (hij : i ≠ j) (hih : i ≠ h) (hhj : h ≠ j)
    (hih' : i ≠ h') (hh'j : h' ≠ j) (a b : α) (v : List α)
    (hM : 2 ≤ M) (hv : 1 + v.length ≤ M) :
    bracket (y ⟨i, h, hih⟩ [a]) (y ⟨h, j, hhj⟩ (b :: v)) =
      bracket (y ⟨i, h', hih'⟩ [a]) (y ⟨h', j, hh'j⟩ (b :: v)) := by
  obtain ⟨c, hci, hcj, hch, hch'⟩ := exists_fresh hn i j h h'
  have h₁ := reassociate y hp hc i h c j hih hci.symm hij hch.symm hhj hcj
    [a] [b] v (by simpa) (by simpa [Nat.add_comm] using hv)
  have h₂ := reassociate y hp hc i h' c j hih' hci.symm hij hch'.symm hh'j hcj
    [a] [b] v (by simpa) (by simpa [Nat.add_comm] using hv)
  simpa using h₁.symm.trans h₂

 theorem first_cut_next (s : Seed n α G) (hn : 5 ≤ n) {M : ℕ}
    (hp : ProductUpTo (word s hn) M) (hc : CommuteUpTo (word s hn) M)
    (i h j : Fin n) (hih : i ≠ h) (hhj : h ≠ j) (hij : i ≠ j)
    (a : α) (v : List α) (hv₂ : 2 ≤ v.length) (hvM : v.length ≤ M) :
    bracket (word s hn ⟨i, h, hih⟩ [a]) (word s hn ⟨h, j, hhj⟩ v) =
      word s hn ⟨i, j, hij⟩ (a :: v) := by
  rw [word_long _ _ _ _ _ hv₂]
  cases v with
  | nil => simp at hv₂
  | cons b v =>
    exact first_cut_independent _ hn hp hc i j h (middle hn ⟨i, j, hij⟩)
      hij hih hhj (middle_ne_row hn ⟨i, j, hij⟩).symm (middle_ne_col hn ⟨i, j, hij⟩) a b v
      (by omega) (by simpa [Nat.add_comm] using hvM)

 theorem positive_next (s : Seed n α G) (hn : 5 ≤ n) {M : ℕ} (hM : 2 ≤ M)
    (hp : ProductUpTo (word s hn) M) (hc : CommuteUpTo (word s hn) M)
    (i h j : Fin n) (hih : i ≠ h) (hhj : h ≠ j) (hij : i ≠ j)
    (u v : List α) (hu : 0 < u.length) (hv : 0 < v.length)
    (huv : u.length + v.length ≤ M + 1) :
    bracket (word s hn ⟨i, h, hih⟩ u) (word s hn ⟨h, j, hhj⟩ v) =
      word s hn ⟨i, j, hij⟩ (u ++ v) := by
  by_cases hsmall : u.length + v.length ≤ M
  · exact hp i h j hih hhj hij u v hsmall
  cases u with
  | nil => simp at hu
  | cons a u =>
    cases u with
    | nil =>
      exact first_cut_next s hn hp hc i h j hih hhj hij a v
        (by simp only [List.length_cons, List.length_nil] at hsmall; omega)
        (by simp only [List.length_cons, List.length_nil] at huv; omega)
    | cons b u =>
      obtain ⟨c, hci, hcj, hch, _⟩ := exists_fresh hn i j h h
      have hassoc := reassociate (word s hn) hp hc i c h j hci.symm hih hij
        hch hcj hhj [a] (b :: u) v
        (by simp only [List.length_cons, List.length_nil] at *; omega)
        (by simp only [List.length_cons] at *; omega)
      calc
        bracket (word s hn ⟨i, h, hih⟩ (a :: b :: u)) (word s hn ⟨h, j, hhj⟩ v) =
            bracket (word s hn ⟨i, c, hci.symm⟩ [a])
              (word s hn ⟨c, j, hcj⟩ ((b :: u) ++ v)) := hassoc
        _ = word s hn ⟨i, j, hij⟩ ((a :: b :: u) ++ v) :=
          first_cut_next s hn hp hc i c j hci.symm hcj hij a ((b :: u) ++ v)
            (by simp only [List.length_cons, List.length_append] at *; omega)
            (by simp only [List.length_cons, List.length_append] at *; omega)

 theorem commute_next_short (s : Seed n α G) (hn : 5 ≤ n) {M : ℕ} (hM : 2 ≤ M)
    (hp : ProductUpTo (word s hn) M) (hc : CommuteUpTo (word s hn) M)
    (p q : Root n) (u v : List α) (hu : u.length ≤ M + 1) (hv : v.length ≤ M)
    (hpq : p.col ≠ q.row) (hqp : p.row ≠ q.col) :
    Commute (word s hn p u) (word s hn q v) := by
  by_cases hus : u.length ≤ M
  · exact hc p q u v hus hv hpq hqp
  cases u with
  | nil => simp at hus
  | cons a u =>
    obtain ⟨c, hci, hcj, hck, hcl⟩ := exists_fresh hn p.row p.col q.row q.col
    have he := positive_next s hn hM hp hc p.row c p.col hci.symm hcj p.ne
      [a] u (by simp) (by simp only [List.length_cons] at hus; omega)
      (by simp only [List.length_cons, List.length_nil] at *; omega)
    rw [show word s hn p (a :: u) =
      bracket (word s hn ⟨p.row, c, hci.symm⟩ [a]) (word s hn ⟨c, p.col, hcj⟩ u) from he.symm]
    apply CommutatorCalculus.commute_bracket_left
    · exact hc _ _ _ _ (by simp; omega) hv hck hqp
    · exact hc _ _ _ _ (by simp only [List.length_cons] at hu; omega) hv hpq hcl

 theorem commute_next (s : Seed n α G) (hn : 5 ≤ n) {M : ℕ} (hM : 2 ≤ M)
    (hp : ProductUpTo (word s hn) M) (hc : CommuteUpTo (word s hn) M) :
    CommuteUpTo (word s hn) (M + 1) := by
  intro p q u v hu hv hpq hqp
  by_cases hus : u.length ≤ M
  · exact (commute_next_short s hn hM hp hc q p v u hv hus hqp.symm hpq.symm).symm
  cases u with
  | nil => simp at hus
  | cons a u =>
    obtain ⟨c, hci, hcj, hck, hcl⟩ := exists_fresh hn p.row p.col q.row q.col
    have he := positive_next s hn hM hp hc p.row c p.col hci.symm hcj p.ne
      [a] u (by simp) (by simp only [List.length_cons] at hus; omega)
      (by simp only [List.length_cons, List.length_nil] at *; omega)
    rw [show word s hn p (a :: u) =
      bracket (word s hn ⟨p.row, c, hci.symm⟩ [a]) (word s hn ⟨c, p.col, hcj⟩ u) from he.symm]
    apply CommutatorCalculus.commute_bracket_left
    · exact (commute_next_short s hn hM hp hc q ⟨p.row, c, hci.symm⟩ v [a] hv (by simp; omega)
        hqp.symm hck.symm).symm
    · exact (commute_next_short s hn hM hp hc q ⟨c, p.col, hcj⟩ v u hv
        (by simp only [List.length_cons] at hu; omega) hcl.symm hpq.symm).symm

 theorem bracket_square {a b : G} (ha : a ^ 2 = 1) (hc : Commute (bracket a b) a) :
    bracket a b ^ 2 = 1 := by
  have haa : a * a = 1 := by simpa only [pow_two] using ha
  have hai : a⁻¹ = a := (eq_inv_of_mul_eq_one_left haa).symm
  have hinv : bracket a b = (bracket a b)⁻¹ := by
    calc
      bracket a b = a * bracket a b * a⁻¹ := (CommutatorCalculus.conj_of_commute hc.symm).symm
      _ = (bracket a b)⁻¹ := by
        simp only [bracket, mul_inv_rev, inv_inv, hai]
        simp only [← mul_assoc, haa, one_mul]
  rw [pow_two]
  conv_lhs => lhs; rw [hinv]
  exact inv_mul_cancel _

 theorem squares_next (s : Seed n α G) (hn : 5 ≤ n) {M : ℕ} (hM : 2 ≤ M)
    (hp : ProductUpTo (word s hn) M) (hc : CommuteUpTo (word s hn) M)
    (hs : SquaresUpTo (word s hn) M) : SquaresUpTo (word s hn) (M + 1) := by
  intro p u hu
  by_cases hus : u.length ≤ M
  · exact hs p u hus
  cases u with
  | nil => simp at hus
  | cons a u =>
    let c := middle hn p
    have hci : c ≠ p.row := middle_ne_row hn p
    have hcj : c ≠ p.col := middle_ne_col hn p
    have he := positive_next s hn hM hp hc p.row c p.col hci.symm hcj p.ne
      [a] u (by simp) (by simp only [List.length_cons] at hus; omega)
      (by simp only [List.length_cons, List.length_nil] at *; omega)
    have he' : word s hn p (a :: u) =
      bracket (word s hn ⟨p.row, c, hci.symm⟩ [a]) (word s hn ⟨c, p.col, hcj⟩ u) := he.symm
    rw [he']
    apply bracket_square (hs _ _ (by simp; omega))
    rw [← he']
    exact commute_next s hn hM hp hc p ⟨p.row, c, hci.symm⟩ _ _ hu
      (by simp only [List.length_cons, List.length_nil]; omega) p.ne.symm hci.symm

 theorem product_next (s : Seed n α G) (hn : 5 ≤ n) {M : ℕ} (hM : 2 ≤ M)
    (hp : ProductUpTo (word s hn) M) (hc : CommuteUpTo (word s hn) M) :
    ProductUpTo (word s hn) (M + 1) := by
  intro i j k hij hjk hik u v huv
  by_cases hsmall : u.length + v.length ≤ M
  · exact hp i j k hij hjk hik u v hsmall
  have hc' := commute_next s hn hM hp hc
  cases u with
  | nil =>
    cases v with
    | nil => simp at hsmall
    | cons a v =>
      obtain ⟨c, hci, hcj, hck, _⟩ := exists_fresh hn i j k k
      have hv : 0 < v.length := by simp only [List.length_nil, List.length_cons] at hsmall; omega
      have hvl : v.length ≤ M := by simp only [List.length_nil, List.length_cons] at huv; omega
      have hpos := positive_next s hn hM hp hc j c k hcj.symm hck hjk [a] v
        (by simp) hv (by simp only [List.length_cons, List.length_nil] at *; omega)
      have hassoc := reassociate_of (word s hn) hc' i j c k hij hci.symm hik
        hcj.symm hjk hck [] [a] v
        (by simp only [List.length_nil, List.length_cons]; omega)
        (by simp only [List.length_nil, List.length_cons] at *; omega)
        (hp i j c hij hcj.symm hci.symm [] [a] (by simp; omega)) hpos
      calc
        bracket (word s hn ⟨i, j, hij⟩ []) (word s hn ⟨j, k, hjk⟩ (a :: v)) =
            bracket (word s hn ⟨i, c, hci.symm⟩ [a]) (word s hn ⟨c, k, hck⟩ v) := by
              simpa using hassoc.symm
        _ = word s hn ⟨i, k, hik⟩ ([] ++ a :: v) :=
          positive_next s hn hM hp hc i c k hci.symm hck hik [a] v (by simp) hv
            (by simp only [List.length_nil, List.length_cons] at *; omega)
  | cons a u =>
    cases v with
    | nil =>
      obtain ⟨c, hci, hcj, hck, _⟩ := exists_fresh hn i j k k
      have hu : 0 < u.length := by simp only [List.length_nil, List.length_cons] at hsmall; omega
      have hul : u.length ≤ M := by simp only [List.length_nil, List.length_cons] at huv; omega
      have hpos := positive_next s hn hM hp hc i c j hci.symm hcj hij [a] u
        (by simp) hu (by simp only [List.length_cons, List.length_nil] at *; omega)
      have hassoc := reassociate_of (word s hn) hc' i c j k hci.symm hij hik
        hcj hck hjk [a] u []
        (by simp only [List.length_nil, List.length_cons] at *; omega)
        (by simp only [List.length_nil]; omega)
        hpos (hp c j k hcj hjk hck u [] (by simpa using hul))
      calc
        bracket (word s hn ⟨i, j, hij⟩ (a :: u)) (word s hn ⟨j, k, hjk⟩ []) =
            bracket (word s hn ⟨i, c, hci.symm⟩ [a]) (word s hn ⟨c, k, hck⟩ u) := by
              simpa using hassoc
        _ = word s hn ⟨i, k, hik⟩ ((a :: u) ++ []) := by
          simpa using positive_next s hn hM hp hc i c k hci.symm hck hik [a] u
            (by simp) hu (by simp only [List.length_cons, List.length_nil] at *; omega)
    | cons b v =>
      exact positive_next s hn hM hp hc i j k hij hjk hik (a :: u) (b :: v)
        (by simp) (by simp) huv

 theorem good (s : Seed n α G) (hn : 5 ≤ n) (N : ℕ) : Good (word s hn) N := by
  induction N with
  | zero => exact base_good s hn 0 (by omega)
  | succ M ih =>
    by_cases hM : M < 2
    · exact base_good s hn (M + 1) (by omega)
    · exact ⟨product_next s hn (by omega) ih.1 ih.2.1,
        commute_next s hn (by omega) ih.1 ih.2.1,
        squares_next s hn (by omega) ih.1 ih.2.1 ih.2.2⟩

 theorem product (s : Seed n α G) (hn : 5 ≤ n)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (u v : List α) :
    bracket (word s hn ⟨i, j, hij⟩ u) (word s hn ⟨j, k, hjk⟩ v) =
      word s hn ⟨i, k, hik⟩ (u ++ v) :=
  (good s hn (u.length + v.length)).1 i j k hij hjk hik u v le_rfl

 theorem commute (s : Seed n α G) (hn : 5 ≤ n)
    (p q : Root n) (u v : List α) (hpq : p.col ≠ q.row) (hqp : p.row ≠ q.col) :
    Commute (word s hn p u) (word s hn q v) :=
  (good s hn (max u.length v.length)).2.1 p q u v (le_max_left _ _) (le_max_right _ _) hpq hqp

 theorem square (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) (u : List α) :
    word s hn p u ^ 2 = 1 := (good s hn u.length).2.2 p u le_rfl

abbrev Polynomial (α : Type u) := MonoidAlgebra (ZMod 2) (FreeMonoid α)

open scoped IsMulCommutative

noncomputable def rootSubgroup (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) : Subgroup G :=
  Subgroup.closure (Set.range (word s hn p))

instance rootSubgroup_comm (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) :
    IsMulCommutative (rootSubgroup s hn p) := by
  apply Subgroup.isMulCommutative_closure
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
  exact commute s hn p p u v p.ne.symm p.ne

noncomputable def rootWord (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) (w : List α) :
    rootSubgroup s hn p := ⟨word s hn p w, Subgroup.subset_closure ⟨w, rfl⟩⟩

noncomputable def coefficient (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) (w : List α) :
    ZMod 2 →+ Additive (rootSubgroup s hn p) where
  toFun a := Additive.ofMul (if a = 0 then 1 else rootWord s hn p w)
  map_zero' := by simp
  map_add' := by
    intro a b
    have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl
    all_goals apply Additive.toMul.injective; apply Subtype.ext
    all_goals simp only [toMul_ofMul, toMul_add]
    all_goals try rw [show (1 : ZMod 2) + 1 = 0 by decide]
    all_goals simp [rootWord]
    simpa only [pow_two] using (square s hn p w).symm

noncomputable def poly (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) (f : Polynomial α) : G :=
  ((Finsupp.liftAddHom (fun w : FreeMonoid α => coefficient s hn p w.toList) f.coeff).toMul : G)

@[simp] theorem poly_zero (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) :
    poly s hn p 0 = 1 := by simp [poly]

 theorem poly_add (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) (f g : Polynomial α) :
    poly s hn p (f + g) = poly s hn p f * poly s hn p g := by
  simp [poly]

@[simp] theorem poly_single (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) (w : FreeMonoid α) :
    poly s hn p (MonoidAlgebra.single w 1) = word s hn p w.toList := by
  simp [poly, coefficient, rootWord]

 theorem closure_commute {S T : Set G}
    (h : ∀ x ∈ S, ∀ y ∈ T, Commute x y) {x y : G}
    (hx : x ∈ Subgroup.closure S) (hy : y ∈ Subgroup.closure T) : Commute x y := by
  have hle : Subgroup.closure S ≤ Subgroup.centralizer T :=
    (Subgroup.closure_le _).mpr (fun a ha =>
      Subgroup.mem_centralizer_iff.mpr (fun b hb => (h a ha b hb).eq.symm))
  have hxc : x ∈ Subgroup.centralizer (Subgroup.closure T : Set G) := by
    rw [Subgroup.centralizer_closure]
    exact hle hx
  exact (Subgroup.mem_centralizer_iff.mp hxc y hy).symm

 theorem poly_mem (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) (f : Polynomial α) :
    poly s hn p f ∈ rootSubgroup s hn p :=
  (Finsupp.liftAddHom (fun w : FreeMonoid α => coefficient s hn p w.toList) f.coeff).toMul.property

 theorem poly_commute (s : Seed n α G) (hn : 5 ≤ n)
    (p q : Root n) (f g : Polynomial α) (hpq : p.col ≠ q.row) (hqp : p.row ≠ q.col) :
    Commute (poly s hn p f) (poly s hn q g) := by
  apply closure_commute (S := Set.range (word s hn p)) (T := Set.range (word s hn q))
    ?_ (poly_mem s hn p f) (poly_mem s hn q g)
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
  exact commute s hn p q u v hpq hqp

 theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 :=
  (of_decide_eq_true (by rfl) : ∀ a : ZMod 2, a = 0 ∨ a = 1) a

 theorem poly_product (s : Seed n α G) (hn : 5 ≤ n)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (f g : Polynomial α) :
    bracket (poly s hn ⟨i, j, hij⟩ f) (poly s hn ⟨j, k, hjk⟩ g) =
      poly s hn ⟨i, k, hik⟩ (f * g) := by
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp [bracket]
  | add f₁ f₂ h₁ h₂ =>
    rw [poly_add, CommutatorCalculus.mul_left, h₂, h₁,
      CommutatorCalculus.conj_of_commute (poly_commute s hn _ _ f₁ (f₂ * g) hij.symm hik),
      add_mul, poly_add]
    exact (poly_commute s hn _ _ (f₂ * g) (f₁ * g) hik.symm hik).eq
  | single u a =>
    rcases zmod_two_cases a with rfl | rfl
    · simp [bracket]
    · induction g using MonoidAlgebra.induction_linear with
      | zero => simp [bracket]
      | add g₁ g₂ h₁ h₂ =>
        rw [poly_add, CommutatorCalculus.mul_right, h₁, h₂, mul_add, poly_add]
        have hconj := CommutatorCalculus.conj_of_commute
          (poly_commute s hn ⟨j, k, hjk⟩ ⟨i, k, hik⟩ g₁ (MonoidAlgebra.single u 1 * g₂)
            hik.symm hjk)
        simpa only [mul_assoc] using congrArg
          (fun x => poly s hn ⟨i, k, hik⟩ (MonoidAlgebra.single u 1 * g₁) * x) hconj
      | single v b =>
        rcases zmod_two_cases b with rfl | rfl
        · simp [bracket]
        · rw [MonoidAlgebra.single_mul_single, one_mul, poly_single, poly_single, poly_single]
          exact product s hn i j k hij hjk hik u.toList v.toList

noncomputable def lift (s : Seed n α G) (hn : 5 ≤ n) : Steinberg n (Polynomial α) →* G :=
  Steinberg.lift (poly s hn) (poly_add s hn)
    (fun p q h₁ h₂ f g => poly_commute s hn p q f g h₁ h₂) (poly_product s hn)

end MonomialCompletion

namespace FiniteSteinbergPresentation

open MonomialCompletion

variable {n : ℕ} {α : Type u}

abbrev ShortWord (α : Type u) := {w : List α // w.length ≤ 2}
abbrev Gen (n : ℕ) (α : Type u) := Root n × ShortWord α

instance root_finite (n : ℕ) : Finite (Root n) :=
  Finite.of_injective (fun p : Root n => (p.row, p.col)) (by
    rintro ⟨i, j, hij⟩ ⟨k, l, hkl⟩ he
    have hi : i = k := congrArg Prod.fst he
    have hj : j = l := congrArg Prod.snd he
    subst k; subst l
    rfl)

def shortWordMap : Unit ⊕ (α ⊕ α × α) → ShortWord α
  | .inl _ => ⟨[], by simp⟩
  | .inr (.inl a) => ⟨[a], by simp⟩
  | .inr (.inr (a, b)) => ⟨[a, b], by simp⟩

instance shortWord_finite [Finite α] : Finite (ShortWord α) :=
  Finite.of_surjective shortWordMap (by
    rintro ⟨w, hw⟩
    match w with
    | [] => exact ⟨.inl (), rfl⟩
    | [a] => exact ⟨.inr (.inl a), rfl⟩
    | [a, b] => exact ⟨.inr (.inr (a, b)), rfl⟩
    | _ :: _ :: _ :: _ => simp only [List.length_cons] at hw; omega)

def gen (p : Root n) (w : ShortWord α) : FreeGroup (Gen n α) := FreeGroup.of (p, w)

inductive Rel (n : ℕ) (α : Type u) : FreeGroup (Gen n α) → Prop
  | square (p : Root n) (w : ShortWord α) : Rel n α (gen p w ^ 2)
  | commute (p q : Root n) (h₁ : p.col ≠ q.row) (h₂ : p.row ≠ q.col)
      (u v : ShortWord α) : Rel n α (bracket (gen p u) (gen q v))
  | product (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
      (u v : ShortWord α) (h : u.val.length + v.val.length ≤ 2) :
      Rel n α (bracket (gen ⟨i, j, hij⟩ u) (gen ⟨j, k, hjk⟩ v) *
        (gen ⟨i, k, hik⟩ ⟨u.val ++ v.val, by simpa only [List.length_append] using h⟩)⁻¹)

end FiniteSteinbergPresentation
end SourceBurnside
end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_KernelRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.Kernel
open scoped BigOperators
noncomputable section
open Classical

variable {n : ℕ} {R : Type u} [Ring R]

def rootHom (p : Root n) : Multiplicative R →* Steinberg n R where
  toFun a := Steinberg.x p a.toAdd
  map_one' := Steinberg.x_zero p
  map_mul' a b := Steinberg.x_add p a.toAdd b.toAdd

abbrev RectIndex (H L : Finset (Fin n)) := {i // i ∈ H} × {j // j ∈ L}

variable (H L : Finset (Fin n)) (hHL : Disjoint H L)

def rectPosition (p : RectIndex H L) : Root n :=
  ⟨p.1.val, p.2.val, fun h => Finset.disjoint_left.mp hHL p.1.property (h ▸ p.2.property)⟩

lemma rect_commute (p q : RectIndex H L) (a b : R) :
    Commute (Steinberg.x (rectPosition H L hHL p) a)
      (Steinberg.x (rectPosition H L hHL q) b) := by
  apply Steinberg.x_commute
  · intro h
    change p.2.val = q.1.val at h
    exact Finset.disjoint_left.mp hHL q.1.property (h ▸ p.2.property)
  · intro h
    change p.1.val = q.2.val at h
    exact Finset.disjoint_left.mp hHL p.1.property (h ▸ q.2.property)

def rectRoot : (RectIndex H L → Multiplicative R) →* Steinberg n R :=
  MonoidHom.noncommPiCoprod (fun p => rootHom (rectPosition H L hHL p))
    (fun p q _ a b => rect_commute H L hHL p q a.toAdd b.toAdd)

@[simp] lemma rectRoot_single (p : RectIndex H L) (a : R) :
    rectRoot H L hHL (Pi.mulSingle p (Multiplicative.ofAdd a)) =
      Steinberg.x (rectPosition H L hHL p) a :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

def rectMatrix (A : RectIndex H L → Multiplicative R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if hi : i ∈ H then if hj : j ∈ L then (A (⟨i, hi⟩, ⟨j, hj⟩)).toAdd
    else 0 else 0

@[simp] lemma rectMatrix_entry (A : RectIndex H L → Multiplicative R)
    (p : RectIndex H L) : rectMatrix H L A p.1.val p.2.val = (A p).toAdd := by
  simp [rectMatrix, p.1.property, p.2.property]

@[simp] lemma rectMatrix_one : rectMatrix H L (1 : RectIndex H L → Multiplicative R) = 0 := by
  ext i j
  simp [rectMatrix]

@[simp] lemma rectMatrix_mul (A B : RectIndex H L → Multiplicative R) :
    rectMatrix H L (A * B) = rectMatrix H L A + rectMatrix H L B := by
  ext i j
  simp only [rectMatrix, Matrix.add_apply]
  split_ifs <;> simp_all

include hHL in
lemma rectMatrix_product (A B : RectIndex H L → Multiplicative R) :
    rectMatrix H L A * rectMatrix H L B = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k ∈ H
  · have hk' : k ∉ L := fun hl => Finset.disjoint_left.mp hHL hk hl
    simp [rectMatrix, hk']
  · simp [rectMatrix, hk]

def rectUnits : (RectIndex H L → Multiplicative R) →*
    (Matrix (Fin n) (Fin n) R)ˣ where
  toFun A :=
    { val := 1 + rectMatrix H L A
      inv := 1 - rectMatrix H L A
      val_inv := by
        simp [add_mul, mul_sub, rectMatrix_product H L hHL]
      inv_val := by
        simp [sub_mul, mul_add, rectMatrix_product H L hHL] }
  map_one' := by apply Units.ext; simp
  map_mul' A B := by
    apply Units.ext
    simp only [Units.val_mul, rectMatrix_mul]
    simp [add_mul, mul_add, rectMatrix_product H L hHL, add_assoc]

@[simp] lemma coe_rectUnits (A : RectIndex H L → Multiplicative R) :
    (rectUnits H L hHL A).val = 1 + rectMatrix H L A := rfl

end
end SourceBurnside.Kernel

namespace SourceBurnside
namespace Root

def map {n m : ℕ} (f : Fin n → Fin m) (hf : Function.Injective f) (p : Root n) : Root m :=
  ⟨f p.row, f p.col, fun h => p.ne (hf h)⟩
end Root

namespace Steinberg
variable {n m : ℕ} {R : Type u} [Ring R]

def coordinateMap (f : Fin n → Fin m) (hf : Function.Injective f) :
    Steinberg n R →* Steinberg m R :=
  lift (fun p a => x (p.map f hf) a)
    (fun _ _ _ => x_add _ _ _)
    (fun _p _q h₁ h₂ a b => x_commute _ _ (fun h => h₁ (hf h)) (fun h => h₂ (hf h)) a b)
    (fun i j k hij hjk hik a b =>
      x_mul (f i) (f j) (f k) (fun h => hij (hf h)) (fun h => hjk (hf h))
        (fun h => hik (hf h)) a b)

@[simp] theorem coordinateMap_x (f : Fin n → Fin m) (hf : Function.Injective f)
    (p : Root n) (a : R) : coordinateMap f hf (x p a) = x (p.map f hf) a :=
  lift_x _ _ _ _ _ _

end Steinberg
end SourceBurnside

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_BlockEmbeddings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
def blockIndex (i : Fin n) (s : Fin N) : Fin (n*N) := finProdFinEquiv (i,s)
lemma blockIndex_ne {i j : Fin n} (h : i≠j) (s t : Fin N) : blockIndex i s≠blockIndex j t := by
  intro he
  exact h (congrArg Prod.fst (finProdFinEquiv.injective he))
def blockPosition (p : Root n) (st : Fin N × Fin N) : Root (n*N) :=
  ⟨blockIndex p.row st.1,blockIndex p.col st.2,blockIndex_ne p.ne _ _⟩
lemma block_factors_commute (p : Root n) (st uv : Fin N×Fin N) (a b : R) :
    Commute (Steinberg.x (blockPosition p st) a) (Steinberg.x (blockPosition p uv) b) := by
  apply Steinberg.x_commute
  · exact blockIndex_ne p.ne.symm _ _
  · exact blockIndex_ne p.ne _ _
def blockHom (p : Root n) : (Fin N×Fin N → Multiplicative R) →* Steinberg (n*N) R :=
  MonoidHom.noncommPiCoprod (fun st=>rootHom (blockPosition p st))
    (fun st uv _ a b=>block_factors_commute p st uv a.toAdd b.toAdd)

def blockRoot (p : Root n) (A : Matrix (Fin N) (Fin N) R) : Steinberg (n*N) R :=
  blockHom p (fun st=>Multiplicative.ofAdd (A st.1 st.2))
lemma blockRoot_zero (p : Root n) : blockRoot p (0 : Matrix (Fin N) (Fin N) R)=1 :=
  map_one (blockHom p)
lemma blockRoot_add (p : Root n) (A B : Matrix (Fin N) (Fin N) R) :
    blockRoot p (A+B)=blockRoot p A*blockRoot p B :=
  map_mul (blockHom p) _ _
lemma blockRoot_single (p : Root n) (s t : Fin N) (a : R) :
    blockRoot p (Matrix.single s t a)=Steinberg.x (blockPosition p (s,t)) a := by
  have he : (fun st : Fin N×Fin N=>Multiplicative.ofAdd ((Matrix.single s t a) st.1 st.2))=
      Pi.mulSingle (s,t) (Multiplicative.ofAdd a) := by
    funext st
    rcases st with ⟨u,v⟩
    by_cases hs : s=u <;> by_cases ht : t=v <;>
      simp_all [Matrix.single,Prod.ext_iff,eq_comm]
  rw [blockRoot,he]
  exact MonoidHom.noncommPiCoprod_mulSingle _ _ _
lemma blockRoot_commute (p q : Root n) (h₁ : p.col≠q.row) (h₂ : p.row≠q.col)
    (A B : Matrix (Fin N) (Fin N) R) : Commute (blockRoot p A) (blockRoot q B) := by
  apply MonoidHom.commute_noncommPiCoprod
  intro st a
  apply Commute.symm
  apply MonoidHom.commute_noncommPiCoprod
  intro uv b
  apply Steinberg.x_commute
  · exact blockIndex_ne h₂.symm _ _
  · exact blockIndex_ne h₁.symm _ _

lemma blockRoot_mul (i j k : Fin n) (hij : i≠j) (hjk : j≠k) (hik : i≠k)
    (A B : Matrix (Fin N) (Fin N) R) :
    bracket (blockRoot ⟨i,j,hij⟩ A) (blockRoot ⟨j,k,hjk⟩ B)=blockRoot ⟨i,k,hik⟩ (A*B) := by
  induction A using Matrix.induction_on' with
  | h_zero => simp [blockRoot_zero,bracket]
  | h_add A A' hA hA' =>
    rw [blockRoot_add,CommutatorCalculus.mul_left,hA,hA',Matrix.add_mul]
    have hc := blockRoot_commute ⟨i,j,hij⟩ ⟨i,k,hik⟩ hij.symm hik A (A'*B)
    rw [CommutatorCalculus.conj_of_commute hc,←blockRoot_add,add_comm]
  | h_std_basis s t a =>
    induction B using Matrix.induction_on' with
    | h_zero => simp [blockRoot_zero,bracket]
    | h_add B B' hB hB' =>
      rw [blockRoot_add,CommutatorCalculus.mul_right,hB,hB',Matrix.mul_add]
      have hc := blockRoot_commute ⟨j,k,hjk⟩ ⟨i,k,hik⟩ hik.symm hjk
        B (Matrix.single s t a*B')
      calc
        _ = blockRoot ⟨i,k,hik⟩ (Matrix.single s t a*B) *
          (blockRoot ⟨j,k,hjk⟩ B*blockRoot ⟨i,k,hik⟩ (Matrix.single s t a*B')*(blockRoot ⟨j,k,hjk⟩ B)⁻¹) := by simp only [mul_assoc]
        _ = _ := by rw [CommutatorCalculus.conj_of_commute hc,←blockRoot_add]
    | h_std_basis u v b =>
      rw [blockRoot_single,blockRoot_single]
      by_cases htu : t=u
      · subst u
        rw [Matrix.single_mul_single_same,blockRoot_single]
        exact Steinberg.x_mul _ _ _ (blockIndex_ne hij s t) (blockIndex_ne hjk t v) (blockIndex_ne hik s v) a b
      · rw [Matrix.single_mul_single_of_ne _ _ _ _ htu,blockRoot_zero]
        apply (bracket_eq_one_iff _ _).mpr
        apply Steinberg.x_commute
        · intro he
          exact htu (congrArg Prod.snd (finProdFinEquiv.injective he))
        · exact blockIndex_ne hik s v

def blockMap : Steinberg n (Matrix (Fin N) (Fin N) R) →* Steinberg (n*N) R :=
  Steinberg.lift blockRoot (fun p A B=>blockRoot_add p A B)
    (fun p q h₁ h₂ A B=>blockRoot_commute p q h₁ h₂ A B)
    (fun i j k hij hjk hik A B=>blockRoot_mul i j k hij hjk hik A B)
@[simp] lemma blockMap_x (p : Root n) (A : Matrix (Fin N) (Fin N) R) :
    blockMap (Steinberg.x p A)=blockRoot p A := Steinberg.lift_x _ _ _ _ p A
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
def copyMap (s : Fin N) : Steinberg n R →* Steinberg (n*N) R :=
  Steinberg.coordinateMap (fun i=>blockIndex i s)
    (fun _row _col he=>congrArg Prod.fst (finProdFinEquiv.injective he))
@[simp] lemma copyMap_x (s : Fin N) (p : Root n) (a : R) :
    copyMap s (Steinberg.x p a)=Steinberg.x (blockPosition p (s,s)) a := rfl
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]
def numericMatrix (T : Matrix (Fin N) (Fin N) (ZMod 2)) : Matrix (Fin N) (Fin N) R :=
  T.map (algebraMap (ZMod 2) R)
lemma numeric_scalar_commute (T : Matrix (Fin N) (Fin N) (ZMod 2)) (a : R) :
    Commute (Matrix.scalar (Fin N) a) (numericMatrix T) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.scalar_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  exact (Algebra.commutes (T i j) a).symm

def matrixEval (T : Matrix (Fin N) (Fin N) (ZMod 2)) : Polynomial R →+* Matrix (Fin N) (Fin N) R :=
  Polynomial.eval₂RingHom' (Matrix.scalar (Fin N)) (numericMatrix T) (numeric_scalar_commute T)
def matrixEvalRingHom (T : Matrix (Fin N) (Fin N) (ZMod 2)) :
    @RingHom (Polynomial R) (Matrix (Fin N) (Fin N) R)
      (inferInstance : Ring (Polynomial R)).toNonAssocSemiring
      (inferInstance : Ring (Matrix (Fin N) (Fin N) R)).toNonAssocSemiring where
  toFun := matrixEval T
  map_zero' := map_zero _
  map_one' := map_one _
  map_add' := map_add _
  map_mul' := map_mul _
def matrixSteinbergEval (T : Matrix (Fin N) (Fin N) (ZMod 2)) :
    Steinberg n (Polynomial R) →* Steinberg (n*N) R := blockMap.comp (Steinberg.map (matrixEvalRingHom T))
end
end SourceBurnside.Kernel

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_CoefficientQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside
namespace FiniteSteinbergPresentation
open MonomialCompletion
variable {n : ℕ} {α : Type u}
abbrev Group (n : ℕ) (α : Type u) := PresentedGroup {r | Rel n α r}

noncomputable def monomial (w : List α) : Polynomial α := MonoidAlgebra.single (FreeMonoid.ofList w) 1

@[simp] theorem monomial_append (u v : List α) : monomial (u ++ v) = monomial u * monomial v := by
  rw [monomial, monomial, monomial, MonoidAlgebra.single_mul_single, one_mul]
  rfl

 theorem monomial_add_self (u : List α) : monomial u + monomial u = 0 := by
  rw [monomial, ← MonoidAlgebra.single_add, show (1 : ZMod 2) + 1 = 0 by decide,
    MonoidAlgebra.single_zero]

end FiniteSteinbergPresentation

namespace SteinbergQuotient

variable {n : ℕ} {R : Type u} [Ring R]

variable (S : Set R)

abbrev coeffIdeal := TwoSidedIdeal.span S

abbrev Coeff := (coeffIdeal S).ringCon.Quotient

end SteinbergQuotient

end SourceBurnside

namespace SourceBurnside.WordAlgebra.Table
noncomputable section
open Classical
variable {α K : Type*} [CommRing K]
def augWords : FreeMonoid α →* K := FreeMonoid.lift (fun _=>0)
lemma augWords_spec (w : FreeMonoid α) : augWords (K:=K) w=if w.length=0 then 1 else 0 := by
  rw [augWords,FreeMonoid.lift_apply]
  change (List.map (fun _ : α=>(0:K)) w.toList).prod=(if w.toList.length=0 then 1 else 0)
  cases he : w.toList with
  | nil => simp
  | cons a w => simp

end
end SourceBurnside.WordAlgebra.Table

namespace SourceBurnside.ConcreteSource
noncomputable section

def dilation : ℕ := 10*(10000+1)*(10+1)+1
lemma dilation_two : 2≤dilation := by decide
end
end SourceBurnside.ConcreteSource

end

end OAI
end


