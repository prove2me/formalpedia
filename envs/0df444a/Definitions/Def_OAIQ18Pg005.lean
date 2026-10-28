-- Prove2me | Definitions.Def_OAIQ18Pg005
-- name    : OAIQ18Pg005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T15:58:33.19002+00:00
-- url     : https://prove2.me/theorems/fdcc843e-95bb-4881-958c-24a966433cb8
-- title:
--   Definitions bundle OAIQ18Pg005 of the split of OpenAI, An infinite finitely presented periodic group
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SourceBurnside.thm_main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented periodic group*, OpenAI Math Release, September 23, 2026, result family 247, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 541 declarations of OpenAI's Lean: 202 definitions, 10 inductive types or structures, 45 instances and 284 theorems. The definitions and types are `OAI.SourceBurnside.CellFormula.unaryMove`, `OAI.SourceBurnside.ClauseFormula.Expr`, `OAI.SourceBurnside.ClauseFormula.Expr.Exponents`, `OAI.SourceBurnside.ClauseFormula.ReadingExpr`, `OAI.SourceBurnside.ClauseFormula.ReadingExpr.Exponents`, `OAI.SourceBurnside.ClauseFormula.Represents`, `OAI.SourceBurnside.ClauseFormula.RepresentsReading`, `OAI.SourceBurnside.ClauseFormula.addressReading`, `OAI.SourceBurnside.ClauseFormula.choose`, `OAI.SourceBurnside.ClauseFormula.circuitClause`, `OAI.SourceBurnside.ClauseFormula.delta`, `OAI.SourceBurnside.ClauseFormula.equalReading`, `OAI.SourceBurnside.ClauseFormula.fixedReading`, `OAI.SourceBurnside.ClauseFormula.initialData`, `OAI.SourceBurnside.ClauseFormula.lookup`, `OAI.SourceBurnside.ClauseFormula.make`, `OAI.SourceBurnside.ClauseFormula.matchReg`, `OAI.SourceBurnside.ClauseFormula.readValue`, `OAI.SourceBurnside.ClauseFormula.regs`, `OAI.SourceBurnside.ClauseFormula.truth`, `OAI.SourceBurnside.ClauseFormula.truthTable`, `OAI.SourceBurnside.ClauseFormula.unit`, `OAI.SourceBurnside.ClauseFormula.wire`, `OAI.SourceBurnside.CompactInit.packet`, `OAI.SourceBurnside.CompactInit.program`, `OAI.SourceBurnside.CompactInit.store`, `OAI.SourceBurnside.CompactProgram.State`, `OAI.SourceBurnside.CompactProgram.boot`, `OAI.SourceBurnside.CompactProgram.enter`, `OAI.SourceBurnside.CompactProgram.initial`, `OAI.SourceBurnside.CompactProgram.initialConfig`, `OAI.SourceBurnside.CompactProgram.inputStore`, `OAI.SourceBurnside.CompactProgram.machine`, `OAI.SourceBurnside.CompactProgram.virtual`, `OAI.SourceBurnside.DropPadding.step`, `OAI.SourceBurnside.FiniteTable.Cell.color`, `OAI.SourceBurnside.FiniteTable.Codec.ReservedZero`, `OAI.SourceBurnside.FiniteTable.Codec.UsedAgree`, `OAI.SourceBurnside.FiniteTable.Codec.binaryZero`, `OAI.SourceBurnside.FiniteTable.Codec.decodeWord` and 172 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory/PeriodicGroups, in whole or in part: `PeriodicGroups_Formulas_BooleanCircuits`, `PeriodicGroups_Formulas_ClauseEncoding`, `PeriodicGroups_Formulas_LocalPredicates`, `PeriodicGroups_Formulas_PredicateCompilation`, `PeriodicGroups_Machines_Compilation`, `PeriodicGroups_Machines_InputEncoding`, `PeriodicGroups_Machines_ProgramAssembly`, `PeriodicGroups_Machines_ProgramFixedPoint`, `PeriodicGroups_Machines_StackCompression`, `PeriodicGroups_Machines_TimedExecution`, `PeriodicGroups_Machines_UniversalInput`, `PeriodicGroups_Rules_BoundaryCell`, `PeriodicGroups_Rules_GeometricRelations`, `PeriodicGroups_Rules_HeadTour`, `PeriodicGroups_Rules_PrefixRewriting`, `PeriodicGroups_Rules_Recognizer`, `PeriodicGroups_Rules_TableEncoding`, `PeriodicGroups_Rules_TemplateHierarchy`, `PeriodicGroups_Rules_WordRewriting`.
--
--   **Imports.** It imports the bundles `OAIQ18Pg000` and `OAIQ18Pg001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ18Pg009` and `OAIQ18Pg010`.
-- source:
--   OpenAI, An infinite finitely presented periodic group, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 247; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/PeriodicGroups at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ18Pg000
import Definitions.Def_OAIQ18Pg001

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

variable (src dst : K) (hne : src≠dst)
include hne

lemma parse_packet (p : Packet K) (i : Fin (width K)) (v : Fin (width K) → Bool)
    (hv : ∀ j, j.val < i.val → v j=packetBits p j) (u todo : List Bool)
    (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    exec (machine src dst) (config src dst (.collect i v) u ((packetWord p).drop i.val++todo) f b pc)
      (width K-i.val)=config src dst (packetState p) u todo f b pc := by
  generalize hn : width K-i.val=n
  induction n using Nat.strong_induction_on generalizing i v with
  | h n ih =>
    have hilt : i.val<(packetWord p).length := by
      simpa only [packetWord,List.length_ofFn] using i.isLt
    rw [List.drop_eq_getElem_cons hilt,List.cons_append]
    have hiword : (packetWord p)[i.val]=packetBits p i := by
      simp only [packetWord,List.getElem_ofFn]
    rw [hiword]
    by_cases hi : i.val+1<width K
    · rw [show n=1+(width K-(i.val+1)) by omega,exec_from]
      rw [exec_one]
      rw [collect_bit src dst hne]
      simp only [collectNext,hi,dite_eq_left]
      exact ih (width K-(i.val+1)) (by omega) ⟨i.val+1,hi⟩
        (Function.update v i (packetBits p i)) (collect_prefix i v p hv) rfl
    · have hn1 : n=1 := by have := i.isLt;omega
      rw [hn1]
      rw [exec_one]
      rw [collect_bit src dst hne,collect_complete i v p hv hi]
      have he : (packetWord p).drop (i.val+1)=[] := by
        apply List.drop_eq_nil_of_le
        simp only [packetWord,List.length_ofFn]
        omega
      rw [he,List.nil_append]

end
end SourceBurnside.UniversalInput

namespace SourceBurnside.Structured
noncomputable section
open StackMachine UniversalStack

namespace Program
variable {K : Type*}

def Loc : Program K → Type
  | .skip | .push _ _ => Unit
  | .pop _ b => Unit ⊕ ((a : Option Bool) × Loc (b a))
  | .seq p q => Loc p ⊕ Loc q
  | .loop _ b => Unit ⊕ ((a : Bool) × Loc (b a))

instance locFintype (P : Program K) : Fintype P.Loc := by
  induction P with
  | skip => exact inferInstanceAs (Fintype Unit)
  | push k b => exact inferInstanceAs (Fintype Unit)
  | pop k b ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Unit ⊕ ((a : Option Bool) × (b a).Loc)))
  | seq p q ihp ihq =>
    letI := ihp;letI := ihq
    exact inferInstanceAs (Fintype (p.Loc ⊕ q.Loc))
  | loop k b ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Unit ⊕ ((a : Bool) × (b a).Loc)))

def start : (P : Program K) → P.Loc
  | .skip | .push _ _ => ()
  | .pop _ _ | .loop _ _ => .inl ()
  | .seq p _ => .inl p.start

def operation : (P : Program K) → P.Loc → StackMachine.Instr (Option K) Bool (Option P.Loc)
  | .skip,_ => .pop none (fun _ => none)
  | .push k b,_ => .push (some k) b none
  | .pop k b,.inl _ => .pop (some k) (fun a => some (.inr ⟨a,(b a).start⟩))
  | .pop _ b,.inr ⟨a,s⟩ => mapInstr (Option.map (fun t => .inr ⟨a,t⟩)) ((b a).operation s)
  | .seq p q,.inl s => mapInstr (done (fun t => some (.inl t)) (some (.inr q.start))) (p.operation s)
  | .seq _ q,.inr s => mapInstr (Option.map Sum.inr) (q.operation s)
  | .loop k b,.inl _ => .pop (some k) (fun a => match a with
      | none => none | some a => some (.inr ⟨a,(b a).start⟩))
  | .loop _ b,.inr ⟨a,s⟩ => mapInstr (done (fun t => some (.inr ⟨a,t⟩)) (some (.inl ())))
      ((b a).operation s)

end Program
open Program
variable {K : Type*} [DecidableEq K]

def extendStore (r : Store K) : Option K → List Bool
  | none => [] | some k => r k

lemma extendStore_update (r : Store K) (k : K) (v : List Bool) :
    extendStore (Function.update r k v)=Function.update (extendStore r) (some k) v := by
  funext j
  cases j with
  | none => simp [extendStore]
  | some j => by_cases h : j=k <;> simp [extendStore,h]

theorem compile_run {P : Program K} {r s : Store K} {n : ℕ} (h : Run P r n s) :
    ∀ {Q : Type*} (M : Q → StackMachine.Instr (Option K) Bool Q) (f : Option P.Loc → Q),
    (∀ l, M (f (some l))=mapInstr f (P.operation l)) →
    exec M ⟨f (some P.start),extendStore r⟩ n=⟨f none,extendStore s⟩ := by
  induction h with
  | skip r =>
    intro Q M f hf
    have he := hf ()
    simp only [operation,mapInstr] at he
    simp [exec,next,he,start,extendStore]
  | push r k b =>
    intro Q M f hf
    have he := hf ()
    simp only [operation,mapInstr] at he
    simp only [exec,next,start,he,extendStore_update]
    rfl
  | pop r k b n s h ih =>
    intro Q M f hf
    rw [exec_from]
    have he := hf (.inl ())
    simp only [operation,mapInstr] at he
    change exec M (next M ⟨f (some (.inl ())),extendStore r⟩) n=_
    simp only [next,he,extendStore]
    let g : Option (b (r k).getLast?).Loc → Q := fun x =>
      f (x.map (fun t => .inr ⟨(r k).getLast?,t⟩))
    have hg : ∀l,M (g (some l))=mapInstr g ((b (r k).getLast?).operation l) := by
      intro l
      change M (f (some (.inr ⟨(r k).getLast?,l⟩)))=_
      have hh := hf (.inr ⟨(r k).getLast?,l⟩)
      change M (f (some (.inr ⟨(r k).getLast?,l⟩)))=
        mapInstr f (mapInstr (Option.map (fun t => .inr ⟨(r k).getLast?,t⟩))
          ((b (r k).getLast?).operation l)) at hh
      exact hh.trans (mapInstr_comp _ _ _)
    have hh := ih M g hg
    dsimp only [g,Option.map] at hh
    rw [extendStore_update] at hh
    exact hh
  | seq p q r s t n m hp hq ihp ihq =>
    intro Q M f hf
    let g : Option p.Loc → Q := fun x =>
      f (done (fun l => some (.inl l)) (some (.inr q.start)) x)
    let j : Option q.Loc → Q := fun x => f (x.map Sum.inr)
    have hg : ∀l,M (g (some l))=mapInstr g (p.operation l) := by
      intro l
      change M (f (some (.inl l)))=_
      have hh := hf (.inl l)
      exact hh.trans (mapInstr_comp _ _ _)
    have hj : ∀l,M (j (some l))=mapInstr j (q.operation l) := by
      intro l
      change M (f (some (.inr l)))=_
      have hh := hf (.inr l)
      exact hh.trans (mapInstr_comp _ _ _)
    rw [exec_from]
    change exec M (exec M ⟨g (some p.start),extendStore r⟩ n) m=_
    rw [ihp M g hg]
    exact ihq M j hj
  | loop_nil r k b hr =>
    intro Q M f hf
    have he := hf (.inl ())
    simp only [operation,mapInstr] at he
    simp only [exec,next,start,he,extendStore,hr,List.getLast?_nil,List.dropLast_nil]
    apply config_ext
    · rfl
    · funext j
      cases j with
      | none => simp [extendStore]
      | some j => by_cases hj : j=k <;> simp [extendStore,hj,hr]
  | loop_cons r k b v a s t n m hr hb ht ihb iht =>
    intro Q M f hf
    let g : Option (b a).Loc → Q := fun x =>
      f (done (fun l => some (.inr ⟨a,l⟩)) (some (.inl ())) x)
    have hg : ∀l,M (g (some l))=mapInstr g ((b a).operation l) := by
      intro l
      change M (f (some (.inr ⟨a,l⟩)))=_
      have hh := hf (.inr ⟨a,l⟩)
      exact hh.trans (mapInstr_comp _ _ _)
    rw [exec_from]
    have he := hf (.inl ())
    simp only [operation,mapInstr] at he
    change exec M (next M ⟨f (some (.inl ())),extendStore r⟩) (n+m)=_
    simp only [next,he,extendStore,hr,List.getLast?_concat,List.dropLast_concat]
    rw [exec_from]
    change exec M (exec M ⟨g (some (b a).start),
      Function.update (extendStore r) (some k) v⟩ n) m=_
    rw [←extendStore_update,ihb M g hg]
    exact iht M f hf

end
end SourceBurnside.Structured

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_HeadTour
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.FiniteTable
open LocalSyntax
open LocalSyntax.Skeleton

variable {q : ℕ} [NeZero q]

inductive Unary (S : Schedule q) : Cell q → Cell q → Prop
  | create (c : Cell q) (s : Bool) (h : c.skeleton.first) :
      Unary S (c.idle s) (c.boundary s)
  | finish_acquisition (c : Cell q) (s : Bool) (h : c.skeleton.last) :
      Unary S (c.boundary s) (c.full s 0 .acquisition 0)
  | read_enter (c : Cell q) (s : Bool) (j : Fin q) (r : Reg) (h : c.skeleton.last) :
      Unary S (c.full s j .acquisition r) (c.full s j .readLeft r)
  | read_turn (c : Cell q) (s : Bool) (j : Fin q) (r : Reg) (h : c.skeleton.first) :
      Unary S (c.full s j .readLeft r) (c.full s j .readRight r)
  | read_exit (c : Cell q) (s : Bool) (j : Fin q) (r : Reg) (h : c.skeleton.last) :
      Unary S (c.full s j .readRight r) (c.full s j .beforeGate r)
  | gate (c : Cell q) (s : Bool) (j : Fin q) (r : Reg)
      (h : c.skeleton.last) (hg : (S.clause c.metadata.task j).truth r = true) :
      Unary S (c.full s j .beforeGate r) (c.full s j .afterGate r)
  | undo_enter (c : Cell q) (s : Bool) (j : Fin q) (r : Reg) (h : c.skeleton.last) :
      Unary S (c.full s j .afterGate r) (c.full s j .undoLeft r)
  | undo_turn (c : Cell q) (s : Bool) (j : Fin q) (r : Reg) (h : c.skeleton.first) :
      Unary S (c.full s j .undoLeft r) (c.full s j .undoRight r)
  | undo_exit (c : Cell q) (s : Bool) (j : Fin q) (r : Reg) (h : c.skeleton.last) :
      Unary S (c.full s j .undoRight r) (c.full s j .finish r)
  | next (c : Cell q) (s : Bool) (j j' : Fin q) (hj : j.val+1=j'.val)
      (h : c.skeleton.last) :
      Unary S (c.full s j .finish 0) (c.full s j' .acquisition 0)
  | success (c : Cell q) (s : Bool) (j : Fin q)
      (hj : j.val+1=(S.count c.metadata.task).val) (h : c.skeleton.last) :
      Unary S (c.full s j .finish 0) (c.full s 0 .success 0)
  | pivot (c : Cell q) (s : Bool) (h : c.skeleton.last) (ht : c.metadata.zeroTask=false) :
      Unary S (c.full s 0 .success 0) (c.full (!s) 0 .success 0)

def Replacement (S : Schedule q) (dataSize : ℕ) (v w : List (Cell q)) : Prop :=
  (∀ c ∈ v++w, c.Format S dataSize) ∧
  ((∃ a b, v=[a] ∧ w=[b] ∧ (Unary S a b ∨ Unary S b a)) ∨
   (∃ a b a' b', v=[a,b] ∧ w=[a',b'] ∧
     (Binary S a b a' b' ∨ Binary S a' b' a b)))

lemma replacement_lengths (S : Schedule q) (dataSize : ℕ) (v w : List (Cell q))
    (h : Replacement S dataSize v w) :
    v.length=w.length ∧ 1≤v.length ∧ v.length≤2 := by
  rcases h.2 with ⟨a,b,rfl,rfl,_⟩ | ⟨a,b,a',b',rfl,rfl,_⟩ <;> simp

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_TableEncoding
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.FiniteTable.Codec
open LocalSyntax

lemma decode_eq_some_iff {h : ℕ} (hh : 4≤h) (w : Raw h) (c : Cell (2^h)) :
    decode (by omega) w=some c ↔ w=encode c := by
  constructor
  · unfold decode
    cases hp : parse (by omega) w with
    | none => simp
    | some d =>
      change (if w=encode d then some d else none)=some c → _
      split
      · intro he
        cases Option.some.inj he
        assumption
      · simp
  · rintro rfl
    exact decode_encode hh c

def decodeWord {h : ℕ} (hh : 0 < h) : List (Raw h) → Option (List (Cell (2^h)))
  | [] => some []
  | a::w => do
    let c ← decode hh a
    let cs ← decodeWord hh w
    return c::cs

lemma decodeWord_eq_some_iff {h : ℕ} (hh : 4≤h) (v : List (Raw h)) (w : List (Cell (2^h))) :
    decodeWord (by omega) v=some w ↔ v=w.map encode := by
  induction v generalizing w with
  | nil => cases w <;> simp [decodeWord]
  | cons a v ih =>
    cases ha : decode (by omega) a with
    | none =>
      have hne : ∀ b : Cell (2^h), a≠encode b := by
        intro b he
        have hx := decode_encode hh b
        rw [he] at ha
        rw [ha] at hx
        contradiction
      cases w <;> simp [decodeWord,ha,hne]
    | some b =>
      have hab : a=encode b := (decode_eq_some_iff hh a b).mp ha
      cases hv : decodeWord (by omega) v with
      | none =>
        have hne : ∀ z : List (Cell (2^h)), v≠z.map encode := by
          intro z hz
          have hz' := (ih z).mpr hz
          rw [hv] at hz'
          contradiction
        cases w <;> simp [decodeWord,ha,hv,hne]
      | some z =>
        have hvz : v=z.map encode := (ih z).mp hv
        simp only [decodeWord,ha,hv]
        rw [hab,hvz,← List.map_cons]
        change some (b::z)=some w ↔ (b::z).map encode=w.map encode
        rw [Option.some.injEq]
        exact (encode_injective hh).list_map.eq_iff.symm

def unaryZero {h : ℕ} (hh : 0 < h) (S : Schedule (2^h)) (d : ℕ) (a : Raw h) : Prop :=
  match decode hh a with
  | none => True
  | some c => UnaryZero S d c

def binaryZero {h : ℕ} (hh : 0 < h) (a b : Raw h) : Prop :=
  match decode hh a, decode hh b with
  | some c,some d => BinaryZero c d
  | _,_ => False

def replacement {h : ℕ} (hh : 0 < h) (S : Schedule (2^h)) (d : ℕ)
    (v w : List (Raw h)) : Prop :=
  match decodeWord hh v,decodeWord hh w with
  | some a,some b => Replacement S d a b
  | _,_ => False

def zero {h : ℕ} (hh : 0 < h) (S : Schedule (2^h)) (d : ℕ) (v : List (Raw h)) : Prop :=
  match v with
  | [a] => unaryZero hh S d a
  | [a,b] => binaryZero hh a b
  | _ => False

lemma replacement_has_encodings {h : ℕ} (hh : 4≤h) (S : Schedule (2^h)) (d : ℕ)
    (v w : List (Raw h)) (hv : replacement (by omega) S d v w) :
    ∃ a b, v=a.map encode ∧ w=b.map encode ∧ Replacement S d a b := by
  unfold replacement at hv
  cases ha : decodeWord (by omega) v with
  | none => simp [ha] at hv
  | some a =>
    cases hb : decodeWord (by omega) w with
    | none => simp [ha,hb] at hv
    | some b =>
      exact ⟨a,b,(decodeWord_eq_some_iff hh v a).mp ha,
        (decodeWord_eq_some_iff hh w b).mp hb,by simpa [ha,hb] using hv⟩

lemma replacement_lengths {h : ℕ} (hh : 4≤h) (S : Schedule (2^h)) (d : ℕ)
    (v w : List (Raw h)) (hv : replacement (by omega) S d v w) :
    v.length=w.length ∧ 1≤v.length ∧ v.length≤2 := by
  obtain ⟨a,b,rfl,rfl,hab⟩ := replacement_has_encodings hh S d v w hv
  simpa using FiniteTable.replacement_lengths S d a b hab

lemma zero_lengths {h : ℕ} (hh : 0 < h) (S : Schedule (2^h)) (d : ℕ)
    (v : List (Raw h)) (hv : zero hh S d v) : 1≤v.length ∧ v.length≤2 := by
  cases v with
  | nil => simp [zero] at hv
  | cons a v =>
    cases v with
    | nil => simp
    | cons b v =>
      cases v with
      | nil => simp
      | cons c v => simp [zero] at hv

end SourceBurnside.FiniteTable.Codec

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_Recognizer
attribute [-instance] _root_.OAI.SourceBurnside.RawFormula.instDecidableInRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable.Recognizer
open LocalSyntax Skeleton
variable {q : ℕ} [NeZero q]

lemma firstTest_iff (c : Skeleton q 10) : firstTest c ↔ c.first := by
  cases hp : c.pos <;> simp [firstTest,Skeleton.first,hp]
instance decideFirst (c : Skeleton q 10) : Decidable c.first := by
  haveI : Decidable (firstTest c) := by unfold firstTest; cases c.pos <;> infer_instance
  exact decidable_of_iff (firstTest c) (firstTest_iff c)
instance decideLast (c : Skeleton q 10) : Decidable c.last :=
  inferInstanceAs (Decidable (c.metadata.block.val=c.metadata.arity.val ∧ c.pos=.stop))
instance decideAdmissible (c : Skeleton q 10) : Decidable c.Admissible :=
  inferInstanceAs (Decidable ((c.marker=.right → ¬c.first) ∧ (c.marker=.left → ¬c.last)))
instance decideLeftExternal (c : Skeleton q 10) : Decidable c.leftExternal :=
  inferInstanceAs (Decidable (c.marker=.idle ∨ (c.marker≠.right ∧ c.first)))
instance decideRightExternal (c : Skeleton q 10) : Decidable c.rightExternal :=
  inferInstanceAs (Decidable (c.marker=.idle ∨ c.marker=.boundary ∨ (c.marker≠.left ∧ c.last)))
instance decideAcceptsLeft (c : Skeleton q 10) (m : Marker) : Decidable (c.acceptsLeft m) := by
  unfold acceptsLeft
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)
instance decideAcceptsRight (c : Skeleton q 10) (m : Marker) : Decidable (c.acceptsRight m) := by
  unfold acceptsRight
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)
instance decideStructural (a b : Skeleton q 10) : Decidable (Structural a b) := by
  unfold Structural
  cases a.pos <;> cases b.pos <;> infer_instance
instance decideInternal (a b : Skeleton q 10) : Decidable (Internal a b) := by
  unfold Internal
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)
instance decidePair (a b : Skeleton q 10) : Decidable (Skeleton.Pair a b) := by
  unfold Skeleton.Pair
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma paletteTest_iff (c : Cell q) : paletteTest c ↔ c.isPalette := by
  cases hp : c.pos <;> simp [paletteTest,Cell.isPalette,hp]
instance decidePalette (c : Cell q) : Decidable c.isPalette := by
  haveI : Decidable (paletteTest c) := by unfold paletteTest; cases c.pos <;> infer_instance
  exact decidable_of_iff (paletteTest c) (paletteTest_iff c)
instance decideHead (c : Skeleton q 10) : Decidable (IsHead c) := by
  unfold IsHead
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)
instance decideEndpoint (p : Phase) : Decidable (Cell.endpoint p) := by
  unfold Cell.endpoint
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

def dataTest (d : ℕ) (c : Cell q) : Prop := match c.pos with
  | .core p => d≤p.val → c.data=0
  | _ => True
omit [NeZero q] in
lemma dataTest_iff (d : ℕ) (c : Cell q) : dataTest d c ↔
    ∀ p, c.pos=.core p → d≤p.val → c.data=0 := by
  cases hp : c.pos <;> simp [dataTest,hp]
instance decideDataTest (d : ℕ) (c : Cell q) :
    Decidable (∀ p, c.pos=.core p → d≤p.val → c.data=0) := by
  haveI : Decidable (dataTest d c) := by unfold dataTest; cases c.pos <;> infer_instance
  exact decidable_of_iff (dataTest d c) (dataTest_iff d c)
instance decideFormat (S : Schedule q) (d : ℕ) (c : Cell q) : Decidable (c.Format S d) := by
  unfold Cell.Format
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

def UnaryTest (S : Schedule q) (a b : Cell q) : Prop :=
  (b.skeleton.first ∧ a=b.idle b.head.side ∧ b=b.boundary b.head.side) ∨
  (b.skeleton.last ∧ a=b.boundary b.head.side ∧ b=b.full b.head.side 0 .acquisition 0) ∨
  (b.skeleton.last ∧ a=b.full b.head.side b.head.clause .acquisition b.head.reg ∧
    b=b.full b.head.side b.head.clause .readLeft b.head.reg) ∨
  (b.skeleton.first ∧ a=b.full b.head.side b.head.clause .readLeft b.head.reg ∧
    b=b.full b.head.side b.head.clause .readRight b.head.reg) ∨
  (b.skeleton.last ∧ a=b.full b.head.side b.head.clause .readRight b.head.reg ∧
    b=b.full b.head.side b.head.clause .beforeGate b.head.reg) ∨
  (b.skeleton.last ∧ a=b.full b.head.side b.head.clause .beforeGate b.head.reg ∧
    b=b.full b.head.side b.head.clause .afterGate b.head.reg ∧
    (S.clause b.metadata.task b.head.clause).truth b.head.reg=true) ∨
  (b.skeleton.last ∧ a=b.full b.head.side b.head.clause .afterGate b.head.reg ∧
    b=b.full b.head.side b.head.clause .undoLeft b.head.reg) ∨
  (b.skeleton.first ∧ a=b.full b.head.side b.head.clause .undoLeft b.head.reg ∧
    b=b.full b.head.side b.head.clause .undoRight b.head.reg) ∨
  (b.skeleton.last ∧ a=b.full b.head.side b.head.clause .undoRight b.head.reg ∧
    b=b.full b.head.side b.head.clause .finish b.head.reg) ∨
  (b.skeleton.last ∧ a=b.full b.head.side a.head.clause .finish 0 ∧
    b=b.full b.head.side b.head.clause .acquisition 0 ∧ a.head.clause.val+1=b.head.clause.val) ∨
  (b.skeleton.last ∧ a=b.full b.head.side a.head.clause .finish 0 ∧
    b=b.full b.head.side 0 .success 0 ∧ a.head.clause.val+1=(S.count b.metadata.task).val) ∨
  (b.skeleton.last ∧ a=b.full (!b.head.side) 0 .success 0 ∧
    b=b.full b.head.side 0 .success 0 ∧ b.metadata.zeroTask=false)

instance decideUnaryTest (S : Schedule q) (a b : Cell q) : Decidable (UnaryTest S a b) := by
  unfold UnaryTest
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma unary_test {S : Schedule q} {a b : Cell q} (h : Unary S a b) : UnaryTest S a b := by
  cases h <;> simp_all [UnaryTest,Cell.idle,Cell.boundary,Cell.full,Skeleton.mark,
    Skeleton.first,Skeleton.last,Cell.pos,Cell.metadata]

lemma unary_of_test {S : Schedule q} {a b : Cell q} (h : UnaryTest S a b) : Unary S a b := by
  rcases h with ⟨hl,ha,hb⟩ | ⟨hl,ha,hb⟩ | ⟨hl,ha,hb⟩ | ⟨hl,ha,hb⟩ | ⟨hl,ha,hb⟩ |
    ⟨hl,ha,hb,hg⟩ | ⟨hl,ha,hb⟩ | ⟨hl,ha,hb⟩ | ⟨hl,ha,hb⟩ |
    ⟨hl,ha,hb,hj⟩ | ⟨hl,ha,hb,hj⟩ | ⟨hl,ha,hb,ht⟩
  · simpa only [← ha,← hb] using Unary.create (S:=S) b b.head.side hl
  · simpa only [← ha,← hb] using Unary.finish_acquisition (S:=S) b b.head.side hl
  · simpa only [← ha,← hb] using Unary.read_enter (S:=S) b b.head.side b.head.clause b.head.reg hl
  · simpa only [← ha,← hb] using Unary.read_turn (S:=S) b b.head.side b.head.clause b.head.reg hl
  · simpa only [← ha,← hb] using Unary.read_exit (S:=S) b b.head.side b.head.clause b.head.reg hl
  · simpa only [← ha,← hb] using Unary.gate (S:=S) b b.head.side b.head.clause b.head.reg hl hg
  · simpa only [← ha,← hb] using Unary.undo_enter (S:=S) b b.head.side b.head.clause b.head.reg hl
  · simpa only [← ha,← hb] using Unary.undo_turn (S:=S) b b.head.side b.head.clause b.head.reg hl
  · simpa only [← ha,← hb] using Unary.undo_exit (S:=S) b b.head.side b.head.clause b.head.reg hl
  · simpa only [← ha,← hb] using Unary.next (S:=S) b b.head.side a.head.clause b.head.clause hj hl
  · simpa only [← ha,← hb] using Unary.success (S:=S) b b.head.side a.head.clause hj hl
  · have hh := Unary.pivot (S:=S) b (!b.head.side) hl ht
    simpa only [Bool.not_not,← ha,← hb] using hh

instance decideUnary (S : Schedule q) (a b : Cell q) : Decidable (Unary S a b) :=
  decidable_of_iff (UnaryTest S a b) ⟨unary_of_test,unary_test⟩

omit [NeZero q] in
lemma headfreeTest_iff (c : Cell q) : headfreeTest c ↔ c.HeadFree := by
  cases hc : c.checker <;> simp [headfreeTest,Cell.HeadFree,hc]
instance decideHeadFree (c : Cell q) : Decidable c.HeadFree := by
  haveI : Decidable (headfreeTest c) := by unfold headfreeTest; cases c.checker <;> infer_instance
  exact decidable_of_iff (headfreeTest c) (headfreeTest_iff c)

instance decideAcquireTest (a b a' b' : Cell q) : Decidable (AcquireTest a b a' b') := by
  unfold AcquireTest; infer_instance
instance decideReadLeftTest (S : Schedule q) (a b a' b' : Cell q) : Decidable (ReadLeftTest S a b a' b') := by
  unfold ReadLeftTest; infer_instance
instance decideReadRightTest (a b a' b' : Cell q) : Decidable (ReadRightTest a b a' b') := by
  unfold ReadRightTest; infer_instance
instance decideUndoLeftTest (a b a' b' : Cell q) : Decidable (UndoLeftTest a b a' b') := by
  unfold UndoLeftTest; infer_instance
instance decideUndoRightTest (S : Schedule q) (a b a' b' : Cell q) : Decidable (UndoRightTest S a b a' b') := by
  unfold UndoRightTest; infer_instance
instance decideCheckerCreateTest (a b a' b' : Cell q) : Decidable (CheckerCreateTest a b a' b') := by
  unfold CheckerCreateTest; cases a.pos <;> cases b'.pos <;> cases b'.checker <;> infer_instance
instance decideCheckerAdvanceTest (a b a' b' : Cell q) : Decidable (CheckerAdvanceTest a b a' b') := by
  unfold CheckerAdvanceTest; cases a.pos <;> cases b.pos <;> cases a.checker <;> infer_instance
instance decideSwapTest (a b a' b' : Cell q) : Decidable (SwapTest a b a' b') := by
  unfold SwapTest; cases a.pos <;> cases b.pos <;> infer_instance
instance decideBinaryTest (S : Schedule q) (a b a' b' : Cell q) : Decidable (BinaryTest S a b a' b') := by
  unfold BinaryTest; infer_instance

instance decideBinary (S : Schedule q) (a b a' b' : Cell q) : Decidable (Binary S a b a' b') :=
  decidable_of_iff (BinaryTest S a b a' b') ⟨binary_of_test,binary_test⟩

def palettePairTest (a b : Palette.Check (Fin q)) : Prop :=
  match a,b with
  | .idle,.idle => True
  | .passed x,.passed y => x=y
  | .passed x,.head y => x=y
  | .head _,.idle => True
  | _,_ => False
omit [NeZero q] in
lemma palettePairTest_iff (a b : Palette.Check (Fin q)) :
    palettePairTest a b ↔ Palette.Pair a b := by
  constructor
  · cases a <;> cases b <;> simp only [palettePairTest] <;> intro h
    all_goals first | contradiction | subst_vars
    all_goals constructor
  · intro h
    cases h <;> simp [palettePairTest]
instance decidePalettePair (a b : Palette.Check (Fin q)) : Decidable (Palette.Pair a b) := by
  haveI : Decidable (palettePairTest a b) := by
    unfold palettePairTest
    cases a <;> cases b <;> infer_instance
  exact decidable_of_iff (palettePairTest a b) (palettePairTest_iff a b)
instance decideLastOK (a : Palette.Check (Fin q)) : Decidable (Palette.LastOK a) := by
  cases a <;> unfold Palette.LastOK <;> infer_instance
instance decideCheckerPair (a b : Cell q) : Decidable (CheckerPair a b) := by
  unfold CheckerPair
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)
instance decideCellPair (a b : Cell q) : Decidable (Pair a b) := by
  unfold Pair
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)
instance decideSemanticZero (S : Schedule q) (c : Cell q) : Decidable (SemanticZero S c) := by
  unfold SemanticZero
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

def passedOwnColorTest (c : Cell q) : Prop := match c.pos,c.checker with
  | .palette x,.passed y => x=y
  | _,_ => False
lemma passedOwnColorTest_iff (c : Cell q) : passedOwnColorTest c ↔
    ∃ x, c.pos=.palette x ∧ c.checker=.passed x := by
  cases hp : c.pos <;> cases hc : c.checker <;> simp [passedOwnColorTest,hp,hc,eq_comm]
instance decidePassedOwnColor (c : Cell q) :
    Decidable (∃ x, c.pos=.palette x ∧ c.checker=.passed x) := by
  haveI : Decidable (passedOwnColorTest c) := by
    unfold passedOwnColorTest
    cases c.pos <;> cases c.checker <;> infer_instance
  exact decidable_of_iff (passedOwnColorTest c) (passedOwnColorTest_iff c)
instance decideUnaryZero (S : Schedule q) (d : ℕ) (c : Cell q) : Decidable (UnaryZero S d c) := by
  unfold UnaryZero
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

def duplicateColorTest (a b : Cell q) : Prop := match a.pos,b.pos with
  | .palette x,.palette y => x=y
  | _,_ => False
lemma duplicateColorTest_iff (a b : Cell q) : duplicateColorTest a b ↔
    ∃ x, a.pos=.palette x ∧ b.pos=.palette x := by
  cases hp : a.pos <;> cases hq : b.pos <;> simp [duplicateColorTest,hp,hq,eq_comm]
instance decideDuplicateColor (a b : Cell q) :
    Decidable (∃ x, a.pos=.palette x ∧ b.pos=.palette x) := by
  haveI : Decidable (duplicateColorTest a b) := by
    unfold duplicateColorTest
    cases a.pos <;> cases b.pos <;> infer_instance
  exact decidable_of_iff (duplicateColorTest a b) (duplicateColorTest_iff a b)

def missingColorTest (a b : Cell q) : Prop := match a.pos,a.checker with
  | .palette x,.head y => b.pos=.stop ∧ x≠y
  | _,_ => False
lemma missingColorTest_iff (a b : Cell q) : missingColorTest a b ↔
    ∃ x y, a.pos=.palette x ∧ a.checker=.head y ∧ b.pos=.stop ∧ x≠y := by
  cases hp : a.pos <;> cases hc : a.checker <;> simp [missingColorTest,hp,hc]
instance decideMissingColor (a b : Cell q) :
    Decidable (∃ x y, a.pos=.palette x ∧ a.checker=.head y ∧ b.pos=.stop ∧ x≠y) := by
  haveI : Decidable (missingColorTest a b) := by
    unfold missingColorTest
    cases a.pos <;> cases a.checker <;> infer_instance
  exact decidable_of_iff (missingColorTest a b) (missingColorTest_iff a b)
instance decideBinaryZero (a b : Cell q) : Decidable (BinaryZero a b) := by
  unfold BinaryZero
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

def ReplacementTest (S : Schedule q) (d : ℕ) (v w : List (Cell q)) : Prop :=
  match v,w with
  | [a],[b] => a.Format S d ∧ b.Format S d ∧ (Unary S a b ∨ Unary S b a)
  | [a,b],[a',b'] => a.Format S d ∧ b.Format S d ∧ a'.Format S d ∧ b'.Format S d ∧
      (Binary S a b a' b' ∨ Binary S a' b' a b)
  | _,_ => False

lemma replacementTest_iff (S : Schedule q) (d : ℕ) (v w : List (Cell q)) :
    ReplacementTest S d v w ↔ Replacement S d v w := by
  rcases v with _|⟨a,_|⟨b,_|⟨c,v⟩⟩⟩ <;>
    rcases w with _|⟨x,_|⟨y,_|⟨z,w⟩⟩⟩ <;>
    simp [ReplacementTest,Replacement,and_assoc]
instance decideReplacement (S : Schedule q) (d : ℕ) (v w : List (Cell q)) :
    Decidable (Replacement S d v w) := by
  haveI : Decidable (ReplacementTest S d v w) := by
    unfold ReplacementTest
    split <;> infer_instance
  exact decidable_of_iff (ReplacementTest S d v w) (replacementTest_iff S d v w)

end SourceBurnside.FiniteTable.Recognizer

namespace SourceBurnside.FiniteTable.Codec
section
open Recognizer
instance decideRawUnaryZero {h : ℕ} (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) (a : Raw h) :
    Decidable (unaryZero hh S d a) := by
  unfold unaryZero
  split <;> infer_instance
instance decideRawBinaryZero {h : ℕ} (hh : 0<h) (a b : Raw h) :
    Decidable (binaryZero hh a b) := by
  unfold binaryZero
  split <;> infer_instance
instance decideRawReplacement {h : ℕ} (hh : 0<h) (S : Schedule (2^h)) (d : ℕ)
    (v w : List (Raw h)) : Decidable (replacement hh S d v w) := by
  unfold replacement
  split <;> infer_instance
instance decideRawZero {h : ℕ} (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) (v : List (Raw h)) :
    Decidable (zero hh S d v) := by
  unfold zero
  split <;> infer_instance

def entry {h : ℕ} (hh : 0<h) (S : Schedule (2^h)) (d : ℕ)
    (z : Bool) (v w : List (Raw h)) : Bool :=
  if z then decide (w=[] ∧ zero hh S d v) else decide (replacement hh S d v w)
lemma entry_zero {h : ℕ} (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) (v w : List (Raw h)) :
    entry hh S d true v w=true ↔ w=[] ∧ zero hh S d v := by simp [entry]
lemma entry_replacement {h : ℕ} (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) (v w : List (Raw h)) :
    entry hh S d false v w=true ↔ replacement hh S d v w := by simp [entry]

end

section

lemma binaryValue_lt (bs : List Bool) : binaryValue bs<2^bs.length := (BitVec.ofBoolListLE bs).isLt

lemma natCode_lt {h : ℕ} (w : Raw h) : natCode w<2^(10000*h) := by simpa [natCode] using binaryValue_lt (List.ofFn w)


open LocalSyntax

lemma getFin_eq_some_iff {n i : ℕ} {j : Fin n} : getFin n i=some j ↔ i=j.val := by
  unfold getFin
  split
  · simp only [Option.some.injEq]
    constructor
    · intro h;exact congrArg Fin.val h
    · intro h;apply Fin.ext;exact h
  · simp only [reduceCtorEq, false_iff]
    have := j.isLt
    omega

lemma getPosition_eq_some_iff {q t i : ℕ} {p : Position q} :
    getPosition q t i=some p ↔ t=positionTag p ∧ i=positionIndex p := by
  cases p <;> (fun_cases getPosition q t i <;>
    simp_all [getFin_eq_some_iff,positionTag,positionIndex])

lemma getMarker_eq_some_iff {t : ℕ} {m : Marker} : getMarker t=some m ↔ t=markerTag m := by
  cases m <;> (fun_cases getMarker t <;> simp_all [markerTag])

lemma getChecker_eq_some_iff {q t i : ℕ} {c : Palette.Check (Fin q)} :
    getChecker q t i=some c ↔ t=checkerTag c ∧ i=checkerIndex c := by
  cases c <;> (fun_cases getChecker q t i <;>
    simp_all [getFin_eq_some_iff,checkerTag,checkerIndex])

lemma getPhase_eq_some_iff {t : ℕ} {p : Phase} : getPhase t=some p ↔ t=phaseTag p := by
  cases p <;> (fun_cases getPhase t <;> simp_all [phaseTag])

lemma getPosition_isSome {q t i : ℕ} (hq : 0<q) :
    (getPosition q t i).isSome=true ↔ t<3 ∧ i<q ∧ (t=2 → i=0) := by
  fun_cases getPosition q t i <;> simp_all [getFin]
  omega
lemma getMarker_isSome {t : ℕ} : (getMarker t).isSome=true ↔ t<5 := by
  fun_cases getMarker t <;> simp_all
  omega
lemma getChecker_isSome {q t i : ℕ} (hq : 0<q) :
    (getChecker q t i).isSome=true ↔ t<3 ∧ i<q ∧ (t=0 → i=0) := by
  fun_cases getChecker q t i <;> simp_all [getFin]
  omega
lemma getPhase_isSome {t : ℕ} : (getPhase t).isSome=true ↔ t<9 := by
  fun_cases getPhase t <;> simp_all
  omega

def UsedAgree {h : ℕ} (hh : 0<h) (w : Raw h) (c : Cell (2^h)) : Prop :=
  (∀s : Fin 32,s.val<9 → integers c s=readInt hh w s) ∧
  (∀s : Fin 512,s.val<8 → flags c s=readFlag hh w s)

lemma parse_used {h : ℕ} (hh : 0<h) {w : Raw h} {c : Cell (2^h)}
    (hc : parse hh w=some c) : UsedAgree hh w c := by
  simp only [parse,bind,pure,Option.bind_eq_some_iff] at hc
  rcases hc with ⟨p,hp,m,hm,a,ha,b,hb,k,hk,z,hz,f,hf,hc⟩
  simp only [getPosition_eq_some_iff,getMarker_eq_some_iff,getFin_eq_some_iff,
    getChecker_eq_some_iff,getPhase_eq_some_iff] at hp hm ha hb hk hz hf
  cases Option.some.inj hc
  constructor
  · intro s hs
    rcases s with ⟨s,hsl⟩
    change s<9 at hs
    interval_cases s <;>
      simp_all [integers,Cell.pos,Cell.marker,Cell.metadata]

  · intro s hs
    rcases s with ⟨s,hsl⟩
    change s<8 at hs
    interval_cases s <;> simp [flags,Cell.metadata]

lemma integers_inRange {q : ℕ} (hq : 0<q) (c : Cell q) : InRange q (integers c) := by
  have hp := (@getPosition_isSome q (positionTag c.pos) (positionIndex c.pos) hq).mp
    (by rw [getPosition_encode];rfl)
  have hk := (@getChecker_isSome q (checkerTag c.checker) (checkerIndex c.checker) hq).mp
    (by rw [getChecker_encode];rfl)
  refine ⟨hp,markerTag_lt c.marker,c.metadata.arity.isLt,?_,hk,c.head.clause.isLt,phaseTag_lt c.head.phase⟩
  change c.metadata.block.val ≤ c.metadata.arity.val
  have := c.metadata.block.isLt
  omega

lemma parse_isSome {h : ℕ} (hh : 0<h) (w : Raw h) :
    (parse hh w).isSome=true ↔ InRange (2^h) (readInt hh w) := by
  constructor
  · intro ha
    rcases Option.isSome_iff_exists.mp ha with ⟨c,hc⟩
    have H := (parse_used hh hc).1
    have H0 := integers_inRange (by positivity : 0<2^h) c
    simpa only [InRange,H 0 (by decide),H 1 (by decide),H 2 (by decide),H 3 (by decide),
      H 4 (by decide),H 5 (by decide),H 6 (by decide),H 7 (by decide),H 8 (by decide)] using H0
  · rintro ⟨hp,hm,ha,hb,hk,hz,hf⟩
    rcases Option.isSome_iff_exists.mp ((getPosition_isSome (by positivity : 0<2^h)).mpr hp) with ⟨p,hp⟩
    rcases Option.isSome_iff_exists.mp (getMarker_isSome.mpr hm) with ⟨m,hm⟩
    let a : Fin 10 := ⟨readInt hh w 3,ha⟩
    let b : Fin (a.val+1) := ⟨readInt hh w 4,by dsimp [a];omega⟩
    rcases Option.isSome_iff_exists.mp ((getChecker_isSome (by positivity : 0<2^h)).mpr hk) with ⟨k,hk⟩
    let z : Fin (2^h) := ⟨readInt hh w 7,hz⟩
    rcases Option.isSome_iff_exists.mp (getPhase_isSome.mpr hf) with ⟨f,hf⟩
    have ha' : getFin 10 (readInt hh w 3)=some a := getFin_eq_some_iff.mpr rfl
    have hb' : getFin (a.val+1) (readInt hh w 4)=some b := getFin_eq_some_iff.mpr rfl
    have hz' : getFin (2^h) (readInt hh w 7)=some z := getFin_eq_some_iff.mpr rfl
    simp [parse,hp,hm,ha',hb',hk,hz',hf]

def usedWrite {h : ℕ} (hh : 0<h) (w : Raw h) : Raw h :=
  write (fun s => if s.val<9 then readInt hh w s else 0)
    (fun s => if s.val<8 then readFlag hh w s else false)

lemma usedWrite_of_parse {h : ℕ} (hh : 0<h) {w : Raw h} {c : Cell (2^h)}
    (hc : parse hh w=some c) : usedWrite hh w=encode c := by
  have H := parse_used hh hc
  unfold usedWrite encode
  congr 1
  · funext s
    by_cases hs : s.val<9
    · simpa [hs] using (H.1 s hs).symm
    · simp [hs,integers_unused c s (by omega)]
  · funext s
    by_cases hs : s.val<8
    · simpa [hs] using (H.2 s hs).symm
    · simp [hs,flags_unused c s (by omega)]

lemma decode_isSome_by_fields {h : ℕ} (hh : 0<h) (w : Raw h) :
    (decode hh w).isSome=true ↔ InRange (2^h) (readInt hh w) ∧ w=usedWrite hh w := by
  cases hc : parse hh w with
  | none =>
    have hr : ¬InRange (2^h) (readInt hh w) := by rw [←parse_isSome hh w,hc];simp
    simp [decode,hc,hr]
  | some c =>
    have hr : InRange (2^h) (readInt hh w) := (parse_isSome hh w).mp (by rw [hc];rfl)
    simp [decode,hc,hr,usedWrite_of_parse hh hc]

end

open LocalSyntax

lemma readInt_bit {h : ℕ} (hh : 0<h) (w : Raw h) (s : Fin 32) (i : Fin (2*h)) :
    (readInt hh w s).testBit i.val=w (intPosition hh s i) := by
  rw [readInt_arithmetic,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
  simp only [i.isLt,decide_true,Bool.true_and]
  have H := natCode_bit w (intPosition hh s i)
  simpa [intPosition,Nat.add_comm] using H

def ReservedZero {h : ℕ} (w : Raw h) : Prop := ∀i : Fin (10000*h),
  (18*h ≤ i.val ∧ i.val<64*h ∨ 64*h+8 ≤ i.val) → w i=false

lemma usedWrite_reserved {h : ℕ} (hh : 0<h) (w : Raw h) : ReservedZero (usedWrite hh w) := by
  intro i hi
  unfold usedWrite write
  split
  · rename_i ht
    have hs : ¬i.val/(2*h)<9 := by
      have h18 : 18*h ≤ i.val := by omega
      have hd : 9 ≤ i.val/(2*h) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
      omega
    simp [hs]
  · split
    · rename_i ht
      have hf : ¬i.val-64*h<8 := by omega
      simp [hf]
    · rfl

lemma usedWrite_eq_of_reserved {h : ℕ} (hh : 0<h) (w : Raw h) (hw : ReservedZero w) :
    usedWrite hh w=w := by
  funext i
  unfold usedWrite write
  split
  · rename_i hi
    let s : Fin 32 := ⟨i.val/(2*h),(Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)⟩
    let j : Fin (2*h) := ⟨i.val%(2*h),Nat.mod_lt _ (by omega)⟩
    have hpos : intPosition hh s j=i := by
      apply Fin.ext
      change i.val/(2*h)*(2*h)+i.val%(2*h)=i.val
      simpa [Nat.mul_comm] using Nat.div_add_mod i.val (2*h)
    change (if s.val<9 then readInt hh w s else 0).testBit j.val=w i
    split
    · rw [readInt_bit hh w s j,hpos]
    · rename_i hs
      have h18 : 18*h ≤ i.val := by
        have H := (Nat.le_div_iff_mul_le (by omega : 0<2*h)).mp (show 9 ≤ i.val/(2*h) by exact Nat.le_of_not_gt hs)
        omega
      simp [hw i (Or.inl ⟨h18,hi⟩)]
  · rename_i hi
    split
    · rename_i hf
      dsimp only
      split
      · change readFlag hh w ⟨i.val-64*h,by omega⟩=w i
        unfold readFlag
        congr 1
        apply Fin.ext
        simp [flagPosition]
        omega
      · have hn : 64*h+8 ≤ i.val := by omega
        exact (hw i (Or.inr hn)).symm
    · have hn : 64*h+8 ≤ i.val := by omega
      exact (hw i (Or.inr hn)).symm

lemma canonical_iff_reserved {h : ℕ} (hh : 0<h) (w : Raw h) : w=usedWrite hh w ↔ ReservedZero w := by
  constructor
  · intro hw
    rw [hw]
    exact usedWrite_reserved hh w
  · exact fun H => (usedWrite_eq_of_reserved hh w H).symm

lemma reserved_arithmetic {h : ℕ} (_hh : 0<h) (w : Raw h) : ReservedZero w ↔
    (natCode w/2^(18*h))%2^(46*h)=0 ∧ natCode w/2^(64*h+8)=0 := by
  rw [zero_window,zero_high]
  constructor
  · intro H
    constructor
    · intro i hi
      have hp : i+18*h<10000*h := by omega
      rw [natCode_bit w ⟨i+18*h,hp⟩]
      exact H _ (Or.inl (by simp;omega))
    · intro i
      by_cases hi : i+(64*h+8)<10000*h
      · rw [natCode_bit w ⟨i+(64*h+8),hi⟩]
        exact H _ (Or.inr (by simp))
      · apply Nat.testBit_lt_two_pow
        exact (natCode_lt w).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  · rintro ⟨H,J⟩ i (hi|hi)
    · have he : i.val-18*h+18*h=i.val := by omega
      have hj : i.val-18*h<46*h := by omega
      have hx := H (i.val-18*h) hj
      rw [he,natCode_bit] at hx
      exact hx
    · have he : i.val-(64*h+8)+(64*h+8)=i.val := by omega
      have hx := J (i.val-(64*h+8))
      rw [he,natCode_bit] at hx
      exact hx

lemma decode_isSome_arithmetic {h : ℕ} (hh : 0<h) (w : Raw h) :
    (decode hh w).isSome=true ↔
      InRange (2^h) (fun s : Fin 32 => (natCode w/2^(s.val*(2*h)))%2^(2*h)) ∧
      ((natCode w/2^(18*h))%2^(46*h)=0 ∧ natCode w/2^(64*h+8)=0) := by
  rw [decode_isSome_by_fields,canonical_iff_reserved,reserved_arithmetic hh]
  have he : readInt hh w=(fun s : Fin 32 => (natCode w/2^(s.val*(2*h)))%2^(2*h)) := funext (readInt_arithmetic hh w)
  rw [he]

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

namespace SourceBurnside.Structured.Device.Formula
section
variable {ι : Type}

lemma bool_any [DecidableEq ι] (es : List (Formula ι)) (vs : ι → ℕ) : (any es).eval vs≤1 := by rw [any_eval];split <;> omega

end

end SourceBurnside.Structured.Device.Formula

namespace SourceBurnside.RawFormula
open Structured.Device Structured.Device.Formula FiniteTable.Codec

def ranges : F := all
  [less (slot 0) (.constant 3),less (slot 1) bound,
   implies (equal (slot 0) (.constant 2)) (equal (slot 1) (.constant 0)),
   less (slot 2) (.constant 5),less (slot 3) (.constant 10),.le (slot 4) (slot 3),
   less (slot 5) (.constant 3),less (slot 6) bound,
   implies (equal (slot 5) (.constant 0)) (equal (slot 6) (.constant 0)),
   less (slot 7) bound,less (slot 8) (.constant 9)]
def reservation : F := and
  (equal (field word (scale 18) (scale 46)) (.constant 0))
  (equal (.div word (.powTwo (.add (scale 64) (.constant 8)))) (.constant 0))
def valid : F := and ranges reservation

lemma ranges_eval (h w : ℕ) : ranges.eval (inputs h w)=
    if InRange (2^h) (fun s : Fin 32 => (w/2^(s.val*(2*h)))%2^(2*h)) then 1 else 0 := by
  simp [ranges,InRange,eval,and_assoc]

lemma reservation_eval (h w : ℕ) : reservation.eval (inputs h w)=
    if (w/2^(18*h))%2^(46*h)=0 ∧ w/2^(64*h+8)=0 then 1 else 0 := by
  simp only [reservation,and_eval,equal_eval,field_eval,scale_eval,word_eval,eval]
  by_cases H : (w/2^(18*h))%2^(46*h)=0 <;>
    by_cases J : w/2^(64*h+8)=0 <;> simp [H,J]

lemma valid_eval (h w : ℕ) : valid.eval (inputs h w)=
    if InRange (2^h) (fun s : Fin 32 => (w/2^(s.val*(2*h)))%2^(2*h)) ∧
      ((w/2^(18*h))%2^(46*h)=0 ∧ w/2^(64*h+8)=0) then 1 else 0 := by
  rw [valid,and_eval,ranges_eval,reservation_eval]
  split_ifs <;> simp_all

theorem accepts_iff_decode {h : ℕ} (hh : 0<h) (w : Raw h) :
    valid.eval (inputs h (natCode w))=1 ↔ (decode hh w).isSome=true := by
  rw [decode_isSome_arithmetic hh w,valid_eval]
  split_ifs <;> simp_all

lemma valid_boolean (h w : ℕ) : valid.eval (inputs h w)≤1 := by rw [valid_eval];split_ifs <;> omega

end SourceBurnside.RawFormula

namespace SourceBurnside.Structured.Device.Formula
attribute [-simp] equal_eval all_eval any_eval and_eval or_eval neg_eval
end SourceBurnside.Structured.Device.Formula

namespace SourceBurnside.Structured.Device.Formula
attribute [-simp] less_eval
end SourceBurnside.Structured.Device.Formula

namespace SourceBurnside.CellFormula

open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]

variable {q : ℕ} [NeZero q] {a b : Expr (ι:=ι)} {v : ι → ℕ} {c d : Cell q}
variable (ha : evaluate a v=cellRecord c) (hb : evaluate b v=cellRecord d)
include ha hb
omit hb in
lemma unaryZero_exact (S : Schedule q) (size count truth : Formula ι) (n : ℕ)
    (hn : size.eval v=n) (hc : count.eval v=(S.count c.metadata.task).val)
    (ht : truth.eval v=boolean ((S.clause c.metadata.task c.head.clause).truth c.head.reg)) :
    (unaryZero a size count truth).eval v≠0 ↔ UnaryZero S n c := by
  simp only [unaryZero,Formula.any_ne_zero,Formula.neg_ne_zero,List.mem_cons,List.not_mem_nil,
    or_false,exists_eq_or_imp,exists_eq_left,formats_exact ha S size count n hn hc,
    semanticZero_exact ha S truth ht,passedOwn_exact ha,UnaryZero]
end SourceBurnside.CellFormula

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Formulas_ClauseEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w

namespace SourceBurnside.ClauseFormula
section
open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
structure Expr where
  address : Fin 3 → AddressFormula.Expr (ι:=ι)
  truth : Reg → Formula ι

def Represents {q : ℕ} (e : Expr (ι:=ι)) (v : ι → ℕ) (C : Clause q) : Prop :=
  (∀i,AddressFormula.evaluate (e.address i) v=AddressFormula.record (C.address i)) ∧
  (∀r,(e.truth r).eval v=boolean (C.truth r))

def matchReg (r : Fin 3 → Formula ι) (R : Reg) : Formula ι :=
  all (List.ofFn (fun i : Fin 3 => equal (r i) (.constant (boolean (bit (R i))))))
def regs : List Reg := [![0,0,0],![0,0,1],![0,1,0],![0,1,1],![1,0,0],![1,0,1],![1,1,0],![1,1,1]]
lemma mem_regs (R : Reg) : R∈regs := by
  have H (z : ZMod 2) : z=0 ∨ z=1 := by
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases H (R 0) with h0|h0 <;> rcases H (R 1) with h1|h1 <;> rcases H (R 2) with h2|h2 <;>
    simp [regs,funext_iff,Fin.forall_fin_succ,h0,h1,h2]
def truth (e : Expr (ι:=ι)) (r : Fin 3 → Formula ι) : Formula ι :=
  any (regs.map (fun R => and (matchReg r R) (e.truth R)))

lemma bit_injective : Function.Injective Codec.bit := by
  intro a b h;simpa only [unbit_bit] using congrArg unbit h
lemma matchReg_exact {r : Fin 3 → Formula ι} {v : ι → ℕ} {R : Reg}
    (hr : ∀i,(r i).eval v=boolean (bit (R i))) (T : Reg) :
    (matchReg r T).eval v≠0 ↔ R=T := by
  simp [matchReg,hr,boolean_injective.eq_iff,bit_injective.eq_iff,funext_iff,Fin.forall_fin_succ]
lemma truth_exact {q : ℕ} {e : Expr (ι:=ι)} {v : ι → ℕ} {C : Clause q}
    (he : Represents e v C) {r : Fin 3 → Formula ι} {R : Reg}
    (hr : ∀i,(r i).eval v=boolean (bit (R i))) :
    (truth e r).eval v≠0 ↔ C.truth R=true := by
  simp [truth,Formula.and_ne_zero,matchReg_exact hr,he.2,mem_regs]
lemma truth_bool (e : Expr (ι:=ι)) (r : Fin 3 → Formula ι) (v : ι → ℕ) :
    (truth e r).eval v≤1 := bool_any _ _
lemma truth_value {q : ℕ} {e : Expr (ι:=ι)} {v : ι → ℕ} {C : Clause q}
    (he : Represents e v C) {r : Fin 3 → Formula ι} {R : Reg}
    (hr : ∀i,(r i).eval v=boolean (bit (R i))) :
    (truth e r).eval v=boolean (C.truth R) := by
  have hb := truth_bool e r v
  cases hc : C.truth R with
  | false =>
    have ht := truth_exact he hr
    simp only [hc,Bool.false_eq_true,iff_false,not_ne_iff] at ht
    simpa only [hc,boolean_false] using ht
  | true =>
    have ht := (truth_exact he hr).mpr hc
    have h1 : (truth e r).eval v=1 := by omega
    simpa only [hc,boolean_true] using h1

def delta (e : Expr (ι:=ι)) (a : CellFormula.Expr (ι:=ι)) : Fin 3 → Formula ι :=
  fun i => AddressFormula.readAt (e.address i) a
lemma delta_exact {q : ℕ} [NeZero q] {e : Expr (ι:=ι)} {v : ι → ℕ} {C : Clause q}
    (he : Represents e v C) {a : CellFormula.Expr (ι:=ι)} {A : Cell q}
    (ha : CellFormula.evaluate a v=cellRecord A) (i : Fin 3) :
    (delta e a i).eval v=boolean (bit (A.delta C i)) := AddressFormula.readAt_exact (he.1 i) ha

def choose (b : Formula ι) (x y : Expr (ι:=ι)) : Expr (ι:=ι) where
  address i j := .branch b (x.address i j) (y.address i j)
  truth r := .branch b (x.truth r) (y.truth r)
omit [DecidableEq ι] in
lemma choose_true {q : ℕ} {b : Formula ι} {x y : Expr (ι:=ι)} {v : ι → ℕ} {C : Clause q}
    (hb : b.eval v≠0) (hx : Represents x v C) : Represents (choose b x y) v C := by
  constructor
  · intro i;funext j
    simpa [choose,AddressFormula.evaluate,Formula.eval,hb] using congrFun (hx.1 i) j
  · intro r;simpa [choose,Formula.eval,hb] using hx.2 r
omit [DecidableEq ι] in
lemma choose_false {q : ℕ} {b : Formula ι} {x y : Expr (ι:=ι)} {v : ι → ℕ} {C : Clause q}
    (hb : b.eval v=0) (hy : Represents y v C) : Represents (choose b x y) v C := by
  constructor
  · intro i;funext j
    simpa [choose,AddressFormula.evaluate,Formula.eval,hb] using congrFun (hy.1 i) j
  · intro r;simpa [choose,Formula.eval,hb] using hy.2 r

def lookup (index : Formula ι) (fallback : Expr (ι:=ι)) : ℕ → List (Expr (ι:=ι)) → Expr (ι:=ι)
  | _,[] => fallback
  | n,x::xs => choose (equal index (.constant n)) x (lookup index fallback (n+1) xs)
omit [DecidableEq ι] in
lemma lookup_exact {q : ℕ} (index : Formula ι) (fallback : Expr (ι:=ι)) (n : ℕ)
    (xs : List (Expr (ι:=ι))) (j : Fin xs.length) (v : ι → ℕ) (C : Clause q)
    (hj : index.eval v=n+j.val) (hr : Represents (xs.get j) v C) :
    Represents (lookup index fallback n xs) v C := by
  induction xs generalizing n with
  | nil => exact Fin.elim0 j
  | cons x xs ih =>
    by_cases h0 : j.val=0
    · have jj : j=0 := Fin.ext h0
      subst jj
      apply choose_true
      · simp [hj]
      · exact hr
    · let k : Fin xs.length := ⟨j.val-1,by have := j.isLt; simp only [List.length_cons] at this;omega⟩
      apply choose_false
      · simp [hj,h0]
      · apply ih (n+1) k
        · dsimp [k];omega
        · have hjk : j=k.succ := Fin.ext (by dsimp [k];omega)
          simpa only [hjk,List.get_cons_succ'] using hr
end

section
open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]

def truthTable (f : Reg → Bool) (r : Fin 3 → Formula ι) : Formula ι :=
  truth ⟨(fun _ => AddressFormula.certificate (.constant 0)),
    (fun R => .constant (boolean (f R)))⟩ r
lemma truthTable_value (f : Reg → Bool) {r : Fin 3 → Formula ι} {v : ι → ℕ} {R : Reg}
    (hr : ∀i,(r i).eval v=boolean (bit (R i))) :
    (truthTable f r).eval v=boolean (f R) := by
  let C : Clause 1 := ⟨fun _ => .certificate 0,f⟩
  apply truth_value (C:=C) _ hr
  constructor
  · intro i;exact AddressFormula.certificate_exact (.constant 0) v (0:Fin 1) rfl
  · intro R;rfl

structure ReadingExpr where
  address : AddressFormula.Expr (ι:=ι)
  value : Bool → Formula ι

def readValue {q : ℕ} : Addressable.Reading q → Bool → Bool
  | .inl a,_ => a
  | .inr _,b => b

def RepresentsReading {q : ℕ} [NeZero q] (e : ReadingExpr (ι:=ι)) (v : ι → ℕ) (w : Addressable.Reading q) : Prop :=
  AddressFormula.evaluate e.address v=AddressFormula.record (match w with | .inl _ => .certificate 0 | .inr a => a) ∧
  ∀b,(e.value b).eval v=boolean (readValue w b)

def fixedReading (b : Formula ι) : ReadingExpr (ι:=ι) :=
  ⟨AddressFormula.certificate (.constant 0),fun _ => b⟩
def addressReading (a : AddressFormula.Expr (ι:=ι)) : ReadingExpr (ι:=ι) := ⟨a,fun b => .constant (boolean b)⟩
omit [DecidableEq ι] in
lemma fixedReading_exact {q : ℕ} [NeZero q] {b : Formula ι} {v : ι → ℕ} {B : Bool}
    (hb : b.eval v=boolean B) : RepresentsReading (q:=q) (fixedReading b) v (.inl B) :=
  ⟨AddressFormula.certificate_exact (.constant 0) v 0 rfl,fun _ => hb⟩
omit [DecidableEq ι] in
lemma addressReading_exact {q : ℕ} [NeZero q] {a : AddressFormula.Expr (ι:=ι)} {v : ι → ℕ} {A : Address q}
    (ha : AddressFormula.evaluate a v=AddressFormula.record A) : RepresentsReading (addressReading a) v (.inr A) := ⟨ha,fun _ => rfl⟩

def make (w : Fin 3 → ReadingExpr (ι:=ι)) (f : (Fin 3 → Bool) → Bool) : Expr (ι:=ι) :=
  ⟨fun i => (w i).address,fun r => truthTable (fun R => f (fun i => bit (R i)))
    (fun i => (w i).value (bit (r i)))⟩
lemma make_exact {q : ℕ} [NeZero q] {w : Fin 3 → ReadingExpr (ι:=ι)} {v : ι → ℕ}
    {W : Fin 3 → Addressable.Reading q} (hw : ∀i,RepresentsReading (w i) v (W i))
    (f : (Fin 3 → Bool) → Bool) : Represents (make w f) v (Addressable.Clause.compile ⟨W,f⟩) := by
  constructor
  · intro i;exact (hw i).1
  · intro R
    let V : Reg := fun i => unbit (readValue (W i) (bit (R i)))
    have hV (i : Fin 3) : ((w i).value (bit (R i))).eval v=boolean (bit (V i)) := by
      simp only [V,bit_unbit];exact (hw i).2 _
    have E := truthTable_value (fun R => f (fun i => bit (R i))) hV
    change _=boolean (f _) at E
    change _=boolean (f _)
    rw [show (make w f).truth R=truthTable (fun R => f (fun i => bit (R i))) _ from rfl,E]
    congr 2;funext i
    cases h : W i <;> simp [V,readValue,h]
    rfl

end

open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
def unit (a : ReadingExpr (ι:=ι)) (b : Formula ι) : Expr (ι:=ι) :=
  choose b (make ![a,a,a] (fun v => decide (v 0=true))) (make ![a,a,a] (fun v => decide (v 0=false)))
lemma unit_exact {q : ℕ} [NeZero q] {a : ReadingExpr (ι:=ι)} {b : Formula ι} {v : ι → ℕ}
    {A : Addressable.Reading q} {B : Bool} (ha : RepresentsReading a v A) (hb : b.eval v=boolean B) :
    Represents (unit a b) v (Addressable.unit A B).compile := by
  have hw (i : Fin 3) : RepresentsReading (![a,a,a] i) v (![A,A,A] i) := by fin_cases i <;> exact ha
  cases B with
  | false => exact choose_false (by simpa using hb) (make_exact hw _)
  | true => exact choose_true (by rw [hb];decide) (make_exact hw _)

def equalReading (a b : ReadingExpr (ι:=ι)) (k : Formula ι) : Expr (ι:=ι) :=
  choose (equal k (.constant 0)) (make ![a,b,a] (fun v => !v 0 || v 1))
    (make ![a,b,a] (fun v => v 0 || !v 1))
lemma equalReading_exact {q : ℕ} [NeZero q] {a b : ReadingExpr (ι:=ι)} {k : Formula ι} {v : ι → ℕ}
    {A B : Addressable.Reading q} (K : Fin 2) (ha : RepresentsReading a v A) (hb : RepresentsReading b v B)
    (hk : k.eval v=K.val) : Represents (equalReading a b k) v (Addressable.equal A B K).compile := by
  have hw (i : Fin 3) : RepresentsReading (![a,b,a] i) v (![A,B,A] i) := by
    fin_cases i
    · exact ha
    · exact hb
    · exact ha
  fin_cases K
  · apply choose_true
    · simp [hk]
    · exact make_exact hw _
  · apply choose_false
    · simp [hk,equal_eval]
    · exact make_exact hw _

def initialData (a : ReadingExpr (ι:=ι)) (p : AddressFormula.Expr (ι:=ι)) (negated k : Formula ι) : Expr (ι:=ι) :=
  let b := addressReading p
  let u := make ![a,b,a] (fun v => !v 0 || !v 1)
  let v := make ![a,b,a] (fun v => v 0 || !!v 1)
  choose negated (choose (equal k (.constant 0)) u v) (equalReading a b k)
lemma initialData_exact {q : ℕ} [NeZero q] {a : ReadingExpr (ι:=ι)} {p : AddressFormula.Expr (ι:=ι)}
    {negated k : Formula ι} {v : ι → ℕ} {A : Addressable.Reading q} {P : Addressable.DataAddress q}
    (N : Bool) (K : Fin 2) (ha : RepresentsReading a v A)
    (hp : AddressFormula.evaluate p v=AddressFormula.record (Addressable.dataAddress P))
    (hn : negated.eval v=boolean N) (hk : k.eval v=K.val) :
    Represents (initialData a p negated k) v (Addressable.initial A (.input P N) K).compile := by
  have hb := addressReading_exact hp
  have hw (i : Fin 3) : RepresentsReading (![a,addressReading p,a] i) v (![A,.inr (Addressable.dataAddress P),A] i) := by
    fin_cases i
    · exact ha
    · exact hb
    · exact ha
  cases N with
  | false =>
    apply choose_false (by simpa using hn)
    exact equalReading_exact K ha hb hk
  | true =>
    apply choose_true (by rw [hn];decide)
    fin_cases K
    · exact choose_true (by simp [hk]) (make_exact hw _)
    · exact choose_false (by simp [hk,equal_eval]) (make_exact hw _)

def wire {n : ℕ} (a : Fin n → AddressFormula.Expr (ι:=ι)) : Tableau.Wire n → ReadingExpr (ι:=ι)
  | .inl b => fixedReading (.constant (boolean b))
  | .inr i => addressReading (a i)
omit [DecidableEq ι] in
lemma wire_exact {n q : ℕ} [NeZero q] {a : Fin n → AddressFormula.Expr (ι:=ι)} {v : ι → ℕ}
    {A : Fin n → Address q} (ha : ∀i,AddressFormula.evaluate (a i) v=AddressFormula.record (A i)) (w : Tableau.Wire n) :
    RepresentsReading (wire a w) v (w.map id A) := by
  cases w with
  | inl b => exact fixedReading_exact rfl
  | inr i => exact addressReading_exact (ha i)
def circuitClause {n : ℕ} (a : Fin n → AddressFormula.Expr (ι:=ι)) (C : Tableau.Circuit.Clause n) : Expr (ι:=ι) :=
  make (fun i => wire a (C.wires i)) C.truth
lemma circuitClause_exact {n q : ℕ} [NeZero q] {a : Fin n → AddressFormula.Expr (ι:=ι)} {v : ι → ℕ}
    {A : Fin n → Address q} (ha : ∀i,AddressFormula.evaluate (a i) v=AddressFormula.record (A i)) (C : Tableau.Circuit.Clause n) :
    Represents (circuitClause a C) v (Addressable.ofCircuitClause A C).compile :=
  make_exact (fun i => wire_exact ha (C.wires i)) _
end SourceBurnside.ClauseFormula

namespace SourceBurnside.InitialFormula
section
open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
structure Expr where
  tag : Formula ι
  address : AddressFormula.Expr (ι:=ι)
  polarity : Formula ι

def Represents {q : ℕ} (e : Expr (ι:=ι)) (v : ι → ℕ) : Addressable.InputBit q → Prop
  | .fixed b => e.tag.eval v=0 ∧ e.polarity.eval v=boolean b
  | .input p n => e.tag.eval v≠0 ∧ AddressFormula.evaluate e.address v=AddressFormula.record (Addressable.dataAddress p) ∧
      e.polarity.eval v=boolean n

def fixed (b : Formula ι) : Expr (ι:=ι) := ⟨.constant 0,AddressFormula.certificate (.constant 0),b⟩
def data (p : AddressFormula.Expr (ι:=ι)) (n : Formula ι) : Expr (ι:=ι) := ⟨.constant 1,p,n⟩
def choose (b : Formula ι) (x y : Expr (ι:=ι)) : Expr (ι:=ι) where
  tag := .branch b x.tag y.tag
  address i := .branch b (x.address i) (y.address i)
  polarity := .branch b x.polarity y.polarity
omit [DecidableEq ι] in
lemma fixed_exact {q : ℕ} {b : Formula ι} {v : ι → ℕ} {B : Bool} (hb : b.eval v=boolean B) :
    Represents (fixed b) v (.fixed (q:=q) B) := ⟨rfl,hb⟩
omit [DecidableEq ι] in
lemma data_exact {q : ℕ} {p : AddressFormula.Expr (ι:=ι)} {n : Formula ι} {v : ι → ℕ}
    (P : Addressable.DataAddress q) (N : Bool) (hp : AddressFormula.evaluate p v=AddressFormula.record (Addressable.dataAddress P))
    (hn : n.eval v=boolean N) : Represents (data p n) v (.input P N) := ⟨by simp [data],hp,hn⟩
omit [DecidableEq ι] in
lemma choose_true {q : ℕ} {b : Formula ι} {x y : Expr (ι:=ι)} {v : ι → ℕ} {I : Addressable.InputBit q}
    (hb : b.eval v≠0) (hx : Represents x v I) : Represents (choose b x y) v I := by
  have haddress : AddressFormula.evaluate (choose b x y).address v=AddressFormula.evaluate x.address v := by
    funext i;simp [choose,AddressFormula.evaluate,eval,hb]
  cases I with
  | fixed B => exact ⟨by simpa [choose,eval,hb] using hx.1,by simpa [choose,eval,hb] using hx.2⟩
  | input P N => exact ⟨by simpa [choose,eval,hb] using hx.1,haddress.trans hx.2.1,
      by simpa [choose,eval,hb] using hx.2.2⟩
omit [DecidableEq ι] in
lemma choose_false {q : ℕ} {b : Formula ι} {x y : Expr (ι:=ι)} {v : ι → ℕ} {I : Addressable.InputBit q}
    (hb : b.eval v=0) (hy : Represents y v I) : Represents (choose b x y) v I := by
  have haddress : AddressFormula.evaluate (choose b x y).address v=AddressFormula.evaluate y.address v := by
    funext i;simp [choose,AddressFormula.evaluate,eval,hb]
  cases I with
  | fixed B => exact ⟨by simpa [choose,eval,hb] using hy.1,by simpa [choose,eval,hb] using hy.2⟩
  | input P N => exact ⟨by simpa [choose,eval,hb] using hy.1,haddress.trans hy.2.1,
      by simpa [choose,eval,hb] using hy.2.2⟩

def clauses (a : ClauseFormula.ReadingExpr (ι:=ι)) (b : Expr (ι:=ι)) (k : Formula ι) : ClauseFormula.Expr (ι:=ι) :=
  ClauseFormula.choose b.tag (ClauseFormula.initialData a b.address b.polarity k) (ClauseFormula.unit a b.polarity)
lemma clauses_exact {q : ℕ} [NeZero q] {a : ClauseFormula.ReadingExpr (ι:=ι)} {b : Expr (ι:=ι)} {k : Formula ι} {v : ι → ℕ}
    {A : Addressable.Reading q} {B : Addressable.InputBit q} (K : Fin 2)
    (ha : ClauseFormula.RepresentsReading a v A) (hb : Represents b v B) (hk : k.eval v=K.val) :
    ClauseFormula.Represents (clauses a b k) v (Addressable.initial A B K).compile := by
  cases B with
  | fixed B => exact ClauseFormula.choose_false hb.1 (ClauseFormula.unit_exact ha hb.2)
  | input P N => exact ClauseFormula.choose_true hb.1 (ClauseFormula.initialData_exact N K ha hb.2.1 hb.2.2 hk)

def mapBit (f : Bool → Bool) {q : ℕ} : Addressable.InputBit q → Addressable.InputBit q
  | .fixed b => .fixed (f b)
  | .input p n => if f false=f true then .fixed (f false) else .input p (xor n (f false))
def symbol (f : Bool → Bool) (b : Expr (ι:=ι)) : Expr (ι:=ι) :=
  if f false=f true then fixed (.constant (boolean (f false)))
  else { b with polarity := if f false then neg b.polarity else b.polarity }
omit [DecidableEq ι] in
lemma symbol_exact {q : ℕ} {b : Expr (ι:=ι)} {v : ι → ℕ} {B : Addressable.InputBit q}
    (hb : Represents b v B) (f : Bool → Bool) : Represents (symbol f b) v (mapBit f B) := by
  have hus : (f false=false ∧ f true=false) ∨ (f false=false ∧ f true=true) ∨
      (f false=true ∧ f true=false) ∨ (f false=true ∧ f true=true) := by
    cases f false <;> cases f true <;> simp
  rcases hus with h|h|h|h
  all_goals cases B with
    | fixed B => cases B <;> simp_all [Represents,symbol,mapBit,fixed,neg_eval,boolean]
    | input P N => cases N <;> simp_all [Represents,symbol,mapBit,fixed,neg_eval,boolean]

structure Piece where
  length : Formula ι
  read : Formula ι → Expr (ι:=ι)
def Piece.Represents {q : ℕ} (p : Piece (ι:=ι)) (v : ι → ℕ) (bits : List (Addressable.InputBit q)) : Prop :=
  p.length.eval v=bits.length ∧ ∀ (j : Formula ι) (k : Fin bits.length), j.eval v=k.val →
    InitialFormula.Represents (p.read j) v (bits.get k)
def Piece.append (a b : Piece (ι:=ι)) : Piece (ι:=ι) where
  length := .add a.length b.length
  read i := choose (less i a.length) (a.read i) (b.read (.sub i a.length))
omit [DecidableEq ι] in
lemma Piece.append_exact {q : ℕ} {a b : Piece (ι:=ι)} {v : ι → ℕ} {as bs : List (Addressable.InputBit q)}
    (ha : a.Represents v as) (hb : b.Represents v bs) : (a.append b).Represents v (as++bs) := by
  refine ⟨by simp [Piece.append,ha.1,hb.1],?_⟩
  intro j k hj
  by_cases hk : k.val<as.length
  · apply choose_true
    · simp [hj,ha.1,hk]
    · have H := ha.2 j ⟨k.val,hk⟩ hj
      simpa only [List.get_eq_getElem,List.getElem_append_left hk] using H
  · apply choose_false
    · simp [less_eval,hj,ha.1,hk]
    · have hk' : k.val-as.length<bs.length := by have := k.isLt;simp only [List.length_append] at this;omega
      have H := hb.2 (.sub j a.length) ⟨k.val-as.length,hk'⟩ (by simp [eval,hj,ha.1])
      simpa only [List.get_eq_getElem,List.getElem_append_right (by omega : as.length≤k.val)] using H

omit [DecidableEq ι] in
lemma bitAt_value (x i : Formula ι) (v : ι → ℕ) :
    (bitAt x i).eval v=boolean ((x.eval v).testBit (i.eval v)) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change (x.eval v/2^(i.eval v))%2=(if decide ((x.eval v/2^(i.eval v))%2=1) then 1 else 0)
  have h := Nat.mod_lt (x.eval v/2^(i.eval v)) (by omega : 0<2)
  split_ifs <;> simp_all

def fixedBits (bits : List Bool) : Piece (ι:=ι) where
  length := .constant bits.length
  read i := fixed (bitAt (.constant (Codec.binaryValue bits)) i)
omit [DecidableEq ι] in
lemma fixedBits_exact {q : ℕ} (bits : List Bool) (v : ι → ℕ) :
    (fixedBits (ι:=ι) bits).Represents v (bits.map (Addressable.InputBit.fixed (q:=q))) := by
  refine ⟨by simp [fixedBits],?_⟩
  intro j k hj
  simp only [List.get_eq_getElem,List.getElem_map]
  apply fixed_exact
  rw [bitAt_value]
  simp [Codec.binaryValue_bit,eval,hj,show k.val<bits.length by simpa using k.isLt]

def number (n : Formula ι) : Piece (ι:=ι) where
  length := .bitLength n
  read i := fixed (bitAt n (.sub (.sub (.bitLength n) (.constant 1)) i))
omit [DecidableEq ι] in
lemma number_exact {q : ℕ} (n : Formula ι) (v : ι → ℕ) :
    (number n).Represents v ((bin (n.eval v)).map (Addressable.InputBit.fixed (q:=q))) := by
  refine ⟨by simp [number,eval,binSize],?_⟩
  intro j k hj
  simp only [List.get_eq_getElem,List.getElem_map]
  apply fixed_exact
  rw [bitAt_value]
  simp [bin,eval,binSize,hj]

def ones (n : Formula ι) : Piece (ι:=ι) where
  length := n
  read _ := fixed (.constant 1)
omit [DecidableEq ι] in
lemma ones_exact {q : ℕ} (n : Formula ι) (v : ι → ℕ) :
    (ones n).Represents v ((List.replicate (n.eval v) true).map (Addressable.InputBit.fixed (q:=q))) := by
  refine ⟨by simp [ones],?_⟩
  intro j k hj
  simp only [List.get_eq_getElem,List.getElem_map]
  apply fixed_exact
  simp [eval]

def header (n : Formula ι) : Piece (ι:=ι) :=
  ((ones (.bitLength n)).append (fixedBits [false])).append (number n)
omit [DecidableEq ι] in
lemma header_exact {q : ℕ} (n : Formula ι) (v : ι → ℕ) :
    (header n).Represents v ((enc (n.eval v)).map (Addressable.InputBit.fixed (q:=q))) := by
  have H := Piece.append_exact (Piece.append_exact (ones_exact (q:=q) (.bitLength n) v) (fixedBits_exact [false] v))
    (number_exact n v)
  simpa [header,enc,eval,binSize,List.map_append,List.append_assoc] using H
end

section
open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]

def bits (value length : Formula ι) : Piece (ι:=ι) where
  length := length
  read i := fixed (bitAt value i)
omit [DecidableEq ι] in
lemma bits_exact {q : ℕ} {value length : Formula ι} {v : ι → ℕ} (bs : List Bool)
    (hv : value.eval v=binaryValue bs) (hl : length.eval v=bs.length) :
    (bits value length).Represents v (bs.map (Addressable.InputBit.fixed (q:=q))) := by
  refine ⟨by simp [bits,hl],?_⟩
  intro j k hj
  simp only [List.get_eq_getElem,List.getElem_map]
  apply fixed_exact
  rw [bitAt_value,hv,binaryValue_bit]
  simp [hj,show k.val<bs.length by simpa using k.isLt]

def single (b : Formula ι) : Piece (ι:=ι) where
  length := .constant 1
  read _ := fixed b
omit [DecidableEq ι] in
lemma single_exact {q : ℕ} {b : Formula ι} {v : ι → ℕ} {B : Bool} (hb : b.eval v=boolean B) :
    (single b).Represents v [Addressable.InputBit.fixed (q:=q) B] := by
  refine ⟨rfl,?_⟩
  intro j k hj
  fin_cases k
  exact fixed_exact hb

def inputData {q : ℕ} (d l : ℕ) (Z : Bool) (hd : 0<d) (hdq : d≤q) (hl : 0<l) (hl10 : l≤10) :
    List (Addressable.InputBit q) :=
  List.ofFn (fun i : Fin (if Z then l*d else 2*(l*d)) =>
    Addressable.InputBit.input
      (decide (l*d ≤ i.val),⟨(i.val/d)%l,(Nat.mod_lt _ hl).trans_le hl10⟩,
        ⟨i.val%d,(Nat.mod_lt _ hd).trans_le hdq⟩) false)
def dataPiece (d l zeroTask : Formula ι) : Piece (ι:=ι) where
  length := .branch zeroTask (.mul l d) (.mul (.constant 2) (.mul l d))
  read i := data (AddressFormula.data (.le (.mul l d) i) (.mod (.div i d) l) (.mod i d)) (.constant 0)
omit [DecidableEq ι] in
lemma dataPiece_exact {q d l : ℕ} (Z : Bool) (hd : 0<d) (hdq : d≤q) (hl : 0<l) (hl10 : l≤10)
    {d' l' z : Formula ι} {v : ι → ℕ} (hD : d'.eval v=d) (hL : l'.eval v=l) (hZ : z.eval v=boolean Z) :
    (dataPiece d' l' z).Represents v (inputData d l Z hd hdq hl hl10) := by
  refine ⟨?_,?_⟩
  · cases Z <;> simp [dataPiece,inputData,eval,hD,hL,hZ,boolean]
  · intro j k hj
    simp only [inputData] at k ⊢
    rw [List.get_ofFn]
    apply data_exact _ false
    · apply AddressFormula.data_exact
      · simp [eval,hD,hL,hj,boolean]
      · simp [eval,hD,hL,hj]
      · simp [eval,hD,hj]
    · rfl

def sourceInput {q : ℕ} (a : List Bool) (H l : ℕ) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10) : List (Addressable.InputBit q) :=
  ((enc a.length++a++enc H++enc l++[Z]).map Addressable.InputBit.fixed) ++
    inputData (10000*H) l Z hd hdq hl hl10

def inputPiece (code codeLength H l zeroTask : Formula ι) : Piece (ι:=ι) :=
  (((((header codeLength).append (bits code codeLength)).append (header H)).append (header l)).append (single zeroTask)).append
    (dataPiece (.mul (.constant 10000) H) l zeroTask)
omit [DecidableEq ι] in
lemma inputPiece_exact {q H l : ℕ} (a : List Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10)
    {code codeLength H' l' z : Formula ι} {v : ι → ℕ}
    (hcode : code.eval v=binaryValue a) (hlen : codeLength.eval v=a.length)
    (hH : H'.eval v=H) (hL : l'.eval v=l) (hz : z.eval v=boolean Z) :
    (inputPiece code codeLength H' l' z).Represents v (sourceInput a H l Z hd hdq hl hl10) := by
  have hh := header_exact (q:=q) codeLength v
  rw [hlen] at hh
  have hc := bits_exact (q:=q) a hcode hlen
  have hH' := header_exact (q:=q) H' v
  rw [hH] at hH'
  have hl' := header_exact (q:=q) l' v
  rw [hL] at hl'
  have h := Piece.append_exact (Piece.append_exact (Piece.append_exact (Piece.append_exact hh hc) hH') hl') (single_exact hz)
  have hd' := dataPiece_exact Z hd hdq hl hl10 (d':=.mul (.constant 10000) H') (by simp [eval,hH]) hL hz
  simpa [inputPiece,sourceInput,List.map_append,List.append_assoc] using Piece.append_exact h hd'
end

open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]

def row {q β W : ℕ} (blank origin : Fin β → Bool) (symbol : Bool → Fin β → Bool) (o : ℕ)
    (input : List (Addressable.InputBit q)) (j : Fin W) (r : Fin β) : Addressable.InputBit q :=
  if j.val=o then .fixed (origin r)
  else if hj : o<j.val ∧ j.val-(o+1) < input.length then
    mapBit (fun b => symbol b r) (input[j.val-(o+1)]'hj.2)
  else .fixed (blank r)

def cell {β : ℕ} (blank origin : Fin β → Bool) (encoding : Bool → Fin β → Bool)
    (o : Formula ι) (input : Piece (ι:=ι)) (j : Formula ι) (r : Fin β) : Expr (ι:=ι) :=
  let k := .sub j (.add o (.constant 1))
  choose (equal j o) (fixed (.constant (boolean (origin r))))
    (choose (and (less o j) (less k input.length))
      (symbol (fun b => encoding b r) (input.read k)) (fixed (.constant (boolean (blank r)))))
omit [DecidableEq ι] in
lemma cell_exact {q β W : ℕ} (blank origin : Fin β → Bool) (encoding : Bool → Fin β → Bool)
    {o j : Formula ι} {input : Piece (ι:=ι)} {v : ι → ℕ} {O : ℕ} {Input : List (Addressable.InputBit q)}
    (J : Fin W) (R : Fin β) (ho : o.eval v=O) (hj : j.eval v=J.val) (hinput : input.Represents v Input) :
    Represents (cell blank origin encoding o input j R) v (row blank origin encoding O Input J R) := by
  by_cases h0 : J.val=O
  · rw [row,ite_eq_left h0]
    apply choose_true
    · simp [hj,ho,h0]
    · exact fixed_exact rfl
  · rw [row,ite_eq_right h0]
    apply choose_false
    · simp [equal_eval,hj,ho,h0]
    · by_cases h1 : O<J.val ∧ J.val-(O+1)<Input.length
      · rw [dite_eq_left h1]
        apply choose_true
        · simp [Formula.and_ne_zero,ho,hj,eval,hinput.1,h1]
        · exact symbol_exact (hinput.2 _ ⟨J.val-(O+1),h1.2⟩ (by simp [eval,hj,ho])) _
      · rw [dite_eq_right h1]
        apply choose_false
        · rw [←not_ne_iff]
          simpa [Formula.and_ne_zero,ho,hj,eval,hinput.1] using h1
        · exact fixed_exact rfl
end SourceBurnside.InitialFormula

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Formulas_LocalPredicates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.PhysicalFormula
section
open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]

def x (β : ℕ) (W t j r : Formula ι) : AddressFormula.Expr (ι:=ι) :=
  AddressFormula.certificate (.add (.mul (.constant β) (.add (.mul W t) j)) r)
def y (β g : ℕ) (T W t j v : Formula ι) : AddressFormula.Expr (ι:=ι) :=
  AddressFormula.certificate (.add (.mul (.mul (.constant β) W) T)
    (.add (.mul (.constant g) (.add (.mul (.sub W (.constant 2)) t) j)) v))

omit [DecidableEq ι] in
lemma x_exact {q β g T W : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    {w t j r : Formula ι} {v : ι → ℕ} (tt : Fin T) (jj : Fin W) (rr : Fin β)
    (hw : w.eval v=W) (ht : t.eval v=tt.val) (hj : j.eval v=jj.val) (hr : r.eval v=rr.val) :
    AddressFormula.evaluate (x β w t j r) v=AddressFormula.record (L.x tt jj rr) := by
  apply AddressFormula.certificate_exact
  rw [L.core_x_val]
  simp [Formula.eval,hw,ht,hj,hr,Tableau.Layout.xAddress]
omit [DecidableEq ι] in
lemma y_exact {q β g T W : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    {T' w t j r : Formula ι} {v : ι → ℕ} (tt : Fin (T-1)) (jj : Fin (W-2)) (rr : Fin g)
    (hT : T'.eval v=T) (hw : w.eval v=W) (ht : t.eval v=tt.val) (hj : j.eval v=jj.val) (hr : r.eval v=rr.val) :
    AddressFormula.evaluate (y β g T' w t j r) v=AddressFormula.record (L.y tt jj rr) := by
  apply AddressFormula.certificate_exact
  rw [L.core_y_val]
  simp [Formula.eval,hT,hw,ht,hj,hr,Tableau.Layout.yAddress,Nat.add_assoc]

def localAddress (β g : ℕ) (T W t j : Formula ι) : Fin (3*β+g) → AddressFormula.Expr (ι:=ι) :=
  Fin.addCases (fun i => let p := finProdFinEquiv.symm i
    x β W t (.add j (.constant p.1.val)) (.constant p.2.val))
    (fun r => y β g T W t j (.constant r.val))
omit [DecidableEq ι] in
lemma localAddress_exact {q β g T W : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    {T' w t j : Formula ι} {v : ι → ℕ} (tt : Fin (T-1)) (jj : Fin (W-2))
    (hT : T'.eval v=T) (hw : w.eval v=W) (ht : t.eval v=tt.val) (hj : j.eval v=jj.val)
    (i : Fin (3*β+g)) :
    AddressFormula.evaluate (localAddress β g T' w t j i) v=AddressFormula.record (L.localRead tt jj i) := by
  refine Fin.addCases ?_ ?_ i
  · intro a
    simp only [localAddress,Addressable.Layout.localRead,Fin.addCases_left]
    apply x_exact L _ _ _ hw ht
    · simp [Formula.eval,hj]
    · rfl
  · intro a
    simp only [localAddress,Addressable.Layout.localRead,Fin.addCases_right]
    exact y_exact L tt jj a hT hw ht hj rfl

omit [DecidableEq ι] in
lemma lookup_ofFn_exact {q n : ℕ} {e : Fin n → ClauseFormula.Expr (ι:=ι)}
    {index : Formula ι} {fallback : ClauseFormula.Expr (ι:=ι)} {v : ι → ℕ} {C : Clause q}
    (k : Fin n) (hk : index.eval v=k.val) (he : ClauseFormula.Represents (e k) v C) :
    ClauseFormula.Represents (ClauseFormula.lookup index fallback 0 (List.ofFn e)) v C := by
  apply ClauseFormula.lookup_exact index fallback 0 (List.ofFn e)
    ⟨k.val,by simp⟩ v C
  · simpa using hk
  · simpa using he

def localClause (β g : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (T W t j i : Formula ι) : ClauseFormula.Expr (ι:=ι) :=
  let addresses := localAddress β g T W t j
  let fallback := ClauseFormula.unit (ClauseFormula.fixedReading (.constant 1)) (.constant 1)
  let gates := c.clauses.map (ClauseFormula.circuitClause addresses)
  let k := .mod (.sub i (.constant (3*g))) (.constant 2)
  let out := List.ofFn (fun r : Fin β => ClauseFormula.equalReading
    (ClauseFormula.addressReading (x β W (.add t (.constant 1)) (.add j (.constant 1)) (.constant r.val)))
    (ClauseFormula.wire addresses (output r)) k)
  ClauseFormula.choose (less i (.constant (3*g)))
    (ClauseFormula.lookup i fallback 0 gates)
    (ClauseFormula.lookup (.div (.sub i (.constant (3*g))) (.constant 2)) fallback 0 out)

lemma localClause_exact {q β g T W : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    {T' w t j i : Formula ι} {v : ι → ℕ} (tt : Fin (T-1)) (jj : Fin (W-2)) (ii : Fin (3*g+2*β))
    (hT : T'.eval v=T) (hw : w.eval v=W) (ht : t.eval v=tt.val) (hj : j.eval v=jj.val) (hi : i.eval v=ii.val) :
    ClauseFormula.Represents (localClause β g c output T' w t j i) v (L.localClause c output tt jj ii).compile := by
  have ha := localAddress_exact L tt jj hT hw ht hj
  by_cases hgate : ii.val<3*g
  · rw [Addressable.Layout.localClause,dite_eq_left hgate]
    apply ClauseFormula.choose_true
    · simpa [hi] using hgate
    · apply ClauseFormula.lookup_exact _ _ 0 _
        ⟨ii.val,by simpa only [List.length_map,c.clauses_length] using hgate⟩
      · simpa using hi
      · simpa using ClauseFormula.circuitClause_exact ha (c.clauses[ii.val]'(by simpa only [c.clauses_length] using hgate))
  · rw [Addressable.Layout.localClause,dite_eq_right hgate]
    apply ClauseFormula.choose_false
    · simp [less_eval,hi,hgate]
    · apply lookup_ofFn_exact ⟨(ii.val-3*g)/2,by have := ii.isLt;omega⟩
      · simp [Formula.eval,hi]
      · apply ClauseFormula.equalReading_exact
          ⟨(ii.val-3*g)%2,Nat.mod_lt _ (by decide)⟩
        · apply ClauseFormula.addressReading_exact
          apply x_exact L _ _ _ hw
          · simp [Formula.eval,ht,Addressable.Layout.nextTime]
          · simp [Formula.eval,hj,Addressable.Layout.interior]
          · rfl
        · exact ClauseFormula.wire_exact ha _
        · simp [Formula.eval,hi]

def chooseIndex (b : Formula ι) (x y : Fin 4 → Formula ι) : Fin 4 → Formula ι :=
  fun i => .branch b (x i) (y i)
def clauseIndex (β g : ℕ) (T W i : Formula ι) : Fin 4 → Formula ι :=
  let A := .mul (.constant (2*β)) W
  let B := .mul (.constant (2*β)) (.sub T (.constant 1))
  let C := .mul (.mul (.constant (3*g+2*β)) (.sub W (.constant 2))) (.sub T (.constant 1))
  let p := .sub i A
  let r := .sub p B
  let c := .constant (3*g+2*β)
  chooseIndex (less i A)
    ![.constant 0,.div (.div i (.constant 2)) (.constant β),.mod (.div i (.constant 2)) (.constant β),.mod i (.constant 2)]
    (chooseIndex (less i (.add A B))
      ![.constant 1,.div (.div p (.constant β)) (.constant 2),.mod (.div p (.constant β)) (.constant 2),.mod p (.constant β)]
      (chooseIndex (less i (.add (.add A B) C))
        ![.constant 2,.div (.div r c) (.sub W (.constant 2)),.mod (.div r c) (.sub W (.constant 2)),.mod r c]
        ![.constant 3,.constant 0,.constant 0,.sub r C]))
def indexEval (x : Fin 4 → Formula ι) (v : ι → ℕ) : ℕ × (ℕ × ℕ × ℕ) :=
  ((x 0).eval v,((x 1).eval v,(x 2).eval v,(x 3).eval v))
omit [DecidableEq ι] in
lemma clauseIndex_exact (β g : ℕ) (T W i : Formula ι) (v : ι → ℕ) :
    indexEval (clauseIndex β g T W i) v=Addressable.Layout.directIndex β g (T.eval v) (W.eval v) (i.eval v) := by
  by_cases h0 : i.eval v<2*β*W.eval v
  · simp [indexEval,clauseIndex,chooseIndex,less_eval,eval,h0,Addressable.Layout.directIndex]
  · by_cases h1 : i.eval v<2*β*W.eval v+2*β*(T.eval v-1)
    · simp [indexEval,clauseIndex,chooseIndex,less_eval,eval,h0,h1,Addressable.Layout.directIndex]
    · by_cases h2 : i.eval v<2*β*W.eval v+2*β*(T.eval v-1)+(3*g+2*β)*(W.eval v-2)*(T.eval v-1)
      all_goals simp [indexEval,clauseIndex,chooseIndex,less_eval,eval,h0,h1,h2,Addressable.Layout.directIndex]
end

section
open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
def fallback : ClauseFormula.Expr (ι:=ι) := ClauseFormula.unit (ClauseFormula.fixedReading (.constant 1)) (.constant 1)
def initialFamily (β : ℕ) (init : Formula ι → Fin β → InitialFormula.Expr (ι:=ι))
    (W j r k : Formula ι) : ClauseFormula.Expr (ι:=ι) :=
  ClauseFormula.lookup r fallback 0 (List.ofFn (fun s : Fin β => InitialFormula.clauses
    (ClauseFormula.addressReading (x β W (.constant 0) j (.constant s.val))) (init j s) k))
lemma initialFamily_exact {q β g T W : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    {init : Formula ι → Fin β → InitialFormula.Expr (ι:=ι)} {Init : Fin W → Fin β → Addressable.InputBit q}
    {w j r k : Formula ι} {v : ι → ℕ} (J : Fin W) (R : Fin β) (K : Fin 2)
    (hw : w.eval v=W) (hj : j.eval v=J.val) (hr : r.eval v=R.val) (hk : k.eval v=K.val)
    (hi : InitialFormula.Represents (init j R) v (Init J R)) :
    ClauseFormula.Represents (initialFamily β init w j r k) v
      (Addressable.initial (.inr (L.x ⟨0,L.time_pos⟩ J R)) (Init J R) K).compile := by
  apply lookup_ofFn_exact R hr
  apply InitialFormula.clauses_exact K
  · exact ClauseFormula.addressReading_exact (x_exact L ⟨0,L.time_pos⟩ J R hw rfl hj rfl)
  · exact hi
  · exact hk

def boundaryFamily (β : ℕ) (blank : Fin β → Bool) (W t j r : Formula ι) : ClauseFormula.Expr (ι:=ι) :=
  let boundary := .branch (equal j (.constant 0)) (.constant 0) (.sub W (.constant 1))
  ClauseFormula.lookup r fallback 0 (List.ofFn (fun s : Fin β => ClauseFormula.unit
    (ClauseFormula.addressReading (x β W (.add t (.constant 1)) boundary (.constant s.val))) (.constant (boolean (blank s)))))
lemma boundaryFamily_exact {q β g T W : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    (blank : Fin β → Bool) {w t j r : Formula ι} {v : ι → ℕ}
    (Tt : Fin (T-1)) (J : Fin 2) (R : Fin β)
    (hw : w.eval v=W) (ht : t.eval v=Tt.val) (hj : j.eval v=J.val) (hr : r.eval v=R.val) :
    ClauseFormula.Represents (boundaryFamily β blank w t j r) v
      (Addressable.unit (.inr (L.x (Addressable.Layout.nextTime Tt) (L.boundary J) R)) (blank R)).compile := by
  apply lookup_ofFn_exact R hr
  apply ClauseFormula.unit_exact
  · apply ClauseFormula.addressReading_exact
    apply x_exact L _ _ _ hw
    · simp [eval,ht,Addressable.Layout.nextTime]
    · simp [eval,equal_eval,hj,hw,Addressable.Layout.boundary]
      split_ifs <;> rfl
    · rfl
  · rfl

def finalFamily (β : ℕ) (accept : Fin β → Bool) (T W O r : Formula ι) : ClauseFormula.Expr (ι:=ι) :=
  ClauseFormula.lookup r fallback 0 (List.ofFn (fun s : Fin β => ClauseFormula.unit
    (ClauseFormula.addressReading (x β W (.sub T (.constant 1)) O (.constant s.val))) (.constant (boolean (accept s)))))
lemma finalFamily_exact {q β g T W : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    (accept : Fin β → Bool) {T' w O r : Formula ι} {v : ι → ℕ}
    (R : Fin β) (hT : T'.eval v=T) (hw : w.eval v=W) (hO : O.eval v=L.origin.val) (hr : r.eval v=R.val) :
    ClauseFormula.Represents (finalFamily β accept T' w O r) v
      (Addressable.unit (.inr (L.x ⟨T-1,by have := L.time_pos;omega⟩ L.origin R)) (accept R)).compile := by
  apply lookup_ofFn_exact R hr
  apply ClauseFormula.unit_exact
  · apply ClauseFormula.addressReading_exact
    exact x_exact L _ _ _ hw (by simp [eval,hT]) hO rfl
  · rfl

def familyClause (β g : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (init : Formula ι → Fin β → InitialFormula.Expr (ι:=ι)) (blank accept : Fin β → Bool)
    (T W O : Formula ι) (e : Fin 4 → Formula ι) : ClauseFormula.Expr (ι:=ι) :=
  ClauseFormula.choose (equal (e 0) (.constant 0)) (initialFamily β init W (e 1) (e 2) (e 3))
    (ClauseFormula.choose (equal (e 0) (.constant 1)) (boundaryFamily β blank W (e 1) (e 2) (e 3))
      (ClauseFormula.choose (equal (e 0) (.constant 2)) (localClause β g c output T W (e 1) (e 2) (e 3))
        (finalFamily β accept T W O (e 3))))
lemma familyClause_exact {q β g T W : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    {init : Formula ι → Fin β → InitialFormula.Expr (ι:=ι)} {Init : Fin W → Fin β → Addressable.InputBit q}
    (blank accept : Fin β → Bool) {T' w O : Formula ι} {v : ι → ℕ} (e : Fin 4 → Formula ι)
    (hT : T'.eval v=T) (hw : w.eval v=W) (hO : O.eval v=L.origin.val)
    (hi : ∀j J, j.eval v=J.val → ∀r, InitialFormula.Represents (init j r) v (Init J r))
    (K : Addressable.Layout.ClauseIndex (β:=β) (g:=g) (T:=T) (W:=W))
    (he : indexEval e v=(Addressable.Layout.family K,Addressable.Layout.coordinates K)) :
    ClauseFormula.Represents (familyClause β g c output init blank accept T' w O e) v
      (L.clause c output Init blank accept K).compile := by
  cases K with
  | inl K => cases K with
    | inl K => cases K with
      | inl K =>
        rcases K with ⟨⟨J,R⟩,N⟩
        simp only [indexEval,Addressable.Layout.family,Addressable.Layout.coordinates,Prod.mk.injEq] at he
        apply ClauseFormula.choose_true (by simp [he.1])
        exact initialFamily_exact L J R N hw he.2.1 he.2.2.1 he.2.2.2 (hi _ J he.2.1 R)
      | inr K =>
        rcases K with ⟨⟨Tt,J⟩,R⟩
        simp only [indexEval,Addressable.Layout.family,Addressable.Layout.coordinates,Prod.mk.injEq] at he
        apply ClauseFormula.choose_false (by simp [equal_eval,he.1])
        apply ClauseFormula.choose_true (by simp [he.1])
        exact boundaryFamily_exact L blank Tt J R hw he.2.1 he.2.2.1 he.2.2.2
    | inr K =>
      rcases K with ⟨⟨Tt,J⟩,R⟩
      simp only [indexEval,Addressable.Layout.family,Addressable.Layout.coordinates,Prod.mk.injEq] at he
      apply ClauseFormula.choose_false (by simp [equal_eval,he.1])
      apply ClauseFormula.choose_false (by simp [equal_eval,he.1])
      apply ClauseFormula.choose_true (by simp [he.1])
      exact localClause_exact L c output Tt J R hT hw he.2.1 he.2.2.1 he.2.2.2
  | inr R =>
    simp only [indexEval,Addressable.Layout.family,Addressable.Layout.coordinates,Prod.mk.injEq] at he
    apply ClauseFormula.choose_false (by simp [equal_eval,he.1])
    apply ClauseFormula.choose_false (by simp [equal_eval,he.1])
    apply ClauseFormula.choose_false (by simp [equal_eval,he.1])
    exact finalFamily_exact L accept R hT hw hO he.2.2.2
end

open FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
def clauseAt (β g : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (init : Formula ι → Fin β → InitialFormula.Expr (ι:=ι)) (blank accept : Fin β → Bool)
    (T W O i : Formula ι) : ClauseFormula.Expr (ι:=ι) :=
  familyClause β g c output init blank accept T W O (clauseIndex β g T W i)
lemma clauseAt_exact {q β g T W : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    {init : Formula ι → Fin β → InitialFormula.Expr (ι:=ι)} {Init : Fin W → Fin β → Addressable.InputBit q}
    (blank accept : Fin β → Bool) {T' w O i : Formula ι} {v : ι → ℕ}
    (hT : T'.eval v=T) (hw : w.eval v=W) (hO : O.eval v=L.origin.val)
    (hi : ∀j J, j.eval v=J.val → ∀r, InitialFormula.Represents (init j r) v (Init J r))
    (K : Fin (Tableau.Layout.clauseCount β g T W)) (hK : i.eval v=K.val) :
    ClauseFormula.Represents (clauseAt β g c output init blank accept T' w O i) v
      (L.clauseAt c output Init blank accept K).compile := by
  apply familyClause_exact L c output blank accept _ hT hw hO hi (Addressable.Layout.clauseEquiv.symm K)
  rw [clauseIndex_exact,hT,hw,hK]
  exact Addressable.Layout.clause_index_lookup K
end SourceBurnside.PhysicalFormula

namespace SourceBurnside.CellFormula
section
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]

def unaryMove (a b : Expr (ι:=ι)) (count truth : Formula ι) : Formula ι :=
  any [
    all [first b,equalCells a (idle b (side b)),equalCells b (boundary b (side b))],
    all [last b,equalCells a (boundary b (side b)),equalCells b (full b (side b) (.constant 0) .acquisition zeroReg)],
    all [last b,equalCells a (full b (side b) (clause b) .acquisition (register b)),equalCells b (full b (side b) (clause b) .readLeft (register b))],
    all [first b,equalCells a (full b (side b) (clause b) .readLeft (register b)),equalCells b (full b (side b) (clause b) .readRight (register b))],
    all [last b,equalCells a (full b (side b) (clause b) .readRight (register b)),equalCells b (full b (side b) (clause b) .beforeGate (register b))],
    all [last b,equalCells a (full b (side b) (clause b) .beforeGate (register b)),equalCells b (full b (side b) (clause b) .afterGate (register b)),equal truth (.constant 1)],
    all [last b,equalCells a (full b (side b) (clause b) .afterGate (register b)),equalCells b (full b (side b) (clause b) .undoLeft (register b))],
    all [first b,equalCells a (full b (side b) (clause b) .undoLeft (register b)),equalCells b (full b (side b) (clause b) .undoRight (register b))],
    all [last b,equalCells a (full b (side b) (clause b) .undoRight (register b)),equalCells b (full b (side b) (clause b) .finish (register b))],
    all [last b,equalCells a (full b (side b) (clause a) .finish zeroReg),equalCells b (full b (side b) (clause b) .acquisition zeroReg),equal (.add (clause a) (.constant 1)) (clause b)],
    all [last b,equalCells a (full b (side b) (clause a) .finish zeroReg),equalCells b (full b (side b) (.constant 0) .success zeroReg),equal (.add (clause a) (.constant 1)) count],
    all [last b,equalCells a (full b (neg (side b)) (.constant 0) .success zeroReg),equalCells b (full b (side b) (.constant 0) .success zeroReg),equal (b.2 0) (.constant 0)]]

lemma unaryMove_exact {h : ℕ} (hh : 4≤h) {a b : Expr (ι:=ι)} {v : ι → ℕ} {c d : Cell (2^h)}
    (ha : evaluate a v=cellRecord c) (hb : evaluate b v=cellRecord d)
    (S : Schedule (2^h)) (count truth : Formula ι)
    (hc : count.eval v=(S.count d.metadata.task).val)
    (ht : truth.eval v=boolean ((S.clause d.metadata.task d.head.clause).truth d.head.reg)) :
    (unaryMove a b count truth).eval v≠0 ↔ Unary S c d := by
  have F (p : Phase) := full_represents hb (side b) (clause b) p (register b)
    d.head.side d.head.clause d.head.reg (side_exact hb) (clause_exact hb) (register_exact hb)
  have Z (p : Phase) := full_represents hb (side b) (.constant 0) p zeroReg
    d.head.side 0 0 (side_exact hb) (zeroClause_exact v) (zeroReg_exact v)
  have A (p : Phase) := full_represents hb (side b) (clause a) p zeroReg
    d.head.side c.head.clause 0 (side_exact hb) (clause_exact ha) (zeroReg_exact v)
  have B (p : Phase) := full_represents hb (side b) (clause b) p zeroReg
    d.head.side d.head.clause 0 (side_exact hb) (clause_exact hb) (zeroReg_exact v)
  have P (p : Phase) := full_represents hb (neg (side b)) (.constant 0) p zeroReg
    (!d.head.side) 0 0 (notSide_exact hb) (zeroClause_exact v) (zeroReg_exact v)
  rw [show Unary S c d ↔ Recognizer.UnaryTest S c d from ⟨Recognizer.unary_test,Recognizer.unary_of_test⟩]
  simp only [unaryMove,Formula.any_ne_zero,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,
    exists_eq_or_imp,exists_eq_left,forall_eq_or_imp,forall_eq,first_exact hb,last_exact hb,
    equals_exact hh ha (idle_represents hb _ _ (side_exact hb)),
    equals_exact hh hb (boundary_represents hb _ _ (side_exact hb)),
    equals_exact hh ha (boundary_represents hb _ _ (side_exact hb)),
    equals_exact hh ha (F _),equals_exact hh hb (F _),
    equals_exact hh hb (Z _),equals_exact hh ha (A _),
    equals_exact hh hb (B _),equals_exact hh ha (P _),
    Formula.equal_ne_zero,Formula.add_eval,Formula.constant_eval,clause_exact ha,clause_exact hb,hc,ht,
    boolean_eq_one,Recognizer.UnaryTest]
  simp only [represent_flag hb,cellRecord,flags,boolean_eq_zero]
  rfl

end

open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
end SourceBurnside.CellFormula

namespace SourceBurnside.PredicateFormula
section
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
open CellFormula
variable {ι : Type} [DecidableEq ι]

structure Table where
  count : CellFormula.Expr (ι:=ι) → Formula ι
  clause : CellFormula.Expr (ι:=ι) → Formula ι → ClauseFormula.Expr (ι:=ι)
def Table.Represents {q : ℕ} (P : Table (ι:=ι)) (v : ι → ℕ) (S : Schedule q) : Prop :=
  ∀a (c : Cell q), CellFormula.evaluate a v=cellRecord c →
    (P.count a).eval v=(S.count c.metadata.task).val ∧
    ∀j (J : Fin q),j.eval v=J.val → ClauseFormula.Represents (P.clause a j) v (S.clause c.metadata.task J)

def Table.truth (P : Table (ι:=ι)) (a : CellFormula.Expr (ι:=ι)) : Formula ι :=
  ClauseFormula.truth (P.clause a (CellFormula.clause a)) (register a)
def Table.delta (P : Table (ι:=ι)) (a b : CellFormula.Expr (ι:=ι)) : Fin 3 → Formula ι :=
  ClauseFormula.delta (P.clause a (CellFormula.clause b)) a
lemma Table.truth_exact {q : ℕ} (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule q}
    (hP : P.Represents v S) {a : CellFormula.Expr (ι:=ι)} {c : Cell q} (ha : CellFormula.evaluate a v=cellRecord c) :
    (P.truth a).eval v=boolean ((S.clause c.metadata.task c.head.clause).truth c.head.reg) :=
  ClauseFormula.truth_value ((hP a c ha).2 _ c.head.clause (clause_exact ha)) (register_exact ha)
lemma Table.delta_exact {q : ℕ} [NeZero q] (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule q}
    (hP : P.Represents v S) {a b : CellFormula.Expr (ι:=ι)} {c d : Cell q}
    (ha : CellFormula.evaluate a v=cellRecord c) (hb : CellFormula.evaluate b v=cellRecord d) (i : Fin 3) :
    (P.delta a b i).eval v=boolean (bit (c.delta (S.clause c.metadata.task d.head.clause) i)) :=
  ClauseFormula.delta_exact ((hP a c ha).2 _ d.head.clause (clause_exact hb)) ha i

def unaryRep (P : Table (ι:=ι)) (size : Formula ι) (a b : CellFormula.Expr (ι:=ι)) : Formula ι :=
  all [formats a size (P.count a),formats b size (P.count b),
    or (unaryMove a b (P.count b) (P.truth b)) (unaryMove b a (P.count a) (P.truth a))]
def binaryRep (P : Table (ι:=ι)) (size Q : Formula ι) (a b a' b' : CellFormula.Expr (ι:=ι)) : Formula ι :=
  all [formats a size (P.count a),formats b size (P.count b),formats a' size (P.count a'),formats b' size (P.count b'),
    or (binaryMove a b a' b' Q (P.delta a b) (P.delta a a))
      (binaryMove a' b' a b Q (P.delta a' b') (P.delta a' a'))]
lemma unaryRep_exact {h n : ℕ} (hh : 4≤h) (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule (2^h)}
    (hP : P.Represents v S) {size : Formula ι} (hs : size.eval v=n)
    {a b : CellFormula.Expr (ι:=ι)} {c d : Cell (2^h)}
    (ha : CellFormula.evaluate a v=cellRecord c) (hb : CellFormula.evaluate b v=cellRecord d) :
    (unaryRep P size a b).eval v≠0 ↔ Replacement S n [c] [d] := by
  rw [←Recognizer.replacementTest_iff]
  simp only [unaryRep,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    Formula.or_ne_zero,formats_exact ha S size (P.count a) n hs (hP a c ha).1,
    formats_exact hb S size (P.count b) n hs (hP b d hb).1,
    unaryMove_exact hh ha hb S (P.count b) (P.truth b) (hP b d hb).1 (P.truth_exact hP hb),
    unaryMove_exact hh hb ha S (P.count a) (P.truth a) (hP a c ha).1 (P.truth_exact hP ha),Recognizer.ReplacementTest]
lemma binaryRep_exact {h n : ℕ} (hh : 4≤h) (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule (2^h)}
    (hP : P.Represents v S) {size Q : Formula ι} (hs : size.eval v=n) (hQ : Q.eval v=2^h)
    {a b a' b' : CellFormula.Expr (ι:=ι)} {c d c' d' : Cell (2^h)}
    (ha : CellFormula.evaluate a v=cellRecord c) (hb : CellFormula.evaluate b v=cellRecord d)
    (ha' : CellFormula.evaluate a' v=cellRecord c') (hb' : CellFormula.evaluate b' v=cellRecord d') :
    (binaryRep P size Q a b a' b').eval v≠0 ↔ Replacement S n [c,d] [c',d'] := by
  rw [←Recognizer.replacementTest_iff]
  simp only [binaryRep,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    Formula.or_ne_zero,formats_exact ha S size (P.count a) n hs (hP a c ha).1,
    formats_exact hb S size (P.count b) n hs (hP b d hb).1,
    formats_exact ha' S size (P.count a') n hs (hP a' c' ha').1,
    formats_exact hb' S size (P.count b') n hs (hP b' d' hb').1,
    binaryMove_exact hh ha hb ha' hb' Q hQ S (P.delta a b) (P.delta a a) (P.delta_exact hP ha hb) (P.delta_exact hP ha ha),
    binaryMove_exact hh ha' hb' ha hb Q hQ S (P.delta a' b') (P.delta a' a') (P.delta_exact hP ha' hb') (P.delta_exact hP ha' ha'),
    Recognizer.ReplacementTest]
end

open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
def clauseCount (β g : ℕ) (T W : Formula ι) : Formula ι :=
  .add (.add (.mul (.constant (2*β)) W) (.mul (.constant (2*β)) (.sub T (.constant 1))))
    (.add (.mul (.mul (.constant (3*g+2*β)) (.sub W (.constant 2))) (.sub T (.constant 1))) (.constant β))
omit [DecidableEq ι] in
lemma clauseCount_exact (β g : ℕ) (T W : Formula ι) (v : ι → ℕ) :
    (clauseCount β g T W).eval v=Tableau.Layout.clauseCount β g (T.eval v) (W.eval v) := by
  simp [clauseCount,eval,Tableau.Layout.clauseCount,Nat.add_assoc]

def physical (β g : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank origin accept : Fin β → Bool) (encoding : Bool → Fin β → Bool)
    (T W O code codeLength H : Formula ι) : Table (ι:=ι) where
  count _ := clauseCount β g T W
  clause a j :=
    let initial := InitialFormula.cell blank origin encoding O
      (InitialFormula.inputPiece code codeLength H (.add (a.1 3) (.constant 1)) (a.2 0))
    ClauseFormula.choose (less j (clauseCount β g T W))
      (PhysicalFormula.clauseAt β g c output initial blank accept T W O j)
      PhysicalFormula.fallback

def initial {q β g T W : ℕ} (L : Addressable.Layout q β g T W)
    (blank origin : Fin β → Bool) (encoding : Bool → Fin β → Bool) (code : List Bool) (H : ℕ)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (task : Task) : Fin W → Fin β → Addressable.InputBit q :=
  InitialFormula.row blank origin encoding L.origin.val
    (InitialFormula.sourceInput code H (task.arity.val+1) task.zeroTask hd hdq (by omega) (by have := task.arity.isLt;omega))

lemma physical_exact {q β g T W H : ℕ} [NeZero q] (L : Addressable.Layout q β g T W)
    (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank origin accept : Fin β → Bool) (encoding : Bool → Fin β → Bool)
    (code : List Bool) (hd : 0<10000*H) (hdq : 10000*H≤q)
    {T' W' O C N H' : Formula ι} {v : ι → ℕ}
    (hT : T'.eval v=T) (hW : W'.eval v=W) (hO : O.eval v=L.origin.val)
    (hC : C.eval v=binaryValue code) (hN : N.eval v=code.length) (hH : H'.eval v=H) :
    (physical β g c output blank origin accept encoding T' W' O C N H').Represents v
      (L.schedule c output (initial L blank origin encoding code H hd hdq) blank accept) := by
  intro a A ha
  have hcount : (clauseCount β g T' W').eval v=Tableau.Layout.clauseCount β g T W := by
    rw [clauseCount_exact,hT,hW]
  refine ⟨hcount,?_⟩
  intro j J hj
  change ClauseFormula.Represents (ClauseFormula.choose _ _ _) v _
  by_cases hJ : J.val<Tableau.Layout.clauseCount β g T W
  · simp only [Addressable.Layout.schedule,dite_eq_left hJ]
    apply ClauseFormula.choose_true (by simp [hj,hcount,hJ])
    apply PhysicalFormula.clauseAt_exact L c output blank accept hT hW hO _ ⟨J.val,hJ⟩ hj
    intro p P hp r
    apply InitialFormula.cell_exact blank origin encoding P r hO hp
    apply InitialFormula.inputPiece_exact code A.metadata.zeroTask hd hdq _ _ hC hN hH
    · simp [eval,CellFormula.represent_int ha,cellRecord,integers,Meta.task]
    · simp [CellFormula.represent_flag ha,cellRecord,flags]
  · simp only [Addressable.Layout.schedule,dite_eq_right hJ]
    apply ClauseFormula.choose_false (by simp [less_eval,hj,hcount,hJ])
    exact ClauseFormula.unit_exact (ClauseFormula.fixedReading_exact (by rfl)) rfl
end SourceBurnside.PredicateFormula

namespace SourceBurnside.PredicateFormula
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
open CellFormula
variable {ι : Type} [DecidableEq ι]
omit [DecidableEq ι] in
lemma branch_value (c a b : Formula ι) (v : ι → ℕ) :
    (Formula.branch c a b).eval v=if c.eval v=0 then b.eval v else a.eval v := rfl
def valid (H W : Formula ι) : Formula ι := RawFormula.valid.bind ![H,W]
omit [DecidableEq ι] in
lemma valid_value {h : ℕ} (hh : 0<h) (w : Raw h) {H W : Formula ι} {v : ι → ℕ}
    (hH : H.eval v=h) (hW : W.eval v=natCode w) :
    (valid H W).eval v=boolean (decode hh w).isSome := by
  have hv : (fun i : Fin 2 => (![H,W] i).eval v)=RawFormula.inputs h (natCode w) := by
    funext i;fin_cases i <;> simp [RawFormula.inputs,hH,hW]
  rw [valid,bind_eval,hv]
  have hb := RawFormula.valid_boolean h (natCode w)
  have he := RawFormula.accepts_iff_decode hh w
  cases hd : decode hh w with
  | none => simp only [hd,Option.isSome_none,Bool.false_eq_true,iff_false] at he; simpa [hd,boolean] using (show RawFormula.valid.eval (RawFormula.inputs h (natCode w))=0 by omega)
  | some c => simp only [hd,Option.isSome_some] at he;simpa [hd,boolean] using he.mpr trivial

omit [DecidableEq ι] in
lemma rawRepresents {h : ℕ} (hh : 4≤h) (w : Raw h) {H W : Formula ι} {v : ι → ℕ}
    {c : Cell (2^h)} (hc : decode (by omega) w=some c) (hH : H.eval v=h) (hW : W.eval v=natCode w) :
    CellFormula.evaluate (CellFormula.ofRaw H W) v=cellRecord c := by
  apply ofRaw_represents hh c H W v hH
  rw [hW,(decode_eq_some_iff hh w c).mp hc]

def rawUnaryZero (P : Table (ι:=ι)) (H size W : Formula ι) : Formula ι :=
  let a := ofRaw H W
  .branch (valid H W) (unaryZero a size (P.count a) (P.truth a)) (.constant 1)
def rawBinaryZero (H Q W Z : Formula ι) : Formula ι :=
  .branch (and (valid H W) (valid H Z)) (binaryZero (ofRaw H W) (ofRaw H Z) Q) (.constant 0)
def rawUnaryRep (P : Table (ι:=ι)) (H size W Z : Formula ι) : Formula ι :=
  .branch (and (valid H W) (valid H Z)) (unaryRep P size (ofRaw H W) (ofRaw H Z)) (.constant 0)
def rawBinaryRep (P : Table (ι:=ι)) (H size Q W X Y Z : Formula ι) : Formula ι :=
  .branch (all [valid H W,valid H X,valid H Y,valid H Z])
    (binaryRep P size Q (ofRaw H W) (ofRaw H X) (ofRaw H Y) (ofRaw H Z)) (.constant 0)

lemma rawUnaryZero_exact {h n : ℕ} (hh : 4≤h) (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule (2^h)}
    (hP : P.Represents v S) {H size W : Formula ι} (w : Raw h)
    (hH : H.eval v=h) (hs : size.eval v=n) (hW : W.eval v=natCode w) :
    (rawUnaryZero P H size W).eval v≠0 ↔ Codec.unaryZero (by omega) S n w := by
  have hv := valid_value (show 0<h by omega) w hH hW
  cases hd : decode (show 0<h by omega) w with
  | none => simp [rawUnaryZero,branch_value,hv,hd,Codec.unaryZero]
  | some c =>
    have hc := rawRepresents hh w hd hH hW
    simpa only [rawUnaryZero,branch_value,hv,hd,Option.isSome_some,boolean_true,Nat.one_ne_zero,ite_false,Codec.unaryZero] using
      (unaryZero_exact hc S size (P.count (ofRaw H W)) (P.truth (ofRaw H W)) n hs (hP _ c hc).1 (P.truth_exact hP hc))
lemma rawBinaryZero_exact {h : ℕ} (hh : 4≤h) {v : ι → ℕ} {H Q W Z : Formula ι} (w z : Raw h)
    (hH : H.eval v=h) (hQ : Q.eval v=2^h) (hW : W.eval v=natCode w) (hZ : Z.eval v=natCode z) :
    (rawBinaryZero H Q W Z).eval v≠0 ↔ Codec.binaryZero (by omega) w z := by
  have hw := valid_value (show 0<h by omega) w hH hW
  have hz := valid_value (show 0<h by omega) z hH hZ
  cases hdw : decode (show 0<h by omega) w <;> cases hdz : decode (show 0<h by omega) z
  all_goals try simp [rawBinaryZero,branch_value,and_eval,hw,hz,hdw,hdz,Codec.binaryZero]
  rename_i c d
  have hc := rawRepresents hh w hdw hH hW
  have hd := rawRepresents hh z hdz hH hZ
  simpa only [rawBinaryZero,branch_value,and_eval,hw,hz,hdw,hdz,Option.isSome_some,boolean_true,Nat.one_ne_zero,ite_false,Codec.binaryZero] using
    (binaryZero_exact hc hd Q hQ)
lemma rawUnaryRep_exact {h n : ℕ} (hh : 4≤h) (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule (2^h)}
    (hP : P.Represents v S) {H size W Z : Formula ι} (w z : Raw h)
    (hH : H.eval v=h) (hs : size.eval v=n) (hW : W.eval v=natCode w) (hZ : Z.eval v=natCode z) :
    (rawUnaryRep P H size W Z).eval v≠0 ↔ Codec.replacement (by omega) S n [w] [z] := by
  have hw := valid_value (show 0<h by omega) w hH hW
  have hz := valid_value (show 0<h by omega) z hH hZ
  cases hdw : decode (show 0<h by omega) w <;> cases hdz : decode (show 0<h by omega) z
  all_goals try simp [rawUnaryRep,branch_value,and_eval,hw,hz,hdw,hdz,Codec.replacement,decodeWord]
  rename_i c d
  have hc := rawRepresents hh w hdw hH hW
  have hd := rawRepresents hh z hdz hH hZ
  simpa only [rawUnaryRep,branch_value,and_eval,hw,hz,hdw,hdz,Option.isSome_some,boolean_true,Nat.one_ne_zero,ite_false,
    Codec.replacement,decodeWord,Option.bind_some,Option.some.injEq] using
    (unaryRep_exact hh P hP hs hc hd)
end SourceBurnside.PredicateFormula

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
namespace SourceBurnside.PredicateFormula
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
open CellFormula
variable {ι : Type} [DecidableEq ι]
lemma rawBinaryRep_exact {h n : ℕ} (hh : 4≤h) (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule (2^h)}
    (hP : P.Represents v S) {H size Q W X Y Z : Formula ι} (w x y z : Raw h)
    (hH : H.eval v=h) (hs : size.eval v=n) (hQ : Q.eval v=2^h)
    (hW : W.eval v=natCode w) (hX : X.eval v=natCode x) (hY : Y.eval v=natCode y) (hZ : Z.eval v=natCode z) :
    (rawBinaryRep P H size Q W X Y Z).eval v≠0 ↔ Codec.replacement (by omega) S n [w,x] [y,z] := by
  have hw := valid_value (show 0<h by omega) w hH hW
  have hx := valid_value (show 0<h by omega) x hH hX
  have hy := valid_value (show 0<h by omega) y hH hY
  have hz := valid_value (show 0<h by omega) z hH hZ
  cases hdw : decode (show 0<h by omega) w <;> cases hdx : decode (show 0<h by omega) x <;>
    cases hdy : decode (show 0<h by omega) y <;> cases hdz : decode (show 0<h by omega) z
  all_goals try simp [rawBinaryRep,branch_value,all_eval,hw,hx,hy,hz,hdw,hdx,hdy,hdz,Codec.replacement,decodeWord]
  rename_i a b c d
  have ha := rawRepresents hh w hdw hH hW
  have hb := rawRepresents hh x hdx hH hX
  have hc := rawRepresents hh y hdy hH hY
  have hd := rawRepresents hh z hdz hH hZ
  simpa [rawBinaryRep,branch_value,all_eval,hw,hx,hy,hz,hdw,hdx,hdy,hdz,
    Codec.replacement,decodeWord] using (binaryRep_exact hh P hP hs hQ ha hb hc hd)

def normalEntry (P : Table (ι:=ι)) (H size Q len zeroTask : Formula ι)
    (data : Bool → Fin 2 → Formula ι) : Formula ι :=
  .branch zeroTask
    (.branch (equal len (.constant 1)) (rawUnaryZero P H size (data false 0))
      (.branch (equal len (.constant 2)) (rawBinaryZero H Q (data false 0) (data false 1)) (.constant 0)))
    (.branch (equal len (.constant 1)) (rawUnaryRep P H size (data false 0) (data true 0))
      (.branch (equal len (.constant 2)) (rawBinaryRep P H size Q (data false 0) (data false 1) (data true 0) (data true 1)) (.constant 0)))
lemma normalEntry_zero_one {h n : ℕ} (hh : 4≤h) (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule (2^h)}
    (hP : P.Represents v S) {H size Q len zeroTask : Formula ι} {data : Bool → Fin 2 → Formula ι}
    (w : Raw h) (hH : H.eval v=h) (hs : size.eval v=n) (hl : len.eval v=1) (hz : zeroTask.eval v=1)
    (hw : (data false 0).eval v=natCode w) :
    (normalEntry P H size Q len zeroTask data).eval v≠0 ↔ Codec.entry (by omega) S n true [w] []=true := by
  simpa [normalEntry,branch_value,hl,hz,Codec.entry,Codec.zero] using rawUnaryZero_exact hh P hP w hH hs hw
lemma normalEntry_zero_two {h n : ℕ} (hh : 4≤h) (P : Table (ι:=ι)) {v : ι → ℕ} (S : Schedule (2^h))
    {H size Q len zeroTask : Formula ι} {data : Bool → Fin 2 → Formula ι}
    (w x : Raw h) (hH : H.eval v=h) (hQ : Q.eval v=2^h) (hl : len.eval v=2) (hz : zeroTask.eval v=1)
    (hw : (data false 0).eval v=natCode w) (hx : (data false 1).eval v=natCode x) :
    (normalEntry P H size Q len zeroTask data).eval v≠0 ↔ Codec.entry (by omega) S n true [w,x] []=true := by
  simpa [normalEntry,branch_value,hl,hz,Codec.entry,Codec.zero] using rawBinaryZero_exact hh w x hH hQ hw hx
lemma normalEntry_rep_one {h n : ℕ} (hh : 4≤h) (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule (2^h)}
    (hP : P.Represents v S) {H size Q len zeroTask : Formula ι} {data : Bool → Fin 2 → Formula ι}
    (w y : Raw h) (hH : H.eval v=h) (hs : size.eval v=n) (hl : len.eval v=1) (hz : zeroTask.eval v=0)
    (hw : (data false 0).eval v=natCode w) (hy : (data true 0).eval v=natCode y) :
    (normalEntry P H size Q len zeroTask data).eval v≠0 ↔ Codec.entry (by omega) S n false [w] [y]=true := by
  simpa [normalEntry,branch_value,hl,hz,Codec.entry] using rawUnaryRep_exact hh P hP w y hH hs hw hy
lemma normalEntry_rep_two {h n : ℕ} (hh : 4≤h) (P : Table (ι:=ι)) {v : ι → ℕ} {S : Schedule (2^h)}
    (hP : P.Represents v S) {H size Q len zeroTask : Formula ι} {data : Bool → Fin 2 → Formula ι}
    (w x y z : Raw h) (hH : H.eval v=h) (hs : size.eval v=n) (hQ : Q.eval v=2^h)
    (hl : len.eval v=2) (hz : zeroTask.eval v=0)
    (hw : (data false 0).eval v=natCode w) (hx : (data false 1).eval v=natCode x)
    (hy : (data true 0).eval v=natCode y) (hz' : (data true 1).eval v=natCode z) :
    (normalEntry P H size Q len zeroTask data).eval v≠0 ↔ Codec.entry (by omega) S n false [w,x] [y,z]=true := by
  simpa [normalEntry,branch_value,hl,hz,Codec.entry] using rawBinaryRep_exact hh P hP w x y z hH hs hQ hw hx hy hz'
omit [DecidableEq ι] in
lemma normalEntry_other (P : Table (ι:=ι)) (H size Q len zeroTask : Formula ι) (data : Bool → Fin 2 → Formula ι)
    (v : ι → ℕ) (h1 : len.eval v≠1) (h2 : len.eval v≠2) :
    (normalEntry P H size Q len zeroTask data).eval v=0 := by
  simp [normalEntry,branch_value,equal_eval,h1,h2]
end SourceBurnside.PredicateFormula

namespace SourceBurnside.Structured.Device.Formula

variable {ι κ : Type} {M : ℕ} {v : ι → ℕ}
lemma exponents_less {a b : Formula ι} (ha : a.Exponents M v) (hb : b.Exponents M v) :
    (less a b).Exponents M v := by
  exact exponents_branch ⟨hb,ha⟩ (exponents_constant 0) (exponents_constant 1)
lemma exponents_or {a b : Formula ι} (ha : a.Exponents M v) (hb : b.Exponents M v) :
    (or a b).Exponents M v := exponents_branch ha (exponents_constant 1) hb
lemma exponents_implies {a b : Formula ι} (ha : a.Exponents M v) (hb : b.Exponents M v) :
    (implies a b).Exponents M v := exponents_branch ha hb (exponents_constant 1)
lemma exponents_any {es : List (Formula ι)} (H : ∀e∈es,e.Exponents M v) : (any es).Exponents M v := by
  induction es with
  | nil => exact exponents_constant 0
  | cons e es ih => exact exponents_or (H e (by simp)) (ih (by intro a ha;exact H a (by simp [ha])))
lemma exponents_bind (e : Formula κ) (f : κ → Formula ι)
    (hf : ∀i,(f i).Exponents M v) (he : e.Exponents M (fun i => (f i).eval v)) :
    (e.bind f).Exponents M v := by
  induction e with
  | read i => exact hf i
  | constant a => trivial
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | mod a b ha hb | le a b ha hb => exact ⟨ha he.1,hb he.2⟩
  | powTwo a ha => exact ⟨ha he.1,by simpa only [bind_eval] using he.2⟩
  | bitLength a ha => exact ha he
  | branch c a b hc ha hb =>
    refine ⟨hc he.1,?_⟩
    simp only [bind_eval]
    split <;> rename_i h
    · exact hb (by simpa only [ite_eq_left h] using he.2)
    · exact ha (by simpa only [ite_eq_right h] using he.2)
end SourceBurnside.Structured.Device.Formula

namespace SourceBurnside.RawFormula
open Structured.Device Structured.Device.Formula
lemma valid_exponents (h w M : ℕ) (hM : 64*h+8≤M) : valid.Exponents M (inputs h w) := by
  have Hs (i : Fin 32) : (slot i).Exponents M (inputs h w) := by
    apply exponents_field
    · trivial
    · exact ⟨trivial,trivial⟩
    · exact ⟨trivial,trivial⟩
    · change 2*i.val*h≤M
      have := i.isLt
      nlinarith
    · change 2*h≤M
      omega
  have Hb : bound.Exponents M (inputs h w) := ⟨trivial,by simpa using (show h≤M by omega)⟩
  have Hr : ranges.Exponents M (inputs h w) := by
    apply exponents_all
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro e he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact exponents_less (Hs _) (exponents_constant _)
    · exact exponents_less (Hs _) Hb
    · exact exponents_implies (exponents_equal (Hs _) (exponents_constant _)) (exponents_equal (Hs _) (exponents_constant _))
    · exact exponents_less (Hs _) (exponents_constant _)
    · exact exponents_less (Hs _) (exponents_constant _)
    · exact ⟨Hs _,Hs _⟩
    · exact exponents_less (Hs _) (exponents_constant _)
    · exact exponents_less (Hs _) Hb
    · exact exponents_implies (exponents_equal (Hs _) (exponents_constant _)) (exponents_equal (Hs _) (exponents_constant _))
    · exact exponents_less (Hs _) Hb
    · exact exponents_less (Hs _) (exponents_constant _)
  apply exponents_and Hr
  apply exponents_and
  · apply exponents_equal _ (exponents_constant _)
    apply exponents_field
    · trivial
    · exact ⟨trivial,trivial⟩
    · exact ⟨trivial,trivial⟩
    · change 18*h≤M;omega
    · change 46*h≤M;omega
  · apply exponents_equal _ (exponents_constant _)
    exact ⟨trivial,⟨⟨trivial,trivial⟩,trivial⟩,hM⟩
end SourceBurnside.RawFormula

namespace SourceBurnside.PredicateFormula
open Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
lemma valid_exponents {H W : Formula ι} (hH : H.Exponents M v) (hW : W.Exponents M v)
    (hM : 64*H.eval v+8≤M) : (valid H W).Exponents M v := by
  apply exponents_bind
  · intro i; fin_cases i <;> assumption
  · exact RawFormula.valid_exponents _ _ _ hM
end SourceBurnside.PredicateFormula

namespace SourceBurnside.InitialFormula
open Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
def Expr.Exponents (a : Expr (ι:=ι)) (M : ℕ) (v : ι → ℕ) :=
  a.tag.Exponents M v ∧ AddressFormula.Exponents a.address M v ∧ a.polarity.Exponents M v
lemma fixed_exponents {b : Formula ι} (hb : b.Exponents M v) : (fixed b).Exponents M v :=
  ⟨trivial,AddressFormula.certificate_exponents trivial,hb⟩
lemma data_exponents {a : AddressFormula.Expr (ι:=ι)} {b : Formula ι}
    (ha : AddressFormula.Exponents a M v) (hb : b.Exponents M v) : (data a b).Exponents M v := ⟨trivial,ha,hb⟩
lemma choose_exponents {c : Formula ι} {a b : Expr (ι:=ι)}
    (hc : c.Exponents M v) (ha : c.eval v≠0 → a.Exponents M v) (hb : c.eval v=0 → b.Exponents M v) :
    (choose c a b).Exponents M v := by
  by_cases h : c.eval v=0
  · have hb := hb h
    refine ⟨⟨hc,?_⟩,?_,⟨hc,?_⟩⟩
    · simpa only [ite_eq_left h] using hb.1
    · intro i;exact ⟨hc,by simpa only [ite_eq_left h] using hb.2.1 i⟩
    · simpa only [ite_eq_left h] using hb.2.2
  · have ha := ha h
    refine ⟨⟨hc,?_⟩,?_,⟨hc,?_⟩⟩
    · simpa only [ite_eq_right h] using ha.1
    · intro i;exact ⟨hc,by simpa only [ite_eq_right h] using ha.2.1 i⟩
    · simpa only [ite_eq_right h] using ha.2.2
lemma symbol_exponents (f : Bool → Bool) {a : Expr (ι:=ι)} (ha : a.Exponents M v) : (symbol f a).Exponents M v := by
  unfold symbol
  split
  · exact fixed_exponents trivial
  · refine ⟨ha.1,ha.2.1,?_⟩
    split
    · exact exponents_neg ha.2.2
    · exact ha.2.2

def Piece.Exponents (p : Piece (ι:=ι)) (M : ℕ) (v : ι → ℕ) :=
  p.length.Exponents M v ∧ ∀i : Formula ι,i.Exponents M v → i.eval v<p.length.eval v → (p.read i).Exponents M v
lemma Piece.append_exponents {a b : Piece (ι:=ι)} (ha : a.Exponents M v) (hb : b.Exponents M v) :
    (a.append b).Exponents M v := by
  refine ⟨⟨ha.1,hb.1⟩,?_⟩
  intro i hi hiv
  apply choose_exponents (exponents_less hi ha.1)
  · intro H
    apply ha.2 i hi
    simpa using H
  · intro H
    apply hb.2 (.sub i a.length) ⟨hi,ha.1⟩
    have H' : ¬i.eval v<a.length.eval v := by simpa using H
    change i.eval v-a.length.eval v<b.length.eval v
    change i.eval v<a.length.eval v+b.length.eval v at hiv
    omega
lemma fixedBits_exponents (bits : List Bool) (hM : 1≤M) (hlen : bits.length≤M+1) :
    (fixedBits (ι:=ι) bits).Exponents M v := by
  refine ⟨trivial,?_⟩
  intro i hi hiv
  apply fixed_exponents
  exact exponents_bit hM trivial hi (by change i.eval v<bits.length at hiv;omega)
lemma number_exponents {n : Formula ι} (hM : 1≤M) (hn : n.Exponents M v) (hv : binSize (n.eval v)≤M+1) :
    (number n).Exponents M v := by
  refine ⟨hn,?_⟩
  intro i hi hiv
  apply fixed_exponents
  apply exponents_bit
  · exact hM
  · exact hn
  · exact ⟨⟨hn,trivial⟩,hi⟩
  · change binSize (n.eval v)-1-i.eval v≤M
    omega
lemma ones_exponents {n : Formula ι} (hn : n.Exponents M v) : (ones n).Exponents M v :=
  ⟨hn,fun _ _ _ => fixed_exponents trivial⟩
lemma header_exponents {n : Formula ι} (hM : 1≤M) (hn : n.Exponents M v) (hv : binSize (n.eval v)≤M+1) :
    (header n).Exponents M v :=
  Piece.append_exponents (Piece.append_exponents (ones_exponents hn) (fixedBits_exponents [false] hM (by simp)))
    (number_exponents hM hn hv)
lemma bits_exponents {n len : Formula ι} (hM : 1≤M) (hn : n.Exponents M v) (hl : len.Exponents M v)
    (hv : len.eval v≤M+1) : (bits n len).Exponents M v := by
  refine ⟨hl,?_⟩
  intro i hi hiv
  exact fixed_exponents (exponents_bit hM hn hi (by change i.eval v<len.eval v at hiv;omega))
lemma single_exponents {b : Formula ι} (hb : b.Exponents M v) : (single b).Exponents M v :=
  ⟨trivial,fun _ _ _ => fixed_exponents hb⟩
lemma dataPiece_exponents {d l z : Formula ι} (hd : d.Exponents M v) (hl : l.Exponents M v) (hz : z.Exponents M v) :
    (dataPiece d l z).Exponents M v := by
  refine ⟨exponents_branch hz ⟨hl,hd⟩ ⟨trivial,hl,hd⟩,?_⟩
  intro i hi hiv
  exact data_exponents (AddressFormula.data_exponents ⟨⟨hl,hd⟩,hi⟩ ⟨⟨hi,hd⟩,hl⟩ ⟨hi,hd⟩) trivial
lemma inputPiece_exponents {code len H l z : Formula ι} (hM : 1≤M)
    (hc : code.Exponents M v) (hn : len.Exponents M v) (hH : H.Exponents M v) (hl : l.Exponents M v) (hz : z.Exponents M v)
    (hlen : len.eval v≤M+1) (hlenbits : binSize (len.eval v)≤M+1)
    (hHbits : binSize (H.eval v)≤M+1) (hlbits : binSize (l.eval v)≤M+1) :
    (inputPiece code len H l z).Exponents M v := by
  apply Piece.append_exponents
  · apply Piece.append_exponents
    · apply Piece.append_exponents
      · apply Piece.append_exponents
        · exact Piece.append_exponents (header_exponents hM hn hlenbits) (bits_exponents hM hc hn hlen)
        · exact header_exponents hM hH hHbits
      · exact header_exponents hM hl hlbits
    · exact single_exponents hz
  · exact dataPiece_exponents ⟨trivial,hH⟩ hl hz

lemma cell_exponents {β : ℕ} (blank origin : Fin β → Bool) (encoding : Bool → Fin β → Bool)
    {o j : Formula ι} {input : Piece (ι:=ι)} (r : Fin β)
    (ho : o.Exponents M v) (hj : j.Exponents M v) (hi : input.Exponents M v) :
    (cell blank origin encoding o input j r).Exponents M v := by
  have hk : (Formula.sub j (.add o (.constant 1))).Exponents M v := ⟨hj,ho,trivial⟩
  apply choose_exponents (exponents_equal hj ho)
  · intro _;exact fixed_exponents trivial
  · intro _
    apply choose_exponents (exponents_and (exponents_less ho hj) (exponents_less hk hi.1))
    · intro H
      apply symbol_exponents
      apply hi.2 _ hk
      exact by
        have H' := ((Formula.and_ne_zero _ _ _).mp H).2
        simpa using H'
    · intro _;exact fixed_exponents trivial
end SourceBurnside.InitialFormula

namespace SourceBurnside.ClauseFormula
open LocalSyntax FiniteTable CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
def Expr.Exponents (a : Expr (ι:=ι)) (M : ℕ) (v : ι → ℕ) :=
  (∀i,AddressFormula.Exponents (a.address i) M v) ∧ (∀r,(a.truth r).Exponents M v)
lemma matchReg_exponents {r : Fin 3 → Formula ι} (hr : ∀i,(r i).Exponents M v) (R : Reg) :
    (matchReg r R).Exponents M v := by
  apply exponents_all
  simp only [List.mem_ofFn]
  rintro e ⟨i,rfl⟩
  exact exponents_equal (hr _) (exponents_constant _)
lemma truth_exponents {a : Expr (ι:=ι)} {r : Fin 3 → Formula ι}
    (ha : a.Exponents M v) (hr : ∀i,(r i).Exponents M v) : (truth a r).Exponents M v := by
  apply exponents_any
  simp only [List.mem_map]
  rintro e ⟨R,_,rfl⟩
  exact exponents_and (matchReg_exponents hr R) (ha.2 _)
lemma delta_exponents {a : Expr (ι:=ι)} {c : CellFormula.Expr (ι:=ι)} (ha : a.Exponents M v)
    (hc : CellFormula.Exponents c M v) (i : Fin 3) : (delta a c i).Exponents M v :=
  AddressFormula.readAt_exponents (ha.1 _) hc
lemma choose_exponents {c : Formula ι} {a b : Expr (ι:=ι)}
    (hc : c.Exponents M v) (ha : a.Exponents M v) (hb : b.Exponents M v) : (choose c a b).Exponents M v :=
  ⟨fun i j => exponents_branch hc (ha.1 i j) (hb.1 i j),fun r => exponents_branch hc (ha.2 r) (hb.2 r)⟩
lemma lookup_exponents {i : Formula ι} {f : Expr (ι:=ι)} {xs : List (Expr (ι:=ι))}
    (hi : i.Exponents M v) (hf : f.Exponents M v) (hx : ∀x∈xs,x.Exponents M v) (n : ℕ) :
    (lookup i f n xs).Exponents M v := by
  induction xs generalizing n with
  | nil => exact hf
  | cons x xs ih =>
    exact choose_exponents (exponents_equal hi (exponents_constant n)) (hx x (by simp))
      (ih (by intro x h;exact hx x (by simp [h])) (n+1))
lemma truthTable_exponents (f : Reg → Bool) {r : Fin 3 → Formula ι} (hr : ∀i,(r i).Exponents M v) :
    (truthTable f r).Exponents M v :=
  truth_exponents ⟨fun _ => AddressFormula.certificate_exponents trivial,fun _ => trivial⟩ hr

def ReadingExpr.Exponents (a : ReadingExpr (ι:=ι)) (M : ℕ) (v : ι → ℕ) :=
  AddressFormula.Exponents a.address M v ∧ ∀b,(a.value b).Exponents M v
lemma fixedReading_exponents {b : Formula ι} (hb : b.Exponents M v) : (fixedReading b).Exponents M v :=
  ⟨AddressFormula.certificate_exponents trivial,fun _ => hb⟩
lemma addressReading_exponents {a : AddressFormula.Expr (ι:=ι)} (ha : AddressFormula.Exponents a M v) :
    (addressReading a).Exponents M v := ⟨ha,fun _ => trivial⟩
lemma make_exponents {w : Fin 3 → ReadingExpr (ι:=ι)} (f : (Fin 3 → Bool) → Bool)
    (hw : ∀i,(w i).Exponents M v) : (make w f).Exponents M v :=
  ⟨fun i => (hw i).1,fun _ => truthTable_exponents _ (fun i => (hw i).2 _)⟩
lemma unit_exponents {a : ReadingExpr (ι:=ι)} {b : Formula ι}
    (ha : a.Exponents M v) (hb : b.Exponents M v) : (unit a b).Exponents M v := by
  apply choose_exponents hb <;> apply make_exponents <;> intro i <;> fin_cases i <;> exact ha
lemma equalReading_exponents {a b : ReadingExpr (ι:=ι)} {k : Formula ι}
    (ha : a.Exponents M v) (hb : b.Exponents M v) (hk : k.Exponents M v) : (equalReading a b k).Exponents M v := by
  apply choose_exponents (exponents_equal hk (exponents_constant 0)) <;> apply make_exponents <;> intro i <;> fin_cases i
  all_goals first | exact ha | exact hb
lemma initialData_exponents {a : ReadingExpr (ι:=ι)} {p : AddressFormula.Expr (ι:=ι)} {n k : Formula ι}
    (ha : a.Exponents M v) (hp : AddressFormula.Exponents p M v) (hn : n.Exponents M v) (hk : k.Exponents M v) :
    (initialData a p n k).Exponents M v := by
  apply choose_exponents hn
  · apply choose_exponents (exponents_equal hk (exponents_constant 0)) <;> apply make_exponents <;> intro i <;> fin_cases i
    all_goals first | exact ha | exact addressReading_exponents hp
  · exact equalReading_exponents ha (addressReading_exponents hp) hk
lemma wire_exponents {n : ℕ} {a : Fin n → AddressFormula.Expr (ι:=ι)}
    (ha : ∀i,AddressFormula.Exponents (a i) M v) (w : Tableau.Wire n) : (wire a w).Exponents M v := by
  cases w with
  | inl b => exact fixedReading_exponents trivial
  | inr i => exact addressReading_exponents (ha i)
lemma circuitClause_exponents {n : ℕ} {a : Fin n → AddressFormula.Expr (ι:=ι)}
    (ha : ∀i,AddressFormula.Exponents (a i) M v) (C : Tableau.Circuit.Clause n) : (circuitClause a C).Exponents M v :=
  make_exponents C.truth (fun _ => wire_exponents ha _)
end SourceBurnside.ClauseFormula

namespace SourceBurnside.InitialFormula
open Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
lemma clauses_exponents {a : ClauseFormula.ReadingExpr (ι:=ι)} {b : Expr (ι:=ι)} {k : Formula ι}
    (ha : a.Exponents M v) (hb : b.Exponents M v) (hk : k.Exponents M v) :
    (clauses a b k).Exponents M v :=
  ClauseFormula.choose_exponents hb.1 (ClauseFormula.initialData_exponents ha hb.2.1 hb.2.2 hk)
    (ClauseFormula.unit_exponents ha hb.2.2)
end SourceBurnside.InitialFormula

namespace SourceBurnside.PhysicalFormula
open Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
lemma x_exponents (β : ℕ) {W t j r : Formula ι}
    (hW : W.Exponents M v) (ht : t.Exponents M v) (hj : j.Exponents M v) (hr : r.Exponents M v) :
    AddressFormula.Exponents (x β W t j r) M v := by
  apply AddressFormula.certificate_exponents
  exact ⟨⟨trivial,⟨hW,ht⟩,hj⟩,hr⟩
lemma y_exponents (β g : ℕ) {T W t j r : Formula ι}
    (hT : T.Exponents M v) (hW : W.Exponents M v) (ht : t.Exponents M v) (hj : j.Exponents M v) (hr : r.Exponents M v) :
    AddressFormula.Exponents (y β g T W t j r) M v := by
  apply AddressFormula.certificate_exponents
  exact ⟨⟨⟨trivial,hW⟩,hT⟩,⟨trivial,⟨⟨hW,trivial⟩,ht⟩,hj⟩,hr⟩
lemma localAddress_exponents (β g : ℕ) {T W t j : Formula ι}
    (hT : T.Exponents M v) (hW : W.Exponents M v) (ht : t.Exponents M v) (hj : j.Exponents M v)
    (i : Fin (3*β+g)) : AddressFormula.Exponents (localAddress β g T W t j i) M v := by
  refine Fin.addCases ?_ ?_ i
  · intro a;simp only [localAddress,Fin.addCases_left]
    exact x_exponents β hW ht ⟨hj,trivial⟩ trivial
  · intro a;simp only [localAddress,Fin.addCases_right]
    exact y_exponents β g hT hW ht hj trivial
lemma localClause_exponents (β g : ℕ) (c : Tableau.Circuit (3*β) g)
    (output : Fin β → Tableau.Wire (3*β+g)) {T W t j i : Formula ι}
    (hT : T.Exponents M v) (hW : W.Exponents M v) (ht : t.Exponents M v) (hj : j.Exponents M v) (hi : i.Exponents M v) :
    (localClause β g c output T W t j i).Exponents M v := by
  have hf : (ClauseFormula.unit (ι:=ι) (ClauseFormula.fixedReading (.constant 1)) (.constant 1)).Exponents M v :=
    ClauseFormula.unit_exponents (ClauseFormula.fixedReading_exponents trivial) trivial
  have ha := localAddress_exponents β g hT hW ht hj
  apply ClauseFormula.choose_exponents (exponents_less hi (exponents_constant _))
  · apply ClauseFormula.lookup_exponents hi hf
    simp only [List.mem_map]
    rintro e ⟨C,_,rfl⟩
    exact ClauseFormula.circuitClause_exponents ha C
  · apply ClauseFormula.lookup_exponents (by exact ⟨⟨hi,trivial⟩,trivial⟩) hf
    simp only [List.mem_ofFn]
    rintro e ⟨r,rfl⟩
    exact ClauseFormula.equalReading_exponents
      (ClauseFormula.addressReading_exponents (x_exponents β hW ⟨ht,trivial⟩ ⟨hj,trivial⟩ trivial))
      (ClauseFormula.wire_exponents ha _) ⟨⟨hi,trivial⟩,trivial⟩
lemma clauseIndex_exponents (β g : ℕ) {T W i : Formula ι}
    (hT : T.Exponents M v) (hW : W.Exponents M v) (hi : i.Exponents M v) (j : Fin 4) :
    (clauseIndex β g T W i j).Exponents M v := by
  fin_cases j <;> simp [clauseIndex,chooseIndex,less,Formula.Exponents,hT,hW,hi]
lemma fallback_exponents : (fallback (ι:=ι)).Exponents M v :=
  ClauseFormula.unit_exponents (ClauseFormula.fixedReading_exponents trivial) trivial
lemma initialFamily_exponents (β : ℕ) {init : Formula ι → Fin β → InitialFormula.Expr (ι:=ι)} {W j r k : Formula ι}
    (hW : W.Exponents M v) (hj : j.Exponents M v) (hr : r.Exponents M v) (hk : k.Exponents M v)
    (hinit : ∀s,(init j s).Exponents M v) : (initialFamily β init W j r k).Exponents M v := by
  apply ClauseFormula.lookup_exponents hr fallback_exponents
  simp only [List.mem_ofFn]
  rintro e ⟨s,rfl⟩
  exact InitialFormula.clauses_exponents (ClauseFormula.addressReading_exponents (x_exponents β hW trivial hj trivial)) (hinit s) hk
lemma boundaryFamily_exponents (β : ℕ) (blank : Fin β → Bool) {W t j r : Formula ι}
    (hW : W.Exponents M v) (ht : t.Exponents M v) (hj : j.Exponents M v) (hr : r.Exponents M v) :
    (boundaryFamily β blank W t j r).Exponents M v := by
  apply ClauseFormula.lookup_exponents hr fallback_exponents
  simp only [List.mem_ofFn]
  rintro e ⟨s,rfl⟩
  apply ClauseFormula.unit_exponents
  · apply ClauseFormula.addressReading_exponents
    apply x_exponents
    · exact hW
    · exact ⟨ht,trivial⟩
    · exact exponents_branch (exponents_equal hj (exponents_constant 0)) trivial ⟨hW,trivial⟩
    · trivial
  · trivial
lemma finalFamily_exponents (β : ℕ) (accept : Fin β → Bool) {T W O r : Formula ι}
    (hT : T.Exponents M v) (hW : W.Exponents M v) (hO : O.Exponents M v) (hr : r.Exponents M v) :
    (finalFamily β accept T W O r).Exponents M v := by
  apply ClauseFormula.lookup_exponents hr fallback_exponents
  simp only [List.mem_ofFn]
  rintro e ⟨s,rfl⟩
  exact ClauseFormula.unit_exponents (ClauseFormula.addressReading_exponents (x_exponents β hW ⟨hT,trivial⟩ hO trivial)) trivial
lemma familyClause_exponents (β g : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    {init : Formula ι → Fin β → InitialFormula.Expr (ι:=ι)} (blank accept : Fin β → Bool) {T W O : Formula ι} {e : Fin 4 → Formula ι}
    (hT : T.Exponents M v) (hW : W.Exponents M v) (hO : O.Exponents M v) (he : ∀i,(e i).Exponents M v)
    (hinit : ∀j,j.Exponents M v → ∀r,(init j r).Exponents M v) :
    (familyClause β g c output init blank accept T W O e).Exponents M v := by
  apply ClauseFormula.choose_exponents (exponents_equal (he _) (exponents_constant 0))
  · exact initialFamily_exponents β hW (he _) (he _) (he _) (hinit _ (he _))
  · apply ClauseFormula.choose_exponents (exponents_equal (he _) (exponents_constant 1))
    · exact boundaryFamily_exponents β blank hW (he _) (he _) (he _)
    · apply ClauseFormula.choose_exponents (exponents_equal (he _) (exponents_constant 2))
      · exact localClause_exponents β g c output hT hW (he _) (he _) (he _)
      · exact finalFamily_exponents β accept hT hW hO (he _)
lemma clauseAt_exponents (β g : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    {init : Formula ι → Fin β → InitialFormula.Expr (ι:=ι)} (blank accept : Fin β → Bool) {T W O i : Formula ι}
    (hT : T.Exponents M v) (hW : W.Exponents M v) (hO : O.Exponents M v) (hi : i.Exponents M v)
    (hinit : ∀j,j.Exponents M v → ∀r,(init j r).Exponents M v) :
    (clauseAt β g c output init blank accept T W O i).Exponents M v :=
  familyClause_exponents β g c output blank accept hT hW hO (clauseIndex_exponents β g hT hW hi) hinit
end SourceBurnside.PhysicalFormula

namespace SourceBurnside.CellFormula
open LocalSyntax Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
attribute [local simp] register_exponents zeroReg_exponents equalCells_exponents wing_exponents boundary_exponents full_exponents
  idle_exponents setChecker_exponents setColor_exponents skeletonPair_exponents
lemma unaryMove_exponents {a b : Expr (ι:=ι)} {count truth : Formula ι}
    (ha : Exponents a M v) (hb : Exponents b M v)
    (hc : count.Exponents M v) (ht : truth.Exponents M v) :
    (unaryMove a b count truth).Exponents M v := by
  have hra := register_exponents ha
  have hrb := register_exponents hb
  have hz : ∀ i, (zeroReg (ι:=ι) i).Exponents M v := zeroReg_exponents
  have h0 (p : FiniteTable.Phase) := full_exponents p hb (hb.2 1) (exponents_constant 0) hz
  have h1 (p : FiniteTable.Phase) := full_exponents p hb (hb.2 1) (hb.1 7) hrb
  have h2 (p : FiniteTable.Phase) := full_exponents p hb (hb.2 1) (ha.1 7) hz
  have h3 (p : FiniteTable.Phase) := full_exponents p hb (exponents_neg (hb.2 1)) (exponents_constant 0) hz
  simp [unaryMove,all,any,Formula.and,Formula.or,equal,first,last,side,clause,
    Formula.Exponents,ha,hb,ha.1,hb.1,hb.2,hc,ht,hz,h0,h1,h2,h3]
attribute [local simp] addReg_exponents
end SourceBurnside.CellFormula

namespace SourceBurnside.InitialFormula
lemma binSize_le_self (n : ℕ) : binSize n ≤ n+1 := by
  unfold binSize
  split
  · omega
  · apply Nat.size_le.mpr
    exact (Nat.lt_succ_self n).trans Nat.lt_two_pow_self
end SourceBurnside.InitialFormula

namespace SourceBurnside.PredicateFormula
section
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
def Table.Exponents (P : Table (ι:=ι)) (M : ℕ) (v : ι → ℕ) : Prop :=
  ∀a, CellFormula.Ready a M v → (P.count a).Exponents M v ∧
    ∀j,j.Exponents M v → (P.clause a j).Exponents M v
lemma Table.truth_exponents {P : Table (ι:=ι)} (hP : P.Exponents M v)
    {a : CellFormula.Expr (ι:=ι)} (ha : CellFormula.Ready a M v) : (P.truth a).Exponents M v :=
  ClauseFormula.truth_exponents ((hP a ha).2 _ (ha.1.1 _)) (fun _ => ha.1.2 _)
lemma Table.delta_exponents {P : Table (ι:=ι)} (hP : P.Exponents M v)
    {a b : CellFormula.Expr (ι:=ι)} (ha : CellFormula.Ready a M v) (hb : CellFormula.Ready b M v) (i : Fin 3) :
    (P.delta a b i).Exponents M v :=
  ClauseFormula.delta_exponents ((hP a ha).2 _ (hb.1.1 _)) ha.1 i
lemma clauseCount_exponents (β g : ℕ) {T W : Formula ι}
    (hT : T.Exponents M v) (hW : W.Exponents M v) : (clauseCount β g T W).Exponents M v := by
  simp [clauseCount,Formula.Exponents,hT,hW]
lemma physical_exponents (β g : ℕ) (c : Tableau.Circuit (3*β) g)
    (output : Fin β → Tableau.Wire (3*β+g)) (blank origin accept : Fin β → Bool)
    (encoding : Bool → Fin β → Bool) {T W O code codeLength H : Formula ι}
    (hM : 1≤M) (hT : T.Exponents M v) (hW : W.Exponents M v) (hO : O.Exponents M v)
    (hcode : code.Exponents M v) (hlen : codeLength.Exponents M v) (hH : H.Exponents M v)
    (hlenv : codeLength.eval v≤M) (hHv : H.eval v≤M) :
    (physical β g c output blank origin accept encoding T W O code codeLength H).Exponents M v := by
  intro a ha
  have hc := clauseCount_exponents β g hT hW
  refine ⟨hc,?_⟩
  intro j hj
  apply ClauseFormula.choose_exponents (exponents_less hj hc)
  · apply PhysicalFormula.clauseAt_exponents β g c output blank accept hT hW hO hj
    intro k hk r
    apply InitialFormula.cell_exponents blank origin encoding r hO hk
    apply InitialFormula.inputPiece_exponents hM hcode hlen hH
    · exact ⟨ha.1.1 _,trivial⟩
    · exact ha.1.2 _
    · omega
    · exact (InitialFormula.binSize_le_self _).trans (by omega)
    · exact (InitialFormula.binSize_le_self _).trans (by omega)
    · exact ha.2
  · exact PhysicalFormula.fallback_exponents
lemma unaryRep_exponents {P : Table (ι:=ι)} {size : Formula ι} {a b : CellFormula.Expr (ι:=ι)}
    (hP : P.Exponents M v) (hs : size.Exponents M v)
    (ha : CellFormula.Ready a M v) (hb : CellFormula.Ready b M v) :
    (unaryRep P size a b).Exponents M v := by
  apply exponents_all
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  intro e he
  rcases he with rfl|rfl|rfl
  · exact CellFormula.formats_exponents ha.1 hs (hP a ha).1
  · exact CellFormula.formats_exponents hb.1 hs (hP b hb).1
  · exact exponents_or (CellFormula.unaryMove_exponents ha.1 hb.1 (hP b hb).1 (Table.truth_exponents hP hb))
      (CellFormula.unaryMove_exponents hb.1 ha.1 (hP a ha).1 (Table.truth_exponents hP ha))
lemma binaryRep_exponents {P : Table (ι:=ι)} {size Q : Formula ι} {a b a' b' : CellFormula.Expr (ι:=ι)}
    (hP : P.Exponents M v) (hs : size.Exponents M v) (hQ : Q.Exponents M v)
    (ha : CellFormula.Ready a M v) (hb : CellFormula.Ready b M v)
    (ha' : CellFormula.Ready a' M v) (hb' : CellFormula.Ready b' M v) :
    (binaryRep P size Q a b a' b').Exponents M v := by
  apply exponents_all
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  intro e he
  rcases he with rfl|rfl|rfl|rfl|rfl
  · exact CellFormula.formats_exponents ha.1 hs (hP a ha).1
  · exact CellFormula.formats_exponents hb.1 hs (hP b hb).1
  · exact CellFormula.formats_exponents ha'.1 hs (hP a' ha').1
  · exact CellFormula.formats_exponents hb'.1 hs (hP b' hb').1
  · exact exponents_or (CellFormula.binaryMove_exponents ha.1 hb.1 ha'.1 hb'.1 hQ
        (Table.delta_exponents hP ha hb) (Table.delta_exponents hP ha ha))
      (CellFormula.binaryMove_exponents ha'.1 hb'.1 ha.1 hb.1 hQ
        (Table.delta_exponents hP ha' hb') (Table.delta_exponents hP ha' ha'))
end

open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} {M : ℕ} {v : ι → ℕ}
lemma rawUnaryZero_exponents {P : Table (ι:=ι)} {H size W : Formula ι}
    (hP : P.Exponents M v) (hH : H.Exponents M v) (hs : size.Exponents M v) (hW : W.Exponents M v)
    (hM : 64*H.eval v+8≤M) : (rawUnaryZero P H size W).Exponents M v := by
  have ha := CellFormula.ofRaw_ready hH hW hM
  exact exponents_branch (valid_exponents hH hW hM)
    (CellFormula.unaryZero_exponents ha.1 hs (hP _ ha).1 (Table.truth_exponents hP ha)) trivial
lemma rawBinaryZero_exponents {H Q W Z : Formula ι}
    (hH : H.Exponents M v) (hQ : Q.Exponents M v) (hW : W.Exponents M v) (hZ : Z.Exponents M v)
    (hM : 64*H.eval v+8≤M) : (rawBinaryZero H Q W Z).Exponents M v :=
  exponents_branch (exponents_and (valid_exponents hH hW hM) (valid_exponents hH hZ hM))
    (CellFormula.binaryZero_exponents (CellFormula.ofRaw_exponents hH hW hM)
      (CellFormula.ofRaw_exponents hH hZ hM) hQ) trivial
lemma rawUnaryRep_exponents {P : Table (ι:=ι)} {H size W Z : Formula ι}
    (hP : P.Exponents M v) (hH : H.Exponents M v) (hs : size.Exponents M v)
    (hW : W.Exponents M v) (hZ : Z.Exponents M v) (hM : 64*H.eval v+8≤M) :
    (rawUnaryRep P H size W Z).Exponents M v :=
  exponents_branch (exponents_and (valid_exponents hH hW hM) (valid_exponents hH hZ hM))
    (unaryRep_exponents hP hs (CellFormula.ofRaw_ready hH hW hM) (CellFormula.ofRaw_ready hH hZ hM)) trivial
lemma rawBinaryRep_exponents {P : Table (ι:=ι)} {H size Q W X Y Z : Formula ι}
    (hP : P.Exponents M v) (hH : H.Exponents M v) (hs : size.Exponents M v) (hQ : Q.Exponents M v)
    (hW : W.Exponents M v) (hX : X.Exponents M v) (hY : Y.Exponents M v) (hZ : Z.Exponents M v)
    (hM : 64*H.eval v+8≤M) : (rawBinaryRep P H size Q W X Y Z).Exponents M v := by
  apply exponents_branch
  · apply exponents_all
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro e he;rcases he with rfl|rfl|rfl|rfl
    · exact valid_exponents hH hW hM
    · exact valid_exponents hH hX hM
    · exact valid_exponents hH hY hM
    · exact valid_exponents hH hZ hM
  · exact binaryRep_exponents hP hs hQ (CellFormula.ofRaw_ready hH hW hM) (CellFormula.ofRaw_ready hH hX hM)
      (CellFormula.ofRaw_ready hH hY hM) (CellFormula.ofRaw_ready hH hZ hM)
  · trivial
lemma normalEntry_exponents {P : Table (ι:=ι)} {H size Q len zeroTask : Formula ι} {data : Bool → Fin 2 → Formula ι}
    (hP : P.Exponents M v) (hH : H.Exponents M v) (hs : size.Exponents M v) (hQ : Q.Exponents M v)
    (hl : len.Exponents M v) (hz : zeroTask.Exponents M v) (hd : ∀b i,(data b i).Exponents M v)
    (hM : 64*H.eval v+8≤M) : (normalEntry P H size Q len zeroTask data).Exponents M v := by
  apply exponents_branch hz
  · apply exponents_branch (exponents_equal hl (exponents_constant 1))
    · exact rawUnaryZero_exponents hP hH hs (hd _ _) hM
    · exact exponents_branch (exponents_equal hl (exponents_constant 2))
        (rawBinaryZero_exponents hH hQ (hd _ _) (hd _ _) hM) trivial
  · apply exponents_branch (exponents_equal hl (exponents_constant 1))
    · exact rawUnaryRep_exponents hP hH hs (hd _ _) (hd _ _) hM
    · exact exponents_branch (exponents_equal hl (exponents_constant 2))
        (rawBinaryRep_exponents hP hH hs hQ (hd _ _) (hd _ _) (hd _ _) (hd _ _) hM) trivial
end SourceBurnside.PredicateFormula

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
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured Structured.Device Structured.Device.Formula

def code : Formula Registers := .read 0
def codeLength : Formula Registers := .read 1
def height : Formula Registers := .read 2
def arity : Formula Registers := .read 3
def zeroTask : Formula Registers := .read 4
def word (b : Bool) (i : Fin 2) : Formula Registers :=
  .read ⟨5+(if b then 2 else 0)+i.val,by have := i.isLt;split <;> omega⟩
def time : Formula Registers := .powTwo (.div height (.constant 5))
def width : Formula Registers := .mul (.constant 4) time
def origin : Formula Registers := .mul (.constant 2) time
def size (D : ℕ) : Formula Registers := .mul (.constant (10000*D)) height
def bound : Formula Registers := .powTwo height
def nextHeight (D : ℕ) : Formula Registers := .mul (.constant D) height
def table (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) : PredicateFormula.Table (ι:=Registers) :=
  PredicateFormula.physical β g c output blank initial accept encoding time width origin code codeLength (nextHeight D)
def body (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) : Formula Registers :=
  PredicateFormula.normalEntry (table β g D c output blank initial accept encoding) height (size D) bound arity zeroTask word

lemma body_exponents (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) (v : Registers → ℕ) :
    (body β g D c output blank initial accept encoding).Exponents (exponentLimit D (v 2) (v 1)) v := by
  let M := exponentLimit D (v 2) (v 1)
  have hM : 64*v 2+8≤M := limit_height D (v 2) (v 1)
  have ht : time.Exponents M v := ⟨⟨trivial,trivial⟩,by change v 2 / 5≤M;exact (Nat.div_le_self _ _).trans (by omega)⟩
  apply PredicateFormula.normalEntry_exponents
  · apply PredicateFormula.physical_exponents β g c output blank initial accept encoding (by omega)
    · exact ht
    · exact ⟨trivial,ht⟩
    · exact ⟨trivial,ht⟩
    · trivial
    · trivial
    · exact ⟨trivial,trivial⟩
    · exact limit_code D (v 2) (v 1)
    · exact limit_next D (v 2) (v 1)
  · trivial
  · exact ⟨trivial,trivial⟩
  · exact ⟨trivial,by change v 2≤M;omega⟩
  · trivial
  · trivial
  · intro b i;trivial
  · exact hM

end SourceBurnside.LocalBody

namespace SourceBurnside.RawHeader
open Structured Structured.Program Structured.Binary

def request (h l : ℕ) (z : Bool) (data : List Bool) :=
  InitialFormula.enc h++InitialFormula.enc l++z::data
end SourceBurnside.RawHeader

namespace SourceBurnside.Structured.Binary
open Program
variable {K : Type*} [DecidableEq K]
def pushes (dst : K) : ℕ → Program K
  | 0 => .skip
  | n+1 => .seq (.push dst false) (pushes dst n)
lemma pushes_run (dst : K) (n : ℕ) (r : Store K) :
    Run (pushes dst n) r (n+1) (Function.update r dst (r dst++List.replicate n false)) := by
  induction n generalizing r with
  | zero => simpa [pushes] using Run.skip r
  | succ n ih =>
    let s := Function.update r dst (r dst++[false])
    have H := Run.seq (.push dst false) (pushes dst n) r s _ 1 (n+1)
      (Run.push _ _ _) (ih s)
    have he : Function.update s dst (s dst++List.replicate n false)=
        Function.update r dst (r dst++List.replicate (n+1) false) := by
      simp only [s,Function.update_self,Function.update_idem,List.replicate_succ,List.append_assoc,List.singleton_append]
    rw [he] at H
    convert H using 1 <;> first | rfl | omega

end SourceBurnside.Structured.Binary

namespace SourceBurnside.DropPadding
open Structured Structured.Program Structured.Binary
def step : Program K := .pop 1 (fun _ => .skip)
end SourceBurnside.DropPadding

namespace SourceBurnside.WrappedInput
open StackMachine UniversalStack
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K]

def specialize (t v : List Bool) : List Bool :=
  true::(InitialFormula.enc t.length++t++InitialFormula.enc v.length++v)
variable (src dst : K) (hne : src≠dst)
include hne

def envelope (a x : List Bool) : List Bool := InitialFormula.enc a.length++a++x

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
namespace SourceBurnside.Structured.Device.Formula
variable {ι : Type}
lemma exponents_mono {e : Formula ι} {m n : ℕ} {v : ι → ℕ} (hmn : m≤n) (he : e.Exponents m v) :
    e.Exponents n v := by
  induction e with
  | read i | constant a => trivial
  | add x y hx hy | sub x y hx hy | mul x y hx hy | div x y hx hy | mod x y hx hy | le x y hx hy =>
    exact ⟨hx he.1,hy he.2⟩
  | powTwo x hx => exact ⟨hx he.1,he.2.trans hmn⟩
  | bitLength x hx => exact hx he
  | branch c a b hc ha hb =>
    refine ⟨hc he.1,?_⟩
    split <;> rename_i h
    · exact hb (by simpa only [ite_eq_left h] using he.2)
    · exact ha (by simpa only [ite_eq_right h] using he.2)
end SourceBurnside.Structured.Device.Formula

namespace SourceBurnside.RawLocalBody
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured Structured.Device Structured.Device.Formula

def height : Formula Registers := .read 2
def length : Formula Registers := .mul (.constant 10000) height
def sideStart : Formula Registers := .branch (equal (.read 3) (.constant 1)) (.constant 1) (.constant 2)
def offset (b : Bool) (i : Fin 2) : Formula Registers :=
  .mul (.add (if b then sideStart else .constant 0) (.constant i.val)) length
def piece (b : Bool) (i : Fin 2) : Formula Registers := field (.read 5) (offset b i) length
def substitution : LocalBody.Registers → Formula Registers :=
  ![.read 0,.read 1,.read 2,.read 3,.read 4,piece false 0,piece false 1,piece true 0,piece true 1]
def body (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) : Formula Registers :=
  (LocalBody.body β g D c output blank initial accept encoding).bind substitution

def lengthOK : Formula Registers := and (less (.read 4) (.constant 2))
  (equal (.read 6) (.mul (.branch (.read 4) (.constant 1) (.constant 2)) (.mul (.read 3) length)))
def checkedBody (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) : Formula Registers :=
  and lengthOK (body β g D c output blank initial accept encoding)
lemma offset_eval_bound (b : Bool) (i : Fin 2) (v : Registers → ℕ) : (offset b i).eval v≤30000*v 2 := by
  have hi : i.val≤1 := by omega
  have he : sideStart.eval v≤2 := by
    by_cases hc : v 3=1 <;> simp [sideStart,eval,equal_eval,hc]
  cases b
  · change (0+i.val)*(10000*v 2)≤_;nlinarith
  · change (sideStart.eval v+i.val)*(10000*v 2)≤_;nlinarith
lemma pieces_exponents (D : ℕ) (v : Registers → ℕ) (b : Bool) (i : Fin 2) :
    (piece b i).Exponents (limit D (v 2) (v 1)) v := by
  apply exponents_field
  · trivial
  · exact ⟨⟨by cases b <;> first | trivial | exact exponents_branch (exponents_equal trivial trivial) trivial trivial,trivial⟩,trivial,trivial⟩
  · exact ⟨trivial,trivial⟩
  · apply le_trans (offset_eval_bound b i v);unfold limit;nlinarith
  · change 10000*v 2≤limit D (v 2) (v 1);unfold limit;nlinarith
lemma body_exponents (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) (v : Registers → ℕ) :
    (body β g D c output blank initial accept encoding).Exponents (limit D (v 2) (v 1)) v := by
  apply exponents_bind
  · intro i;fin_cases i
    all_goals first | trivial | exact pieces_exponents D v _ _
  · have H := LocalBody.body_exponents β g D c output blank initial accept encoding (fun i => (substitution i).eval v)
    apply exponents_mono _ H
    change LocalBody.exponentLimit D (v 2) (v 1)≤limit D (v 2) (v 1)
    unfold LocalBody.exponentLimit limit;nlinarith
lemma lengthOK_exponents (M : ℕ) (v : Registers → ℕ) : lengthOK.Exponents M v := by
  apply exponents_and
  · apply exponents_less <;> trivial
  · apply exponents_equal
    · trivial
    · exact ⟨exponents_branch trivial trivial trivial,⟨trivial,⟨trivial,trivial⟩⟩⟩
lemma checkedBody_exponents (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) (v : Registers → ℕ) :
    (checkedBody β g D c output blank initial accept encoding).Exponents (limit D (v 2) (v 1)) v :=
  exponents_and (lengthOK_exponents _ _) (body_exponents β g D c output blank initial accept encoding v)
end SourceBurnside.RawLocalBody

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

namespace SourceBurnside.RawPreparedInputs
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
open FiniteTable.Codec
def bound (D h : ℕ) (code data : List Bool) (l : ℕ) :=
  RawLocalBody.limit D h code.length+data.length+InitialFormula.binSize l
def semantic (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) : I → ℕ :=
  ![binaryValue code,code.length,h,l,CellRepr.boolean z,binaryValue data,data.length]
end SourceBurnside.RawPreparedInputs

namespace SourceBurnside.RawCompiled
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
variable {f : (Fin 7 → ℕ) → ℕ} {Pre : ℕ → (Fin 7 → ℕ) → Prop}
abbrev K (R : Realizer f Pre) := RawAssembler.K ⊕ R.W
end SourceBurnside.RawCompiled

namespace SourceBurnside.RawFit
open Structured Structured.Device Structured.Device.Formula
abbrev F := Formula (Fin 7)
def height : F := .read 2
def q : F := .powTwo height
def capacity : F := .powTwo (.mul (.constant 2) height)
def time : F := .powTwo (.div height (.constant 5))
def width : F := .mul (.constant 4) time
def nextHeight (D : ℕ) : F := .mul (.constant D) height
def payload (D : ℕ) : F := .mul (.constant 10000) (nextHeight D)
def binSize (x : F) : F := .branch x (.bitLength x) (.constant 1)
def certificate (β g : ℕ) : F :=
  .add (.mul (.mul (.constant β) width) time)
    (.mul (.mul (.constant g) (.sub width (.constant 2))) (.sub time (.constant 1)))
def clauses (β g : ℕ) : F :=
  .add (.add (.add (.mul (.constant (2*β)) width) (.mul (.constant (2*β)) (.sub time (.constant 1))))
    (.mul (.mul (.constant (3*g+2*β)) (.sub width (.constant 2))) (.sub time (.constant 1)))) (.constant β)

def inputLength (D : ℕ) : F :=
  .add (.add (.add (.add (.read 1) (.mul (.constant 2) (binSize (.read 1))))
    (.mul (.constant 2) (binSize (nextHeight D)))) (.constant 12)) (.mul (.constant 20) (payload D))

def fits (β g D : ℕ) : F := all [
  .le (.add (.mul (.constant 64) height) (.constant 512)) (.mul (.constant 10000) height),
  .le (.constant 10) capacity,
  .le q capacity,
  .le (payload D) q,
  .le (certificate β g) q,
  .le (clauses β g) q,
  less (inputLength D) (.div time (.constant 4))]
def trivialBody : F := all [RawLocalBody.lengthOK,equal (.read 3) (.constant 1),equal (.read 4) (.constant 1)]
def body (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) : F :=
  .branch (fits β g D) (RawLocalBody.checkedBody β g D c output blank initial accept encoding) trivialBody
@[simp] lemma binSize_eval (x : F) (v : Fin 7 → ℕ) : (binSize x).eval v=InitialFormula.binSize (x.eval v) := by
  by_cases h : x.eval v=0 <;> simp [binSize,eval,InitialFormula.binSize,h]
lemma fits_exponents (β g D M : ℕ) (v : Fin 7 → ℕ) (hM : 2*v 2 ≤ M) :
    (fits β g D).Exponents M v := by
  have hh : v 2 ≤ M := by omega
  have ht : v 2/5 ≤ M := (Nat.div_le_self _ _).trans hh
  have qb : q.Exponents M v := ⟨trivial,hh⟩
  have cb : capacity.Exponents M v := ⟨⟨trivial,trivial⟩,hM⟩
  have tb : time.Exponents M v := ⟨⟨trivial,trivial⟩,ht⟩
  have bsz (x : F) (hx : x.Exponents M v) : (binSize x).Exponents M v :=
    exponents_branch hx hx trivial
  have ib : (inputLength D).Exponents M v := by
    exact ⟨⟨⟨⟨trivial,⟨trivial,bsz _ trivial⟩⟩,⟨trivial,bsz _ ⟨trivial,trivial⟩⟩⟩,trivial⟩,
      ⟨trivial,⟨trivial,⟨trivial,trivial⟩⟩⟩⟩
  have ce : (certificate β g).Exponents M v :=
    ⟨⟨⟨trivial,⟨trivial,tb⟩⟩,tb⟩,⟨⟨trivial,⟨⟨trivial,tb⟩,trivial⟩⟩,⟨tb,trivial⟩⟩⟩
  have cl : (clauses β g).Exponents M v :=
    ⟨⟨⟨⟨trivial,⟨trivial,tb⟩⟩,⟨trivial,⟨tb,trivial⟩⟩⟩,
      ⟨⟨trivial,⟨⟨trivial,tb⟩,trivial⟩⟩,⟨tb,trivial⟩⟩⟩,trivial⟩
  apply exponents_all
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨⟨⟨trivial,trivial⟩,trivial⟩,⟨trivial,trivial⟩⟩
  · exact ⟨trivial,cb⟩
  · exact ⟨qb,cb⟩
  · exact ⟨⟨trivial,⟨trivial,trivial⟩⟩,qb⟩
  · exact ⟨ce,qb⟩
  · exact ⟨cl,qb⟩
  · exact exponents_less ib ⟨tb,trivial⟩
lemma trivial_exponents (M : ℕ) (v : Fin 7 → ℕ) : trivialBody.Exponents M v := by
  apply exponents_all
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl
  · exact RawLocalBody.lengthOK_exponents M v
  · exact exponents_equal trivial trivial
  · exact exponents_equal trivial trivial
lemma body_exponents (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) (v : Fin 7 → ℕ) :
    (body β g D c output blank initial accept encoding).Exponents (RawLocalBody.limit D (v 2) (v 1)) v := by
  apply exponents_branch
  · apply fits_exponents;unfold RawLocalBody.limit;nlinarith
  · exact RawLocalBody.checkedBody_exponents β g D c output blank initial accept encoding v
  · exact trivial_exponents _ _

def Fits (β g D h n : ℕ) : Prop :=
  let T := 2^(h/5)
  let W := 4*T
  64*h+512 ≤ 10000*h ∧ 10 ≤ 2^(2*h) ∧ 2^h ≤ 2^(2*h) ∧
  10000*(D*h) ≤ 2^h ∧
  β*W*T+g*(W-2)*(T-1) ≤ 2^h ∧
  2*β*W+2*β*(T-1)+(3*g+2*β)*(W-2)*(T-1)+β ≤ 2^h ∧
  n+2*InitialFormula.binSize n+2*InitialFormula.binSize (D*h)+12+20*(10000*(D*h)) < T/4
instance instDecidableFits (β g D h n : ℕ) : Decidable (Fits β g D h n) := inferInstanceAs (Decidable (_ ∧ _))
lemma fits_eval (β g D : ℕ) (v : Fin 7 → ℕ) :
    (fits β g D).eval v=if Fits β g D (v 2) (v 1) then 1 else 0 := by
  simp [fits,all_eval,certificate,clauses,inputLength,height,width,time,q,capacity,nextHeight,payload,
    eval,Fits]
  rfl
lemma fallback_eval (v : Fin 7 → ℕ) :
    trivialBody.eval v=if RawLocalBody.lengthOK.eval v≠0 ∧ v 3=1 ∧ v 4=1 then 1 else 0 := by
  simp [trivialBody,all_eval,eval]
lemma body_eval (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) (v : Fin 7 → ℕ) :
    (body β g D c output blank initial accept encoding).eval v=
      if Fits β g D (v 2) (v 1) then (RawLocalBody.checkedBody β g D c output blank initial accept encoding).eval v
      else if RawLocalBody.lengthOK.eval v≠0 ∧ v 3=1 ∧ v 4=1 then 1 else 0 := by
  by_cases h : Fits β g D (v 2) (v 1) <;> simp [body,eval,fits_eval,h,fallback_eval]
end SourceBurnside.RawFit

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

lemma words_update (r : Fin m → List Bool) (k : Fin m) (bs : List Bool) :
    words (registers (Function.update r k bs))=
      words ((registers r).take k.val)++block bs.reverse++words ((registers r).drop (k.val+1)) := by
  rw [registers_update,List.set_eq_take_append_cons_drop,ite_eq_left (by simp)]
  simp [List.append_assoc]

lemma encode_push (P : Q → Instr (Fin m) Bool Q) (C : Config (Fin m) Bool Q)
    (k : Fin m) (b : Bool) (q' : Q) (h : P C.state=.push k b q') :
    exec (machine P) (encode C) (ticks P C)=encode (next P C) := by
  have H := full_push P C.state q' k b h ((registers C.store).take k.val)
    (C.store k).reverse (words ((registers C.store).drop (k.val+1))) (by simp)
  have hs : words (registers C.store)=words ((registers C.store).take k.val)++
    block (C.store k).reverse++words ((registers C.store).drop (k.val+1)) := by
    conv_lhs => rw [registers_split C.store k]
    simp [List.append_assoc]
  simpa [encode,ticks,next,h,hs,words_update,List.reverse_append,List.reverse_cons] using H

lemma encode_pop (P : Q → Instr (Fin m) Bool Q) (C : Config (Fin m) Bool Q)
    (k : Fin m) (f : Option Bool → Q) (h : P C.state=.pop k f) :
    exec (machine P) (encode C) (ticks P C)=encode (next P C) := by
  have hs : words (registers C.store)=words ((registers C.store).take k.val)++
    block (C.store k).reverse++words ((registers C.store).drop (k.val+1)) := by
    conv_lhs => rw [registers_split C.store k]
    simp [List.append_assoc]
  generalize hb : (C.store k).reverse=bs
  have hl : C.store k=bs.reverse := by rw [←hb,List.reverse_reverse]
  cases bs with
  | nil =>
    have H := full_pop_nil P C.state k f h ((registers C.store).take k.val)
      (words ((registers C.store).drop (k.val+1))) (by simp)
    rw [hb] at hs
    simpa [encode,ticks,next,h,hs,words_update,hl] using H
  | cons b bs =>
    have H := full_pop_cons P C.state k f h ((registers C.store).take k.val) b bs
      (words ((registers C.store).drop (k.val+1))) (by simp)
    rw [hb] at hs
    simpa [encode,ticks,next,h,hs,words_update,hl,List.dropLast_reverse] using H

theorem encode_next (P : Q → Instr (Fin m) Bool Q) (C : Config (Fin m) Bool Q) :
    exec (machine P) (encode C) (ticks P C)=encode (next P C) := by
  cases h : P C.state with
  | halt => simp [ticks,h,exec,next]
  | push k b q => exact encode_push P C k b q h
  | pop k f => exact encode_pop P C k f h

theorem encode_exec (P : Q → Instr (Fin m) Bool Q) (C : Config (Fin m) Bool Q) (n : ℕ) :
    exec (machine P) (encode C) (clock P C n)=encode (exec P C n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [clock,UniversalStack.exec_from,ih,encode_next]
    rfl

end SourceBurnside.CompactStacks

namespace SourceBurnside.CompactInit
open Structured Structured.Program Structured.Binary
def store (todo acc : List Bool) : Store K := ![todo.reverse,acc]
def packet : Program K := .loop 0 (fun b => .seq (.push 1 true) (.push 1 b))
lemma push_run (x acc : List Bool) (b : Bool) :
    Run (.push (1:K) b) (store x acc) 1 (store x (acc++[b])) := by
  convert Run.push (store x acc) (1:K) b using 1
  all_goals try with_reducible_and_instances rfl
  funext j;fin_cases j <;> simp [store]
lemma packet_run (x acc : List Bool) :
    Run packet (store x acc) (3*x.length+1) (store [] (acc++pairs x)) := by
  induction x generalizing acc with
  | nil => simpa [packet,pairs,List.append_nil] using Run.loop_nil (store [] acc) (0:K) (fun b => .seq (.push 1 true) (.push 1 b)) rfl
  | cons b xs ih =>
    have he : Function.update (store (b::xs) acc) (0:K) xs.reverse=store xs acc := by
      funext j;fin_cases j <;> simp [store]
    have hb := Run.seq _ _ _ _ _ _ _ (push_run xs acc true) (push_run xs (acc++[true]) b)
    rw [←he] at hb
    have H := Run.loop_cons (store (b::xs) acc) (0:K) (fun b => .seq (.push 1 true) (.push 1 b))
      xs.reverse b (store xs ((acc++[true])++[b])) _ 2 (3*xs.length+1) (by simp [store]) hb
      (ih ((acc++[true])++[b]))
    convert H using 1 <;> simp [packet,pairs,List.append_assoc]
    omega
def program (m j : ℕ) : Program K :=
  .seq (pushes 1 j) (.seq packet (.seq (pushes 1 (m-j)) (move 1 0)))
lemma program_run (m j : ℕ) (x : List Bool) :
    Run (program m j) (store x [])
      ((j+1)+(3*x.length+1)+((m-j+1)+(2*(layout m j x).length+1)))
      (store (layout m j x) []) := by
  have h0 := pushes_run (1:K) j (store x [])
  have he0 : Function.update (store x []) (1:K) ([]++List.replicate j false)=store x (List.replicate j false) := by
    funext i;fin_cases i <;> simp [store]
  change Run (pushes (1:K) j) (store x []) (j+1) (Function.update (store x []) (1:K) ([]++List.replicate j false)) at h0
  rw [he0] at h0
  have h1 := packet_run x (List.replicate j false)
  have h2 := pushes_run (1:K) (m-j) (store [] (List.replicate j false++pairs x))
  have he2 : Function.update (store [] (List.replicate j false++pairs x)) (1:K)
      ((List.replicate j false++pairs x)++List.replicate (m-j) false)=store [] (layout m j x) := by
    funext i;fin_cases i <;> simp [store,layout]
  change Run _ _ _ (Function.update (store [] (List.replicate j false++pairs x)) (1:K)
      ((List.replicate j false++pairs x)++List.replicate (m-j) false)) at h2
  rw [he2] at h2
  have h3 := move_run (1:K) 0 (by decide) (store [] (layout m j x))
  have he3 : Function.update (Function.update (store [] (layout m j x)) (1:K) []) (0:K)
      ([]++(layout m j x).reverse)=store (layout m j x) [] := by
    funext i;fin_cases i <;> simp [store]
  change Run _ _ (2*(layout m j x).length+1) (Function.update (Function.update (store [] (layout m j x)) (1:K) []) (0:K)
      ([]++(layout m j x).reverse)) at h3
  rw [he3] at h3
  have H := Run.seq _ _ _ _ _ _ _ h0 (Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 h3))
  simpa only [program,Nat.add_assoc] using H
end SourceBurnside.CompactInit

namespace SourceBurnside.FixedArity
noncomputable section
open StackMachine Structured Structured.Program Structured.Binary
variable {A B Q Q' : Type*} [DecidableEq A] [DecidableEq B]
def liftConfig (f : Q → Q') (C : Config A Bool Q) : Config (Option A) Bool Q' := ⟨f C.state,extendStore C.store⟩
lemma lift_next (P : Q → Instr A Bool Q) (M : Q' → Instr (Option A) Bool Q') (f : Q → Q')
    (hf : ∀q,M (f q)=liftInstr f (P q)) (C : Config A Bool Q) :
    next M (liftConfig f C)=liftConfig f (next P C) := by
  cases h : P C.state <;> simp [next,liftConfig,hf,liftInstr,h,extendStore_update,extendStore]
lemma lift_exec (P : Q → Instr A Bool Q) (M : Q' → Instr (Option A) Bool Q') (f : Q → Q')
    (hf : ∀q,M (f q)=liftInstr f (P q)) (C : Config A Bool Q) (n : ℕ) :
    exec M (liftConfig f C) n=liftConfig f (exec P C n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [exec,ih,lift_next P M f hf];rfl
abbrev AnswerState (P : Program A) := Option P.Loc ⊕ Bool
def answerMachine (P : Program A) (out : A) : AnswerState P → Instr (Option A) Bool (AnswerState P)
  | .inl (some l) => mapInstr Sum.inl (P.operation l)
  | .inl none => .pop (some out) (fun b => .inr (b.getD false))
  | .inr _ => .halt
lemma answer_trace {P : Program A} {r s : Store A} {n : ℕ} (h : Run P r n s) (out : A) :
    exec (answerMachine P out) ⟨.inl (some P.start),extendStore r⟩ (n+1)=
      ⟨.inr ((s out).getLast?.getD false),Function.update (extendStore s) (some out) (s out).dropLast⟩ := by
  have H := compile_run h (answerMachine P out) Sum.inl (by intro l;rfl)
  rw [exec,H]
  rfl
lemma output_bit (y : List Bool) : Add.bit (y.getLast?.getD false)=Add.value y.reverse%2 := by
  rw [←List.head?_reverse]
  generalize y.reverse=z
  cases z with
  | nil => rfl
  | cons b z => cases b <;> simp [Add.value,Add.bit]
end
end SourceBurnside.FixedArity

namespace SourceBurnside.CompactProgram
noncomputable section
open StackMachine Structured Structured.Program FixedArity
variable {A : Type*} [DecidableEq A] {m : ℕ}
def inputStore (j : A) (x : List Bool) : Store A := Function.update (fun _ => []) j x.reverse
def virtual (e : Option A ≃ Fin m) (P : Program A) (out : A) := rename e (answerMachine P out)
def initial (e : Option A ≃ Fin m) (P : Program A) (j : A) (x : List Bool) :=
  renameConfig e (⟨.inl (some P.start),extendStore (inputStore j x)⟩ : Config (Option A) Bool (AnswerState P))
def boot (e : Option A ≃ Fin m) (j : A) := CompactInit.program m (e (some j)).val
abbrev State (e : Option A ≃ Fin m) (P : Program A) (j : A) :=
  (boot e j).Loc ⊕ CompactStacks.State m (AnswerState P)
def enter (e : Option A ≃ Fin m) (P : Program A) (j : A) : Option (boot e j).Loc → State e P j
  | some l => .inl l
  | none => .inr (.start (.inl (some P.start)))
def machine (e : Option A ≃ Fin m) (P : Program A) (j out : A) :
    State e P j → Instr (Option (Fin 2)) Bool (State e P j)
  | .inl l => mapInstr (enter e P j) ((boot e j).operation l)
  | .inr q => liftInstr Sum.inr (CompactStacks.machine (virtual e P out) q)
def initialConfig (e : Option A ≃ Fin m) (P : Program A) (j : A) (x : List Bool) :
    Config (Option (Fin 2)) Bool (State e P j) :=
  ⟨.inl (boot e j).start,extendStore (CompactInit.store x [])⟩
lemma initial_store (e : Option A ≃ Fin m) (P : Program A) (j : A) (x : List Bool) :
    (initial e P j x).store=Function.update (fun _ => []) (e (some j)) x.reverse := by
  change (extendStore (Function.update (fun _ => []) j x.reverse)) ∘ e.symm=_
  rw [extendStore_update,update_comp]
  congr 1
  funext a
  simp only [Function.comp_apply]
  cases e.symm a <;> simp [extendStore]
lemma boot_trace (e : Option A ≃ Fin m) (P : Program A) (j out : A) (x : List Bool) :
    exec (machine e P j out) (initialConfig e P j x) (bootTime e j x)=
      liftConfig Sum.inr (CompactStacks.encode (initial e P j x)) := by
  have H := compile_run (CompactInit.program_run m (e (some j)).val x)
    (machine e P j out) (enter e P j) (by intro l;rfl)
  change exec (machine e P j out) (initialConfig e P j x) (bootTime e j x)=_ at H
  rw [H]
  congr 1
  simp only [CompactStacks.encode,CompactStacks.config]
  rw [initial_store]
  change extendStore (CompactInit.store (CompactInit.layout m (e (some j)).val x) [])=
    extendStore ![(CompactStacks.words (CompactStacks.registers (Function.update (fun _ => []) (e (some j)) x.reverse))).reverse,[]]
  rw [CompactInit.layout_eq_words]
  rfl
lemma execution (e : Option A ≃ Fin m) (P : Program A) (j out : A) (x : List Bool) (n : ℕ) :
    exec (machine e P j out) (initialConfig e P j x)
      (bootTime e j x+CompactStacks.clock (virtual e P out) (initial e P j x) n)=
      liftConfig Sum.inr (CompactStacks.encode (exec (virtual e P out) (initial e P j x) n)) := by
  rw [UniversalStack.exec_from,boot_trace,
    lift_exec (CompactStacks.machine (virtual e P out)) (machine e P j out) Sum.inr (by intro q;rfl),
    CompactStacks.encode_exec]
lemma initial_length (e : Option A ≃ Fin m) (P : Program A) (j : A) (x : List Bool) (k : Fin m) :
    ((initial e P j x).store k).length ≤ x.length := by
  rw [initial_store]
  by_cases h : k=e (some j) <;> simp [h]
lemma time_bound (e : Option A ≃ Fin m) (P : Program A) (j out : A) (x : List Bool) (n : ℕ) :
    bootTime e j x+CompactStacks.clock (virtual e P out) (initial e P j x) n ≤
      3*m+7*x.length+4+n*(4*m*(2*(x.length+n)+1)+3) := by
  have hb := CompactInit.program_time_le (Nat.le_of_lt (e (some j)).isLt) x
  have hc := CompactStacks.clock_bound (virtual e P out) (initial e P j x) x.length (initial_length e P j x) n
  exact Nat.add_le_add hb hc
lemma answer_execution (e : Option A ≃ Fin m) {P : Program A} (j out : A) (x : List Bool)
    {n : ℕ} {s : Store A} (h : Run P (inputStore j x) n s) :
    (exec (machine e P j out) (initialConfig e P j x)
      (bootTime e j x+CompactStacks.clock (virtual e P out) (initial e P j x) (n+1))).state=
      .inr (.start (.inr ((s out).getLast?.getD false))) := by
  rw [execution]
  apply congrArg (fun q => Sum.inr (CompactStacks.State.start q))
  rw [show exec (virtual e P out) (initial e P j x) (n+1)=
    renameConfig e (exec (answerMachine P out) ⟨.inl (some P.start),extendStore (inputStore j x)⟩ (n+1)) from
      rename_exec e _ _ _,answer_trace h out]
  rfl
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

namespace SourceBurnside.LiteralCompiler
noncomputable section
open StackMachine Structured Structured.Program FixedArity
variable {A : Type*} [DecidableEq A] {m : ℕ}
def start (e : Option A ≃ Fin m) (P : Program A) (j : A) : CompactProgram.State e P j :=
  .inl (CompactProgram.boot e j).start
def result (e : Option A ≃ Fin m) (P : Program A) (j : A) : CompactProgram.State e P j → Bool
  | .inr (.start (.inr b)) => b
  | _ => false
def tokens (e : Option A ≃ Fin m) (P : Program A) (j out : A) :=
  UniversalStack.encodeProgram (FiniteCode.program (CompactProgram.machine e P j out) (start e P j) (result e P j))
def code (e : Option A ≃ Fin m) (P : Program A) (j out : A) : List Bool := WrappedInput.plain (tokens e P j out)
def loaderTime (ts : List (UniversalStack.Token K)) :=
  ((4*InitialFormula.binSize (WrappedInput.plain ts).length+3)+((UniversalInput.width K+1)*ts.length+
    UniversalInput.width K)+(2*ts.length+1))
def runTime (e : Option A ≃ Fin m) (P : Program A) (j out : A) (x : List Bool) (n : ℕ) :=
  CompactProgram.bootTime e j x+CompactStacks.clock (CompactProgram.virtual e P out) (CompactProgram.initial e P j x) (n+1)
lemma input_regs (x : List Bool) :
    extendStore (CompactInit.store x [])=UniversalInput.inputRegs src dst [] x := by
  funext k
  cases k with
  | none => simp [extendStore,UniversalInput.inputRegs,src,dst]
  | some k => fin_cases k <;> simp [extendStore,CompactInit.store,UniversalInput.inputRegs,src,dst]
lemma compiled_trace (e : Option A ≃ Fin m) {P : Program A} (j out : A) (x : List Bool)
    {n : ℕ} {s : Store A} (h : Run P (CompactProgram.inputStore j x) n s) :
    ∃ t r front back, t ≤ (runTime e P j out x n+1)*(5*(tokens e P j out).length+3) ∧
      exec UniversalStack.interpreter
        (UniversalStack.config .pick (UniversalInput.inputRegs src dst [] x) (tokens e P j out) [] 0) t=
        UniversalStack.config (.stopped ((s out).getLast?.getD false)) r front back 0 := by
  have H := CompactProgram.answer_execution e j out x h
  let M := CompactProgram.machine e P j out
  let C := CompactProgram.initialConfig e P j x
  have hh : M (exec M C (runTime e P j out x n)).state=.halt := by
    change CompactProgram.machine e P j out _=.halt
    rw [show (exec M C (runTime e P j out x n)).state=_ from H]
    rfl
  have hb : result e P j (exec M C (runTime e P j out x n)).state=(s out).getLast?.getD false := by
    rw [show (exec M C (runTime e P j out x n)).state=_ from H]
    rfl
  have HC := FiniteCode.program_trace M (start e P j) (result e P j)
    (extendStore (CompactInit.store x [])) (runTime e P j out x n) ((s out).getLast?.getD false) hh hb
  simpa only [tokens,input_regs] using HC
end
end SourceBurnside.LiteralCompiler

namespace SourceBurnside.LiteralCompiler
noncomputable section
open PolynomialAccounting
variable {A : Type*} [DecidableEq A] {m : ℕ}
def coefficient (m c din draw : ℕ) (spec : List Bool) (ts : List (UniversalStack.Token K)) :=
  2*draw+4+4*InitialFormula.binSize spec.length+loaderTime ts+
    (compactCoefficient m c din+1)*(5*ts.length+3)
lemma specialized_bound (e : Option A ≃ Fin m) (P : Structured.Program A) (j out : A) (v x : List Bool)
    (n S c din draw : ℕ) (hS : 1 ≤ S)
    (hx : (InitialFormula.enc v.length++v++x).length ≤ din*S)
    (hr : (WrappedInput.envelope (WrappedInput.specialize (code e P j out) v) x).length ≤ draw*S)
    (hn : n ≤ c*S^2) :
    (2*(WrappedInput.envelope (WrappedInput.specialize (code e P j out) v) x).length+1)+
        (4*InitialFormula.binSize (WrappedInput.specialize (code e P j out) v).length+3)+
        (loaderTime (tokens e P j out)+(runTime e P j out (InitialFormula.enc v.length++v++x) n+1)*
          (5*(tokens e P j out).length+3)) ≤
      coefficient m c din draw (WrappedInput.specialize (code e P j out) v) (tokens e P j out)*S^4 := by
  let xs := InitialFormula.enc v.length++v++x
  have hc := CompactProgram.time_bound e P j out xs (n+1)
  have HB := compact_bound m c din xs.length n S hS hx hn
  have hRun : runTime e P j out xs n ≤ compactCoefficient m c din*S^4 := hc.trans HB
  have hI := interpreter_bound (runTime e P j out xs n) (compactCoefficient m c din)
    (5*(tokens e P j out).length+3) S hS hRun
  have hs4 := (powers S hS).2.2.1
  have hs14 := (powers S hS).2.2.2.2
  have hRaw := hr.trans (Nat.mul_le_mul_left draw hs14)
  have hconst := Nat.mul_le_mul_left
    (4+4*InitialFormula.binSize (WrappedInput.specialize (code e P j out) v).length+loaderTime (tokens e P j out)) hs4
  unfold coefficient
  change _ ≤ (2*draw+4+4*InitialFormula.binSize (WrappedInput.specialize (code e P j out) v).length+
    loaderTime (tokens e P j out)+(compactCoefficient m c din+1)*(5*(tokens e P j out).length+3))*S^4
  nlinarith only [hI,hRaw,hconst]
end
end SourceBurnside.LiteralCompiler

namespace SourceBurnside.RawFixedPoint
noncomputable section
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
lemma body_exponents (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool)
    (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) :
    (RawFit.body β g D c output blank initial accept encoding).Exponents
      (RawPreparedInputs.bound D h code data l) (RawPreparedInputs.semantic code h l z data) := by
  apply exponents_mono _ (RawFit.body_exponents β g D c output blank initial accept encoding (RawPreparedInputs.semantic code h l z data))
  change RawLocalBody.limit D h code.length ≤ RawPreparedInputs.bound D h code data l
  unfold RawPreparedInputs.bound;omega
lemma body_boolean (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) (v : Fin 7 → ℕ) :
    (RawFit.body β g D c output blank initial accept encoding).eval v ≤ 1 := by
  have Hbody : (RawLocalBody.body β g D c output blank initial accept encoding).eval v ≤ 1 := by
    rw [RawLocalBody.body,bind_eval]
    unfold LocalBody.body
    simp only [PredicateFormula.normalEntry,PredicateFormula.rawUnaryZero,PredicateFormula.rawBinaryZero,
      PredicateFormula.rawUnaryRep,PredicateFormula.rawBinaryRep,PredicateFormula.unaryRep,PredicateFormula.binaryRep,
      CellFormula.unaryZero,CellFormula.binaryZero,PredicateFormula.branch_value,all_eval,any_eval]
    split_ifs <;> norm_num [eval]
  rw [RawFit.body_eval]
  split
  · simp only [RawLocalBody.checkedBody,and_eval];split <;> omega
  · split <;> omega

end
end SourceBurnside.RawFixedPoint

namespace SourceBurnside.Tableau

namespace Formula
variable {n m : ℕ}
def eval (v : Fin n → Bool) : Formula n → Bool
  | .constant b => b
  | .input i => v i
  | .nand a b => Tableau.nand (a.eval v) (b.eval v)
def map (f : Fin n → Fin m) : Formula n → Formula m
  | .constant b => .constant b
  | .input i => .input (f i)
  | .nand a b => .nand (a.map f) (b.map f)
@[simp] lemma eval_map (f : Fin n → Fin m) (a : Formula n) (v : Fin m → Bool) :
    (a.map f).eval v=a.eval (v ∘ f) := by induction a <;> simp_all [map,eval]
def neg (a : Formula n) : Formula n := .nand a a
def conj (a b : Formula n) : Formula n := neg (.nand a b)
def disj (a b : Formula n) : Formula n := .nand a.neg b.neg
def mux (b x y : Formula n) : Formula n := (b.conj x).disj (b.neg.conj y)
lemma eval_mux (b x y : Formula n) (v : Fin n → Bool) :
    (mux b x y).eval v = if b.eval v then x.eval v else y.eval v := by
  unfold mux conj disj neg
  simp only [eval]
  cases b.eval v <;> cases x.eval v <;> cases y.eval v <;> decide

theorem represents (f : (Fin n → Bool) → Bool) : ∃ a : Formula n, ∀ v, a.eval v=f v := by
  induction n with
  | zero =>
    refine ⟨.constant (f Fin.elim0),?_⟩
    intro v
    have hv : v=Fin.elim0 := funext (fun i => Fin.elim0 i)
    simp [eval,hv]
  | succ n ih =>
    obtain ⟨a,ha⟩ := ih (fun v => f (Fin.cons true v))
    obtain ⟨b,hb⟩ := ih (fun v => f (Fin.cons false v))
    refine ⟨mux (.input 0) (a.map Fin.succ) (b.map Fin.succ),?_⟩
    intro v
    rw [eval_mux,eval_map,eval_map,ha,hb]
    change (if v 0 then f (Fin.cons true (v ∘ Fin.succ)) else
      f (Fin.cons false (v ∘ Fin.succ)))=f v
    have he : Fin.cons (v 0) (v ∘ Fin.succ)=v := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    cases hh : v 0 <;> simpa only [hh,Bool.false_eq_true,ite_false,ite_true] using congrArg f he
end Formula

namespace Circuit
variable {I g h k : ℕ}

def rename (le : g≤h) (w : Wire (I+g)) : Wire (I+h) :=
  w.map id (Fin.castLE (Nat.add_le_add_left le I))

structure Extension (c : Circuit I g) (d : Circuit I h) : Prop where
  le : g≤h
  agree : ∀ v i, d.evaluate v (Fin.castLE (Nat.add_le_add_left le I) i)=c.evaluate v i

lemma Extension.refl (c : Circuit I g) : Extension c c := ⟨le_refl _,fun _ _ => rfl⟩
lemma Extension.trans {c : Circuit I g} {d : Circuit I h} {e : Circuit I k}
    (hc : Extension c d) (hd : Extension d e) : Extension c e := by
  refine ⟨hc.le.trans hd.le,?_⟩
  intro v i
  have he := hd.agree v (Fin.castLE (Nat.add_le_add_left hc.le I) i)
  exact he.trans (hc.agree v i)
lemma extension_snoc (c : Circuit I g) (a b : Wire (I+g)) : Extension c (c.snoc a b) := by
  refine ⟨Nat.le_succ g,?_⟩
  intro v i
  change Fin.lastCases (motive:=fun _ => Bool) _ (c.evaluate v) (Fin.castSucc i)=_
  exact Fin.lastCases_castSucc i
lemma Extension.wire {c : Circuit I g} {d : Circuit I h} (he : Extension c d)
    (w : Wire (I+g)) (v : Fin I → Bool) : (rename he.le w).eval (d.evaluate v)=w.eval (c.evaluate v) := by
  cases w with
  | inl b => rfl
  | inr i => exact he.agree v i

theorem compile_formula {n : ℕ} (a : Formula n) (c : Circuit I g)
    (env : Fin n → Wire (I+g)) : ∃ h, ∃ d : Circuit I h, ∃ _ : Extension c d,
      ∃ w : Wire (I+h), ∀ v, w.eval (d.evaluate v)=a.eval (fun i => (env i).eval (c.evaluate v)) := by
  induction a generalizing g with
  | constant b => exact ⟨g,c,Extension.refl c,.inl b,fun _ => rfl⟩
  | input i => exact ⟨g,c,Extension.refl c,env i,fun _ => rfl⟩
  | nand a b ia ib =>
    obtain ⟨g₁,c₁,e₁,w₁,hw₁⟩ := ia c env
    let env₁ := fun i => rename e₁.le (env i)
    obtain ⟨g₂,c₂,e₂,w₂,hw₂⟩ := ib c₁ env₁
    let w₁' := rename e₂.le w₁
    refine ⟨g₂+1,c₂.snoc w₁' w₂,(e₁.trans e₂).trans (extension_snoc _ _ _),
      .inr (Fin.last _),?_⟩
    intro v
    change Fin.lastCases (motive:=fun _ => Bool) _ _ (Fin.last _)=_
    rw [Fin.lastCases_last]
    rw [e₂.wire w₁ v,hw₁ v,hw₂ v]
    have hen : (fun i => (env₁ i).eval (c₁.evaluate v))=fun i => (env i).eval (c.evaluate v) := by
      funext i; exact e₁.wire (env i) v
    rw [hen]
    rfl

theorem compile_outputs {n m : ℕ} (a : Fin m → Formula n) (c : Circuit I g)
    (env : Fin n → Wire (I+g)) : ∃ h, ∃ d : Circuit I h, ∃ _ : Extension c d,
      ∃ w : Fin m → Wire (I+h), ∀ v r,
        (w r).eval (d.evaluate v)=(a r).eval (fun i => (env i).eval (c.evaluate v)) := by
  induction m with
  | zero => exact ⟨g,c,Extension.refl c,Fin.elim0,fun _ r => Fin.elim0 r⟩
  | succ m ih =>
    obtain ⟨g₁,c₁,e₁,w₁,hw₁⟩ := ih (fun r => a r.castSucc)
    let env₁ := fun i => rename e₁.le (env i)
    obtain ⟨g₂,c₂,e₂,w₂,hw₂⟩ := compile_formula (a (Fin.last m)) c₁ env₁
    refine ⟨g₂,c₂,e₁.trans e₂,Fin.lastCases w₂ (fun r => rename e₂.le (w₁ r)),?_⟩
    intro v r
    refine Fin.lastCases ?_ (fun j => ?_) r
    · simp only [Fin.lastCases_last]
      rw [hw₂]
      congr 1
      funext i
      exact e₁.wire (env i) v
    · simp only [Fin.lastCases_castSucc]
      rw [e₂.wire,hw₁]

end Circuit

theorem exists_nand_circuit {n m : ℕ} (f : (Fin n → Bool) → Fin m → Bool) :
    ∃ g, ∃ c : Circuit n g, ∃ out : Fin m → Wire (n+g),
      ∀ v r, (out r).eval (c.evaluate v)=f v r := by
  classical
  choose a ha using fun r => Formula.represents (fun v => f v r)
  obtain ⟨g,c,_,out,ho⟩ := Circuit.compile_outputs a (Circuit.nil (inputs:=n)) (fun i => .inr i)
  refine ⟨g,c,out,?_⟩
  intro v r
  exact (ho v r).trans (ha r v)

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

namespace Coding
section
variable [Fintype Γ] [Fintype Q]

noncomputable def oneHot (blank : Γ) : Coding Γ Q where
  bits := Fintype.card (Label Γ Q)
  positive := Fintype.card_pos_iff.mpr ⟨⟨blank,false,none⟩⟩
  encode := oneHotEncode
  decode v := if hv : ∃ a, oneHotEncode a=v then Classical.choose hv else ⟨blank,false,none⟩
  decode_encode a := by
    rw [dite_eq_left (show ∃ b, oneHotEncode b=oneHotEncode a from ⟨a,rfl⟩)]
    exact oneHotEncode_injective (Classical.choose_spec
      (show ∃ b, oneHotEncode b=oneHotEncode a from ⟨a,rfl⟩))
end

variable (K : Coding Γ Q)

structure Realization (δ : Q → Γ → Command Γ Q) where
  gates : ℕ
  circuit : Tableau.Circuit (3*K.bits) gates
  output : Fin K.bits → Tableau.Wire (3*K.bits+gates)
  correct : ∀ v r, (output r).eval (circuit.evaluate v)=K.transition δ v r

noncomputable def realization (δ : Q → Γ → Command Γ Q) : K.Realization δ :=
  Classical.choice (by
    obtain ⟨g,c,out,hc⟩ := Tableau.exists_nand_circuit (K.transition δ)
    exact ⟨⟨g,c,out,hc⟩⟩)

theorem local_trace (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) (origin t j : ℕ) :
    K.transition δ (Rectangle.neighborhood (K.trace δ C origin t) j)=
      K.trace δ C origin (t+1) (j+1) := by
  have hex (b : Fin 3) : K.decode (fun r =>
      Rectangle.neighborhood (K.trace δ C origin t) j (finProdFinEquiv (b,r)))=
      (run δ C t).cell ((j+b.val:ℕ)- (origin:ℤ)) := by
    simp only [Rectangle.neighborhood,Equiv.symm_apply_apply,trace,K.decode_encode]
  dsimp only [transition]
  rw [hex 0,hex 1,hex 2]
  simp only [Fin.val_zero,Fin.val_one,Fin.val_two]
  have h₁ : ((j+1:ℕ):ℤ)-(origin:ℤ)-1=(j:ℤ)-(origin:ℤ) := by push_cast; ring
  have h₂ : ((j+1:ℕ):ℤ)-(origin:ℤ)+1=((j+2:ℕ):ℤ)-(origin:ℤ) := by push_cast; ring
  have he := local_cell δ (run δ C t) (((j+1:ℕ):ℤ)-(origin:ℤ))
  rw [h₁,h₂] at he
  simpa only [Nat.add_zero,trace,run] using congrArg K.encode he
end Coding

namespace Coding
variable (K : Coding Γ Q)

theorem rectangle_valid (δ : Q → Γ → Command Γ Q) (M : K.Realization δ)
    (C : Config Γ Q) (blank : Γ) (T : ℕ) (hT : 0<T) (hp : C.position=0)
    (hl : C.tape (-(2*(T:ℤ)))=blank) (hr : C.tape (2*(T:ℤ)-1)=blank) :
    Rectangle.Valid M.circuit M.output T (4*T) (K.encode ⟨blank,false,none⟩)
      (K.trace δ C (2*T) 0) (K.trace δ C (2*T))
      (fun t j v => M.circuit.evaluate (Rectangle.neighborhood (K.trace δ C (2*T) t) j)
        (Fin.natAdd (3*K.bits) v)) := by
  refine ⟨fun _ _ => rfl,?_,?_,?_⟩
  · intro t ht j hj he
    exact K.boundary_trace δ C blank T hT hp hl hr (t+1) ht j he
  · intro t ht j hj
    rw [Rectangle.assignment_evaluate]
    exact M.circuit.evaluate_satisfies _
  · intro t ht j hj r
    rw [Rectangle.assignment_evaluate,M.correct]
    exact (congrFun (K.local_trace δ C (2*T) t j) r).symm

end Coding
end SourceBurnside.OneTape

namespace SourceBurnside.OneTape
section
open Tableau Addressable
variable {Γ Q : Type*} {q : ℕ}

structure Input where
  content : List (InputBit q)
  blank : Γ
  origin : Γ
  bitSymbol : Bool → Γ
  start : Q

namespace Input
variable (A : Input (Γ:=Γ) (Q:=Q) (q:=q))
def symbol (v : FiniteTable.Address q → Bool) (j : ℤ) : Γ :=
  if j=0 then A.origin else
    if hj : 0<j.toNat ∧ j.toNat≤A.content.length then
      A.bitSymbol ((A.content[j.toNat-1]'(by omega)).eval v)
    else A.blank

def config (v : FiniteTable.Address q → Bool) : Config Γ Q := ⟨0,A.start,A.symbol v⟩

def reading (K : Coding Γ Q) (j : ℤ) (r : Fin K.bits) : InputBit q :=
  if j=0 then .fixed (K.encode ⟨A.origin,true,some A.start⟩ r) else
    if hj : 0<j.toNat ∧ j.toNat≤A.content.length then
      (A.content[j.toNat-1]'(by omega)).mapBool
        (fun b => K.encode ⟨A.bitSymbol b,false,none⟩ r)
    else .fixed (K.encode ⟨A.blank,false,none⟩ r)

lemma reading_eval (K : Coding Γ Q) (v : FiniteTable.Address q → Bool) (j : ℤ) (r : Fin K.bits) :
    (A.reading K j r).eval v=K.encode ((A.config v).cell j) r := by
  by_cases h0 : j=0
  · subst j
    simp only [reading,ite_true,InputBit.eval,config,Config.cell,symbol,decide_true]
  · by_cases hh : 0<j.toNat ∧ j.toNat≤A.content.length
    · simp [reading,h0,hh,InputBit.eval_mapBool,config,Config.cell,symbol]
    · have hh' : ¬ (0 < j ∧ j ≤ (A.content.length : ℤ)) := by omega
      simp [reading,h0,hh',InputBit.eval,config,Config.cell,symbol]

lemma left_blank (v : FiniteTable.Address q → Bool) (T : ℕ) (hT : 0<T) :
    (A.config v).tape (-(2*(T:ℤ)))=A.blank := by
  unfold config symbol
  simp only
  rw [ite_eq_right (by omega)]
  rw [dite_eq_right (by omega)]

lemma right_blank (v : FiniteTable.Address q → Bool) (T : ℕ) (hT : 0<T)
    (hl : A.content.length<T) : (A.config v).tape (2*(T:ℤ)-1)=A.blank := by
  unfold config symbol
  simp only
  rw [ite_eq_right (by omega)]
  rw [dite_eq_right (by omega)]

def initialBits (K : Coding Γ Q) (T : ℕ) (j : Fin (4*T)) (r : Fin K.bits) : InputBit q :=
  A.reading K ((j.val:ℤ)-((2*T:ℕ):ℤ)) r

lemma initialBits_eval (K : Coding Γ Q) (δ : Q → Γ → Command Γ Q) (T : ℕ)
    (v : FiniteTable.Address q → Bool) (j : Fin (4*T)) (r : Fin K.bits) :
    (A.initialBits K T j r).eval v=K.trace δ (A.config v) (2*T) 0 j.val r :=
  A.reading_eval K v _ r

theorem addressed_rectangle (K : Coding Γ Q) (δ : Q → Γ → Command Γ Q)
    (M : K.Realization δ) (T : ℕ) (hT : 0<T) (hl : A.content.length<T)
    (L : Addressable.Layout q K.bits M.gates T (4*T)) (v : FiniteTable.Address q → Bool) :
    Rectangle.Valid M.circuit M.output T (4*T) (K.encode ⟨A.blank,false,none⟩)
      (L.inputRow (A.initialBits K T) v) (K.trace δ (A.config v) (2*T))
      (fun t j r => M.circuit.evaluate (Rectangle.neighborhood (K.trace δ (A.config v) (2*T) t) j)
        (Fin.natAdd (3*K.bits) r)) := by
  have hv := K.rectangle_valid δ M (A.config v) A.blank T hT rfl
    (A.left_blank v T hT) (A.right_blank v T hT hl)
  refine ⟨?_,hv.2⟩
  intro j hj
  funext r
  rw [L.inputRow_at _ v hj]
  exact (A.initialBits_eval K δ T v ⟨j,hj⟩ r).symm

theorem certificate_machine_iff (K : Coding Γ Q) (δ : Q → Γ → Command Γ Q)
    (M : K.Realization δ) (T : ℕ) (hT : 0<T) (hl : A.content.length<T)
    (L : Addressable.Layout q K.bits M.gates T (4*T)) (ho : L.origin.val=2*T)
    (accept : Label Γ Q) (data : DataAddress q → Bool) :
    (∃ cert : Fin q → Bool, ∀ i,
      (L.clauseAt M.circuit M.output (A.initialBits K T)
        (K.encode ⟨A.blank,false,none⟩) (K.encode accept) i).Holds (Addressable.Layout.assemble data cert)) ↔
    (run δ (A.config (Addressable.Layout.assemble data (fun _ => false))) (T-1)).cell 0=accept := by
  rw [L.certificate_iff]
  have hv := A.addressed_rectangle K δ M T hT hl L
    (Addressable.Layout.assemble data (fun _ => false))
  rw [← Rectangle.valid_run M.circuit M.output hv (T-1) (by omega) L.origin.val L.origin.isLt]
  rw [ho]
  simp only [Coding.trace,sub_self]
  exact K.encode_injective.eq_iff

end Input
end

end SourceBurnside.OneTape

namespace SourceBurnside.RawFit
open ExponentialThreshold
lemma eventually_fits (β g D n : ℕ) : ∃h0 : ℕ, ∀h≥h0,Fits β g D h n := by
  let B := 25*β+12*g+1
  let A := 3*n+2*D+12+200000*D
  obtain ⟨u,hu⟩ := scaled (8*A) 1 5 (by omega)
  obtain ⟨v,hv⟩ := scaled (10000*D) 1 1 (by omega)
  obtain ⟨w,hw⟩ := scaled B 0 5 (by omega)
  refine ⟨max 4 (max u (max v w)),?_⟩
  intro h hh
  have h4 : 4≤h := (le_max_left _ _).trans hh
  have h1 : 1≤h := by omega
  have HH : u≤h ∧ v≤h ∧ w≤h := by omega
  have hT : 1 ≤ 2^(h/5) := Nat.one_le_pow _ _ (by omega)
  have hBn : B ≤ 2^(h/5) := by have := hw h HH.2.2;simp only [pow_zero,mul_one] at this;omega
  have hBeq : (2:ℕ)^(h/5)*(2^(h/5))^2=2^(3*(h/5)) := by rw [←pow_mul,←pow_add];congr 1;omega
  have hQ : B*(2^(h/5))^2 ≤ 2^h := by
    calc
      B*(2^(h/5))^2 ≤ (2^(h/5))*(2^(h/5))^2 := Nat.mul_le_mul_right _ hBn
      _ = 2^(3*(h/5)) := hBeq
      _ ≤ 2^h := Nat.pow_le_pow_right (by omega) (by have := Nat.div_mul_le_self h 5;omega)
  have hN : n+2*InitialFormula.binSize n+2*InitialFormula.binSize (D*h)+12+20*(10000*(D*h)) ≤ A*h := by
    have hn := InitialFormula.binSize_le_self n
    have hdh := InitialFormula.binSize_le_self (D*h)
    have hc := Nat.mul_le_mul_left (3*n+12) h1
    unfold A
    nlinarith
  have hi : n+2*InitialFormula.binSize n+2*InitialFormula.binSize (D*h)+12+20*(10000*(D*h)) < 2^(h/5)/4 := by
    have H := hu h HH.1
    simp only [pow_one] at H
    have Hextra : (n+2*InitialFormula.binSize n+2*InitialFormula.binSize (D*h)+12+20*(10000*(D*h))+1)*4 ≤ 2^(h/5) := by

      nlinarith only [hN,H]
    exact (Nat.lt_div_iff_mul_lt (by omega)).mpr (by omega)
  unfold Fits
  refine ⟨by omega,?_,?_,?_,?_,?_,hi⟩
  · have H : 2^4 ≤ 2^(2*h) := Nat.pow_le_pow_right (by omega) (by omega)
    norm_num at H ⊢;omega
  · exact Nat.pow_le_pow_right (by omega) (by omega)
  · have H := hv h HH.2.1
    simp only [pow_one,Nat.div_one] at H
    nlinarith
  · have ht0 : 4*2^(h/5)-2 ≤ 4*2^(h/5) := Nat.sub_le _ _
    have ht1 : 2^(h/5)-1 ≤ 2^(h/5) := Nat.sub_le _ _
    have hm := Nat.mul_le_mul ht0 ht1
    have hm' := Nat.mul_le_mul_left g hm
    change _ ≤ _
    unfold B at hQ
    nlinarith only [hQ,hm']
  · have ht0 : 4*2^(h/5)-2 ≤ 4*2^(h/5) := Nat.sub_le _ _
    have ht1 : 2^(h/5)-1 ≤ 2^(h/5) := Nat.sub_le _ _
    have ht2 : 2^(h/5) ≤ (2^(h/5))^2 := by nlinarith
    have hm := Nat.mul_le_mul ht0 ht1
    have hm' := Nat.mul_le_mul_left (3*g+2*β) hm
    have hβ := Nat.mul_le_mul_left (10*β) ht2
    have hβ' := Nat.mul_le_mul_left β (show 1≤(2^(h/5))^2 by nlinarith)
    have hsm := Nat.mul_le_mul_left (2*β) ht1
    unfold B at hQ
    nlinarith only [hQ,hm',hβ,hβ',hsm]
end SourceBurnside.RawFit

namespace SourceBurnside.SourceMachine
noncomputable section
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
open TimedTape

opaque coding : OneTape.Coding Γ Q := OneTape.Coding.oneHot blank
opaque localCircuit : coding.Realization δ := coding.realization δ
abbrev β := coding.bits
abbrev g := localCircuit.gates
def blankBits := coding.encode ⟨blank,false,none⟩
def initialBits := coding.encode ⟨origin,true,some initialState⟩
def acceptBits := coding.encode (output true)
def bitEncoding (b : Bool) := coding.encode ⟨bitSymbol b,false,none⟩
def body (D : ℕ) : Formula (Fin 7) :=
  RawFit.body β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding
lemma bit_positive : 0<β := coding.positive

end
end SourceBurnside.SourceMachine

namespace SourceBurnside.TimedTape
noncomputable section
open Addressable
variable {q : ℕ}
abbrev addressedInput (content : List (InputBit q)) : OneTape.Input (Γ:=Γ) (Q:=Q) (q:=q) :=
  ⟨content,blank,origin,bitSymbol,initialState⟩
lemma raw_symbol_pos (x : List Bool) (j : ℤ) (hj : 0<j) (hx : j.toNat-1<x.length) :
    StackMachine.tape (start x).store j=bitSymbol (x[j.toNat-1]) := by
  apply congrArg₂ StackMachine.Symbol.mk
  · simp [ne_of_gt hj]
  · funext k
    simp only [ite_eq_left hj,initial_store]
    by_cases hk : k=.reg LiteralCompiler.src
    · simp [hk,List.getElem?_eq_getElem hx]
    · simp [hk]
lemma raw_symbol_far (x : List Bool) (j : ℤ) (hj : j≠0) (hx : ¬(0<j ∧ j.toNat-1<x.length)) :
    StackMachine.tape (start x).store j=blank := by
  apply congrArg₂ StackMachine.Symbol.mk
  · simp [hj]
  · funext k
    by_cases hp : 0<j
    · have hn : x.length≤j.toNat-1 := by omega
      simp only [ite_eq_left hp,initial_store]
      split_ifs <;> simp [List.getElem?_eq_none hn]
    · simp [hp]
lemma addressed_config (content : List (InputBit q)) (v : FiniteTable.Address q → Bool) :
    (addressedInput content).config v=StackMachine.encode (start (content.map (fun b => b.eval v))) := by
  change OneTape.Config.mk 0 initialState _=OneTape.Config.mk 0 initialState _
  congr 1
  funext j
  by_cases h0 : j=0
  · subst j;simp [OneTape.Input.symbol,raw_symbol_zero]
  · by_cases hp : 0<j.toNat ∧ j.toNat ≤ content.length
    · have hj : 0<j := by omega
      have hx : j.toNat-1<(content.map (fun b => b.eval v)).length := by simp only [List.length_map];omega
      rw [raw_symbol_pos _ j hj hx]
      simp [OneTape.Input.symbol,h0,hp]
    · rw [raw_symbol_far]
      · dsimp only [OneTape.Input.symbol,addressedInput]; rw [ite_eq_right h0,dite_eq_right hp]
      · exact h0
      · simp only [List.length_map]
        omega
end
end SourceBurnside.TimedTape

namespace SourceBurnside.SourceMachine
noncomputable section
section
open TimedTape Addressable
variable {q H l : ℕ}
def candidateBits (data : DataAddress q → Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10) : List Bool :=
  (InitialFormula.inputData (10000*H) l Z hd hdq hl hl10).map
    (fun b => b.eval (Layout.assemble data (fun _ => false)))
lemma candidate_length (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10) :
    (candidateBits data Z hd hdq hl hl10).length=(if Z then l*(10000*H) else 2*(l*(10000*H))) := by
  simp [candidateBits,InitialFormula.inputData]
lemma candidate_length_le (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10) :
    (candidateBits data Z hd hdq hl hl10).length≤200000*H := by
  rw [candidate_length]
  cases Z <;> simp <;> nlinarith
lemma source_input_eval (a : List Bool) (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10) :
    (InitialFormula.sourceInput a H l Z hd hdq hl hl10).map
      (fun b => b.eval (Layout.assemble data (fun _ => false)))=
    WrappedInput.envelope a (RawHeader.request H l Z (candidateBits data Z hd hdq hl hl10)) := by
  simp [InitialFormula.sourceInput,List.map_append,List.map_map,InputBit.eval,WrappedInput.envelope,
    RawHeader.request,candidateBits,List.append_assoc,Function.comp_def]
lemma small_arity (l : ℕ) (hl : l≤10) : InitialFormula.binSize l≤4 := by
  interval_cases l <;> decide
lemma source_input_length (a : List Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10) :
    (InitialFormula.sourceInput a H l Z hd hdq hl hl10).length≤
      a.length+2*InitialFormula.binSize a.length+2*InitialFormula.binSize H+12+200000*H := by
  have Hl := small_arity l hl10
  have Hdata : (InitialFormula.inputData (10000*H) l Z hd hdq hl hl10).length≤200000*H := by
    simpa only [candidateBits,List.length_map] using
      candidate_length_le (fun _ => false) Z hd hdq hl hl10
  simp only [InitialFormula.sourceInput,List.length_append,List.length_map,List.length_cons,List.length_nil,
    InitialFormula.enc_length]
  omega
lemma source_config (a : List Bool) (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10) :
    (addressedInput (InitialFormula.sourceInput a H l Z hd hdq hl hl10)).config
      (Layout.assemble data (fun _ => false))=
      StackMachine.encode (start (WrappedInput.envelope a (RawHeader.request H l Z
        (candidateBits data Z hd hdq hl hl10)))) := by
  rw [addressed_config,source_input_eval]
def layout (h n D : ℕ) (fit : RawFit.Fits β g D h n) : Layout (2^h) β g (2^(h/5)) (4*2^(h/5)) where
  bit_pos := bit_positive
  time_pos := Nat.pow_pos (by omega)
  width_ge := by have := Nat.one_le_pow (h/5) 2 (by omega);omega
  certificate_fit := fit.2.2.2.2.1
  clause_fit := fit.2.2.2.2.2.1
  origin := ⟨2*2^(h/5),by have := Nat.pow_pos (n:=h/5) (by omega : 0<2);omega⟩
lemma input_short (a : List Bool) (h D l : ℕ) (Z : Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) (hl : 0<l) (hl10 : l≤10) :
    (InitialFormula.sourceInput a (D*h) l Z hd fit.2.2.2.1 hl hl10).length<2^(h/5) := by
  have H := source_input_length a Z hd fit.2.2.2.1 hl hl10
  have Hfit := fit.2.2.2.2.2.2
  have Hmono := Nat.div_le_self (2^(h/5)) 4
  nlinarith
end

open TimedTape Addressable Structured Structured.Binary

end
end SourceBurnside.SourceMachine

namespace SourceBurnside.TimedTape
noncomputable section
open Addressable
lemma initialBits_row {q : ℕ} (K : OneTape.Coding Γ Q) (content : List (InputBit q))
    (T : ℕ) (j : Fin (4*T)) (r : Fin K.bits) :
    (addressedInput content).initialBits K T j r=
      InitialFormula.row (K.encode ⟨blank,false,none⟩) (K.encode ⟨origin,true,some initialState⟩)
        (fun b => K.encode ⟨bitSymbol b,false,none⟩) (2*T) content j r := by
  let p : ℤ := (j.val:ℤ)-((2*T:ℕ):ℤ)
  have hn : p.toNat=j.val-2*T := by unfold p;omega
  have hz : p=0 ↔ j.val=2*T := by unfold p;omega
  change (addressedInput content).reading K p r=_
  unfold OneTape.Input.reading InitialFormula.row
  dsimp only [addressedInput]
  by_cases h0 : j.val=2*T
  · rw [ite_eq_left (hz.mpr h0),ite_eq_left h0]
  · rw [ite_eq_right (mt hz.mp h0),ite_eq_right h0]
    by_cases hg : 2*T<j.val ∧ j.val-(2*T+1) < content.length
    · have hp : 0<p.toNat ∧ p.toNat ≤ content.length := by omega
      rw [dite_eq_left hp,dite_eq_left hg]
      have hi : p.toNat-1=j.val-(2*T+1) := by omega
      simp only [hi]
      cases content[j.val-(2*T+1)] with
      | fixed b => rfl
      | input a n =>
        cases h0 : K.encode ⟨bitSymbol false,false,none⟩ r <;>
          cases h1 : K.encode ⟨bitSymbol true,false,none⟩ r <;> cases n <;>
          simp [InputBit.mapBool,InitialFormula.mapBit,h0,h1]
    · have hp : ¬(0<p.toNat ∧ p.toNat ≤ content.length) := by omega
      rw [dite_eq_right hp,dite_eq_right hg]
end
end SourceBurnside.TimedTape

namespace SourceBurnside.FiniteTable.Codec
lemma field_of_bits {H : ℕ} (bs : List Bool) (off : ℕ) (w : Raw H)
    (hw : ∀i : Fin (10000*H), bs.getD (off+i.val) false=w i) :
    (binaryValue bs/2^off)%2^(10000*H)=natCode w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow,binaryValue_bit]
  by_cases hi : i<10000*H
  · simp only [hi,decide_true,Bool.true_and]
    rw [Nat.add_comm,hw ⟨i,hi⟩,natCode_bit w ⟨i,hi⟩]
  · simp [hi,natCode,binaryValue_bit]
end SourceBurnside.FiniteTable.Codec
namespace SourceBurnside.SourceMachine
noncomputable section
section
open Addressable FiniteTable.Codec
variable {q H l : ℕ}
def candidateWord (data : DataAddress q→Bool) (hdq : 10000*H≤q) (hl10 : l≤10)
    (b : Bool) (i : Fin l) : Raw H :=
  fun j => data (b,⟨i.val,i.isLt.trans_le hl10⟩,⟨j.val,j.isLt.trans_le hdq⟩)
lemma candidate_bit (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10)
    (b : Bool) (i : Fin l) (hside : Z=false ∨ b=false) (j : Fin (10000*H)) :
    (candidateBits data Z hd hdq hl hl10).getD
      (((if b then l else 0)+i.val)*(10000*H)+j.val) false=
        candidateWord data hdq hl10 b i j := by
  let d := 10000*H
  have hi := i.isLt
  have hj : j.val<d := j.isLt
  have hd0 : 0<d := hd
  have offlt : ((if b then l else 0)+i.val)*d+j.val < if Z then l*d else 2*(l*d) := by
    cases b <;> cases Z <;> simp_all
    all_goals have hi := i.isLt; nlinarith
  have hm : (((if b then l else 0)+i.val)*d+j.val)%d=j.val := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt hj]
  have hdiv : (((if b then l else 0)+i.val)*d+j.val)/d=(if b then l else 0)+i.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hd0,Nat.div_eq_of_lt hj,Nat.zero_add]
  have hmod : (((if b then l else 0)+i.val)*d+j.val)/d%l=i.val := by
    rw [hdiv];cases b <;> simp [Nat.mod_eq_of_lt hi]
  have hb : decide (l*d≤((if b then l else 0)+i.val)*d+j.val)=b := by
    cases b <;> simp <;> nlinarith
  simp only [candidateBits,InitialFormula.inputData,List.getD_eq_getElem,List.length_map,List.length_ofFn,
    show ((if b then l else 0)+i.val)*(10000*H)+j.val<(if Z then l*(10000*H) else 2*(l*(10000*H))) from offlt,
    List.getElem_map,List.getElem_ofFn,InputBit.eval,Layout.assemble,dataAddress]
  change data (decide (l*d≤_),⟨_ ,_⟩,⟨_,_⟩)=_
  rw [hb]
  congr 1
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> apply Fin.ext
    · exact hmod
    · exact hm
lemma candidate_field (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10)
    (b : Bool) (i : Fin l) (hside : Z=false ∨ b=false) :
    (binaryValue (candidateBits data Z hd hdq hl hl10)/2^(((if b then l else 0)+i.val)*(10000*H)))%
      2^(10000*H)=natCode (candidateWord data hdq hl10 b i) :=
  field_of_bits _ _ _ (candidate_bit data Z hd hdq hl hl10 b i hside)
end

section
open Addressable FiniteTable.Codec Structured.Device Structured.Device.Formula
variable {q H l : ℕ}
lemma candidate_lengthOK (a : List Bool) (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10) :
    RawLocalBody.lengthOK.eval (RawPreparedInputs.semantic a H l Z (candidateBits data Z hd hdq hl hl10))=1 := by
  simp only [RawLocalBody.lengthOK,and_eval,less_eval,equal_eval,eval,RawPreparedInputs.semantic,
    RawLocalBody.length,RawLocalBody.height,candidate_length]
  cases Z <;> simp [CellRepr.boolean]
lemma candidate_piece (a : List Bool) (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl2 : l≤2)
    (b : Bool) (i : Fin 2) (hi : i.val<l) (hside : Z=false ∨ b=false) :
    (RawLocalBody.piece b i).eval (RawPreparedInputs.semantic a H l Z
      (candidateBits data Z hd hdq hl (by omega)))=
      natCode (candidateWord data hdq (by omega) b ⟨i.val,hi⟩) := by
  have hs : RawLocalBody.sideStart.eval (RawPreparedInputs.semantic a H l Z
      (candidateBits data Z hd hdq hl (by omega)))=l := by
    interval_cases l <;> simp [RawLocalBody.sideStart,equal_eval,eval,RawPreparedInputs.semantic]
  have ho : (RawLocalBody.offset b i).eval (RawPreparedInputs.semantic a H l Z
      (candidateBits data Z hd hdq hl (by omega)))=((if b then l else 0)+i.val)*(10000*H) := by
    cases b
    · rfl
    · change (RawLocalBody.sideStart.eval (RawPreparedInputs.semantic a H l Z
        (candidateBits data Z hd hdq hl (by omega)))+i.val)*(10000*H)=(l+i.val)*(10000*H)
      rw [hs]
  change (binaryValue (candidateBits data Z hd hdq hl (by omega))/2^((RawLocalBody.offset b i).eval
    (RawPreparedInputs.semantic a H l Z (candidateBits data Z hd hdq hl (by omega)))))%2^(10000*H)=_
  rw [ho]
  exact candidate_field data Z hd hdq hl (by omega) b ⟨i.val,hi⟩ hside

lemma candidate_body_eq (a : List Bool) (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10)
    (D : ℕ) (fit : RawFit.Fits β g D H a.length) :
    (body D).eval (RawPreparedInputs.semantic a H l Z (candidateBits data Z hd hdq hl hl10))=
    (LocalBody.body β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding).eval
      (fun i => (RawLocalBody.substitution i).eval
        (RawPreparedInputs.semantic a H l Z (candidateBits data Z hd hdq hl hl10))) := by
  rw [body,RawFit.body_eval]
  have hf : RawFit.Fits β g D (RawPreparedInputs.semantic a H l Z (candidateBits data Z hd hdq hl hl10) 2)
    (RawPreparedInputs.semantic a H l Z (candidateBits data Z hd hdq hl hl10) 1) := fit
  rw [ite_eq_left hf]
  simp only [RawLocalBody.checkedBody,and_eval,candidate_lengthOK,one_ne_zero,ite_false,
    RawLocalBody.body,bind_eval]
lemma sourceBody_boolean (D : ℕ) (v : Fin 7→ℕ) : (body D).eval v≤1 :=
  RawFixedPoint.body_boolean β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding v
lemma sourceBody_eq_one_iff_ne_zero (D : ℕ) (v : Fin 7→ℕ) : (body D).eval v=1 ↔ (body D).eval v≠0 := by
  have := sourceBody_boolean D v
  omega
end

section
open TimedTape Addressable LocalSyntax FiniteTable FiniteTable.Codec
open Structured.Device Structured.Device.Formula
variable {h D : ℕ}
def sourceInitial (a : List Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) : Task → Fin (4*2^(h/5)) → Fin β → InputBit (2^h) :=
  PredicateFormula.initial (layout h a.length D fit) blankBits initialBits bitEncoding a (D*h) hd fit.2.2.2.1
def sourceSchedule (a : List Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) : Schedule (2^h) :=
  (layout h a.length D fit).schedule localCircuit.circuit localCircuit.output
    (sourceInitial a fit hd) blankBits acceptBits
lemma sourceInitial_input (a : List Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) (task : Task) :
    sourceInitial a fit hd task=(addressedInput (InitialFormula.sourceInput a (D*h)
      (task.arity.val+1) task.zeroTask hd fit.2.2.2.1 (by omega) (by have := task.arity.isLt;omega))).initialBits coding (2^(h/5)) := by
  funext j r
  exact (initialBits_row coding _ _ j r).symm
lemma physical_represents (a : List Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) (v : LocalBody.Registers → ℕ)
    (hcode : v 0=binaryValue a) (hlen : v 1=a.length) (hheight : v 2=h) :
    (LocalBody.table β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding).Represents
      v (sourceSchedule a fit hd) := by
  let : NeZero (2^h) := ⟨pow_ne_zero h (by omega)⟩
  apply PredicateFormula.physical_exact (layout h a.length D fit) localCircuit.circuit localCircuit.output
    blankBits initialBits acceptBits bitEncoding a hd fit.2.2.2.1
  · simp [LocalBody.time,LocalBody.height,eval,hheight]
  · simp [LocalBody.width,LocalBody.time,LocalBody.height,eval,hheight]
  · simp [LocalBody.origin,LocalBody.time,LocalBody.height,eval,hheight,layout]
  · exact hcode
  · exact hlen
  · simp [LocalBody.nextHeight,LocalBody.height,eval,hheight]
lemma local_zero_one (hh : 4≤h) (a : List Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) (v : LocalBody.Registers→ℕ) (w : Raw h)
    (hcode : v 0=binaryValue a) (hlen : v 1=a.length) (hheight : v 2=h)
    (harity : v 3=1) (hz : v 4=1) (hw : v 5=natCode w) :
    (LocalBody.body β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding).eval v≠0 ↔
      entry (by omega) (sourceSchedule a fit hd) (10000*(D*h)) true [w] []=true := by
  unfold LocalBody.body
  apply PredicateFormula.normalEntry_zero_one (H:=LocalBody.height) (v:=v) hh _ (physical_represents a fit hd v hcode hlen hheight) w hheight
  · simp [LocalBody.size,LocalBody.height,eval,hheight,Nat.mul_assoc]
  · exact harity
  · exact hz
  · exact hw
lemma local_zero_two (hh : 4≤h) (a : List Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) (v : LocalBody.Registers→ℕ) (w x : Raw h)
    (hheight : v 2=h) (harity : v 3=2) (hz : v 4=1)
    (hw : v 5=natCode w) (hx : v 6=natCode x) :
    (LocalBody.body β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding).eval v≠0 ↔
      entry (by omega) (sourceSchedule a fit hd) (10000*(D*h)) true [w,x] []=true := by
  unfold LocalBody.body
  apply PredicateFormula.normalEntry_zero_two (H:=LocalBody.height) (v:=v) hh _ (sourceSchedule a fit hd) w x hheight
  · simp [LocalBody.bound,LocalBody.height,eval,hheight]
  · exact harity
  · exact hz
  · exact hw
  · exact hx
lemma local_rep_one (hh : 4≤h) (a : List Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) (v : LocalBody.Registers→ℕ) (w y : Raw h)
    (hcode : v 0=binaryValue a) (hlen : v 1=a.length) (hheight : v 2=h)
    (harity : v 3=1) (hz : v 4=0) (hw : v 5=natCode w) (hy : v 7=natCode y) :
    (LocalBody.body β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding).eval v≠0 ↔
      entry (by omega) (sourceSchedule a fit hd) (10000*(D*h)) false [w] [y]=true := by
  unfold LocalBody.body
  apply PredicateFormula.normalEntry_rep_one (H:=LocalBody.height) (v:=v) hh _ (physical_represents a fit hd v hcode hlen hheight) w y hheight
  · simp [LocalBody.size,LocalBody.height,eval,hheight,Nat.mul_assoc]
  · exact harity
  · exact hz
  · exact hw
  · exact hy
lemma local_rep_two (hh : 4≤h) (a : List Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) (v : LocalBody.Registers→ℕ) (w x y z : Raw h)
    (hcode : v 0=binaryValue a) (hlen : v 1=a.length) (hheight : v 2=h)
    (harity : v 3=2) (hz : v 4=0) (hw : v 5=natCode w) (hx : v 6=natCode x)
    (hy : v 7=natCode y) (hz' : v 8=natCode z) :
    (LocalBody.body β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding).eval v≠0 ↔
      entry (by omega) (sourceSchedule a fit hd) (10000*(D*h)) false [w,x] [y,z]=true := by
  unfold LocalBody.body
  apply PredicateFormula.normalEntry_rep_two (H:=LocalBody.height) (v:=v) hh _ (physical_represents a fit hd v hcode hlen hheight) w x y z hheight
  · simp [LocalBody.size,LocalBody.height,eval,hheight,Nat.mul_assoc]
  · simp [LocalBody.bound,LocalBody.height,eval,hheight]
  · exact harity
  · exact hz
  · exact hw
  · exact hx
  · exact hy
  · exact hz'
end

section
open Addressable FiniteTable.Codec Structured.Device Structured.Device.Formula
variable {q H l D : ℕ}
lemma candidate_entry (hH : 4≤H) (a : List Bool) (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10)
    (fit : RawFit.Fits β g D H a.length) (hdnext : 0<10000*(D*H)) :
    (body D).eval (RawPreparedInputs.semantic a H l Z (candidateBits data Z hd hdq hl hl10))=1 ↔
      entry (by omega) (sourceSchedule a fit hdnext) (10000*(D*H)) Z
        (List.ofFn (candidateWord data hdq hl10 false))
        (if Z then [] else List.ofFn (candidateWord data hdq hl10 true))=true := by
  rw [sourceBody_eq_one_iff_ne_zero,candidate_body_eq a data Z hd hdq hl hl10 D fit]
  let v : LocalBody.Registers→ℕ := fun i => (RawLocalBody.substitution i).eval
    (RawPreparedInputs.semantic a H l Z (candidateBits data Z hd hdq hl hl10))
  change (LocalBody.body β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding).eval v≠0 ↔ _
  by_cases h1 : l=1
  · subst l
    cases Z
    · have Hc := local_rep_one hH a fit hdnext v
        (candidateWord data hdq hl10 false 0) (candidateWord data hdq hl10 true 0)
        rfl rfl rfl rfl rfl
        (candidate_piece a data false hd hdq hl (by omega) false 0 (by decide) (Or.inl rfl))
        (candidate_piece a data false hd hdq hl (by omega) true 0 (by decide) (Or.inl rfl))
      simpa only [Bool.false_eq_true,ite_false,List.ofFn_succ,List.ofFn_zero,Fin.succ_zero_eq_one] using Hc
    · have Hc := local_zero_one hH a fit hdnext v
        (candidateWord data hdq hl10 false 0) rfl rfl rfl rfl rfl
        (candidate_piece a data true hd hdq hl (by omega) false 0 (by decide) (Or.inr rfl))
      simpa only [ite_true,List.ofFn_succ,List.ofFn_zero,Fin.succ_zero_eq_one] using Hc
  · by_cases h2 : l=2
    · subst l
      cases Z
      · have Hc := local_rep_two hH a fit hdnext v
          (candidateWord data hdq hl10 false 0) (candidateWord data hdq hl10 false 1)
          (candidateWord data hdq hl10 true 0) (candidateWord data hdq hl10 true 1)
          rfl rfl rfl rfl rfl
          (candidate_piece a data false hd hdq hl (by omega) false 0 (by decide) (Or.inl rfl))
          (candidate_piece a data false hd hdq hl (by omega) false 1 (by decide) (Or.inl rfl))
          (candidate_piece a data false hd hdq hl (by omega) true 0 (by decide) (Or.inl rfl))
          (candidate_piece a data false hd hdq hl (by omega) true 1 (by decide) (Or.inl rfl))
        simpa only [Bool.false_eq_true,ite_false,List.ofFn_succ,List.ofFn_zero,Fin.succ_zero_eq_one] using Hc
      · have Hc := local_zero_two hH a fit hdnext v
          (candidateWord data hdq hl10 false 0) (candidateWord data hdq hl10 false 1) rfl rfl rfl
          (candidate_piece a data true hd hdq hl (by omega) false 0 (by decide) (Or.inr rfl))
          (candidate_piece a data true hd hdq hl (by omega) false 1 (by decide) (Or.inr rfl))
        simpa only [ite_true,List.ofFn_succ,List.ofFn_zero,Fin.succ_zero_eq_one] using Hc
    · have hb : (LocalBody.body β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding).eval v=0 := by
        apply PredicateFormula.normalEntry_other
        · exact h1
        · exact h2
      rw [hb]
      simp only [ne_eq,not_true_eq_false,false_iff]
      cases Z
      · simp only [entry_replacement,Bool.false_eq_true,ite_false]
        intro he
        have Hlen := FiniteTable.Codec.replacement_lengths hH _ _ _ _ he
        simp only [List.length_ofFn] at Hlen
        omega
      · simp only [ite_true,entry_zero,true_and]
        intro he
        have Hlen := FiniteTable.Codec.zero_lengths (by omega : 0<H) _ _ _ he
        simp only [List.length_ofFn] at Hlen
        omega
end

open TimedTape Addressable LocalSyntax FiniteTable FiniteTable.Codec

end
end SourceBurnside.SourceMachine

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_WordRewriting
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAdmissible _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFirst _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHead _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideInternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLast _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLastOK _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLeftExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalettePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideRightExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideStructural _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

namespace Cell

def color (c : Cell q) : Fin q := match c.pos with
  | .palette x => x | _ => 0

omit [NeZero q] in
@[simp] lemma setColor_setColor (c : Cell q) (x y : Fin q) :
    (c.setColor x).setColor y = c.setColor y := by
  cases c; rfl

omit [NeZero q] in
@[simp] lemma setColor_of_palette (c : Cell q) {x : Fin q} (h : c.pos = .palette x) :
    c.setColor x = c := by
  cases c with | mk sk ch dat cert head => cases sk; simp_all [pos,setColor]

end Cell

def canonicalCell (bits : Fin d → ZMod 2) (p : Position q) : Cell q :=
  { skeleton := ⟨p,.idle,defaultMeta⟩
    checker := .idle
    data := fun side => if side then 0 else
      match p with
      | .core r => if h : r.val < d then bits ⟨r.val,h⟩ else 0
      | _ => 0
    certificate := 0
    head := defaultHead }

def canonicalBlock (bits : Fin d → ZMod 2) : List (Cell q) :=
  (List.finRange q).map (fun p => canonicalCell bits (.core p)) ++
  (List.finRange q).map (fun x => canonicalCell bits (.palette x)) ++
  [canonicalCell bits .stop]

def encodeWord (w : List (Fin d → ZMod 2)) : List (Cell q) := w.flatMap canonicalBlock

@[simp] lemma canonicalCell_pos (bits : Fin d → ZMod 2) (p : Position q) :
    (canonicalCell bits p).pos=p := rfl

@[simp] lemma canonicalCell_marker (bits : Fin d → ZMod 2) (p : Position q) :
    (canonicalCell bits p).marker=.idle := rfl

@[simp] lemma canonicalCell_checker (bits : Fin d → ZMod 2) (p : Position q) :
    (canonicalCell bits p).checker=.idle := rfl

@[simp] lemma canonicalBlock_length (bits : Fin d → ZMod 2) :
    (canonicalBlock (q:=q) bits).length=2*q+1 := by
  simp [canonicalBlock]; omega

@[simp] lemma encodeWord_length (w : List (Fin d → ZMod 2)) :
    (encodeWord (q:=q) w).length=(2*q+1)*w.length := by
  induction w with
  | nil => simp [encodeWord]
  | cons a w ih =>
    change (canonicalBlock a ++ encodeWord w).length = (2*q+1) * (a::w).length
    rw [List.length_append, canonicalBlock_length, ih, List.length_cons, Nat.mul_succ]
    omega

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_BoundaryCell
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAdmissible _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFirst _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHead _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideInternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLast _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLastOK _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLeftExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalettePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideRightExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideStructural _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q] {S : Schedule q}
namespace Cell
omit [NeZero q] in
@[simp] lemma setChecker_self (c : Cell q) : c.setChecker c.checker=c := by cases c; rfl
omit [NeZero q] in
@[simp] lemma setChecker_setChecker (c : Cell q) (a b : Palette.Check (Fin q)) :
    (c.setChecker a).setChecker b=c.setChecker b := rfl
omit [NeZero q] in
@[simp] lemma setChecker_checker (c : Cell q) (a : Palette.Check (Fin q)) :
    (c.setChecker a).checker=a := rfl
omit [NeZero q] in
@[simp] lemma setChecker_pos (c : Cell q) (a : Palette.Check (Fin q)) :
    (c.setChecker a).pos=c.pos := rfl
@[simp] lemma setChecker_color (c : Cell q) (a : Palette.Check (Fin q)) :
    (c.setChecker a).color=c.color := rfl
omit [NeZero q] in
@[simp] lemma setChecker_palette (c : Cell q) (a : Palette.Check (Fin q)) :
    (c.setChecker a).isPalette ↔ c.isPalette := Iff.rfl
end Cell

def checkerIdle (w : List (Cell q)) : List (Cell q) := w.map (fun c => c.setChecker .idle)
omit [NeZero q] in
@[simp] lemma checkerIdle_append (v w : List (Cell q)) :
    checkerIdle (v++w)=checkerIdle v++checkerIdle w := List.map_append
omit [NeZero q] in
@[simp] lemma checkerIdle_cons (a : Cell q) (w : List (Cell q)) :
    checkerIdle (a::w)=a.setChecker .idle::checkerIdle w := rfl
end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_PrefixRewriting
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable
section
open LocalSyntax LocalSyntax.Skeleton
variable {q d N : ℕ} [NeZero q]

namespace Cell

@[simp] lemma idle_marker (c : Cell q) (s : Bool) : (c.idle s).marker=.idle := rfl
end Cell

end

section
open LocalSyntax LocalSyntax.Skeleton
variable {q d N : ℕ} [NeZero q] {S : Schedule q}

def lockedCount (w : List (Cell q)) : ℕ := w.countP (fun c => decide (c.marker≠.idle))
omit [NeZero q] in
@[simp] lemma lockedCount_append (v w : List (Cell q)) :
    lockedCount (v++w)=lockedCount v+lockedCount w := List.countP_append

end

open LocalSyntax LocalSyntax.Skeleton
end SourceBurnside.FiniteTable

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_GeometricRelations
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable
section
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q] {S : Schedule q}

omit [NeZero q] in
@[simp] lemma Cell.shape_core_iff (c : Cell q) (p : Fin q) :
    c.shape=.core p ↔ c.pos=.core p := by
  cases hp : c.pos <;> simp [shape,hp]
omit [NeZero q] in
@[simp] lemma Cell.shape_stop_iff (c : Cell q) : c.shape=.stop ↔ c.pos=.stop := by
  cases hp : c.pos <;> simp [shape,hp]

end

section
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q] {S : Schedule q}

def beginnings (w : List (Cell q)) : List (Cell q) :=
  w.filter (fun c => decide (c.pos=.core (0 : Fin q)))
def firstCoreCount (w : List (Cell q)) : ℕ := (beginnings w).length

lemma firstCoreCount_eq (w : List (Cell q)) : firstCoreCount w=
    w.countP (fun c => decide (c.pos=.core (0 : Fin q))) := by
  simp [firstCoreCount,beginnings,List.countP_eq_length_filter]

@[simp] lemma firstCoreCount_append (v w : List (Cell q)) :
    firstCoreCount (v++w)=firstCoreCount v+firstCoreCount w := by
  simp [firstCoreCount_eq,List.countP_append]

end

open LocalSyntax LocalSyntax.Skeleton
namespace Rigid
variable {q d n : ℕ} [NeZero q]

def position (i : Fin (width q)) : Position q :=
  if hi : i.val<q then .core ⟨i.val,hi⟩
  else if hp : i.val<2*q then .palette ⟨i.val-q,by omega⟩ else .stop

end Rigid
end SourceBurnside.FiniteTable

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_TemplateHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q]
namespace Rigid

namespace Template
variable (task : Task) (u : Bool → Fin (task.arity.val+1) → Fin d → ZMod 2)
    (cert : Fin q → ZMod 2)

def cell (i : Fin ((task.arity.val+1)*width q)) : Cell q :=
  { skeleton := ⟨position (coord i),.idle,⟨task.arity,task.zeroTask,block i⟩⟩
    checker := .idle
    data := fun s => match position (coord i) with
      | .core p => if hp : p.val<d then u s (block i) ⟨p.val,hp⟩ else 0
      | _ => 0
    certificate := match position (coord i) with
      | .core p => if (block i).val=0 then cert p else 0
      | _ => 0
    head := defaultHead }

@[simp] lemma pos (i : Fin ((task.arity.val+1)*width q)) :
    (cell task u cert i).pos=position (coord i) := rfl
@[simp] lemma metadata (i : Fin ((task.arity.val+1)*width q)) :
    (cell task u cert i).metadata=⟨task.arity,task.zeroTask,block i⟩ := rfl

end Template
end Rigid
end SourceBurnside.FiniteTable

namespace SourceBurnside.SourceMachine
noncomputable section
open Addressable LocalSyntax FiniteTable

structure MachineHierarchy (D : ℕ) (hD : 2≤D) where
  program : List Bool
  threshold : ℕ
  threshold_four : 4≤threshold
  fits : ∀ h, threshold≤h → RawFit.Fits β g D h (WrappedInput.specialize program program).length
  certifies : ∀ (h : ℕ) (hh : threshold≤h) (task : Task) (data : DataAddress (2^h) → Bool),
    let a := WrappedInput.specialize program program
    let fit := fits h hh
    let fitnext := fits (D*h) (by nlinarith)
    let hd : 0<10000*(D*h) := by nlinarith
    let hdnext : 0<10000*(D*(D*h)) := by nlinarith
    (∃cert : Fin (2^h) → Bool, ∀i,
      ((layout h a.length D fit).clauseAt localCircuit.circuit localCircuit.output
        (sourceInitial a fit hd task) blankBits acceptBits i).Holds (Layout.assemble data cert)) ↔
    Codec.entry (by nlinarith : 0<D*h) (sourceSchedule a fitnext hdnext) (10000*(D*(D*h))) task.zeroTask
      (List.ofFn (candidateWord (l:=task.arity.val+1) data fit.2.2.2.1 (by have := task.arity.isLt;omega) false))
      (if task.zeroTask then [] else List.ofFn
        (candidateWord (l:=task.arity.val+1) data fit.2.2.2.1 (by have := task.arity.isLt;omega) true))=true

end
end SourceBurnside.SourceMachine

end

end OAI
end


