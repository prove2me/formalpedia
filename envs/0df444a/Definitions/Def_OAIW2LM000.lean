-- Prove2me | Definitions.Def_OAIW2LM000
-- name    : OAIW2LM000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T03:00:01.009355+00:00
-- url     : https://prove2.me/theorems/128c1698-35bf-4d98-b890-6c8a374e42f3
-- title:
--   Definitions bundle OAIW2LM000 of the split of OpenAI, the Lean development OAI.Computability.LoopMatching (comparator challenge of OAI.LoopMatching.fullEndpoint)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LoopMatching.fullEndpoint`, carved from OpenAI's openai/math development (OpenAI, *the Lean development OAI.Computability.LoopMatching (comparator challenge of OAI.LoopMatching.fullEndpoint)*, OpenAI Math Release, October 2026, result family not identified here; see lean/formalization.yaml, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 708 declarations of OpenAI's Lean: 258 definitions, 12 inductive types or structures, 20 instances and 418 theorems. The definitions and types are `Convexity.StdSimplex.equivIcc`, `Convexity.StdSimplex.subBarycenter`, `Convexity.StdSimplex.topologicalSpaceInduced`, `OAI.BinaryMatching.Algorithm.Affine`, `OAI.BinaryMatching.Algorithm.Affine.eval`, `OAI.BinaryMatching.Algorithm.Affine.evalReal`, `OAI.BinaryMatching.Algorithm.A₀`, `OAI.BinaryMatching.Algorithm.B`, `OAI.BinaryMatching.Algorithm.D₀`, `OAI.BinaryMatching.Algorithm.IntegralState`, `OAI.BinaryMatching.Algorithm.K`, `OAI.BinaryMatching.Algorithm.L`, `OAI.BinaryMatching.Algorithm.M₀`, `OAI.BinaryMatching.Algorithm.Piece`, `OAI.BinaryMatching.Algorithm.Piece.eval`, `OAI.BinaryMatching.Algorithm.Piece.evalReal`, `OAI.BinaryMatching.Algorithm.Q`, `OAI.BinaryMatching.Algorithm.R`, `OAI.BinaryMatching.Algorithm.State`, `OAI.BinaryMatching.Algorithm.Table`, `OAI.BinaryMatching.Algorithm.Z`, `OAI.BinaryMatching.Algorithm.Zbad`, `OAI.BinaryMatching.Algorithm.Zgood`, `OAI.BinaryMatching.Algorithm.activeRow`, `OAI.BinaryMatching.Algorithm.activeRows`, `OAI.BinaryMatching.Algorithm.allRows`, `OAI.BinaryMatching.Algorithm.badWeight`, `OAI.BinaryMatching.Algorithm.beta`, `OAI.BinaryMatching.Algorithm.capacities`, `OAI.BinaryMatching.Algorithm.coordinates`, `OAI.BinaryMatching.Algorithm.covered`, `OAI.BinaryMatching.Algorithm.cutRow`, `OAI.BinaryMatching.Algorithm.decodeIntegral`, `OAI.BinaryMatching.Algorithm.degreeRow`, `OAI.BinaryMatching.Algorithm.dyadic`, `OAI.BinaryMatching.Algorithm.edgeWeight`, `OAI.BinaryMatching.Algorithm.entry`, `OAI.BinaryMatching.Algorithm.estimate`, `OAI.BinaryMatching.Algorithm.goodWeight`, `OAI.BinaryMatching.Algorithm.gradient` and 230 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, lean/OAI/Combinatorics, in whole or in part: `MatchingCount_ArgRoutine`, `MatchingCount_BinaryAlgorithm`, `MatchingCount_BinaryParser`, `MatchingCount_CappedPower`, `MatchingCount_CutAlgebra`, `MatchingCount_DenseOracle`, `MatchingCount_DivisionRoutine`, `MatchingCount_FiniteStack`, `MatchingCount_FoldRoutine`, `MatchingCount_GuardRoutine`, `MatchingCount_IntegerRoutine`, `MatchingCount_IterateRoutine`, `MatchingCount_LengthRoutine`, `MatchingCount_ListNumeric`, `MatchingCount_ListRoutine`, `MatchingCount_MapRoutine`, `MatchingCount_OddCutParity`, `MatchingCount_OddMincut`, `MatchingCount_OptionCases`, `MatchingCount_OracleBounds`, `MatchingCount_OrbitRoutine`, `MatchingCount_PairRoutine`, `MatchingCount_ParamRoutine`, `MatchingCount_ParserSupport`, `MatchingCount_PolyCoding`, `MatchingCount_ProjectionRoutine`, `MatchingCount_RawBitsBridge`, `MatchingCount_RawData`, `MatchingCount_RawInput`, `MatchingCount_RawPrimitives`, `MatchingCount_RawRoutine`, `MatchingCount_RawSearch`, `MatchingCount_RawSearchCompiler`, `MatchingCount_RawSearchSize`, `MatchingCount_RawSize`, `MatchingCount_ResidualSearch`, `MatchingCount_ScaledAlgorithm`, `MatchingCount_ScaledBounds`, `MatchingCount_ScaledState`, `MatchingCount_SelectRoutine`, `MatchingCount_SequenceRoutine`, `MatchingCount_StackCopy`, `MatchingCount_StackEmbed`, `MatchingCount_StackFrame`, `MatchingCount_StackMacros`, `MatchingCount_StackPair`, `MatchingCount_StackRoutine`, `MatchingCount_SumRoutine`, `MatchingCount_TerminalMincut`, `MatchingCount_UnaryArithmetic`, `MatchingCount_UnaryDivision`, `MatchingCount_UnitFlow`, `MatchingCount_UnitMincut`, `PerfectMatching_AlgorithmPartition`, `PerfectMatching_Ascent`, `PerfectMatching_Basic`, `PerfectMatching_Completion`, `PerfectMatching_DyadicEntropy`, `PerfectMatching_DyadicEnvelope`, `PerfectMatching_Entropy`, `PerfectMatching_ForcedReduction`, `PerfectMatching_Model`, `PerfectMatching_ObjectivePenalty`, `PerfectMatching_OddCuts`, `PerfectMatching_ParameterBounds`, `PerfectMatching_Partition`, `PerfectMatching_Polytope`, `PerfectMatching_Violation`.
--
--   **Imports.** It imports the published bundle `Def_SingletonLoopMatching`.
--
--   **Imported by** (directly, in this split): the bundles `OAIW2LM002` and `OAIW2LM003`; the statement `OAI.BinaryMatching.Algorithm.R_partition_bracket`.
-- source:
--   OpenAI, the Lean development OAI.Computability.LoopMatching (comparator challenge of OAI.LoopMatching.fullEndpoint), OpenAI Math Release, October 2026, https://github.com/openai/math (result family not identified here; see lean/formalization.yaml; paper: https://github.com/openai/math; Apache License 2.0); definitions carved from lean/OAI/Computability, lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_SingletonLoopMatching

section
-- module Solutions.OAIW2_LoopMatching.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

namespace MatchingEntropy
namespace LooplessGraph
variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
def IsPerfectMatching (G : LooplessGraph V E) (M : Finset E) : Prop :=
  ∀ v, ∃! e, e∈M ∧ G.Incident v e
abbrev Matching (G : LooplessGraph V E) := {M : Finset E // G.IsPerfectMatching M}
noncomputable instance matchingFintype (G : LooplessGraph V E) : Fintype G.Matching :=
  Fintype.ofFinite _
end LooplessGraph
end MatchingEntropy

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_FiniteStack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode

abbrev Store (r : ℕ) := Fin r → List Bool

inductive Instr (r : ℕ) (L : Type)
  | go : L → Instr r L
  | push : Fin r → Bool → L → Instr r L
  | pop : Fin r → L → Instr r L
  | branch : Fin r → L → L → L → Instr r L

namespace Instr
variable {r : ℕ} {L L' : Type}

def map (f : L → L') : Instr r L → Instr r L'
  | .go q => .go (f q)
  | .push k b q => .push k b (f q)
  | .pop k q => .pop k (f q)
  | .branch k e z o => .branch k (f e) (f z) (f o)

def eval : Instr r L → Store r → L × Store r
  | .go q,s => (q,s)
  | .push k b q,s => (q,Function.update s k (b::s k))
  | .pop k q,s => (q,Function.update s k (s k).tail)
  | .branch k e z o,s => ((s k).head?.elim e (fun b => if b then o else z),s)

@[simp] theorem eval_map (f : L → L') (i : Instr r L) (s : Store r) :
    (i.map f).eval s = (f (i.eval s).1,(i.eval s).2) := by
  cases i <;> simp only [map,eval]
  rename_i k e z o
  cases h : (s k).head? with
  | none => rfl
  | some b => cases b <;> rfl

abbrev Stmt (r : ℕ) (L : Type) := Turing.TM2.Stmt (fun _ : Fin r => Bool) L (Option Bool)

def target (q : Option L) : Stmt r L :=
  .load (fun _ => none) (q.elim .halt (fun l => .goto (fun _ => l)))

def translate : Instr r (Option L) → Stmt r L
  | .go q => target q
  | .push k b q => .push k (fun _ => b) (target q)
  | .pop k q => .pop k (fun _ _ => none) (target q)
  | .branch k e z o => .peek k (fun _ h => h)
      (.branch Option.isNone (target e) (.branch (fun h => h.getD false) (target o) (target z)))

@[simp] theorem target_step (q : Option L) (v : Option Bool) (s : Store r) :
    Turing.TM2.stepAux (target q) v s = ⟨q,none,s⟩ := by cases q <;> rfl

@[simp] theorem translate_step (i : Instr r (Option L)) (v : Option Bool) (s : Store r) :
    Turing.TM2.stepAux i.translate v s = ⟨(i.eval s).1,none,(i.eval s).2⟩ := by
  cases i with
  | go q => exact target_step q v s
  | push k b q => simp only [translate,Turing.TM2.stepAux,target_step,eval]
  | pop k q => simp only [translate,Turing.TM2.stepAux,target_step,eval]
  | branch k e z o =>
    simp only [translate,Turing.TM2.stepAux,target_step,eval]
    cases h : (s k).head? with
    | none => rfl
    | some b => cases b <;> rfl
end Instr

structure Block (r : ℕ) where
  Label : Type
  finite : Fintype Label
  entry : Label
  code : Label → Instr r (Option Label)

attribute [instance] Block.finite

inductive Steps {r : ℕ} {L : Type} (code : L → Instr r (Option L)) :
    Option L → Store r → Option L → Store r → ℕ → Prop
  | refl (q s) : Steps code q s q s 0
  | next (q s q' s' t)
      (rest : Steps code ((code q).eval s).1 ((code q).eval s).2 q' s' t) :
      Steps code (some q) s q' s' (t+1)

namespace Steps
variable {r : ℕ} {L L' : Type} {code : L → Instr r (Option L)}

theorem trans {q s q' s' q'' s'' t u}
    (h : Steps code q s q' s' t) (h' : Steps code q' s' q'' s'' u) :
    Steps code q s q'' s'' (t+u) := by
  induction h with
  | refl => simpa using h'
  | next q s q' s' t h ih => simpa [Nat.add_right_comm] using Steps.next q s _ _ _ (ih h')

theorem map (code' : L' → Instr r (Option L')) (f : L → L') (last : Option L')
    (hcode : ∀ l, code' (f l)=(code l).map (fun q => q.elim last (some ∘ f)))
    {q s q' s' t} (h : Steps code q s q' s' t) :
    Steps code' (q.elim last (some ∘ f)) s (q'.elim last (some ∘ f)) s' t := by
  induction h with
  | refl => exact .refl _ _
  | next q s q' s' t h ih =>
    apply Steps.next
    simpa only [hcode,Instr.eval_map] using ih

end Steps

namespace Block
variable {r : ℕ}

def primitive (i : Instr r Unit) : Block r where
  Label := Unit
  finite := inferInstance
  entry := ()
  code _ := i.map (fun _ => none)

def seq (a b : Block r) : Block r where
  Label := a.Label ⊕ b.Label
  finite := inferInstance
  entry := .inl a.entry
  code := fun l => match l with
    | .inl q => (a.code q).map (fun t => t.elim (some (.inr b.entry)) (fun u => some (.inl u)))
    | .inr q => (b.code q).map (Option.map Sum.inr)

def cases (k : Fin r) (e z o : Block r) : Block r where
  Label := Unit ⊕ (e.Label ⊕ (z.Label ⊕ o.Label))
  finite := inferInstance
  entry := .inl ()
  code := fun l => match l with
    | .inl _ => .branch k (some (.inr (.inl e.entry)))
        (some (.inr (.inr (.inl z.entry)))) (some (.inr (.inr (.inr o.entry))))
    | .inr (.inl q) => (e.code q).map (Option.map (Sum.inr ∘ Sum.inl))
    | .inr (.inr (.inl q)) => (z.code q).map (Option.map (Sum.inr ∘ Sum.inr ∘ Sum.inl))
    | .inr (.inr (.inr q)) => (o.code q).map (Option.map (Sum.inr ∘ Sum.inr ∘ Sum.inr))

def loop (k : Fin r) (b : Block r) : Block r where
  Label := Unit ⊕ b.Label
  finite := inferInstance
  entry := .inl ()
  code := fun l => match l with
    | .inl _ => .branch k none (some (.inr b.entry)) (some (.inr b.entry))
    | .inr q => (b.code q).map (fun t => t.elim (some (.inl ())) (fun u => some (.inr u)))

abbrev Runs (b : Block r) (s s' : Store r) (t : ℕ) : Prop :=
  Steps b.code (some b.entry) s none s' t

theorem primitive_runs (i : Instr r Unit) (s : Store r) :
    (primitive i).Runs s (i.eval s).2 1 := by
  apply Steps.next
  simp only [primitive,Instr.eval_map]
  exact .refl _ _

theorem seq_runs (a b : Block r) {s s' s'' : Store r} {t u : ℕ}
    (ha : a.Runs s s' t) (hb : b.Runs s' s'' u) : (a.seq b).Runs s s'' (t+u) := by
  have h₁ := ha.map (a.seq b).code Sum.inl (some (Sum.inr b.entry)) (fun _ => rfl)
  have h₂ := hb.map (a.seq b).code Sum.inr none (by
    intro l
    change (b.code l).map _ = (b.code l).map _
    congr 1
    funext t
    cases t <;> rfl)
  exact h₁.trans h₂

end Block
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_StackMacros
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
namespace Block
variable {r : ℕ}

theorem option_map_elim {α β : Type} (f : α → β) :
    Option.map f = fun q => q.elim none (some ∘ f) := by funext q; cases q <;> rfl

theorem cases_runs_empty (k : Fin r) (e z o : Block r) {s s' : Store r} {t : ℕ}
    (hs : s k=[]) (he : e.Runs s s' t) : (cases k e z o).Runs s s' (t+1) := by
  apply Steps.next
  have h := he.map (cases k e z o).code (Sum.inr ∘ Sum.inl) none (by
    intro l
    change (e.code l).map _ = (e.code l).map _
    rw [option_map_elim]; rfl)
  simpa only [cases,Instr.eval,hs,List.head?_nil,Option.elim_none,Option.elim_some,
    Function.comp_apply] using h

theorem cases_runs_false (k : Fin r) (e z o : Block r) {s s' : Store r} {t : ℕ}
    (hs : (s k).head?=some false) (hz : z.Runs s s' t) : (cases k e z o).Runs s s' (t+1) := by
  apply Steps.next
  have h := hz.map (cases k e z o).code (Sum.inr ∘ Sum.inr ∘ Sum.inl) none (by
    intro l
    change (z.code l).map _ = (z.code l).map _
    rw [option_map_elim]; rfl)
  simpa only [cases,Instr.eval,hs,Option.elim_none,Option.elim_some,
    Function.comp_apply,Bool.false_eq_true,ite_false] using h

theorem cases_runs_true (k : Fin r) (e z o : Block r) {s s' : Store r} {t : ℕ}
    (hs : (s k).head?=some true) (ho : o.Runs s s' t) : (cases k e z o).Runs s s' (t+1) := by
  apply Steps.next
  have h := ho.map (cases k e z o).code (Sum.inr ∘ Sum.inr ∘ Sum.inr) none (by
    intro l
    change (o.code l).map _ = (o.code l).map _
    rw [option_map_elim]; rfl)
  simpa only [cases,Instr.eval,hs,Option.elim_none,Option.elim_some,
    Function.comp_apply,ite_true] using h

theorem loop_runs_empty (k : Fin r) (b : Block r) (s : Store r) (hs : s k=[]) :
    (loop k b).Runs s s 1 := by
  apply Steps.next
  simp only [loop,Instr.eval,hs,List.head?_nil,Option.elim_none]
  exact .refl _ _

theorem loop_runs_step (k : Fin r) (b : Block r) {s s' s'' : Store r} {t u : ℕ}
    (hs : s k≠[]) (hb : b.Runs s s' t) (hl : (loop k b).Runs s' s'' u) :
    (loop k b).Runs s s'' (t+u+1) := by
  apply Steps.next
  have h := hb.map (loop k b).code Sum.inr (some (Sum.inl ())) (fun _ => rfl)
  have hh := h.trans hl
  cases he : s k with
  | nil => exact (hs he).elim
  | cons a l =>
    cases a <;> simpa only [loop,Instr.eval,he,List.head?_cons,Option.elim_none,
      Option.elim_some,Function.comp_apply,Bool.false_eq_true,ite_false,ite_true] using hh

def skip : Block r := primitive (.go ())
def push (k : Fin r) (b : Bool) : Block r := primitive (.push k b ())
def pop (k : Fin r) : Block r := primitive (.pop k ())

theorem skip_runs (s : Store r) : skip.Runs s s 1 := primitive_runs _ s

theorem push_runs (k : Fin r) (b : Bool) (s : Store r) :
    (push k b).Runs s (Function.update s k (b::s k)) 1 := primitive_runs _ s

theorem pop_runs (k : Fin r) (s : Store r) :
    (pop k).Runs s (Function.update s k (s k).tail) 1 := primitive_runs _ s

def clear (k : Fin r) : Block r := loop k (pop k)

theorem clear_runs (k : Fin r) (s : Store r) :
    (clear k).Runs s (Function.update s k []) (2*(s k).length+1) := by
  generalize hl : s k=l
  induction l generalizing s with
  | nil =>
    have he : Function.update s k []=s := by rw [←hl,Function.update_eq_self]
    rw [he]
    exact loop_runs_empty k (pop k) s hl
  | cons a l ih =>
    let s' := Function.update s k l
    have hi := ih s' (by simp [s'])
    have hp : (pop k).Runs s s' 1 := by simpa [s',hl] using pop_runs k s
    have hx := loop_runs_step k (pop k) (by simp [hl]) hp hi
    have ht : 1+(2*l.length+1)+1=2*(a::l).length+1 := by simp only [List.length_cons]; omega
    rw [ht] at hx
    simpa only [clear,s',Function.update_idem] using hx

def moveBody (src dst : Fin r) : Block r :=
  cases src skip ((pop src).seq (push dst false)) ((pop src).seq (push dst true))

def reverseInto (src dst : Fin r) : Block r := loop src (moveBody src dst)

theorem moveBody_runs (src dst : Fin r) (hne : src≠dst) (s : Store r) (a : Bool) (l : List Bool)
    (hs : s src=a::l) :
    (moveBody src dst).Runs s (Function.update (Function.update s src l) dst (a::s dst)) 3 := by
  have hp : (pop src).Runs s (Function.update s src l) 1 := by
    simpa only [hs,List.tail_cons] using pop_runs src s
  have ht := push_runs dst a (Function.update s src l)
  rw [Function.update_of_ne hne.symm] at ht
  have hseq : ((pop src).seq (push dst a)).Runs s
      (Function.update (Function.update s src l) dst (a::s dst)) 2 := by
    exact seq_runs _ _ hp ht
  cases a with
  | false => exact cases_runs_false _ _ _ _ (by simp [hs]) hseq
  | true => exact cases_runs_true _ _ _ _ (by simp [hs]) hseq

theorem reverseInto_runs (src dst : Fin r) (hne : src≠dst) (s : Store r) :
    (reverseInto src dst).Runs s
      (Function.update (Function.update s src []) dst ((s src).reverse++s dst))
      (4*(s src).length+1) := by
  generalize hl : s src=l
  induction l generalizing s with
  | nil =>
    have he : Function.update (Function.update s src []) dst ([].reverse++s dst)=s := by
      rw [←hl,Function.update_eq_self]
      simp [hl]
    rw [he]
    exact loop_runs_empty src (moveBody src dst) s hl
  | cons a l ih =>
    let s' := Function.update (Function.update s src l) dst (a::s dst)
    have hs' : s' src=l := by simp [s',hne]
    have hi := ih s' hs'
    have hm := moveBody_runs src dst hne s a l hl
    have hx := loop_runs_step src (moveBody src dst) (by simp [hl]) hm hi
    have he : Function.update (Function.update s' src []) dst (l.reverse++s' dst)=
        Function.update (Function.update s src []) dst ((a::l).reverse++s dst) := by
      funext k
      by_cases hk : k=dst
      · subst k; simp [List.reverse_cons,List.append_assoc,s']
      · by_cases hks : k=src
        · subst k; simp [hne,s']
        · simp [Function.update_of_ne,hk,hks,s']
    rw [he] at hx
    have ht : 3+(4*l.length+1)+1=4*(a::l).length+1 := by simp only [List.length_cons]; omega
    rw [ht] at hx
    exact hx

end Block
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_StackCopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode.Block
variable {r : ℕ}

def moveTwoBody (src dst aux : Fin r) : Block r :=
  cases src skip
    ((pop src).seq ((push dst false).seq (push aux false)))
    ((pop src).seq ((push dst true).seq (push aux true)))

def reverseIntoTwo (src dst aux : Fin r) : Block r := loop src (moveTwoBody src dst aux)

lemma moveTwoBody_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) (a : Bool) (l : List Bool) (hs : s src=a::l) :
    (moveTwoBody src dst aux).Runs s
      (Function.update (Function.update (Function.update s src l) dst (a::s dst)) aux (a::s aux)) 4 := by
  have hp : (pop src).Runs s (Function.update s src l) 1 := by
    simpa only [hs,List.tail_cons] using pop_runs src s
  have hd := push_runs dst a (Function.update s src l)
  rw [Function.update_of_ne hsd.symm] at hd
  have ha := push_runs aux a (Function.update (Function.update s src l) dst (a::s dst))
  rw [Function.update_of_ne hda.symm,Function.update_of_ne hsa.symm] at ha
  have hseq : ((pop src).seq ((push dst a).seq (push aux a))).Runs s
      (Function.update (Function.update (Function.update s src l) dst (a::s dst)) aux (a::s aux)) 3 :=
    seq_runs _ _ hp (seq_runs _ _ hd ha)
  cases a with
  | false => exact cases_runs_false _ _ _ _ (by simp [hs]) hseq
  | true => exact cases_runs_true _ _ _ _ (by simp [hs]) hseq

lemma reverseIntoTwo_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) :
    (reverseIntoTwo src dst aux).Runs s
      (Function.update (Function.update (Function.update s src []) dst ((s src).reverse++s dst))
        aux ((s src).reverse++s aux)) (5*(s src).length+1) := by
  generalize hl : s src=l
  induction l generalizing s with
  | nil =>
    have he : Function.update (Function.update (Function.update s src []) dst ([].reverse++s dst))
        aux ([].reverse++s aux)=s := by
      rw [←hl,Function.update_eq_self]
      simp only [hl,List.reverse_nil,List.nil_append,Function.update_eq_self]
    rw [he]
    exact loop_runs_empty src (moveTwoBody src dst aux) s hl
  | cons a l ih =>
    let s' := Function.update (Function.update (Function.update s src l) dst (a::s dst)) aux (a::s aux)
    have hs' : s' src=l := by simp [s',hsd,hsa]
    have hi := ih s' hs'
    have hm := moveTwoBody_runs src dst aux hsd hsa hda s a l hl
    have hx := loop_runs_step src (moveTwoBody src dst aux) (by simp [hl]) hm hi
    have he : Function.update (Function.update (Function.update s' src []) dst (l.reverse++s' dst))
        aux (l.reverse++s' aux)=
        Function.update (Function.update (Function.update s src []) dst ((a::l).reverse++s dst))
          aux ((a::l).reverse++s aux) := by
      funext k
      by_cases hka : k=aux
      · subst k; simp [List.reverse_cons,List.append_assoc,s']
      · by_cases hkd : k=dst
        · subst k; simp [hda,List.reverse_cons,List.append_assoc,s']
        · by_cases hks : k=src
          · subst k; simp [hsd,hsa,s']
          · simp [Function.update_of_ne,hka,hkd,hks,s']
    rw [he] at hx
    have ht : 4+(5*l.length+1)+1=5*(a::l).length+1 := by simp only [List.length_cons]; omega
    rw [ht] at hx
    exact hx

def copy (src dst aux : Fin r) : Block r :=
  (clear dst).seq ((reverseInto src aux).seq (reverseIntoTwo aux src dst))

lemma copy_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) (ha : s aux=[]) :
    (copy src dst aux).Runs s (Function.update s dst (s src))
      (2*(s dst).length+9*(s src).length+3) := by
  let s₁ := Function.update s dst []
  let s₂ := Function.update (Function.update s₁ src []) aux ((s₁ src).reverse++s₁ aux)
  have h₁ := clear_runs dst s
  have h₂ := reverseInto_runs src aux hsa s₁
  have h₃ := reverseIntoTwo_runs aux src dst hsa.symm hda.symm hsd s₂
  have he : Function.update
      (Function.update (Function.update s₂ aux []) src ((s₂ aux).reverse++s₂ src))
        dst ((s₂ aux).reverse++s₂ dst)=Function.update s dst (s src) := by
    funext k
    by_cases hkd : k=dst
    · subst k; simp [s₂,s₁,hsd,hsa,hda,hsd.symm,hda.symm,ha]
    · by_cases hks : k=src
      · subst k; simp [s₂,s₁,hsd,hsa,hda,hsd.symm,hda.symm,ha]
      · by_cases hka : k=aux
        · subst k; simp [s₂,s₁,hsd,hsa,hda,ha,Ne.symm]
        · simp [s₂,s₁,Function.update_of_ne,hkd,hks,hka]
  rw [he] at h₃
  have hh := seq_runs (clear dst) _ h₁ (seq_runs _ _ h₂ h₃)
  change (copy src dst aux).Runs s (Function.update s dst (s src)) _ at hh
  have hlen₁ : (s₁ src).length=(s src).length := by simp [s₁,hsd]
  have hlen₂ : (s₂ aux).length=(s src).length := by simp [s₂,s₁,hsd,hda.symm,ha]
  rw [hlen₁,hlen₂] at hh
  have ht : (2*(s dst).length+1)+(4*(s src).length+1+(5*(s src).length+1))=
      2*(s dst).length+9*(s src).length+3 := by omega
  rw [ht] at hh
  exact hh

end BinaryMatching.StackCode.Block
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_StackEmbed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode

noncomputable def liftStore {r R : ℕ} (f : Fin r → Fin R) (s : Store r) (base : Store R) : Store R :=
  fun k => if h : ∃ i,f i=k then s h.choose else base k

lemma liftStore_at {r R : ℕ} (f : Fin r → Fin R) (hf : Function.Injective f)
    (s : Store r) (base : Store R) (i : Fin r) : liftStore f s base (f i)=s i := by
  classical
  unfold liftStore
  have h : ∃ j,f j=f i := ⟨i,rfl⟩
  rw [dite_eq_left h]
  rw [hf h.choose_spec]

lemma liftStore_outside {r R : ℕ} (f : Fin r → Fin R) (s : Store r) (base : Store R)
    (k : Fin R) (hk : ∀ i,f i≠k) : liftStore f s base k=base k := by
  classical
  exact dite_eq_right (by simpa only [not_exists] using hk)

lemma liftStore_update {r R : ℕ} (f : Fin r → Fin R) (hf : Function.Injective f)
    (s : Store r) (base : Store R) (i : Fin r) (v : List Bool) :
    liftStore f (Function.update s i v) base=Function.update (liftStore f s base) (f i) v := by
  classical
  funext k
  by_cases hk : ∃ j,f j=k
  · obtain ⟨j,rfl⟩ := hk
    rw [liftStore_at f hf]
    by_cases hji : j=i
    · subst j; simp
    · rw [Function.update_of_ne hji,Function.update_of_ne (fun h => hji (hf h)),liftStore_at f hf]
  · have ho : ∀ j,f j≠k := by simpa only [not_exists] using hk
    rw [liftStore_outside f _ base k ho,Function.update_of_ne (ho i).symm,
      liftStore_outside f _ base k ho]

lemma liftStore_eq {r R : ℕ} (f : Fin r → Fin R) (s : Store r) (base : Store R)
    (h : ∀ i,base (f i)=s i) : liftStore f s base=base := by
  classical
  funext k
  unfold liftStore
  split_ifs with hk
  · rw [←h, hk.choose_spec]
  · rfl

namespace Instr
variable {r R : ℕ} {L : Type}

def rename (f : Fin r → Fin R) : Instr r L → Instr R L
  | .go q => .go q
  | .push k b q => .push (f k) b q
  | .pop k q => .pop (f k) q
  | .branch k e z o => .branch (f k) e z o

lemma eval_rename (f : Fin r → Fin R) (hf : Function.Injective f) (i : Instr r L)
    (s : Store r) (base : Store R) :
    (i.rename f).eval (liftStore f s base)=((i.eval s).1,liftStore f (i.eval s).2 base) := by
  cases i with
  | go q => rfl
  | push k b q => simp only [rename,eval,liftStore_at f hf,liftStore_update f hf]
  | pop k q => simp only [rename,eval,liftStore_at f hf,liftStore_update f hf]
  | branch k e z o => simp only [rename,eval,liftStore_at f hf]
end Instr

namespace Steps
variable {r R : ℕ} {L : Type} {code : L → Instr r (Option L)}

lemma rename (f : Fin r → Fin R) (hf : Function.Injective f) (base : Store R)
    {q s q' s' t} (h : Steps code q s q' s' t) :
    Steps (fun l => (code l).rename f) q (liftStore f s base) q' (liftStore f s' base) t := by
  induction h with
  | refl => exact .refl _ _
  | next q s q' s' t h ih =>
    apply Steps.next
    simpa only [Instr.eval_rename f hf] using ih
end Steps

namespace Block
variable {r R : ℕ}

def rename (b : Block r) (f : Fin r → Fin R) : Block R where
  Label := b.Label
  finite := b.finite
  entry := b.entry
  code l := (b.code l).rename f

lemma rename_runs (b : Block r) (f : Fin r → Fin R) (hf : Function.Injective f)
    (base : Store R) {s s' : Store r} {t : ℕ} (h : b.Runs s s' t) :
    (b.rename f).Runs (liftStore f s base) (liftStore f s' base) t := h.rename f hf base

end Block
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_StackRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Finset Polynomial

lemma polynomial_eval_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  simp only [Polynomial.eval_eq_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i)

def volume {r : ℕ} (s : Store r) : ℕ := ∑ i,(s i).length

lemma volume_update {r : ℕ} (s : Store r) (k : Fin r) (v : List Bool) :
    volume (Function.update s k v)+(s k).length=volume s+v.length := by
  classical
  simp only [volume]
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ k),
    ←Finset.sum_erase_add (Finset.univ) (fun i => (s i).length) (Finset.mem_univ k)]
  simp only [Function.update_self]
  have he : ∑ i∈Finset.univ.erase k,(Function.update s k v i).length =
      ∑ i∈Finset.univ.erase k,(s i).length := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [he]
  omega

lemma volume_instruction {r : ℕ} {L : Type} (i : Instr r L) (s : Store r) :
    volume (i.eval s).2≤volume s+1 := by
  cases i with
  | go q => exact Nat.le_succ _
  | push k b q =>
    have h := volume_update s k (b::s k)
    simp only [Instr.eval,List.length_cons] at *
    omega
  | pop k q =>
    have h := volume_update s k (s k).tail
    have hh : (s k).tail.length≤(s k).length := by simp
    simp only [Instr.eval] at *
    omega
  | branch k e z o => exact Nat.le_succ _

lemma Steps.volume_bound {r : ℕ} {L : Type} {code : L → Instr r (Option L)}
    {q s q' s' t} (h : Steps code q s q' s' t) : volume s'≤volume s+t := by
  induction h with
  | refl => exact le_rfl
  | next q s q' s' t h ih =>
    have he := volume_instruction (code q) s
    omega

lemma volume_single {r : ℕ} (k : Fin r) (s : List Bool) :
    volume (Function.update (fun _ => []) k s)=s.length := by
  classical
  unfold volume
  rw [Finset.sum_eq_single k]
  · simp
  · intro i hi hik
    simp [Function.update_of_ne hik]
  · simp

structure Routine {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) where
  scratch : ℕ
  block : Block (scratch+1)
  time : Polynomial ℕ
  correct : ∀ a, ∃ t≤time.eval (ea a).length,
    block.Runs (Function.update (fun _ => []) 0 (ea a))
      (Function.update (fun _ => []) 0 (eb (f a))) t

namespace Routine
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
  {ec : γ → List Bool} {f : α → β} {g : β → γ}

lemma length_bound (p : Routine ea eb f) (a : α) :
    (eb (f a)).length≤(ea a).length+p.time.eval (ea a).length := by
  obtain ⟨t,ht,h⟩ := p.correct a
  have hv := h.volume_bound
  simp only [volume_single] at hv
  omega

def embedding (r s : ℕ) : Fin (r+1) → Fin (r+s+1) :=
  Fin.castLE (by omega)

lemma embedding_injective (r s : ℕ) : Function.Injective (embedding r s) := by
  intro a b h
  exact Fin.ext (congrArg (fun x : Fin (r+s+1) => x.val) h)

lemma lift_initial {r R : ℕ} (hR : 0<R) (f : Fin (r+1) → Fin R) (hf : Function.Injective f)
    (hz : f 0=⟨0,hR⟩) (v : List Bool) :
    liftStore f (Function.update (fun _ => []) 0 v) (fun _ => [])=
      Function.update (fun _ => []) ⟨0,hR⟩ v := by
  rw [liftStore_update f hf,hz]
  congr 1
  exact liftStore_eq f _ _ (fun _ => rfl)

noncomputable def comp (p : Routine ea eb f) (q : Routine eb ec g) : Routine ea ec (g ∘ f) where
  scratch := p.scratch+q.scratch
  block := (p.block.rename (embedding p.scratch q.scratch)).seq
    (q.block.rename (fun i => ⟨i.val,by have := i.isLt; omega⟩))
  time := p.time+q.time.comp (X+p.time)
  correct a := by
    obtain ⟨t,ht,hp⟩ := p.correct a
    obtain ⟨u,hu,hq⟩ := q.correct (f a)
    let f₁ := embedding p.scratch q.scratch
    let f₂ : Fin (q.scratch+1) → Fin (p.scratch+q.scratch+1) :=
      fun i => ⟨i.val,by have := i.isLt; omega⟩
    have hf₁ : Function.Injective f₁ := embedding_injective _ _
    have hf₂ : Function.Injective f₂ := by
      intro i j h
      exact Fin.ext (congrArg (fun x : Fin (p.scratch+q.scratch+1) => x.val) h)
    have hm₁ := p.block.rename_runs f₁ hf₁ (fun _ => []) hp
    have hm₂ := q.block.rename_runs f₂ hf₂ (fun _ => []) hq
    rw [lift_initial (by omega) f₁ hf₁ rfl,lift_initial (by omega) f₁ hf₁ rfl] at hm₁
    rw [lift_initial (by omega) f₂ hf₂ rfl,lift_initial (by omega) f₂ hf₂ rfl] at hm₂
    refine ⟨t+u,?_,Block.seq_runs _ _ hm₁ hm₂⟩
    simp only [Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_X]
    exact Nat.add_le_add ht (hu.trans (polynomial_eval_mono q.time (p.length_bound a)))

end Routine
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_StackPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode

def pairBits : List Bool → List Bool → List Bool
  | [],y => true::y
  | b::x,y => false::b::pairBits x y

@[simp] lemma pairBits_length (x y : List Bool) : (pairBits x y).length=2*x.length+y.length+1 := by
  induction x with
  | nil => simp [pairBits]
  | cons b x ih => simp only [pairBits,List.length_cons,ih]; omega

namespace Block
variable {r : ℕ}

def tagBody (src dst : Fin r) : Block r :=
  cases src skip ((pop src).seq ((push dst false).seq (push dst false)))
    ((pop src).seq ((push dst true).seq (push dst false)))

def tagAll (src dst : Fin r) : Block r := loop src (tagBody src dst)

lemma tagBody_runs (src dst : Fin r) (hne : src≠dst) (s : Store r) (b : Bool) (l : List Bool)
    (hs : s src=b::l) :
    (tagBody src dst).Runs s (Function.update (Function.update s src l) dst (false::b::s dst)) 4 := by
  have hp : (pop src).Runs s (Function.update s src l) 1 := by
    simpa only [hs,List.tail_cons] using pop_runs src s
  have hb := push_runs dst b (Function.update s src l)
  rw [Function.update_of_ne hne.symm] at hb
  have hf := push_runs dst false (Function.update (Function.update s src l) dst (b::s dst))
  simp only [Function.update_self,Function.update_idem] at hf
  have hx := seq_runs _ _ hp (seq_runs _ _ hb hf)
  cases b with
  | false => exact cases_runs_false _ _ _ _ (by simp [hs]) hx
  | true => exact cases_runs_true _ _ _ _ (by simp [hs]) hx

lemma pairBits_eq (x y : List Bool) :
    pairBits x y=x.flatMap (fun b => [false,b])++true::y := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [pairBits,ih]

lemma tagAll_runs (src dst : Fin r) (hne : src≠dst) (x y : List Bool) (s : Store r)
    (hs : s src=x.reverse) (hd : s dst=y) :
    (tagAll src dst).Runs s
      (Function.update (Function.update s src []) dst (x.flatMap (fun b => [false,b])++y))
      (5*x.length+1) := by
  induction x using List.reverseRecOn generalizing y s with
  | nil =>
    have he : Function.update (Function.update s src []) dst
        ([].flatMap (fun b => [false,b])++y)=s := by
      simp only [List.reverse_nil] at hs
      simp only [List.flatMap_nil,List.nil_append]
      rw [←hs,Function.update_eq_self,←hd,Function.update_eq_self]
    rw [he]
    apply loop_runs_empty
    simpa using hs
  | append_singleton x b ih =>
    have hs' : s src=b::x.reverse := by simpa using hs
    let s' := Function.update (Function.update s src x.reverse) dst (false::b::s dst)
    have hm := tagBody_runs src dst hne s b x.reverse hs'
    have hi := ih (false::b::y) s' (by simp [s',hne]) (by simp [s',hd])
    have hx := loop_runs_step src (tagBody src dst) (by simp [hs']) hm hi
    have he : Function.update (Function.update s' src []) dst
        (x.flatMap (fun b => [false,b])++false::b::y)=
        Function.update (Function.update s src []) dst
          ((x++[b]).flatMap (fun b => [false,b])++y) := by
      funext k
      by_cases hk : k=dst
      · subst k; simp [List.flatMap_append,List.append_assoc]
      · by_cases hks : k=src
        · subst k; simp [s',hne]
        · simp [s',Function.update_of_ne,hk,hks]
    rw [he] at hx
    have ht : 4+(5*x.length+1)+1=5*(x++[b]).length+1 := by simp; omega
    rw [ht] at hx
    exact hx

def pairInto (src dst aux : Fin r) : Block r :=
  (reverseInto src aux).seq ((push dst true).seq (tagAll aux dst))

lemma pairInto_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) (ha : s aux=[]) :
    (pairInto src dst aux).Runs s
      (Function.update (Function.update s src []) dst (pairBits (s src) (s dst)))
      (9*(s src).length+3) := by
  let s₁ := Function.update (Function.update s src []) aux ((s src).reverse++s aux)
  let s₂ := Function.update s₁ dst (true::s₁ dst)
  have h₁ := reverseInto_runs src aux hsa s
  have h₂ := push_runs dst true s₁
  have h₃ := tagAll_runs aux dst hda.symm (s src) (true::s dst) s₂
    (by simp [s₂,s₁,hda.symm,ha]) (by simp [s₂,s₁,hda,hsd.symm])
  rw [←pairBits_eq] at h₃
  have he : Function.update (Function.update s₂ aux []) dst (pairBits (s src) (s dst))=
      Function.update (Function.update s src []) dst (pairBits (s src) (s dst)) := by
    funext k
    by_cases hkd : k=dst
    · subst k; simp
    · by_cases hks : k=src
      · subst k; simp [s₂,s₁,hsd,hsa]
      · by_cases hka : k=aux
        · subst k; simp [s₂,s₁,ha,hda.symm,hsa.symm]
        · simp [s₂,s₁,Function.update_of_ne,hkd,hks,hka]
  rw [he] at h₃
  have hx := seq_runs _ _ h₁ (seq_runs _ _ h₂ h₃)
  have ht : (4*(s src).length+1)+(1+(5*(s src).length+1))=9*(s src).length+3 := by omega
  rw [ht] at hx
  exact hx

def moveInto (src dst aux : Fin r) : Block r :=
  (reverseInto src aux).seq (reverseInto aux dst)

lemma moveInto_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) (hd : s dst=[]) (ha : s aux=[]) :
    (moveInto src dst aux).Runs s
      (Function.update (Function.update s src []) dst (s src)) (8*(s src).length+2) := by
  let s' := Function.update (Function.update s src []) aux ((s src).reverse++s aux)
  have h₁ := reverseInto_runs src aux hsa s
  have h₂ := reverseInto_runs aux dst hda.symm s'
  have he : Function.update (Function.update s' aux []) dst ((s' aux).reverse++s' dst)=
      Function.update (Function.update s src []) dst (s src) := by
    funext k
    by_cases hkd : k=dst
    · subst k; simp [s',ha,hd,hda,hsd.symm]
    · by_cases hks : k=src
      · subst k; simp [s',hsd,hsa]
      · by_cases hka : k=aux
        · subst k; simp [ha,hda.symm,hsa.symm]
        · simp [s',Function.update_of_ne,hkd,hks,hka]
  rw [he] at h₂
  have hh := seq_runs _ _ h₁ h₂
  have hl : (s' aux).length=(s src).length := by simp [s',ha]
  rw [hl] at hh
  have ht : (4*(s src).length+1)+(4*(s src).length+1)=8*(s src).length+2 := by omega
  rw [ht] at hh
  exact hh

def decodeRev (src dst : Fin r) : Block r where
  Label := Fin 7
  finite := inferInstance
  entry := 0
  code k := match k.val with
    | 0 => .branch src none (some 1) (some 6)
    | 1 => .pop src (some 2)
    | 2 => .branch src none (some 3) (some 4)
    | 3 => .push dst false (some 5)
    | 4 => .push dst true (some 5)
    | 5 => .pop src (some 0)
    | _ => .pop src none

lemma decodeRev_runs (src dst : Fin r) (hne : src≠dst) (x y : List Bool) (s : Store r)
    (hs : s src=pairBits x y) :
    (decodeRev src dst).Runs s
      (Function.update (Function.update s src y) dst (x.reverse++s dst)) (5*x.length+2) := by
  induction x generalizing s with
  | nil =>
    have hx : s src=true::y := hs
    have he : Function.update (Function.update s src y) dst ([].reverse++s dst)=
        Function.update s src y := by
      simp only [List.reverse_nil,List.nil_append]
      rw [←Function.update_of_ne hne.symm y s,Function.update_eq_self]
    rw [he]
    apply Steps.next
    simp [decodeRev,Instr.eval,hx]
    apply Steps.next
    simp [Instr.eval,hx]
    exact .refl _ _
  | cons b x ih =>
    let s' := Function.update (Function.update s dst (b::s dst)) src (pairBits x y)
    have hs' : s' src=pairBits x y := by simp [s']
    have hi := ih s' hs'
    have he : Function.update (Function.update s' src y) dst (x.reverse++s' dst)=
        Function.update (Function.update s src y) dst ((b::x).reverse++s dst) := by
      funext k
      by_cases hkd : k=dst
      · subst k; simp [s',hne.symm,List.reverse_cons,List.append_assoc]
      · by_cases hks : k=src
        · subst k; simp [s',hne]
        · simp [s',Function.update_of_ne,hkd,hks]
    rw [he] at hi
    have ht : 5*(b::x).length+2=(5*x.length+2)+1+1+1+1+1 := by simp; omega
    rw [ht]
    apply Steps.next
    simp [decodeRev,Instr.eval,hs,pairBits]
    apply Steps.next
    simp [Instr.eval,hs,pairBits]
    cases b <;>
      (apply Steps.next
       simp [Instr.eval]
       apply Steps.next
       simp [Instr.eval,hne.symm]
       apply Steps.next
       simp [Instr.eval,hne]
       convert hi using 1; simp [s',Function.update_comm hne,Function.update_idem,Block.Runs,decodeRev])

end Block
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_StackFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode

lemma lift_clean {r R : ℕ} (f : Fin (r+1) → Fin R) (hf : Function.Injective f)
    (s : Store R) (hs : ∀ i : Fin (r+1), i≠0 → s (f i)=[]) (v : List Bool) :
    liftStore f (Function.update (fun _ => []) 0 v) s=Function.update s (f 0) v := by
  classical
  funext k
  by_cases hk : ∃ i,f i=k
  · obtain ⟨i,rfl⟩ := hk
    rw [liftStore_at f hf]
    by_cases hi : i=0
    · subst i; simp
    · rw [Function.update_of_ne hi,Function.update_of_ne (fun h => hi (hf h)),hs i hi]
  · rw [liftStore_outside f _ _ k (by simpa only [not_exists] using hk),
      Function.update_of_ne (fun h => hk ⟨0,h.symm⟩)]

namespace Routine
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

lemma run_at (p : Routine ea eb f) {R : ℕ} (ι : Fin (p.scratch+1) → Fin R)
    (hι : Function.Injective ι) (s : Store R) (a : α)
    (hinput : s (ι 0)=ea a) (hclean : ∀ i, i≠0 → s (ι i)=[]) :
    ∃ t ≤ p.time.eval (ea a).length,
      (p.block.rename ι).Runs s (Function.update s (ι 0) (eb (f a))) t := by
  obtain ⟨t,ht,h⟩ := p.correct a
  have hh := p.block.rename_runs ι hι s h
  rw [lift_clean ι hι s hclean,lift_clean ι hι s hclean,
    ←hinput,Function.update_eq_self] at hh
  exact ⟨t,ht,hh⟩

noncomputable def reindex {α' β' : Type} (p : Routine ea eb f) (ea' : α' → List Bool)
    (eb' : β' → List Bool) (f' : α' → β') (u : α' → α)
    (hin : ∀ a,ea (u a)=ea' a) (hout : ∀ a,eb (f (u a))=eb' (f' a)) :
    Routine ea' eb' f' where
  scratch := p.scratch
  block := p.block
  time := p.time
  correct a := by simpa only [hin,hout] using p.correct (u a)

noncomputable def identity (ea : α → List Bool) : Routine ea ea id where
  scratch := 0
  block := Block.skip
  time := 1
  correct a := ⟨1,by simp,Block.skip_runs _⟩

end Routine
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_PairRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

namespace PairRegisters

def left (p q : ℕ) (i : Fin (p+1)) : Fin (p+q+3) := ⟨i.val,by have := i.isLt; omega⟩
def right (p q : ℕ) (i : Fin (q+1)) : Fin (p+q+3) := ⟨p+1+i.val,by have := i.isLt; omega⟩
def aux (p q : ℕ) : Fin (p+q+3) := ⟨p+q+2,by omega⟩

@[simp] lemma left_zero (p q : ℕ) : left p q 0=0 := rfl
lemma left_inj (p q : ℕ) : Function.Injective (left p q) := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin (p+q+3) => k.val) h)
lemma right_inj (p q : ℕ) : Function.Injective (right p q) := by
  intro i j h
  have hh := congrArg (fun k : Fin (p+q+3) => k.val) h
  simp only [right] at hh
  exact Fin.ext (by omega)
@[simp] lemma left_ne_right (p q : ℕ) (i : Fin (p+1)) (j : Fin (q+1)) : left p q i≠right p q j := by
  intro h
  have hh := congrArg (fun k : Fin (p+q+3) => k.val) h
  simp only [left,right] at hh
  have := i.isLt
  omega
@[simp] lemma left_ne_aux (p q : ℕ) (i : Fin (p+1)) : left p q i≠aux p q := by
  intro h
  have hh := congrArg (fun k : Fin (p+q+3) => k.val) h
  simp only [left,aux] at hh
  have := i.isLt
  omega
@[simp] lemma right_ne_aux (p q : ℕ) (i : Fin (q+1)) : right p q i≠aux p q := by
  intro h
  have hh := congrArg (fun k : Fin (p+q+3) => k.val) h
  simp only [right,aux] at hh
  have := i.isLt
  omega
@[simp] lemma zero_ne_right (p q : ℕ) (j : Fin (q+1)) : (0:Fin (p+q+3))≠right p q j :=
  left_ne_right p q 0 j
@[simp] lemma zero_ne_aux (p q : ℕ) : (0:Fin (p+q+3))≠aux p q := left_ne_aux p q 0

end PairRegisters

namespace Routine
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
  {ec : γ → List Bool} {f : α → β} {g : α → γ}

noncomputable def pair (p : Routine ea eb f) (q : Routine ea ec g) :
    Routine ea (fun z : β×γ => pairBits (eb z.1) (ec z.2)) (fun a => (f a,g a)) where
  scratch := p.scratch+q.scratch+2
  block :=
    let fst := (0:Fin (p.scratch+q.scratch+3))
    let snd := PairRegisters.right p.scratch q.scratch 0
    let aux := PairRegisters.aux p.scratch q.scratch
    (Block.copy fst snd aux).seq
      ((p.block.rename (PairRegisters.left p.scratch q.scratch)).seq
        ((q.block.rename (PairRegisters.right p.scratch q.scratch)).seq
          ((Block.pairInto fst snd aux).seq (Block.moveInto snd fst aux))))
  time := 100*(X+p.time+q.time+1)
  correct a := by
    let R := p.scratch+q.scratch+3
    let d := PairRegisters.right p.scratch q.scratch 0
    let aux := PairRegisters.aux p.scratch q.scratch
    have h0d : (0:Fin R)≠d := PairRegisters.zero_ne_right _ _ _
    have h0a : (0:Fin R)≠aux := PairRegisters.zero_ne_aux _ _
    have hda : d≠aux := PairRegisters.right_ne_aux _ _ _
    let s₀ : Store R := Function.update (fun _ => []) 0 (ea a)
    let s₁ := Function.update s₀ d (ea a)
    let s₂ := Function.update s₁ 0 (eb (f a))
    let s₃ := Function.update s₂ d (ec (g a))
    let s₄ := Function.update (Function.update s₃ 0 []) d (pairBits (eb (f a)) (ec (g a)))
    have hc : (Block.copy 0 d aux).Runs s₀ s₁ (9*(ea a).length+3) := by
      simpa [s₀,s₁,h0d.symm] using Block.copy_runs 0 d aux h0d h0a hda s₀
        (by simp [s₀,h0a.symm])
    obtain ⟨t,ht,hp⟩ := p.run_at (PairRegisters.left p.scratch q.scratch)
      (PairRegisters.left_inj _ _) s₁ a (by simp [s₁,s₀,h0d]) (by
        intro i hi
        have hne : PairRegisters.left p.scratch q.scratch i≠0 := by
          simpa only [←PairRegisters.left_zero p.scratch q.scratch] using
            (fun h => hi (PairRegisters.left_inj _ _ h))
        simp [s₁,s₀,d,PairRegisters.left_ne_right,hne])
    obtain ⟨u,hu,hq⟩ := q.run_at (PairRegisters.right p.scratch q.scratch)
      (PairRegisters.right_inj _ _) s₂ a (by
        change s₂ d=ea a
        simp [s₂,s₁,h0d.symm]) (by
        intro i hi
        have hne : PairRegisters.right p.scratch q.scratch i≠d :=
          fun h => hi (PairRegisters.right_inj _ _ h)
        have hn0 : PairRegisters.right p.scratch q.scratch i≠0 :=
          (PairRegisters.zero_ne_right _ _ _).symm
        simp [s₂,s₁,s₀,Function.update_of_ne,hne,hn0])
    change (p.block.rename (PairRegisters.left _ _)).Runs s₁ s₂ t at hp
    change (q.block.rename (PairRegisters.right _ _)).Runs s₂ s₃ u at hq
    have h₃ : (Block.pairInto 0 d aux).Runs s₃ s₄ (9*(eb (f a)).length+3) := by
      simpa [s₄,s₃,s₂,h0d] using Block.pairInto_runs 0 d aux h0d h0a hda s₃
        (by simp [s₃,s₂,s₁,s₀,h0a.symm,hda.symm])
    have h₄ := Block.moveInto_runs d 0 aux h0d.symm hda h0a s₄
      (by simp [s₄,h0d]) (by simp [s₄,s₃,s₂,s₁,s₀,h0a.symm,hda.symm])
    have hf : Function.update (Function.update s₄ d []) 0 (s₄ d)=
        Function.update (fun _ => []) 0 (pairBits (eb (f a)) (ec (g a))) := by
      funext k
      by_cases hk : k=0
      · subst k; simp [s₄]
      · by_cases hkd : k=d
        · subst k; simp [h0d.symm]
        · simp [s₄,s₃,s₂,s₁,s₀,Function.update_of_ne,hk,hkd]
    rw [hf] at h₄
    have hlen : (s₄ d).length=(pairBits (eb (f a)) (ec (g a))).length := by simp [s₄]
    rw [hlen] at h₄
    have hrun := Block.seq_runs _ _ hc (Block.seq_runs _ _ hp
      (Block.seq_runs _ _ hq (Block.seq_runs _ _ h₃ h₄)))
    refine ⟨_,?_,hrun⟩
    simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one,pairBits_length]
    have hf := p.length_bound a
    have hg := q.length_bound a
    omega

end Routine
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_ProjectionRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Routine
variable {α β : Type} (ea : α → List Bool) (eb : β → List Bool)

noncomputable def first :
    Routine (fun z : α×β => pairBits (ea z.1) (eb z.2)) ea Prod.fst where
  scratch := 1
  block := (Block.decodeRev 0 1).seq ((Block.clear 0).seq (Block.reverseInto 1 0))
  time := 10*X+10
  correct a := by
    let s₀ : Store 2 := Function.update (fun _ => []) 0 (pairBits (ea a.1) (eb a.2))
    let s₁ := Function.update (Function.update s₀ 0 (eb a.2)) 1 (ea a.1).reverse
    let s₂ := Function.update s₁ 0 []
    have h₁ : (Block.decodeRev 0 1).Runs s₀ s₁ (5*(ea a.1).length+2) := by
      simpa [s₁,s₀] using Block.decodeRev_runs (0:Fin 2) 1 (by decide) (ea a.1) (eb a.2)
        s₀ (by simp [s₀])
    have h₂ : (Block.clear 0).Runs s₁ s₂ (2*(eb a.2).length+1) := by
      simpa [s₁] using Block.clear_runs (0:Fin 2) s₁
    have h₃ := Block.reverseInto_runs (1:Fin 2) 0 (by decide) s₂
    have he : Function.update (Function.update s₂ 1 []) 0 ((s₂ 1).reverse++s₂ 0)=
        Function.update (fun _ => []) 0 (ea a.1) := by
      funext k
      fin_cases k <;> simp [s₂,s₁,s₀]
    rw [he] at h₃
    have hl : (s₂ 1).length=(ea a.1).length := by simp [s₂,s₁]
    rw [hl] at h₃
    refine ⟨_,?_,Block.seq_runs _ _ h₁ (Block.seq_runs _ _ h₂ h₃)⟩
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,pairBits_length]
    omega

noncomputable def second :
    Routine (fun z : α×β => pairBits (ea z.1) (eb z.2)) eb Prod.snd where
  scratch := 1
  block := (Block.decodeRev 0 1).seq (Block.clear 1)
  time := 10*X+10
  correct a := by
    let s₀ : Store 2 := Function.update (fun _ => []) 0 (pairBits (ea a.1) (eb a.2))
    let s₁ := Function.update (Function.update s₀ 0 (eb a.2)) 1 (ea a.1).reverse
    have h₁ : (Block.decodeRev 0 1).Runs s₀ s₁ (5*(ea a.1).length+2) := by
      simpa [s₁,s₀] using Block.decodeRev_runs (0:Fin 2) 1 (by decide) (ea a.1) (eb a.2)
        s₀ (by simp [s₀])
    have h₂ := Block.clear_runs (1:Fin 2) s₁
    have he : Function.update s₁ 1 []=Function.update (fun _ => []) 0 (eb a.2) := by
      funext k
      fin_cases k <;> simp [s₁,s₀]
    rw [he] at h₂
    have hl : (s₁ 1).length=(ea a.1).length := by simp [s₁]
    rw [hl] at h₂
    refine ⟨_,?_,Block.seq_runs _ _ h₁ h₂⟩
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,pairBits_length]
    omega

end Routine
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_SelectRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Block
variable {r : ℕ}
def dropTwo (k : Fin r) : Block r := (pop k).seq (pop k)
lemma dropTwo_runs (k : Fin r) (s : Store r) (a b : Bool) (l : List Bool)
    (hs : s k=a::b::l) :
    (dropTwo k).Runs s (Function.update s k l) 2 := by
  have h₁ := pop_runs k s
  have h₂ := pop_runs k (Function.update s k (s k).tail)
  have h := seq_runs _ _ h₁ h₂
  simpa [dropTwo,hs,Function.update_idem] using h

def emit (k : Fin r) : List Bool → Block r
  | [] => skip
  | b::l => (emit k l).seq (push k b)
lemma emit_runs (k : Fin r) (x : List Bool) (s : Store r) :
    (emit k x).Runs s (Function.update s k (x++s k)) (x.length+1) := by
  induction x with
  | nil => simpa [emit] using skip_runs s
  | cons b x ih =>
    have h := seq_runs _ _ ih (push_runs k b (Function.update s k (x++s k)))
    simpa [emit,Function.update_idem,Nat.add_assoc] using h
end Block
namespace Routine
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
  {f g : α → β}

noncomputable def constant (ea : α → List Bool) (eb : β → List Bool) (b : β) :
    Routine ea eb (fun _ => b) where
  scratch := 0
  block := (Block.clear 0).seq (Block.emit 0 (eb b))
  time := 2*X+C ((eb b).length+2)
  correct a := by
    have h := Block.seq_runs _ _ (Block.clear_runs (0:Fin 1)
      (Function.update (fun _ => []) 0 (ea a)))
      (Block.emit_runs (0:Fin 1) (eb b)
        (Function.update (Function.update (fun _ => []) 0 (ea a)) 0 []))
    refine ⟨2*(ea a).length+1+((eb b).length+1),?_,?_⟩
    · simpa only [eval_add,eval_mul,eval_ofNat,eval_X,eval_C,Function.update_self]
        using (show 2*(ea a).length+1+((eb b).length+1)≤2*(ea a).length+((eb b).length+2) by omega)
    · simpa only [Function.update_idem,Function.update_self,List.append_nil] using h

noncomputable def select (p : Routine ea eb f) (q : Routine ea eb g) :
    Routine (fun z : Bool×α => pairBits [z.1] (ea z.2)) eb
      (fun z => if z.1 then g z.2 else f z.2) where
  scratch := p.scratch+q.scratch
  block :=
    let ι : Fin (p.scratch+1) → Fin (p.scratch+q.scratch+1) :=
      fun i => ⟨i.val,by have := i.isLt; omega⟩
    let κ : Fin (q.scratch+1) → Fin (p.scratch+q.scratch+1) :=
      fun i => ⟨i.val,by have := i.isLt; omega⟩
    (Block.pop 0).seq (Block.cases 0 Block.skip
      ((Block.dropTwo 0).seq (p.block.rename ι))
      ((Block.dropTwo 0).seq (q.block.rename κ)))
  time := p.time+q.time+4
  correct z := by
    let R := p.scratch+q.scratch+1
    let ι : Fin (p.scratch+1) → Fin R := fun i => ⟨i.val,by have := i.isLt; omega⟩
    let κ : Fin (q.scratch+1) → Fin R := fun i => ⟨i.val,by have := i.isLt; omega⟩
    have hι : Function.Injective ι := fun i j h => Fin.ext (congrArg (fun k : Fin R => k.val) h)
    have hκ : Function.Injective κ := fun i j h => Fin.ext (congrArg (fun k : Fin R => k.val) h)
    let s₀ : Store R := Function.update (fun _ => []) 0 (pairBits [z.1] (ea z.2))
    let s₁ : Store R := Function.update (fun _ => []) 0 (z.1::true::ea z.2)
    let s₂ : Store R := Function.update (fun _ => []) 0 (ea z.2)
    have hp : (Block.pop 0).Runs s₀ s₁ 1 := by
      simpa [s₀,s₁,pairBits,Function.update_idem] using Block.pop_runs (0:Fin R) s₀
    have hd : (Block.dropTwo 0).Runs s₁ s₂ 2 := by
      simpa [s₁,s₂,Function.update_idem] using Block.dropTwo_runs (0:Fin R) s₁ z.1 true
        (ea z.2) (by simp [s₁])
    have hp₀ := p.run_at ι hι s₂ z.2 (by simp [s₂,ι]) (by
      intro i hi
      have hk : ι i≠0 := fun h => hi (hι h)
      simp [s₂,Function.update_of_ne hk])
    have hq₀ := q.run_at κ hκ s₂ z.2 (by simp [s₂,κ]) (by
      intro i hi
      have hk : κ i≠0 := fun h => hi (hκ h)
      simp [s₂,Function.update_of_ne hk])
    have hlen : (ea z.2).length≤(pairBits [z.1] (ea z.2)).length := by
      simp only [pairBits_length,List.length_singleton]
      omega
    have ht₁ := polynomial_eval_mono p.time hlen
    have ht₂ := polynomial_eval_mono q.time hlen
    rcases z with ⟨b,a⟩
    cases b with
    | false =>
      obtain ⟨t,ht,hr⟩ := hp₀
      have hx := Block.cases_runs_false (0:Fin R) Block.skip
        ((Block.dropTwo 0).seq (p.block.rename ι)) ((Block.dropTwo 0).seq (q.block.rename κ))
        (by simp [s₁]) (Block.seq_runs _ _ hd hr)
      refine ⟨1+(2+t+1),?_,?_⟩
      · simp only [eval_add,eval_ofNat]
        dsimp only at ht₁ ht₂ ht
        omega
      · simpa [s₂,ι,Function.update_idem] using Block.seq_runs _ _ hp hx
    | true =>
      obtain ⟨t,ht,hr⟩ := hq₀
      have hx := Block.cases_runs_true (0:Fin R) Block.skip
        ((Block.dropTwo 0).seq (p.block.rename ι)) ((Block.dropTwo 0).seq (q.block.rename κ))
        (by simp [s₁]) (Block.seq_runs _ _ hd hr)
      refine ⟨1+(2+t+1),?_,?_⟩
      · simp only [eval_add,eval_ofNat]
        dsimp only at ht₁ ht₂ ht
        omega
      · simpa [s₂,κ,Function.update_idem] using Block.seq_runs _ _ hp hx

end Routine
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_IterateRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

def unary (n : ℕ) : List Bool := List.replicate n true
@[simp] lemma unary_length (n : ℕ) : (unary n).length=n := by simp [unary]
@[simp] lemma unary_reverse (n : ℕ) : (unary n).reverse=unary n := by simp [unary]
@[simp] lemma unary_zero : unary 0=[] := rfl
@[simp] lemma unary_succ (n : ℕ) : unary (n+1)=true::unary n := by simp [unary,List.replicate_succ]

namespace Routine
variable {α : Type} {ea : α → List Bool} {f : α → α}

lemma iterate_runs_at (p : Routine ea ea f) {R : ℕ}
    (ι : Fin (p.scratch+1) → Fin R) (hι : Function.Injective ι)
    (counter : Fin R) (hc : ∀ i,ι i≠counter) (B n : ℕ) (a : α) (s : Store R)
    (hin : s (ι 0)=ea a) (hclean : ∀ i,i≠0 → s (ι i)=[]) (hcount : s counter=unary n)
    (hb : ∀ j≤n,(ea (f^[j] a)).length≤B) :
    ∃ t≤n*(p.time.eval B+2)+1,
      (Block.loop counter ((Block.pop counter).seq (p.block.rename ι))).Runs s
        (Function.update (Function.update s counter []) (ι 0) (ea (f^[n] a))) t := by
  induction n generalizing a s with
  | zero =>
    have he : Function.update (Function.update s counter []) (ι 0) (ea (f^[0] a))=s := by
      simp only [Function.iterate_zero, id_eq]
      have hc0 : s counter=[] := hcount
      rw [←hin,←hc0,Function.update_eq_self,Function.update_eq_self]
    rw [he]
    exact ⟨1,by simp,Block.loop_runs_empty _ _ _ (by simpa using hcount)⟩
  | succ n ih =>
    let s₁ := Function.update s counter (unary n)
    let s₂ := Function.update s₁ (ι 0) (ea (f a))
    have hp : (Block.pop counter).Runs s s₁ 1 := by
      simpa [s₁,hcount] using Block.pop_runs counter s
    obtain ⟨t,ht,hp₀⟩ := p.run_at ι hι s₁ a (by simpa [s₁,hc] using hin) (by
      intro i hi
      simpa [s₁,hc] using hclean i hi)
    change (p.block.rename ι).Runs s₁ s₂ t at hp₀
    obtain ⟨u,hu,hi⟩ := ih (f a) s₂ (by simp [s₂]) (by
      intro i hi
      have hne : ι i≠ι 0 := fun h => hi (hι h)
      simp [s₂,s₁,Function.update_of_ne hne,hc,hclean i hi])
      (by simp [s₂,s₁,(hc 0).symm]) (by
        intro j hj
        simpa only [Function.iterate_succ_apply] using hb (j+1) (by omega))
    have he : Function.update (Function.update s₂ counter []) (ι 0) (ea (f^[n] (f a)))=
        Function.update (Function.update s counter []) (ι 0) (ea (f^[n+1] a)) := by
      funext k
      by_cases hk : k=ι 0
      · subst k; simp [Function.iterate_succ_apply]
      · by_cases hkc : k=counter
        · subst k; simp [(hc 0).symm]
        · simp [s₂,s₁,Function.update_of_ne,hk,hkc]
    rw [he] at hi
    have hh := Block.loop_runs_step counter ((Block.pop counter).seq (p.block.rename ι))
      (by simp [hcount]) (Block.seq_runs _ _ hp hp₀) hi
    refine ⟨_,?_,hh⟩
    have ht' : t≤p.time.eval B := ht.trans (polynomial_eval_mono p.time (by simpa using hb 0 (by omega)))
    nlinarith

noncomputable def boundedIterate {δ : Type} (p : Routine ea ea f)
    (count : δ → ℕ) (initial : δ → α) (P : Polynomial ℕ)
    (hbound : ∀ d j,j≤count d → (ea (f^[j] (initial d))).length≤
      P.eval (pairBits (unary (count d)) (ea (initial d))).length) :
    Routine (fun d => pairBits (unary (count d)) (ea (initial d))) ea
      (fun d => f^[count d] (initial d)) where
  scratch := p.scratch+1
  block :=
    let ι : Fin (p.scratch+1) → Fin (p.scratch+2) := fun i => ⟨i.val,by omega⟩
    let c : Fin (p.scratch+2) := ⟨p.scratch+1,by omega⟩
    (Block.decodeRev 0 c).seq (Block.loop c ((Block.pop c).seq (p.block.rename ι)))
  time := X*(p.time.comp P+7)+3
  correct d := by
    let R := p.scratch+2
    let ι : Fin (p.scratch+1) → Fin R := fun i => ⟨i.val,by omega⟩
    let c : Fin R := ⟨p.scratch+1,by omega⟩
    have hι : Function.Injective ι := fun i j h => Fin.ext (congrArg (fun k : Fin R => k.val) h)
    have hc : ∀ i,ι i≠c := by
      intro i h
      have hh := congrArg (fun k : Fin R => k.val) h
      have hi := i.isLt
      simp only [ι,c] at hh
      omega
    have h0c : (0:Fin R)≠c := hc 0
    let e := pairBits (unary (count d)) (ea (initial d))
    let s₀ : Store R := Function.update (fun _ => []) 0 e
    let s₁ : Store R := Function.update (Function.update s₀ 0 (ea (initial d))) c (unary (count d))
    have hd : (Block.decodeRev 0 c).Runs s₀ s₁ (5*count d+2) := by
      simpa [s₁,s₀,h0c.symm] using Block.decodeRev_runs (0:Fin R) c h0c
        (unary (count d)) (ea (initial d)) s₀ (by simp [s₀,e])
    obtain ⟨t,ht,hi⟩ := p.iterate_runs_at ι hι c hc (P.eval e.length) (count d) (initial d) s₁
      (by change s₁ 0=_; simp [s₁,h0c]) (by
        intro i hi
        have hne : ι i≠0 := fun h => hi (hι h)
        simp [s₁,s₀,Function.update_of_ne,hne,hc])
      (by simp [s₁]) (hbound d)
    have he : Function.update (Function.update s₁ c []) (ι 0) (ea (f^[count d] (initial d)))=
        Function.update (fun _ => []) 0 (ea (f^[count d] (initial d))) := by
      funext k
      change Function.update (Function.update s₁ c []) 0 _ k=_
      by_cases hk : k=0
      · subst k; simp
      · by_cases hkc : k=c
        · subst k; simp [h0c.symm]
        · simp [s₁,s₀,Function.update_of_ne,hk,hkc]
    rw [he] at hi
    refine ⟨_,?_,Block.seq_runs _ _ hd hi⟩
    simp only [eval_add,eval_mul,eval_X,eval_comp,eval_ofNat]
    change 5*count d+2+t≤e.length*(p.time.eval (P.eval e.length)+7)+3
    have hn : count d≤e.length := by simp [e,pairBits_length]; omega
    have hmul := Nat.mul_le_mul_right (p.time.eval (P.eval e.length)+7) hn
    nlinarith

end Routine
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Routine

noncomputable def append : Routine (fun z : List Bool×List Bool => pairBits z.1 z.2) id
    (fun z => z.1++z.2) where
  scratch := 1
  block := (Block.decodeRev 0 1).seq (Block.reverseInto 1 0)
  time := 10*X+10
  correct z := by
    let s₀ : Store 2 := Function.update (fun _ => []) 0 (pairBits z.1 z.2)
    let s₁ := Function.update (Function.update s₀ 0 z.2) 1 z.1.reverse
    have h₁ : (Block.decodeRev 0 1).Runs s₀ s₁ (5*z.1.length+2) := by
      simpa [s₁,s₀] using Block.decodeRev_runs (0:Fin 2) 1 (by decide) z.1 z.2
        s₀ (by simp [s₀])
    have h₂ := Block.reverseInto_runs (1:Fin 2) 0 (by decide) s₁
    have he : Function.update (Function.update s₁ 1 []) 0 ((s₁ 1).reverse++s₁ 0)=
        Function.update (fun _ => []) 0 (z.1++z.2) := by
      funext k
      fin_cases k <;> simp [s₁,s₀]
    rw [he] at h₂
    have hl : (s₁ 1).length=z.1.length := by simp [s₁]
    rw [hl] at h₂
    refine ⟨_,?_,Block.seq_runs _ _ h₁ h₂⟩
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,pairBits_length]
    omega

noncomputable def pushBit (b : Bool) : Routine (id : List Bool → List Bool) id (List.cons b) where
  scratch := 0
  block := Block.push 0 b
  time := 1
  correct x := by
    refine ⟨1,by simp,?_⟩
    simpa [Function.update_idem] using Block.push_runs (0:Fin 1) b (Function.update (fun _ => []) 0 x)

noncomputable def tail : Routine (id : List Bool → List Bool) id List.tail where
  scratch := 0
  block := Block.pop 0
  time := 1
  correct x := by
    refine ⟨1,by simp,?_⟩
    simpa [Function.update_idem] using Block.pop_runs (0:Fin 1) (Function.update (fun _ => []) 0 x)

noncomputable def isEmpty : Routine (id : List Bool → List Bool) (fun b : Bool => [b]) List.isEmpty where
  scratch := 0
  block := Block.cases 0 (Block.push 0 true)
    ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 false))
  time := 2*X+3
  correct x := by
    let s : Store 1 := Function.update (fun _ => []) 0 x
    have hfalse := Block.seq_runs _ _ (Block.clear_runs (0:Fin 1) s)
      (Block.push_runs (0:Fin 1) false (Function.update s 0 []))
    have htrue := Block.push_runs (0:Fin 1) true s
    cases x with
    | nil =>
      have hh := Block.cases_runs_empty (0:Fin 1) (Block.push 0 true)
        ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 false)) (by simp [s]) htrue
      refine ⟨2,by simp,?_⟩
      simpa [s,Function.update_idem] using hh
    | cons b l =>
      cases b with
      | false =>
        have hh := Block.cases_runs_false (0:Fin 1) (Block.push 0 true)
          ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 false))
          (by simp [s]) hfalse
        refine ⟨2*(l.length+1)+3,?_,?_⟩
        · simp
        · simpa [s,Function.update_idem,Nat.add_assoc] using hh
      | true =>
        have hh := Block.cases_runs_true (0:Fin 1) (Block.push 0 true)
          ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 false))
          (by simp [s]) hfalse
        refine ⟨2*(l.length+1)+3,?_,?_⟩
        · simp
        · simpa [s,Function.update_idem,Nat.add_assoc] using hh

end Routine
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_LengthRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Block
variable {r : ℕ}
def lengthInto (src dst : Fin r) : Block r := loop src ((pop src).seq (push dst true))
lemma lengthInto_runs (src dst : Fin r) (hne : src≠dst) (s : Store r) :
    (lengthInto src dst).Runs s
      (Function.update (Function.update s src []) dst (unary (s src).length++s dst))
      (3*(s src).length+1) := by
  generalize hl : s src=l
  induction l generalizing s with
  | nil =>
    have he : Function.update (Function.update s src []) dst (unary 0++s dst)=s := by
      simp only [unary_zero,List.nil_append]
      rw [←hl,Function.update_eq_self,Function.update_eq_self]
    change (lengthInto src dst).Runs s
      (Function.update (Function.update s src []) dst (unary 0++s dst)) 1
    rw [he]
    exact loop_runs_empty src _ s hl
  | cons b l ih =>
    let s' := Function.update (Function.update s src l) dst (true::s dst)
    have hp : (pop src).Runs s (Function.update s src l) 1 := by
      simpa [hl] using pop_runs src s
    have ht : (push dst true).Runs (Function.update s src l) s' 1 := by
      simpa [s',hne.symm] using push_runs dst true (Function.update s src l)
    have hi := ih s' (by simp [s',hne])
    have he : Function.update (Function.update s' src []) dst (unary l.length++s' dst)=
        Function.update (Function.update s src []) dst (unary (b::l).length++s dst) := by
      funext k
      by_cases hk : k=dst
      · subst k
        simp only [Function.update_self,s',List.length_cons,unary]
        simp only [List.replicate_succ',List.append_assoc,List.singleton_append]
      · by_cases hks : k=src
        · subst k; simp [s',hne]
        · simp [s',Function.update_of_ne,hk,hks]
    rw [he] at hi
    have h := loop_runs_step src ((pop src).seq (push dst true)) (by simp [hl])
      (seq_runs _ _ hp ht) hi
    have heq : 2+(3*l.length+1)+1=3*(b::l).length+1 := by simp; omega
    rw [heq] at h
    exact h
end Block
namespace Routine
variable {α : Type}
noncomputable def codeLength (ea : α → List Bool) : Routine ea unary (fun a => (ea a).length) where
  scratch := 1
  block := (Block.lengthInto 0 1).seq (Block.reverseInto 1 0)
  time := 7*X+2
  correct a := by
    let s₀ : Store 2 := Function.update (fun _ => []) 0 (ea a)
    let s₁ := Function.update (Function.update s₀ 0 []) 1 (unary (ea a).length)
    have h₁ : (Block.lengthInto 0 1).Runs s₀ s₁ (3*(ea a).length+1) := by
      simpa [s₀,s₁] using Block.lengthInto_runs (0:Fin 2) 1 (by decide) s₀
    have h₂ := Block.reverseInto_runs (1:Fin 2) 0 (by decide) s₁
    have he : Function.update (Function.update s₁ 1 []) 0 ((s₁ 1).reverse++s₁ 0)=
        Function.update (fun _ => []) 0 (unary (ea a).length) := by
      funext k
      fin_cases k <;> simp [s₁,s₀]
    rw [he] at h₂
    have hl : (s₁ 1).length=(ea a).length := by simp [s₁]
    rw [hl] at h₂
    refine ⟨_,?_,Block.seq_runs _ _ h₁ h₂⟩
    simp only [eval_add,eval_mul,eval_ofNat,eval_X]
    omega
end Routine
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_PolyCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
class Coding (α : Type) where
  encode : α → List Bool
export Coding (encode)
instance instCodingNat : Coding ℕ := ⟨unary⟩
instance instCodingBool : Coding Bool := ⟨fun b => [b]⟩
instance instCodingProd {α β : Type} [Coding α] [Coding β] : Coding (α×β) :=
  ⟨fun z => pairBits (encode z.1) (encode z.2)⟩

def listCode {α : Type} (ea : α → List Bool) : List α → List Bool
  | [] => []
  | a::l => pairBits (ea a) (listCode ea l)
instance instCodingList {α : Type} [Coding α] : Coding (List α) := ⟨listCode encode⟩

@[simp] lemma encode_nat (n : ℕ) : encode n=unary n := rfl
@[simp] lemma encode_bool (b : Bool) : encode b=[b] := rfl
@[simp] lemma encode_pair {α β : Type} [Coding α] [Coding β] (a : α) (b : β) :
    encode (a,b)=pairBits (encode a) (encode b) := rfl
@[simp] lemma encode_prod {α β : Type} [Coding α] [Coding β] (z : α×β) :
    encode z=pairBits (encode z.1) (encode z.2) := rfl

@[simp] lemma code_nil {α : Type} [Coding α] : encode ([]:List α)=[] := rfl
@[simp] lemma code_cons {α : Type} [Coding α] (a : α) (l : List α) :
    encode (a::l)=pairBits (encode a) (encode l) := rfl

lemma pairBits_append (x y z : List Bool) : pairBits x (y++z)=pairBits x y++z := by
  induction x with
  | nil => rfl
  | cons b x ih => simpa only [pairBits,List.cons_append,Function.comp_apply] using congrArg (List.cons false ∘ List.cons b) ih

lemma code_append {α : Type} [Coding α] (l m : List α) : encode (l++m)=encode l++encode m := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.cons_append,code_cons,ih,pairBits_append]

lemma list_length_le_code {α : Type} [Coding α] (l : List α) : l.length≤(encode l).length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.length_cons,code_cons,pairBits_length]; omega

@[fun_prop] def Poly {α β : Type} [Coding α] [Coding β] (f : α → β) : Prop :=
  Nonempty (Routine encode encode f)

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]
noncomputable def routine {f : α → β} (h : Poly f) : Routine encode encode f := Classical.choice h

@[fun_prop] theorem identity : Poly (fun a : α => a) := ⟨Routine.identity encode⟩
@[fun_prop] theorem constant (b : β) : Poly (fun _ : α => b) := ⟨Routine.constant encode encode b⟩
@[fun_prop] theorem comp (f : β → γ) (g : α → β) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => f (g a)) := ⟨hg.routine.comp hf.routine⟩
@[fun_prop] theorem pair (f : α → β) (g : α → γ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => (f a,g a)) := ⟨hf.routine.pair hg.routine⟩
@[fun_prop] theorem first (f : α → β×γ) (hf : Poly f) : Poly (fun a => (f a).1) :=
  ⟨hf.routine.comp (Routine.first encode encode)⟩
@[fun_prop] theorem second (f : α → β×γ) (hf : Poly f) : Poly (fun a => (f a).2) :=
  ⟨hf.routine.comp (Routine.second encode encode)⟩

@[fun_prop] theorem cond (b : α → Bool) (f g : α → β) (hb : Poly b) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => if b a then g a else f a) := by
  let p := (hb.routine.pair (Routine.identity encode)).comp (hf.routine.select hg.routine)
  exact ⟨p⟩

@[fun_prop] theorem codeLength : Poly (fun a : α => (encode a).length) := ⟨Routine.codeLength encode⟩

theorem boundedIterate (f : α → α) (hf : Poly f) (P : Polynomial ℕ)
    (h : ∀ (z : ℕ×α) j,j≤z.1 → (encode (f^[j] z.2)).length≤P.eval (encode z).length) :
    Poly (fun z : ℕ×α => f^[z.1] z.2) :=
  ⟨hf.routine.boundedIterate Prod.fst Prod.snd P h⟩

theorem congr {f g : α → β} (hf : Poly f) (h : ∀ a,f a=g a) : Poly g := by
  have he : f=g := funext h
  rwa [←he]

end Poly
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_ListRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Routine
variable {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
  {f : α×List α → β}

noncomputable def listCases (b : β)
    (p : Routine (fun z : α×List α => pairBits (ea z.1) (listCode ea z.2)) eb f) :
    Routine (listCode ea) eb (fun l => match l with | [] => b | a::l => f (a,l)) where
  scratch := p.scratch
  block := Block.cases 0 (Block.emit 0 (eb b)) p.block p.block
  time := p.time+C ((eb b).length+2)
  correct l := by
    let s : Store (p.scratch+1) := Function.update (fun _ => []) 0 (listCode ea l)
    cases l with
    | nil =>
      have he := Block.emit_runs (0:Fin (p.scratch+1)) (eb b) s
      have hh := Block.cases_runs_empty (0:Fin (p.scratch+1)) (Block.emit 0 (eb b))
        p.block p.block (by simp [s,listCode]) he
      refine ⟨(eb b).length+1+1,?_,?_⟩
      · simp only [eval_add,eval_C]
        omega
      · simpa [s,listCode,Function.update_idem] using hh
    | cons a l =>
      obtain ⟨t,ht,hp⟩ := p.correct (a,l)
      change p.block.Runs s (Function.update (fun _ => []) 0 (eb (f (a,l)))) t at hp
      refine ⟨t+1,?_,?_⟩
      · simp only [eval_add,eval_C,listCode] at *
        omega
      · cases ha : ea a with
        | nil => exact Block.cases_runs_true _ _ _ _ (by simp [listCode,ha,pairBits]) hp
        | cons x xs => exact Block.cases_runs_false _ _ _ _ (by simp [listCode,ha,pairBits]) hp
end Routine
namespace Poly
variable {α β : Type} [Coding α] [Coding β]

@[fun_prop] theorem listCases (b : β) (f : α×List α → β) (hf : Poly f) :
    Poly (fun l => match l with | [] => b | a::l => f (a,l)) :=
  ⟨Routine.listCases encode encode b hf.routine⟩

@[fun_prop] theorem listCons : Poly (fun z : α×List α => z.1::z.2) := by
  refine ⟨(Routine.identity (encode : α×List α → List Bool)).reindex encode encode
    (fun z : α×List α => z.1::z.2) id (fun _ => rfl) (fun _ => rfl)⟩

@[fun_prop] theorem listTail : Poly (List.tail : List α → List α) := by
  exact listCases [] Prod.snd (by fun_prop)

@[fun_prop] theorem listHeadD (a : α) : Poly (fun l : List α => l.headD a) := by
  exact (listCases a Prod.fst (by fun_prop)).congr (fun l => by cases l <;> rfl)

@[fun_prop] theorem listIsEmpty : Poly (List.isEmpty : List α → Bool) := by
  exact listCases true (fun _ : α×List α => false) (by fun_prop)

@[fun_prop] theorem listAppend : Poly (fun z : List α×List α => z.1++z.2) := by
  refine ⟨Routine.append.reindex encode encode (fun z : List α×List α => z.1++z.2)
    (fun z => (encode z.1,encode z.2)) (fun _ => rfl) ?_⟩
  intro z
  exact (code_append z.1 z.2).symm

end Poly
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_UnaryArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Poly

@[fun_prop] theorem natSucc : Poly (fun n : ℕ => n+1) := by
  refine ⟨(Routine.pushBit true).reindex encode encode (fun n : ℕ => n+1) unary
    (fun _ => rfl) ?_⟩
  intro n
  simp

@[fun_prop] theorem natPred : Poly (Nat.pred : ℕ → ℕ) := by
  refine ⟨Routine.tail.reindex encode encode Nat.pred unary (fun _ => rfl) ?_⟩
  intro n
  cases n <;> simp

@[fun_prop] theorem natZeroTest : Poly (fun n : ℕ => decide (n=0)) := by
  refine ⟨Routine.isEmpty.reindex encode encode (fun n : ℕ => decide (n=0)) unary
    (fun _ => rfl) ?_⟩
  intro n
  cases n <;> simp

@[fun_prop] theorem natAdd : Poly (fun z : ℕ×ℕ => z.1+z.2) := by
  refine ⟨Routine.append.reindex encode encode (fun z : ℕ×ℕ => z.1+z.2)
    (fun z => (unary z.1,unary z.2)) (fun _ => rfl) ?_⟩
  intro z
  simp only [id_eq,encode_nat,unary,List.replicate_add]

@[fun_prop] theorem natSub : Poly (fun z : ℕ×ℕ => z.1-z.2) := by
  have hp : Poly (fun z : ℕ×ℕ => Nat.pred^[z.1] z.2) :=
    boundedIterate Nat.pred natPred X (by
      intro z j hj
      simp only [Nat.pred_iterate,encode_nat,unary_length,encode_prod,pairBits_length,eval_X]
      omega)
  have h : Poly (fun z : ℕ×ℕ => Nat.pred^[z.2] z.1) := by fun_prop
  exact h.congr (fun z => Nat.pred_iterate z.1 z.2)

@[fun_prop] theorem boolNot : Poly (Bool.not : Bool → Bool) := by
  have h : Poly (fun b : Bool => if b then false else true) := by fun_prop
  exact h.congr (fun b => by cases b <;> rfl)

@[fun_prop] theorem boolAnd : Poly (fun z : Bool×Bool => z.1 && z.2) := by
  have h : Poly (fun z : Bool×Bool => if z.1 then z.2 else false) := by fun_prop
  exact h.congr (fun z => by cases z.1 <;> rfl)

@[fun_prop] theorem boolOr : Poly (fun z : Bool×Bool => z.1 || z.2) := by
  have h : Poly (fun z : Bool×Bool => if z.1 then true else z.2) := by fun_prop
  exact h.congr (fun z => by cases z.1 <;> rfl)

@[fun_prop] theorem natLE : Poly (fun z : ℕ×ℕ => decide (z.1≤z.2)) := by
  have h : Poly (fun z : ℕ×ℕ => decide (z.1-z.2=0)) := comp _ _ natZeroTest natSub
  exact h.congr (fun z => by simp [Nat.sub_eq_zero_iff_le])

@[fun_prop] theorem natLT : Poly (fun z : ℕ×ℕ => decide (z.1<z.2)) := by
  have hle : Poly (fun z : ℕ×ℕ => decide (z.2≤z.1)) := comp _ (fun z : ℕ×ℕ => (z.2,z.1)) natLE (by fun_prop)
  have h : Poly (fun z : ℕ×ℕ => !(decide (z.2≤z.1))) := comp _ _ boolNot hle
  exact h.congr (fun z => by simp [←decide_not])

@[fun_prop] theorem natEQ : Poly (fun z : ℕ×ℕ => decide (z.1=z.2)) := by
  have hle : Poly (fun z : ℕ×ℕ => decide (z.2≤z.1)) := comp _ (fun z : ℕ×ℕ => (z.2,z.1)) natLE (by fun_prop)
  have h : Poly (fun z : ℕ×ℕ => decide (z.1≤z.2) && decide (z.2≤z.1)) :=
    comp _ _ boolAnd (pair _ _ natLE hle)
  exact h.congr (fun z => by simp [le_antisymm_iff])

def addStep (z : ℕ×ℕ) : ℕ×ℕ := (z.1,z.2+z.1)
lemma addStep_iterate (n : ℕ) (z : ℕ×ℕ) : addStep^[n] z=(z.1,z.2+n*z.1) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply',ih,addStep,Nat.add_mul,Nat.add_assoc]

@[fun_prop] theorem natMul : Poly (fun z : ℕ×ℕ => z.1*z.2) := by
  have hs : Poly addStep := by unfold addStep; fun_prop
  have hi : Poly (fun z : ℕ×(ℕ×ℕ) => addStep^[z.1] z.2) :=
    boundedIterate addStep hs ((X+1)^2) (by
      intro z j hj
      simp only [addStep_iterate,encode_prod,encode_nat,unary_length,pairBits_length,
        eval_pow,eval_add,eval_X,eval_one]
      have hh : j*z.2.1≤z.1*z.2.1 := Nat.mul_le_mul_right _ hj
      nlinarith [sq_nonneg (z.1:ℤ),sq_nonneg (z.2.1:ℤ)])
  have h : Poly (fun z : ℕ×ℕ => (addStep^[z.2] (z.1,0)).2) := by fun_prop
  exact h.congr (fun z => by simp [addStep_iterate,Nat.mul_comm])

@[fun_prop] theorem natMin : Poly (fun z : ℕ×ℕ => min z.1 z.2) := by
  have h : Poly (fun z : ℕ×ℕ => if decide (z.1≤z.2) then z.1 else z.2) := by fun_prop
  exact h.congr (fun z => by simp [min_def])

@[fun_prop] theorem natMax : Poly (fun z : ℕ×ℕ => max z.1 z.2) := by
  have h : Poly (fun z : ℕ×ℕ => if decide (z.1≤z.2) then z.2 else z.1) := by fun_prop
  exact h.congr (fun z => by simp [max_def])

variable {α : Type} [Coding α]
@[fun_prop] theorem natLe_apply (f g : α → ℕ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a≤g a)) := comp _ _ natLE (pair _ _ hf hg)
@[fun_prop] theorem natLt_apply (f g : α → ℕ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a<g a)) := comp _ _ natLT (pair _ _ hf hg)
@[fun_prop] theorem natEq_apply (f g : α → ℕ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a=g a)) := comp _ _ natEQ (pair _ _ hf hg)
@[fun_prop] theorem natPow (k : ℕ) : Poly (fun n : ℕ => n^k) := by
  induction k with
  | zero => simpa only [pow_zero] using (constant (α := ℕ) (1:ℕ))
  | succ k ih =>
    have h : Poly (fun n : ℕ => n^k*n) := comp _ _ natMul (pair _ _ ih identity)
    exact h.congr (fun n => (pow_succ n k).symm)
end Poly
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_FoldRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma code_drop_le {α : Type} [Coding α] (l : List α) (n : ℕ) :
    (encode (l.drop n)).length≤(encode l).length := by
  have h := congrArg (fun xs => (encode xs).length) (List.take_append_drop n l)
  rw [code_append,List.length_append] at h
  omega

def foldStep {α β : Type} (a₀ : α) (f : β×α → β) (z : List α×β) : List α×β :=
  if z.1.isEmpty then z else (z.1.tail,f (z.2,z.1.headD a₀))

lemma foldStep_iterate {α β : Type} (a₀ : α) (f : β×α → β) (n : ℕ) (z : List α×β) :
    (foldStep a₀ f)^[n] z=(z.1.drop n,(z.1.take n).foldl (fun b a => f (b,a)) z.2) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rcases z with ⟨l,b⟩
    cases l with
    | nil => simp [Function.iterate_succ_apply,foldStep,ih]
    | cons a l => simp [Function.iterate_succ_apply,foldStep,ih]

namespace Poly
variable {α β : Type} [Coding α] [Coding β]

theorem listFold (a₀ : α) (f : β×α → β) (hf : Poly f) (P : Polynomial ℕ)
    (hb : ∀ (z : List α×β) k,
      (encode ((z.1.take k).foldl (fun b a => f (b,a)) z.2)).length≤P.eval (encode z).length) :
    Poly (fun z : List α×β => z.1.foldl (fun b a => f (b,a)) z.2) := by
  have hs : Poly (foldStep a₀ f) := by unfold foldStep; fun_prop
  have hi : Poly (fun z : ℕ×(List α×β) => (foldStep a₀ f)^[z.1] z.2) :=
    boundedIterate (foldStep a₀ f) hs (X+P) (by
      intro z j hj
      rw [foldStep_iterate]
      have hl := code_drop_le z.2.1 j
      have hn : (encode z.2).length≤(encode z).length := by
        simp only [encode_prod,pairBits_length]
        omega
      have hacc := (hb z.2 j).trans (polynomial_eval_mono P hn)
      simp only [encode_prod,pairBits_length,eval_add,eval_X] at *
      omega)
  have h : Poly (fun z : List α×β => ((foldStep a₀ f)^[(encode z.1).length] z).2) :=
    second _ (comp _ (fun z : List α×β => ((encode z.1).length,z)) hi
      (pair _ _ (comp _ Prod.fst codeLength (first _ identity)) identity))
  exact h.congr (fun z => by
    rw [foldStep_iterate]
    simp only [List.take_of_length_le (list_length_le_code z.1)])

omit [Coding α] in
lemma count_fold (l : List α) (b : ℕ) :
    l.foldl (fun b _ => b+1) b=b+l.length := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih,Nat.add_comm,Nat.add_left_comm]

@[fun_prop] theorem listLength [Inhabited α] : Poly (List.length : List α → ℕ) := by
  have hf : Poly (fun z : ℕ×α => z.1+1) := by fun_prop
  have hfold := listFold (default:α) (fun z : ℕ×α => z.1+1) hf X (by
    intro z k
    rw [count_fold]
    have hk : (z.1.take k).length≤z.1.length := by simp only [List.length_take]; exact Nat.min_le_right _ _
    have hl := list_length_le_code z.1
    simp only [encode_nat,unary_length,encode_prod,pairBits_length,eval_X]
    omega)
  have hh : Poly (fun l : List α => l.foldl (fun b _ => b+1) 0) :=
    comp _ (fun l : List α => (l,0)) hfold (by fun_prop)
  exact hh.congr (fun l => by simp)

end Poly
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_MapRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma element_code_le {α : Type} [Coding α] (l : List α) (a : α) (ha : a∈l) :
    (encode a).length≤(encode l).length := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.mem_cons] at ha
    simp only [code_cons,pairBits_length]
    rcases ha with rfl | ha
    · omega
    · have hh := ih ha; omega

lemma list_code_bound {α : Type} [Coding α] (l : List α) (M : ℕ)
    (hb : ∀ a∈l,(encode a).length≤M) : (encode l).length≤l.length*(2*M+1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hb a (by simp)
    have hl := ih (fun a ha => hb a (List.mem_cons_of_mem _ ha))
    simp only [code_cons,pairBits_length,List.length_cons]
    nlinarith

lemma append_map_fold {α β : Type} (f : α → β) (l : List α) (b : List β) :
    l.foldl (fun b a => b++[f a]) b=b++l.map f := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih,List.append_assoc]

lemma append_fold {α : Type} (l : List (List α)) (b : List α) :
    l.foldl (fun b a => b++a) b=b++l.flatten := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih,List.append_assoc]

lemma code_flatten_le {α : Type} [Coding α] (l : List (List α)) :
    (encode l.flatten).length≤(encode l).length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatten_cons,code_append,List.length_append,code_cons,pairBits_length]; omega

namespace Poly
variable {α β : Type} [Coding α] [Coding β]

@[fun_prop] theorem listMap [Inhabited α] (f : α → β) (hf : Poly f) : Poly (List.map f) := by
  let p := hf.routine.time
  have hs : Poly (fun z : List β×α => z.1++[f z.2]) := by fun_prop
  have hfold := listFold (default:α) (fun z : List β×α => z.1++[f z.2]) hs
    (X+X*(2*(X+p)+1)) (by
      intro z k
      rw [append_map_fold,code_append,List.length_append]
      let N := (encode z).length
      have help : ∀ a∈z.1.take k,(encode a).length≤N := by
        intro a ha
        have hh := element_code_le z.1 a (List.mem_of_mem_take ha)
        simp only [N,encode_prod,pairBits_length]
        omega
      have hb : ∀ b∈(z.1.take k).map f,(encode b).length≤N+p.eval N := by
        intro b hb
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
        have ht := hf.routine.length_bound a
        have hh := help a ha
        have hm := polynomial_eval_mono p hh
        exact ht.trans (Nat.add_le_add hh hm)
      have hmap := list_code_bound ((z.1.take k).map f) (N+p.eval N) hb
      have ht : (z.1.take k).length≤N := (show (z.1.take k).length≤z.1.length by simp only [List.length_take]; exact Nat.min_le_right _ _).trans
        ((list_length_le_code z.1).trans (by simp only [N,encode_prod,pairBits_length]; omega))
      have hmul := Nat.mul_le_mul_right (2*(N+p.eval N)+1) ht
      simp only [List.length_map] at hmap
      have hb₀ : (encode z.2).length≤N := by simp only [N,encode_prod,pairBits_length]; omega
      simp only [eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
      change (encode z.2).length+(encode ((z.1.take k).map f)).length≤N+N*(2*(N+p.eval N)+1)
      omega)
  have hh : Poly (fun l : List α => l.foldl (fun b a => b++[f a]) []) :=
    comp _ (fun l : List α => (l,[])) hfold (by fun_prop)
  exact hh.congr (fun l => by rw [append_map_fold,List.nil_append])

@[fun_prop] theorem listFlatten : Poly (List.flatten : List (List α) → List α) := by
  have hs : Poly (fun z : List α×List α => z.1++z.2) := by fun_prop
  have hfold := listFold ([]:List α) (fun z : List α×List α => z.1++z.2) hs X (by
    intro z k
    rw [append_fold,code_append,List.length_append]
    have h₁ := code_flatten_le (z.1.take k)
    have h₂ : (encode (z.1.take k)).length≤(encode z.1).length := by
      have hh := congrArg (fun l => (encode l).length) (List.take_append_drop k z.1)
      rw [code_append,List.length_append] at hh
      omega
    simp only [eval_X,encode_prod,pairBits_length]
    omega)
  have hh : Poly (fun l : List (List α) => l.foldl (fun b a => b++a) []) :=
    comp _ (fun l : List (List α) => (l,[])) hfold (by fun_prop)
  exact hh.congr (fun l => by simp [append_fold])

@[fun_prop] theorem listFlatMap [Inhabited α] (f : α → List β) (hf : Poly f) :
    Poly (List.flatMap f) := by
  have hm := listMap f hf
  have hl : Poly (List.flatten : List (List β) → List β) := listFlatten
  have hh : Poly (fun l : List α => (l.map f).flatten) := comp _ _ hl hm
  exact hh

@[fun_prop] theorem listFilter [Inhabited α] (f : α → Bool) (hf : Poly f) :
    Poly (List.filter f) := by
  have hs : Poly (fun a => if f a then [a] else []) := by fun_prop
  have hh := listFlatMap (fun a => if f a then [a] else []) hs
  exact hh.congr (fun l => by
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.filter_cons,ih]; split <;> simp_all)

end Poly
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_SequenceRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma code_take_le {α : Type} [Coding α] (l : List α) (n : ℕ) :
    (encode (l.take n)).length≤(encode l).length := by
  have h := congrArg (fun xs => (encode xs).length) (List.take_append_drop n l)
  rw [code_append,List.length_append] at h
  omega

lemma code_replicate {α : Type} [Coding α] (a : α) (n : ℕ) :
    (encode (List.replicate n a)).length=n*(2*(encode a).length+1) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ,code_cons,pairBits_length,ih]; nlinarith

def dupStep {α : Type} (z : α×List α) : α×List α := (z.1,z.1::z.2)
lemma dupStep_iterate {α : Type} (n : ℕ) (z : α×List α) :
    dupStep^[n] z=(z.1,List.replicate n z.1++z.2) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply',ih,dupStep,List.replicate_succ]

lemma code_zip_bound {α β : Type} [Coding α] [Coding β] (l : List α) (m : List β) :
    (encode (l.zip m)).length≤2*(encode l).length+(encode m).length := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    cases m with
    | nil => simp
    | cons b m =>
      have h := ih m
      simp only [List.zip_cons_cons,code_cons,encode_prod,pairBits_length]
      omega

def zipStep {α β : Type} [Inhabited α] [Inhabited β]
    (z : List α×(List β×List (α×β))) : List α×(List β×List (α×β)) :=
  (z.1.tail,z.2.1.tail,if z.1.isEmpty || z.2.1.isEmpty then z.2.2
    else z.2.2++[(z.1.headD default,z.2.1.headD default)])

lemma zipStep_iterate {α β : Type} [Inhabited α] [Inhabited β]
    (n : ℕ) (z : List α×(List β×List (α×β))) :
    zipStep^[n] z=(z.1.drop n,z.2.1.drop n,
      z.2.2++(z.1.take n).zip (z.2.1.take n)) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rcases z with ⟨l,m,o⟩
    cases l <;> cases m <;>
      simp [Function.iterate_succ_apply,zipStep,ih,List.append_assoc]

lemma zip_take_right_of_ge {α β : Type} (l : List α) (m : List β) (n : ℕ)
    (hn : l.length≤n) : l.zip (m.take n)=l.zip m := by
  induction l generalizing m n with
  | nil => simp
  | cons a l ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      cases m with
      | nil => simp
      | cons b m => simp only [List.take_succ_cons,List.zip_cons_cons,ih m n (by simpa using hn)]

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

@[fun_prop] theorem listReplicate : Poly (fun z : ℕ×α => List.replicate z.1 z.2) := by
  have hs : Poly (dupStep : α×List α → α×List α) := by unfold dupStep; fun_prop
  have hi : Poly (fun z : ℕ×(α×List α) => dupStep^[z.1] z.2) :=
    boundedIterate dupStep hs ((X+1)^2) (by
      intro z j hj
      rw [dupStep_iterate]
      simp only [encode_prod,pairBits_length,code_append,List.length_append,code_replicate,
        encode_nat,unary_length,eval_pow,eval_add,eval_X,eval_one]
      have hm := Nat.mul_le_mul_right (2*(encode z.2.1).length+1) hj
      nlinarith)
  have h : Poly (fun z : ℕ×α => (dupStep^[z.1] (z.2,[])).2) :=
    second _ (comp _ (fun z : ℕ×α => (z.1,(z.2,[]))) hi (by fun_prop))
  exact h.congr (fun z => by simp [dupStep_iterate])

@[fun_prop] theorem listZip [Inhabited α] [Inhabited β] :
    Poly (fun z : List α×List β => z.1.zip z.2) := by
  have hs : Poly (zipStep : List α×(List β×List (α×β)) → _) := by unfold zipStep; fun_prop
  have hi : Poly (fun z : ℕ×(List α×(List β×List (α×β))) => zipStep^[z.1] z.2) :=
    boundedIterate zipStep hs (2*X) (by
      intro z j hj
      rw [zipStep_iterate]
      have h₁ := code_drop_le z.2.1 j
      have h₂ := code_drop_le z.2.2.1 j
      have h₃ := code_take_le z.2.1 j
      have h₄ := code_take_le z.2.2.1 j
      have h₅ := code_zip_bound (z.2.1.take j) (z.2.2.1.take j)
      simp only [encode_prod,pairBits_length,code_append,List.length_append,encode_nat,unary_length,
        eval_mul,eval_ofNat,eval_X]
      omega)
  have h : Poly (fun z : List α×List β => (zipStep^[(encode z.1).length] (z.1,z.2,[])).2.2) := by
    apply second
    apply second
    apply comp _ (fun z : List α×List β => ((encode z.1).length,(z.1,z.2,[]))) hi
    apply pair
    · exact comp _ Prod.fst codeLength (first _ identity)
    · fun_prop
  exact h.congr (fun z => by
    rw [zipStep_iterate]
    simp only [List.nil_append,List.take_of_length_le (list_length_le_code z.1)]
    exact zip_take_right_of_ge z.1 z.2 _ (list_length_le_code z.1))

@[fun_prop] theorem listMapParam [Inhabited α] [Inhabited γ]
    (f : γ×α → β) (hf : Poly f) : Poly (fun z : γ×List α => z.2.map (fun a => f (z.1,a))) := by
  have hm : Poly (List.map f) := listMap f hf
  have h : Poly (fun z : γ×List α => (List.zip (List.replicate z.2.length z.1) z.2).map f) := by fun_prop
  exact h.congr (fun z => by
    have hz : List.zip (List.replicate z.2.length z.1) z.2=z.2.map (fun a => (z.1,a)) := by
      induction z.2 with
      | nil => rfl
      | cons a l ih => simpa only [List.length_cons,List.replicate_succ,List.zip_cons_cons,List.map_cons] using congrArg (List.cons (z.1,a)) ih
    simp [hz,List.map_map,Function.comp_def])

end Poly
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_OrbitRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Poly
variable {α β γ δ : Type} [Coding α] [Coding β] [Coding γ] [Coding δ]

theorem reindex {f : α → β} (hf : Poly f) (g : γ → δ) (i : γ → α)
    (hin : ∀ x,encode x=encode (i x))
    (hout : ∀ x,encode (f (i x))=encode (g x)) : Poly g :=
  ⟨hf.routine.reindex encode encode g i (fun x => (hin x).symm) hout⟩

end Poly
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_SumRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode

instance instCodingOption {α : Type} [Coding α] : Coding (Option α) := ⟨fun x => encode x.toList⟩
instance instCodingSum {α β : Type} [Coding α] [Coding β] : Coding (Sum α β) :=
  ⟨fun x => match x with | .inl a => encode ([a],([]:List β)) | .inr b => encode (([]:List α),[b])⟩

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

@[fun_prop] theorem some : Poly (Option.some : α → Option α) := by
  have h : Poly (fun a : α => [a]) := by fun_prop
  exact h.reindex Option.some id (fun _ => rfl) (fun _ => rfl)

@[fun_prop] theorem optionToList : Poly (Option.toList : Option α → List α) :=
  identity.reindex Option.toList Option.toList (fun _ => rfl) (fun _ => rfl)

@[fun_prop] theorem optionGetD (a : α) : Poly (fun x : Option α => x.getD a) := by
  have h : Poly (fun x : Option α => x.toList.headD a) := comp _ _ (listHeadD a) optionToList
  exact h.congr (fun x => by cases x <;> rfl)

@[fun_prop] theorem optionIsSome : Poly (Option.isSome : Option α → Bool) := by
  have h : Poly (fun x : Option α => !x.toList.isEmpty) := by fun_prop
  exact h.congr (fun x => by cases x <;> rfl)

@[fun_prop] theorem optionMap [Inhabited α] (f : α → β) (hf : Poly f) :
    Poly (Option.map f) := by
  have h : Poly (fun x : Option α => x.toList.map f) := by fun_prop
  exact h.reindex (Option.map f) id (fun _ => rfl) (fun x => by cases x <;> rfl)

@[fun_prop] theorem optionElim [Inhabited α] (b : β) (f : α → β) (hf : Poly f) :
    Poly (fun x : Option α => x.elim b f) := by
  have h : Poly (fun x : Option α => if x.isSome then f (x.getD default) else b) := by fun_prop
  exact h.congr (fun x => by cases x <;> rfl)

@[fun_prop] theorem sumInl : Poly (Sum.inl : α → Sum α β) := by
  have h : Poly (fun a : α => ([a],([]:List β))) := by fun_prop
  exact h.reindex Sum.inl id (fun _ => rfl) (fun _ => rfl)
@[fun_prop] theorem sumInr : Poly (Sum.inr : β → Sum α β) := by
  have h : Poly (fun b : β => (([]:List α),[b])) := by fun_prop
  exact h.reindex Sum.inr id (fun _ => rfl) (fun _ => rfl)

@[fun_prop] theorem sumCases [Inhabited α] [Inhabited β]
    (f : α → γ) (g : β → γ) (hf : Poly f) (hg : Poly g) :
    Poly (Sum.elim f g) := by
  let repr : Sum α β → List α×List β :=
    fun x => match x with | .inl a => ([a],[]) | .inr b => ([],[b])
  have h : Poly (fun z : List α×List β => if z.1.isEmpty then g (z.2.headD default)
      else f (z.1.headD default)) := by fun_prop
  exact h.reindex (Sum.elim f g) repr (fun x => by cases x <;> rfl)
    (fun x => by cases x <;> rfl)

end Poly
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_UnaryDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma bounded_stops {α : Type} (f : α → α) (active : α → Bool) (rank : α → ℕ)
    (hfix : ∀ a,active a=false → f a=a)
    (hdec : ∀ a,active a=true → rank (f a)+1≤rank a) :
    ∀ n a,rank a≤n → active (f^[n] a)=false := by
  intro n
  induction n with
  | zero =>
    intro a ha
    cases h : active a with
    | false => simpa using h
    | true => have hh := hdec a h; omega
  | succ n ih =>
    intro a ha
    cases h : active a with
    | false => rw [Function.iterate_fixed (hfix a h)]; exact h
    | true =>
      rw [Function.iterate_succ_apply]
      apply ih
      have hh := hdec a h
      omega

def divActive (z : ℕ×(ℕ×ℕ)) : Bool := decide (0<z.1) && decide (z.1≤z.2.1)
def divStep (z : ℕ×(ℕ×ℕ)) : ℕ×(ℕ×ℕ) :=
  if divActive z then (z.1,(z.2.1-z.1,z.2.2+1)) else z

lemma divStep_spec (z : ℕ×(ℕ×ℕ)) :
    (divStep z).1=z.1 ∧ (divStep z).2.1≤z.2.1 ∧ (divStep z).2.2≤z.2.2+1 ∧
      (divStep z).2.1+z.1*(divStep z).2.2=z.2.1+z.1*z.2.2 := by
  unfold divStep
  split_ifs with h
  · have hz : 0<z.1 ∧ z.1≤z.2.1 := by simpa [divActive] using h
    have he := Nat.sub_add_cancel hz.2
    dsimp only
    refine ⟨rfl,Nat.sub_le _ _,le_rfl,?_⟩
    nlinarith
  · simp

lemma divIterate_spec (n : ℕ) (z : ℕ×(ℕ×ℕ)) :
    (divStep^[n] z).1=z.1 ∧ (divStep^[n] z).2.1≤z.2.1 ∧ (divStep^[n] z).2.2≤z.2.2+n ∧
      (divStep^[n] z).2.1+z.1*(divStep^[n] z).2.2=z.2.1+z.1*z.2.2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h₁,h₂,h₃,h₄⟩ := divStep_spec (divStep^[n] z)
    rw [ih.1] at h₁ h₄
    exact ⟨h₁,h₂.trans ih.2.1,by omega,h₄.trans ih.2.2.2⟩

lemma divIterate_stops (n m : ℕ) : divActive (divStep^[n] (m,n,0))=false := by
  apply bounded_stops divStep divActive (fun z => z.2.1)
    (fun z hz => by simp [divStep,hz]) (fun z hz => ?_) n (m,n,0) le_rfl
  have hh : 0<z.1 ∧ z.1≤z.2.1 := by simpa [divActive] using hz
  simp only [divStep,hz,ite_true]
  omega

lemma divIterate_result (n m : ℕ) : (divStep^[n] (m,n,0)).2=(n%m,n/m) := by
  obtain ⟨hm,_,_,hh⟩ := divIterate_spec n (m,n,0)
  have hs := divIterate_stops n m
  by_cases hm0 : m=0
  · subst m
    have hf : divStep (0,n,0)=(0,n,0) := by simp [divStep,divActive]
    rw [Function.iterate_fixed hf]
    simp
  · have hr : (divStep^[n] (m,n,0) ).2.1 < m := by
      have hpos : 0 < m := Nat.pos_of_ne_zero hm0
      simpa [divActive,hm,hpos] using hs
    simp only [Nat.mul_zero,Nat.add_zero] at hh
    have hq : n/m=(divStep^[n] (m,n,0)).2.2 := by
      apply Nat.div_eq_of_lt_le
      · nlinarith
      · nlinarith
    apply Prod.ext
    · have hn := Nat.mod_add_div n m
      rw [hq] at hn
      omega
    · exact hq.symm

namespace Poly
@[fun_prop] theorem natDivMod : Poly (fun z : ℕ×ℕ => (z.1%z.2,z.1/z.2)) := by
  have hs : Poly divStep := by unfold divStep divActive; fun_prop
  have hi : Poly (fun z : ℕ×(ℕ×(ℕ×ℕ)) => divStep^[z.1] z.2) :=
    boundedIterate divStep hs X (by
      intro z j hj
      obtain ⟨h₁,h₂,h₃,_⟩ := divIterate_spec j z.2
      simp only [encode_prod,pairBits_length,encode_nat,unary_length,eval_X,h₁]
      omega)
  have hh : Poly (fun z : ℕ×ℕ => (divStep^[z.1] (z.2,z.1,0)).2) := by fun_prop
  exact hh.congr (fun z => divIterate_result z.1 z.2)

@[fun_prop] theorem natDiv : Poly (fun z : ℕ×ℕ => z.1/z.2) := by
  have h : Poly (fun z : ℕ×ℕ => (z.1%z.2,z.1/z.2).2) := second _ natDivMod
  exact h
@[fun_prop] theorem natMod : Poly (fun z : ℕ×ℕ => z.1%z.2) := by
  have h : Poly (fun z : ℕ×ℕ => (z.1%z.2,z.1/z.2).1) := first _ natDivMod
  exact h
end Poly
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_IntegerRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

def intParts (z : ℤ) : Bool×ℕ := (decide (z<0),z.natAbs)
def fromParts (p : Bool×ℕ) : ℤ := if p.1 then -(p.2:ℤ) else p.2
instance instCodingInt : Coding ℤ := ⟨fun z => encode (intParts z)⟩
@[simp] lemma encode_int (z : ℤ) : encode z=encode (intParts z) := rfl
lemma fromParts_parts (z : ℤ) : fromParts (intParts z)=z := by
  simp only [fromParts,intParts,decide_eq_true_eq]
  split_ifs with h
  · exact (Int.eq_neg_natAbs_of_nonpos (le_of_lt h)).symm
  · exact Int.natAbs_of_nonneg (le_of_not_gt h)

lemma intParts_nat (n : ℕ) : intParts (n:ℤ)=(false,n) := by
  have h : ¬ (n:ℤ)<0 := by omega
  simp [intParts,h]
lemma intParts_fromParts (p : Bool×ℕ) :
    intParts (fromParts p)=(p.1 && !(decide (p.2=0)),p.2) := by
  rcases p with ⟨b,n⟩
  cases b with
  | false => simp [fromParts,intParts_nat]
  | true =>
    by_cases hn : n=0
    · subst n; simp [intParts,fromParts]
    · simp [intParts,fromParts,Nat.pos_iff_ne_zero,hn]

namespace Poly
@[fun_prop] theorem intParts_poly : Poly intParts := by
  exact ⟨(Routine.identity (encode : Bool×ℕ → List Bool)).reindex encode encode intParts intParts
    (fun _ => rfl) (fun _ => rfl)⟩

@[fun_prop] theorem natCastInt : Poly (Int.ofNat : ℕ → ℤ) := by
  have h : Poly (fun n : ℕ => (false,n)) := by fun_prop
  refine ⟨h.routine.reindex encode encode Int.ofNat id (fun _ => rfl) ?_⟩
  intro n
  change encode (false,n)=encode (intParts (n:ℤ))
  rw [intParts_nat]

@[fun_prop] theorem natToInt : Poly (fun n : ℕ => (n:ℤ)) := natCastInt

@[fun_prop] theorem fromParts_poly : Poly fromParts := by
  have h : Poly (fun p : Bool×ℕ => (p.1 && !(decide (p.2=0)),p.2)) := by
    apply pair
    · exact comp _ _ boolAnd (pair _ _ (by fun_prop) (comp _ _ boolNot (comp _ _ natZeroTest (by fun_prop))))
    · fun_prop
  refine ⟨h.routine.reindex encode encode fromParts id (fun _ => rfl) ?_⟩
  intro p
  simp only [id_eq,encode_int,intParts_fromParts]

@[fun_prop] theorem intNatAbs : Poly (Int.natAbs : ℤ → ℕ) := by
  have h : Poly (fun z : ℤ => (intParts z).2) := second _ intParts_poly
  exact h

@[fun_prop] theorem intSign : Poly (fun z : ℤ => decide (z<0)) := by
  have h : Poly (fun z : ℤ => (intParts z).1) := first _ intParts_poly
  exact h

@[fun_prop] theorem intNeg : Poly (fun z : ℤ => -z) := by
  have h : Poly (fun z : ℤ => fromParts (!(intParts z).1,(intParts z).2)) := by fun_prop
  exact h.congr (fun z => by cases z <;> simp [intParts,fromParts])

def addParts (p : (Bool×ℕ)×(Bool×ℕ)) : ℤ :=
  if p.1.1 then
    if p.2.1 then fromParts (true,p.1.2+p.2.2)
    else if decide (p.2.2≤p.1.2) then fromParts (true,p.1.2-p.2.2)
    else fromParts (false,p.2.2-p.1.2)
  else if p.2.1 then
    if decide (p.1.2≤p.2.2) then fromParts (true,p.2.2-p.1.2)
    else fromParts (false,p.1.2-p.2.2)
  else fromParts (false,p.1.2+p.2.2)

lemma addParts_eq (p q : Bool×ℕ) : addParts (p,q)=fromParts p+fromParts q := by
  rcases p with ⟨b,n⟩; rcases q with ⟨c,m⟩
  cases b <;> cases c <;> simp only [addParts,fromParts,Bool.false_eq_true,ite_false,ite_true,
    decide_eq_true_eq]
  · omega
  · split_ifs <;> omega
  · split_ifs <;> omega
  · omega

@[fun_prop] theorem intAdd : Poly (fun z : ℤ×ℤ => z.1+z.2) := by
  have ha : Poly addParts := by unfold addParts; fun_prop
  have h : Poly (fun z : ℤ×ℤ => addParts (intParts z.1,intParts z.2)) := by fun_prop
  exact h.congr (fun z => by rw [addParts_eq,fromParts_parts,fromParts_parts])

@[fun_prop] theorem intSub : Poly (fun z : ℤ×ℤ => z.1-z.2) := by
  have h : Poly (fun z : ℤ×ℤ => z.1+ -z.2) := by fun_prop
  exact h.congr (fun z => sub_eq_add_neg _ _)

@[fun_prop] theorem intMul : Poly (fun z : ℤ×ℤ => z.1*z.2) := by
  have hm : Poly (fun p : (Bool×ℕ)×(Bool×ℕ) => fromParts
      (if p.1.1 then !p.2.1 else p.2.1,p.1.2*p.2.2)) := by fun_prop
  have hp : Poly (fun z : ℤ×ℤ => (intParts z.1,intParts z.2)) :=
    pair _ _ (comp _ Prod.fst intParts_poly (first _ identity))
      (comp _ Prod.snd intParts_poly (second _ identity))
  have h := comp _ _ hm hp
  have he (p q : Bool×ℕ) :
      fromParts (if p.1 then !q.1 else q.1,p.2*q.2)=fromParts p*fromParts q := by
    rcases p with ⟨b,n⟩; rcases q with ⟨c,m⟩
    cases b <;> cases c <;> simp [fromParts]
  exact h.congr (fun z => by dsimp only; rw [he,fromParts_parts,fromParts_parts])

@[fun_prop] theorem intLE : Poly (fun z : ℤ×ℤ => decide (z.1≤z.2)) := by
  have h : Poly (fun z : ℤ×ℤ => !(decide (z.2-z.1<0))) := by
    exact comp _ _ boolNot (comp _ _ intSign (comp _ (fun z : ℤ×ℤ => (z.2,z.1)) intSub (by fun_prop)))
  exact h.congr (fun z => by simp [←decide_not,sub_neg])

@[fun_prop] theorem intLT : Poly (fun z : ℤ×ℤ => decide (z.1<z.2)) := by
  have h : Poly (fun z : ℤ×ℤ => decide (z.1-z.2<0)) := comp _ _ intSign intSub
  exact h.congr (fun z => by simp [sub_neg])

@[fun_prop] theorem intEQ : Poly (fun z : ℤ×ℤ => decide (z.1=z.2)) := by
  have h : Poly (fun z : ℤ×ℤ => decide ((z.1-z.2).natAbs=0)) :=
    comp _ _ natZeroTest (comp _ _ intNatAbs intSub)
  exact h.congr (fun z => by simp [sub_eq_zero])

@[fun_prop] theorem intMin : Poly (fun z : ℤ×ℤ => min z.1 z.2) := by
  have h : Poly (fun z : ℤ×ℤ => if decide (z.1≤z.2) then z.1 else z.2) := by fun_prop
  exact h.congr (fun z => by simp [min_def])
@[fun_prop] theorem intMax : Poly (fun z : ℤ×ℤ => max z.1 z.2) := by
  have h : Poly (fun z : ℤ×ℤ => if decide (z.1≤z.2) then z.2 else z.1) := by fun_prop
  exact h.congr (fun z => by simp [max_def])
@[fun_prop] theorem intToNat : Poly (Int.toNat : ℤ → ℕ) := by
  have h : Poly (fun z : ℤ => if (intParts z).1 then 0 else (intParts z).2) := by fun_prop
  exact h.congr (fun z => by cases z <;> simp [intParts])
variable {α : Type} [Coding α]
@[fun_prop] theorem intLt_apply (f g : α → ℤ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a<g a)) := comp _ _ intLT (pair _ _ hf hg)
@[fun_prop] theorem intLe_apply (f g : α → ℤ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a≤g a)) := comp _ _ intLE (pair _ _ hf hg)
end Poly
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_ListNumeric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma code_option_none {α : Type} [Coding α] : encode (none:Option α)=[] := rfl
lemma code_option_some {α : Type} [Coding α] (a : α) :
    (encode (some a)).length=2*(encode a).length+1 := by
  change (encode ([a]:List α)).length=_
  simp

lemma fold_code_additive {α β : Type} [Coding α] [Coding β]
    (f : β×α → β) (C : ℕ)
    (hf : ∀ z,(encode (f z)).length≤(encode z.1).length+C*(2*(encode z.2).length+1))
    (l : List α) (b : β) :
    (encode (l.foldl (fun b a => f (b,a)) b)).length≤
      (encode b).length+C*(encode l).length := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    have h := hf (b,a)
    have hi := ih (f (b,a))
    simp only [List.foldl_cons,code_cons,pairBits_length]
    nlinarith

namespace Poly
variable {α β : Type} [Coding α] [Coding β]

theorem listFoldAdd [Inhabited α] (f : β×α → β) (hf : Poly f) (C : ℕ)
    (hb : ∀ z,(encode (f z)).length≤(encode z.1).length+C*(2*(encode z.2).length+1)) :
    Poly (fun z : List α×β => z.1.foldl (fun b a => f (b,a)) z.2) := by
  apply listFold default f hf ((Polynomial.C C+1)*X)
  intro z k
  have hh := fold_code_additive f C hb (z.1.take k) z.2
  have ht := code_take_le z.1 k
  have hm := Nat.mul_le_mul_left C ht
  simp only [encode_prod,pairBits_length,eval_mul,eval_add,eval_C,eval_one,eval_X]
  nlinarith

@[fun_prop] theorem listDrop : Poly (fun z : ℕ×List α => z.2.drop z.1) := by
  have hi := boundedIterate (List.tail:List α → List α) listTail X (by
    intro z j hj
    have he : ∀ (k : ℕ) (l : List α),List.tail^[k] l=l.drop k := by
      intro k l
      induction k with
      | zero => simp
      | succ k ih => simp [Function.iterate_succ_apply',ih,List.tail_drop]
    rw [he]
    have hh := code_drop_le z.2 j
    simp only [encode_prod,pairBits_length,eval_X]
    omega)
  apply hi.congr
  intro z
  induction z.1 generalizing z with
  | zero => simp
  | succ k ih => simp [Function.iterate_succ_apply',ih,List.tail_drop]

@[fun_prop] theorem listGetD (a : α) : Poly (fun z : List α×ℕ => z.1[z.2]?.getD a) := by
  have h : Poly (fun z : List α×ℕ => (z.1.drop z.2).headD a) := by fun_prop
  exact h.congr (fun z => by simp only [List.headD_eq_head?_getD,List.head?_drop])

@[fun_prop] theorem listNatSum : Poly (List.sum : List ℕ → ℕ) := by
  have hfold := listFoldAdd (fun z : ℕ×ℕ => z.1+z.2) natAdd 1 (by
    intro z; simp only [encode_nat,unary_length]; omega)
  have h : Poly (fun l : List ℕ => l.foldl (·+·) 0) := comp _ (fun l : List ℕ => (l,0)) hfold (by fun_prop)
  exact h.congr (fun l => by simp [List.sum_eq_foldl])

@[fun_prop] theorem listIntSum : Poly (List.sum : List ℤ → ℤ) := by
  have hfold := listFoldAdd (fun z : ℤ×ℤ => z.1+z.2) intAdd 1 (by
    intro z
    have h := Int.natAbs_add_le z.1 z.2
    simp only [encode_int,encode_prod,pairBits_length,intParts,encode_bool,List.length_singleton,
      encode_nat,unary_length]
    omega)
  have h : Poly (fun l : List ℤ => l.foldl (·+·) 0) := comp _ (fun l : List ℤ => (l,0)) hfold (by fun_prop)
  exact h.congr (fun l => by simp [List.sum_eq_foldl])

end Poly

def rangeStep (z : ℕ×List ℕ) : ℕ×List ℕ := (z.1+1,z.2++[z.1])
lemma rangeStep_iterate (k : ℕ) (z : ℕ×List ℕ) :
    rangeStep^[k] z=(z.1+k,z.2++List.range' z.1 k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp [Function.iterate_succ_apply',ih,rangeStep,List.range'_concat,List.append_assoc,Nat.add_assoc]

namespace Poly
@[fun_prop] theorem listRange : Poly List.range := by
  have hs : Poly rangeStep := by unfold rangeStep; fun_prop
  have hi : Poly (fun z : ℕ×(ℕ×List ℕ) => rangeStep^[z.1] z.2) :=
    boundedIterate rangeStep hs (8*(X+1)^2) (by
      intro z j hj
      rw [rangeStep_iterate]
      have hb := list_code_bound (List.range' z.2.1 j) (z.2.1+j) (by
        intro a ha
        obtain ⟨i,hi,he⟩ := List.mem_range'.mp ha
        simp only [encode_nat,unary_length]
        omega)
      simp only [List.length_range'] at hb
      simp only [encode_prod,pairBits_length,encode_nat,unary_length,code_append,List.length_append,
        eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
      nlinarith [Nat.mul_le_mul hj hj, Nat.mul_le_mul_right z.2.1 hj])
  have h : Poly (fun n : ℕ => (rangeStep^[n] (0,[])).2) := by fun_prop
  exact h.congr (fun n => by simp [rangeStep_iterate,List.range_eq_range'])
end Poly
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.StdSimplexCompat
/-!
# Standard simplex compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. Both have the structure `Convexity.StdSimplex`, but `0df444a`
lacks part of its API (the files `Mathlib.Geometry.Convex.ConvexSpace.{Topology,
CompactSpaceStdSimplex, Barycenter, PathConnectedSpaceStdSimplex}` and some lemmas of `Defs`),
and its `SimplexCategory.toTop` takes the topological simplex to be the subtype
`stdSimplex ℝ (Fin (n+1))`, where `d13f23b` takes the structure.

Part 1 adds the missing `d13f23b` API to `Convexity.StdSimplex` under its `d13f23b` names. It is
copied from Mathlib `d13f23b` (Copyright (c) 2025 Lean FRO, LLC, authors Kim Morrison, Andrew
Yang, Yaël Dillies; Copyright (c) 2026 Joël Riou; released under the Apache 2.0 license), adapted
to `0df444a` (module keywords removed).

Part 2 (`OAI.SStd`) is ours: the subtype `stdSimplex R X` on a finite type with the `d13f23b`
names, for ported code that identifies the simplex with `SimplexCategory.toTop.obj`; there the
port rewrites `Convexity.StdSimplex` to `OAI.SStd`.
-/

noncomputable section StdSimplexCompat

universe u v w

open Topology

/-! ## Part 1: the `d13f23b` API missing from `0df444a`, on `Convexity.StdSimplex` -/

namespace Convexity

namespace StdSimplex

section Semiring

variable {R : Type u} [PartialOrder R] [Semiring R] {X Y Z : Type*}

@[simp]
lemma total_of_fintype [Fintype X] (w : StdSimplex R X) :
    ∑ i, w.weights i = 1 := by
  have := w.total
  rwa [Finsupp.sum_fintype _ _ (by simp)] at this

@[simp]
lemma total_fin_two (w : StdSimplex R (Fin 2)) :
    w.weights 0 + w.weights 1 = 1 := by
  rw [← w.total_of_fintype, Fin.sum_univ_two]

@[simp]
lemma weights_apply_eq_one [Subsingleton X] (s : StdSimplex R X) (m : X) :
    s.weights m = 1 := by
  rw [← s.total, Finsupp.sum_eq_single m
    (fun _ _ h ↦ (h (by subsingleton)).elim) (by simp)]

instance instSubsingleton [Subsingleton X] : Subsingleton (StdSimplex R X) where
  allEq := by
    intro a b
    ext m
    simp

variable [IsStrictOrderedRing R]

@[simp]
lemma weights_apply_le_one
    (s : StdSimplex R X) (m : X) : s.weights m ≤ 1 := by
  by_cases hm : s.weights m = 0
  · simpa only [hm] using zero_le_one' R
  · rw [← s.total, Finsupp.sum]
    exact Finset.single_le_sum (fun i _ => s.weights_nonneg i) (Finsupp.mem_support_iff.mpr hm)

instance instInhabited [Inhabited X] : Inhabited (StdSimplex R X) where
  default := .single default

instance instNonempty [Nonempty X] : Nonempty (StdSimplex R X) :=
  ⟨.single (Classical.arbitrary _)⟩

instance instUnique [Unique X] : Unique (StdSimplex R X) where
  uniq := by subsingleton

end Semiring

section

variable {R' : Type*} [Ring R'] [PartialOrder R'] [IsStrictOrderedRing R']

/-- The bijection between the one dimensional standard simplex and the interval `[0, 1]`. -/
@[simps -isSimp]
def equivIcc : StdSimplex R' (Fin 2) ≃ Set.Icc (0 : R') 1 where
  toFun s := ⟨s.weights 1, s.weights_nonneg 1, s.weights_apply_le_one 1⟩
  invFun t := duple (s := 1 - t) (t := t) 0 1 (sub_nonneg.mpr t.2.2) t.2.1 (by simp)
  left_inv s := by
    ext i
    fin_cases i
    · have := s.total_fin_two
      simp
      exact (eq_sub_of_add_eq this).symm
    · simp
  right_inv t := by
    ext
    simp [Finsupp.single_apply]

attribute [local simp] equivIcc_apply_coe

@[simp]
lemma equivIcc_single_zero : equivIcc (.single (R := R') 0) = 0 := by
  ext
  simp [Finsupp.single_apply]

@[simp]
lemma equivIcc_single_one : equivIcc (.single (R := R') 1) = 1 := by
  ext
  simp

@[simp]
lemma equivIcc_symm_zero : equivIcc.symm 0 = .single (R := R') 0 :=
  equivIcc.injective (by simp)

@[simp]
lemma equivIcc_symm_one : equivIcc.symm 1 = .single (R := R') 1 :=
  equivIcc.injective (by simp)

end

section ConvexSpace

variable {R : Type u} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] {I : Type*}

@[simp]
lemma iConvexComb_single (x : StdSimplex R I) :
    x.iConvexComb single = x := by
  ext : 1
  simp [weights_iConvexComb, Finsupp.smul_single_one, Finsupp.sum_single]

end ConvexSpace

end StdSimplex

/-! ### Topology (Mathlib `d13f23b`, `Geometry/Convex/ConvexSpace/Topology.lean`) -/

namespace StdSimplex

variable (R : Type u) [PartialOrder R] [Ring R] [TopologicalSpace R]

/-- The topology on `StdSimplex R ι` that is induced by the embedding
`StdSimplex R ι → (ι → R)`. This is the correct topoplogy only when
`ι` is finite, see `StdSimplex.isEmbedding_toFun_comp_weights`. -/
abbrev topologicalSpaceInduced (ι : Type*) : TopologicalSpace (StdSimplex R ι) :=
  .induced (fun t ↦ t.weights : StdSimplex R ι → ι → R) inferInstance

namespace topologicalSpaceInduced

attribute [local instance] topologicalSpaceInduced

@[fun_prop]
lemma continuous_weights_apply {ι : Type*} (i : ι) :
    Continuous (fun (t : StdSimplex R ι) ↦ t.weights i) :=
  (continuous_apply i).comp (by rw [continuous_iff_le_induced])

open Classical in
@[fun_prop]
lemma continuous_map_weights_apply
    [IsStrictOrderedRing R] [IsTopologicalRing R] {ι₁ ι₂ : Type*}
    [Finite ι₁] (f : ι₁ → ι₂) (i₂ : ι₂) :
    Continuous (fun t ↦ (map (R := R) f t).weights i₂) := by
  have := Fintype.ofFinite ι₁
  have (t : StdSimplex R ι₁) :
      (map (R := R) f t).weights i₂ =
        ∑ i₁ with f i₁ = i₂, t.weights i₁ := by
    rw [weights_map, Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp),
      Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply, Finset.sum_filter]
  simp only [this]
  fun_prop

end topologicalSpaceInduced

variable [IsStrictOrderedRing R] [IsTopologicalRing R]

attribute [local instance] topologicalSpaceInduced in
/-- The topology on `StdSimplex R M`: the supremum of the coinduced topologies for the maps
`StdSimplex.map f : StdSimplex R ι → StdSimplex R M` with `ι` finite. When `M` is finite it is the
topology induced by the embedding `StdSimplex R M → (M → R)`. -/
noncomputable instance topologicalSpace (M : Type v) :
    TopologicalSpace (StdSimplex R M) :=
  ⨆ (ι : Type v) (_ : Finite ι) (f : ι → M), .coinduced (map f) inferInstance

end StdSimplex

/-! ### Compactness (Mathlib `d13f23b`, `CompactSpaceStdSimplex.lean`) -/

/-! ### Barycenters (Mathlib `d13f23b`, `Barycenter.lean`) -/

namespace StdSimplex

variable {K M : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]

/-- In the standard simplex with vertices `M`, the barycenter of a nonempty finite subset `S`. -/
@[simps -isSimp]
noncomputable def subBarycenter (S : Finset M) (hS : S.Nonempty) : StdSimplex K M where
  weights := S.sum (fun m ↦ .single m (S.card : K)⁻¹)
  nonneg := Finset.sum_nonneg (fun m _ => by
    classical
    intro i
    rw [Finsupp.single_apply]
    split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_rfl)
  total := by
    rw [← Finsupp.sum_finsetSum_index (by simp) (by simp)]
    simp only [Finsupp.sum_single_index, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Finset.card_pos.mpr hS).ne')

@[simp]
lemma subBarycenter_singleton (m : M) :
    subBarycenter (K := K) {m} (by simp) = .single m := by
  ext
  simp [weights_subBarycenter]

end StdSimplex

/-! ### Path-connectedness (Mathlib `d13f23b`, `PathConnectedSpaceStdSimplex.lean`) -/

end Convexity

/-! ## Part 2: `OAI.SStd`, the subtype `stdSimplex R X` with the `d13f23b` names -/

end StdSimplexCompat
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite loopless multigraphs, perfect matching indicators, and their convex hull.
The edge type distinguishes parallel edges. Feasible laws are probability vectors
on perfect matchings with a prescribed mean.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

instance incidentDecidable (G : LooplessGraph V E) (v : V) (e : E) :
    Decidable (G.Incident v e) := inferInstanceAs (Decidable (G.left e = v ∨ G.right e = v))

def indicator (G : LooplessGraph V E) (M : G.Matching) (e : E) : ℝ :=
  if e ∈ M.val then 1 else 0

def mean (G : LooplessGraph V E) (p : G.Matching → ℝ) (e : E) : ℝ :=
  ∑ M, p M * G.indicator M e

omit [Fintype V] [Fintype E] [DecidableEq V] in
@[simp] theorem indicator_nonneg (G : LooplessGraph V E) (M : G.Matching) (e : E) :
    0 ≤ G.indicator M e := by
  simp only [indicator]
  split <;> norm_num

omit [Fintype V] [Fintype E] [DecidableEq V] in
@[simp] theorem indicator_le_one (G : LooplessGraph V E) (M : G.Matching) (e : E) :
    G.indicator M e ≤ 1 := by
  simp only [indicator]
  split <;> norm_num

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mean_single (G : LooplessGraph V E) (M : G.Matching) :
    G.mean (Pi.single M 1) = G.indicator M := by
  classical
  ext e
  simp [mean, Pi.single_apply, ite_mul]


end LooplessGraph

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_OddCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Degree and odd-cut constraints for the perfect matching polytope.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

/-- Exactly one endpoint in S; edge identities are kept, including parallels. -/
def Crosses (G : LooplessGraph V E) (S : Finset V) (e : E) : Prop :=
  (G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.left e ∉ S ∧ G.right e ∈ S)

instance crossesDecidable (G : LooplessGraph V E) (S : Finset V) (e : E) :
    Decidable (G.Crosses S e) := inferInstanceAs (Decidable
      ((G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.left e ∉ S ∧ G.right e ∈ S)))

def cut (G : LooplessGraph V E) (S : Finset V) : Finset E :=
  Finset.univ.filter (G.Crosses S)

def degree (G : LooplessGraph V E) (x : E → ℝ) (v : V) : ℝ :=
  ∑ e, if G.Incident v e then x e else 0

def cutMass (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ G.cut S, x e

omit [Fintype V] [DecidableEq E] in
@[simp] theorem mem_cut (G : LooplessGraph V E) (S : Finset V) (e : E) :
    e ∈ G.cut S ↔ G.Crosses S e := by simp [cut]

omit [Fintype E] [DecidableEq E] in
theorem crosses_compl (G : LooplessGraph V E) (S : Finset V) (e : E) :
    G.Crosses Sᶜ e ↔ G.Crosses S e := by
  simp only [Crosses, Finset.mem_compl, not_not]
  tauto

omit [DecidableEq E] in
@[simp] theorem cut_compl (G : LooplessGraph V E) (S : Finset V) :
    G.cut Sᶜ = G.cut S := by ext; simp [crosses_compl]

end LooplessGraph

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Polytope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Tutte's criterion and Edmonds' perfect matching polytope theorem for multigraphs.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph


omit [Fintype V] [Fintype E] [DecidableEq E] in
@[simp] theorem crosses_singleton (G : LooplessGraph V E) (v : V) (e : E) :
    G.Crosses {v} e ↔ G.Incident v e := by
  have hh := G.loopless e
  simp only [Crosses, Finset.mem_singleton, Incident]
  have hn : ¬ (G.left e=v ∧ G.right e=v) := fun h => hh (h.1.trans h.2.symm)
  tauto

omit [Fintype V] [DecidableEq E] in
@[simp] theorem cutMass_singleton (G : LooplessGraph V E) (x : E → ℝ) (v : V) :
    G.cutMass x {v} = G.degree x v := by
  simp [cutMass,cut,Finset.sum_filter,degree]

end LooplessGraph

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite Shannon entropy and attainment of its supremum over feasible matching laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_UnitFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.UnitFlow
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Matrix (V : Type*) := V → V → ℤ

def divergence (b : Matrix V) (i : V) : ℤ := ∑ j, b i j

def cutCapacity (c : V → V → ℕ) (S : Finset V) : ℕ :=
  ∑ i ∈ S, ∑ j ∈ Sᶜ, c i j

def cutFlow (b : Matrix V) (S : Finset V) : ℤ :=
  ∑ i ∈ S, ∑ j ∈ Sᶜ, b i j

structure Feasible (c : V → V → ℕ) (a z : V) (b : Matrix V) : Prop where
  antisymm : ∀ i j, b i j = -b j i
  capacity : ∀ i j, b i j ≤ c i j
  conservation : ∀ i, i ≠ a → i ≠ z → divergence b i = 0

omit [DecidableEq V] in
lemma feasible_zero (c : V → V → ℕ) (a z : V) :
    Feasible c a z (fun _ _ => 0) where
  antisymm _ _ := by simp
  capacity _ _ := by positivity
  conservation _ _ _ := by simp [divergence]

omit [Fintype V] [DecidableEq V] in
lemma antisymm_internal (b : Matrix V) (h : ∀ i j, b i j = -b j i)
    (S : Finset V) : (∑ i ∈ S, ∑ j ∈ S, b i j) = 0 := by
  have hh : (∑ i ∈ S, ∑ j ∈ S, b i j) = -(∑ i ∈ S, ∑ j ∈ S, b i j) := by
    calc
      _ = ∑ i ∈ S, ∑ j ∈ S, -b j i := by
        apply sum_congr rfl; intro i hi
        apply sum_congr rfl; intro j hj
        exact h i j
      _ = -(∑ i ∈ S, ∑ j ∈ S, b j i) := by simp
      _ = _ := by rw [sum_comm]
  omega

lemma divergence_cut (b : Matrix V) (h : ∀ i j, b i j = -b j i)
    (S : Finset V) : (∑ i ∈ S, divergence b i) = cutFlow b S := by
  have split : ∀ i, divergence b i = (∑ j ∈ S, b i j) + ∑ j ∈ Sᶜ, b i j := by
    intro i
    exact (sum_add_sum_compl S (fun j => b i j)).symm
  simp_rw [split]
  rw [sum_add_distrib, antisymm_internal b h S, zero_add]
  rfl

lemma source_cut {c : V → V → ℕ} {a z : V} {b : Matrix V}
    (h : Feasible c a z b) (S : Finset V) (ha : a ∈ S) (hz : z ∉ S) :
    cutFlow b S = divergence b a := by
  rw [← divergence_cut b h.antisymm]
  exact sum_eq_single a (fun i hi hia => h.conservation i hia (by intro e; subst i; exact hz hi))
    (fun hna => (hna ha).elim)

lemma cutFlow_le_capacity {c : V → V → ℕ} {b : Matrix V}
    (h : ∀ i j, b i j ≤ c i j) (S : Finset V) :
    cutFlow b S ≤ cutCapacity c S := by
  simp only [cutFlow, cutCapacity, Nat.cast_sum]
  exact sum_le_sum (fun i _ => sum_le_sum (fun j _ => h i j))

lemma weak_duality {c : V → V → ℕ} {a z : V} {b : Matrix V}
    (h : Feasible c a z b) (S : Finset V) (ha : a ∈ S) (hz : z ∉ S) :
    divergence b a ≤ cutCapacity c S := by
  rw [← source_cut h S ha hz]
  exact cutFlow_le_capacity h.capacity S

lemma saturated_minimum {c : V → V → ℕ} {a z : V} {b : Matrix V}
    (h : Feasible c a z b) (S : Finset V) (ha : a ∈ S) (hz : z ∉ S)
    (hsat : ∀ i ∈ S, ∀ j ∉ S, b i j = c i j) :
    ∀ T : Finset V, a ∈ T → z ∉ T → cutCapacity c S ≤ cutCapacity c T := by
  have heq : cutFlow b S = cutCapacity c S := by
    simp only [cutFlow, cutCapacity, Nat.cast_sum]
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro j hj
    exact hsat i hi j (mem_compl.mp hj)
  intro T hTa hTz
  have := weak_duality h T hTa hTz
  rw [← source_cut h S ha hz, heq] at this
  exact_mod_cast this

omit [DecidableEq V] in
lemma source_bound {c : V → V → ℕ} {a z : V} {b : Matrix V}
    (h : Feasible c a z b) : divergence b a ≤ ∑ j, (c a j : ℤ) :=
  sum_le_sum (fun j _ => h.capacity a j)

def arc (u v : V) : Matrix V := fun i j =>
  (if i=u ∧ j=v then 1 else 0) - (if i=v ∧ j=u then 1 else 0)

omit [Fintype V] in
lemma arc_antisymm (u v i j : V) : arc u v i j = -arc u v j i := by
  simp only [arc]
  have h₁ : (i=u ∧ j=v) ↔ (j=v ∧ i=u) := and_comm
  have h₂ : (i=v ∧ j=u) ↔ (j=u ∧ i=v) := and_comm
  simp only [h₁, h₂]
  ring

lemma arc_divergence (u v i : V) : divergence (arc u v) i =
    (if i=u then 1 else 0) - (if i=v then 1 else 0) := by
  simp only [divergence, arc, sum_sub_distrib]
  simp_rw [ite_and]
  simp

def pathFlow : List V → Matrix V
  | [] => fun _ _ => 0
  | [_] => fun _ _ => 0
  | v::u::p => fun i j => pathFlow (u::p) i j + arc u v i j

omit [Fintype V] in
lemma pathFlow_antisymm (p : List V) (i j : V) :
    pathFlow p i j = -pathFlow p j i := by
  induction p using List.twoStepInduction with
  | nil => simp [pathFlow]
  | singleton v => simp [pathFlow]
  | cons_cons v u p _ ih =>
    simp only [pathFlow]
    rw [ih, arc_antisymm]
    ring

lemma pathFlow_divergence (p : List V) (i : V) :
    divergence (pathFlow p) i =
      (if p.getLast? = some i then 1 else 0) -
      (if p.head? = some i then 1 else 0) := by
  induction p using List.twoStepInduction with
  | nil => simp [pathFlow, divergence]
  | singleton v => simp [pathFlow, divergence]
  | cons_cons v u p _ ih =>
    rw [show divergence (pathFlow (v::u::p)) i =
        divergence (pathFlow (u::p)) i + divergence (arc u v) i by
      simp [divergence, pathFlow, sum_add_distrib]]
    rw [ih, arc_divergence]
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_cons_cons]
    by_cases hiu : i=u <;> by_cases hiv : i=v <;> simp_all [eq_comm, sub_eq_add_neg]

omit [Fintype V] in
lemma pathFlow_zero_of_not_mem (p : List V) (i j : V) (hi : i ∉ p) :
    pathFlow p i j = 0 := by
  induction p using List.twoStepInduction with
  | nil => rfl
  | singleton v => rfl
  | cons_cons v u p _ ih =>
    have hiv : i ≠ v := by intro hh; exact hi (by simp [hh])
    have hit : i ∉ u::p := by intro hh; exact hi (List.mem_cons_of_mem _ hh)
    have hiu : i ≠ u := by intro hh; exact hit (by simp [hh])
    simp [pathFlow, ih u hit, arc, hiv, hiu]

omit [Fintype V] in
lemma pathFlow_le_one (p : List V) (hp : p.Nodup) (i j : V) : pathFlow p i j ≤ 1 := by
  induction p using List.twoStepInduction with
  | nil => simp [pathFlow]
  | singleton v => simp [pathFlow]
  | cons_cons v u p _ ih =>
    have hv : v ∉ u::p := hp.notMem
    have htail := ih u hp.of_cons
    by_cases hiv : i = v
    · subst i
      simp only [pathFlow]
      rw [pathFlow_zero_of_not_mem _ _ _ hv]
      simp only [arc]
      split_ifs <;> omega
    · by_cases hjv : j = v
      · subst j
        have hz : pathFlow (u::p) i v = 0 := by
          rw [pathFlow_antisymm, pathFlow_zero_of_not_mem _ _ _ hv, neg_zero]
        simp only [pathFlow]
        rw [hz]
        simp only [arc]
        split_ifs <;> omega
      · simpa [pathFlow, arc, hiv, hjv] using htail

omit [Fintype V] in
lemma pathFlow_pos_relation (R : V → V → Prop) (p : List V) (hp : p.Nodup)
    (hc : p.IsChain (fun v u => R u v)) (i j : V) (hij : 0 < pathFlow p i j) :
    R i j := by
  induction p using List.twoStepInduction with
  | nil => simp [pathFlow] at hij
  | singleton v => simp [pathFlow] at hij
  | cons_cons v u p _ ih =>
    have hv : v ∉ u::p := hp.notMem
    have huv : u ≠ v := by intro e; exact hv (by simp [e])
    have ht : (u::p).IsChain (fun v u => R u v) := hc.tail
    have hr : R u v := (List.isChain_cons_cons.mp hc).1
    by_cases hiv : i = v
    · subst i
      simp only [pathFlow] at hij
      rw [pathFlow_zero_of_not_mem _ _ _ hv] at hij
      simp only [arc] at hij
      by_cases hju : j=u <;> simp [huv, huv.symm, hju] at hij
    · by_cases hjv : j = v
      · subst j
        have hz : pathFlow (u::p) i v = 0 := by
          rw [pathFlow_antisymm, pathFlow_zero_of_not_mem _ _ _ hv, neg_zero]
        simp only [pathFlow] at hij
        rw [hz] at hij
        by_cases hiu : i=u
        · simpa [hiu] using hr
        · simp [arc, hiu, hiv] at hij
      · apply ih u hp.of_cons ht
        simpa [pathFlow, arc, hiv, hjv] using hij

lemma augment_feasible {c : V → V → ℕ} {a z : V} {b : Matrix V}
    (hb : Feasible c a z b) (p : List V) (hp : p.Nodup)
    (hc : p.IsChain (fun v u => b u v < c u v))
    (hhead : p.head? = some z) (hlast : p.getLast? = some a) :
    Feasible c a z (fun i j => b i j + pathFlow p i j) where
  antisymm i j := by rw [hb.antisymm, pathFlow_antisymm]; ring
  capacity i j := by
    have hcap := hb.capacity i j
    by_cases hpos : 0 < pathFlow p i j
    · have hres := pathFlow_pos_relation (fun u v => b u v < c u v) p hp hc i j hpos
      have hle := pathFlow_le_one p hp i j
      omega
    · omega
  conservation i hia hiz := by
    simp only [divergence, sum_add_distrib]
    change divergence b i + divergence (pathFlow p) i = 0
    rw [hb.conservation i hia hiz, pathFlow_divergence, hhead, hlast]
    simp [Ne.symm hia, Ne.symm hiz]

lemma augment_value {a z : V} (haz : a ≠ z) (b : Matrix V) (p : List V)
    (hhead : p.head? = some z) (hlast : p.getLast? = some a) :
    divergence (fun i j => b i j + pathFlow p i j) a = divergence b a + 1 := by
  simp only [divergence, sum_add_distrib]
  change divergence b a + divergence (pathFlow p) a = _
  rw [pathFlow_divergence, hhead, hlast]
  simp [Ne.symm haz, divergence]

end BinaryMatching.UnitFlow
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_CutAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.CutAlgebra
open Finset UnitFlow
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

abbrev cross (S : Finset V) (i j : V) : Prop := i∈S ∧ j∉S

def push (c : V → V → ℕ) (f : V → W) (i j : W) : ℕ :=
  if i=j then 0 else ∑ u, ∑ v, if f u=i ∧ f v=j then c u v else 0

def lift (f : V → W) (T : Finset W) : Finset V := univ.filter (fun v => f v∈T)

omit [DecidableEq V] [Fintype W] in
lemma mem_lift (f : V → W) (T : Finset W) (v : V) : v∈lift f T ↔ f v∈T := by
  simp [lift]

omit [DecidableEq V] [DecidableEq W] in
lemma sum_four_swap (h : W → W → V → V → ℕ) :
    (∑ i, ∑ j, ∑ u, ∑ v, h i j u v) = ∑ u, ∑ v, ∑ i, ∑ j, h i j u v := by
  calc
    _ = ∑ i, ∑ u, ∑ j, ∑ v, h i j u v := by
      apply sum_congr rfl; intro i hi
      rw [sum_comm]
    _ = ∑ u, ∑ i, ∑ j, ∑ v, h i j u v := by rw [sum_comm]
    _ = ∑ u, ∑ i, ∑ v, ∑ j, h i j u v := by
      apply sum_congr rfl; intro u hu
      apply sum_congr rfl; intro i hi
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl; intro u hu
      rw [sum_comm]

end BinaryMatching.CutAlgebra
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_ResidualSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.ResidualSearch
open Finset
variable {n : ℕ}
abbrev Table (n : ℕ) := Fin n → Option (List (Fin n))

def initial (a : Fin n) : Table n := fun v => if v=a then some [a] else none

def predecessor (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (v : Fin n) : Option (Fin n) :=
  (List.finRange n).find? (fun u => decide (R u v) && (p u).isSome)

def step (R : Fin n → Fin n → Prop) [DecidableRel R] (p : Table n) : Table n :=
  fun v => match p v with
  | some l => some l
  | none => match predecessor R p v with
    | none => none
    | some u => (p u).map (fun l => v::l)

def search (R : Fin n → Fin n → Prop) [DecidableRel R] (a : Fin n) : ℕ → Table n
  | 0 => initial a
  | k+1 => step R (search R a k)

def reached (p : Table n) : Finset (Fin n) := univ.filter (fun v => (p v).isSome)

def Closed (R : Fin n → Fin n → Prop) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v, R u v → v ∈ S

structure Good (R : Fin n → Fin n → Prop) (a : Fin n) (p : Table n) : Prop where
  head : ∀ v l, p v=some l → l.head?=some v
  last : ∀ v l, p v=some l → l.getLast?=some a
  simple : ∀ v l, p v=some l → l.Nodup
  chain : ∀ v l, p v=some l → l.IsChain (fun v u => R u v)
  visited : ∀ v l, p v=some l → ∀ u∈l, (p u).isSome

lemma mem_reached (p : Table n) (v : Fin n) : v∈reached p ↔ (p v).isSome := by
  simp [reached]

lemma predecessor_some (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (v u : Fin n) (h : predecessor R p v=some u) :
    R u v ∧ (p u).isSome := by
  have := List.find?_some h
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using this

lemma predecessor_exists (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (v : Fin n) :
    (predecessor R p v).isSome ↔ ∃ u, R u v ∧ (p u).isSome := by
  simp [predecessor, List.find?_isSome, Bool.and_eq_true]

lemma step_old (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (v : Fin n) (l : List (Fin n)) (h : p v=some l) :
    step R p v=some l := by simp [step, h]

lemma step_some (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (v : Fin n) (l : List (Fin n)) (h : step R p v=some l) :
    p v=some l ∨ (p v=none ∧ ∃ u t, p u=some t ∧ R u v ∧ l=v::t) := by
  unfold step at h
  cases he : p v with
  | some t => simp only [he] at h; exact Or.inl h
  | none =>
    simp only [he] at h
    cases hu : predecessor R p v with
    | none => simp [hu] at h
    | some u =>
      have hh := predecessor_some R p v u hu
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hh.2
      simp [hu, ht] at h
      exact Or.inr ⟨rfl, u, t, ht, hh.1, h.symm⟩

lemma step_reached (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (v : Fin n) :
    v∈reached (step R p) ↔ v∈reached p ∨ ∃ u∈reached p, R u v := by
  simp only [mem_reached]
  constructor
  · intro h
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp h
    rcases step_some R p v l hl with ho | ⟨_,u,t,ht,hr,_⟩
    · exact Or.inl (by simp [ho])
    · exact Or.inr ⟨u, by simp [ht], hr⟩
  · rintro (ho | ⟨u,hu,hr⟩)
    · obtain ⟨l,hl⟩ := Option.isSome_iff_exists.mp ho
      simp [step_old R p v l hl]
    · cases hv : p v with
      | some l => simp [step_old R p v l hv]
      | none =>
        have hh : (predecessor R p v).isSome := (predecessor_exists R p v).2 ⟨u,hr,hu⟩
        obtain ⟨w,hw⟩ := Option.isSome_iff_exists.mp hh
        obtain ⟨l,hl⟩ := Option.isSome_iff_exists.mp (predecessor_some R p v w hw).2
        simp [step,hv,hw,hl]

lemma reached_mono (R : Fin n → Fin n → Prop) [DecidableRel R] (p : Table n) :
    reached p ⊆ reached (step R p) := fun v hv => (step_reached R p v).2 (Or.inl hv)

lemma good_initial (R : Fin n → Fin n → Prop) (a : Fin n) : Good R a (initial a) := by
  constructor
  all_goals intro v l h; by_cases hv : v=a
  all_goals simp [initial,hv] at h
  all_goals subst v; subst l
  · rfl
  · rfl
  · simp
  · simp
  · intro u hu; simpa [initial] using hu

lemma good_step (R : Fin n → Fin n → Prop) [DecidableRel R]
    (a : Fin n) (p : Table n) (hp : Good R a p) : Good R a (step R p) := by
  have hpaths : ∀ v l, step R p v=some l →
      l.head?=some v ∧ l.getLast?=some a ∧ l.Nodup ∧
      l.IsChain (fun v u => R u v) ∧ ∀ u∈l, (step R p u).isSome := by
    intro v l hl
    rcases step_some R p v l hl with ho | ⟨hv,u,t,ht,hr,hlt⟩
    · refine ⟨hp.head v l ho, hp.last v l ho, hp.simple v l ho, hp.chain v l ho, ?_⟩
      intro u hu
      exact (mem_reached _ _).mp (reached_mono R p ((mem_reached _ _).mpr (hp.visited v l ho u hu)))
    · subst l
      have hvnot : v∉t := by
        intro hh
        have hhv := hp.visited u t ht v hh
        simp [hv] at hhv
      have htnon : t≠[] := by
        intro hnil
        have hh := hp.head u t ht
        simp [hnil] at hh
      refine ⟨rfl, ?_, (hp.simple u t ht).cons hvnot, ?_, ?_⟩
      · cases t with
        | nil => exact (htnon rfl).elim
        | cons w t => simpa only [List.getLast?_cons_cons] using hp.last u (w::t) ht
      · apply (hp.chain u t ht).cons
        intro w hw
        rw [hp.head u t ht] at hw
        simp only [Option.mem_some_iff] at hw
        subst w
        exact hr
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hwt
        · simp [hl]
        · exact (mem_reached _ _).mp (reached_mono R p
            ((mem_reached _ _).mpr (hp.visited u t ht w hwt)))
  exact ⟨fun v l h => (hpaths v l h).1, fun v l h => (hpaths v l h).2.1,
    fun v l h => (hpaths v l h).2.2.1, fun v l h => (hpaths v l h).2.2.2.1,
    fun v l h => (hpaths v l h).2.2.2.2⟩

lemma good_search (R : Fin n → Fin n → Prop) [DecidableRel R] (a : Fin n) (k : ℕ) :
    Good R a (search R a k) := by
  induction k with
  | zero => exact good_initial R a
  | succ k ih => exact good_step R a _ ih

lemma closed_step_eq (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (hc : Closed R (reached p)) : reached (step R p) = reached p := by
  ext v
  rw [step_reached]
  constructor
  · rintro (h | ⟨u,hu,hr⟩)
    · exact h
    · exact hc u hu v hr
  · exact Or.inl

lemma closed_step (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (hc : Closed R (reached p)) : Closed R (reached (step R p)) := by
  rw [closed_step_eq R p hc]
  exact hc

lemma card_increases (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (hc : ¬Closed R (reached p)) :
    (reached p).card < (reached (step R p)).card := by
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨reached_mono R p, ?_⟩
  intro heq
  apply hc
  intro u hu v hr
  rw [heq]
  exact (step_reached R p v).2 (Or.inr ⟨u, hu, hr⟩)

lemma closed_or_card (R : Fin n → Fin n → Prop) [DecidableRel R]
    (a : Fin n) (k : ℕ) :
    Closed R (reached (search R a k)) ∨ k+1 ≤ (reached (search R a k)).card := by
  induction k with
  | zero =>
    right
    apply card_pos.mpr
    refine ⟨a, ?_⟩
    simp [search,mem_reached,initial]
  | succ k ih =>
    by_cases hc : Closed R (reached (search R a k))
    · exact Or.inl (closed_step R _ hc)
    · have hh := ih.resolve_left hc
      have hlt := card_increases R _ hc
      right
      change k+1+1 ≤ (reached (step R (search R a k))).card
      omega

lemma search_closed (R : Fin n → Fin n → Prop) [DecidableRel R] (a : Fin n) :
    Closed R (reached (search R a n)) := by
  rcases closed_or_card R a n with h | h
  · exact h
  · have hc := card_le_univ (reached (search R a n))
    simp only [Fintype.card_fin] at hc
    omega

lemma source_reached (R : Fin n → Fin n → Prop) [DecidableRel R] (a : Fin n) (k : ℕ) :
    a ∈ reached (search R a k) := by
  induction k with
  | zero => simp [search,mem_reached,initial]
  | succ k ih => exact reached_mono R _ ih

lemma search_path (R : Fin n → Fin n → Prop) [DecidableRel R]
    (a z : Fin n) (p : List (Fin n)) (hp : search R a n z = some p) :
    p.head?=some z ∧ p.getLast?=some a ∧ p.Nodup ∧
      p.IsChain (fun v u => R u v) := by
  have h := good_search R a n
  exact ⟨h.head z p hp, h.last z p hp, h.simple z p hp, h.chain z p hp⟩

lemma search_no_path (R : Fin n → Fin n → Prop) [DecidableRel R]
    (a z : Fin n) (hp : search R a n z = none) :
    a∈reached (search R a n) ∧ z∉reached (search R a n) ∧
      Closed R (reached (search R a n)) := by
  exact ⟨source_reached R a n, by simp [mem_reached,hp], search_closed R a⟩

end BinaryMatching.ResidualSearch
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_UnitMincut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.UnitMincut
open Finset UnitFlow ResidualSearch
variable {n : ℕ}

def residual (c : Fin n → Fin n → ℕ) (b : Matrix (Fin n)) : Fin n → Fin n → Prop :=
  fun i j => b i j < c i j
instance residualDecidable (c : Fin n → Fin n → ℕ) (b : Matrix (Fin n)) :
    DecidableRel (residual c b) := fun _ _ => inferInstanceAs (Decidable (_ < (_ : ℤ)))

def augment (c : Fin n → Fin n → ℕ) (a z : Fin n) (b : Matrix (Fin n)) : Matrix (Fin n) :=
  match search (residual c b) a n z with
  | none => b
  | some p => fun i j => b i j + pathFlow p i j

def iterate (c : Fin n → Fin n → ℕ) (a z : Fin n) : ℕ → Matrix (Fin n)
  | 0 => fun _ _ => 0
  | k+1 => augment c a z (iterate c a z k)

def sourceCapacity (c : Fin n → Fin n → ℕ) (a : Fin n) : ℕ := ∑ j, c a j

def mincut (c : Fin n → Fin n → ℕ) (a z : Fin n) : Finset (Fin n) :=
  let b := iterate c a z (sourceCapacity c a)
  reached (search (residual c b) a n)

lemma augment_of_none (c : Fin n → Fin n → ℕ) (a z : Fin n) (b : Matrix (Fin n))
    (h : search (residual c b) a n z=none) : augment c a z b=b := by
  simp [augment,h]

lemma augment_of_some (c : Fin n → Fin n → ℕ) (a z : Fin n) (b : Matrix (Fin n))
    (p : List (Fin n)) (h : search (residual c b) a n z=some p) :
    augment c a z b = (fun i j => b i j + pathFlow p i j) := by
  simp [augment,h]

lemma augment_preserves (c : Fin n → Fin n → ℕ) (a z : Fin n) (b : Matrix (Fin n))
    (hb : Feasible c a z b) : Feasible c a z (augment c a z b) := by
  cases he : search (residual c b) a n z with
  | none => rwa [augment_of_none c a z b he]
  | some p =>
    rw [augment_of_some c a z b p he]
    obtain ⟨hhead,hlast,hnd,hchain⟩ := search_path (residual c b) a z p he
    exact augment_feasible hb p hnd hchain hhead hlast

lemma iterate_feasible (c : Fin n → Fin n → ℕ) (a z : Fin n) (k : ℕ) :
    Feasible c a z (iterate c a z k) := by
  induction k with
  | zero => exact feasible_zero c a z
  | succ k ih => exact augment_preserves c a z _ ih

lemma iterate_none_or_value (c : Fin n → Fin n → ℕ) (a z : Fin n) (haz : a≠z) (k : ℕ) :
    search (residual c (iterate c a z k)) a n z=none ∨
      divergence (iterate c a z k) a = k := by
  induction k with
  | zero => exact Or.inr (by simp [iterate,divergence])
  | succ k ih =>
    cases he : search (residual c (iterate c a z k)) a n z with
    | none =>
      left
      rwa [iterate,augment_of_none c a z _ he]
    | some p =>
      have hv := ih.resolve_left (by simp [he])
      right
      rw [iterate,augment_of_some c a z _ p he]
      obtain ⟨hhead,hlast,_,_⟩ := search_path (residual c (iterate c a z k)) a z p he
      rw [augment_value haz _ p hhead hlast,hv]
      simp

lemma final_no_path (c : Fin n → Fin n → ℕ) (a z : Fin n) (haz : a≠z) :
    search (residual c (iterate c a z (sourceCapacity c a))) a n z=none := by
  rcases iterate_none_or_value c a z haz (sourceCapacity c a) with h | h
  · exact h
  · cases he : search (residual c (iterate c a z (sourceCapacity c a))) a n z with
    | none => rfl
    | some p =>
      have hfeas := iterate_feasible c a z (sourceCapacity c a + 1)
      have hbound := source_bound hfeas
      rw [iterate,augment_of_some c a z _ p he] at hbound
      obtain ⟨hhead,hlast,_,_⟩ :=
        search_path (residual c (iterate c a z (sourceCapacity c a))) a z p he
      rw [augment_value haz _ p hhead hlast,h] at hbound
      have hc : (sourceCapacity c a : ℤ) = ∑ j, (c a j : ℤ) := by
        simp [sourceCapacity]
      rw [← hc] at hbound
      omega

theorem mincut_correct (c : Fin n → Fin n → ℕ) (a z : Fin n) (haz : a≠z) :
    a∈mincut c a z ∧ z∉mincut c a z ∧
      ∀ T : Finset (Fin n), a∈T → z∉T → cutCapacity c (mincut c a z) ≤ cutCapacity c T := by
  let b := iterate c a z (sourceCapacity c a)
  have hb : Feasible c a z b := iterate_feasible c a z _
  have hn : search (residual c b) a n z=none := final_no_path c a z haz
  obtain ⟨ha,hz,hclosed⟩ := search_no_path (residual c b) a z hn
  refine ⟨ha,hz,saturated_minimum hb _ ha hz ?_⟩
  intro i hi j hj
  apply le_antisymm (hb.capacity i j)
  by_contra hnot
  have hr : residual c b i j := lt_of_not_ge hnot
  exact hj (hclosed i hi j hr)

end BinaryMatching.UnitMincut
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_TerminalMincut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.TerminalMincut
open Finset UnitFlow UnitMincut
variable {n : ℕ}

def Separates (U S : Finset (Fin n)) : Prop :=
  ∃ a∈U, ∃ z∈U, a∈S ∧ z∉S

def pairCuts (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) : List (Finset (Fin n)) :=
  (((List.finRange n).product (List.finRange n)).filter
    (fun az => decide (az.1∈U ∧ az.2∈U ∧ az.1≠az.2))).map
    (fun az => mincut c az.1 az.2)

def terminalCut (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) : Finset (Fin n) :=
  ((pairCuts c U).argmin (cutCapacity c)).getD ∅

lemma mem_pairCuts (c : Fin n → Fin n → ℕ) (U S : Finset (Fin n)) :
    S∈pairCuts c U ↔ ∃ a∈U, ∃ z∈U, a≠z ∧ S=mincut c a z := by
  simp only [pairCuts,List.mem_map,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a,z⟩,⟨_,ha,hz,haz⟩,hS⟩
    exact ⟨a,ha,z,hz,haz,hS.symm⟩
  · rintro ⟨a,ha,z,hz,haz,hS⟩
    exact ⟨(a,z),⟨by simp,ha,hz,haz⟩,hS.symm⟩

lemma pairCuts_nonempty (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) (hU : 2≤U.card) :
    pairCuts c U ≠ [] := by
  obtain ⟨a,ha,z,hz,haz⟩ := Finset.one_lt_card.mp hU
  have hm := (mem_pairCuts c U (mincut c a z)).2 ⟨a,ha,z,hz,haz,rfl⟩
  intro hh
  simp [hh] at hm

lemma terminalCut_mem (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) (hU : 2≤U.card) :
    terminalCut c U∈(pairCuts c U).argmin (cutCapacity c) := by
  have hn := pairCuts_nonempty c U hU
  unfold terminalCut
  cases he : (pairCuts c U).argmin (cutCapacity c) with
  | none => exact (hn (List.argmin_eq_none.mp he)).elim
  | some S => simp

lemma terminalCut_correct (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) (hU : 2≤U.card) :
    Separates U (terminalCut c U) ∧
      ∀ T : Finset (Fin n), Separates U T → cutCapacity c (terminalCut c U) ≤ cutCapacity c T := by
  have hmem := terminalCut_mem c U hU
  obtain ⟨a,ha,z,hz,haz,heq⟩ := (mem_pairCuts c U _).1 (List.argmin_mem hmem)
  constructor
  · obtain ⟨hac,hzc,_⟩ := mincut_correct c a z haz
    exact ⟨a,ha,z,hz,heq.symm ▸ hac,heq.symm ▸ hzc⟩
  · intro T hT
    obtain ⟨u,hu,v,hv,huT,hvT⟩ := hT
    have huv : u≠v := by intro hh; subst v; exact hvT huT
    have hpair := (mem_pairCuts c U (mincut c u v)).2 ⟨u,hu,v,hv,huv,rfl⟩
    exact (List.le_of_mem_argmin hpair hmem).trans ((mincut_correct c u v huv).2.2 T huT hvT)

end BinaryMatching.TerminalMincut
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_OddCutParity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.OddCutParity
open Finset UnitFlow CutAlgebra TerminalMincut
variable {n : ℕ}

def OddSide (U S : Finset (Fin n)) : Prop := Odd (S∩U).card
instance oddSideDecidable (U S : Finset (Fin n)) : Decidable (OddSide U S) :=
  inferInstanceAs (Decidable (Odd _))

lemma terminal_partition (U A : Finset (Fin n)) :
    (A∩U).card + (Aᶜ∩U).card=U.card := by
  simpa only [sdiff_eq_inter_compl,inter_comm] using card_inter_add_card_sdiff U A

lemma even_other (U A : Finset (Fin n)) (hU : Even U.card) (hA : Even (A∩U).card) :
    Even (Aᶜ∩U).card := by
  have hh := terminal_partition U A
  rw [Nat.even_iff] at hU hA ⊢
  omega

lemma separate_cards (U A : Finset (Fin n)) (hA : Separates U A) :
    0<(A∩U).card ∧ 0<(Aᶜ∩U).card := by
  obtain ⟨a,ha,z,hz,haa,hza⟩ := hA
  exact ⟨card_pos.mpr ⟨a,mem_inter.mpr ⟨haa,ha⟩⟩,
    card_pos.mpr ⟨z,mem_inter.mpr ⟨mem_compl.mpr hza,hz⟩⟩⟩

def contractMap (A : Finset (Fin n)) (r : Fin n) (v : Fin n) : Fin n :=
  if v∈A then v else r

end BinaryMatching.OddCutParity
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_OddMincut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.OddMincut
open Finset UnitFlow UnitMincut TerminalMincut CutAlgebra OddCutParity
variable {n : ℕ}

def outside (A : Finset (Fin n)) : Option (Fin n) :=
  (List.finRange n).find? (fun v => decide (v∉A))

def cheaper (c : Fin n → Fin n → ℕ) (S T : Finset (Fin n)) : Finset (Fin n) :=
  if cutCapacity c S ≤ cutCapacity c T then S else T

def recurse : ℕ → (Fin n → Fin n → ℕ) → Finset (Fin n) → Finset (Fin n)
  | 0,_,_ => ∅
  | k+1,c,U =>
    let A := terminalCut c U
    if OddSide U A then A else
      match outside A, outside Aᶜ with
      | some r, some q =>
        cheaper c
          (lift (contractMap A r) (recurse k (push c (contractMap A r)) (A∩U)))
          (lift (contractMap Aᶜ q) (recurse k (push c (contractMap Aᶜ q)) (Aᶜ∩U)))
      | _,_ => ∅

def oddCut (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) : Finset (Fin n) :=
  recurse U.card c U

end BinaryMatching.OddMincut
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_BinaryAlgorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
open Finset
variable {n : ℕ}

abbrev Table (n : ℕ) (α : Type) := Vector (Vector α n) n

def tabulate {α : Type} (f : Fin n → Fin n → α) : Table n α :=
  Vector.ofFn (fun i => Vector.ofFn (f i))

def entry {α : Type} (a : Table n α) (e : Pair n) : α := a[e.val.1][e.val.2]

@[simp] theorem at_tabulate {α : Type} (f : Fin n → Fin n → α) (e : Pair n) :
    entry (tabulate f) e=f e.val.1 e.val.2 := by simp [entry,tabulate]

def toTable {α : Type} [Zero α] (f : Pair n → α) : Table n α :=
  tabulate (fun i j => if h : i < j then f ⟨(i,j),h⟩ else 0)

@[simp] theorem at_toTable {α : Type} [Zero α] (f : Pair n → α) (e : Pair n) :
    entry (toTable f) e=f e := by simp [at_tabulate,toTable,e.property]

def capacities (a : Table n ℤ) (i j : Fin n) : ℕ :=
  if i < j then (a[i][j]).toNat else if j < i then (a[j][i]).toNat else 0

def q (n : ℕ) : ℕ := Fintype.card (Pair n)
def K (n : ℕ) : ℕ := Nat.clog 2 (q n)
def B (G : Input) : ℕ := (G.records.map (fun e => Nat.log2 e.multiplicity)).foldl max 0
def L (G : Input) : ℕ := 100*(G.n+B G+1)^3
def A₀ (n : ℕ) : ℕ := 10*n^2
def M₀ (G : Input) : ℕ := q G.n*(K G.n+L G)*(2+A₀ G.n)
def D₀ (G : Input) : ℕ := q G.n*(K G.n+L G+M₀ G)^2

def beta (G : Input) (e : Pair G.n) : ℤ :=
  if multiplicity G e=0 then -(L G:ℤ) else (Nat.log2 (multiplicity G e):ℤ)

structure Piece where
  slope : ℤ
  constant : ℚ
  deriving Inhabited, DecidableEq

def Piece.eval (p : Piece) (t : ℚ) : ℚ := p.slope*t+p.constant

def pieces (k : ℕ) : List Piece :=
  (List.range k).map (fun j => ⟨(j:ℤ)-1,(2:ℚ)⁻¹^j⟩) ++ [⟨k,0⟩]

def selectedPiece (k : ℕ) (t : ℚ) : Piece :=
  ((pieces k).argmin (fun p => p.eval t)).getD ⟨k,0⟩

def psi (k : ℕ) (t : ℚ) : ℚ := (selectedPiece k t).eval t

def slope (k : ℕ) (t : ℚ) : ℤ := (selectedPiece k t).slope

structure Affine (n : ℕ) where
  coeff : Pair n → ℤ
  constant : ℤ

def Affine.eval (a : Affine n) (x : Pair n → ℚ) : ℚ :=
  (∑ e, (a.coeff e:ℚ)*x e)+a.constant

def zeroRow : Affine n := ⟨fun _ => 0,0⟩
def degreeRow (v : Fin n) (positive : Bool) : Affine n :=
  ⟨fun e => if e.val.1=v ∨ e.val.2=v then (if positive then 1 else -1) else 0,
    if positive then -1 else 1⟩
def cutRow (S : Finset (Fin n)) : Affine n :=
  ⟨fun e => if (e.val.1∈S ∧ e.val.2∉S) ∨ (e.val.2∈S ∧ e.val.1∉S) then -1 else 0,1⟩

def activeRows (a : Table n ℤ) : List (Affine n) :=
  zeroRow :: ((List.finRange n).flatMap (fun v => [degreeRow v true,degreeRow v false])) ++
    [cutRow (OddMincut.oddCut (capacities a) univ)]

def coordinates (D : ℕ) (a : Table n ℤ) (e : Pair n) : ℚ := entry a e/(D:ℚ)

def activeRow (D : ℕ) (a : Table n ℤ) : Affine n :=
  ((activeRows a).argmax (fun r => r.eval (coordinates D a))).getD zeroRow

def trialValue (G : Input) (a : Table G.n ℤ) (r : Affine G.n) : ℚ :=
  (∑ e, (psi (K G.n) (coordinates (D₀ G) a e)+(beta G e:ℚ)*coordinates (D₀ G) a e)) -
    (M₀ G:ℚ)*r.eval (coordinates (D₀ G) a)

def gradient (G : Input) (a : Table G.n ℤ) (r : Affine G.n) (e : Pair G.n) : ℤ :=
  slope (K G.n) (coordinates (D₀ G) a e)+beta G e-(M₀ G:ℤ)*r.coeff e

def update (G : Input) (a : Table G.n ℤ) (r : Affine G.n) : Table G.n ℤ :=
  toTable (fun e => min (D₀ G:ℤ) (max 0 (entry a e+gradient G a r e)))

structure State (n : ℕ) where
  numerators : Table n ℤ
  best : Option ℚ

def step (G : Input) (s : State G.n) : State G.n :=
  let r := activeRow (D₀ G) s.numerators
  let value := trialValue G s.numerators r
  ⟨update G s.numerators r, some (s.best.elim value (max value))⟩

def initial (n : ℕ) : State n := ⟨tabulate (fun _ _ => 0),none⟩

def iterate (G : Input) : ℕ → State G.n
  | 0 => initial G.n
  | t+1 => step G (iterate G t)

def R (G : Input) : ℤ := ⌊((iterate G (q G.n*D₀ G)).best).getD 0⌋

def estimate (G : Input) : ℕ :=
  let r := R G
  if r < -10*(G.n:ℤ) then 0 else 2^(r-5*(G.n:ℤ)).toNat

def covered (G : Input) : Finset ℕ :=
  ((G.records.filter (fun e => 0<e.multiplicity)).flatMap (fun e => [e.left,e.right])).toFinset

def rawMultiplicity (G : Input) (i j : ℕ) : ℕ :=
  ((G.records.find? (fun r => r.left=i && r.right=j)).map Record.multiplicity).getD 0

end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_DenseOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.DenseOracle
open Finset UnitFlow CutAlgebra OddCutParity
variable {n : ℕ}

abbrev Matrix (n : ℕ) (α : Type) := Vector (Vector α n) n

def make {α : Type} (f : Fin n → Fin n → α) : Matrix n α :=
  Vector.ofFn (fun i => Vector.ofFn (f i))

def view {α : Type} (a : Matrix n α) : Fin n → Fin n → α := fun i j => a[i][j]

@[simp] lemma view_make {α : Type} (f : Fin n → Fin n → α) : view (make f)=f := by
  funext i j; simp [view,make]

abbrev Paths (n : ℕ) := Vector (Option (List (Fin n))) n

def pathView (p : Paths n) : ResidualSearch.Table n := fun v => p[v]

def pathInitial (a : Fin n) : Paths n := Vector.ofFn (ResidualSearch.initial a)

def pathStep (c : Matrix n ℕ) (b : Matrix n ℤ) (p : Paths n) : Paths n :=
  Vector.ofFn (ResidualSearch.step (UnitMincut.residual (view c) (view b)) (pathView p))

def search (c : Matrix n ℕ) (b : Matrix n ℤ) (a : Fin n) : ℕ → Paths n
  | 0 => pathInitial a
  | k+1 => pathStep c b (search c b a k)

lemma pathView_ofFn (p : ResidualSearch.Table n) : pathView (Vector.ofFn p)=p := by
  funext v; simp [pathView]

lemma search_view (c : Matrix n ℕ) (b : Matrix n ℤ) (a : Fin n) (k : ℕ) :
    pathView (search c b a k)=ResidualSearch.search (UnitMincut.residual (view c) (view b)) a k := by
  induction k with
  | zero => exact pathView_ofFn _
  | succ k ih => simp only [search,pathStep,pathView_ofFn,ih,ResidualSearch.search]

def augment (c : Matrix n ℕ) (a z : Fin n) (b : Matrix n ℤ) : Matrix n ℤ :=
  match (search c b a n)[z] with
  | none => b
  | some p => make (fun i j => view b i j+pathFlow p i j)

def iterate (c : Matrix n ℕ) (a z : Fin n) : ℕ → Matrix n ℤ
  | 0 => make (fun _ _ => 0)
  | k+1 => augment c a z (iterate c a z k)

lemma augment_view (c : Matrix n ℕ) (a z : Fin n) (b : Matrix n ℤ) :
    view (augment c a z b)=UnitMincut.augment (view c) a z (view b) := by
  have hs := congrFun (search_view c b a n) z
  change (search c b a n)[z]=_ at hs
  simp only [augment,hs,UnitMincut.augment]
  cases h : ResidualSearch.search (UnitMincut.residual (view c) (view b)) a n z <;>
    simp only [view_make]

lemma iterate_view (c : Matrix n ℕ) (a z : Fin n) (k : ℕ) :
    view (iterate c a z k)=UnitMincut.iterate (view c) a z k := by
  induction k with
  | zero => exact view_make _
  | succ k ih => simp only [iterate,augment_view,ih,UnitMincut.iterate]

def mincut (c : Matrix n ℕ) (a z : Fin n) : Finset (Fin n) :=
  let b := iterate c a z (UnitMincut.sourceCapacity (view c) a)
  ResidualSearch.reached (pathView (search c b a n))

lemma mincut_eq (c : Matrix n ℕ) (a z : Fin n) : mincut c a z=UnitMincut.mincut (view c) a z := by
  unfold mincut UnitMincut.mincut
  dsimp only
  rw [search_view]
  have h := iterate_view c a z (UnitMincut.sourceCapacity (view c) a)
  rw [h]

def terminalCut (c : Matrix n ℕ) (U : Finset (Fin n)) : Finset (Fin n) :=
  let cuts := (((List.finRange n).product (List.finRange n)).filter
    (fun az => decide (az.1∈U ∧ az.2∈U ∧ az.1≠az.2))).map
    (fun az => mincut c az.1 az.2)
  ((cuts.argmin (cutCapacity (view c))).getD ∅)

lemma terminalCut_eq (c : Matrix n ℕ) (U : Finset (Fin n)) :
    terminalCut c U=TerminalMincut.terminalCut (view c) U := by
  simp only [terminalCut,mincut_eq,TerminalMincut.terminalCut,TerminalMincut.pairCuts]

def contract (c : Matrix n ℕ) (f : Fin n → Fin n) : Matrix n ℕ := make (push (view c) f)

@[simp] lemma contract_view (c : Matrix n ℕ) (f : Fin n → Fin n) :
    view (contract c f)=push (view c) f := view_make _

def recurse : ℕ → Matrix n ℕ → Finset (Fin n) → Finset (Fin n)
  | 0,_,_ => ∅
  | k+1,c,U =>
    let A := terminalCut c U
    if OddSide U A then A else
      match OddMincut.outside A, OddMincut.outside Aᶜ with
      | some r,some q =>
        let f := contractMap A r
        let g := contractMap Aᶜ q
        let X := recurse k (contract c f) (A∩U)
        let Y := recurse k (contract c g) (Aᶜ∩U)
        OddMincut.cheaper (view c) (lift f X) (lift g Y)
      | _,_ => ∅

lemma recurse_eq (k : ℕ) (c : Matrix n ℕ) (U : Finset (Fin n)) :
    recurse k c U=OddMincut.recurse k (view c) U := by
  induction k generalizing c U with
  | zero => rfl
  | succ k ih =>
    simp only [recurse,terminalCut_eq,OddMincut.recurse]
    split
    · rfl
    · cases h₁ : OddMincut.outside (TerminalMincut.terminalCut (view c) U) <;>
        cases h₂ : OddMincut.outside (TerminalMincut.terminalCut (view c) U)ᶜ <;>
        simp only [ih,contract_view]

def oddCut (c : Matrix n ℕ) (U : Finset (Fin n)) : Finset (Fin n) := recurse U.card c U

lemma oddCut_eq (c : Matrix n ℕ) (U : Finset (Fin n)) :
    oddCut c U=OddMincut.oddCut (view c) U := recurse_eq _ _ _

end BinaryMatching.DenseOracle
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_ParamRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

@[fun_prop] theorem mapWith [Inhabited α] [Inhabited β]
    (l : α → List β) (f : α×β → γ) (hl : Poly l) (hf : Poly f) :
    Poly (fun a => (l a).map (fun b => f (a,b))) :=
  comp _ (fun a => (a,l a)) (listMapParam f hf) (by fun_prop)

@[fun_prop] theorem flatMapWith [Inhabited α] [Inhabited β]
    (l : α → List β) (f : α×β → List γ) (hl : Poly l) (hf : Poly f) :
    Poly (fun a => (l a).flatMap (fun b => f (a,b))) := by
  have h : Poly (fun a => ((l a).map (fun b => f (a,b))).flatten) :=
    comp _ _ (listFlatten (α := γ)) (mapWith l f hl hf)
  exact h.congr (fun a => rfl)

@[fun_prop] theorem listHeadOption : Poly (List.head? : List α → Option α) := by
  exact (listCases none (fun z : α×List α => Option.some z.1) (by fun_prop)).congr
    (fun l => by cases l <;> rfl)

@[fun_prop] theorem listFilterParam [Inhabited α] [Inhabited β]
    (f : α×β → Bool) (hf : Poly f) :
    Poly (fun z : α×List β => z.2.filter (fun b => f (z.1,b))) := by
  have h : Poly (fun z : α×List β => ((z.2.map fun b => (z.1,b)).filter f).map Prod.snd) := by
    exact comp _ _ (listMap Prod.snd (by fun_prop))
      (comp _ _ (listFilter f hf) (listMapParam (fun z : α×β => z) identity))
  exact h.congr (fun z => by simp [List.filter_map,Function.comp_def])

@[fun_prop] theorem filterWith [Inhabited α] [Inhabited β]
    (l : α → List β) (f : α×β → Bool) (hl : Poly l) (hf : Poly f) :
    Poly (fun a => (l a).filter (fun b => f (a,b))) :=
  comp _ (fun a => (a,l a)) (listFilterParam f hf) (by fun_prop)

@[fun_prop] theorem listFind [Inhabited α] (p : α → Bool) (hp : Poly p) :
    Poly (List.find? p) := by
  have h : Poly (fun l : List α => (l.filter p).head?) := by fun_prop
  exact h.congr (fun l => by
    induction l with
    | nil => rfl
    | cons a l ih => cases h : p a <;> simp [h,ih])

@[fun_prop] theorem listFindParam [Inhabited α] [Inhabited β]
    (p : α×β → Bool) (hp : Poly p) :
    Poly (fun z : α×List β => z.2.find? (fun b => p (z.1,b))) := by
  have h : Poly (fun z : α×List β => (z.2.filter (fun b => p (z.1,b))).head?) :=
    comp _ _ listHeadOption (listFilterParam p hp)
  exact h.congr (fun z => by
    have hh : ∀ l : List β,(l.filter (fun b => p (z.1,b))).head?=l.find? (fun b => p (z.1,b)) := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih => cases h : p (z.1,a) <;> simp [h,ih]
    exact hh _)

@[fun_prop] theorem findWith [Inhabited α] [Inhabited β]
    (l : α → List β) (p : α×β → Bool) (hl : Poly l) (hp : Poly p) :
    Poly (fun a => (l a).find? (fun b => p (a,b))) :=
  comp _ (fun a => (a,l a)) (listFindParam p hp) (by fun_prop)

end Poly
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw
open Finset
abbrev Matrix (α : Type) := List (List α)
abbrev Cut := List Bool
abbrev Paths := List (Option (List ℕ))

def nth {α : Type} [Inhabited α] (l : List α) (i : ℕ) : α := l[i]?.getD default
def get {α : Type} [Inhabited α] (a : Matrix α) (i j : ℕ) : α := nth (nth a i) j
def tab {α : Type} (n : ℕ) (f : ℕ → α) : List α := (List.range n).map f
def matrix {α : Type} (n : ℕ) (f : ℕ → ℕ → α) : Matrix α := tab n (fun i => tab n (f i))
def mem (S : Cut) (i : ℕ) : Bool := nth S i
def empty (n : ℕ) : Cut := List.replicate n false
def full (n : ℕ) : Cut := List.replicate n true
def inter (n : ℕ) (S T : Cut) : Cut := tab n (fun i => mem S i && mem T i)
def compl (n : ℕ) (S : Cut) : Cut := tab n (fun i => !mem S i)
def cardinal (S : Cut) : ℕ := (S.filter id).length

def vectorRep {n : ℕ} {α : Type} (f : Fin n → α) : List α := List.ofFn f
def matrixRep {n : ℕ} {α : Type} (f : Fin n → Fin n → α) : Matrix α :=
  vectorRep (fun i => vectorRep (f i))
def cutRep {n : ℕ} (S : Finset (Fin n)) : Cut := vectorRep (fun i => decide (i∈S))
def pathRep {n : ℕ} (p : ResidualSearch.Table n) : Paths :=
  vectorRep (fun i => (p i).map (List.map Fin.val))

@[simp] lemma at_rep {n : ℕ} {α : Type} [Inhabited α] (f : Fin n → α) (i : Fin n) :
    nth (vectorRep f) i.val=f i := by simp [nth,vectorRep,i.isLt]

@[simp] lemma get_rep {n : ℕ} {α : Type} [Inhabited α] (f : Fin n → Fin n → α) (i j : Fin n) :
    get (matrixRep f) i.val j.val=f i j := by simp [get,matrixRep]

@[simp] lemma mem_rep {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    mem (cutRep S) i.val=decide (i∈S) := by simp [mem,cutRep]

end BinaryMatching.Raw
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_ArgRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma argAux_code {α : Type} [Coding α] (r : α → α → Prop) [DecidableRel r]
    (z : Option α×α) :
    (encode (List.argAux r z.1 z.2)).length≤(encode z.1).length+2*(encode z.2).length+1 := by
  rcases z with ⟨o,a⟩
  cases o with
  | none => simp [List.argAux,code_option_none,code_option_some]
  | some b =>
    simp only [List.argAux]
    split_ifs <;> simp only [code_option_some] <;> omega

namespace Poly
variable {α β : Type} [Coding α] [Coding β]

@[fun_prop] theorem argAux [Inhabited α] (r : α → α → Prop) [DecidableRel r]
    (hr : Poly (fun z : α×α => decide (r z.1 z.2))) :
    Poly (fun z : Option α×α => List.argAux r z.1 z.2) := by
  have h : Poly (fun z : Option α×α => if z.1.isSome then
      if decide (r z.2 (z.1.getD default)) then Option.some z.2 else z.1 else Option.some z.2) := by
    apply cond
    · fun_prop
    · fun_prop
    · apply cond
      · exact comp _ (fun z : Option α×α => (z.2,z.1.getD default)) hr (by fun_prop)
      · fun_prop
      · fun_prop
  exact h.congr (fun z => by cases z.1 <;> simp [List.argAux])

theorem listArgAux [Inhabited α] (r : α → α → Prop) [DecidableRel r]
    (hr : Poly (fun z : α×α => decide (r z.1 z.2))) :
    Poly (fun l : List α => l.foldl (List.argAux r) none) := by
  have hf := listFoldAdd (fun z : Option α×α => List.argAux r z.1 z.2)
    (argAux r hr) 1 (by intro z; simpa only [one_mul,Nat.add_assoc] using argAux_code r z)
  exact comp _ (fun l : List α => (l,(none:Option α))) hf (by fun_prop)

@[fun_prop] theorem listArgmin [Inhabited α] [Preorder β] [DecidableLT β]
    (hb : Poly (fun z : β×β => decide (z.1<z.2))) (f : α → β) (hf : Poly f) :
    Poly (List.argmin f) := by
  apply listArgAux (fun a b => f a<f b)
  exact comp _ (fun z : α×α => (f z.1,f z.2)) hb (by fun_prop)

@[fun_prop] theorem listArgmax [Inhabited α] [Preorder β] [DecidableLT β]
    (hb : Poly (fun z : β×β => decide (z.1<z.2))) (f : α → β) (hf : Poly f) :
    Poly (List.argmax f) := by
  apply listArgAux (fun a b => f b<f a)
  exact comp _ (fun z : α×α => (f z.2,f z.1)) hb (by fun_prop)

end Poly

lemma argmin_map_exact {α β γ : Type} [Preorder γ] [DecidableLT γ]
    (l : List α) (f : α → β) (g : β → γ) :
    (l.map f).argmin g=(l.argmin (g ∘ f)).map f := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    simp only [List.map_append,List.map_singleton,List.argmin_concat,ih]
    cases h : l.argmin (g ∘ f) with
    | none => rfl
    | some b => simp only [Option.map_some,Function.comp_apply]; split_ifs <;> rfl

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

@[fun_prop] theorem listArgminParam [Inhabited α] [Inhabited γ]
    [Preorder β] [DecidableLT β]
    (hb : Poly (fun z : β×β => decide (z.1<z.2))) (f : γ×α → β) (hf : Poly f) :
    Poly (fun z : γ×List α => z.2.argmin (fun a => f (z.1,a))) := by
  have hm : Poly (fun z : γ×List α => z.2.map (fun a => (z.1,a))) :=
    listMapParam (fun z : γ×α => z) identity
  have h : Poly (fun z : γ×List α => ((z.2.map fun a => (z.1,a)).argmin f).map Prod.snd) := by
    apply comp _ _ (optionMap Prod.snd (by fun_prop))
    exact comp _ _ (listArgmin hb f hf) hm
  exact h.congr (fun z => by
    rw [argmin_map_exact]
    simp [Option.map_map,Function.comp_def])

@[fun_prop] theorem listArgmaxParam [Inhabited α] [Inhabited γ]
    [Preorder β] [DecidableLT β]
    (hb : Poly (fun z : β×β => decide (z.1<z.2))) (f : γ×α → β) (hf : Poly f) :
    Poly (fun z : γ×List α => z.2.argmax (fun a => f (z.1,a))) := by
  let : Coding βᵒᵈ := inferInstanceAs (Coding β)
  apply @listArgminParam α βᵒᵈ γ _ _ _ _ _ _ _ _ f hf
  exact comp (fun z : β×β => decide (z.1<z.2)) (fun z : β×β => (z.2,z.1)) hb (by fun_prop)

end Poly
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_DivisionRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Poly

@[fun_prop] theorem intDivNat : Poly (fun z : ℤ×ℕ => z.1/(z.2:ℤ)) := by
  have h : Poly (fun z : ℤ×ℕ => if decide (z.2=0) then (0:ℤ) else
      if decide (z.1<0) then -(((z.1.natAbs-1)/z.2+1:ℕ):ℤ)
      else ((z.1.natAbs/z.2:ℕ):ℤ)) := by fun_prop
  exact h.congr (fun z => by
    by_cases hd : z.2=0
    · simp [hd]
    · have hp : (0:ℤ)<z.2 := by exact_mod_cast (Nat.pos_of_ne_zero hd)
      simp only [hd,decide_false,Bool.false_eq_true,ite_false,decide_eq_true_eq]
      by_cases ha : z.1<0
      · rw [ite_eq_left ha]
        change -(((z.1.natAbs-1)/z.2+1:ℕ):ℤ)=Int.ediv z.1 (z.2:ℤ)
        rw [Int.ediv_of_neg_of_pos ha hp]
        have ha' : 0<z.1.natAbs := Int.natAbs_pos.mpr (ne_of_lt ha)
        have habs : (z.1.natAbs:ℤ) = -z.1 := by omega
        rw [Nat.cast_add,Nat.cast_one,Int.natCast_ediv,Nat.cast_sub (by omega : 1≤z.1.natAbs),Nat.cast_one,habs]
      · rw [ite_eq_right ha,Int.natCast_ediv,Int.natAbs_of_nonneg (le_of_not_gt ha)])

end Poly

end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode.Poly
open BinaryMatching.Raw
variable {α β : Type} [Coding α] [Coding β]

@[fun_prop] theorem rawNth [Inhabited β] (l : α → List β) (i : α → ℕ)
    (hl : Poly l) (hi : Poly i) : Poly (fun a => nth (l a) (i a)) :=
  comp _ _ (listGetD default) (pair l i hl hi)
@[fun_prop] theorem rawGet [Inhabited β] (m : α → Matrix β) (i j : α → ℕ)
    (hm : Poly m) (hi : Poly i) (hj : Poly j) : Poly (fun a => get (m a) (i a) (j a)) := by
  unfold Raw.get
  fun_prop
@[fun_prop] theorem rawMem (S : α → Cut) (i : α → ℕ) (hS : Poly S) (hi : Poly i) :
    Poly (fun a => mem (S a) (i a)) := by unfold mem; fun_prop
@[fun_prop] theorem rawTab [Inhabited α] (n : α → ℕ) (f : α×ℕ → β)
    (hn : Poly n) (hf : Poly f) : Poly (fun a => tab (n a) (fun i => f (a,i))) := by
  unfold tab
  apply mapWith _ _ (by fun_prop) hf
@[fun_prop] theorem rawMatrix [Inhabited α] (n : α → ℕ) (f : (α×ℕ)×ℕ → β)
    (hn : Poly n) (hf : Poly f) : Poly (fun a => matrix (n a) (fun i j => f ((a,i),j))) := by
  unfold matrix
  exact rawTab n (fun z => tab (n z.1) (fun j => f (z,j))) hn
    (rawTab (fun z : α×ℕ => n z.1) f (by fun_prop) hf)

@[fun_prop] theorem rawEmpty : Poly empty := by unfold empty; fun_prop
@[fun_prop] theorem rawFull : Poly full := by unfold full; fun_prop
@[fun_prop] theorem rawInter : Poly (fun z : ℕ×(Cut×Cut) => inter z.1 z.2.1 z.2.2) := by
  unfold inter
  exact rawTab Prod.fst (fun z : (ℕ×(Cut×Cut))×ℕ => mem z.1.2.1 z.2 && mem z.1.2.2 z.2)
    (by fun_prop) (by fun_prop)
@[fun_prop] theorem rawCompl : Poly (fun z : ℕ×Cut => compl z.1 z.2) := by
  unfold Raw.compl
  exact rawTab Prod.fst (fun z : (ℕ×Cut)×ℕ => !mem z.1.2 z.2) (by fun_prop) (by fun_prop)
@[fun_prop] theorem rawCardinal : Poly cardinal := by
  unfold cardinal
  fun_prop

@[fun_prop] theorem uncurriedOptionMap [Inhabited α] [Inhabited β]
    (f : α×β → β) (hf : Poly f) :
    Poly (fun z : α×Option β => z.2.map (fun b => f (z.1,b))) := by
  have h : Poly (fun z : α×Option β => if z.2.isSome then
      Option.some (f (z.1,z.2.getD default)) else none) := by fun_prop
  exact h.congr (fun z => by cases z.2 <;> rfl)

end BinaryMatching.StackCode.Poly
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open BinaryMatching.Raw

@[simp] lemma code_bool_length (b : Bool) : (encode b).length=1 := rfl
@[simp] lemma code_nat_length (n : ℕ) : (encode n).length=n := unary_length n
@[simp] lemma code_int_length (z : ℤ) : (encode z).length=z.natAbs+3 := by
  simp only [encode_int,encode_prod,pairBits_length,intParts,code_bool_length,code_nat_length]
  omega
@[simp] lemma code_pair_length {α β : Type} [Coding α] [Coding β] (z : α×β) :
    (encode z).length=2*(encode z.1).length+(encode z.2).length+1 := pairBits_length _ _

lemma pair_left_le {α β : Type} [Coding α] [Coding β] (z : α×β) :
    (encode z.1).length≤(encode z).length := by simp only [code_pair_length]; omega
lemma pair_right_le {α β : Type} [Coding α] [Coding β] (z : α×β) :
    (encode z.2).length≤(encode z).length := by simp only [code_pair_length]; omega

lemma nth_code_bound {α : Type} [Coding α] [Inhabited α] (l : List α) (i M : ℕ)
    (hd : (encode (default:α)).length≤M) (h : ∀ a∈l,(encode a).length≤M) :
    (encode (nth l i)).length≤M := by
  unfold nth
  cases hi : l[i]? with
  | none => exact hd
  | some a =>
    exact h a (List.mem_of_getElem? hi)

lemma cut_code_length (S : Cut) : (encode S).length=3*S.length := by
  induction S with
  | nil => rfl
  | cons b S ih => simp only [code_cons,pairBits_length,code_bool_length,ih,List.length_cons]; omega

lemma option_prepend_bound (v : ℕ) (p : Option (List ℕ)) :
    (encode (p.map (v::·))).length≤(encode p).length+4*v+2 := by
  cases p with
  | none => simp only [Option.map_none,code_option_none,List.length_nil]; omega
  | some l => simp only [Option.map_some,code_option_some,code_cons,pairBits_length,code_nat_length]; omega

end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawBitsBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

structure Bits where
  data : List Bool
  deriving Inhabited
instance instCodingBits : Coding Bits := ⟨Bits.data⟩
@[simp] lemma encode_Bits (b : Bits) : encode b=b.data := rfl

namespace Routine
noncomputable def headBool : Routine (id : List Bool → List Bool) (fun b : Bool => [b])
    (fun l => l.headD false) where
  scratch := 0
  block := Block.cases 0 (Block.push 0 false)
    ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 true))
  time := 2*X+3
  correct l := by
    let s : Store 1 := Function.update (fun _ => []) 0 l
    have hfalse := Block.seq_runs _ _ (Block.clear_runs (0:Fin 1) s)
      (Block.push_runs (0:Fin 1) false (Function.update s 0 []))
    have htrue := Block.seq_runs _ _ (Block.clear_runs (0:Fin 1) s)
      (Block.push_runs (0:Fin 1) true (Function.update s 0 []))
    cases l with
    | nil =>
      have hh := Block.cases_runs_empty (0:Fin 1) (Block.push 0 false)
        ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 true))
        (by simp [s]) (Block.push_runs (0:Fin 1) false s)
      exact ⟨2,by simp,by simpa [s,Function.update_idem] using hh⟩
    | cons b l =>
      cases b with
      | false =>
        have hh := Block.cases_runs_false (0:Fin 1) (Block.push 0 false)
          ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 true))
          (by simp [s]) hfalse
        exact ⟨2*(l.length+1)+3,by simp,by simpa [s,Function.update_idem,Nat.add_assoc] using hh⟩
      | true =>
        have hh := Block.cases_runs_true (0:Fin 1) (Block.push 0 false)
          ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 true))
          (by simp [s]) htrue
        exact ⟨2*(l.length+1)+3,by simp,by simpa [s,Function.update_idem,Nat.add_assoc] using hh⟩
end Routine

namespace Poly
@[fun_prop] theorem bitsTail : Poly (fun b : Bits => Bits.mk b.data.tail) :=
  ⟨Routine.tail.reindex encode encode _ Bits.data (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem bitsEmpty : Poly (fun b : Bits => b.data.isEmpty) :=
  ⟨Routine.isEmpty.reindex encode encode _ Bits.data (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem bitsHead : Poly (fun b : Bits => b.data.headD false) :=
  ⟨Routine.headBool.reindex encode encode _ Bits.data (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem bitsLength : Poly (fun b : Bits => b.data.length) := Poly.codeLength
@[fun_prop] theorem bitsAppend : Poly (fun z : Bits×Bits => Bits.mk (z.1.data++z.2.data)) :=
  ⟨Routine.append.reindex encode encode _ (fun z : Bits×Bits => (z.1.data,z.2.data)) (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem bitsSingleton : Poly (fun b : Bool => Bits.mk [b]) :=
  ⟨(Routine.identity (fun b : Bool => [b])).reindex encode encode _ id (fun _ => rfl) (fun _ => rfl)⟩
end Poly

def encodeBitsStep (z : Bits×List Bool) : Bits×List Bool :=
  if z.1.data.isEmpty then z else (⟨z.1.data.tail⟩,z.2++[z.1.data.headD false])
lemma encodeBitsStep_iterate (j : ℕ) (b : Bits) (acc : List Bool) :
    encodeBitsStep^[j] (b,acc)=(⟨b.data.drop j⟩,acc++b.data.take j) := by
  induction j generalizing b acc with
  | zero => simp
  | succ j ih =>
    cases b with | mk l =>
    cases l with
    | nil => simp [Function.iterate_succ_apply,encodeBitsStep,ih]
    | cons a l => simp [Function.iterate_succ_apply,encodeBitsStep,ih,List.append_assoc]

namespace Poly
@[fun_prop] theorem bitsDecode : Poly (fun b : Bits => b.data) := by
  have ht : Poly (fun z : Bits×List Bool => Bits.mk z.1.data.tail) :=
    Poly.comp _ Prod.fst bitsTail (by fun_prop)
  have hh : Poly (fun z : Bits×List Bool => z.1.data.headD false) :=
    Poly.comp _ Prod.fst bitsHead (by fun_prop)
  have hs : Poly encodeBitsStep := by
    exact Poly.cond _ _ _ (Poly.comp _ Prod.fst bitsEmpty (by fun_prop))
      (Poly.pair _ _ ht (by fun_prop)) Poly.identity
  have hi := Poly.boundedIterate encodeBitsStep hs (5*X+1) (by
    intro z j hj
    rw [show z.2=(z.2.1,z.2.2) from rfl,encodeBitsStep_iterate]
    simp only [code_pair_length,encode_Bits,code_append,List.length_append,cut_code_length,
      List.length_drop,List.length_take,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,code_nat_length]
    omega)
  have h := Poly.second _ (Poly.comp _ (fun b : Bits => (b.data.length,(b,([]:List Bool)))) hi (by fun_prop))
  exact h.congr (fun b => by rw [encodeBitsStep_iterate]; simp)

lemma bits_fold (l acc : List Bool) :
    l.foldl (fun b a => Bits.mk (b.data++[a])) (Bits.mk acc)=Bits.mk (acc++l) := by
  induction l generalizing acc with
  | nil => simp
  | cons b l ih => simp [ih,List.append_assoc]

@[fun_prop] theorem bitsEncode : Poly (fun l : List Bool => Bits.mk l) := by
  have hf : Poly (fun z : Bits×Bool => Bits.mk (z.1.data++[z.2])) := by
    exact Poly.comp _ (fun z : Bits×Bool => (z.1,Bits.mk [z.2])) bitsAppend (Poly.pair _ _ (by fun_prop) (Poly.comp _ Prod.snd bitsSingleton (by fun_prop)))
  have hfold := Poly.listFold false _ hf X (by
    intro z k
    rw [show z.2=Bits.mk z.2.data from rfl,bits_fold]
    have hl := list_length_le_code z.1
    simp only [encode_Bits,List.length_append,List.length_take,eval_X,code_pair_length]
    omega)
  have h := Poly.comp _ (fun l : List Bool => (l,Bits.mk [])) hfold (by fun_prop)
  exact h.congr (fun l => by rw [bits_fold]; rfl)
end Poly
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_ParserSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Poly
variable {α : Type} [Coding α] [Inhabited α]
@[fun_prop] theorem listReverse : Poly (List.reverse : List α → List α) := by
  have hf := listFoldAdd (fun z : List α×α => z.2::z.1) (by fun_prop) 1 (by
    intro z
    simp only [code_cons,pairBits_length]
    omega)
  have hh := comp _ (fun l : List α => (l,([]:List α))) hf (by fun_prop)
  exact hh.congr (fun l => by simp)
@[fun_prop] theorem listTake : Poly (fun z : ℕ×List α => z.2.take z.1) := by
  have hh : Poly (fun z : ℕ×List α => (z.2.reverse.drop (z.2.length-z.1)).reverse) := by fun_prop
  exact hh.congr (fun z => by rw [←List.reverse_take,List.reverse_reverse])
end Poly
end BinaryMatching.StackCode

namespace BinaryMatching.Parse
open StackCode Polynomial

def zeroPrefix (l : List Bool) : ℕ := l.foldr (fun b k => if b then 0 else k+1) 0
lemma zeroPrefix_delimited (k : ℕ) (l : List Bool) : zeroPrefix (List.replicate k false++true::l)=k := by
  induction k with
  | zero => simp [zeroPrefix]
  | succ k ih =>
    change zeroPrefix (false::(List.replicate k false++true::l))=k+1
    change zeroPrefix (List.replicate k false++true::l)+1=k+1
    rw [ih]

@[fun_prop] theorem zeroPrefix_poly : Poly zeroPrefix := by
  have hf := Poly.listFoldAdd (fun z : ℕ×Bool => if z.2 then 0 else z.1+1) (by fun_prop) 1 (by
    intro z
    cases z.2 <;> simp)
  have hh := Poly.comp _ (fun l : List Bool => (l.reverse,0)) hf (by fun_prop)
  exact hh.congr (fun _ => by simp [zeroPrefix])

def numeral (l : List Bool) : List Bool×List Bool :=
  let k := zeroPrefix l
  ((l.drop (k+1)).take k,l.drop (2*k+1))
lemma numeral_encode (n : ℕ) (l : List Bool) : numeral (encodeNat n++l)=(n.bits,l) := by
  unfold numeral encodeNat
  rw [List.append_assoc,List.cons_append,zeroPrefix_delimited]
  simp [List.drop_append,List.drop_replicate]
  rw [show n.bits.length-(2*n.bits.length+1)=0 by omega,
    show 2*n.bits.length+1-n.bits.length=n.bits.length+1 by omega]
  simp
lemma numeral_lengths (l : List Bool) : (numeral l).1.length≤l.length ∧ (numeral l).2.length≤l.length := by
  simp only [numeral,List.length_take,List.length_drop]
  omega
@[fun_prop] theorem numeral_poly : Poly numeral := by unfold numeral; fun_prop

def value (l : List Bool) : ℕ := l.foldr Nat.bit 0
lemma value_bits (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => simp [value]
  | bit b n h ih => simpa only [Nat.bits_append_bit n b h,value,List.foldr_cons] using congrArg (Nat.bit b) ih

def capStep (z : (ℕ×ℕ)×Bool) : ℕ×ℕ := (z.1.1,min z.1.1 (2*z.1.2+if z.2 then 1 else 0))
lemma capStep_fold (b : ℕ) (l : List Bool) (a : ℕ) :
    l.foldr (fun c z => capStep (z,c)) (b,min b a)=(b,min b (l.foldr Nat.bit a)) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [List.foldr_cons,ih]
    apply Prod.ext
    · rfl
    · cases c <;> simp [capStep,List.foldr_cons,Nat.bit] <;> omega

def boundedValue (b : ℕ) (l : List Bool) : ℕ := (l.reverse.foldl (fun z c => capStep (z,c)) (b,0)).2
lemma boundedValue_eq (b : ℕ) (l : List Bool) : boundedValue b l=min b (value l) := by
  unfold boundedValue
  rw [List.foldl_reverse,show (b,0)=(b,min b 0) by simp,capStep_fold]
  rfl
lemma boundedValue_bits (b n : ℕ) : boundedValue b n.bits=min b n := by rw [boundedValue_eq,value_bits]
lemma capStep_fold_bound (l : List Bool) (z : ℕ×ℕ) :
    (l.foldl (fun z c => capStep (z,c)) z).1=z.1 ∧
    (l.foldl (fun z c => capStep (z,c)) z).2≤ max z.1 z.2 := by
  induction l generalizing z with
  | nil => exact ⟨rfl,Nat.le_max_right _ _⟩
  | cons c l ih =>
    obtain ⟨h₁,h₂⟩ := ih (capStep (z,c))
    refine ⟨h₁,?_⟩
    have hh : (capStep (z,c)).2≤z.1 := min_le_left _ _
    exact h₂.trans (max_le (by exact Nat.le_max_left _ _) (hh.trans (Nat.le_max_left _ _)))
@[fun_prop] theorem boundedValue_poly : Poly (fun z : ℕ×List Bool => boundedValue z.1 z.2) := by
  have hs : Poly capStep := by unfold capStep; fun_prop
  have hf := Poly.listFold false capStep hs (4*X+2) (by
    intro z k
    obtain ⟨h₁,h₂⟩ := capStep_fold_bound (z.1.take k) z.2
    simp only [code_pair_length,code_nat_length,h₁,eval_add,eval_mul,eval_ofNat,eval_X]
    omega)
  unfold boundedValue
  exact Poly.second _ (Poly.comp _ (fun z : ℕ×List Bool => (z.2.reverse,(z.1,0))) hf (by fun_prop))

lemma log2_bits_length (n : ℕ) : n.log2=n.bits.length-1 := by
  by_cases hn : n=0
  · simp [hn]
  have h₁ := (Nat.lt_size).mpr (Nat.log2_self_le hn)
  have h₂ := (Nat.size_le).mpr (Nat.lt_log2_self (n := n))
  rw [←Nat.size_eq_bits_len] at h₁ h₂
  omega
lemma bits_nil_iff (n : ℕ) : n.bits=[] ↔ n=0 := by
  rw [←List.length_eq_zero_iff,Nat.size_eq_bits_len,Nat.size_eq_zero]
end BinaryMatching.Parse
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_BinaryParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Parse
open StackCode Polynomial
abbrev RecordBits := List Bool×(List Bool×List Bool)
def recordRepr (r : Record) : RecordBits := (r.left.bits,(r.right.bits,r.multiplicity.bits))
def record (l : List Bool) : RecordBits×List Bool :=
  let a := numeral l
  let b := numeral a.2
  let c := numeral b.2
  ((a.1,(b.1,c.1)),c.2)
lemma record_encode (r : Record) (l : List Bool) : record (encodeRecord r++l)=(recordRepr r,l) := by
  unfold record encodeRecord
  simp only [List.append_assoc,numeral_encode]
  rfl
lemma record_size (l : List Bool) : (record l).2.length≤l.length ∧
    (encode (record l).1).length≤20*l.length+10 := by
  have h₁ := numeral_lengths l
  have h₂ := numeral_lengths (numeral l).2
  have h₃ := numeral_lengths (numeral (numeral l).2).2
  simp only [record,code_pair_length,cut_code_length]
  omega
@[fun_prop] theorem record_poly : Poly record := by unfold record; fun_prop

def recordStep (z : List Bool×List RecordBits) : List Bool×List RecordBits :=
  if z.1.isEmpty then z else ((record z.1).2,z.2++[(record z.1).1])
lemma encodeRecord_ne_nil (r : Record) : encodeRecord r≠[] := by
  simp [encodeRecord,encodeNat]
lemma recordStep_encode (r : Record) (l : List Bool) (acc : List RecordBits) :
    recordStep (encodeRecord r++l,acc)=(l,acc++[recordRepr r]) := by
  simp [recordStep, List.isEmpty_iff, List.append_eq_nil_iff, encodeRecord_ne_nil, record_encode]
lemma records_length_le_bits (rs : List Record) : rs.length≤(rs.flatMap encodeRecord).length := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hr := List.length_pos_iff.mpr (encodeRecord_ne_nil r)
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    omega

lemma recordStep_size (z : List Bool×List RecordBits) : (recordStep z).1.length≤z.1.length ∧
    (encode (recordStep z).2).length≤(encode z.2).length+40*z.1.length+21 := by
  have hr := record_size z.1
  unfold recordStep
  split_ifs
  · simp; omega
  · simp only [code_append,List.length_append,code_cons,pairBits_length,List.length_nil,code_nil]
    omega
lemma recordStep_iterate_size (k : ℕ) (z : List Bool×List RecordBits) :
    (recordStep^[k] z).1.length≤z.1.length ∧
    (encode (recordStep^[k] z).2).length≤(encode z.2).length+k*(40*z.1.length+21) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := recordStep_size (recordStep^[k] z)
    constructor
    · exact h.1.trans ih.1
    · nlinarith
end BinaryMatching.Parse
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_DyadicEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset

def Piece.evalReal (p : Piece) (t : ℝ) : ℝ := (p.slope:ℝ)*t+(p.constant:ℝ)

def selectedReal (k : ℕ) (t : ℝ) : Piece := by
  classical
  exact ((pieces k).argmin (fun p => p.evalReal t)).getD ⟨k,0⟩

def psiReal (k : ℕ) (t : ℝ) : ℝ := (selectedReal k t).evalReal t

def dyadic (j : ℕ) : ℝ := (2:ℝ)⁻¹^j

lemma mem_pieces (k : ℕ) (p : Piece) :
    p∈pieces k ↔ p=⟨k,0⟩ ∨ ∃ j<k,p=⟨(j:ℤ)-1,(2:ℚ)⁻¹^j⟩ := by
  simp only [pieces,List.mem_append,List.mem_map,List.mem_range,List.mem_singleton]
  aesop

end
end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_DyadicEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset

def phi (t : ℝ) : ℝ := Real.negMulLog t / Real.log 2

end
end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Violation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy
variable {n : ℕ}

def Affine.evalReal (r : Affine n) (x : Pair n → ℝ) : ℝ :=
  (∑ e,(r.coeff e:ℝ)*x e)+r.constant

def allRows (n : ℕ) : List (Affine n) :=
  zeroRow :: ((List.finRange n).flatMap (fun v => [degreeRow v true,degreeRow v false])) ++
    (univ.toList.filter (fun S : Finset (Fin n) => decide (Odd S.card))).map cutRow

def maxRow (x : Pair n → ℝ) : Affine n := by
  classical
  exact ((allRows n).argmax (fun r => r.evalReal x)).getD zeroRow

def violation (x : Pair n → ℝ) : ℝ := (maxRow x).evalReal x

lemma mem_activeRows (a : Table n ℤ) (r : Affine n) : r∈activeRows a ↔
    r=zeroRow ∨ (∃ v,r=degreeRow v true ∨ r=degreeRow v false) ∨
      r=cutRow (OddMincut.oddCut (capacities a) univ) := by
  simp only [activeRows,List.mem_append,List.mem_cons,List.mem_flatMap,List.mem_finRange,
    true_and]
  aesop

end
end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_ObjectivePenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset

lemma le_foldl_max (l : List ℕ) (a : ℕ) : a≤l.foldl max a := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => exact (le_max_left a x).trans (ih (max a x))

lemma mem_le_foldl_max (l : List ℕ) (a x : ℕ) (hx : x∈l) : x≤l.foldl max a := by
  induction l generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl|h
    · exact (le_max_right a x).trans (le_foldl_max ys (max a x))
    · exact ih (max a y) h

lemma record_log_le_B (G : Input) (r : Record) (hr : r∈G.records) : Nat.log2 r.multiplicity≤B G :=
  mem_le_foldl_max _ 0 _ (List.mem_map.mpr ⟨r,hr,rfl⟩)

lemma multiplicity_log_le_B (G : Input) (e : Pair G.n) : Nat.log2 (multiplicity G e)≤B G := by
  unfold multiplicity
  cases he : G.records.find? (fun r => r.left=e.val.1.val && r.right=e.val.2.val) with
  | none => simp
  | some r => exact record_log_le_B G r (List.mem_of_find?_eq_some he)

lemma B_le_L (G : Input) : B G≤L G := by
  have h : B G≤G.n+B G+1 := by omega
  have hp : 1≤G.n+B G+1 := by omega
  have hpow : G.n+B G+1≤(G.n+B G+1)^3 := by exact Nat.le_self_pow (by omega) _
  unfold L
  omega

lemma beta_bound (G : Input) (e : Pair G.n) : |(beta G e:ℝ)|≤L G := by
  unfold beta
  split_ifs
  · simp
  · have hh := (multiplicity_log_le_B G e).trans (B_le_L G)
    norm_cast

lemma piece_slope_bound (k : ℕ) (p : Piece) (hp : p∈pieces k) : |(p.slope:ℝ)|≤k := by
  rcases (mem_pieces k p).1 hp with rfl|⟨j,hj,rfl⟩
  · simp
  · simp only [Int.cast_sub,Int.cast_natCast,Int.cast_one]
    have hj' : (j:ℝ)+1≤k := by exact_mod_cast hj
    have hj0 : (0:ℝ)≤j := by positivity
    rw [abs_le]; constructor <;> linarith

def objective (G : Input) (x : Pair G.n → ℝ) : ℝ :=
  ∑ e, (psiReal (K G.n) (x e)+(beta G e:ℝ)*x e)

def penalized (G : Input) (x : Pair G.n → ℝ) : ℝ :=
  objective G x-(M₀ G:ℝ)*violation x

end
end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Ascent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy

lemma q_pos {n : ℕ} (hn : 2 ≤ n) : 0 < q n := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by change 0 < 1; omega⟩⟩

lemma D₀_pos (G : Input) (hn : 2 ≤ G.n) : 0 < D₀ G := by
  have hL : 0 < L G := by unfold L; positivity
  exact Nat.mul_pos (q_pos hn) (pow_pos (by omega) _)

lemma update_box (G : Input) (a : Table G.n ℤ) (r : Affine G.n) (e : Pair G.n) :
    entry (update G a r) e ∈ Set.Icc (0:ℤ) (D₀ G) := by
  rw [update, at_toTable]
  exact ⟨le_min (Int.natCast_nonneg _) (le_max_left _ _), min_le_left _ _⟩

lemma iterate_box (G : Input) (j : ℕ) (e : Pair G.n) :
    entry (iterate G j).numerators e ∈ Set.Icc (0:ℤ) (D₀ G) := by
  cases j with
  | zero => simp [iterate, initial, at_tabulate]
  | succ j => exact update_box G _ _ e

def point (G : Input) (j : ℕ) (e : Pair G.n) : ℝ :=
  (coordinates (D₀ G) (iterate G j).numerators e : ℝ)

def sampledValue (G : Input) (j : ℕ) : ℚ :=
  trialValue G (iterate G j).numerators (activeRow (D₀ G) (iterate G j).numerators)

def squareDistance {I : Type*} [Fintype I] (x z : I → ℝ) : ℝ :=
  ∑ e, (x e-z e)^2

end
end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_ForcedReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section

noncomputable section
open scoped BigOperators
namespace MatchingEntropy
namespace LooplessGraph
variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def RemainingVertex (G : LooplessGraph V E) (e₀ : E) (v : V) : Prop :=
  ¬G.Incident v e₀

instance remainingVertexDecidable (G : LooplessGraph V E) (e₀ : E) (v : V) :
    Decidable (G.RemainingVertex e₀ v) := inferInstanceAs (Decidable (¬G.Incident v e₀))

def RemainingEdge (G : LooplessGraph V E) (e₀ e : E) : Prop :=
  G.RemainingVertex e₀ (G.left e) ∧ G.RemainingVertex e₀ (G.right e)

instance remainingEdgeDecidable (G : LooplessGraph V E) (e₀ e : E) :
    Decidable (G.RemainingEdge e₀ e) := inferInstanceAs
      (Decidable (G.RemainingVertex e₀ (G.left e) ∧ G.RemainingVertex e₀ (G.right e)))

def deleteEndpoints (G : LooplessGraph V E) (e₀ : E) :
    LooplessGraph {v // G.RemainingVertex e₀ v} {e // G.RemainingEdge e₀ e} where
  left e := ⟨G.left e.val, e.property.1⟩
  right e := ⟨G.right e.val, e.property.2⟩
  loopless e he := G.loopless e.val (congrArg Subtype.val he)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem remainingEdge_ne (G : LooplessGraph V E) (e₀ : E)
    {e : E} (he : G.RemainingEdge e₀ e) : e ≠ e₀ := by
  rintro rfl
  exact he.1 (Or.inl rfl)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem remaining_of_incident (G : LooplessGraph V E) (e₀ : E)
    {e : E} (he : G.RemainingEdge e₀ e) {v : V} (hv : G.Incident v e) :
    G.RemainingVertex e₀ v := by
  rcases hv with h | h
  · exact h ▸ he.1
  · exact h ▸ he.2

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
@[simp] theorem deleteEndpoints_incident (G : LooplessGraph V E) (e₀ : E)
    (v : {v // G.RemainingVertex e₀ v}) (e : {e // G.RemainingEdge e₀ e}) :
    (G.deleteEndpoints e₀).Incident v e ↔ G.Incident v.val e.val := by
  simp only [Incident, deleteEndpoints, Subtype.ext_iff]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem matching_common_vertex (G : LooplessGraph V E) (M : G.Matching)
    {e f : E} (he : e ∈ M.val) (hf : f ∈ M.val) {v : V}
    (hve : G.Incident v e) (hvf : G.Incident v f) : e=f := by
  obtain ⟨g, _, hg⟩ := M.property v
  exact (hg e ⟨he,hve⟩).trans (hg f ⟨hf,hvf⟩).symm

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in

theorem matching_remaining (G : LooplessGraph V E) (e₀ : E) (M : G.Matching)
    (h₀ : e₀ ∈ M.val) {e : E} (he : e ∈ M.val) (hne : e ≠ e₀) :
    G.RemainingEdge e₀ e := by
  constructor
  · intro hv
    exact hne (G.matching_common_vertex M he h₀ (Or.inl rfl) hv)
  · intro hv
    exact hne (G.matching_common_vertex M he h₀ (Or.inr rfl) hv)

def addForced (G : LooplessGraph V E) (e₀ : E) (N : (G.deleteEndpoints e₀).Matching) :
    G.Matching := by
  refine ⟨insert e₀ (N.val.image Subtype.val), ?_⟩
  intro v
  by_cases hv : G.Incident v e₀
  · refine ⟨e₀, ⟨by simp, hv⟩, ?_⟩
    rintro f ⟨hf,hfv⟩
    rcases Finset.mem_insert.mp hf with h | h
    · exact h
    · obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp h
      exact False.elim (G.remaining_of_incident e₀ g.property hfv hv)
  · let v' : {v // G.RemainingVertex e₀ v} := ⟨v,hv⟩
    obtain ⟨f,⟨hf,hfv⟩, hu⟩ := N.property v'
    refine ⟨f.val, ⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨f,hf,rfl⟩),
      (G.deleteEndpoints_incident e₀ v' f).mp hfv⟩, ?_⟩
    rintro g ⟨hg,hgv⟩
    rcases Finset.mem_insert.mp hg with h | h
    · exact False.elim (hv (h ▸ hgv))
    · obtain ⟨g',hg',rfl⟩ := Finset.mem_image.mp h
      exact congrArg Subtype.val (hu g' ⟨hg', (G.deleteEndpoints_incident e₀ v' g').mpr hgv⟩)

omit [Fintype V] [Fintype E] in
@[simp] theorem mem_addForced (G : LooplessGraph V E) (e₀ : E)
    (N : (G.deleteEndpoints e₀).Matching) (e : E) :
    e ∈ (G.addForced e₀ N).val ↔ e=e₀ ∨ ∃ h : G.RemainingEdge e₀ e, ⟨e,h⟩ ∈ N.val := by
  simp only [addForced, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (h | ⟨f,hf,rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨f.property,hf⟩
  · rintro (h | ⟨h,he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨e,h⟩,he,rfl⟩

omit [Fintype V] [Fintype E] in
@[simp] theorem mem_addForced_remaining (G : LooplessGraph V E) (e₀ : E)
    (N : (G.deleteEndpoints e₀).Matching) (e : {e // G.RemainingEdge e₀ e}) :
    e.val ∈ (G.addForced e₀ N).val ↔ e ∈ N.val := by
  rw [mem_addForced]
  simp only [G.remainingEdge_ne e₀ e.property, false_or]
  exact ⟨fun ⟨_,h⟩ => h, fun h => ⟨e.property,h⟩⟩

def removeForced (G : LooplessGraph V E) (e₀ : E)
    (M : {M : G.Matching // e₀ ∈ M.val}) : (G.deleteEndpoints e₀).Matching := by
  refine ⟨M.val.val.subtype (G.RemainingEdge e₀), ?_⟩
  intro v
  obtain ⟨e,⟨he,hev⟩,hu⟩ := M.val.property v.val
  have hne : e ≠ e₀ := by rintro rfl; exact v.property hev
  have hrem := G.matching_remaining e₀ M.val M.property he hne
  refine ⟨⟨e,hrem⟩, ⟨by simpa using he,
    (G.deleteEndpoints_incident e₀ v ⟨e,hrem⟩).mpr hev⟩, ?_⟩
  rintro f ⟨hf,hfv⟩
  apply Subtype.ext
  exact hu f.val ⟨by simpa using hf, (G.deleteEndpoints_incident e₀ v f).mp hfv⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
@[simp] theorem mem_removeForced (G : LooplessGraph V E) (e₀ : E)
    (M : {M : G.Matching // e₀ ∈ M.val}) (e : {e // G.RemainingEdge e₀ e}) :
    e ∈ (G.removeForced e₀ M).val ↔ e.val ∈ M.val.val := by
  simp [removeForced]

def forcedMatchingEquiv (G : LooplessGraph V E) (e₀ : E) :
    (G.deleteEndpoints e₀).Matching ≃ {M : G.Matching // e₀ ∈ M.val} where
  toFun N := ⟨G.addForced e₀ N, (G.mem_addForced e₀ N e₀).mpr (Or.inl rfl)⟩
  invFun M := G.removeForced e₀ M
  left_inv N := by
    apply Subtype.ext
    ext e
    exact (G.mem_removeForced e₀ _ e).trans (G.mem_addForced_remaining e₀ N e)
  right_inv M := by
    apply Subtype.ext
    apply Subtype.ext
    ext e
    rw [mem_addForced]
    constructor
    · rintro (rfl | ⟨h,he⟩)
      · exact M.property
      · exact (G.mem_removeForced e₀ M ⟨e,h⟩).mp he
    · intro he
      by_cases h : e=e₀
      · exact Or.inl h
      · exact Or.inr ⟨G.matching_remaining e₀ M.val M.property he h,
          (G.mem_removeForced e₀ M _).mpr he⟩

omit [Fintype V] [Fintype E] in
@[simp] theorem range_addForced (G : LooplessGraph V E) (e₀ : E) (M : G.Matching) :
    M ∈ Set.range (G.addForced e₀) ↔ e₀ ∈ M.val := by
  constructor
  · rintro ⟨N,rfl⟩
    exact (G.mem_addForced e₀ N e₀).mpr (Or.inl rfl)
  · intro h
    refine ⟨G.removeForced e₀ ⟨M,h⟩, ?_⟩
    exact congrArg Subtype.val ((G.forcedMatchingEquiv e₀).apply_symm_apply ⟨M,h⟩)

end LooplessGraph

end MatchingEntropy
end
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Partition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section

noncomputable section
open Finset
namespace MatchingEntropy

variable {I : Type*} [Fintype I]

def expSum (a : I → ℝ) : ℝ := ∑ i, Real.exp (a i)

namespace LooplessGraph
variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def score (G : LooplessGraph V E) (β : E → ℝ) (M : G.Matching) : ℝ :=
  ∑ e∈M.val,β e

def weightedZ (G : LooplessGraph V E) (β : E → ℝ) : ℝ :=
  expSum (fun M => Real.log 2*G.score β M)

end LooplessGraph
end MatchingEntropy
end
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_AlgorithmPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy

def smoothObjective (G : Input) (x : Pair G.n → ℝ) : ℝ :=
  entropy x/Real.log 2+∑ e,(beta G e:ℝ)*x e

def Z (G : Input) : ℝ := (completeGraph G.n).weightedZ (fun e => (beta G e:ℝ))
def logZ (G : Input) : ℝ := Real.log (Z G)/Real.log 2

end
end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Completion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy

def edgeWeight (G : Input) (e : Pair G.n) : ℝ := Real.exp (Real.log 2*(beta G e:ℝ))
def matchingWeight (G : Input) (M : (completeGraph G.n).Matching) : ℝ :=
  ∏ e∈M.val,edgeWeight G e

def validMatching (G : Input) (M : (completeGraph G.n).Matching) : Prop :=
  ∀ e∈M.val,0< multiplicity G e

def goodWeight (G : Input) (M : (completeGraph G.n).Matching) : ℝ :=
  @ite ℝ (validMatching G M) (Classical.propDecidable _) (matchingWeight G M) 0

def badWeight (G : Input) (M : (completeGraph G.n).Matching) : ℝ :=
  @ite ℝ (validMatching G M) (Classical.propDecidable _) 0 (matchingWeight G M)

def Zgood (G : Input) : ℝ := ∑ M,goodWeight G M
def Zbad (G : Input) : ℝ := ∑ M,badWeight G M

def multProduct (G : Input) (M : (completeGraph G.n).Matching) : ℕ :=
  ∏ e∈M.val,multiplicity G e

end
end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_ParameterBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
open Finset

def Q (G : Input) : ℕ := D₀ G*2^(K G.n)

end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_ScaledAlgorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
open Finset
local instance instPreorderInt_solutions : Preorder ℤ := Int.instLinearOrder.toPreorder

lemma argmin_map {α β γ : Type} [LinearOrder γ] (l : List α) (f : α → β)
    (g : β → γ) : (l.map f).argmin g=(l.argmin (g ∘ f)).map f := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.map_append,List.map_singleton,List.argmin_concat,List.argmin_concat,ih]
    cases h : l.argmin (g ∘ f) with
    | none => rfl
    | some b => simp only [Option.map_some,Function.comp_apply]; split_ifs <;> rfl

lemma argmin_congr_on {α β γ : Type} [LinearOrder β] [LinearOrder γ]
    (l : List α) (f : α → β) (g : α → γ)
    (h : ∀ a∈l, ∀ b∈l, f a<f b ↔ g a<g b) : l.argmin f=l.argmin g := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    have hl (b : α) (hb : b∈l) : b∈l++[a] := List.mem_append_left _ hb
    have ha : a∈l++[a] := by simp
    rw [List.argmin_concat,List.argmin_concat,ih (fun b hb c hc => h b (hl b hb) c (hl c hc))]
    cases hg : l.argmin g with
    | none => rfl
    | some b =>
      simp only
      simp only [h a ha b (hl b (List.argmin_mem hg))]

lemma argmax_congr_on {α β γ : Type} [LinearOrder β] [LinearOrder γ]
    (l : List α) (f : α → β) (g : α → γ)
    (h : ∀ a∈l, ∀ b∈l, f a<f b ↔ g a<g b) : l.argmax f=l.argmax g :=
  @argmin_congr_on α βᵒᵈ γᵒᵈ _ _ l f g (fun a ha b hb => h b hb a ha)

def indexedPiece (k j : ℕ) : Piece :=
  if j<k then ⟨(j:ℤ)-1,(2:ℚ)⁻¹^j⟩ else ⟨k,0⟩

def pieceNumerator (k D : ℕ) (a : ℤ) (j : ℕ) : ℤ :=
  (indexedPiece k j).slope*a*2^k + if j<k then (D:ℤ)*2^(k-j) else 0

lemma pieces_indexed (k : ℕ) : pieces k=(List.range (k+1)).map (indexedPiece k) := by
  rw [List.range_succ,List.map_append,List.map_singleton]
  unfold pieces
  congr 1
  · apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    simp only [indexedPiece,ite_eq_left hj]
  · simp [indexedPiece]

lemma pieceNumerator_cast (k D j : ℕ) (hD : 0<D) (hj : j≤k) (a : ℤ) :
    (pieceNumerator k D a j:ℚ)=(D:ℚ)*2^k*(indexedPiece k j).eval (a/(D:ℚ)) := by
  have hD' : (D:ℚ)≠0 := by exact_mod_cast hD.ne'
  have hp : (2:ℚ)^k=(2:ℚ)^j*2^(k-j) := by rw [←pow_add,Nat.add_sub_of_le hj]
  unfold pieceNumerator Piece.eval indexedPiece
  split_ifs with hjk
  · push_cast
    rw [inv_pow]
    field_simp
    nlinarith [hp]
  · push_cast
    field_simp
    ring

def selectedIndex (k D : ℕ) (a : ℤ) : ℕ :=
  ((List.range (k+1)).argmin (pieceNumerator k D a)).getD k

lemma selectedIndex_mem (k D : ℕ) (a : ℤ) :
    selectedIndex k D a∈(List.range (k+1)).argmin (pieceNumerator k D a) := by
  unfold selectedIndex
  cases h : (List.range (k+1)).argmin (pieceNumerator k D a) with
  | none => have hh := List.argmin_eq_none.mp h; simp at hh
  | some j => rfl

lemma selectedIndex_le (k D : ℕ) (a : ℤ) : selectedIndex k D a≤k := by
  have h := List.argmin_mem (selectedIndex_mem k D a)
  simpa only [List.mem_range,Nat.lt_succ_iff] using h

lemma selectedPiece_index (k D : ℕ) (hD : 0<D) (a : ℤ) :
    selectedPiece k (a/(D:ℚ))=indexedPiece k (selectedIndex k D a) := by
  have hQ : (0:ℚ)<(D:ℚ)*2^k := mul_pos (by exact_mod_cast hD) (by positivity)
  have hc := argmin_congr_on (List.range (k+1))
    (fun j => (indexedPiece k j).eval (a/(D:ℚ))) (pieceNumerator k D a) (by
      intro i hi j hj
      have hi' : i≤k := by simpa only [List.mem_range,Nat.lt_succ_iff] using hi
      have hj' : j≤k := by simpa only [List.mem_range,Nat.lt_succ_iff] using hj
      rw [←mul_lt_mul_iff_right₀ hQ]
      rw [←pieceNumerator_cast k D i hD hi' a,←pieceNumerator_cast k D j hD hj' a]
      exact_mod_cast Iff.rfl)
  unfold selectedPiece selectedIndex
  rw [pieces_indexed,argmin_map]
  change (((List.range (k+1)).argmin (fun j => (indexedPiece k j).eval (a/(D:ℚ)))).map
    (indexedPiece k)).getD _=_
  rw [hc]
  cases h : (List.range (k+1)).argmin (pieceNumerator k D a) with
  | none => simp [indexedPiece]
  | some j => rfl

def scaledPsi (k D : ℕ) (a : ℤ) : ℤ := pieceNumerator k D a (selectedIndex k D a)
def scaledSlope (k D : ℕ) (a : ℤ) : ℤ := (indexedPiece k (selectedIndex k D a)).slope

lemma scaledPsi_cast (k D : ℕ) (hD : 0<D) (a : ℤ) :
    (scaledPsi k D a:ℚ)=(D:ℚ)*2^k*psi k (a/(D:ℚ)) := by
  unfold scaledPsi psi
  rw [selectedPiece_index k D hD]
  exact pieceNumerator_cast k D _ hD (selectedIndex_le k D a) a

lemma scaledSlope_eq (k D : ℕ) (hD : 0<D) (a : ℤ) :
    scaledSlope k D a=slope k (a/(D:ℚ)) := by
  unfold scaledSlope slope
  rw [selectedPiece_index k D hD]

variable {n : ℕ}

def rowNumerator (D : ℕ) (a : Table n ℤ) (r : Affine n) : ℤ :=
  (∑ e,r.coeff e*entry a e)+r.constant*D

lemma rowNumerator_cast (D : ℕ) (hD : 0<D) (a : Table n ℤ) (r : Affine n) :
    (rowNumerator D a r:ℚ)=(D:ℚ)*r.eval (coordinates D a) := by
  have hD' : (D:ℚ)≠0 := by exact_mod_cast hD.ne'
  simp only [rowNumerator,Affine.eval,coordinates,Int.cast_add,Int.cast_sum,Int.cast_mul,
    Int.cast_natCast,mul_add,mul_sum]
  congr 1
  · apply sum_congr rfl
    intro e he
    field_simp
  · ring

def integralRows (a : Table n ℤ) : List (Affine n) :=
  zeroRow :: ((List.finRange n).flatMap (fun v => [degreeRow v true,degreeRow v false])) ++
    [cutRow (DenseOracle.oddCut (DenseOracle.make (capacities a)) univ)]

lemma integralRows_eq (a : Table n ℤ) : integralRows a=activeRows a := by
  simp only [integralRows,DenseOracle.oddCut_eq,DenseOracle.view_make,activeRows]

def integralRow (D : ℕ) (a : Table n ℤ) : Affine n :=
  ((integralRows a).argmax (rowNumerator D a)).getD zeroRow

lemma integralRow_eq (D : ℕ) (hD : 0<D) (a : Table n ℤ) :
    integralRow D a=activeRow D a := by
  unfold integralRow activeRow
  rw [integralRows_eq]
  congr 1
  apply argmax_congr_on
  intro r hr s hs
  rw [←Int.cast_lt (R := ℚ),rowNumerator_cast D hD,rowNumerator_cast D hD]
  exact mul_lt_mul_iff_right₀ (by exact_mod_cast hD)

def integralValue (G : Input) (a : Table G.n ℤ) (r : Affine G.n) : ℤ :=
  (∑ e, (scaledPsi (K G.n) (D₀ G) (entry a e)+beta G e*entry a e*2^(K G.n))) -
    (M₀ G:ℤ)*rowNumerator (D₀ G) a r*2^(K G.n)

def integralGradient (G : Input) (a : Table G.n ℤ) (r : Affine G.n) (e : Pair G.n) : ℤ :=
  scaledSlope (K G.n) (D₀ G) (entry a e)+beta G e-(M₀ G:ℤ)*r.coeff e

def integralUpdate (G : Input) (a : Table G.n ℤ) (r : Affine G.n) : Table G.n ℤ :=
  toTable (fun e => min (D₀ G:ℤ) (max 0 (entry a e+integralGradient G a r e)))

lemma integralGradient_eq (G : Input) (hn : 2≤G.n) (a : Table G.n ℤ) (r : Affine G.n) :
    integralGradient G a r=gradient G a r := by
  funext e
  simp only [integralGradient,gradient,coordinates,scaledSlope_eq _ _ (D₀_pos G hn)]

lemma integralUpdate_eq (G : Input) (hn : 2≤G.n) (a : Table G.n ℤ) (r : Affine G.n) :
    integralUpdate G a r=update G a r := by
  simp only [integralUpdate,update,integralGradient_eq G hn]

lemma integralValue_cast (G : Input) (hn : 2≤G.n) (a : Table G.n ℤ) (r : Affine G.n) :
    (integralValue G a r:ℚ)=(Q G:ℚ)*trialValue G a r := by
  have hD : (D₀ G:ℚ)≠0 := by exact_mod_cast (D₀_pos G hn).ne'
  simp only [integralValue,Int.cast_sub,Int.cast_sum,Int.cast_add,Int.cast_mul,Int.cast_pow,
    Int.cast_ofNat,Int.cast_natCast,scaledPsi_cast _ _ (D₀_pos G hn),
    rowNumerator_cast _ (D₀_pos G hn),trialValue,Q,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
    mul_sub,mul_sum,mul_add,coordinates]
  congr 1
  · apply sum_congr rfl
    intro e he
    field_simp
  · ring

structure IntegralState (n : ℕ) where
  numerators : Table n ℤ
  best : Option ℤ

def integralStep (G : Input) (s : IntegralState G.n) : IntegralState G.n :=
  let r := integralRow (D₀ G) s.numerators
  let value := integralValue G s.numerators r
  ⟨integralUpdate G s.numerators r,some (s.best.elim value (max value))⟩

def integralInitial (n : ℕ) : IntegralState n := ⟨tabulate (fun _ _ => 0),none⟩

def integralIterate (G : Input) : ℕ → IntegralState G.n
  | 0 => integralInitial G.n
  | t+1 => integralStep G (integralIterate G t)

end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_ScaledState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm

lemma Q_pos (G : Input) (hn : 2≤G.n) : 0<Q G :=
  Nat.mul_pos (D₀_pos G hn) (by positivity)

def decodeIntegral (G : Input) (s : IntegralState G.n) : State G.n :=
  ⟨s.numerators,s.best.map (fun v : ℤ => (v:ℚ)/(Q G:ℚ))⟩

lemma integralValue_div (G : Input) (hn : 2≤G.n) (a : Table G.n ℤ) (r : Affine G.n) :
    (integralValue G a r:ℚ)/(Q G:ℚ)=trialValue G a r := by
  rw [integralValue_cast G hn]
  have hQ : (Q G:ℚ)≠0 := by exact_mod_cast (Q_pos G hn).ne'
  exact mul_div_cancel_left₀ _ hQ

lemma decodeIntegral_step (G : Input) (hn : 2≤G.n) (s : IntegralState G.n) :
    decodeIntegral G (integralStep G s)=step G (decodeIntegral G s) := by
  obtain ⟨a,b⟩ := s
  dsimp only [decodeIntegral,integralStep,step]
  rw [integralRow_eq _ (D₀_pos G hn),integralUpdate_eq G hn]
  congr 1
  cases b with
  | none => simp only [Option.map_none,Option.elim_none,Option.map_some,integralValue_div G hn]
  | some v =>
    simp only [Option.map_some,Option.elim_some,Int.cast_max]
    rw [←max_div_div_right (by positivity : (0:ℚ)≤Q G),integralValue_div G hn]

lemma decodeIntegral_iterate (G : Input) (hn : 2≤G.n) (j : ℕ) :
    decodeIntegral G (integralIterate G j)=iterate G j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [integralIterate,decodeIntegral_step G hn,ih,iterate]

lemma integralIterate_table (G : Input) (hn : 2≤G.n) (j : ℕ) :
    (integralIterate G j).numerators=(iterate G j).numerators :=
  congrArg State.numerators (decodeIntegral_iterate G hn j)

def integralR (G : Input) : ℤ := ((integralIterate G (q G.n*D₀ G)).best).getD 0/(Q G:ℤ)

def integralEstimate (G : Input) : ℕ :=
  let r := integralR G
  if r < -10*(G.n:ℤ) then 0 else 2^(r-5*(G.n:ℤ)).toNat

end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_GuardRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

def guardedStep {α : Type} [Coding α] [Inhabited α] (f : α → α) (z : ℕ×α) : ℕ×α :=
  (z.1,if (encode (f z.2)).length≤z.1 then f z.2 else z.2)

lemma guardedStep_size {α : Type} [Coding α] [Inhabited α] (f : α → α) (z : ℕ×α) (j : ℕ) :
    ((guardedStep f)^[j] z).1=z.1 ∧
      (encode ((guardedStep f)^[j] z).2).length≤ max z.1 (encode z.2).length := by
  induction j with
  | zero => exact ⟨rfl,Nat.le_max_right _ _⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    constructor
    · exact ih.1
    · simp only [guardedStep,ih.1]
      split_ifs with h
      · exact h.trans (Nat.le_max_left _ _)
      · exact ih.2

namespace Poly
variable {α : Type} [Coding α] [Inhabited α]
@[fun_prop] theorem guardedStep_poly (f : α → α) (hf : Poly f) : Poly (guardedStep f) := by
  unfold guardedStep
  have hc : Poly (fun z : ℕ×α => (encode (f z.2)).length) :=
    Poly.comp _ (fun z : ℕ×α => f z.2) Poly.codeLength (by fun_prop)
  have hh : Poly (fun z : ℕ×α => (z.1,if decide ((encode (f z.2)).length≤z.1) then f z.2 else z.2)) := by fun_prop
  exact hh.congr (fun _ => by simp)

@[fun_prop] theorem guardedIterate (f : α → α) (hf : Poly f) :
    Poly (fun z : ℕ×(ℕ×α) => ((guardedStep f)^[z.1] z.2).2) := by
  apply second
  apply boundedIterate (guardedStep f) (guardedStep_poly f hf) (3*X+1)
  intro z j hj
  have hh := guardedStep_size f z.2 j
  rw [code_pair_length,hh.1,code_nat_length]
  have hb : max z.2.1 (encode z.2.2).length≤(encode z).length := by
    simp only [code_pair_length,code_nat_length]
    omega
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
  have hN : z.2.1≤(encode z).length := by simp only [code_pair_length,code_nat_length]; omega
  omega
end Poly
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_CappedPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

def capDouble (z : ℕ×ℕ) : ℕ×ℕ := (z.1,min z.1 (2*z.2))
lemma capDouble_spec (z : ℕ×ℕ) (k : ℕ) :
    (capDouble^[k] z).1=z.1 ∧ (capDouble^[k] z).2≤ max z.1 z.2 := by
  induction k with
  | zero => exact ⟨rfl,Nat.le_max_right _ _⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨ih.1,(min_le_left _ _).trans (by rw [ih.1]; exact Nat.le_max_left _ _)⟩

def cappedPow2 (b k : ℕ) : ℕ := (capDouble^[k] (b,min b 1)).2

namespace Poly
@[fun_prop] theorem capDouble_poly : Poly capDouble := by unfold capDouble; fun_prop
@[fun_prop] theorem cappedPow2_poly : Poly (fun z : ℕ×ℕ => cappedPow2 z.1 z.2) := by
  have hi : Poly (fun z : ℕ×(ℕ×ℕ) => capDouble^[z.1] z.2) :=
    boundedIterate capDouble capDouble_poly (3*X+1) (by
      intro z j hj
      obtain ⟨h₁,h₂⟩ := capDouble_spec z.2 j
      rw [code_pair_length,h₁,code_nat_length,code_nat_length]
      have hm : max z.2.1 z.2.2≤(encode z).length := by
        simp only [code_pair_length,code_nat_length]; omega
      have hn : z.2.1≤(encode z).length := by
        simp only [code_pair_length,code_nat_length]; omega
      simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
      omega)
  unfold cappedPow2
  fun_prop
end Poly
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw
open Finset

def residual (c : Matrix ℕ) (b : Matrix ℤ) (i j : ℕ) : Bool :=
  decide (get b i j < ((get c i j : ℕ):ℤ))
def initial (n a : ℕ) : Paths := tab n (fun v => if v=a then some [a] else none)
def predecessor (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (p : Paths) (v : ℕ) : Option ℕ :=
  (List.range n).find? (fun u => residual c b u v && (nth p u).isSome)
def pathStep (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (p : Paths) : Paths :=
  tab n (fun v => match nth p v with
    | some l => some l
    | none => match predecessor n c b p v with
      | none => none
      | some u => (nth p u).map (fun l => v::l))
def search (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (a k : ℕ) : Paths :=
  (pathStep n c b)^[k] (initial n a)
def reached (n : ℕ) (p : Paths) : Cut := tab n (fun v => (nth p v).isSome)

@[simp] lemma nth_pathRep {n : ℕ} (p : ResidualSearch.Table n) (v : Fin n) :
    nth (pathRep p) v.val=(p v).map (List.map Fin.val) := by simp [pathRep]

end BinaryMatching.Raw
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawSearchSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw
open StackCode

def PathSize (p : Paths) (M : ℕ) : Prop := ∀ q∈p,(encode q).length≤M

lemma initial_size (n a : ℕ) : PathSize (initial n a) (4*a+3) := by
  intro q hq
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hq
  split_ifs
  · simp only [code_option_some,code_cons,code_nat_length,code_nil,List.length_nil,pairBits_length]
    omega
  · simp only [code_option_none,List.length_nil]; omega

lemma search_length (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (a k : ℕ) :
    (search n c b a k).length=n := by
  cases k with
  | zero => simp [search,initial,tab]
  | succ k => simp [search,Function.iterate_succ_apply',pathStep,tab]

end BinaryMatching.Raw
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_OptionCases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode.Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ] [Inhabited β]

theorem optionCasesWith (p : α → Option β) (f : α → γ) (g : α×β → γ)
    (hp : Poly p) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => match p a with | none => f a | Option.some b => g (a,b)) := by
  have h : Poly (fun a => if (p a).isSome then g (a,(p a).getD default) else f a) := by fun_prop
  exact h.congr (fun a => by cases p a <;> rfl)

theorem optionMapWith (p : α → Option β) (g : α×β → γ) (hp : Poly p) (hg : Poly g) :
    Poly (fun a => (p a).map (fun b => g (a,b))) := by
  have h := optionCasesWith p (fun _ => (none:Option γ))
    (fun z => Option.some (g z)) hp (by fun_prop) (by fun_prop)
  exact h.congr (fun a => by cases p a <;> rfl)
end BinaryMatching.StackCode.Poly
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawSearchCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw
open StackCode Polynomial
abbrev SearchContext := ℕ×(Matrix ℕ×(Matrix ℤ×ℕ))
abbrev SearchState := SearchContext×Paths

def searchStep (s : SearchState) : SearchState :=
  (s.1,pathStep s.1.1 s.1.2.1 s.1.2.2.1 s.2)
def searchInitial (z : SearchContext×ℕ) : SearchState :=
  (z.1,initial z.1.1 z.1.2.2.2)

lemma searchStep_iterate (z : SearchContext×ℕ) (j : ℕ) :
    searchStep^[j] (searchInitial z)=(z.1,search z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 j) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply',ih,searchStep,search]

namespace Compiler
open StackCode.Poly

@[fun_prop] theorem residual_poly :
    Poly (fun z : (Matrix ℕ×Matrix ℤ)×(ℕ×ℕ) => residual z.1.1 z.1.2 z.2.1 z.2.2) := by
  unfold residual
  fun_prop

@[fun_prop] theorem initial_poly : Poly (fun z : ℕ×ℕ => initial z.1 z.2) := by
  unfold initial
  apply Poly.rawTab Prod.fst (fun z : (ℕ×ℕ)×ℕ => if z.2=z.1.2 then Option.some [z.1.2] else none)
  · fun_prop
  · have h : Poly (fun z : (ℕ×ℕ)×ℕ => if decide (z.2=z.1.2) then Option.some [z.1.2] else none) := by fun_prop
    exact h.congr (fun z => by simp)

@[fun_prop] theorem predecessor_poly :
    Poly (fun z : ((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ =>
      predecessor z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2) := by
  unfold predecessor
  apply Poly.findWith (fun z => List.range z.1.1.1)
    (fun z : (((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ)×ℕ =>
      residual z.1.1.1.2.1 z.1.1.1.2.2 z.2 z.1.2 && (nth z.1.1.2 z.2).isSome)
  · fun_prop
  · have hr := Poly.comp _ (fun z : (((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ)×ℕ =>
        ((z.1.1.1.2.1,z.1.1.1.2.2),(z.2,z.1.2))) residual_poly (by fun_prop)
    have hs : Poly (fun z : (((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ)×ℕ =>
        (nth z.1.1.2 z.2).isSome) := by fun_prop
    exact Poly.comp _ _ Poly.boolAnd (Poly.pair _ _ hr hs)

def pathEntry (z : ((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ) : Option (List ℕ) :=
  match nth z.1.2 z.2 with
  | Option.some l => Option.some l
  | none => match predecessor z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2 with
    | none => none
    | Option.some u => (nth z.1.2 u).map (fun l => z.2::l)

@[fun_prop] theorem pathEntry_poly : Poly pathEntry := by
  have h := Poly.optionCasesWith
    (fun z : ((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ => nth z.1.2 z.2)
    (fun z => match predecessor z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2 with
      | none => none
      | Option.some u => (nth z.1.2 u).map (fun l => z.2::l))
    (fun z => Option.some z.2)
    (by fun_prop)
    (by
      have hi := Poly.optionCasesWith
        (fun z : ((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ => predecessor z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2)
        (fun _ => (none:Option (List ℕ)))
        (fun z => (nth z.1.1.2 z.2).map (fun l => z.1.2::l))
        predecessor_poly (by fun_prop)
        (Poly.optionMapWith (fun z : (((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ)×ℕ => nth z.1.1.2 z.2)
          (fun z => z.1.1.2::z.2) (by fun_prop) (by fun_prop))
      exact hi.congr (fun z => by cases predecessor z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2 <;> rfl))
    (by fun_prop)
  exact h.congr (fun z => by unfold pathEntry; cases nth z.1.2 z.2 <;> rfl)

@[fun_prop] theorem pathStep_poly :
    Poly (fun z : (ℕ×(Matrix ℕ×Matrix ℤ))×Paths => pathStep z.1.1 z.1.2.1 z.1.2.2 z.2) := by
  exact Poly.rawTab (fun z => z.1.1) pathEntry (by fun_prop) pathEntry_poly

@[fun_prop] theorem searchStep_poly : Poly searchStep := by
  unfold searchStep
  apply Poly.pair
  · fun_prop
  · exact Poly.comp _ (fun s : SearchState => ((s.1.1,(s.1.2.1,s.1.2.2.1)),s.2))
      pathStep_poly (by fun_prop)

@[fun_prop] theorem searchInitial_poly : Poly searchInitial := by
  unfold searchInitial
  apply Poly.pair
  · fun_prop
  · exact Poly.comp _ (fun z : SearchContext×ℕ => (z.1.1,z.1.2.2.2)) initial_poly (by fun_prop)

end Compiler
end BinaryMatching.Raw
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_OracleBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.DenseOracle
open Finset UnitFlow CutAlgebra OddCutParity
variable {n : ℕ}

def total (c : Fin n → Fin n → ℕ) : ℕ := ∑ i, ∑ j, c i j

lemma entry_le_total (c : Fin n → Fin n → ℕ) (i j : Fin n) : c i j≤total c :=
  (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)).trans
    (single_le_sum (fun x _ => Nat.zero_le (∑ y, c x y)) (mem_univ i))

lemma push_total_le (c : Fin n → Fin n → ℕ) (f : Fin n → Fin n) :
    total (push c f)≤total c := by
  calc
    _ ≤ ∑ i,∑ j,∑ u,∑ v,if f u=i ∧ f v=j then c u v else 0 := by
      apply sum_le_sum; intro i hi
      apply sum_le_sum; intro j hj
      unfold push
      split_ifs
      · exact Nat.zero_le _
      · rfl
    _ = ∑ u,∑ v,∑ i,∑ j,if f u=i ∧ f v=j then c u v else 0 := sum_four_swap _
    _ = total c := by simp [total,ite_and,Finset.sum_ite_irrel,eq_comm]

def calls : ℕ → Matrix n ℕ → Finset (Fin n) → ℕ
  | 0,_,_ => 1
  | k+1,c,U =>
    let A := terminalCut c U
    if OddSide U A then 1 else
      match OddMincut.outside A, OddMincut.outside Aᶜ with
      | some r,some q =>
        1+calls k (contract c (contractMap A r)) (A∩U)+
          calls k (contract c (contractMap Aᶜ q)) (Aᶜ∩U)
      | _,_ => 1

lemma calls_bound (fuel : ℕ) (c : Matrix n ℕ) (U : Finset (Fin n))
    (he : Even U.card) (hU : 2≤U.card) (hbound : U.card≤fuel) :
    calls fuel c U≤U.card-1 := by
  induction fuel generalizing c U with
  | zero => omega
  | succ k ih =>
    let A := terminalCut c U
    obtain ⟨hsep,_⟩ := TerminalMincut.terminalCut_correct (view c) U hU
    rw [←terminalCut_eq] at hsep
    change TerminalMincut.Separates U A at hsep
    by_cases hodd : OddSide U A
    · have hcall : calls (k+1) c U=1 := by
        rw [calls]
        change (if OddSide U A then 1 else _)=1
        exact ite_eq_left hodd
      rw [hcall]; omega
    · have heA : Even (A∩U).card := by
        simp only [OddSide,Nat.odd_iff] at hodd
        rw [Nat.even_iff]; omega
      have heB := even_other U A he heA
      obtain ⟨hposA,hposB⟩ := separate_cards U A hsep
      have hpart := terminal_partition U A
      have htwoA : 2≤(A∩U).card := by rw [Nat.even_iff] at heA; omega
      have htwoB : 2≤(Aᶜ∩U).card := by rw [Nat.even_iff] at heB; omega
      have hboundA : (A∩U).card≤k := by omega
      have hboundB : (Aᶜ∩U).card≤k := by omega
      rw [calls]
      change (if OddSide U A then 1 else _ )≤_
      rw [ite_eq_right hodd]
      split
      · rename_i r q hr hq
        have h₁ := ih (contract c (contractMap A r)) (A∩U) heA htwoA hboundA
        have h₂ := ih (contract c (contractMap Aᶜ q)) (Aᶜ∩U) heB htwoB hboundB
        change 1+calls k (contract c (contractMap A r)) (A∩U)+
          calls k (contract c (contractMap Aᶜ q)) (Aᶜ∩U)≤U.card-1
        omega
      · omega

end BinaryMatching.DenseOracle
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_ScaledBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
open Finset
variable {n : ℕ}
lemma int_two_abs : (2:ℤ).natAbs=2 := rfl

lemma beta_abs_nat (G : Input) (e : Pair G.n) : (beta G e).natAbs ≤ L G := by
  have h := beta_bound G e
  have h' : |beta G e| ≤ (L G:ℤ) := by exact_mod_cast h
  rw [←Int.natCast_natAbs] at h'
  exact_mod_cast h'

lemma indexed_slope_abs (k j : ℕ) (hj : j ≤ k) : (indexedPiece k j).slope.natAbs ≤ k := by
  have hm : indexedPiece k j∈pieces k := by
    rw [pieces_indexed]
    exact List.mem_map.mpr ⟨j,List.mem_range.mpr (by omega),rfl⟩
  have h := piece_slope_bound k _ hm
  have h' : |(indexedPiece k j).slope| ≤ (k:ℤ) := by exact_mod_cast h
  rw [←Int.natCast_natAbs] at h'
  exact_mod_cast h'

lemma pieceNumerator_abs (k D j : ℕ) (hj : j ≤ k) (a : ℤ) (ha : a.natAbs ≤ D) :
    (pieceNumerator k D a j).natAbs ≤ (k+1)*D*2^k := by
  have hs := indexed_slope_abs k j hj
  have hp : 2^(k-j) ≤ 2^k := Nat.pow_le_pow_right (by omega) (Nat.sub_le k j)
  unfold pieceNumerator
  refine (Int.natAbs_add_le _ _).trans ?_
  simp only [Int.natAbs_mul,Int.natAbs_pow,int_two_abs]
  split_ifs
  · have h₁ := Nat.mul_le_mul_right (2^k) (Nat.mul_le_mul hs ha)
    have h₂ := Nat.mul_le_mul_left D hp
    simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast,int_two_abs]
    nlinarith
  · simpa only [Int.natAbs_zero,Nat.add_zero] using
      (Nat.mul_le_mul_right (2^k) (Nat.mul_le_mul (hs.trans (Nat.le_succ k)) ha))

lemma integralRow_mem (D : ℕ) (a : Table n ℤ) : integralRow D a∈integralRows a := by
  unfold integralRow
  cases h : (integralRows a).argmax (rowNumerator D a) with
  | none => simp [integralRows]
  | some r => exact List.argmax_mem h

lemma integral_row_coeff (a : Table n ℤ) (r : Affine n) (hr : r∈integralRows a)
    (e : Pair n) : (r.coeff e).natAbs ≤ 1 := by
  rw [integralRows_eq] at hr
  rcases (mem_activeRows a r).mp hr with rfl|⟨v,rfl|rfl⟩|rfl
  · simp [zeroRow]
  · simp only [degreeRow,↓reduceIte]; split_ifs <;> norm_num
  · simp only [degreeRow,Bool.false_eq_true,↓reduceIte]; split_ifs <;> norm_num
  · simp only [cutRow]; split_ifs <;> norm_num

lemma integral_row_constant (a : Table n ℤ) (r : Affine n) (hr : r∈integralRows a) :
    r.constant.natAbs ≤ 1 := by
  rw [integralRows_eq] at hr
  rcases (mem_activeRows a r).mp hr with rfl|⟨v,rfl|rfl⟩|rfl <;>
    simp [zeroRow,degreeRow,cutRow]

lemma rowNumerator_abs (D : ℕ) (a : Table n ℤ) (ha : ∀ e,(entry a e).natAbs ≤ D)
    (r : Affine n) (hr : r∈integralRows a) : (rowNumerator D a r).natAbs ≤ (q n+1)*D := by
  have hs : (∑ e,r.coeff e*entry a e).natAbs ≤ q n*D := by
    calc
      _  ≤  ∑ e,(r.coeff e*entry a e).natAbs := Int.natAbs_sum_le _ _
      _  ≤  ∑ _e : Pair n,D := sum_le_sum fun e _ => by
        rw [Int.natAbs_mul]
        simpa using Nat.mul_le_mul (integral_row_coeff a r hr e) (ha e)
      _ = _ := by simp [q]
  have hc : (r.constant*(D:ℤ)).natAbs ≤ D := by
    rw [Int.natAbs_mul,Int.natAbs_natCast]
    simpa using Nat.mul_le_mul_right D (integral_row_constant a r hr)
  exact (Int.natAbs_add_le _ _).trans (by nlinarith)

lemma scaledPsi_abs (k D : ℕ) (a : ℤ) (ha : a.natAbs ≤ D) :
    (scaledPsi k D a).natAbs ≤ (k+1)*D*2^k :=
  pieceNumerator_abs k D _ (selectedIndex_le k D a) a ha

def operandBound (G : Input) : ℕ :=
  Q G*(q G.n*(K G.n+L G+1)+M₀ G*(q G.n+1))

lemma integralValue_abs (G : Input) (a : Table G.n ℤ)
    (ha : ∀ e,(entry a e).natAbs ≤ D₀ G) (r : Affine G.n) (hr : r∈integralRows a) :
    (integralValue G a r).natAbs ≤ operandBound G := by
  have he (e : Pair G.n) :
      (scaledPsi (K G.n) (D₀ G) (entry a e)+beta G e*entry a e*2^(K G.n)).natAbs
         ≤ (K G.n+L G+1)*Q G := by
    have h₁ := scaledPsi_abs (K G.n) (D₀ G) (entry a e) (ha e)
    have h₂ : (beta G e*entry a e*2^(K G.n)).natAbs ≤ L G*Q G := by
      simp only [Int.natAbs_mul,Int.natAbs_pow,int_two_abs]
      calc
        _  ≤  L G*D₀ G*2^(K G.n) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (beta_abs_nat G e) (ha e))
        _ = _ := by unfold Q; ring
    exact (Int.natAbs_add_le _ _).trans (by unfold Q at *; nlinarith)
  have hs : (∑ e,(scaledPsi (K G.n) (D₀ G) (entry a e)+beta G e*entry a e*2^(K G.n))).natAbs
       ≤ q G.n*((K G.n+L G+1)*Q G) := by
    calc
      _ ≤ ∑ e,(scaledPsi (K G.n) (D₀ G) (entry a e)+beta G e*entry a e*2^(K G.n)).natAbs :=
        Int.natAbs_sum_le _ _
      _ ≤ ∑ _e : Pair G.n,(K G.n+L G+1)*Q G := sum_le_sum (fun e _ => he e)
      _ = _ := by simp only [sum_const,card_univ,smul_eq_mul,q]
  have hc : ((M₀ G:ℤ)*rowNumerator (D₀ G) a r*2^(K G.n)).natAbs ≤ M₀ G*(q G.n+1)*Q G := by
    simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast,int_two_abs]
    calc
      _  ≤  M₀ G*((q G.n+1)*D₀ G)*2^(K G.n) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (rowNumerator_abs _ a ha r hr))
      _ = _ := by unfold Q; ring
  exact (Int.natAbs_sub_le _ _).trans (by unfold operandBound; nlinarith)

lemma integralIterate_abs (G : Input) (hn : 2 ≤ G.n) (t : ℕ) (e : Pair G.n) :
    (entry (integralIterate G t).numerators e).natAbs ≤ D₀ G := by
  rw [integralIterate_table G hn]
  have h := iterate_box G t e
  have hh : |entry (iterate G t).numerators e| ≤ (D₀ G:ℤ) := by rw [abs_of_nonneg h.1]; exact h.2
  rw [←Int.natCast_natAbs] at hh
  exact_mod_cast hh

lemma integralBest_abs (G : Input) (hn : 2 ≤ G.n) (t : ℕ) (v : ℤ)
    (hv : v∈(integralIterate G t).best) : v.natAbs ≤ operandBound G := by
  induction t generalizing v with
  | zero => simp [integralIterate,integralInitial] at hv
  | succ t ih =>
    let a := (integralIterate G t).numerators
    let r := integralRow (D₀ G) a
    have hrow : r∈integralRows a := integralRow_mem _ _
    have hval := integralValue_abs G a (integralIterate_abs G hn t) r hrow
    change v∈some ((integralIterate G t).best.elim (integralValue G a r) (max (integralValue G a r))) at hv
    have he := Option.mem_some_iff.mp hv
    subst v
    cases hb : (integralIterate G t).best with
    | none => simpa only [Option.elim_none] using hval
    | some w =>
      have hw := ih w hb
      simp only [Option.elim_some]
      by_cases hh : w ≤ integralValue G a r
      · rwa [max_eq_left hh]
      · rwa [max_eq_right (le_of_not_ge hh)]

end BinaryMatching.Algorithm
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw.InputData
open StackCode Algorithm
abbrev Rec := ℕ×(ℕ×List Bool)
end BinaryMatching.Raw.InputData
end

end OAI
end


