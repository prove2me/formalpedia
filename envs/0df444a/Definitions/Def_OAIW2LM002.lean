-- Prove2me | Definitions.Def_OAIW2LM002
-- name    : OAIW2LM002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T03:03:41.132625+00:00
-- url     : https://prove2.me/theorems/cc173683-9976-4de0-b533-2bae43a6d595
-- title:
--   Definitions bundle OAIW2LM002 of the split of OpenAI, the Lean development OAI.Computability.LoopMatching (comparator challenge of OAI.LoopMatching.fullEndpoint)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LoopMatching.fullEndpoint`, carved from OpenAI's openai/math development (OpenAI, *the Lean development OAI.Computability.LoopMatching (comparator challenge of OAI.LoopMatching.fullEndpoint)*, OpenAI Math Release, October 2026, result family not identified here; see lean/formalization.yaml, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 441 declarations of OpenAI's Lean: 136 definitions, 1 inductive type or structure, 5 instances and 299 theorems. The definitions and types are `OAI.BinaryMatching.Raw.ArgGood`, `OAI.BinaryMatching.Raw.CutGood`, `OAI.BinaryMatching.Raw.FlowContext`, `OAI.BinaryMatching.Raw.FlowState`, `OAI.BinaryMatching.Raw.InputData.Data`, `OAI.BinaryMatching.Raw.InputData.betaMatrix`, `OAI.BinaryMatching.Raw.InputData.betaValue`, `OAI.BinaryMatching.Raw.InputData.bitsBudget`, `OAI.BinaryMatching.Raw.InputData.decodeRecord`, `OAI.BinaryMatching.Raw.InputData.multiplicityBits`, `OAI.BinaryMatching.Raw.InputData.pairs`, `OAI.BinaryMatching.Raw.InputData.parameters`, `OAI.BinaryMatching.Raw.InputData.repr`, `OAI.BinaryMatching.Raw.InputData.smallEstimate`, `OAI.BinaryMatching.Raw.InputData.smallSolve`, `OAI.BinaryMatching.Raw.InputData.solve`, `OAI.BinaryMatching.Raw.InputData.sparseEstimate`, `OAI.BinaryMatching.Raw.JoinGood`, `OAI.BinaryMatching.Raw.MatrixBound`, `OAI.BinaryMatching.Raw.OddArg`, `OAI.BinaryMatching.Raw.OddJoin`, `OAI.BinaryMatching.Raw.Optimize.IntState`, `OAI.BinaryMatching.Raw.Optimize.ParamData`, `OAI.BinaryMatching.Raw.Optimize.Params`, `OAI.BinaryMatching.Raw.Optimize.Params.ofData`, `OAI.BinaryMatching.Raw.Optimize.Params.repr`, `OAI.BinaryMatching.Raw.Optimize.Row`, `OAI.BinaryMatching.Raw.Optimize.budget`, `OAI.BinaryMatching.Raw.Optimize.capacities`, `OAI.BinaryMatching.Raw.Optimize.cutRow`, `OAI.BinaryMatching.Raw.Optimize.degreeRow`, `OAI.BinaryMatching.Raw.Optimize.gradient`, `OAI.BinaryMatching.Raw.Optimize.initial`, `OAI.BinaryMatching.Raw.Optimize.operandBound`, `OAI.BinaryMatching.Raw.Optimize.params`, `OAI.BinaryMatching.Raw.Optimize.pieceNumerator`, `OAI.BinaryMatching.Raw.Optimize.result`, `OAI.BinaryMatching.Raw.Optimize.rowNumerator`, `OAI.BinaryMatching.Raw.Optimize.rowRep`, `OAI.BinaryMatching.Raw.Optimize.rows` and 97 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, lean/OAI/Combinatorics, in whole or in part: `LoopMatching_Approximation`, `LoopMatching_BinaryMultiply`, `LoopMatching_BitAddRoutine`, `LoopMatching_BitNormalize`, `LoopMatching_CountedParser`, `LoopMatching_ExpandBijection`, `LoopMatching_InputDecode`, `LoopMatching_InputMachine`, `LoopMatching_LoopParser`, `LoopMatching_MachineMain`, `LoopMatching_RawAccumulator`, `MatchingCount_BinarySolve`, `MatchingCount_CappedPower`, `MatchingCount_FiniteStack`, `MatchingCount_GuardRoutine`, `MatchingCount_OrbitRoutine`, `MatchingCount_PolyCoding`, `MatchingCount_RawContraction`, `MatchingCount_RawContractionCompiler`, `MatchingCount_RawData`, `MatchingCount_RawFlow`, `MatchingCount_RawFlowCompiler`, `MatchingCount_RawFlowSize`, `MatchingCount_RawInput`, `MatchingCount_RawOddBounds`, `MatchingCount_RawOddCompiler`, `MatchingCount_RawOddCut`, `MatchingCount_RawOptimizer`, `MatchingCount_RawOptimizerCompiler`, `MatchingCount_RawOptimizerData`, `MatchingCount_RawOptimizerDataCompiler`, `MatchingCount_RawOptimizerRows`, `MatchingCount_RawOptimizerRowsCompiler`, `MatchingCount_RawSearch`, `MatchingCount_RawSearchCompiler`, `MatchingCount_RawSearchSize`, `MatchingCount_RecursiveBounds`, `MatchingCount_RecursiveCoding`, `MatchingCount_RecursiveCompiler`, `MatchingCount_StackRoutine`, `MatchingCount_UnaryClog`, `PerfectMatching_Contraction`, `PerfectMatching_FeasibilityRepair`, `PerfectMatching_Model`.
--
--   **Imports.** It imports the published bundle `Def_SingletonLoopMatching`; the bundles `OAIW2LM000` and `OAIW2LM001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIW2LM004`.
-- source:
--   OpenAI, the Lean development OAI.Computability.LoopMatching (comparator challenge of OAI.LoopMatching.fullEndpoint), OpenAI Math Release, October 2026, https://github.com/openai/math (result family not identified here; see lean/formalization.yaml; paper: https://github.com/openai/math; Apache License 2.0); definitions carved from lean/OAI/Computability, lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_SingletonLoopMatching
import Definitions.Def_OAIW2LM000
import Definitions.Def_OAIW2LM001

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Model
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

namespace BinaryMatching

noncomputable def count (G : Input) : ℕ :=
  ∑ M : (completeGraph G.n).Matching, ∏ e∈M.val, multiplicity G e

end BinaryMatching

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_FiniteStack
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode

attribute [instance] Block.finite

namespace Steps
variable {r : ℕ} {L L' : Type} {code : L → Instr r (Option L)}

abbrev cfg (q : Option L) (s : Store r) :
    Turing.TM2.Cfg (fun _ : Fin r => Bool) L (Option Bool) := ⟨q,none,s⟩

theorem simulation {q s q' s' t} (h : Steps code q s q' s' t) :
    (fun o => o.bind (Turing.TM2.step (fun l => (code l).translate)))^[t]
      (some (cfg q s)) = some (cfg q' s') := by
  induction h with
  | refl => rfl
  | next q s q' s' t h ih =>
    rw [Function.iterate_succ_apply]
    simpa only [Option.bind_some,Turing.TM2.step,Instr.translate_step] using ih
end Steps

namespace Block
variable {r : ℕ}

def machine (b : Block r) (input output : Fin r) : Turing.FinTM2 where
  K := Fin r
  k₀ := input
  k₁ := output
  Γ _ := Bool
  Λ := b.Label
  main := b.entry
  σ := Option Bool
  initialState := none
  m l := (b.code l).translate

def machine_runs (b : Block r) (input output : Fin r) (s s' : List Bool) {t : ℕ}
    (h : b.Runs (Function.update (fun _ => []) input s)
      (Function.update (fun _ => []) output s') t) :
    Turing.TM2OutputsInTime (b.machine input output) s (some s') t := by
  refine ⟨⟨t,?_⟩,le_rfl⟩
  have hini : Turing.initList (b.machine input output) s =
      Steps.cfg (some b.entry) (Function.update (fun _ => []) input s) := by
    simp only [Turing.initList,machine,Steps.cfg]
    congr 1
    funext k
    by_cases hk : k=input
    · subst k; rfl
    · simp [Function.update,hk]
  have hout : Turing.haltList (b.machine input output) s' =
      Steps.cfg none (Function.update (fun _ => []) output s') := by
    simp only [Turing.haltList,machine,Steps.cfg]
    congr 1
    funext k
    by_cases hk : k=output
    · subst k; rfl
    · simp [Function.update,hk]
  change (fun o => o.bind (Turing.TM2.step (fun l => (b.code l).translate)))^[t]
    (some (Turing.initList (b.machine input output) s)) =
    some (Turing.haltList (b.machine input output) s')
  rw [hini,hout]
  exact h.simulation
end Block
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_StackRoutine
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Finset Polynomial

namespace Routine
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
  {ec : γ → List Bool} {f : α → β} {g : β → γ}

noncomputable def machine (p : Routine ea eb f) : Turing.TM2ComputableInPolyTime ea eb f where
  tm := p.block.machine 0 0
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := p.time
  outputsFun a := by
    let t := (p.correct a).choose
    have ht := (p.correct a).choose_spec.1
    have h := (p.correct a).choose_spec.2
    have hm := p.block.machine_runs 0 0 (ea a) (eb (f a)) h
    change Turing.TM2OutputsInTime (p.block.machine 0 0) (List.map id (ea a))
      (some (List.map id (eb (f a)))) (p.time.eval (ea a).length)
    rw [List.map_id_fun,List.map_id_fun]
    exact ⟨hm.toEvalsTo,hm.steps_le_m.trans ht⟩

end Routine
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_PolyCoding
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.BinaryMatching.StackCode.instCodingBits _root_.OAI.BinaryMatching.StackCode.instCodingInt _root_.OAI.BinaryMatching.StackCode.instCodingOption _root_.OAI.BinaryMatching.StackCode.instCodingSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
export Coding (encode)
instance instCodingUnit : Coding Unit := ⟨fun _ => []⟩
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_OrbitRoutine
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.BinaryMatching.StackCode.instCodingBits _root_.OAI.BinaryMatching.StackCode.instCodingInt _root_.OAI.BinaryMatching.StackCode.instCodingOption _root_.OAI.BinaryMatching.StackCode.instCodingSum
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

theorem iterateFrom (step : α → α) (hs : Poly step) (count : β → ℕ) (initial : β → α)
    (hc : Poly count) (hi : Poly initial) (P : Polynomial ℕ)
    (hb : ∀ b j,j≤count b → (encode (step^[j] (initial b))).length≤
      P.eval (encode (count b,initial b)).length) :
    Poly (fun b => step^[count b] (initial b)) := by
  let paired := (pair count initial hc hi).routine
  let setup : Routine encode (fun b => encode (count b,initial b)) (id : β → β) :=
    paired.reindex encode (fun b => encode (count b,initial b)) id id
      (fun _ => rfl) (fun _ => rfl)
  exact ⟨setup.comp (hs.routine.boundedIterate count initial P hb)⟩

end Poly
end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Contraction
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Contraction of tight odd cuts and gluing of perfect matchings and their laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

/-- Contraction of the complement of S to a new vertex. Edges retain identities;
only edges with both endpoints outside S are discarded. -/
def onSide (G : LooplessGraph V E) (S : Finset V) :
    LooplessGraph (Option {v // v ∈ S}) {e // G.left e ∈ S ∨ G.right e ∈ S} where
  left e := if h : G.left e.val ∈ S then some ⟨G.left e.val, h⟩ else none
  right e := if h : G.right e.val ∈ S then some ⟨G.right e.val, h⟩ else none
  loopless e := by
    dsimp
    split_ifs with hl hr
    · intro he
      have hv := Option.some.inj he
      exact G.loopless e.val (congrArg Subtype.val hv)
    · simp
    · simp
    · rename_i hr
      exact (e.property.elim hl hr).elim


def boundaryEdge (G : LooplessGraph V E) (S : Finset V) (M : (G.onSide S).Matching) :
    {e // G.left e ∈ S ∨ G.right e ∈ S} := Classical.choose (M.property none)

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem boundaryEdge_mem (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) : G.boundaryEdge S M ∈ M.val :=
  (Classical.choose_spec (M.property none)).1.1

def liftedEdges (G : LooplessGraph V E) (S : Finset V) (M : (G.onSide S).Matching) : Finset E :=
  M.val.image Subtype.val

end LooplessGraph

end MatchingEntropy

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

lemma tab_eq_ofFn {α : Type} (n : ℕ) (f : ℕ → α) :
    tab n f=List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp [tab]
  · intro i hi hi'
    simp [tab]

lemma range_eq_fin (n : ℕ) : List.range n=(List.finRange n).map Fin.val := by
  have h := tab_eq_ofFn n id
  simpa [tab,List.finRange,List.map_ofFn,Function.comp_def] using h

lemma tab_eq_rep {n : ℕ} {α : Type} (g : ℕ → α) (f : Fin n → α)
    (h : ∀ i,g i.val=f i) : tab n g=vectorRep f := by
  rw [tab_eq_ofFn]; congr 1; funext i; exact h i
lemma matrix_eq_rep {n : ℕ} {α : Type} (g : ℕ → ℕ → α) (f : Fin n → Fin n → α)
    (h : ∀ i j,g i.val j.val=f i j) : matrix n g=matrixRep f := by
  apply tab_eq_rep
  intro i
  exact tab_eq_rep _ _ (h i)

lemma empty_rep (n : ℕ) : empty n=cutRep (∅:Finset (Fin n)) := by
  simp [empty,cutRep,vectorRep]
lemma full_rep (n : ℕ) : full n=cutRep (univ:Finset (Fin n)) := by
  simp [full,cutRep,vectorRep]
lemma inter_rep {n : ℕ} (S T : Finset (Fin n)) :
    inter n (cutRep S) (cutRep T)=cutRep (S∩T) := by
  apply tab_eq_rep
  intro i
  simp
lemma compl_rep {n : ℕ} (S : Finset (Fin n)) : compl n (cutRep S)=cutRep Sᶜ := by
  apply tab_eq_rep
  intro i
  simp only [mem_rep,Finset.mem_compl,decide_not]
lemma cardinal_rep {n : ℕ} (S : Finset (Fin n)) : cardinal (cutRep S)=S.card := by
  unfold cardinal cutRep vectorRep
  have hh : List.ofFn (fun i : Fin n => decide (i∈S))=
    (List.finRange n).map (fun i => decide (i∈S)) := by
      simp [List.finRange,List.map_ofFn,Function.comp_def]
  rw [hh]
  rw [List.filter_map]
  simp only [List.length_map]
  rw [←List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  simp

lemma sum_tab {α : Type} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    (tab n f).sum=∑ i : Fin n,f i.val := by rw [tab_eq_ofFn,List.sum_ofFn]

end BinaryMatching.Raw
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_FeasibilityRepair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching
noncomputable section
open Finset MatchingEntropy
variable {n : ℕ}

def degreeCorrection (x : Pair n → ℝ) (e : Pair n) : ℝ :=
  let d := fun v => 1-(completeGraph n).degree x v
  (d e.val.1+d e.val.2)/((n:ℝ)-2)-(∑ v,d v)/(((n:ℝ)-2)*((n:ℝ)-1))

def uniform (n : ℕ) : Pair n → ℝ := fun _ => 1/((n:ℝ)-1)

end
end BinaryMatching
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

lemma guardedStep_eq {α : Type} [Coding α] [Inhabited α] (f : α → α) (B : ℕ) (a : α) (k : ℕ)
    (h : ∀ j,j≤k → (encode (f^[j] a)).length≤B) :
    (guardedStep f)^[k] (B,a)=(B,f^[k] a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih (fun j hj => h j (by omega))]
    have hh := h (k+1) le_rfl
    rw [Function.iterate_succ_apply'] at hh
    simp only [guardedStep,ite_eq_left hh,Function.iterate_succ_apply']

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

lemma capDouble_start (b k : ℕ) : (capDouble^[k] (b,min b 1))=(b,min b (2^k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih]
    change (b,min b (2*min b (2^k)))=(b,min b (2^(k+1)))
    rw [pow_succ]
    congr 1
    omega

lemma cappedPow2_eq (b k : ℕ) : cappedPow2 b k=min b (2^k) := by
  simp only [cappedPow2,capDouble_start]
lemma cappedPow2_of_le (b k : ℕ) (h : 2^k≤b) : cappedPow2 b k=2^k := by
  rw [cappedPow2_eq,min_eq_right h]

end BinaryMatching.StackCode
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawOptimizerData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw.Optimize
open Algorithm Finset StackCode

abbrev Row := Matrix ℤ × ℤ
abbrev IntState := Matrix ℤ × Option ℤ
structure Params where
  n : ℕ
  q : ℕ
  k : ℕ
  L : ℕ
  D : ℕ
  M : ℕ
  pow : ℕ
  beta : Matrix ℤ
  deriving Inhabited
abbrev ParamData := ℕ×(ℕ×(ℕ×(ℕ×(ℕ×(ℕ×(ℕ×Matrix ℤ))))))
def Params.repr (p : Params) : ParamData := (p.n,(p.q,(p.k,(p.L,(p.D,(p.M,(p.pow,p.beta)))))))
instance instCodingParams : Coding Params := ⟨fun p => encode p.repr⟩
def Params.ofData (z : ParamData) : Params := ⟨z.1,z.2.1,z.2.2.1,z.2.2.2.1,z.2.2.2.2.1,z.2.2.2.2.2.1,z.2.2.2.2.2.2.1,z.2.2.2.2.2.2.2⟩

@[simp] lemma Params.ofData_repr (p : Params) : Params.ofData p.repr=p := rfl

def tableRep {n : ℕ} (a : Table n ℤ) : Matrix ℤ := matrixRep (fun i j => a[i][j])
def rowRep {n : ℕ} (r : Affine n) : Row := (tableRep (toTable r.coeff),r.constant)
def stateRep {n : ℕ} (s : IntegralState n) : IntState := (tableRep s.numerators,s.best)
def params (G : Input) : Params := ⟨G.n,q G.n,K G.n,L G,D₀ G,M₀ G,2^(K G.n),tableRep (toTable (Algorithm.beta G))⟩

def upperSum (n : ℕ) (f : ℕ → ℕ → ℤ) : ℤ :=
  (tab n (fun i => (tab n (fun j => if i<j then f i j else 0)).sum)).sum

lemma upperSum_rep {n : ℕ} (f : Pair n → ℤ) (g : ℕ → ℕ → ℤ)
    (h : ∀ e : Pair n,g e.val.1.val e.val.2.val=f e) : upperSum n g=∑ e,f e := by
  unfold upperSum
  rw [sum_tab]
  simp_rw [sum_tab]
  have hh : ∀ i j : Fin n,(if i.val<j.val then g i.val j.val else 0)=
      if h' : i<j then f ⟨(i,j),h'⟩ else 0 := by
    intro i j
    by_cases hij : i<j
    · simp only [dite_eq_left hij,show i.val<j.val from hij,ite_true]
      exact h ⟨(i,j),hij⟩
    · simp only [dite_eq_right hij,show ¬i.val<j.val from hij,ite_false]
  simp_rw [hh]
  rw [←Fintype.sum_prod_type (f := fun ij : Fin n×Fin n => if h' : ij.1 < ij.2 then f ⟨ij,h'⟩ else 0)]
  symm
  apply Fintype.sum_of_injective (fun e : Pair n => e.val) Subtype.val_injective f _
  · intro ij hij
    by_cases h' : ij.1 < ij.2
    · exact False.elim (hij ⟨⟨ij,h'⟩,rfl⟩)
    · simp only [dite_eq_right h']
  · intro e
    simp only [dite_eq_left e.property]

lemma get_tableRep {n : ℕ} (a : Table n ℤ) (i j : Fin n) : get (tableRep a) i.val j.val=a[i][j] :=
  get_rep _ _ _
lemma get_rowRep {n : ℕ} (r : Affine n) (e : Pair n) : get (rowRep r).1 e.val.1.val e.val.2.val=r.coeff e := by
  rw [rowRep,get_tableRep]
  exact at_toTable _ e
lemma get_beta (G : Input) (e : Pair G.n) : get (params G).beta e.val.1.val e.val.2.val=Algorithm.beta G e := by
  change get (tableRep (toTable (Algorithm.beta G))) e.val.1.val e.val.2.val=_
  rw [get_tableRep]
  exact at_toTable _ e

def rowNumerator (D : ℕ) (a : Matrix ℤ) (r : Row) : ℤ :=
  upperSum a.length (fun i j => get r.1 i j*get a i j)+r.2*D
lemma tableRep_length {n : ℕ} (a : Table n ℤ) : (tableRep a).length=n := by simp [tableRep,matrixRep,vectorRep]
lemma rowNumerator_rep {n : ℕ} (D : ℕ) (a : Table n ℤ) (r : Affine n) :
    rowNumerator D (tableRep a) (rowRep r)=Algorithm.rowNumerator D a r := by
  unfold rowNumerator Algorithm.rowNumerator
  rw [tableRep_length]
  congr 1
  apply upperSum_rep
  intro e
  rw [get_rowRep,get_tableRep]
  rfl

def pieceNumerator (k D pow : ℕ) (a : ℤ) (j : ℕ) : ℤ :=
  indexedSlope k j*a*pow+if j<k then (D:ℤ)*(cappedPow2 pow (k-j):ℕ) else 0
lemma pieceNumerator_rep (k D : ℕ) (a : ℤ) (j : ℕ) :
    pieceNumerator k D (2^k) a j=Algorithm.pieceNumerator k D a j := by
  have hp : 2^(k-j)≤2^k := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  simp only [pieceNumerator,cappedPow2_of_le _ _ hp,Algorithm.pieceNumerator,
    indexedSlope,indexedPiece]
  split_ifs <;> push_cast <;> rfl

attribute [local instance] OAI.BinaryMatching.Raw.Optimize.instPreorderInt_solutions
def selectedIndex (k D pow : ℕ) (a : ℤ) : ℕ :=
  ((List.range (k+1)).argmin (pieceNumerator k D pow a)).getD k
lemma selectedIndex_rep (k D : ℕ) (a : ℤ) : selectedIndex k D (2^k) a=Algorithm.selectedIndex k D a := by
  have hf : pieceNumerator k D (2^k) a=Algorithm.pieceNumerator k D a := funext (pieceNumerator_rep k D a)
  rw [selectedIndex,Algorithm.selectedIndex,hf]
def scaledPsi (p : Params) (a : ℤ) : ℤ := pieceNumerator p.k p.D p.pow a (selectedIndex p.k p.D p.pow a)
def scaledSlope (p : Params) (a : ℤ) : ℤ := indexedSlope p.k (selectedIndex p.k p.D p.pow a)
lemma scaledPsi_rep (G : Input) (a : ℤ) : scaledPsi (params G) a=Algorithm.scaledPsi (K G.n) (D₀ G) a := by
  simp only [scaledPsi,params,selectedIndex_rep,pieceNumerator_rep,Algorithm.scaledPsi]
lemma scaledSlope_rep (G : Input) (a : ℤ) : scaledSlope (params G) a=Algorithm.scaledSlope (K G.n) (D₀ G) a := by
  simp only [scaledSlope,params,selectedIndex_rep,Algorithm.scaledSlope,indexedSlope,indexedPiece]
  split_ifs <;> rfl
end BinaryMatching.Raw.Optimize
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

lemma residual_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (b : UnitFlow.Matrix (Fin n)) (i j : Fin n) :
    residual (matrixRep c) (matrixRep b) i.val j.val=decide (UnitMincut.residual c b i j) := by
  simp only [residual,UnitMincut.residual,get_rep]
  rfl

lemma initial_rep {n : ℕ} (a : Fin n) : initial n a.val=pathRep (ResidualSearch.initial a) := by
  apply tab_eq_rep
  intro v
  simp only [ResidualSearch.initial]
  by_cases hv : v=a
  · simp [hv]
  · have hval : v.val≠a.val := fun h => hv (Fin.ext h)
    simp [hv,hval]

lemma predecessor_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (b : UnitFlow.Matrix (Fin n))
    (p : ResidualSearch.Table n) (v : Fin n) :
    predecessor n (matrixRep c) (matrixRep b) (pathRep p) v.val=
      (ResidualSearch.predecessor (UnitMincut.residual c b) p v).map Fin.val := by
  unfold predecessor ResidualSearch.predecessor
  rw [range_eq_fin,List.find?_map]
  congr 1
  congr 1
  funext u
  simp only [Function.comp_apply,residual_rep,nth_pathRep,Option.isSome_map]

lemma pathStep_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (b : UnitFlow.Matrix (Fin n))
    (p : ResidualSearch.Table n) :
    pathStep n (matrixRep c) (matrixRep b) (pathRep p)=
      pathRep (ResidualSearch.step (UnitMincut.residual c b) p) := by
  apply tab_eq_rep
  intro v
  rw [nth_pathRep]
  simp only [ResidualSearch.step]
  cases hp : p v with
  | some l => rfl
  | none =>
    simp only [Option.map_none,predecessor_rep]
    cases hu : ResidualSearch.predecessor (UnitMincut.residual c b) p v with
    | none => rfl
    | some u =>
      simp only [Option.map_some,nth_pathRep,Option.map_map]
      rfl

lemma search_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (b : UnitFlow.Matrix (Fin n))
    (a : Fin n) (k : ℕ) : search n (matrixRep c) (matrixRep b) a.val k=
      pathRep (ResidualSearch.search (UnitMincut.residual c b) a k) := by
  induction k with
  | zero => exact initial_rep a
  | succ k ih =>
    simp only [search,Function.iterate_succ_apply'] at *
    rw [ih,pathStep_rep]
    rfl

lemma reached_rep {n : ℕ} (p : ResidualSearch.Table n) :
    reached n (pathRep p)=cutRep (ResidualSearch.reached p) := by
  apply tab_eq_rep
  intro v
  simp only [nth_pathRep,Option.isSome_map,ResidualSearch.mem_reached]
  cases p v <;> rfl

lemma pathFlow_rep {n : ℕ} (p : List (Fin n)) (i j : Fin n) :
    pathFlow (p.map Fin.val) i.val j.val=UnitFlow.pathFlow p i j := by
  induction p using List.twoStepInduction with
  | nil => simp [pathFlow,UnitFlow.pathFlow]
  | singleton v => simp [pathFlow,UnitFlow.pathFlow]
  | cons_cons v u p _ ih =>
    have hv : (i.val=v.val)↔i=v := Fin.ext_iff.symm
    have hu : (i.val=u.val)↔i=u := Fin.ext_iff.symm
    have jv : (j.val=v.val)↔j=v := Fin.ext_iff.symm
    have ju : (j.val=u.val)↔j=u := Fin.ext_iff.symm
    simp only [pathFlow,List.map_cons,List.tail_cons,List.zip_cons_cons,List.sum_cons,
      UnitFlow.pathFlow,UnitFlow.arc,hv,hu,jv,ju] at *
    rw [ih]
    omega
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

lemma pathStep_size (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (p : Paths) (M : ℕ)
    (hp : PathSize p M) : PathSize (pathStep n c b p) (M+4*n+2) := by
  intro q hq
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hq
  have hvn := List.mem_range.mp hv
  have hsize (u : ℕ) : (encode (nth p u)).length≤M :=
    nth_code_bound p u M (Nat.zero_le M) hp
  change (encode (match nth p v with
    | some l => some l
    | none => match predecessor n c b p v with
      | none => none
      | some u => (nth p u).map (fun l => v::l))).length≤_
  cases h : nth p v with
  | some l => dsimp only; have hh := hsize v; rw [h] at hh; omega
  | none =>
    cases hu : predecessor n c b p v with
    | none => simp only [code_option_none,List.length_nil]; omega
    | some u =>
      dsimp only
      have hh := option_prepend_bound v (nth p u)
      have he := hsize u
      omega

lemma search_size (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (a k : ℕ) :
    PathSize (search n c b a k) (4*a+3+k*(4*n+2)) := by
  induction k with
  | zero => simpa only [search,Function.iterate_zero,id_eq,Nat.zero_mul,Nat.add_zero] using initial_size n a
  | succ k ih =>
    have hh := pathStep_size n c b _ _ ih
    simpa only [search,Function.iterate_succ_apply',Nat.add_mul,Nat.one_mul,Nat.add_assoc] using hh

lemma search_code_bound (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (a k : ℕ) :
    (encode (search n c b a k)).length≤n*(2*(4*a+3+k*(4*n+2))+1) := by
  have h := list_code_bound _ _ (search_size n c b a k)
  rwa [search_length] at h

end BinaryMatching.Raw
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

namespace Compiler
open StackCode.Poly

@[fun_prop] theorem search_poly : Poly (fun z : SearchContext×ℕ =>
    search z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2) := by
  have hi := Poly.iterateFrom searchStep searchStep_poly Prod.snd searchInitial (by fun_prop)
    searchInitial_poly (100*(X+1)^3) (by
      intro z j hj
      rw [searchStep_iterate]
      let N := (encode (z.2,searchInitial z)).length
      have hctx : (encode z.1).length≤N := by
        simp only [N,searchInitial,code_pair_length,code_nat_length]; omega
      have hn : z.1.1≤N := by
        have := (pair_left_le z.1).trans hctx
        simpa only [code_nat_length] using this
      have ha : z.1.2.2.2≤N := by
        have := (pair_right_le z.1.2.2).trans ((pair_right_le z.1.2).trans ((pair_right_le z.1).trans hctx))
        simpa only [code_nat_length] using this
      have hk : j≤N := by
        simp only [N,code_pair_length,code_nat_length]; omega
      have hb := search_code_bound z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 j
      have hm : z.1.1*(2*(4*z.1.2.2.2+3+j*(4*z.1.1+2))+1)≤
          N*(2*(4*N+3+N*(4*N+2))+1) := by gcongr
      simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
      change (encode (z.1,search z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 j)).length≤100*(N+1)^3
      rw [code_pair_length]
      have hbb := hb.trans hm
      nlinarith)
  have h := Poly.second _ hi
  exact h.congr (fun z => by rw [searchStep_iterate])

end Compiler
end BinaryMatching.Raw
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw
open Finset

def augment (n : ℕ) (c : Matrix ℕ) (a z : ℕ) (b : Matrix ℤ) : Matrix ℤ :=
  match nth (search n c b a n) z with
  | none => b
  | some p => matrix n (fun i j => get b i j+pathFlow p i j)
def flow (n : ℕ) (c : Matrix ℕ) (a z k : ℕ) : Matrix ℤ :=
  (augment n c a z)^[k] (matrix n (fun _ _ => 0))
def sourceCapacity (n : ℕ) (c : Matrix ℕ) (a : ℕ) : ℕ := (tab n (get c a)).sum
def mincut (n : ℕ) (c : Matrix ℕ) (a z : ℕ) : Cut :=
  reached n (search n c (flow n c a z (sourceCapacity n c a)) a n)
def cutCapacity (n : ℕ) (c : Matrix ℕ) (S : Cut) : ℕ :=
  (tab n (fun i => (tab n (fun j => if mem S i && !mem S j then get c i j else 0)).sum)).sum

def pairCuts (n : ℕ) (c : Matrix ℕ) (U : Cut) : List Cut :=
  ((pairs n).filter (fun az => mem U az.1 && mem U az.2 && decide (az.1≠az.2))).map
    (fun az => mincut n c az.1 az.2)
def terminalCut (n : ℕ) (c : Matrix ℕ) (U : Cut) : Cut :=
  ((pairCuts n c U).argmin (cutCapacity n c)).getD (empty n)

lemma augment_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (a z : Fin n) (b : UnitFlow.Matrix (Fin n)) :
    augment n (matrixRep c) a.val z.val (matrixRep b)=matrixRep (UnitMincut.augment c a z b) := by
  unfold augment
  rw [search_rep,nth_pathRep]
  unfold UnitMincut.augment
  cases h : ResidualSearch.search (UnitMincut.residual c b) a n z with
  | none => rfl
  | some p =>
    simp only [Option.map_some]
    apply matrix_eq_rep
    intro i j
    simp only [get_rep,pathFlow_rep]
lemma flow_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (a z : Fin n) (k : ℕ) :
    flow n (matrixRep c) a.val z.val k=matrixRep (UnitMincut.iterate c a z k) := by
  induction k with
  | zero => exact matrix_eq_rep _ _ (fun _ _ => rfl)
  | succ k ih =>
    simp only [flow,Function.iterate_succ_apply'] at *
    rw [ih,augment_rep]
    rfl
lemma sourceCapacity_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (a : Fin n) :
    sourceCapacity n (matrixRep c) a.val=UnitMincut.sourceCapacity c a := by
  simp [sourceCapacity,sum_tab,UnitMincut.sourceCapacity]
lemma mincut_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (a z : Fin n) :
    mincut n (matrixRep c) a.val z.val=cutRep (UnitMincut.mincut c a z) := by
  simp only [mincut,sourceCapacity_rep,flow_rep,search_rep,reached_rep,UnitMincut.mincut]
lemma cutCapacity_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (S : Finset (Fin n)) :
    cutCapacity n (matrixRep c) (cutRep S)=UnitFlow.cutCapacity c S := by
  simp only [cutCapacity,sum_tab,mem_rep,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,
    decide_eq_false_iff_not,get_rep]
  simp only [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp only [Finset.sum_ite_mem,Finset.univ_inter]
  unfold UnitFlow.cutCapacity
  apply Finset.sum_congr rfl
  intro i hi
  rw [show Sᶜ=univ.filter (fun j => j∉S) by ext; simp]
  simp only [Finset.sum_filter]

lemma pairs_rep (n : ℕ) : pairs n=(((List.finRange n).product (List.finRange n)).map
    (fun az => (az.1.val,az.2.val))) := by
  simp only [pairs,List.product,range_eq_fin,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]

lemma pairCuts_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) :
    pairCuts n (matrixRep c) (cutRep U)=(TerminalMincut.pairCuts c U).map cutRep := by
  unfold pairCuts TerminalMincut.pairCuts
  rw [pairs_rep,List.filter_map,List.map_map,List.map_map]
  have hp : (fun az : Fin n×Fin n => mem (cutRep U) az.1.val && mem (cutRep U) az.2.val &&
      decide (az.1.val≠az.2.val))=(fun az => decide (az.1∈U ∧ az.2∈U ∧ az.1≠az.2)) := by
    funext az
    simp [Fin.ext_iff,Bool.and_assoc]
  simp only [Function.comp_def]
  rw [hp]
  apply List.map_congr_left
  intro az haz
  exact mincut_rep c az.1 az.2

lemma terminalCut_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) :
    terminalCut n (matrixRep c) (cutRep U)=cutRep (TerminalMincut.terminalCut c U) := by
  unfold terminalCut TerminalMincut.terminalCut
  rw [pairCuts_rep,argmin_map_eq]
  have hg : cutCapacity n (matrixRep c) ∘ cutRep=UnitFlow.cutCapacity c := by
    funext S; exact cutCapacity_rep c S
  rw [hg,empty_rep]
  cases h : (TerminalMincut.pairCuts c U).argmin (UnitFlow.cutCapacity c) <;> rfl

end BinaryMatching.Raw
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawFlowSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw
open StackCode

lemma nth_property {α : Type} [Inhabited α] (P : α → Prop) (l : List α) (i : ℕ)
    (hd : P default) (h : ∀ a∈l,P a) : P (nth l i) := by
  unfold nth
  cases hi : l[i]? with
  | none => exact hd
  | some a => exact h a (List.mem_of_getElem? hi)

def MatrixBound (b : Matrix ℤ) (M : ℕ) : Prop := ∀ row∈b,∀ v∈row,v.natAbs≤M

def Square {α : Type} (n : ℕ) (b : Matrix α) : Prop := b.length=n ∧ ∀ row∈b,row.length=n

lemma matrix_square {α : Type} (n : ℕ) (f : ℕ → ℕ → α) : Square n (matrix n f) := by
  constructor
  · simp [matrix,tab]
  · intro row hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    simp [tab]

lemma matrix_bound (n M : ℕ) (f : ℕ → ℕ → ℤ) (h : ∀ i,i<n → ∀ j,j<n → (f i j).natAbs≤M) :
    MatrixBound (matrix n f) M := by
  intro row hr v hv
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
  exact h _ (List.mem_range.mp hi) _ (List.mem_range.mp hj)

lemma get_abs_bound (b : Matrix ℤ) (M : ℕ) (hb : MatrixBound b M) (i j : ℕ) :
    (get b i j).natAbs≤M := by
  apply nth_property (fun z : ℤ => z.natAbs≤M)
  · exact Nat.zero_le _
  · apply nth_property (fun row : List ℤ => ∀ v∈row,v.natAbs≤M)
    · intro v hv; cases hv
    · exact hb

lemma matrix_bound_code (n M : ℕ) (b : Matrix ℤ) (hs : Square n b) (hb : MatrixBound b M) :
    (encode b).length≤n*(2*(n*(2*(M+3)+1))+1) := by
  have hh := list_code_bound b (n*(2*(M+3)+1)) (by
    intro row hr
    have hrow := list_code_bound row (M+3) (by
      intro v hv
      rw [code_int_length]
      have he := hb row hr v hv
      omega)
    rwa [hs.2 row hr] at hrow)
  rwa [hs.1] at hh

lemma search_path_bound (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (a z : ℕ) (p : List ℕ)
    (hp : nth (search n c b a n) z=some p) : p.length≤4*a+3+n*(4*n+2) := by
  have hh := nth_code_bound (search n c b a n) z (4*a+3+n*(4*n+2))
    (Nat.zero_le _) (search_size n c b a n)
  rw [hp,code_option_some] at hh
  have hl := list_length_le_code p
  omega

lemma augment_bound (n : ℕ) (c : Matrix ℕ) (a z : ℕ) (b : Matrix ℤ) (M : ℕ)
    (hb : MatrixBound b M) : MatrixBound (augment n c a z b) (M+(4*a+3+n*(4*n+2))) := by
  unfold augment
  cases hp : nth (search n c b a n) z with
  | none => intro row hr v hv; have := hb row hr v hv; omega
  | some p =>
    apply matrix_bound
    intro i hi j hj
    have hh := Int.natAbs_add_le (get b i j) (pathFlow p i j)
    have h₁ := get_abs_bound b M hb i j
    have h₂ := (pathFlow_abs p i j).trans (search_path_bound n c b a z p hp)
    omega

lemma augment_square (n : ℕ) (c : Matrix ℕ) (a z : ℕ) (b : Matrix ℤ)
    (hb : Square n b) : Square n (augment n c a z b) := by
  unfold augment
  split
  · exact hb
  · exact matrix_square _ _

lemma flow_bound (n : ℕ) (c : Matrix ℕ) (a z k : ℕ) :
    MatrixBound (flow n c a z k) (k*(4*a+3+n*(4*n+2))) := by
  induction k with
  | zero => simpa only [flow,Function.iterate_zero,Function.id_def,Nat.zero_mul] using matrix_bound n 0 (fun _ _ => 0) (fun _ _ _ _ => le_rfl)
  | succ k ih =>
    have hh := augment_bound n c a z _ _ ih
    simpa only [flow,Function.iterate_succ_apply',Nat.add_mul,Nat.one_mul] using hh

lemma flow_square (n : ℕ) (c : Matrix ℕ) (a z k : ℕ) : Square n (flow n c a z k) := by
  induction k with
  | zero => exact matrix_square _ _
  | succ k ih => simpa only [flow,Function.iterate_succ_apply'] using augment_square n c a z _ ih
lemma flow_code_bound (n : ℕ) (c : Matrix ℕ) (a z k : ℕ) :
    (encode (flow n c a z k)).length≤n*(2*(n*(2*(k*(4*a+3+n*(4*n+2))+3)+1))+1) :=
  matrix_bound_code _ _ _ (flow_square n c a z k) (flow_bound n c a z k)
end BinaryMatching.Raw
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawFlowCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw
open StackCode Polynomial
abbrev FlowContext := ℕ×(Matrix ℕ×(ℕ×ℕ))
abbrev FlowState := FlowContext×Matrix ℤ

def flowStep (s : FlowState) : FlowState :=
  (s.1,augment s.1.1 s.1.2.1 s.1.2.2.1 s.1.2.2.2 s.2)
def flowInitial (z : FlowContext×ℕ) : FlowState :=
  (z.1,matrix z.1.1 (fun _ _ => 0))
lemma flowStep_iterate (z : FlowContext×ℕ) (j : ℕ) :
    flowStep^[j] (flowInitial z)=(z.1,flow z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 j) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply',ih,flowStep,flow]

namespace Compiler
open StackCode.Poly
@[fun_prop] theorem reached_poly : Poly (fun z : ℕ×Paths => reached z.1 z.2) := by
  unfold reached
  exact Poly.rawTab Prod.fst (fun z : (ℕ×Paths)×ℕ => (nth z.1.2 z.2).isSome)
    (by fun_prop) (by fun_prop)
@[fun_prop] theorem pathFlow_poly : Poly (fun z : List ℕ×(ℕ×ℕ) => pathFlow z.1 z.2.1 z.2.2) := by
  unfold pathFlow
  have h : Poly (fun z : (List ℕ×(ℕ×ℕ))×(ℕ×ℕ) =>
      ((if decide (z.1.2.1=z.2.2) && decide (z.1.2.2=z.2.1) then 1 else 0)-
       (if decide (z.1.2.1=z.2.1) && decide (z.1.2.2=z.2.2) then 1 else 0):ℤ)) := by fun_prop
  have hm := Poly.mapWith (fun z : List ℕ×(ℕ×ℕ) => z.1.zip z.1.tail) _ (by fun_prop) h
  exact (Poly.comp List.sum _ Poly.listIntSum hm).congr (fun z => by simp only [Bool.and_eq_true,decide_eq_true_eq])
@[fun_prop] theorem augment_poly : Poly (fun z : FlowState =>
    augment z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2) := by
  have hp : Poly (fun z : FlowState => nth (search z.1.1 z.1.2.1 z.2 z.1.2.2.1 z.1.1) z.1.2.2.2) := by
    apply Poly.rawNth
    · exact Poly.comp _ (fun z : FlowState => ((z.1.1,(z.1.2.1,(z.2,z.1.2.2.1))),z.1.1))
        search_poly (by fun_prop)
    · fun_prop
  have hm : Poly (fun z : FlowState×List ℕ => matrix z.1.1.1 (fun i j => get z.1.2 i j+pathFlow z.2 i j)) := by
    apply Poly.rawMatrix (fun z : FlowState×List ℕ => z.1.1.1)
      (fun z : ((FlowState×List ℕ)×ℕ)×ℕ => get z.1.1.1.2 z.1.2 z.2+pathFlow z.1.1.2 z.1.2 z.2)
    · fun_prop
    · have hp := Poly.comp _ (fun z : ((FlowState×List ℕ)×ℕ)×ℕ => (z.1.1.2,(z.1.2,z.2)))
        pathFlow_poly (by fun_prop)
      fun_prop
  have h := Poly.optionCasesWith
    (fun z : FlowState => nth (search z.1.1 z.1.2.1 z.2 z.1.2.2.1 z.1.1) z.1.2.2.2)
    Prod.snd
    (fun z => matrix z.1.1.1 (fun i j => get z.1.2 i j+pathFlow z.2 i j)) hp (by fun_prop) hm
  exact h.congr (fun z => by unfold augment; cases nth (search z.1.1 z.1.2.1 z.2 z.1.2.2.1 z.1.1) z.1.2.2.2 <;> rfl)
@[fun_prop] theorem flowStep_poly : Poly flowStep := Poly.pair _ _ (by fun_prop) augment_poly
@[fun_prop] theorem flowInitial_poly : Poly flowInitial := by
  unfold flowInitial
  apply Poly.pair
  · fun_prop
  · exact Poly.rawMatrix (fun z : FlowContext×ℕ => z.1.1) (fun _ => (0:ℤ)) (by fun_prop) (by fun_prop)
@[fun_prop] theorem flow_poly : Poly (fun z : FlowContext×ℕ =>
    flow z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2) := by
  have hi := Poly.iterateFrom flowStep flowStep_poly Prod.snd flowInitial (by fun_prop)
    flowInitial_poly (1000*(X+1)^5) (by
      intro z j hj
      rw [flowStep_iterate]
      let N := (encode (z.2,flowInitial z)).length
      have hctx : (encode z.1).length≤N := by
        simp only [N,flowInitial,code_pair_length,code_nat_length]; omega
      have hn : z.1.1≤N := by
        have := (pair_left_le z.1).trans hctx
        simpa only [code_nat_length] using this
      have ha : z.1.2.2.1≤N := by
        have := (pair_left_le z.1.2.2).trans ((pair_right_le z.1.2).trans ((pair_right_le z.1).trans hctx))
        simpa only [code_nat_length] using this
      have hk : j≤N := by
        simp only [N,code_pair_length,code_nat_length]; omega
      have hb := flow_code_bound z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 j
      have hm : z.1.1*(2*(z.1.1*(2*(j*(4*z.1.2.2.1+3+z.1.1*(4*z.1.1+2))+3)+1))+1)≤
          N*(2*(N*(2*(N*(4*N+3+N*(4*N+2))+3)+1))+1) := by gcongr
      simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
      change (encode (z.1,flow z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 j)).length≤1000*(N+1)^5
      rw [code_pair_length]
      dsimp only
      have hbb := hb.trans hm
      calc
        _ ≤ 2*N+N*(2*(N*(2*(N*(4*N+3+N*(4*N+2))+3)+1))+1)+1 := by omega
        _ ≤ 1000*(N+1)^5 := by ring_nf; omega)
  exact (Poly.second _ hi).congr (fun z => by rw [flowStep_iterate])
@[fun_prop] theorem sourceCapacity_poly : Poly (fun z : ℕ×(Matrix ℕ×ℕ) => sourceCapacity z.1 z.2.1 z.2.2) := by
  unfold sourceCapacity
  apply Poly.comp List.sum _ Poly.listNatSum
  exact Poly.rawTab Prod.fst (fun z : (ℕ×(Matrix ℕ×ℕ))×ℕ => get z.1.2.1 z.1.2.2 z.2)
    (by fun_prop) (by fun_prop)
@[fun_prop] theorem mincut_poly : Poly (fun z : FlowContext => mincut z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold mincut
  have hs : Poly (fun z : FlowContext => sourceCapacity z.1 z.2.1 z.2.2.1) :=
    Poly.comp _ (fun z : FlowContext => (z.1,(z.2.1,z.2.2.1))) sourceCapacity_poly (by fun_prop)
  have hf : Poly (fun z : FlowContext => flow z.1 z.2.1 z.2.2.1 z.2.2.2 (sourceCapacity z.1 z.2.1 z.2.2.1)) :=
    Poly.comp _ (fun z : FlowContext => (z,sourceCapacity z.1 z.2.1 z.2.2.1)) flow_poly (by fun_prop)
  have hsearch := Poly.comp _ (fun z : FlowContext =>
    ((z.1,(z.2.1,(flow z.1 z.2.1 z.2.2.1 z.2.2.2 (sourceCapacity z.1 z.2.1 z.2.2.1),z.2.2.1))),z.1)) search_poly (by fun_prop)
  exact Poly.comp _ (fun z : FlowContext =>
    (z.1,search z.1 z.2.1 (flow z.1 z.2.1 z.2.2.1 z.2.2.2 (sourceCapacity z.1 z.2.1 z.2.2.1)) z.2.2.1 z.1)) reached_poly (by fun_prop)
@[fun_prop] theorem cutCapacity_poly : Poly (fun z : ℕ×(Matrix ℕ×Cut) => cutCapacity z.1 z.2.1 z.2.2) := by
  unfold cutCapacity
  apply Poly.comp List.sum _ Poly.listNatSum
  apply Poly.rawTab Prod.fst (fun z : (ℕ×(Matrix ℕ×Cut))×ℕ =>
    (tab z.1.1 (fun j => if mem z.1.2.2 z.2 && !mem z.1.2.2 j then get z.1.2.1 z.2 j else 0)).sum)
  · fun_prop
  · apply Poly.comp List.sum _ Poly.listNatSum
    apply Poly.rawTab (fun z : (ℕ×(Matrix ℕ×Cut))×ℕ => z.1.1)
      (fun z : ((ℕ×(Matrix ℕ×Cut))×ℕ)×ℕ => if mem z.1.1.2.2 z.1.2 && !mem z.1.1.2.2 z.2 then
        get z.1.1.2.1 z.1.2 z.2 else 0)
    · fun_prop
    · fun_prop
@[fun_prop] theorem pairs_poly : Poly pairs := by
  unfold pairs
  apply Poly.flatMapWith List.range (fun z : ℕ×ℕ => (List.range z.1).map (fun j => (z.2,j))) (by fun_prop)
  exact Poly.mapWith (fun z : ℕ×ℕ => List.range z.1) (fun z : (ℕ×ℕ)×ℕ => (z.1.2,z.2)) (by fun_prop) (by fun_prop)
@[fun_prop] theorem pairCuts_poly : Poly (fun z : ℕ×(Matrix ℕ×Cut) => pairCuts z.1 z.2.1 z.2.2) := by
  unfold pairCuts
  apply Poly.mapWith _ (fun z : (ℕ×(Matrix ℕ×Cut))×(ℕ×ℕ) => mincut z.1.1 z.1.2.1 z.2.1 z.2.2)
  · apply Poly.filterWith _ (fun z : (ℕ×(Matrix ℕ×Cut))×(ℕ×ℕ) =>
      mem z.1.2.2 z.2.1 && mem z.1.2.2 z.2.2 && decide (z.2.1≠z.2.2))
    · fun_prop
    · have h : Poly (fun z : (ℕ×(Matrix ℕ×Cut))×(ℕ×ℕ) =>
        mem z.1.2.2 z.2.1 && mem z.1.2.2 z.2.2 && !decide (z.2.1=z.2.2)) := by fun_prop
      exact h.congr (fun z => by simp)
  · exact Poly.comp _ (fun z : (ℕ×(Matrix ℕ×Cut))×(ℕ×ℕ) => (z.1.1,(z.1.2.1,z.2))) mincut_poly (by fun_prop)
@[fun_prop] theorem terminalCut_poly : Poly (fun z : ℕ×(Matrix ℕ×Cut) => terminalCut z.1 z.2.1 z.2.2) := by
  unfold terminalCut
  have hf := Poly.listArgminParam Poly.natLT
    (fun z : (ℕ×Matrix ℕ)×Cut => cutCapacity z.1.1 z.1.2 z.2)
    (Poly.comp _ (fun z : (ℕ×Matrix ℕ)×Cut => (z.1.1,(z.1.2,z.2))) cutCapacity_poly (by fun_prop))
  have ha := Poly.comp _ (fun z : ℕ×(Matrix ℕ×Cut) => ((z.1,z.2.1),pairCuts z.1 z.2.1 z.2.2)) hf (by fun_prop)
  have h : Poly (fun z : ℕ×(Matrix ℕ×Cut) => if ((pairCuts z.1 z.2.1 z.2.2).argmin (cutCapacity z.1 z.2.1)).isSome then
      ((pairCuts z.1 z.2.1 z.2.2).argmin (cutCapacity z.1 z.2.1)).getD default else empty z.1) := by fun_prop
  exact h.congr (fun z => by cases (pairCuts z.1 z.2.1 z.2.2).argmin (cutCapacity z.1 z.2.1) <;> rfl)
end Compiler
end BinaryMatching.Raw
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw
open Finset

def outside (n : ℕ) (A : Cut) : Option ℕ := (List.range n).find? (fun i => !mem A i)
def contractMap (A : Cut) (r i : ℕ) : ℕ := if mem A i then i else r
def contract (n : ℕ) (c : Matrix ℕ) (A : Cut) (r : ℕ) : Matrix ℕ :=
  matrix n (fun i j => if i=j then 0 else
    (tab n (fun u => (tab n (fun v =>
      if contractMap A r u=i ∧ contractMap A r v=j then get c u v else 0)).sum)).sum)
def lift (n : ℕ) (A : Cut) (r : ℕ) (S : Cut) : Cut :=
  tab n (fun i => mem S (contractMap A r i))
def cheaper (n : ℕ) (c : Matrix ℕ) (S T : Cut) : Cut :=
  if cutCapacity n c S≤cutCapacity n c T then S else T

lemma outside_rep {n : ℕ} (A : Finset (Fin n)) :
    outside n (cutRep A)=(OddMincut.outside A).map Fin.val := by
  unfold outside OddMincut.outside
  rw [range_eq_fin,List.find?_map]
  congr 1
  congr 1
  funext i
  simp only [Function.comp_apply,mem_rep,decide_not]

lemma contractMap_rep {n : ℕ} (A : Finset (Fin n)) (r i : Fin n) :
    contractMap (cutRep A) r.val i.val=(OddCutParity.contractMap A r i).val := by
  simp only [contractMap,mem_rep,decide_eq_true_eq,OddCutParity.contractMap]
  split_ifs <;> rfl

lemma contract_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (A : Finset (Fin n)) (r : Fin n) :
    contract n (matrixRep c) (cutRep A) r.val=
      matrixRep (CutAlgebra.push c (OddCutParity.contractMap A r)) := by
  apply matrix_eq_rep
  intro i j
  simp only [Fin.ext_iff,contractMap_rep,sum_tab,get_rep,CutAlgebra.push]

lemma lift_rep {n : ℕ} (A S : Finset (Fin n)) (r : Fin n) :
    lift n (cutRep A) r.val (cutRep S)=cutRep (CutAlgebra.lift (OddCutParity.contractMap A r) S) := by
  apply tab_eq_rep
  intro i
  simp only [contractMap_rep,mem_rep,CutAlgebra.mem_lift]

lemma cheaper_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (S T : Finset (Fin n)) :
    cheaper n (matrixRep c) (cutRep S) (cutRep T)=cutRep (OddMincut.cheaper c S T) := by
  simp only [cheaper,cutCapacity_rep,OddMincut.cheaper]
  split_ifs <;> rfl
end BinaryMatching.Raw
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawContractionCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw.Compiler
open StackCode StackCode.Poly
@[fun_prop] theorem doubleNatSum {α : Type} [Coding α] [Inhabited α]
    (n : α → ℕ) (f : (α×ℕ)×ℕ → ℕ) (hn : Poly n) (hf : Poly f) :
    Poly (fun a => (tab (n a) (fun i => (tab (n a) (fun j => f ((a,i),j))).sum)).sum) := by
  apply Poly.comp List.sum _ Poly.listNatSum
  apply Poly.rawTab n (fun z : α×ℕ => (tab (n z.1) (fun j => f (z,j))).sum) hn
  apply Poly.comp List.sum _ Poly.listNatSum
  exact Poly.rawTab (fun z : α×ℕ => n z.1) f (by fun_prop) hf

@[fun_prop] theorem outside_poly : Poly (fun z : ℕ×Cut => outside z.1 z.2) := by
  unfold outside
  exact Poly.findWith (fun z : ℕ×Cut => List.range z.1)
    (fun z : (ℕ×Cut)×ℕ => !mem z.1.2 z.2) (by fun_prop) (by fun_prop)
@[fun_prop] theorem contractMap_poly : Poly (fun z : Cut×(ℕ×ℕ) => contractMap z.1 z.2.1 z.2.2) := by
  unfold contractMap
  fun_prop
@[fun_prop] theorem contract_poly : Poly (fun z : ℕ×(Matrix ℕ×(Cut×ℕ)) => contract z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold contract
  apply Poly.rawMatrix Prod.fst
    (fun z : ((ℕ×(Matrix ℕ×(Cut×ℕ)))×ℕ)×ℕ => if z.1.2=z.2 then 0 else
      (tab z.1.1.1 (fun u => (tab z.1.1.1 (fun v =>
        if contractMap z.1.1.2.2.1 z.1.1.2.2.2 u=z.1.2 ∧ contractMap z.1.1.2.2.1 z.1.1.2.2.2 v=z.2
        then get z.1.1.2.1 u v else 0)).sum)).sum)
  · fun_prop
  · have hs := doubleNatSum
      (fun z : ((ℕ×(Matrix ℕ×(Cut×ℕ)))×ℕ)×ℕ => z.1.1.1)
      (fun z : ((((ℕ×(Matrix ℕ×(Cut×ℕ)))×ℕ)×ℕ)×ℕ)×ℕ =>
        if decide (contractMap z.1.1.1.1.2.2.1 z.1.1.1.1.2.2.2 z.1.2=z.1.1.1.2) &&
          decide (contractMap z.1.1.1.1.2.2.1 z.1.1.1.1.2.2.2 z.2=z.1.1.2)
        then get z.1.1.1.1.2.1 z.1.2 z.2 else 0)
      (by fun_prop) (by fun_prop)
    have h : Poly (fun z : ((ℕ×(Matrix ℕ×(Cut×ℕ)))×ℕ)×ℕ => if decide (z.1.2=z.2) then 0 else
        (tab z.1.1.1 (fun u => (tab z.1.1.1 (fun v =>
          if decide (contractMap z.1.1.2.2.1 z.1.1.2.2.2 u=z.1.2) && decide (contractMap z.1.1.2.2.1 z.1.1.2.2.2 v=z.2)
          then get z.1.1.2.1 u v else 0)).sum)).sum) := by
      fun_prop
    exact h.congr (fun z => by simp only [decide_eq_true_eq,Bool.and_eq_true])
@[fun_prop] theorem lift_poly : Poly (fun z : ℕ×(Cut×(ℕ×Cut)) => lift z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold lift
  exact Poly.rawTab Prod.fst
    (fun z : (ℕ×(Cut×(ℕ×Cut)))×ℕ => mem z.1.2.2.2 (contractMap z.1.2.1 z.1.2.2.1 z.2))
    (by fun_prop) (by fun_prop)
@[fun_prop] theorem cheaper_poly : Poly (fun z : ℕ×(Matrix ℕ×(Cut×Cut)) => cheaper z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold cheaper
  have h : Poly (fun z : ℕ×(Matrix ℕ×(Cut×Cut)) =>
      if decide (cutCapacity z.1 z.2.1 z.2.2.1≤cutCapacity z.1 z.2.1 z.2.2.2) then z.2.2.1 else z.2.2.2) := by fun_prop
  exact h.congr (fun _ => by simp)
end BinaryMatching.Raw.Compiler
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawOddCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw
open RecursiveEval
abbrev OddArg := Matrix ℕ×Cut
abbrev OddJoin := Matrix ℕ×(Cut×(ℕ×ℕ))

def oddExpand (n : ℕ) (a : OddArg) : Branch OddArg Cut OddJoin :=
  let A := terminalCut n a.1 a.2
  if cardinal (inter n A a.2)%2=1 then .leaf A else
    match outside n A,outside n (compl n A) with
    | some r,some q => .fork (a.1,(A,(r,q)))
        (contract n a.1 A r,inter n A a.2)
        (contract n a.1 (compl n A) q,inter n (compl n A) a.2)
    | _,_ => .leaf (empty n)
def oddCombine (n : ℕ) (c : OddJoin) (X Y : Cut) : Cut :=
  cheaper n c.1 (lift n c.2.1 c.2.2.1 X) (lift n (compl n c.2.1) c.2.2.2 Y)
def oddValue (n k : ℕ) (a : OddArg) : Cut :=
  value (empty n) (oddExpand n) (oddCombine n) k a

theorem oddValue_rep {n : ℕ} (k : ℕ) (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) :
    oddValue n k (matrixRep c,cutRep U)=cutRep (OddMincut.recurse k c U) := by
  induction k generalizing c U with
  | zero => exact empty_rep _
  | succ k ih =>
    simp only [oddValue,value,oddExpand,terminalCut_rep,inter_rep,cardinal_rep,compl_rep,outside_rep,
      OddMincut.recurse,OddCutParity.OddSide,Nat.odd_iff]
    split_ifs with hodd
    · rfl
    · cases hr : OddMincut.outside (TerminalMincut.terminalCut c U) <;>
        cases hq : OddMincut.outside (TerminalMincut.terminalCut c U)ᶜ <;>
        simp only [Option.map_none,Option.map_some,contract_rep]
      · exact empty_rep _
      · exact empty_rep _
      · exact empty_rep _
      · rename_i r q
        change oddCombine n (matrixRep c,(cutRep (TerminalMincut.terminalCut c U),(r.val,q.val)))
          (oddValue n k (matrixRep _,cutRep _)) (oddValue n k (matrixRep _,cutRep _))=_
        rw [ih,ih]
        simp only [oddCombine,compl_rep,lift_rep,cheaper_rep]

theorem oddCalls_rep {n : ℕ} (k : ℕ) (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) :
    calls (oddExpand n) k (matrixRep c,cutRep U)=
      DenseOracle.calls k (DenseOracle.make c) U := by
  induction k generalizing c U with
  | zero => rfl
  | succ k ih =>
    simp only [calls,oddExpand,terminalCut_rep,inter_rep,cardinal_rep,compl_rep,outside_rep,
      DenseOracle.calls,DenseOracle.terminalCut_eq,DenseOracle.view_make,OddCutParity.OddSide,Nat.odd_iff]
    split_ifs with hodd
    · rfl
    · cases hr : OddMincut.outside (TerminalMincut.terminalCut c U) <;>
        cases hq : OddMincut.outside (TerminalMincut.terminalCut c U)ᶜ <;>
        simp only [Option.map_none,Option.map_some,contract_rep]
      all_goals simp only [ih,DenseOracle.contract,DenseOracle.view_make]

theorem oddCost_bound {n : ℕ} (c : Fin n → Fin n → ℕ) (U : Finset (Fin n))
    (he : Even U.card) (hU : 2≤U.card) :
    cost (oddExpand n) U.card (matrixRep c,cutRep U)≤2*n := by
  have hb := DenseOracle.calls_bound U.card (DenseOracle.make c) U he hU le_rfl
  rw [←oddCalls_rep] at hb
  have hc := cost_le_calls (oddExpand n) U.card (matrixRep c,cutRep U)
  have hu := Finset.card_le_univ U
  simp only [Fintype.card_fin] at hu
  omega
end BinaryMatching.Raw
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RecursiveCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.RecursiveEval
open StackCode

instance instCodingBranch {A B C : Type} [Coding A] [Coding B] [Coding C] : Coding (Branch A B C) := ⟨fun b => encode (branchRepr b)⟩
instance instCodingCommand {A C : Type} [Coding A] [Coding C] : Coding (Command A C) := ⟨fun c => encode (commandRepr c)⟩

namespace Compile
open StackCode.Poly
variable {A B C D P : Type} [Coding A] [Coding B] [Coding C] [Coding D] [Coding P]
@[fun_prop] theorem leaf_poly : Poly (Branch.leaf : B → Branch A B C) :=
  (Poly.sumInl (β := C×(A×A))).reindex Branch.leaf id (fun _ => rfl) (fun _ => rfl)
@[fun_prop] theorem fork_poly : Poly (fun z : C×(A×A) => Branch.fork z.1 z.2.1 z.2.2 : C×(A×A) → Branch A B C) :=
  (Poly.sumInr (α := B)).reindex (fun z : C×(A×A) => Branch.fork z.1 z.2.1 z.2.2) id (fun _ => rfl) (fun _ => rfl)
@[fun_prop] theorem call_poly : Poly (fun z : ℕ×A => Command.call z.1 z.2 : ℕ×A → Command A C) :=
  (Poly.sumInl (β := C)).reindex (fun z : ℕ×A => Command.call z.1 z.2) id (fun _ => rfl) (fun _ => rfl)
@[fun_prop] theorem join_poly : Poly (Command.join : C → Command A C) :=
  (Poly.sumInr (α := ℕ×A)).reindex Command.join id (fun _ => rfl) (fun _ => rfl)

@[fun_prop] theorem branchCasesWith [Inhabited A] [Inhabited B] [Inhabited C]
    (p : P → Branch A B C) (f : P×B → D) (g : P×(C×(A×A)) → D)
    (hp : Poly p) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => match p a with | .leaf b => f (a,b) | .fork c x y => g (a,(c,(x,y)))) := by
  have hr : Poly (fun a => branchRepr (p a)) :=
    hp.reindex (fun a => branchRepr (p a)) id (fun _ => rfl) (fun _ => rfl)
  let repr : Sum B (C×(A×A)) → List B×List (C×(A×A)) :=
    fun x => match x with | .inl b => ([b],[]) | .inr c => ([],[c])
  have hc : Poly repr := Poly.identity.reindex repr repr (fun x => by cases x <;> rfl) (fun _ => rfl)
  have h : Poly (fun a => if (repr (branchRepr (p a))).1.isEmpty then
      g (a,(repr (branchRepr (p a))).2.headD default) else
      f (a,(repr (branchRepr (p a))).1.headD default)) := by fun_prop
  exact h.congr (fun a => by cases p a <;> rfl)

@[fun_prop] theorem commandCasesWith [Inhabited A] [Inhabited C]
    (p : P → Command A C) (f : P×(ℕ×A) → D) (g : P×C → D)
    (hp : Poly p) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => match p a with | .call k x => f (a,(k,x)) | .join c => g (a,c)) := by
  have hr : Poly (fun a => commandRepr (p a)) :=
    hp.reindex (fun a => commandRepr (p a)) id (fun _ => rfl) (fun _ => rfl)
  let repr : Sum (ℕ×A) C → List (ℕ×A)×List C :=
    fun x => match x with | .inl b => ([b],[]) | .inr c => ([],[c])
  have hc : Poly repr := Poly.identity.reindex repr repr (fun x => by cases x <;> rfl) (fun _ => rfl)
  have h : Poly (fun a => if (repr (commandRepr (p a))).1.isEmpty then
      g (a,(repr (commandRepr (p a))).2.headD default) else
      f (a,(repr (commandRepr (p a))).1.headD default)) := by fun_prop
  exact h.congr (fun a => by cases p a <;> rfl)
end Compile
end BinaryMatching.RecursiveEval
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RecursiveBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.RecursiveEval
open StackCode
variable {A B C : Type}

def CommandGood (K : ℕ) (PA : A → Prop) (PC : C → Prop) : Command A C → Prop
  | .call k a => k≤K ∧ PA a
  | .join c => PC c

def StateGood (K : ℕ) (PA : A → Prop) (PB : B → Prop) (PC : C → Prop) (s : State A B C) : Prop :=
  (∀ c∈s.1,CommandGood K PA PC c) ∧ (∀ b∈s.2,PB b)

lemma step_good (zero : B) (expand : A → Branch A B C) (combine : C → B → B → B)
    (K : ℕ) (PA : A → Prop) (PB : B → Prop) (PC : C → Prop)
    (hz : PB zero)
    (he : ∀ a,PA a → match expand a with | .leaf b => PB b | .fork c x y => PC c ∧ PA x ∧ PA y)
    (hc : ∀ c,PC c → ∀ x,PB x → ∀ y,PB y → PB (combine c x y))
    (s : State A B C) (hs : StateGood K PA PB PC s) :
    StateGood K PA PB PC (step zero expand combine s) := by
  rcases s with ⟨w,v⟩
  rcases hs with ⟨hw,hv⟩
  cases w with
  | nil => exact ⟨hw,hv⟩
  | cons cmd w =>
    have hw' : ∀ c∈w,CommandGood K PA PC c := fun c h => hw c (List.mem_cons_of_mem _ h)
    have hcmd := hw cmd List.mem_cons_self
    cases cmd with
    | call k a =>
      rcases hcmd with ⟨hk,ha⟩
      cases k with
      | zero =>
        exact ⟨hw',by simpa only [step,List.mem_cons,forall_eq_or_imp] using And.intro hz hv⟩
      | succ k =>
        have hh := he a ha
        cases h : expand a with
        | leaf b =>
          simp only [h] at hh
          simp only [step,h,StateGood]
          exact ⟨hw',by simpa only [List.mem_cons,forall_eq_or_imp] using And.intro hh hv⟩
        | fork c x y =>
          simp only [h] at hh
          simp only [step,h,StateGood]
          refine ⟨?_,hv⟩
          intro d hd
          simp only [List.mem_cons] at hd
          rcases hd with rfl|rfl|rfl|hd
          · exact ⟨by omega,hh.2.1⟩
          · exact ⟨by omega,hh.2.2⟩
          · exact hh.1
          · exact hw' d hd
    | join c =>
      cases v with
      | nil => exact ⟨by simp [step],hv⟩
      | cons y v =>
        cases v with
        | nil => exact ⟨by simp [step],hv⟩
        | cons x v =>
          simp only [step,StateGood]
          refine ⟨hw',?_⟩
          intro b hb
          rcases List.mem_cons.mp hb with rfl|hb
          · exact hc c hcmd x (hv x (by simp)) y (hv y (by simp))
          · exact hv b (by simp [hb])

lemma step_length (zero : B) (expand : A → Branch A B C) (combine : C → B → B → B)
    (s : State A B C) :
    (step zero expand combine s).1.length+(step zero expand combine s).2.length ≤ s.1.length+s.2.length+2 := by
  rcases s with ⟨w,v⟩
  cases w with
  | nil => simp [step]
  | cons cmd w =>
    cases cmd with
    | call k a =>
      cases k with
      | zero => simp [step]; omega
      | succ k => cases h : expand a <;> simp [step,h] <;> omega
    | join c => cases v with
      | nil => simp [step]
      | cons y v => cases v <;> simp [step]; omega

lemma iterate_length (zero : B) (expand : A → Branch A B C) (combine : C → B → B → B)
    (s : State A B C) (j : ℕ) :
    ((step zero expand combine)^[j] s).1.length+((step zero expand combine)^[j] s).2.length ≤ s.1.length+s.2.length+2*j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hh := step_length zero expand combine ((step zero expand combine)^[j] s)
    omega

lemma iterate_good (zero : B) (expand : A → Branch A B C) (combine : C → B → B → B)
    (K : ℕ) (PA : A → Prop) (PB : B → Prop) (PC : C → Prop)
    (hz : PB zero)
    (he : ∀ a,PA a → match expand a with | .leaf b => PB b | .fork c x y => PC c ∧ PA x ∧ PA y)
    (hc : ∀ c,PC c → ∀ x,PB x → ∀ y,PB y → PB (combine c x y))
    (s : State A B C) (hs : StateGood K PA PB PC s) (j : ℕ) :
    StateGood K PA PB PC ((step zero expand combine)^[j] s) := by
  induction j with
  | zero => exact hs
  | succ j ih => rw [Function.iterate_succ_apply']; exact step_good zero expand combine K PA PB PC hz he hc _ ih

lemma code_call {A C : Type} [Coding A] [Coding C] (k : ℕ) (a : A) :
    (encode (Command.call k a : Command A C)).length=8*k+4*(encode a).length+7 := by
  change (pairBits (pairBits (pairBits (encode k) (encode a)) []) []).length=_
  simp only [pairBits_length,List.length_nil,code_nat_length]
  omega
lemma code_join {A C : Type} [Coding A] [Coding C] (c : C) :
    (encode (Command.join c : Command A C)).length=2*(encode c).length+2 := by
  change (pairBits [] (pairBits (encode c) [])).length=_
  simp only [pairBits_length,List.length_nil]
  omega

lemma state_code_bound [Coding A] [Coding B] [Coding C] (s : State A B C) (M : ℕ)
    (hw : ∀ c∈s.1,(encode c).length≤M) (hv : ∀ b∈s.2,(encode b).length≤M) :
    (encode s).length≤2*(s.1.length+s.2.length)*(2*M+1)+1 := by
  have h₁ := list_code_bound s.1 M hw
  have h₂ := list_code_bound s.2 M hv
  rw [code_pair_length]
  nlinarith
end BinaryMatching.RecursiveEval
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RecursiveCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.RecursiveEval
open StackCode
variable {A B C P : Type}

def paramStep (zero : P → B) (expand : P → A → Branch A B C)
    (combine : P → C → B → B → B) (z : P×State A B C) : P×State A B C :=
  (z.1,step (zero z.1) (expand z.1) (combine z.1) z.2)

lemma paramStep_iterate (zero : P → B) (expand : P → A → Branch A B C)
    (combine : P → C → B → B → B) (z : P×State A B C) (k : ℕ) :
    (paramStep zero expand combine)^[k] z=
      (z.1,(step (zero z.1) (expand z.1) (combine z.1))^[k] z.2) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply',ih,paramStep]

namespace Compile
open StackCode.Poly
variable [Coding A] [Coding B] [Coding C] [Coding P]
  [Inhabited A] [Inhabited B] [Inhabited C]

def execCommand (zero : P → B) (expand : P → A → Branch A B C)
    (combine : P → C → B → B → B) (z : (P×State A B C)×Command A C) : State A B C :=
  match z.2 with
  | .call k a => if k=0 then (z.1.2.1.tail,zero z.1.1::z.1.2.2) else
    match expand z.1.1 a with
    | .leaf b => (z.1.2.1.tail,b::z.1.2.2)
    | .fork c x y => (.call (k-1) x::.call (k-1) y::.join c::z.1.2.1.tail,z.1.2.2)
  | .join c => if 2≤z.1.2.2.length then
      (z.1.2.1.tail,combine z.1.1 c (z.1.2.2.tail.headD default) (z.1.2.2.headD default)::z.1.2.2.tail.tail)
    else ([],z.1.2.2)

@[fun_prop] theorem execCommand_poly (zero : P → B) (expand : P → A → Branch A B C)
    (combine : P → C → B → B → B) (hz : Poly zero)
    (he : Poly (fun z : P×A => expand z.1 z.2))
    (hc : Poly (fun z : P×(C×(B×B)) => combine z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Poly (execCommand zero expand combine) := by
  unfold execCommand
  apply commandCasesWith Prod.snd
    (fun z : ((P×State A B C)×Command A C)×(ℕ×A) =>
      if z.2.1=0 then (z.1.1.2.1.tail,zero z.1.1.1::z.1.1.2.2) else
      match expand z.1.1.1 z.2.2 with
      | .leaf b => (z.1.1.2.1.tail,b::z.1.1.2.2)
      | .fork c x y => (.call (z.2.1-1) x::.call (z.2.1-1) y::.join c::z.1.1.2.1.tail,z.1.1.2.2))
    (fun z => if 2≤z.1.1.2.2.length then
      (z.1.1.2.1.tail,combine z.1.1.1 z.2 (z.1.1.2.2.tail.headD default) (z.1.1.2.2.headD default)::z.1.1.2.2.tail.tail)
      else ([],z.1.1.2.2))
  · fun_prop
  · have hb₀ := branchCasesWith
      (fun z : ((P×State A B C)×Command A C)×(ℕ×A) => expand z.1.1.1 z.2.2)
      (fun z => (z.1.1.1.2.1.tail,z.2::z.1.1.1.2.2))
      (fun z => (Command.call (z.1.2.1-1) z.2.2.1::Command.call (z.1.2.1-1) z.2.2.2::
        Command.join z.2.1::z.1.1.1.2.1.tail,z.1.1.1.2.2))
      (by fun_prop) (by fun_prop) (by fun_prop)
    have hb : Poly (fun z : ((P×State A B C)×Command A C)×(ℕ×A) =>
        match expand z.1.1.1 z.2.2 with
        | .leaf b => (z.1.1.2.1.tail,b::z.1.1.2.2)
        | .fork c x y => (.call (z.2.1-1) x::.call (z.2.1-1) y::.join c::z.1.1.2.1.tail,z.1.1.2.2)) :=
      hb₀.congr (fun z => by cases expand z.1.1.1 z.2.2 <;> rfl)
    have h : Poly (fun z : ((P×State A B C)×Command A C)×(ℕ×A) =>
        if decide (z.2.1=0) then (z.1.1.2.1.tail,zero z.1.1.1::z.1.1.2.2) else
        match expand z.1.1.1 z.2.2 with
        | .leaf b => (z.1.1.2.1.tail,b::z.1.1.2.2)
        | .fork c x y => (.call (z.2.1-1) x::.call (z.2.1-1) y::.join c::z.1.1.2.1.tail,z.1.1.2.2)) := by fun_prop
    exact h.congr (fun _ => by simp)
  · have h : Poly (fun z : ((P×State A B C)×Command A C)×C => if decide (2≤z.1.1.2.2.length) then
        (z.1.1.2.1.tail,combine z.1.1.1 z.2 (z.1.1.2.2.tail.headD default) (z.1.1.2.2.headD default)::z.1.1.2.2.tail.tail)
        else ([],z.1.1.2.2)) := by fun_prop
    exact h.congr (fun _ => by simp)

@[fun_prop] theorem paramStep_poly (zero : P → B) (expand : P → A → Branch A B C)
    (combine : P → C → B → B → B) (hz : Poly zero)
    (he : Poly (fun z : P×A => expand z.1 z.2))
    (hc : Poly (fun z : P×(C×(B×B)) => combine z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Poly (paramStep zero expand combine) := by
  have hx := execCommand_poly zero expand combine hz he hc
  have h : Poly (fun z : P×State A B C =>
      (z.1,if z.2.1.isEmpty then z.2 else execCommand zero expand combine (z,z.2.1.headD default))) := by fun_prop
  apply h.congr
  intro z
  rcases z with ⟨p,w,v⟩
  unfold paramStep
  cases w with
  | nil => rfl
  | cons a w =>
    cases a with
    | call k a =>
      cases k <;> rfl
    | join c =>
      cases v with
      | nil => simp [execCommand,step]
      | cons b v => cases v <;> simp [execCommand,step]
end Compile
end BinaryMatching.RecursiveEval
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawOddBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw
open StackCode RecursiveEval

def ArgGood (n B : ℕ) (a : OddArg) : Prop :=
  ∃ (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)),a=(matrixRep c,cutRep U) ∧ DenseOracle.total c≤B
def CutGood (n : ℕ) (S : Cut) : Prop := ∃ U : Finset (Fin n),S=cutRep U
def JoinGood (n B : ℕ) (a : OddJoin) : Prop :=
  ∃ (c : Fin n → Fin n → ℕ) (A : Finset (Fin n)) (r q : Fin n),
    a=(matrixRep c,(cutRep A,(r.val,q.val))) ∧ DenseOracle.total c≤B

lemma oddExpand_good (n B : ℕ) (a : OddArg) (ha : ArgGood n B a) :
    match oddExpand n a with
    | .leaf S => CutGood n S
    | .fork c x y => JoinGood n B c ∧ ArgGood n B x ∧ ArgGood n B y := by
  obtain ⟨c,U,rfl,hc⟩ := ha
  simp only [oddExpand,terminalCut_rep,inter_rep,cardinal_rep,compl_rep,outside_rep]
  split_ifs
  · exact ⟨_,rfl⟩
  · cases hr : OddMincut.outside (TerminalMincut.terminalCut c U) <;>
      cases hq : OddMincut.outside (TerminalMincut.terminalCut c U)ᶜ <;>
      simp only [Option.map_none,Option.map_some,contract_rep]
    · exact ⟨_,empty_rep _⟩
    · exact ⟨_,empty_rep _⟩
    · exact ⟨_,empty_rep _⟩
    · rename_i r q
      refine ⟨⟨c,_,r,q,rfl,hc⟩,⟨_,_,rfl,?_⟩,⟨_,_,rfl,?_⟩⟩ <;>
        exact (DenseOracle.push_total_le _ _).trans hc

lemma oddCombine_good (n B : ℕ) (c : OddJoin) (hc : JoinGood n B c)
    (X : Cut) (hX : CutGood n X) (Y : Cut) (hY : CutGood n Y) : CutGood n (oddCombine n c X Y) := by
  obtain ⟨c,A,r,q,rfl,hc⟩ := hc
  obtain ⟨X,rfl⟩ := hX
  obtain ⟨Y,rfl⟩ := hY
  simp only [oddCombine,compl_rep,lift_rep,cheaper_rep]
  exact ⟨_,rfl⟩

lemma vectorRep_code_bound {α : Type} [Coding α] {n : ℕ} (f : Fin n → α) (M : ℕ)
    (h : ∀ i,(encode (f i)).length≤M) :
    (encode (vectorRep f)).length≤n*(2*M+1) := by
  have hh := list_code_bound (vectorRep f) M (by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact h i)
  simpa only [vectorRep,List.length_ofFn] using hh

lemma matrixRep_code_bound {n : ℕ} (c : Fin n → Fin n → ℕ) (B : ℕ)
    (h : DenseOracle.total c≤B) : (encode (matrixRep c)).length≤n*(2*(n*(2*B+1))+1) := by
  apply vectorRep_code_bound
  intro i
  apply vectorRep_code_bound
  intro j
  simpa only [code_nat_length] using (DenseOracle.entry_le_total c i j).trans h

lemma cutRep_code_length {n : ℕ} (S : Finset (Fin n)) : (encode (cutRep S)).length=3*n := by
  rw [cut_code_length]
  simp only [cutRep,vectorRep,List.length_ofFn]

lemma arg_code_bound (n B : ℕ) (a : OddArg) (ha : ArgGood n B a) :
    (encode a).length≤100*(n+1)^2*(B+1) := by
  obtain ⟨c,U,rfl,hc⟩ := ha
  have hh := matrixRep_code_bound c B hc
  simp only [code_pair_length,cutRep_code_length]
  calc
    _ ≤ 2*(n*(2*(n*(2*B+1))+1))+3*n+1 := by omega
    _ ≤ _ := by ring_nf; omega
lemma join_code_bound (n B : ℕ) (a : OddJoin) (ha : JoinGood n B a) :
    (encode a).length≤100*(n+1)^2*(B+1) := by
  obtain ⟨c,A,r,q,rfl,hc⟩ := ha
  have hh := matrixRep_code_bound c B hc
  have hr := r.isLt
  have hq := q.isLt
  simp only [code_pair_length,cutRep_code_length,code_nat_length]
  calc
    _ ≤ 2*(n*(2*(n*(2*B+1))+1))+9*n+3 := by omega
    _ ≤ _ := by ring_nf; omega

lemma command_code_bound (n B : ℕ) (c : Command OddArg OddJoin)
    (hc : CommandGood n (ArgGood n B) (JoinGood n B) c) : (encode c).length≤oddWordBound n B := by
  cases c with
  | call k a =>
    obtain ⟨hk,ha⟩ := hc
    have hh := arg_code_bound n B a ha
    rw [code_call]
    unfold oddWordBound
    calc
      _ ≤ 8*n+4*(100*(n+1)^2*(B+1))+7 := by omega
      _ ≤ _ := by ring_nf; omega
  | join c =>
    have hh := join_code_bound n B c hc
    rw [code_join]
    unfold oddWordBound
    calc
      _ ≤ 2*(100*(n+1)^2*(B+1))+2 := by omega
      _ ≤ _ := by ring_nf; omega
lemma cut_code_bound (n B : ℕ) (S : Cut) (hS : CutGood n S) : (encode S).length≤oddWordBound n B := by
  obtain ⟨S,rfl⟩ := hS
  rw [cutRep_code_length]
  unfold oddWordBound
  ring_nf
  omega

lemma oddOrbit_bound {n : ℕ} (c : Fin n → Fin n → ℕ) (U : Finset (Fin n))
    (B : ℕ) (hB : DenseOracle.total c≤B) (j : ℕ) (hj : j≤2*n) :
    (encode ((paramStep empty oddExpand oddCombine)^[j]
      (n,([Command.call U.card (matrixRep c,cutRep U)],[])))).length≤oddBudget n B := by
  rw [paramStep_iterate]
  dsimp only
  have hz : CutGood n (empty n) := ⟨_,empty_rep _⟩
  have hU : U.card≤n := by simpa only [Fintype.card_fin] using Finset.card_le_univ U
  have hgood : StateGood n (ArgGood n B) (CutGood n) (JoinGood n B)
      ([Command.call U.card (matrixRep c,cutRep U)],[]) := by
    constructor
    · intro a ha
      obtain rfl := List.mem_singleton.mp ha
      exact ⟨hU,⟨c,U,rfl,hB⟩⟩
    · simp
  have hg := iterate_good (empty n) (oddExpand n) (oddCombine n) n (ArgGood n B) (CutGood n) (JoinGood n B)
    hz (fun a ha => by
      have hh := oddExpand_good n B a ha
      cases h : oddExpand n a <;> simpa only [h] using hh) (oddCombine_good n B) _ hgood j
  have hl := iterate_length (empty n) (oddExpand n) (oddCombine n)
    ([Command.call U.card (matrixRep c,cutRep U)],[]) j
  simp only [List.length_singleton,List.length_nil,Nat.add_zero] at hl
  have hs := state_code_bound _ (oddWordBound n B)
    (fun cmd hc => command_code_bound n B cmd (hg.1 cmd hc))
    (fun S hS => cut_code_bound n B S (hg.2 S hS))
  have hlen : ((step (empty n) (oddExpand n) (oddCombine n))^[j]
      ([Command.call U.card (matrixRep c,cutRep U)],[])).1.length+
    ((step (empty n) (oddExpand n) (oddCombine n))^[j]
      ([Command.call U.card (matrixRep c,cutRep U)],[])).2.length≤1+4*n := by omega
  have hm := Nat.add_le_add_right
    (Nat.mul_le_mul_right (2*oddWordBound n B+1) (Nat.mul_le_mul_left 2 hlen)) 1
  rw [code_pair_length,code_nat_length]
  dsimp only
  have hss := hs.trans hm
  calc
    _ ≤ 2*n+(2*(1+4*n)*(2*oddWordBound n B+1)+1)+1 := by omega
    _ ≤ oddBudget n B := by unfold oddWordBound oddBudget; ring_nf; omega
end BinaryMatching.Raw
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawOddCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw
open StackCode RecursiveEval

def rawTotal (c : Matrix ℕ) : ℕ := c.flatten.sum
lemma rawTotal_rep {n : ℕ} (c : Fin n → Fin n → ℕ) : rawTotal (matrixRep c)=DenseOracle.total c := by
  simp only [rawTotal,matrixRep,vectorRep,List.sum_flatten,List.map_ofFn,List.sum_ofFn,DenseOracle.total,Function.comp_def]

def oddFlat (z : ℕ×(Matrix ℕ×Cut)) : Cut :=
  let s := ((guardedStep (paramStep empty oddExpand oddCombine))^[2*z.1]
    (oddBudget z.1 (rawTotal z.2.1),(z.1,([Command.call (cardinal z.2.2) (z.2.1,z.2.2)],[])))).2
  s.2.2.headD []

theorem oddFlat_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (U : Finset (Fin n))
    (he : Even U.card) (hU : 2≤U.card) :
    oddFlat (n,(matrixRep c,cutRep U))=cutRep (OddMincut.oddCut c U) := by
  unfold oddFlat
  simp only [rawTotal_rep,cardinal_rep]
  rw [guardedStep_eq (paramStep empty oddExpand oddCombine)
    (oddBudget n (DenseOracle.total c)) (n,([Command.call U.card (matrixRep c,cutRep U)],[])) (2*n)
    (fun j hj => oddOrbit_bound c U _ le_rfl j hj)]
  rw [paramStep_iterate]
  rw [runs_extra (empty n) (oddExpand n) (oddCombine n) U.card
    (matrixRep c,cutRep U) (2*n) (oddCost_bound c U he hU)]
  exact oddValue_rep _ c U

namespace Compiler
open StackCode.Poly RecursiveEval.Compile
@[fun_prop] theorem rawTotal_poly : Poly rawTotal := by unfold rawTotal; fun_prop
@[fun_prop] theorem oddBudget_poly : Poly (fun z : ℕ×ℕ => oddBudget z.1 z.2) := by unfold oddBudget; fun_prop
@[fun_prop] theorem oddExpand_poly : Poly (fun z : ℕ×OddArg => oddExpand z.1 z.2) := by
  let A (z : ℕ×OddArg) := terminalCut z.1 z.2.1 z.2.2
  have hA : Poly A := terminalCut_poly
  have h : Poly (fun z : ℕ×OddArg =>
      if decide (cardinal (inter z.1 (A z) z.2.2)%2=1) then Branch.leaf (A z) else
      if (outside z.1 (A z)).isSome && (outside z.1 (compl z.1 (A z))).isSome then
        Branch.fork (z.2.1,(A z,((outside z.1 (A z)).getD 0,(outside z.1 (compl z.1 (A z))).getD 0)))
          (contract z.1 z.2.1 (A z) ((outside z.1 (A z)).getD 0),inter z.1 (A z) z.2.2)
          (contract z.1 z.2.1 (compl z.1 (A z)) ((outside z.1 (compl z.1 (A z))).getD 0),inter z.1 (compl z.1 (A z)) z.2.2)
      else Branch.leaf (empty z.1) : (ℕ×OddArg) → Branch OddArg Cut OddJoin) := by fun_prop
  exact h.congr (fun z => by
    unfold oddExpand
    dsimp only [A]
    simp only [decide_eq_true_eq]
    by_cases hp : cardinal (inter z.1 (terminalCut z.1 z.2.1 z.2.2) z.2.2)%2=1
    · simp only [ite_eq_left hp]
    · simp only [ite_eq_right hp]
      cases outside z.1 (terminalCut z.1 z.2.1 z.2.2) <;>
        cases outside z.1 (compl z.1 (terminalCut z.1 z.2.1 z.2.2)) <;> rfl)
@[fun_prop] theorem oddCombine_poly : Poly (fun z : ℕ×(OddJoin×(Cut×Cut)) => oddCombine z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold oddCombine
  fun_prop
@[fun_prop] theorem oddFlat_poly : Poly oddFlat := by
  have hs := paramStep_poly empty oddExpand oddCombine rawEmpty oddExpand_poly oddCombine_poly
  have hg := Poly.guardedIterate (paramStep empty oddExpand oddCombine) hs
  have hi := Poly.comp _ (fun z : ℕ×(Matrix ℕ×Cut) =>
    (2*z.1,(oddBudget z.1 (rawTotal z.2.1),(z.1,([Command.call (cardinal z.2.2) (z.2.1,z.2.2)],[]))))) hg (by fun_prop)
  exact Poly.comp (fun s : ℕ×State OddArg Cut OddJoin => s.2.2.headD []) _ (by fun_prop) hi
end Compiler
end BinaryMatching.Raw
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawOptimizerRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw.Optimize
open Algorithm Finset

def capacities (n : ℕ) (a : Matrix ℤ) : Matrix ℕ :=
  matrix n (fun i j => if i < j then (get a i j).toNat else if j < i then (get a j i).toNat else 0)
lemma capacities_rep {n : ℕ} (a : Table n ℤ) :
    capacities n (tableRep a)=matrixRep (Algorithm.capacities a) := by
  apply matrix_eq_rep
  intro i j
  simp only [get_tableRep,Algorithm.capacities,Fin.lt_def]

def zeroRow (n : ℕ) : Row := (matrix n (fun _ _ => 0),0)
def degreeRow (n v : ℕ) (positive : Bool) : Row :=
  (matrix n (fun i j => if i < j then
    if i=v ∨ j=v then (if positive then 1 else -1) else 0 else 0),if positive then -1 else 1)
def cutRow (n : ℕ) (S : Cut) : Row :=
  (matrix n (fun i j => if i < j then
    if (mem S i && !mem S j) || (mem S j && !mem S i) then -1 else 0 else 0),1)
lemma zeroRow_rep (n : ℕ) : zeroRow n=rowRep (Algorithm.zeroRow (n := n)) := by
  apply Prod.ext
  · apply matrix_eq_rep
    intro i j
    simp [toTable,tabulate,Algorithm.zeroRow]
  · rfl
lemma degreeRow_rep {n : ℕ} (v : Fin n) (b : Bool) : degreeRow n v.val b=rowRep (Algorithm.degreeRow v b) := by
  apply Prod.ext
  · apply matrix_eq_rep
    intro i j
    by_cases h : i < j <;> simp [toTable,tabulate,Algorithm.degreeRow,Fin.ext_iff,h]
  · rfl
lemma cutRow_rep {n : ℕ} (S : Finset (Fin n)) : cutRow n (cutRep S)=rowRep (Algorithm.cutRow S) := by
  apply Prod.ext
  · apply matrix_eq_rep
    intro i j
    by_cases h : i < j <;> simp [toTable,tabulate,Algorithm.cutRow,h]
  · rfl

def rows (n : ℕ) (a : Matrix ℤ) : List Row :=
  zeroRow n :: ((List.range n).flatMap (fun v => [degreeRow n v true,degreeRow n v false])) ++
    [cutRow n (oddFlat (n,(capacities n a,full n)))]
lemma rows_rep {n : ℕ} (hn : 2≤n) (he : Even n) (a : Table n ℤ) :
    rows n (tableRep a)=(integralRows a).map rowRep := by
  have hu : (univ : Finset (Fin n)).card=n := Fintype.card_fin n
  unfold rows integralRows
  rw [capacities_rep,full_rep,oddFlat_rep _ _ (by simpa only [hu] using he) (by simpa only [hu] using hn)]
  simp only [zeroRow_rep,cutRow_rep,List.map_append,List.map_cons,List.map_nil,
    DenseOracle.oddCut_eq,DenseOracle.view_make]
  congr 2
  rw [range_eq_fin,List.flatMap_map,List.map_flatMap]
  congr 1
  funext v
  simp only [degreeRow_rep,List.map_cons,List.map_nil]

lemma argmax_map {α β γ : Type} [Preorder γ] [DecidableLT γ] (l : List α) (f : α → β) (g : β → γ) :
    (l.map f).argmax g=(l.argmax (g ∘ f)).map f :=
  @StackCode.argmin_map_exact α β γᵒᵈ _ _ l f g

attribute [local instance] OAI.BinaryMatching.Raw.Optimize.instPreorderInt_solutions_1
def selectedRow (n D : ℕ) (a : Matrix ℤ) : Row :=
  ((rows n a).argmax (rowNumerator D a)).getD (zeroRow n)
lemma selectedRow_rep {n : ℕ} (hn : 2≤n) (he : Even n) (D : ℕ) (a : Table n ℤ) :
    selectedRow n D (tableRep a)=rowRep (integralRow D a) := by
  unfold selectedRow integralRow
  rw [rows_rep hn he,argmax_map]
  have hf : rowNumerator D (tableRep a) ∘ rowRep=Algorithm.rowNumerator D a := by
    funext r
    exact rowNumerator_rep D a r
  rw [hf]
  cases h : (integralRows a).argmax (Algorithm.rowNumerator D a) with
  | none => exact zeroRow_rep n
  | some r => rfl
end BinaryMatching.Raw.Optimize
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawOptimizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw.Optimize
open Algorithm Finset StackCode

def value (p : Params) (a : Matrix ℤ) (r : Row) : ℤ :=
  upperSum p.n (fun i j => scaledPsi p (get a i j)+get p.beta i j*get a i j*p.pow)-
    (p.M:ℤ)*rowNumerator p.D a r*p.pow
lemma value_rep (G : Input) (a : Table G.n ℤ) (r : Affine G.n) :
    value (params G) (tableRep a) (rowRep r)=integralValue G a r := by
  unfold value integralValue
  rw [rowNumerator_rep]
  congr 1
  change upperSum G.n _=_
  apply upperSum_rep
  intro e
  rw [get_tableRep,get_beta,scaledPsi_rep]
  rfl

def gradient (p : Params) (a : Matrix ℤ) (r : Row) (i j : ℕ) : ℤ :=
  scaledSlope p (get a i j)+get p.beta i j-(p.M:ℤ)*get r.1 i j
lemma gradient_rep (G : Input) (a : Table G.n ℤ) (r : Affine G.n) (e : Pair G.n) :
    gradient (params G) (tableRep a) (rowRep r) e.val.1.val e.val.2.val=integralGradient G a r e := by
  unfold gradient integralGradient
  rw [get_tableRep,get_beta,get_rowRep,scaledSlope_rep]
  rfl

def update (p : Params) (a : Matrix ℤ) (r : Row) : Matrix ℤ :=
  matrix p.n (fun i j => if i < j then min (p.D:ℤ) (max 0 (get a i j+gradient p a r i j)) else 0)
lemma update_rep (G : Input) (a : Table G.n ℤ) (r : Affine G.n) :
    update (params G) (tableRep a) (rowRep r)=tableRep (integralUpdate G a r) := by
  change matrix G.n _=matrixRep _
  apply matrix_eq_rep
  intro i j
  change (if i.val<j.val then _ else 0)=(integralUpdate G a r)[i][j]
  by_cases h : i < j
  · simp [integralUpdate,toTable,tabulate,h,get_tableRep,
      gradient_rep G a r ⟨(i,j),h⟩,show (params G).D=D₀ G from rfl,entry]
  · simp [integralUpdate,toTable,tabulate,h]

def step (z : Params×IntState) : Params×IntState :=
  let r := selectedRow z.1.n z.1.D z.2.1
  let v := value z.1 z.2.1 r
  (z.1,(update z.1 z.2.1 r,some (z.2.2.elim v (max v))))

def initial (p : Params) : Params×IntState := (p,(matrix p.n (fun _ _ => 0),none))
lemma initial_rep (G : Input) : initial (params G)=(params G,stateRep (integralInitial G.n)) := by
  change (params G,(matrix G.n (fun _ _ => 0),none))=(params G,(tableRep (integralInitial G.n).numerators,none))
  apply congrArg (fun a : Matrix ℤ => (params G,(a,(none:Option ℤ))))
  apply matrix_eq_rep
  intro i j
  simp [integralInitial,tabulate]
lemma step_rep (G : Input) (hn : 2≤G.n) (he : Even G.n) (s : IntegralState G.n) :
    step (params G,stateRep s)=(params G,stateRep (integralStep G s)) := by
  dsimp only [step]
  rw [show (stateRep s).1=tableRep s.numerators from rfl,
    show (params G).n=G.n from rfl,selectedRow_rep hn he,value_rep,update_rep]
  rfl
lemma step_iterate_rep (G : Input) (hn : 2≤G.n) (he : Even G.n) (k : ℕ) :
    step^[k] (initial (params G))=(params G,stateRep (integralIterate G k)) := by
  induction k with
  | zero => exact initial_rep G
  | succ k ih => rw [Function.iterate_succ_apply',ih,step_rep G hn he]; rfl

lemma integralIterate_lower (G : Input) (t : ℕ) (i j : Fin G.n) (h : ¬i < j) :
    (integralIterate G t).numerators[i][j]=0 := by
  cases t with
  | zero => simp [integralIterate,integralInitial,tabulate]
  | succ t => simp [integralIterate,integralStep,integralUpdate,toTable,tabulate,h]
lemma integralIterate_all_abs (G : Input) (hn : 2≤G.n) (t : ℕ) (i j : Fin G.n) :
    ((integralIterate G t).numerators[i][j]).natAbs≤D₀ G := by
  by_cases hij : i < j
  · exact integralIterate_abs G hn t ⟨(i,j),hij⟩
  · rw [integralIterate_lower G t i j hij]
    exact Nat.zero_le _

def operandBound (p : Params) : ℕ := p.D*p.pow*(p.q*(p.k+p.L+1)+p.M*(p.q+1))
def budget (p : Params) : ℕ :=
  2*(encode p).length+2*(p.n*(2*(p.n*(2*(p.D+3)+1))+1))+(2*(operandBound p+3)+1)+2

lemma state_code_bound (G : Input) (hn : 2≤G.n) (t : ℕ) :
    (encode (params G,stateRep (integralIterate G t))).length≤budget (params G) := by
  have ht : (encode (tableRep (integralIterate G t).numerators)).length≤
      G.n*(2*(G.n*(2*(D₀ G+3)+1))+1) := by
    apply vectorRep_code_bound
    intro i
    apply vectorRep_code_bound
    intro j
    rw [code_int_length]
    exact Nat.add_le_add_right (integralIterate_all_abs G hn t i j) 3
  have hb : (encode (integralIterate G t).best).length≤2*(Algorithm.operandBound G+3)+1 := by
    cases h : (integralIterate G t).best with
    | none => simp only [code_option_none,List.length_nil]; omega
    | some v =>
      simp only [code_option_some,code_int_length]
      have hv := integralBest_abs G hn t v h
      omega
  simp only [code_pair_length,stateRep] at ht ⊢
  change 2*(encode (params G)).length+
    (2*(encode (tableRep (integralIterate G t).numerators)).length+
     (encode (integralIterate G t).best).length+1)+1≤_
  change _≤2*(encode (params G)).length+2*(G.n*(2*(G.n*(2*(D₀ G+3)+1))+1))+
    (2*(Algorithm.operandBound G+3)+1)+2
  omega

def run (p : Params) : IntState :=
  (((guardedStep step)^[p.q*p.D] (budget p,initial p)).2).2
lemma run_rep (G : Input) (hn : 2≤G.n) (he : Even G.n) :
    run (params G)=stateRep (integralIterate G (q G.n*D₀ G)) := by
  unfold run
  rw [guardedStep_eq step (budget (params G)) (initial (params G)) _ (by
    intro j hj
    rw [step_iterate_rep G hn he]
    exact state_code_bound G hn j),step_iterate_rep G hn he]
  rfl

def result (p : Params) : ℤ := (run p).2.getD 0/(p.D*p.pow:ℕ)
lemma result_rep (G : Input) (hn : 2≤G.n) (he : Even G.n) : result (params G)=integralR G := by
  unfold result integralR
  rw [run_rep G hn he]
  rfl
end BinaryMatching.Raw.Optimize
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawOptimizerDataCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw.Optimize.Compiler
open StackCode StackCode.Poly

@[fun_prop] theorem paramsRepr_poly : Poly Params.repr :=
  (Poly.identity (α := ParamData)).reindex Params.repr Params.repr (fun _ => rfl) (fun _ => rfl)
@[fun_prop] theorem paramsOfData_poly : Poly Params.ofData :=
  (Poly.identity (α := ParamData)).reindex Params.ofData id (fun _ => rfl) (fun _ => rfl)
@[fun_prop] theorem params_n : Poly Params.n :=
  Poly.comp (fun z : ParamData => z.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_q : Poly Params.q :=
  Poly.comp (fun z : ParamData => z.2.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_k : Poly Params.k :=
  Poly.comp (fun z : ParamData => z.2.2.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_L : Poly Params.L :=
  Poly.comp (fun z : ParamData => z.2.2.2.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_D : Poly Params.D :=
  Poly.comp (fun z : ParamData => z.2.2.2.2.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_M : Poly Params.M :=
  Poly.comp (fun z : ParamData => z.2.2.2.2.2.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_pow : Poly Params.pow :=
  Poly.comp (fun z : ParamData => z.2.2.2.2.2.2.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_beta : Poly Params.beta :=
  Poly.comp (fun z : ParamData => z.2.2.2.2.2.2.2) Params.repr (by fun_prop) paramsRepr_poly

@[fun_prop] theorem doubleIntSum {α : Type} [Coding α] [Inhabited α]
    (n : α → ℕ) (f : (α×ℕ)×ℕ → ℤ) (hn : Poly n) (hf : Poly f) :
    Poly (fun a => (tab (n a) (fun i => (tab (n a) (fun j => f ((a,i),j))).sum)).sum) := by
  apply Poly.comp List.sum _ Poly.listIntSum
  apply Poly.rawTab n (fun z : α×ℕ => (tab (n z.1) (fun j => f (z,j))).sum) hn
  apply Poly.comp List.sum _ Poly.listIntSum
  exact Poly.rawTab (fun z : α×ℕ => n z.1) f (by fun_prop) hf

@[fun_prop] theorem upperSum_poly {α : Type} [Coding α] [Inhabited α]
    (n : α → ℕ) (f : (α×ℕ)×ℕ → ℤ) (hn : Poly n) (hf : Poly f) :
    Poly (fun a => upperSum (n a) (fun i j => f ((a,i),j))) := by
  have h := doubleIntSum n (fun z : (α×ℕ)×ℕ => if decide (z.1.2<z.2) then f z else 0) hn (by fun_prop)
  exact h.congr (fun a => by simp only [upperSum,decide_eq_true_eq])

@[fun_prop] theorem rowNumerator_poly : Poly (fun z : ℕ×(Matrix ℤ×Row) => rowNumerator z.1 z.2.1 z.2.2) := by
  have hh := upperSum_poly (fun z : ℕ×(Matrix ℤ×Row) => z.2.1.length)
    (fun z : ((ℕ×(Matrix ℤ×Row))×ℕ)×ℕ => get z.1.1.2.2.1 z.1.2 z.2*get z.1.1.2.1 z.1.2 z.2)
    (by fun_prop) (by fun_prop)
  unfold rowNumerator
  fun_prop

@[fun_prop] theorem indexedSlope_poly : Poly (fun z : ℕ×ℕ => indexedSlope z.1 z.2) := by
  have h : Poly (fun z : ℕ×ℕ => if decide (z.2<z.1) then (z.2:ℤ)-1 else (z.1:ℤ)) := by fun_prop
  exact h.congr (fun _ => by simp only [indexedSlope,decide_eq_true_eq])

@[fun_prop] theorem pieceNumerator_poly : Poly (fun z : (ℕ×(ℕ×ℕ))×(ℤ×ℕ) =>
    pieceNumerator z.1.1 z.1.2.1 z.1.2.2 z.2.1 z.2.2) := by
  have h : Poly (fun z : (ℕ×(ℕ×ℕ))×(ℤ×ℕ) => indexedSlope z.1.1 z.2.2*z.2.1*(z.1.2.2:ℤ)+
      if decide (z.2.2<z.1.1) then (z.1.2.1:ℤ)*(cappedPow2 z.1.2.2 (z.1.1-z.2.2):ℤ) else 0) := by fun_prop
  exact h.congr (fun _ => by simp only [pieceNumerator,decide_eq_true_eq])

attribute [local instance] OAI.BinaryMatching.Raw.Optimize.Compiler.instPreorderInt_solutions
@[fun_prop] theorem selectedIndex_poly : Poly (fun z : (ℕ×(ℕ×ℕ))×ℤ => selectedIndex z.1.1 z.1.2.1 z.1.2.2 z.2) := by
  let arg (z : (ℕ×(ℕ×ℕ))×ℤ) := (List.range (z.1.1+1)).argmin (pieceNumerator z.1.1 z.1.2.1 z.1.2.2 z.2)
  have ha : Poly arg := by
    apply Poly.comp _ (fun z : (ℕ×(ℕ×ℕ))×ℤ => (z,List.range (z.1.1+1)))
      (Poly.listArgminParam Poly.intLT (fun z : ((ℕ×(ℕ×ℕ))×ℤ)×ℕ => pieceNumerator z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2)
        (Poly.comp _ (fun z : ((ℕ×(ℕ×ℕ))×ℤ)×ℕ => (z.1.1,(z.1.2,z.2))) pieceNumerator_poly (by fun_prop)))
      (by fun_prop)
  have h : Poly (fun z : (ℕ×(ℕ×ℕ))×ℤ => if (arg z).isSome then (arg z).getD 0 else z.1.1) := by fun_prop
  exact h.congr (fun z => by change _=(arg z).getD _; cases arg z <;> rfl)

@[fun_prop] theorem selectedIndex_params_poly : Poly (fun z : Params×ℤ => selectedIndex z.1.k z.1.D z.1.pow z.2) :=
  Poly.comp _ (fun z : Params×ℤ => ((z.1.k,(z.1.D,z.1.pow)),z.2)) selectedIndex_poly (by fun_prop)
@[fun_prop] theorem scaledPsi_poly : Poly (fun z : Params×ℤ => scaledPsi z.1 z.2) :=
  Poly.comp _ (fun z : Params×ℤ => ((z.1.k,(z.1.D,z.1.pow)),(z.2,selectedIndex z.1.k z.1.D z.1.pow z.2)))
    pieceNumerator_poly (by fun_prop)
@[fun_prop] theorem scaledSlope_poly : Poly (fun z : Params×ℤ => scaledSlope z.1 z.2) :=
  Poly.comp _ (fun z : Params×ℤ => (z.1.k,selectedIndex z.1.k z.1.D z.1.pow z.2)) indexedSlope_poly (by fun_prop)
end BinaryMatching.Raw.Optimize.Compiler
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawOptimizerRowsCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw.Optimize.Compiler
open StackCode StackCode.Poly BinaryMatching.Raw.Compiler

@[fun_prop] theorem capacities_poly : Poly (fun z : ℕ×Matrix ℤ => capacities z.1 z.2) := by
  have h := Poly.rawMatrix Prod.fst (fun z : ((ℕ×Matrix ℤ)×ℕ)×ℕ =>
    if decide (z.1.2<z.2) then (get z.1.1.2 z.1.2 z.2).toNat else
    if decide (z.2<z.1.2) then (get z.1.1.2 z.2 z.1.2).toNat else 0) (by fun_prop) (by fun_prop)
  exact h.congr (fun _ => by simp only [capacities,decide_eq_true_eq])
@[fun_prop] theorem zeroRow_poly : Poly zeroRow := by
  unfold zeroRow
  apply Poly.pair
  · exact Poly.rawMatrix id (fun _ => (0:ℤ)) (by fun_prop) (by fun_prop)
  · fun_prop
@[fun_prop] theorem degreeRow_poly : Poly (fun z : ℕ×(ℕ×Bool) => degreeRow z.1 z.2.1 z.2.2) := by
  have h := Poly.rawMatrix Prod.fst (fun z : ((ℕ×(ℕ×Bool))×ℕ)×ℕ =>
    if decide (z.1.2<z.2) then
      if decide (z.1.2=z.1.1.2.1) || decide (z.2=z.1.1.2.1) then (if z.1.1.2.2 then (1:ℤ) else -1) else 0 else 0)
    (by fun_prop) (by fun_prop)
  have hh := Poly.pair _ (fun z : ℕ×(ℕ×Bool) => if z.2.2 then (-1:ℤ) else 1) h (by fun_prop)
  exact hh.congr (fun _ => by simp only [degreeRow,Bool.or_eq_true,decide_eq_true_eq])
@[fun_prop] theorem cutRow_poly : Poly (fun z : ℕ×Cut => cutRow z.1 z.2) := by
  have h := Poly.rawMatrix Prod.fst (fun z : ((ℕ×Cut)×ℕ)×ℕ =>
    if decide (z.1.2<z.2) then
      if (mem z.1.1.2 z.1.2 && !mem z.1.1.2 z.2) || (mem z.1.1.2 z.2 && !mem z.1.1.2 z.1.2) then (-1:ℤ) else 0 else 0)
    (by fun_prop) (by fun_prop)
  exact (Poly.pair _ (fun _ => (1:ℤ)) h (by fun_prop)).congr (fun _ => by simp only [cutRow,decide_eq_true_eq])
@[fun_prop] theorem rows_poly : Poly (fun z : ℕ×Matrix ℤ => rows z.1 z.2) := by
  have hd : Poly (fun z : ℕ×Matrix ℤ => (List.range z.1).flatMap (fun v => [degreeRow z.1 v true,degreeRow z.1 v false])) :=
    Poly.flatMapWith (fun z : ℕ×Matrix ℤ => List.range z.1)
      (fun z : (ℕ×Matrix ℤ)×ℕ => [degreeRow z.1.1 z.2 true,degreeRow z.1.1 z.2 false]) (by fun_prop) (by fun_prop)
  unfold rows
  fun_prop
attribute [local instance] OAI.BinaryMatching.Raw.Optimize.Compiler.instPreorderInt_solutions_1
@[fun_prop] theorem selectedRow_poly : Poly (fun z : ℕ×(ℕ×Matrix ℤ) => selectedRow z.1 z.2.1 z.2.2) := by
  let arg (z : ℕ×(ℕ×Matrix ℤ)) := (rows z.1 z.2.2).argmax (rowNumerator z.2.1 z.2.2)
  have ha : Poly arg :=
    Poly.comp _ (fun z : ℕ×(ℕ×Matrix ℤ) => (z,rows z.1 z.2.2))
      (Poly.listArgmaxParam Poly.intLT (fun z : (ℕ×(ℕ×Matrix ℤ))×Row => rowNumerator z.1.2.1 z.1.2.2 z.2)
        (by fun_prop)) (by fun_prop)
  have h : Poly (fun z : ℕ×(ℕ×Matrix ℤ) => if (arg z).isSome then (arg z).getD (default:Row) else zeroRow z.1) := by fun_prop
  exact h.congr (fun z => by change _=(arg z).getD _; cases arg z <;> rfl)
end BinaryMatching.Raw.Optimize.Compiler
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawOptimizerCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw.Optimize.Compiler
open StackCode StackCode.Poly BinaryMatching.Raw.Compiler

@[fun_prop] theorem value_poly : Poly (fun z : Params×(Matrix ℤ×Row) => value z.1 z.2.1 z.2.2) := by
  have hs := upperSum_poly (fun z : Params×(Matrix ℤ×Row) => z.1.n)
    (fun z : ((Params×(Matrix ℤ×Row))×ℕ)×ℕ =>
      scaledPsi z.1.1.1 (get z.1.1.2.1 z.1.2 z.2)+
      get z.1.1.1.beta z.1.2 z.2*get z.1.1.2.1 z.1.2 z.2*(z.1.1.1.pow:ℤ))
    (by fun_prop) (by fun_prop)
  unfold value
  fun_prop
@[fun_prop] theorem gradient_poly : Poly (fun z : (Params×(Matrix ℤ×Row))×(ℕ×ℕ) =>
    gradient z.1.1 z.1.2.1 z.1.2.2 z.2.1 z.2.2) := by unfold gradient; fun_prop
@[fun_prop] theorem update_poly : Poly (fun z : Params×(Matrix ℤ×Row) => update z.1 z.2.1 z.2.2) := by
  have hg : Poly (fun z : ((Params×(Matrix ℤ×Row))×ℕ)×ℕ => gradient z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2) :=
    Poly.comp _ (fun z : ((Params×(Matrix ℤ×Row))×ℕ)×ℕ => (z.1.1,(z.1.2,z.2))) gradient_poly (by fun_prop)
  have h := Poly.rawMatrix (fun z : Params×(Matrix ℤ×Row) => z.1.n)
    (fun z : ((Params×(Matrix ℤ×Row))×ℕ)×ℕ => if decide (z.1.2<z.2) then
      min (z.1.1.1.D:ℤ) (max 0 (get z.1.1.2.1 z.1.2 z.2+gradient z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2)) else 0)
    (by fun_prop) (by fun_prop)
  exact h.congr (fun _ => by simp only [update,decide_eq_true_eq])
@[fun_prop] theorem step_poly : Poly step := by
  let r (z : Params×IntState) := selectedRow z.1.n z.1.D z.2.1
  let v (z : Params×IntState) := value z.1 z.2.1 (r z)
  have hr : Poly r := by dsimp [r]; fun_prop
  have hv : Poly v := by dsimp [v]; fun_prop
  have h := Poly.optionCasesWith (fun z : Params×IntState => z.2.2) v
    (fun z : (Params×IntState)×ℤ => max (v z.1) z.2) (by fun_prop) hv (by fun_prop)
  have hm : Poly (fun z : Params×IntState => match z.2.2 with | none => v z | Option.some w => max (v z) w) :=
    h.congr (fun z => by cases z.2.2 <;> rfl)
  have hh := Poly.pair (fun z : Params×IntState => z.1)
    (fun z : Params×IntState => (update z.1 z.2.1 (r z),Option.some (match z.2.2 with | none => v z | Option.some w => max (v z) w)))
    (by fun_prop) (Poly.pair _ _ (by fun_prop) (Poly.comp _ _ Poly.some hm))
  exact hh.congr (fun z => by unfold step; dsimp [r,v]; cases z.2.2 <;> rfl)
@[fun_prop] theorem initial_poly : Poly initial := by
  unfold initial
  have hh := Poly.rawMatrix Params.n (fun _ => (0:ℤ)) (by fun_prop) (by fun_prop)
  fun_prop
@[fun_prop] theorem operandBound_poly : Poly operandBound := by unfold operandBound; fun_prop
@[fun_prop] theorem budget_poly : Poly budget := by unfold budget; fun_prop
@[fun_prop] theorem run_poly : Poly run := by
  have h := Poly.comp _ (fun p : Params => (p.q*p.D,(budget p,initial p)))
    (Poly.guardedIterate step step_poly) (by fun_prop)
  exact Poly.second _ h
@[fun_prop] theorem result_poly : Poly result := by
  exact Poly.comp _ (fun p : Params => ((run p).2.getD 0,p.D*p.pow)) Poly.intDivNat (by fun_prop)
end BinaryMatching.Raw.Optimize.Compiler
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_UnaryClog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.StackCode

def unaryClog (x : ℕ) : ℕ :=
  ((List.range (x+1)).find? (fun j => decide (x≤cappedPow2 x j))).getD 0

lemma unaryClog_eq (x : ℕ) : unaryClog x=Nat.clog 2 x := by
  have hk : Nat.clog 2 x≤x := Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
  have hp (j : ℕ) : (x≤cappedPow2 x j) ↔ Nat.clog 2 x≤j := by
    rw [cappedPow2_eq,le_min_iff]
    simpa only [le_refl,true_and] using (Nat.clog_le_iff_le_pow (by decide : 1<2) (x := x) (y := j)).symm
  have hf : (List.range (x+1)).find? (fun j => decide (x≤cappedPow2 x j))=some (Nat.clog 2 x) := by
    apply List.find?_eq_some_iff_getElem.mpr
    refine ⟨by simp [hp],Nat.clog 2 x,by simpa using Nat.lt_succ_of_le hk,by simp,?_⟩
    intro j hj
    simp only [List.getElem_range,Bool.not_eq_true',decide_eq_false_iff_not,hp]
    omega
  simp only [unaryClog,hf,Option.getD_some]

namespace Poly
@[fun_prop] theorem natClog2 : Poly (Nat.clog 2) := by
  have hf := Poly.findWith (fun x : ℕ => List.range (x+1))
    (fun z : ℕ×ℕ => decide (z.1≤cappedPow2 z.1 z.2)) (by fun_prop) (by fun_prop)
  have h : Poly unaryClog := by unfold unaryClog; fun_prop
  exact h.congr unaryClog_eq

@[fun_prop] theorem powClog2 : Poly (fun x : ℕ => 2^(Nat.clog 2 x)) := by
  have hbound (x : ℕ) : 2^(Nat.clog 2 x)≤2*x+1 := by
    by_cases hx : x≤1
    · rw [Nat.clog_of_right_le_one hx]; simp
    · have hpos : 0<Nat.clog 2 x := Nat.clog_pos (by decide) (by omega)
      have hh : 2^(Nat.clog 2 x-1)<x := by
        simpa only [Nat.pred_eq_sub_one] using Nat.pow_pred_clog_lt_self (by decide : 1<2) (by omega : 1<x)
      have he : 2^(Nat.clog 2 x)=2^(Nat.clog 2 x-1)*2 := by rw [←pow_succ,Nat.sub_add_cancel hpos]
      rw [he]
      omega
  have h : Poly (fun x : ℕ => cappedPow2 (2*x+1) (Nat.clog 2 x)) := by fun_prop
  exact h.congr (fun x => cappedPow2_of_le _ _ (hbound x))
end Poly
end BinaryMatching.StackCode
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
open StackCode Algorithm Raw.Optimize
abbrev Data := ℕ×List Rec

def repr (r : Record) : Rec := (r.left,(r.right,r.multiplicity.bits))
def decodeRecord (b : ℕ) (r : Parse.RecordBits) : Rec :=
  (Parse.boundedValue b r.1,(Parse.boundedValue b r.2.1,r.2.2))
lemma decodeRecord_repr (G : Input) (b : ℕ) (hb : G.n≤b) (r : Record) (hr : r∈G.records) :
    decodeRecord b (Parse.recordRepr r)=repr r := by
  have hv := G.valid r hr
  simp only [decodeRecord,Parse.recordRepr,Parse.boundedValue_bits,repr]
  rw [min_eq_right (by omega : r.left≤b),min_eq_right (by omega : r.right≤b)]
@[fun_prop] theorem decodeRecord_poly : Poly (fun z : ℕ×Parse.RecordBits => decodeRecord z.1 z.2) := by
  unfold decodeRecord
  fun_prop

def multiplicityBits (rs : List Rec) (i j : ℕ) : List Bool :=
  ((rs.find? (fun a => a.1=i && a.2.1=j)).map (fun a => a.2.2)).getD []
lemma multiplicityBits_repr (G : Input) (i j : ℕ) :
    multiplicityBits (G.records.map repr) i j=(rawMultiplicity G i j).bits := by
  unfold multiplicityBits rawMultiplicity
  rw [List.find?_map]
  change (((G.records.find? (fun r => r.left=i && r.right=j)).map repr).map (fun a => a.2.2)).getD []=_
  cases G.records.find? (fun r => r.left=i && r.right=j) <;> rfl
lemma multiplicityBits_pair (G : Input) (e : Pair G.n) :
    multiplicityBits (G.records.map repr) e.val.1.val e.val.2.val=(multiplicity G e).bits := by
  rw [multiplicityBits_repr]
  unfold rawMultiplicity multiplicity
  cases G.records.find? (fun r => r.left=e.val.1.val && r.right=e.val.2.val) <;> rfl
@[fun_prop] theorem multiplicityBits_poly : Poly (fun z : List Rec×(ℕ×ℕ) => multiplicityBits z.1 z.2.1 z.2.2) := by
  have hf := Poly.findWith (fun z : List Rec×(ℕ×ℕ) => z.1)
    (fun z : (List Rec×(ℕ×ℕ))×Rec => decide (z.2.1=z.1.2.1) && decide (z.2.2.1=z.1.2.2)) (by fun_prop) (by fun_prop)
  unfold multiplicityBits
  fun_prop

def bitsBudget (rs : List Rec) : ℕ := (rs.map (fun r => r.2.2.length-1)).foldl max 0
lemma bitsBudget_repr (G : Input) : bitsBudget (G.records.map repr)=B G := by
  unfold bitsBudget B
  simp only [List.map_map,Function.comp_def,repr,←Parse.log2_bits_length]
@[fun_prop] theorem bitsBudget_poly : Poly bitsBudget := by
  have hf := Poly.listFoldAdd (fun z : ℕ×ℕ => max z.1 z.2) Poly.natMax 1 (by
    intro z
    simp only [code_nat_length]
    omega)
  exact Poly.comp _ (fun rs : List Rec => (rs.map (fun r => r.2.2.length-1),0)) hf (by fun_prop)

def pairs (n : ℕ) : ℕ := (upperSum n (fun _ _ => (1:ℤ))).toNat
lemma pairs_eq (n : ℕ) : pairs n=q n := by
  have h := upperSum_rep (fun _ : Pair n => (1:ℤ)) (fun _ _ => (1:ℤ)) (fun _ => rfl)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at h
  unfold pairs
  rw [h]
  simp [q]
@[fun_prop] theorem pairs_poly : Poly pairs := by
  have h := Raw.Optimize.Compiler.upperSum_poly id (fun _ => (1:ℤ)) (by fun_prop) (by fun_prop)
  unfold pairs
  fun_prop

def betaValue (rs : List Rec) (L i j : ℕ) : ℤ :=
  let bits := multiplicityBits rs i j
  if bits.isEmpty then -(L:ℤ) else (bits.length-1:ℕ)
lemma betaValue_repr (G : Input) (e : Pair G.n) :
    betaValue (G.records.map repr) (L G) e.val.1.val e.val.2.val=Algorithm.beta G e := by
  unfold betaValue Algorithm.beta
  rw [multiplicityBits_pair]
  simp only [List.isEmpty_iff,Parse.bits_nil_iff,Parse.log2_bits_length]
@[fun_prop] theorem betaValue_poly : Poly (fun z : (List Rec×ℕ)×(ℕ×ℕ) => betaValue z.1.1 z.1.2 z.2.1 z.2.2) := by
  unfold betaValue
  fun_prop

def betaMatrix (n : ℕ) (rs : List Rec) (L : ℕ) : Matrix ℤ :=
  matrix n (fun i j => if i < j then betaValue rs L i j else 0)
lemma betaMatrix_repr (G : Input) :
    betaMatrix G.n (G.records.map repr) (L G)=tableRep (toTable (Algorithm.beta G)) := by
  apply matrix_eq_rep
  intro i j
  by_cases hij : i < j
  · simp [toTable,tabulate,hij,betaValue_repr G ⟨(i,j),hij⟩]
  · simp [toTable,tabulate,hij]
@[fun_prop] theorem betaMatrix_poly : Poly (fun z : Data×ℕ => betaMatrix z.1.1 z.1.2 z.2) := by
  have hb : Poly (fun z : ((Data×ℕ)×ℕ)×ℕ => betaValue z.1.1.1.2 z.1.1.2 z.1.2 z.2) :=
    Poly.comp _ (fun z : ((Data×ℕ)×ℕ)×ℕ => ((z.1.1.1.2,z.1.1.2),(z.1.2,z.2))) betaValue_poly (by fun_prop)
  have h := Poly.rawMatrix (fun z : Data×ℕ => z.1.1)
    (fun z : ((Data×ℕ)×ℕ)×ℕ => if decide (z.1.2<z.2) then betaValue z.1.1.1.2 z.1.1.2 z.1.2 z.2 else 0)
    (by fun_prop) (by fun_prop)
  exact h.congr (fun _ => by simp only [betaMatrix,decide_eq_true_eq])

def parameters (z : Data) : Params :=
  let q := pairs z.1
  let k := Nat.clog 2 q
  let l := 100*(z.1+bitsBudget z.2+1)^3
  let m := q*(k+l)*(2+10*z.1^2)
  let d := q*(k+l+m)^2
  ⟨z.1,q,k,l,d,m,2^(Nat.clog 2 q),betaMatrix z.1 z.2 l⟩
lemma parameters_repr (G : Input) : parameters (G.n,G.records.map repr)=params G := by
  simp only [parameters,pairs_eq,bitsBudget_repr,params,K,L,M₀,D₀,A₀]
  congr 1
  exact betaMatrix_repr G
@[fun_prop] theorem parameters_poly : Poly parameters := by
  let p (z : Data) : ParamData :=
    let q := pairs z.1
    let k := Nat.clog 2 q
    let l := 100*(z.1+bitsBudget z.2+1)^3
    let m := q*(k+l)*(2+10*z.1^2)
    let d := q*(k+l+m)^2
    (z.1,(q,(k,(l,(d,(m,(2^(Nat.clog 2 q),betaMatrix z.1 z.2 l)))))))
  have hb : Poly (fun z : Data => betaMatrix z.1 z.2 (100*(z.1+bitsBudget z.2+1)^3)) :=
    Poly.comp _ (fun z : Data => (z,100*(z.1+bitsBudget z.2+1)^3)) betaMatrix_poly (by fun_prop)
  have hpw : Poly (fun z : Data => 2^(Nat.clog 2 (pairs z.1))) :=
    Poly.comp _ (fun z : Data => pairs z.1) Poly.powClog2 (by fun_prop)
  have hp : Poly p := by dsimp only [p]; fun_prop
  exact Poly.comp _ p Raw.Optimize.Compiler.paramsOfData_poly hp
end BinaryMatching.Raw.InputData
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_BinarySolve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw.InputData
open StackCode Algorithm Optimize

@[fun_prop] theorem powerBits_poly : Poly powerBits := by unfold powerBits; fun_prop

def smallSolve (z : Data) : List Bool :=
  if z.1=0 then [true] else
  if z.1%2=1 then [] else
  if z.1=2 then multiplicityBits z.2 0 1 else
  let r := result (parameters z)
  if r < -10*(z.1:ℤ) then [] else powerBits (r-5*(z.1:ℤ)).toNat

def smallEstimate (G : Input) : ℕ :=
  if G.n=0 then 1 else
  if G.n%2=1 then 0 else
  if G.n=2 then rawMultiplicity G 0 1 else integralEstimate G
lemma smallSolve_repr (G : Input) : smallSolve (G.n,G.records.map repr)=(smallEstimate G).bits := by
  unfold smallSolve smallEstimate
  dsimp only
  by_cases hn0 : G.n=0
  · simp only [hn0,ite_true]; rfl
  simp only [hn0,ite_false]
  by_cases ho : G.n%2=1
  · simp only [ho,ite_true]; rfl
  simp only [ho,ite_false]
  by_cases hn2 : G.n=2
  · simpa only [hn2,ite_true] using multiplicityBits_repr G 0 1
  simp only [hn2,ite_false]
  have he : Even G.n := Nat.even_iff.mpr (by omega)
  have hn : 2≤G.n := by omega
  rw [parameters_repr,result_rep G hn he]
  dsimp only [integralEstimate]
  split_ifs
  · rfl
  · exact powerBits_eq _
@[fun_prop] theorem smallSolve_poly : Poly smallSolve := by
  have h : Poly (fun z : Data => if decide (z.1=0) then [true] else
      if decide (z.1%2=1) then [] else if decide (z.1=2) then multiplicityBits z.2 0 1 else
      if decide (result (parameters z) < -10*(z.1:ℤ)) then [] else
        powerBits (result (parameters z)-5*(z.1:ℤ)).toNat) := by fun_prop
  exact h.congr (fun z => by simp only [smallSolve,decide_eq_true_eq])

def solve (z : Data) : List Bool := if 2*z.2.length<z.1 then [] else smallSolve z

def sparseEstimate (G : Input) : ℕ := if 2*G.records.length<G.n then 0 else smallEstimate G
@[fun_prop] theorem solve_poly : Poly solve := by
  have hh : Poly (fun z : Data => if decide (2*z.2.length<z.1) then [] else smallSolve z) := by fun_prop
  exact hh.congr (fun z => by simp only [solve,decide_eq_true_eq])

end BinaryMatching.Raw.InputData

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_Approximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching
open scoped BigOperators

namespace Approximation

def term (G : Input) (j : ℕ) : ℕ :=
  BinaryMatching.Raw.InputData.sparseEstimate (expand G j)

def output (G : Input) : ℕ × ℕ :=
  (Accumulator.Q (term G) G.n, G.n.factorial)

end Approximation
end LoopMatching

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_BitAddRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.BitAdd
open BinaryMatching.StackCode

lemma boolList_code_length (l : List Bool) : (encode l).length = 3*l.length := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [code_cons, pairBits_length, encode_bool, List.length_cons,
      List.length_nil, ih]
    omega

lemma state_code_length (s : State) :
    (encode s).length = 12*s.1.1.length + 6*s.1.2.length + 3*s.2.2.length + 6 := by
  simp only [encode_prod, pairBits_length, boolList_code_length, encode_bool,
    List.length_singleton]
  omega

@[fun_prop] theorem xor_poly : Poly (fun z : Bool × Bool => xor z.1 z.2) := by
  unfold xor
  fun_prop

@[fun_prop] theorem digit_poly : Poly (fun z : (Bool × Bool) × Bool => digit z.1.1 z.1.2 z.2) := by
  unfold digit
  fun_prop

@[fun_prop] theorem carry_poly : Poly (fun z : (Bool × Bool) × Bool => carry z.1.1 z.1.2 z.2) := by
  unfold carry
  fun_prop

@[fun_prop] theorem step_poly : Poly step := by
  have hi : Poly (fun z : State × Bool =>
      ((z.1.1.1.headD false, z.1.1.2.headD false), z.1.2.1)) := by fun_prop
  have hc : Poly (fun z : State × Bool =>
      carry (z.1.1.1.headD false) (z.1.1.2.headD false) z.1.2.1) :=
    Poly.comp _ _ carry_poly hi
  have hd : Poly (fun z : State × Bool =>
      digit (z.1.1.1.headD false) (z.1.1.2.headD false) z.1.2.1) :=
    Poly.comp _ _ digit_poly hi
  have ho : Poly (fun z : State × Bool =>
      z.1.2.2 ++ [digit (z.1.1.1.headD false) (z.1.1.2.headD false) z.1.2.1]) :=
    Poly.comp (fun p : List Bool × Bool => p.1 ++ [p.2]) _ (by fun_prop)
      (Poly.pair _ _ (by fun_prop) hd)
  unfold step
  exact Poly.pair _ _ (by fun_prop) (Poly.pair _ _ hc ho)

lemma step_growth (z : State × Bool) :
    (encode (step z)).length ≤ (encode z.1).length + 1*(2*(encode z.2).length+1) := by
  rw [state_code_length, state_code_length]
  simp only [step, encode_bool, List.length_singleton, List.length_append]
  have hx : z.1.1.1.tail.length ≤ z.1.1.1.length := by simp
  have hy : z.1.1.2.tail.length ≤ z.1.1.2.length := by simp
  omega

@[fun_prop] theorem run_poly : Poly (fun z : List Bool × State => run z.1 z.2) := by
  exact Poly.listFoldAdd step step_poly 1 step_growth

@[fun_prop] theorem initial_poly : Poly initial := by
  unfold initial
  fun_prop

@[fun_prop] theorem finish_poly : Poly finish := by
  unfold finish
  fun_prop

@[fun_prop] theorem add_poly : Poly add := by
  unfold add
  fun_prop

end LoopMatching.BitAdd

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_BitNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.BitNormalize
open BinaryMatching.StackCode
open BitAdd (value)

@[fun_prop] theorem step_poly : Poly step := by
  unfold step
  fun_prop

lemma step_growth (z : List Bool × Bool) :
    (encode (step z)).length ≤ (encode z.1).length + 1*(2*(encode z.2).length+1) := by
  rw [BitAdd.boolList_code_length, BitAdd.boolList_code_length]
  simp only [encode_bool, List.length_singleton]
  have h := step_length z.1 z.2
  change (step z).length ≤ z.1.length + 1 at h
  omega

@[fun_prop] theorem normalize_poly : Poly normalize := by
  have hf := Poly.listFoldAdd step step_poly 1 step_growth
  have hh := Poly.comp _ (fun l : List Bool => (l.reverse, ([] : List Bool))) hf (by fun_prop)
  exact hh.congr (fun l => by simp [normalize, List.foldl_reverse])

def add (z : List Bool × List Bool) : List Bool := normalize (BitAdd.add z)

@[fun_prop] theorem add_poly : Poly add := by unfold add; fun_prop

theorem add_eq_bits (z : List Bool × List Bool) :
    add z = (value z.1 + value z.2).bits := by
  rw [add, normalize_eq_bits, BitAdd.value_add]

theorem value_add (z : List Bool × List Bool) : value (add z) = value z.1 + value z.2 := by
  rw [add, value_normalize, BitAdd.value_add]

theorem length_add (z : List Bool × List Bool) :
    (add z).length ≤ max z.1.length z.2.length + 1 := by
  rw [add_eq_bits]
  exact BitAdd.length_bits_value_add z.1 z.2

end LoopMatching.BitNormalize

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_BinaryMultiply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.SmallBinaryMultiply
open BinaryMatching.StackCode Polynomial

def step (s : State) : State := (s.1, BitNormalize.add (s.1,s.2))
def mul (z : ℕ × List Bool) : List Bool := (step^[z.1] (initial z)).2

@[fun_prop] theorem step_poly : Poly step := by
  unfold step
  fun_prop

@[fun_prop] theorem initial_poly : Poly initial := by
  unfold initial
  fun_prop

lemma orbit_first (z : ℕ × List Bool) (k : ℕ) :
    (step^[k] (initial z)).1 = z.2 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [Function.iterate_succ_apply', step] using ih

lemma orbit_value (z : ℕ × List Bool) (k : ℕ) :
    BitAdd.value (step^[k] (initial z)).2 = k * BitAdd.value z.2 := by
  induction k with
  | zero => simp [initial, BitAdd.value]
  | succ k ih =>
    simp only [Function.iterate_succ_apply', step, BitNormalize.value_add,
      orbit_first, ih]
    ring

lemma orbit_length (z : ℕ × List Bool) (k : ℕ) :
    (step^[k] (initial z)).2.length ≤ z.2.length + k := by
  induction k with
  | zero => simp [initial]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change (BitNormalize.add ((step^[k] (initial z)).1,
      (step^[k] (initial z)).2)).length ≤ z.2.length + (k+1)
    have h := BitNormalize.length_add ((step^[k] (initial z)).1,
      (step^[k] (initial z)).2)
    change (BitNormalize.add ((step^[k] (initial z)).1,
      (step^[k] (initial z)).2)).length ≤
        max (step^[k] (initial z)).1.length (step^[k] (initial z)).2.length + 1 at h
    rw [orbit_first] at h ⊢
    have hm : max z.2.length (step^[k] (initial z)).2.length ≤ z.2.length+k :=
      max_le (by omega) ih
    exact h.trans (Nat.add_le_add_right hm 1)

lemma orbit_code_length (z : ℕ × List Bool) (k : ℕ) :
    (encode (step^[k] (initial z))).length ≤ 9*z.2.length+3*k+1 := by
  rw [code_pair_length, BitAdd.boolList_code_length,
    BitAdd.boolList_code_length, orbit_first]
  have h := orbit_length z k
  omega

@[fun_prop] theorem orbit_poly :
    Poly (fun z : ℕ × List Bool => step^[z.1] (initial z)) := by
  apply Poly.iterateFrom step step_poly Prod.fst initial (by fun_prop)
    initial_poly (10*(X+1))
  intro z k hk
  have h := orbit_code_length z k
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]
  have he : (encode (z.1,initial z)).length = 2*z.1+6*z.2.length+2 := by
    simp only [initial, code_pair_length, code_nat_length,
      BitAdd.boolList_code_length, List.length_nil]
    omega
  change (encode (step^[k] (initial z))).length ≤
    10*((encode (z.1,initial z)).length+1)
  rw [he]
  omega

@[fun_prop] theorem mul_poly : Poly mul := by
  unfold mul
  fun_prop

theorem value_mul (z : ℕ × List Bool) :
    BitAdd.value (mul z) = z.1 * BitAdd.value z.2 := orbit_value z z.1

theorem length_mul (z : ℕ × List Bool) :
    (mul z).length ≤ z.2.length + z.1 := orbit_length z z.1

def horner (z : (ℕ × List Bool) × List Bool) : List Bool :=
  BitNormalize.add (mul z.1,z.2)

@[fun_prop] theorem horner_poly : Poly horner := by
  unfold horner
  fun_prop

theorem value_horner (z : (ℕ × List Bool) × List Bool) :
    BitAdd.value (horner z) = z.1.1 * BitAdd.value z.1.2 + BitAdd.value z.2 := by
  simp only [horner, BitNormalize.value_add, value_mul]

theorem length_horner (z : (ℕ × List Bool) × List Bool) :
    (horner z).length ≤ max z.1.2.length z.2.length + z.1.1 + 1 := by
  have ha := BitNormalize.length_add (mul z.1,z.2)
  change (BitNormalize.add (mul z.1,z.2)).length ≤
    max (mul z.1).length z.2.length + 1 at ha
  have hm := length_mul z.1
  have hx := le_max_left z.1.2.length z.2.length
  have hy := le_max_right z.1.2.length z.2.length
  have hb : max (mul z.1).length z.2.length ≤
      max z.1.2.length z.2.length + z.1.1 := max_le (by omega) (by omega)
  exact ha.trans (Nat.add_le_add_right hb 1)

end LoopMatching.SmallBinaryMultiply

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_CountedParser
attribute [-instance] _root_.OAI.BinaryMatching.Raw.Optimize.instCodingParams _root_.OAI.BinaryMatching.RecursiveEval.instCodingBranch _root_.OAI.BinaryMatching.RecursiveEval.instCodingCommand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.InputMachine
open BinaryMatching BinaryMatching.StackCode Polynomial

def countedRecords (k : ℕ) (l : List Bool) : List Bool × List Parse.RecordBits :=
  Parse.recordStep^[k] (l,[])

lemma recordStep_records_suffix (rs : List BinaryMatching.Record)
    (suffix : List Bool) (acc : List Parse.RecordBits) :
    Parse.recordStep^[rs.length] (rs.flatMap encodeRecord ++ suffix,acc) =
      (suffix,acc ++ rs.map Parse.recordRepr) := by
  induction rs generalizing acc with
  | nil => simp
  | cons r rs ih =>
    rw [List.length_cons,Function.iterate_succ_apply,List.flatMap_cons,
      List.append_assoc,Parse.recordStep_encode,ih]
    simp [List.append_assoc]

lemma countedRecords_encoded (rs : List BinaryMatching.Record) (suffix : List Bool) :
    countedRecords rs.length (rs.flatMap encodeRecord ++ suffix) =
      (suffix,rs.map Parse.recordRepr) := by
  simpa only [countedRecords,List.nil_append] using
    recordStep_records_suffix rs suffix []

@[fun_prop] theorem countedRecords_poly :
    Poly (fun z : ℕ × List Bool => countedRecords z.1 z.2) := by
  have hs : Poly Parse.recordStep := by unfold Parse.recordStep; fun_prop
  have hi := Poly.boundedIterate Parse.recordStep hs (100*(X+1)^2) (by
    intro z j hj
    obtain ⟨h₁,h₂⟩ := Parse.recordStep_iterate_size j z.2
    have he : (encode (Parse.recordStep^[j] z.2)).length ≤
        6*z.2.1.length+(encode z.2.2).length+j*(40*z.2.1.length+21)+1 := by
      simp only [code_pair_length,cut_code_length]
      omega
    have hl : z.2.1.length≤(encode z).length := by
      simp only [code_pair_length,code_nat_length,cut_code_length]; omega
    have hk : j≤(encode z).length := by
      simp only [code_pair_length,code_nat_length]; omega
    have ha : (encode z.2.2).length≤(encode z).length := by
      simp only [code_pair_length]; omega
    have hm := Nat.mul_le_mul hk hl
    simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
    nlinarith)
  exact Poly.comp _ (fun z : ℕ × List Bool => (z.1,(z.2,([]:List Parse.RecordBits))))
    hi (by fun_prop)

def ordinaryPrefix (l : List Bool) : List Bool × (List Bool × List Parse.RecordBits) :=
  let n := Parse.numeral l
  let r := Parse.numeral n.2
  (n.1,countedRecords (Parse.boundedValue l.length r.1) r.2)

@[fun_prop] theorem ordinaryPrefix_poly : Poly ordinaryPrefix := by
  unfold ordinaryPrefix
  fun_prop

lemma ordinaryPrefix_encoded (G : LoopMatching.Input) :
    ordinaryPrefix (LoopMatching.encodeInput G) =
      (G.n.bits,(encodeNat G.loops.length ++ G.loops.flatMap encodeLoopRecord,
        G.ordinary.records.map Parse.recordRepr)) := by
  have hr := Parse.records_length_le_bits G.ordinary.records
  have hbound : G.ordinary.records.length ≤ (LoopMatching.encodeInput G).length := by
    simp only [LoopMatching.encodeInput,BinaryMatching.encodeInput,List.length_append]
    omega
  unfold ordinaryPrefix LoopMatching.encodeInput BinaryMatching.encodeInput
  simp only [List.append_assoc,Parse.numeral_encode,Parse.boundedValue_bits]
  simp only [LoopMatching.encodeInput,BinaryMatching.encodeInput,List.append_assoc] at hbound
  rw [min_eq_right hbound,countedRecords_encoded]

end LoopMatching.InputMachine

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_ExpandBijection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.MatchingEntropy.LooplessGraph.crossesDecidable _root_.OAI.MatchingEntropy.LooplessGraph.incidentDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

noncomputable section
open scoped BigOperators
namespace LoopMatching

def SupportedMatching (G : Input) (j : ℕ) :=
  {N : (BinaryMatching.completeGraph (expand G j).n).Matching //
    ∀ e ∈ N.val, e.val.1.val < G.n}

lemma matching_edge_unique (G : Input) (j : ℕ)
    (N : (BinaryMatching.completeGraph (expand G j).n).Matching)
    (v : Fin (expand G j).n) (e f : BinaryMatching.Pair (expand G j).n)
    (he : e ∈ N.val) (hf : f ∈ N.val)
    (hve : (BinaryMatching.completeGraph (expand G j).n).Incident v e)
    (hvf : (BinaryMatching.completeGraph (expand G j).n).Incident v f) : e = f := by
  obtain ⟨a, ha, hu⟩ := N.property v
  exact (hu e ⟨he,hve⟩).trans (hu f ⟨hf,hvf⟩).symm

def restrictMatching (G : Input) (j : ℕ) (N : SupportedMatching G j) :
    PartialMatching G.n := by
  classical
  refine ⟨Finset.univ.filter (fun e => oldPair G j e ∈ N.val.val), ?_⟩
  intro v e he f hf hve hvf
  apply oldPair_injective G j
  exact matching_edge_unique G j N.val (oldVertex G j v) _ _
    (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2
    ((incident_oldPair G j v e).mpr hve) ((incident_oldPair G j v f).mpr hvf)

@[simp] lemma mem_restrictMatching (G : Input) (j : ℕ) (N : SupportedMatching G j)
    (e : BinaryMatching.Pair G.n) :
    e ∈ (restrictMatching G j N).val ↔ oldPair G j e ∈ N.val.val := by
  simp [restrictMatching]

lemma exists_crossPartner (G : Input) (j : ℕ) (N : SupportedMatching G j)
    (d : Fin j) : ∃ v : Fin G.n, crossPair G j v d ∈ N.val.val := by
  obtain ⟨e,⟨he,hi⟩,hu⟩ := N.val.property (dummyVertex G j d)
  have hl := N.property e he
  have hr : e.val.2.val = G.n + d.val := by
    rcases hi with hi | hi
    · have hh := congrArg Fin.val hi
      dsimp [BinaryMatching.completeGraph, dummyVertex] at hh
      omega
    · exact congrArg Fin.val hi
  let v : Fin G.n := ⟨e.val.1.val,hl⟩
  refine ⟨v, ?_⟩
  have hh : crossPair G j v d = e := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · rfl
    · exact hr.symm
  simpa only [hh] using he

def crossPartner (G : Input) (j : ℕ) (N : SupportedMatching G j) (d : Fin j) : Fin G.n :=
  Classical.choose (exists_crossPartner G j N d)

lemma crossPartner_mem (G : Input) (j : ℕ) (N : SupportedMatching G j) (d : Fin j) :
    crossPair G j (crossPartner G j N d) d ∈ N.val.val :=
  Classical.choose_spec (exists_crossPartner G j N d)

lemma crossPartner_eq (G : Input) (j : ℕ) (N : SupportedMatching G j)
    (v : Fin G.n) (d : Fin j) (hv : crossPair G j v d ∈ N.val.val) :
    crossPartner G j N d = v := by
  have he := matching_edge_unique G j N.val (dummyVertex G j d) _ _
    (crossPartner_mem G j N d) hv (Or.inr rfl) (Or.inr rfl)
  exact (crossPair_injective G j he).1

lemma mem_loopVertices_iff' {n : ℕ} (M : PartialMatching n) (v : Fin n) :
    v ∈ loopVertices M ↔ ∀ e ∈ M.val, ¬ (BinaryMatching.completeGraph n).Incident v e := by
  unfold loopVertices
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma crossPartner_uncovered (G : Input) (j : ℕ) (N : SupportedMatching G j) (d : Fin j) :
    crossPartner G j N d ∈ loopVertices (restrictMatching G j N) := by
  classical
  apply (mem_loopVertices_iff' _ _).mpr
  intro e he hi
  apply oldPair_ne_crossPair G j e (crossPartner G j N d) d
  exact matching_edge_unique G j N.val (oldVertex G j (crossPartner G j N d)) _ _
    ((mem_restrictMatching G j N e).mp he) (crossPartner_mem G j N d)
    ((incident_oldPair G j _ e).mpr hi) (Or.inl rfl)

lemma crossPartner_injective (G : Input) (j : ℕ) (N : SupportedMatching G j) :
    Function.Injective (crossPartner G j N) := by
  intro d c h
  have he := matching_edge_unique G j N.val (oldVertex G j (crossPartner G j N d))
    _ _ (crossPartner_mem G j N d) (crossPartner_mem G j N c)
    (Or.inl rfl) (Or.inl (congrArg (oldVertex G j) h.symm))
  exact (crossPair_injective G j he).2

lemma crossPartner_surjective (G : Input) (j : ℕ) (N : SupportedMatching G j)
    (v : loopVertices (restrictMatching G j N)) :
    ∃ d : Fin j, crossPartner G j N d = v.val := by
  classical
  obtain ⟨e,⟨he,hi⟩,hu⟩ := N.val.property (oldVertex G j v.val)
  have hl := N.property e he
  have hr : G.n ≤ e.val.2.val := by
    by_contra hh
    have hright : e.val.2.val < G.n := by omega
    let f : BinaryMatching.Pair G.n :=
      ⟨(⟨e.val.1.val,hl⟩,⟨e.val.2.val,hright⟩), e.property⟩
    have hef : oldPair G j f = e := by
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> rfl
    have hf : f ∈ (restrictMatching G j N).val := by
      rw [mem_restrictMatching, hef]
      exact he
    have huv := (mem_loopVertices_iff' _ _).mp v.property
    apply huv f hf
    apply (incident_oldPair G j v.val f).mp
    simpa only [hef] using hi
  have hleft : e.val.1.val = v.val.val := by
    rcases hi with hi | hi
    · exact congrArg Fin.val hi
    · have hh := congrArg Fin.val hi
      have hv := v.val.isLt
      dsimp [BinaryMatching.completeGraph,oldVertex] at hh
      omega
  let d : Fin j := ⟨e.val.2.val-G.n, by
    have he2 := e.val.2.isLt
    simp only [expand_n] at he2
    omega⟩
  have hed : crossPair G j v.val d = e := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · exact hleft.symm
    · dsimp [crossPair,d]
      omega
  exact ⟨d,crossPartner_eq G j N v.val d (by simpa only [hed] using he)⟩

def dummyEquiv (G : Input) (j : ℕ) (N : SupportedMatching G j) :
    Fin j ≃ ↥(loopVertices (restrictMatching G j N)) :=
  Equiv.ofBijective (fun d => ⟨crossPartner G j N d,crossPartner_uncovered G j N d⟩)
    ⟨fun d c h => crossPartner_injective G j N (congrArg Subtype.val h), by
      intro v
      obtain ⟨d,hd⟩ := crossPartner_surjective G j N v
      exact ⟨d,Subtype.ext hd⟩⟩

@[simp] lemma incident_cross_old (G : Input) (j : ℕ) (v w : Fin G.n) (d : Fin j) :
    (BinaryMatching.completeGraph (expand G j).n).Incident
      (oldVertex G j v) (crossPair G j w d) ↔ w = v := by
  have hv := v.isLt
  simp only [MatchingEntropy.LooplessGraph.Incident, BinaryMatching.completeGraph,
    crossPair, oldVertex, Fin.ext_iff]
  omega

@[simp] lemma incident_cross_dummy (G : Input) (j : ℕ) (v : Fin G.n) (d c : Fin j) :
    (BinaryMatching.completeGraph (expand G j).n).Incident
      (dummyVertex G j d) (crossPair G j v c) ↔ c = d := by
  have hv := v.isLt
  simp only [MatchingEntropy.LooplessGraph.Incident, BinaryMatching.completeGraph,
    crossPair, dummyVertex, Fin.ext_iff]
  omega

@[simp] lemma not_incident_old_dummy (G : Input) (j : ℕ)
    (e : BinaryMatching.Pair G.n) (d : Fin j) :
    ¬ (BinaryMatching.completeGraph (expand G j).n).Incident
      (dummyVertex G j d) (oldPair G j e) := by
  have h1 := e.val.1.isLt
  have h2 := e.val.2.isLt
  simp only [MatchingEntropy.LooplessGraph.Incident, BinaryMatching.completeGraph,
    oldPair, dummyVertex, Fin.ext_iff]
  omega

def assembledEdges (G : Input) (j : ℕ) (M : PartialMatching G.n)
    (b : Fin j ≃ ↥(loopVertices M)) : Finset (BinaryMatching.Pair (expand G j).n) := by
  classical
  exact M.val.image (oldPair G j) ∪ Finset.univ.image (fun d => crossPair G j (b d).val d)

lemma mem_assembledEdges (G : Input) (j : ℕ) (M : PartialMatching G.n)
    (b : Fin j ≃ ↥(loopVertices M)) (e : BinaryMatching.Pair (expand G j).n) :
    e ∈ assembledEdges G j M b ↔
      (∃ f ∈ M.val, oldPair G j f = e) ∨ (∃ d, crossPair G j (b d).val d = e) := by
  classical
  simp only [assembledEdges, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]

lemma assembledEdges_perfect (G : Input) (j : ℕ) (M : PartialMatching G.n)
    (b : Fin j ≃ ↥(loopVertices M)) :
    (BinaryMatching.completeGraph (expand G j).n).IsPerfectMatching
      (assembledEdges G j M b) := by
  classical
  intro x
  by_cases hx : x.val < G.n
  · let v : Fin G.n := ⟨x.val,hx⟩
    have hxv : x = oldVertex G j v := by apply Fin.ext; rfl
    rw [hxv]
    by_cases hv : ∃ e ∈ M.val, (BinaryMatching.completeGraph G.n).Incident v e
    · obtain ⟨e,he,hi⟩ := hv
      refine ⟨oldPair G j e, ⟨?_,(incident_oldPair G j v e).mpr hi⟩, ?_⟩
      · exact (mem_assembledEdges G j M b _).mpr (Or.inl ⟨e,he,rfl⟩)
      · intro f hf
        rcases (mem_assembledEdges G j M b f).mp hf.1 with ⟨a,ha,rfl⟩ | ⟨d,rfl⟩
        · exact congrArg (oldPair G j)
            (M.property v a ha e he ((incident_oldPair G j v a).mp hf.2) hi)
        · have hbv := (incident_cross_old G j v (b d).val d).mp hf.2
          have hloop := (mem_loopVertices_iff' _ _).mp (b d).property
          exact False.elim (hloop e he (by simpa only [hbv] using hi))
    · have hvloop : v ∈ loopVertices M := by
        simp only [loopVertices,Finset.mem_filter,Finset.mem_univ,true_and]
        simpa only [not_exists,not_and] using hv
      let d := b.symm ⟨v,hvloop⟩
      have hbd : (b d).val = v := congrArg Subtype.val (b.apply_symm_apply _)
      refine ⟨crossPair G j (b d).val d, ⟨?_, ?_⟩, ?_⟩
      · exact (mem_assembledEdges G j M b _).mpr (Or.inr ⟨d,rfl⟩)
      · exact (incident_cross_old G j v (b d).val d).mpr hbd
      · intro f hf
        rcases (mem_assembledEdges G j M b f).mp hf.1 with ⟨a,ha,rfl⟩ | ⟨c,rfl⟩
        · exact False.elim (hv ⟨a,ha,(incident_oldPair G j v a).mp hf.2⟩)
        · have hbc := (incident_cross_old G j v (b c).val c).mp hf.2
          have hcd : c = d := b.injective (Subtype.ext (hbc.trans hbd.symm))
          subst c
          rfl
  · let d : Fin j := ⟨x.val-G.n,by have := x.isLt; simp only [expand_n] at this; omega⟩
    have hxd : x = dummyVertex G j d := by apply Fin.ext; dsimp [dummyVertex,d]; omega
    rw [hxd]
    refine ⟨crossPair G j (b d).val d, ⟨?_,Or.inr rfl⟩, ?_⟩
    · exact (mem_assembledEdges G j M b _).mpr (Or.inr ⟨d,rfl⟩)
    · intro f hf
      rcases (mem_assembledEdges G j M b f).mp hf.1 with ⟨a,ha,rfl⟩ | ⟨c,rfl⟩
      · exact False.elim (not_incident_old_dummy G j a d hf.2)
      · have hcd := (incident_cross_dummy G j (b c).val d c).mp hf.2
        subst c
        rfl

def assembleMatching (G : Input) (j : ℕ) (M : PartialMatching G.n)
    (b : Fin j ≃ ↥(loopVertices M)) : SupportedMatching G j := by
  refine ⟨⟨assembledEdges G j M b,assembledEdges_perfect G j M b⟩,?_⟩
  intro e he
  rcases (mem_assembledEdges G j M b e).mp he with ⟨a,ha,rfl⟩ | ⟨d,rfl⟩
  · exact a.val.1.isLt
  · exact (b d).val.isLt

lemma restrict_assemble (G : Input) (j : ℕ) (M : PartialMatching G.n)
    (b : Fin j ≃ ↥(loopVertices M)) :
    restrictMatching G j (assembleMatching G j M b) = M := by
  classical
  apply Subtype.ext
  ext e
  rw [mem_restrictMatching]
  change oldPair G j e ∈ assembledEdges G j M b ↔ e ∈ M.val
  rw [mem_assembledEdges]
  constructor
  · rintro (⟨a,ha,hea⟩ | ⟨d,hd⟩)
    · exact (oldPair_injective G j hea) ▸ ha
    · exact False.elim (oldPair_ne_crossPair G j e (b d).val d hd.symm)
  · intro he
    exact Or.inl ⟨e,he,rfl⟩

lemma crossPartner_assemble (G : Input) (j : ℕ) (M : PartialMatching G.n)
    (b : Fin j ≃ ↥(loopVertices M)) (d : Fin j) :
    crossPartner G j (assembleMatching G j M b) d = (b d).val := by
  apply crossPartner_eq
  exact (mem_assembledEdges G j M b _).mpr (Or.inr ⟨d,rfl⟩)

lemma supported_edge_cases (G : Input) (j : ℕ) (N : SupportedMatching G j)
    (e : BinaryMatching.Pair (expand G j).n) (he : e ∈ N.val.val) :
    (∃ f ∈ (restrictMatching G j N).val, oldPair G j f = e) ∨
      (∃ d, crossPair G j (crossPartner G j N d) d = e) := by
  have hl := N.property e he
  by_cases hr : e.val.2.val < G.n
  · let f : BinaryMatching.Pair G.n :=
      ⟨(⟨e.val.1.val,hl⟩,⟨e.val.2.val,hr⟩),e.property⟩
    have hf : oldPair G j f = e := by
      apply Subtype.ext; apply Prod.ext <;> apply Fin.ext <;> rfl
    exact Or.inl ⟨f,(mem_restrictMatching G j N f).mpr (by simpa only [hf] using he),hf⟩
  · let d : Fin j := ⟨e.val.2.val-G.n,by
      have := e.val.2.isLt; simp only [expand_n] at this; omega⟩
    let v : Fin G.n := ⟨e.val.1.val,hl⟩
    have hf : crossPair G j v d = e := by
      apply Subtype.ext; apply Prod.ext <;> apply Fin.ext
      · rfl
      · dsimp [crossPair,d]; omega
    have hv := crossPartner_eq G j N v d (by simpa only [hf] using he)
    exact Or.inr ⟨d,by simpa only [hv] using hf⟩

lemma assemble_restrict (G : Input) (j : ℕ) (N : SupportedMatching G j) :
    assembleMatching G j (restrictMatching G j N) (dummyEquiv G j N) = N := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  ext e
  change e ∈ assembledEdges G j (restrictMatching G j N) (dummyEquiv G j N) ↔ e ∈ N.val.val
  rw [mem_assembledEdges]
  constructor
  · rintro (⟨f,hf,rfl⟩ | ⟨d,rfl⟩)
    · exact (mem_restrictMatching G j N f).mp hf
    · exact crossPartner_mem G j N d
  · exact supported_edge_cases G j N e

instance supportedMatchingFintype (G : Input) (j : ℕ) : Fintype (SupportedMatching G j) := by
  classical
  unfold SupportedMatching
  exact Fintype.ofFinite _

def assembleMatchingEquiv (G : Input) (j : ℕ) :
    ((M : PartialMatching G.n) × (Fin j ≃ ↥(loopVertices M))) ≃ SupportedMatching G j :=
  Equiv.ofBijective (fun z => assembleMatching G j z.1 z.2) ⟨by
    rintro ⟨M,b⟩ ⟨M',b'⟩ h
    have hm : M = M' := by
      have hh := congrArg (restrictMatching G j) h
      simpa only [restrict_assemble] using hh
    cases hm
    change assembleMatching G j M b = assembleMatching G j M b' at h
    have hb : b = b' := by
      apply Equiv.ext
      intro d
      apply Subtype.ext
      rw [← crossPartner_assemble G j M b d, h, crossPartner_assemble]
    cases hb
    rfl,
    fun N => ⟨⟨restrictMatching G j N,dummyEquiv G j N⟩,assemble_restrict G j N⟩⟩

def supportedMatchingEquiv (G : Input) (j : ℕ) :
    SupportedMatching G j ≃ ((M : PartialMatching G.n) × (Fin j ≃ ↥(loopVertices M))) :=
  (assembleMatchingEquiv G j).symm

def supportedEdgeEquiv (G : Input) (j : ℕ) (N : SupportedMatching G j) :
    (↥(restrictMatching G j N).val ⊕ Fin j) ≃ ↥N.val.val :=
  Equiv.ofBijective (fun x => match x with
    | Sum.inl e => ⟨oldPair G j e.val,(mem_restrictMatching G j N e.val).mp e.property⟩
    | Sum.inr d => ⟨crossPair G j (crossPartner G j N d) d,crossPartner_mem G j N d⟩)
    ⟨by
      intro x y h
      have hh := congrArg Subtype.val h
      cases x with
      | inl e =>
        cases y with
        | inl f => exact congrArg Sum.inl (Subtype.ext (oldPair_injective G j hh))
        | inr d => exact False.elim (oldPair_ne_crossPair G j e.val _ d hh)
      | inr d =>
        cases y with
        | inl e => exact False.elim (oldPair_ne_crossPair G j e.val _ d hh.symm)
        | inr c => exact congrArg Sum.inr (crossPair_injective G j hh).2,
      by
        intro e
        rcases supported_edge_cases G j N e.val e.property with ⟨f,hf,he⟩ | ⟨d,he⟩
        · exact ⟨Sum.inl ⟨f,hf⟩,Subtype.ext he⟩
        · exact ⟨Sum.inr d,Subtype.ext he⟩⟩

end LoopMatching

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_InputMachine
attribute [-instance] _root_.OAI.LoopMatching.supportedMatchingFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.InputMachine
open BinaryMatching BinaryMatching.StackCode

abbrev Data := ℕ × (List Raw.InputData.Rec × List LoopData)

def repr (G : LoopMatching.Input) : Data :=
  (G.n,(G.ordinary.records.map Raw.InputData.repr,G.loops.map loopRepr))

def crossBlock (n j : ℕ) (r : LoopData) : List Raw.InputData.Rec :=
  (List.range j).map (fun d => (r.1,(n+d,r.2)))

def cross (n j : ℕ) (rs : List LoopData) : List Raw.InputData.Rec :=
  rs.flatMap (crossBlock n j)

def expanded (z : Data) (j : ℕ) : Raw.InputData.Data :=
  (z.1+j,z.2.1 ++ cross z.1 j z.2.2)

@[fun_prop] theorem crossBlock_poly :
    Poly (fun z : (ℕ × ℕ) × LoopData => crossBlock z.1.1 z.1.2 z.2) := by
  exact Poly.mapWith (fun z : (ℕ × ℕ) × LoopData => List.range z.1.2)
    (fun z : ((ℕ × ℕ) × LoopData) × ℕ =>
      (z.1.2.1,(z.1.1.1+z.2,z.1.2.2))) (by fun_prop) (by fun_prop)

@[fun_prop] theorem cross_poly :
    Poly (fun z : (ℕ × ℕ) × List LoopData => cross z.1.1 z.1.2 z.2) := by
  apply Poly.flatMapWith (fun z : (ℕ × ℕ) × List LoopData => z.2)
    (fun z : ((ℕ × ℕ) × List LoopData) × LoopData =>
      crossBlock z.1.1.1 z.1.1.2 z.2) (by fun_prop)
  exact Poly.comp _ (fun z : ((ℕ × ℕ) × List LoopData) × LoopData =>
    (z.1.1,z.2)) crossBlock_poly (by fun_prop)

@[fun_prop] theorem expanded_poly : Poly (fun z : Data × ℕ => expanded z.1 z.2) := by
  have hc : Poly (fun z : Data × ℕ => cross z.1.1 z.2 z.1.2.2) :=
    Poly.comp _ (fun z : Data × ℕ => ((z.1.1,z.2),z.1.2.2)) cross_poly (by fun_prop)
  unfold expanded
  fun_prop

lemma cross_repr (n j : ℕ) (rs : List LoopRecord) :
    cross n j (rs.map loopRepr) = (crossRecords n j rs).map Raw.InputData.repr := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, cross, List.flatMap_cons, crossRecords, List.map_append]
    rw [← cross, ih]
    simp only [crossBlock, List.map_map]
    rfl

lemma expanded_repr (G : LoopMatching.Input) (j : ℕ) :
    expanded (repr G) j = ((expand G j).n,(expand G j).records.map Raw.InputData.repr) := by
  simp only [expanded, repr, cross_repr, expand, List.map_append]

def call (z : Data) (j : ℕ) : List Bool := Raw.InputData.solve (expanded z j)

@[fun_prop] theorem call_poly : Poly (fun z : Data × ℕ => call z.1 z.2) :=
  Poly.comp Raw.InputData.solve _ Raw.InputData.solve_poly expanded_poly

lemma solve_repr (G : BinaryMatching.Input) :
    Raw.InputData.solve (G.n,G.records.map Raw.InputData.repr) =
      (Raw.InputData.sparseEstimate G).bits := by
  unfold Raw.InputData.solve Raw.InputData.sparseEstimate
  simp only [List.length_map]
  split_ifs
  · rfl
  · exact Raw.InputData.smallSolve_repr G

lemma call_repr (G : LoopMatching.Input) (j : ℕ) :
    call (repr G) j = (Raw.InputData.sparseEstimate (expand G j)).bits := by
  rw [call, expanded_repr, solve_repr]

end LoopMatching.InputMachine

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_InputDecode
attribute [-instance] _root_.OAI.LoopMatching.supportedMatchingFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.InputMachine
open BinaryMatching BinaryMatching.StackCode

abbrev BitsData := List Bool × (List Parse.RecordBits × List LoopBits)

def bitsRepr (G : LoopMatching.Input) : BitsData :=
  (G.n.bits,(G.ordinary.records.map Parse.recordRepr,G.loops.map loopBitsRepr))

def supportBound (z : BitsData) : ℕ := 2*z.2.1.length+z.2.2.length

def decodeLoop (b : ℕ) (r : LoopBits) : LoopData := (Parse.boundedValue b r.1,r.2)

def decode (z : BitsData) : Data :=
  let b := supportBound z+1
  (Parse.boundedValue b z.1,
    (z.2.1.map (Raw.InputData.decodeRecord b),z.2.2.map (decodeLoop b)))

@[fun_prop] theorem decodeLoop_poly : Poly (fun z : ℕ × LoopBits => decodeLoop z.1 z.2) := by
  unfold decodeLoop
  fun_prop

@[fun_prop] theorem decode_poly : Poly decode := by
  have hr := Poly.mapWith (fun z : BitsData => z.2.1)
    (fun z : BitsData × Parse.RecordBits => Raw.InputData.decodeRecord (supportBound z.1+1) z.2)
    (by fun_prop) (by unfold supportBound; fun_prop)
  have hs := Poly.mapWith (fun z : BitsData => z.2.2)
    (fun z : BitsData × LoopBits => decodeLoop (supportBound z.1+1) z.2)
    (by fun_prop) (by unfold supportBound; fun_prop)
  have hn : Poly (fun z : BitsData => Parse.boundedValue (supportBound z+1) z.1) := by
    unfold supportBound
    fun_prop
  exact Poly.pair _ _ hn (Poly.pair _ _ hr hs)

lemma supportBound_repr (G : LoopMatching.Input) :
    supportBound (bitsRepr G) = 2*G.ordinary.records.length+G.loops.length := by
  simp [supportBound,bitsRepr]

lemma decode_n_repr (G : LoopMatching.Input) :
    (decode (bitsRepr G)).1 = min (2*G.ordinary.records.length+G.loops.length+1) G.n := by
  simp [decode,bitsRepr,supportBound,Parse.boundedValue_bits]

lemma decode_repr (G : LoopMatching.Input)
    (hn : G.n ≤ 2*G.ordinary.records.length+G.loops.length) :
    decode (bitsRepr G)=repr G := by
  let b := 2*G.ordinary.records.length+G.loops.length+1
  have hb : G.n ≤ b := by dsimp [b]; omega
  have hr : (G.ordinary.records.map Parse.recordRepr).map (Raw.InputData.decodeRecord b) =
      G.ordinary.records.map Raw.InputData.repr := by
    rw [List.map_map]
    apply List.map_congr_left
    intro r hr
    exact Raw.InputData.decodeRecord_repr G.ordinary b hb r hr
  have hs : (G.loops.map loopBitsRepr).map (decodeLoop b)=G.loops.map loopRepr := by
    rw [List.map_map]
    apply List.map_congr_left
    intro r hr
    have hv := G.valid r hr
    change r.vertex < G.n at hv
    simp only [Function.comp_def,decodeLoop,loopBitsRepr,loopRepr,Parse.boundedValue_bits]
    rw [min_eq_right (by omega : r.vertex ≤ b)]
  unfold decode
  rw [supportBound_repr]
  change (Parse.boundedValue b G.n.bits,
    ((G.ordinary.records.map Parse.recordRepr).map (Raw.InputData.decodeRecord b),
      (G.loops.map loopBitsRepr).map (decodeLoop b))) = _
  rw [Parse.boundedValue_bits,min_eq_right hb,hr,hs]
  rfl

lemma sparse_guard_repr (G : LoopMatching.Input) :
    (2*(decode (bitsRepr G)).2.1.length+(decode (bitsRepr G)).2.2.length <
      (decode (bitsRepr G)).1) ↔
    2*G.ordinary.records.length+G.loops.length < G.n := by
  rw [decode_n_repr]
  simp only [decode,bitsRepr,List.length_map]
  omega

end LoopMatching.InputMachine

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_LoopParser
attribute [-instance] _root_.OAI.LoopMatching.supportedMatchingFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.InputMachine
open BinaryMatching BinaryMatching.StackCode Polynomial

def loopRecord (l : List Bool) : LoopBits × List Bool :=
  let a := Parse.numeral l
  let b := Parse.numeral a.2
  ((a.1,b.1),b.2)

lemma loopRecord_encode (r : LoopRecord) (l : List Bool) :
    loopRecord (encodeLoopRecord r ++ l)=(loopBitsRepr r,l) := by
  unfold loopRecord encodeLoopRecord
  simp only [List.append_assoc,Parse.numeral_encode]
  rfl

@[fun_prop] theorem loopRecord_poly : Poly loopRecord := by unfold loopRecord; fun_prop

lemma loopRecord_size (l : List Bool) : (loopRecord l).2.length≤l.length ∧
    (encode (loopRecord l).1).length≤20*l.length+10 := by
  have h₁ := Parse.numeral_lengths l
  have h₂ := Parse.numeral_lengths (Parse.numeral l).2
  simp only [loopRecord,code_pair_length,cut_code_length]
  omega

def loopStep (z : List Bool × List LoopBits) : List Bool × List LoopBits :=
  if z.1.isEmpty then z else ((loopRecord z.1).2,z.2++[(loopRecord z.1).1])

lemma loopStep_encode (r : LoopRecord) (l : List Bool) (acc : List LoopBits) :
    loopStep (encodeLoopRecord r ++ l,acc)=(l,acc++[loopBitsRepr r]) := by
  simp [loopStep,List.isEmpty_iff,List.append_eq_nil_iff,
    encodeLoopRecord_ne_nil,loopRecord_encode]

lemma loopStep_records_suffix (rs : List LoopRecord) (suffix : List Bool)
    (acc : List LoopBits) :
    loopStep^[rs.length] (rs.flatMap encodeLoopRecord ++ suffix,acc)=
      (suffix,acc++rs.map loopBitsRepr) := by
  induction rs generalizing acc with
  | nil => simp
  | cons r rs ih =>
    rw [List.length_cons,Function.iterate_succ_apply,List.flatMap_cons,
      List.append_assoc,loopStep_encode,ih]
    simp [List.append_assoc]

lemma loopStep_size (z : List Bool × List LoopBits) :
    (loopStep z).1.length≤z.1.length ∧
    (encode (loopStep z).2).length≤(encode z.2).length+40*z.1.length+21 := by
  have hr := loopRecord_size z.1
  unfold loopStep
  split_ifs
  · simp; omega
  · simp only [code_append,List.length_append,code_cons,pairBits_length,List.length_nil,code_nil]
    omega

lemma loopStep_iterate_size (k : ℕ) (z : List Bool × List LoopBits) :
    (loopStep^[k] z).1.length≤z.1.length ∧
    (encode (loopStep^[k] z).2).length≤(encode z.2).length+k*(40*z.1.length+21) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := loopStep_size (loopStep^[k] z)
    constructor
    · exact h.1.trans ih.1
    · nlinarith

def countedLoops (k : ℕ) (l : List Bool) : List LoopBits := (loopStep^[k] (l,[])).2

@[fun_prop] theorem countedLoops_poly : Poly (fun z : ℕ × List Bool => countedLoops z.1 z.2) := by
  have hs : Poly loopStep := by unfold loopStep; fun_prop
  have hi := Poly.boundedIterate loopStep hs (100*(X+1)^2) (by
    intro z j hj
    obtain ⟨h₁,h₂⟩ := loopStep_iterate_size j z.2
    have he : (encode (loopStep^[j] z.2)).length ≤
        6*z.2.1.length+(encode z.2.2).length+j*(40*z.2.1.length+21)+1 := by
      simp only [code_pair_length,cut_code_length]
      omega
    have hl : z.2.1.length≤(encode z).length := by
      simp only [code_pair_length,code_nat_length,cut_code_length]; omega
    have hk : j≤(encode z).length := by
      simp only [code_pair_length,code_nat_length]; omega
    have ha : (encode z.2.2).length≤(encode z).length := by
      simp only [code_pair_length]; omega
    have hm := Nat.mul_le_mul hk hl
    simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
    nlinarith)
  exact Poly.second _ (Poly.comp _
    (fun z : ℕ × List Bool => (z.1,(z.2,([]:List LoopBits)))) hi (by fun_prop))

lemma countedLoops_encoded (rs : List LoopRecord) :
    countedLoops rs.length (rs.flatMap encodeLoopRecord)=rs.map loopBitsRepr := by
  have h := loopStep_records_suffix rs [] []
  simpa only [countedLoops,List.append_nil,List.nil_append] using congrArg Prod.snd h

def loops (l : List Bool) : List LoopBits :=
  let a := Parse.numeral l
  countedLoops (Parse.boundedValue l.length a.1) a.2

@[fun_prop] theorem loops_poly : Poly loops := by unfold loops; fun_prop

lemma loops_encoded (rs : List LoopRecord) :
    loops (encodeNat rs.length ++ rs.flatMap encodeLoopRecord)=rs.map loopBitsRepr := by
  have h := loopRecords_length_le_bits rs
  have hb : rs.length ≤ (encodeNat rs.length ++ rs.flatMap encodeLoopRecord).length := by
    rw [List.length_append]
    omega
  unfold loops
  rw [Parse.numeral_encode]
  dsimp only
  rw [Parse.boundedValue_bits,min_eq_right hb,countedLoops_encoded]

def parse (l : List Bool) : BitsData :=
  let a := ordinaryPrefix l
  (a.1,(a.2.2,loops a.2.1))

@[fun_prop] theorem parse_poly : Poly parse := by unfold parse; fun_prop

lemma parse_encoded (G : LoopMatching.Input) : parse (LoopMatching.encodeInput G)=bitsRepr G := by
  unfold parse
  rw [ordinaryPrefix_encoded]
  dsimp only
  rw [loops_encoded]
  rfl

def prepare (l : List Bool) : Option Data :=
  let z := decode (parse l)
  if 2*z.2.1.length+z.2.2.length<z.1 then none else some z

@[fun_prop] theorem prepare_poly : Poly prepare := by
  have h : Poly (fun l : List Bool =>
      if decide (2*(decode (parse l)).2.1.length+(decode (parse l)).2.2.length <
        (decode (parse l)).1) then (none : Option Data) else some (decode (parse l))) := by
    fun_prop
  exact h.congr (fun l => by simp only [prepare,decide_eq_true_eq])

lemma prepare_encoded (G : LoopMatching.Input) :
    prepare (LoopMatching.encodeInput G)=
      if 2*G.ordinary.records.length+G.loops.length<G.n then none else some (repr G) := by
  unfold prepare
  rw [parse_encoded]
  by_cases h : 2*G.ordinary.records.length+G.loops.length<G.n
  · rw [ite_eq_left h,ite_eq_left ((sparse_guard_repr G).mpr h)]
  · rw [ite_eq_right h,ite_eq_right (by simpa only [sparse_guard_repr] using h),decode_repr G (by omega)]

end LoopMatching.InputMachine

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_RawAccumulator
attribute [-instance] _root_.OAI.LoopMatching.supportedMatchingFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.RawAccumulator
open BinaryMatching.StackCode Polynomial

abbrev Data := InputMachine.Data
abbrev State := Data × (ℕ × (List Bool × List Bool))

def step (s : State) : State :=
  (s.1,(s.2.1+1,
    (SmallBinaryMultiply.horner ((s.2.1+1,s.2.2.1),InputMachine.call s.1 (s.2.1+1)),
     SmallBinaryMultiply.mul (s.2.1+1,s.2.2.2))))

def initial (z : Data) : State := (z,(0,(InputMachine.call z 0,[true])))
def rawAccumulator (z : Data) : List Bool × List Bool :=
  (step^[z.1] (initial z)).2.2

def term (z : Data) (j : ℕ) : ℕ := BitAdd.value (InputMachine.call z j)

@[fun_prop] theorem step_poly : Poly step := by
  unfold step
  fun_prop

@[fun_prop] theorem initial_poly : Poly initial := by
  unfold initial
  fun_prop

lemma orbit_context (z : Data) (k : ℕ) : (step^[k] (initial z)).1 = z := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [Function.iterate_succ_apply', step] using ih

lemma orbit_index (z : Data) (k : ℕ) : (step^[k] (initial z)).2.1 = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', step, ih]

lemma orbit_values (z : Data) (k : ℕ) :
    BitAdd.value (step^[k] (initial z)).2.2.1 = Accumulator.Q (term z) k ∧
    BitAdd.value (step^[k] (initial z)).2.2.2 = k.factorial := by
  induction k with
  | zero => simp [initial, Accumulator.Q, term, BitAdd.value]
  | succ k ih =>
    constructor <;> simp only [Function.iterate_succ_apply', step, orbit_context, orbit_index,
      SmallBinaryMultiply.value_horner, SmallBinaryMultiply.value_mul,
      ih.1, ih.2, Accumulator.Q_succ, Nat.factorial_succ, term]

lemma orbit_lengths (z : Data) (M k : ℕ) (hk : k ≤ z.1)
    (hcall : ∀ j ≤ z.1, (InputMachine.call z j).length ≤ M) :
    (step^[k] (initial z)).2.2.1.length ≤ M+k*(z.1+2) ∧
    (step^[k] (initial z)).2.2.2.length ≤ 1+k*(z.1+1) := by
  induction k with
  | zero =>
    constructor
    · simpa only [Function.iterate_zero_apply, initial, Nat.zero_mul,
        Nat.add_zero] using hcall 0 (by omega)
    · simp [initial]
  | succ k ih =>
    obtain ⟨hq,hd⟩ := ih (by omega)
    have hc := hcall (k+1) hk
    have hq' := SmallBinaryMultiply.length_horner
      ((k+1,(step^[k] (initial z)).2.2.1),InputMachine.call z (k+1))
    have hd' := SmallBinaryMultiply.length_mul (k+1,(step^[k] (initial z)).2.2.2)
    have hm : max (step^[k] (initial z)).2.2.1.length
        (InputMachine.call z (k+1)).length ≤ M+k*(z.1+2) :=
      max_le hq (by omega)
    simp only [Function.iterate_succ_apply', step, orbit_context, orbit_index]
    constructor <;> nlinarith

noncomputable def callBound : Polynomial ℕ :=
  (X + InputMachine.call_poly.routine.time).comp (3*X+1)

lemma call_length_bound (z : Data) (N j : ℕ)
    (hz : (encode z).length ≤ N) (hj : j ≤ N) :
    (InputMachine.call z j).length ≤ callBound.eval N := by
  have hin : (encode (z,j)).length ≤ 3*N+1 := by
    rw [code_pair_length, code_nat_length]
    change 2*(encode z).length+j+1 ≤ 3*N+1
    omega
  have ho := InputMachine.call_poly.routine.length_bound (z,j)
  change (encode (InputMachine.call z j)).length ≤ (encode (z,j)).length +
    InputMachine.call_poly.routine.time.eval (encode (z,j)).length at ho
  have hm := polynomial_eval_mono InputMachine.call_poly.routine.time hin
  change InputMachine.call_poly.routine.time.eval (encode (z,j)).length ≤
    InputMachine.call_poly.routine.time.eval (3*N+1) at hm
  rw [BitAdd.boolList_code_length] at ho
  simp only [callBound, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_one]
  omega

lemma state_code_length (s : State) :
    (encode s).length = 2*(encode s.1).length + 2*s.2.1 +
      6*s.2.2.1.length + 3*s.2.2.2.length + 3 := by
  simp only [code_pair_length, code_nat_length, BitAdd.boolList_code_length]
  omega

noncomputable def orbitBound : Polynomial ℕ := 20*(callBound+(X+1)^2+1)

lemma orbit_bound (z : Data) (k : ℕ) (hk : k ≤ z.1) :
    (encode (step^[k] (initial z))).length ≤
      orbitBound.eval (encode (z.1,initial z)).length := by
  let N := (encode (z.1,initial z)).length
  have hz : (encode z).length ≤ N := by
    simp only [N, initial, code_pair_length, code_nat_length]
    omega
  have hn : z.1 ≤ N := by
    simp only [N, code_pair_length, code_nat_length]
    omega
  have hc : ∀ j ≤ z.1, (InputMachine.call z j).length ≤ callBound.eval N := by
    intro j hj
    exact call_length_bound z N j hz (hj.trans hn)
  obtain ⟨hq,hd⟩ := orbit_lengths z (callBound.eval N) k hk hc
  have hkN := hk.trans hn
  have hqmul : k*(z.1+2) ≤ N*(N+2) := Nat.mul_le_mul hkN (by omega)
  have hdmul : k*(z.1+1) ≤ N*(N+1) := Nat.mul_le_mul hkN (by omega)
  rw [state_code_length, orbit_context, orbit_index]
  change 2*(encode z).length + 2*k + 6*(step^[k] (initial z)).2.2.1.length +
    3*(step^[k] (initial z)).2.2.2.length + 3 ≤ orbitBound.eval N
  simp only [orbitBound, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

@[fun_prop] theorem orbit_poly : Poly (fun z : Data => step^[z.1] (initial z)) := by
  exact Poly.iterateFrom step step_poly Prod.fst initial (by fun_prop)
    initial_poly orbitBound orbit_bound

@[fun_prop] theorem rawAccumulator_poly : Poly rawAccumulator := by
  unfold rawAccumulator
  fun_prop

theorem rawAccumulator_values (z : Data) :
    BitAdd.value (rawAccumulator z).1 = Accumulator.Q (term z) z.1 ∧
    BitAdd.value (rawAccumulator z).2 = z.1.factorial := orbit_values z z.1

lemma term_repr (G : LoopMatching.Input) (j : ℕ) :
    term (InputMachine.repr G) j =
      BinaryMatching.Raw.InputData.sparseEstimate (expand G j) := by
  rw [term, InputMachine.call_repr, BitAdd.value_bits]

theorem rawAccumulator_repr (G : LoopMatching.Input) :
    BitAdd.value (rawAccumulator (InputMachine.repr G)).1 =
      Accumulator.Q (fun j => BinaryMatching.Raw.InputData.sparseEstimate (expand G j)) G.n ∧
    BitAdd.value (rawAccumulator (InputMachine.repr G)).2 = G.n.factorial := by
  have ht : term (InputMachine.repr G) =
      fun j => BinaryMatching.Raw.InputData.sparseEstimate (expand G j) :=
    funext (term_repr G)
  have hv := rawAccumulator_values (InputMachine.repr G)
  rw [ht] at hv
  exact hv

end LoopMatching.RawAccumulator

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_MachineMain
attribute [-instance] _root_.OAI.LoopMatching.supportedMatchingFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.MachineMain
open BinaryMatching.StackCode

def packBits (l : List Bool) : List Bool :=
  let b := BitNormalize.normalize l
  List.replicate b.length false ++ true :: b

@[fun_prop] theorem packBits_poly : Poly packBits := by
  unfold packBits
  fun_prop

lemma packBits_value (l : List Bool) :
    packBits l = BinaryMatching.encodeNat (BitAdd.value l) := by
  simp only [packBits,BitNormalize.normalize_eq_bits,BinaryMatching.encodeNat]

def serialize (p : List Bool × List Bool) : List Bool := packBits p.1 ++ packBits p.2

@[fun_prop] theorem serialize_poly : Poly serialize := by
  unfold serialize
  fun_prop

lemma serialize_values (p : List Bool × List Bool) :
    serialize p = encodeOutput (BitAdd.value p.1,BitAdd.value p.2) := by
  simp only [serialize,packBits_value,encodeOutput]

lemma serialize_rawAccumulator (G : Input) :
    serialize (RawAccumulator.rawAccumulator (InputMachine.repr G)) =
      encodeOutput (Approximation.output G) := by
  obtain ⟨hq,hd⟩ := RawAccumulator.rawAccumulator_repr G
  rw [serialize_values,hq,hd]
  rfl

def rawPair (l : List Bool) : List Bool × List Bool :=
  (InputMachine.prepare l).elim ([],[true]) RawAccumulator.rawAccumulator

@[fun_prop] theorem rawPair_poly : Poly rawPair := by
  exact Poly.comp _ InputMachine.prepare
    (Poly.optionElim ([],[true]) RawAccumulator.rawAccumulator
      RawAccumulator.rawAccumulator_poly) InputMachine.prepare_poly

def runInput (l : List Bool) : List Bool := serialize (rawPair l)

@[fun_prop] theorem runInput_poly : Poly runInput := by
  unfold runInput
  fun_prop

def A (G : Input) : ℕ × ℕ :=
  if 2*G.ordinary.records.length+G.loops.length<G.n then (0,1)
  else Approximation.output G

lemma runInput_encoded (G : Input) : runInput (encodeInput G)=encodeOutput (A G) := by
  unfold runInput rawPair
  rw [InputMachine.prepare_encoded]
  unfold A
  by_cases h : 2*G.ordinary.records.length+G.loops.length<G.n
  · simp only [ite_eq_left h]
    change serialize ([],[true]) = encodeOutput (0,1)
    rw [serialize_values]
    rfl
  · simp only [ite_eq_right h]
    exact serialize_rawAccumulator G

def bitAlgorithm (b : Bits) : Bits := ⟨runInput b.data⟩

theorem bitAlgorithm_poly : Poly bitAlgorithm := by
  change Poly (fun b : Bits => Bits.mk (runInput b.data))
  exact Poly.comp Bits.mk (fun b : Bits => runInput b.data) Poly.bitsEncode
    (Poly.comp runInput Bits.data runInput_poly Poly.bitsDecode)

noncomputable def binaryRoutine : Routine Bits.data Bits.data bitAlgorithm :=
  bitAlgorithm_poly.routine

lemma bitAlgorithm_encoded (G : Input) :
    (bitAlgorithm ⟨encodeInput G⟩).data=encodeOutput (A G) :=
  runInput_encoded G

noncomputable def countingRoutine : Routine encodeInput encodeOutput A :=
  binaryRoutine.reindex encodeInput encodeOutput A (fun G => Bits.mk (encodeInput G))
    (fun _ => rfl) bitAlgorithm_encoded

end LoopMatching.MachineMain

end OAI
end


