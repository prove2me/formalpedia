-- Prove2me | Definitions.Def_OAIQ076M012
-- name    : OAIQ076M012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:06:05.756013+00:00
-- url     : https://prove2.me/theorems/8415d218-6b91-4505-99dd-378e728017d0
-- title:
--   Definitions bundle OAIQ076M012 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 243 declarations of OpenAI's Lean: 65 definitions, 1 inductive type or structure, 1 instance and 176 theorems. The definitions and types are `OAI.MinUncut.Preprocess.Alphabet.Slot`, `OAI.MinUncut.Preprocess.Alphabet.axes`, `OAI.MinUncut.Preprocess.Alphabet.equalities`, `OAI.MinUncut.Preprocess.Alphabet.positions`, `OAI.MinUncut.Preprocess.Alphabet.positionsList`, `OAI.MinUncut.Preprocess.Alphabet.slotEquiv`, `OAI.MinUncut.Preprocess.Alphabet.slotPairs`, `OAI.MinUncut.Preprocess.Alphabet.slots`, `OAI.MinUncut.Preprocess.Face.axes`, `OAI.MinUncut.Preprocess.Face.points`, `OAI.MinUncut.Preprocess.Face.rowGood`, `OAI.MinUncut.Preprocess.Face.rowPairs`, `OAI.MinUncut.Preprocess.Face.values`, `OAI.MinUncut.Preprocess.Source.ds`, `OAI.MinUncut.Preprocess.Source.positions`, `OAI.MinUncut.Preprocess.Source.up`, `OAI.MinUncut.Preprocess.Syntax.eqCode`, `OAI.MinUncut.Preprocess.Syntax.lookupCode`, `OAI.MinUncut.Preprocess.Syntax.unitN`, `OAI.MinUncut.Preprocess.UEncoding`, `OAI.MinUncut.Preprocess.UEncoding.Map`, `OAI.MinUncut.Preprocess.UEncoding.Out`, `OAI.MinUncut.Preprocess.UEncoding.bool`, `OAI.MinUncut.Preprocess.UEncoding.fin`, `OAI.MinUncut.Preprocess.UEncoding.fixed`, `OAI.MinUncut.Preprocess.UEncoding.function`, `OAI.MinUncut.Preprocess.UEncoding.goodCodes`, `OAI.MinUncut.Preprocess.UEncoding.ofEquiv`, `OAI.MinUncut.Preprocess.UEncoding.option`, `OAI.MinUncut.Preprocess.UEncoding.prod`, `OAI.MinUncut.Preprocess.UEncoding.pullback`, `OAI.MinUncut.Preprocess.UEncoding.restrict`, `OAI.MinUncut.Preprocess.UEncoding.restrictEquiv`, `OAI.MinUncut.Preprocess.UEncoding.sum`, `OAI.MinUncut.Preprocess.maskEquiv`, `OAI.MinUncut.Preprocess.rawSet`, `OAI.MinUncut.Preprocess.setEncoding`, `OAI.MinUncut.Preprocess.sets`, `OAI.MinUncutGames.Foundations.Hastad.ConditionedOracle.fallback`, `OAI.MinUncutGames.Foundations.Hastad.SourceGame.repeatedVisible` and 26 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Analysis_UniformCube`, `MinUncut_Encoding_BitOutputBound`, `MinUncut_Encoding_Decoder`, `MinUncut_Encoding_GameDecoder`, `MinUncut_Encoding_ThreeBitTest`, `MinUncut_Encoding_UniformEncoding`, `MinUncut_Estimates_ExpressionEffectivity`, `MinUncut_Estimates_OutputSize`, `MinUncut_Estimates_TemplateExpressions`, `MinUncut_Estimates_UniformAlgebra`, `MinUncut_Estimates_UniformBoolean`, `MinUncut_Estimates_UniformEquation`, `MinUncut_Estimates_UniformEquationOutput`, `MinUncut_Estimates_UniformGrid`, `MinUncut_Estimates_UniformOutput`, `MinUncut_Estimates_UniformProduct`, `MinUncut_Estimates_UniformRestrict`, `MinUncut_Estimates_UniformSets`, `MinUncut_Estimates_UniformTransport`, `MinUncut_Games_Parameters`, `MinUncut_Machines_AlphabetGraph`, `MinUncut_Machines_MachineFiniteSequence`, `MinUncut_Machines_RuntimeFinish`, `MinUncut_Machines_RuntimeSpace`, `MinUncut_Machines_UniformAlphabet`, `MinUncut_Machines_UniformDemandAlphabet`, `MinUncut_PCP_CayleySampling`, `MinUncut_PCP_CayleySpectral`, `MinUncut_PCP_ClauseVerifier`, `MinUncut_PCP_DegreeReplacement`, `MinUncut_PCP_Folding`, `MinUncut_PCP_Game`, `MinUncut_PCP_GraphTables`, `MinUncut_PCP_Overlay`, `MinUncut_PCP_PoweringReturn`, `MinUncut_PCP_PoweringTableSemantics`, `MinUncut_PCP_RawInitialTables`, `MinUncut_PCP_SpectralCut`, `MinUncut_PCP_UniformRestriction`, `MinUncut_Search_ArithmeticTactic`, `MinUncut_Search_UniformFind`, `MinUncut_Search_UniformQuantifier`.
--
--   **Imports.** It imports the published bundle `Def_MinUncut`; the bundles `OAIQ076M000`, `OAIQ076M001`, `OAIQ076M002`, `OAIQ076M003`, `OAIQ076M004` and `OAIQ076M005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M020` and `OAIQ076M021`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_MinUncut
import Definitions.Def_OAIQ076M000
import Definitions.Def_OAIQ076M001
import Definitions.Def_OAIQ076M002
import Definitions.Def_OAIQ076M003
import Definitions.Def_OAIQ076M004
import Definitions.Def_OAIQ076M005

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_ThreeBitTest
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MinUncutGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def projectedCoefficient (π : J → I) (A : Cube I → ℝ) (s : Cube J) : ℝ :=
  𝔼 f, A f * walsh s (fun y => f (π y))

theorem threeBit_indicator (a b c : Bool) :
    (if a ^^ b ^^ c then (0 : ℝ) else 1) =
      (1 + bitSign a * bitSign b * bitSign c) / 2 := by
  cases a <;> cases b <;> cases c <;> norm_num [bitSign]

end MinUncutGames.Foundations.Hastad

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Folding
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncutGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem sum_cubeFlip (F : Cube I → ℝ) : (∑ f, F (cubeFlip f)) = ∑ f, F f := by
  refine Finset.sum_bij (fun f _ => cubeFlip f) ?_ ?_ ?_ ?_
  · intro f _
    exact Finset.mem_univ _
  · intro f _ g _ h
    have h' := congrArg cubeFlip h
    simpa only [cubeFlip_cubeFlip] using h'
  · intro g _
    exact ⟨cubeFlip g, Finset.mem_univ _, cubeFlip_cubeFlip g⟩
  · intro f _
    rfl

omit [Fintype I] [DecidableEq I] in
theorem representative_flip (i₀ : I) (f : Cube I) :
    representative i₀ (cubeFlip f) = representative i₀ f := by
  cases hf : f i₀ <;> simp [representative, cubeFlip, hf]

omit [Fintype I] [DecidableEq I] in
theorem canonicalInput_flip (i₀ : I) (f : Cube I) :
    canonicalInput i₀ (cubeFlip f) = canonicalInput i₀ f := by
  apply Subtype.ext
  exact representative_flip i₀ f

omit [Fintype I] [DecidableEq I] in
theorem foldedAnswer_flip (i₀ : I) (table : HalfCube i₀ → Bool) (f : Cube I) :
    foldedAnswer i₀ table (cubeFlip f) = !(foldedAnswer i₀ table f) := by
  unfold foldedAnswer
  rw [canonicalInput_flip]
  change (table (canonicalInput i₀ f) ^^ !(f i₀)) =
    !(table (canonicalInput i₀ f) ^^ f i₀)
  cases table (canonicalInput i₀ f) <;> cases f i₀ <;> rfl

theorem sum_cubeToggle (i : I) (F : Cube I → ℝ) :
    (∑ f, F (cubeToggle i f)) = ∑ f, F f := by
  refine Finset.sum_bij (fun f _ => cubeToggle i f) ?_ ?_ ?_ ?_
  · intro f _
    exact Finset.mem_univ _
  · intro f _ g _ h
    have h' := congrArg (cubeToggle i) h
    simpa only [cubeToggle_twice] using h'
  · intro g _
    exact ⟨cubeToggle i g, Finset.mem_univ _, cubeToggle_twice i g⟩
  · intro f _
    rfl

omit [Fintype I] in
theorem restrictQuery_cubeToggle (valid : I → Bool) (i : I)
    (hi : valid i = false) (f : Cube I) :
    restrictQuery valid (cubeToggle i f) = restrictQuery valid f := by
  funext j
  have hj : j.val ≠ i := by
    intro heq
    have hp := j.property
    rw [heq, hi] at hp
    contradiction
  simp [restrictQuery, cubeToggle, cubeXor, coordinateMask, hj]

end MinUncutGames.Foundations.Hastad

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ClauseVerifier
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP

open Target

def matchingSlots (a b : ClauseAnswer) : Nat :=
  (if a.first = b.first then 1 else 0) +
  (if a.second = b.second then 1 else 0) +
  (if a.third = b.third then 1 else 0)

theorem matchingSlots_le (a b : ClauseAnswer) : matchingSlots a b ≤ 3 := by
  rcases a with ⟨a₁,a₂,a₃⟩
  rcases b with ⟨b₁,b₂,b₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> decide

theorem matchingSlots_eq_three (a b : ClauseAnswer) : matchingSlots a b = 3 ↔ a = b := by
  rcases a with ⟨a₁,a₂,a₃⟩
  rcases b with ⟨b₁,b₂,b₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> decide

def acceptedSlots {n : Nat} (clause : Clause n) (alice bob : ClauseAnswer) : Nat :=
  if localSatisfies clause alice then matchingSlots alice bob else 0

abbrev AliceStrategy (formula : Formula) := Fin formula.clauses.length → ClauseAnswer
abbrev BobStrategy (formula : Formula) := Fin formula.«variables» → Bool

def accepts (formula : Formula) (alice : AliceStrategy formula) (bob : BobStrategy formula)
    (event : RandomEvent formula) : Bool :=
  localSatisfies (clauseAt formula event.1) (alice event.1) &&
    decide (answerAt (alice event.1) event.2 = bob (nameAt (clauseAt formula event.1) event.2))

def acceptedCount (formula : Formula) (alice : AliceStrategy formula)
    (bob : BobStrategy formula) : List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => acceptedSlots (clauseAt formula i) (alice i)
      (honestAnswer (clauseAt formula i) bob) + acceptedCount formula alice bob rest

def allIndices (formula : Formula) : List (Fin formula.clauses.length) :=
  List.finRange formula.clauses.length

end MinUncutGames.Foundations.PCP

end
section
namespace MinUncutGames.Foundations.Hastad.SourceContexts

open Target PCP

instance clauseAnswerInhabited : Inhabited ClauseAnswer := ⟨⟨false, false, false⟩⟩

theorem validJ_satisfies (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (j : J u) (hj : validJ F c j = true) (t : Fin u) :
    localSatisfies (clauseAt F (c t)) (j t) = true :=
  ((validJ_eq_true_iff F c j).mp hj).1 t

theorem validJ_consistent (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (j : J u) (hj : validJ F c j = true) (t : Fin u) (s : Slot)
    (t' : Fin u) (s' : Slot)
    (hname : nameAt (clauseAt F (c t)) s = nameAt (clauseAt F (c t')) s') :
    answerAt (j t) s = answerAt (j t') s' :=
  ((validJ_eq_true_iff F c j).mp hj).2 t t' s s' hname

theorem validJ_localConsistent (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (j : J u) (hj : validJ F c j = true) (t : Fin u) :
    localConsistent (clauseAt F (c t)) (j t) = true := by
  apply (localConsistent_eq_true_iff _ _).mpr
  intro s s' hs
  exact validJ_consistent F c j hj t s t s' hs

theorem projection_implies_coordinate_accepts (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (v : VariableContext F u) (i : I u) (j : J u)
    (hj : validJ F c j = true) (hpi : pi F c v j = i) (t : Fin u) :
    baseAccepts F (v t) (c t) (i t) (j t) = true := by
  exact (baseAccepts_eq_true_iff F _ _ _ _).mpr
    ⟨validJ_satisfies F c j hj t, validJ_localConsistent F c j hj t, congrFun hpi t⟩

end MinUncutGames.Foundations.Hastad.SourceContexts

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_UniformEncoding
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open scoped BigOperators

structure UEncoding (P : Type) [Primcodable P] (A : P → Type) where
  enc : ∀p, Encoding (A p)
  computableSize : Computable (fun p=>(enc p).size)

namespace UEncoding
variable {P : Type} [Primcodable P] {A B C Γ : P → Type}

def prod (a : UEncoding P A) (b : UEncoding P B) : UEncoding P (fun p=>A p × B p) where
  enc p := (a.enc p).prod (b.enc p)
  computableSize := ca_mul a.computableSize b.computableSize

def function (a : UEncoding P A) (b : UEncoding P B) : UEncoding P (fun p=>A p → B p) where
  enc p := (a.enc p).function (b.enc p)
  computableSize := ca_pow b.computableSize a.computableSize

def Map (a : UEncoding P A) (b : UEncoding P B) (f : ∀p,A p → B p) : Prop :=
  ∃g : P × ℕ → ℕ, Computable g ∧ ∀p x,g (p,((a.enc p).code x).val)=((b.enc p).code (f p x)).val

lemma map_id (a : UEncoding P A) : a.Map a (fun _ x=>x) :=
  ⟨Prod.snd,Computable.snd,by intros; rfl⟩

lemma map_comp {a : UEncoding P A} {b : UEncoding P B} {c : UEncoding P C}
    {f : ∀p,A p → B p} {g : ∀p,B p → C p} (hf : a.Map b f) (hg : b.Map c g) :
    a.Map c (fun p x=>g p (f p x)) := by
  obtain ⟨f',hf',hf⟩:=hf
  obtain ⟨g',hg',hg⟩:=hg
  exact ⟨fun q=>g' (q.1,f' q),hg'.comp (Computable.fst.pair hf'),by intro p x; dsimp only; rw [hf,hg]⟩

lemma prod_code {Left Right : Type} (a : Encoding Left) (b : Encoding Right)
    (x : Left) (y : Right) :
    ((a.prod b).code (x,y)).val=(a.code x).val*b.size+(b.code y).val := by
  change (b.code y).val+b.size*(a.code x).val=_
  ac_rfl

lemma map_pair {a : UEncoding P A} {b : UEncoding P B} {c : UEncoding P C}
    {f : ∀p,A p → B p} {g : ∀p,A p → C p} (hf : a.Map b f) (hg : a.Map c g) :
    a.Map (b.prod c) (fun p x=>(f p x,g p x)) := by
  obtain ⟨f',hf',hf⟩:=hf
  obtain ⟨g',hg',hg⟩:=hg
  refine ⟨fun q=>f' q*(c.enc q.1).size+g' q,?_,?_⟩
  · exact ca_add (ca_mul hf' (c.computableSize.comp Computable.fst)) hg'
  · intro p x
    dsimp only
    rw [hf,hg]
    exact (prod_code _ _ _ _).symm

lemma map_fst (a : UEncoding P A) (b : UEncoding P B) :
    (a.prod b).Map a (fun _ x=>x.1) := by
  refine ⟨fun q=>q.2/(b.enc q.1).size,ca_div Computable.snd (b.computableSize.comp Computable.fst),?_⟩
  intro p ⟨x,y⟩
  change (((b.enc p).code y).val+(b.enc p).size*((a.enc p).code x).val)/(b.enc p).size=_
  rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt ((b.enc p).code y).isLt),
    Nat.div_eq_of_lt ((b.enc p).code y).isLt,Nat.zero_add]

lemma map_snd (a : UEncoding P A) (b : UEncoding P B) :
    (a.prod b).Map b (fun _ x=>x.2) := by
  refine ⟨fun q=>q.2%(b.enc q.1).size,ca_mod Computable.snd (b.computableSize.comp Computable.fst),?_⟩
  intro p ⟨x,y⟩
  change (((b.enc p).code y).val+(b.enc p).size*((a.enc p).code x).val)%(b.enc p).size=_
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ((b.enc p).code y).isLt]

lemma function_digit {X Y : Type} (a : Encoding X) (b : Encoding Y) (f : X → Y) (x : X) :
    (((a.function b).code f).val/(b.size^(a.code x).val))%b.size=(b.code (f x)).val := by
  have hh:=congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply
    (fun i=>b.code (f (a.code.symm i)))) (a.code x))
  change (((a.function b).code f).val/(b.size^(a.code x).val))%b.size=
    (b.code (f (a.code.symm (a.code x)))).val at hh
  simpa only [Equiv.symm_apply_apply] using hh

lemma map_apply {g : UEncoding P Γ} {a : UEncoding P A} {b : UEncoding P B}
    {f : ∀p,Γ p → A p → B p} {x : ∀p,Γ p → A p}
    (hf : g.Map (a.function b) f) (hx : g.Map a x) :
    g.Map b (fun p s=>f p s (x p s)) := by
  obtain ⟨f',hf',hf⟩:=hf
  obtain ⟨x',hx',hx⟩:=hx
  refine ⟨fun q=>(f' q/(b.enc q.1).size^(x' q))%(b.enc q.1).size,?_,?_⟩
  · exact ca_mod (ca_div hf' (ca_pow (b.computableSize.comp Computable.fst) hx'))
      (b.computableSize.comp Computable.fst)
  · intro p s
    dsimp only
    rw [hf,hx]
    exact function_digit _ _ _ _

lemma function_number {X Y : Type} (a : Encoding X) (b : Encoding Y) (f : X → Y) :
    ((a.function b).code f).val=
      ∑i : Fin a.size,(b.code (f (a.code.symm i))).val*b.size^i.val := rfl

lemma map_lambda {g : UEncoding P Γ} {a : UEncoding P A} {b : UEncoding P B}
    {f : ∀p,Γ p × A p → B p} (hf : (g.prod a).Map b f) :
    g.Map (a.function b) (fun p s x=>f p (s,x)) := by
  obtain ⟨f',hf',hf⟩:=hf
  let raw : (P × ℕ) → ℕ → ℕ := fun q i=>f' (q.1,q.2*(a.enc q.1).size+i)*(b.enc q.1).size^i
  have hr : Computable₂ raw := by
    unfold raw
    exact ca_mul (hf'.comp ((Computable.fst.comp Computable.fst).pair
      (ca_add (ca_mul (Computable.snd.comp Computable.fst)
        (a.computableSize.comp (Computable.fst.comp Computable.fst))) Computable.snd)))
      (ca_pow (b.computableSize.comp (Computable.fst.comp Computable.fst)) Computable.snd)
  refine ⟨fun q=>((List.range (a.enc q.1).size).map (raw q)).sum,
    c_boundedSum hr (a.computableSize.comp Computable.fst),?_⟩
  intro p s
  dsimp only
  rw [function, function_number,←List.sum_ofFn,List.ofFn_eq_map]
  rw [←finRange_values ((a.enc p).size),List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hh : f' (p, (((g.enc p).prod (a.enc p)).code (s, (a.enc p).code.symm i)).val) =
      ((b.enc p).code (f p (s, (a.enc p).code.symm i))).val :=
    hf p (s, (a.enc p).code.symm i)
  rw [prod_code,Equiv.apply_symm_apply] at hh
  dsimp only [Function.comp_def,raw]
  rw [hh]

end UEncoding
end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineFiniteSequence
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineDrainMany

open _root_.Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem finalTapes_mem (chosen : List K) (base : Tapes K) (k : K) (h : k ∈ chosen) :
    finalTapes chosen base k = [] := by rw [finalTapes_apply, ite_eq_left h]

end MinUncutGames.Foundations.Complexity.MachineDrainMany

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RuntimeFinish
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceRuntimeFinish

open _root_.Turing Complexity

variable {K Λ σ : Type} [DecidableEq K]

def finishCost (clearKeys : List K) (accumulator : K) (base : Tapes K) : Nat :=
  MachineDrainMany.steps clearKeys base + (base accumulator).length + 2

theorem reversed_tapes (clearKeys : List K) (accumulator output : K)
    (distinct : accumulator ≠ output)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : Tapes K) :
    Reduction.MachineTransfer.tapesAt accumulator output
      (MachineDrainMany.finalTapes clearKeys base) [] (base accumulator).reverse =
      canonicalTapes output (base accumulator).reverse := by
  funext k
  by_cases hout : k = output
  · subst k
    simp [Reduction.MachineTransfer.tapesAt, canonicalTapes]
  · by_cases hacc : k = accumulator
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, canonicalTapes, distinct]
    · have hclear := MachineDrainMany.finalTapes_mem clearKeys base k (covers k hacc hout)
      simp [Reduction.MachineTransfer.tapesAt, canonicalTapes, hout, hacc, hclear]

variable [Fintype K]
open scoped BigOperators

theorem drain_conservation (clearKeys : List K) (base : Tapes K) :
    MachineDrainMany.steps clearKeys base +
      totalLength (MachineDrainMany.finalTapes clearKeys base) =
        totalLength base + clearKeys.length := by
  induction clearKeys generalizing base with
  | nil => simp [MachineDrainMany.steps, MachineDrainMany.finalTapes]
  | cons source rest ih =>
      have h := ih (Function.update base source [])
      have erase := totalLength_erase base source
      simp only [MachineDrainMany.steps, MachineDrainMany.finalTapes, List.length_cons]
      omega

end MinUncutGames.Foundations.Hastad.SourceRuntimeFinish

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RuntimeSpace
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceRuntimeSpace

open _root_.Turing Complexity
open scoped BigOperators

attribute [local instance] FinTM2.kFin

theorem step_configurationLength (tm : FinTM2) (a b : tm.Cfg)
    (transition : tm.step a = some b) :
    configurationLength tm b ≤ configurationLength tm a +
      Fintype.card tm.K * Runtime.programPushBound tm := by
  calc
    _ ≤ ∑ k : tm.K, ((a.stk k).length + Runtime.programPushBound tm) :=
      Finset.sum_le_sum (fun k _ => Runtime.stepStackLength tm k a b transition)
    _ = _ := by simp [configurationLength, Finset.sum_add_distrib]

theorem execution_configurationLength (tm : FinTM2) {start finish : tm.Cfg}
    {budget : Nat}
    (run : StateTransition.EvalsToInTime tm.step start (some finish) budget) :
    configurationLength tm finish ≤ configurationLength tm start +
      budget * (Fintype.card tm.K * Runtime.programPushBound tm) :=
  Runtime.executionSizeBound tm.step (configurationLength tm)
    (Fintype.card tm.K * Runtime.programPushBound tm) (step_configurationLength tm) run

theorem prefix_configurationLength (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    {finish : tm.Cfg} {budget : Nat}
    (run : StateTransition.EvalsToInTime tm.step (initList tm input) (some finish) budget) :
    configurationLength tm finish ≤ input.length +
      budget * (Fintype.card tm.K * Runtime.programPushBound tm) := by
  simpa only [initial_configurationLength] using execution_configurationLength tm run

end MinUncutGames.Foundations.Hastad.SourceRuntimeSpace

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_Decoder
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MinUncutGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def zeroMask : Cube I := fun _ => false

end MinUncutGames.Foundations.Hastad

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_GameDecoder
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncutGames.Foundations.Hastad

open scoped BigOperators
open Finset
open MinUncutGames.Foundations.Games

variable {Q₁ Q₂ I J : Type*}
  [Fintype Q₁] [DecidableEq Q₁] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype J] [DecidableEq J] [Nonempty J]

def projectionGame (questions : FiniteDistribution (Q₁ × Q₂))
    (π : Q₁ → Q₂ → J → I) (valid : Q₂ → J → Bool) : Game Q₁ Q₂ I J where
  questions := questions
  accepts q₁ q₂ i j := decide (π q₁ q₂ j = i ∧ valid q₂ j = true)

def ConditionedOracle.fallback {valid : J → Bool} (default : J) :
    ConditionedOracle valid → J
  | .empty _ => default
  | .stored j₀ _ => j₀.val

end MinUncutGames.Foundations.Hastad

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Game
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncutGames.Foundations.Hastad.SourceGame

open scoped BigOperators
open Target PCP Games SourceContexts

theorem eventLaw_probability (F : Formula) (hne : F.clauses ≠ [])
    (P : RandomEvent F → Bool) :
    (eventLaw F hne).probability P =
      (∑ e : RandomEvent F, if P e then (1 : ℝ) else 0) /
        (3 * F.clauses.length : ℕ) := by
  classical
  simp only [eventLaw, FiniteDistribution.uniform, FiniteDistribution.probability]
  simp_rw [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  cases P e <;> simp [RandomEvent, Fintype.card_prod, card_slot, Nat.mul_comm]

theorem sum_slots (H : Slot → ℝ) :
    (∑ s : Slot, H s) = H .first + H .second + H .third := by
  have hu : (Finset.univ : Finset Slot) = {.first, .second, .third} := by
    ext s
    cases s <;> simp
  rw [hu]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    reduceCtorEq, or_self, not_false_eq_true, Finset.sum_singleton]
  ring

theorem sum_slot_accepts (F : Formula) (alice : AliceStrategy F)
    (bob : BobStrategy F) (c : Fin F.clauses.length) :
    (∑ s : Slot, if accepts F alice bob (c,s) then (1 : ℝ) else 0) =
      (acceptedSlots (clauseAt F c) (alice c)
        (honestAnswer (clauseAt F c) bob) : ℕ) := by
  rw [sum_slots]
  by_cases hs : localSatisfies (clauseAt F c) (alice c) = true
  · by_cases h₁ : (alice c).first = bob (clauseAt F c)[0].variableIndex <;>
      by_cases h₂ : (alice c).second = bob (clauseAt F c)[1].variableIndex <;>
      by_cases h₃ : (alice c).third = bob (clauseAt F c)[2].variableIndex <;>
      norm_num [accepts, hs, acceptedSlots, matchingSlots, honestAnswer, answerAt, nameAt,
        h₁, h₂, h₃]
  · simp [accepts, acceptedSlots, hs]

def repeatedVisible (F : Formula) (u : ℕ) (events : Fin u → RandomEvent F) :
    VariableContext F u × ClauseContext F u :=
  (fun t => nameAt (clauseAt F (events t).1) (events t).2,
   fun t => (events t).1)

def sourceProjectionGame (F : Formula) (hne : F.clauses ≠ []) (u : ℕ) :
    Game (VariableContext F u) (ClauseContext F u) (I u) (J u) :=
  projectionGame ((baseGame F hne).repetition u).questions
    (fun v c => pi F c v) (validJ F)

end MinUncutGames.Foundations.Hastad.SourceGame

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_Parameters
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Integration.SourceParameters

theorem fourth_power_comparison {gap : ℚ} (hgap : 0 ≤ gap) (hgap1 : gap ≤ 1) :
    1 - (gap : ℝ) ^ 3 / 6000 ≤ (rate gap : ℝ) ^ 4 := by
  have hg : (0 : ℝ) ≤ gap := by exact_mod_cast hgap
  have hg1 : (gap : ℝ) ≤ 1 := by exact_mod_cast hgap1
  have hc : (gap : ℝ) ^ 3 ≤ 1 := pow_le_one₀ hg hg1
  have hc0 : 0 ≤ (gap : ℝ) ^ 3 := pow_nonneg hg _
  have hb := one_add_mul_le_pow (a := -(gap : ℝ) ^ 3 / 100000)
    (by linarith : (-2 : ℝ) ≤ -(gap : ℝ) ^ 3 / 100000) 4
  have hr : (rate gap : ℝ) = 1 - (gap : ℝ) ^ 3 / 100000 := by
    simp only [rate, Rat.cast_sub, Rat.cast_one, Rat.cast_div,
      Rat.cast_pow, Rat.cast_ofNat]
  rw [hr]
  calc
    _ ≤ 1 + 4 * (-(gap : ℝ) ^ 3 / 100000) := by linarith
    _ ≤ _ := by simpa only [Nat.cast_ofNat, sub_eq_add_neg, neg_div] using hb

theorem four_bit_rate_comparison {gap : ℚ}
    (hgap : 0 < gap) (hgap1 : gap ≤ 1) (n : Nat) :
    (1 - (gap : ℝ) ^ 3 / 6000) ^ ((n : ℝ) / 4) ≤ (rate gap : ℝ) ^ n := by
  have hg : (0 : ℝ) ≤ gap := by exact_mod_cast hgap.le
  have hg1 : (gap : ℝ) ≤ 1 := by exact_mod_cast hgap1
  have hc : (gap : ℝ) ^ 3 ≤ 1 := pow_le_one₀ hg hg1
  have hr : (0 : ℝ) ≤ rate gap := by exact_mod_cast (rate_bounds hgap hgap1).1.le
  calc
    _ ≤ ((rate gap : ℝ) ^ 4) ^ ((n : ℝ) / 4) :=
      Real.rpow_le_rpow (by linarith) (fourth_power_comparison hgap.le hgap1) (by positivity)
    _ = (rate gap : ℝ) ^ ((4 : ℝ) * ((n : ℝ) / 4)) :=
      (Real.rpow_natCast_mul hr 4 ((n : ℝ) / 4)).symm
    _ = (rate gap : ℝ) ^ (n : ℝ) := by congr 1; ring
    _ = _ := Real.rpow_natCast _ _

theorem logTwo_sixteen : MinUncutGames.Foundations.Repetition.logTwo 16 = 4 := by
  unfold MinUncutGames.Foundations.Repetition.logTwo
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  simp [hlog]

theorem repetitionLength_spec (gap δ : ℚ) (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) (D : Nat) (hD : 0 < D) :
    0 < repetitionLength gap δ hgap hgap1 hδ D hD ∧
      rate gap ^ repetitionLength gap δ hgap hgap1 hδ D hD < sourceThreshold D δ :=
  Nat.find_spec (exists_repetition_length hgap hgap1 hδ hD)

theorem repetitionLength_real_bound (gap δ : ℚ) (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) (D : Nat) (hD : 0 < D) :
    (rate gap : ℝ) ^ repetitionLength gap δ hgap hgap1 hδ D hD ≤
      4 * (D : ℝ)⁻¹ * (δ : ℝ) ^ 2 := by
  have h := (repetitionLength_spec gap δ hgap hgap1 hδ D hD).2.le
  unfold sourceThreshold at h
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hr
  exact hr

end MinUncutGames.Integration.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_GraphTables
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringWalks

variable {V D : Type*}

def headTailEquiv (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ (Walk V D n × D) where
  toFun w := ((w.1, fun j => w.2 j.succ), w.2 0)
  invFun z := (z.1.1, Fin.cases z.2 z.1.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    · funext j
      exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

def pivotEquiv (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) →
      (Walk V D (n + 1) ≃ (Edge V D × (Fin n → D)))
  | 0, _ => splitHead V D 0
  | n + 1, k => Fin.cases (splitHead V D (n + 1))
      (fun j => (rotateHead G (n + 1)).trans
        ((headTailEquiv V D (n + 1)).trans
          ((Equiv.prodCongr (pivotEquiv G n j) (Equiv.refl D)).trans
            (headTailEquiv (Edge V D) D n).symm))) k

theorem pivotEquiv_fst (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      (pivotEquiv G n k w).1 = edgeAt G n w k := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · change (pivotEquiv G n j (advanceTail G w)).1 =
        edgeAt G n (advanceTail G w) j
      exact ih j (advanceTail G w)

theorem pivotEquiv_succ_apply (G : PortGraph V D)
    (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 2)) :
    pivotEquiv G (n + 1) k.succ w =
      ((pivotEquiv G n k (advanceTail G w)).1,
       Fin.cases (G.rot (w.1, w.2 0)).2
         (pivotEquiv G n k (advanceTail G w)).2) := rfl

def leftFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → V → (Fin n → D) → V
  | 0, _, v, _ => v
  | n + 1, k, v, r => Fin.cases v
      (fun j => next G (leftFromPivot G n j v (fun m => r m.succ)) (r 0)) k

def rightFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → Edge V D → (Fin n → D) → V
  | 0, _, e, _ => next G e.1 e.2
  | n + 1, k, e, r => Fin.cases
      (wordEnd G (n + 1) (next G e.1 e.2) r)
      (fun j => rightFromPivot G n j e (fun m => r m.succ)) k

theorem leftFromPivot_actual (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      leftFromPivot G n k (pivotEquiv G n k w).1.1 (pivotEquiv G n k w).2 = w.1 := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rw [pivotEquiv_succ_apply]
      change next G
        (leftFromPivot G n j (pivotEquiv G n j (advanceTail G w)).1.1
          (pivotEquiv G n j (advanceTail G w)).2)
        (G.rot (w.1, w.2 0)).2 = w.1
      rw [ih j (advanceTail G w)]
      change (G.rot ((G.rot (w.1, w.2 0)).1, (G.rot (w.1, w.2 0)).2)).1 = w.1
      exact congrArg Prod.fst (rot_rot G (w.1, w.2 0))

theorem rightFromPivot_actual (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      rightFromPivot G n k (pivotEquiv G n k w).1 (pivotEquiv G n k w).2 =
        endpoint G w := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rw [pivotEquiv_succ_apply]
      change rightFromPivot G n j (pivotEquiv G n j (advanceTail G w)).1
        (pivotEquiv G n j (advanceTail G w)).2 = endpoint G w
      rw [ih j (advanceTail G w)]
      rfl

end MinUncutGames.Foundations.PCP.PoweringWalks

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_DegreeReplacement
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MinUncutGames.Foundations.PCP.AssignmentTester

open MinUncutGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem truth_nonneg (b : Bool) : 0 ≤ truth b := by cases b <;> norm_num [truth]

theorem disagree_nonneg (a b : Bool) : 0 ≤ disagree a b := by
  cases a <;> cases b <;> norm_num [disagree]

theorem disagree_xor_le (a b c d : Bool) :
    disagree (a ^^ b) (c ^^ d) ≤ disagree a c + disagree b d := by
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [disagree]

omit [Fintype A] [DecidableEq A] in
theorem cubeXor_comm (f g : Cube A) : cubeXor f g = cubeXor g f := by
  funext a
  simp [cubeXor, Bool.xor_comm]

def distance {K : Type*} [Fintype K] (f g : K → Bool) : ℝ :=
  𝔼 k, disagree (f k) (g k)

theorem four_truth_lower (e₀ e₁ d : Bool) :
    (1 : ℝ) ≤ truth e₀ + truth (e₀ ^^ d) + truth e₁ + truth (e₁ ^^ (!d)) := by
  cases e₀ <;> cases e₁ <;> cases d <;> norm_num [truth]

theorem truth_xor (a b : Bool) : truth (a ^^ b) = disagree a b := by
  cases a <;> cases b <;> norm_num [truth, disagree]

theorem disagree_triangle (a b c : Bool) :
    disagree a c ≤ disagree a b + disagree b c := by
  cases a <;> cases b <;> cases c <;> norm_num [disagree]

theorem and_disagree_transfer (p₀ p₁ p₂ q₀ q₁ q₂ : Bool) :
    disagree p₀ (p₁ && p₂) ≤ disagree q₀ (q₁ && q₂) +
      disagree q₀ p₀ + disagree q₁ p₁ + disagree q₂ p₂ := by
  cases p₀ <;> cases p₁ <;> cases p₂ <;>
    cases q₀ <;> cases q₁ <;> cases q₂ <;> norm_num [disagree]

end MinUncutGames.Foundations.PCP.AssignmentTester

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_CayleySampling
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

noncomputable section

def correlation {A : Type*} [Fintype A] (f g : A → ℝ) : ℝ :=
  mean (fun x => f x * g x)

def iterateOperator {V D : Type*} [Fintype D] (G : PortGraph V D) :
    Nat → (V → ℝ) → (V → ℝ)
  | 0, f => f
  | n + 1, f => averagingOperator G (iterateOperator G n f)

def edgeDensity {V D : Type*} [Fintype V] [Fintype D] (bad : V × D → Bool) : ℝ :=
  mean (edgeProfile bad)

def markedStep {V D : Type*} [Fintype D] (G : PortGraph V D)
    (bad : V × D → Bool) (f : V → ℝ) (v : V) : ℝ :=
  Finset.univ.expect (fun d => if bad (v, d) then f (G.rot (v, d)).1 else 0)

def returnMass {V D : Type*} [Fintype V] [Fintype D]
    (G : PortGraph V D) (bad : V × D → Bool) (gap : Nat) : ℝ :=
  mean (markedStep G bad (iterateOperator G gap (edgeProfile bad)))

section Averages

variable {A B : Type*} [Fintype A] [Fintype B]

theorem mean_eq_sum_div_card (f : A → ℝ) :
    mean f = (∑ x, f x) / (Fintype.card A : ℝ) :=
  Fintype.expect_eq_sum_div_card f

theorem mean_add (f g : A → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g :=
  Finset.expect_add_distrib _ f g

theorem mean_sub (f g : A → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g :=
  Finset.expect_sub_distrib _ f g

theorem mean_mul_left (c : ℝ) (f : A → ℝ) :
    mean (fun x => c * f x) = c * mean f :=
  (Finset.mul_expect _ f c).symm

theorem mean_mul_right (f : A → ℝ) (c : ℝ) :
    mean (fun x => f x * c) = mean f * c :=
  (Finset.expect_mul _ f c).symm

theorem mean_nonnegative (f : A → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f :=
  Finset.expect_nonneg (fun x _ => hf x)

theorem mean_mono {f g : A → ℝ} (h : ∀ x, f x ≤ g x) : mean f ≤ mean g :=
  Finset.expect_le_expect (fun x _ => h x)

theorem energy_nonnegative (f : A → ℝ) : 0 ≤ energy f :=
  mean_nonnegative _ (fun x => sq_nonneg (f x))

theorem correlation_sq_le (f g : A → ℝ) :
    correlation f g ^ 2 ≤ energy f * energy g :=
  Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f g

theorem energy_sub_const [Nonempty A] (f : A → ℝ) (c : ℝ) :
    energy (fun x => f x - c) = energy f - 2 * c * mean f + c ^ 2 := by
  have h : (fun x => (f x - c) ^ 2) =
      (fun x => (f x) ^ 2 - (2 * c) * f x + c ^ 2) := by
    funext x
    ring
  unfold energy
  rw [h, mean_add, mean_sub, mean_mul_left, mean_const]

theorem correlation_sub_const [Nonempty A] (f g : A → ℝ) (c d : ℝ) :
    correlation (fun x => f x - c) (fun x => g x - d) =
      correlation f g - d * mean f - c * mean g + c * d := by
  have h : (fun x => (f x - c) * (g x - d)) =
      (fun x => f x * g x - d * f x - c * g x + c * d) := by
    funext x
    ring
  unfold correlation
  rw [h, mean_add, mean_sub, mean_sub, mean_mul_left, mean_mul_left, mean_const]

end Averages

section Graph

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  (G : PortGraph V D)

omit [Nonempty V] in
theorem mean_operator (f : V → ℝ) : mean (averagingOperator G f) = mean f := by
  calc
    mean (averagingOperator G f) = mean (fun e : V × D => f (G.rot e).1) :=
      (mean_prod (fun e : V × D => f (G.rot e).1)).symm
    _ = mean (fun e : V × D => f e.1) := mean_equiv G.rot (fun e => f e.1)
    _ = mean (fun v : V => mean (fun _ : D => f v)) :=
      mean_prod (fun e : V × D => f e.1)
    _ = mean f := by simp only [mean_const]

omit [Fintype V] [Nonempty V] in
theorem operator_sub_const (f : V → ℝ) (c : ℝ) :
    averagingOperator G (fun v => f v - c) = fun v => averagingOperator G f v - c := by
  funext v
  change mean (fun d => f (G.rot (v, d)).1 - c) = _
  rw [mean_sub, mean_const]
  rfl

omit [Nonempty V] in
theorem mean_iterate (n : Nat) (f : V → ℝ) : mean (iterateOperator G n f) = mean f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateOperator, mean_operator, ih]

omit [Fintype V] [Nonempty V] in
theorem iterate_sub_const (n : Nat) (f : V → ℝ) (c : ℝ) :
    iterateOperator G n (fun v => f v - c) = fun v => iterateOperator G n f v - c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateOperator, ih, operator_sub_const]; rfl

omit [Nonempty V] [Nonempty D] in
theorem mean_markedStep (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (f : V → ℝ) :
    mean (markedStep G bad f) = correlation (edgeProfile bad) f := by
  calc
    mean (markedStep G bad f) =
        mean (fun e : V × D => if bad e then f (G.rot e).1 else 0) := by
      exact (mean_prod (fun e : V × D => if bad e then f (G.rot e).1 else 0)).symm
    _ = mean (fun e : V × D => if bad (G.rot e)
          then f (G.rot (G.rot e)).1 else 0) :=
      (mean_equiv G.rot (fun e : V × D => if bad e then f (G.rot e).1 else 0)).symm
    _ = mean (fun e : V × D => if bad e then f e.1 else 0) := by
      congr 1
      funext e
      rw [reversal e, G.rot_involutive e]
    _ = mean (fun v => mean (fun d => if bad (v, d) then f v else 0)) :=
      mean_prod (fun e : V × D => if bad e then f e.1 else 0)
    _ = correlation (edgeProfile bad) f := by
      unfold correlation
      congr 1
      funext v
      have h : (fun d => if bad (v, d) then f v else 0) =
          (fun d => (if bad (v, d) then (1 : ℝ) else 0) * f v) := by
        funext d
        cases bad (v, d) <;> simp
      rw [h, mean_mul_right]
      rfl

omit [Nonempty V] [Nonempty D] in
theorem returnMass_eq_correlation (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap = correlation (edgeProfile bad)
      (iterateOperator G gap (edgeProfile bad)) :=
  mean_markedStep G bad reversal _

theorem correlation_centered (f : V → ℝ) (n : Nat) :
    correlation f (iterateOperator G n f) = mean f ^ 2 +
      correlation (fun v => f v - mean f)
        (iterateOperator G n (fun v => f v - mean f)) := by
  rw [iterate_sub_const, correlation_sub_const, mean_iterate]
  ring

end Graph

section Profiles

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

omit [Fintype V] [Nonempty V] [Nonempty D] in
theorem edgeProfile_nonnegative (bad : V × D → Bool) (v : V) : 0 ≤ edgeProfile bad v :=
  mean_nonnegative _ (fun d => by cases bad (v, d) <;> norm_num)

omit [Fintype V] [Nonempty V] in
theorem edgeProfile_le_one (bad : V × D → Bool) (v : V) : edgeProfile bad v ≤ 1 := by
  change mean (fun d => if bad (v, d) then (1 : ℝ) else 0) ≤ 1
  calc
    _ ≤ mean (fun _ : D => (1 : ℝ)) := mean_mono (fun d => by
      cases bad (v, d) <;> norm_num)
    _ = 1 := mean_const _

omit [Nonempty V] [Nonempty D] in
theorem edgeDensity_nonnegative (bad : V × D → Bool) : 0 ≤ edgeDensity bad :=
  mean_nonnegative _ (edgeProfile_nonnegative bad)

omit [Nonempty V] in
theorem edgeProfile_energy_le_density (bad : V × D → Bool) :
    energy (edgeProfile bad) ≤ edgeDensity bad :=
  mean_mono (fun v => by
    have h0 := edgeProfile_nonnegative bad v
    have h1 := edgeProfile_le_one bad v
    nlinarith)

theorem edgeProfile_centered_energy (bad : V × D → Bool) :
    energy (fun v => edgeProfile bad v - edgeDensity bad) ≤
      edgeDensity bad * (1 - edgeDensity bad) := by
  rw [energy_sub_const]
  have h := edgeProfile_energy_le_density bad
  change energy (edgeProfile bad) - 2 * edgeDensity bad * edgeDensity bad +
    edgeDensity bad ^ 2 ≤ _
  nlinarith

end Profiles

end

end MinUncutGames.Foundations.PCP.SpectralReturn

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_CayleySpectral
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.ZigzagSpectral

open PoweringWalks SpectralReturn ZigzagGraphs

noncomputable section

variable {V D E : Type*}

def cloudMean [Fintype D] (f : V × D → ℝ) (v : V) : ℝ :=
  mean (fun d => f (v, d))

def projection [Fintype D] (f : V × D → ℝ) : V × D → ℝ :=
  liftCloud (cloudMean f)

def centered [Fintype D] (f : V × D → ℝ) : V × D → ℝ := f - projection f

theorem mean_liftCloud [Fintype V] [Fintype D] [Nonempty D] (f : V → ℝ) :
    mean (liftCloud (D := D) f) = mean f := by
  change mean (fun x : V × D => f x.1) = mean f
  rw [mean_prod]
  simp only [mean_const]

theorem energy_liftCloud [Fintype V] [Fintype D] [Nonempty D] (f : V → ℝ) :
    energy (liftCloud (D := D) f) = energy f :=
  mean_liftCloud (D := D) (fun v => f v ^ 2)

theorem mean_cloudMean [Fintype V] [Fintype D] (f : V × D → ℝ) :
    mean (cloudMean f) = mean f := (mean_prod f).symm

theorem energy_prod [Fintype V] [Fintype D] (f : V × D → ℝ) :
    energy f = mean (fun v => energy (fun d => f (v, d))) :=
  mean_prod (fun x => f x ^ 2)

theorem cloudMean_centered_zero [Fintype D] [Nonempty D]
    (f : V × D → ℝ) (v : V) : cloudMean (centered f) v = 0 := by
  change mean (fun d => f (v, d) - cloudMean f v) = 0
  rw [mean_sub, mean_const]
  exact sub_self _

theorem energy_centered_eq_sub [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (centered f) = energy f - energy (projection f) := by
  have hpoint (v : V) : energy (fun d => centered f (v, d)) =
      energy (fun d => f (v, d)) - (cloudMean f v) ^ 2 := by
    change energy (fun d => f (v, d) - cloudMean f v) = _
    rw [energy_sub_const]
    change energy (fun d => f (v, d)) - 2 * cloudMean f v * cloudMean f v +
      (cloudMean f v) ^ 2 = _
    ring
  have hproj : energy (projection f) = energy (cloudMean f) := energy_liftCloud _
  calc
    energy (centered f) = mean (fun v => energy (fun d => centered f (v, d))) :=
      energy_prod _
    _ = mean (fun v => energy (fun d => f (v, d)) - (cloudMean f v) ^ 2) := by
      congr 1
      funext v
      exact hpoint v
    _ = mean (fun v => energy (fun d => f (v, d))) -
        mean (fun v => (cloudMean f v) ^ 2) := mean_sub _ _
    _ = energy f - energy (projection f) := by
      rw [← energy_prod f, hproj]
      rfl

theorem projection_energy_decomposition [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy f = energy (projection f) + energy (centered f) := by
  rw [energy_centered_eq_sub]
  ring

theorem energy_centered_le [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (centered f) ≤ energy f := by
  rw [energy_centered_eq_sub]
  exact sub_le_self _ (energy_nonnegative _)

theorem mean_sq_le_energy {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    mean f ^ 2 ≤ energy f := by
  have h := correlation_sq_le f (fun _ => 1)
  simpa [correlation, energy] using h

theorem energy_add_three_le {A : Type*} [Fintype A] (a b c : A → ℝ) :
    energy (a + b + c) ≤ 3 * (energy a + energy b + energy c) := by
  calc
    energy (a + b + c) ≤ mean (fun x => 3 * (a x ^ 2 + b x ^ 2 + c x ^ 2)) := by
      apply mean_mono
      intro x
      change (a x + b x + c x) ^ 2 ≤ 3 * (a x ^ 2 + b x ^ 2 + c x ^ 2)
      nlinarith [sq_nonneg (a x - b x), sq_nonneg (a x - c x), sq_nonneg (b x - c x)]
    _ = 3 * (energy a + energy b + energy c) := by
      rw [mean_mul_left, mean_add, mean_add]
      rfl

end

end MinUncutGames.Foundations.PCP.ZigzagSpectral

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Overlay
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators

namespace MinUncutGames.Foundations.PCP.Overlay

open PoweringWalks SpectralReturn

variable {V D E A : Type*}

section Averages

variable [Fintype V] [Fintype D] [Fintype E]

theorem energy_convex_mix (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (f g : V → ℝ) :
    energy (fun v => a * f v + b * g v) ≤ a * energy f + b * energy g := by
  calc
    energy (fun v => a * f v + b * g v) ≤
        mean (fun v => a * (f v) ^ 2 + b * (g v) ^ 2) := by
      apply mean_mono
      intro v
      have hnormalize := congrArg (fun t : ℝ => t * (a * (f v) ^ 2 + b * (g v) ^ 2)) hab
      have hnonneg := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (f v - g v))
      nlinarith
    _ = a * energy f + b * energy g := by
      rw [mean_add, mean_mul_left, mean_mul_left]
      rfl

end Averages

end MinUncutGames.Foundations.PCP.Overlay

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_SpectralCut
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncutGames.Foundations.PCP.SpectralCut

open scoped BigOperators
open PoweringWalks SpectralReturn

section Indicators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mean_indicator (S : Finset V) :
    mean (indicator S) = (S.card : ℝ) / (Fintype.card V : ℝ) := by
  have hf : Finset.univ.filter (fun v : V => v ∈ S) = S := by
    ext v
    simp
  rw [mean_eq_sum_div_card]
  simp only [indicator, Finset.sum_boole, hf]

theorem energy_indicator (S : Finset V) : energy (indicator S) = mean (indicator S) := by
  unfold energy
  congr 1
  funext v
  unfold indicator
  split_ifs <;> norm_num

end Indicators

end MinUncutGames.Foundations.PCP.SpectralCut


end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringReturn
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringReturn

open PoweringWalks SpectralReturn
open PoweringMoment (bit)

variable {V D : Type*}

theorem mean_word_cons_head [Fintype D] (n : Nat)
    (F : (Fin (n + 1) → D) → ℝ) :
    mean F = mean (fun d : D => mean (fun r : Fin n → D => F (Fin.cases d r))) := by
  calc
    mean F = mean (fun z : D × (Fin n → D) => F (Fin.cases z.1 z.2)) :=
      (mean_equiv (portConsEquiv D n) F).symm
    _ = _ := mean_prod _

theorem mean_word_cons_tail [Fintype D] (n : Nat)
    (F : (Fin (n + 1) → D) → ℝ) :
    mean F = mean (fun r : Fin n → D => mean (fun d : D => F (Fin.cases d r))) := by
  calc
    mean F = mean (fun z : (Fin n → D) × D => F (Fin.cases z.2 z.1)) :=
      (mean_equiv ((Equiv.prodComm (Fin n → D) D).trans (portConsEquiv D n)) F).symm
    _ = _ := mean_prod _

theorem mean_edge_bit [Fintype D] (bad : V × D → Bool) (v : V) :
    mean (fun d : D => bit (bad (v, d) = true)) = edgeProfile bad v := by
  simp only [bit_bool, mean, edgeProfile]

end MinUncutGames.Foundations.PCP.PoweringReturn

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringTableSemantics
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.QueryIncidence

variable {E X : Type*} {q : Nat}

def decodedAssignment (positive : 0 < q) (labeling : Vertex E X → Label q) : X → Bool :=
  fun address => decodeRight positive (labeling (.inr address))

theorem incidenceAccept_true [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (event : E) (slot : Fin q) (left right : Label q)
    (accepted : incidenceAccept T positive event slot left right = true) :
    T.accepts event left = true ∧ RepeatedConsistent T event left ∧
      left (canonicalSlot T event slot) = decodeRight positive right := by
  simp only [incidenceAccept, Bool.and_eq_true] at accepted
  have hvalid : LeftValid T event left := _root_.of_decide_eq_true accepted.1
  exact ⟨hvalid.1, hvalid.2, _root_.of_decide_eq_true accepted.2⟩

end MinUncutGames.Foundations.PCP.QueryIncidence

noncomputable section

namespace MinUncutGames.Foundations.PCP.CodeComposition

open scoped BigOperators
open MinUncutGames.Foundations.Hastad

theorem pairWord_distance {X : Type*} [Fintype X] [Nonempty X]
    (left right left' right' : X → Bool) :
    relativeDistance (pairWord left right) (pairWord left' right') =
      (relativeDistance left left' + relativeDistance right right') / 2 := by
  classical
  simp [relativeDistance, Fintype.expect_eq_sum_div_card, Fintype.card_prod,
    Fintype.sum_prod_type, pairWord]
  ring

end MinUncutGames.Foundations.PCP.CodeComposition

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_UniformRestriction
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.UniformRestriction

open scoped BigOperators

variable {B : Type*} (p : B → Prop)

variable [DecidablePred p]

section Finite

variable [Fintype B] [DecidableEq B]

theorem expect_restrict (h : ({b // p b} → Bool) → ℝ) :
    (𝔼 f : B → Bool, h (restrict p f)) = 𝔼 g : {b // p b} → Bool, h g := by
  calc
    (𝔼 f : B → Bool, h (restrict p f)) =
        𝔼 g : ({b // p b} → Bool) × ({b // ¬ p b} → Bool), h g.1 :=
      Fintype.expect_equiv (Equiv.piEquivPiSubtypeProd p (fun _ => Bool))
        _ _ (fun _ => rfl)
    _ = 𝔼 g : {b // p b} → Bool, 𝔼 _k : {b // ¬ p b} → Bool, h g := by
      simpa only [Finset.univ_product_univ] using
        Finset.expect_product
          (Finset.univ : Finset ({b // p b} → Bool))
          (Finset.univ : Finset ({b // ¬ p b} → Bool))
          (fun g : ({b // p b} → Bool) × ({b // ¬ p b} → Bool) => h g.1)
    _ = 𝔼 g : {b // p b} → Bool, h g := by
      simp only [Fintype.expect_const]

end Finite

end MinUncutGames.Foundations.PCP.UniformRestriction

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_AlphabetGraph
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncutGames.Foundations.PCP.AlphabetGraph

open MinUncutGames.Foundations.Hastad
open scoped BigOperators

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem expect_restrict_five {B : Type*} [Fintype B] [DecidableEq B]
    (p : B → Prop) [DecidablePred p]
    (h : ({b // p b} → Bool) → ({b // p b} → Bool) → ({b // p b} → Bool) →
      ({b // p b} → Bool) → ({b // p b} → Bool) → ℝ) :
    (𝔼 f : B → Bool, 𝔼 g : B → Bool, 𝔼 r₀ : B → Bool,
      𝔼 r₁ : B → Bool, 𝔼 r₂ : B → Bool,
        h (UniformRestriction.restrict p f) (UniformRestriction.restrict p g)
          (UniformRestriction.restrict p r₀) (UniformRestriction.restrict p r₁)
          (UniformRestriction.restrict p r₂)) =
    𝔼 f : {b // p b} → Bool, 𝔼 g : {b // p b} → Bool,
      𝔼 r₀ : {b // p b} → Bool, 𝔼 r₁ : {b // p b} → Bool,
        𝔼 r₂ : {b // p b} → Bool, h f g r₀ r₁ r₂ := by
  rw [UniformRestriction.expect_restrict p
    (fun f => 𝔼 g : B → Bool, 𝔼 r₀ : B → Bool, 𝔼 r₁ : B → Bool,
      𝔼 r₂ : B → Bool, h f (UniformRestriction.restrict p g)
        (UniformRestriction.restrict p r₀) (UniformRestriction.restrict p r₁)
        (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro f _
  rw [UniformRestriction.expect_restrict p
    (fun g => 𝔼 r₀ : B → Bool, 𝔼 r₁ : B → Bool, 𝔼 r₂ : B → Bool,
      h f g (UniformRestriction.restrict p r₀) (UniformRestriction.restrict p r₁)
        (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro g _
  rw [UniformRestriction.expect_restrict p
    (fun r₀ => 𝔼 r₁ : B → Bool, 𝔼 r₂ : B → Bool,
      h f g r₀ (UniformRestriction.restrict p r₁) (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro r₀ _
  rw [UniformRestriction.expect_restrict p
    (fun r₁ => 𝔼 r₂ : B → Bool, h f g r₀ r₁ (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro r₁ _
  exact UniformRestriction.expect_restrict p (h f g r₀ r₁)

theorem expect_rejection_eq_count {I : Type*} [Fintype I] (b : I → Bool) :
    (𝔼 i : I, AssignmentTester.truth (!(b i))) =
      ((Finset.univ.filter (fun i => b i = false)).card : ℝ) / Fintype.card I := by
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  calc
    (∑ i : I, AssignmentTester.truth (!(b i))) = ∑ i : I, if b i = false then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      cases b i <;> norm_num [AssignmentTester.truth]
    _ = _ := Finset.sum_boole _ _

end MinUncutGames.Foundations.PCP.AlphabetGraph

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_RawInitialTables
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.FinalConstants

theorem denominator_positive : 0 < denominator := by
  norm_num [denominator, alphabet, compositionLoss]

end MinUncutGames.Foundations.PCP.FinalConstants

end
section
namespace MinUncutGames.Foundations.PCP.AmplificationIteration

theorem run_gap {X : Type*} (step : X → X) (gap : X → ℝ)
    (cap : ℝ) (hc : 0 ≤ cap)
    (amplifies : ∀ x, min (2 * gap x) cap ≤ gap (step x))
    (n : Nat) (x : X) :
    min (2 ^ n * gap x) cap ≤ gap (run step n x) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hm : min (2 * min (2 ^ n * gap x) cap) cap ≤
        min (2 * gap (run step n x)) cap :=
      min_le_min (mul_le_mul_of_nonneg_left ih (by norm_num)) le_rfl
    rw [min_double_min _ _ hc] at hm
    have h := hm.trans (amplifies (run step n x))
    simpa [run, pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

theorem rounds_large (n : Nat) : n < 2 ^ rounds n := by
  simpa [rounds, Nat.log2_eq_log_two] using
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n)

theorem run_reaches_cap {X : Type*} (step : X → X) (gap : X → ℝ)
    (cap : ℝ) (hc : 0 ≤ cap) (hc1 : cap ≤ 1)
    (amplifies : ∀ x, min (2 * gap x) cap ≤ gap (step x))
    (n : Nat) (x : X) (hg : 0 ≤ gap x) (hstart : 1 ≤ (n : ℝ) * gap x) :
    cap ≤ gap (run step (rounds n) x) := by
  have hp : (n : ℝ) ≤ (2 : ℝ) ^ rounds n := by
    exact_mod_cast (Nat.le_of_lt (rounds_large n))
  have hcap : cap ≤ (2 : ℝ) ^ rounds n * gap x :=
    hc1.trans (hstart.trans (mul_le_mul_of_nonneg_right hp hg))
  have h := run_gap step gap cap hc amplifies (rounds n) x
  rwa [min_eq_right hcap] at h

end MinUncutGames.Foundations.PCP.AmplificationIteration

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformTransport
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
namespace UEncoding
variable {P Q : Type} [Primcodable P] [Primcodable Q] {A B C Γ : P → Type}

def ofEquiv (a : UEncoding P A) (e : ∀p,B p ≃ A p) : UEncoding P B where
  enc p := ⟨(a.enc p).size,(e p).trans (a.enc p).code⟩
  computableSize := a.computableSize
lemma map_to (a : UEncoding P A) (e : ∀p,B p ≃ A p) :
    (a.ofEquiv e).Map a (fun p x=>e p x) :=
  ⟨Prod.snd,Computable.snd,by intros; rfl⟩
lemma map_from (a : UEncoding P A) (e : ∀p,B p ≃ A p) :
    a.Map (a.ofEquiv e) (fun p x=>(e p).symm x) :=
  ⟨Prod.snd,Computable.snd,by intro p x; exact congrArg Fin.val ((a.enc p).code.congr_arg ((e p).apply_symm_apply x)).symm⟩

def pullback (a : UEncoding P A) (f : Q → P) (hf : Computable f) : UEncoding Q (fun q=>A (f q)) where
  enc q := a.enc (f q)
  computableSize := a.computableSize.comp hf
lemma Map.pullback {a : UEncoding P A} {b : UEncoding P B} {g : ∀p,A p → B p}
    (hg : a.Map b g) {f : Q → P} (hf : Computable f) :
    (a.pullback f hf).Map (b.pullback f hf) (fun q x=>g (f q) x) := by
  obtain ⟨g',hg',hg⟩:=hg
  refine ⟨fun q=>g' (f q.1,q.2),hg'.comp ((hf.comp Computable.fst).pair Computable.snd),?_⟩
  intro q x
  exact hg (f q) x

lemma Map.first {a : UEncoding P A} {b : UEncoding P B} {c : UEncoding P C}
    {f : ∀p,A p → B p} (hf : a.Map b f) :
    (a.prod c).Map b (fun p x=>f p x.1) := map_comp (map_fst a c) hf
lemma Map.second {a : UEncoding P A} {b : UEncoding P B} {c : UEncoding P C}
    {f : ∀p,A p → B p} (hf : a.Map b f) :
    (c.prod a).Map b (fun p x=>f p x.2) := map_comp (map_snd c a) hf

end UEncoding

namespace UEncoding
variable {P : Type} [Primcodable P] {A B C Γ : P → Type}
variable {p : P}
def sum (a : UEncoding P A) (b : UEncoding P B) : UEncoding P (fun p=>A p ⊕ B p) where
  enc p := (a.enc p).sum (b.enc p)
  computableSize := ca_add a.computableSize b.computableSize
lemma map_inl (a : UEncoding P A) (b : UEncoding P B) :
    a.Map (a.sum b) (fun _ x=>Sum.inl x) :=
  ⟨Prod.snd, Computable.snd, by intro p x; rfl⟩
lemma map_inr (a : UEncoding P A) (b : UEncoding P B) :
    b.Map (a.sum b) (fun _ x=>Sum.inr x) :=
  ⟨fun q=>(a.enc q.1).size+q.2,
    ca_add (a.computableSize.comp Computable.fst) Computable.snd,
    by intro p x; rfl⟩
end UEncoding
end MinUncut.Preprocess

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ExpressionEffectivity
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncut.Costed MinUncut.CodeEffective Turing.ToPartrec
lemma p_constCode : Primrec constCode := by
  have hh := Primrec.nat_rec₁ Code.zero
    (primrec_comp.comp (Primrec.const Code.succ) Primrec.snd).to₂
  exact hh.of_eq (by intro n; induction n <;> simp_all only [Nat.rec_zero,constCode])
lemma p_bin (op : Code) : Primrec₂ (bin op) :=
  primrec_comp.comp (Primrec.const op) (primrec_cons.comp Primrec.fst (primrec_cons.comp Primrec.snd (Primrec.const Code.nil)))
lemma p_branch : Primrec (fun p : Code × Code × Code=>branch p.1 p.2.1 p.2.2) :=
  primrec_comp.comp (primrec_case.comp (Primrec.fst.comp Primrec.snd)
    (primrec_comp.comp (Primrec.snd.comp Primrec.snd) (Primrec.const Code.tail)))
    (primrec_cons.comp Primrec.fst (Primrec.const Code.id))

attribute [local irreducible] PolyProgram.add PolyProgram.sub PolyProgram.mul
end MinUncut.Preprocess.Syntax

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformBoolean
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
namespace UEncoding
variable {P : Type} [Primcodable P] {A B C Γ : P → Type}

def fixed {X : Type} (e : Encoding X) : UEncoding P (fun _=>X) :=
  ⟨fun _=>e,Computable.const e.size⟩
def bool : UEncoding P (fun _=>Bool) := fixed Encoding.bool
def fin (n : P → ℕ) (hn : Computable n) : UEncoding P (fun p=>Fin (n p)) :=
  ⟨fun p=>Encoding.fin (n p),hn⟩

lemma map_const {a : UEncoding P A} {b : UEncoding P B} {f : ∀p,B p}
    (hf : Computable (fun p=>((b.enc p).code (f p)).val)) :
    a.Map b (fun p _=>f p) :=
  ⟨_,hf.comp Computable.fst,by intros; rfl⟩

lemma bool_code (x : Bool) : (Encoding.bool.code x).val=x.toNat := by
  cases x <;> rfl

lemma map_bool_eq {a : UEncoding P A} {b : UEncoding P B}
    {f g : ∀p,A p → B p} [∀p,DecidableEq (B p)]
    (hf : a.Map b f) (hg : a.Map b g) :
    a.Map bool (fun p x=>decide (f p x=g p x)) := by
  obtain ⟨f',hf',hf⟩:=hf
  obtain ⟨g',hg',hg⟩:=hg
  refine ⟨fun q=>(decide (f' q=g' q)).toNat,?_,?_⟩
  · exact (Primrec.dom_bool Bool.toNat).to_comp.comp
      (Primrec.eq.decide.to_comp.comp hf' hg')
  · intro p x
    dsimp only
    rw [hf,hg]
    change _=(Encoding.bool.code _).val
    rw [bool_code]
    congr 2
    exact propext (Fin.val_inj.trans (b.enc p).code.injective.eq_iff)

lemma map_cond {a : UEncoding P A} {b : UEncoding P B}
    {c : ∀p,A p → Bool} {f g : ∀p,A p → B p}
    (hc : a.Map bool c) (hf : a.Map b f) (hg : a.Map b g) :
    a.Map b (fun p x=>if c p x then f p x else g p x) := by
  obtain ⟨c',hc',hc⟩:=hc
  obtain ⟨f',hf',hf⟩:=hf
  obtain ⟨g',hg',hg⟩:=hg
  refine ⟨fun q=>if c' q=1 then f' q else g' q,?_,?_⟩
  · exact (Computable.cond (Primrec.eq.decide.to_comp.comp hc' (Computable.const 1)) hf' hg').of_eq (by intro q; simp)
  · intro p x
    dsimp only
    rw [hc,hf,hg]
    change (if (Encoding.bool.code (c p x)).val=1 then _ else _)=_
    rw [bool_code]
    cases h:c p x <;> simp

lemma map_fixed {X Y : Type} (a : Encoding X) (b : Encoding Y) (f : X → Y) :
    (fixed (P:=P) a).Map (fixed b) (fun _ x=>f x) := by
  let table := List.ofFn (fun i : Fin a.size=>(b.code (f (a.code.symm i))).val)
  refine ⟨fun q=>(table[q.2]?).getD 0,?_,?_⟩
  · exact Primrec.option_getD_default.to_comp.comp
      ((Primrec.list_getElem?₁ table).to_comp.comp Computable.snd)
  · intro p x
    dsimp only
    change (table[(a.code x).val]?).getD 0=(b.code (f x)).val
    simp [table,(a.code x).isLt]

lemma map_fixed_apply {X Y : Type} {a : UEncoding P A} (b : Encoding X) (c : Encoding Y)
    (op : X → Y) {f : ∀p,A p → X} (hf : a.Map (fixed b) f) :
    a.Map (fixed c) (fun p x=>op (f p x)) :=
  map_comp hf (map_fixed b c op)

lemma map_binary {X Y Z : Type} {a : UEncoding P A}
    (b : Encoding X) (c : Encoding Y) (d : Encoding Z) (op : X → Y → Z)
    {f : ∀p,A p → X} {g : ∀p,A p → Y}
    (hf : a.Map (fixed b) f) (hg : a.Map (fixed c) g) :
    a.Map (fixed d) (fun p x=>op (f p x) (g p x)) :=
  map_comp (map_pair hf hg) (map_fixed (b.prod c) d (fun x=>op x.1 x.2))

lemma map_not {a : UEncoding P A} {f : ∀p,A p → Bool} (hf : a.Map bool f) :
    a.Map bool (fun p x=>!(f p x)) :=
  map_fixed_apply Encoding.bool Encoding.bool Bool.not hf
lemma map_and {a : UEncoding P A} {f g : ∀p,A p → Bool}
    (hf : a.Map bool f) (hg : a.Map bool g) : a.Map bool (fun p x=>f p x && g p x) :=
  map_binary Encoding.bool Encoding.bool Encoding.bool Bool.and hf hg
lemma map_or {a : UEncoding P A} {f g : ∀p,A p → Bool}
    (hf : a.Map bool f) (hg : a.Map bool g) : a.Map bool (fun p x=>f p x || g p x) :=
  map_binary Encoding.bool Encoding.bool Encoding.bool Bool.or hf hg

end UEncoding
end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformRestrict
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
namespace UEncoding
variable {P : Type} [Primcodable P] {A B Γ : P → Type}

def goodCodes (a : UEncoding P A) (b : ∀p,A p → Bool) (p : P) : List ℕ :=
  (List.range (a.enc p).size).filter (fun n=>if h:n<(a.enc p).size then b p ((a.enc p).code.symm ⟨n,h⟩) else false)
lemma goodCodes_nodup (a : UEncoding P A) (b : ∀p,A p → Bool) (p : P) :
    (goodCodes a b p).Nodup := List.nodup_range.filter _
lemma mem_goodCodes (a : UEncoding P A) (b : ∀p,A p → Bool) (p : P) (n : ℕ) :
    n∈goodCodes a b p ↔ ∃h:n<(a.enc p).size,b p ((a.enc p).code.symm ⟨n,h⟩)=true := by
  simp only [goodCodes,List.mem_filter,List.mem_range]
  by_cases hn:n<(a.enc p).size <;> simp [hn]
lemma original_mem_goodCodes (a : UEncoding P A) (b : ∀p,A p → Bool) (p : P) (x : A p) :
    ((a.enc p).code x).val∈goodCodes a b p ↔ b p x=true := by
  rw [mem_goodCodes]
  simp only [Equiv.symm_apply_apply,Fin.eta]
  exact ⟨fun h=>h.2,fun h=>⟨((a.enc p).code x).isLt,h⟩⟩

lemma computable_goodCodes (a : UEncoding P A) (b : ∀p,A p → Bool) (hb : a.Map bool b) :
    Computable (goodCodes a b) := by
  obtain ⟨f,hf,h⟩:=hb
  have hr : Computable₂ (fun p n=>if f (p,n)=1 then [n] else []) := by
    exact (Computable.cond (Primrec.eq.decide.to_comp.comp hf (Computable.const 1))
      (Computable.list_cons.comp Computable.snd (Computable.const []))
      (Computable.const [])).of_eq (by intro q; simp)
  have hh := Primrec.list_flatten.to_comp.comp ((c_rangeMap hr).comp Computable.id a.computableSize)
  apply hh.of_eq
  intro p
  change (List.range (a.enc p).size).flatMap _=_
  rw [show goodCodes a b p=(List.range (a.enc p).size).flatMap
    (fun n=>if (if h:n<(a.enc p).size then b p ((a.enc p).code.symm ⟨n,h⟩) else false) then [n] else []) by
      unfold goodCodes
      generalize List.range (a.enc p).size = xs
      induction xs with
      | nil => rfl
      | cons x xs ih => simp only [List.filter_cons,List.flatMap_cons,ih]; split_ifs <;> simp_all]
  apply List.flatMap_congr
  intro n hn
  have hn' : n<(a.enc p).size := List.mem_range.mp hn
  have ht := h p ((a.enc p).code.symm ⟨n,hn'⟩)
  simp only [Equiv.apply_symm_apply] at ht
  dsimp only [id]
  simp only [dite_eq_left hn',ht]
  change (if (Encoding.bool.code _).val=1 then _ else _) = _
  rw [bool_code]
  cases b p ((a.enc p).code.symm ⟨n,hn'⟩) <;> rfl

def restrictEquiv (a : UEncoding P A) (b : ∀p,A p → Bool) (p : P) :
    {x:A p // b p x=true} ≃ {n:ℕ // n∈goodCodes a b p} where
  toFun x := ⟨((a.enc p).code x.val).val,(original_mem_goodCodes a b p x).mpr x.property⟩
  invFun n := ⟨(a.enc p).code.symm ⟨n.val,((mem_goodCodes a b p n).mp n.property).choose⟩,
    ((mem_goodCodes a b p n).mp n.property).choose_spec⟩
  left_inv x := by apply Subtype.ext; exact (a.enc p).code.symm_apply_apply x.val
  right_inv n := by apply Subtype.ext; exact congrArg Fin.val ((a.enc p).code.apply_symm_apply _)

def restrict (a : UEncoding P A) (b : ∀p,A p → Bool) (hb : a.Map bool b) :
    UEncoding P (fun p=>{x:A p // b p x=true}) where
  enc p := ⟨(goodCodes a b p).length,(restrictEquiv a b p).trans
    ((goodCodes_nodup a b p).getEquiv (goodCodes a b p)).symm⟩
  computableSize := Computable.list_length.comp (computable_goodCodes a b hb)

lemma restrict_code (a : UEncoding P A) (b : ∀p,A p → Bool) (hb : a.Map bool b)
    (p : P) (x : {x:A p // b p x=true}) :
    (((a.restrict b hb).enc p).code x).val=(goodCodes a b p).idxOf (((a.enc p).code x.val).val) := rfl

lemma map_restrict_val (a : UEncoding P A) (b : ∀p,A p → Bool) (hb : a.Map bool b) :
    (a.restrict b hb).Map a (fun _ x=>x.val) := by
  refine ⟨fun q=>((goodCodes a b q.1)[q.2]?).getD 0,?_,?_⟩
  · exact Primrec.option_getD_default.to_comp.comp
      (Computable.list_getElem?.comp ((computable_goodCodes a b hb).comp Computable.fst) Computable.snd)
  · intro p x
    dsimp only
    rw [restrict_code,List.getElem?_idxOf (by exact (original_mem_goodCodes a b p x).mpr x.property)]
    rfl

lemma map_restrict_mk {g : UEncoding P Γ} {a : UEncoding P A} {b : ∀p,A p → Bool}
    (hb : a.Map bool b) {f : ∀p,Γ p → A p} (hf : g.Map a f)
    (h : ∀p x,b p (f p x)=true) :
    g.Map (a.restrict b hb) (fun p x=>⟨f p x,h p x⟩) := by
  obtain ⟨f',hf',he⟩:=hf
  refine ⟨fun q=>(goodCodes a b q.1).idxOf (f' q),?_,?_⟩
  · exact Primrec.list_idxOf.to_comp.comp hf' ((computable_goodCodes a b hb).comp Computable.fst)
  · intro p x
    dsimp only
    rw [he,restrict_code]

end UEncoding

namespace UEncoding
variable {P : Type} [Primcodable P] {A B Γ : P → Type}
variable {X Y Z : Type} [Primcodable X] [Primcodable Y] [Primcodable Z]

def Out (a : UEncoding P A) (f : ∀p,A p → X) : Prop :=
  ∃g : P × ℕ → X, Computable g ∧ ∀p x,g (p,((a.enc p).code x).val)=f p x
lemma Out.ofEq {a : UEncoding P A} {f g : ∀p,A p → X} (hf : a.Out f)
    (h : ∀p x,f p x=g p x) : a.Out g := by
  obtain ⟨f',hr,hh⟩:=hf
  exact ⟨f',hr,fun p x=>(hh p x).trans (h p x)⟩
lemma out_const (a : UEncoding P A) {f : P → X} (hf : Computable f) :
    a.Out (fun p _=>f p) := ⟨_,hf.comp Computable.fst,by intros; rfl⟩
lemma out_code (a : UEncoding P A) : a.Out (fun p x=>((a.enc p).code x).val) :=
  ⟨Prod.snd,Computable.snd,by intros; rfl⟩
lemma Out.comp {a : UEncoding P A} {b : UEncoding P B}
    {f : ∀p,A p → B p} {g : ∀p,B p → X} (hg : b.Out g) (hf : a.Map b f) :
    a.Out (fun p x=>g p (f p x)) := by
  obtain ⟨f',hrf,hf⟩:=hf
  obtain ⟨g',hrg,hg⟩:=hg
  exact ⟨fun q=>g' (q.1,f' q),hrg.comp (Computable.fst.pair hrf),
    by intro p x; dsimp only; rw [hf,hg]⟩
lemma Out.map {a : UEncoding P A} {f : ∀p,A p → X} (hf : a.Out f)
    {g : X → Y} (hg : Computable g) : a.Out (fun p x=>g (f p x)) := by
  obtain ⟨f',hrf,hf⟩:=hf
  exact ⟨_,hg.comp hrf,by intro p x; dsimp only; rw [hf]⟩
lemma Out.map₂ {a : UEncoding P A} {f : ∀p,A p → X} {g : ∀p,A p → Y}
    (hf : a.Out f) (hg : a.Out g) {op : X → Y → Z} (hop : Computable₂ op) :
    a.Out (fun p x=>op (f p x) (g p x)) := by
  obtain ⟨f',hrf,hf⟩:=hf
  obtain ⟨g',hrg,hg⟩:=hg
  exact ⟨_,hop.comp hrf hrg,by intro p x; dsimp only; rw [hf,hg]⟩
lemma Out.pair {a : UEncoding P A} {f : ∀p,A p → X} {g : ∀p,A p → Y}
    (hf : a.Out f) (hg : a.Out g) : a.Out (fun p x=>(f p x,g p x)) :=
  hf.map₂ hg (Computable.fst.pair Computable.snd)
lemma Out.first {a : UEncoding P A} {b : UEncoding P B} {f : ∀p,A p → X}
    (hf : a.Out f) : (a.prod b).Out (fun p x=>f p x.1) := hf.comp (map_fst a b)
lemma Out.second {a : UEncoding P A} {b : UEncoding P B} {f : ∀p,A p → X}
    (hf : a.Out f) : (b.prod a).Out (fun p x=>f p x.2) := hf.comp (map_snd b a)

lemma out_list {g : UEncoding P Γ} {a : UEncoding P A}
    {f : ∀p,Γ p × A p → X} (hf : (g.prod a).Out f) :
    g.Out (fun p s=>(a.enc p).enumerate.map (fun x=>f p (s,x))) := by
  obtain ⟨f',hf',hf⟩:=hf
  let raw : (P × ℕ) → ℕ → X := fun q i=>f' (q.1,q.2*(a.enc q.1).size+i)
  have hr : Computable₂ raw := by
    unfold raw
    exact hf'.comp ((Computable.fst.comp Computable.fst).pair
      (ca_add (ca_mul (Computable.snd.comp Computable.fst)
        (a.computableSize.comp (Computable.fst.comp Computable.fst))) Computable.snd))
  refine ⟨fun q=>(List.range (a.enc q.1).size).map (raw q),
    (c_rangeMap hr).comp Computable.id (a.computableSize.comp Computable.fst),?_⟩
  intro p s
  dsimp only
  rw [Encoding.enumerate,List.ofFn_eq_map,List.map_map]
  rw [←finRange_values ((a.enc p).size),List.map_map]
  apply List.map_congr_left
  intro i hi
  have hh:=hf p (s,(a.enc p).code.symm i)
  change f' (p,(((g.enc p).prod (a.enc p)).code (s,(a.enc p).code.symm i)).val)=_ at hh
  rw [prod_code,Equiv.apply_symm_apply] at hh
  exact hh

lemma Out.enumerate {a : UEncoding P A} {f : ∀p,A p → X} (hf : a.Out f) :
    Computable (fun p=>(a.enc p).enumerate.map (f p)) := by
  have hh:=out_list (g:=fixed Encoding.unit) hf.second
  obtain ⟨h,hr,he⟩:=hh
  exact (hr.comp (Computable.id.pair (Computable.const 0))).of_eq (fun p=>he p ())

lemma fixed_out (a : Encoding X) (x₀ : X) : (fixed (P:=P) a).Out (fun _ x=>x) := by
  let table:=a.enumerate
  refine ⟨fun q=>(table[q.2]?).getD x₀,?_,?_⟩
  · exact Primrec.option_getD.to_comp.comp
      ((Primrec.list_getElem?₁ table).to_comp.comp Computable.snd) (Computable.const x₀)
  · intro p x
    dsimp only
    change (a.enumerate[(a.code x).val]?).getD x₀=x
    simp [Encoding.enumerate,(a.code x).isLt]
lemma Map.out {a : UEncoding P A} {b : Encoding X} {f : ∀p,A p → X}
    (hf : a.Map (fixed b) f) (x₀ : X) : a.Out f := (fixed_out b x₀).comp hf
lemma Out.toBool {a : UEncoding P A} {f : ∀p,A p → Bool} (hf : a.Out f) : a.Map bool f := by
  obtain ⟨f',hr,h⟩:=hf
  refine ⟨fun q=>(f' q).toNat,(Primrec.dom_bool Bool.toNat).to_comp.comp hr,?_⟩
  intro p x
  dsimp only
  rw [h]
  exact (bool_code _).symm
lemma Out.cond {a : UEncoding P A} {c : ∀p,A p → Bool} {f g : ∀p,A p → X}
    (hc : a.Map bool c) (hf : a.Out f) (hg : a.Out g) :
    a.Out (fun p x=>if c p x then f p x else g p x) := by
  obtain ⟨c',hcr,hc⟩:=hc.out false
  obtain ⟨f',hfr,hf⟩:=hf
  obtain ⟨g',hgr,hg⟩:=hg
  exact ⟨_,Computable.cond hcr hfr hgr,by intro p x; simp only [hc,hf,hg,Bool.cond_eq_ite]⟩

end UEncoding
end MinUncut.Preprocess

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_UniformQuantifier
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
namespace UEncoding
variable {P : Type} [Primcodable P] {A B Γ : P → Type}

lemma Map.ofEq {a : UEncoding P A} {b : UEncoding P B}
    {f g : ∀p,A p → B p} (hf : a.Map b f) (h : ∀p x,f p x=g p x) : a.Map b g := by
  obtain ⟨f',hr,hf⟩:=hf
  exact ⟨f',hr,by intro p x; rw [hf,h]⟩

lemma map_true (a : UEncoding P A) : a.Map bool (fun _ _=>true) :=
  map_const (Computable.const 1)
lemma map_false (a : UEncoding P A) : a.Map bool (fun _ _=>false) :=
  map_const (Computable.const 0)

lemma map_forall {g : UEncoding P Γ} {a : UEncoding P A}
    {f : ∀p,Γ p × A p → Bool} [∀p s,Decidable (∀x,f p (s,x)=true)]
    (hf : (g.prod a).Map bool f) :
    g.Map bool (fun p s=>decide (∀x,f p (s,x)=true)) := by
  classical
  have hh := map_bool_eq (map_lambda hf) (map_lambda (map_true (g.prod a)))
  apply hh.ofEq
  intro p s
  apply decide_eq_decide.mpr
  exact ⟨fun h x=>congrFun h x,fun h=>funext h⟩

lemma map_exists {g : UEncoding P Γ} {a : UEncoding P A}
    {f : ∀p,Γ p × A p → Bool} [∀p s,Decidable (∃x,f p (s,x)=true)]
    (hf : (g.prod a).Map bool f) :
    g.Map bool (fun p s=>decide (∃x,f p (s,x)=true)) := by
  classical
  have hh := map_not (map_forall (map_not hf))
  apply hh.ofEq
  intro p s
  rw [←decide_not]
  apply decide_eq_decide.mpr
  simp

end UEncoding
end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_TemplateExpressions
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncut.FiniteProof MinUncut.Costed MinUncut.CodeEffective Turing.ToPartrec UEncoding
variable {P : Type} [Primcodable P] {A B : P → Type} {c : UEncoding P A}

def eqCode (a b : Code) : Code := branch (bin PolyProgram.add.code
  (bin PolyProgram.sub.code a b) (bin PolyProgram.sub.code b a)) (constCode 1) (constCode 0)
lemma p_eqCode : Primrec₂ eqCode := p_branch.comp
  (((p_bin _).comp ((p_bin _).comp Primrec.fst Primrec.snd)
    ((p_bin _).comp Primrec.snd Primrec.fst)).pair
    ((Primrec.const (constCode 1)).pair (Primrec.const (constCode 0))))
def lookupCode (a : Code) (xs : List (ℕ × ℕ)) : Code := xs.foldr
  (fun ix b=>branch (eqCode a (constCode ix.1)) b (constCode ix.2)) (constCode 0)
lemma p_lookupCode : Primrec₂ lookupCode := by
  exact Primrec.list_foldr Primrec.snd (Primrec.const (constCode 0))
    (p_branch.comp
      ((p_eqCode.comp (Primrec.fst.comp Primrec.fst)
        (p_constCode.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))).pair
        (Primrec.snd.comp Primrec.snd |>.pair
          (p_constCode.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))))).to₂
lemma out_constantTable {b : UEncoding P B} {f : ∀p,A p × B p → ℕ}
    (hf : (c.prod b).Out f) : c.Out (fun p x=>MinUncut.Outer.LocalTemplate.constantTable (b.enc p) (fun y=>f p (x,y))) :=
  out_list ((out_code b).second.pair hf)
end MinUncut.Preprocess.Syntax

end
end
section
namespace MinUncut.Preprocess.Source
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncut.SourceTemplate UEncoding

def positions : UEncoding ℕ Fin := UEncoding.fin id Computable.id

end MinUncut.Preprocess.Source

end
section

namespace MinUncut.Preprocess.UEncoding
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncutGames.Foundations.Hastad
variable {P : Type} [Primcodable P] {A Γ : P → Type}
lemma map_xor {g : UEncoding P Γ} {f h : ∀p,Γ p → Bool}
    (hf : g.Map bool f) (hh : g.Map bool h) : g.Map bool (fun p x=>f p x ^^ h p x) :=
  map_binary Encoding.bool Encoding.bool Encoding.bool Bool.xor hf hh

end MinUncut.Preprocess.UEncoding

end
section
namespace MinUncut.SourceTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap

lemma findValid_map {X : Type} (valid : X → Bool) (xs : List X) :
    (findValid valid xs).map Subtype.val=xs.find? valid := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h:valid x=true <;> simp [findValid,h,ih]

end MinUncut.SourceTemplate

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_UniformCube
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess.UEncoding
open MinUncutGames.Foundations.Hastad MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap
variable {P : Type} [Primcodable P] {A B Γ : P → Type}

lemma map_thirdQuery {g : UEncoding P Γ} {a : UEncoding P A} {b : UEncoding P B}
    {π : ∀p,Γ p → B p → A p} {f : ∀p,Γ p → A p → Bool}
    {h μ : ∀p,Γ p → B p → Bool}
    (hπ : g.Map (b.function a) π) (hf : g.Map (a.function bool) f)
    (hh : g.Map (b.function bool) h) (hμ : g.Map (b.function bool) μ) :
    g.Map (b.function bool) (fun p x=>thirdQuery (π p x) (f p x) (h p x) (μ p x)) := by
  exact map_lambda (map_xor (map_apply hh.first (map_snd g b))
    (map_xor (map_apply hf.first (map_apply hπ.first (map_snd g b)))
      (map_apply hμ.first (map_snd g b))))

lemma map_value_zero {g : UEncoding P Γ} {n : P → ℕ} {hn : Computable n}
    {f : ∀p,Γ p → Fin (n p)} (hf : g.Map (fin n hn) f) :
    g.Map bool (fun p x=>decide ((f p x).val=0)) := by
  obtain ⟨f',hf',hf⟩:=hf
  refine ⟨fun q=>(decide (f' q=0)).toNat,
    (Primrec.dom_bool Bool.toNat).to_comp.comp
      (Primrec.eq.decide.to_comp.comp hf' (Computable.const 0)),?_⟩
  intro p x
  dsimp only
  rw [hf]
  change _=(Encoding.bool.code _).val
  rw [bool_code]
  rfl
end MinUncut.Preprocess.UEncoding

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_OutputSize
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut
open MinUncutGames.BinaryEncoding

lemma Output.bits_length (G : Output) :
    G.bits.length=(nameBits G.vertices).length+G.vertices^2+(nameBits G.threshold).length := by
  unfold Output.bits
  simp only [List.length_append,List.length_flatMap,List.length_map,List.length_finRange]
  simp [pow_two]

end MinUncut

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_BitOutputBound
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut
open _root_.Turing MinUncutGames.Foundations.Complexity
lemma Output.vertices_le_bits (G : Output) : G.vertices≤G.bits.length := by
  have h:G.vertices≤G.vertices^2:=by
    by_cases hz:G.vertices=0
    · simp [hz]
    · have hp:1≤G.vertices:=Nat.one_le_iff_ne_zero.mpr hz
      simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left G.vertices hp
  rw [G.bits_length]
  omega
end MinUncut

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformAlgebra
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open scoped BigOperators
variable {P X : Type} [Primcodable P] [Primcodable X] [AddCommMonoid X]

namespace UEncoding
variable {A B Γ : P → Type}
omit [AddCommMonoid X] in
lemma Out.toFixed {a : UEncoding P A} {b : Encoding X} [Finite X]
    {f : ∀p,A p → X} (hf : a.Out f) : a.Map (fixed b) f := by
  obtain ⟨f',hr,he⟩:=hf
  exact ⟨_,(Primrec.dom_finite (fun x=>(b.code x).val)).to_comp.comp hr,
    by intro p x; dsimp only; rw [he]; rfl⟩

end UEncoding
end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_UniformFind
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
namespace UEncoding
variable {P : Type} [Primcodable P] {A B Γ : P → Type}

def option (a : UEncoding P A) : UEncoding P (fun p=>Option (A p)) :=
  (a.sum (fixed Encoding.unit)).ofEquiv (fun p=>optionEquiv (A p))
lemma option_code_some (a : UEncoding P A) (p : P) (x : A p) :
    ((a.option.enc p).code (some x)).val=((a.enc p).code x).val := rfl
lemma option_code_none (a : UEncoding P A) (p : P) :
    ((a.option.enc p).code none).val=(a.enc p).size := by
  change (a.enc p).size+0=_
  omega

lemma enumeration_codes {X : Type} (a : Encoding X) :
    a.enumerate.map (fun x=>(a.code x).val)=List.range a.size := by
  simp only [Encoding.enumerate,List.map_ofFn]
  rw [List.ofFn_eq_map]
  simpa only [Function.comp_def,Equiv.apply_symm_apply] using finRange_values a.size

lemma map_find (a : UEncoding P A) :
    (a.function bool).Map a.option (fun p f=>(a.enc p).enumerate.find? f) := by
  let search : ℕ × ℕ → ℕ := fun q=>(List.range q.1).findIdx (fun i=>decide ((q.2/2^i)%2=1))
  have hs : Primrec search := by
    exact Primrec.list_findIdx (Primrec.list_range.comp Primrec.fst)
      (Primrec.eq.decide.comp₂
        (Primrec.nat_mod.comp₂
          (Primrec.nat_div.comp₂ (Primrec.snd.comp Primrec.fst).to₂
            (primrec_pow.comp₂ (Primrec.const 2).to₂ Primrec.snd.to₂))
          (Primrec.const 2).to₂) (Primrec.const 1).to₂)
  refine ⟨fun q=>search ((a.enc q.1).size,q.2),hs.to_comp.comp
    ((a.computableSize.comp Computable.fst).pair Computable.snd),?_⟩
  intro p f
  have he : search ((a.enc p).size,((a.function bool).enc p).code f|>.val)=
      (a.enc p).enumerate.findIdx f := by
    unfold search
    rw [←enumeration_codes (a.enc p),List.findIdx_map]
    congr 1
    funext x
    have hd:=function_digit (a.enc p) Encoding.bool f x
    change decide ((((a.enc p).function Encoding.bool).code f|>.val)/Encoding.bool.size^((a.enc p).code x|>.val)%Encoding.bool.size=1)=f x
    rw [hd,bool_code]
    cases f x <;> rfl
  dsimp only
  rw [he,List.find?_eq_getElem?_findIdx]
  by_cases h:(a.enc p).enumerate.findIdx f < (a.enc p).size
  · rw [show (a.enc p).enumerate=((List.ofFn (a.enc p).code.symm)) from rfl]
    dsimp only [Encoding.enumerate] at h
    rw [List.getElem?_ofFn,dite_eq_left h]
    simp only [option_code_some,Equiv.apply_symm_apply]
  · have hn : (a.enc p).enumerate.findIdx f=(a.enc p).size :=
      le_antisymm (by simpa using List.findIdx_le_length (p:=f) (xs:=(a.enc p).enumerate)) (by omega)
    rw [hn,List.getElem?_eq_none (by simp),option_code_none]

lemma map_find_apply {g : UEncoding P Γ} {a : UEncoding P A}
    {f : ∀p,Γ p → A p → Bool} (hf : g.Map (a.function bool) f) :
    g.Map a.option (fun p x=>(a.enc p).enumerate.find? (f p x)) := map_comp hf (map_find a)

end UEncoding
end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformEquation
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Preprocess.Source
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap
open MinUncut.SourceTemplate UEncoding

abbrev up {A : ℕ → Type} (a : UEncoding ℕ A) : UEncoding Par (fun p=>A p.1) := a.pullback Prod.fst Computable.fst

variable {Γ : Par → Type} {e : UEncoding Par Γ}

def ds : UEncoding Par (fun p=>Fin p.2) := fin Prod.snd Computable.snd
end MinUncut.Preprocess.Source

noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncutGames.Foundations.PCP
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncutGames.Foundations.Hastad.SourceContexts
open MinUncut.Costed MinUncut.SourceTemplate UEncoding
variable {P Q : Type} [Primcodable P] [Primcodable Q] {A : P → Type} {c : UEncoding P A}

abbrev unitN : UEncoding ℕ (fun _=>Unit) := UEncoding.fixed Encoding.unit
end MinUncut.Preprocess.Syntax

namespace MinUncut.Preprocess.Face
open MinUncut.Inner MinUncut.FiniteProof
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open UEncoding
open scoped BigOperators
variable {P : Type} [Primcodable P]
variable (m n : P → ℕ) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
def axes := fin m hm
def values := fin n hn
def points := (axes m hm).function (values n hn)
def rowPairs := (axes m hm).prod (points m n hm hn)
def rowGood (p : P) (x : Fin (m p) × Point (m p) (n p)) : Bool :=
  decide (x.2 x.1=⟨0,hnpos p⟩)
lemma map_rowGood : (rowPairs m n hm hn).Map bool (rowGood m n hnpos) := by
  exact map_bool_eq
    (map_apply (map_snd (axes m hm) (points m n hm hn)) (map_fst _ _))
    (map_const (Computable.const 0))

end MinUncut.Preprocess.Face

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformOutput
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess.UEncoding
variable {P Q : Type} [Primcodable P] [Primcodable Q] {A : P → Type}
  {X : Type} [Primcodable X]
lemma Out.pullback {a : UEncoding P A} {g : ∀p,A p → X}
    (hg : a.Out g) {f : Q → P} (hf : Computable f) :
    (a.pullback f hf).Out (fun q x=>g (f q) x) := by
  obtain ⟨g',hgr,hg⟩:=hg
  exact ⟨fun q=>g' (f q.1,q.2),hgr.comp ((hf.comp Computable.fst).pair Computable.snd),
    by intro q x; exact hg (f q) x⟩
lemma Out.cons {a : UEncoding P A} {f : ∀p,A p → X} {g : ∀p,A p → List X}
    (hf : a.Out f) (hg : a.Out g) : a.Out (fun p x=>f p x::g p x) :=
  hf.map₂ hg Primrec.list_cons.to_comp
lemma out_boolNat {a : UEncoding P A} {f : ∀p,A p → Bool} (hf : a.Map bool f) :
    a.Out (fun p x=>(f p x).toNat) :=
  (hf.out false).map (Primrec.dom_bool Bool.toNat).to_comp
end MinUncut.Preprocess.UEncoding

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_UniformAlphabet
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Alphabet
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open UEncoding
open scoped BigOperators
variable {P : Type} [Primcodable P]
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
variable (hc : Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code (h p)).val))
abbrev Slot (p : P) := Σj:Fin (t p),Fin (width (h p j))
def axes := fin t ht
def positions : UEncoding P (fun _=>Fin 3) := fixed (Encoding.fin 3)
def slotPairs := (axes t ht).prod (positions (P:=P))
omit [Primcodable P] in
lemma slotGood_iff (p : P) (x : Fin (t p) × Fin 3) :
    slotGood t h p x=true ↔ x.2.val<width (h p x.1) := by
  cases hh:h p x.1
  · simp [slotGood,hh,width,x.2.isLt]
  · simp only [slotGood,hh,Bool.not_true,Bool.false_or,decide_eq_true_eq,width,ite_true]
    constructor
    · intro hx; rw [hx]; decide
    · intro hx; apply Fin.ext; change x.2.val=0; omega
include hc in
lemma map_slotGood : (slotPairs t ht).Map bool (slotGood t h) := by
  have hh : (slotPairs t ht).Map ((axes t ht).function bool) (fun p _=>h p) := map_const hc
  exact map_or (map_not (map_apply hh (map_fst _ _)))
    (map_bool_eq (map_snd _ _) (map_const (Computable.const 0)))

def slotEquiv (p : P) : Slot t h p ≃ {x:Fin (t p) × Fin 3 // slotGood t h p x=true} where
  toFun x := ⟨(x.1,⟨x.2.val,by
    have hx:=x.2.isLt
    have hw:width (h p x.1)≤3 := by cases h p x.1 <;> decide
    omega⟩),(slotGood_iff t h p _).mpr x.2.isLt⟩
  invFun x := ⟨x.val.1,⟨x.val.2.val,(slotGood_iff t h p x.val).mp x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def slots : UEncoding P (Slot t h) :=
  ((slotPairs t ht).restrict (slotGood t h) (map_slotGood t ht h hc)).ofEquiv (slotEquiv t h)
end MinUncut.Preprocess.Alphabet

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformProduct
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open scoped BigOperators
variable {P X : Type} [Primcodable P] [Primcodable X] [CommMonoid X]

namespace UEncoding
variable {A B Γ : P → Type}

omit [Primcodable X] [CommMonoid X] in
lemma computableCard (a : UEncoding P A) [∀p,Fintype (A p)] : Computable (fun p=>Fintype.card (A p)) :=
  a.computableSize.of_eq (fun p=>(Fintype.card_congr (a.enc p).code).trans (Fintype.card_fin _)|>.symm)

end UEncoding
end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_UniformDemandAlphabet
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Alphabet
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate MinUncut.FiniteProof
open MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
attribute [local instance] Classical.propDecidable
variable {P : Type} [Primcodable P]
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
variable (hc : Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code (h p)).val))
def positionsList := (axes t ht).function (positions (P:=P))
def equalities := (axes t ht).function ((positions (P:=P)).function ((positions (P:=P)).function bool))
lemma map_slotCoords : (slots t ht h hc).Map (slotPairs t ht)
    (fun _ x=>((slotEquiv t h _ x).val)) :=
  map_comp (map_to _ (slotEquiv t h)) (map_restrict_val _ _ (map_slotGood t ht h hc))
lemma map_slotAxis : (slots t ht h hc).Map (axes t ht) (fun _ x=>x.1) := by
  have hh := map_comp (map_slotCoords t ht h hc) (map_fst (axes t ht) (positions (P:=P)))
  exact hh
lemma map_slotPosition : (slots t ht h hc).Map (positions (P:=P))
    (fun p x=>(slotEquiv t h p x).val.2) := by
  have hh := map_comp (map_slotCoords t ht h hc) (map_snd (axes t ht) (positions (P:=P)))
  exact hh
end MinUncut.Preprocess.Alphabet

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformGrid
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.FiniteProof MinUncut.FiniteGaussian MinUncut.Outer
open MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
open scoped BigOperators
namespace UEncoding
variable {P X : Type} [Primcodable P] [Primcodable X] {A : P → Type}
lemma Out.unit {f : P → X} (hf : (fixed (P:=P) Encoding.unit).Out (fun p _=>f p)) : Computable f := by
  obtain ⟨g,hg,hh⟩:=hf
  exact (hg.comp (Computable.id.pair (Computable.const 0))).of_eq (fun p=>hh p ())
end UEncoding

open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate MinUncut.FiniteProof MinUncut.FiniteGaussian
open MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
end MinUncut.Preprocess

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformEquationOutput
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess.UEncoding
open MinUncutGames.Foundations.Hastad.SourceOccurrences MinUncutGames.Reduction.CloneGap
variable {P : Type} [Primcodable P] {A B : P → Type} {X : Type} [Primcodable X]
lemma out_elimSum {a : UEncoding P A} {b : UEncoding P B} {f : ∀p,A p → X} {g : ∀p,B p → X}
    (hf : a.Out f) (hg : b.Out g) :
    (a.sum b).Out (fun p x=>Sum.elim (f p) (g p) x) := by
  obtain ⟨f',hfr,hf⟩:=hf
  obtain ⟨g',hgr,hg⟩:=hg
  let sz : P × ℕ → ℕ := fun p=>(a.enc p.1).size
  have hs : Computable sz := a.computableSize.comp Computable.fst
  let raw : P × ℕ → X := fun x=>if x.2 < sz x then f' x else g' (x.1,x.2-sz x)
  refine ⟨raw,?_,?_⟩
  · exact (Computable.cond (ca_natLt Computable.snd hs).decide hfr
      (hgr.comp (Computable.fst.pair (ca_sub Computable.snd hs)))).of_eq
        (by intro p; simp only [raw,Bool.cond_eq_ite,decide_eq_true_eq])
  · intro p x
    cases x with
    | inl x =>
      change (if ((a.enc p).code x).val<(a.enc p).size then _ else _)=_
      rw [ite_eq_left ((a.enc p).code x).isLt]
      change f' (p,((a.enc p).code x).val)=f p x
      exact hf p x
    | inr x =>
      change (if (a.enc p).size+((b.enc p).code x).val<(a.enc p).size then _ else _)=_
      rw [ite_eq_right (by omega)]
      change g' (p,(a.enc p).size+((b.enc p).code x).val-(a.enc p).size)=_
      rw [Nat.add_sub_cancel_left,hg]
      rfl
end MinUncut.Preprocess.UEncoding

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformSets
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess
open MinUncut.Outer MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
open scoped BigOperators
def maskEquiv (t : ℕ) : Finset (Fin t) ≃ (Fin t → Bool) where
  toFun := hiddenSet
  invFun h := Finset.univ.filter (fun i=>h i=true)
  left_inv S := by ext i; simp [hiddenSet]
  right_inv h := by funext i; simp [hiddenSet]
def setEncoding (t : ℕ) : Encoding (Finset (Fin t)) :=
  ⟨2^t,(maskEquiv t).trans (((Encoding.fin t).function Encoding.bool).code)⟩
def rawSet (t z : ℕ) : Finset (Fin t) :=
  (setEncoding t).code.symm ⟨z%(2^t),Nat.mod_lt _ (pow_pos (by decide) _)⟩
lemma rawSet_code (t : ℕ) (S : Finset (Fin t)) :
    rawSet t ((setEncoding t).code S).val=S := by
  unfold rawSet
  have hs : ((setEncoding t).code S).val<2^t := ((setEncoding t).code S).isLt
  simp only [Nat.mod_eq_of_lt hs]
  exact (setEncoding t).code.symm_apply_apply S
lemma rawSet_maskCode (t z : ℕ) :
    (((Encoding.fin t).function Encoding.bool).code (hiddenSet (rawSet t z))).val=z%(2^t) := by
  change ((setEncoding t).code ((setEncoding t).code.symm _)).val=_
  rw [Equiv.apply_symm_apply]
variable {P : Type} [Primcodable P]
def sets (t : P → ℕ) (ht : Computable t) : UEncoding P (fun p=>Finset (Fin (t p))) where
  enc p := setEncoding (t p)
  computableSize := ca_pow (ca_const 2) ht
lemma map_hidden (t : P → ℕ) (ht : Computable t) :
    (sets t ht).Map ((fin t ht).function bool) (fun _ S=>hiddenSet S) :=
  ⟨Prod.snd,Computable.snd,by intros; rfl⟩
lemma c_rawHidden (t : P → ℕ) (ht : Computable t) (z : P → ℕ) (hz : Computable z) :
    Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code
      (hiddenSet (rawSet (t p) (z p)))).val) :=
  (ca_mod hz (ca_pow (ca_const 2) ht)).of_eq (by intro p; exact (rawSet_maskCode _ _).symm)
end MinUncut.Preprocess

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_ArithmeticTactic
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

set_option maxHeartbeats 1000000
section
namespace MinUncut.Preprocess
open MinUncut.FiniteGaussian

@[fun_prop] lemma c_gridField : Computable gridField :=
  Computable.snd.comp (Computable.unpair.comp
    (ca_sub (Computable.fst.comp Computable.unpair) (ca_const 1)))
end MinUncut.Preprocess

end

end OAI
end


