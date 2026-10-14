-- Prove2me | Definitions.Def_OAI_QuantumFactoring_Part16
-- name    : OAI_QuantumFactoring_Part16
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T07:58:55.286994+00:00
-- url     : https://prove2.me/theorems/d7bbe219-5544-4a5b-a552-6dd351bb3607
-- title:
--   Exact quantum factoring, part 16 of 38 (port of OpenAI's formalization)
-- statement:
--   Part 16 of 38 of a port of OpenAI's Lean formalization of the manuscript *Exact quantum factoring over a fixed finite gate set* (OpenAI, September 25, 2026). This part contains the modules `PhysicalMachine`, `HardCofactor`, `UniversalSplit`, `NodeStateCircuit`, `NodeSplitMachine`, `NodeStateNil`, `NodeProgress`, `PhysicalMachineMass`, `PhysicalNodeCompletion`, `SortedWords`, `SortedEncoding`, `SortingCircuit`, `TensorList`, `PhysicalNodeOutput`, `MachineInitialization`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/QuantumFactoring`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `ExactQuantumFactoring`, which is identical to upstream `Basic.lean`.
--
--   The development is split into 38 parts only so that each compiles within the platform's time limit. Together the parts supply the circuit family `PhysicalTree.finalCircuit` and its specification, used to prove `OAI.ExactQuantumFactoring.zero_amplitude_core`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/QuantumFactoring: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalMachine.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/HardCofactor.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/UniversalSplit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/NodeStateCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/NodeSplitMachine.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/NodeStateNil.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/NodeProgress.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalMachineMass.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalNodeCompletion.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/SortedWords.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/SortedEncoding.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/SortingCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/TensorList.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalNodeOutput.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/MachineInitialization.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf

/-
Exact quantum factoring development (port of OpenAI's formalization), part 16 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: PhysicalMachine.lean, HardCofactor.lean, UniversalSplit.lean, NodeStateCircuit.lean, NodeSplitMachine.lean, NodeStateNil.lean, NodeProgress.lean, PhysicalMachineMass.lean, PhysicalNodeCompletion.lean, SortedWords.lean, SortedEncoding.lean, SortingCircuit.lean, TensorList.lean, PhysicalNodeOutput.lean, MachineInitialization.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part15

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalMachine.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork RecordedHistory

lemma oracleOn_encode {α : Type*} [Fintype α] {n m r : ℕ}
    (e : α→Basis n) (ψ : α→ℂ) (c : BooleanNetwork n m) (hc : c.net.count≤r) :
    (programMatrix (oracleOn c hc)).mulVec
      (encodeState (fun a=>packed r (e a) (fun _=>false)) ψ)=
    encodeState (fun a=>packed r (e a) (c.eval (e a))) ψ := by
  rw [encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,oracleOn_basis,Bool.false_xor]
  rfl

lemma appendPrepared_state_dependent {α β : Type*} [Fintype α] [Fintype β] {p q r : ℕ}
    (e : α→Basis p) (f : α→β→Basis q) (ψ : α→ℂ) (F : α→β→ℂ)
    (A : List (Instruction p)) (v : Basis p)
    (hA : (programMatrix A).mulVec (basisVector v)=encodeState e ψ)
    (c : BooleanNetwork p q) (hc : c.net.count≤r) (ops : List (Instruction q))
    (hlocal : ∀ a,(programMatrix ops).mulVec (basisVector (c.eval (e a)))=
      encodeState (f a) (F a)) :
    (programMatrix (appendPrepared A c hc ops)).mulVec
      (basisVector (packed r v (fun _=>false)))=
    encodeState (fun ab : α×β=>packed r (e ab.1) (f ab.1 ab.2)) (appendState ψ F) := by
  rw [appendPrepared,programMatrix_append,←Matrix.mulVec_mulVec,firstProgram_basis,hA,encodeState_comp]
  exact preparedOracle_encode_dependent e f ψ F c hc ops hlocal

/-- A bit-level finite-state controller. Both transition functions are literal
Boolean networks; this structure does not grant any classical computation oracle. -/
structure SplitMachine (n c : ℕ) where
  query : BooleanNetwork c n
  update : BooleanNetwork (c+FixedSplit.width n) c

namespace SplitMachine
variable {n c : ℕ} (M : SplitMachine n c)

abbrev initWork := M.query.net.count+(FixedSplit.initialNet n).net.count
abbrev updateWork := M.update.net.count

abbrev width : ℕ→ℕ
  | 0=>c
  | t+1=>(width t+FixedSplit.width n+M.initWork)+c+M.updateWork

def current : (t : ℕ)→Register c (M.width t)
  | 0=>⟨id,Function.injective_id⟩
  | t+1=>targetRegister (M.width t+FixedSplit.width n+M.initWork) c M.updateWork

def currentNet (t : ℕ) : BooleanNetwork (M.width t) c := select (M.current t)
def initNet (t : ℕ) : BooleanNetwork (M.width t) (FixedSplit.width n) :=
  ((M.currentNet t).comp M.query).comp (FixedSplit.initialNet n)
lemma initNet_count (t : ℕ) : (M.initNet t).net.count=M.initWork := by
  simp only [initNet,count_comp,currentNet,count_select,zero_add]

def updateNet (t : ℕ) : BooleanNetwork (M.width t+FixedSplit.width n+M.initWork) c :=
  (((select (firstRegister (M.width t) (FixedSplit.width n) M.initWork)).comp
    (M.currentNet t)).pair (select (targetRegister (M.width t) (FixedSplit.width n) M.initWork))).comp M.update
lemma updateNet_count (t : ℕ) : (M.updateNet t).net.count=M.updateWork := by
  simp only [updateNet,count_comp,count_pair,count_select,currentNet,zero_add]

def program : (t : ℕ)→List (Instruction (M.width t))
  | 0=>[]
  | t+1=>firstProgram c M.updateWork
      (appendPrepared (program t) (M.initNet t) (M.initNet_count t).le (FixedSplit.program n))++
      oracleOn (M.updateNet t) (M.updateNet_count t).le

def initial : (t : ℕ)→Basis c→Basis (M.width t)
  | 0,x=>x
  | t+1,x=>packed M.updateWork (packed M.initWork (initial t x) (fun _=>false)) (fun _=>false)

abbrev Trace (n : ℕ) : ℕ→Type
  | 0=>Unit
  | t+1=>Trace n t×FixedSplit.Raw n
noncomputable instance traceFintype (n t : ℕ) : Fintype (Trace n t) := by
  induction t with
  | zero=>exact inferInstanceAs (Fintype Unit)
  | succ t ih=>letI:=ih;exact inferInstanceAs (Fintype (Trace n t×FixedSplit.Raw n))

def next (x : Basis c) (r : FixedSplit.Raw n) : Basis c :=
  M.update.eval (Fin.append x (FixedSplit.encoding (M.query.eval x) r))
def config (x : Basis c) : (t : ℕ)→Trace n t→Basis c
  | 0,_=>x
  | t+1,h=>M.next (config x t h.1) h.2

def encoded (x : Basis c) : (t : ℕ)→Trace n t→Basis (M.width t)
  | 0,_=>x
  | t+1,h=>packed M.updateWork
      (packed M.initWork (encoded x t h.1)
        (FixedSplit.encoding (M.query.eval (M.config x t h.1)) h.2)) (M.config x (t+1) h)
noncomputable def state (x : Basis c) : (t : ℕ)→Trace n t→ℂ
  | 0,_=>1
  | t+1,h=>state x t h.1*FixedSplit.fresh (M.query.eval (M.config x t h.1)) h.2

lemma current_encoded (x : Basis c) (t : ℕ) (h : Trace n t) :
    (M.currentNet t).eval (M.encoded x t h)=M.config x t h := by
  cases t with
  | zero=>rfl
  | succ t=>exact packed_targetRegister _ _
lemma initNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) :
    (M.initNet t).eval (M.encoded x t h)=FixedSplit.zero (M.query.eval (M.config x t h)) := by
  rw [initNet,eval_comp,FixedSplit.initialNet_eval,eval_comp,M.current_encoded]
lemma updateNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : FixedSplit.Raw n) :
    (M.updateNet t).eval (packed M.initWork (M.encoded x t h)
      (FixedSplit.encoding (M.query.eval (M.config x t h)) r))=M.next (M.config x t h) r := by
  rw [updateNet,eval_comp,eval_pair,eval_comp,eval_select,packed_first,
    M.current_encoded,eval_select,packed_targetRegister]
  rfl

/-- The actual adaptive quantum history, not a table of independent
counterfactual branches. Every update and next modulus comes from this run. -/
theorem program_state (x : Basis c) (t : ℕ) :
    (programMatrix (M.program t)).mulVec (basisVector (M.initial t x))=
      encodeState (M.encoded x t) (M.state x t) := by
  induction t with
  | zero=>
    simp only [program,initial,programMatrix,state,encoded,encodeState]
    simp [Trace]
  | succ t ih=>
    have hp := appendPrepared_state_dependent (M.encoded x t)
      (fun h r=>FixedSplit.encoding (M.query.eval (M.config x t h)) r) (M.state x t)
      (fun h=>FixedSplit.fresh (M.query.eval (M.config x t h)))
      (M.program t) (M.initial t x) ih (M.initNet t) (M.initNet_count t).le
      (FixedSplit.program n) (by
        intro h
        rw [M.initNet_encoded,FixedSplit.program_state])
    dsimp only [program,initial,width]
    rw [programMatrix_append,←Matrix.mulVec_mulVec,firstProgram_basis,hp,encodeState_comp]
    simp only [Function.comp_def]
    rw [oracleOn_encode (fun ab : Trace n t×FixedSplit.Raw n=>
      packed M.initWork (M.encoded x t ab.1) (FixedSplit.encoding
        (M.query.eval (M.config x t ab.1)) ab.2))
      (appendState (M.state x t) (fun h=>FixedSplit.fresh (M.query.eval (M.config x t h))))
      (M.updateNet t) (M.updateNet_count t).le]
    congr 1
    funext h
    rw [M.updateNet_encoded]
    rfl

lemma encoded_injective (x : Basis c) (t : ℕ) : Function.Injective (M.encoded x t) := by
  induction t with
  | zero=>intro a b _;exact @Subsingleton.elim Unit inferInstance a b
  | succ t ih=>
    rintro ⟨a,r⟩ ⟨b,s⟩ he
    dsimp only [encoded] at he
    have hinner := congrArg (fun z=>z ∘ firstRegister (M.width t+FixedSplit.width n+M.initWork) c M.updateWork) he
    simp only [packed_first] at hinner
    have he' := congrArg (fun z=>z ∘ firstRegister (M.width t) (FixedSplit.width n) M.initWork) hinner
    simp only [packed_first] at he'
    have hab : a=b := ih he' 
    subst b
    have hr := congrArg (fun z=>z ∘ targetRegister (M.width t) (FixedSplit.width n) M.initWork) hinner
    simp only [packed_targetRegister] at hr
    have hrs : r=s := FixedSplit.encoding_injective _ hr
    subst s
    rfl

lemma width_eq (t : ℕ) : M.width t=c+t*(FixedSplit.width n+M.initWork+c+M.updateWork) := by
  induction t with
  | zero=>simp [width]
  | succ t ih=>simp only [width,ih];ring

lemma program_length (t : ℕ) : (M.program t).length≤
    t*(4*M.initWork+2*FixedSplit.width n+(FixedSplit.program n).length+4*M.updateWork+2*c) := by
  induction t with
  | zero=>simp [program]
  | succ t ih=>
    have hp := appendPrepared_length (M.program t) (M.initNet t) (M.initNet_count t).le (FixedSplit.program n)
    have hu := oracleOn_length (M.updateNet t) (M.updateNet_count t).le
    simp only [M.initNet_count] at hp
    simp only [M.updateNet_count] at hu
    simp only [program,List.length_append,firstProgram_length]
    rw [Nat.succ_mul]
    omega

end SplitMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/HardCofactor.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

/-- The randomized splitter is invoked only after the prime and perfect-power
cases. Such an input has two genuinely different prime-power components. -/
lemma exists_distinct_components {m : ℕ} (hm : 2 ≤ m) (hc : ¬m.Prime)
    (hp : ¬Primality.PerfectPower m) : ∃ p₀ p₁ : Component m, p₁≠p₀ := by
  obtain ⟨p,hp₀⟩ := Nat.nonempty_primeFactors.mpr (by omega : 1 < m)
  by_cases hh : ∀ q∈m.primeFactors,q=p
  · have hs : m.factorization.support ⊆ {p} := by
      intro q hq
      rw [Nat.support_factorization] at hq
      exact Finset.mem_singleton.mpr (hh q hq)
    have hpow : p^(m.factorization p)=m := by
      have he := m.factorization.prod_of_support_subset hs (fun p e => p^e)
        (by intro i _; simp)
      simpa only [Finset.prod_singleton] using he.symm.trans (Nat.prod_factorization_pow_eq_self (by omega))
    have hprime := (Nat.mem_primeFactors.mp hp₀).1
    have hexp : m.factorization p≠0 := by
      apply Finsupp.mem_support_iff.mp
      simpa only [Nat.support_factorization] using hp₀
    by_cases he : m.factorization p=1
    · rw [he,pow_one] at hpow
      exact False.elim (hc (hpow ▸ hprime))
    · exact False.elim (hp ⟨p,m.factorization p,hprime.two_le,by omega,hpow⟩)
  · push Not at hh
    obtain ⟨q,hq,hne⟩ := hh
    exact ⟨⟨p,hp₀⟩,⟨q,hq⟩,fun h => hne (congrArg Subtype.val h)⟩

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/UniversalSplit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials OrderTrial
namespace UniversalSplit

/-- The unchanging request register dimensions depend only on the original n. -/
abbrev Raw := FixedSplit.Raw

def Hard (m : ℕ) : Prop := 2 ≤ m ∧ ¬m.Prime ∧ Odd m ∧ ¬Primality.PerfectPower m

/-- Source's distinguished component: the least prime divisor, not an arbitrary
component for which the compiler would need extra advice. -/
def firstComponent {m : ℕ} (hm : 2 ≤ m) : Component m :=
  ⟨m.minFac,Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd m,by omega⟩⟩

lemma secondComponent {m : ℕ} (hm : Hard m) :
    ∃ p₁ : Component m,p₁≠firstComponent hm.1 := by
  classical
  obtain ⟨a,b,hne⟩ := exists_distinct_components hm.1 hm.2.1 hm.2.2.2
  by_cases ha : a=firstComponent hm.1
  · exact ⟨b,by simpa only [←ha] using hne⟩
  · exact ⟨a,ha⟩

noncomputable def dummyList {n : ℕ} : PhysicalListSlots.Result n→Prop :=
  Completion.passed (fun _=>True) (natBasis _ 0) 1 (Completion.target n)
noncomputable def dummyOrder {n : ℕ} : OrderSlots.Result n→Prop :=
  Completion.passed (fun _=>True) (natBasis _ 0) 1 (Completion.target n)
noncomputable def dummy {n : ℕ} (r : Raw n) : Prop := dummyList r.1 ∧ ∀ i,dummyOrder (r.2 i)

lemma dummy_mass {n : ℕ} (hn : 128 ≤ n) (m : Basis n) :
    outcomeMass dummy (FixedSplit.fresh m)=(Completion.target n:ℝ)^(n^5+1) := by
  change outcomeMass (fun r : Raw n => dummyList r.1 ∧ (fun (_ : PhysicalListSlots.Result n)
    (rr : Fin (n^5)→OrderSlots.Result n)=>∀ i,dummyOrder (rr i)) r.1 r.2)
      (RecordedHistory.appendState _ _) = _
  have ho : ∀ l : PhysicalListSlots.Result n, outcomeMass
      (fun rr : Fin (n^5)→OrderSlots.Result n => ∀ i,dummyOrder (rr i))
      (productState (fun i=>OrderSlots.fresh n (FixedSplit.bases l i) m))=
        (Completion.target n:ℝ)^(n^5) := by
    intro l
    rw [productState_all_mass]
    have he : ∀ i : Fin (n^5),outcomeMass dummyOrder
        (OrderSlots.fresh n (FixedSplit.bases l i) m)=(Completion.target n:ℝ) := by
      intro i
      exact Completion.dummy_passed_mass _ n _ hn
        (tensor_normalized _ _ (raw_normalized _ _ _ _)) (natBasis _ 0)
    simp only [he,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [RecordedHistory.append_constant_mass (PhysicalListSlots.fresh m)
    (fun l=>productState (fun i=>OrderSlots.fresh n (FixedSplit.bases l i) m))
    dummyList (fun _ rr=>∀ i,dummyOrder (rr i)) ((Completion.target n:ℝ)^(n^5)) (fun l _=>ho l)]
  have hl := Completion.dummy_passed_mass (PhysicalListSlots.ordinaryState m) n (n*n^5)
    hn (PhysicalListSlots.ordinary_normalized m) (natBasis _ 0)
  change outcomeMass dummyList (PhysicalListSlots.fresh m)=(Completion.target n:ℝ) at hl
  rw [hl]
  exact (mul_comm _ _).trans (pow_succ (Completion.target n:ℝ) (n^5)).symm

noncomputable def passed {n : ℕ} (m : Basis n) : Raw n→Prop := by
  classical
  exact if h : Hard (bitsValue m).toNat then
    FixedSplit.passed m (by have := h.1; omega) (firstComponent h.1) else dummy

lemma passed_mass {n : ℕ} (hn : 128 ≤ n) (m : Basis n) :
    outcomeMass (passed m) (FixedSplit.fresh m)=(Completion.target n:ℝ)^(n^5+1) := by
  classical
  unfold passed
  split_ifs with h
  · obtain ⟨p₁,hne⟩ := secondComponent h
    exact FixedSplit.passed_mass hn m h.1 h.2.2.1 (firstComponent h.1) p₁ hne
  · exact dummy_mass hn m

lemma passed_divisor {n : ℕ} (hn : 128 ≤ n) (m : Basis n)
    (hm : 2 ≤ (bitsValue m).toNat) (hc : ¬(bitsValue m).toNat.Prime)
    (r : Raw n) (hr : passed m r) :
    FactorController.ProperDivisor (bitsValue m).toNat (FixedSplit.divisor m r) := by
  classical
  have hh := hr
  unfold passed at hh
  split_ifs at hh with h
  · obtain ⟨p₁,hne⟩ := secondComponent h
    exact FixedSplit.passed_divisor hn m hm hc h.2.2.1 (firstComponent h.1) p₁ hne r hh
  · apply suppliedDivisor_good hm (bitsValue m).isLt hc
    intro ho hpow
    exact False.elim (h ⟨hm,hc,ho,hpow⟩)

/-- Every quantum preparation below is the same physical fixed-width program
(on the runtime input word). Hard/easy tests affect the deferred predicate only. -/
noncomputable def fresh (n m : ℕ) : Raw n→ℂ := FixedSplit.fresh (natBasis n m)
noncomputable def good (n m : ℕ) : Raw n→Prop := passed (natBasis n m)
noncomputable def decode (n m : ℕ) (r : Raw n) : ℕ := FixedSplit.divisor (natBasis n m) r

lemma fresh_normalized (n m : ℕ) : ∑ r,Complex.normSq (fresh n m r)=1 :=
  FixedSplit.fresh_normalized _
lemma good_mass {n : ℕ} (hn : 128 ≤ n) (m : ℕ) :
    outcomeMass (good n m) (fresh n m)=(Completion.target n:ℝ)^(n^5+1) := passed_mass hn _

lemma good_divisor {n m : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hb : m<2^n) (hc : ¬m.Prime)
    (r : Raw n) (hr : good n m r) : FactorController.ProperDivisor m (decode n m r) := by
  have he : (bitsValue (natBasis n m)).toNat=m := by simpa only [natBasis_value] using Nat.mod_eq_of_lt hb
  have hh := passed_divisor hn (natBasis n m) (by simpa only [he] using hm)
    (by simpa only [he] using hc) r hr
  simpa only [he,decode] using hh

end UniversalSplit
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NodeStateCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork FactorController
namespace NodeStateCircuit

abbrev width (s w : ℕ) := ((s+1)*w+(s+1)*w)+1
abbrev inWidth (s w : ℕ) := width s w+w

def pending (s w : ℕ) : BooleanNetwork (width s w) ((s+1)*w) :=
  select ((Fin.castAdd 1) ∘ (Fin.castAdd ((s+1)*w)))
def output (s w : ℕ) : BooleanNetwork (width s w) ((s+1)*w) :=
  select ((Fin.castAdd 1) ∘ (Fin.natAdd ((s+1)*w)))
def bad (s w : ℕ) : BooleanNetwork (width s w) 1 :=
  select (Fin.natAdd ((s+1)*w+(s+1)*w))
def top (s w : ℕ) : BooleanNetwork (width s w) w := (pending s w).comp (blockNet (s+1) w 0)
def old (s w : ℕ) : BooleanNetwork (inWidth s w) (width s w) := select (Fin.castAdd w)
def supplied (s w : ℕ) : BooleanNetwork (inWidth s w) w := select (Fin.natAdd (width s w))
def nodeInput (s w : ℕ) : BooleanNetwork (inWidth s w) (NodeCircuit.width s w) :=
  ((old s w).comp (pending s w)).pair (supplied s w)
def nextPending (s w : ℕ) : BooleanNetwork (inWidth s w) ((s+1)*w) :=
  (nodeInput s w).comp (NodeCircuit.next s w)
def emission (s w : ℕ) : BooleanNetwork (inWidth s w) w :=
  (nodeInput s w).comp (NodeCircuit.emitted s w)
def nextOutput (s w : ℕ) : BooleanNetwork (inWidth s w) ((s+1)*w) :=
  wordMux (zeroWord (emission s w)) ((old s w).comp (output s w))
    (stackPush (emission s w) ((old s w).comp (output s w)))
def nextBad (s w : ℕ) : BooleanNetwork (inWidth s w) 1 :=
  ((old s w).comp (bad s w)).bor ((nodeInput s w).comp (NodeCircuit.failed s w))
def step (s w : ℕ) : BooleanNetwork (inWidth s w) (width s w) :=
  ((nextPending s w).pair (nextOutput s w)).pair (nextBad s w)

def pack {s w : ℕ} (xs ys : List (Basis w)) (bad : Bool) : Basis (width s w) :=
  Fin.append (Fin.append (stackEncoding (s+1) w xs) (stackEncoding (s+1) w ys)) (fun _=>bad)

@[simp] lemma pending_pack {s w : ℕ} (xs ys : List (Basis w)) (b : Bool) :
    (pending s w).eval (pack xs ys b)=stackEncoding (s+1) w xs := by
  funext i
  simp [pending,eval_select,pack]
@[simp] lemma output_pack {s w : ℕ} (xs ys : List (Basis w)) (b : Bool) :
    (output s w).eval (pack xs ys b)=stackEncoding (s+1) w ys := by
  funext i
  rw [output,eval_select]
  change Fin.append (Fin.append (stackEncoding (s+1) w xs) (stackEncoding (s+1) w ys))
    (fun _=>b) (Fin.castAdd 1 (Fin.natAdd ((s+1)*w) i))=_
  rw [Fin.append_left,Fin.append_right]
@[simp] lemma bad_pack {s w : ℕ} (xs ys : List (Basis w)) (b : Bool) :
    (bad s w).eval (pack xs ys b)=(fun _=>b) := by
  funext i
  simp [bad,eval_select,pack]
lemma top_pack {s w : ℕ} (xs ys : List (Basis w)) (b : Bool) :
    (top s w).eval (pack xs ys b)=xs.head?.getD (fun _=>false) := by
  rw [top,eval_comp,pending_pack,blockNet_eval,block_stackEncoding]
  cases xs <;> rfl

lemma old_append {s w : ℕ} (x : Basis (width s w)) (d : Basis w) :
    (old s w).eval (Fin.append x d)=x := by
  funext i
  exact Fin.append_left _ _ i
lemma supplied_append {s w : ℕ} (x : Basis (width s w)) (d : Basis w) :
    (supplied s w).eval (Fin.append x d)=d := by
  funext i
  exact Fin.append_right _ _ i
lemma nodeInput_pack {s w : ℕ} (xs ys : List (Basis w)) (b : Bool) (d : Basis w) :
    (nodeInput s w).eval (Fin.append (pack xs ys b) d)=NodeCircuit.pack xs d := by
  rw [nodeInput,eval_pair,eval_comp,old_append,pending_pack,supplied_append]
  rfl

lemma nextBad_pack {s w : ℕ} (xs ys : List (Basis w)) (b : Bool) (d : Basis w)
    (hf : (NodeCircuit.failed s w).eval (NodeCircuit.pack xs d) 0=false) :
    (nextBad s w).eval (Fin.append (pack xs ys b) d)=(fun _=>b) := by
  funext i
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  rw [nextBad,eval_bor,eval_comp,old_append,bad_pack,eval_comp,nodeInput_pack,hf,Bool.or_false]

lemma step_prime {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w) (xs ys : List (Basis w))
    (b : Bool) (hx : xs.length ≤ s) (hp : (bitsValue a).toNat.Prime) :
    (step s w).eval (Fin.append (pack (a::xs) ys b) d)=pack xs (a::ys) b := by
  have ha : 2 ≤ (bitsValue a).toNat := hp.two_le
  have he : (emission s w).eval (Fin.append (pack (a::xs) ys b) d)=a := by
    rw [emission,eval_comp,nodeInput_pack,NodeCircuit.emitted_pack_cons hw,ite_eq_left hp]
  have hz : (zeroWord (emission s w)).eval (Fin.append (pack (a::xs) ys b) d) 0 ≠ true := by
    intro hz
    have hh := (zeroWord_value (emission s w) _).mp hz
    rw [he] at hh
    omega
  have hf : (NodeCircuit.failed s w).eval (NodeCircuit.pack (a::xs) d) 0=false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    exact ((NodeCircuit.failed_pack_cons hw a d xs ha).mp hh).1 hp
  rw [step,eval_pair,eval_pair,nextPending,eval_comp,nodeInput_pack,
    NodeCircuit.next_pack_cons hw _ _ _ hx ha,ite_eq_left hp,nextOutput,wordMux_eval,ite_eq_right hz,
    stackPush_encoding _ _ _ ys (by rw [eval_comp,old_append,output_pack]),he,
    nextBad_pack _ _ _ _ hf]
  rfl

lemma step_split {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w) (xs ys : List (Basis w))
    (b : Bool) (hx : xs.length ≤ s) (ha : 2 ≤ (bitsValue a).toNat) (hp : ¬(bitsValue a).toNat.Prime)
    (hd : ProperDivisor (bitsValue a).toNat (bitsValue d).toNat) :
    (step s w).eval (Fin.append (pack (a::xs) ys b) d)=
      pack (d::(NodeCircuit.quotient s w).eval (NodeCircuit.pack (a::xs) d)::xs) ys b := by
  have he : (emission s w).eval (Fin.append (pack (a::xs) ys b) d)=(fun _=>false) := by
    rw [emission,eval_comp,nodeInput_pack,NodeCircuit.emitted_pack_cons hw,ite_eq_right hp]
  have hz : (zeroWord (emission s w)).eval (Fin.append (pack (a::xs) ys b) d) 0=true := by
    rw [zeroWord_value,he]
    have hh : bitsValue (fun _ : Fin w=>false)=(0 : BitVec w) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [bitsValue_bit _ ⟨i,hi⟩]
      simp
    rw [hh]
    rfl
  have hf : (NodeCircuit.failed s w).eval (NodeCircuit.pack (a::xs) d) 0=false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    exact ((NodeCircuit.failed_pack_cons hw a d xs ha).mp hh).2 hd
  rw [step,eval_pair,eval_pair,nextPending,eval_comp,nodeInput_pack,
    NodeCircuit.next_pack_cons hw _ _ _ hx ha,ite_eq_right hp,ite_eq_left hd,nextOutput,wordMux_eval,ite_eq_left hz,
    eval_comp,old_append,output_pack,nextBad_pack _ _ _ _ hf]
  rfl

end NodeStateCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NodeSplitMachine.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace PhysicalNode

abbrev configWidth (n s : ℕ) := NodeStateCircuit.width s (n+1)
def query (n s : ℕ) : BooleanNetwork (configWidth n s) n :=
  (NodeStateCircuit.top s (n+1)).comp (resizeWord (n+1) n)
def update (n s : ℕ) : BooleanNetwork (configWidth n s+FixedSplit.width n) (configWidth n s) :=
  ((select (Fin.castAdd (FixedSplit.width n))).pair
    ((select (Fin.natAdd (configWidth n s))).comp (FixedSplit.divisorNet n))).comp
      (NodeStateCircuit.step s (n+1))
def machine (n s : ℕ) : SplitMachine n (configWidth n s) := ⟨query n s,update n s⟩
def decoded {n : ℕ} (q : Basis n) (r : FixedSplit.Raw n) : Basis (n+1) :=
  (FixedSplit.divisorNet n).eval (FixedSplit.encoding q r)

lemma query_pack (n s : ℕ) (a : Basis (n+1)) (xs ys : List (Basis (n+1))) (b : Bool) :
    (query n s).eval (NodeStateCircuit.pack (a::xs) ys b)=
      (resizeWord (n+1) n).eval a := by
  rw [query,eval_comp,NodeStateCircuit.top_pack]
  rfl
lemma query_value {n s : ℕ} (a : Basis (n+1)) (xs ys : List (Basis (n+1))) (b : Bool)
    (ha : (bitsValue a).toNat < 2^n) :
    (bitsValue ((query n s).eval (NodeStateCircuit.pack (a::xs) ys b))).toNat=(bitsValue a).toNat := by
  rw [query_pack,resizeWord_value,BitVec.toNat_setWidth,Nat.mod_eq_of_lt ha]
lemma decoded_value {n : ℕ} (hn : 2 ≤ n) (q : Basis n) (r : FixedSplit.Raw n)
    (hq : 2 ≤ (bitsValue q).toNat) :
    (bitsValue (decoded q r)).toNat=FixedSplit.divisor q r :=
  FixedSplit.divisorNet_value hn q r hq

lemma next_eq {n s : ℕ} (x : Basis (configWidth n s)) (r : FixedSplit.Raw n) :
    (machine n s).next x r=(NodeStateCircuit.step s (n+1)).eval
      (Fin.append x (decoded ((query n s).eval x) r)) := by
  rw [SplitMachine.next]
  change (update n s).eval _=_
  rw [update,eval_comp,eval_pair,eval_select,eval_comp,eval_select]
  apply congrArg (NodeStateCircuit.step s (n+1)).eval
  apply congrArg₂ Fin.append
  · funext i
    exact Fin.append_left _ _ i
  · change (FixedSplit.divisorNet n).eval _=(FixedSplit.divisorNet n).eval _
    apply congrArg (FixedSplit.divisorNet n).eval
    funext i
    exact Fin.append_right _ _ i

lemma next_prime {n s : ℕ} (hn : 128 ≤ n) (a : Basis (n+1)) (xs ys : List (Basis (n+1)))
    (b : Bool) (hx : xs.length ≤ s) (hp : (bitsValue a).toNat.Prime) (r : FixedSplit.Raw n) :
    (machine n s).next (NodeStateCircuit.pack (a::xs) ys b) r=
      NodeStateCircuit.pack xs (a::ys) b := by
  rw [next_eq]
  exact NodeStateCircuit.step_prime (by omega) _ _ _ _ _ hx hp

/-- A passed actual split advances the bounded node stack. Its inputs are the
runtime stack top and this very clock tick's retained raw outcome. -/
lemma next_split {n s : ℕ} (hn : 128 ≤ n) (a : Basis (n+1)) (xs ys : List (Basis (n+1)))
    (b : Bool) (hx : xs.length ≤ s) (ha : 2 ≤ (bitsValue a).toNat) (hb : (bitsValue a).toNat < 2^n)
    (hp : ¬(bitsValue a).toNat.Prime) (r : FixedSplit.Raw n)
    (hr : UniversalSplit.passed ((query n s).eval (NodeStateCircuit.pack (a::xs) ys b)) r) :
    let q := (query n s).eval (NodeStateCircuit.pack (a::xs) ys b)
    let d := decoded q r
    (machine n s).next (NodeStateCircuit.pack (a::xs) ys b) r=
      NodeStateCircuit.pack (d::(NodeCircuit.quotient s (n+1)).eval
        (NodeCircuit.pack (a::xs) d)::xs) ys b ∧
      FactorController.ProperDivisor (bitsValue a).toNat (bitsValue d).toNat := by
  dsimp only
  have hq := query_value (s:=s) a xs ys b hb
  have hqm : 2 ≤ (bitsValue ((query n s).eval (NodeStateCircuit.pack (a::xs) ys b))).toNat := by
    rw [hq]
    exact ha
  have he := decoded_value (by omega : 2 ≤ n) ((query n s).eval (NodeStateCircuit.pack (a::xs) ys b)) r hqm
  have hd := UniversalSplit.passed_divisor hn ((query n s).eval (NodeStateCircuit.pack (a::xs) ys b)) hqm
    (by rw [hq];exact hp) r hr
  rw [hq,←he] at hd
  refine ⟨?_,hd⟩
  rw [next_eq]
  exact NodeStateCircuit.step_split (by omega) _ _ _ _ _ hx ha hp hd

end PhysicalNode
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NodeStateNil.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma zeroBasis_value (w : ℕ) : bitsValue (fun _ : Fin w=>false)=(0 : BitVec w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [bitsValue_bit _ ⟨i,hi⟩]
  simp

namespace NodeCircuit
lemma done_nil (s w : ℕ) (d : Basis w) : (isDone s w).eval (pack [] d) 0=true := by
  rw [isDone_pack]
  simp only [List.head?_nil,Option.getD_none,zeroBasis_value]
  rfl
lemma notPrime_nil {s w : ℕ} (hw : 128 ≤ w) (d : Basis w) :
    (isPrime s w).eval (pack [] d) 0≠true := by
  intro h
  rw [isPrime,eval_comp] at h
  have hp := (primeWord_value hw ((top s w).eval (pack [] d))).mp h
  rw [top_pack] at hp
  simp only [List.head?_nil,Option.getD_none,zeroBasis_value] at hp
  exact Nat.not_prime_zero hp
lemma next_nil (s w : ℕ) (d : Basis w) :
    (next s w).eval (pack [] d)=stackEncoding (s+1) w [] := by
  rw [next,wordMux_eval,ite_eq_left (done_nil s w d),pending_pack]
lemma emitted_nil {s w : ℕ} (hw : 128≤w) (d : Basis w) :
    (emitted s w).eval (pack [] d)=(fun _=>false) := by
  rw [emitted,wordMux_eval,ite_eq_right (notPrime_nil hw d)]
  funext i
  simp [wordConstant]
lemma failed_nil (s w : ℕ) (d : Basis w) :
    (failed s w).eval (pack [] d) 0=false := by
  rw [failed,eval_band,eval_band,eval_bnot,done_nil]
  rfl
end NodeCircuit

namespace NodeStateCircuit
lemma step_nil {s w : ℕ} (hw : 128 ≤ w) (d : Basis w) (ys : List (Basis w)) (b : Bool) :
    (step s w).eval (Fin.append (pack [] ys b) d)=pack [] ys b := by
  have he : (emission s w).eval (Fin.append (pack [] ys b) d)=(fun _=>false) := by
    rw [emission,eval_comp,nodeInput_pack,NodeCircuit.emitted_nil hw]
  have hz : (zeroWord (emission s w)).eval (Fin.append (pack [] ys b) d) 0=true := by
    rw [zeroWord_value,he,zeroBasis_value]
    rfl
  rw [step,eval_pair,eval_pair,nextPending,eval_comp,nodeInput_pack,
    NodeCircuit.next_nil,nextOutput,wordMux_eval,ite_eq_left hz,eval_comp,old_append,output_pack,
    nextBad_pack _ _ _ _ (NodeCircuit.failed_nil s w d)]
  rfl
end NodeStateCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NodeProgress.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic FactorController
namespace PhysicalNode

def values {w : ℕ} (xs : List (Basis w)) : List ℕ := xs.map (fun x=>(bitsValue x).toNat)
@[simp] lemma values_nil (w : ℕ) : values ([] : List (Basis w))=[] := rfl
@[simp] lemma values_cons {w : ℕ} (a : Basis w) (xs : List (Basis w)) :
    values (a::xs)=(bitsValue a).toNat::values xs := rfl

lemma length_le_weight (ms : List ℕ) (hm : ∀ m ∈ ms,2 ≤ m) : ms.length ≤ weight ms := by
  induction ms with
  | nil=>simp [weight]
  | cons m ms ih=>
    have hp := splitWeight_pos (hm m (by simp))
    have ht := ih (fun a ha=>hm a (by simp [ha]))
    simp only [List.length_cons,weight,List.map_cons,List.sum_cons] at *
    omega

structure Good (n N fuel : ℕ) (xs ys : List (Basis (n+1))) : Prop where
  bounded : ∀ a ∈ xs, 2 ≤ (bitsValue a).toNat ∧ (bitsValue a).toNat<2^n
  primes : ∀ a ∈ ys, (bitsValue a).toNat.Prime
  product : (values xs).prod*(values ys).prod=N
  clock : weight (values xs) ≤ fuel

lemma Good.length_le {n N f : ℕ} {xs ys : List (Basis (n+1))} (h : Good n N f xs ys) :
    xs.length ≤ f := by
  have hh := length_le_weight (values xs) (by
    intro m hm
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact (h.bounded a ha).1)
  have hl : (values xs).length=xs.length := List.length_map _
  rw [hl] at hh
  exact hh.trans h.clock

lemma next_nil {n s : ℕ} (hn : 128 ≤ n) (ys : List (Basis (n+1))) (b : Bool) (r : FixedSplit.Raw n) :
    (machine n s).next (NodeStateCircuit.pack [] ys b) r=NodeStateCircuit.pack [] ys b := by
  rw [next_eq]
  exact NodeStateCircuit.step_nil (by omega) _ _ _

/-- One literal machine step consumes one unit of the genuine prime-factor
weight whenever pending work is nonempty. Empty work stays empty. -/
theorem next_good {n N s k : ℕ} (hn : 128 ≤ n) (hk : k ≤ s)
    (xs ys : List (Basis (n+1))) (h : Good n N (k+1) xs ys) (r : FixedSplit.Raw n)
    (hr : UniversalSplit.passed ((query n s).eval (NodeStateCircuit.pack xs ys false)) r) :
    ∃ xs' ys', (machine n s).next (NodeStateCircuit.pack xs ys false) r=
      NodeStateCircuit.pack xs' ys' false ∧ Good n N k xs' ys' := by
  cases xs with
  | nil=>
    refine ⟨[],ys,next_nil hn ys false r,⟨h.bounded,h.primes,h.product,?_⟩⟩
    simp [weight]
  | cons a xs=>
    have ha := h.bounded a (by simp)
    have ht : ∀ x ∈ xs,2 ≤ (bitsValue x).toNat ∧ (bitsValue x).toNat<2^n :=
      fun x hx=>h.bounded x (by simp [hx])
    have hcap : xs.length ≤ s := by have hh:=h.length_le; simp only [List.length_cons] at hh;omega
    by_cases hp : (bitsValue a).toNat.Prime
    · refine ⟨xs,a::ys,next_prime hn a xs ys false hcap hp r,⟨ht,?_,?_,?_⟩⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hp
        · exact h.primes z hz
      · have he := h.product
        simp only [values_cons,List.prod_cons] at he ⊢
        calc
          (values xs).prod*((bitsValue a).toNat*(values ys).prod)=
            ((bitsValue a).toNat*(values xs).prod)*(values ys).prod := by ac_rfl
          _=N := he
      · have hw := h.clock
        rw [values_cons,weight_prime _ _ hp] at hw
        omega
    · let q := (query n s).eval (NodeStateCircuit.pack (a::xs) ys false)
      let d := decoded q r
      let b := (NodeCircuit.quotient s (n+1)).eval (NodeCircuit.pack (a::xs) d)
      obtain ⟨he,hd⟩ := next_split hn a xs ys false hcap ha.1 ha.2 hp r hr
      change (machine n s).next (NodeStateCircuit.pack (a::xs) ys false) r=
        NodeStateCircuit.pack (d::b::xs) ys false at he
      change ProperDivisor (bitsValue a).toNat (bitsValue d).toNat at hd
      have hb : (bitsValue b).toNat=(bitsValue a).toNat/(bitsValue d).toNat :=
        NodeCircuit.quotient_pack a d xs
      have hquot := hd.quotient
      refine ⟨d::b::xs,ys,he,⟨?_,h.primes,?_,?_⟩⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨by have hh:=hd.1;omega,hd.2.1.trans ha.2⟩
        · rcases List.mem_cons.mp hz with rfl | hz
          · rw [hb]
            exact ⟨hquot.1,hquot.2.1.trans ha.2⟩
          · exact ht z hz
      · have hh := h.product
        simp only [values_cons,List.prod_cons] at hh ⊢
        rw [hb,←Nat.mul_assoc,hd.quotient.2.2]
        exact hh
      · have hw := h.clock
        rw [values_cons,weight_split hd] at hw
        simpa only [values_cons,hb] using (show weight
          ((bitsValue d).toNat::(bitsValue a).toNat/(bitsValue d).toNat::values xs) ≤ k by omega)

end PhysicalNode
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalMachineMass.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RecordedHistory
namespace SplitMachine
variable {n c : ℕ} (M : SplitMachine n c)

/-- Filtering the actual chronological query at each clock tick. No collection
of answers for unselected/counterfactual moduli occurs in this predicate. -/
noncomputable def passed (x : Basis c) : (t : ℕ)→Trace n t→Prop
  | 0,_=>True
  | t+1,h=>passed x t h.1 ∧ UniversalSplit.passed (M.query.eval (M.config x t h.1)) h.2

lemma state_normalized (x : Basis c) (t : ℕ) :
    ∑ h,Complex.normSq (M.state x t h)=1 := by
  induction t with
  | zero=>simp [state,Trace]
  | succ t ih=>
    change ∑ h,Complex.normSq (appendState (M.state x t)
      (fun h=>FixedSplit.fresh (M.query.eval (M.config x t h))) h)=1
    exact append_normalized _ _ ih (fun h=>FixedSplit.fresh_normalized _)

/-- Exact physical-history probability for a clocked network controller. This
is unconditional in its update network and retains all quantum scratch. -/
theorem passed_mass (hn : 128≤n) (x : Basis c) (t : ℕ) :
    outcomeMass (M.passed x t) (M.state x t)=
      ((Completion.target n:ℝ)^(n^5+1))^t := by
  induction t with
  | zero=>simp [outcomeMass,passed,state,Trace]
  | succ t ih=>
    change outcomeMass (fun h : Trace n t×FixedSplit.Raw n=>M.passed x t h.1 ∧
      UniversalSplit.passed (M.query.eval (M.config x t h.1)) h.2)
      (appendState (M.state x t) (fun h=>FixedSplit.fresh (M.query.eval (M.config x t h))))=_
    rw [append_constant_mass (M.state x t)
      (fun h=>FixedSplit.fresh (M.query.eval (M.config x t h))) (M.passed x t)
      (fun h=>UniversalSplit.passed (M.query.eval (M.config x t h)))
      ((Completion.target n:ℝ)^(n^5+1))
      (fun h _=>UniversalSplit.passed_mass hn (M.query.eval (M.config x t h))),ih]
    exact (pow_succ ((Completion.target n:ℝ)^(n^5+1)) t).symm

/-- The on-support passing event in the retained concrete physical registers.
An efficient retrospective Boolean validator is still needed before using it as
a circuit-controlled phase; this definition does not provide one by fiat. -/
noncomputable def physicalPassed (x : Basis c) (t : ℕ) (z : Basis (M.width t)) : Prop :=
  ∃ h,M.encoded x t h=z ∧ M.passed x t h

lemma physicalPassed_encoded (x : Basis c) (t : ℕ) (h : Trace n t) :
    M.physicalPassed x t (M.encoded x t h) ↔ M.passed x t h := by
  constructor
  · rintro ⟨a,ha,hp⟩
    exact (M.encoded_injective x t ha) ▸ hp
  · exact fun hp=>⟨h,rfl,hp⟩

theorem program_passed_mass (hn : 128≤n) (x : Basis c) (t : ℕ) :
    outcomeMass (M.physicalPassed x t)
      ((programMatrix (M.program t)).mulVec (basisVector (M.initial t x)))=
      ((Completion.target n:ℝ)^(n^5+1))^t := by
  rw [M.program_state,outcomeMass_encode _ (M.encoded_injective x t)]
  have he : M.physicalPassed x t ∘ M.encoded x t=M.passed x t := by
    funext h
    exact propext (M.physicalPassed_encoded x t h)
  rw [he]
  exact M.passed_mass hn x t

end SplitMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalNodeCompletion.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic FactorController AuxiliaryTree OrderTrial
namespace PhysicalNode

lemma config_good {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (t : ℕ) (ht : t ≤ 2*n) (h : SplitMachine.Trace n t)
    (hp : (machine n (2*n)).passed (NodeStateCircuit.pack [natBasis (n+1) N] [] false) t h) :
    ∃ xs ys, (machine n (2*n)).config (NodeStateCircuit.pack [natBasis (n+1) N] [] false) t h=
      NodeStateCircuit.pack xs ys false ∧ Good n N (2*n-t) xs ys := by
  have hbw : N<2^(n+1) := hb.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have ha : (bitsValue (natBasis (n+1) N)).toNat=N := by
    rw [natBasis_value,Nat.mod_eq_of_lt hbw]
  induction t with
  | zero=>
    refine ⟨[natBasis (n+1) N],[],rfl,⟨?_,?_,?_,?_⟩⟩
    · intro a ha'
      have he : a=natBasis (n+1) N := List.mem_singleton.mp ha'
      subst a
      rw [ha]
      exact ⟨hN,hb⟩
    · simp
    · simp only [values_cons,values_nil,List.prod_cons,List.prod_nil,ha,mul_one]
    · have hs := splitWeight_bound (by omega : 0<N) hb
      simp only [values_cons,values_nil,ha,weight,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      omega
  | succ t ih=>
    obtain ⟨xs,ys,he,hg⟩ := ih (by omega) h.1 hp.1
    have hg' : Good n N ((2*n-(t+1))+1) xs ys := by
      convert hg using 1; omega
    have hpass : UniversalSplit.passed ((query n (2*n)).eval (NodeStateCircuit.pack xs ys false)) h.2 := by
      have hh := hp.2
      change UniversalSplit.passed ((query n (2*n)).eval ((machine n (2*n)).config _ t h.1)) h.2 at hh
      rw [he] at hh
      exact hh
    obtain ⟨xs',ys',he',hg'⟩ := next_good hn (by omega : 2*n-(t+1) ≤ 2*n) xs ys hg' h.2 hpass
    refine ⟨xs',ys',?_,hg'⟩
    change (machine n (2*n)).next ((machine n (2*n)).config _ t h.1) h.2=_
    rw [he,he']

/-- Every passing actual history of the literal 2n-clock machine ends in a
complete prime list, without sticky failure. The input and all next queries are
actual measured-word encodings, not an oracle call to mathematical factorization. -/
theorem complete {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (h : SplitMachine.Trace n (2*n))
    (hp : (machine n (2*n)).passed (NodeStateCircuit.pack [natBasis (n+1) N] [] false) (2*n) h) :
    ∃ ys, (machine n (2*n)).config (NodeStateCircuit.pack [natBasis (n+1) N] [] false) (2*n) h=
      NodeStateCircuit.pack [] ys false ∧
      (∀ p ∈ values ys,p.Prime) ∧ (values ys).prod=N ∧ ys.length<n := by
  obtain ⟨xs,ys,he,hg⟩ := config_good hn hN hb (2*n) (le_refl _) h hp
  have hl := hg.length_le
  have hxs : xs=[] := List.length_eq_zero_iff.mp (by omega)
  subst xs
  have hpr : ∀ p ∈ values ys,p.Prime := by
    intro p hp'
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp'
    exact hg.primes a ha
  have hprod : (values ys).prod=N := by simpa only [values_nil,List.prod_nil,one_mul] using hg.product
  have hlen : (values ys).length=splitWeight N := (Nat.primeFactorsList_unique hprod hpr).length_eq
  have hlen' : ys.length<n := by
    have hb' := splitWeight_bound (by omega : 0<N) hb
    rw [values,List.length_map] at hlen
    omega
  exact ⟨ys,he,hpr,hprod,hlen'⟩

end PhysicalNode
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/SortedWords.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
namespace SortedWords

def LEWord {w : ℕ} (a b : Basis w) : Prop := PaddedOrder (bitsValue a).toNat (bitsValue b).toNat
instance {w : ℕ} (a b : Basis w) : Decidable (LEWord a b) :=
  inferInstanceAs (Decidable (_=0 ∨ (_≠0 ∧ _ ≤ _)))

lemma le_total {w : ℕ} (a b : Basis w) : LEWord a b ∨ LEWord b a := by
  dsimp only [LEWord,PaddedOrder]
  omega
lemma le_trans {w : ℕ} {a b c : Basis w} (h : LEWord a b) (h' : LEWord b c) : LEWord a c := by
  dsimp only [LEWord,PaddedOrder] at *
  omega

def insert {w : ℕ} (a : Basis w) : List (Basis w)→List (Basis w)
  | []=>[a]
  | b::bs=>if LEWord a b then a::insert b bs else b::insert a bs

def sort {w : ℕ} : List (Basis w)→List (Basis w)
  | []=>[]
  | a::as=>insert a (sort as)

lemma insert_perm {w : ℕ} (a : Basis w) (bs : List (Basis w)) : (insert a bs).Perm (a::bs) := by
  induction bs generalizing a with
  | nil=>rfl
  | cons b bs ih=>
    rw [insert]
    split_ifs
    · exact (ih b).cons a
    · exact ((ih a).cons b).trans (List.Perm.swap b a bs).symm
lemma insert_length {w : ℕ} (a : Basis w) (bs : List (Basis w)) : (insert a bs).length=bs.length+1 :=
  (insert_perm a bs).length_eq
lemma sort_perm {w : ℕ} (bs : List (Basis w)) : (sort bs).Perm bs := by
  induction bs with
  | nil=>rfl
  | cons b bs ih=>exact (insert_perm b (sort bs)).trans (ih.cons b)
lemma sort_length {w : ℕ} (bs : List (Basis w)) : (sort bs).length=bs.length := (sort_perm bs).length_eq

lemma insert_sorted {w : ℕ} (a : Basis w) (bs : List (Basis w)) (hs : bs.Pairwise LEWord) :
    (insert a bs).Pairwise LEWord := by
  induction bs generalizing a with
  | nil=>simp [insert]
  | cons b bs ih=>
    obtain ⟨hfirst,htail⟩ := List.pairwise_cons.mp hs
    rw [insert]
    split_ifs with hab
    · rw [List.pairwise_cons]
      refine ⟨?_,ih b htail⟩
      intro c hc
      rcases List.mem_cons.mp ((insert_perm b bs).mem_iff.mp hc) with rfl | hc
      · exact hab
      · exact le_trans hab (hfirst c hc)
    · rw [List.pairwise_cons]
      refine ⟨?_,ih a htail⟩
      intro c hc
      rcases List.mem_cons.mp ((insert_perm a bs).mem_iff.mp hc) with rfl | hc
      · exact (le_total _ _).resolve_left hab
      · exact hfirst c hc
lemma sort_sorted {w : ℕ} (bs : List (Basis w)) : (sort bs).Pairwise LEWord := by
  induction bs with
  | nil=>simp [sort]
  | cons b bs ih=>exact insert_sorted b (sort bs) ih

end SortedWords
end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/SortedEncoding.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic.SortedWords

def numbers {w : ℕ} (xs : List (Basis w)) : List ℕ := xs.map (fun a=>(bitsValue a).toNat)

lemma zero_number (w : ℕ) : (bitsValue (fun _ : Fin w=>false)).toNat=0 := by
  have hz : bitsValue (fun _ : Fin w=>false)=(0 : BitVec w) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [bitsValue_bit _ ⟨i,hi⟩]
    simp
  rw [hz]
  rfl
lemma numbers_pad {w : ℕ} (xs : List (Basis w)) (k : ℕ) :
    numbers (xs++List.replicate k (fun _=>false))=numbers xs++List.replicate k 0 := by
  simp only [numbers,List.map_append,List.map_replicate,zero_number]

/-- Literal compare-exchange sorting gives the exact source sorted padded
encoding, not just an arbitrary prime multiset. -/
theorem sort_correct {w N r : ℕ} (xs : List (Basis w))
    (hp : ∀ p∈numbers xs,p.Prime) (hprod : (numbers xs).prod=N) (hlen : xs.length ≤ r) :
    CorrectEncoding N r (numbers (sort (xs++List.replicate (r-xs.length) (fun _=>false)))) := by
  let zs := xs++List.replicate (r-xs.length) (fun _ : Fin w=>false)
  have hlen' : (numbers (sort zs)).length=r := by
    simp only [numbers,List.length_map,sort_length,zs,List.length_append,List.length_replicate]
    omega
  apply (factorListValid_iff hlen').mp
  have hperm : (numbers (sort zs)).Perm (numbers zs) := (sort_perm zs).map _
  refine ⟨?_,?_,?_⟩
  · intro p hpm
    have hz := hperm.mem_iff.mp hpm
    simp only [zs,numbers_pad] at hz
    rcases List.mem_append.mp hz with hx | hx
    · exact Or.inr (hp p hx)
    · exact Or.inl (List.mem_replicate.mp hx).2
  · exact List.pairwise_map.mpr (sort_sorted zs)
  · calc
      unpadProduct (numbers (sort zs))=unpadProduct (numbers zs) := (hperm.map _).prod_eq
      _ = N := by
        simp only [zs,numbers_pad]
        rw [unpadProduct_append _ _ (fun p hp'=> (hp p hp').ne_zero),hprod]

end ExactQuantumFactoring.BitArithmetic.SortedWords


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/SortingCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
namespace SortedWords

def layout (w : ℕ) : (r : ℕ)→List (Basis w)→Basis (tensorWidth w r)
  | 0,_=>Fin.elim0
  | r+1,xs=>Fin.append (xs.head?.getD (fun _=>false)) (layout w r xs.tail)

def headNet (w r : ℕ) : BooleanNetwork (tensorWidth w (r+1)) w := select (Fin.castAdd (tensorWidth w r))
def tailNet (w r : ℕ) : BooleanNetwork (tensorWidth w (r+1)) (tensorWidth w r) := select (Fin.natAdd w)
lemma headNet_eval (w r : ℕ) (a : Basis w) (x : Basis (tensorWidth w r)) :
    (headNet w r).eval (Fin.append a x)=a := by
  funext i
  exact Fin.append_left _ _ _
lemma tailNet_eval (w r : ℕ) (a : Basis w) (x : Basis (tensorWidth w r)) :
    (tailNet w r).eval (Fin.append a x)=x := by
  funext i
  exact Fin.append_right _ _ _

/-- A recursive subnetwork is used ONCE, with its prefix wire retained. -/
def keepHead {w r : ℕ} (c : BooleanNetwork (tensorWidth w r) (tensorWidth w r)) :
    BooleanNetwork (tensorWidth w (r+1)) (tensorWidth w (r+1)) :=
  (headNet w r).pair ((tailNet w r).comp c)
lemma keepHead_eval {w r : ℕ} (c : BooleanNetwork (tensorWidth w r) (tensorWidth w r))
    (a : Basis w) (x : Basis (tensorWidth w r)) :
    (keepHead c).eval (Fin.append a x)=Fin.append a (c.eval x) := by
  rw [keepHead,eval_pair,eval_comp,headNet_eval,tailNet_eval]
lemma keepHead_count {w r : ℕ} (c : BooleanNetwork (tensorWidth w r) (tensorWidth w r)) :
    (keepHead c).net.count=c.net.count := by
  simp only [keepHead,count_pair,count_comp,headNet,tailNet,count_select,zero_add]

def compareStep (w r : ℕ) : BooleanNetwork (tensorWidth w (r+2)) (tensorWidth w (r+2)) :=
  let a := headNet w (r+1)
  let b := (tailNet w (r+1)).comp (headNet w r)
  let rest := (tailNet w (r+1)).comp (tailNet w r)
  (wordMux (paddedPair a b) a b).pair ((wordMux (paddedPair a b) b a).pair rest)

lemma compareStep_eval (w r : ℕ) (a b : Basis w) (x : Basis (tensorWidth w r)) :
    (compareStep w r).eval (Fin.append a (Fin.append b x))=
      if LEWord a b then Fin.append a (Fin.append b x) else Fin.append b (Fin.append a x) := by
  have hc : (paddedPair (headNet w (r+1)) ((tailNet w (r+1)).comp (headNet w r))).eval
      (Fin.append a (Fin.append b x)) 0=true ↔ LEWord a b := by
    rw [paddedPair_value,headNet_eval,eval_comp,tailNet_eval,headNet_eval]
    rfl
  simp only [compareStep,eval_pair,wordMux_eval,eval_comp,headNet_eval,tailNet_eval]
  by_cases hab : LEWord a b
  · have ht := hc.mpr hab
    simp only [ite_eq_left ht,ite_eq_left hab]
  · have ht : ¬(paddedPair (headNet w (r+1)) ((tailNet w (r+1)).comp (headNet w r))).eval
        (Fin.append a (Fin.append b x)) 0=true := fun h=>hab (hc.mp h)
    simp only [ite_eq_right ht,ite_eq_right hab]

lemma compareStep_count (w r : ℕ) : (compareStep w r).net.count ≤ 498*w+114 := by
  have hp := paddedPair_count (headNet w (r+1)) ((tailNet w (r+1)).comp (headNet w r))
  simp only [headNet,tailNet,count_comp,count_select,mul_zero,zero_add] at hp
  simp only [compareStep,count_pair,wordMux_count,headNet,tailNet,count_comp,count_select]
  omega

def insertNet (w : ℕ) : (r : ℕ)→BooleanNetwork (tensorWidth w (r+1)) (tensorWidth w (r+1))
  | 0=>select id
  | r+1=>(compareStep w r).comp (keepHead (insertNet w r))
def sortNet (w : ℕ) : (r : ℕ)→BooleanNetwork (tensorWidth w r) (tensorWidth w r)
  | 0=>select id
  | r+1=>(keepHead (sortNet w r)).comp (insertNet w r)

lemma insertNet_eval (w r : ℕ) (a : Basis w) (xs : List (Basis w)) (hx : xs.length=r) :
    (insertNet w r).eval (layout w (r+1) (a::xs))=layout w (r+1) (insert a xs) := by
  induction r generalizing a xs with
  | zero=>have he : xs=[] := List.length_eq_zero_iff.mp hx;subst xs;rfl
  | succ r ih=>
    cases xs with
    | nil=>simp at hx
    | cons b bs=>
      have hb : bs.length=r := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hx
      change (insertNet w (r+1)).eval (Fin.append a (Fin.append b (layout w r bs)))=_
      rw [insertNet,eval_comp,compareStep_eval,insert]
      split_ifs with hab
      · rw [keepHead_eval]
        change Fin.append a ((insertNet w r).eval (layout w (r+1) (b::bs)))=_
        rw [ih b bs hb]
        rfl
      · rw [keepHead_eval]
        change Fin.append b ((insertNet w r).eval (layout w (r+1) (a::bs)))=_
        rw [ih a bs hb]
        rfl
lemma sortNet_eval (w r : ℕ) (xs : List (Basis w)) (hx : xs.length=r) :
    (sortNet w r).eval (layout w r xs)=layout w r (sort xs) := by
  induction r generalizing xs with
  | zero=>have he : xs=[] := List.length_eq_zero_iff.mp hx;subst xs;rfl
  | succ r ih=>
    cases xs with
    | nil=>simp at hx
    | cons a as=>
      have ha : as.length=r := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hx
      change (sortNet w (r+1)).eval (Fin.append a (layout w r as))=_
      rw [sortNet,eval_comp,keepHead_eval,ih as ha]
      change (insertNet w r).eval (layout w (r+1) (a::sort as))=_
      rw [insertNet_eval w r a (sort as) ((sort_length as).trans ha)]
      rfl
lemma insertNet_count (w r : ℕ) : (insertNet w r).net.count ≤ r*(498*w+114) := by
  induction r with
  | zero=>simp [insertNet,count_select]
  | succ r ih=>
    have hc := compareStep_count w r
    rw [insertNet,count_comp,keepHead_count,Nat.succ_mul]
    omega
/-- Quadratic number of word comparisons, each a polynomial Boolean network.
No expanded sorting expression duplicates its recursively generated circuits. -/
theorem sortNet_count (w r : ℕ) : (sortNet w r).net.count ≤ r*r*(498*w+114) := by
  induction r with
  | zero=>simp [sortNet,count_select]
  | succ r ih=>
    have hc := insertNet_count w r
    rw [sortNet,count_comp,keepHead_count]
    calc
      _ ≤ r*r*(498*w+114)+r*(498*w+114) := Nat.add_le_add ih hc
      _ ≤ (r+1)*(r+1)*(498*w+114) := by nlinarith

end SortedWords
end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TensorList.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic.SortedWords

lemma layout_ofFn (w r : ℕ) (f : Fin r→Basis w) :
    layout w r (List.ofFn f)=tensorLayout w r f := by
  induction r with
  | zero=>rfl
  | succ r ih=>
    rw [List.ofFn_succ,layout,tensorLayout_succ]
    simp only [List.head?_cons,Option.getD_some,List.tail_cons]
    rw [ih]
    rfl

lemma ofFn_getD_pad {α : Type} (xs : List α) (d : α) (r : ℕ) (hlen : xs.length ≤ r) :
    List.ofFn (fun i : Fin r=>xs[i.val]?.getD d)=xs++List.replicate (r-xs.length) d := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_append,List.length_replicate]
    omega
  · intro i hi hj
    rw [List.getElem_ofFn]
    by_cases hx : i<xs.length
    · rw [List.getElem?_eq_getElem hx,Option.getD_some,List.getElem_append_left hx]
    · have hle : xs.length ≤ i := by omega
      rw [List.getElem?_eq_none hle,Option.getD_none,List.getElem_append_right hle,List.getElem_replicate]

lemma ofFn_map_getD_pad {α β : Type} (xs : List α) (d : α) (r : ℕ) (hlen : xs.length ≤ r) (f : α→β) :
    List.ofFn (fun i : Fin r=>f (xs[i.val]?.getD d))=
      xs.map f++List.replicate (r-xs.length) (f d) := by
  have h := congrArg (List.map f) (ofFn_getD_pad xs d r hlen)
  simpa only [List.map_ofFn,List.map_append,List.map_replicate,Function.comp_def] using h

end ExactQuantumFactoring.BitArithmetic.SortedWords


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalNodeOutput.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalNode

def resultField (n : ℕ) (i : Fin n) : BooleanNetwork (configWidth n (2*n)) n :=
  ((NodeStateCircuit.output (2*n) (n+1)).comp
    (blockNet (2*n+1) (n+1) ⟨i.val,by omega⟩)).comp (resizeWord (n+1) n)

def sortedOutput (n : ℕ) : BooleanNetwork (configWidth n (2*n)) (tensorWidth n n) :=
  (tensorNetwork (resultField n)).comp (SortedWords.sortNet n n)

def shrink (n : ℕ) (a : Basis (n+1)) : Basis n := (resizeWord (n+1) n).eval a

lemma resultField_pack (n : ℕ) (xs ys : List (Basis (n+1))) (b : Bool) (i : Fin n) :
    (resultField n i).eval (NodeStateCircuit.pack xs ys b)=
      shrink n (ys[i.val]?.getD (fun _=>false)) := by
  rw [resultField,eval_comp,eval_comp,NodeStateCircuit.output_pack,blockNet_eval,block_stackEncoding]
  rfl
lemma shrink_zero (n : ℕ) : shrink n (fun _=>false)=(fun _=>false) := by
  funext i
  simp only [shrink,resizeWord,eval_vector]
  rw [dite_eq_left (by omega)]
  rfl

lemma sortedOutput_pack (n : ℕ) (xs ys : List (Basis (n+1))) (b : Bool) (hlen : ys.length ≤ n) :
    (sortedOutput n).eval (NodeStateCircuit.pack xs ys b)=SortedWords.layout n n
      (SortedWords.sort (ys.map (shrink n)++List.replicate (n-ys.length) (fun _=>false))) := by
  rw [sortedOutput,eval_comp,tensorNetwork_eval]
  simp_rw [resultField_pack]
  rw [←SortedWords.layout_ofFn]
  rw [SortedWords.sortNet_eval _ _ _ List.length_ofFn,
    SortedWords.ofFn_map_getD_pad ys (fun _=>false) n hlen,shrink_zero]

lemma shrink_values {n : ℕ} (ys : List (Basis (n+1))) (hb : ∀ a∈ys,(bitsValue a).toNat<2^n) :
    SortedWords.numbers (ys.map (shrink n))=values ys := by
  simp only [SortedWords.numbers,values,List.map_map]
  apply List.map_congr_left
  intro a ha
  simp only [Function.comp_apply,shrink,resizeWord_value,BitVec.toNat_setWidth,Nat.mod_eq_of_lt (hb a ha)]

/-- The actual retained node configuration admits an explicit polynomial
Boolean sorting/readout network. Its output is the LITERAL main-theorem
encoding, with exactly n fields, zero padding and multiplicities. -/
theorem complete_output {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (h : SplitMachine.Trace n (2*n))
    (hp : (machine n (2*n)).passed (NodeStateCircuit.pack [natBasis (n+1) N] [] false) (2*n) h) :
    ∃ zs : List (Basis n), zs.length=n ∧ CorrectEncoding N n (SortedWords.numbers zs) ∧
      (sortedOutput n).eval
        ((machine n (2*n)).config (NodeStateCircuit.pack [natBasis (n+1) N] [] false) (2*n) h)=
          SortedWords.layout n n zs := by
  obtain ⟨ys,he,hpr,hprod,hlen⟩ := complete hn hN hb h hp
  have hyb : ∀ a∈ys,(bitsValue a).toNat<2^n := by
    intro a ha
    have hm : (bitsValue a).toNat∈values ys := List.mem_map.mpr ⟨a,ha,rfl⟩
    have hd : (bitsValue a).toNat∣N := by rw [←hprod];exact List.dvd_prod hm
    exact (Nat.le_of_dvd (by omega) hd).trans_lt hb
  have hv := shrink_values ys hyb
  refine ⟨SortedWords.sort (ys.map (shrink n)++List.replicate (n-ys.length) (fun _=>false)),?_,?_,?_⟩
  · simp only [SortedWords.sort_length,List.length_append,List.length_map,List.length_replicate]
    omega
  · have hc := SortedWords.sort_correct (N:=N) (r:=n) (ys.map (shrink n)) (by rw [hv];exact hpr)
      (by rw [hv];exact hprod) (by simp only [List.length_map];omega : (ys.map (shrink n)).length ≤ n)
    simpa only [List.length_map] using hc
  · rw [he,sortedOutput_pack _ _ _ _ hlen.le]

end PhysicalNode
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/MachineInitialization.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace SplitMachine
variable {n c : ℕ} (M : SplitMachine n c)

/-- Literal clean initialization: retain the runtime controller word and create
only zero history/output/scratch fields. No query result is precomputed. -/
def initialNet : (t : ℕ) → BooleanNetwork c (M.width t)
  | 0 => select id
  | t+1 => packNet M.updateWork
      (packNet M.initWork (initialNet t) (Completion.zeros c (FixedSplit.width n)))
      (Completion.zeros c c)

lemma initialNet_eval (t : ℕ) (x : Basis c) :
    (M.initialNet t).eval x=M.initial t x := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    rw [initialNet,packNet_eval,packNet_eval,Completion.zeros_eval,Completion.zeros_eval,ih]
    rfl

lemma initialNet_count (t : ℕ) : (M.initialNet t).net.count=
    t*(FixedSplit.width n+M.initWork+c+M.updateWork) := by
  induction t with
  | zero=>simp [initialNet, count_select]
  | succ t ih=>
    simp only [initialNet,packNet_count,Completion.zeros_count,ih]
    ring

/-- A whole fixed-period machine can itself be launched coherently from a
Boolean-computed runtime controller state, retaining earlier history exactly. -/
theorem launch_on_history {α : Type*} [Fintype α] {p r : ℕ}
    (e : α→Basis p) (ψ : α→ℂ) (v : BooleanNetwork p c) (t : ℕ)
    (hc : (v.comp (M.initialNet t)).net.count ≤ r) :
    (programMatrix (preparedOracle (v.comp (M.initialNet t)) hc (M.program t))).mulVec
      (encodeState (fun a=>packed r (e a) (fun _=>false)) ψ)=
      encodeState (fun ar : α×Trace n t => packed r (e ar.1)
        (M.encoded (v.eval (e ar.1)) t ar.2))
        (RecordedHistory.appendState ψ (fun a=>M.state (v.eval (e a)) t)) := by
  apply preparedOracle_encode_dependent e (fun a=>M.encoded (v.eval (e a)) t) ψ
    (fun a=>M.state (v.eval (e a)) t) (v.comp (M.initialNet t)) hc (M.program t)
  intro a
  rw [eval_comp,M.initialNet_eval,M.program_state]

end SplitMachine
end ExactQuantumFactoring


end

end OAI


