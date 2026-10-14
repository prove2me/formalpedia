-- Prove2me | Definitions.Def_OAI_QuantumFactoring_Part17
-- name    : OAI_QuantumFactoring_Part17
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T08:06:50.393422+00:00
-- url     : https://prove2.me/theorems/1dc32705-cd57-42f2-abdc-41559f0f3fe3
-- title:
--   Exact quantum factoring, part 17 of 38 (port of OpenAI's formalization)
-- statement:
--   Part 17 of 38 of a port of OpenAI's Lean formalization of the manuscript *Exact quantum factoring over a fixed finite gate set* (OpenAI, September 25, 2026). This part contains the modules `PhysicalNodeLaunch`, `PhysicalNodeKernel`, `ChildQueue`, `ChildQueueCorrect`, `PhysicalTreeQueue`, `PhysicalTreeMachine`, `PhysicalTreeMass`, `AuxiliaryData`, `PrimeRecords`, `LoggedExecution`, `ControllerQueries`, `AuxiliaryProducer`, `TraceBounds`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/QuantumFactoring`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `ExactQuantumFactoring`, which is identical to upstream `Basic.lean`.
--
--   The development is split into 38 parts only so that each compiles within the platform's time limit. Together the parts supply the circuit family `PhysicalTree.finalCircuit` and its specification, used to prove `OAI.ExactQuantumFactoring.zero_amplitude_core`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/QuantumFactoring: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalNodeLaunch.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalNodeKernel.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ChildQueue.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ChildQueueCorrect.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalTreeQueue.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalTreeMachine.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalTreeMass.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/AuxiliaryData.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PrimeRecords.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/LoggedExecution.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ControllerQueries.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/AuxiliaryProducer.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/TraceBounds.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf

/-
Exact quantum factoring development (port of OpenAI's formalization), part 17 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: PhysicalNodeLaunch.lean, PhysicalNodeKernel.lean, ChildQueue.lean, ChildQueueCorrect.lean, PhysicalTreeQueue.lean, PhysicalTreeMachine.lean, PhysicalTreeMass.lean, AuxiliaryData.lean, PrimeRecords.lean, LoggedExecution.lean, ControllerQueries.lean, AuxiliaryProducer.lean, TraceBounds.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part16

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalNodeLaunch.lean =====
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

/-- The node's initial pending stack contains only the runtime modulus, enlarged
by one bit. Emission and error registers are zero. No factor data is supplied. -/
def startNet (n : ℕ) : BooleanNetwork n (configWidth n (2*n)) :=
  ((stackPush (resizeWord n (n+1))
      (Completion.zeros n ((2*n+1)*(n+1)))).pair
    (Completion.zeros n ((2*n+1)*(n+1)))).pair (constant false)

lemma startNet_eval (n : ℕ) (a : Basis n) :
    (startNet n).eval a=NodeStateCircuit.pack [natBasis (n+1) (bitsValue a).toNat] [] false := by
  have hr : (resizeWord n (n+1)).eval a=natBasis (n+1) (bitsValue a).toNat := by
    apply (bitsEquiv (n+1)).injective
    apply BitVec.eq_of_toNat_eq
    change (bitsValue ((resizeWord n (n+1)).eval a)).toNat=
      (bitsValue (natBasis (n+1) (bitsValue a).toNat)).toNat
    rw [resizeWord_value,BitVec.toNat_setWidth,natBasis_value]
  have hz : (Completion.zeros n ((2*n+1)*(n+1))).eval a=stackEncoding (2*n+1) (n+1) [] := by
    rw [Completion.zeros_eval]
    rfl
  rw [startNet,eval_pair,eval_pair,stackPush_encoding _ _ _ [] hz,hr,hz]
  apply congrArg (Fin.append _)
  funext i
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  exact eval_constant false a 0

abbrev runWidth (n : ℕ) := (machine n (2*n)).width (2*n)
def runInitial (n : ℕ) : BooleanNetwork n (runWidth n) :=
  (startNet n).comp ((machine n (2*n)).initialNet (2*n))

lemma runInitial_eval (n : ℕ) (a : Basis n) :
    (runInitial n).eval a=(machine n (2*n)).initial (2*n)
      (NodeStateCircuit.pack [natBasis (n+1) (bitsValue a).toNat] [] false) := by
  rw [runInitial,eval_comp,SplitMachine.initialNet_eval,startNet_eval]

/-- Coherent launch of a complete node computation, including all literal fresh
split trials and the deterministic bounded-stack controller. Earlier entangled
histories are retained; this is not a truth-table preparation. -/
theorem launch {n p r : ℕ} {α : Type*} [Fintype α] (e : α→Basis p) (ψ : α→ℂ)
    (query : BooleanNetwork p n) (hc : (query.comp (runInitial n)).net.count≤r) :
    (programMatrix (preparedOracle (query.comp (runInitial n)) hc
      ((machine n (2*n)).program (2*n)))).mulVec
      (encodeState (fun a=>packed r (e a) (fun _=>false)) ψ)=
    encodeState (fun ar : α×SplitMachine.Trace n (2*n)=>packed r (e ar.1)
      ((machine n (2*n)).encoded ((startNet n).eval (query.eval (e ar.1))) (2*n) ar.2))
      (RecordedHistory.appendState ψ (fun a=>(machine n (2*n)).state
        ((startNet n).eval (query.eval (e a))) (2*n))) := by
  apply preparedOracle_encode_dependent e
    (fun a=>(machine n (2*n)).encoded ((startNet n).eval (query.eval (e a))) (2*n)) ψ
    (fun a=>(machine n (2*n)).state ((startNet n).eval (query.eval (e a))) (2*n))
    (query.comp (runInitial n)) hc ((machine n (2*n)).program (2*n))
  intro a
  rw [eval_comp,runInitial,eval_comp,SplitMachine.initialNet_eval,SplitMachine.program_state]

end PhysicalNode
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalNodeKernel.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace NodeKernel
abbrev width (n : ℕ) := PhysicalNode.runWidth n
abbrev Raw (n : ℕ) := SplitMachine.Trace n (2*n)
def initialNet (n : ℕ) : BooleanNetwork n (width n) := PhysicalNode.runInitial n
def start {n : ℕ} (q : Basis n) := (PhysicalNode.startNet n).eval q
def zero {n : ℕ} (q : Basis n) : Basis (width n) :=
  (PhysicalNode.machine n (2*n)).initial (2*n) (start q)
def encoding {n : ℕ} (q : Basis n) (r : Raw n) : Basis (width n) :=
  (PhysicalNode.machine n (2*n)).encoded (start q) (2*n) r
noncomputable def fresh {n : ℕ} (q : Basis n) (r : Raw n) : ℂ :=
  (PhysicalNode.machine n (2*n)).state (start q) (2*n) r
def program (n : ℕ) : List (Instruction (width n)) :=
  (PhysicalNode.machine n (2*n)).program (2*n)
noncomputable def passed {n : ℕ} (q : Basis n) (r : Raw n) : Prop :=
  (PhysicalNode.machine n (2*n)).passed (start q) (2*n) r
lemma initialNet_eval {n : ℕ} (q : Basis n) : (initialNet n).eval q=zero q := by
  rw [initialNet,PhysicalNode.runInitial,eval_comp,SplitMachine.initialNet_eval]
  rfl
lemma program_state {n : ℕ} (q : Basis n) :
    (programMatrix (program n)).mulVec (basisVector (zero q))=encodeState (encoding q) (fresh q) :=
  (PhysicalNode.machine n (2*n)).program_state (start q) (2*n)
lemma encoding_injective {n : ℕ} (q : Basis n) : Function.Injective (encoding q) :=
  (PhysicalNode.machine n (2*n)).encoded_injective (start q) (2*n)
lemma fresh_normalized {n : ℕ} (q : Basis n) : ∑ r,Complex.normSq (fresh q r)=1 :=
  (PhysicalNode.machine n (2*n)).state_normalized (start q) (2*n)
lemma passed_mass {n : ℕ} (hn : 128 ≤ n) (q : Basis n) :
    Exactness.outcomeMass (passed q) (fresh q)=
      ((Completion.target n:ℝ)^(n^5+1))^(2*n) :=
  (PhysicalNode.machine n (2*n)).passed_mass hn (start q) (2*n)
end NodeKernel
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ChildQueue.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
namespace ChildQueue

def predBits {w : ℕ} (a : Basis w) : Basis w :=
  (sub w).eval (Fin.append a (fun i => (BitVec.ofNat w 1).getLsbD i.val))

/-- Children from the distinct prime fields, ignoring zero padding and 2.
Repeated labels in DIFFERENT node records are not identified. -/
def kids {w : ℕ} : List (Basis w) → List (Basis w)
  | [] => []
  | a::as => if 2<(bitsValue a).toNat ∧ a∉as then predBits a::kids as else kids as

def wordMember {k w : ℕ} (a : BooleanNetwork k w) (as : List (BooleanNetwork k w)) :
    BooleanNetwork k 1 := any (as.map (fun b => (a.pair b).comp (wordEq w)))

lemma wordMember_eval {k w : ℕ} (a : BooleanNetwork k w) (as : List (BooleanNetwork k w)) (x : Basis k) :
    (wordMember a as).eval x 0=true ↔ a.eval x∈as.map (fun b=>b.eval x) := by
  rw [wordMember,any_eval]
  constructor
  · rintro ⟨c,hc,ht⟩
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
    rw [eval_comp,eval_pair,wordEq_eval,decide_eq_true_eq] at ht
    exact List.mem_map.mpr ⟨b,hb,((bitsEquiv w).injective ht).symm⟩
  · rintro hm
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hm
    refine ⟨(a.pair b).comp (wordEq w),List.mem_map.mpr ⟨b,hb,rfl⟩,?_⟩
    rw [eval_comp,eval_pair,wordEq_eval,decide_eq_true_eq,he]


def source (k s w : ℕ) : BooleanNetwork (k+s*w) k := select (Fin.castAdd (s*w))
def queue (k s w : ℕ) : BooleanNetwork (k+s*w) (s*w) := select (Fin.natAdd k)
def liftWord {k w : ℕ} (s : ℕ) (a : BooleanNetwork k w) := (source k s w).comp a

def active {k w : ℕ} (a : BooleanNetwork k w) (as : List (BooleanNetwork k w)) : BooleanNetwork k 1 :=
  (wordLt (wordConstant (BitVec.ofNat w 2)) a).band (wordMember a as).bnot

def pushOne {k w : ℕ} (s : ℕ) (a : BooleanNetwork k w) (as : List (BooleanNetwork k w)) :
    BooleanNetwork (k+s*w) (k+s*w) :=
  (source k s w).pair
    (wordMux ((source k s w).comp (active a as))
      (stackPush (((liftWord s a).pair (wordConstant (BitVec.ofNat w 1))).comp (sub w)) (queue k s w))
      (queue k s w))

/-- Tail before head: the recursive network occurs just ONCE in the syntax.
All original factor fields remain read-only while the bounded queue is updated. -/
def pushAll {k w : ℕ} (s : ℕ) : List (BooleanNetwork k w) → BooleanNetwork (k+s*w) (k+s*w)
  | [] => select id
  | a::as => (pushAll s as).comp (pushOne s a as)

lemma source_eval (k s w : ℕ) (x : Basis k) (y : Basis (s*w)) :
    (source k s w).eval (Fin.append x y)=x := by
  funext i
  exact Fin.append_left _ _ _
lemma queue_eval (k s w : ℕ) (x : Basis k) (y : Basis (s*w)) :
    (queue k s w).eval (Fin.append x y)=y := by
  funext i
  exact Fin.append_right _ _ _

lemma active_eval {k w : ℕ} (hw : 2 ≤ w) (a : BooleanNetwork k w)
    (as : List (BooleanNetwork k w)) (x : Basis k) :
    (active a as).eval x 0=true ↔ 2<(bitsValue (a.eval x)).toNat ∧ a.eval x∉as.map (fun b=>b.eval x) := by
  have hb : 2<2^w := (by norm_num : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) hw)
  simp only [active,eval_band,Bool.and_eq_true,eval_bnot,Bool.not_eq_true',wordLt_eval,
    wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb,decide_eq_true_eq]
  have hm := wordMember_eval a as x
  cases hh : (wordMember a as).eval x 0 <;> simp_all

lemma pushOne_eval {k w : ℕ} (hw : 2 ≤ w) (s : ℕ) (a : BooleanNetwork k w)
    (as : List (BooleanNetwork k w)) (x : Basis k) (ys : List (Basis w)) :
    (pushOne s a as).eval (Fin.append x (stackEncoding s w ys))=
      Fin.append x (stackEncoding s w
        (if 2<(bitsValue (a.eval x)).toNat ∧ a.eval x∉as.map (fun b=>b.eval x)
          then predBits (a.eval x)::ys else ys)) := by
  have hv : ((((liftWord s a).pair (wordConstant (BitVec.ofNat w 1))).comp (sub w)).eval
      (Fin.append x (stackEncoding s w ys)))=predBits (a.eval x) := by
    rw [eval_comp,eval_pair,liftWord,eval_comp,source_eval]
    unfold predBits
    congr 2
    funext i
    simp [wordConstant,eval_vector,eval_constant]
  have hs := stackPush_encoding
    (((liftWord s a).pair (wordConstant (BitVec.ofNat w 1))).comp (sub w))
    (queue k s w) (Fin.append x (stackEncoding s w ys)) ys (queue_eval k s w x _)
  rw [hv] at hs
  rw [pushOne,eval_pair,source_eval,wordMux_eval,eval_comp,source_eval,hs,queue_eval]
  by_cases hc : 2<(bitsValue (a.eval x)).toNat ∧ a.eval x∉as.map (fun b=>b.eval x)
  · rw [ite_eq_left ((active_eval hw a as x).mpr hc),ite_eq_left hc]
  · rw [ite_eq_right (fun h=>hc ((active_eval hw a as x).mp h)),ite_eq_right hc]

lemma pushAll_eval {k w : ℕ} (hw : 2 ≤ w) (s : ℕ) (as : List (BooleanNetwork k w))
    (x : Basis k) (ys : List (Basis w)) :
    (pushAll s as).eval (Fin.append x (stackEncoding s w ys))=
      Fin.append x (stackEncoding s w (kids (as.map (fun a=>a.eval x))++ys)) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [pushAll,eval_comp,ih,pushOne_eval hw,List.map_cons,kids]
    split_ifs <;> rfl

lemma predBits_value {w : ℕ} (hw : 1 ≤ w) (a : Basis w) (ha : 1 ≤ (bitsValue a).toNat) :
    (bitsValue (predBits a)).toNat=(bitsValue a).toNat-1 := by
  have hb : 1<2^w := Nat.one_lt_pow (by omega) (by decide)
  rw [predBits,sub_word]
  have hv : bitsValue (fun i : Fin w => (BitVec.ofNat w 1).getLsbD i.val)=BitVec.ofNat w 1 := bitsValue_bits _
  rw [hv,BitVec.toNat_sub_of_le]
  · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb]
  · simpa only [BitVec.le_def,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb] using ha

end ChildQueue
end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ChildQueueCorrect.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic.ChildQueue
open SortedWords

def naturalKids (xs : List ℕ) : List ℕ :=
  (xs.dedup.filter (fun a=>2<a)).map (·-1)

lemma naturalKids_cons (a : ℕ) (as : List ℕ) :
    naturalKids (a::as) = if 2<a ∧ a∉as then (a-1)::naturalKids as else naturalKids as := by
  by_cases hm : a∈as <;> by_cases ha : 2<a <;>
    simp [naturalKids,hm,ha]

lemma number_injective {w : ℕ} : Function.Injective (fun a : Basis w=>(bitsValue a).toNat) := by
  intro a b h
  exact (bitsEquiv w).injective (BitVec.eq_of_toNat_eq h)

lemma kids_numbers {w : ℕ} (hw : 2 ≤ w) (xs : List (Basis w)) :
    numbers (kids xs)=naturalKids (numbers xs) := by
  induction xs with
  | nil=>rfl
  | cons a as ih=>
    have hm : (bitsValue a).toNat∈numbers as ↔ a∈as :=
      List.mem_map_of_injective number_injective
    simp only [numbers,List.map_cons] at ih ⊢
    rw [naturalKids_cons,kids]
    by_cases hc : 2<(bitsValue a).toNat ∧ a∉as
    · have hd : 2<(bitsValue a).toNat ∧ (bitsValue a).toNat∉numbers as := ⟨hc.1,fun h=>hc.2 (hm.mp h)⟩
      dsimp only [numbers] at hd
      rw [ite_eq_left hc,ite_eq_left hd,List.map_cons,predBits_value (by omega) a (by omega),ih]
    · have hd : ¬(2<(bitsValue a).toNat ∧ (bitsValue a).toNat∉numbers as) := by
        rintro ⟨h1,h2⟩
        exact hc ⟨h1,fun h=>h2 (hm.mpr h)⟩
      dsimp only [numbers] at hd
      rw [ite_eq_right hc,ite_eq_right hd,ih]

/-- No factorization oracle is used in the queue circuit: the child list obtained
from the ACTUAL correct sorted prime fields is the source's exact ordered child
list, with distinct primes within one node and occurrence multiplicity outside it. -/
lemma naturalKids_correct {N n : ℕ} {xs : List ℕ} (hN : 2 ≤ N)
    (hx : CorrectEncoding N n xs) : naturalKids xs=AuxiliaryTree.children N := by
  obtain ⟨ps,hp,hs,hprod,_,rfl⟩ := hx
  let ys := (ps++List.replicate (n-ps.length) 0).dedup.filter (fun a=>2<a)
  have hmem (p : ℕ) : p∈ys ↔ p.Prime ∧ p∣N ∧ 2<p := by
    have hperm := Nat.primeFactorsList_unique hprod hp
    dsimp only [ys]
    simp only [List.mem_filter,List.mem_dedup,decide_eq_true_eq,List.mem_append]
    constructor
    · rintro ⟨hm,ht⟩
      have hps : p∈ps := by
        rcases hm with hm | hm
        · exact hm
        · have hz := (List.mem_replicate.mp hm).2
          omega
      exact ⟨hp p hps,by rw [←hprod];exact List.dvd_prod hps,ht⟩
    · rintro ⟨hprime,hdvd,ht⟩
      exact ⟨Or.inl (hperm.mem_iff.mpr ((Nat.mem_primeFactorsList (by omega)).mpr ⟨hprime,hdvd⟩)),ht⟩
  have hn : ys.Nodup := (List.nodup_dedup _).filter _
  have hsorted : ys.Pairwise (·≤·) := by
    have hpad := paddedOrder_append ps (n-ps.length) hp hs
    have hsub : List.Sublist ys (ps++List.replicate (n-ps.length) 0) :=
      List.filter_sublist.trans (List.dedup_sublist _)
    apply (hpad.sublist hsub).imp_of_mem
    intro a b _ hb hab
    have hb2 := (hmem b).mp hb
    rcases hab with hb0 | hab
    · omega
    · exact hab.2
  have hfin : ys.toFinset=N.primeFactors.filter (fun p=>2<p) := by
    ext p
    simp only [List.mem_toFinset,hmem,Finset.mem_filter,
      Nat.mem_primeFactors_of_ne_zero (by omega : N≠0)]
    tauto
  have he : (N.primeFactors.filter (fun p=>2<p)).sort (·≤·)=ys := by
    rw [←hfin]
    exact (List.toFinset_sort (·≤·) hn).mpr hsorted
  change ys.map (·-1)=AuxiliaryTree.children N
  rw [AuxiliaryTree.children,he]

theorem kids_correct {w N n : ℕ} (hw : 2 ≤ w) (hN : 2 ≤ N)
    (xs : List (Basis w)) (hx : CorrectEncoding N n (numbers xs)) :
    numbers (kids xs)=AuxiliaryTree.children N := by
  rw [kids_numbers hw,naturalKids_correct hN hx]

end ExactQuantumFactoring.BitArithmetic.ChildQueue


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalTreeQueue.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalTree
abbrev capacity (n : ℕ) := 2*n^2+1
abbrev configWidth (n : ℕ) := capacity n*n

def query (n : ℕ) : BooleanNetwork (configWidth n) n := blockNet (capacity n) n 0

def nodeResult (n : ℕ) : BooleanNetwork (NodeKernel.width n) (tensorWidth n n) :=
  ((PhysicalNode.machine n (2*n)).currentNet (2*n)).comp (PhysicalNode.sortedOutput n)
def fields (n : ℕ) : List (BooleanNetwork (NodeKernel.width n) n) :=
  List.ofFn (fun i : Fin n=>(nodeResult n).comp (tensorSelect n n i))

def old (n : ℕ) : BooleanNetwork (configWidth n+NodeKernel.width n) (configWidth n) :=
  select (Fin.castAdd (NodeKernel.width n))
def localNode (n : ℕ) : BooleanNetwork (configWidth n+NodeKernel.width n) (NodeKernel.width n) :=
  select (Fin.natAdd (configWidth n))
def pushed (n : ℕ) : BooleanNetwork (configWidth n+NodeKernel.width n) (configWidth n) :=
  (((localNode n).pair ((old n).comp (stackPop (capacity n) n))).comp
    (ChildQueue.pushAll (capacity n) (fields n))).comp
      (ChildQueue.queue (NodeKernel.width n) (capacity n) n)
/-- Literal fixed-capacity pending-node controller. The current modulus is
removed and this very node's distinct p−1 children are prepended in sorted order.
An empty queue is an idle tick, not a new root query. -/
def update (n : ℕ) : BooleanNetwork (configWidth n+NodeKernel.width n) (configWidth n) :=
  wordMux (zeroWord ((old n).comp (query n))) (old n) (pushed n)

lemma query_encoding (n : ℕ) (a : Basis n) (xs : List (Basis n)) :
    (query n).eval (stackEncoding (capacity n) n (a::xs))=a := by
  rw [query,blockNet_eval,block_stackEncoding]
  rfl
lemma old_append (n : ℕ) (x : Basis (configWidth n)) (y : Basis (NodeKernel.width n)) :
    (old n).eval (Fin.append x y)=x := by
  funext i
  exact Fin.append_left _ _ i
lemma localNode_append (n : ℕ) (x : Basis (configWidth n)) (y : Basis (NodeKernel.width n)) :
    (localNode n).eval (Fin.append x y)=y := by
  funext i
  exact Fin.append_right _ _ i

lemma fields_eval {n : ℕ} (z : Basis (NodeKernel.width n)) (xs : List (Basis n))
    (hlen : xs.length=n) (he : (nodeResult n).eval z=SortedWords.layout n n xs) :
    (fields n).map (fun a=>a.eval z)=xs := by
  have hpad := SortedWords.ofFn_getD_pad xs (fun _=>false) n hlen.le
  simp only [hlen,Nat.sub_self,List.replicate_zero,List.append_nil] at hpad
  have hl : SortedWords.layout n n xs=tensorLayout n n
      (fun i : Fin n=>xs[i.val]?.getD (fun _=>false)) := by
    calc
      _ = SortedWords.layout n n (List.ofFn (fun i : Fin n=>xs[i.val]?.getD (fun _=>false))) :=
        congrArg (SortedWords.layout n n) hpad.symm
      _ = _ := SortedWords.layout_ofFn _ _ _
  simp only [fields,List.map_ofFn,Function.comp_def,eval_comp,he,hl,tensorSelect_eval]
  exact hpad

lemma pushed_eval {n : ℕ} (hn : 2 ≤ n) (a : Basis n) (as : List (Basis n))
    (hlen : (a::as).length ≤ capacity n) (z : Basis (NodeKernel.width n)) :
    (pushed n).eval (Fin.append (stackEncoding (capacity n) n (a::as)) z)=
      stackEncoding (capacity n) n
        (ChildQueue.kids ((fields n).map (fun b=>b.eval z))++as) := by
  rw [pushed,eval_comp,eval_comp,eval_pair,localNode_append,eval_comp,old_append,
    stackPop_encoding _ hlen,ChildQueue.pushAll_eval hn,ChildQueue.queue_eval]
  rfl

lemma update_eval {n : ℕ} (hn : 2 ≤ n) (a : Basis n) (as : List (Basis n))
    (hlen : (a::as).length ≤ capacity n) (ha : 2 ≤ (bitsValue a).toNat) (z : Basis (NodeKernel.width n)) :
    (update n).eval (Fin.append (stackEncoding (capacity n) n (a::as)) z)=
      stackEncoding (capacity n) n
        (ChildQueue.kids ((fields n).map (fun b=>b.eval z))++as) := by
  have htest : (zeroWord ((old n).comp (query n))).eval
      (Fin.append (stackEncoding (capacity n) n (a::as)) z) 0≠true := by
    intro h
    rw [zeroWord_value,eval_comp,old_append,query_encoding] at h
    omega
  rw [update,wordMux_eval,ite_eq_right htest,pushed_eval hn a as hlen z]

lemma update_nil (n : ℕ) (z : Basis (NodeKernel.width n)) :
    (update n).eval (Fin.append (stackEncoding (capacity n) n []) z)=
      stackEncoding (capacity n) n [] := by
  have hq : (query n).eval (stackEncoding (capacity n) n [])=fun _=>false := by
    rw [query,blockNet_eval,block_stackEncoding]
    rfl
  have ht : (zeroWord ((old n).comp (query n))).eval
      (Fin.append (stackEncoding (capacity n) n []) z) 0=true := by
    rw [zeroWord_value,eval_comp,old_append,hq,zeroBasis_value]
    rfl
  rw [update,wordMux_eval,ite_eq_left ht,old_append]

/-- Passed physical local computation produces EXACT canonical children in the
physical outer queue. It does not use trueData to select or initialize a query. -/
theorem update_passed {n : ℕ} (hn : 128 ≤ n) (a : Basis n) (as : List (Basis n))
    (hlen : (a::as).length ≤ capacity n) (ha : 2 ≤ (bitsValue a).toNat)
    (r : NodeKernel.Raw n) (hp : NodeKernel.passed a r) :
    ∃ kids : List (Basis n), SortedWords.numbers kids=AuxiliaryTree.children (bitsValue a).toNat ∧
      (update n).eval (Fin.append (stackEncoding (capacity n) n (a::as)) (NodeKernel.encoding a r))=
        stackEncoding (capacity n) n (kids++as) := by
  have hp' : (PhysicalNode.machine n (2*n)).passed
      (NodeStateCircuit.pack [natBasis (n+1) (bitsValue a).toNat] [] false) (2*n) r := by
    simpa only [NodeKernel.passed,NodeKernel.start,PhysicalNode.startNet_eval] using hp
  obtain ⟨zs,hl,hc,he⟩ := PhysicalNode.complete_output hn ha (bitsValue a).isLt r hp'
  have hf : (fields n).map (fun b=>b.eval (NodeKernel.encoding a r))=zs := by
    apply fields_eval _ zs hl
    rw [nodeResult,eval_comp,NodeKernel.encoding,SplitMachine.current_encoded,
      NodeKernel.start,PhysicalNode.startNet_eval]
    exact he
  refine ⟨ChildQueue.kids zs,ChildQueue.kids_correct (by omega) ha zs hc,?_⟩
  rw [update_eval (by omega : 2 ≤ n) a as hlen ha,hf]

end PhysicalTree
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalTreeMachine.lean =====
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

/-- A bit-level finite-state controller. Both transition functions are literal
Boolean networks; this structure does not grant any classical computation oracle. -/
structure NodeMachine (n c : ℕ) where
  query : BooleanNetwork c n
  update : BooleanNetwork (c+NodeKernel.width n) c

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

abbrev initWork := M.query.net.count+(NodeKernel.initialNet n).net.count
abbrev updateWork := M.update.net.count

abbrev width : ℕ→ℕ
  | 0=>c
  | t+1=>(width t+NodeKernel.width n+M.initWork)+c+M.updateWork

def current : (t : ℕ)→Register c (M.width t)
  | 0=>⟨id,Function.injective_id⟩
  | t+1=>targetRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork

def currentNet (t : ℕ) : BooleanNetwork (M.width t) c := select (M.current t)
def initNet (t : ℕ) : BooleanNetwork (M.width t) (NodeKernel.width n) :=
  ((M.currentNet t).comp M.query).comp (NodeKernel.initialNet n)
lemma initNet_count (t : ℕ) : (M.initNet t).net.count=M.initWork := by
  simp only [initNet,count_comp,currentNet,count_select,zero_add]

def updateNet (t : ℕ) : BooleanNetwork (M.width t+NodeKernel.width n+M.initWork) c :=
  (((select (firstRegister (M.width t) (NodeKernel.width n) M.initWork)).comp
    (M.currentNet t)).pair (select (targetRegister (M.width t) (NodeKernel.width n) M.initWork))).comp M.update
lemma updateNet_count (t : ℕ) : (M.updateNet t).net.count=M.updateWork := by
  simp only [updateNet,count_comp,count_pair,count_select,currentNet,zero_add]

def program : (t : ℕ)→List (Instruction (M.width t))
  | 0=>[]
  | t+1=>firstProgram c M.updateWork
      (appendPrepared (program t) (M.initNet t) (M.initNet_count t).le (NodeKernel.program n))++
      oracleOn (M.updateNet t) (M.updateNet_count t).le

def initial : (t : ℕ)→Basis c→Basis (M.width t)
  | 0,x=>x
  | t+1,x=>packed M.updateWork (packed M.initWork (initial t x) (fun _=>false)) (fun _=>false)

abbrev Trace (n : ℕ) : ℕ→Type
  | 0=>Unit
  | t+1=>Trace n t×NodeKernel.Raw n
noncomputable instance traceFintype (n t : ℕ) : Fintype (Trace n t) := by
  induction t with
  | zero=>exact inferInstanceAs (Fintype Unit)
  | succ t ih=>letI:=ih;exact inferInstanceAs (Fintype (Trace n t×NodeKernel.Raw n))

def next (x : Basis c) (r : NodeKernel.Raw n) : Basis c :=
  M.update.eval (Fin.append x (NodeKernel.encoding (M.query.eval x) r))
def config (x : Basis c) : (t : ℕ)→Trace n t→Basis c
  | 0,_=>x
  | t+1,h=>M.next (config x t h.1) h.2

def encoded (x : Basis c) : (t : ℕ)→Trace n t→Basis (M.width t)
  | 0,_=>x
  | t+1,h=>packed M.updateWork
      (packed M.initWork (encoded x t h.1)
        (NodeKernel.encoding (M.query.eval (M.config x t h.1)) h.2)) (M.config x (t+1) h)
noncomputable def state (x : Basis c) : (t : ℕ)→Trace n t→ℂ
  | 0,_=>1
  | t+1,h=>state x t h.1*NodeKernel.fresh (M.query.eval (M.config x t h.1)) h.2

lemma current_encoded (x : Basis c) (t : ℕ) (h : Trace n t) :
    (M.currentNet t).eval (M.encoded x t h)=M.config x t h := by
  cases t with
  | zero=>rfl
  | succ t=>exact packed_targetRegister _ _
lemma initNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) :
    (M.initNet t).eval (M.encoded x t h)=NodeKernel.zero (M.query.eval (M.config x t h)) := by
  rw [initNet,eval_comp,NodeKernel.initialNet_eval,eval_comp,M.current_encoded]
lemma updateNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) :
    (M.updateNet t).eval (packed M.initWork (M.encoded x t h)
      (NodeKernel.encoding (M.query.eval (M.config x t h)) r))=M.next (M.config x t h) r := by
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
      (fun h r=>NodeKernel.encoding (M.query.eval (M.config x t h)) r) (M.state x t)
      (fun h=>NodeKernel.fresh (M.query.eval (M.config x t h)))
      (M.program t) (M.initial t x) ih (M.initNet t) (M.initNet_count t).le
      (NodeKernel.program n) (by
        intro h
        rw [M.initNet_encoded,NodeKernel.program_state])
    dsimp only [program,initial,width]
    rw [programMatrix_append,←Matrix.mulVec_mulVec,firstProgram_basis,hp,encodeState_comp]
    simp only [Function.comp_def]
    rw [oracleOn_encode (fun ab : Trace n t×NodeKernel.Raw n=>
      packed M.initWork (M.encoded x t ab.1) (NodeKernel.encoding
        (M.query.eval (M.config x t ab.1)) ab.2))
      (appendState (M.state x t) (fun h=>NodeKernel.fresh (M.query.eval (M.config x t h))))
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
    have hinner := congrArg (fun z=>z ∘ firstRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork) he
    simp only [packed_first] at hinner
    have he' := congrArg (fun z=>z ∘ firstRegister (M.width t) (NodeKernel.width n) M.initWork) hinner
    simp only [packed_first] at he'
    have hab : a=b := ih he' 
    subst b
    have hr := congrArg (fun z=>z ∘ targetRegister (M.width t) (NodeKernel.width n) M.initWork) hinner
    simp only [packed_targetRegister] at hr
    have hrs : r=s := NodeKernel.encoding_injective _ hr
    subst s
    rfl

lemma width_eq (t : ℕ) : M.width t=c+t*(NodeKernel.width n+M.initWork+c+M.updateWork) := by
  induction t with
  | zero=>simp [width]
  | succ t ih=>simp only [width,ih];ring

lemma program_length (t : ℕ) : (M.program t).length≤
    t*(4*M.initWork+2*NodeKernel.width n+(NodeKernel.program n).length+4*M.updateWork+2*c) := by
  induction t with
  | zero=>simp [program]
  | succ t ih=>
    have hp := appendPrepared_length (M.program t) (M.initNet t) (M.initNet_count t).le (NodeKernel.program n)
    have hu := oracleOn_length (M.updateNet t) (M.updateNet_count t).le
    simp only [M.initNet_count] at hp
    simp only [M.updateNet_count] at hu
    simp only [program,List.length_append,firstProgram_length]
    rw [Nat.succ_mul]
    omega

end NodeMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalTreeMass.lean =====
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
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- Filtering the actual chronological query at each clock tick. No collection
of answers for unselected/counterfactual moduli occurs in this predicate. -/
noncomputable def passed (x : Basis c) : (t : ℕ)→Trace n t→Prop
  | 0,_=>True
  | t+1,h=>passed x t h.1 ∧ NodeKernel.passed (M.query.eval (M.config x t h.1)) h.2

lemma state_normalized (x : Basis c) (t : ℕ) :
    ∑ h,Complex.normSq (M.state x t h)=1 := by
  induction t with
  | zero=>simp [state,Trace]
  | succ t ih=>
    change ∑ h,Complex.normSq (appendState (M.state x t)
      (fun h=>NodeKernel.fresh (M.query.eval (M.config x t h))) h)=1
    exact append_normalized _ _ ih (fun h=>NodeKernel.fresh_normalized _)

/-- Exact physical-history probability for a clocked network controller. This
is unconditional in its update network and retains all quantum scratch. -/
theorem passed_mass (hn : 128≤n) (x : Basis c) (t : ℕ) :
    outcomeMass (M.passed x t) (M.state x t)=
      (((Completion.target n:ℝ)^(n^5+1))^(2*n))^t := by
  induction t with
  | zero=>simp [outcomeMass,passed,state,Trace]
  | succ t ih=>
    change outcomeMass (fun h : Trace n t×NodeKernel.Raw n=>M.passed x t h.1 ∧
      NodeKernel.passed (M.query.eval (M.config x t h.1)) h.2)
      (appendState (M.state x t) (fun h=>NodeKernel.fresh (M.query.eval (M.config x t h))))=_
    rw [append_constant_mass (M.state x t)
      (fun h=>NodeKernel.fresh (M.query.eval (M.config x t h))) (M.passed x t)
      (fun h=>NodeKernel.passed (M.query.eval (M.config x t h)))
      (((Completion.target n:ℝ)^(n^5+1))^(2*n))
      (fun h _=>NodeKernel.passed_mass hn (M.query.eval (M.config x t h))),ih]
    exact (pow_succ (((Completion.target n:ℝ)^(n^5+1))^(2*n)) t).symm

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
      (((Completion.target n:ℝ)^(n^5+1))^(2*n))^t := by
  rw [M.program_state,outcomeMass_encode _ (M.encoded_injective x t)]
  have he : M.physicalPassed x t ∘ M.encoded x t=M.passed x t := by
    funext h
    exact propext (M.physicalPassed_encoded x t h)
  rw [he]
  exact M.passed_mass hn x t

end NodeMachine
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/AuxiliaryData.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree

/-- The source's distinct positive-exponent factor records. Finsupp stores each
prime once; its canonical serialization sorts its support in increasing order. -/
abbrev FactorRecord := ℕ→₀ℕ

def factorRecordList (f : FactorRecord) : List (ℕ×ℕ) :=
  (f.support.sort (· ≤ ·)).map (fun p => (p,f p))

def recordChildren (f : FactorRecord) : List ℕ :=
  ((f.support.filter (fun p => 2 < p)).sort (· ≤ ·)).map (·-1)

inductive FactorData where
  | node (label : ℕ) (factors : FactorRecord) (descendants : List FactorData) : FactorData

def FactorData.label : FactorData→ℕ
  | .node m _ _ => m

def trueData (m : ℕ) : FactorData :=
  .node m m.factorization ((children m).attach.map (fun d => trueData d.val))
termination_by m
decreasing_by exact (child_bounds d.property).2

lemma trueData_eq (m : ℕ) : trueData m =
    .node m m.factorization ((children m).map trueData) := by
  rw [trueData]
  congr 1
  simp only [List.attach_map_val]

@[simp] lemma trueData_label (m : ℕ) : (trueData m).label=m := by
  rw [trueData_eq]; rfl

lemma recordChildren_factorization (m : ℕ) : recordChildren m.factorization=children m := rfl

/-- Complete-data acceptance. The local tests are finite prime checks and a
product check, followed by EXACT ordered children; no witness fields or advice. -/
inductive FactorData.Valid : FactorData→Prop where
  | node (m : ℕ) (f : FactorRecord) (ds : List FactorData)
      (hm : 2 ≤ m) (hp : ∀ p∈f.support,p.Prime) (hprod : f.prod (·^·)=m)
      (hlabels : ds.map FactorData.label=recordChildren f)
      (hchildren : ∀ d∈ds, FactorData.Valid d) : FactorData.Valid (.node m f ds)

lemma valid_factorRecord {m : ℕ} {f : FactorRecord}
    (hp : ∀ p∈f.support,p.Prime) (hprod : f.prod (·^·)=m) : f=m.factorization := by
  rw [← hprod,Nat.prod_pow_factorization_eq_self hp]

/-- Unique prime factorization makes the entire ordered occurrence tree unique;
equal child labels under different parents remain separate list occurrences. -/
theorem valid_eq_trueData {d : FactorData} (hd : d.Valid) : d=trueData d.label := by
  induction hd with
  | node m f ds hm hp hprod hlabels _ ih =>
    have hf := valid_factorRecord hp hprod
    have hds : ds=(children m).map trueData := by
      have hh : ds.map (fun d => trueData d.label)=ds := by
        calc
          _ = ds.map id := List.map_congr_left (fun d hd => (ih d hd).symm)
          _ = ds := List.map_id ds
      calc
        ds = ds.map (fun d => trueData d.label) := hh.symm
        _ = (ds.map FactorData.label).map trueData := List.map_map.symm
        _ = (children m).map trueData := by rw [hlabels,hf,recordChildren_factorization]
    rw [hf,hds]
    exact (trueData_eq m).symm

/-- The canonical data are always complete; recursion is justified by the
literal source decrease p−1<m, not a guessed tree. -/
theorem trueData_valid {m : ℕ} (hm : 2 ≤ m) : (trueData m).Valid := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rw [trueData_eq]
    apply FactorData.Valid.node m m.factorization ((children m).map trueData) hm
    · intro p hp
      exact Nat.prime_of_mem_primeFactors hp
    · exact Nat.prod_factorization_pow_eq_self (by omega)
    · simp only [List.map_map,Function.comp_def,trueData_label,recordChildren_factorization]
      exact List.map_id (children m)
    · intro d hd
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hd
      exact ih a (child_bounds ha).2 (child_bounds ha).1

theorem valid_iff_trueData {m : ℕ} (hm : 2 ≤ m) (d : FactorData) (hl : d.label=m) :
    d.Valid ↔ d=trueData m := by
  constructor
  · intro hd
    simpa only [hl] using valid_eq_trueData hd
  · rintro rfl
    exact trueData_valid hm

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PrimeRecords.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

noncomputable def primeRecord : List ℕ→FactorRecord
  | [] => 0
  | p::ps => Finsupp.single p 1+primeRecord ps

lemma primeRecord_eq_factorization (ps : List ℕ) (hp : ∀ p∈ps,p.Prime) :
    primeRecord ps=ps.prod.factorization := by
  induction ps with
  | nil => simp [primeRecord]
  | cons p ps ih =>
    have hprime := hp p (by simp)
    have ht : ∀ q∈ps,q.Prime := fun q hq => hp q (by simp [hq])
    have hprod : ps.prod≠0 := by
      apply List.prod_ne_zero
      intro hzero
      exact (ht 0 hzero).ne_zero rfl
    rw [primeRecord,List.prod_cons,Nat.factorization_mul hprime.ne_zero hprod,
      hprime.factorization,ih ht]

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/LoggedExecution.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

/-- A bounded deterministic computation and the chronological requests it
actually made. Failure retains its prefix and does not query later work. -/
structure Logged (Q α : Type*) where
  result : Option α
  requests : List Q

namespace Logged
variable {Q α β γ : Type*}

def pure (a : α) : Logged Q α := ⟨some a,[]⟩
def abort : Logged Q α := ⟨none,[]⟩
def bind (x : Logged Q α) (f : α→Logged Q β) : Logged Q β :=
  match x.result with
  | none => ⟨none,x.requests⟩
  | some a => ⟨(f a).result,x.requests++(f a).requests⟩
def map (f : α→β) (x : Logged Q α) : Logged Q β := x.bind (fun a => pure (f a))
def Good (P : Q→Prop) (x : Logged Q α) : Prop := ∀ q∈x.requests,P q

lemma good_bind_left (P : Q→Prop) (x : Logged Q α) (f : α→Logged Q β)
    (h : Good P (x.bind f)) : Good P x := by
  intro q hq
  cases hx : x.result with
  | none => exact h q (by simpa only [bind,hx] using hq)
  | some a => exact h q (by simp only [bind,hx,List.mem_append]; exact Or.inl hq)

lemma good_bind_right (P : Q→Prop) (x : Logged Q α) (f : α→Logged Q β) {a : α}
    (hx : x.result=some a) (h : Good P (x.bind f)) : Good P (f a) := by
  intro q hq
  exact h q (by simp only [bind,hx,List.mem_append]; exact Or.inr hq)

lemma bind_result_some (x : Logged Q α) (f : α→Logged Q β) {a : α}
    (hx : x.result=some a) : (x.bind f).result=(f a).result := by simp only [bind,hx]

lemma map_result (f : α→β) (x : Logged Q α) : (x.map f).result=x.result.map f := by
  cases hx : x.result <;> simp [map,bind,hx,pure]

lemma map_requests (f : α→β) (x : Logged Q α) : (x.map f).requests=x.requests := by
  cases hx : x.result <;> simp [map,bind,hx,pure]

lemma good_map (P : Q→Prop) (f : α→β) (x : Logged Q α) :
    Good P (x.map f) ↔ Good P x := by simp only [Good,map_requests]

def traverse (f : α→Logged Q β) : List α→Logged Q (List β)
  | [] => pure []
  | a::as => (f a).bind (fun b => (traverse f as).map (b::·))

/-- No hypothesis at unvisited requests: the induction uses the good prefix,
obtains its successful result, then exposes the actual next prefix. -/
lemma traverse_complete (P : Q→Prop) (f : α→Logged Q β) (g : α→β) (xs : List α)
    (hlocal : ∀ a∈xs, Good P (f a) → (f a).result=some (g a))
    (hg : Good P (traverse f xs)) : (traverse f xs).result=some (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    have hhead := good_bind_left P _ _ hg
    have hs := hlocal a (by simp) hhead
    have htail := good_bind_right P _ _ hs hg
    have ht := (good_map P (g a::·) (traverse f as)).mp htail
    have hr := ih (fun b hb => hlocal b (by simp [hb])) ht
    rw [traverse,bind_result_some _ _ hs,map_result,hr,Option.map_some,List.map_cons]

lemma traverse_sound (f : α→Logged Q β) (g : α→β) (xs : List α)
    (hlocal : ∀ a∈xs, ∀ b, (f a).result=some b → b=g a)
    {ys : List β} (hs : (traverse f xs).result=some ys) : ys=xs.map g := by
  induction xs generalizing ys with
  | nil => simpa only [traverse,pure,List.map_nil,Option.some.injEq] using hs.symm
  | cons a as ih =>
    cases hf : (f a).result with
    | none => simp only [traverse,bind,hf] at hs; contradiction
    | some b =>
      have hb := hlocal a (by simp) b hf
      rw [traverse,bind_result_some _ _ hf,map_result] at hs
      obtain ⟨bs,hbs,hys⟩ := Option.map_eq_some_iff.mp hs
      have ht := ih (fun c hc => hlocal c (by simp [hc])) hbs
      subst ys
      rw [hb,ht,List.map_cons]

end Logged
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ControllerQueries.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.FactorController

/-- The actual queried moduli, in chronological order. A rejected divisor
aborts and does not query nonexistent later work. -/
def queries (choose : ℕ→ℕ→ℕ) : ℕ→ℕ→List ℕ→List (ℕ×ℕ)
  | _, _, [] => []
  | 0, _, _::_ => []
  | fuel+1, i, m::ms =>
    if m.Prime then queries choose fuel (i+1) ms
    else (i,m)::(if ProperDivisor m (choose i m) then
      queries choose fuel (i+1) (choose i m::m/choose i m::ms) else [])

lemma queries_length (choose : ℕ→ℕ→ℕ) (fuel i : ℕ) (ms : List ℕ) :
    (queries choose fuel i ms).length ≤ fuel := by
  induction fuel generalizing i ms with
  | zero => cases ms <;> simp [queries]
  | succ fuel ih =>
    cases ms with
    | nil => simp [queries]
    | cons m ms =>
      simp only [queries]
      split_ifs with hp hd
      · exact (ih _ _).trans (by omega)
      · simpa only [List.length_cons] using Nat.succ_le_succ (ih (i+1) _)
      · simp

/-- All-good is required ONLY at queries of this very run, not at a table of
counterfactual future requests. Exhaustion is excluded by the split weight. -/
theorem run_complete_on_queries (choose : ℕ→ℕ→ℕ) {fuel i : ℕ} {ms : List ℕ}
    (hms : ∀ m∈ms, 2 ≤ m) (hw : weight ms ≤ fuel)
    (hg : ∀ im∈queries choose fuel i ms, ProperDivisor im.2 (choose im.1 im.2)) :
    ∃ ps, run choose fuel i ms=some ps := by
  induction fuel generalizing i ms with
  | zero =>
    cases ms with
    | nil => exact ⟨[],rfl⟩
    | cons m ms =>
      have hp := splitWeight_pos (hms m (by simp))
      simp only [weight,List.map_cons,List.sum_cons] at hw
      omega
  | succ fuel ih =>
    cases ms with
    | nil => exact ⟨[],rfl⟩
    | cons m ms =>
      have hm := hms m (by simp)
      have ht : ∀ a∈ms,2 ≤ a := fun a ha => hms a (by simp [ha])
      by_cases hp : m.Prime
      · have hw' : weight ms ≤ fuel := by rw [weight_prime m ms hp] at hw; omega
        have hg' : ∀ im∈queries choose fuel (i+1) ms, ProperDivisor im.2 (choose im.1 im.2) := by
          intro im hi
          exact hg im (by simpa only [queries,ite_eq_left hp] using hi)
        obtain ⟨ps,hps⟩ := ih ht hw' hg'
        exact ⟨m::ps,by simp only [run,ite_eq_left hp,hps,Option.map_some]⟩
      · have hd := hg (i,m) (by simp only [queries,ite_eq_right hp,List.mem_cons]; exact Or.inl trivial)
        have hd' : ProperDivisor m (choose i m) := hd
        have hq := hd'.quotient
        have hw' : weight (choose i m::m/choose i m::ms) ≤ fuel := by
          rw [weight_split hd' ms] at hw
          omega
        have hm' : ∀ a∈choose i m::m/choose i m::ms,2 ≤ a := by
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · have := hd'.1; omega
          · rcases List.mem_cons.mp ha with rfl | ha
            · exact hq.1
            · exact ht a ha
        have hg' : ∀ im∈queries choose fuel (i+1) (choose i m::m/choose i m::ms),
            ProperDivisor im.2 (choose im.1 im.2) := by
          intro im hi
          exact hg im (by simp only [queries,ite_eq_right hp,ite_eq_left hd',List.mem_cons]; exact Or.inr hi)
        obtain ⟨ps,hps⟩ := ih hm' hw' hg'
        exact ⟨ps,by simp only [run,ite_eq_right hp,ite_eq_left hd',hps]⟩

lemma queries_bounded (choose : ℕ→ℕ→ℕ) {fuel i N : ℕ} {ms : List ℕ}
    (hms : ∀ m∈ms,2 ≤ m ∧ m ≤ N) :
    ∀ im∈queries choose fuel i ms, 2 ≤ im.2 ∧ im.2 ≤ N ∧ ¬im.2.Prime := by
  induction fuel generalizing i ms with
  | zero => cases ms <;> simp [queries]
  | succ fuel ih =>
    cases ms with
    | nil => simp [queries]
    | cons m ms =>
      have hm := hms m (by simp)
      have ht : ∀ a∈ms,2 ≤ a ∧ a ≤ N := fun a ha => hms a (by simp [ha])
      simp only [queries]
      split_ifs with hp hd
      · exact ih ht
      · intro im hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact ⟨hm.1,hm.2,hp⟩
        · apply ih (ms:=choose i m::m/choose i m::ms) ?_ im hi
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact ⟨by have := hd.1; omega,hd.2.1.le.trans hm.2⟩
          · rcases List.mem_cons.mp ha with rfl | ha
            · exact ⟨hd.quotient.1,hd.quotient.2.1.le.trans hm.2⟩
            · exact ht a ha
      · intro im hi
        have he : im=(i,m) := by simpa only [List.mem_singleton] using hi
        subst im
        exact ⟨hm.1,hm.2,hp⟩

/-- Instantiate the local event with the source's favorable list and actual
true-order outputs. Only recorded queries, no counterfactual oracle inputs. -/
theorem supplied_node_complete_on_queries {N n : ℕ} (hN : 2 ≤ N) (hb : N < 2^n)
    (outputs : ℕ→ℕ→List (ℕ×ℕ))
    (hg : ∀ im∈queries (fun i m => suppliedDivisor m n (outputs i m)) (2*n) 0 [N],
      ∀ (hm : 2 ≤ im.2) (hle : im.2 ≤ N), Odd im.2 → ¬Primality.PerfectPower im.2 →
      ∃ (p₀ : Component im.2) (u : (ZMod im.2)ˣ),
        FavorableUnit (by omega : im.2≠0) (hle.trans_lt hb) p₀ u ∧
        ((u : ZMod im.2).val,orderOf u)∈outputs im.1 im.2) :
    ∃ ps, run (fun i m => suppliedDivisor m n (outputs i m)) (2*n) 0 [N]=some ps := by
  apply run_complete_on_queries _ (by
    intro m hm
    have he : m=N := by simpa using hm
    subst m
    exact hN)
  · have hh := AuxiliaryTree.splitWeight_bound (by omega) hb
    simp only [weight,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    omega
  · intro im hi
    have hbounds := queries_bounded (fun i m => suppliedDivisor m n (outputs i m))
      (N:=N) (by
        intro m hm
        have he : m=N := by simpa using hm
        subst m
        exact ⟨hN,le_rfl⟩) im hi
    exact suppliedDivisor_good hbounds.1 (hbounds.2.1.trans_lt hb) hbounds.2.2 _
      (hg im hi hbounds.1 hbounds.2.1)

end ExactQuantumFactoring.FactorController


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/AuxiliaryProducer.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree FactorController

namespace DataProducer

/-- Each occurrence carries its complete ancestral path. Equal labels under
separate parents are never identified or memoized. -/
abbrev NodeKey := List ℕ × ℕ
abbrev Choices := NodeKey→ℕ→ℕ→ℕ

def nodeRun (n : ℕ) (choose : Choices) (path : List ℕ) (m : ℕ) : Logged NodeKey (List ℕ) :=
  ⟨run (choose (path,m)) (2*n) 0 [m],[(path,m)]⟩

def NodeGood (n : ℕ) (choose : Choices) (k : NodeKey) : Prop :=
  ∀ im∈queries (choose k) (2*n) 0 [k.2], ProperDivisor im.2 (choose k im.1 im.2)

/-- The source's factor-and-recurse producer, with a depth cap. The Finsupp is
only a representation of the multiplicities in the returned prime list;
`primeRecord` never computes an unknown prime factorization. -/
noncomputable def build (n : ℕ) (choose : Choices) : ℕ→List ℕ→ℕ→Logged NodeKey FactorData
  | 0, _, _ => Logged.abort
  | depth+1, path, m => (nodeRun n choose path m).bind (fun ps =>
      (Logged.traverse (fun d => build n choose depth (path++[d]) d)
        (recordChildren (primeRecord ps))).map (FactorData.node m (primeRecord ps)))

lemma nodeRun_complete {m n : ℕ} (hm : 2 ≤ m) (hb : m<2^n)
    (choose : Choices) (path : List ℕ) (hg : Logged.Good (NodeGood n choose) (nodeRun n choose path m)) :
    ∃ ps, (nodeRun n choose path m).result=some ps := by
  apply run_complete_on_queries (choose (path,m))
  · intro a ha
    have he : a=m := by simpa using ha
    subst a
    exact hm
  · have hw := splitWeight_bound (by omega) hb
    simp only [weight,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    omega
  · exact hg (path,m) (by simp [nodeRun])

lemma nodeRun_record {n m : ℕ} {choose : Choices} {path : List ℕ} {ps : List ℕ}
    (h : (nodeRun n choose path m).result=some ps) : primeRecord ps=m.factorization := by
  have hs := run_sound (choose (path,m)) h
  have hp : ps.prod=m := by simpa using hs.2
  rw [primeRecord_eq_factorization ps hs.1,hp]

lemma child_level_empty {m depth d : ℕ} (h : level m (depth+1)=[]) (hd : d∈children m) :
    level d depth=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro e he
  have hh : e∈level m (depth+1) := List.mem_flatMap.mpr ⟨d,hd,he⟩
  rw [h] at hh
  exact List.not_mem_nil hh

/-- Literal all-good completion follows the actual short-circuit trace. There
is no hypothesis about queries or child occurrences that this run never made. -/
theorem build_complete (n : ℕ) (choose : Choices) (depth : ℕ) (path : List ℕ) (m : ℕ)
    (hm : 2 ≤ m) (hb : m<2^n) (hd : level m depth=[])
    (hg : Logged.Good (NodeGood n choose) (build n choose depth path m)) :
    (build n choose depth path m).result=some (trueData m) := by
  induction depth generalizing path m with
  | zero => simp only [level,List.cons_ne_self] at hd
  | succ depth ih =>
    have hroot := Logged.good_bind_left (NodeGood n choose) _ _ hg
    obtain ⟨ps,hps⟩ := nodeRun_complete hm hb choose path hroot
    have hf := nodeRun_record hps
    have hg' := Logged.good_bind_right (NodeGood n choose) _ _ hps hg
    have hchildren := (Logged.good_map (NodeGood n choose) _ _).mp hg'
    rw [hf,recordChildren_factorization] at hchildren
    have hc : (Logged.traverse (fun d => build n choose depth (path++[d]) d)
        (children m)).result=some ((children m).map trueData) := by
      apply Logged.traverse_complete (NodeGood n choose) _ trueData _ ?_ hchildren
      intro d hdm hgd
      have hbounds := child_bounds hdm
      exact ih _ _ hbounds.1 (hbounds.2.trans hb) (child_level_empty hd hdm) hgd
    rw [build,Logged.bind_result_some _ _ hps,Logged.map_result,hf,recordChildren_factorization,
      hc,Option.map_some,trueData_eq]

/-- Even a bad run cannot produce false accepted data. Every successful local
prime list and all ordered descendants agree with the canonical occurrence tree. -/
theorem build_sound (n : ℕ) (choose : Choices) (depth : ℕ) (path : List ℕ) (m : ℕ)
    {d : FactorData} (hs : (build n choose depth path m).result=some d) : d=trueData m := by
  induction depth generalizing path m d with
  | zero => simp only [build,Logged.abort] at hs; contradiction
  | succ depth ih =>
    cases hroot : (nodeRun n choose path m).result with
    | none => simp only [build,Logged.bind,hroot] at hs; contradiction
    | some ps =>
      have hf := nodeRun_record hroot
      rw [build,Logged.bind_result_some _ _ hroot,Logged.map_result,hf,recordChildren_factorization] at hs
      obtain ⟨ds,hds,he⟩ := Option.map_eq_some_iff.mp hs
      have hcan := Logged.traverse_sound (fun a => build n choose depth (path++[a]) a)
        trueData (children m) (fun a _ b hab => ih (path++[a]) a hab) hds
      subst d
      rw [hcan]
      exact (trueData_eq m).symm

theorem bounded_complete {m n : ℕ} (hm : 2 ≤ m) (hb : m<2^n)
    (choose : Choices) (hg : Logged.Good (NodeGood n choose) (build n choose (2*n) [] m)) :
    (build n choose (2*n) [] m).result=some (trueData m) ∧ (trueData m).Valid :=
  ⟨build_complete n choose (2*n) [] m hm hb (level_empty hm hb) hg,trueData_valid hm⟩

end DataProducer
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TraceBounds.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma list_map_sum_le {α : Type*} (xs : List α) (f g : α→ℕ) (h : ∀ a∈xs,f a ≤ g a) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    exact Nat.add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

namespace Logged
variable {Q α β : Type*}

lemma traverse_requests_length (f : α→Logged Q β) (xs : List α) :
    (traverse f xs).requests.length  ≤  (xs.map (fun a => (f a).requests.length)).sum := by
  induction xs with
  | nil => simp [traverse,pure]
  | cons a as ih =>
    cases hx : (f a).result with
    | none => simp [traverse,bind,hx]
    | some b =>
      simp only [traverse,bind,hx,List.length_append,map_requests,List.map_cons,List.sum_cons]
      exact Nat.add_le_add_left ih _

end Logged
namespace AuxiliaryTree

def visits : ℕ→ℕ→List ℕ
  | 0, _ => []
  | depth+1, m => m::(children m).flatMap (visits depth)

lemma sum_map_range (xs : List ℕ) (f : ℕ→ℕ→ℕ) (d : ℕ) :
    (xs.map (fun a => ∑ k∈Finset.range d, f a k)).sum =
      ∑ k∈Finset.range d, (xs.map (fun a => f a k)).sum := by
  induction xs with
  | nil => simp
  | cons a as ih => simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]

lemma visits_length (depth m : ℕ) :
    (visits depth m).length = ∑ k∈Finset.range depth, (level m k).length := by
  induction depth generalizing m with
  | zero => simp [visits]
  | succ d ih =>
    rw [visits,List.length_cons,List.length_flatMap]
    simp_rw [ih]
    rw [sum_map_range,Finset.sum_range_succ']
    simp only [level,List.length_flatMap,List.length_singleton]

lemma visits_length_le {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (depth : ℕ) :
    (visits depth m).length  ≤  depth*n := by
  rw [visits_length]
  calc
    _  ≤  ∑ _k∈Finset.range depth,n := Finset.sum_le_sum (fun k _ => (level_length_lt (k:=k) hm hb).le)
    _ = depth*n := by simp

end AuxiliaryTree
namespace DataProducer
open AuxiliaryTree FactorController

/-- A failing producer only visits a prefix of the genuine occurrence tree.
Whenever it proceeds below a node, the validated factor list forces exactly the
canonical children. This bound does not assume that any stochastic test passed. -/
theorem build_requests_length (n : ℕ) (choose : Choices) (depth : ℕ) (path : List ℕ) (m : ℕ) :
    (build n choose depth path m).requests.length  ≤  (visits depth m).length := by
  induction depth generalizing path m with
  | zero => simp [build,Logged.abort,visits]
  | succ depth ih =>
    cases hs : (nodeRun n choose path m).result with
    | none =>
      simp only [build,Logged.bind,hs,visits,List.length_cons]
      change 1 ≤ _+1
      omega
    | some ps =>
      have hf := nodeRun_record hs
      simp only [build,Logged.bind,hs,Logged.map_requests,hf,recordChildren_factorization,
        List.length_append,visits,List.length_cons,List.length_flatMap]
      have ht := Logged.traverse_requests_length (fun d => build n choose depth (path++[d]) d) (children m)
      have hsum : ((children m).map (fun d => (build n choose depth (path++[d]) d).requests.length)).sum  ≤ 
          ((children m).map (fun d => (visits depth d).length)).sum := by
        exact list_map_sum_le _ _ _ (fun d _ => ih _ d)
      have ht' := ht.trans hsum
      change 1+_  ≤  _+1
      omega

lemma full_requests_length {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (choose : Choices) :
    (build n choose (2*n) [] m).requests.length  ≤  2*n^2 := by
  exact (build_requests_length n choose (2*n) [] m).trans
    (by simpa only [pow_two,Nat.mul_assoc] using visits_length_le hm hb (2*n))

/-- Count every local splitting request, including the final failed one. -/
noncomputable def splitRequests (n : ℕ) (choose : Choices) (depth : ℕ) (m : ℕ) : List (NodeKey×(ℕ×ℕ)) :=
  (build n choose depth [] m).requests.flatMap (fun k =>
    (queries (choose k) (2*n) 0 [k.2]).map (k,·))

lemma splitRequests_length {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (choose : Choices) :
    (splitRequests n choose (2*n) m).length  ≤  4*n^3 := by
  simp only [splitRequests,List.length_flatMap,List.length_map]
  calc
    _  ≤  ((build n choose (2*n) [] m).requests.map (fun _ => 2*n)).sum := by
      exact list_map_sum_le _ _ _ (fun k _ => queries_length _ _ _ _)
    _ = (build n choose (2*n) [] m).requests.length*(2*n) := by simp
    _  ≤  (2*n^2)*(2*n) := Nat.mul_le_mul_right _ (full_requests_length hm hb choose)
    _ = 4*n^3 := by ring

lemma padded_transition_bound {n : ℕ} (hn : 128 ≤ n) : 4*n^3*(n^5+1)<n^10 := by
  have hp : 1 ≤ n^5 := Nat.one_le_pow _ _ (by omega)
  have hsmall : 8<n^2 := by
    have hh := Nat.pow_le_pow_left hn 2
    norm_num at hh
    omega
  calc
    _  ≤  4*n^3*(2*n^5) := Nat.mul_le_mul_left _ (by omega)
    _ = 8*n^8 := by ring
    _ < n^2*n^8 := Nat.mul_lt_mul_of_pos_right hsmall (pow_pos (by omega) _)
    _ = n^10 := by ring

end DataProducer
end ExactQuantumFactoring


end

end OAI


