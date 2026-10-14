-- Prove2me | Definitions.Def_OAI_QuantumFactoring_Part13
-- name    : OAI_QuantumFactoring_Part13
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T07:42:09.771479+00:00
-- url     : https://prove2.me/theorems/c773847f-7fee-4764-8aa5-c6356fe40fa8
-- title:
--   Exact quantum factoring, part 13 of 38 (port of OpenAI's formalization)
-- statement:
--   Part 13 of 38 of a port of OpenAI's Lean formalization of the manuscript *Exact quantum factoring over a fixed finite gate set* (OpenAI, September 25, 2026). This part contains the modules `ReadOnlyCircuit`, `ControlledHadamard`, `MaskedPreparation`, `RuntimeListPreparation`, `TransitionWords`, `TransitionNetworks`, `ListSamplerCircuit`, `PhysicalListSlots`, `PhysicalListNetworks`, `ProvidedSplits`, `CompletedSplit`, `FixedSplit`, `AdaptivePrepared`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/QuantumFactoring`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `ExactQuantumFactoring`, which is identical to upstream `Basic.lean`. This part also makes small compatibility edits for Lean 4.33.1 / Mathlib 0df444a: in PhysicalListSlots.lean, use the `↓reduceIte` simproc instead of `ite_true` (the classical decidability instance no longer matches `ite_true`).
--
--   The development is split into 38 parts only so that each compiles within the platform's time limit. Together the parts supply the circuit family `PhysicalTree.finalCircuit` and its specification, used to prove `OAI.ExactQuantumFactoring.zero_amplitude_core`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/QuantumFactoring: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ReadOnlyCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ControlledHadamard.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/MaskedPreparation.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/RuntimeListPreparation.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/TransitionWords.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/TransitionNetworks.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ListSamplerCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalListSlots.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalListNetworks.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ProvidedSplits.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/CompletedSplit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/FixedSplit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/AdaptivePrepared.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf

/-
Exact quantum factoring development (port of OpenAI's formalization), part 13 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: ReadOnlyCircuit.lean, ControlledHadamard.lean, MaskedPreparation.lean, RuntimeListPreparation.lean, TransitionWords.lean, TransitionNetworks.lean, ListSamplerCircuit.lean, PhysicalListSlots.lean, PhysicalListNetworks.lean, ProvidedSplits.lean, CompletedSplit.lean, FixedSplit.lean, AdaptivePrepared.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted; compatibility edits for the platform Lean/Mathlib versions: in PhysicalListSlots.lean, use the `↓reduceIte` simproc instead of `ite_true` (the classical decidability instance no longer matches `ite_true`).
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part12

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ReadOnlyCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma Gate.arity_pos (g : Gate) : 0<g.arity := by
  cases g with
  | mk p inv ctrl => cases p <;> cases ctrl <;> simp [Gate.arity,Primitive.arity]

def Instruction.target {q : ℕ} (o : Instruction q) : Fin q :=
  o.wire ⟨o.gate.arity-1,by have := o.gate.arity_pos; omega⟩

lemma Primitive.nonTarget_zero (p : Primitive) (x y : Basis p.arity) (i : Fin p.arity)
    (hi : i.val+1<p.arity) (hne : x i≠y i) : p.localMatrix x y=0 := by
  cases p with
  | not => simp only [Primitive.arity] at hi; omega
  | hadamard => simp only [Primitive.arity] at hi; omega
  | phase => simp only [Primitive.arity] at hi; omega
  | cnot =>
    rw [cnot_localMatrix]
    have hc : cnotPerm y i=y i := by
      fin_cases i <;> simp_all [cnotPerm,Primitive.arity]
    have hxy : x≠cnotPerm y := fun he => hne ((congrFun he i).trans hc)
    change (if x=_ then (1 : ℂ) else 0)=0
    exact ite_eq_right hxy
  | toffoli =>
    rw [toffoli_localMatrix]
    have hc : toffoliPerm y i=y i := by
      fin_cases i <;> simp_all [toffoliPerm,Primitive.arity]
    have hxy : x≠toffoliPerm y := fun he => hne ((congrFun he i).trans hc)
    change (if x=_ then (1 : ℂ) else 0)=0
    exact ite_eq_right hxy

lemma Gate.base_nonTarget_zero (g : Gate) (x y : Basis g.primitive.arity)
    (i : Fin g.primitive.arity) (hi : i.val+1<g.primitive.arity) (hne : x i≠y i) :
    g.baseLocalMatrix x y=0 := by
  rw [g.baseLocalMatrix_eq]
  split_ifs
  · change star (g.primitive.localMatrix y x)=0
    rw [g.primitive.nonTarget_zero y x i hi (Ne.symm hne),star_zero]
  · exact g.primitive.nonTarget_zero x y i hi hne

/-- In the literal fixed alphabet, all but the final wire are controls.
The inverse and added-control variants preserve these same wires. -/
lemma Gate.nonTarget_zero (g : Gate) (x y : Basis g.arity) (i : Fin g.arity)
    (hi : i.val+1<g.arity) (hne : x i≠y i) : g.localMatrix x y=0 := by
  rcases g with ⟨p,inv,ctrl⟩
  cases ctrl
  · exact Gate.base_nonTarget_zero ⟨p,inv,false⟩ x y i hi hne
  · change Basis (p.arity+1) at x y
    change Fin (p.arity+1) at i
    rw [Gate.controlled_localMatrix]
    change controlledMatrix (Gate.mk p inv true).baseLocalMatrix
      (x 0,Fin.tail x) (y 0,Fin.tail y)=0
    by_cases ht : x 0=y 0
    · have hi0 : i.val≠0 := by
        intro hi0
        have hie : i=0 := Fin.ext hi0
        exact hne (hie ▸ ht)
      have hi' : i.val+1<p.arity+1 := hi
      let j : Fin p.arity := ⟨i.val-1,by omega⟩
      have hji : j.succ=i := Fin.ext (by simp only [Fin.val_succ,j]; omega)
      have hjn : Fin.tail x j≠Fin.tail y j := by
        simpa only [Fin.tail_def,hji] using hne
      have htail : Fin.tail x≠Fin.tail y := fun he => hjn (congrFun he j)
      dsimp only [controlledMatrix,Matrix.of_apply]
      rw [ite_eq_left ht]
      split_ifs
      · exact Gate.base_nonTarget_zero ⟨p,inv,true⟩ _ _ j (by simp only [j]; omega) hjn
      · simp
    · simp [controlledMatrix,ht]

lemma Instruction.nonzero_eq {q : ℕ} (o : Instruction q) (x y : Basis q)
    (h : o.matrix x y≠0) (i : Fin q) (hi : i≠o.target) : x i=y i := by
  classical
  have houtside : ∀ i : Fin q,(∀ j,o.wire j≠i)→x i=y i := by
    by_contra hn
    exact h (by simp only [Instruction.matrix,ite_eq_right hn])
  have hlocal : o.gate.localMatrix (x∘o.wire) (y∘o.wire)≠0 := by
    simpa only [Instruction.matrix,ite_eq_left houtside,Gate.localMatrix,Matrix.of_apply] using h
  by_cases hw : ∃ j,o.wire j=i
  · obtain ⟨j,rfl⟩ := hw
    have hj : j.val+1<o.gate.arity := by
      have hjne : j.val≠o.gate.arity-1 := by
        intro he
        apply hi
        unfold Instruction.target
        congr 1
        exact Fin.ext he
      omega
    by_contra hne
    exact hlocal (o.gate.nonTarget_zero _ _ j hj hne)
  · exact houtside i (by simpa only [not_exists] using hw)


end ExactQuantumFactoring
end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ControlledHadamard.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

/-- One of the literal fixed alphabet gates; the extra control is the first
wire and is never modified. -/
abbrev controlledHadamardAt {q : ℕ} (c t : Fin q) (h : c≠t) : Instruction q :=
  ⟨⟨.hadamard,false,true⟩, ![c,t], by
    change Function.Injective (![c,t] : Fin 2→Fin q)
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all⟩

lemma controlledHadamardAt_matrix {q : ℕ} (c t : Fin q) (h : c≠t) (x y : Basis q) :
    (controlledHadamardAt c t h).matrix y x =
      if x c then (hadamardAt t).matrix y x else if y=x then 1 else 0 := by
  classical
  have ho : (∀ i : Fin q,(∀ j : Fin 2, (![c,t] : Fin 2→Fin q) j≠i)→y i=x i) ↔
      (∀ i : Fin q, i≠c→i≠t→y i=x i) := by
    constructor
    · intro hh i hic hit
      apply hh i
      intro j
      fin_cases j
      · exact Ne.symm hic
      · exact Ne.symm hit
    · intro hh i hi
      exact hh i (Ne.symm (hi 0)) (Ne.symm (hi 1))
  change (if ∀ i : Fin q,(∀ j : Fin 2, (![c,t] : Fin 2→Fin q) j≠i)→y i=x i then
    (Gate.mk .hadamard false true).matrix
      (List.ofFn (y∘(![c,t] : Fin 2→Fin q)))
      (List.ofFn (x∘(![c,t] : Fin 2→Fin q))) else 0)=_
  simp only [ho,List.ofFn_succ,List.ofFn_zero,Function.comp_apply,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  rw [hadamardAt_matrix]
  have hyc : (∀ i : Fin q,i≠t→y i=x i) ↔ y c=x c ∧ (∀ i : Fin q,i≠c→i≠t→y i=x i) := by
    constructor
    · exact fun hh => ⟨hh c h,fun i _ hit => hh i hit⟩
    · rintro ⟨hc,hh⟩ i hit
      by_cases hic : i=c
      · simpa [hic] using hc
      · exact hh i hic hit
  have heq : y=x ↔ y c=x c ∧ y t=x t ∧ (∀ i : Fin q,i≠c→i≠t→y i=x i) := by
    constructor
    · rintro rfl; simp
    · rintro ⟨hc,ht,hh⟩
      funext i
      by_cases hic : i=c
      · simpa [hic] using hc
      · by_cases hit : i=t
        · simpa [hit] using ht
        · exact hh i hic hit
  simp only [hyc,heq]
  cases xc : x c <;> cases yc : y c <;>
    simp only [Gate.matrix,Gate.baseMatrix,Bool.true_eq,Bool.false_eq_true,ite_true,ite_false,
      Primitive.matrix,List.cons.injEq, and_true]
  all_goals split_ifs <;> simp_all

lemma controlledHadamardAt_basis {q : ℕ} (c t : Fin q) (h : c≠t) (x : Basis q) :
    (controlledHadamardAt c t h).matrix.mulVec (basisVector x)=
      if x c then (hadamardAt t).matrix.mulVec (basisVector x) else basisVector x := by
  classical
  rw [matrix_basisVector]
  funext y
  rw [controlledHadamardAt_matrix]
  cases hx : x c <;> simp [matrix_basisVector,basisVector]

lemma controlledHadamardAt_target {q : ℕ} (c t : Fin q) (h : c≠t) :
    (controlledHadamardAt c t h).target=t := rfl

/-- On a sector with a fixed control, controlled H is H or the identity on an
arbitrary coherent state, including all old retained work. -/
lemma controlledHadamardAt_sector {q : ℕ} (c t : Fin q) (h : c≠t) (b : Bool)
    (ψ : State q) (hs : Supported (fun x => x c=b) ψ) :
    (controlledHadamardAt c t h).matrix.mulVec ψ=
      if b then (hadamardAt t).matrix.mulVec ψ else ψ := by
  classical
  funext y
  change (∑ x,(controlledHadamardAt c t h).matrix y x*ψ x)=_
  simp_rw [controlledHadamardAt_matrix]
  cases b
  · simp only [Bool.false_eq_true,ite_false]
    calc
      _ = ∑ x : Basis q,(if y=x then (1 : ℂ) else 0)*ψ x := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x c=false
        · simp [hx]
        · rw [hs x hx]; simp
      _ = ψ y := by simp
  · simp only [ite_true]
    change _=∑ x,(hadamardAt t).matrix y x*ψ x
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x c=true
    · simp [hx]
    · rw [hs x hx]; simp

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/MaskedPreparation.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness BitArithmetic BooleanNetwork

lemma rightProgram_state {p q : ℕ} (ops : List (Instruction q)) (x : Basis p) (ψ : State q) :
    (programMatrix (rightProgram p ops)).mulVec (encodeState (fun y => Fin.append x y) ψ)=
      encodeState (fun y => Fin.append x y) ((programMatrix ops).mulVec ψ) := by
  apply matrix_encodeState
  intro y
  simpa only [matrix_basisVector] using rightProgram_basis ops x y

lemma encode_append_supported {p q : ℕ} (x : Basis p) (ψ : State q) (i : Fin p) :
    Supported (fun y : Basis (p+q) => y (i.castAdd q)=x i)
      (encodeState (fun y => Fin.append x y) ψ) := by
  intro y hy
  apply encodeState_outside
  rintro ⟨z,rfl⟩
  exact hy (Fin.append_left _ _ _)

def maskGate (n : ℕ) (j : Fin n) : Instruction (n+n) :=
  controlledHadamardAt (j.castAdd n) (Fin.natAdd n j) (by
    intro hh
    have he := congrArg Fin.val hh
    simp only [Fin.val_castAdd,Fin.val_natAdd] at he
    have := j.isLt
    omega)

lemma maskGate_state (n : ℕ) (j : Fin n) (mask : Basis n) (ψ : State n) :
    (maskGate n j).matrix.mulVec (encodeState (fun y => Fin.append mask y) ψ)=
      encodeState (fun y => Fin.append mask y)
        (if mask j then (hadamardAt j).matrix.mulVec ψ else ψ) := by
  rw [maskGate,controlledHadamardAt_sector _ _ _ (mask j) _ (encode_append_supported mask ψ j)]
  cases hj : mask j
  · rfl
  · have he : (hadamardAt j).place (rightRegister n n)=hadamardAt (Fin.natAdd n j) := rfl
    have hh := rightProgram_state [hadamardAt j] mask ψ
    simpa only [rightProgram,List.map_cons,List.map_nil,he,programMatrix_singleton,ite_true] using hh

def maskedPrefix (n : ℕ) : (k : ℕ)→k ≤ n→List (Instruction (n+n))
  | 0,_ => []
  | k+1,h => maskedPrefix n k (by omega)++[maskGate n ⟨k,by omega⟩]

def selectedPrefix {n : ℕ} (mask : Basis n) : (k : ℕ)→k ≤ n→List (Instruction n)
  | 0,_ => []
  | k+1,h => selectedPrefix mask k (by omega)++
      (if mask ⟨k,by omega⟩ then [hadamardAt ⟨k,by omega⟩] else [])

lemma maskedPrefix_length (n k : ℕ) (h : k ≤ n) : (maskedPrefix n k h).length=k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [maskedPrefix,List.length_append,List.length_singleton,ih]

/-- The mask is ordinary retained input data. This equation is valid before
any measurement and for arbitrary coherent states in the target register. -/
lemma maskedPrefix_state (n k : ℕ) (h : k ≤ n) (mask : Basis n) (ψ : State n) :
    (programMatrix (maskedPrefix n k h)).mulVec (encodeState (fun y => Fin.append mask y) ψ)=
      encodeState (fun y => Fin.append mask y) ((programMatrix (selectedPrefix mask k h)).mulVec ψ) := by
  induction k with
  | zero => simp only [maskedPrefix,selectedPrefix,programMatrix_nil,Matrix.one_mulVec]
  | succ k ih =>
    rw [maskedPrefix,programMatrix_append,programMatrix_singleton,← Matrix.mulVec_mulVec,ih,
      maskGate_state,selectedPrefix,programMatrix_append,← Matrix.mulVec_mulVec]
    split_ifs <;> simp only [programMatrix_singleton,programMatrix_nil,Matrix.one_mulVec]

def prefixMask (n b : ℕ) : Basis n := fun i => decide (i.val<b)

lemma selectedPrefix_eq (n b k : ℕ) (h : k ≤ n) :
    selectedPrefix (prefixMask n b) k h=hadamardPrefix n (min k b) (by omega) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [selectedPrefix,ih]
    by_cases hk : k<b
    · have hk0 : min k b=k := Nat.min_eq_left (by omega)
      have hk1 : min (k+1) b=k+1 := Nat.min_eq_left (by omega)
      simp only [prefixMask,hk,decide_true,ite_true,hk0,hk1,hadamardPrefix]
    · have hk0 : min k b=b := Nat.min_eq_right (by omega)
      have hk1 : min (k+1) b=b := Nat.min_eq_right (by omega)
      simp only [prefixMask,hk,decide_false,Bool.false_eq_true,ite_false,hk0,hk1,List.append_nil]

/-- Uniformly n gates suffice for EVERY runtime width b<=n. Unlike n fair
bits, the upper n-b bits remain exactly zero, as required for the source list
success bound on small cofactors. -/
lemma maskedPrefix_zero (n b : ℕ) (hb : b ≤ n) :
    (programMatrix (maskedPrefix n n le_rfl)).mulVec
      (basisVector (Fin.append (prefixMask n b) (fun _ => false))) =
      encodeState (fun y => Fin.append (prefixMask n b) y)
        (fun y => if ∀ i : Fin n,b ≤ i.val→y i=false then (Real.sqrt 2:ℂ)⁻¹^b else 0) := by
  rw [← encodeState_basis (fun y => Fin.append (prefixMask n b) y) (fun _ => false),
    maskedPrefix_state,selectedPrefix_eq]
  simp only [Nat.min_eq_right hb,hadamardPrefix_zero]

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RuntimeListPreparation.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness BitArithmetic BooleanNetwork

/-- Compute ceil-log activation bits by bounded comparisons. The constant
2^i fits n bits, and the circuit is polynomial on invalid inputs too. -/
def listMaskNet (n : ℕ) : BooleanNetwork n n :=
  vector (fun i : Fin n => wordLt (wordConstant (BitVec.ofNat n (2^i.val))) (select id))

lemma listMaskNet_eval (n : ℕ) (m : Basis n) :
    (listMaskNet n).eval m=prefixMask n (Nat.clog 2 (bitsValue m).toNat) := by
  funext i
  have hp : 2^i.val<2^n := Nat.pow_lt_pow_right (by decide) i.isLt
  simp only [listMaskNet,eval_vector,wordLt_eval,wordConstant_eval,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hp,eval_select,Function.comp_id,prefixMask]
  congr 1
  exact propext (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).symm

lemma listMaskNet_count (n : ℕ) : (listMaskNet n).net.count ≤ n*(49*n+8) := by
  apply count_vector_le
  intro i
  have hh := wordLt_count (wordConstant (n:=n) (BitVec.ofNat n (2^i.val))) (select id)
  simp only [wordConstant_count,count_select,add_zero] at hh
  omega

def padBits {b n : ℕ} (_h : b ≤ n) (x : Basis b) : Basis n :=
  fun i => if hi : i.val<b then x ⟨i.val,hi⟩ else false

lemma padBits_at {b n : ℕ} (h : b ≤ n) (x : Basis b) (i : Fin b) :
    padBits h x (i.castLE h)=x i := by
  simp [padBits,i.isLt]

lemma padBits_injective {b n : ℕ} (h : b ≤ n) : Function.Injective (padBits h) := by
  intro x y hh
  funext i
  have he := congrFun hh (i.castLE h)
  simpa only [padBits_at] using he

lemma padBits_range {b n : ℕ} (h : b ≤ n) (y : Basis n) :
    y∈Set.range (padBits h) ↔ ∀ i : Fin n,b ≤ i.val→y i=false := by
  constructor
  · rintro ⟨x,rfl⟩ i hi
    simp [padBits,Nat.not_lt.mpr hi]
  · intro hh
    refine ⟨fun i => y (i.castLE h),?_⟩
    funext i
    unfold padBits
    split_ifs with hi
    · rfl
    · exact (hh i (by omega)).symm

lemma prefixFair_encode {b n : ℕ} (hb : b ≤ n) :
    (fun y : Basis n => if ∀ i : Fin n,b ≤ i.val→y i=false then (Real.sqrt 2:ℂ)⁻¹^b else 0)=
      encodeState (padBits hb) (fairState b) := by
  classical
  funext y
  by_cases hy : y∈Set.range (padBits hb)
  · obtain ⟨x,rfl⟩ := hy
    rw [encodeState_at _ (padBits_injective hb),ite_eq_left ((padBits_range hb _).mp ⟨x,rfl⟩)]
    rfl
  · rw [encodeState_outside _ _ y hy,ite_eq_right (fun hh => hy ((padBits_range hb y).mpr hh))]

/-- Runtime active-width preparation, stated as an exact physical program
column over the source's b=ceil(log₂m) fair state. -/
lemma maskedList_state (n : ℕ) (m : Basis n) :
    (programMatrix (maskedPrefix n n le_rfl)).mulVec
      (basisVector (Fin.append ((listMaskNet n).eval m) (fun _ => false)))=
      encodeState (fun y => Fin.append ((listMaskNet n).eval m)
        (padBits (Nat.clog_le_of_le_pow (bitsValue m).isLt.le) y))
        (fairState (Nat.clog 2 (bitsValue m).toNat)) := by
  rw [listMaskNet_eval,maskedPrefix_zero _ _ (Nat.clog_le_of_le_pow (bitsValue m).isLt.le),
    prefixFair_encode (Nat.clog_le_of_le_pow (bitsValue m).isLt.le),encodeState_comp]
  rfl

lemma padBits_value {b n : ℕ} (hb : b ≤ n) (x : Basis b) :
    (bitsValue (padBits hb x)).toNat=(bitsValue x).toNat := by
  have he : bitsValue (padBits hb x)=(bitsValue x).setWidth n := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [show (bitsValue (padBits hb x)).getLsbD i=padBits hb x ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
      BitVec.getLsbD_setWidth]
    simp only [hi,decide_true,Bool.true_and,padBits]
    split_ifs with hib
    · exact (bitsValue_bit x ⟨i,hib⟩).symm
    · exact (BitVec.getLsbD_of_ge _ _ (by omega)).symm
  rw [he,setWidth_toNat_of_le hb]

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TransitionWords.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials

namespace TransitionWords

/-- K n-bit words in consecutive little-endian fields, followed by one zero
word. This fits exactly the source's W=n(K+1) output cap. -/
def encode {n K : ℕ} (a : Fin K→Basis n) : Basis (n*(K+1)) := fun i =>
  let j := finProdFinEquiv.symm (Fin.cast (Nat.mul_comm _ _) i)
  if h : j.1.val<K then a ⟨j.1.val,h⟩ j.2 else false

def read {n K : ℕ} (x : Basis (n*(K+1))) (i : Fin K) : Basis n := fun j =>
  x (Fin.cast (Nat.mul_comm _ _) (finProdFinEquiv (i.castSucc,j)))

lemma read_encode {n K : ℕ} (a : Fin K→Basis n) (i : Fin K) : read (encode a) i=a i := by
  funext j
  simp only [read,encode,Fin.cast_cast,Fin.cast_eq_self,Equiv.symm_apply_apply,Fin.val_castSucc]
  rw [dite_eq_left i.isLt]

lemma encode_injective (n K : ℕ) : Function.Injective (@encode n K) := by
  intro a b hh
  funext i
  have he := congrArg (fun x => read x i) hh
  simpa only [read_encode] using he

lemma pow_width_le (n K : ℕ) : 2^n ≤ 2^(n*(K+1)) := by
  apply Nat.pow_le_pow_right (by decide : 1≤2)
  nlinarith

end TransitionWords

namespace ListSlots

abbrev K (n : ℕ) := n^5
abbrev Ordinary (n m : ℕ) := Fin (K n)→Basis (Nat.clog 2 m)
abbrev Result (n m : ℕ) := Completion.Raw (Ordinary n m) (Completion.transitionWidth n)
  (2*n) (n*K n)

noncomputable def fresh (n m : ℕ) : Result n m→ℂ :=
  Completion.fresh (tensorState (fairState (Nat.clog 2 m)) (K n))
    (Completion.transitionWidth n) (2*n) (n*K n)

def ordinary {n m : ℕ} (hb : m < 2^n) (x : Ordinary n m) : Basis (Completion.transitionWidth n) :=
  TransitionWords.encode (fun i => padBits (Nat.clog_le_of_le_pow hb.le) (x i))

noncomputable def canonical {n m : ℕ} (hm : m ≠ 0) (hb : m < 2^n) (p₀ : Component m) :
    Basis (Completion.transitionWidth n) := ordinary hb (canonicalList hm p₀ (K n))

noncomputable def passed {n m : ℕ} (hm : m ≠ 0) (hb : m < 2^n) (p₀ : Component m) : Result n m→Prop :=
  Completion.passed (GoodList hm hb p₀ (K n)) (canonical hm hb p₀)
    (Completion.listSuccess m n (K n)) (Completion.target n)

def output {n m : ℕ} (hb : m < 2^n) : Result n m→Basis (Completion.transitionWidth n) :=
  Completion.output (ordinary hb)

noncomputable def GoodOutput {n m : ℕ} (hm : m ≠ 0) (hb : m < 2^n) (p₀ : Component m)
    (y : Basis (Completion.transitionWidth n)) : Prop :=
  ∃ (i : Fin (K n)) (u : (ZMod m)ˣ),
    (bitsValue (TransitionWords.read y i)).toNat=(u : ZMod m).val ∧ FavorableUnit hm hb p₀ u

lemma ordinary_good {n m : ℕ} (hm : m ≠ 0) (hb : m < 2^n) (p₀ : Component m)
    (x : Ordinary n m) (hh : GoodList hm hb p₀ (K n) x) :
    GoodOutput hm hb p₀ (ordinary hb x) := by
  obtain ⟨i,u,hu,hf⟩ := hh
  refine ⟨i,u,?_,hf⟩
  change (bitsValue (TransitionWords.read (TransitionWords.encode _) i)).toNat=_
  rw [TransitionWords.read_encode,padBits_value]
  exact hu.symm

lemma canonical_good {n m : ℕ} (hn : 128 ≤ n) (hm : m ≠ 0) (hb : m < 2^n) (hodd : Odd m)
    (p₀ p₁ : Component m) (hne : p₁≠p₀) : GoodOutput hm hb p₀ (canonical hm hb p₀) := by
  apply ordinary_good
  exact canonicalList_good hm hb hodd p₀ p₁ hne (pow_pos (by omega) _)

lemma fresh_normalized (n m : ℕ) : ∑ r,Complex.normSq (fresh n m r)=1 :=
  Completion.fresh_normalized _ _ _ _ (tensor_normalized _ _ (fairState_normalized _))

lemma passed_mass {n m : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hb : m < 2^n) (hodd : Odd m)
    (p₀ p₁ : Component m) (hne : p₁≠p₀) :
    outcomeMass (passed (by omega : m ≠ 0) hb p₀) (fresh n m)=(Completion.target n:ℝ) :=
  Completion.list_passed_mass hn hm hb hodd p₀ p₁ hne (canonical (by omega) hb p₀)

lemma passed_good {n m : ℕ} (hn : 128 ≤ n) (hm : m ≠ 0) (hb : m < 2^n) (hodd : Odd m)
    (p₀ p₁ : Component m) (hne : p₁≠p₀) (r : Result n m) (hp : passed hm hb p₀ r) :
    GoodOutput hm hb p₀ (output hb r) := by
  rcases hp with hp | hp
  · rw [output,Completion.output,ite_eq_right hp.1]
    exact ordinary_good hm hb p₀ _ hp.2.1
  · rw [output,Completion.output,ite_eq_left hp.1,hp.2.1]
    exact canonical_good hn hm hb hodd p₀ p₁ hne

end ListSlots
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TransitionNetworks.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork
namespace TransitionWords

/-- Each field is wired into its fixed source layout, and the final unused word
is explicitly zeroed. The cap K and all placements are independent of inputs. -/
def encodeNet {k n K : ℕ} (f : Fin K → BooleanNetwork k n) : BooleanNetwork k (n*(K+1)) :=
  vector (fun i =>
    let j := finProdFinEquiv.symm (Fin.cast (Nat.mul_comm _ _) i)
    if h : j.1.val<K then (f ⟨j.1.val,h⟩).rewire (fun _ => j.2) else constant false)

lemma encodeNet_eval {k n K : ℕ} (f : Fin K → BooleanNetwork k n) (x : Basis k) :
    (encodeNet f).eval x=encode (fun i => (f i).eval x) := by
  funext i
  rw [encodeNet,eval_vector]
  dsimp only [encode]
  split_ifs <;> simp only [eval_rewire,Function.comp_apply,eval_constant]

lemma encodeNet_count {k n K c : ℕ} (f : Fin K → BooleanNetwork k n)
    (hf : ∀ i,(f i).net.count ≤ c) : (encodeNet f).net.count ≤ n*(K+1)*(c+1) := by
  apply count_vector_le
  intro i
  dsimp only
  split_ifs with h
  · rw [dite_eq_left h,count_rewire]
    exact (hf _).trans (Nat.le_add_right _ _)
  · rw [dite_eq_right h]
    change 1 ≤ c+1
    omega

end TransitionWords
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ListSamplerCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.ListSampler
open Exactness BitArithmetic BooleanNetwork

abbrev work (n : ℕ) := n*(49*n+8)
abbrev width (n : ℕ) := n+n+(n+work n)

def word {n : ℕ} (m mask y : Basis n) : Basis (width n) := fun i =>
  if h₀ : i.val<n then m ⟨i.val,h₀⟩ else
  if h₁ : i.val<n+n then mask ⟨i.val-n,by omega⟩ else
  if h₂ : i.val<n+n+n then y ⟨i.val-(n+n),by omega⟩ else false

lemma word_input {n : ℕ} (m mask y : Basis n) (i : Fin n) :
    word m mask y ⟨i.val,by have := i.isLt; dsimp [width]; omega⟩=m i := by
  simp only [word,i.isLt,dite_eq_left]

lemma word_mask {n : ℕ} (m mask y : Basis n) (i : Fin n) :
    word m mask y ⟨n+i.val,by have := i.isLt; dsimp [width]; omega⟩=mask i := by
  have h₀ : ¬n+i.val<n := by omega
  have h₁ : n+i.val<n+n := by omega
  simp only [word,dite_eq_right h₀,dite_eq_left h₁,Nat.add_sub_cancel_left]

lemma word_sample {n : ℕ} (m mask y : Basis n) (i : Fin n) :
    word m mask y ⟨n+n+i.val,by have := i.isLt; dsimp [width]; omega⟩=y i := by
  have h₀ : ¬n+n+i.val<n := by omega
  have h₁ : ¬n+n+i.val<n+n := by omega
  have h₂ : n+n+i.val<n+n+n := by omega
  simp only [word,dite_eq_right h₀,dite_eq_right h₁,dite_eq_left h₂,Nat.add_sub_cancel_left]

lemma word_work {n : ℕ} (m mask y : Basis n) (i : Fin (width n)) (hi : n+n+n ≤ i.val) :
    word m mask y i=false := by
  simp only [word,dite_eq_right (show ¬i.val<n by omega),dite_eq_right (show ¬i.val<n+n by omega),
    dite_eq_right (Nat.not_lt.mpr hi)]

lemma packed_word {n : ℕ} (m mask : Basis n) :
    packed (n+work n) m mask=word m mask (fun _ => false) := by
  funext i
  unfold packed word
  split_ifs <;> rfl

def maskRegister (n : ℕ) : Register (n+n) (width n) where
  toFun i := ⟨n+i.val,by have := i.isLt; dsimp [width]; omega⟩
  inj' := by
    intro i j hh
    apply Fin.ext
    have h := congrArg Fin.val hh
    dsimp at h
    omega

lemma maskRegister_val (n : ℕ) (i : Fin (n+n)) : (maskRegister n i).val=n+i.val := rfl

lemma word_register {n : ℕ} (m mask y : Basis n) :
    word m mask y ∘ maskRegister n=Fin.append mask y := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact (word_mask m mask y j).trans (Fin.append_left _ _ _).symm
  · have he : maskRegister n (Fin.natAdd n j)=⟨n+n+j.val,by have := j.isLt; dsimp [width]; omega⟩ :=
      Fin.ext (by simp only [maskRegister_val,Fin.val_natAdd]; omega)
    rw [Function.comp_apply,he,word_sample,Fin.append_right]

lemma word_replace {n : ℕ} (m mask y mask' y' : Basis n) :
    (maskRegister n).replace (word m mask y) (Fin.append mask' y')=word m mask' y' := by
  funext i
  by_cases hi₀ : i.val<n
  · have ho : ∀ j,maskRegister n j≠i := by
      intro j hh
      have h := congrArg Fin.val hh
      rw [maskRegister_val] at h
      omega
    rw [Register.replace_outside _ _ _ ⟨i,ho⟩]
    simp only [word,hi₀,dite_eq_left]
  · by_cases hi₁ : i.val<n+n+n
    · let j : Fin (n+n) := ⟨i.val-n,by omega⟩
      have he : maskRegister n j=i := Fin.ext (by rw [maskRegister_val]; dsimp [j]; omega)
      rw [←he,Register.replace_inside]
      exact (congrFun (word_register m mask' y') j).symm
    · have ho : ∀ j,maskRegister n j≠i := by
        intro j hh
        have h := congrArg Fin.val hh
        rw [maskRegister_val] at h
        have := j.isLt
        omega
      rw [Register.replace_outside _ _ _ ⟨i,ho⟩]
      change word m mask y i=word m mask' y' i
      rw [word_work _ _ _ _ (by omega),word_work _ _ _ _ (by omega)]

/-- A single family (depending only on n) prepares the manuscript's exact
runtime-b(n,m) fair sample. No Hadamard is chosen by a metalevel value of m. -/
def circuit (n : ℕ) : List (Instruction (width n)) :=
  oracleOn (listMaskNet n) (show (listMaskNet n).net.count ≤ n+work n from
    (listMaskNet_count n).trans (Nat.le_add_left _ _)) ++
  (maskedPrefix n n le_rfl).map (Instruction.place (maskRegister n))

lemma circuit_length (n : ℕ) : (circuit n).length ≤ 4*work n+3*n := by
  have h := oracleOn_length (listMaskNet n) (show (listMaskNet n).net.count ≤ n+work n from
    (listMaskNet_count n).trans (Nat.le_add_left _ _))
  have hc : (listMaskNet n).net.count ≤ work n := listMaskNet_count n
  simp only [circuit,List.length_append,List.length_map,maskedPrefix_length]
  omega

lemma circuit_state (n : ℕ) (m : Basis n) :
    (programMatrix (circuit n)).mulVec
      (basisVector (word m (fun _ => false) (fun _ => false)))=
    encodeState (fun y => word m ((listMaskNet n).eval m)
      (padBits (Nat.clog_le_of_le_pow (bitsValue m).isLt.le) y))
      (fairState (Nat.clog 2 (bitsValue m).toNat)) := by
  rw [circuit,programMatrix_append,←Matrix.mulVec_mulVec,←packed_word,
    oracleOn_basis]
  simp only [Bool.false_xor]
  rw [packed_word,Register.placed_basis_state,word_register,maskedList_state,
    encodeState_comp]
  congr 1
  funext y
  exact word_replace _ _ _ _ _

lemma word_injective {n : ℕ} (m mask : Basis n) : Function.Injective (word m mask) := by
  intro x y h
  funext i
  have he := congrFun h ⟨n+n+i.val,by have := i.isLt; dsimp [width]; omega⟩
  simpa only [word_sample] using he

/-- Born events in the actual prepared register are exactly the b(n,m)-bit
fair events, retaining the original input, mask and all clean work wires. -/
lemma circuit_mass (n : ℕ) (m : Basis n) (P : Basis (width n)→Prop) :
    outcomeMass P ((programMatrix (circuit n)).mulVec
      (basisVector (word m (fun _ => false) (fun _ => false))))=
    outcomeMass (fun y => P (word m ((listMaskNet n).eval m)
      (padBits (Nat.clog_le_of_le_pow (bitsValue m).isLt.le) y)))
      (fairState (Nat.clog 2 (bitsValue m).toNat)) := by
  rw [circuit_state]
  exact outcomeMass_encode _ ((word_injective _ _).comp (padBits_injective _)) _ _

end ExactQuantumFactoring.ListSampler


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalListSlots.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials
namespace PhysicalListSlots

abbrev ordinaryWidth (n : ℕ) := tensorWidth (ListSampler.width n) (n^5)
abbrev Result (n : ℕ) := Completion.Raw (Basis (ordinaryWidth n))
  (Completion.transitionWidth n) (2*n) (n*n^5)
noncomputable instance resultFintype (n : ℕ) : Fintype (Result n) := inferInstance

def sampleRead {n : ℕ} (x : Basis (ListSampler.width n)) : Basis n := fun i =>
  x ⟨n+n+i.val,by have := i.isLt; dsimp [ListSampler.width]; omega⟩
lemma sampleRead_word {n : ℕ} (m mask y : Basis n) : sampleRead (ListSampler.word m mask y)=y := by
  funext i
  exact ListSampler.word_sample _ _ _ _

def ordinary {n : ℕ} (x : Basis (ordinaryWidth n)) : Basis (Completion.transitionWidth n) :=
  TransitionWords.encode (fun i => sampleRead ((tensorLayout _ (n^5)).symm x i))

def ordinaryProgram (n : ℕ) : List (Instruction (ordinaryWidth n)) :=
  tensorProgram (ListSampler.circuit n) (n^5)

def ordinaryZero {n : ℕ} (m : Basis n) : Basis (ordinaryWidth n) :=
  tensorLayout _ (n^5) (fun _ => ListSampler.word m (fun _ => false) (fun _ => false))

noncomputable def ordinaryState {n : ℕ} (m : Basis n) : State (ordinaryWidth n) :=
  (programMatrix (ordinaryProgram n)).mulVec (basisVector (ordinaryZero m))

lemma single_normalized {n : ℕ} (m : Basis n) :
    ∑ x,Complex.normSq ((programMatrix (ListSampler.circuit n)).mulVec
      (basisVector (ListSampler.word m (fun _ => false) (fun _ => false))) x)=1 := by
  have hh := ListSampler.circuit_mass n m (fun _ => True)
  simp only [outcomeMass,↓reduceIte] at hh
  exact hh.trans (fairState_normalized _)

lemma ordinary_normalized {n : ℕ} (m : Basis n) : ∑ x,Complex.normSq (ordinaryState m x)=1 := by
  have hh := tensorProgram_event (ListSampler.circuit n) (n^5)
    (ListSampler.word m (fun _ => false) (fun _ => false)) (fun _ => True)
  change outcomeMass (fun _ => True) (ordinaryState m)=_ at hh
  simp only [outcomeMass,↓reduceIte] at hh
  exact hh.trans (tensor_normalized _ _ (single_normalized m))

lemma ordinary_good_mass {n : ℕ} (m : Basis n) (hm : (bitsValue m).toNat≠0)
    (hodd : Odd (bitsValue m).toNat) (p₀ : Component (bitsValue m).toNat) :
    outcomeMass (ListSlots.GoodOutput hm (bitsValue m).isLt p₀ ∘ ordinary) (ordinaryState m)=
      (Completion.listSuccess (bitsValue m).toNat n (n^5):ℝ) := by
  have he : ListSlots.GoodOutput hm (bitsValue m).isLt p₀ ∘ ordinary =
      (fun x : Fin (n^5)→Basis (ListSampler.width n) => ∃ i,
        FavorableBits hm (bitsValue m).isLt p₀ n (sampleRead (x i))) ∘ (tensorLayout _ (n^5)).symm := by
    funext x
    apply propext
    simp only [Function.comp_def,ListSlots.GoodOutput,ordinary,TransitionWords.read_encode,FavorableBits]
    exact ⟨fun ⟨i,u,h,hf⟩ => ⟨i,u,h.symm,hf⟩,fun ⟨i,u,h,hf⟩ => ⟨i,u,h.symm,hf⟩⟩
  rw [he,ordinaryState,ordinaryProgram,ordinaryZero,tensorProgram_event]
  rw [tensor_some_mass _ _ (fun x => FavorableBits hm (bitsValue m).isLt p₀ n (sampleRead x)) (single_normalized m)]
  rw [ListSampler.circuit_mass]
  have hs : (fun y => FavorableBits hm (bitsValue m).isLt p₀ n
      (sampleRead (ListSampler.word m ((listMaskNet n).eval m)
        (padBits (Nat.clog_le_of_le_pow (bitsValue m).isLt.le) y)))) =
      FavorableBits hm (bitsValue m).isLt p₀ (Nat.clog 2 (bitsValue m).toNat) := by
    funext y
    simp only [sampleRead_word,FavorableBits,padBits_value]
  rw [hs,favorableBits_mass hm (bitsValue m).isLt hodd p₀ (Nat.le_pow_clog (by decide) _)]
  simp only [Completion.listSuccess,Rat.cast_sub,Rat.cast_one,Rat.cast_pow,Rat.cast_div,
    Rat.cast_natCast,Rat.cast_ofNat]

noncomputable def fresh {n : ℕ} (m : Basis n) : Result n→ℂ :=
  Completion.fresh (ordinaryState m) (Completion.transitionWidth n) (2*n) (n*n^5)
noncomputable def passed {n : ℕ} (m : Basis n) (hm : (bitsValue m).toNat≠0)
    (p₀ : Component (bitsValue m).toNat) : Result n→Prop :=
  Completion.passed (ListSlots.GoodOutput hm (bitsValue m).isLt p₀ ∘ ordinary)
    (ListSlots.canonical hm (bitsValue m).isLt p₀)
    (Completion.listSuccess (bitsValue m).toNat n (n^5)) (Completion.target n)
def output {n : ℕ} : Result n→Basis (Completion.transitionWidth n) := Completion.output ordinary

lemma fresh_normalized {n : ℕ} (m : Basis n) : ∑ r,Complex.normSq (fresh m r)=1 :=
  Completion.fresh_normalized _ _ _ _ (ordinary_normalized m)

lemma passed_mass {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (hodd : Odd (bitsValue m).toNat) (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀) :
    outcomeMass (passed m (by omega) p₀) (fresh m)=(Completion.target n:ℝ) := by
  have hl := Completion.listSuccess_lower hn hm (bitsValue m).isLt hodd p₀ p₁ hne
  have hu := Completion.listSuccess_le_one (by omega) (bitsValue m).isLt hodd p₀ (n^5)
  have hε : (1:ℚ)/(2:ℚ)^(2*n)<1 := by
    apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)
  apply Completion.passed_mass _ _ _ _ _ (ordinary_normalized m)
    (ordinary_good_mass m (by omega) hodd p₀)
    (Completion.listSuccess_at (bitsValue m).isLt.le _) (Completion.target_at n)
  · unfold Completion.coinBits Completion.transitionWidth; omega
  · linarith
  · exact hu
  · omega
  · exact Completion.target_pos (by omega)
  · exact Completion.target_le_ordinary (by omega) hl

lemma passed_good {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : (bitsValue m).toNat≠0)
    (hodd : Odd (bitsValue m).toNat) (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀)
    (r : Result n) (hp : passed m hm p₀ r) : ListSlots.GoodOutput hm (bitsValue m).isLt p₀ (output r) :=
  Completion.passed_good ordinary _ _ _ _
    (ListSlots.canonical_good hn hm (bitsValue m).isLt hodd p₀ p₁ hne) r hp

abbrev width (n : ℕ) := 2*n+(ordinaryWidth n+(Completion.transitionWidth n+
  Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5)))
def layout (n : ℕ) : Result n≃Basis (width n) := Completion.layout _ _ _ _
def program (n : ℕ) : List (Instruction (width n)) :=
  Completion.program (ordinaryProgram n) (Completion.transitionWidth n) (2*n) (n*n^5)
def zero {n : ℕ} (m : Basis n) : Result n :=
  ((fun _ => false),ordinaryZero m,(fun _ => false),(fun _ => false))

lemma program_entry {n : ℕ} (m : Basis n) (r : Result n) :
    (programMatrix (program n)).mulVec (basisVector (layout n (zero m))) (layout n r)=fresh m r :=
  Completion.program_entry _ _ _ _ _ _
lemma program_state {n : ℕ} (m : Basis n) :
    (programMatrix (program n)).mulVec (basisVector (layout n (zero m)))=encodeState (layout n) (fresh m) := by
  funext x
  obtain ⟨r,rfl⟩ := (layout n).surjective x
  rw [program_entry,encodeState_at _ (layout n).injective]

lemma program_length (n : ℕ) : (program n).length ≤
    n^5*(4*ListSampler.work n+3*n)+2*n+Completion.transitionWidth n+
      Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5) := by
  rw [program,Completion.program_length,ordinaryProgram,tensorProgram_length]
  have hh := Nat.mul_le_mul_left (n^5) (ListSampler.circuit_length n)
  omega

end PhysicalListSlots
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalListNetworks.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace PhysicalListSlots

def sampleNet (n : ℕ) : BooleanNetwork (ListSampler.width n) n :=
  select (fun i => ⟨n+n+i.val,by have := i.isLt; dsimp [ListSampler.width]; omega⟩)
lemma sampleNet_eval {n : ℕ} (x : Basis (ListSampler.width n)) : (sampleNet n).eval x=sampleRead x := rfl

def ordinaryNet (n : ℕ) : BooleanNetwork (ordinaryWidth n) (Completion.transitionWidth n) :=
  TransitionWords.encodeNet (fun i : Fin (n^5) => (tensorSelect (ListSampler.width n) (n^5) i).comp (sampleNet n))
lemma ordinaryNet_eval {n : ℕ} (x : Basis (ordinaryWidth n)) : (ordinaryNet n).eval x=ordinary x := by
  change (TransitionWords.encodeNet _).eval x=TransitionWords.encode _
  rw [TransitionWords.encodeNet_eval]
  congr 1
  funext i
  rw [eval_comp,tensorSelect_inverse,sampleNet_eval]
lemma ordinaryNet_count (n : ℕ) : (ordinaryNet n).net.count ≤ Completion.transitionWidth n := by
  have h := TransitionWords.encodeNet_count
    (fun i : Fin (n^5) => (tensorSelect (ListSampler.width n) (n^5) i).comp (sampleNet n))
    (c:=0) (by intro i; simp only [count_comp,tensorSelect,sampleNet,count_select]; omega)
  change (TransitionWords.encodeNet (fun i : Fin (n^5) =>
    (tensorSelect (ListSampler.width n) (n^5) i).comp (sampleNet n))).net.count ≤ n*(n^5+1)
  simpa only [Nat.zero_add,Nat.mul_one] using h

def outputNet (n : ℕ) : BooleanNetwork (width n) (Completion.transitionWidth n) :=
  Completion.outputNet (ordinaryNet n) (2*n) (n*n^5)
lemma outputNet_eval {n : ℕ} (r : Result n) :
    (outputNet n).eval (layout n r)=output r := by
  change (Completion.outputNet _ _ _).eval (Completion.layout _ _ _ _ r)=_
  rw [Completion.outputNet_eval]
  unfold output Completion.output
  simp only [ordinaryNet_eval]
lemma outputNet_count (n : ℕ) : (outputNet n).net.count ≤
    8*Completion.transitionWidth n+194*n+21 := by
  have h := Completion.outputNet_count (ordinaryNet n) (2*n) (n*n^5)
  have hh := ordinaryNet_count n
  change (Completion.outputNet _ _ _).net.count ≤ _
  nlinarith

/-- Copy the runtime modulus into each literal sampler block; all other input
cells are zero. Only fixed wire placements and constants are used. -/
def singleZeroNet (n : ℕ) : BooleanNetwork n (ListSampler.width n) :=
  vector (fun i => if h : i.val<n then bit ⟨i.val,h⟩ else constant false)
lemma singleZeroNet_eval {n : ℕ} (m : Basis n) :
    (singleZeroNet n).eval m=ListSampler.word m (fun _=>false) (fun _=>false) := by
  funext i
  rw [singleZeroNet,eval_vector]
  by_cases h : i.val<n
  · rw [dite_eq_left h,eval_bit]
    unfold ListSampler.word
    rw [dite_eq_left h]
  · rw [dite_eq_right h,eval_constant]
    unfold ListSampler.word
    split_ifs <;> rfl
lemma singleZeroNet_count (n : ℕ) : (singleZeroNet n).net.count ≤ ListSampler.width n := by
  unfold singleZeroNet
  apply (count_vector_le _ (c:=1) ?_).trans (by omega)
  intro i
  by_cases h : i.val<n
  · rw [dite_eq_left h,count_bit]; omega
  · rw [dite_eq_right h,count_constant]

def ordinaryZeroNet (n : ℕ) : BooleanNetwork n (ordinaryWidth n) :=
  tensorNetwork (fun _ : Fin (n^5) => singleZeroNet n)
lemma ordinaryZeroNet_eval {n : ℕ} (m : Basis n) : (ordinaryZeroNet n).eval m=ordinaryZero m := by
  rw [ordinaryZeroNet,tensorNetwork_eval,ordinaryZero]
  congr 1
  funext i
  exact singleZeroNet_eval m
lemma ordinaryZeroNet_count (n : ℕ) : (ordinaryZeroNet n).net.count ≤ n^5*ListSampler.width n :=
  tensorNetwork_count_le _ (fun _ => singleZeroNet_count n)

def initialNet (n : ℕ) : BooleanNetwork n (width n) :=
  Completion.initialNet (ordinaryZeroNet n) (Completion.transitionWidth n) (2*n) (n*n^5)
lemma initialNet_eval {n : ℕ} (m : Basis n) : (initialNet n).eval m=layout n (zero m) := by
  rw [initialNet,Completion.initialNet_eval,ordinaryZeroNet_eval]
  rfl
lemma initialNet_count (n : ℕ) : (initialNet n).net.count ≤ n^5*ListSampler.width n+
    2*n+Completion.transitionWidth n+Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5) := by
  rw [initialNet,Completion.initialNet_count]
  have h := ordinaryZeroNet_count n
  omega

abbrev work (n : ℕ) := (initialNet n).net.count
abbrev launchWidth (n : ℕ) := n+width n+work n
/-- Length-uniform placement of the completed runtime-modulus list sampler. -/
def launch (n : ℕ) : List (Instruction (launchWidth n)) :=
  preparedOracle (initialNet n) le_rfl (program n)
lemma launch_state {n : ℕ} (m : Basis n) :
    (programMatrix (launch n)).mulVec (basisVector (packed (work n) m (fun _=>false)))=
      encodeState (fun r : Result n => packed (work n) m (layout n r)) (fresh m) := by
  rw [launch,preparedOracle_basis,initialNet_eval,program_state,encodeState_comp]
  rfl
lemma launch_length (n : ℕ) : (launch n).length ≤
    4*work n+2*width n+(program n).length := preparedOracle_length _ _ _

end PhysicalListSlots
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ProvidedSplits.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open FactorController

/-- A guarded scan. Invalid proposals never change the arithmetic product
invariant of the factoring controller. -/
def firstProper (m : ℕ) : List ℕ→ℕ
  | [] => 0
  | d::ds => if ProperDivisor m d then d else firstProper m ds

lemma firstProper_of_mem {m d : ℕ} {ds : List ℕ} (hd : d∈ds)
    (hp : ProperDivisor m d) : ProperDivisor m (firstProper m ds) := by
  induction ds with
  | nil => simp at hd
  | cons a ds ih =>
    simp only [firstProper]
    split_ifs with ha
    · exact ha
    · rcases List.mem_cons.mp hd with rfl | ht
      · exact False.elim (ha hp)
      · exact ih ht

lemma firstProper_sound {m : ℕ} (ds : List ℕ) :
    firstProper m ds=0 ∨ ProperDivisor m (firstProper m ds) := by
  induction ds with
  | nil => exact Or.inl rfl
  | cons d ds ih =>
    simp only [firstProper]
    split_ifs with hd
    · exact Or.inr hd
    · exact ih

def orderSplit (m : ℕ) (ars : List (ℕ×ℕ)) : ℕ :=
  firstProper m (ars.map (fun ar => candidateDivisor m ar.1 ar.2))

/-- `ars` are the supplied list entries paired with the recorded order outputs.
When the good list entry has its true order, the actual guarded scan splits. -/
lemma orderSplit_good {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (hodd : Odd m)
    (p₀ : Component m) (ars : List (ℕ×ℕ))
    (u : (ZMod m)ˣ) (hf : FavorableUnit (by omega : m≠0) hb p₀ u)
    (hmem : ((u : ZMod m).val,orderOf u)∈ars) : ProperDivisor m (orderSplit m ars) := by
  let : NeZero m := ⟨by omega⟩
  have hh := favorable_split hm hb hodd p₀ u hf
  have he : candidateDivisor m (u : ZMod m).val (orderOf u)=splitGcd u :=
    candidateDivisor_trueOrder hm u (ZMod.natCast_zmod_val _) hh.1
  apply firstProper_of_mem (List.mem_map.mpr ⟨_,hmem,rfl⟩)
  exact he ▸ hh.2

/-- Root searches are clocked by the ORIGINAL input length n. -/
def rootProposals (m n : ℕ) : List ℕ :=
  (List.range (n+1)).map (fun e => Primality.boundedRoot m e n)

def rootSplit (m n : ℕ) : ℕ := firstProper m (rootProposals m n)

lemma perfectPower_proper {m b e : ℕ} (hb : 2 ≤ b) (he : 2 ≤ e) (hp : b^e=m) :
    ProperDivisor m b := by
  rcases e with _ | e
  · omega
  have he0 : 0 < e := by omega
  have hpow : 1 < b^e := by exact one_lt_pow₀ (by omega) (by omega)
  refine ⟨by omega,?_,?_⟩
  · rw [← hp,pow_succ]
    nlinarith
  · rw [← hp,pow_succ]
    exact dvd_mul_left b (b^e)

lemma rootSplit_good {m n : ℕ} (hb : m < 2^n) (hp : Primality.PerfectPower m) :
    ProperDivisor m (rootSplit m n) := by
  obtain ⟨b,e,hb2,he,hpow⟩ := hp
  have hen := Primality.perfectPower_exponent_lt hb hb2 hpow
  have hroot := Primality.boundedRoot_pow_eq (by omega : 0 < e) hb hpow
  apply firstProper_of_mem (d:=b)
  · apply List.mem_map.mpr
    refine ⟨e,List.mem_range.mpr (by omega),hroot⟩
  · exact perfectPower_proper hb2 he hpow

def suppliedDivisor (m n : ℕ) (ars : List (ℕ×ℕ)) : ℕ :=
  if 2∣m then 2 else
  if ProperDivisor m (rootSplit m n) then rootSplit m n else orderSplit m ars

lemma suppliedDivisor_good {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (hprime : ¬m.Prime)
    (ars : List (ℕ×ℕ))
    (hgood : Odd m → ¬Primality.PerfectPower m →
      ∃ (p₀ : Component m) (u : (ZMod m)ˣ),
        FavorableUnit (by omega : m≠0) hb p₀ u ∧ ((u : ZMod m).val,orderOf u)∈ars) :
    ProperDivisor m (suppliedDivisor m n ars) := by
  simp only [suppliedDivisor]
  split_ifs with htwo hroot
  · refine ⟨by decide,?_,htwo⟩
    by_contra h
    have : m=2 := by omega
    exact hprime (this ▸ Nat.prime_two)
  · exact hroot
  · have hodd : Odd m := Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using htwo)
    have hpow : ¬Primality.PerfectPower m := fun hp => hroot (rootSplit_good hb hp)
    obtain ⟨p₀,u,hf,hu⟩ := hgood hodd hpow
    exact orderSplit_good hm hb hodd p₀ ars u hf hu

/-- The all-good node completion used in the source. The chosen divisor is now
an actual even/root/order scan, not an assumed proper-divisor oracle. -/
theorem supplied_node_complete {N n : ℕ} (hN : 2 ≤ N) (hb : N < 2^n)
    (outputs : ℕ→ℕ→List (ℕ×ℕ))
    (hgood : ∀ i m (hm : 2 ≤ m) (hle : m ≤ N), ¬m.Prime → Odd m →
      ¬Primality.PerfectPower m →
      ∃ (p₀ : Component m) (u : (ZMod m)ˣ),
        FavorableUnit (by omega : m≠0) (hle.trans_lt hb) p₀ u ∧
        ((u : ZMod m).val,orderOf u)∈outputs i m) :
    ∃ ps, run (fun i m => suppliedDivisor m n (outputs i m)) (2*n) 0 [N]=some ps ∧
      (∀ p∈ps,p.Prime) ∧ ps.prod=N ∧ ps.length < n := by
  apply bounded_node_complete hN hb
  intro i m hm hle hp
  exact suppliedDivisor_good hm (hle.trans_lt hb) hp _ (hgood i m hm hle hp)

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CompletedSplit.lean =====
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

namespace OrderSlots

lemma unitOrder_eq {n : ℕ} (a m : Basis n) (u : (ZMod (bitsValue m).toNat)ˣ)
    (hlt : (bitsValue a).toNat < (bitsValue m).toNat)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat)) :
    unitOrder a m=orderOf u := by
  classical
  have hu : IsUnit ((bitsValue a).toNat : ZMod (bitsValue m).toNat) := ha.symm ▸ u.isUnit
  have hva : Usable a m := ⟨hlt,hu⟩
  rw [unitOrder,dite_eq_left hva]
  congr 1
  apply Units.ext
  exact hu.unit_spec.trans ha

lemma passed_value {n : ℕ} (a m : Basis n) (hm : 2 ≤ (bitsValue m).toNat) (r : Result n)
    (hp : passed a m r) : (bitsValue (output a m r)).toNat=unitOrder a m := by
  rw [passed_output a m r hp,canonical,natBasis_value,Nat.mod_eq_of_lt]
  exact (unitOrder_lt a m hm).trans_le (TransitionWords.pow_width_le n (n^5))

lemma passed_order {n : ℕ} (a m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (u : (ZMod (bitsValue m).toNat)ˣ)
    (hlt : (bitsValue a).toNat < (bitsValue m).toNat)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (r : Result n) (hp : passed a m r) : (bitsValue (output a m r)).toNat=orderOf u := by
  rw [passed_value a m hm r hp,unitOrder_eq a m u hlt ha]

end OrderSlots

namespace CompletedSplit

abbrev Raw {n : ℕ} (m : Basis n) :=
  ListSlots.Result n (bitsValue m).toNat × (Fin (n^5)→OrderSlots.Result n)

noncomputable instance rawFintype {n : ℕ} (m : Basis n) : Fintype (Raw m) := inferInstance

def bases {n : ℕ} (m : Basis n) (r : ListSlots.Result n (bitsValue m).toNat) : Fin (n^5)→Basis n :=
  TransitionWords.read (ListSlots.output (bitsValue m).isLt r)

/-- Actual next fresh registers depend only on the completed list output,
including its rare guessing branch. Previous outcomes remain in the record. -/
noncomputable def fresh {n : ℕ} (m : Basis n) : Raw m→ℂ :=
  RecordedHistory.appendState (ListSlots.fresh n (bitsValue m).toNat)
    (fun l => productState (fun i => OrderSlots.fresh n (bases m l i) m))

noncomputable def passed {n : ℕ} (m : Basis n) (hm : (bitsValue m).toNat≠0)
    (p₀ : Component (bitsValue m).toNat) (r : Raw m) : Prop :=
  ListSlots.passed hm (bitsValue m).isLt p₀ r.1 ∧
    ∀ i,OrderSlots.passed (bases m r.1 i) m (r.2 i)

noncomputable def pairs {n : ℕ} (m : Basis n) (r : Raw m) : List (ℕ×ℕ) :=
  List.ofFn (fun i : Fin (n^5) => ((bitsValue (bases m r.1 i)).toNat,
    (bitsValue (OrderSlots.output (bases m r.1 i) m (r.2 i))).toNat))

noncomputable def divisor {n : ℕ} (m : Basis n) (r : Raw m) : ℕ :=
  suppliedDivisor (bitsValue m).toNat n (pairs m r)

lemma fresh_normalized {n : ℕ} (m : Basis n) : ∑ r,Complex.normSq (fresh m r)=1 := by
  apply RecordedHistory.append_normalized
  · exact ListSlots.fresh_normalized _ _
  · intro l
    exact productState_normalized _ (fun _ => OrderSlots.fresh_normalized _ _ _)

/-- One list transition followed by the K order/dummy transitions has exactly
z^(K+1) retained mass, unconditioned on the successful factor-data computation. -/
theorem passed_mass {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (hodd : Odd (bitsValue m).toNat) (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀) :
    outcomeMass (passed m (by omega) p₀) (fresh m)=(Completion.target n:ℝ)^(n^5+1) := by
  change outcomeMass (fun r => ListSlots.passed (by omega) (bitsValue m).isLt p₀ r.1 ∧
    (fun l (rr : Fin (n^5)→OrderSlots.Result n) => ∀ i,OrderSlots.passed (bases m l i) m (rr i)) r.1 r.2)
    (RecordedHistory.appendState _ _) = _
  rw [RecordedHistory.append_constant_mass _ _ _ _ ((Completion.target n:ℝ)^(n^5))
    (fun l _ => OrderSlots.all_passed_mass hn m hm (bases m l))]
  rw [ListSlots.passed_mass hn hm (bitsValue m).isLt hodd p₀ p₁ hne]
  exact (mul_comm _ _).trans (pow_succ (Completion.target n:ℝ) (n^5)).symm

lemma passed_pair {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (hodd : Odd (bitsValue m).toNat) (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀)
    (r : Raw m) (hp : passed m (by omega) p₀ r) :
    ∃ u : (ZMod (bitsValue m).toNat)ˣ,
      FavorableUnit (by omega : (bitsValue m).toNat≠0) (bitsValue m).isLt p₀ u ∧
        ((u : ZMod (bitsValue m).toNat).val,orderOf u)∈pairs m r := by
  let : NeZero (bitsValue m).toNat := ⟨by omega⟩
  obtain ⟨i,u,ha,hf⟩ := ListSlots.passed_good hn (by omega) (bitsValue m).isLt hodd p₀ p₁ hne r.1 hp.1
  have haz : ((bitsValue (bases m r.1 i)).toNat : ZMod (bitsValue m).toNat)=u := by
    rw [show (bitsValue (bases m r.1 i)).toNat=(u : ZMod (bitsValue m).toNat).val from ha]
    exact ZMod.natCast_zmod_val _
  have ho := OrderSlots.passed_order (bases m r.1 i) m hm u (by change (bitsValue (TransitionWords.read (ListSlots.output (bitsValue m).isLt r.1) i)).toNat < _; rw [ha]; exact (u : ZMod (bitsValue m).toNat).val_lt) haz (r.2 i) (hp.2 i)
  refine ⟨u,hf,?_⟩
  exact List.mem_ofFn.mpr ⟨i,Prod.ext ha ho⟩

/-- The output is the actual guarded even/root/order divisor scan, not a chosen
mathematical divisor. Both ordinary and guessed good list outputs are covered. -/
theorem passed_divisor {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (hc : ¬(bitsValue m).toNat.Prime) (hodd : Odd (bitsValue m).toNat)
    (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀)
    (r : Raw m) (hp : passed m (by omega) p₀ r) :
    FactorController.ProperDivisor (bitsValue m).toNat (divisor m r) := by
  obtain ⟨u,hf,hu⟩ := passed_pair hn m hm hodd p₀ p₁ hne r hp
  exact suppliedDivisor_good hm (bitsValue m).isLt hc (pairs m r) (fun _ _ => ⟨p₀,u,hf,hu⟩)

end CompletedSplit
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FixedSplit.lean =====
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

namespace FixedSplit

abbrev Raw (n : ℕ) :=
  PhysicalListSlots.Result n × (Fin (n^5)→OrderSlots.Result n)

noncomputable instance rawFintype (n : ℕ) : Fintype (Raw n) := inferInstance

def bases {n : ℕ} (r : PhysicalListSlots.Result n) : Fin (n^5)→Basis n :=
  TransitionWords.read (PhysicalListSlots.output r)

/-- Actual next fresh registers depend only on the completed list output,
including its rare guessing branch. Previous outcomes remain in the record. -/
noncomputable def fresh {n : ℕ} (m : Basis n) : Raw n→ℂ :=
  RecordedHistory.appendState (PhysicalListSlots.fresh m)
    (fun l => productState (fun i => OrderSlots.fresh n (bases l i) m))

noncomputable def passed {n : ℕ} (m : Basis n) (hm : (bitsValue m).toNat≠0)
    (p₀ : Component (bitsValue m).toNat) (r : Raw n) : Prop :=
  PhysicalListSlots.passed m hm p₀ r.1 ∧
    ∀ i,OrderSlots.passed (bases r.1 i) m (r.2 i)

noncomputable def pairs {n : ℕ} (m : Basis n) (r : Raw n) : List (ℕ×ℕ) :=
  List.ofFn (fun i : Fin (n^5) => ((bitsValue (bases r.1 i)).toNat,
    (bitsValue (OrderSlots.output (bases r.1 i) m (r.2 i))).toNat))

noncomputable def divisor {n : ℕ} (m : Basis n) (r : Raw n) : ℕ :=
  suppliedDivisor (bitsValue m).toNat n (pairs m r)

lemma fresh_normalized {n : ℕ} (m : Basis n) : ∑ r,Complex.normSq (fresh m r)=1 := by
  apply RecordedHistory.append_normalized
  · exact PhysicalListSlots.fresh_normalized _
  · intro l
    exact productState_normalized _ (fun _ => OrderSlots.fresh_normalized _ _ _)

/-- One list transition followed by the K order/dummy transitions has exactly
z^(K+1) retained mass, unconditioned on the successful factor-data computation. -/
theorem passed_mass {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (hodd : Odd (bitsValue m).toNat) (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀) :
    outcomeMass (passed m (by omega) p₀) (fresh m)=(Completion.target n:ℝ)^(n^5+1) := by
  change outcomeMass (fun r => PhysicalListSlots.passed m (by omega) p₀ r.1 ∧
    (fun l (rr : Fin (n^5)→OrderSlots.Result n) => ∀ i,OrderSlots.passed (bases l i) m (rr i)) r.1 r.2)
    (RecordedHistory.appendState _ _) = _
  rw [RecordedHistory.append_constant_mass _ _ _ _ ((Completion.target n:ℝ)^(n^5))
    (fun l _ => OrderSlots.all_passed_mass hn m hm (bases l))]
  rw [PhysicalListSlots.passed_mass hn m hm hodd p₀ p₁ hne]
  exact (mul_comm _ _).trans (pow_succ (Completion.target n:ℝ) (n^5)).symm

lemma passed_pair {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (hodd : Odd (bitsValue m).toNat) (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀)
    (r : Raw n) (hp : passed m (by omega) p₀ r) :
    ∃ u : (ZMod (bitsValue m).toNat)ˣ,
      FavorableUnit (by omega : (bitsValue m).toNat≠0) (bitsValue m).isLt p₀ u ∧
        ((u : ZMod (bitsValue m).toNat).val,orderOf u)∈pairs m r := by
  let : NeZero (bitsValue m).toNat := ⟨by omega⟩
  obtain ⟨i,u,ha,hf⟩ := PhysicalListSlots.passed_good hn m (by omega) hodd p₀ p₁ hne r.1 hp.1
  have haz : ((bitsValue (bases r.1 i)).toNat : ZMod (bitsValue m).toNat)=u := by
    rw [show (bitsValue (bases r.1 i)).toNat=(u : ZMod (bitsValue m).toNat).val from ha]
    exact ZMod.natCast_zmod_val _
  have ho := OrderSlots.passed_order (bases r.1 i) m hm u (by change (bitsValue (TransitionWords.read (PhysicalListSlots.output r.1) i)).toNat < _; rw [ha]; exact (u : ZMod (bitsValue m).toNat).val_lt) haz (r.2 i) (hp.2 i)
  refine ⟨u,hf,?_⟩
  exact List.mem_ofFn.mpr ⟨i,Prod.ext ha ho⟩

/-- The output is the actual guarded even/root/order divisor scan, not a chosen
mathematical divisor. Both ordinary and guessed good list outputs are covered. -/
theorem passed_divisor {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (hc : ¬(bitsValue m).toNat.Prime) (hodd : Odd (bitsValue m).toNat)
    (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀)
    (r : Raw n) (hp : passed m (by omega) p₀ r) :
    FactorController.ProperDivisor (bitsValue m).toNat (divisor m r) := by
  obtain ⟨u,hf,hu⟩ := passed_pair hn m hm hodd p₀ p₁ hne r hp
  exact suppliedDivisor_good hm (bitsValue m).isLt hc (pairs m r) (fun _ _ => ⟨p₀,u,hf,hu⟩)

end FixedSplit
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/AdaptivePrepared.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

/-- A coherent fresh launch on an encoded old history. The local law refers
only to the actually computed Boolean initializer, never to a selected outcome. -/
lemma preparedOracle_encode {α β : Type*} [Fintype α] [Fintype β] {p q r : ℕ}
    (e : α→Basis p) (f : β→Basis q) (ψ : α→ℂ) (F : α→β→ℂ)
    (c : BooleanNetwork p q) (hc : c.net.count ≤ r) (ops : List (Instruction q))
    (hlocal : ∀ a,(programMatrix ops).mulVec (basisVector (c.eval (e a)))=encodeState f (F a)) :
    (programMatrix (preparedOracle c hc ops)).mulVec
      (encodeState (fun a=>packed r (e a) (fun _=>false)) ψ)=
    encodeState (fun ab : α×β=>packed r (e ab.1) (f ab.2)) (RecordedHistory.appendState ψ F) := by
  rw [encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,preparedOracle_basis,hlocal,encodeState_comp]
  unfold encodeState RecordedHistory.appendState
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [smul_smul]
  rfl

def appendPrepared {p q r : ℕ} (A : List (Instruction p)) (c : BooleanNetwork p q)
    (hc : c.net.count ≤ r) (ops : List (Instruction q)) : List (Instruction (p+q+r)) :=
  firstProgram q r A++preparedOracle c hc ops

lemma appendPrepared_length {p q r : ℕ} (A : List (Instruction p)) (c : BooleanNetwork p q)
    (hc : c.net.count ≤ r) (ops : List (Instruction q)) :
    (appendPrepared A c hc ops).length ≤ A.length+4*c.net.count+2*q+ops.length := by
  have h := preparedOracle_length c hc ops
  simp only [appendPrepared,List.length_append,firstProgram_length]
  omega

lemma appendPrepared_state {α β : Type*} [Fintype α] [Fintype β] {p q r : ℕ}
    (e : α→Basis p) (f : β→Basis q) (ψ : α→ℂ) (F : α→β→ℂ)
    (A : List (Instruction p)) (v : Basis p)
    (hA : (programMatrix A).mulVec (basisVector v)=encodeState e ψ)
    (c : BooleanNetwork p q) (hc : c.net.count ≤ r) (ops : List (Instruction q))
    (hlocal : ∀ a,(programMatrix ops).mulVec (basisVector (c.eval (e a)))=encodeState f (F a)) :
    (programMatrix (appendPrepared A c hc ops)).mulVec (basisVector (packed r v (fun _=>false)))=
      encodeState (fun ab : α×β=>packed r (e ab.1) (f ab.2)) (RecordedHistory.appendState ψ F) := by
  rw [appendPrepared,programMatrix_append,←Matrix.mulVec_mulVec,firstProgram_basis,hA,encodeState_comp]
  exact preparedOracle_encode e f ψ F c hc ops hlocal

end ExactQuantumFactoring


end

end OAI


