-- Prove2me | Definitions.Def_OAI_QuantumFactoring_Part07
-- name    : OAI_QuantumFactoring_Part07
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T07:10:49.284885+00:00
-- url     : https://prove2.me/theorems/6951d8e1-d631-4278-88d3-e48c32ae10c3
-- title:
--   Exact quantum factoring, part 7 of 38 (port of OpenAI's formalization)
-- statement:
--   Part 7 of 38 of a port of OpenAI's Lean formalization of the manuscript *Exact quantum factoring over a fixed finite gate set* (OpenAI, September 25, 2026). This part contains the modules `BooleanFold`, `ArithmeticPredicates`, `StaticPredicates`, `AKSNetworks`, `WordBlocks`, `CyclicCircuit`, `CyclicConstants`, `CyclicPowerCircuit`, `CyclicTestCircuit`, `CyclicTestBounds`, `BinaryRoots`, `RootCircuit`, `PerfectPowerCircuit`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/QuantumFactoring`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `ExactQuantumFactoring`, which is identical to upstream `Basic.lean`.
--
--   The development is split into 38 parts only so that each compiles within the platform's time limit. Together the parts supply the circuit family `PhysicalTree.finalCircuit` and its specification, used to prove `OAI.ExactQuantumFactoring.zero_amplitude_core`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/QuantumFactoring: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/BooleanFold.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ArithmeticPredicates.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/StaticPredicates.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/AKSNetworks.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/WordBlocks.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/CyclicCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/CyclicConstants.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/CyclicPowerCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/CyclicTestCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/CyclicTestBounds.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/BinaryRoots.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/RootCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PerfectPowerCircuit.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf

/-
Exact quantum factoring development (port of OpenAI's formalization), part 7 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: BooleanFold.lean, ArithmeticPredicates.lean, StaticPredicates.lean, AKSNetworks.lean, WordBlocks.lean, CyclicCircuit.lean, CyclicConstants.lean, CyclicPowerCircuit.lean, CyclicTestCircuit.lean, CyclicTestBounds.lean, BinaryRoots.lean, RootCircuit.lean, PerfectPowerCircuit.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part06

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BooleanFold.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork
open scoped BigOperators

def any {n : ℕ} : List (BooleanNetwork n 1) → BooleanNetwork n 1
  | [] => constant false
  | c::cs => c.bor (any cs)

lemma any_eval {n : ℕ} (cs : List (BooleanNetwork n 1)) (x : Fin n → Bool) :
    (any cs).eval x 0=true ↔ ∃ c ∈ cs, c.eval x 0=true := by
  induction cs with
  | nil => simp [any]
  | cons c cs ih => simp [any,ih]

lemma any_count {n c : ℕ} (cs : List (BooleanNetwork n 1))
    (h : ∀ a ∈ cs, a.net.count ≤ c) : (any cs).net.count ≤ cs.length*(c+4)+1 := by
  induction cs with
  | nil => simp [any]
  | cons a cs ih =>
    have ha := h a (by simp)
    have hc := ih (fun b hb => h b (by simp [hb]))
    simp only [any,count_bor,List.length_cons]
    nlinarith

def all {n : ℕ} : List (BooleanNetwork n 1) → BooleanNetwork n 1
  | [] => constant true
  | c::cs => c.band (all cs)

lemma all_eval {n : ℕ} (cs : List (BooleanNetwork n 1)) (x : Fin n → Bool) :
    (all cs).eval x 0=true ↔ ∀ c ∈ cs, c.eval x 0=true := by
  induction cs with
  | nil => simp [all]
  | cons c cs ih => simp [all,ih]

lemma all_count {n c : ℕ} (cs : List (BooleanNetwork n 1))
    (h : ∀ a ∈ cs, a.net.count ≤ c) : (all cs).net.count ≤ cs.length*(c+1)+1 := by
  induction cs with
  | nil => simp [all]
  | cons a cs ih =>
    have ha := h a (by simp)
    have hc := ih (fun b hb => h b (by simp [hb]))
    simp only [all,count_band,List.length_cons]
    nlinarith

end ExactQuantumFactoring.BooleanNetwork


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ArithmeticPredicates.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open Std.Sat Std.Tactic.BVDecide
open AIGCompiler BooleanNetwork

def ult (w : ℕ) : BooleanNetwork (w+w) 1 :=
  let r := BVPred.mkUlt (inputs (w+w)).1 (binaryInputs w)
  compile r.aig (fun _ => r.ref)

lemma ult_correct (w : ℕ) (a b : Basis w) :
    (ult w).eval (Fin.append a b) 0 =
      decide ((bitsValue a).toNat < (bitsValue b).toNat) := by
  rw [ult,compile_correct]
  have h := BVPred.mkUlt_denote_eq (inputs (w+w)).1
    (leftWord (Fin.append a b)) (rightWord (Fin.append a b))
    (binaryInputs w) (Fin.append a b) (binaryInputs_left w _) (binaryInputs_right w _)
  simpa only [leftWord_append,rightWord_append,BitVec.ult] using h

lemma ult_count (w : ℕ) : (ult w).net.count ≤ 48*w+8 := by
  have h := compile_count (BVPred.mkUlt (inputs (w+w)).1 (binaryInputs w)).aig
    (m := 1) (fun _ => (BVPred.mkUlt (inputs (w+w)).1 (binaryInputs w)).ref)
  have hs := AIGBounds.ult_size (inputs (w+w)).1 (binaryInputs w)
  rw [inputs_size] at hs
  dsimp only [ult]
  omega

def wordLt {n w : ℕ} (a b : BooleanNetwork n w) : BooleanNetwork n 1 :=
  (a.pair b).comp (ult w)

lemma wordLt_eval {n w : ℕ} (a b : BooleanNetwork n w) (x : Basis n) :
    (wordLt a b).eval x 0 = decide ((bitsValue (a.eval x)).toNat < (bitsValue (b.eval x)).toNat) := by
  rw [wordLt,eval_comp,eval_pair,ult_correct]

lemma wordLt_count {n w : ℕ} (a b : BooleanNetwork n w) :
    (wordLt a b).net.count ≤ a.net.count+b.net.count+48*w+8 := by
  simp only [wordLt,count_comp,count_pair]
  have := ult_count w
  omega

def wordLe {n w : ℕ} (a b : BooleanNetwork n w) : BooleanNetwork n 1 :=
  (wordLt b a).bnot

lemma wordLe_eval {n w : ℕ} (a b : BooleanNetwork n w) (x : Basis n) :
    (wordLe a b).eval x 0 = decide ((bitsValue (a.eval x)).toNat ≤ (bitsValue (b.eval x)).toNat) := by
  rw [wordLe,eval_bnot,wordLt_eval]
  by_cases h : (bitsValue (a.eval x)).toNat ≤ (bitsValue (b.eval x)).toNat
  · simp [h,Nat.not_lt.mpr h]
  · simp [h,Nat.lt_of_not_ge h]

lemma wordLe_count {n w : ℕ} (a b : BooleanNetwork n w) :
    (wordLe a b).net.count ≤ a.net.count+b.net.count+48*w+9 := by
  simp only [wordLe,count_bnot]
  have := wordLt_count b a
  omega

def wordEq (w : ℕ) : BooleanNetwork (w+w) 1 :=
  ((ult w).bor (((select (Fin.addCases (Fin.natAdd w) (Fin.castAdd w))).comp (ult w)))).bnot

lemma wordEq_eval (w : ℕ) (a b : Basis w) :
    (wordEq w).eval (Fin.append a b) 0 = decide (bitsValue a = bitsValue b) := by
  have he : (select (Fin.addCases (Fin.natAdd w) (Fin.castAdd w))).eval (Fin.append a b) =
      Fin.append b a := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [eval_select,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
        Fin.append_left,Fin.append_right]
  rw [wordEq,eval_bnot,eval_bor,eval_comp,he,ult_correct,ult_correct]
  have hh : bitsValue a = bitsValue b ↔ (bitsValue a).toNat=(bitsValue b).toNat := by
    constructor
    · exact congrArg BitVec.toNat
    · exact BitVec.eq_of_toNat_eq
  simp only [hh]
  cases h₁ : decide ((bitsValue a).toNat < (bitsValue b).toNat) <;>
    cases h₂ : decide ((bitsValue b).toNat < (bitsValue a).toNat) <;>
    simp_all <;> omega

lemma wordEq_count (w : ℕ) : (wordEq w).net.count ≤ 96*w+21 := by
  simp only [wordEq,count_bnot,count_bor,count_comp,count_select,zero_add]
  have := ult_count w
  omega

/-- Static natural exponent, with retained accumulator and no repeated
construction of earlier expressions. This circuit has O(e w²) Boolean nodes. -/
def staticPowerStep (w : ℕ) : BooleanNetwork (w+w) (w+w) :=
  (select (Fin.castAdd w)).pair (mul w)

def staticPower (w e : ℕ) : BooleanNetwork w w :=
  ((select id).pair (wordConstant (BitVec.ofNat w 1))).comp
    (((staticPowerStep w).iterate e).rewire (Fin.natAdd w))

lemma staticPowerStep_eval (w : ℕ) (a b : Basis w) :
    (staticPowerStep w).eval (Fin.append a b) =
      Fin.append a ((mul w).eval (Fin.append a b)) := by
  simp only [staticPowerStep,eval_pair,eval_select]
  congr 1
  funext i
  exact Fin.append_left a b i

lemma staticPower_iterate (w e : ℕ) (a b : Basis w) :
    ∃ z : Basis w,
      ((staticPowerStep w).iterate e).eval (Fin.append a b) = Fin.append a z ∧
      bitsValue z = bitsValue a^e * bitsValue b := by
  induction e generalizing b with
  | zero => refine ⟨b,?_,?_⟩ <;> simp [eval_iterate]
  | succ e ih =>
    rw [eval_iterate,Function.iterate_succ_apply,staticPowerStep_eval]
    have h := ih ((mul w).eval (Fin.append a b))
    rw [eval_iterate] at h
    obtain ⟨z,hz,hv⟩ := h
    refine ⟨z,hz,?_⟩
    rw [hv,mul_word,pow_succ]
    exact (mul_assoc _ _ _).symm

lemma staticPower_eval (w e : ℕ) (a : Basis w) :
    bitsValue ((staticPower w e).eval a) = bitsValue a^e := by
  simp only [staticPower,eval_comp,eval_pair,eval_select,Function.comp_id,eval_rewire]
  obtain ⟨z,hz,hv⟩ := staticPower_iterate w e a ((wordConstant (BitVec.ofNat w 1)).eval a)
  rw [hz]
  have he : Fin.append a z ∘ Fin.natAdd w = z := by funext i; exact Fin.append_right _ _ i
  rw [he,hv,wordConstant_eval]
  simp

lemma staticPower_count (w e : ℕ) : (staticPower w e).net.count ≤
    w+e*(90*w*w+14*w+6) := by
  simp only [staticPower,count_comp,count_pair,count_select,wordConstant_count,zero_add,
    count_rewire,count_iterate,staticPowerStep]
  have h := mul_count w
  exact Nat.add_le_add_left (Nat.mul_le_mul_left e h) w

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/StaticPredicates.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

def equalOn {n w : ℕ} (a b : BooleanNetwork n w) : BooleanNetwork n 1 :=
  (a.pair b).comp (wordEq w)

lemma equalOn_value {n w : ℕ} (a b : BooleanNetwork n w) (x : Basis n) :
    (equalOn a b).eval x 0=true ↔ (bitsValue (a.eval x)).toNat=(bitsValue (b.eval x)).toNat := by
  rw [equalOn,eval_comp,eval_pair,wordEq_eval,decide_eq_true_eq]
  exact ⟨congrArg BitVec.toNat,BitVec.eq_of_toNat_eq⟩

lemma equalOn_count {n w : ℕ} (a b : BooleanNetwork n w) :
    (equalOn a b).net.count ≤ a.net.count+b.net.count+96*w+21 := by
  simp only [equalOn,count_comp,count_pair]
  have := wordEq_count w
  omega

def constMod (w d : ℕ) : BooleanNetwork w w :=
  ((select id).pair (wordConstant (BitVec.ofNat w d))).comp (mod w)

lemma constMod_value (w d : ℕ) (x : Basis w) (hd : d < 2^w) :
    (bitsValue ((constMod w d).eval x)).toNat=(bitsValue x).toNat%d := by
  rw [constMod,eval_comp,eval_pair,eval_select,Function.comp_id,mod_word,wordConstant_eval,
    BitVec.toNat_umod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hd]

lemma constMod_count (w d : ℕ) : (constMod w d).net.count ≤ 216*w*w+57*w+6 := by
  simp only [constMod,count_comp,count_pair,count_select,wordConstant_count,zero_add]
  have := mod_count w
  omega

def dividesNet (w d : ℕ) : BooleanNetwork w 1 :=
  equalOn (constMod w d) (wordConstant (BitVec.ofNat w 0))

lemma dividesNet_value (w d : ℕ) (x : Basis w) (hd : d < 2^w) :
    (dividesNet w d).eval x 0=true ↔ d ∣ (bitsValue x).toNat := by
  rw [dividesNet,equalOn_value,constMod_value _ _ _ hd,wordConstant_eval]
  simp only [BitVec.toNat_ofNat,Nat.zero_mod]
  exact Nat.dvd_iff_mod_eq_zero.symm

lemma dividesNet_count (w d : ℕ) : (dividesNet w d).net.count ≤ 216*w*w+154*w+27 := by
  have h := equalOn_count (constMod w d) (wordConstant (BitVec.ofNat w 0))
  rw [wordConstant_count] at h
  have := constMod_count w d
  change (equalOn (constMod w d) (wordConstant (BitVec.ofNat w 0))).net.count ≤ _
  omega

/-- Static modulus and exponent; exponent wiring is reversed explicitly. -/
def constPowMod (w s j : ℕ) : BooleanNetwork w w :=
  (((select id).pair (wordConstant (BitVec.ofNat w s))).pair
    ((wordConstant (BitVec.ofNat w j)).rewire Fin.rev)).comp (modularPower w w)

lemma constPowMod_value (w s j : ℕ) (x : Basis w) (hs : 2 ≤ s)
    (hsw : s < 2^w) (hjw : j < 2^w) :
    (bitsValue ((constPowMod w s j).eval x)).toNat = (bitsValue x).toNat^j%s := by
  let sb := (wordConstant (n := w) (BitVec.ofNat w s)).eval x
  let eb := ((wordConstant (n := w) (BitVec.ofNat w j)).rewire Fin.rev).eval x
  have hs' : (bitsValue sb).toNat=s := by
    simp only [sb,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hsw]
  have he : horner eb w le_rfl=j := by
    rw [horner_full,Triangular.inputNumber_reverse]
    have hh : reverseBits w eb = (wordConstant (n := w) (BitVec.ofNat w j)).eval x := by
      funext i
      simp [reverseBits,eb]
    rw [hh,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hjw]
  have hm : 2 ≤ (bitsValue sb).toNat := by omega
  simp only [constPowMod,eval_comp,eval_pair,eval_select,Function.comp_id]
  change (bitsValue ((modularPower w w).eval (Fin.append (Fin.append x sb) eb))).toNat=_
  rw [modularPower_value _ _ _ hm,he,hs']

lemma constPowMod_count (w s j : ℕ) :
    (constPowMod w s j).net.count ≤ 3*w+w*(3672*w*w+436*w+36) := by
  simp only [constPowMod,count_comp,count_pair,count_select,wordConstant_count,count_rewire,zero_add]
  have := modularPower_count w w
  omega

def powerOneNet (w s j : ℕ) : BooleanNetwork w 1 :=
  equalOn (constPowMod w s j) (wordConstant (BitVec.ofNat w 1))

lemma powerOneNet_value (w s j : ℕ) (x : Basis w) (hs : 2 ≤ s)
    (hsw : s < 2^w) (hjw : j < 2^w) :
    (powerOneNet w s j).eval x 0=true ↔ (bitsValue x).toNat^j%s=1 := by
  rw [powerOneNet,equalOn_value,constPowMod_value _ _ _ _ hs hsw hjw,wordConstant_eval,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 1 < 2^w)]

lemma powerOneNet_count (w s j : ℕ) :
    (powerOneNet w s j).net.count ≤ 100*w+21+w*(3672*w*w+436*w+36) := by
  have h := equalOn_count (constPowMod w s j) (wordConstant (BitVec.ofNat w 1))
  rw [wordConstant_count] at h
  have := constPowMod_count w s j
  change (equalOn (constPowMod w s j) (wordConstant (BitVec.ofNat w 1))).net.count ≤ _
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/AKSNetworks.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork

lemma all_ofFn_eval {n k : ℕ} (cs : Fin k → BooleanNetwork n 1) (x : Basis n) :
    (all (List.ofFn cs)).eval x 0=true ↔ ∀ i, (cs i).eval x 0=true := by
  rw [all_eval]
  simp

lemma any_ofFn_eval {n k : ℕ} (cs : Fin k → BooleanNetwork n 1) (x : Basis n) :
    (any (List.ofFn cs)).eval x 0=true ↔ ∃ i, (cs i).eval x 0=true := by
  rw [any_eval]
  simp

lemma bnot_value {n : ℕ} (c : BooleanNetwork n 1) (x : Basis n) :
    c.bnot.eval x 0=true ↔ ¬ c.eval x 0=true := by simp

end ExactQuantumFactoring.BooleanNetwork

namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

def orderTests (w s k : ℕ) : BooleanNetwork w 1 :=
  all (List.ofFn (fun i : Fin k => (powerOneNet w s (i.val+1)).bnot))

lemma orderTests_value (w s k : ℕ) (x : Basis w) (hs : 2 ≤ s)
    (hsw : s < 2^w) (hkw : k < 2^w) :
    (orderTests w s k).eval x 0=true ↔
      ∀ j : ℕ, 1 ≤ j → j ≤ k → (bitsValue x).toNat^j%s ≠ 1 := by
  rw [orderTests,all_ofFn_eval]
  constructor
  · intro h j hj hjk
    have hh := (bnot_value _ _).mp (h (⟨j-1,by omega⟩ : Fin k))
    rw [powerOneNet_value _ _ _ _ hs hsw (by omega)] at hh
    simpa only [show j-1+1=j by omega] using hh
  · intro h i
    rw [bnot_value,powerOneNet_value _ _ _ _ hs hsw (by have := i.isLt;omega)]
    exact h (i.val+1) (by omega) (by omega)

lemma orderTests_count (w s k : ℕ) : (orderTests w s k).net.count ≤
    k*(100*w+23+w*(3672*w*w+436*w+36))+1 := by
  have h := all_count (c := 100*w+22+w*(3672*w*w+436*w+36))
    (List.ofFn (fun i : Fin k => (powerOneNet w s (i.val+1)).bnot)) (by
      intro c hc
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
      rw [count_bnot]
      have := powerOneNet_count w s (i.val+1)
      omega)
  convert h using 1 <;> simp only [orderTests,List.length_ofFn]
  ring

def properDivisor (w d : ℕ) : BooleanNetwork w 1 :=
  (dividesNet w d).band (wordLt (wordConstant (BitVec.ofNat w d)) (select id))

lemma properDivisor_value (w d : ℕ) (x : Basis w) (hd : d < 2^w) :
    (properDivisor w d).eval x 0=true ↔ d ∣ (bitsValue x).toNat ∧ d < (bitsValue x).toNat := by
  rw [properDivisor,eval_band,Bool.and_eq_true,dividesNet_value _ _ _ hd,
    wordLt_eval,wordConstant_eval,eval_select,Function.comp_id,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hd,decide_eq_true_eq]

lemma properDivisor_count (w d : ℕ) :
    (properDivisor w d).net.count ≤ 216*w*w+203*w+36 := by
  have h := wordLt_count (wordConstant (n := w) (BitVec.ofNat w d)) (select id)
  rw [wordConstant_count,count_select] at h
  have hd := dividesNet_count w d
  rw [properDivisor,count_band]
  omega

def noSmallDivisor (w B : ℕ) : BooleanNetwork w 1 :=
  all (List.ofFn (fun i : Fin (B-1) => (properDivisor w (i.val+2)).bnot))

lemma noSmallDivisor_value (w B : ℕ) (x : Basis w) (hB : B < 2^w) :
    (noSmallDivisor w B).eval x 0=true ↔
      ∀ d : ℕ, 2 ≤ d → d ≤ B → d < (bitsValue x).toNat → ¬ d ∣ (bitsValue x).toNat := by
  rw [noSmallDivisor,all_ofFn_eval]
  constructor
  · intro h d hd hdB hdm hdiv
    have hh := (bnot_value _ _).mp (h (⟨d-2,by omega⟩ : Fin (B-1)))
    rw [properDivisor_value _ _ _ (by omega)] at hh
    exact hh (by simpa [show d-2+2=d by omega] using And.intro hdiv hdm)
  · intro h i
    rw [bnot_value,properDivisor_value _ _ _ (by have := i.isLt;omega)]
    rintro ⟨hd,hlt⟩
    exact h (i.val+2) (by omega) (by omega) hlt hd

lemma noSmallDivisor_count (w B : ℕ) : (noSmallDivisor w B).net.count ≤
    (B-1)*(216*w*w+203*w+38)+1 := by
  have h := all_count (c := 216*w*w+203*w+37)
    (List.ofFn (fun i : Fin (B-1) => (properDivisor w (i.val+2)).bnot)) (by
      intro c hc
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
      rw [count_bnot]
      have := properDivisor_count w (i.val+2)
      omega)
  simpa only [noSmallDivisor,List.length_ofFn] using h

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/WordBlocks.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
open scoped BigOperators

/-- Consecutive fixed-width words; construction duplicates a word network at
most w times and so has a direct polynomial-size bound. -/
def wordBlocks {n s w : ℕ} (f : Fin s → BooleanNetwork n w) : BooleanNetwork n (s*w) :=
  vector (fun k => (f (finProdFinEquiv.symm k).1).rewire
    (fun _ => (finProdFinEquiv.symm k).2))

def block {s w : ℕ} (x : Basis (s*w)) (i : Fin s) : Basis w :=
  fun j => x (finProdFinEquiv (i,j))

def blockNet (s w : ℕ) (i : Fin s) : BooleanNetwork (s*w) w :=
  select (fun j => finProdFinEquiv (i,j))

@[simp] lemma blockNet_eval {s w : ℕ} (i : Fin s) (x : Basis (s*w)) :
    (blockNet s w i).eval x = block x i := rfl
@[simp] lemma blockNet_count {s w : ℕ} (i : Fin s) : (blockNet s w i).net.count=0 := rfl

lemma wordBlocks_eval {n s w : ℕ} (f : Fin s → BooleanNetwork n w) (x : Basis n) (i : Fin s) :
    block ((wordBlocks f).eval x) i=(f i).eval x := by
  funext j
  simp only [block,wordBlocks,eval_vector,eval_rewire,Function.comp_apply,Equiv.symm_apply_apply]

lemma wordBlocks_count {n s w c : ℕ} (f : Fin s → BooleanNetwork n w)
    (h : ∀ i, (f i).net.count ≤ c) : (wordBlocks f).net.count ≤ s*w*c := by
  apply count_vector_le
  intro i
  simpa only [count_rewire] using h (finProdFinEquiv.symm i).1

/-- One extra carry bit before reduction avoids overflow even on noncanonical
coefficient representatives; all arrays use exactly as many bits as specified. -/
def addMod {n w : ℕ} (a b m : BooleanNetwork n w) : BooleanNetwork n w :=
  let p := ((a.comp (padRight w 1)).pair (b.comp (padRight w 1))).comp (add (w+1))
  ((p.pair (m.comp (padRight w 1))).comp (mod (w+1))).rewire (Fin.castAdd 1)

lemma addMod_count {n w : ℕ} (a b m : BooleanNetwork n w) :
    (addMod a b m).net.count ≤ a.net.count+b.net.count+m.net.count+
      216*(w+1)^2+142*(w+1)+15 := by
  have h₁ := add_count (w+1)
  have h₂ := mod_count (w+1)
  simp only [addMod,count_rewire,count_comp,count_pair,count_padRight]
  nlinarith

lemma addMod_value {n w : ℕ} (a b m : BooleanNetwork n w) (x : Basis n)
    (hm : 0 < (bitsValue (m.eval x)).toNat) :
    (bitsValue ((addMod a b m).eval x)).toNat =
      ((bitsValue (a.eval x)).toNat+(bitsValue (b.eval x)).toNat)%
        (bitsValue (m.eval x)).toNat := by
  simp only [addMod,eval_rewire,eval_comp,eval_pair]
  rw [bitsValue_take,mod_word,BitVec.toNat_setWidth,BitVec.toNat_umod,add_word,BitVec.toNat_add]
  simp only [padRight_word,setWidth_toNat_of_le (by omega : w ≤ w+1)]
  have hp : (bitsValue (a.eval x)).toNat+(bitsValue (b.eval x)).toNat < 2^(w+1) := by
    rw [pow_succ]
    have ha := (bitsValue (a.eval x)).isLt
    have hb := (bitsValue (b.eval x)).isLt
    omega
  rw [Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt]
  exact (Nat.mod_lt _ hm).trans (bitsValue (m.eval x)).isLt

/-- Linear-length modular accumulation, not a repeated expanded expression. -/
def sumMod {n w : ℕ} (m : BooleanNetwork n w) : List (BooleanNetwork n w) → BooleanNetwork n w
  | [] => wordConstant 0
  | a::as => addMod a (sumMod m as) m

lemma sumMod_value {n w : ℕ} (m : BooleanNetwork n w) (as : List (BooleanNetwork n w))
    (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat) :
    (bitsValue ((sumMod m as).eval x)).toNat =
      (as.map (fun a => (bitsValue (a.eval x)).toNat)).sum%(bitsValue (m.eval x)).toNat := by
  induction as with
  | nil => simp [sumMod,wordConstant_eval]
  | cons a as ih =>
    rw [sumMod,addMod_value _ _ _ _ hm,ih]
    simp only [List.map_cons,List.sum_cons,Nat.add_mod_mod]

lemma sumMod_count {n w c : ℕ} (m : BooleanNetwork n w) (as : List (BooleanNetwork n w))
    (h : ∀ a ∈ as, a.net.count ≤ c) :
    (sumMod m as).net.count ≤ w+as.length*(c+m.net.count+216*(w+1)^2+142*(w+1)+15) := by
  induction as with
  | nil => simp [sumMod,wordConstant_count]
  | cons a as ih =>
    have ha := h a (by simp)
    have hi := ih (fun b hb => h b (by simp [hb]))
    have hh := addMod_count a (sumMod m as) m
    simp only [sumMod,List.length_cons]
    nlinarith

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CyclicCircuit.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality
open scoped BigOperators

noncomputable def decodeCyclic {s w : ℕ} (m : ℕ) (x : Basis (s*w)) : Cyclic (ZMod m) s :=
  cyclicOf (fun i => ((bitsValue (block x i)).toNat : ZMod m))

@[simp] lemma decodeCyclic_coeff {s w : ℕ} (m : ℕ) (x : Basis (s*w)) (i : Fin s) :
    (decodeCyclic m x).coeff i=((bitsValue (block x i)).toNat : ZMod m) := rfl

def cyclicTerm {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (k i : Fin s) : BooleanNetwork n w :=
  mulMod (a.comp (blockNet s w i)) (b.comp (blockNet s w (k-i))) m

def cyclicMulNet {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) : BooleanNetwork n (s*w) :=
  wordBlocks (fun k => sumMod m (List.ofFn (cyclicTerm a b m k)))

lemma cyclicMulNet_value {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat)
    (k : Fin s) :
    (bitsValue (block ((cyclicMulNet a b m).eval x) k)).toNat =
      (∑ i : Fin s, (bitsValue (block (a.eval x) i)).toNat *
        (bitsValue (block (b.eval x) (k-i))).toNat) % (bitsValue (m.eval x)).toNat := by
  rw [cyclicMulNet,wordBlocks_eval,sumMod_value _ _ _ hm]
  simp only [List.map_ofFn,List.sum_ofFn]
  have hh : ∀ i : Fin s, (bitsValue ((cyclicTerm a b m k i).eval x)).toNat =
      ((bitsValue (block (a.eval x) i)).toNat *
        (bitsValue (block (b.eval x) (k-i))).toNat) % (bitsValue (m.eval x)).toNat := by
    intro i
    rw [cyclicTerm,mulMod_word _ _ _ _ hm]
    simp only [eval_comp,blockNet_eval]
  simp only [Function.comp_apply]
  simp_rw [hh]
  exact (Finset.sum_nat_mod _ _ _).symm

lemma cyclicMulNet_correct {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat) :
    decodeCyclic (bitsValue (m.eval x)).toNat ((cyclicMulNet a b m).eval x) =
      decodeCyclic (bitsValue (m.eval x)).toNat (a.eval x)*
        decodeCyclic (bitsValue (m.eval x)).toNat (b.eval x) := by
  ext k
  rw [decodeCyclic_coeff,cyclicMulNet_value _ _ _ _ hm,cyclic_mul_coeff]
  simp only [ZMod.natCast_mod,Nat.cast_sum,Nat.cast_mul,decodeCyclic_coeff]

abbrev cyclicMulBound (s w ac bc mc : ℕ) : ℕ :=
  s*w*(w+s*(ac+bc+2*mc+(1224*w*w+143*w+12)+216*(w+1)^2+142*(w+1)+15))

lemma cyclicTerm_count {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (k i : Fin s) :
    (cyclicTerm a b m k i).net.count ≤ a.net.count+b.net.count+m.net.count+
      (1224*w*w+143*w+12) := by
  have h := mulMod_count (a.comp (blockNet s w i)) (b.comp (blockNet s w (k-i))) m
  simpa only [cyclicTerm,count_comp,blockNet_count,add_zero] using h

lemma cyclicMulNet_count {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) : (cyclicMulNet a b m).net.count ≤
      cyclicMulBound s w a.net.count b.net.count m.net.count := by
  apply wordBlocks_count
  intro k
  have h := sumMod_count m (List.ofFn (cyclicTerm a b m k)) (by
    intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    exact cyclicTerm_count a b m k i)
  simp only [List.length_ofFn] at h
  
  nlinarith

/-- Canonical representatives permit exact word comparison of arrays. -/
def CanonicalCyclic {s w : ℕ} (m : ℕ) (x : Basis (s*w)) : Prop :=
  ∀ i : Fin s, (bitsValue (block x i)).toNat < m

lemma cyclicMulNet_canonical {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat) :
    CanonicalCyclic (bitsValue (m.eval x)).toNat ((cyclicMulNet a b m).eval x) := by
  intro k
  rw [cyclicMulNet_value _ _ _ _ hm]
  exact Nat.mod_lt _ hm

lemma decodeCyclic_injective {s w m : ℕ} (hm : 0 < m) {a b : Basis (s*w)}
    (ha : CanonicalCyclic m a) (hb : CanonicalCyclic m b)
    (hh : decodeCyclic m a=decodeCyclic m b) : a=b := by
  let : NeZero m := ⟨by omega⟩
  have hv : ∀ i : Fin s, bitsValue (block a i)=bitsValue (block b i) := by
    intro i
    have he := congrArg (fun c : Cyclic (ZMod m) s => (c.coeff i).val) hh
    simp only [decodeCyclic_coeff,ZMod.val_natCast,Nat.mod_eq_of_lt (ha i),
      Nat.mod_eq_of_lt (hb i)] at he
    exact BitVec.eq_of_toNat_eq he
  funext k
  obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective k
  have he := congrArg (fun v : BitVec w => v.getLsbD j.val) (hv i)
  simpa only [bitsValue_bit,block] using he

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CyclicConstants.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality
open scoped BigOperators

def arrayConstant {n : ℕ} (s w : ℕ) (f : Fin s → ℕ) : BooleanNetwork n (s*w) :=
  wordBlocks (fun i => wordConstant (BitVec.ofNat w (f i)))

lemma arrayConstant_value {n s w : ℕ} (f : Fin s → ℕ) (x : Basis n) (i : Fin s) :
    (bitsValue (block ((arrayConstant s w f).eval x) i)).toNat = f i % 2^w := by
  rw [arrayConstant,wordBlocks_eval,wordConstant_eval,BitVec.toNat_ofNat]

lemma arrayConstant_count {n s w : ℕ} (f : Fin s → ℕ) :
    (arrayConstant (n := n) s w f).net.count ≤ s*w*w := by
  apply wordBlocks_count
  intro i
  exact (wordConstant_count _).le

def cyclicOne {n : ℕ} (s w : ℕ) [NeZero s] : BooleanNetwork n (s*w) :=
  arrayConstant s w (fun i => if i=0 then 1 else 0)

lemma cyclicOne_value {n s w m : ℕ} [NeZero s] (hw : 0 < w) (x : Basis n) :
    decodeCyclic m ((cyclicOne s w).eval x)=1 := by
  have hp : 1 < 2^w := Nat.one_lt_pow (by omega) (by decide)
  ext i
  rw [decodeCyclic_coeff,cyclicOne,arrayConstant_value,AddMonoidAlgebra.one_def]
  simp only [AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  split_ifs <;> simp_all [Nat.mod_eq_of_lt hp]

lemma cyclicOne_canonical {n s w m : ℕ} [NeZero s] (hm : 2 ≤ m) (x : Basis n) :
    CanonicalCyclic m ((cyclicOne s w).eval x) := by
  intro i
  rw [cyclicOne,arrayConstant_value]
  split_ifs
  · exact (Nat.mod_le _ _).trans_lt (by omega)
  · simp only [Nat.zero_mod]
    omega

def cyclicAddNet {n s w : ℕ} (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) : BooleanNetwork n (s*w) :=
  wordBlocks (fun i => addMod (a.comp (blockNet s w i)) (b.comp (blockNet s w i)) m)

lemma cyclicAddNet_value {n s w : ℕ} (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat)
    (i : Fin s) :
    (bitsValue (block ((cyclicAddNet a b m).eval x) i)).toNat =
      ((bitsValue (block (a.eval x) i)).toNat+(bitsValue (block (b.eval x) i)).toNat)%
        (bitsValue (m.eval x)).toNat := by
  rw [cyclicAddNet,wordBlocks_eval,addMod_value _ _ _ _ hm]
  simp only [eval_comp,blockNet_eval]

lemma cyclicAddNet_correct {n s w : ℕ} (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat) :
    decodeCyclic (bitsValue (m.eval x)).toNat ((cyclicAddNet a b m).eval x) =
      decodeCyclic (bitsValue (m.eval x)).toNat (a.eval x)+
        decodeCyclic (bitsValue (m.eval x)).toNat (b.eval x) := by
  ext i
  rw [decodeCyclic_coeff,cyclicAddNet_value _ _ _ _ hm]
  simp [ZMod.natCast_mod,decodeCyclic_coeff]

lemma cyclicAddNet_canonical {n s w : ℕ} (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat) :
    CanonicalCyclic (bitsValue (m.eval x)).toNat ((cyclicAddNet a b m).eval x) := by
  intro i
  rw [cyclicAddNet_value _ _ _ _ hm]
  exact Nat.mod_lt _ hm

lemma cyclicAddNet_count {n s w : ℕ} (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) : (cyclicAddNet a b m).net.count ≤
      s*w*(a.net.count+b.net.count+m.net.count+216*(w+1)^2+142*(w+1)+15) := by
  apply wordBlocks_count
  intro i
  have h := addMod_count (a.comp (blockNet s w i)) (b.comp (blockNet s w i)) m
  simpa only [count_comp,blockNet_count,add_zero] using h

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CyclicPowerCircuit.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality

abbrev cyclicPowerWidth (s w b : ℕ) := ((s*w+w)+b)+s*w

def cyclicPack {s w b : ℕ} (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) : Basis (cyclicPowerWidth s w b) :=
  Fin.append (Fin.append (Fin.append a m) e) z

def cyclicBase (s w b : ℕ) : BooleanNetwork (cyclicPowerWidth s w b) (s*w) :=
  select (fun i => ((i.castAdd w).castAdd b).castAdd (s*w))
def cyclicMod (s w b : ℕ) : BooleanNetwork (cyclicPowerWidth s w b) w :=
  select (fun i => ((Fin.natAdd (s*w) i).castAdd b).castAdd (s*w))
def cyclicAcc (s w b : ℕ) : BooleanNetwork (cyclicPowerWidth s w b) (s*w) :=
  select (Fin.natAdd ((s*w+w)+b))
def cyclicBit (s w : ℕ) {b : ℕ} (i : Fin b) : BooleanNetwork (cyclicPowerWidth s w b) 1 :=
  bit ((Fin.natAdd (s*w+w) i).castAdd (s*w))

@[simp] lemma cyclicBase_eval {s w b : ℕ} (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) : (cyclicBase s w b).eval (cyclicPack a m e z)=a := by
  funext i
  simp only [cyclicBase,eval_select,Function.comp_apply,cyclicPack,Fin.append_left]
@[simp] lemma cyclicMod_eval {s w b : ℕ} (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) : (cyclicMod s w b).eval (cyclicPack a m e z)=m := by
  funext i
  simp only [cyclicMod,eval_select,Function.comp_apply,cyclicPack,Fin.append_left,Fin.append_right]
@[simp] lemma cyclicAcc_eval {s w b : ℕ} (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) : (cyclicAcc s w b).eval (cyclicPack a m e z)=z := by
  funext i
  simp only [cyclicAcc,eval_select,Function.comp_apply,cyclicPack,Fin.append_right]
@[simp] lemma cyclicBit_eval {s w b : ℕ} (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) (i : Fin b) : (cyclicBit s w i).eval (cyclicPack a m e z) 0=e i := by
  simp only [cyclicBit,eval_bit,cyclicPack,Fin.append_left,Fin.append_right]

def cyclicNew (s w : ℕ) [NeZero s] {b : ℕ} (i : Fin b) :
    BooleanNetwork (cyclicPowerWidth s w b) (s*w) :=
  let sq := cyclicMulNet (cyclicAcc s w b) (cyclicAcc s w b) (cyclicMod s w b)
  wordMux (cyclicBit s w i) (cyclicMulNet sq (cyclicBase s w b) (cyclicMod s w b)) sq

def cyclicStep (s w : ℕ) [NeZero s] {b : ℕ} (i : Fin b) :
    BooleanNetwork (cyclicPowerWidth s w b) (cyclicPowerWidth s w b) :=
  (select (Fin.castAdd (s*w))).pair (cyclicNew s w i)

lemma cyclicStep_pack {s w b : ℕ} [NeZero s] (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) (i : Fin b) :
    (cyclicStep s w i).eval (cyclicPack a m e z)=
      cyclicPack a m e ((cyclicNew s w i).eval (cyclicPack a m e z)) := by
  simp only [cyclicStep,eval_pair,eval_select,cyclicPack]
  congr 1
  funext j
  exact Fin.append_left _ _ j

lemma cyclicNew_value {s w b : ℕ} [NeZero s] (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) (i : Fin b) (hm : 0 < (bitsValue m).toNat) :
    decodeCyclic (bitsValue m).toNat ((cyclicNew s w i).eval (cyclicPack a m e z)) =
      if e i then decodeCyclic (bitsValue m).toNat z ^ 2 * decodeCyclic (bitsValue m).toNat a
        else decodeCyclic (bitsValue m).toNat z ^ 2 := by
  have hm' : 0 < (bitsValue ((cyclicMod s w b).eval (cyclicPack a m e z))).toNat := by
    simpa only [cyclicMod_eval] using hm
  have hs := cyclicMulNet_correct (cyclicAcc s w b) (cyclicAcc s w b)
    (cyclicMod s w b) (cyclicPack a m e z) hm'
  have hp := cyclicMulNet_correct
    (cyclicMulNet (cyclicAcc s w b) (cyclicAcc s w b) (cyclicMod s w b))
    (cyclicBase s w b) (cyclicMod s w b) (cyclicPack a m e z) hm'
  rw [cyclicMod_eval] at hs hp
  simp only [cyclicAcc_eval,cyclicBase_eval] at hs hp
  rw [cyclicNew,wordMux_eval,cyclicBit_eval]
  split
  · rw [hp,hs,pow_two]
  · rw [hs,pow_two]

lemma cyclicNew_canonical {s w b : ℕ} [NeZero s] (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) (i : Fin b) (hm : 0 < (bitsValue m).toNat) :
    CanonicalCyclic (bitsValue m).toNat ((cyclicNew s w i).eval (cyclicPack a m e z)) := by
  have hm' : 0 < (bitsValue ((cyclicMod s w b).eval (cyclicPack a m e z))).toNat := by
    simpa only [cyclicMod_eval] using hm
  rw [cyclicNew,wordMux_eval,cyclicBit_eval]
  split <;>
    simpa only [cyclicMod_eval] using (cyclicMulNet_canonical _ _ _ _ hm')

lemma cyclicMulBound_mono {s w a b c a' b' c' : ℕ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    cyclicMulBound s w a b c ≤ cyclicMulBound s w a' b' c' := by
  dsimp [cyclicMulBound]
  gcongr

abbrev cyclicStepBound (s w : ℕ) :=
  cyclicMulBound s w (cyclicMulBound s w 0 0 0) 0 0 + cyclicMulBound s w 0 0 0+7*(s*w)

lemma cyclicNew_count (s w : ℕ) [NeZero s] {b : ℕ} (i : Fin b) :
    (cyclicNew s w i).net.count ≤ cyclicStepBound s w := by
  let sq := cyclicMulNet (cyclicAcc s w b) (cyclicAcc s w b) (cyclicMod s w b)
  have hs : sq.net.count ≤ cyclicMulBound s w 0 0 0 := cyclicMulNet_count _ _ _
  have hh : (cyclicMulNet sq (cyclicBase s w b) (cyclicMod s w b)).net.count ≤
      cyclicMulBound s w (cyclicMulBound s w 0 0 0) 0 0 :=
    (cyclicMulNet_count sq (cyclicBase s w b) (cyclicMod s w b)).trans
      (cyclicMulBound_mono hs (by rfl) (by rfl))
  simp only [cyclicNew,wordMux_count,cyclicBit,count_bit,zero_add]
  change (cyclicMulNet sq (cyclicBase s w b) (cyclicMod s w b)).net.count +
    sq.net.count + 7*(s*w) ≤ cyclicStepBound s w
  dsimp [cyclicStepBound]
  omega

lemma cyclicStep_count (s w : ℕ) [NeZero s] {b : ℕ} (i : Fin b) :
    (cyclicStep s w i).net.count ≤ cyclicStepBound s w := by
  simpa only [cyclicStep,count_pair,count_select,zero_add] using cyclicNew_count s w i

def cyclicPrefix (s w b : ℕ) [NeZero s] : (k : ℕ) → k ≤ b →
    BooleanNetwork (cyclicPowerWidth s w b) (cyclicPowerWidth s w b)
  | 0,_ => select id
  | k+1,h => (cyclicPrefix s w b k (by omega)).comp (cyclicStep s w ⟨k,by omega⟩)

lemma cyclicPrefix_count (s w b k : ℕ) [NeZero s] (hk : k ≤ b) :
    (cyclicPrefix s w b k hk).net.count ≤ k*cyclicStepBound s w := by
  induction k with
  | zero => simp [cyclicPrefix]
  | succ k ih =>
    have h := cyclicStep_count s w (⟨k,by omega⟩ : Fin b)
    have hi := ih (by omega)
    simp only [cyclicPrefix,count_comp]
    nlinarith

lemma cyclicPrefix_value {s w b : ℕ} [NeZero s] (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z₀ : Basis (s*w)) (hm : 0 < (bitsValue m).toNat)
    (h₀ : decodeCyclic (bitsValue m).toNat z₀=1) (hc : CanonicalCyclic (bitsValue m).toNat z₀)
    (k : ℕ) (hk : k ≤ b) :
    ∃ z : Basis (s*w), (cyclicPrefix s w b k hk).eval (cyclicPack a m e z₀)=cyclicPack a m e z ∧
      decodeCyclic (bitsValue m).toNat z=decodeCyclic (bitsValue m).toNat a ^horner e k hk ∧
      CanonicalCyclic (bitsValue m).toNat z := by
  induction k with
  | zero => exact ⟨z₀,by simp [cyclicPrefix],by simpa only [horner,pow_zero] using h₀,hc⟩
  | succ k ih =>
    obtain ⟨z,hz,hv,_hzc⟩ := ih (by omega)
    refine ⟨(cyclicNew s w ⟨k,by omega⟩).eval (cyclicPack a m e z),?_,?_,
      cyclicNew_canonical _ _ _ _ _ hm⟩
    · rw [cyclicPrefix,eval_comp,hz,cyclicStep_pack]
    · rw [cyclicNew_value _ _ _ _ _ hm,hv]
      cases he : e (⟨k,by omega⟩ : Fin b)
      · simp only [horner,he,Bool.false_eq_true,ite_false,Bool.toNat_false,Nat.add_zero]
        rw [← pow_mul,Nat.mul_comm (horner e k _) 2]
      · simp only [horner,he,ite_true,Bool.toNat_true]
        rw [← pow_mul,pow_succ,Nat.mul_comm (horner e k _) 2]

/-- n-bit repeated squaring in the coefficient array; no exponential polynomial
or algebraic root is part of the computation. -/
def cyclicPower (s w b : ℕ) [NeZero s] : BooleanNetwork ((s*w+w)+b) (s*w) :=
  ((select id).pair (cyclicOne s w)).comp
    ((cyclicPrefix s w b b le_rfl).rewire (Fin.natAdd ((s*w+w)+b)))

lemma cyclicPower_count (s w b : ℕ) [NeZero s] :
    (cyclicPower s w b).net.count ≤ s*w*w+b*cyclicStepBound s w := by
  have h₁ := arrayConstant_count (n := (s*w+w)+b) (s := s) (w := w) (fun i => if i=0 then 1 else 0)
  have h₂ := cyclicPrefix_count s w b b le_rfl
  simp only [cyclicPower,count_comp,count_pair,count_select,count_rewire,zero_add]
  change (arrayConstant s w _).net.count + _ ≤ _
  omega

lemma cyclicPower_value {s w b : ℕ} [NeZero s] (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (hw : 0 < w) (hm : 2 ≤ (bitsValue m).toNat) :
    decodeCyclic (bitsValue m).toNat ((cyclicPower s w b).eval (Fin.append (Fin.append a m) e))=
      decodeCyclic (bitsValue m).toNat a ^ horner e b le_rfl ∧
    CanonicalCyclic (bitsValue m).toNat ((cyclicPower s w b).eval (Fin.append (Fin.append a m) e)) := by
  let input := Fin.append (Fin.append a m) e
  obtain ⟨z,hz,hv,hc⟩ := cyclicPrefix_value a m e ((cyclicOne s w).eval input)
    (by omega) (cyclicOne_value hw input) (cyclicOne_canonical hm input) b le_rfl
  have he : (cyclicPower s w b).eval input=z := by
    simp only [cyclicPower,eval_comp,eval_rewire,eval_pair,eval_select,Function.comp_id]
    change ((cyclicPrefix s w b b le_rfl).eval
      (cyclicPack a m e ((cyclicOne s w).eval input))) ∘ Fin.natAdd ((s*w+w)+b)=z
    rw [hz]
    funext i
    exact Fin.append_right _ _ i
  change decodeCyclic (bitsValue m).toNat ((cyclicPower s w b).eval input)=_ ∧
    CanonicalCyclic (bitsValue m).toNat ((cyclicPower s w b).eval input)
  rw [he]
  exact ⟨hv,hc⟩

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CyclicTestCircuit.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality

lemma arrayConstant_decode {n s w m : ℕ} (f : Fin s → ℕ)
    (hf : ∀ i, f i < 2^w) (x : Basis n) :
    decodeCyclic m ((arrayConstant s w f).eval x)=cyclicOf (fun i => (f i : ZMod m)) := by
  ext i
  rw [decodeCyclic_coeff,arrayConstant_value,cyclicOf_coeff,Nat.mod_eq_of_lt (hf i)]

def cyclicXNet {n : ℕ} (s w : ℕ) [NeZero s] : BooleanNetwork n (s*w) :=
  arrayConstant s w (fun i => if i=1 then 1 else 0)
def cyclicCNet {n : ℕ} (s w a : ℕ) [NeZero s] : BooleanNetwork n (s*w) :=
  arrayConstant s w (fun i => if i=0 then a else 0)

lemma cyclicXNet_value {n s w m : ℕ} [NeZero s] (hw : 0 < w) (x : Basis n) :
    decodeCyclic m ((cyclicXNet s w).eval x)=cyclicX s := by
  have hp : 1 < 2^w := Nat.one_lt_pow (by omega) (by decide)
  unfold cyclicXNet
  rw [arrayConstant_decode _ (by intro i; split_ifs <;> omega)]
  ext i
  simp only [cyclicOf_coeff,cyclicX,AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  split_ifs <;> simp_all

lemma cyclicCNet_value {n s w m a : ℕ} [NeZero s] (ha : a < 2^w) (x : Basis n) :
    decodeCyclic m ((cyclicCNet s w a).eval x)=cyclicC s (a : ZMod m) := by
  unfold cyclicCNet
  rw [arrayConstant_decode _ (by intro i; split_ifs <;> omega)]
  ext i
  simp only [cyclicOf_coeff,cyclicC,AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  split_ifs <;> simp_all

def cyclicPowerOn {n s w b : ℕ} [NeZero s] (a : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (e : BooleanNetwork n b) : BooleanNetwork n (s*w) :=
  ((a.pair m).pair e).comp (cyclicPower s w b)

lemma cyclicPowerOn_value {n s w b : ℕ} [NeZero s] (a : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (e : BooleanNetwork n b) (x : Basis n)
    (hw : 0 < w) (hm : 2 ≤ (bitsValue (m.eval x)).toNat) :
    decodeCyclic (bitsValue (m.eval x)).toNat ((cyclicPowerOn a m e).eval x)=
      decodeCyclic (bitsValue (m.eval x)).toNat (a.eval x)^horner (e.eval x) b le_rfl ∧
    CanonicalCyclic (bitsValue (m.eval x)).toNat ((cyclicPowerOn a m e).eval x) := by
  simpa only [cyclicPowerOn,eval_comp,eval_pair] using
    cyclicPower_value (a.eval x) (m.eval x) (e.eval x) hw hm

lemma cyclicPowerOn_count {n s w b : ℕ} [NeZero s] (a : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (e : BooleanNetwork n b) :
    (cyclicPowerOn a m e).net.count ≤ a.net.count+m.net.count+e.net.count+
      s*w*w+b*cyclicStepBound s w := by
  have h := cyclicPower_count s w b
  simp only [cyclicPowerOn,count_comp,count_pair]
  omega

lemma horner_reverse {w : ℕ} (x : Basis w) :
    horner (x ∘ Fin.rev) w le_rfl = (bitsValue x).toNat := by
  rw [horner_full,Triangular.inputNumber_reverse]
  congr 2
  funext i
  simp [reverseBits]

/-- Literal 8s AKS congruence on s coefficient words, m in the input word. -/
def cyclicTest (s w a : ℕ) [NeZero s] : BooleanNetwork w 1 :=
  let m := select id
  let e := select Fin.rev
  let X := cyclicXNet s w
  let C := cyclicCNet s w a
  let lhs := cyclicPowerOn (cyclicAddNet X C m) m e
  let rhs := cyclicAddNet (cyclicPowerOn X m e) C m
  (lhs.pair rhs).comp (wordEq (s*w))

lemma cyclicTest_correct (s w a : ℕ) [NeZero s] (x : Basis w)
    (hw : 0 < w) (hm : 2 ≤ (bitsValue x).toNat) (ha : a < 2^w) :
    (cyclicTest s w a).eval x 0=true ↔
      (cyclicX s+cyclicC s (a : ZMod (bitsValue x).toNat) : Cyclic (ZMod (bitsValue x).toNat) s)^
        (bitsValue x).toNat = cyclicX s^(bitsValue x).toNat+cyclicC s (a : ZMod (bitsValue x).toNat) := by
  let m : BooleanNetwork w w := select id
  let e : BooleanNetwork w w := select Fin.rev
  let X : BooleanNetwork w (s*w) := cyclicXNet s w
  let C : BooleanNetwork w (s*w) := cyclicCNet s w a
  let lhs := cyclicPowerOn (cyclicAddNet X C m) m e
  let rhs := cyclicAddNet (cyclicPowerOn X m e) C m
  have hm' : 2 ≤ (bitsValue (m.eval x)).toNat := hm
  have hl := cyclicPowerOn_value (cyclicAddNet X C m) m e x hw hm'
  have hX := cyclicPowerOn_value X m e x hw hm'
  have ha' := cyclicAddNet_correct X C m x (by omega)
  have hr := cyclicAddNet_correct (cyclicPowerOn X m e) C m x (by omega)
  have hrc := cyclicAddNet_canonical (cyclicPowerOn X m e) C m x (by omega)
  have he : horner (e.eval x) w le_rfl=(bitsValue x).toNat := horner_reverse x
  have hx : decodeCyclic (bitsValue (m.eval x)).toNat (X.eval x)=cyclicX s := cyclicXNet_value hw x
  have hc : decodeCyclic (bitsValue x).toNat (C.eval x)=cyclicC s (a : ZMod (bitsValue x).toNat) :=
    cyclicCNet_value ha x
  have hmval : m.eval x=x := by simp [m]
  rw [hmval] at hl hX ha' hr hrc hx
  have hleft : decodeCyclic (bitsValue x).toNat (lhs.eval x)=
      (cyclicX s+cyclicC s (a : ZMod (bitsValue x).toNat))^(bitsValue x).toNat := by
    change decodeCyclic (bitsValue x).toNat ((cyclicPowerOn (cyclicAddNet X C m) m e).eval x)=_
    rw [hl.1,ha',hx,hc,he]
  have hright : decodeCyclic (bitsValue x).toNat (rhs.eval x)=
      cyclicX s^(bitsValue x).toNat+cyclicC s (a : ZMod (bitsValue x).toNat) := by
    change decodeCyclic (bitsValue x).toNat ((cyclicAddNet (cyclicPowerOn X m e) C m).eval x)=_
    rw [hr,hX.1,hx,hc,he]
  change ((lhs.pair rhs).comp (wordEq (s*w))).eval x 0=true ↔ _
  rw [eval_comp,eval_pair,wordEq_eval,decide_eq_true_eq]
  rw [show bitsValue (lhs.eval x)=bitsValue (rhs.eval x) ↔ lhs.eval x=rhs.eval x from
    (bitsEquiv (s*w)).injective.eq_iff]
  constructor
  · intro h
    have hh := congrArg (decodeCyclic (bitsValue x).toNat) h
    simpa only [hleft,hright] using hh
  · intro h
    apply decodeCyclic_injective (by omega) hl.2 hrc
    change decodeCyclic (bitsValue x).toNat (lhs.eval x)=decodeCyclic (bitsValue x).toNat (rhs.eval x)
    rw [hleft,hright]
    exact h

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CyclicTestBounds.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

abbrev cyclicAddBound (s w ac bc mc : ℕ) :=
  s*w*(ac+bc+mc+216*(w+1)^2+142*(w+1)+15)

lemma cyclicAddBound_mono {s w a b c a' b' c' : ℕ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    cyclicAddBound s w a b c ≤ cyclicAddBound s w a' b' c' := by
  dsimp [cyclicAddBound]
  gcongr

abbrev cyclicTestBound (s w : ℕ) :=
  cyclicAddBound s w (s*w*w) (s*w*w) 0+s*w*w+w*cyclicStepBound s w+
    cyclicAddBound s w (2*(s*w*w)+w*cyclicStepBound s w) (s*w*w) 0+96*(s*w)+21

lemma cyclicTest_count (s w a : ℕ) [NeZero s] :
    (cyclicTest s w a).net.count ≤ cyclicTestBound s w := by
  let m : BooleanNetwork w w := select id
  let e : BooleanNetwork w w := select Fin.rev
  let X : BooleanNetwork w (s*w) := cyclicXNet s w
  let C : BooleanNetwork w (s*w) := cyclicCNet s w a
  let lhs := cyclicPowerOn (cyclicAddNet X C m) m e
  let rhs := cyclicAddNet (cyclicPowerOn X m e) C m
  have hx : X.net.count ≤ s*w*w := arrayConstant_count _
  have hc : C.net.count ≤ s*w*w := arrayConstant_count _
  have hm : m.net.count=0 := rfl
  have he : e.net.count=0 := rfl
  have ha : (cyclicAddNet X C m).net.count ≤ cyclicAddBound s w (s*w*w) (s*w*w) 0 :=
    (cyclicAddNet_count X C m).trans (cyclicAddBound_mono hx hc (by rfl))
  have hl := cyclicPowerOn_count (cyclicAddNet X C m) m e
  rw [hm,he] at hl
  have hp : (cyclicPowerOn X m e).net.count ≤ 2*(s*w*w)+w*cyclicStepBound s w := by
    have h := cyclicPowerOn_count X m e
    rw [hm,he] at h
    omega
  have hr : rhs.net.count ≤ cyclicAddBound s w (2*(s*w*w)+w*cyclicStepBound s w) (s*w*w) 0 :=
    (cyclicAddNet_count (cyclicPowerOn X m e) C m).trans
      (cyclicAddBound_mono hp hc (by rfl))
  have hq := wordEq_count (s*w)
  change ((lhs.pair rhs).comp (wordEq (s*w))).net.count ≤ _
  rw [count_comp,count_pair]
  change (cyclicPowerOn (cyclicAddNet X C m) m e).net.count+rhs.net.count+_ ≤ _
  dsimp [cyclicTestBound]
  omega

lemma cyclicStepBound_mono {s w s' w' : ℕ} (hs : s ≤ s') (hw : w ≤ w') :
    cyclicStepBound s w ≤ cyclicStepBound s' w' := by
  unfold cyclicStepBound cyclicMulBound
  gcongr

lemma cyclicTestBound_mono {s w s' w' : ℕ} (hs : s ≤ s') (hw : w ≤ w') :
    cyclicTestBound s w ≤ cyclicTestBound s' w' := by
  unfold cyclicTestBound cyclicAddBound
  gcongr <;> exact cyclicStepBound_mono hs hw

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BinaryRoots.lean =====
namespace OAI

section
open scoped BigOperators


/-! Bounded binary-root search required by the appendix's perfect-power check.
The search uses only comparisons and powers with exponent at most the input
bit bound; no unbounded Nat.nthRoot primitive is used by the algorithm. -/
namespace ExactQuantumFactoring.Primality

def rootSearch (m e : ℕ) : (k guess : ℕ) → ℕ
  | 0, guess => guess
  | k+1, guess =>
      let next := guess+2^k
      rootSearch m e k (if next^e ≤ m then next else guess)

lemma rootSearch_spec {m e : ℕ} (_he : 0 < e) (k guess : ℕ)
    (hlo : guess^e ≤ m) (hhi : m < (guess+2^k)^e) :
    (rootSearch m e k guess)^e ≤ m ∧ m < (rootSearch m e k guess+1)^e := by
  induction k generalizing guess with
  | zero => simpa only [rootSearch,pow_zero] using And.intro hlo hhi
  | succ k ih =>
    simp only [rootSearch]
    by_cases hnext : (guess+2^k)^e ≤ m
    · rw [ite_eq_left hnext]
      apply ih _ hnext
      have hh : guess+2^k+2^k=guess+2^(k+1) := by rw [pow_succ]; omega
      rw [hh]
      exact hhi
    · rw [ite_eq_right hnext]
      exact ih _ hlo (by omega)

lemma rootSearch_eq {m e : ℕ} (he : 0 < e) (k guess b : ℕ)
    (hlo : guess^e ≤ m) (hhi : m < (guess+2^k)^e) (hb : b^e=m) :
    rootSearch m e k guess=b := by
  obtain ⟨hl,hh⟩ := rootSearch_spec he k guess hlo hhi
  have hl' : rootSearch m e k guess ≤ b :=
    (Nat.pow_le_pow_iff_left he.ne').mp (hl.trans_eq hb.symm)
  have hh' : b < rootSearch m e k guess+1 :=
    (Nat.pow_lt_pow_iff_left he.ne').mp (hb ▸ hh)
  omega

def boundedRoot (m e n : ℕ) : ℕ := rootSearch m e n 0

lemma boundedRoot_spec {m e n : ℕ} (he : 0 < e) (hm : m < 2^n) :
    (boundedRoot m e n)^e ≤ m ∧ m < (boundedRoot m e n+1)^e := by
  apply rootSearch_spec he n 0
  · simp [Nat.ne_of_gt he]
  · simp only [zero_add]
    exact hm.trans_le (Nat.le_self_pow he.ne' (2^n))

lemma boundedRoot_pow_eq {m e n b : ℕ} (he : 0 < e) (hm : m < 2^n) (hb : b^e=m) :
    boundedRoot m e n=b := by
  apply rootSearch_eq he n 0 b
  · simp [Nat.ne_of_gt he]
  · simp only [zero_add]
    exact hm.trans_le (Nat.le_self_pow he.ne' (2^n))
  · exact hb

lemma perfectPower_exponent_lt {m n b e : ℕ} (hm : m < 2^n) (hb : 2 ≤ b)
    (h : b^e=m) : e < n := by
  have hh : 2^e < 2^n := (Nat.pow_le_pow_left hb e).trans_lt (h ▸ hm)
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hh

end ExactQuantumFactoring.Primality


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RootCircuit.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

/-- Width large enough for every candidate's e-th power, e≤n. -/
abbrev rootWidth (n : ℕ) := n*n+1

def rootModulus (w : ℕ) : BooleanNetwork (w+w) w := select (Fin.castAdd w)
def rootGuess (w : ℕ) : BooleanNetwork (w+w) w := select (Fin.natAdd w)

def rootNext (w k : ℕ) : BooleanNetwork (w+w) w :=
  ((rootGuess w).pair (wordConstant (BitVec.ofNat w (2^k)))).comp (add w)

def rootNew (w e k : ℕ) : BooleanNetwork (w+w) w :=
  wordMux (wordLe ((rootNext w k).comp (staticPower w e)) (rootModulus w))
    (rootNext w k) (rootGuess w)

def rootStep (w e k : ℕ) : BooleanNetwork (w+w) (w+w) :=
  (rootModulus w).pair (rootNew w e k)

def rootPrefix (w e : ℕ) : ℕ → BooleanNetwork (w+w) (w+w)
  | 0 => select id
  | k+1 => (rootStep w e k).comp (rootPrefix w e k)

lemma rootModulus_eval (w : ℕ) (m g : Basis w) :
    (rootModulus w).eval (Fin.append m g)=m := by
  funext i
  exact Fin.append_left m g i
lemma rootGuess_eval (w : ℕ) (m g : Basis w) :
    (rootGuess w).eval (Fin.append m g)=g := by
  funext i
  exact Fin.append_right m g i

lemma rootNext_word (w k : ℕ) (m g : Basis w) :
    bitsValue ((rootNext w k).eval (Fin.append m g)) =
      bitsValue g + BitVec.ofNat w (2^k) := by
  rw [rootNext,eval_comp,eval_pair,add_word,rootGuess_eval,wordConstant_eval]

lemma rootStep_pack (w e k : ℕ) (m g : Basis w) :
    (rootStep w e k).eval (Fin.append m g) =
      Fin.append m ((rootNew w e k).eval (Fin.append m g)) := by
  rw [rootStep,eval_pair,rootModulus_eval]

lemma rootNext_value {n k : ℕ} (m g : Basis (rootWidth n))
    (hk : k ≤ n) (hg : (bitsValue g).toNat+2^k ≤ 2^n) :
    (bitsValue ((rootNext (rootWidth n) k).eval (Fin.append m g))).toNat =
      (bitsValue g).toNat+2^k := by
  have hn : n < rootWidth n := by dsimp [rootWidth]; nlinarith
  have hp : 2^n < 2^(rootWidth n) := Nat.pow_lt_pow_right (by decide) hn
  have hkp : 2^k < 2^(rootWidth n) :=
    (Nat.pow_le_pow_right (by decide) hk).trans_lt hp
  rw [rootNext_word,BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hkp,
    Nat.mod_eq_of_lt (hg.trans_lt hp)]

lemma candidatePower_lt {n e v : ℕ} (he : e ≤ n) (hv : v ≤ 2^n) :
    v^e < 2^(rootWidth n) := by
  have hne : n*e ≤ n*n := Nat.mul_le_mul_left n he
  calc
    v^e ≤ (2^n)^e := Nat.pow_le_pow_left hv e
    _ = 2^(n*e) := (pow_mul 2 n e).symm
    _ ≤ 2^(n*n) := Nat.pow_le_pow_right (by decide) hne
    _ < 2^(rootWidth n) := Nat.pow_lt_pow_right (by decide) (by simp [rootWidth])

lemma rootNew_value {n e k : ℕ} (m g : Basis (rootWidth n))
    (he : e ≤ n) (hk : k ≤ n) (hg : (bitsValue g).toNat+2^k ≤ 2^n) :
    (bitsValue ((rootNew (rootWidth n) e k).eval (Fin.append m g))).toNat =
      if ((bitsValue g).toNat+2^k)^e ≤ (bitsValue m).toNat
      then (bitsValue g).toNat+2^k else (bitsValue g).toNat := by
  have hv := rootNext_value m g hk hg
  rw [rootNew,wordMux_eval,wordLe_eval,eval_comp,staticPower_eval,rootModulus_eval]
  rw [BitVec.toNat_pow,hv,Nat.mod_eq_of_lt (candidatePower_lt he hg)]
  split_ifs <;> simp_all [rootGuess_eval]

lemma rootPrefix_value {n e : ℕ} (m g : Basis (rootWidth n)) (he : e ≤ n)
    (k : ℕ) (hk : k ≤ n) (hg : (bitsValue g).toNat+2^k ≤ 2^n) :
    ∃ z : Basis (rootWidth n),
      (rootPrefix (rootWidth n) e k).eval (Fin.append m g) = Fin.append m z ∧
      (bitsValue z).toNat = Primality.rootSearch (bitsValue m).toNat e k (bitsValue g).toNat := by
  induction k generalizing g with
  | zero => exact ⟨g,rfl,rfl⟩
  | succ k ih =>
    have hg' : (bitsValue g).toNat+2^k ≤ 2^n := by
      have : 2^k ≤ 2^(k+1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    let z := (rootNew (rootWidth n) e k).eval (Fin.append m g)
    have hz : (bitsValue z).toNat =
        if ((bitsValue g).toNat+2^k)^e ≤ (bitsValue m).toNat
        then (bitsValue g).toNat+2^k else (bitsValue g).toNat := rootNew_value m g he (by omega) hg'
    have hzk : (bitsValue z).toNat+2^k ≤ 2^n := by
      rw [hz]
      split_ifs
      · rw [pow_succ] at hg
        omega
      · exact hg'
    obtain ⟨z',hz',hv'⟩ := ih z (by omega) hzk
    refine ⟨z',?_,?_⟩
    · rw [rootPrefix,eval_comp,rootStep_pack]
      exact hz'
    · rw [hv',hz]
      rfl

lemma rootNext_count (w k : ℕ) : (rootNext w k).net.count ≤ 87*w+6 := by
  simp only [rootNext,count_comp,count_pair,rootGuess,count_select,wordConstant_count,zero_add]
  have := add_count w
  omega

lemma rootStep_count (w e k : ℕ) : (rootStep w e k).net.count ≤
    230*w+21+e*(90*w*w+14*w+6) := by
  have h₁ := rootNext_count w k
  have h₂ := staticPower_count w e
  have h₃ := wordLe_count ((rootNext w k).comp (staticPower w e)) (rootModulus w)
  simp only [count_comp,rootModulus,count_select] at h₃
  simp only [rootStep,count_pair,rootModulus,count_select,zero_add,rootNew,wordMux_count,
    rootGuess,count_select,add_zero]
  omega

lemma rootPrefix_count (w e k : ℕ) : (rootPrefix w e k).net.count ≤
    k*(230*w+21+e*(90*w*w+14*w+6)) := by
  induction k with
  | zero => simp [rootPrefix]
  | succ k ih =>
    have h := rootStep_count w e k
    rw [rootPrefix,count_comp]
    nlinarith

def boundedRootNet (n e : ℕ) : BooleanNetwork (rootWidth n) (rootWidth n) :=
  ((select id).pair (wordConstant (BitVec.ofNat (rootWidth n) 0))).comp
    ((rootPrefix (rootWidth n) e n).rewire (Fin.natAdd (rootWidth n)))

lemma boundedRootNet_value (n e : ℕ) (he : e ≤ n) (m : Basis (rootWidth n)) :
    (bitsValue ((boundedRootNet n e).eval m)).toNat =
      Primality.boundedRoot (bitsValue m).toNat e n := by
  let g := (wordConstant (BitVec.ofNat (rootWidth n) 0)).eval m
  have hg : (bitsValue g).toNat=0 := by
    dsimp [g]
    rw [wordConstant_eval]
    simp
  obtain ⟨z,hz,hv⟩ := rootPrefix_value m g he n le_rfl (by rw [hg];omega)
  simp only [boundedRootNet,eval_comp,eval_pair,eval_select,Function.comp_id,eval_rewire]
  change (bitsValue (((rootPrefix (rootWidth n) e n).eval (Fin.append m g)) ∘
    Fin.natAdd (rootWidth n))).toNat = _
  rw [hz]
  have hh : Fin.append m z ∘ Fin.natAdd (rootWidth n)=z := by
    funext i
    exact Fin.append_right m z i
  rw [hh,hv,hg]
  rfl

lemma boundedRootNet_count (n e : ℕ) : (boundedRootNet n e).net.count ≤
    rootWidth n+n*(230*rootWidth n+21+e*(90*rootWidth n*rootWidth n+14*rootWidth n+6)) := by
  have h := rootPrefix_count (rootWidth n) e n
  simp only [boundedRootNet,count_comp,count_pair,count_select,wordConstant_count,
    zero_add,count_rewire]
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PerfectPowerCircuit.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

/-- Check a candidate root against the input integer, with its static exponent. -/
def rootCheck (w e : ℕ) : BooleanNetwork (w+w) 1 :=
  (wordLe (wordConstant (BitVec.ofNat w 2)) (rootGuess w)).band
    ((((rootGuess w).comp (staticPower w e)).pair (rootModulus w)).comp (wordEq w))

lemma rootCheck_eval (w e : ℕ) (m g : Basis w) :
    (rootCheck w e).eval (Fin.append m g) 0=true ↔
      2 % 2^w ≤ (bitsValue g).toNat ∧
        (bitsValue g).toNat^e % 2^w = (bitsValue m).toNat := by
  rw [rootCheck,eval_band,wordLe_eval,wordConstant_eval,rootGuess_eval,
    eval_comp,eval_pair,wordEq_eval,eval_comp,staticPower_eval,rootGuess_eval,rootModulus_eval]
  simp only [Bool.and_eq_true,decide_eq_true_eq,BitVec.toNat_ofNat]
  constructor
  · rintro ⟨hle,h⟩
    refine ⟨hle,?_⟩
    simpa only [BitVec.toNat_pow] using congrArg BitVec.toNat h
  · rintro ⟨hle,h⟩
    refine ⟨hle,?_⟩
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.toNat_pow] using h

def exponentCheck (n e : ℕ) : BooleanNetwork (rootWidth n) 1 :=
  ((select id).pair (boundedRootNet n e)).comp (rootCheck (rootWidth n) e)

lemma exponentCheck_eval {n e : ℕ} (hn : 2 ≤ n) (he : 2 ≤ e) (hen : e ≤ n)
    (m : Basis (rootWidth n)) (hm : (bitsValue m).toNat < 2^n) :
    (exponentCheck n e).eval m 0=true ↔
      2 ≤ Primality.boundedRoot (bitsValue m).toNat e n ∧
      (Primality.boundedRoot (bitsValue m).toNat e n)^e=(bitsValue m).toNat := by
  rw [exponentCheck,eval_comp,eval_pair,eval_select,Function.comp_id,rootCheck_eval,
    boundedRootNet_value n e hen]
  have hp : 2 < 2^(rootWidth n) := by
    have hh : 1 < rootWidth n := by dsimp [rootWidth]; nlinarith
    exact lt_of_eq_of_lt (by norm_num : 2=2^1) (Nat.pow_lt_pow_right (by decide) hh)
  have hroot := (Primality.boundedRoot_spec (by omega : 0 < e) hm).1
  have hmn : n ≤ rootWidth n := by dsimp [rootWidth];nlinarith
  rw [Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt
    (hroot.trans_lt (hm.trans_le (Nat.pow_le_pow_right (by decide) hmn)))]

def perfectPowerNet (n : ℕ) : BooleanNetwork (rootWidth n) 1 :=
  any (List.ofFn (fun e : Fin (n+1) => if 2 ≤ e.val then exponentCheck n e.val else constant false))

/-- The complete first AKS rejection check, as an actual polynomial-size
Boolean circuit: exponents2..n and n exact bounded binary-root steps each. -/
theorem perfectPowerNet_correct {n : ℕ} (hn : 2 ≤ n) (m : Basis (rootWidth n))
    (hm : (bitsValue m).toNat < 2^n) :
    (perfectPowerNet n).eval m 0=true ↔ Primality.PerfectPower (bitsValue m).toNat := by
  rw [perfectPowerNet,any_eval]
  constructor
  · rintro ⟨c,hc,hv⟩
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hc
    by_cases he : 2 ≤ e.val
    · rw [ite_eq_left he] at hv
      have hh := (exponentCheck_eval hn he (by omega) m hm).mp hv
      exact ⟨_,e.val,hh.1,he,hh.2⟩
    · simp [he] at hv
  · rintro ⟨b,e,hb,he,hbm⟩
    have hen : e < n := Primality.perfectPower_exponent_lt hm hb hbm
    have hr := Primality.boundedRoot_pow_eq (by omega : 0 < e) hm hbm
    refine ⟨exponentCheck n e,?_,?_⟩
    · apply List.mem_ofFn.mpr
      exact ⟨⟨e,by omega⟩,ite_eq_left he⟩
    · rw [exponentCheck_eval hn he (by omega) m hm,hr]
      exact ⟨hb,hbm⟩

lemma rootCheck_count (w e : ℕ) : (rootCheck w e).net.count ≤
    146*w+31+e*(90*w*w+14*w+6) := by
  have h₁ := wordLe_count (wordConstant (n := w+w) (BitVec.ofNat w 2)) (rootGuess w)
  have h₂ := wordEq_count w
  have h₃ := staticPower_count w e
  simp only [rootGuess,count_select,wordConstant_count] at h₁
  simp only [rootCheck,count_band,count_comp,count_pair,rootGuess,rootModulus,count_select,
    zero_add,add_zero]
  omega

abbrev perfectCheckBound (n : ℕ) : ℕ :=
  147*rootWidth n+31+n*(230*rootWidth n+21+n*(90*rootWidth n*rootWidth n+14*rootWidth n+6))+
    n*(90*rootWidth n*rootWidth n+14*rootWidth n+6)

lemma exponentCheck_count (n e : ℕ) (he : e ≤ n) : (exponentCheck n e).net.count ≤
    perfectCheckBound n := by
  have h₁ := boundedRootNet_count n e
  have h₂ := rootCheck_count (rootWidth n) e
  have h₃ := Nat.mul_le_mul_right (90*rootWidth n*rootWidth n+14*rootWidth n+6) he
  have h₄ := Nat.mul_le_mul_left n h₃
  simp only [exponentCheck,count_comp,count_pair,count_select,zero_add]
  dsimp [perfectCheckBound]
  nlinarith

lemma perfectExponent_count (n : ℕ) (e : Fin (n+1)) :
    (if 2 ≤ e.val then exponentCheck n e.val else
      (constant false : BooleanNetwork (rootWidth n) 1)).net.count ≤ perfectCheckBound n := by
  by_cases he : 2 ≤ e.val
  · have hh := congrArg (fun c : BooleanNetwork (rootWidth n) 1 => c.net.count)
      (ite_eq_left he : (if 2 ≤ e.val then exponentCheck n e.val else constant false)=exponentCheck n e.val)
    exact hh.trans_le (exponentCheck_count n e.val (by omega))
  · have hh := congrArg (fun c : BooleanNetwork (rootWidth n) 1 => c.net.count)
      (ite_eq_right he : (if 2 ≤ e.val then exponentCheck n e.val else constant false)=constant false)
    apply hh.trans_le
    change 1 ≤ perfectCheckBound n
    dsimp [perfectCheckBound,rootWidth]
    omega

lemma perfectPowerNet_count (n : ℕ) : (perfectPowerNet n).net.count ≤
    (n+1)*(perfectCheckBound n+4)+1 := by
  have h := any_count (c := perfectCheckBound n)
    (List.ofFn (fun e : Fin (n+1) => if 2 ≤ e.val then exponentCheck n e.val else constant false)) (by
      intro c hc
      obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hc
      exact perfectExponent_count n e)
  simpa only [perfectPowerNet,List.length_ofFn] using h

end ExactQuantumFactoring.BitArithmetic


end

end OAI


