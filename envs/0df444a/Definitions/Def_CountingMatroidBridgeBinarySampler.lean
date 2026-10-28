-- Prove2me | Definitions.Def_CountingMatroidBridgeBinarySampler
-- name    : CountingMatroidBridgeBinarySampler
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T19:53:12.887681+00:00
-- url     : https://prove2.me/theorems/a311543b-8db3-4a9f-ab43-4c83566c7021
-- title:
--   Polynomial-clock finite sampler with a binary counter
-- statement:
--   A fixed register program decrements a binary counter K into a unary loop count, samples exactly K bits with the verified balanced sampler, and then enters an arbitrary continuation program. For every K ≤ H, the sampled bits occur at distinct, input-determined positions in a finite random tape of length 26(H+1)^2. The proved handoff gives the continuation the exact ordered sample and an exact polynomial prefix cost. The counter K is supplied in register 9; computing K from the estimator parameters remains a separate implementation obligation.
-- source:
--   Lean 4.33.1 register-machine sampling and continuation bridge, using the local CommonBasesFPRAS machine and Cslib polynomial-growth results.

import Definitions.Def_CountingMatroid_Bridge_BinaryTapeSemantics
import Definitions.Def_CountingMatroidBridgeProgramAppend
import Theorems.Thm_Cslib_polynomiallyBounded_iff_le
import Theorems.Thm_CountingMatroid_Bridge_sampledStack_eq_reverse_ofFn
import Theorems.Thm_CountingMatroid_Bridge_balancedSampler_samples

set_option autoImplicit false

namespace CountingMatroid.Bridge
open OAI.CommonBasesFPRAS

private theorem natBits_foldr_bit (K : ℕ) : K.bits.foldr Nat.bit 0 = K := by
  induction K using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih => rw [Nat.bits_append_bit n b h, List.foldr_cons, ih]

/-- The binary word stored by the initializer represents exactly K in the
machine's little-endian convention. -/
theorem machineBinaryValue_bits (K : ℕ) : binaryValue K.bits = K := by
  have hfold (w : List Bool) : binaryValue w = w.foldr Nat.bit 0 := by
    induction w with
    | nil => rfl
    | cons b w ih =>
      cases b <;> simp [binaryValue, ih, Nat.bit_val] <;> omega
  rw [hfold]
  exact natBits_foldr_bit K

/-- The word operation performed by the counter's borrow states. It subtracts
one in little-endian order and intentionally preserves high zero bits. -/
def decrementBinaryWord : List Bool → Option (List Bool)
  | [] => none
  | true :: xs => some (false :: xs)
  | false :: xs => (decrementBinaryWord xs).map (true :: ·)

/-- Every successful borrow chain subtracts exactly one from the represented
number, including words with redundant high zeroes. -/
theorem decrementBinaryWord_sound : ∀ {xs ys : List Bool},
    decrementBinaryWord xs = some ys → binaryValue ys + 1 = binaryValue xs := by
  intro xs
  induction xs with
  | nil => simp [decrementBinaryWord]
  | cons b xs ih =>
    cases b
    · intro ys h
      simp only [decrementBinaryWord, Option.map_eq_some_iff] at h
      obtain ⟨z, hz, rfl⟩ := h
      have hz' := ih hz
      simp [binaryValue] at *
      omega
    · intro ys h
      simp only [decrementBinaryWord, Option.some.injEq] at h
      subst ys
      simp [binaryValue]
      omega

/-- A positive binary word always has a successful decrement result. -/
theorem decrementBinaryWord_exists_of_pos : ∀ xs : List Bool,
    0 < binaryValue xs → ∃ ys, decrementBinaryWord xs = some ys := by
  intro xs
  induction xs with
  | nil => simp [binaryValue]
  | cons b xs ih =>
    cases b
    · intro h
      have htail : 0 < binaryValue xs := by
        simpa [binaryValue] using h
      obtain ⟨ys, hys⟩ := ih htail
      exact ⟨true :: ys, by simp [decrementBinaryWord, hys]⟩
    · intro _
      exact ⟨false :: xs, rfl⟩

/-- Embed an instruction whose control states have been shifted by ten. -/
def shiftBinarySamplerInstruction {s : ℕ} :
    Instruction 2 s → Instruction 2 (s + 15)
  | .push i b q => .push i b ⟨q.val + 15, by have := q.isLt; omega⟩
  | .pop i empty zero one =>
      .pop i ⟨empty.val + 15, by have := empty.isLt; omega⟩
        ⟨zero.val + 15, by have := zero.isLt; omega⟩
        ⟨one.val + 15, by have := one.isLt; omega⟩
  | .coin zero one =>
      .coin ⟨zero.val + 15, by have := zero.isLt; omega⟩
        ⟨one.val + 15, by have := one.isLt; omega⟩
  | .query which i no yes =>
      .query which i ⟨no.val + 15, by have := no.isLt; omega⟩
        ⟨yes.val + 15, by have := yes.isLt; omega⟩
  | .halt => .halt

/-- A fixed binary-counter initializer followed by the already verified
balanced sampler and an arbitrary continuation. Register 9 initially holds
the little-endian binary encoding of K. Register 6 temporarily holds the
processed low-order prefix while a borrow travels toward the first one bit;
the prefix is restored before one unary zero is added to register 8. If the
counter reaches zero, the temporary prefix is cleared. States 10--13 run the
balanced sampler, and the continuation begins at state 15. -/
def binaryCounterThenProgram {s : ℕ} (P : Program 2 s) : Program 2 (s + 15) :=
  fun q => match h : q.val with
  | 0 => .pop 9 ⟨10, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
  | 1 => .push 6 true ⟨3, by omega⟩
  | 2 => .push 6 false ⟨4, by omega⟩
  | 3 => .pop 9 ⟨6, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
  | 4 => .pop 6 ⟨5, by omega⟩ ⟨7, by omega⟩ ⟨8, by omega⟩
  | 5 => .push 8 false ⟨0, by omega⟩
  | 6 => .pop 6 ⟨10, by omega⟩ ⟨6, by omega⟩ ⟨6, by omega⟩
  | 7 => .push 9 false ⟨4, by omega⟩
  | 8 => .push 9 true ⟨4, by omega⟩
  | 9 => .pop 6 ⟨10, by omega⟩ ⟨9, by omega⟩ ⟨9, by omega⟩
  | 10 => .pop 8 ⟨15, by omega⟩ ⟨11, by omega⟩ ⟨11, by omega⟩
  | 11 => .coin ⟨12, by omega⟩ ⟨13, by omega⟩
  | 12 => .push 9 false ⟨10, by omega⟩
  | 13 => .push 9 true ⟨10, by omega⟩
  | 14 => .halt
  | v + 15 => shiftBinarySamplerInstruction (P ⟨v, by have hq := q.isLt; rw [h] at hq; omega⟩)

/-- Binary encodings can always be assigned their represented natural value.
This is the initial-state condition used by `binaryCounterThenProgram`. -/
def binarySamplerInput {k s : ℕ} (c : MachineConfig k s) (K : ℕ) :
    MachineConfig k s :=
  { c with registers := Function.update c.registers 9 K.bits }

@[simp] theorem binarySamplerInput_register9 {k s : ℕ}
    (c : MachineConfig k s) (K : ℕ) :
    (binarySamplerInput c K).registers 9 = K.bits := by
  simp [binarySamplerInput]

@[simp] theorem binarySamplerInput_register8 {s : ℕ}
    (c : MachineConfig 2 s) (K : ℕ) :
    (binarySamplerInput c K).registers 8 = c.registers 8 := by
  simp [binarySamplerInput]

/-- Fieldwise extensionality for the finite-stack machine configuration. -/
theorem binarySamplerConfig_ext {k s : ℕ} {a b : MachineConfig k s}
    (hregisters : a.registers = b.registers) (hcontrol : a.control = b.control)
    (houtput : a.output = b.output) (horacleCalls : a.oracleCalls = b.oracleCalls)
    (hbitOperations : a.bitOperations = b.bitOperations) : a = b := by
  cases a
  cases b
  simp_all

/-- Execution splits exactly at a deterministic time offset. -/
theorem binarySampler_execution_add_steps {k s n : ℕ} (P : Program k s)
    (O : IndependenceOracle n) (c : MachineConfig k s) (bits : ℕ → Bool)
    (a b : ℕ) :
    execution P O c bits (a + b) =
      execution P O (execution P O c bits a) (fun t => bits (a + t)) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change machineStep P O (bits (a + b)) (execution P O c bits (a + b)) = _
    rw [ih]
    rfl

/-- State 6 discards the temporary stack after the binary counter reaches
zero, then enters the balanced sampler with an empty sample stack. -/
theorem binaryCounter_clearScratch {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 (s + 15))
    (bits : ℕ → Bool) (acc : List Bool)
    (hcontrol : c.control = (⟨6, by omega⟩ : Fin (s + 15 + 1)))
    (houtput : c.output = none) (hscratch : c.registers 6 = acc)
    (hcounter : c.registers 9 = []) :
    execution (binaryCounterThenProgram P) O c bits (acc.length + 1) =
      { c with
        registers := Function.update c.registers 6 []
        control := ⟨10, by omega⟩
        output := none
        bitOperations := c.bitOperations + (acc.length + 1) } := by
  induction acc generalizing c bits with
  | nil =>
    cases c with
    | mk registers control output oracleCalls bitOperations =>
      simp only at hcontrol houtput hscratch hcounter
      subst control
      subst output
      let q6 : Fin (s + 15 + 1) := ⟨6, by omega⟩
      let q10 : Fin (s + 15 + 1) := ⟨10, by omega⟩
      let c0 : MachineConfig 2 (s + 15) :=
        ⟨registers, q6, none, oracleCalls, bitOperations⟩
      let c1 : MachineConfig 2 (s + 15) :=
        ⟨registers, q10, none, oracleCalls, bitOperations + 1⟩
      have hstep : machineStep (binaryCounterThenProgram P) O (bits 0) c0 = c1 := by
        simp [machineStep, binaryCounterThenProgram, hscratch, c0, c1, q6, q10]
      have hrun : execution (binaryCounterThenProgram P) O c0 bits 1 = c1 := by
        simp only [execution, hstep]
      change execution (binaryCounterThenProgram P) O c0 bits 1 = _
      rw [hrun]
      apply binarySamplerConfig_ext
      · funext i
        by_cases hi : i = 6
        · subst i
          simp [c1, Function.update, hscratch]
        · simp [c1, Function.update, hi]
      · rfl
      · rfl
      · rfl
      · rfl
  | cons b acc ih =>
    cases c with
    | mk registers control output oracleCalls bitOperations =>
      simp only at hcontrol houtput hscratch hcounter
      subst control
      subst output
      let q6 : Fin (s + 15 + 1) := ⟨6, by omega⟩
      let q10 : Fin (s + 15 + 1) := ⟨10, by omega⟩
      let c0 : MachineConfig 2 (s + 15) :=
        ⟨registers, q6, none, oracleCalls, bitOperations⟩
      let c1 : MachineConfig 2 (s + 15) :=
        ⟨Function.update registers 6 acc, q6, none, oracleCalls, bitOperations + 1⟩
      have hstep : machineStep (binaryCounterThenProgram P) O (bits 0) c0 = c1 := by
        simp [machineStep, binaryCounterThenProgram, hscratch, c0, c1, q6]
      have hrun : execution (binaryCounterThenProgram P) O c0 bits (acc.length + 2) =
          { c0 with
            registers := Function.update c0.registers 6 [],
            control := q10,
            output := none,
            bitOperations := c0.bitOperations + (acc.length + 2) } := by
        have hih := ih c1 (fun t => bits (1 + t)) (by rfl) (by rfl)
          (by simp [c1, Function.update]) (by simp [c1, Function.update, hcounter])
        rw [show acc.length + 2 = 1 + (acc.length + 1) by omega,
          binarySampler_execution_add_steps]
        rw [show execution (binaryCounterThenProgram P) O c0 bits 1 = c1 by
          simp [execution, hstep]]
        rw [hih]
        apply binarySamplerConfig_ext
        · funext i
          by_cases hi : i = 6
          · subst i
            simp [c0, c1, Function.update, hscratch]
          · simp [c0, c1, Function.update, hi]
        · rfl
        · rfl
        · rfl
        · simp [c0, c1]
          omega
      change execution (binaryCounterThenProgram P) O c0 bits (acc.length + 2) = _
      rw [hrun]
      simp [c0, q6, q10, Function.update, hscratch, List.length_cons]

/-- The transfer phase reverses the temporary stack back onto the binary
counter, clears scratch, then increments the unary counter. -/
theorem binaryCounter_transfer {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 (s + 15))
    (bits : ℕ → Bool) (acc rest : List Bool)
    (hcontrol : c.control = (⟨4, by omega⟩ : Fin (s + 15 + 1)))
    (houtput : c.output = none) (hscratch : c.registers 6 = acc)
    (hcounter : c.registers 9 = rest) :
    execution (binaryCounterThenProgram P) O c bits (2 * acc.length + 2) =
      { c with
        registers := Function.update
          (Function.update (Function.update c.registers 6 []) 9
            (acc.reverse ++ rest)) 8 (false :: c.registers 8)
        control := ⟨0, by omega⟩
        output := none
        bitOperations := c.bitOperations + (2 * acc.length + 2) } := by
  induction acc generalizing c rest bits with
  | nil =>
    cases c with
    | mk registers control output oracleCalls bitOperations =>
      simp only at hcontrol houtput hscratch hcounter
      subst control
      subst output
      let q0 : Fin (s + 15 + 1) := ⟨0, by omega⟩
      let q4 : Fin (s + 15 + 1) := ⟨4, by omega⟩
      let q5 : Fin (s + 15 + 1) := ⟨5, by omega⟩
      let c0 : MachineConfig 2 (s + 15) :=
        ⟨registers, q4, none, oracleCalls, bitOperations⟩
      let c1 : MachineConfig 2 (s + 15) :=
        ⟨registers, q5, none, oracleCalls, bitOperations + 1⟩
      let c2 : MachineConfig 2 (s + 15) :=
        ⟨Function.update registers 8 (false :: registers 8), q0, none,
          oracleCalls, bitOperations + 2⟩
      have h1 : machineStep (binaryCounterThenProgram P) O (bits 0) c0 = c1 := by
        simp [machineStep, binaryCounterThenProgram, hscratch, c0, c1, q4, q5]
      have h2 : machineStep (binaryCounterThenProgram P) O (bits 1) c1 = c2 := by
        simp [machineStep, binaryCounterThenProgram, c1, c2, q5, q0]
      have hrun : execution (binaryCounterThenProgram P) O c0 bits 2 = c2 := by
        simp only [execution, h1, h2]
      change execution (binaryCounterThenProgram P) O c0 bits 2 = _
      rw [hrun]
      have hregs : c2.registers =
          Function.update (Function.update (Function.update registers 6 []) 9 rest) 8
            (false :: registers 8) := by
        funext i
        by_cases hi6 : i = 6
        · subst i
          simp [c2, Function.update, hscratch]
        · by_cases hi9 : i = 9
          · subst i
            simp [c2, Function.update, hcounter]
          · by_cases hi8 : i = 8
            · subst i
              simp [c2, Function.update]
            · simp [c2, Function.update, hi6, hi9, hi8]
      apply binarySamplerConfig_ext
      · exact hregs
      · simp [c2, q0]
      · rfl
      · rfl
      · rfl
  | cons b acc ih =>
    cases c with
    | mk registers control output oracleCalls bitOperations =>
      simp only at hcontrol houtput hscratch hcounter
      subst control
      subst output
      let q0 : Fin (s + 15 + 1) := ⟨0, by omega⟩
      let q1 : Fin (s + 15 + 1) := ⟨1, by omega⟩
      let q2 : Fin (s + 15 + 1) := ⟨2, by omega⟩
      let q3 : Fin (s + 15 + 1) := ⟨3, by omega⟩
      let q4 : Fin (s + 15 + 1) := ⟨4, by omega⟩
      let q7 : Fin (s + 15 + 1) := ⟨7, by omega⟩
      let q8 : Fin (s + 15 + 1) := ⟨8, by omega⟩
      let qB : Fin (s + 15 + 1) := if b then q8 else q7
      let c0 : MachineConfig 2 (s + 15) :=
        ⟨registers, q4, none, oracleCalls, bitOperations⟩
      let c1 : MachineConfig 2 (s + 15) :=
        ⟨Function.update registers 6 acc, qB, none, oracleCalls, bitOperations + 1⟩
      let c2 : MachineConfig 2 (s + 15) :=
        ⟨Function.update (Function.update registers 6 acc) 9 (b :: rest),
          q4, none, oracleCalls, bitOperations + 2⟩
      have h1 : machineStep (binaryCounterThenProgram P) O (bits 0) c0 = c1 := by
        cases b <;> simp [machineStep, binaryCounterThenProgram, hscratch,
          c0, c1, q4, qB, q7, q8]
      have h2 : machineStep (binaryCounterThenProgram P) O (bits 1) c1 = c2 := by
        cases b <;> simp [machineStep, binaryCounterThenProgram, c1, c2,
          qB, q4, q7, q8, Function.update, hcounter, hscratch]
      have htwo : execution (binaryCounterThenProgram P) O c0 bits 2 = c2 := by
        simp only [execution, h1, h2]
      have hih : execution (binaryCounterThenProgram P) O c2
          (fun t => bits (2 + t)) (2 * acc.length + 2) =
          { c2 with
            registers := Function.update
              (Function.update (Function.update c2.registers 6 []) 9
                (acc.reverse ++ (b :: rest))) 8 (false :: c2.registers 8)
            control := q0
            output := none
            bitOperations := c2.bitOperations + (2 * acc.length + 2) } := by
        apply ih c2 (fun t => bits (2 + t)) (b :: rest)
        · rfl
        · rfl
        · simp [c2, Function.update]
        · simp [c2, Function.update]
      have hsteps : 2 * (b :: acc).length + 2 = 2 + (2 * acc.length + 2) := by
        simp
        omega
      rw [hsteps]
      rw [binarySampler_execution_add_steps, htwo, hih]
      apply binarySamplerConfig_ext
      · funext i
        by_cases hi6 : i = 6
        · subst i
          simp [c2, Function.update]
        · by_cases hi9 : i = 9
          · subst i
            simp [c2, Function.update, List.reverse_cons, List.append_assoc]
          · by_cases hi8 : i = 8
            · subst i
              simp [c2, Function.update]
            · simp [c2, Function.update, hi6, hi9, hi8]
      · simp [q0]
      · rfl
      · simp [c2]
      · simp [c2]
        omega

/-- Number of instructions used by the scan-to-one phase followed by prefix
restoration. -/
def binaryCounterScanSteps (acc : List Bool) : List Bool → ℕ
  | [] => 0
  | true :: _ => 2 * acc.length + 6
  | false :: rest => 2 + binaryCounterScanSteps (true :: acc) rest

/-- Binary word remaining after the scan has changed every borrowed zero to one
and the first one to zero. -/
def binaryCounterScanResult (acc : List Bool) : List Bool → List Bool
  | [] => []
  | true :: rest => (false :: acc).reverse ++ rest
  | false :: rest => binaryCounterScanResult (true :: acc) rest

/-- The scan loop on a positive suffix restores its processed prefix, clears
scratch, and increments the unary counter in exactly the specified number of
machine steps. -/
theorem binaryCounter_scan {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 (s + 15))
    (bits : ℕ → Bool) (acc xs : List Bool)
    (hcontrol : c.control = (⟨3, by omega⟩ : Fin (s + 15 + 1)))
    (houtput : c.output = none) (hscratch : c.registers 6 = acc)
    (hcounter : c.registers 9 = xs) (hpositive : 0 < binaryValue xs) :
    execution (binaryCounterThenProgram P) O c bits (binaryCounterScanSteps acc xs) =
      { c with
        registers := Function.update
          (Function.update (Function.update c.registers 6 []) 9
            (binaryCounterScanResult acc xs)) 8 (false :: c.registers 8)
        control := ⟨0, by omega⟩
        output := none
        bitOperations := c.bitOperations + binaryCounterScanSteps acc xs } := by
  induction xs generalizing c bits acc with
  | nil => simp [binaryValue] at hpositive
  | cons b xs ih =>
    cases b
    · have htail : 0 < binaryValue xs := by
        simpa [binaryValue] using hpositive
      cases c with
      | mk registers control output oracleCalls bitOperations =>
        simp only at hcontrol houtput hscratch hcounter
        subst control
        subst output
        let q0 : Fin (s + 15 + 1) := ⟨0, by omega⟩
        let q1 : Fin (s + 15 + 1) := ⟨1, by omega⟩
        let q3 : Fin (s + 15 + 1) := ⟨3, by omega⟩
        let q4 : Fin (s + 15 + 1) := ⟨4, by omega⟩
        let c0 : MachineConfig 2 (s + 15) :=
          ⟨registers, q3, none, oracleCalls, bitOperations⟩
        let c1 : MachineConfig 2 (s + 15) :=
          ⟨Function.update registers 9 xs, q1, none, oracleCalls, bitOperations + 1⟩
        let c2 : MachineConfig 2 (s + 15) :=
          ⟨Function.update (Function.update registers 9 xs) 6 (true :: acc),
            q3, none, oracleCalls, bitOperations + 2⟩
        have h1 : machineStep (binaryCounterThenProgram P) O (bits 0) c0 = c1 := by
          simp [machineStep, binaryCounterThenProgram, hcounter, c0, c1, q3, q1]
        have h2 : machineStep (binaryCounterThenProgram P) O (bits 1) c1 = c2 := by
          simp [machineStep, binaryCounterThenProgram, c1, c2, q1, q3, hscratch]
        have htwo : execution (binaryCounterThenProgram P) O c0 bits 2 = c2 := by
          simp only [execution, h1, h2]
        have hih := ih c2 (fun t => bits (2 + t)) (true :: acc)
          (by rfl) (by rfl) (by simp [c2, Function.update])
          (by simp [c2, Function.update, hcounter]) htail
        have hsteps : binaryCounterScanSteps acc (false :: xs) =
            2 + binaryCounterScanSteps (true :: acc) xs := rfl
        rw [hsteps, binarySampler_execution_add_steps, htwo, hih]
        apply binarySamplerConfig_ext
        · funext i
          fin_cases i <;>
            simp_all [c2, Function.update, binaryCounterScanResult,
              List.reverse_cons, List.append_assoc]
        · simp [q0]
        · rfl
        · rfl
        · simp [c2]
          omega

    · cases c with
      | mk registers control output oracleCalls bitOperations =>
        simp only at hcontrol houtput hscratch hcounter
        subst control
        subst output
        let q0 : Fin (s + 15 + 1) := ⟨0, by omega⟩
        let q2 : Fin (s + 15 + 1) := ⟨2, by omega⟩
        let q3 : Fin (s + 15 + 1) := ⟨3, by omega⟩
        let q4 : Fin (s + 15 + 1) := ⟨4, by omega⟩
        let q7 : Fin (s + 15 + 1) := ⟨7, by omega⟩
        let q8 : Fin (s + 15 + 1) := ⟨8, by omega⟩
        let c0 : MachineConfig 2 (s + 15) :=
          ⟨registers, q3, none, oracleCalls, bitOperations⟩
        let c1 : MachineConfig 2 (s + 15) :=
          ⟨Function.update registers 9 xs, q2, none, oracleCalls, bitOperations + 1⟩
        let c2 : MachineConfig 2 (s + 15) :=
          ⟨Function.update (Function.update registers 9 xs) 6 (false :: acc),
            q4, none, oracleCalls, bitOperations + 2⟩
        have h1 : machineStep (binaryCounterThenProgram P) O (bits 0) c0 = c1 := by
          simp [machineStep, binaryCounterThenProgram, hcounter, c0, c1, q3, q2]
        have h2 : machineStep (binaryCounterThenProgram P) O (bits 1) c1 = c2 := by
          simp [machineStep, binaryCounterThenProgram, c1, c2, q2, q4, hscratch]
        have htwo : execution (binaryCounterThenProgram P) O c0 bits 2 = c2 := by
          simp only [execution, h1, h2]
        have htransfer := binaryCounter_transfer P O c2
          (fun t => bits (2 + t)) (false :: acc) xs (by rfl) (by rfl)
          (by simp [c2, Function.update]) (by simp [c2, Function.update, hcounter])
        have hsteps : binaryCounterScanSteps acc (true :: xs) =
            2 + (2 * (false :: acc).length + 2) := by
          simp [binaryCounterScanSteps]
          omega
        rw [hsteps, binarySampler_execution_add_steps, htwo, htransfer]
        apply binarySamplerConfig_ext
        · funext i
          fin_cases i <;>
            simp_all [c2, Function.update, binaryCounterScanResult,
              List.reverse_cons, List.append_assoc]
        · simp [q0]
        · rfl
        · rfl
        · simp [c2]
          omega

/-- Instruction count for recognizing and clearing an all-zero binary stack. -/
def binaryCounterZeroScanSteps (acc : List Bool) : List Bool → ℕ
  | [] => acc.length + 2
  | false :: xs => 2 + binaryCounterZeroScanSteps (true :: acc) xs
  | true :: _ => 0

/-- When the scanned suffix represents zero, the machine drains it and clears
the borrowed scratch prefix before entering the sampler. -/
theorem binaryCounter_scan_zero {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 (s + 15))
    (bits : ℕ → Bool) (acc xs : List Bool)
    (hcontrol : c.control = (⟨3, by omega⟩ : Fin (s + 15 + 1)))
    (houtput : c.output = none) (hscratch : c.registers 6 = acc)
    (hcounter : c.registers 9 = xs) (hzero : binaryValue xs = 0) :
    execution (binaryCounterThenProgram P) O c bits
        (binaryCounterZeroScanSteps acc xs) =
      { c with
        registers := Function.update (Function.update c.registers 9 []) 6 []
        control := ⟨10, by omega⟩
        output := none
        bitOperations := c.bitOperations + binaryCounterZeroScanSteps acc xs } := by
  induction xs generalizing c bits acc with
  | nil =>
    cases c with
    | mk registers control output oracleCalls bitOperations =>
      simp only at hcontrol houtput hscratch hcounter
      subst control
      subst output
      let q3 : Fin (s + 15 + 1) := ⟨3, by omega⟩
      let q6 : Fin (s + 15 + 1) := ⟨6, by omega⟩
      let q10 : Fin (s + 15 + 1) := ⟨10, by omega⟩
      let c0 : MachineConfig 2 (s + 15) :=
        ⟨registers, q3, none, oracleCalls, bitOperations⟩
      let c1 : MachineConfig 2 (s + 15) :=
        ⟨registers, q6, none, oracleCalls, bitOperations + 1⟩
      have hstep : machineStep (binaryCounterThenProgram P) O (bits 0) c0 = c1 := by
        simp [machineStep, binaryCounterThenProgram, hcounter, c0, c1, q3, q6]
      have hclear := binaryCounter_clearScratch P O c1 (fun t => bits (1 + t)) acc
        (by rfl) (by rfl) (by simp [c1, Function.update, hscratch])
        (by simp [c1, Function.update, hcounter])
      have hrun : execution (binaryCounterThenProgram P) O c0 bits (acc.length + 2) =
          { c0 with
            registers := Function.update (Function.update c0.registers 9 []) 6 [],
            control := q10,
            output := none,
            bitOperations := c0.bitOperations + (acc.length + 2) } := by
        rw [show acc.length + 2 = 1 + (acc.length + 1) by omega,
          binarySampler_execution_add_steps]
        rw [show execution (binaryCounterThenProgram P) O c0 bits 1 = c1 by
          simp [execution, hstep]]
        rw [hclear]
        apply binarySamplerConfig_ext
        · funext i
          fin_cases i <;> simp_all [c0, c1, Function.update]
        · rfl
        · rfl
        · rfl
        · simp [c0, c1]
          omega
      change execution (binaryCounterThenProgram P) O c0 bits (acc.length + 2) = _
      rw [hrun]
      simp [c0, q3, q6, q10, Function.update, List.length_cons,
        binaryCounterZeroScanSteps]
  | cons b xs ih =>
    cases b
    · have htail : binaryValue xs = 0 := by
        simpa [binaryValue] using hzero
      cases c with
      | mk registers control output oracleCalls bitOperations =>
        simp only at hcontrol houtput hscratch hcounter
        subst control
        subst output
        let q1 : Fin (s + 15 + 1) := ⟨1, by omega⟩
        let q3 : Fin (s + 15 + 1) := ⟨3, by omega⟩
        let q9 : Fin (s + 15 + 1) := ⟨9, by omega⟩
        let c0 : MachineConfig 2 (s + 15) :=
          ⟨registers, q3, none, oracleCalls, bitOperations⟩
        let c1 : MachineConfig 2 (s + 15) :=
          ⟨Function.update registers 9 xs, q1, none, oracleCalls, bitOperations + 1⟩
        let c2 : MachineConfig 2 (s + 15) :=
          ⟨Function.update (Function.update registers 9 xs) 6 (true :: acc),
            q3, none, oracleCalls, bitOperations + 2⟩
        have h1 : machineStep (binaryCounterThenProgram P) O (bits 0) c0 = c1 := by
          simp [machineStep, binaryCounterThenProgram, hcounter, c0, c1, q3, q1]
        have h2 : machineStep (binaryCounterThenProgram P) O (bits 1) c1 = c2 := by
          simp [machineStep, binaryCounterThenProgram, c1, c2, q1, q3, hscratch]
        have htwo : execution (binaryCounterThenProgram P) O c0 bits 2 = c2 := by
          simp only [execution, h1, h2]
        have hih := ih c2 (fun t => bits (2 + t)) (true :: acc)
          (by rfl) (by rfl) (by simp [c2, Function.update])
          (by simp [c2, Function.update, hcounter]) htail
        rw [show binaryCounterZeroScanSteps acc (false :: xs) =
            2 + binaryCounterZeroScanSteps (true :: acc) xs by rfl,
          binarySampler_execution_add_steps]
        rw [htwo, hih]
        apply binarySamplerConfig_ext
        · funext i
          fin_cases i <;> simp_all [c2, Function.update, List.length_cons]
        · simp [q3]
        · rfl
        · rfl
        · simp [c2]
          omega
    · simp [binaryValue] at hzero

/-- The all-zero cleanup takes linear time in the counter width and scratch
prefix length. -/
theorem binaryCounterZeroScanSteps_le (acc xs : List Bool) :
    binaryCounterZeroScanSteps acc xs ≤ 3 * xs.length + acc.length + 2 := by
  induction xs generalizing acc with
  | nil => simp [binaryCounterZeroScanSteps]
  | cons b xs ih =>
    cases b
    · simp only [binaryCounterZeroScanSteps, List.length_cons]
      have h := ih (true :: acc)
      simp only [List.length_cons] at h
      omega
    · simp [binaryCounterZeroScanSteps, List.length_cons]

/-- Instruction count for the outer counter state when its word is zero. -/
def binaryCounterZeroCycleSteps : List Bool → ℕ
  | [] => 1
  | false :: xs => 2 + binaryCounterZeroScanSteps [true] xs
  | true :: _ => 0

/-- Starting at the counter entry, an all-zero word is cleared and handed to
the sampler. The number of steps is linear in the fixed counter width. -/
theorem binaryCounter_zero_cycle {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 (s + 15))
    (bits : ℕ → Bool) (xs : List Bool)
    (hcontrol : c.control = (⟨0, by omega⟩ : Fin (s + 15 + 1)))
    (houtput : c.output = none) (hcounter : c.registers 9 = xs)
    (hscratch : c.registers 6 = []) (hzero : binaryValue xs = 0) :
    let out := execution (binaryCounterThenProgram P) O c bits
      (binaryCounterZeroCycleSteps xs)
    out.control = (⟨10, by omega⟩ : Fin (s + 15 + 1)) ∧ out.output = none ∧
      out.registers 9 = [] ∧ out.registers 6 = [] ∧
      out.registers 8 = c.registers 8 ∧
      out.bitOperations = c.bitOperations + binaryCounterZeroCycleSteps xs ∧
      out.oracleCalls = c.oracleCalls := by
  cases xs with
  | nil =>
    cases c with
    | mk registers control output oracleCalls bitOperations =>
      simp only at hcontrol houtput hcounter hscratch
      subst control
      subst output
      simp [binaryCounterZeroCycleSteps, execution, machineStep,
        binaryCounterThenProgram, hcounter, hscratch]
  | cons b xs =>
    cases b
    · have htail : binaryValue xs = 0 := by
        simpa [binaryValue] using hzero
      cases c with
      | mk registers control output oracleCalls bitOperations =>
        simp only at hcontrol houtput hcounter hscratch
        subst control
        subst output
        let q0 : Fin (s + 15 + 1) := ⟨0, by omega⟩
        let q1 : Fin (s + 15 + 1) := ⟨1, by omega⟩
        let q3 : Fin (s + 15 + 1) := ⟨3, by omega⟩
        let c0 : MachineConfig 2 (s + 15) :=
          ⟨registers, q0, none, oracleCalls, bitOperations⟩
        let c1 : MachineConfig 2 (s + 15) :=
          ⟨Function.update registers 9 xs, q1, none, oracleCalls, bitOperations + 1⟩
        let c2 : MachineConfig 2 (s + 15) :=
          ⟨Function.update (Function.update registers 9 xs) 6 [true],
            q3, none, oracleCalls, bitOperations + 2⟩
        have h1 : machineStep (binaryCounterThenProgram P) O (bits 0) c0 = c1 := by
          simp [machineStep, binaryCounterThenProgram, hcounter, c0, c1, q0, q1]
        have h2 : machineStep (binaryCounterThenProgram P) O (bits 1) c1 = c2 := by
          simp [machineStep, binaryCounterThenProgram, c1, c2, q1, q3, hscratch]
        have htwo : execution (binaryCounterThenProgram P) O c0 bits 2 = c2 := by
          simp only [execution, h1, h2]
        have hscan := binaryCounter_scan_zero P O c2 (fun t => bits (2 + t))
          [true] xs (by rfl) (by rfl) (by simp [c2, Function.update])
          (by simp [c2, Function.update, hcounter]) htail
        rw [show binaryCounterZeroCycleSteps (false :: xs) =
            2 + binaryCounterZeroScanSteps [true] xs by rfl,
          binarySampler_execution_add_steps, htwo, hscan]
        simp [c2, q0, binaryCounterZeroCycleSteps, Function.update,
          List.length_cons, hcounter]
        omega
    · simp [binaryValue] at hzero

/-- The last zero-cleanup pass is linear in the original counter width. -/
theorem binaryCounterZeroCycleSteps_le_of_zero (xs : List Bool)
    (hzero : binaryValue xs = 0) :
    binaryCounterZeroCycleSteps xs ≤ 3 * xs.length + 2 := by
  cases xs with
  | nil => simp [binaryCounterZeroCycleSteps]
  | cons b xs =>
    cases b
    · simp only [binaryCounterZeroCycleSteps, List.length_cons]
      have h := binaryCounterZeroScanSteps_le [true] xs
      simp only [List.length_cons, List.length_nil] at h
      omega
    · simp [binaryValue] at hzero

/-- The machine scan computes the same borrowed suffix as the pure word
decrement. The accumulator records the already borrowed low-order prefix. -/
theorem binaryCounterScanResult_eq_append_decrement :
    ∀ (acc xs ys : List Bool), decrementBinaryWord xs = some ys →
      binaryCounterScanResult acc xs = acc.reverse ++ ys := by
  intro acc xs
  induction xs generalizing acc with
  | nil => simp [decrementBinaryWord]
  | cons b xs ih =>
    cases b
    · intro ys h
      simp only [decrementBinaryWord, Option.map_eq_some_iff] at h
      obtain ⟨z, hz, rfl⟩ := h
      have hi := ih (true :: acc) z hz
      simpa [binaryCounterScanResult, List.reverse_cons, List.append_assoc] using hi
    · intro ys h
      simp only [decrementBinaryWord, Option.some.injEq] at h
      subst ys
      simp [binaryCounterScanResult, List.reverse_cons, List.append_assoc]

/-- A zero low bit enters the borrow scan after two instructions. The scan
then restores the borrowed prefix and decrements the binary counter. -/
theorem binaryCounter_false_cycle {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 (s + 15))
    (bits : ℕ → Bool) (xs : List Bool)
    (hcontrol : c.control = (⟨0, by omega⟩ : Fin (s + 15 + 1)))
    (houtput : c.output = none) (hcounter : c.registers 9 = false :: xs)
    (hscratch : c.registers 6 = []) (hpositive : 0 < binaryValue xs) :
    execution (binaryCounterThenProgram P) O c bits
        (2 + binaryCounterScanSteps [true] xs) =
      { c with
        registers := Function.update
          (Function.update (Function.update c.registers 6 []) 9
            (binaryCounterScanResult [true] xs)) 8 (false :: c.registers 8)
        control := ⟨0, by omega⟩
        output := none
        bitOperations := c.bitOperations + (2 + binaryCounterScanSteps [true] xs) } := by
  cases c with
  | mk registers control output oracleCalls bitOperations =>
    simp only at hcontrol houtput hcounter hscratch
    subst control
    subst output
    let q0 : Fin (s + 15 + 1) := ⟨0, by omega⟩
    let q1 : Fin (s + 15 + 1) := ⟨1, by omega⟩
    let q3 : Fin (s + 15 + 1) := ⟨3, by omega⟩
    let c0 : MachineConfig 2 (s + 15) :=
      ⟨registers, q0, none, oracleCalls, bitOperations⟩
    let c1 : MachineConfig 2 (s + 15) :=
      ⟨Function.update registers 9 xs, q1, none, oracleCalls, bitOperations + 1⟩
    let c2 : MachineConfig 2 (s + 15) :=
      ⟨Function.update (Function.update registers 9 xs) 6 [true],
        q3, none, oracleCalls, bitOperations + 2⟩
    have h1 : machineStep (binaryCounterThenProgram P) O (bits 0) c0 = c1 := by
      simp [machineStep, binaryCounterThenProgram, hcounter, c0, c1, q0, q1]
    have h2 : machineStep (binaryCounterThenProgram P) O (bits 1) c1 = c2 := by
      simp [machineStep, binaryCounterThenProgram, hscratch, c1, c2, q1, q3]
    have htwo : execution (binaryCounterThenProgram P) O c0 bits 2 = c2 := by
      simp only [execution, h1, h2]
    have hscan := binaryCounter_scan P O c2 (fun t => bits (2 + t)) [true] xs
      (by rfl) (by rfl) (by simp [c2, Function.update])
      (by simp [c2, Function.update, hcounter]) hpositive
    rw [binarySampler_execution_add_steps, htwo, hscan]
    apply binarySamplerConfig_ext
    · funext i
      fin_cases i <;>
        simp_all [c2, Function.update, binaryCounterScanResult,
          List.reverse_cons, List.append_assoc]
    · simp [q0]
    · rfl
    · rfl
    · simp [c2]
      omega

/-- A one-bit counter decrement restores the scratch register, writes the
decremented low-order word, and adds one unary counter bit. -/
theorem binaryCounter_true_cycle {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 (s + 15))
    (bits : ℕ → Bool) (xs : List Bool)
    (hcontrol : c.control = 0) (houtput : c.output = none)
    (hcounter : c.registers 9 = true :: xs) (hscratch : c.registers 6 = []) :
    let out := execution (binaryCounterThenProgram P) O c bits 6
    out.control = 0 ∧ out.output = none ∧ out.registers 9 = false :: xs ∧
      out.registers 6 = [] ∧ out.registers 8 = false :: c.registers 8 ∧
      out.bitOperations = c.bitOperations + 6 ∧ out.oracleCalls = c.oracleCalls := by
  cases c with
  | mk registers control output oracleCalls bitOperations =>
    simp only at hcontrol houtput hcounter hscratch
    subst control
    subst output
    let q0 : Fin (s + 15 + 1) := ⟨0, by omega⟩
    let q2 : Fin (s + 15 + 1) := ⟨2, by omega⟩
    let q4 : Fin (s + 15 + 1) := ⟨4, by omega⟩
    let q5 : Fin (s + 15 + 1) := ⟨5, by omega⟩
    let q7 : Fin (s + 15 + 1) := ⟨7, by omega⟩
    let c0 : MachineConfig 2 (s + 15) :=
      ⟨registers, q0, none, oracleCalls, bitOperations⟩
    let c1 : MachineConfig 2 (s + 15) :=
      ⟨Function.update registers 9 xs, q2, none, oracleCalls, bitOperations + 1⟩
    let c2 : MachineConfig 2 (s + 15) :=
      ⟨Function.update (Function.update registers 9 xs) 6 [false], q4, none,
        oracleCalls, bitOperations + 2⟩
    let c3 : MachineConfig 2 (s + 15) :=
      ⟨Function.update (Function.update (Function.update registers 9 xs) 6 [false])
        6 [], q7, none, oracleCalls, bitOperations + 3⟩
    let c4 : MachineConfig 2 (s + 15) :=
      ⟨Function.update (Function.update (Function.update (Function.update registers 9 xs)
        6 [false]) 6 []) 9 (false :: xs), q4, none,
        oracleCalls, bitOperations + 4⟩
    let c5 : MachineConfig 2 (s + 15) :=
      ⟨Function.update c4.registers 6 [], q5, none, oracleCalls, bitOperations + 5⟩
    let c6 : MachineConfig 2 (s + 15) :=
      ⟨Function.update c5.registers 8 (false :: c5.registers 8), q0, none,
        oracleCalls, bitOperations + 6⟩
    have h1 : machineStep (binaryCounterThenProgram P) O (bits 0) c0 = c1 := by
      simp [machineStep, binaryCounterThenProgram, hcounter, c0, c1, q0, q2]
    have h2 : machineStep (binaryCounterThenProgram P) O (bits 1) c1 = c2 := by
      simp [machineStep, binaryCounterThenProgram, hscratch, c1, c2, q2, q4]
    have h3 : machineStep (binaryCounterThenProgram P) O (bits 2) c2 = c3 := by
      simp [machineStep, binaryCounterThenProgram, hscratch, c2, c3, q4, q7]
    have h4 : machineStep (binaryCounterThenProgram P) O (bits 3) c3 = c4 := by
      simp [machineStep, binaryCounterThenProgram, c3, c4, q7, q4]
    have h5 : machineStep (binaryCounterThenProgram P) O (bits 4) c4 = c5 := by
      simp [machineStep, binaryCounterThenProgram, c4, c5, q4, q5]
    have h6 : machineStep (binaryCounterThenProgram P) O (bits 5) c5 = c6 := by
      simp [machineStep, binaryCounterThenProgram, c5, c6, q5, q0]
    have hreg8 : c4.registers 8 = registers 8 := by
      simp [c4, c3, c2, c1, Function.update]
    simp only [c0] at h1
    dsimp only
    simp only [execution]
    have hzero : q0 = (0 : Fin (s + 15 + 1)) := by
      apply Fin.ext
      simp [q0]
    rw [hzero] at h1
    rw [h1, h2, h3, h4, h5, h6]
    simp [c6, c5, c4, c3, q0, Function.update, hreg8]

/-- Exact instruction count for one positive binary-counter decrement. -/
def binaryCounterCycleSteps : List Bool → ℕ
  | [] => 0
  | true :: _ => 6
  | false :: xs => 2 + binaryCounterScanSteps [true] xs

/-- One complete counter cycle implements the pure decrement function and
adds exactly one unary counter bit. This is the local simulation invariant
needed for induction over the input value K. -/
theorem binaryCounter_decrement_cycle {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 (s + 15))
    (bits : ℕ → Bool) (xs ys : List Bool)
    (hcontrol : c.control = (⟨0, by omega⟩ : Fin (s + 15 + 1)))
    (houtput : c.output = none) (hcounter : c.registers 9 = xs)
    (hscratch : c.registers 6 = [])
    (hdecrement : decrementBinaryWord xs = some ys) :
    let out := execution (binaryCounterThenProgram P) O c bits
      (binaryCounterCycleSteps xs)
    out.control = 0 ∧ out.output = none ∧ out.registers 9 = ys ∧ out.registers 6 = [] ∧
      out.registers 8 = false :: c.registers 8 ∧
      out.bitOperations = c.bitOperations + binaryCounterCycleSteps xs ∧
      out.oracleCalls = c.oracleCalls := by
  cases xs with
  | nil => simp [decrementBinaryWord] at hdecrement
  | cons b xs =>
    cases b
    · obtain ⟨z, hz, rfl⟩ := by
        simpa [decrementBinaryWord, Option.map_eq_some_iff] using hdecrement
      have hpos : 0 < binaryValue xs := by
        have hs := decrementBinaryWord_sound hz
        omega
      have hcycle := binaryCounter_false_cycle P O c bits xs hcontrol houtput
        (by simpa using hcounter) hscratch hpos
      have hresult := binaryCounterScanResult_eq_append_decrement [true] xs z hz
      simp [binaryCounterCycleSteps, hcycle, hresult]
    · simp only [decrementBinaryWord, Option.some.injEq] at hdecrement
      subst ys
      have hcycle := binaryCounter_true_cycle P O c bits xs hcontrol houtput
        (by simpa using hcounter) hscratch
      simpa [binaryCounterCycleSteps] using hcycle

/-- Total instruction count for K positive decrements followed by the zero
cleanup and sampler handoff. -/
def binaryCounterCountdownSteps : ℕ → List Bool → ℕ
  | 0, xs => binaryCounterZeroCycleSteps xs
  | k + 1, xs => match decrementBinaryWord xs with
      | some ys => binaryCounterCycleSteps xs + binaryCounterCountdownSteps k ys
      | none => 0

private theorem binaryCounter_replicate_false_append (k : ℕ) (xs : List Bool) :
    List.replicate k false ++ false :: xs =
      false :: (List.replicate k false ++ xs) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simpa only [List.replicate_succ, List.cons_append] using
        congrArg (List.cons false) ih

/-- Starting with a word representing K, the fixed counter machine performs
exactly K decrements, clears its fixed-width zero word, and enters the sampler.
It leaves K unary zeroes in register 8 and accounts for every instruction. -/
theorem binaryCounter_countdown {s n K : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 (s + 15))
    (bits : ℕ → Bool) (xs : List Bool)
    (hvalue : binaryValue xs = K)
    (hcontrol : c.control = (⟨0, by omega⟩ : Fin (s + 15 + 1)))
    (houtput : c.output = none) (hcounter : c.registers 9 = xs)
    (hscratch : c.registers 6 = []) :
    let out := execution (binaryCounterThenProgram P) O c bits
      (binaryCounterCountdownSteps K xs)
    out.control = (⟨10, by omega⟩ : Fin (s + 15 + 1)) ∧ out.output = none ∧
      out.registers 9 = [] ∧ out.registers 6 = [] ∧
      out.registers 8 = List.replicate K false ++ c.registers 8 ∧
      out.bitOperations = c.bitOperations + binaryCounterCountdownSteps K xs ∧
      out.oracleCalls = c.oracleCalls := by
  induction K generalizing xs c bits with
  | zero =>
    have hzero : binaryValue xs = 0 := hvalue
    have hrun := binaryCounter_zero_cycle P O c bits xs
      hcontrol houtput hcounter hscratch hzero
    simpa [binaryCounterCountdownSteps, List.replicate_succ] using hrun
  | succ K ih =>
    have hpositive : 0 < binaryValue xs := by omega
    obtain ⟨ys, hdec⟩ := decrementBinaryWord_exists_of_pos xs hpositive
    have hvalue' : binaryValue ys = K := by
      have hs := decrementBinaryWord_sound hdec
      omega
    let cycle := binaryCounterCycleSteps xs
    let c1 := execution (binaryCounterThenProgram P) O c bits cycle
    have hcycle := binaryCounter_decrement_cycle P O c bits xs ys
      hcontrol houtput hcounter hscratch hdec
    rcases hcycle with ⟨hcontrol1, houtput1, hcounter1, hscratch1,
      hregister8, hbitOperations1, horacle1⟩
    have hih := ih c1 (fun t => bits (cycle + t)) ys hvalue'
      (by simpa [c1] using hcontrol1) (by simpa [c1] using houtput1)
      (by simpa [c1] using hcounter1) (by simpa [c1] using hscratch1)
    have hsplit : execution (binaryCounterThenProgram P) O c bits
        (cycle + binaryCounterCountdownSteps K ys) =
      execution (binaryCounterThenProgram P) O c1
        (fun t => bits (cycle + t)) (binaryCounterCountdownSteps K ys) := by
      rw [binarySampler_execution_add_steps]
    rw [show binaryCounterCountdownSteps (K + 1) xs =
        cycle + binaryCounterCountdownSteps K ys by
          simp [binaryCounterCountdownSteps, hdec, cycle]]
    rw [hsplit]
    have hregister8' : c1.registers 8 = false :: c.registers 8 := by
      simpa [c1, cycle] using hregister8
    have hbitOperations' : c1.bitOperations = c.bitOperations + cycle := by
      simpa [c1, cycle] using hbitOperations1
    have horacle' : c1.oracleCalls = c.oracleCalls := by
      simpa [c1, cycle] using horacle1
    have hstack := binaryCounter_replicate_false_append K (c.registers 8)
    simpa [hregister8', hbitOperations', horacle', hstack,
      List.replicate_succ, Nat.add_assoc] using hih

/-- Running the counter from the actual binary initializer reaches the sampler
with K unary zeroes, without changing the supplied random-bit stream. -/
theorem binaryCounter_countdown_from_binary_input {s n K : ℕ}
    (P : Program 2 s) (O : IndependenceOracle n)
    (c : MachineConfig 2 (s + 15)) (bits : ℕ → Bool)
    (hcontrol : c.control = (⟨0, by omega⟩ : Fin (s + 15 + 1)))
    (houtput : c.output = none) (hscratch : c.registers 6 = []) :
    let input := binarySamplerInput c K
    let out := execution (binaryCounterThenProgram P) O input bits
      (binaryCounterCountdownSteps K K.bits)
    out.control = (⟨10, by omega⟩ : Fin (s + 15 + 1)) ∧
      out.output = none ∧ out.registers 9 = [] ∧ out.registers 6 = [] ∧
      out.registers 8 = List.replicate K false ++ c.registers 8 ∧
      out.bitOperations = input.bitOperations +
        binaryCounterCountdownSteps K K.bits ∧ out.oracleCalls = input.oracleCalls := by
  let input := binarySamplerInput c K
  have h := binaryCounter_countdown P O input bits K.bits
    (machineBinaryValue_bits K)
    (by simpa [input, binarySamplerInput] using hcontrol)
    (by simpa [input, binarySamplerInput] using houtput)
    (by simp [input, binarySamplerInput])
    (by simpa [input, binarySamplerInput] using hscratch)
  simpa [input, binarySamplerInput] using h

/-- A borrow scan costs linearly many instructions in the counter width and
the temporary prefix length. -/
theorem binaryCounterScanSteps_le (acc xs : List Bool) :
    binaryCounterScanSteps acc xs ≤
      4 * xs.length + 2 * acc.length + 6 := by
  induction xs generalizing acc with
  | nil => simp [binaryCounterScanSteps]
  | cons b xs ih =>
    cases b
    · simp only [binaryCounterScanSteps, List.length_cons]
      have h := ih (true :: acc)
      simp only [List.length_cons] at h
      omega
    · simp [binaryCounterScanSteps, List.length_cons]

/-- A successful pure decrement preserves the stored binary-word width. -/
theorem decrementBinaryWord_length : ∀ {xs ys : List Bool},
    decrementBinaryWord xs = some ys → ys.length = xs.length := by
  intro xs
  induction xs with
  | nil => simp [decrementBinaryWord]
  | cons b xs ih =>
    cases b
    · intro ys h
      simp only [decrementBinaryWord, Option.map_eq_some_iff] at h
      obtain ⟨z, hz, rfl⟩ := h
      have := ih hz
      simp [this]
    · intro ys h
      simp only [decrementBinaryWord, Option.some.injEq] at h
      subst ys
      simp

/-- The machine decrements a positive counter in time linear in its encoded
width. -/
theorem binaryCounterCycleSteps_le (xs : List Bool) :
    binaryCounterCycleSteps xs ≤ 4 * xs.length + 6 := by
  cases xs with
  | nil => simp [binaryCounterCycleSteps]
  | cons b xs =>
    cases b
    · simp only [binaryCounterCycleSteps, List.length_cons]
      have h := binaryCounterScanSteps_le [true] xs
      simp only [List.length_cons, List.length_nil] at h
      omega
    · simp [binaryCounterCycleSteps, List.length_cons]

/-- The zero-value cleanup is bounded by a linear function of the fixed word
width. -/
theorem binaryCounterZeroCycleSteps_le {xs : List Bool}
    (hzero : binaryValue xs = 0) :
    binaryCounterZeroCycleSteps xs ≤ 3 * xs.length + 2 := by
  cases xs with
  | nil => simp [binaryCounterZeroCycleSteps]
  | cons b xs =>
    cases b
    · have htail : binaryValue xs = 0 := by
        simpa [binaryValue] using hzero
      have hscan := binaryCounterZeroScanSteps_le [true] xs
      simp only [List.length_cons, List.length_singleton, List.length_nil] at hscan
      simp only [binaryCounterZeroCycleSteps, List.length_cons]
      omega
    · simp [binaryValue] at hzero

/-- Counting down from K costs at most K linear-width decrement cycles followed
by one linear-width zero cleanup. -/
theorem binaryCounterCountdownSteps_le {K : ℕ} (xs : List Bool)
    (hvalue : binaryValue xs = K) :
    binaryCounterCountdownSteps K xs ≤
      K * (4 * xs.length + 6) + 3 * xs.length + 2 := by
  induction K generalizing xs with
  | zero =>
    have h := binaryCounterZeroCycleSteps_le (xs := xs) hvalue
    simpa [binaryCounterCountdownSteps] using h
  | succ K ih =>
    have hpositive : 0 < binaryValue xs := by omega
    obtain ⟨ys, hdec⟩ := decrementBinaryWord_exists_of_pos xs hpositive
    have hvalue' : binaryValue ys = K := by
      have hs := decrementBinaryWord_sound hdec
      omega
    have hlength := decrementBinaryWord_length hdec
    have htail := ih ys hvalue'
    rw [hlength] at htail
    have hcycle := binaryCounterCycleSteps_le xs
    simp [binaryCounterCountdownSteps, hdec]
    rw [Nat.succ_mul]
    omega

/-- The K sampler coins occupy a fixed injective block after the deterministic
counter prefix. Their locations depend on K, never on the sampled bits. -/
def binaryCounterSamplingPositions (K : ℕ) :
    Fin K ↪ Fin (binaryCounterCountdownSteps K K.bits + (3 * K + 1)) where
  toFun i := ⟨binaryCounterCountdownSteps K K.bits + 3 * i.val + 1, by
    have hi := i.isLt
    omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp at hv
    omega

@[simp] theorem binaryCounterSamplingPositions_val {K : ℕ} (i : Fin K) :
    (binaryCounterSamplingPositions K i).val =
      binaryCounterCountdownSteps K K.bits + 3 * i.val + 1 := rfl

/-- The embedded sampler's output stack is exactly the reverse of the K bits
read at the counter-shifted injective positions. -/
theorem binaryCounterSampledStack_eq_positions {K : ℕ} (bits : ℕ → Bool) :
    sampledStack (fun t => bits (binaryCounterCountdownSteps K K.bits + t)) K =
      (List.ofFn (fun i : Fin K => bits ((binaryCounterSamplingPositions K i).val))).reverse := by
  rw [sampledStack_eq_reverse_ofFn]
  congr 1

/-- Listing a finite function at reverse indices reverses its `ofFn` list. -/
theorem ofFn_rev_eq_reverse {α : Type*} : ∀ {K : ℕ} (f : Fin K → α),
    List.ofFn (fun i : Fin K => f i.rev) = (List.ofFn f).reverse
  | 0, f => by simp
  | K + 1, f => by
      rw [List.ofFn_succ, List.ofFn_succ', List.concat_eq_append,
        List.reverse_append]
      simp only [List.reverse_singleton, List.nil_append]
      have hzero : (0 : Fin (K + 1)).rev = Fin.last K := by
        apply Fin.ext
        simp [Fin.rev]
      have hsucc : ∀ i : Fin K, (Fin.succ i).rev = Fin.castSucc i.rev := by
        intro i
        apply Fin.ext
        simp [Fin.rev]
      simp_rw [hzero, hsucc]
      have hrec := ofFn_rev_eq_reverse (fun i : Fin K => f (Fin.castSucc i))
      simpa using congrArg (fun xs => f (Fin.last K) :: xs) hrec

/-- Reindex the deterministic sampler positions backwards so the resulting
stack is the ordinary `List.ofFn` input expected by the estimator. -/
def binaryCounterSamplingPositionsReversed (K : ℕ) :
    Fin K ↪ Fin (binaryCounterCountdownSteps K K.bits + (3 * K + 1)) :=
  { toFun := fun i => binaryCounterSamplingPositions K i.rev
    inj' := by
      intro i j h
      apply Fin.rev_injective
      exact (binaryCounterSamplingPositions K).injective h }

@[simp] theorem binaryCounterSamplingPositionsReversed_val {K : ℕ} (i : Fin K) :
    (binaryCounterSamplingPositionsReversed K i).val =
      binaryCounterCountdownSteps K K.bits + 3 * i.rev.val + 1 := rfl

theorem binaryCounterSampledStack_eq_positionsReversed {K : ℕ}
    (bits : ℕ → Bool) :
    sampledStack (fun t => bits (binaryCounterCountdownSteps K K.bits + t)) K =
      List.ofFn (fun i : Fin K =>
        bits ((binaryCounterSamplingPositionsReversed K i).val)) := by
  rw [binaryCounterSampledStack_eq_positions, ← ofFn_rev_eq_reverse]
  rfl

/-- Regard every sampler coin position as a position in a larger finite tape. -/
def binaryCounterSamplingPositionsBelow (K B : ℕ)
    (hbound : binaryCounterCountdownSteps K K.bits + (3 * K + 1) ≤ B) :
    Fin K ↪ Fin B :=
  (binaryCounterSamplingPositions K).trans (Fin.castLEEmb hbound)

/-- The combined machine samples exactly the selected bits of the original
finite tape, with the same ordering convention as the published sampler. -/
theorem binaryCounterSampledStack_eq_finiteTape {K B : ℕ}
    (tape : Fin B → Bool)
    (hbound : binaryCounterCountdownSteps K K.bits + (3 * K + 1) ≤ B) :
    sampledStack (fun t => finiteBits tape
        (binaryCounterCountdownSteps K K.bits + t)) K =
      (List.ofFn (fun i : Fin K =>
        tape (binaryCounterSamplingPositionsBelow K B hbound i))).reverse := by
  rw [binaryCounterSampledStack_eq_positions]
  apply List.reverse_injective
  simp only [List.reverse_reverse]
  rw [List.ofFn_inj]
  funext i
  have hpos : (binaryCounterSamplingPositions K i).val < B := by
    have hi := i.isLt
    dsimp [binaryCounterSamplingPositions]
    omega
  simp only [finiteBits, dif_pos hpos]
  congr 1

/-- The finite-tape identity in the exact order consumed by the estimator. -/
theorem binaryCounterSampledStack_eq_finiteTapeReversed {K B : ℕ}
    (tape : Fin B → Bool)
    (hbound : binaryCounterCountdownSteps K K.bits + (3 * K + 1) ≤ B) :
    sampledStack (fun t => finiteBits tape
        (binaryCounterCountdownSteps K K.bits + t)) K =
      List.ofFn (fun i : Fin K =>
        tape (binaryCounterSamplingPositionsBelow K B hbound i.rev)) := by
  rw [binaryCounterSampledStack_eq_finiteTape, ← ofFn_rev_eq_reverse]

/-- The concrete countdown overhead is quadratic in K, so it remains
polynomial when K is the already-bounded source schedule. -/
theorem binaryCounterCountdownSteps_bits_le (K : ℕ) :
    binaryCounterCountdownSteps K K.bits ≤
      K * (4 * (K + 1) + 6) + 3 * (K + 1) + 2 := by
  have hlen : K.bits.length ≤ K + 1 := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.2
    exact Nat.lt_of_le_of_lt (Nat.le_succ K)
      (Nat.lt_pow_self (by decide : 1 < 2))
  calc
    binaryCounterCountdownSteps K K.bits ≤
        K * (4 * K.bits.length + 6) + 3 * K.bits.length + 2 :=
      binaryCounterCountdownSteps_le K.bits (machineBinaryValue_bits K)
    _ ≤ K * (4 * (K + 1) + 6) + 3 * (K + 1) + 2 := by gcongr

/-- Total tape prefix through the last sampler coin, including the deterministic
counter startup, is quadratic in K. -/
theorem binaryCounterSamplingPrefixSteps_le (K : ℕ) :
    binaryCounterCountdownSteps K K.bits + (3 * K + 1) ≤
      4 * K ^ 2 + 16 * K + 6 := by
  have h := binaryCounterCountdownSteps_bits_le K
  nlinarith [h]

/-- If the requested sample count is at most H, the counter and sampling
prefix fits in a fixed quadratic clock budget in H. -/
theorem binaryCounterSamplingPrefixSteps_le_of_le {K H : ℕ} (hK : K ≤ H) :
    binaryCounterCountdownSteps K K.bits + (3 * K + 1) ≤ 26 * (H + 1) ^ 2 := by
  have hprefix := binaryCounterSamplingPrefixSteps_le K
  have hpow : K ^ 2 ≤ H ^ 2 := Nat.pow_le_pow_left hK 2
  nlinarith

/-- Uniform polynomial-clock positions, useful when the caller knows only the
polynomial input/tape/charge envelope H rather than the exact K. -/
def binaryCounterSamplingPositionsPolynomial (K H : ℕ) (hK : K ≤ H) :
    Fin K ↪ Fin (26 * (H + 1) ^ 2) :=
  binaryCounterSamplingPositionsBelow K (26 * (H + 1) ^ 2)
    (binaryCounterSamplingPrefixSteps_le_of_le hK)

/-- This explicit sampling clock is polynomial in the charge envelope H. -/
theorem binaryCounterSamplingClock_polynomial :
    Cslib.PolynomiallyBounded (fun H => 26 * (H + 1) ^ 2) := by
  rw [Cslib.polynomiallyBounded_iff_le]
  exact ⟨26, 2, fun _ => le_rfl⟩

/-- The finite-tape sampler is therefore valid directly at the quadratic clock
budget obtained from the coarse bound K≤H. -/
theorem binaryCounterSampledStack_eq_polynomialTape {K H : ℕ}
    (tape : Fin (26 * (H + 1) ^ 2) → Bool) (hK : K ≤ H) :
    sampledStack (fun t => finiteBits tape
        (binaryCounterCountdownSteps K K.bits + t)) K =
      (List.ofFn (fun i : Fin K =>
        tape (binaryCounterSamplingPositionsPolynomial K H hK i))).reverse := by
  simpa [binaryCounterSamplingPositionsPolynomial] using
    (binaryCounterSampledStack_eq_finiteTape (K := K)
      (B := 26 * (H + 1) ^ 2) tape
      (binaryCounterSamplingPrefixSteps_le_of_le hK))

/-- The mission-order sampled list is available directly from the explicit
quadratic finite random tape budget. -/
def binaryCounterSamplingPositionsPolynomialReversed (K H : ℕ) (hK : K ≤ H) :
    Fin K ↪ Fin (26 * (H + 1) ^ 2) :=
  { toFun := fun i => binaryCounterSamplingPositionsPolynomial K H hK i.rev
    inj' := by
      intro i j h
      apply Fin.rev_injective
      exact (binaryCounterSamplingPositionsPolynomial K H hK).injective h }

theorem binaryCounterSampledStack_eq_polynomialTapeReversed {K H : ℕ}
    (tape : Fin (26 * (H + 1) ^ 2) → Bool) (hK : K ≤ H) :
    sampledStack (fun t => finiteBits tape
        (binaryCounterCountdownSteps K K.bits + t)) K =
      List.ofFn (fun i : Fin K =>
        tape (binaryCounterSamplingPositionsPolynomialReversed K H hK i)) := by
  simpa [binaryCounterSamplingPositionsPolynomialReversed,
    binaryCounterSamplingPositionsPolynomial, binaryCounterSamplingPositionsBelow] using
    (binaryCounterSampledStack_eq_finiteTapeReversed (K := K)
      (B := 26 * (H + 1) ^ 2) tape
      (binaryCounterSamplingPrefixSteps_le_of_le hK))

/-- State 10 of the counter machine is the existing balanced sampler with its
control states shifted by ten. -/
def binaryCounterSamplingConfig {s : ℕ} (c : MachineConfig 2 (s + 15))
    (bits : ℕ → Bool) (K m : ℕ) : MachineConfig 2 (s + 15) :=
  { c with
    registers := Function.update
      (Function.update c.registers 8 (List.replicate (K - m) false)) 9
      (sampledStack bits m ++ c.registers 9)
    control := ⟨10, by omega⟩
    output := none
    bitOperations := c.bitOperations + 3 * m }

/-- One balanced-sampling cycle in the combined counter program. -/
theorem binaryCounterSampling_cycle {s n : ℕ}
    (P : Program 2 s) (O : IndependenceOracle n)
    (c : MachineConfig 2 (s + 15)) (bits : ℕ → Bool)
    (rest : List Bool) (hcontrol : c.control = (⟨10, by omega⟩ : Fin (s + 15 + 1)))
    (houtput : c.output = none) (hcounter : c.registers 8 = false :: rest) :
    execution (binaryCounterThenProgram P) O c bits 3 =
      { c with
        registers := Function.update (Function.update c.registers 8 rest) 9
          (bits 1 :: c.registers 9)
        control := ⟨10, by omega⟩
        bitOperations := c.bitOperations + 3 } := by
  cases c with
  | mk registers control output oracleCalls bitOperations =>
    simp only at hcontrol houtput hcounter
    subst control
    subst output
    let q10 : Fin (s + 15 + 1) := ⟨10, by omega⟩
    let q11 : Fin (s + 15 + 1) := ⟨11, by omega⟩
    let q12 : Fin (s + 15 + 1) := ⟨12, by omega⟩
    let q13 : Fin (s + 15 + 1) := ⟨13, by omega⟩
    let c0 : MachineConfig 2 (s + 15) := ⟨registers, q10, none, oracleCalls, bitOperations⟩
    let c1 : MachineConfig 2 (s + 15) :=
      ⟨Function.update registers 8 rest, q11, none, oracleCalls, bitOperations + 1⟩
    have hstep1 : machineStep (binaryCounterThenProgram P) O (bits 0) c0 = c1 := by
      simp [machineStep, binaryCounterThenProgram, c0, c1, q10, q11, hcounter]
    cases hbit : bits 1 with
    | false =>
      let c2 : MachineConfig 2 (s + 15) :=
        ⟨Function.update registers 8 rest, q12, none, oracleCalls, bitOperations + 2⟩
      let c3 : MachineConfig 2 (s + 15) :=
        ⟨Function.update (Function.update registers 8 rest) 9
          (false :: registers 9), q10, none, oracleCalls, bitOperations + 3⟩
      have hstep2 : machineStep (binaryCounterThenProgram P) O (bits 1) c1 = c2 := by
        simp [machineStep, binaryCounterThenProgram, c1, c2, q11, q12, hbit]
      have hstep3 : machineStep (binaryCounterThenProgram P) O (bits 2) c2 = c3 := by
        simp [machineStep, binaryCounterThenProgram, c2, c3, q12, q10]
      have hrun : execution (binaryCounterThenProgram P) O c0 bits 3 = c3 := by
        simp only [execution]
        rw [hstep1, hstep2, hstep3]
      change execution (binaryCounterThenProgram P) O c0 bits 3 = _
      simpa [c3, c0, Function.update] using hrun
    | true =>
      let c2 : MachineConfig 2 (s + 15) :=
        ⟨Function.update registers 8 rest, q13, none, oracleCalls, bitOperations + 2⟩
      let c3 : MachineConfig 2 (s + 15) :=
        ⟨Function.update (Function.update registers 8 rest) 9
          (true :: registers 9), q10, none, oracleCalls, bitOperations + 3⟩
      have hstep2 : machineStep (binaryCounterThenProgram P) O (bits 1) c1 = c2 := by
        simp [machineStep, binaryCounterThenProgram, c1, c2, q11, q13, hbit]
      have hstep3 : machineStep (binaryCounterThenProgram P) O (bits 2) c2 = c3 := by
        simp [machineStep, binaryCounterThenProgram, c2, c3, q13, q10]
      have hrun : execution (binaryCounterThenProgram P) O c0 bits 3 = c3 := by
        simp only [execution]
        rw [hstep1, hstep2, hstep3]
      change execution (binaryCounterThenProgram P) O c0 bits 3 = _
      simpa [c3, c0, Function.update] using hrun

/-- The shifted sampler consumes any prefix of the K unary counter bits and
stores exactly the corresponding fair-bit prefix on register 9. -/
theorem binaryCounterSampling_prefix {s n : ℕ}
    (P : Program 2 s) (O : IndependenceOracle n)
    (c : MachineConfig 2 (s + 15)) (bits : ℕ → Bool) (K m : ℕ)
    (hm : m ≤ K) :
    execution (binaryCounterThenProgram P) O
      (binaryCounterSamplingConfig c bits K 0) bits (3 * m) =
      binaryCounterSamplingConfig c bits K m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hrem : K - m = (K - (m + 1)) + 1 := by omega
    rw [show 3 * (m + 1) = 3 * m + 3 by omega,
      binarySampler_execution_add_steps, ih (by omega)]
    rw [binaryCounterSampling_cycle P O
      (binaryCounterSamplingConfig c bits K m) (fun t => bits (3 * m + t))
      (List.replicate (K - (m + 1)) false)
      (by simp [binaryCounterSamplingConfig]) (by simp [binaryCounterSamplingConfig])
      (by simp [binaryCounterSamplingConfig, hrem, List.replicate_succ])]
    apply binarySamplerConfig_ext
    · funext i
      by_cases h8 : i = 8 <;> by_cases h9 : i = 9 <;>
        simp [binaryCounterSamplingConfig, hrem, sampledStack,
          List.replicate_succ, Function.update, h8, h9]
    · rfl
    · rfl
    · rfl
    · simp [binaryCounterSamplingConfig, Nat.mul_add, Nat.add_assoc]

/-- After K sampler cycles, the machine exits to the continuation at state 15. -/
theorem binaryCounterSampling_done {s n : ℕ}
    (P : Program 2 s) (O : IndependenceOracle n)
    (c : MachineConfig 2 (s + 15)) (bits : ℕ → Bool) (K : ℕ) :
    execution (binaryCounterThenProgram P) O
      (binaryCounterSamplingConfig c bits K 0) bits (3 * K + 1) =
      { binaryCounterSamplingConfig c bits K K with
        control := ⟨15, by omega⟩
        bitOperations := c.bitOperations + (3 * K + 1) } := by
  rw [binarySampler_execution_add_steps (a := 3 * K) (b := 1)]
  rw [binaryCounterSampling_prefix P O c bits K K (by omega)]
  change machineStep (binaryCounterThenProgram P) O (bits (3 * K))
    (binaryCounterSamplingConfig c bits K K) = _
  simp [machineStep, binaryCounterThenProgram, binaryCounterSamplingConfig,
    Function.update, Nat.add_assoc]

/-- From the actual K.bits initializer, the counter and embedded sampler run
back-to-back and hand the exact sampled stack to the estimator continuation. -/
theorem binaryCounterThenSampler {s n K : ℕ}
    (P : Program 2 s) (O : IndependenceOracle n)
    (c : MachineConfig 2 (s + 15)) (bits : ℕ → Bool)
    (hcontrol : c.control = (⟨0, by omega⟩ : Fin (s + 15 + 1)))
    (houtput : c.output = none) (hscratch : c.registers 6 = [])
    (hcounter : c.registers 8 = []) :
    let input := binarySamplerInput c K
    let counterSteps := binaryCounterCountdownSteps K K.bits
    let prefixConfig := execution (binaryCounterThenProgram P) O input bits counterSteps
    execution (binaryCounterThenProgram P) O input bits (counterSteps + (3 * K + 1)) =
      { binaryCounterSamplingConfig prefixConfig (fun t => bits (counterSteps + t)) K K with
        control := ⟨15, by omega⟩
        bitOperations := prefixConfig.bitOperations + (3 * K + 1) } := by
  let input := binarySamplerInput c K
  let counterSteps := binaryCounterCountdownSteps K K.bits
  let prefixConfig := execution (binaryCounterThenProgram P) O input bits counterSteps
  have hcount := binaryCounter_countdown_from_binary_input (K := K) P O c bits
    hcontrol houtput hscratch
  dsimp only at hcount
  rcases hcount with ⟨hcontrol1, houtput1, hregister9, hregister6,
    hregister8, hbitOperations, horacleCalls⟩
  have hstart : binaryCounterSamplingConfig prefixConfig
      (fun t => bits (counterSteps + t)) K 0 = prefixConfig := by
    apply binarySamplerConfig_ext
    · funext i
      by_cases h8 : i = 8 <;> by_cases h9 : i = 9 <;>
        simp [binaryCounterSamplingConfig, prefixConfig, input, counterSteps,
          hregister9, hregister8, hcounter, h8, h9, sampledStack, Function.update]
    · simp [binaryCounterSamplingConfig, prefixConfig, input, counterSteps, hcontrol1]
    · simp [binaryCounterSamplingConfig, prefixConfig, input, counterSteps, houtput1]
    · rfl
    · simp [binaryCounterSamplingConfig, prefixConfig, input, counterSteps,
        hbitOperations, Nat.add_assoc]
  calc
    execution (binaryCounterThenProgram P) O input bits
        (counterSteps + (3 * K + 1)) =
      execution (binaryCounterThenProgram P) O prefixConfig
        (fun t => bits (counterSteps + t)) (3 * K + 1) := by
          rw [binarySampler_execution_add_steps]
    _ = execution (binaryCounterThenProgram P) O
        (binaryCounterSamplingConfig prefixConfig
          (fun t => bits (counterSteps + t)) K 0)
        (fun t => bits (counterSteps + t)) (3 * K + 1) := by
          congr 1
          exact hstart.symm
    _ = _ := binaryCounterSampling_done P O prefixConfig
      (fun t => bits (counterSteps + t)) K

/-- From the ordinary parameter-register initializer, after placing `K.bits`
in scratch register 9, a polynomial finite random tape lets the sampler hand
the continuation the exact `List.ofFn` sample in register 9. Its own prefix
performs no oracle calls and uses exactly the counter plus balanced-sampler
steps. Computing K from the parameters is a separate remaining obligation. -/
theorem binaryCounterThenSampler_polynomialTape_handoff
    {s n r K H : ℕ} (P : Program 2 s) (O : IndependenceOracle n)
    (tape : Fin (26 * (H + 1) ^ 2) → Bool) (hK : K ≤ H)
    (ε δ : ℚ) :
    let c := initialConfig 2 (s + 15) n r ε δ
    let bits := fun t => finiteBits tape t
    let counterSteps := binaryCounterCountdownSteps K K.bits
    let prefixLength := counterSteps + (3 * K + 1)
    let sampled := execution (binaryCounterThenProgram P) O
      (binarySamplerInput c K) bits prefixLength
    sampled.control.val = 15 ∧ sampled.output = none ∧
      sampled.registers 9 = List.ofFn (fun i : Fin K =>
        tape (binaryCounterSamplingPositionsPolynomialReversed K H hK i)) ∧
      sampled.oracleCalls = 0 ∧ sampled.bitOperations = prefixLength := by
  dsimp only
  let c : MachineConfig 2 (s + 15) := initialConfig 2 (s + 15) n r ε δ
  let bits : ℕ → Bool := fun t => finiteBits tape t
  let input := binarySamplerInput c K
  let counterSteps := binaryCounterCountdownSteps K K.bits
  let prefixConfig := execution (binaryCounterThenProgram P) O input bits counterSteps
  let prefixLength := counterSteps + (3 * K + 1)
  let sampled := execution (binaryCounterThenProgram P) O input bits prefixLength
  have hcount := binaryCounter_countdown_from_binary_input (K := K) P O c bits
    (by simp [c, initialConfig]) (by simp [c, initialConfig])
    (by simp [c, initialConfig])
  dsimp only at hcount
  rcases hcount with ⟨hcontrol, houtput, hregister9, hregister6,
    hregister8, hbitOperations, horacleCalls⟩
  have hprefixOutput : prefixConfig.output = none := by
    simpa [prefixConfig, input, c, bits, initialConfig, binarySamplerInput] using houtput
  have hprefixCalls : prefixConfig.oracleCalls = 0 := by
    simpa [prefixConfig, input, c, bits, initialConfig, binarySamplerInput] using horacleCalls
  have hprefixCost : prefixConfig.bitOperations = counterSteps := by
    simpa [prefixConfig, input, c, bits, initialConfig, binarySamplerInput] using hbitOperations
  have hhandoff := binaryCounterThenSampler (K := K) P O c bits
    (by simp [c, initialConfig]) (by simp [c, initialConfig])
    (by simp [c, initialConfig]) (by simp [c, initialConfig])
  dsimp only at hhandoff
  have hstate : sampled.control.val = 15 := by
    have h := congrArg (fun cfg : MachineConfig 2 (s + 15) => cfg.control.val) hhandoff
    simpa [sampled, prefixLength, prefixConfig, input, counterSteps] using h
  have hout : sampled.output = none := by
    have h := congrArg (fun cfg : MachineConfig 2 (s + 15) => cfg.output) hhandoff
    simpa [sampled, prefixLength, prefixConfig, input, counterSteps,
      binaryCounterSamplingConfig, hprefixOutput] using h
  have hstack : sampled.registers 9 =
      sampledStack (fun t => bits (counterSteps + t)) K := by
    have h := congrArg (fun cfg : MachineConfig 2 (s + 15) => cfg.registers 9) hhandoff
    simpa [sampled, prefixLength, prefixConfig, input, counterSteps,
      binaryCounterSamplingConfig, Function.update, hregister9] using h
  have hstack' : sampled.registers 9 =
      List.ofFn (fun i : Fin K =>
        tape (binaryCounterSamplingPositionsPolynomialReversed K H hK i)) := by
    rw [hstack]
    simpa [bits, counterSteps] using
      (binaryCounterSampledStack_eq_polynomialTapeReversed tape hK)
  have hcalls : sampled.oracleCalls = 0 := by
    have h := congrArg (fun cfg : MachineConfig 2 (s + 15) => cfg.oracleCalls) hhandoff
    simpa [sampled, prefixLength, prefixConfig, input, counterSteps,
      binaryCounterSamplingConfig, hprefixCalls] using h
  have hcost : sampled.bitOperations = prefixLength := by
    have h := congrArg (fun cfg : MachineConfig 2 (s + 15) => cfg.bitOperations) hhandoff
    simpa [sampled, prefixLength, prefixConfig, input, counterSteps,
      binaryCounterSamplingConfig, hprefixCost] using h
  exact ⟨hstate, hout, hstack', hcalls, hcost⟩

/-- Decode continuation states, whose fixed offset is fifteen. -/
def binaryCounterDecodeState {s : ℕ} (q : Fin (s + 15 + 1)) : Fin (s + 1) :=
  ⟨if q.val < 15 then 0 else q.val - 15, by
    split
    · have hq := q.isLt
      omega
    · have hq := q.isLt
      omega⟩

def binaryCounterDecodeConfig {s : ℕ} (c : MachineConfig 2 (s + 15)) :
    MachineConfig 2 s where
  registers := c.registers
  control := binaryCounterDecodeState c.control
  output := c.output
  oracleCalls := c.oracleCalls
  bitOperations := c.bitOperations

def binaryCounterProgramStartConfig {s : ℕ} (c : MachineConfig 2 (s + 15)) :
    MachineConfig 2 s where
  registers := c.registers
  control := 0
  output := c.output
  oracleCalls := c.oracleCalls
  bitOperations := c.bitOperations

@[simp] theorem binaryCounterDecodeState_shifted {s : ℕ} (q : Fin (s + 1)) :
    binaryCounterDecodeState ⟨q.val + 15, by have hq := q.isLt; omega⟩ = q := by
  apply Fin.ext
  simp [binaryCounterDecodeState]

/-- At every continuation state, the combined program is exactly the shifted
instruction of P. -/
theorem binaryCounterThenProgram_current_instruction {s : ℕ}
    (P : Program 2 s) (q : Fin (s + 15 + 1)) (hcontrol : 15 ≤ q.val) :
    binaryCounterThenProgram P q =
      shiftBinarySamplerInstruction (P (binaryCounterDecodeState q)) := by
  let i : Fin (s + 1) := ⟨q.val - 15, by have hq := q.isLt; omega⟩
  have hq : q = ⟨i.val + 15, by have hi := i.isLt; omega⟩ := by
    apply Fin.ext
    simp [i]
    omega
  rw [hq]
  simp [binaryCounterThenProgram, i, binaryCounterDecodeState,
    shiftBinarySamplerInstruction]

theorem binaryCounterDecode_step_of_current_instruction {s n : ℕ}
    (Q : Program 2 (s + 15)) (P : Program 2 s)
    (O : IndependenceOracle n) (bit : Bool) (c : MachineConfig 2 (s + 15))
    (hcurrent : Q c.control =
      shiftBinarySamplerInstruction (P (binaryCounterDecodeState c.control))) :
    binaryCounterDecodeConfig (machineStep Q O bit c) =
      machineStep P O bit (binaryCounterDecodeConfig c) := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  cases output with
  | some value => rfl
  | none =>
      have hcurrent' : Q control =
          shiftBinarySamplerInstruction (P (binaryCounterDecodeState control)) := by
        simpa using hcurrent
      simp only [machineStep, Option.isSome_none, ↓reduceIte, hcurrent']
      cases hp : P (binaryCounterDecodeState control) with
      | push i b next => simp [binaryCounterDecodeConfig, shiftBinarySamplerInstruction, hp]
      | pop i empty zero one =>
          cases hstack : regs i with
          | nil => simp [binaryCounterDecodeConfig, shiftBinarySamplerInstruction, hp, hstack]
          | cons b rest => cases b <;>
              simp [binaryCounterDecodeConfig, shiftBinarySamplerInstruction, hp, hstack]
      | coin zero one => cases bit <;>
          simp [binaryCounterDecodeConfig, shiftBinarySamplerInstruction, hp]
      | query which i no yes =>
          by_cases hlen : (regs i).length = n
          · have hbits : (fun j : Fin n => (regs i)[j.val]?.getD false) =
                (fun j : Fin n => (regs i)[j.val]) := by
              funext j
              simp [List.getElem?_eq_getElem (by rw [hlen]; exact j.isLt)]
            by_cases hquery : O which
                (fun j : Fin n => (regs i)[j.val]?.getD false) = true
            · have hraw : O which (fun j : Fin n => (regs i)[j.val]) = true := by
                simpa only [← hbits] using hquery
              simp [binaryCounterDecodeConfig, shiftBinarySamplerInstruction, hp,
                hlen, hquery, hraw, binaryCounterDecodeState_shifted]
            · have hraw : ¬ O which (fun j : Fin n => (regs i)[j.val]) = true := by
                simpa only [← hbits] using hquery
              simp [binaryCounterDecodeConfig, shiftBinarySamplerInstruction, hp,
                hlen, hquery, hraw, binaryCounterDecodeState_shifted]
          · simp [binaryCounterDecodeConfig, shiftBinarySamplerInstruction, hp, hlen]
      | halt => simp [binaryCounterDecodeConfig, shiftBinarySamplerInstruction, hp]

theorem binaryCounterThenProgram_machineStep_decode {s n : ℕ}
    (P : Program 2 s) (O : IndependenceOracle n) (bit : Bool)
    (c : MachineConfig 2 (s + 15)) (hcontrol : 15 ≤ c.control.val) :
    binaryCounterDecodeConfig (machineStep (binaryCounterThenProgram P) O bit c) =
      machineStep P O bit (binaryCounterDecodeConfig c) := by
  apply binaryCounterDecode_step_of_current_instruction
  exact binaryCounterThenProgram_current_instruction P c.control hcontrol

theorem binaryCounterThenProgram_step_control_valid {s n : ℕ}
    (P : Program 2 s) (O : IndependenceOracle n) (bit : Bool)
    (c : MachineConfig 2 (s + 15)) (hcontrol : 15 ≤ c.control.val) :
    15 ≤ (machineStep (binaryCounterThenProgram P) O bit c).control.val := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  cases output with
  | some value => exact hcontrol
  | none =>
      have hcontrol' : 15 ≤ control.val := by simpa using hcontrol
      have hcurrent := binaryCounterThenProgram_current_instruction P control hcontrol
      have hcurrent' : binaryCounterThenProgram P control =
          shiftBinarySamplerInstruction (P (binaryCounterDecodeState control)) := by
        simpa using hcurrent
      simp only [machineStep, Option.isSome_none, ↓reduceIte, hcurrent']
      cases hp : P (binaryCounterDecodeState control) with
      | push i b next => simp [shiftBinarySamplerInstruction, hp]
      | pop i empty zero one =>
          cases hstack : regs i with
          | nil => simp [shiftBinarySamplerInstruction, hp, hstack]
          | cons b rest => cases b <;>
              simp [shiftBinarySamplerInstruction, hp, hstack]
      | coin zero one => cases bit <;>
          simp [shiftBinarySamplerInstruction, hp]
      | query which i no yes =>
          by_cases hlen : (regs i).length = n
          · have hbits : (fun j : Fin n => (regs i)[j.val]?.getD false) =
                (fun j : Fin n => (regs i)[j.val]) := by
              funext j
              simp [List.getElem?_eq_getElem (by rw [hlen]; exact j.isLt)]
            by_cases hquery : O which
                (fun j : Fin n => (regs i)[j.val]?.getD false) = true
            · have hraw : O which (fun j : Fin n => (regs i)[j.val]) = true := by
                simpa only [← hbits] using hquery
              simp [shiftBinarySamplerInstruction, hp, hlen, hquery, hraw]
            · have hraw : ¬ O which (fun j : Fin n => (regs i)[j.val]) = true := by
                simpa only [← hbits] using hquery
              simp [shiftBinarySamplerInstruction, hp, hlen, hquery, hraw]
          · simp [shiftBinarySamplerInstruction, hp, hlen, hcontrol']
      | halt => simp [shiftBinarySamplerInstruction, hp, hcontrol']

theorem binaryCounterThenProgram_execution_control_valid {s n : ℕ}
    (P : Program 2 s) (O : IndependenceOracle n)
    (c : MachineConfig 2 (s + 15)) (bits : ℕ → Bool) (t : ℕ)
    (hcontrol : 15 ≤ c.control.val) :
    15 ≤ (execution (binaryCounterThenProgram P) O c bits t).control.val := by
  induction t with
  | zero => exact hcontrol
  | succ t ih =>
      change 15 ≤ (machineStep (binaryCounterThenProgram P) O (bits t)
        (execution (binaryCounterThenProgram P) O c bits t)).control.val
      exact binaryCounterThenProgram_step_control_valid P O (bits t) _ ih

theorem binaryCounterThenProgram_execution_decode {s n : ℕ}
    (P : Program 2 s) (O : IndependenceOracle n)
    (c : MachineConfig 2 (s + 15)) (bits : ℕ → Bool) (t : ℕ)
    (hcontrol : c.control.val = 15) :
    binaryCounterDecodeConfig
      (execution (binaryCounterThenProgram P) O c bits t) =
      execution P O (binaryCounterProgramStartConfig c) bits t := by
  induction t with
  | zero =>
      rcases c with ⟨regs, control, output, calls, ops⟩
      have hc : control = ⟨15, by omega⟩ := Fin.ext hcontrol
      rw [hc]
      rfl
  | succ t ih =>
      change binaryCounterDecodeConfig
          (machineStep (binaryCounterThenProgram P) O (bits t)
            (execution (binaryCounterThenProgram P) O c bits t)) = _
      rw [binaryCounterThenProgram_machineStep_decode P O (bits t) _
        (binaryCounterThenProgram_execution_control_valid P O c bits t
          (by omega))]
      rw [ih]
      rfl

/-- The complete counter-plus-sampler prefix is observationally the same as
starting the continuation program on the sampled configuration.  The tail of
the infinite tape is shifted by the exact deterministic prefix length. -/
theorem binaryCounterThenSampler_then_program {s n K : ℕ}
    (P : Program 2 s) (O : IndependenceOracle n)
    (c : MachineConfig 2 (s + 15)) (bits : ℕ → Bool)
    (hcontrol : c.control = (⟨0, by omega⟩ : Fin (s + 15 + 1)))
    (houtput : c.output = none) (hscratch : c.registers 6 = [])
    (hcounter : c.registers 8 = []) (t : ℕ) :
    let input := binarySamplerInput c K
    let totalPrefix := binaryCounterCountdownSteps K K.bits + (3 * K + 1)
    let sampled := execution (binaryCounterThenProgram P) O input bits totalPrefix
    binaryCounterDecodeConfig
        (execution (binaryCounterThenProgram P) O input bits (totalPrefix + t)) =
      execution P O (binaryCounterProgramStartConfig sampled)
        (fun j => bits (totalPrefix + j)) t := by
  let input := binarySamplerInput c K
  let counterSteps := binaryCounterCountdownSteps K K.bits
  let totalPrefix := counterSteps + (3 * K + 1)
  let sampled := execution (binaryCounterThenProgram P) O input bits totalPrefix
  have hhandoff := binaryCounterThenSampler (K := K) P O c bits hcontrol houtput
    hscratch hcounter
  dsimp only at hhandoff
  have hsampled_control : sampled.control.val = 15 := by
    have hcontrol15 := congrArg (fun x : MachineConfig 2 (s + 15) => x.control.val)
      hhandoff
    simpa [sampled, totalPrefix, counterSteps, input] using hcontrol15
  change binaryCounterDecodeConfig
      (execution (binaryCounterThenProgram P) O input bits (totalPrefix + t)) = _
  rw [binarySampler_execution_add_steps]
  rw [binaryCounterThenProgram_execution_decode P O sampled
    (fun j => bits (totalPrefix + j)) t hsampled_control]

/-- Specialize the counter/sampler composition to the mission's ordinary
parameter-register initializer. Only the deterministic estimator body remains
to be supplied as P. -/
theorem binaryCounterThenSampler_from_initialConfig {s n r K : ℕ}
    (P : Program 2 s) (O : IndependenceOracle n) (bits : ℕ → Bool)
    (ε δ : ℚ) (t : ℕ) :
    let c := initialConfig 2 (s + 15) n r ε δ
    let totalPrefix := binaryCounterCountdownSteps K K.bits + (3 * K + 1)
    let sampled := execution (binaryCounterThenProgram P) O
      (binarySamplerInput c K) bits totalPrefix
    binaryCounterDecodeConfig
        (execution (binaryCounterThenProgram P) O (binarySamplerInput c K) bits
          (totalPrefix + t)) =
      execution P O (binaryCounterProgramStartConfig sampled)
        (fun j => bits (totalPrefix + j)) t := by
  simpa [initialConfig] using
    (binaryCounterThenSampler_then_program (K := K) P O
      (initialConfig 2 (s + 15) n r ε δ) bits rfl rfl
      (by simp [initialConfig]) (by simp [initialConfig]) t)

/-- The zero counter takes the sampler handoff branch in one charged step. -/
theorem binaryCounter_zero_handoff {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 (s + 15))
    (bits : ℕ → Bool) (hcontrol : c.control = 0) (houtput : c.output = none)
    (hcounter : c.registers 9 = []) (hscratch : c.registers 6 = []) :
    let out := execution (binaryCounterThenProgram P) O c bits 1
    out.control = (⟨10, by omega⟩ : Fin (s + 15 + 1)) ∧
      out.output = none ∧ out.registers 9 = [] ∧ out.registers 6 = [] ∧
      out.bitOperations = c.bitOperations + 1 ∧ out.oracleCalls = c.oracleCalls := by
  cases c with
  | mk registers control output oracleCalls bitOperations =>
    simp only at hcontrol houtput hcounter hscratch
    subst control
    subst output
    simp [execution, machineStep, binaryCounterThenProgram, hcounter, hscratch]

end CountingMatroid.Bridge


