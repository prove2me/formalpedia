-- Prove2me | Definitions.Def_CommonBasesFPRAS
-- name    : CommonBasesFPRAS
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:04.400753+00:00
-- url     : https://prove2.me/theorems/1699bb1a-f442-4d87-8511-289d98772c60
-- statement:
--   For two matroids on the labeled set {0,…,n−1}, an independence oracle takes a choice of matroid and an n-bit subset indicator; exactness means its answer is true precisely for independent subsets. The common-base count Z is the number of subsets that are bases of both matroids. A randomized oracle machine has k+8 registers containing bit lists, s+1 control states, an optional rational output, and counters for oracle calls and bit operations. Its instructions push or pop bits, branch on a random bit, query either oracle using a register of length n, or halt. An invalid query terminates with output zero; halting outputs the ratio of the unsigned binary values in registers 6 and 7, with division by zero interpreted as zero. Push, pop, and coin instructions cost one bit operation; queries cost the register length plus n+1, and halting costs the two output-register lengths plus one. Registers 0 through 5 initially encode n, r, and the absolute numerators and denominators of rational parameters ε and δ; the remaining registers are empty. Let L be six plus the combined binary lengths of these six input integers, and set B=C(1+n+L+⌈ε⁻¹⌉+⌈log₂⌈δ⁻¹⌉⌉)^d. The defined proposition MainTheorem asserts the existence of fixed k, s, a program, and natural constants C>0 and d such that, for every pair of matroids with full ground set and common rank r, every exact oracle, and 0<ε,δ<1, execution has produced a nonnegative rational output after B steps on every random-bit stream, using at most B oracle calls and B bit operations. Every output must equal zero when Z=0. Moreover, at least a fraction 1−δ of the 2^B equally weighted length-B bit strings produce an output z satisfying (1−ε)Z≤z≤(1+ε)Z. Execution uses the bit at the current time step, and finite bit strings are extended by zeros. This is a defined approximation-scheme proposition, not an established theorem in this block.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CommonBasesFPRAS.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CommonBasesFPRAS.lean; bytes 16..4767
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace CommonBasesFPRAS

abbrev IndependenceOracle (n : ℕ) := Bool → (Fin n → Bool) → Bool

def ExactOracles {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (O : IndependenceOracle n) : Prop :=
  ∀ (which : Bool) (A : Fin n → Bool),
    O which A = true ↔ (if which then M₂ else M₁).Indep {i | A i = true}

noncomputable def commonBaseCount {n : ℕ} (M₁ M₂ : Matroid (Fin n)) : ℕ :=
  Nat.card {A : Finset (Fin n) // M₁.IsBase (A : Set (Fin n)) ∧
    M₂.IsBase (A : Set (Fin n))}

inductive Instruction (k s : ℕ) where
  | push (register : Fin (k + 8)) (bit : Bool) (next : Fin (s + 1))
  | pop (register : Fin (k + 8)) (empty zero one : Fin (s + 1))
  | coin (zero one : Fin (s + 1))
  | query (which : Bool) (register : Fin (k + 8)) (no yes : Fin (s + 1))
  | halt

def Program (k s : ℕ) := Fin (s + 1) → Instruction k s

def binaryValue : List Bool → ℕ
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * binaryValue l

structure MachineConfig (k s : ℕ) where
  registers : Fin (k + 8) → List Bool
  control : Fin (s + 1)
  output : Option ℚ := none
  oracleCalls : ℕ := 0
  bitOperations : ℕ := 0

def inputLength (n r : ℕ) (ε δ : ℚ) : ℕ :=
  6 + n.bits.length + r.bits.length + ε.num.natAbs.bits.length + ε.den.bits.length +
    δ.num.natAbs.bits.length + δ.den.bits.length

def initialConfig (k s n r : ℕ) (ε δ : ℚ) : MachineConfig k s where
  registers := fun i => match i.val with
    | 0 => n.bits
    | 1 => r.bits
    | 2 => ε.num.natAbs.bits
    | 3 => ε.den.bits
    | 4 => δ.num.natAbs.bits
    | 5 => δ.den.bits
    | _ => []
  control := 0

def machineStep {k s n : ℕ} (P : Program k s) (O : IndependenceOracle n)
    (randomBit : Bool) (c : MachineConfig k s) : MachineConfig k s :=
  if c.output.isSome then c else
  match P c.control with
  | .push i b next =>
    { c with
      registers := Function.update c.registers i (b :: c.registers i)
      control := next
      bitOperations := c.bitOperations + 1 }
  | .pop i empty zero one =>
    match c.registers i with
    | [] => { c with
      control := empty
      bitOperations := c.bitOperations + 1 }
    | b :: l =>
      { c with
      registers := Function.update c.registers i l
      control := if b then one else zero
      bitOperations := c.bitOperations + 1 }
  | .coin zero one =>
    { c with
      control := if randomBit then one else zero
      bitOperations := c.bitOperations + 1 }
  | .query which i no yes =>
    if (c.registers i).length = n then
      { c with
      control := if O which (fun j => (c.registers i)[j.val]?.getD false)
          then yes else no
      oracleCalls := c.oracleCalls + 1
      bitOperations := c.bitOperations + (c.registers i).length + n + 1 }
    else
      { c with
      output := some 0
      bitOperations := c.bitOperations + (c.registers i).length + n + 1 }
  | .halt =>
    { c with
      output := some ((binaryValue (c.registers ⟨6, by omega⟩) : ℚ) /
        (binaryValue (c.registers ⟨7, by omega⟩) : ℚ))
      bitOperations := c.bitOperations + (c.registers ⟨6, by omega⟩).length +
        (c.registers ⟨7, by omega⟩).length + 1 }

def execution {k s n : ℕ} (P : Program k s) (O : IndependenceOracle n)
    (c : MachineConfig k s) (bits : ℕ → Bool) : ℕ → MachineConfig k s
  | 0 => c
  | t + 1 => machineStep P O (bits t) (execution P O c bits t)

def finiteBits {B : ℕ} (bits : Fin B → Bool) (t : ℕ) : Bool :=
  if h : t < B then bits ⟨t, h⟩ else false

def relativeAccuracy (ε : ℚ) (Z : ℕ) (z : ℚ) : Prop :=
  (1-ε)*(Z:ℚ)≤z ∧ z≤(1+ε)*(Z:ℚ)

def resourceBound (C d n r : ℕ) (ε δ : ℚ) : ℕ :=
  C * (1 + n + inputLength n r ε δ + ⌈ε⁻¹⌉₊ + Nat.clog 2 ⌈δ⁻¹⌉₊) ^ d

def MainTheorem : Prop :=
  ∃ (k s : ℕ) (P : Program k s) (C d : ℕ), 0 < C ∧
    ∀ (n r : ℕ) (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
      (ε δ : ℚ),
      M₁.E = Set.univ → M₂.E = Set.univ →
      M₁.eRank = (r : ℕ∞) → M₂.eRank = (r : ℕ∞) →
      ExactOracles M₁ M₂ O → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      let B := resourceBound C d n r ε δ
      let Z := commonBaseCount M₁ M₂
      (∀ bits : ℕ → Bool,
        let out := execution P O (initialConfig k s n r ε δ) bits B
        out.output.isSome ∧ out.oracleCalls ≤ B ∧ out.bitOperations ≤ B ∧
        ∀ z, out.output = some z → 0 ≤ z ∧ (Z = 0 → z = 0)) ∧
      (1 - δ) * (2 : ℚ) ^ B ≤
        (Nat.card {bits : Fin B → Bool //
          ∃ z, (execution P O (initialConfig k s n r ε δ) (finiteBits bits) B).output
            = some z ∧ relativeAccuracy ε Z z} : ℚ)

end CommonBasesFPRAS



end OAI


