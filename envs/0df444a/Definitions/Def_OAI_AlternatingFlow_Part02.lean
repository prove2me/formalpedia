-- Prove2me | Definitions.Def_OAI_AlternatingFlow_Part02
-- name    : OAI_AlternatingFlow_Part02
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T03:28:49.910275+00:00
-- url     : https://prove2.me/theorems/60b69924-d593-4abf-9ae6-6182f3512fdc
-- title:
--   Alternating-flow construction, part 2 of 11 (port of OpenAI's formalization): Turing-machine simulation, machine profiles and local rules
-- statement:
--   Part 2 of 11 of a port of OpenAI's Lean formalization of the alternating-flow construction from the manuscript *Computation under Rapidly Vanishing Navier–Stokes Forcing* (OpenAI, September 27, 2026). This part contains Turing-machine simulation, machine profiles and local rules.
--
--   **Attribution.** The code is adapted verbatim from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, modules `Machines`, `MachineProfiles`, `LocalRules` of `lean/OAI/MathematicalPhysics/AlternatingFlow`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order with their imports replaced by the previous part. The model definitions come from the platform definition `NavierStokesAlternating`. Part 1 adds compatibility shims for three core lemmas renamed after Lean 4.33.1, and part 3 adjusts one side-goal tactic for Mathlib 0df444a.
--
--   The development is split into eleven parts only so that each compiles within the platform's time limit. Together the parts supply the velocity construction used to prove `OAI.AlternatingNS.velocity_construction`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/MathematicalPhysics/AlternatingFlow: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/Machines.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/MachineProfiles.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/LocalRules.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf

/-
Alternating-flow construction (port of OpenAI's formalization), part 2 of 11: Turing-machine simulation, machine profiles and local rules.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/MathematicalPhysics/AlternatingFlow/: Machines.lean, MachineProfiles.lean, LocalRules.lean
These files formalize the manuscript "Computation under Rapidly Vanishing Navier-Stokes Forcing"
(OpenAI, September 27, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions come from the platform definition `NavierStokesAlternating`.
-/
import Mathlib
import Definitions.Def_OAI_AlternatingFlow_Part01

set_option autoImplicit false

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Machines.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Machine

def Admissible (M : Machine) (c : Configuration) : Prop :=
  c.state ≤ M.states ∧ ∀ i, c.tape i < M.alphabet

def command (M : Machine) (q a : ℕ) : Rule :=
  letI := neZeroThree
  if q = M.states ∨ q ∈ M.haltingStates then (q, a, 1)
  else (M.instruction q a).getD (M.states, a, 1)

lemma step_eq_command (M : Machine) (c : Configuration) :
    M.step c =
      { state := (M.command c.state (c.tape c.head)).1
        head := c.head + (((M.command c.state (c.tape c.head)).2.2.val : ℤ) - 1)
        tape := Function.update c.tape c.head (M.command c.state (c.tape c.head)).2.1 } := by
  unfold step isHalting command
  simp only [decide_eq_true_eq]
  split_ifs with h
  · simp [Function.update_eq_self]
  · cases M.instruction c.state (c.tape c.head) <;> simp [Function.update_eq_self]

lemma command_valid (M : Machine) (hM : M.WellFormed) (q a : ℕ)
    (hq : q ≤ M.states) (ha : a < M.alphabet) :
    (M.command q a).1 ≤ M.states ∧ (M.command q a).2.1 < M.alphabet := by
  unfold command
  split_ifs with h
  · exact ⟨hq, ha⟩
  · cases hc : M.instruction q a with
    | none => simp [ha]
    | some r =>
      have hr := hM.2.2 q a r (lt_of_le_of_ne hq (by tauto)) ha hc
      exact ⟨hr.1.le, hr.2⟩

lemma initial_admissible (M : Machine) (hM : M.WellFormed) (w : List ℕ)
    (hw : M.ValidInput w) : M.Admissible (M.initial w) := by
  refine ⟨hM.1.le, ?_⟩
  intro i
  dsimp [initial]
  split_ifs
  · cases h : w[i.toNat]? with
    | none => simp [alphabet]
    | some a => exact hw a (List.mem_of_getElem? h)
  · simp [alphabet]

lemma step_admissible (M : Machine) (hM : M.WellFormed) (c : Configuration)
    (hc : M.Admissible c) : M.Admissible (M.step c) := by
  rw [step_eq_command]
  have hr := command_valid M hM c.state (c.tape c.head) hc.1 (hc.2 c.head)
  refine ⟨hr.1, ?_⟩
  intro i
  dsimp
  by_cases hi : i = c.head
  · subst i; simpa using hr.2
  · simpa [Function.update_of_ne hi] using hc.2 i

lemma run_zero (M : Machine) (w : List ℕ) : M.run w 0 = M.initial w := rfl

lemma run_succ (M : Machine) (w : List ℕ) (n : ℕ) :
    M.run w (n + 1) = M.step (M.run w n) :=
  Function.iterate_succ_apply' _ _ _

lemma run_admissible (M : Machine) (hM : M.WellFormed) (w : List ℕ)
    (hw : M.ValidInput w) (n : ℕ) : M.Admissible (M.run w n) := by
  induction n with
  | zero => exact initial_admissible M hM w hw
  | succ n ih => rw [run_succ]; exact step_admissible M hM _ ih

def Window (N n : ℕ) (c : Configuration) : Prop :=
  -(n : ℤ) ≤ c.head ∧ c.head ≤ n ∧
    ∀ i : ℤ, (i < -(n : ℤ) ∨ (N : ℤ) + n ≤ i) → c.tape i = 0

lemma initial_window (M : Machine) (w : List ℕ) : Window w.length 0 (M.initial w) := by
  refine ⟨by simp [initial], by simp [initial], ?_⟩
  intro i hi
  dsimp [initial]
  by_cases h : 0 ≤ i
  · rw [ite_eq_left h, List.getElem?_eq_none (by omega)]
    rfl
  · simp [h]

lemma step_window (M : Machine) (N n : ℕ) (c : Configuration)
    (hc : Window N n c) : Window N (n + 1) (M.step c) := by
  rw [step_eq_command]
  have hd := (M.command c.state (c.tape c.head)).2.2.isLt
  rcases hc with ⟨hl, hu, ht⟩
  refine ⟨?_, ?_, ?_⟩
  · dsimp; omega
  · dsimp; omega
  · intro i hi
    have hi' : i ≠ c.head := by omega
    have hblank := ht i (by omega)
    simpa [Function.update_of_ne hi'] using hblank

lemma run_window (M : Machine) (w : List ℕ) (n : ℕ) :
    Window w.length n (M.run w n) := by
  induction n with
  | zero => exact initial_window M w
  | succ n ih => rw [run_succ]; exact step_window M w.length n _ ih

def leftDigits (c : Configuration) (j : ℕ) : ℕ := 2 * c.tape (c.head - (j + 1))
def rightDigits (c : Configuration) (j : ℕ) : ℕ := 2 * c.tape (c.head + j)

lemma leftDigits_padded (N n : ℕ) (c : Configuration) (hc : Window N n c)
    (j : ℕ) (hj : Scales.K N n ≤ j) : leftDigits c j = 0 := by
  unfold leftDigits
  have hh := hc.2.1
  rw [hc.2.2 _ (Or.inl (by dsimp [Scales.K] at hj; omega))]

lemma rightDigits_padded (N n : ℕ) (c : Configuration) (hc : Window N n c)
    (j : ℕ) (hj : Scales.K N n ≤ j) : rightDigits c j = 0 := by
  unfold rightDigits
  have hh := hc.1
  rw [hc.2.2 _ (Or.inr (by dsimp [Scales.K] at hj; omega))]

def base (M : Machine) : ℕ := 2 * (1 + max (M.states + 1) M.alphabet)

lemma base_ge_four (M : Machine) : 4 ≤ M.base := by
  have h := le_max_left (M.states + 1) M.alphabet
  dsimp [base, states] at *
  omega

lemma state_digit_bound (M : Machine) (q : ℕ) (hq : q ≤ M.states) :
    2 * q + 2 ≤ M.base := by
  have h := le_max_left (M.states + 1) M.alphabet
  dsimp [base]
  omega

lemma symbol_digit_bound (M : Machine) (a : ℕ) (ha : a < M.alphabet) :
    2 * a + 2 ≤ M.base := by
  have h := le_max_right (M.states + 1) M.alphabet
  dsimp [base]
  omega

end Machine
end AlternatingNS

namespace AlternatingNS
namespace Encoding

def digits (K : ℕ) (f : ℕ → ℕ) : List ℕ := List.ofFn (fun i : Fin K => f i)

noncomputable def streamCode (b K : ℕ) (f : ℕ → ℕ) : ℝ := code b (digits K f)

lemma digits_length (K : ℕ) (f : ℕ → ℕ) : (digits K f).length = K := by
  simp [digits]

lemma digits_succ (K : ℕ) (f : ℕ → ℕ) :
    digits (K + 1) f = f 0 :: digits K (fun j => f (j + 1)) :=
  List.ofFn_succ

lemma streamCode_succ (b K : ℕ) (f : ℕ → ℕ) :
    streamCode b (K + 1) f = ((f 0 : ℝ) + streamCode b K (fun j => f (j + 1))) / b := by
  simp only [streamCode, digits_succ, code]

lemma streamCode_congr (b K : ℕ) (f g : ℕ → ℕ) (h : ∀ j < K, f j = g j) :
    streamCode b K f = streamCode b K g := by
  have hl : digits K f = digits K g :=
    congrArg List.ofFn (funext (fun j : Fin K => h j j.isLt))
  exact congrArg (code b) hl

lemma streamCode_extend_one (b K : ℕ) (hb : 0 < b) (f : ℕ → ℕ) (hK : f K = 0) :
    streamCode b (K + 1) f = streamCode b K f := by
  unfold streamCode digits
  rw [List.ofFn_succ', List.concat_eq_append]
  change code b (List.ofFn (fun i : Fin K => f i) ++ [f K]) = _
  rw [code_append b hb]
  simp [hK, code]

lemma streamCode_padding (b K L : ℕ) (hb : 0 < b) (hKL : K ≤ L) (f : ℕ → ℕ)
    (hf : ∀ j, K ≤ j → f j = 0) : streamCode b L f = streamCode b K f := by
  induction L, hKL using Nat.le_induction with
  | base => rfl
  | succ L hL ih => rw [streamCode_extend_one b L hb f (hf L hL), ih]

lemma streamCode_pop (b K L : ℕ) (hb : 0 < b) (hKL : K ≤ L + 1)
    (f : ℕ → ℕ) (hf : ∀ j, K ≤ j → f j = 0) :
    streamCode b L (fun j => f (j + 1)) = (b : ℝ) * streamCode b K f - f 0 := by
  have h := streamCode_succ b L f
  rw [streamCode_padding b K (L + 1) hb hKL f hf] at h
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  apply (eq_div_iff hb').1 at h
  linarith

end Encoding

namespace Machine

noncomputable def leftCode (b N n : ℕ) (c : Configuration) : ℝ :=
  Encoding.streamCode b (Scales.K N n) (leftDigits c)

noncomputable def rightCode (b N n : ℕ) (c : Configuration) : ℝ :=
  Encoding.streamCode b (Scales.K N n) (rightDigits c)

def recordedDigits (M : Machine) (w : List ℕ) (n : ℕ) : List ℕ :=
  let c := M.run w n
  2 * c.state :: (Encoding.digits (Scales.K w.length n) (leftDigits c) ++
    Encoding.digits (Scales.K w.length n) (rightDigits c))

noncomputable def recordedBlock (M : Machine) (w : List ℕ) (n : ℕ) : ℝ :=
  Encoding.code M.base (M.recordedDigits w n)

lemma recordedDigits_bound (M : Machine) (hM : M.WellFormed) (w : List ℕ)
    (hw : M.ValidInput w) (n : ℕ) :
    ∀ d ∈ M.recordedDigits w n, d + 2 ≤ M.base := by
  have hc := run_admissible M hM w hw n
  intro d hd
  simp only [recordedDigits, Encoding.digits, List.mem_cons, List.mem_append,
    List.mem_ofFn] at hd
  rcases hd with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact state_digit_bound M _ hc.1
  · exact symbol_digit_bound M _ (hc.2 _)
  · exact symbol_digit_bound M _ (hc.2 _)

lemma recordedBlock_mem (M : Machine) (hM : M.WellFormed) (w : List ℕ)
    (hw : M.ValidInput w) (n : ℕ) :
    M.recordedBlock w n ∈ Set.Icc (0 : ℝ) (Encoding.tailMax M.base) :=
  ⟨Encoding.code_nonneg _ _, Encoding.code_le_tailMax _ (by have := base_ge_four M; omega)
    _ (recordedDigits_bound M hM w hw n)⟩

lemma recordedBlock_formula (M : Machine) (w : List ℕ) (n : ℕ) :
    M.recordedBlock w n =
      ((2 * (M.run w n).state : ℕ) + leftCode M.base w.length n (M.run w n) +
        ((M.base : ℝ) ^ Scales.K w.length n)⁻¹ *
          rightCode M.base w.length n (M.run w n)) / M.base := by
  unfold recordedBlock recordedDigits leftCode rightCode Encoding.streamCode
  rw [Encoding.configuration_block _ _ (by have := base_ge_four M; omega),
    Encoding.digits_length]

lemma recordedBlock_integral (M : Machine) (w : List ℕ) (n : ℕ) :
    ∃ a : ℤ, (M.base : ℝ) ^ (1 + 2 * Scales.K w.length n) * M.recordedBlock w n = a := by
  obtain ⟨a, ha⟩ := Encoding.code_denominator M.base (by have := base_ge_four M; omega)
    (M.recordedDigits w n)
  refine ⟨a, ?_⟩
  have hlen : (M.recordedDigits w n).length = 1 + 2 * Scales.K w.length n := by
    simp only [recordedDigits, List.length_cons, List.length_append, Encoding.digits_length]
    omega
  simpa only [recordedBlock, hlen, Int.cast_natCast] using ha

lemma read_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w)
    (n : ℕ) :
    let b := M.base
    let s := Scales.s w.length n
    let K := Scales.K w.length n
    let D := Encoding.donor b w.length (M.recordedBlock w) n
    Profiles.decoder b ((b : ℝ) ^ s * D) = M.recordedBlock w n ∧
    Profiles.decoder b ((b : ℝ) ^ (s + 1 + K) * D) = rightCode b w.length n (M.run w n) ∧
    Profiles.decoder b ((b : ℝ) ^ (s + 1) * D) - ((b : ℝ) ^ K)⁻¹ *
      Profiles.decoder b ((b : ℝ) ^ (s + 1 + K) * D) = leftCode b w.length n (M.run w n) :=
  Encoding.read_donor_configuration M.base w.length n (by have := base_ge_four M; omega)
    (fun j => 2 * (M.run w j).state)
    (fun j => Encoding.digits (Scales.K w.length j) (leftDigits (M.run w j)))
    (fun j => Encoding.digits (Scales.K w.length j) (rightDigits (M.run w j)))
    (fun j => Encoding.digits_length _ _) (fun j => Encoding.digits_length _ _)
    (recordedDigits_bound M hM w hw)

end Machine
end AlternatingNS

namespace AlternatingNS
namespace Machine

def execute (c : Configuration) (r : Rule) : Configuration where
  state := r.1
  head := c.head + ((r.2.2.val : ℤ) - 1)
  tape := Function.update c.tape c.head r.2.1

lemma step_execute (M : Machine) (c : Configuration) :
    M.step c = execute c (M.command c.state (c.tape c.head)) := step_eq_command M c

lemma execute_right (c : Configuration) (r : Rule) (hd : r.2.2 = 2) :
    leftDigits (execute c r) 0 = 2 * r.2.1 ∧
    (∀ j, leftDigits (execute c r) (j + 1) = leftDigits c j) ∧
    (∀ j, rightDigits (execute c r) j = rightDigits c (j + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [leftDigits, execute, hd]
  · intro j
    have hi : c.head - ((j : ℤ) + 1) ≠ c.head := by omega
    have he : c.head + 1 - ((j : ℤ) + 1 + 1) = c.head - ((j : ℤ) + 1) := by omega
    simp [leftDigits, execute, hd, he, Function.update_of_ne hi]
  · intro j
    have hi : c.head + ((j : ℤ) + 1) ≠ c.head := by omega
    have he : c.head + 1 + (j : ℤ) = c.head + ((j : ℤ) + 1) := by omega
    simp [rightDigits, execute, hd, he, Function.update_of_ne hi]

lemma execute_stay (c : Configuration) (r : Rule) (hd : r.2.2 = 1) :
    (∀ j, leftDigits (execute c r) j = leftDigits c j) ∧
    rightDigits (execute c r) 0 = 2 * r.2.1 ∧
    (∀ j, rightDigits (execute c r) (j + 1) = rightDigits c (j + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have hi : c.head - ((j : ℤ) + 1) ≠ c.head := by omega
    simp [leftDigits, execute, hd, Function.update_of_ne hi]
  · simp [rightDigits, execute, hd]
  · intro j
    have hi : c.head + ((j : ℤ) + 1) ≠ c.head := by omega
    simp [rightDigits, execute, hd, Function.update_of_ne hi]

lemma execute_left (c : Configuration) (r : Rule) (hd : r.2.2 = 0) :
    (∀ j, leftDigits (execute c r) j = leftDigits c (j + 1)) ∧
    rightDigits (execute c r) 0 = leftDigits c 0 ∧
    rightDigits (execute c r) 1 = 2 * r.2.1 ∧
    (∀ j, rightDigits (execute c r) (j + 1 + 1) = rightDigits c (j + 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    have hi : c.head - ((j : ℤ) + 1 + 1) ≠ c.head := by omega
    have he : c.head + (-1) - ((j : ℤ) + 1) = c.head - ((j : ℤ) + 1 + 1) := by omega
    simp [leftDigits, execute, hd, he, Function.update_of_ne hi]
  · simp [leftDigits, rightDigits, execute, hd, sub_eq_add_neg]
  · simp [rightDigits, execute, hd]
  · intro j
    have hi : c.head + ((j : ℤ) + 1) ≠ c.head := by omega
    have he : c.head + (-1) + ((j : ℤ) + 1 + 1) = c.head + ((j : ℤ) + 1) := by omega
    simp [rightDigits, execute, hd, he, Function.update_of_ne hi]

lemma code_execute_right (b N n : ℕ) (hb : 0 < b) (c : Configuration)
    (hc : Window N n c) (r : Rule) (hd : r.2.2 = 2) :
    leftCode b N (n + 1) (execute c r) = ((2 * r.2.1 : ℕ) + leftCode b N n c) / b ∧
    rightCode b N (n + 1) (execute c r) =
      (b : ℝ) * rightCode b N n c - rightDigits c 0 := by
  obtain ⟨h₀, h₁, h₂⟩ := execute_right c r hd
  have hK : Scales.K N (n + 1) = (Scales.K N n + 1) + 1 := by dsimp [Scales.K]; omega
  constructor
  · unfold leftCode
    rw [hK, Encoding.streamCode_succ, h₀]
    have he : (fun j => leftDigits (execute c r) (j + 1)) = leftDigits c := funext h₁
    rw [he, Encoding.streamCode_padding b (Scales.K N n) (Scales.K N n + 1) hb
      (by omega) _ (leftDigits_padded N n c hc)]
  · unfold rightCode
    rw [show rightDigits (execute c r) = (fun j => rightDigits c (j + 1)) from funext h₂]
    exact Encoding.streamCode_pop b (Scales.K N n) _ hb (by omega) _
      (rightDigits_padded N n c hc)

lemma code_execute_stay (b N n : ℕ) (hb : 0 < b) (c : Configuration)
    (hc : Window N n c) (r : Rule) (hd : r.2.2 = 1) :
    leftCode b N (n + 1) (execute c r) = leftCode b N n c ∧
    rightCode b N (n + 1) (execute c r) =
      ((2 * r.2.1 : ℕ) + ((b : ℝ) * rightCode b N n c - rightDigits c 0)) / b := by
  obtain ⟨h₀, h₁, h₂⟩ := execute_stay c r hd
  have hK : Scales.K N (n + 1) = (Scales.K N n + 1) + 1 := by dsimp [Scales.K]; omega
  constructor
  · unfold leftCode
    rw [show leftDigits (execute c r) = leftDigits c from funext h₀]
    exact Encoding.streamCode_padding b (Scales.K N n) _ hb (by omega) _
      (leftDigits_padded N n c hc)
  · unfold rightCode
    rw [hK, Encoding.streamCode_succ, h₁, funext h₂]
    rw [Encoding.streamCode_pop b (Scales.K N n) (Scales.K N n + 1) hb (by omega) _
      (rightDigits_padded N n c hc)]

lemma code_execute_left (b N n : ℕ) (hb : 0 < b) (c : Configuration)
    (hc : Window N n c) (r : Rule) (hd : r.2.2 = 0) :
    leftCode b N (n + 1) (execute c r) =
      (b : ℝ) * leftCode b N n c - leftDigits c 0 ∧
    rightCode b N (n + 1) (execute c r) =
      ((leftDigits c 0 : ℝ) + ((2 * r.2.1 : ℕ) +
        ((b : ℝ) * rightCode b N n c - rightDigits c 0)) / b) / b := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := execute_left c r hd
  have hK : Scales.K N (n + 1) = (Scales.K N n + 1) + 1 := by dsimp [Scales.K]; omega
  constructor
  · unfold leftCode
    rw [funext h₀]
    exact Encoding.streamCode_pop b (Scales.K N n) _ hb (by omega) _
      (leftDigits_padded N n c hc)
  · unfold rightCode
    rw [hK, Encoding.streamCode_succ, Encoding.streamCode_succ]
    simp only [h₁, zero_add, h₂]
    rw [funext h₃, Encoding.streamCode_pop b (Scales.K N n) (Scales.K N n) hb (by omega) _
      (rightDigits_padded N n c hc)]

end Machine
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/MachineProfiles.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Profiles

noncomputable def selector (b a : ℕ) (v : ℝ) : ℝ :=
  letI := twoAtLeastTwo
  letI := eightAtLeastTwo
  Real.smoothTransition (8 * ((b : ℝ) * v - 2 * a) + 2) *
    Real.smoothTransition (8 * (2 * a + 1 - (b : ℝ) * v) + 2)

lemma selector_smooth (b a : ℕ) : ContDiff ℝ ∞ (selector b a) := by
  unfold selector
  fun_prop

lemma selector_nonneg (b a : ℕ) (v : ℝ) : 0 ≤ selector b a v :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma selector_le_one (b a : ℕ) (v : ℝ) : selector b a v ≤ 1 := by
  exact (mul_le_of_le_one_left (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)

lemma selector_one (b a : ℕ) (v : ℝ)
    (h₀ : 2 * (a : ℝ) - 1 / 8 ≤ b * v) (h₁ : (b : ℝ) * v ≤ 2 * a + 9 / 8) :
    selector b a v = 1 := by
  rw [selector, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith)]
  norm_num

lemma selector_zero_left (b a : ℕ) (v : ℝ) (h : (b : ℝ) * v ≤ 2 * a - 1 / 4) :
    selector b a v = 0 := by
  rw [selector, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

lemma selector_zero_right (b a : ℕ) (v : ℝ) (h : 2 * (a : ℝ) + 5 / 4 ≤ b * v) :
    selector b a v = 0 := by
  rw [selector, Real.smoothTransition.zero_of_nonpos (by linarith :
    8 * (2 * (a : ℝ) + 1 - b * v) + 2 ≤ 0), mul_zero]

lemma selector_support_bound (b a : ℕ) (v : ℝ) (h : selector b a v ≠ 0) :
    2 * (a : ℝ) - 1 / 4 < b * v ∧ (b : ℝ) * v < 2 * a + 5 / 4 := by
  constructor
  · by_contra hn
    exact h (selector_zero_left b a v (le_of_not_gt hn))
  · by_contra hn
    exact h (selector_zero_right b a v (le_of_not_gt hn))

lemma selector_support_disjoint (b a q : ℕ) (haq : a ≠ q) :
    Disjoint (Function.support (selector b a)) (Function.support (selector b q)) := by
  rw [Set.disjoint_left]
  intro v ha hq
  obtain ⟨ha₀, ha₁⟩ := selector_support_bound b a v ha
  obtain ⟨hq₀, hq₁⟩ := selector_support_bound b q v hq
  rcases lt_or_gt_of_ne haq with h | h
  · have h' : (a : ℝ) + 1 ≤ q := by exact_mod_cast h
    linarith
  · have h' : (q : ℝ) + 1 ≤ a := by exact_mod_cast h
    linarith

lemma selector_on_cell (b a q : ℕ) (v : ℝ)
    (h₀ : 2 * (q : ℝ) ≤ b * v) (h₁ : (b : ℝ) * v ≤ 2 * q + 1) :
    selector b a v = if a = q then 1 else 0 := by
  split_ifs with h
  · subst a
    apply selector_one <;> linarith
  · rcases lt_or_gt_of_ne h with ha | ha
    · have h' : (a : ℝ) + 1 ≤ q := by exact_mod_cast ha
      apply selector_zero_right
      linarith
    · have h' : (q : ℝ) + 1 ≤ a := by exact_mod_cast ha
      apply selector_zero_left
      linarith

lemma selector_code (b a q : ℕ) (hb : 2 ≤ b) (L : List ℕ)
    (hL : ∀ d ∈ L, d + 2 ≤ b) :
    selector b a (Encoding.code b (2 * q :: L)) = if a = q then 1 else 0 := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have h := Encoding.digit_interval b (2 * q) hb L hL
  have h₀ := (div_le_iff₀ hb').1 h.1
  have h₁ := (le_div_iff₀ hb').1 h.2
  push_cast at h₀ h₁
  apply selector_on_cell <;> nlinarith

lemma selector_streamCode (b a q K : ℕ) (hb : 2 ≤ b) (hK : 0 < K) (f : ℕ → ℕ)
    (hf : ∀ j, f j + 2 ≤ b) (h₀ : f 0 = 2 * q) :
    selector b a (Encoding.streamCode b K f) = if a = q then 1 else 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hK)
  rw [Encoding.streamCode, Encoding.digits_succ, h₀]
  apply selector_code b a q hb
  intro d hd
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hd
  exact hf _

end Profiles

namespace Machine

lemma selector_recordedBlock (M : Machine) (hM : M.WellFormed) (w : List ℕ)
    (hw : M.ValidInput w) (n q : ℕ) :
    Profiles.selector M.base q (M.recordedBlock w n) =
      if q = (M.run w n).state then 1 else 0 := by
  apply Profiles.selector_code _ _ _ (by have := base_ge_four M; omega)
  intro d hd
  exact recordedDigits_bound M hM w hw n d (List.mem_cons_of_mem _ hd)

lemma selector_leftCode (M : Machine) (c : Configuration) (hc : M.Admissible c) (N n a : ℕ) :
    Profiles.selector M.base a (leftCode M.base N n c) =
      if a = c.tape (c.head - 1) then 1 else 0 := by
  apply Profiles.selector_streamCode _ _ _ _ (by have := base_ge_four M; omega)
    (by dsimp [Scales.K]; omega)
  · intro j
    exact symbol_digit_bound M _ (hc.2 _)
  · simp [leftDigits]

lemma selector_rightCode (M : Machine) (c : Configuration) (hc : M.Admissible c) (N n a : ℕ) :
    Profiles.selector M.base a (rightCode M.base N n c) =
      if a = c.tape c.head then 1 else 0 := by
  apply Profiles.selector_streamCode _ _ _ _ (by have := base_ge_four M; omega)
    (by dsimp [Scales.K]; omega)
  · intro j
    exact symbol_digit_bound M _ (hc.2 _)
  · simp [rightDigits]

end Machine
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/LocalRules.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace LocalRule

noncomputable def readC (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  Profiles.decoder M.base ((M.base : ℝ) ^ Scales.s N n * D)
noncomputable def readB (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  Profiles.decoder M.base ((M.base : ℝ) ^ (Scales.s N n + 1 + Scales.K N n) * D)
noncomputable def readA (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  Profiles.decoder M.base ((M.base : ℝ) ^ (Scales.s N n + 1) * D) -
    ((M.base : ℝ) ^ Scales.K N n)⁻¹ * readB M N n D

noncomputable def updateLeft (b _a l : ℕ) (r : Rule) (A _B : ℝ) : ℝ :=
  letI := neZeroThree
  letI := twoAtLeastTwo
  if r.2.2 = 0 then (b : ℝ) * A - 2 * l
  else if r.2.2 = 1 then A else ((2 * r.2.1 : ℕ) + A) / b

noncomputable def updateRight (b a l : ℕ) (r : Rule) (_A B : ℝ) : ℝ :=
  letI := neZeroThree
  letI := twoAtLeastTwo
  let R := (b : ℝ) * B - 2 * a
  if r.2.2 = 0 then ((2 * l : ℕ) + ((2 * r.2.1 : ℕ) + R) / b) / b
  else if r.2.2 = 1 then ((2 * r.2.1 : ℕ) + R) / b else R

noncomputable def branchNumerator (b K a l : ℕ) (r : Rule) (A B : ℝ) : ℝ :=
  (2 * r.1 : ℕ) + updateLeft b a l r A B +
    ((b : ℝ) ^ K)⁻¹ * updateRight b a l r A B

noncomputable def branch (M : Machine) (N n q a : ℕ) (A B : ℝ) : ℝ :=
  letI := neZeroThree
  let r := M.command q a
  if r.2.2 = 0 then ∑ l ∈ Finset.range M.alphabet,
    Profiles.selector M.base l A * branchNumerator M.base (Scales.K N (n + 1)) a l r A B
  else branchNumerator M.base (Scales.K N (n + 1)) a 0 r A B

noncomputable def write (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  Scales.ε M.base N (n + 1) / M.base *
    ∑ q ∈ Finset.range (M.states + 1), ∑ a ∈ Finset.range M.alphabet,
      Profiles.selector M.base q (readC M N n D) *
        Profiles.selector M.base a (readB M N n D) *
          branch M N n q a (readA M N n D) (readB M N n D)

noncomputable def haltWeight (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (M.states + 1),
    if q = M.states ∨ q ∈ M.haltingStates then Profiles.selector M.base q (readC M N n D) else 0

noncomputable def signal (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  letI := twoAtLeastTwo
  Scales.ε M.base N n - Scales.ε M.base N (n + 1) +
    2 * Scales.ε M.base N (n + 1) * haltWeight M N n D

lemma readC_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (readC M N n) := by
  exact (Profiles.decoder_smooth M.base (by have := M.base_ge_four; omega)).comp
    (contDiff_const.mul contDiff_id)

lemma readB_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (readB M N n) := by
  exact (Profiles.decoder_smooth M.base (by have := M.base_ge_four; omega)).comp
    (contDiff_const.mul contDiff_id)

lemma readA_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (readA M N n) := by
  exact ((Profiles.decoder_smooth M.base (by have := M.base_ge_four; omega)).comp
    (contDiff_const.mul contDiff_id)).sub (contDiff_const.mul (readB_smooth M N n))

lemma branchNumerator_smooth (b K a l : ℕ) (r : Rule) (A B : ℝ → ℝ)
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (fun D => branchNumerator b K a l r (A D) (B D)) := by
  unfold branchNumerator updateLeft updateRight
  split_ifs <;> fun_prop

lemma branch_smooth (M : Machine) (N n q a : ℕ) (A B : ℝ → ℝ)
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (fun D => branch M N n q a (A D) (B D)) := by
  unfold branch
  dsimp only
  split_ifs
  · apply ContDiff.sum
    intro l _
    exact ((Profiles.selector_smooth M.base l).comp hA).mul
      (branchNumerator_smooth _ _ _ _ _ _ _ hA hB)
  · exact branchNumerator_smooth _ _ _ _ _ _ _ hA hB

lemma write_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (write M N n) := by
  unfold write
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro q _
  apply ContDiff.sum
  intro a _
  exact (((Profiles.selector_smooth M.base q).comp (readC_smooth M N n)).mul
    ((Profiles.selector_smooth M.base a).comp (readB_smooth M N n))).mul
    (branch_smooth M N n q a _ _ (readA_smooth M N n) (readB_smooth M N n))

lemma haltWeight_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (haltWeight M N n) := by
  unfold haltWeight
  apply ContDiff.sum
  intro q _
  split_ifs
  · exact (Profiles.selector_smooth M.base q).comp (readC_smooth M N n)
  · exact contDiff_const

lemma signal_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (signal M N n) := by
  exact contDiff_const.add (contDiff_const.mul (haltWeight_smooth M N n))

lemma readC_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) (n : ℕ) :
    readC M w.length n (Encoding.donor M.base w.length (M.recordedBlock w) n) =
      M.recordedBlock w n := (M.read_run hM w hw n).1

lemma readB_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) (n : ℕ) :
    readB M w.length n (Encoding.donor M.base w.length (M.recordedBlock w) n) =
      Machine.rightCode M.base w.length n (M.run w n) := (M.read_run hM w hw n).2.1

lemma readA_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) (n : ℕ) :
    readA M w.length n (Encoding.donor M.base w.length (M.recordedBlock w) n) =
      Machine.leftCode M.base w.length n (M.run w n) := (M.read_run hM w hw n).2.2

end LocalRule
end AlternatingNS

namespace AlternatingNS
namespace LocalRule

lemma branchNumerator_execute (b N n : ℕ) (hb : 0 < b) (c : Machine.Configuration)
    (hc : Machine.Window N n c) (r : Rule) :
    branchNumerator b (Scales.K N (n + 1)) (c.tape c.head) (c.tape (c.head - 1)) r
      (Machine.leftCode b N n c) (Machine.rightCode b N n c) =
    (2 * r.1 : ℕ) + Machine.leftCode b N (n + 1) (Machine.execute c r) +
      ((b : ℝ) ^ Scales.K N (n + 1))⁻¹ * Machine.rightCode b N (n + 1) (Machine.execute c r) := by
  by_cases h₀ : r.2.2 = 0
  · obtain ⟨hL, hR⟩ := Machine.code_execute_left b N n hb c hc r h₀
    rw [hL, hR]
    simp [branchNumerator, updateLeft, updateRight, h₀, Machine.leftDigits, Machine.rightDigits]
  · by_cases h₁ : r.2.2 = 1
    · obtain ⟨hL, hR⟩ := Machine.code_execute_stay b N n hb c hc r h₁
      rw [hL, hR]
      simp [branchNumerator, updateLeft, updateRight, h₁, Machine.rightDigits]
    · have h₂ : r.2.2 = 2 := by omega
      obtain ⟨hL, hR⟩ := Machine.code_execute_right b N n hb c hc r h₂
      rw [hL, hR]
      simp [branchNumerator, updateLeft, updateRight, h₀, h₁, Machine.rightDigits]

lemma branch_on_configuration (M : Machine) (N n : ℕ) (c : Machine.Configuration)
    (ha : M.Admissible c) (hw : Machine.Window N n c) :
    branch M N n c.state (c.tape c.head)
      (Machine.leftCode M.base N n c) (Machine.rightCode M.base N n c) =
    (2 * (M.step c).state : ℕ) + Machine.leftCode M.base N (n + 1) (M.step c) +
      ((M.base : ℝ) ^ Scales.K N (n + 1))⁻¹ * Machine.rightCode M.base N (n + 1) (M.step c) := by
  have hb : 0 < M.base := by have := M.base_ge_four; omega
  have hnum := branchNumerator_execute M.base N n hb c hw (M.command c.state (c.tape c.head))
  rw [Machine.step_execute]
  unfold branch
  dsimp only
  split_ifs with h₀
  · rw [Finset.sum_eq_single_of_mem (c.tape (c.head - 1)) (Finset.mem_range.2 (ha.2 _))]
    · rw [Machine.selector_leftCode M c ha N n, ite_eq_left rfl, one_mul]
      exact hnum
    · intro l _ hl
      simp [Machine.selector_leftCode M c ha N n l, hl]
  · simpa only [branchNumerator, updateLeft, updateRight, h₀, ite_false, Machine.execute] using hnum

lemma write_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) (n : ℕ) :
    write M w.length n (Encoding.donor M.base w.length (M.recordedBlock w) n) =
      Scales.ε M.base w.length (n + 1) * M.recordedBlock w (n + 1) := by
  have hc := M.run_admissible hM w hw n
  have hq : (M.run w n).state ∈ Finset.range (M.states + 1) :=
    Finset.mem_range.2 (Nat.lt_succ_of_le hc.1)
  have ha : (M.run w n).tape (M.run w n).head ∈ Finset.range M.alphabet :=
    Finset.mem_range.2 (hc.2 _)
  unfold write
  rw [readC_run M hM w hw n, readB_run M hM w hw n, readA_run M hM w hw n]
  simp only [Machine.selector_recordedBlock M hM w hw n,
    Machine.selector_rightCode M (M.run w n) hc w.length n,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', ite_eq_left hq, ite_eq_left ha]
  rw [branch_on_configuration M w.length n (M.run w n) hc (M.run_window w n)]
  rw [Machine.recordedBlock_formula, Machine.run_succ]
  ring

lemma haltWeight_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) (n : ℕ) :
    haltWeight M w.length n (Encoding.donor M.base w.length (M.recordedBlock w) n) =
      if M.isHalting (M.run w n) then 1 else 0 := by
  have hc := (M.run_admissible hM w hw n).1
  unfold haltWeight
  rw [readC_run M hM w hw n,
    Finset.sum_eq_single_of_mem (M.run w n).state (Finset.mem_range.2 (by omega))]
  · simp [Machine.selector_recordedBlock M hM w hw n, Machine.isHalting]
  · intro q _ hq
    simp [Machine.selector_recordedBlock M hM w hw n q, hq]

lemma signal_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) (n : ℕ) :
    signal M w.length n (Encoding.donor M.base w.length (M.recordedBlock w) n) =
      Detector.increment M.base w.length (fun j => M.isHalting (M.run w j)) n := by
  rw [signal, haltWeight_run M hM w hw n]
  simp only [Detector.increment, mul_ite, mul_one, mul_zero]

end LocalRule
end AlternatingNS

end OAI


