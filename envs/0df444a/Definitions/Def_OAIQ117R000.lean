-- Prove2me | Definitions.Def_OAIQ117R000
-- name    : OAIQ117R000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:04:30.60313+00:00
-- url     : https://prove2.me/theorems/63a08c8c-055d-4d22-9e48-7a916dea0928
-- title:
--   Definitions bundle OAIQ117R000 of the split of OpenAI, Randomized quasipolynomial-time mean-payoff games
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.randomized_quasipolynomial_mean_payoff`, carved from OpenAI's openai/math development (OpenAI, *Randomized quasipolynomial-time mean-payoff games*, OpenAI Math Release, September 25, 2026, result family 104, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1407 declarations of OpenAI's Lean: 743 definitions, 37 inductive types or structures, 9 instances and 618 theorems. The definitions and types are `OAI.MeanPayoff.AdmissibleSub`, `OAI.MeanPayoff.AdmissibleSuper`, `OAI.MeanPayoff.Alternative`, `OAI.MeanPayoff.ArithmeticForest.addTime`, `OAI.MeanPayoff.ArithmeticForest.addWord`, `OAI.MeanPayoff.ArithmeticForest.boxTime`, `OAI.MeanPayoff.ArithmeticForest.flow`, `OAI.MeanPayoff.ArithmeticForest.placeA`, `OAI.MeanPayoff.ArithmeticForest.placeAdd`, `OAI.MeanPayoff.ArithmeticForest.placeB`, `OAI.MeanPayoff.ArithmeticForest.placeBox`, `OAI.MeanPayoff.ArithmeticForest.program`, `OAI.MeanPayoff.ArithmeticForest.store0`, `OAI.MeanPayoff.ArithmeticForest.store1`, `OAI.MeanPayoff.ArithmeticForest.store2`, `OAI.MeanPayoff.ArithmeticForest.store3`, `OAI.MeanPayoff.ArithmeticForest.store4`, `OAI.MeanPayoff.ArithmeticForest.unboxTime`, `OAI.MeanPayoff.BinaryData.Box.Label`, `OAI.MeanPayoff.BinaryData.Box.cfg`, `OAI.MeanPayoff.BinaryData.Box.enc`, `OAI.MeanPayoff.BinaryData.Box.equiv`, `OAI.MeanPayoff.BinaryData.Box.program`, `OAI.MeanPayoff.BinaryData.Box.stopped`, `OAI.MeanPayoff.BinaryData.Copy.Label`, `OAI.MeanPayoff.BinaryData.Copy.cfg`, `OAI.MeanPayoff.BinaryData.Copy.enc`, `OAI.MeanPayoff.BinaryData.Copy.equiv`, `OAI.MeanPayoff.BinaryData.Copy.program`, `OAI.MeanPayoff.BinaryData.Copy.stopped`, `OAI.MeanPayoff.BinaryData.Data`, `OAI.MeanPayoff.BinaryData.Take.Label`, `OAI.MeanPayoff.BinaryData.Take.cfg`, `OAI.MeanPayoff.BinaryData.Take.enc`, `OAI.MeanPayoff.BinaryData.Take.equiv`, `OAI.MeanPayoff.BinaryData.Take.program`, `OAI.MeanPayoff.BinaryData.Take.stopped`, `OAI.MeanPayoff.BinaryData.Unbox.Label`, `OAI.MeanPayoff.BinaryData.Unbox.cfg`, `OAI.MeanPayoff.BinaryData.Unbox.enc` and 740 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MeanPayoff_Alternatives`, `MeanPayoff_ArenaParsing`, `MeanPayoff_Arithmetic`, `MeanPayoff_ArithmeticBounds`, `MeanPayoff_ArithmeticDevices`, `MeanPayoff_BatchDevices`, `MeanPayoff_BinaryData`, `MeanPayoff_BitDepth`, `MeanPayoff_BitProgram`, `MeanPayoff_Budgets`, `MeanPayoff_Comparison`, `MeanPayoff_CountedRecursion`, `MeanPayoff_CountedTraversal`, `MeanPayoff_Counters`, `MeanPayoff_Decoding`, `MeanPayoff_Deviation`, `MeanPayoff_Drift`, `MeanPayoff_Driver`, `MeanPayoff_DriverExecution`, `MeanPayoff_EncodedArithmetic`, `MeanPayoff_EncodedPrograms`, `MeanPayoff_FiniteBox`, `MeanPayoff_FiniteIteration`, `MeanPayoff_FiniteSuccess`, `MeanPayoff_FiniteTrees`, `MeanPayoff_InputCode`, `MeanPayoff_InputSize`, `MeanPayoff_Instructions`, `MeanPayoff_LoopDevices`, `MeanPayoff_Normalization`, `MeanPayoff_Online`, `MeanPayoff_OperatorCosts`, `MeanPayoff_OperatorDevices`, `MeanPayoff_ParserCosts`, `MeanPayoff_PolynomialCosts`, `MeanPayoff_Preparation`, `MeanPayoff_RawLabels`, `MeanPayoff_RawSolutions`, `MeanPayoff_Realizer`, `MeanPayoff_Recursion`, `MeanPayoff_Registers`, `MeanPayoff_Sampling`, `MeanPayoff_SignedBits`, `MeanPayoff_Simulation`, `MeanPayoff_SizeBounds`, `MeanPayoff_Sorting`, `MeanPayoff_Stack`, `MeanPayoff_StackMacros`, `MeanPayoff_Traversal`, `MeanPayoff_TreeCopy`, `MeanPayoff_TreeDevices`, `MeanPayoff_VectorDevices`, `MeanPayoff_WordDecoding`, `RandomMean_Control`, `RandomMean_Loop`, `RandomMean_Orientation`, `RandomMean_SizeBounds`, `RandomMean_StateGrowth`.
--
--   **Imports.** It imports the published bundle `Def_RandomizedMeanPayoff`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ117R002`.
-- source:
--   OpenAI, Randomized quasipolynomial-time mean-payoff games, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 104; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Randomized-quasipolynomial-time-mean-payoff-games-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_RandomizedMeanPayoff

section
-- module Solutions.OAIQ117_RM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_FiniteBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff

abbrev Vec (V : Type) := V → ℤ

def shift {V : Type} (p : Vec V) (c : ℤ) : Vec V := fun i => p i + c

def clip {V : Type} (a b p : Vec V) : Vec V :=
  fun i => min (b i) (max (a i) (p i))

def InBox {V : Type} (a b p : Vec V) : Prop := a ≤ p ∧ p ≤ b

def Subsolution {V : Type} (F : Vec V → Vec V) (a b y : Vec V) : Prop :=
  InBox a b y ∧ ∀ i, a i < y i → y i ≤ F y i

def Supersolution {V : Type} (F : Vec V → Vec V) (a b z : Vec V) : Prop :=
  InBox a b z ∧ ∀ i, z i < b i → F z i ≤ z i

structure OperatorLaws {V : Type} (F : Vec V → Vec V) : Prop where
  mono : Monotone F
  translation : ∀ p c, F (shift p c) = shift (F p) c

def transformed (G : Game) (e : Fin G.m) : ℤ := (G.n + 1 : ℤ) * G.weight e + 1

def outgoing (G : Game) (v : Fin G.n) : Finset (Fin G.m) :=
  Finset.univ.filter (fun e => G.tail e = v)

theorem outgoing_nonempty (G : Game) (v : Fin G.n) : (outgoing G v).Nonempty := by
  obtain ⟨e, he⟩ := G.total v
  exact ⟨e, by simp [outgoing, he]⟩

def operator (G : Game) (p : Vec (Fin G.n)) : Vec (Fin G.n) := fun i =>
  if G.maxOwner i then
    (outgoing G i).sup' (outgoing_nonempty G i) (fun e => transformed G e + p (G.head e))
  else
    (outgoing G i).inf' (outgoing_nonempty G i) (fun e => transformed G e + p (G.head e))

theorem operator_laws (G : Game) : OperatorLaws (operator G) := by
  constructor
  · intro p q hpq i
    simp only [operator]
    split
    · apply (Finset.sup'_le_iff _ _).2
      intro e he
      exact le_trans (add_le_add_right (hpq (G.head e)) _)
        (Finset.le_sup' (fun e => transformed G e + q (G.head e)) he)
    · apply (Finset.le_inf'_iff _ _).2
      intro e he
      exact le_trans (Finset.inf'_le (fun e => transformed G e + p (G.head e)) he)
        (add_le_add_right (hpq (G.head e)) _)
  · intro p c
    funext i
    simp only [operator, shift]
    split
    · simpa only [add_assoc] using
        (Finset.sup'_add (outgoing G i)
          (fun e => transformed G e + p (G.head e)) c (outgoing_nonempty G i)).symm
    · obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_inf' (outgoing_nonempty G i)
        (fun e => transformed G e + p (G.head e))
      obtain ⟨f, hf, hfq⟩ := Finset.exists_mem_eq_inf' (outgoing_nonempty G i)
        (fun e => transformed G e + (p (G.head e) + c))
      have hlo := Finset.inf'_le (fun e => transformed G e + p (G.head e)) hf
      have hup := Finset.inf'_le (fun e => transformed G e + (p (G.head e) + c)) he
      rw [heq] at hlo ⊢
      rw [hfq] at hup ⊢
      omega

def boxStep {V : Type} (F : Vec V → Vec V) (a b p : Vec V) : Vec V :=
  clip a b (F p)

theorem boxStep_in_box {V : Type} (F : Vec V → Vec V)
    {a b : Vec V} (hab : a ≤ b) (p : Vec V) : InBox a b (boxStep F a b p) := by
  constructor
  · intro i
    exact le_min (hab i) (le_max_left _ _)
  · intro i; exact min_le_left _ _

theorem boxStep_mono {V : Type} {F : Vec V → Vec V} (hF : Monotone F)
    (a b : Vec V) : Monotone (boxStep F a b) := by
  intro p q hpq i
  exact min_le_min_left _ (max_le_max_left _ (hF hpq i))

theorem fixed_iff_comparisons {V : Type} (F : Vec V → Vec V)
    {a b p : Vec V} (hab : a ≤ b) :
    boxStep F a b p = p ↔ Subsolution F a b p ∧ Supersolution F a b p := by
  constructor
  · intro heq
    have hp := boxStep_in_box F hab p
    rw [heq] at hp
    have hc : ∀ i, min (b i) (max (a i) (F p i)) = p i := congrFun heq
    constructor
    · refine ⟨hp, ?_⟩
      intro i hi
      have := hc i
      omega
    · refine ⟨hp, ?_⟩
      intro i hi
      have := hc i
      omega
  · rintro ⟨hy, hz⟩
    funext i
    have ha : a i ≤ p i := hy.1.1 i
    have hb : p i ≤ b i := hy.1.2 i
    have hs := hy.2 i
    have ht := hz.2 i
    change min (b i) (max (a i) (F p i)) = p i
    omega

def volume {n : ℕ} (b p : Vec (Fin n)) : ℕ := ∑ i, (b i - p i).toNat

theorem volume_decreases {n : ℕ} {b p q : Vec (Fin n)}
    (hpq : p ≤ q) (hqb : q ≤ b) (hne : p ≠ q) : volume b q < volume b p := by
  apply Finset.sum_lt_sum
  · intro i _
    exact Int.toNat_le_toNat (sub_le_sub_left (hpq i) _)
  · have hx : ∃ i, p i ≠ q i := Function.ne_iff.mp hne
    obtain ⟨i, hi⟩ := hx
    have hpi : p i ≤ q i := hpq i
    have hqi : q i ≤ b i := hqb i
    refine ⟨i, Finset.mem_univ i, ?_⟩
    apply (Int.toNat_lt_toNat (by omega)).mpr
    omega

def basicFrom {n : ℕ} (F : Vec (Fin n) → Vec (Fin n)) (hF : Monotone F)
    (a b : Vec (Fin n)) (hab : a ≤ b) (p : Vec (Fin n))
    (hp : InBox a b p) (hinc : p ≤ boxStep F a b p) :
    {r : Vec (Fin n) × ℕ // InBox a b r.1 ∧ boxStep F a b r.1 = r.1 ∧
      r.2 ≤ volume b p + 1} := by
  by_cases heq : boxStep F a b p = p
  · exact ⟨(p, 1), hp, heq, by omega⟩
  · have hq := boxStep_in_box F hab p
    have hnext : boxStep F a b p ≤ boxStep F a b (boxStep F a b p) :=
      boxStep_mono hF a b hinc
    have hvol : volume b (boxStep F a b p) < volume b p :=
      volume_decreases hinc hq.2 (Ne.symm heq)
    let r := basicFrom F hF a b hab (boxStep F a b p) hq hnext
    exact ⟨(r.val.1, r.val.2 + 1), r.property.1, r.property.2.1, by
      have := r.property.2.2; dsimp only; omega⟩
termination_by volume b p

def basic (G : Game) (a b : Vec (Fin G.n)) (hab : a ≤ b) : Vec (Fin G.n) × ℕ :=
  (basicFrom (operator G) (operator_laws G).mono a b hab a
    ⟨le_refl a, hab⟩ (boxStep_in_box (operator G) hab a).1).val

theorem basic_spec (G : Game) (a b : Vec (Fin G.n)) (hab : a ≤ b) :
    Subsolution (operator G) a b (basic G a b hab).1 ∧
    Supersolution (operator G) a b (basic G a b hab).1 ∧
    (basic G a b hab).2 ≤ volume b a + 1 := by
  have h := (basicFrom (operator G) (operator_laws G).mono a b hab a
    ⟨le_refl a, hab⟩ (boxStep_in_box (operator G) hab a).1).property
  have hc := (fixed_iff_comparisons (operator G) hab).mp h.2.1
  exact ⟨hc.1, hc.2, h.2.2⟩

def mass {n : ℕ} (a : Fin n → ℚ) (S : Finset (Fin n)) : ℚ := ∑ i ∈ S, a i

def lowerActive {n : ℕ} (a y : Vec (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => a i < y i)

def upperActive {n : ℕ} (b z : Vec (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => z i < b i)

end MeanPayoff

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Budgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff

structure Budgets (n : ℕ) where
  alpha : Fin n → ℚ
  beta : Fin n → ℚ
  k : ℚ
  m : ℚ
  alpha_pos : ∀ i, 0 < alpha i
  beta_pos : ∀ i, 0 < beta i
  k_pos : 0 < k
  m_pos : 0 < m

def AdmissibleSub {n : ℕ} (F : Vec (Fin n) → Vec (Fin n))
    (a b y : Vec (Fin n)) (P : Budgets n) : Prop :=
  Subsolution F a b y ∧ mass P.alpha (lowerActive a y) ≤ P.k

def AdmissibleSuper {n : ℕ} (F : Vec (Fin n) → Vec (Fin n))
    (a b z : Vec (Fin n)) (P : Budgets n) : Prop :=
  Supersolution F a b z ∧ mass P.beta (upperActive b z) ≤ P.m

def Budgets.density {n : ℕ} (P : Budgets n) (i : Fin n) : ℚ := 1 / (P.alpha i * P.beta i)
def Budgets.totalDensity {n : ℕ} (P : Budgets n) : ℚ := mass P.density Finset.univ
def Budgets.parameter {n : ℕ} (P : Budgets n) : ℚ := P.k * P.m * P.totalDensity
def Budgets.measure {n : ℕ} (P : Budgets n) (S : Finset (Fin n)) : ℚ :=
  mass P.density S / P.totalDensity

theorem Budgets.density_pos {n : ℕ} (P : Budgets n) (i : Fin n) : 0 < P.density i :=
  one_div_pos.mpr (mul_pos (P.alpha_pos i) (P.beta_pos i))

theorem Budgets.totalDensity_pos {n : ℕ} (P : Budgets n) (hn : 0 < n) :
    0 < P.totalDensity := by
  exact Finset.sum_pos (fun i _ => P.density_pos i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem Budgets.measure_compl {n : ℕ} (P : Budgets n) (hn : 0 < n) (S : Finset (Fin n)) :
    P.measure Sᶜ = 1 - P.measure S := by
  have hs : mass P.density S + mass P.density Sᶜ = P.totalDensity :=
    Finset.sum_add_sum_compl S P.density
  unfold Budgets.measure
  rw [← div_self (ne_of_gt (P.totalDensity_pos hn))]
  rw [← sub_div]
  congr 1
  linarith

def smallRankAnswer {n : ℕ} (a b : Vec (Fin n)) (P : Budgets n) : Vec (Fin n) :=
  fun i => if P.m < P.beta i then b i else a i

def halve {n : ℕ} (a : Fin n → ℚ) (H : Finset (Fin n)) : Fin n → ℚ :=
  fun i => if i ∈ H then a i / 2 else a i

theorem halve_pos {n : ℕ} {a : Fin n → ℚ} (ha : ∀ i, 0 < a i)
    (H : Finset (Fin n)) (i : Fin n) : 0 < halve a H i := by
  unfold halve
  split_ifs
  · exact div_pos (ha i) (by norm_num)
  · exact ha i

def Budgets.reduceK {n : ℕ} (P : Budgets n) : Budgets n :=
  { P with k := (4 / 5) * P.k, k_pos := mul_pos (by norm_num) P.k_pos }
def Budgets.reduceM {n : ℕ} (P : Budgets n) : Budgets n :=
  { P with m := (4 / 5) * P.m, m_pos := mul_pos (by norm_num) P.m_pos }
def Budgets.reweightK {n : ℕ} (P : Budgets n) (H : Finset (Fin n)) : Budgets n :=
  { P with
    alpha := halve P.alpha H
    alpha_pos := halve_pos P.alpha_pos H
    k := (3 / 5) * P.k
    k_pos := mul_pos (by norm_num) P.k_pos }
def Budgets.reweightM {n : ℕ} (P : Budgets n) (H : Finset (Fin n)) : Budgets n :=
  { P with
    beta := halve P.beta H
    beta_pos := halve_pos P.beta_pos H
    m := (3 / 5) * P.m
    m_pos := mul_pos (by norm_num) P.m_pos }

theorem Budgets.reduceK_parameter {n : ℕ} (P : Budgets n) :
    P.reduceK.parameter = (4 / 5) * P.parameter := by
  unfold Budgets.parameter Budgets.totalDensity Budgets.density Budgets.reduceK
  ring

theorem Budgets.reduceM_parameter {n : ℕ} (P : Budgets n) :
    P.reduceM.parameter = (4 / 5) * P.parameter := by
  unfold Budgets.parameter Budgets.totalDensity Budgets.density Budgets.reduceM
  ring

theorem density_reweightK {n : ℕ} (P : Budgets n) (H : Finset (Fin n)) (i : Fin n) :
    (P.reweightK H).density i = P.density i + if i ∈ H then P.density i else 0 := by
  simp only [Budgets.density, Budgets.reweightK, halve]
  split_ifs <;> ring

theorem density_reweightM {n : ℕ} (P : Budgets n) (H : Finset (Fin n)) (i : Fin n) :
    (P.reweightM H).density i = P.density i + if i ∈ H then P.density i else 0 := by
  simp only [Budgets.density, Budgets.reweightM, halve]
  split_ifs <;> ring

theorem Budgets.reweightK_totalDensity {n : ℕ} (P : Budgets n) (H : Finset (Fin n)) :
    (P.reweightK H).totalDensity = P.totalDensity + mass P.density H := by
  simp only [Budgets.totalDensity, mass, density_reweightK, Finset.sum_add_distrib]
  congr 1
  simp

theorem Budgets.reweightM_totalDensity {n : ℕ} (P : Budgets n) (H : Finset (Fin n)) :
    (P.reweightM H).totalDensity = P.totalDensity + mass P.density H := by
  simp only [Budgets.totalDensity, mass, density_reweightM, Finset.sum_add_distrib]
  congr 1
  simp

theorem Budgets.reweightK_contraction {n : ℕ} (P : Budgets n) (hn : 0 < n)
    {H : Finset (Fin n)} (hH : P.measure H ≤ 1 / 2) :
    (P.reweightK H).parameter ≤ (9 / 10) * P.parameter := by
  have hm := (div_le_iff₀ (P.totalDensity_pos hn)).mp hH
  change (3 / 5) * P.k * P.m * (P.reweightK H).totalDensity ≤ _
  rw [P.reweightK_totalDensity]
  unfold Budgets.parameter
  have hk := mul_pos P.k_pos P.m_pos
  nlinarith [mul_le_mul_of_nonneg_left hm (le_of_lt hk)]

theorem Budgets.reweightM_contraction {n : ℕ} (P : Budgets n) (hn : 0 < n)
    {H : Finset (Fin n)} (hH : P.measure H ≤ 1 / 2) :
    (P.reweightM H).parameter ≤ (9 / 10) * P.parameter := by
  have hm := (div_le_iff₀ (P.totalDensity_pos hn)).mp hH
  change P.k * ((3 / 5) * P.m) * (P.reweightM H).totalDensity ≤ _
  rw [P.reweightM_totalDensity]
  unfold Budgets.parameter
  have hk := mul_pos P.k_pos P.m_pos
  nlinarith [mul_le_mul_of_nonneg_left hm (le_of_lt hk)]

theorem parameter_rank_exists (R : ℚ) : ∃ d : ℕ, (9 / 10 : ℚ) ^ d * R < 1 := by
  by_cases hR : 0 < R
  · obtain ⟨d, hd⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr hR)
      (show (9 / 10 : ℚ) < 1 by norm_num)
    exact ⟨d, (lt_div_iff₀ hR).mp hd⟩
  · exact ⟨0, by simp; linarith⟩

noncomputable def parameterRank (R : ℚ) : ℕ := Nat.find (parameter_rank_exists R)

theorem parameterRank_spec (R : ℚ) : (9 / 10 : ℚ) ^ parameterRank R * R < 1 :=
  Nat.find_spec (parameter_rank_exists R)

theorem parameterRank_zero_iff (R : ℚ) : parameterRank R = 0 ↔ R < 1 := by
  rw [parameterRank, Nat.find_eq_zero]
  simp

theorem parameterRank_decreases {R R' : ℚ} (hR : 1 ≤ R) (h : R' ≤ (9 / 10) * R) :
    parameterRank R' < parameterRank R := by
  have hp : 0 < parameterRank R := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact (not_lt_of_ge hR) ((parameterRank_zero_iff R).mp hz)
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hs := parameterRank_spec R
  rw [hd, pow_succ] at hs
  have hs' : (9 / 10 : ℚ) ^ d * R' < 1 := by
    have hh := mul_le_mul_of_nonneg_left h (show (0 : ℚ) ≤ (9 / 10 : ℚ) ^ d by positivity)
    nlinarith
  have hmin : parameterRank R' ≤ d := Nat.find_min' (parameter_rank_exists R') hs'
  omega



inductive RandomTree (α : Type) where
  | leaf : α → RandomTree α
  | coin : RandomTree α → RandomTree α → RandomTree α

namespace RandomTree

def bind {α β : Type} : RandomTree α → (α → RandomTree β) → RandomTree β
  | .leaf a, f => f a
  | .coin l r, f => .coin (bind l f) (bind r f)

def map {α β : Type} (f : α → β) (t : RandomTree α) : RandomTree β :=
  t.bind (fun a => .leaf (f a))

def expect {α : Type} : RandomTree α → (α → ℚ) → ℚ
  | .leaf a, f => f a
  | .coin l r, f => (expect l f + expect r f) / 2

def All {α : Type} : RandomTree α → (α → Prop) → Prop
  | .leaf a, P => P a
  | .coin l r, P => All l P ∧ All r P

@[simp] theorem expect_leaf {α : Type} (a : α) (f : α → ℚ) :
    expect (.leaf a) f = f a := rfl
@[simp] theorem expect_coin {α : Type} (l r : RandomTree α) (f : α → ℚ) :
    expect (.coin l r) f = (expect l f + expect r f) / 2 := rfl

@[simp] theorem expect_bind {α β : Type} (t : RandomTree α)
    (f : α → RandomTree β) (g : β → ℚ) :
    expect (t.bind f) g = expect t (fun a => expect (f a) g) := by
  induction t with
  | leaf a => rfl
  | coin l r hl hr => simp [bind, hl, hr]

@[simp] theorem expect_map {α β : Type} (t : RandomTree α)
    (f : α → β) (g : β → ℚ) : expect (t.map f) g = expect t (g ∘ f) := by
  simp [map, Function.comp_def]

@[simp] theorem expect_const {α : Type} (t : RandomTree α) (c : ℚ) :
    expect t (fun _ => c) = c := by
  induction t with
  | leaf a => rfl
  | coin l r hl hr => simp [hl, hr]

@[simp] theorem all_bind {α β : Type} (t : RandomTree α)
    (f : α → RandomTree β) (P : β → Prop) :
    (t.bind f).All P ↔ t.All (fun a => (f a).All P) := by
  induction t with
  | leaf a => rfl
  | coin l r hl hr => simp only [bind, All, hl, hr]

noncomputable def probability {α : Type} (t : RandomTree α) (P : α → Prop) : ℚ := by
  classical
  exact t.expect (fun a => if P a then 1 else 0)

open scoped Classical

end RandomTree
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

def medianInt (as : List ℤ) : ℤ :=
  if h : 0 < as.length then
    (as.mergeSort (· ≤ ·))[as.length / 2]'(by
      simpa only [List.length_mergeSort] using Nat.div_lt_self h (by norm_num))
  else 0

def median {V : Type} (as : List (Vec V)) : Vec V :=
  fun i => medianInt (as.map (fun p => p i))

theorem medianInt_mem {as : List ℤ} (ha : 0 < as.length) : medianInt as ∈ as := by
  rw [medianInt, dite_eq_left ha]
  exact (List.mergeSort_perm as (· ≤ ·)).mem_iff.mp (List.getElem_mem _)

theorem median_inBox {V : Type} {as : List (Vec V)} {a b : Vec V}
    (ha : 0 < as.length) (h : ∀ p ∈ as, InBox a b p) : InBox a b (median as) := by
  constructor
  · intro i
    obtain ⟨p, hp, he⟩ := List.mem_map.mp (medianInt_mem (by simpa using ha :
      0 < (as.map (fun p => p i)).length))
    rw [median, ← he]
    exact (h p hp).1 i
  · intro i
    obtain ⟨p, hp, he⟩ := List.mem_map.mp (medianInt_mem (by simpa using ha :
      0 < (as.map (fun p => p i)).length))
    rw [median, ← he]
    exact (h p hp).2 i

end MeanPayoff

namespace MeanPayoff


def globalG (Bmax : ℕ) : ℕ := 1 + Nat.clog 2 (Bmax + 1)
def sampleExponent (Bmax : ℕ) : ℕ := Nat.clog 2 (2 ^ 17 * (globalG Bmax + 1))
def globalS (Bmax : ℕ) : ℕ := 2 ^ sampleExponent Bmax
def globalJ (n Bmax : ℕ) : ℕ := 2 * (globalS Bmax * (n + 1)) ^ 6 + 1

theorem globalS_lower (Bmax : ℕ) : 2 ^ 17 * (globalG Bmax + 1) ≤ globalS Bmax :=
  Nat.le_pow_clog (by norm_num) _

theorem globalS_large (Bmax : ℕ) : 16 ≤ globalS Bmax := by
  have h := globalS_lower Bmax
  have hg : 1 ≤ globalG Bmax := by unfold globalG; omega
  norm_num at h
  omega

structure SolveBox (n Bmax : ℕ) where
  a : Vec (Fin n)
  b : Vec (Fin n)
  ordered : a ≤ b
  width : ℕ
  positive : 0 < width
  bounded : width ≤ Bmax
  width_bound : ∀ i, b i - a i ≤ (width : ℤ)

abbrev BoxVector {n Bmax : ℕ} (I : SolveBox n Bmax) := {p : Vec (Fin n) // InBox I.a I.b p}

namespace SolveBox

def bottom {n Bmax : ℕ} (I : SolveBox n Bmax) : BoxVector I := ⟨I.a, le_refl _, I.ordered⟩

def medianBox {n Bmax : ℕ} (I : SolveBox n Bmax) (as : List (BoxVector I)) : BoxVector I :=
  if h : 0 < as.length then
    ⟨median (as.map Subtype.val), median_inBox (by simpa using h) (by
      intro p hp
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hp
      exact r.property)⟩
  else I.bottom

def withFloor {n Bmax : ℕ} (I : SolveBox n Bmax) (p : BoxVector I) : SolveBox n Bmax :=
  { I with
    a := p.val
    ordered := p.property.2
    width_bound := fun i => by
      have hp : I.a i ≤ p.val i := p.property.1 i
      have hi := I.width_bound i
      omega }

def withCeiling {n Bmax : ℕ} (I : SolveBox n Bmax) (p : BoxVector I) : SolveBox n Bmax :=
  { I with
    b := p.val
    ordered := p.property.1
    width_bound := fun i => by
      have hp : p.val i ≤ I.b i := p.property.2 i
      have hi := I.width_bound i
      omega }

def capLow {n Bmax : ℕ} (I : SolveBox n Bmax) (C : ℕ) (hC : 0 < C)
    (hle : C ≤ I.width) : SolveBox n Bmax :=
  { I with
    b := fun i => min (I.b i) (I.a i + C)
    ordered := fun i => by
      have hi : I.a i ≤ I.b i := I.ordered i
      dsimp only
      omega
    width := C
    positive := hC
    bounded := hle.trans I.bounded
    width_bound := fun i => by omega }

def capHigh {n Bmax : ℕ} (I : SolveBox n Bmax) (C : ℕ) (hC : 0 < C)
    (hle : C ≤ I.width) : SolveBox n Bmax :=
  { I with
    a := fun i => max (I.a i) (I.b i - C)
    ordered := fun i => by
      have hi : I.a i ≤ I.b i := I.ordered i
      dsimp only
      omega
    width := C
    positive := hC
    bounded := hle.trans I.bounded
    width_bound := fun i => by omega }

def centered {n Bmax : ℕ} (q : Vec (Fin n)) (A : ℕ) (hA : 0 < A)
    (hmax : 2 * A ≤ Bmax) : SolveBox n Bmax where
  a := fun i => q i - A
  b := fun i => q i + A
  ordered := fun i => by
    dsimp only
    omega
  width := 2 * A
  positive := by omega
  bounded := hmax
  width_bound := fun i => by push_cast; omega

def exactVector (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax) : BoxVector I :=
  ⟨(basic G I.a I.b I.ordered).1, (basic_spec G I.a I.b I.ordered).1.1⟩

def smallVector {n Bmax : ℕ} (I : SolveBox n Bmax) (P : Budgets n) : BoxVector I :=
  ⟨smallRankAnswer I.a I.b P, by
    constructor
    · intro i
      unfold smallRankAnswer
      split_ifs <;> first | exact I.ordered i | exact le_refl _
    · intro i
      unfold smallRankAnswer
      split_ifs <;> first | exact I.ordered i | exact le_refl _⟩

def midpoint {n Bmax : ℕ} (I : SolveBox n Bmax) : BoxVector I :=
  ⟨fun i => (I.a i + I.b i) / 2, by
    constructor
    · intro i
      change I.a i ≤ (I.a i + I.b i) / 2
      have hi : I.a i ≤ I.b i := I.ordered i
      omega
    · intro i
      change (I.a i + I.b i) / 2 ≤ I.b i
      have hi : I.a i ≤ I.b i := I.ordered i
      omega⟩

def averageClipped {n Bmax : ℕ} (I : SolveBox n Bmax)
    (r₁ r₂ : Vec (Fin n)) : BoxVector I :=
  ⟨clip I.a I.b (fun i => (r₁ i + r₂ i) / 2), by
    constructor
    · intro i
      dsimp [clip]
      have hi : I.a i ≤ I.b i := I.ordered i
      omega
    · intro i
      dsimp [clip]
      have hi : I.a i ≤ I.b i := I.ordered i
      omega⟩

end SolveBox

namespace RandomTree

def uniformBelow : ℕ → RandomTree ℕ
  | 0 => .leaf 0
  | k + 1 => .coin (uniformBelow k) ((uniformBelow k).map (fun i => i + 2 ^ k))

end RandomTree
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Recursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

theorem Budgets.reduceK_rank {n : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter) :
    parameterRank P.reduceK.parameter < parameterRank P.parameter := by
  apply parameterRank_decreases hR
  rw [P.reduceK_parameter]
  linarith

theorem Budgets.reduceM_rank {n : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter) :
    parameterRank P.reduceM.parameter < parameterRank P.parameter := by
  apply parameterRank_decreases hR
  rw [P.reduceM_parameter]
  linarith

theorem Budgets.reweightK_rank {n : ℕ} (P : Budgets n) (hn : 0 < n)
    (hR : 1 ≤ P.parameter) {H : Finset (Fin n)} (hH : P.measure H ≤ 1 / 2) :
    parameterRank (P.reweightK H).parameter < parameterRank P.parameter :=
  parameterRank_decreases hR (P.reweightK_contraction hn hH)

theorem Budgets.reweightM_rank {n : ℕ} (P : Budgets n) (hn : 0 < n)
    (hR : 1 ≤ P.parameter) {H : Finset (Fin n)} (hH : P.measure H ≤ 1 / 2) :
    parameterRank (P.reweightM H).parameter < parameterRank P.parameter :=
  parameterRank_decreases hR (P.reweightM_contraction hn hH)

abbrev LowerSolver {n Bmax : ℕ} (P : Budgets n) :=
  (Q : Budgets n) → parameterRank Q.parameter < parameterRank P.parameter →
    (I : SolveBox n Bmax) → RandomTree (BoxVector I)

abbrev SmallSet {n : ℕ} (P : Budgets n) := {H : Finset (Fin n) // P.measure H ≤ 1 / 2}

structure Orientation {n : ℕ} (P : Budgets n) where
  chooseY : Bool
  exceptions : List (SmallSet P)

namespace SolveBox

def D {n Bmax : ℕ} (I : SolveBox n Bmax) : ℕ := I.width / (32 * globalS Bmax)
def E {n Bmax : ℕ} (I : SolveBox n Bmax) : ℕ := I.width / 8
def delta {n Bmax : ℕ} (I : SolveBox n Bmax) : ℕ := I.width / (4 * globalS Bmax)
def C {n Bmax : ℕ} (I : SolveBox n Bmax) : ℕ := I.width - I.delta

theorem D_positive {n Bmax : ℕ} (I : SolveBox n Bmax)
    (h : 128 * globalS Bmax < I.width) : 0 < I.D := by
  have hs := globalS_large Bmax
  exact Nat.div_pos (by omega) (by omega)

theorem D_small {n Bmax : ℕ} (I : SolveBox n Bmax) : 2 * I.D ≤ I.width := by
  have hs := globalS_large Bmax
  have hd := Nat.div_mul_le_self I.width (32 * globalS Bmax)
  change 2 * (I.width / (32 * globalS Bmax)) ≤ I.width
  nlinarith

theorem E_positive {n Bmax : ℕ} (I : SolveBox n Bmax)
    (h : 128 * globalS Bmax < I.width) : 0 < I.E := by
  have hs := globalS_large Bmax
  exact Nat.div_pos (by omega) (by omega)

theorem E_smaller {n Bmax : ℕ} (I : SolveBox n Bmax) : 2 * I.E < I.width := by
  have hd := Nat.div_mul_le_self I.width 8
  have hp := I.positive
  change 2 * (I.width / 8) < I.width
  omega

theorem delta_positive {n Bmax : ℕ} (I : SolveBox n Bmax)
    (h : 128 * globalS Bmax < I.width) : 0 < I.delta := by
  have hs := globalS_large Bmax
  exact Nat.div_pos (by omega) (by omega)

theorem delta_smaller {n Bmax : ℕ} (I : SolveBox n Bmax) : I.delta < I.width := by
  have hs := globalS_large Bmax
  have hd := Nat.div_mul_le_self I.width (4 * globalS Bmax)
  have hp := I.positive
  change I.width / (4 * globalS Bmax) < I.width
  nlinarith

theorem C_positive {n Bmax : ℕ} (I : SolveBox n Bmax) : 0 < I.C := by
  have hd := I.delta_smaller
  unfold C
  omega

theorem C_smaller {n Bmax : ℕ} (I : SolveBox n Bmax)
    (h : 128 * globalS Bmax < I.width) : I.C < I.width := by
  have hd := I.delta_positive h
  have hp := I.C_positive
  unfold C at *
  omega

def narrowCentered {n Bmax : ℕ} (I : SolveBox n Bmax)
    (h : 128 * globalS Bmax < I.width) (q : Vec (Fin n)) : SolveBox n Bmax :=
  centered q I.D (I.D_positive h) (I.D_small.trans I.bounded)

def wideCentered {n Bmax : ℕ} (I : SolveBox n Bmax)
    (h : 128 * globalS Bmax < I.width) (q : Vec (Fin n)) : SolveBox n Bmax :=
  centered q I.E (I.E_positive h) (I.E_smaller.le.trans I.bounded)

end SolveBox

def PositiveDisplacement {n Bmax : ℕ} (I : SolveBox n Bmax) (q : BoxVector I) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 2 * (I.width : ℤ) <
    (globalS Bmax : ℤ) * (q.val i - I.midpoint.val i))

def NegativeDisplacement {n Bmax : ℕ} (I : SolveBox n Bmax) (q : BoxVector I) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (globalS Bmax : ℤ) * (q.val i - I.midpoint.val i) <
    -2 * (I.width : ℤ))

def orientBase (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax) :
    Orientation P :=
  let p := I.exactVector G
  let H : Finset (Fin G.n) := Finset.univ.filter (fun i => (I.width : ℤ) ≤ 2 * (p.val i - I.a i))
  if hH : 1 / 2 < P.measure H then
    ⟨true, [⟨Hᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩
  else ⟨false, [⟨H, le_of_not_gt hH⟩]⟩

def combineOrientations {n : ℕ} {P : Budgets n} (os : List (Orientation P)) : Orientation P :=
  ⟨decide (os.length < 2 * (os.filter (fun o => o.chooseY)).length),
      (os.map Orientation.exceptions).flatten⟩



structure InnerBox {n Bmax : ℕ} (I : SolveBox n Bmax) where
  box : SolveBox n Bmax
  width_eq : box.width = I.width
  floor_le : I.a ≤ box.a
  ceiling_le : box.b ≤ I.b

def InnerBox.include {n Bmax : ℕ} {I : SolveBox n Bmax} (K : InnerBox I)
    (p : BoxVector K.box) : BoxVector I :=
  ⟨p.val, K.floor_le.trans p.property.1, p.property.2.trans K.ceiling_le⟩

theorem volume_ceiling_decreases {n : ℕ} {a b r : Vec (Fin n)}
    (har : a ≤ r) (hrb : r ≤ b) (hne : r ≠ b) : volume r a < volume b a := by
  apply Finset.sum_lt_sum
  · intro i _
    exact Int.toNat_le_toNat (sub_le_sub_right (hrb i) _)
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    have hai : a i ≤ r i := har i
    have hbi : r i ≤ b i := hrb i
    refine ⟨i, Finset.mem_univ i, ?_⟩
    apply (Int.toNat_lt_toNat (by omega)).mpr
    omega

namespace SolveBox

def maxVector {n Bmax : ℕ} (I : SolveBox n Bmax) (p q : BoxVector I) : BoxVector I :=
  ⟨fun i => max (p.val i) (q.val i), by
    constructor
    · intro i
      exact (p.property.1 i).trans (le_max_left _ _)
    · intro i
      exact max_le (p.property.2 i) (q.property.2 i)⟩

def minVector {n Bmax : ℕ} (I : SolveBox n Bmax) (p q : BoxVector I) : BoxVector I :=
  ⟨fun i => min (p.val i) (q.val i), by
    constructor
    · intro i
      exact le_min (p.property.1 i) (q.property.1 i)
    · intro i
      exact (min_le_left _ _).trans (p.property.2 i)⟩

def includeCapLow {n Bmax : ℕ} (I : SolveBox n Bmax) (C : ℕ) (hC : 0 < C)
    (hle : C ≤ I.width) (p : BoxVector (I.capLow C hC hle)) : BoxVector I :=
  ⟨p.val, p.property.1, fun i => (p.property.2 i).trans (min_le_left _ _)⟩

def includeCapHigh {n Bmax : ℕ} (I : SolveBox n Bmax) (C : ℕ) (hC : 0 < C)
    (hle : C ≤ I.width) (p : BoxVector (I.capHigh C hC hle)) : BoxVector I :=
  ⟨p.val, fun i => (le_max_left _ _).trans (p.property.1 i), p.property.2⟩

end SolveBox

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Deviation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff


namespace RandomTree

open Classical in
@[simp] theorem probability_leaf {α : Type} (a : α) (P : α → Prop) :
    (leaf a).probability P = if P a then 1 else 0 := by
  classical
  rfl

end RandomTree

def Comparisons (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (solver : (I : SolveBox G.n Bmax) → RandomTree (BoxVector I)) : Prop :=
  (∀ I y, AdmissibleSub (operator G) I.a I.b y P →
    (solver I).probability (fun p => ¬ y ≤ p.val) ≤ 1 / 16) ∧
  (∀ I z, AdmissibleSuper (operator G) I.a I.b z P →
    (solver I).probability (fun p => ¬ p.val ≤ z) ≤ 1 / 16)

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Drift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff



def Linked {α : Type} (R : α → α → Prop) (q : α) (qs : List α) : Prop :=
  qs.head? = some q ∧ qs.IsChain R

def CenterDrift {n Bmax : ℕ} (I : SolveBox n Bmax) (r : ℕ) (q : BoxVector I) : Prop :=
  ∀ i, |q.val i - I.midpoint.val i| ≤ (r : ℤ) * I.D

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Alternatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
open scoped Classical

def Moving {n Bmax : ℕ} (I : SolveBox n Bmax) (q q' : BoxVector I) : Prop :=
  ∀ i, |q'.val i - q.val i| ≤ (I.D : ℤ)

end MeanPayoff

namespace MeanPayoff
open scoped Classical

def Alternative {n : ℕ} {P : Budgets n} (side : Bool) (w : Fin n → ℚ)
    (S : Finset (Fin n)) (budget : ℚ) (O : Orientation P) : Prop :=
  O.chooseY = side ∨ ∃ H ∈ O.exceptions, (4 / 5) * budget < mass w (S ∩ H.val)

def HighAlternative {n Bmax : ℕ} (I : SolveBox n Bmax) (P : Budgets n)
    (y : Vec (Fin n)) : Orientation P → Prop :=
  Alternative true P.alpha (lowerActive I.a y) P.k

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Traversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff


def HighAccuracy (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax)
    (t : RandomTree (BoxVector I)) (δ : ℚ) : Prop :=
  ∀ y, AdmissibleSub (operator G) I.a I.b y P → t.probability (fun p => ¬y ≤ p.val) ≤ δ

def LowAccuracy (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax)
    (t : RandomTree (BoxVector I)) (δ : ℚ) : Prop :=
  ∀ z, AdmissibleSuper (operator G) I.a I.b z P → t.probability (fun p => ¬p.val ≤ z) ≤ δ

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_CountedTraversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

def CorrectSet (G : Game) (out : Fin G.n → Bool) : Prop := ∀ v, out v = true ↔ Winning G v


namespace RandomTree

@[simp] theorem leaf_bind {α β : Type} (a : α) (f : α → RandomTree β) :
    (leaf a).bind f = f a := rfl

@[simp] theorem bind_leaf {α : Type} (t : RandomTree α) : t.bind leaf = t := by
  induction t with
  | leaf a => rfl
  | coin l r il ir => simp only [bind, il, ir]

@[simp] theorem bind_assoc {α β γ : Type} (t : RandomTree α)
    (f : α → RandomTree β) (g : β → RandomTree γ) :
    (t.bind f).bind g = t.bind (fun a => (f a).bind g) := by
  induction t with
  | leaf a => rfl
  | coin l r il ir => simp only [bind, il, ir]

@[simp] theorem map_map {α β γ : Type} (t : RandomTree α) (f : α → β) (g : β → γ) :
    (t.map f).map g = t.map (fun a => g (f a)) := by simp [map]

@[simp] theorem bind_map {α β γ : Type} (t : RandomTree α) (f : α → β)
    (g : β → RandomTree γ) : (t.map f).bind g = t.bind (fun a => g (f a)) := by
  simp [map]

@[simp] theorem all_map {α β : Type} (t : RandomTree α) (f : α → β) (P : β → Prop) :
    (t.map f).All P ↔ t.All (fun a => P (f a)) := by
  simp only [map, all_bind, All]

end RandomTree

structure Counted (α : Type) where
  tree : RandomTree (α × ℕ)

namespace Counted

def pure {α : Type} (a : α) : Counted α := ⟨.leaf (a, 0)⟩
def lift {α : Type} (t : RandomTree α) : Counted α := ⟨t.map (fun a => (a, 0))⟩
def map {α β : Type} (f : α → β) (t : Counted α) : Counted β :=
  ⟨t.tree.map (fun p => (f p.1, p.2))⟩
def bind {α β : Type} (t : Counted α) (f : α → Counted β) : Counted β :=
  ⟨t.tree.bind fun p => (f p.1).tree.map (fun q => (q.1, p.2 + q.2))⟩
def charge {α : Type} (c : ℕ) (t : Counted α) : Counted α :=
  ⟨t.tree.map (fun p => (p.1, c + p.2))⟩
def erase {α : Type} (t : Counted α) : RandomTree α := t.tree.map Prod.fst
def Bounded {α : Type} (t : Counted α) (N : ℕ) : Prop := t.tree.All (fun p => p.2 ≤ N)

@[simp] theorem erase_pure {α : Type} (a : α) : (pure a).erase = .leaf a := rfl
@[simp] theorem erase_lift {α : Type} (t : RandomTree α) : (lift t).erase = t := by
  simp [erase, lift, RandomTree.map]
@[simp] theorem erase_map {α β : Type} (t : Counted α) (f : α → β) :
    (t.map f).erase = t.erase.map f := by simp [erase, map]
@[simp] theorem erase_charge {α : Type} (c : ℕ) (t : Counted α) :
    (t.charge c).erase = t.erase := by simp [erase, charge]

def trials {α : Type} (t : Counted α) : ℕ → Counted (List α)
  | 0 => pure []
  | J + 1 => t.bind fun a => (trials t J).map (a :: ·)

def traverse {α β : Type} (f : α → Counted β) : List α → Counted (List β)
  | [] => pure []
  | a :: as => (f a).bind fun b => (traverse f as).map (b :: ·)

end Counted
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_CountedRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

def SolveBox.repeatedCounted {n Bmax : ℕ} (I : SolveBox n Bmax)
    (t : Counted (BoxVector I)) (J : ℕ) : Counted (BoxVector I) :=
  (Counted.trials t J).map I.medianBox

namespace CountedAlgorithm

abbrev LowerSolver {n Bmax : ℕ} (P : Budgets n) :=
  (Q : Budgets n) → parameterRank Q.parameter < parameterRank P.parameter →
    (I : SolveBox n Bmax) → Counted (BoxVector I)

def centerUpdate {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (q : BoxVector I) : Counted (BoxVector I) :=
  let K := I.narrowCentered hB q.val
  (K.repeatedCounted (lower P.reduceK (P.reduceK_rank hR) K) (globalJ n Bmax)).bind fun r₁ =>
  (K.repeatedCounted (lower P.reduceM (P.reduceM_rank hR) K) (globalJ n Bmax)).map fun r₂ =>
    I.averageClipped r₁.val r₂.val

def centerSteps {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) :
    ℕ → BoxVector I → Counted (List (BoxVector I))
  | 0, q => Counted.pure [q]
  | t + 1, q =>
    (centerUpdate P hR lower I hB q).bind fun q' =>
    (centerSteps P hR lower I hB t q').map (q :: ·)

def orientationTail (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax)
    (qs : List (BoxVector I)) (child : BoxVector I → Counted (Orientation P)) :
    Counted (Orientation P) :=
  let H := PositiveDisplacement I (qs.getD (globalS Bmax) I.midpoint)
  let N := NegativeDisplacement I (qs.getD (globalS Bmax) I.midpoint)
  if hH : 1 / 2 < P.measure H then
    Counted.pure ⟨true, [⟨Hᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩
  else if hN : 1 / 2 < P.measure N then
    Counted.pure ⟨false, [⟨Nᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩
  else
    (Counted.lift (RandomTree.uniformBelow (sampleExponent Bmax))).bind fun j =>
      (child (qs.getD j I.midpoint)).map fun O =>
        ⟨O.chooseY, O.exceptions ++ [⟨H, le_of_not_gt hH⟩, ⟨N, le_of_not_gt hN⟩]⟩

def orient (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) :
    Counted (Orientation P) :=
  if hB : I.width ≤ 128 * globalS Bmax then
    Counted.pure (orientBase G P I)
  else
    let hb : 128 * globalS Bmax < I.width := lt_of_not_ge hB
    (centerSteps P hR lower I hb (globalS Bmax) I.midpoint).bind fun qs =>
      orientationTail G P I qs (fun q => orient G P hR lower (I.wideCentered hb q.val))
termination_by I.width
decreasing_by exact I.E_smaller

def orientPlus {n : ℕ} {P : Budgets n} (t : Counted (Orientation P)) (J : ℕ) :
    Counted (Orientation P) :=
  (Counted.trials t J).map combineOrientations

def tighten {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) : Counted (InnerBox I) :=
  (I.repeatedCounted (lower P.reduceK (P.reduceK_rank hR) I) (globalJ n Bmax)).bind fun r₁ =>
  if _h₁ : ∃ i, (I.delta : ℤ) ≤ r₁.val i - I.a i then
    let K := I.withFloor r₁
    (tighten P hR lower K hB).map fun T =>
      ⟨T.box, T.width_eq, r₁.property.1.trans T.floor_le, T.ceiling_le⟩
  else
    (I.repeatedCounted (lower P.reduceM (P.reduceM_rank hR) I) (globalJ n Bmax)).bind fun r₂ =>
    if _h₂ : ∃ i, (I.delta : ℤ) ≤ I.b i - r₂.val i then
      let K := I.withCeiling r₂
      (tighten P hR lower K hB).map fun T =>
        ⟨T.box, T.width_eq, T.floor_le, T.ceiling_le.trans r₂.property.2⟩
    else Counted.pure ⟨I, rfl, le_refl _, le_refl _⟩
termination_by volume I.b I.a
decreasing_by
  · apply volume_decreases r₁.property.1 r₁.property.2
    obtain ⟨i, hi⟩ := _h₁
    have hd := I.delta_positive hB
    intro heq
    have he := congrFun heq i
    omega
  · apply volume_ceiling_decreases r₂.property.1 r₂.property.2
    obtain ⟨i, hi⟩ := _h₂
    have hd := I.delta_positive hB
    intro heq
    have he := congrFun heq i
    omega

def finishChoice (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax)
    (hB : 128 * globalS Bmax < I.width) (O : Orientation P)
    (up : Counted (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : Counted (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le))) :
    Counted (BoxVector I) :=
  if O.chooseY then
    (Counted.traverse (fun H : SmallSet P =>
      I.repeatedCounted (lower (P.reweightM H.val)
        (P.reweightM_rank G.positive hR H.property) I) (globalJ G.n Bmax)) O.exceptions).bind fun rs =>
    up.map fun p => rs.foldl I.minVector (I.includeCapHigh I.C I.C_positive (I.C_smaller hB).le p)
  else
    (Counted.traverse (fun H : SmallSet P =>
      I.repeatedCounted (lower (P.reweightK H.val)
        (P.reweightK_rank G.positive hR H.property) I) (globalJ G.n Bmax)) O.exceptions).bind fun rs =>
    lo.map fun p => rs.foldl I.maxVector (I.includeCapLow I.C I.C_positive (I.C_smaller hB).le p)

def solveWidth (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) : Counted (BoxVector I) :=
  Counted.charge 1 <|
  if hB : I.width ≤ 128 * globalS Bmax then Counted.pure (I.exactVector G)
  else
    (tighten P hR lower I (lt_of_not_ge hB)).bind fun T =>
    let K := T.box
    have hK : 128 * globalS Bmax < K.width := by rw [T.width_eq]; omega
    let c := K.C
    have hc : 0 < c := K.C_positive
    have hcsmall : c < K.width := K.C_smaller hK
    (orientPlus (orient G P hR lower K) (globalJ G.n Bmax)).bind fun O =>
    (finishChoice G P hR lower K hK O
      (solveWidth G P hR lower (K.capHigh c hc hcsmall.le))
      (solveWidth G P hR lower (K.capLow c hc hcsmall.le))).map T.include
termination_by I.width
decreasing_by
  all_goals
    change c < I.width
    rw [← T.width_eq]
    exact hcsmall

def solve (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax) :
    Counted (BoxVector I) :=
  if hR : P.parameter < 1 then Counted.charge 1 (Counted.pure (I.smallVector P))
  else solveWidth G P (le_of_not_gt hR) (fun Q _ K => solve G Q K) I
termination_by parameterRank P.parameter

end CountedAlgorithm


namespace CountedAlgorithm

def eraseLower {n Bmax : ℕ} {P : Budgets n} (lower : LowerSolver (Bmax := Bmax) P) :
    MeanPayoff.LowerSolver (Bmax := Bmax) P := fun Q h I => (lower Q h I).erase

abbrev LowerBound {n Bmax : ℕ} {P : Budgets n} (lower : LowerSolver (Bmax := Bmax) P)
    (N : ℕ) : Prop := ∀ Q h I, (lower Q h I).Bounded N

end CountedAlgorithm
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_InputSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

@[simp] theorem encodeNat_length (n : ℕ) :
    (encodeNat n).length = 2 * Nat.size (n + 1) + 1 := by
  simp [encodeNat, Nat.size_eq_bits_len]
  omega

@[simp] theorem encodeInt_length (z : ℤ) :
    (encodeInt z).length = 2 * Nat.size (z.natAbs + 1) + 2 := by
  simp [encodeInt]

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_BitDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace RandomTree
open scoped Classical

def bitDepth {α : Type} : RandomTree α → ℕ
  | .leaf _ => 0
  | .coin l r => max l.bitDepth r.bitDepth + 1

def read {α : Type} : RandomTree α → (ℕ → Bool) → α
  | .leaf a, _ => a
  | .coin l r, bits => if bits 0 then r.read (fun i => bits (i + 1))
    else l.read (fun i => bits (i + 1))

def readPrefix {α : Type} (t : RandomTree α) {T : ℕ} (bits : Fin T → Bool) : α :=
  t.read (padBits bits)

@[simp] theorem padBits_cons_zero {T : ℕ} (b : Bool) (bits : Fin T → Bool) :
    padBits (Fin.cons b bits) 0 = b := by simp [padBits]

@[simp] theorem padBits_cons_succ {T : ℕ} (b : Bool) (bits : Fin T → Bool) (j : ℕ) :
    padBits (Fin.cons b bits) (j + 1) = padBits bits j := by
  by_cases h : j < T
  · simp only [padBits, Nat.add_lt_add_iff_right, h, ↓reduceDIte]
    rfl
  · simp only [padBits, Nat.add_lt_add_iff_right, h, ↓reduceDIte]

@[simp] theorem readPrefix_leaf {α : Type} (a : α) {T : ℕ} (bits : Fin T → Bool) :
    readPrefix (.leaf a) bits = a := rfl

@[simp] theorem readPrefix_coin_cons {α : Type} (l r : RandomTree α) {T : ℕ}
    (b : Bool) (bits : Fin T → Bool) :
    readPrefix (.coin l r) (Fin.cons b bits) =
      if b then readPrefix r bits else readPrefix l bits := by
  simp only [readPrefix, read, padBits_cons_zero, padBits_cons_succ]

end RandomTree
end MeanPayoff

namespace MeanPayoff


namespace RandomTree

@[simp] theorem bitDepth_map {α β : Type} (t : RandomTree α) (f : α → β) :
    (t.map f).bitDepth = t.bitDepth := by
  induction t with
  | leaf a => rfl
  | coin l r il ir => simpa only [map, bind, bitDepth] using congrArg₂ (fun x y => max x y + 1) il ir

@[simp] theorem bitDepth_uniformBelow (k : ℕ) : (uniformBelow k).bitDepth = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [uniformBelow, bitDepth, bitDepth_map, ih, max_self]

end RandomTree

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Decoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace BinaryInput

def bitsValue : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (bitsValue bs)

@[simp] theorem bitsValue_bits (n : ℕ) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih => rw [Nat.bits_append_bit n b h, bitsValue, ih]

abbrev Edge := ℕ × ℕ × ℤ

def encodeEdge (e : Edge) : List Bool := encodeNat (e.1 + 1) ++ encodeNat (e.2.1 + 1) ++ encodeInt e.2.2

structure RawGame where
  n : ℕ
  m : ℕ
  owner : List Bool
  edges : List Edge
  deriving DecidableEq

def lower (G : Game) : RawGame where
  n := G.n
  m := G.m
  owner := List.ofFn G.maxOwner
  edges := List.ofFn (fun e : Fin G.m => ((G.tail e).val, (G.head e).val, G.weight e))

def rawCode (R : RawGame) : List Bool :=
  encodeNat R.n ++ encodeNat R.m ++ R.owner ++ (R.edges.map encodeEdge).flatten

end BinaryInput
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Online
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace RandomTree

def consume {α : Type} : RandomTree α → (ℕ → Bool) → ℕ → α × ℕ
  | .leaf a, _, pos => (a, pos)
  | .coin l r, bits, pos => if bits pos then consume r bits (pos + 1)
    else consume l bits (pos + 1)

@[simp] theorem consume_bind {α β : Type} (t : RandomTree α) (f : α → RandomTree β)
    (bits : ℕ → Bool) (pos : ℕ) :
    (t.bind f).consume bits pos =
      let p := t.consume bits pos
      (f p.1).consume bits p.2 := by
  induction t generalizing pos with
  | leaf a => rfl
  | coin l r il ir => simp only [bind, consume]; split <;> simp_all

@[simp] theorem consume_map {α β : Type} (t : RandomTree α) (f : α → β)
    (bits : ℕ → Bool) (pos : ℕ) :
    (t.map f).consume bits pos = (f (t.consume bits pos).1, (t.consume bits pos).2) := by
  simp only [map, consume_bind, consume]

end RandomTree

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_FiniteSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff


@[simp] theorem RandomTree.read_map {α β : Type} (t : RandomTree α) (f : α → β)
    (bits : ℕ → Bool) : (t.map f).read bits = f (t.read bits) := by
  induction t generalizing bits with
  | leaf a => rfl
  | coin l r il ir => simp only [RandomTree.map, RandomTree.bind, RandomTree.read]; split <;> simp_all [RandomTree.map]

namespace BinaryInput

def CorrectList (G : Game) (out : List Bool) : Prop :=
  out.length = G.n ∧ ∀ v : Fin G.n, out[v.val]? = some true ↔ Winning G v

@[simp] theorem correctList_ofFn (G : Game) (out : Fin G.n → Bool) :
    CorrectList G (List.ofFn out) ↔ CorrectSet G out := by
  simp only [CorrectList, List.length_ofFn, List.getElem?_ofFn, Fin.isLt, ↓reduceDIte,
    Option.some.injEq, true_and, CorrectSet]

open scoped Classical

end BinaryInput
end MeanPayoff

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_BitProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace BinaryStack

inductive Op where
  | keep | pop | push (b : Bool)
  deriving DecidableEq, Fintype

structure Act (q : ℕ) where
  next : Fin q
  work : Fin 2 → Op
  emit : Option Bool

structure Program where
  states : ℕ
  start : Fin states
  transition : Fin states → (Fin 2 → Option Bool) → Bool → Option (Act states)

structure Config (P : Program) where
  control : Option (Fin P.states)
  stack : Fin 2 → List Bool
  output : List Bool

def applyOp : Op → List Bool → List Bool
  | .keep, xs => xs
  | .pop, xs => xs.tail
  | .push b, xs => b :: xs

def shiftOp : Op → List Bool → Direction
  | .keep, _ => .stay
  | .pop, [] => .stay
  | .pop, _ :: _ => .right
  | .push _, _ => .left

def firstWrite : Op → Symbol → Symbol
  | .pop, _ => none
  | _, a => a

def pendingWrite : Op → Option Bool
  | .push b => some b
  | _ => none

def step (P : Program) (c : Config P) (bit : Bool) : Config P :=
  match c.control with
  | none => c
  | some q =>
    match P.transition q (fun k => (c.stack k).head?) bit with
    | none => { c with control := none }
    | some a =>
      ⟨some a.next, fun k => applyOp (a.work k) (c.stack k),
        c.output ++ a.emit.toList⟩

def initial (P : Program) (code : List Bool) : Config P :=
  ⟨some P.start, fun k => if k = 0 then code else [], []⟩

def run (P : Program) (code : List Bool) (random : ℕ → Bool) : ℕ → Config P
  | 0 => initial P code
  | t + 1 => step P (run P code random t) (random t)

def cells (xs : List Bool) (h : ℤ) (j : ℤ) : Symbol :=
  if 0 ≤ j - h then xs[(j - h).toNat]? else none

@[simp] theorem cells_top (xs : List Bool) (h : ℤ) : cells xs h h = xs.head? := by
  cases xs <;> simp [cells]

@[simp] theorem cells_nil (h : ℤ) : cells [] h = fun _ => none := by
  funext j; simp [cells]

abbrev Control (P : Program) := Fin P.states ⊕ (Fin P.states × (Fin 2 → Option Bool))

noncomputable def controlEquiv (P : Program) : Control P ≃ Fin (Fintype.card (Control P)) :=
  Fintype.equivFin _

noncomputable def normal (P : Program) (q : Fin P.states) : Fin (Fintype.card (Control P)) :=
  controlEquiv P (.inl q)

noncomputable def pending (P : Program) (q : Fin P.states) (w : Fin 2 → Option Bool) :
    Fin (Fintype.card (Control P)) := controlEquiv P (.inr (q, w))

noncomputable def machine (P : Program) : Machine where
  states := Fintype.card (Control P)
  start := normal P P.start
  transition q top bit :=
    match (controlEquiv P).symm q with
    | .inl q =>
      (P.transition q (fun k => top ⟨k.val, by omega⟩) bit).map fun a =>
        ⟨pending P a.next (fun k => pendingWrite (a.work k)),
          fun k => if hk : k.val < 2 then firstWrite (a.work ⟨k.val, hk⟩) (top k)
            else a.emit,
          fun k => if hk : k.val < 2 then
            match a.work ⟨k.val, hk⟩ with
            | .keep => .stay
            | .pop => if (top k).isSome then .right else .stay
            | .push _ => .left
          else if a.emit.isSome then .right else .stay⟩
    | .inr (q, w) =>
      some ⟨normal P q, fun k => if hk : k.val < 2 then
          (w ⟨k.val, hk⟩).or (top k) else top k,
        fun _ => .stay⟩

noncomputable def concrete (P : Program) (c : Config P) (h : Fin 2 → ℤ) : Configuration (machine P) where
  control := c.control.map (normal P)
  head k := if hk : k.val < 2 then h ⟨k.val, hk⟩ else c.output.length
  tape k := if hk : k.val < 2 then cells (c.stack ⟨k.val, hk⟩) (h ⟨k.val, hk⟩)
    else cells c.output 0

@[simp] theorem cells_end (xs : List Bool) : cells xs 0 (xs.length : ℤ) = none := by
  simp [cells]

def newHeads {P : Program} (c : Config P) (h : Fin 2 → ℤ) (a : Act P.states) : Fin 2 → ℤ :=
  fun k => h k + (shiftOp (a.work k) (c.stack k)).offset

@[ext] theorem concrete_ext {M : Machine} {a b : Configuration M}
    (hc : a.control = b.control) (hh : a.head = b.head) (ht : a.tape = b.tape) : a = b := by
  cases a; cases b; simp_all

@[simp] theorem decode_normal (P : Program) (q : Fin P.states) :
    (controlEquiv P).symm (normal P q) = .inl q := by
  exact (controlEquiv P).symm_apply_apply _
@[simp] theorem decode_pending (P : Program) (q : Fin P.states) (w : Fin 2 → Option Bool) :
    (controlEquiv P).symm (pending P q w) = .inr (q,w) := by
  exact (controlEquiv P).symm_apply_apply _

@[simp] theorem shiftOp_formula (op : Op) (xs : List Bool) :
    (match op with
     | .keep => Direction.stay
     | .pop => if xs = [] then Direction.stay else Direction.right
     | .push _ => Direction.left) = shiftOp op xs := by
  cases op <;> cases xs <;> rfl

@[simp] theorem concrete_halted (P : Program) (c : Config P) (h : Fin 2 → ℤ) :
    (concrete P c h).control = none ↔ c.control = none := by
  change c.control.map (normal P) = none ↔ c.control = none
  exact Option.map_eq_none_iff

end BinaryStack
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Simulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff
namespace BinaryStack

def advance (P : Program) (bits : ℕ → Bool) (c : Config P) : ℕ → Config P
  | 0 => c
  | t + 1 => step P (advance P bits c t) (bits t)

theorem advance_front (P : Program) (bits : ℕ → Bool) (c : Config P) (t : ℕ) :
    advance P bits c (t + 1) = advance P (fun j => bits (j + 1)) (step P c (bits 0)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change step P (advance P bits c (t + 1)) (bits (t + 1)) =
      step P (advance P (fun j => bits (j + 1)) (step P c (bits 0)) t) (bits (t + 1))
    rw [ih]

theorem advance_halted (P : Program) (bits : ℕ → Bool) (c : Config P)
    (hc : c.control = none) (t : ℕ) : advance P bits c t = c := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [advance, ih, step, hc]

@[ext] theorem Config.ext {P : Program} {a b : Config P}
    (hc : a.control = b.control) (hs : a.stack = b.stack) (ho : a.output = b.output) : a = b := by
  cases a; cases b; simp_all

namespace Addition

def value : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * value bs

def low (a b c : Bool) : Bool := xor (xor a b) c
def carry (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

theorem full_adder (a b c : Bool) :
    (low a b c).toNat + 2 * (carry a b c).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> rfl

def label : Bool → Fin 2
  | false => 0
  | true => 1

def finiteProgram : Program where
  states := 2
  start := 0
  transition q top _ :=
    if top 0 = none ∧ top 1 = none then
      if q = 1 then some ⟨0, fun _ => Op.keep, some true⟩ else none
    else
      let a := (top 0).getD false
      let b := (top 1).getD false
      let c := decide (q = 1)
      some ⟨label (carry a b c), fun _ => Op.pop, some (low a b c)⟩

def state (c : Bool) (xs ys out : List Bool) : Config finiteProgram :=
  ⟨some (label c), ![xs, ys], out⟩

@[simp] theorem label_one (c : Bool) : decide (label c = 1) = c := by
  cases c <;> rfl

@[simp] theorem step_nil_true (out : List Bool) (bit : Bool) :
    step finiteProgram (state true [] [] out) bit = state false [] [] (out ++ [true]) := by
  rfl

@[simp] theorem step_cons_left (c a : Bool) (as out : List Bool) (bit : Bool) :
    step finiteProgram (state c (a :: as) [] out) bit =
      state (carry a false c) as [] (out ++ [low a false c]) := by
  cases c <;> apply Config.ext <;> try rfl
  all_goals funext k; fin_cases k <;> rfl

@[simp] theorem step_cons_right (c b : Bool) (bs out : List Bool) (bit : Bool) :
    step finiteProgram (state c [] (b :: bs) out) bit =
      state (carry false b c) [] bs (out ++ [low false b c]) := by
  cases c <;> apply Config.ext <;> try rfl
  all_goals funext k; fin_cases k <;> rfl

@[simp] theorem step_cons_both (c a b : Bool) (as bs out : List Bool) (bit : Bool) :
    step finiteProgram (state c (a :: as) (b :: bs) out) bit =
      state (carry a b c) as bs (out ++ [low a b c]) := by
  cases c <;> apply Config.ext <;> try rfl
  all_goals funext k; fin_cases k <;> rfl

end Addition
end BinaryStack

namespace WorkStack
open BinaryStack (Op applyOp shiftOp firstWrite pendingWrite cells cells_top concrete_ext)

structure Act (q : ℕ) where
  next : Fin q
  work : Fin 3 → Op

structure Program where
  states : ℕ
  start : Fin states
  transition : Fin states → (Fin 3 → Option Bool) → Bool → Option (Act states)

structure Config (P : Program) where
  control : Option (Fin P.states)
  stack : Fin 3 → List Bool

@[ext] theorem Config.ext {P : Program} {a b : Config P}
    (hc : a.control = b.control) (hs : a.stack = b.stack) : a = b := by
  cases a; cases b; simp_all

def step (P : Program) (c : Config P) (bit : Bool) : Config P :=
  match c.control with
  | none => c
  | some q =>
    match P.transition q (fun k => (c.stack k).head?) bit with
    | none => { c with control := none }
    | some a => ⟨some a.next, fun k => applyOp (a.work k) (c.stack k)⟩

def advance (P : Program) (bits : ℕ → Bool) (c : Config P) : ℕ → Config P
  | 0 => c
  | t + 1 => step P (advance P bits c t) (bits t)

@[simp] theorem advance_zero (P : Program) (bits : ℕ → Bool) (c : Config P) :
    advance P bits c 0 = c := rfl

theorem advance_front (P : Program) (bits : ℕ → Bool) (c : Config P) (t : ℕ) :
    advance P bits c (t + 1) = advance P (fun j => bits (j + 1)) (step P c (bits 0)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change step P (advance P bits c (t + 1)) (bits (t + 1)) =
      step P (advance P (fun j => bits (j + 1)) (step P c (bits 0)) t) (bits (t + 1))
    rw [ih]

theorem advance_add (P : Program) (bits : ℕ → Bool) (c : Config P) (t u : ℕ) :
    advance P bits c (t + u) = advance P (fun j => bits (t + j)) (advance P bits c t) u := by
  induction u with
  | zero => rfl
  | succ u ih =>
    change step P (advance P bits c (t + u)) (bits (t + u)) =
      step P (advance P (fun j => bits (t + j)) (advance P bits c t) u) (bits (t + u))
    rw [ih]

end WorkStack
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_SignedBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.WorkStack
open BinaryStack (Op applyOp)
namespace Addition
open BinaryStack.Addition (low carry value )

def finiteProgram : Program where
  states := 3
  start := 0
  transition q top _ :=
    if q = 2 then
      (top 2).map fun b => ⟨2, ![.push b, .keep, .pop]⟩
    else if top 0 = none ∧ top 1 = none then
      some ⟨2, ![.keep, .keep, if q = 1 then .push true else .keep]⟩
    else
      let a := (top 0).getD false
      let b := (top 1).getD false
      let c := decide (q = 1)
      some ⟨if carry a b c then 1 else 0, ![.pop, .pop, .push (low a b c)]⟩

def transfer (xs ys zs : List Bool) : Config finiteProgram :=
  ⟨some (2 : Fin 3), ![xs, ys, zs]⟩
def stopped (xs ys : List Bool) : Config finiteProgram :=
  ⟨none, ![xs, ys, []]⟩

@[simp] theorem step_transfer_cons (xs ys zs : List Bool) (b bit : Bool) :
    step finiteProgram (transfer xs ys (b :: zs)) bit = transfer (b :: xs) ys zs := by
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl

@[simp] theorem step_transfer_nil (xs ys : List Bool) (bit : Bool) :
    step finiteProgram (transfer xs ys []) bit = stopped xs ys := rfl

end Addition
end MeanPayoff.WorkStack
namespace MeanPayoff
namespace SignedBits
open BinaryStack.Addition (value low carry full_adder)

structure Word where
  sign : Bool
  digits : List Bool
  deriving DecidableEq

def Word.val (w : Word) : ℤ := (value w.digits : ℤ) - if w.sign then (2 : ℤ) ^ w.digits.length else 0

def cons (b : Bool) (w : Word) : Word := ⟨w.sign, b :: w.digits⟩

def head (s : Bool) (xs : List Bool) : Bool := xs.head?.getD s

@[simp] theorem val_cons (b : Bool) (w : Word) :
    (cons b w).val = b.toNat + 2 * w.val := by
  cases w with
  | mk s xs =>
    cases s <;> simp [Word.val, cons, value, pow_succ] ; ring

theorem val_uncons (s : Bool) (xs : List Bool) :
    (Word.mk s xs).val = (head s xs).toNat + 2 * (Word.mk s xs.tail).val := by
  cases xs with
  | nil => cases s <;> norm_num [Word.val, head, value]
  | cons b bs => exact val_cons b ⟨s, bs⟩

def finalSign (a b c : Bool) : Bool := if a = b then a else !c

def add (a b c : Bool) : List Bool → List Bool → Word
  | [], [] => ⟨finalSign a b c, [low a b c]⟩
  | x :: xs, [] => cons (low x b c) (add a b (carry x b c) xs [])
  | [], y :: ys => cons (low a y c) (add a b (carry a y c) [] ys)
  | x :: xs, y :: ys => cons (low x y c) (add a b (carry x y c) xs ys)
termination_by xs ys => xs.length + ys.length

theorem add_val (a b c : Bool) (xs ys : List Bool) :
    (add a b c xs ys).val = (Word.mk a xs).val + (Word.mk b ys).val + c.toNat := by
  cases xs with
  | nil =>
    cases ys with
    | nil => cases a <;> cases b <;> cases c <;> norm_num [add, Word.val, value, low, finalSign]
    | cons y ys =>
      rw [add, val_cons, add_val]
      have hx := val_uncons a []
      have hy := val_uncons b (y :: ys)
      have hh := full_adder a y c
      simp only [head, List.head?_nil, List.head?_cons, Option.getD_none, Option.getD_some,
        List.tail_nil, List.tail_cons] at hx hy
      have hh' : ((low a y c).toNat : ℤ) + 2 * (carry a y c).toNat = a.toNat + y.toNat + c.toNat := by
        exact_mod_cast hh
      omega
  | cons x xs =>
    cases ys with
    | nil =>
      rw [add, val_cons, add_val]
      have hx := val_uncons a (x :: xs)
      have hy := val_uncons b []
      have hh := full_adder x b c
      simp only [head, List.head?_nil, List.head?_cons, Option.getD_none, Option.getD_some,
        List.tail_nil, List.tail_cons] at hx hy
      have hh' : ((low x b c).toNat : ℤ) + 2 * (carry x b c).toNat = x.toNat + b.toNat + c.toNat := by
        exact_mod_cast hh
      omega
    | cons y ys =>
      rw [add, val_cons, add_val]
      have hx := val_uncons a (x :: xs)
      have hy := val_uncons b (y :: ys)
      have hh := full_adder x y c
      simp only [head, List.head?_cons, Option.getD_some, List.tail_cons] at hx hy
      have hh' : ((low x y c).toNat : ℤ) + 2 * (carry x y c).toNat = x.toNat + y.toNat + c.toNat := by
        exact_mod_cast hh
      omega
termination_by xs.length + ys.length

theorem add_length (a b c : Bool) (xs ys : List Bool) :
    (add a b c xs ys).digits.length = max xs.length ys.length + 1 := by
  cases xs with
  | nil =>
    cases ys with
    | nil => rw [add]; rfl
    | cons y ys =>
      rw [add]
      change (add a b (carry a y c) [] ys).digits.length + 1 = _
      rw [add_length a b (carry a y c) [] ys]
      simp
  | cons x xs =>
    cases ys with
    | nil =>
      rw [add]
      change (add a b (carry x b c) xs []).digits.length + 1 = _
      rw [add_length a b (carry x b c) xs []]
      simp
    | cons y ys =>
      rw [add]
      change (add a b (carry x y c) xs ys).digits.length + 1 = _
      rw [add_length a b (carry x y c) xs ys]
      simp only [List.length_cons, Nat.succ_max_succ]
termination_by xs.length + ys.length

end SignedBits
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Arithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.WorkStack.SignedAddition
open BinaryStack (Op applyOp)
open BinaryStack.Addition (low carry)
open SignedBits (Word)

inductive Label where
  | start
  | feed (a b c : Bool)
  | transfer (s : Bool)
  | halt
  deriving DecidableEq, Fintype

noncomputable def equiv : Label ≃ Fin (Fintype.card Label) := Fintype.equivFin _
noncomputable def enc (q : Label) := equiv q
@[simp] theorem decode (q : Label) : equiv.symm (enc q) = q := equiv.symm_apply_apply _

noncomputable def program : Program where
  states := Fintype.card Label
  start := enc .start
  transition q top _ :=
    match equiv.symm q with
    | .start => some ⟨enc (.feed ((top 0).getD false) ((top 1).getD false) false), ![.pop, .pop, .keep]⟩
    | .feed a b c =>
      if top 0 = none ∧ top 1 = none then
        some ⟨enc (.transfer (SignedBits.finalSign a b c)), ![.keep, .keep, .push (low a b c)]⟩
      else
        let x := (top 0).getD a
        let y := (top 1).getD b
        some ⟨enc (.feed a b (carry x y c)), ![.pop, .pop, .push (low x y c)]⟩
    | .transfer s =>
      match top 2 with
      | none => some ⟨enc .halt, ![.push s, .keep, .keep]⟩
      | some b => some ⟨enc (.transfer s), ![.push b, .keep, .pop]⟩
    | .halt => none

noncomputable def state (q : Label) (xs ys zs : List Bool) : Config program :=
  ⟨some (enc q), ![xs, ys, zs]⟩
def stopped (xs ys : List Bool) : Config program := ⟨none, ![xs, ys, []]⟩

@[simp] theorem step_start (a b : Bool) (xs ys zs : List Bool) (bit : Bool) :
    step program (state .start (a :: xs) (b :: ys) zs) bit = state (.feed a b false) xs ys zs := by
  simp only [step, state, program, decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl

@[simp] theorem step_feed_nil (a b c : Bool) (zs : List Bool) (bit : Bool) :
    step program (state (.feed a b c) [] [] zs) bit =
      state (.transfer (SignedBits.finalSign a b c)) [] [] (low a b c :: zs) := by
  simp only [step, state, program, decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl

@[simp] theorem step_feed_left (a b c x : Bool) (xs zs : List Bool) (bit : Bool) :
    step program (state (.feed a b c) (x :: xs) [] zs) bit =
      state (.feed a b (carry x b c)) xs [] (low x b c :: zs) := by
  simp only [step, state, program, decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl

@[simp] theorem step_feed_right (a b c y : Bool) (ys zs : List Bool) (bit : Bool) :
    step program (state (.feed a b c) [] (y :: ys) zs) bit =
      state (.feed a b (carry a y c)) [] ys (low a y c :: zs) := by
  simp only [step, state, program, decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl

@[simp] theorem step_feed_both (a b c x y : Bool) (xs ys zs : List Bool) (bit : Bool) :
    step program (state (.feed a b c) (x :: xs) (y :: ys) zs) bit =
      state (.feed a b (carry x y c)) xs ys (low x y c :: zs) := by
  simp only [step, state, program, decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl

@[simp] theorem step_transfer_cons (s b : Bool) (xs ys zs : List Bool) (bit : Bool) :
    step program (state (.transfer s) xs ys (b :: zs)) bit = state (.transfer s) (b :: xs) ys zs := by
  simp only [step, state, program, decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl

@[simp] theorem step_transfer_nil (s : Bool) (xs ys : List Bool) (bit : Bool) :
    step program (state (.transfer s) xs ys []) bit = state .halt (s :: xs) ys [] := by
  simp only [step, state, program, decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl

@[simp] theorem step_halt (xs ys : List Bool) (bit : Bool) :
    step program (state .halt xs ys []) bit = stopped xs ys := by
  simp only [step, state, program, decode]; rfl

theorem feed_runs (a b c : Bool) (xs ys zs : List Bool) (bits : ℕ → Bool) :
    advance program bits (state (.feed a b c) xs ys zs) (max xs.length ys.length + 1) =
      state (.transfer (SignedBits.add a b c xs ys).sign) [] []
        ((SignedBits.add a b c xs ys).digits.reverse ++ zs) := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp [advance, SignedBits.add]
    | cons y ys =>
      rw [show max [].length (y :: ys).length + 1 = max [].length ys.length + 1 + 1 by simp,
        advance_front, step_feed_right, feed_runs]
      simp only [SignedBits.add, SignedBits.cons, List.reverse_cons,
        List.append_assoc, List.singleton_append]
  | cons x xs =>
    cases ys with
    | nil =>
      rw [show max (x :: xs).length [].length + 1 = max xs.length [].length + 1 + 1 by simp,
        advance_front, step_feed_left, feed_runs]
      simp only [SignedBits.add, SignedBits.cons, List.reverse_cons,
        List.append_assoc, List.singleton_append]
    | cons y ys =>
      rw [show max (x :: xs).length (y :: ys).length + 1 = max xs.length ys.length + 1 + 1 by simp,
        advance_front, step_feed_both, feed_runs]
      simp only [SignedBits.add, SignedBits.cons, List.reverse_cons,
        List.append_assoc, List.singleton_append]
termination_by xs.length + ys.length

theorem transfer_runs (s : Bool) (xs ys zs : List Bool) (bits : ℕ → Bool) :
    advance program bits (state (.transfer s) xs ys zs) (zs.length + 2) =
      stopped (s :: (zs.reverse ++ xs)) ys := by
  induction zs generalizing xs bits with
  | nil => simp [advance]
  | cons b zs ih =>
    rw [show (b :: zs).length + 2 = zs.length + 2 + 1 by simp,
      advance_front, step_transfer_cons, ih]
    simp [List.reverse_cons, List.append_assoc]

theorem program_adds (a b : Bool) (xs ys : List Bool) (bits : ℕ → Bool) :
    advance program bits (state .start (a :: xs) (b :: ys) [])
      (2 * max xs.length ys.length + 5) =
      stopped ((SignedBits.add a b false xs ys).sign ::
        (SignedBits.add a b false xs ys).digits) [] := by
  rw [show 2 * max xs.length ys.length + 5 = (2 * max xs.length ys.length + 4) + 1 by omega,
    advance_front, step_start]
  rw [show 2 * max xs.length ys.length + 4 = (max xs.length ys.length + 1) +
    ((SignedBits.add a b false xs ys).digits.length + 2) by rw [SignedBits.add_length]; omega,
    advance_add, feed_runs]
  simp only [List.append_nil]
  have h := transfer_runs (SignedBits.add a b false xs ys).sign [] []
    (SignedBits.add a b false xs ys).digits.reverse
    (fun j => bits (max xs.length ys.length + 1 + j + 1))
  simpa only [List.length_reverse, List.reverse_reverse, List.append_nil] using h

end MeanPayoff.WorkStack.SignedAddition
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Registers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace RegisterBits
open BinaryStack (Op applyOp)

structure Act (s : ℕ) where
  next : Fin s
  work : Op
  emit : Option Bool
structure Program (K : ℕ) where
  states : ℕ
  start : Fin states
  read : Fin states → Fin K
  transition : Fin states → Option Bool → Bool → Option (Act states)
structure Config {K : ℕ} (P : Program K) where
  control : Option (Fin P.states)
  stack : Fin K → List Bool
  output : List Bool

def step {K : ℕ} (P : Program K) (c : Config P) (bit : Bool) : Config P :=
  match c.control with
  | none => c
  | some q =>
    match P.transition q (c.stack (P.read q)).head? bit with
    | none => {c with control := none}
    | some a => ⟨some a.next, Function.update c.stack (P.read q) (applyOp a.work (c.stack (P.read q))),
        c.output ++ a.emit.toList⟩

def encode : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: encode bs

def encodeAll : List (List Bool) → List Bool
  | [] => []
  | bs :: bss => encode bs ++ encodeAll bss

@[simp] theorem encode_length (bs : List Bool) : (encode bs).length = 2 * bs.length + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [encode, ih]; omega

@[simp] theorem encodeAll_append (a b : List (List Bool)) :
    encodeAll (a ++ b) = encodeAll a ++ encodeAll b := by
  induction a with
  | nil => rfl
  | cons xs a ih => simp [encodeAll, ih, List.append_assoc]

@[simp] theorem encodeAll_length (bss : List (List Bool)) :
    (encodeAll bss).length = 2 * (bss.map List.length).sum + bss.length := by
  induction bss with
  | nil => rfl
  | cons bs bss ih => simp only [encodeAll, List.length_append, encode_length, List.map_cons,
      List.sum_cons, List.length_cons, ih]; omega

namespace Compile
inductive Label (s K : ℕ) where
  | initMove
  | initPad (left : Fin (K + 1))
  | initRestore
  | initTag
  | source (q : Fin s)
  | seek (q : Fin s) (bit : Bool) (left : Fin (K + 1))
  | payload (q : Fin s) (bit : Bool)
  | skip (q : Fin s) (bit : Bool) (left : Fin (K + 1))
  | pushOne (dest : Option (Fin s)) (b : Bool)
  | pushTwo (dest : Option (Fin s)) (b c : Bool)
  | restore (dest : Option (Fin s))
  | halt
  deriving DecidableEq, Fintype

noncomputable def equiv (s K : ℕ) : Label s K ≃ Fin (Fintype.card (Label s K)) := Fintype.equivFin _
noncomputable def enc {s K : ℕ} (q : Label s K) := equiv s K q
@[simp] theorem decode {s K : ℕ} (q : Label s K) : (equiv s K).symm (enc q) = q :=
  (equiv s K).symm_apply_apply _

noncomputable def dispatch {K : ℕ} (P : Program K) (q : Fin P.states) (bit : Bool)
    (top : Option Bool) : BinaryStack.Act (Fintype.card (Label P.states K)) :=
  let instruction := P.transition q top bit
  let dest := instruction.map Act.next
  let op := instruction.map Act.work |>.getD .keep
  let emit := instruction.bind Act.emit
  match top, op with
  | none, .keep | none, .pop => ⟨enc (.restore dest), ![.keep, .keep], emit⟩
  | none, .push b => ⟨enc (.pushOne dest true), ![.push b, .keep], emit⟩
  | some _, .keep => ⟨enc (.restore dest), ![.push true, .keep], emit⟩
  | some _, .pop => ⟨enc (.restore dest), ![.pop, .keep], emit⟩
  | some _, .push b => ⟨enc (.pushTwo dest b true), ![.push true, .keep], emit⟩

noncomputable def program {K : ℕ} (P : Program K) : BinaryStack.Program where
  states := Fintype.card (Label P.states K)
  start := enc .initMove
  transition q top bit :=
    match (equiv P.states K).symm q with
    | .initMove =>
      match top 0 with
      | some b => some ⟨enc .initMove, ![.pop, .push b], none⟩
      | none => some ⟨enc (.initPad ⟨K, by omega⟩), ![.keep, .keep], none⟩
    | .initPad left =>
      if h : left.val = 0 then some ⟨enc .initRestore, ![.keep, .keep], none⟩
      else some ⟨enc (.initPad ⟨left.val - 1, by omega⟩), ![.push false, .keep], none⟩
    | .initRestore =>
      match top 1 with
      | some b => some ⟨enc .initTag, ![.push b, .pop], none⟩
      | none => some ⟨enc (.source P.start), ![.keep, .keep], none⟩
    | .initTag => some ⟨enc .initRestore, ![.push true, .keep], none⟩
    | .source q => some ⟨enc (.seek q bit ⟨(P.read q).val, by omega⟩), ![.keep, .keep], none⟩
    | .seek q coin left =>
      if h : left.val = 0 then
        match top 0 with
        | some false => some (dispatch P q coin none)
        | some true => some ⟨enc (.payload q coin), ![.pop, .keep], none⟩
        | none => some ⟨enc .halt, ![.keep, .keep], none⟩
      else
        match top 0 with
        | some false => some ⟨enc (.seek q coin ⟨left.val - 1, by omega⟩), ![.pop, .push false], none⟩
        | some true => some ⟨enc (.skip q coin left), ![.pop, .push true], none⟩
        | none => some ⟨enc .halt, ![.keep, .keep], none⟩
    | .skip q coin left =>
      match top 0 with
      | some b => some ⟨enc (.seek q coin left), ![.pop, .push b], none⟩
      | none => some ⟨enc .halt, ![.keep, .keep], none⟩
    | .payload q coin =>
      match top 0 with
      | some b => some (dispatch P q coin (some b))
      | none => some ⟨enc .halt, ![.keep, .keep], none⟩
    | .pushOne dest b => some ⟨enc (.restore dest), ![.push b, .keep], none⟩
    | .pushTwo dest b c => some ⟨enc (.pushOne dest c), ![.push b, .keep], none⟩
    | .restore dest =>
      match top 1 with
      | some b => some ⟨enc (.restore dest), ![.push b, .pop], none⟩
      | none => dest.map fun q => ⟨enc (.source q), ![.keep, .keep], none⟩
    | .halt => none

end Compile
end RegisterBits
end MeanPayoff

namespace MeanPayoff.RegisterBits.Compile
open BinaryStack (advance)

noncomputable def cfg {K : ℕ} (P : Program K) (q : Label P.states K)
    (xs ys out : List Bool) : BinaryStack.Config (program P) :=
  ⟨some (enc q), ![xs, ys], out⟩

@[simp] theorem step_skip {K : ℕ} (P : Program K) (q : Fin P.states)
    (coin bit b : Bool) (left : Fin (K + 1)) (xs ys out : List Bool) :
    BinaryStack.step (program P) (cfg P (.skip q coin left) (b :: xs) ys out) bit =
      cfg P (.seek q coin left) xs (b :: ys) out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, BinaryStack.applyOp]
  · simp [BinaryStack.step, cfg, program]

@[simp] theorem step_seek_tag {K : ℕ} (P : Program K) (q : Fin P.states)
    (coin bit : Bool) (left : Fin (K + 1)) (h : left.val ≠ 0) (xs ys out : List Bool) :
    BinaryStack.step (program P) (cfg P (.seek q coin left) (true :: xs) ys out) bit =
      cfg P (.skip q coin left) xs (true :: ys) out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program, h]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, h, BinaryStack.applyOp]
  · simp [BinaryStack.step, cfg, program, h]

@[simp] theorem step_seek_delim {K : ℕ} (P : Program K) (q : Fin P.states)
    (coin bit : Bool) (left : Fin (K + 1)) (h : left.val ≠ 0) (xs ys out : List Bool) :
    BinaryStack.step (program P) (cfg P (.seek q coin left) (false :: xs) ys out) bit =
      cfg P (.seek q coin ⟨left.val - 1, by omega⟩) xs (false :: ys) out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program, h]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, h, BinaryStack.applyOp]
  · simp [BinaryStack.step, cfg, program, h]

@[simp] theorem step_restore_some {K : ℕ} (P : Program K) (dest : Option (Fin P.states))
    (bit b : Bool) (xs ys out : List Bool) :
    BinaryStack.step (program P) (cfg P (.restore dest) xs (b :: ys) out) bit =
      cfg P (.restore dest) (b :: xs) ys out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, BinaryStack.applyOp]
  · simp [BinaryStack.step, cfg, program]

noncomputable def sourceCfg {K : ℕ} (P : Program K) (dest : Option (Fin P.states))
    (xs ys out : List Bool) : BinaryStack.Config (program P) :=
  ⟨dest.map (fun q => enc (.source q)), ![xs, ys], out⟩

@[simp] theorem step_restore_nil {K : ℕ} (P : Program K) (dest : Option (Fin P.states))
    (bit : Bool) (xs out : List Bool) :
    BinaryStack.step (program P) (cfg P (.restore dest) xs [] out) bit =
      sourceCfg P dest xs [] out := by
  cases dest <;> apply BinaryStack.Config.ext
  all_goals first
    | solve | simp [BinaryStack.step, cfg, sourceCfg, program]
    | solve | funext i; fin_cases i <;> simp [BinaryStack.step, cfg, sourceCfg, program, BinaryStack.applyOp]

end MeanPayoff.RegisterBits.Compile

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Instructions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.RegisterBits.Compile
open BinaryStack (advance applyOp)

@[simp] theorem step_source {K : ℕ} (P : Program K) (q : Fin P.states)
    (bit : Bool) (xs ys out : List Bool) :
    BinaryStack.step (program P) (cfg P (.source q) xs ys out) bit =
      cfg P (.seek q bit ⟨(P.read q).val, by omega⟩) xs ys out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, applyOp]
  · simp [BinaryStack.step, cfg, program]

end MeanPayoff.RegisterBits.Compile

namespace MeanPayoff.RegisterBits

@[ext] theorem Config.ext {K : ℕ} {P : Program K} {a b : Config P}
    (hc : a.control = b.control) (hs : a.stack = b.stack) (ho : a.output = b.output) : a = b := by
  cases a; cases b; simp_all

def storeSize {K : ℕ} (s : Fin K → List Bool) : ℕ := ∑ i, (s i).length

def advance {K : ℕ} (P : Program K) (bits : ℕ → Bool) (c : Config P) : ℕ → Config P
  | 0 => c
  | n + 1 => step P (advance P bits c n) (bits n)

namespace Compile

@[simp] theorem encoded_size {K : ℕ} (s : Fin K → List Bool) :
    (encodeAll (List.ofFn s)).length = 2 * storeSize s + K := by
  simp [storeSize, List.map_ofFn, List.sum_ofFn]

end Compile


 theorem update_size {K : ℕ} (s : Fin K → List Bool) (k : Fin K) (xs : List Bool) :
    storeSize (Function.update s k xs) + (s k).length = storeSize s + xs.length := by
  have he : (fun i => ((Function.update s k xs) i).length) =
      Function.update (fun i => (s i).length) k xs.length := by
    funext i
    by_cases h : i = k <;> simp [h]
  have h₁ := Finset.sum_update_of_mem (Finset.mem_univ k) (fun i => (s i).length) xs.length
  have h₂ := Finset.sum_update_of_mem (Finset.mem_univ k) (fun i => (s i).length) (s k).length
  simp only [Function.update_eq_self] at h₂
  unfold storeSize
  rw [he, h₁, h₂]
  omega

 theorem op_size (op : BinaryStack.Op) (xs : List Bool) :
    (BinaryStack.applyOp op xs).length ≤ xs.length + 1 := by
  cases op <;> cases xs <;> simp [BinaryStack.applyOp] ; omega

theorem step_size {K : ℕ} (P : Program K) (c : Config P) (bit : Bool) :
    storeSize (step P c bit).stack ≤ storeSize c.stack + 1 := by
  unfold step
  cases hc : c.control with
  | none => simp
  | some q =>
    cases he : P.transition q (c.stack (P.read q)).head? bit with
    | none => simp [he]
    | some a =>
      simp only [he]
      have hs := update_size c.stack (P.read q) (BinaryStack.applyOp a.work (c.stack (P.read q)))
      have ho := op_size a.work (c.stack (P.read q))
      omega

 theorem advance_size {K : ℕ} (P : Program K) (c : Config P) (bits : ℕ → Bool) (n : ℕ) :
    storeSize (advance P bits c n).stack ≤ storeSize c.stack + n := by
  induction n with
  | zero => simp [advance]
  | succ n ih =>
    have h := step_size P (advance P bits c n) (bits n)
    simp only [advance]
    omega

namespace Compile
open BinaryStack (advance applyOp)

@[simp] theorem init_move_step {K : ℕ} (P : Program K) (xs ys out : List Bool) (b bit : Bool) :
    BinaryStack.step (program P) (cfg P .initMove (b :: xs) ys out) bit =
      cfg P .initMove xs (b :: ys) out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, applyOp]
  · simp [BinaryStack.step, cfg, program]

@[simp] theorem init_move_empty {K : ℕ} (P : Program K) (ys out : List Bool) (bit : Bool) :
    BinaryStack.step (program P) (cfg P .initMove [] ys out) bit =
      cfg P (.initPad ⟨K, by omega⟩) [] ys out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, applyOp]
  · simp [BinaryStack.step, cfg, program]

@[simp] theorem init_pad_zero {K : ℕ} (P : Program K) (xs ys out : List Bool) (bit : Bool) :
    BinaryStack.step (program P) (cfg P (.initPad 0) xs ys out) bit =
      cfg P .initRestore xs ys out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, applyOp]
  · simp [BinaryStack.step, cfg, program]

@[simp] theorem init_pad_succ {K : ℕ} (P : Program K) (n : ℕ) (hn : n + 1 < K + 1)
    (xs ys out : List Bool) (bit : Bool) :
    BinaryStack.step (program P) (cfg P (.initPad ⟨n + 1, hn⟩) xs ys out) bit =
      cfg P (.initPad ⟨n, by omega⟩) (false :: xs) ys out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, applyOp]
  · simp [BinaryStack.step, cfg, program]

@[simp] theorem init_restore_step {K : ℕ} (P : Program K) (xs ys out : List Bool) (b bit : Bool) :
    BinaryStack.step (program P) (cfg P .initRestore xs (b :: ys) out) bit =
      cfg P .initTag (b :: xs) ys out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, applyOp]
  · simp [BinaryStack.step, cfg, program]

@[simp] theorem init_tag_step {K : ℕ} (P : Program K) (xs ys out : List Bool) (bit : Bool) :
    BinaryStack.step (program P) (cfg P .initTag xs ys out) bit =
      cfg P .initRestore (true :: xs) ys out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, applyOp]
  · simp [BinaryStack.step, cfg, program]

@[simp] theorem init_restore_empty {K : ℕ} (P : Program K) (xs out : List Bool) (bit : Bool) :
    BinaryStack.step (program P) (cfg P .initRestore xs [] out) bit =
      cfg P (.source P.start) xs [] out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, applyOp]
  · simp [BinaryStack.step, cfg, program]

end Compile
end MeanPayoff.RegisterBits
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_FiniteTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.BinaryStack
@[simp] theorem advance_initial (P : Program) (code : List Bool) (bits : ℕ → Bool) (n : ℕ) :
    advance P bits (initial P code) n = run P code bits n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [advance, run, ih]
end MeanPayoff.BinaryStack

namespace MeanPayoff.RandomTree

def wait {α : Type} : ℕ → RandomTree α → RandomTree α
  | 0, t => t
  | n + 1, t => .coin (wait n t) (wait n t)

@[simp] theorem expect_wait {α : Type} (n : ℕ) (t : RandomTree α) (f : α → ℚ) :
    (wait n t).expect f = t.expect f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [wait, expect, ih]; ring

@[simp] theorem depth_wait {α : Type} (n : ℕ) (t : RandomTree α) :
    (wait n t).bitDepth = n + t.bitDepth := by
  induction n with
  | zero => simp [wait]
  | succ n ih => simp [wait, bitDepth, ih]; omega

@[simp] theorem all_wait {α : Type} (n : ℕ) (t : RandomTree α) (Q : α → Prop) :
    (wait n t).All Q ↔ t.All Q := by
  induction n with
  | zero => rfl
  | succ n ih => simp [wait, All, ih]

@[simp] theorem consume_wait {α : Type} (n : ℕ) (t : RandomTree α) (bits : ℕ → Bool) (pos : ℕ) :
    (wait n t).consume bits pos = t.consume bits (pos + n) := by
  induction n generalizing pos with
  | zero => simp [wait]
  | succ n ih => simp only [wait, consume, ih]; split <;> congr 1 <;> omega

end MeanPayoff.RandomTree
namespace MeanPayoff
namespace BinaryData

inductive Data where
  | nil
  | pair (left right : Data)
  deriving DecidableEq

def encode : Data → List Bool
  | .nil => [false]
  | .pair a b => true :: encode a ++ encode b

@[simp] theorem encode_nonempty (a : Data) : encode a ≠ [] := by cases a <;> simp [encode]
@[simp] theorem encode_positive (a : Data) : 0 < (encode a).length := List.length_pos_iff.mpr (encode_nonempty a)

namespace Take
open RegisterBits
open BinaryStack (Op applyOp)

inductive Label where
  | start | check | read | put (b : Bool) | depth (b : Bool)
  | restore | restorePut (b : Bool)
  deriving DecidableEq, Fintype
noncomputable def equiv : Label ≃ Fin (Fintype.card Label) := Fintype.equivFin _
noncomputable def enc (q : Label) := equiv q
@[simp] theorem dec (q : Label) : equiv.symm (enc q) = q := equiv.symm_apply_apply q

noncomputable def program : Program 4 where
  states := Fintype.card Label
  start := enc .start
  read q := match equiv.symm q with
    | .start | .check | .depth _ => 3
    | .read => 0
    | .put _ | .restore => 2
    | .restorePut _ => 1
  transition q top _ := match equiv.symm q with
    | .start => some ⟨enc .check, .push true, none⟩
    | .check => some ⟨enc (if top.isSome then .read else .restore), .keep, none⟩
    | .read => top.map fun b => ⟨enc (.put b), .pop, none⟩
    | .put b => some ⟨enc (.depth b), .push b, none⟩
    | .depth b => some ⟨enc .check, if b then .push true else .pop, none⟩
    | .restore => top.map fun b => ⟨enc (.restorePut b), .pop, none⟩
    | .restorePut b => some ⟨enc .restore, .push b, none⟩

noncomputable def cfg (q : Label) (xs ys zs ds out : List Bool) : Config program :=
  ⟨some (enc q), ![xs, ys, zs, ds], out⟩
noncomputable def stopped (xs ys zs ds out : List Bool) : Config program :=
  ⟨none, ![xs, ys, zs, ds], out⟩

@[ext] theorem config_ext {K : ℕ} {P : Program K} {a b : Config P}
    (hc : a.control = b.control) (hs : a.stack = b.stack) (ho : a.output = b.output) : a = b := by
  cases a; cases b; simp_all

theorem advance_front {K : ℕ} (P : Program K) (bits : ℕ → Bool) (c : Config P) (n : ℕ) :
    advance P bits c (n + 1) = advance P (fun j => bits (j + 1)) (RegisterBits.step P c (bits 0)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change RegisterBits.step P (advance P bits c (n + 1)) (bits (n + 1)) = _
    rw [ih]
    rfl

theorem advance_add {K : ℕ} (P : Program K) (bits : ℕ → Bool) (c : Config P) (a b : ℕ) :
    advance P bits c (a + b) = advance P (fun j => bits (a + j)) (advance P bits c a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change RegisterBits.step P (advance P bits c (a + b)) (bits (a + b)) = _
    rw [ih]
    rfl

@[simp] theorem start_step (xs ys zs ds out : List Bool) (bit : Bool) :
    RegisterBits.step program (cfg .start xs ys zs ds out) bit = cfg .check xs ys zs (true :: ds) out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem check_step (xs ys zs ds out : List Bool) (a bit : Bool) :
    RegisterBits.step program (cfg .check xs ys zs (a :: ds) out) bit = cfg .read xs ys zs (a :: ds) out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem read_step (xs ys zs ds out : List Bool) (b bit : Bool) :
    RegisterBits.step program (cfg .read (b :: xs) ys zs ds out) bit = cfg (.put b) xs ys zs ds out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem put_step (xs ys zs ds out : List Bool) (b bit : Bool) :
    RegisterBits.step program (cfg (.put b) xs ys zs ds out) bit = cfg (.depth b) xs ys (b :: zs) ds out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem depth_false (xs ys zs ds out : List Bool) (a bit : Bool) :
    RegisterBits.step program (cfg (.depth false) xs ys zs (a :: ds) out) bit = cfg .check xs ys zs ds out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem depth_true (xs ys zs ds out : List Bool) (bit : Bool) :
    RegisterBits.step program (cfg (.depth true) xs ys zs ds out) bit = cfg .check xs ys zs (true :: ds) out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

theorem scan_nil (xs ys zs ds out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .check (false :: xs) ys zs (true :: ds) out) 4 =
      cfg .check xs ys (false :: zs) ds out := by
  simp [advance, check_step, read_step, put_step, depth_false]

theorem scan_pair (xs ys zs ds out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .check (true :: xs) ys zs (true :: ds) out) 4 =
      cfg .check xs ys (true :: zs) (true :: true :: ds) out := by
  simp [advance, check_step, read_step, put_step, depth_true]

theorem scan (t : Data) (xs ys zs ds out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .check (encode t ++ xs) ys zs (true :: ds) out)
      (4 * (encode t).length) = cfg .check xs ys ((encode t).reverse ++ zs) ds out := by
  induction t generalizing xs zs ds bits with
  | nil => simpa [encode] using scan_nil xs ys zs ds out bits
  | pair a b ia ib =>
    simp only [encode, List.length_cons, List.length_append, List.cons_append]
    have hn : 4 * (1 + (encode a).length + (encode b).length) =
        4 + 4 * (encode a).length + 4 * (encode b).length := by omega
    rw [show 4 * ((encode a).length + (encode b).length + 1) =
      4 + 4 * (encode a).length + 4 * (encode b).length by omega,
      advance_add (a := 4 + 4 * (encode a).length) (b := 4 * (encode b).length),
      advance_add (a := 4), scan_pair, List.append_assoc, ia, ib]
    simp [List.reverse_cons, List.reverse_append, List.append_assoc]

@[simp] theorem check_empty (xs ys zs out : List Bool) (bit : Bool) :
    RegisterBits.step program (cfg .check xs ys zs [] out) bit = cfg .restore xs ys zs [] out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem restore_step (xs ys zs ds out : List Bool) (b bit : Bool) :
    RegisterBits.step program (cfg .restore xs ys (b :: zs) ds out) bit = cfg (.restorePut b) xs ys zs ds out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem restore_put (xs ys zs ds out : List Bool) (b bit : Bool) :
    RegisterBits.step program (cfg (.restorePut b) xs ys zs ds out) bit = cfg .restore xs (b :: ys) zs ds out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem restore_empty (xs ys ds out : List Bool) (bit : Bool) :
    RegisterBits.step program (cfg .restore xs ys [] ds out) bit = stopped xs ys [] ds out := by
  simp [RegisterBits.step, program, cfg, stopped]

theorem restore_all (xs ys zs ds out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .restore xs ys zs ds out) (2 * zs.length + 1) =
      stopped xs (zs.reverse ++ ys) [] ds out := by
  induction zs generalizing ys bits with
  | nil => simp [advance, restore_empty]
  | cons b zs ih =>
    rw [List.length_cons, show 2 * (zs.length + 1) + 1 = (2 * zs.length + 1 + 1) + 1 by omega,
      advance_front, restore_step, advance_front, restore_put, ih]
    simp [List.reverse_cons, List.append_assoc]

theorem takes (t : Data) (xs ys out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .start (encode t ++ xs) ys [] [] out)
      (6 * (encode t).length + 3) = stopped xs (encode t ++ ys) [] [] out := by
  rw [show 6 * (encode t).length + 3 = (4 * (encode t).length + 1 + (2 * (encode t).length + 1)) + 1 by omega,
    advance_front, start_step, advance_add (a := 4 * (encode t).length + 1)]
  have hs (bits : ℕ → Bool) : advance program bits (cfg .check (encode t ++ xs) ys [] [true] out)
      (4 * (encode t).length + 1) = cfg .restore xs ys (encode t).reverse [] out := by
    rw [advance, scan, List.append_nil, check_empty]
  rw [hs]
  simpa using restore_all xs ys (encode t).reverse [] out (fun j => bits (4 * (encode t).length + 1 + j + 1))

end Take
end BinaryData
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_TreeCopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.RegisterBits
open BinaryStack (applyOp)

def rename {K N : ℕ} (P : Program K) (f : Fin K → Fin N) : Program N where
  states := P.states
  start := P.start
  read q := f (P.read q)
  transition := P.transition

noncomputable def install {K N : ℕ} (f : Fin K → Fin N)
    (ambient : Fin N → List Bool) (s : Fin K → List Bool) : Fin N → List Bool :=
  fun j => if h : ∃ i, f i = j then s (Classical.choose h) else ambient j

@[simp] theorem install_at {K N : ℕ} (f : Fin K → Fin N) (hf : Function.Injective f)
    (ambient : Fin N → List Bool) (s : Fin K → List Bool) (i : Fin K) :
    install f ambient s (f i) = s i := by
  unfold install
  split_ifs with h
  · rw [hf (Classical.choose_spec h)]
  · exact False.elim (h ⟨i, rfl⟩)

@[simp] theorem install_off {K N : ℕ} (f : Fin K → Fin N)
    (ambient : Fin N → List Bool) (s : Fin K → List Bool) (j : Fin N)
    (hj : ∀ i, f i ≠ j) : install f ambient s j = ambient j := by
  simp [install, not_exists.mpr hj]

theorem install_update {K N : ℕ} (f : Fin K → Fin N) (hf : Function.Injective f)
    (ambient : Fin N → List Bool) (s : Fin K → List Bool) (i : Fin K) (xs : List Bool) :
    install f ambient (Function.update s i xs) = Function.update (install f ambient s) (f i) xs := by
  funext j
  by_cases h : ∃ k, f k = j
  · obtain ⟨k, rfl⟩ := h
    simp only [install_at f hf]
    by_cases hi : k = i
    · subst k; simp
    · have hfi : f k ≠ f i := fun he => hi (hf he)
      simp [Function.update_of_ne hi, Function.update_of_ne hfi, install_at f hf]
  · have hi : j ≠ f i := by rintro rfl; exact h ⟨i, rfl⟩
    simp only [Function.update_of_ne hi]
    simp [install, h]

noncomputable def renamed {K N : ℕ} (P : Program K) (f : Fin K → Fin N)
    (ambient : Fin N → List Bool) (c : Config P) : Config (rename P f) :=
  ⟨c.control, install f ambient c.stack, c.output⟩

theorem rename_step {K N : ℕ} (P : Program K) (f : Fin K → Fin N)
    (hf : Function.Injective f) (ambient : Fin N → List Bool) (c : Config P) (bit : Bool) :
    RegisterBits.step (rename P f) (renamed P f ambient c) bit =
      renamed P f ambient (RegisterBits.step P c bit) := by
  cases hc : c.control with
  | none => simp [RegisterBits.step, renamed, hc]
  | some q =>
    simp only [RegisterBits.step, renamed, hc, rename, install_at f hf]
    cases ha : P.transition q (c.stack (P.read q)).head? bit with
    | none => rfl
    | some a => simp only [install_update f hf]

theorem rename_advance {K N : ℕ} (P : Program K) (f : Fin K → Fin N)
    (hf : Function.Injective f) (ambient : Fin N → List Bool) (c : Config P)
    (bits : ℕ → Bool) (n : ℕ) :
    advance (rename P f) bits (renamed P f ambient c) n =
      renamed P f ambient (advance P bits c n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [advance, ih, rename_step P f hf]

@[simp] theorem halted_step {K : ℕ} (P : Program K) (c : Config P) (h : c.control = none)
    (bit : Bool) : RegisterBits.step P c bit = c := by simp [RegisterBits.step, h]

theorem advance_halted {K : ℕ} (P : Program K) (c : Config P) (h : c.control = none)
    (bits : ℕ → Bool) (n : ℕ) : advance P bits c n = c := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [advance, ih, halted_step P c h]

theorem first_termination {K : ℕ} (P : Program K) (c : Config P)
    (bits : ℕ → Bool) (N : ℕ) (h : (advance P bits c N).control = none) :
    ∃ t ≤ N, (advance P bits c t).control = none ∧
      (∀ j < t, (advance P bits c j).control ≠ none) ∧
      advance P bits c t = advance P bits c N := by
  have hex : ∃ j, (advance P bits c j).control = none := ⟨N, h⟩
  let t := Nat.find hex
  have ht : (advance P bits c t).control = none := Nat.find_spec hex
  have hb : t ≤ N := Nat.find_min' hex h
  refine ⟨t, hb, ht, ?_, ?_⟩
  · intro j hj; exact Nat.find_min hex hj
  · rw [show N = t + (N - t) by omega, BinaryData.Take.advance_add, advance_halted P _ ht]

namespace Flow

structure Program (K : ℕ) where
  nodes : ℕ
  start : Fin nodes
  block : Fin nodes → RegisterBits.Program K
  read : Fin nodes → Fin K
  next : Fin nodes → Option Bool → Bool → Option (Act nodes)

abbrev Labels {K : ℕ} (P : Program K) :=
  (Σ q : Fin P.nodes, Fin (P.block q).states) ⊕ Fin P.nodes
noncomputable def equiv {K : ℕ} (P : Program K) : Labels P ≃ Fin (Fintype.card (Labels P)) :=
  Fintype.equivFin _
noncomputable def inner {K : ℕ} (P : Program K) (q : Fin P.nodes) (p : Fin (P.block q).states) :=
  equiv P (.inl ⟨q, p⟩)
noncomputable def boundary {K : ℕ} (P : Program K) (q : Fin P.nodes) := equiv P (.inr q)
@[simp] theorem dec_inner {K : ℕ} (P : Program K) (q : Fin P.nodes) (p : Fin (P.block q).states) :
    (equiv P).symm (inner P q p) = .inl ⟨q, p⟩ := (equiv P).symm_apply_apply _
@[simp] theorem dec_boundary {K : ℕ} (P : Program K) (q : Fin P.nodes) :
    (equiv P).symm (boundary P q) = .inr q := (equiv P).symm_apply_apply _

noncomputable def compile {K : ℕ} (P : Program K) : RegisterBits.Program K where
  states := Fintype.card (Labels P)
  start := inner P P.start (P.block P.start).start
  read q := match (equiv P).symm q with
    | .inl ⟨p, q⟩ => (P.block p).read q
    | .inr p => P.read p
  transition q top bit := match (equiv P).symm q with
    | .inl ⟨p, q⟩ => some (match (P.block p).transition q top bit with
        | none => ⟨boundary P p, .keep, none⟩
        | some a => ⟨inner P p a.next, a.work, a.emit⟩)
    | .inr p => (P.next p top bit).map fun a =>
        ⟨inner P a.next (P.block a.next).start, a.work, a.emit⟩

noncomputable def embed {K : ℕ} (P : Program K) (p : Fin P.nodes) (c : Config (P.block p)) :
    Config (compile P) :=
  ⟨some (c.control.elim (boundary P p) (inner P p)), c.stack, c.output⟩

noncomputable def state {K : ℕ} (P : Program K) (p : Fin P.nodes)
    (s : Fin K → List Bool) (out : List Bool) : Config (compile P) :=
  ⟨some (inner P p (P.block p).start), s, out⟩

noncomputable def edge {K : ℕ} (P : Program K) (p : Fin P.nodes)
    (s : Fin K → List Bool) (out : List Bool) : Config (compile P) :=
  ⟨some (boundary P p), s, out⟩

theorem step_inner {K : ℕ} (P : Program K) (p : Fin P.nodes) (c : Config (P.block p))
    (hc : c.control ≠ none) (bit : Bool) :
    RegisterBits.step (compile P) (embed P p c) bit =
      embed P p (RegisterBits.step (P.block p) c bit) := by
  cases he : c.control with
  | none => exact False.elim (hc he)
  | some q =>
    simp only [RegisterBits.step, embed, he, Option.elim_some, compile, dec_inner]
    cases ha : (P.block p).transition q (c.stack ((P.block p).read q)).head? bit with
    | none =>
      apply BinaryData.Take.config_ext
      · rfl
      · funext k; simp [applyOp]
      · simp
    | some a => rfl

theorem advance_inner {K : ℕ} (P : Program K) (p : Fin P.nodes) (c : Config (P.block p))
    (bits : ℕ → Bool) (n : ℕ)
    (hc : ∀ j < n, (advance (P.block p) bits c j).control ≠ none) :
    advance (compile P) bits (embed P p c) n = embed P p (advance (P.block p) bits c n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change RegisterBits.step (compile P) (advance (compile P) bits (embed P p c) n) (bits n) = _
    rw [ih (fun j hj => hc j (by omega)), step_inner P p _ (hc n (by omega))]
    rfl

theorem macro_runs {K : ℕ} (P : Program K) (p : Fin P.nodes) (s : Fin K → List Bool)
    (out : List Bool) (bits : ℕ → Bool) (N : ℕ)
    (h : (advance (P.block p) bits ⟨some (P.block p).start, s, out⟩ N).control = none) :
    ∃ t ≤ N, advance (compile P) bits (state P p s out) t =
      edge P p (advance (P.block p) bits ⟨some (P.block p).start, s, out⟩ N).stack
        (advance (P.block p) bits ⟨some (P.block p).start, s, out⟩ N).output := by
  obtain ⟨t, ht, hh, hn, he⟩ := first_termination (P.block p) ⟨some _, s, out⟩ bits N h
  refine ⟨t, ht, ?_⟩
  change advance (compile P) bits (embed P p ⟨some _, s, out⟩) t = _
  rw [advance_inner P p _ bits t hn, he]
  simp only [embed, h, edge]
  rfl

theorem step_boundary {K : ℕ} (P : Program K) (p : Fin P.nodes) (s : Fin K → List Bool)
    (out : List Bool) (bit : Bool) :
    RegisterBits.step (compile P) (edge P p s out) bit =
      match P.next p (s (P.read p)).head? bit with
      | none => ⟨none, s, out⟩
      | some a => state P a.next (Function.update s (P.read p) (applyOp a.work (s (P.read p))))
          (out ++ a.emit.toList) := by
  simp only [RegisterBits.step, edge, compile, dec_boundary]
  cases P.next p (s (P.read p)).head? bit <;> rfl

end Flow
end MeanPayoff.RegisterBits
namespace MeanPayoff
namespace BinaryData
namespace Copy
open RegisterBits
open BinaryStack (Op applyOp)

inductive Label where
  | start | check | read | put (b : Bool) | depth (b : Bool)
  | restore | restoreSource (b : Bool) | restorePut (b : Bool)
  deriving DecidableEq, Fintype
noncomputable def equiv : Label ≃ Fin (Fintype.card Label) := Fintype.equivFin _
noncomputable def enc (q : Label) := equiv q
@[simp] theorem dec (q : Label) : equiv.symm (enc q) = q := equiv.symm_apply_apply q

noncomputable def program : Program 4 where
  states := Fintype.card Label
  start := enc .start
  read q := match equiv.symm q with
    | .start | .check | .depth _ => 3
    | .read | .restoreSource _ => 0
    | .put _ | .restore => 2
    | .restorePut _ => 1
  transition q top _ := match equiv.symm q with
    | .start => some ⟨enc .check, .push true, none⟩
    | .check => some ⟨enc (if top.isSome then .read else .restore), .keep, none⟩
    | .read => top.map fun b => ⟨enc (.put b), .pop, none⟩
    | .put b => some ⟨enc (.depth b), .push b, none⟩
    | .depth b => some ⟨enc .check, if b then .push true else .pop, none⟩
    | .restore => top.map fun b => ⟨enc (.restoreSource b), .pop, none⟩
    | .restoreSource b => some ⟨enc (.restorePut b), .push b, none⟩
    | .restorePut b => some ⟨enc .restore, .push b, none⟩

noncomputable def cfg (q : Label) (xs ys zs ds out : List Bool) : Config program :=
  ⟨some (enc q), ![xs, ys, zs, ds], out⟩
noncomputable def stopped (xs ys zs ds out : List Bool) : Config program :=
  ⟨none, ![xs, ys, zs, ds], out⟩

@[ext] theorem config_ext {K : ℕ} {P : Program K} {a b : Config P}
    (hc : a.control = b.control) (hs : a.stack = b.stack) (ho : a.output = b.output) : a = b := by
  cases a; cases b; simp_all

theorem advance_front {K : ℕ} (P : Program K) (bits : ℕ → Bool) (c : Config P) (n : ℕ) :
    advance P bits c (n + 1) = advance P (fun j => bits (j + 1)) (RegisterBits.step P c (bits 0)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change RegisterBits.step P (advance P bits c (n + 1)) (bits (n + 1)) = _
    rw [ih]
    rfl

theorem advance_add {K : ℕ} (P : Program K) (bits : ℕ → Bool) (c : Config P) (a b : ℕ) :
    advance P bits c (a + b) = advance P (fun j => bits (a + j)) (advance P bits c a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change RegisterBits.step P (advance P bits c (a + b)) (bits (a + b)) = _
    rw [ih]
    rfl

@[simp] theorem start_step (xs ys zs ds out : List Bool) (bit : Bool) :
    RegisterBits.step program (cfg .start xs ys zs ds out) bit = cfg .check xs ys zs (true :: ds) out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem check_step (xs ys zs ds out : List Bool) (a bit : Bool) :
    RegisterBits.step program (cfg .check xs ys zs (a :: ds) out) bit = cfg .read xs ys zs (a :: ds) out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem read_step (xs ys zs ds out : List Bool) (b bit : Bool) :
    RegisterBits.step program (cfg .read (b :: xs) ys zs ds out) bit = cfg (.put b) xs ys zs ds out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem put_step (xs ys zs ds out : List Bool) (b bit : Bool) :
    RegisterBits.step program (cfg (.put b) xs ys zs ds out) bit = cfg (.depth b) xs ys (b :: zs) ds out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem depth_false (xs ys zs ds out : List Bool) (a bit : Bool) :
    RegisterBits.step program (cfg (.depth false) xs ys zs (a :: ds) out) bit = cfg .check xs ys zs ds out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem depth_true (xs ys zs ds out : List Bool) (bit : Bool) :
    RegisterBits.step program (cfg (.depth true) xs ys zs ds out) bit = cfg .check xs ys zs (true :: ds) out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

theorem scan_nil (xs ys zs ds out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .check (false :: xs) ys zs (true :: ds) out) 4 =
      cfg .check xs ys (false :: zs) ds out := by
  simp [advance, check_step, read_step, put_step, depth_false]

theorem scan_pair (xs ys zs ds out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .check (true :: xs) ys zs (true :: ds) out) 4 =
      cfg .check xs ys (true :: zs) (true :: true :: ds) out := by
  simp [advance, check_step, read_step, put_step, depth_true]

theorem scan (t : Data) (xs ys zs ds out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .check (encode t ++ xs) ys zs (true :: ds) out)
      (4 * (encode t).length) = cfg .check xs ys ((encode t).reverse ++ zs) ds out := by
  induction t generalizing xs zs ds bits with
  | nil => simpa [encode] using scan_nil xs ys zs ds out bits
  | pair a b ia ib =>
    simp only [encode, List.length_cons, List.length_append, List.cons_append]
    have hn : 4 * (1 + (encode a).length + (encode b).length) =
        4 + 4 * (encode a).length + 4 * (encode b).length := by omega
    rw [show 4 * ((encode a).length + (encode b).length + 1) =
      4 + 4 * (encode a).length + 4 * (encode b).length by omega,
      advance_add (a := 4 + 4 * (encode a).length) (b := 4 * (encode b).length),
      advance_add (a := 4), scan_pair, List.append_assoc, ia, ib]
    simp [List.reverse_cons, List.reverse_append, List.append_assoc]

@[simp] theorem check_empty (xs ys zs out : List Bool) (bit : Bool) :
    RegisterBits.step program (cfg .check xs ys zs [] out) bit = cfg .restore xs ys zs [] out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem restore_step (xs ys zs ds out : List Bool) (b bit : Bool) :
    RegisterBits.step program (cfg .restore xs ys (b :: zs) ds out) bit = cfg (.restoreSource b) xs ys zs ds out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem restore_source (xs ys zs ds out : List Bool) (b bit : Bool) :
    RegisterBits.step program (cfg (.restoreSource b) xs ys zs ds out) bit =
      cfg (.restorePut b) (b :: xs) ys zs ds out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem restore_put (xs ys zs ds out : List Bool) (b bit : Bool) :
    RegisterBits.step program (cfg (.restorePut b) xs ys zs ds out) bit = cfg .restore xs (b :: ys) zs ds out := by
  apply config_ext
  · simp [RegisterBits.step, program, cfg]
  · funext i; fin_cases i <;> simp [RegisterBits.step, program, cfg, applyOp]
  · simp [RegisterBits.step, program, cfg]

@[simp] theorem restore_empty (xs ys ds out : List Bool) (bit : Bool) :
    RegisterBits.step program (cfg .restore xs ys [] ds out) bit = stopped xs ys [] ds out := by
  simp [RegisterBits.step, program, cfg, stopped]

theorem restore_all (xs ys zs ds out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .restore xs ys zs ds out) (3 * zs.length + 1) =
      stopped (zs.reverse ++ xs) (zs.reverse ++ ys) [] ds out := by
  induction zs generalizing xs ys bits with
  | nil => simp [advance, restore_empty]
  | cons b zs ih =>
    rw [List.length_cons, show 3 * (zs.length + 1) + 1 = ((3 * zs.length + 1 + 1) + 1) + 1 by omega,
      advance_front, restore_step, advance_front, restore_source, advance_front, restore_put, ih]
    simp [List.reverse_cons, List.append_assoc]

theorem copies (t : Data) (xs ys out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .start (encode t ++ xs) ys [] [] out)
      (7 * (encode t).length + 3) = stopped (encode t ++ xs) (encode t ++ ys) [] [] out := by
  rw [show 7 * (encode t).length + 3 = (4 * (encode t).length + 1 + (3 * (encode t).length + 1)) + 1 by omega,
    advance_front, start_step, advance_add (a := 4 * (encode t).length + 1)]
  have hs (bits : ℕ → Bool) : advance program bits (cfg .check (encode t ++ xs) ys [] [true] out)
      (4 * (encode t).length + 1) = cfg .restore xs ys (encode t).reverse [] out := by
    rw [advance, scan, List.append_nil, check_empty]
  rw [hs]
  simpa using restore_all xs ys (encode t).reverse [] out (fun j => bits (4 * (encode t).length + 1 + j + 1))

end Copy
end BinaryData
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Stack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace Counted
@[ext] theorem ext {α : Type} {a b : Counted α} (h : a.tree = b.tree) : a = b := by
  cases a; cases b; cases h; rfl
@[simp] theorem pure_bind {α β : Type} (a : α) (f : α → Counted β) :
    (pure a).bind f = f a := by ext; simp [pure, bind, RandomTree.map]
@[simp] theorem bind_pure {α : Type} (t : Counted α) : t.bind pure = t := by
  ext; simp [bind, pure, RandomTree.map]
@[simp] theorem map_pure {α β : Type} (a : α) (f : α → β) :
    (pure a).map f = pure (f a) := rfl
@[simp] theorem bind_map {α β γ : Type} (t : Counted α) (f : α → β) (g : β → Counted γ) :
    (t.map f).bind g = t.bind (fun a => g (f a)) := by
  ext; simp [map, bind]
@[simp] theorem map_map {α β γ : Type} (t : Counted α) (f : α → β) (g : β → γ) :
    (t.map f).map g = t.map (fun a => g (f a)) := by
  ext; simp [map]
@[simp] theorem bind_pure_eq_map {α β : Type} (t : Counted α) (f : α → β) :
    t.bind (fun a => pure (f a)) = t.map f := by
  ext; simp [bind, map, pure, RandomTree.map]
end Counted

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_StackMacros
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.RegisterBits
@[simp] theorem install_self {K N : ℕ} (f : Fin K → Fin N) (s : Fin N → List Bool) :
    install f s (fun i => s (f i)) = s := by
  funext j
  unfold install
  split_ifs with h
  · exact congrArg s (Classical.choose_spec h)
  · rfl

def slots {K : ℕ} (i j : Fin K) : Fin 4 → Fin (K + 2)
  | 0 => i.castAdd 2
  | 1 => j.castAdd 2
  | 2 => ⟨K, by omega⟩
  | 3 => ⟨K + 1, by omega⟩

theorem slots_injective {K : ℕ} (i j : Fin K) (hij : i ≠ j) :
    Function.Injective (slots i j) := by
  intro a b hab
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hi := i.isLt
  have hj := j.isLt
  fin_cases a <;> fin_cases b <;> simp only [slots, Fin.ext_iff, Fin.val_castAdd] at hab ⊢ <;> omega

theorem renamed_start {K N : ℕ} (P : Program K) (f : Fin K → Fin N)
    (s : Fin N → List Bool) (out : List Bool) :
    renamed P f s ⟨some P.start, (fun i => s (f i)), out⟩ =
      ⟨some (rename P f).start, s, out⟩ := by
  simp only [renamed, install_self]; rfl

theorem move_tree {K : ℕ} (i j : Fin K) (hij : i ≠ j) (s : Fin (K+2) → List Bool)
    (out : List Bool) (t : BinaryData.Data) (xs ys : List Bool)
    (h0 : s (i.castAdd 2) = BinaryData.encode t ++ xs)
    (h1 : s (j.castAdd 2) = ys)
    (h2 : s ⟨K, by omega⟩ = []) (h3 : s ⟨K+1, by omega⟩ = []) (bits : ℕ → Bool) :
    advance (rename BinaryData.Take.program (slots i j)) bits
      ⟨some (rename BinaryData.Take.program (slots i j)).start, s, out⟩
      (6 * (BinaryData.encode t).length + 3) =
    ⟨none, Function.update (Function.update s (i.castAdd 2) xs) (j.castAdd 2)
      (BinaryData.encode t ++ ys), out⟩ := by
  have hf := slots_injective i j hij
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hKi : K ≠ i.val := by have hi := i.isLt; omega
  have hKj : K ≠ j.val := by have hj := j.isLt; omega
  have h1i : K+1 ≠ i.val := by have hi := i.isLt; omega
  have h1j : K+1 ≠ j.val := by have hj := j.isLt; omega
  have hs : (fun a => s (slots i j a)) = ![BinaryData.encode t ++ xs, ys, [], []] := by
    funext a; fin_cases a <;> simpa only [slots, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using (by assumption)
  rw [← renamed_start BinaryData.Take.program (slots i j) s out, hs, rename_advance _ _ hf]
  change renamed _ _ s (advance BinaryData.Take.program bits
    (BinaryData.Take.cfg .start (BinaryData.encode t ++ xs) ys [] [] out) _) = _
  rw [BinaryData.Take.takes]
  apply BinaryData.Take.config_ext
  · rfl
  · funext a
    change install (slots i j) s ![xs, BinaryData.encode t ++ ys, [], []] a = _
    by_cases ha : ∃ b, slots i j b = a
    · obtain ⟨b, rfl⟩ := ha
      rw [install_at _ hf]
      fin_cases b <;> simp [slots, h2, h3,
        Fin.ext_iff, hne, hKi, hKj, h1i, h1j]
    · rw [install_off _ _ _ _ (by simpa using ha)]
      have hi : a ≠ i.castAdd 2 := by intro h; exact ha ⟨0, h.symm⟩
      have hj : a ≠ j.castAdd 2 := by intro h; exact ha ⟨1, h.symm⟩
      simp [Function.update_of_ne hi, Function.update_of_ne hj]
  · rfl

theorem copy_tree {K : ℕ} (i j : Fin K) (hij : i ≠ j) (s : Fin (K+2) → List Bool)
    (out : List Bool) (t : BinaryData.Data) (xs ys : List Bool)
    (h0 : s (i.castAdd 2) = BinaryData.encode t ++ xs)
    (h1 : s (j.castAdd 2) = ys)
    (h2 : s ⟨K, by omega⟩ = []) (h3 : s ⟨K+1, by omega⟩ = []) (bits : ℕ → Bool) :
    advance (rename BinaryData.Copy.program (slots i j)) bits
      ⟨some (rename BinaryData.Copy.program (slots i j)).start, s, out⟩
      (7 * (BinaryData.encode t).length + 3) =
    ⟨none, Function.update s (j.castAdd 2) (BinaryData.encode t ++ ys), out⟩ := by
  have hf := slots_injective i j hij
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hKi : K ≠ i.val := by have hi := i.isLt; omega
  have hKj : K ≠ j.val := by have hj := j.isLt; omega
  have h1i : K+1 ≠ i.val := by have hi := i.isLt; omega
  have h1j : K+1 ≠ j.val := by have hj := j.isLt; omega
  have hs : (fun a => s (slots i j a)) = ![BinaryData.encode t ++ xs, ys, [], []] := by
    funext a; fin_cases a <;> simpa only [slots, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using (by assumption)
  rw [← renamed_start BinaryData.Copy.program (slots i j) s out, hs, rename_advance _ _ hf]
  change renamed _ _ s (advance BinaryData.Copy.program bits
    (BinaryData.Copy.cfg .start (BinaryData.encode t ++ xs) ys [] [] out) _) = _
  rw [BinaryData.Copy.copies]
  apply BinaryData.Take.config_ext
  · rfl
  · funext a
    change install (slots i j) s ![BinaryData.encode t ++ xs, BinaryData.encode t ++ ys, [], []] a = _
    by_cases ha : ∃ b, slots i j b = a
    · obtain ⟨b, rfl⟩ := ha
      rw [install_at _ hf]
      fin_cases b <;> simp [slots, h0, h2, h3,
        Fin.ext_iff, hne, hKj, h1j]
    · rw [install_off _ _ _ _ (by simpa using ha)]
      have hj : a ≠ j.castAdd 2 := by intro h; exact ha ⟨1, h.symm⟩
      simp [Function.update_of_ne hj]
  · rfl
end MeanPayoff.RegisterBits
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_ArithmeticBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff
namespace RandomTree

def maximum {α : Type} : RandomTree α → (α → ℕ) → ℕ
  | .leaf a, f => f a
  | .coin l r, f => max (maximum l f) (maximum r f)

end RandomTree
namespace Counted

def maximum {α : Type} (t : Counted α) : ℕ := t.tree.maximum Prod.snd

end Counted
end MeanPayoff
namespace MeanPayoff
namespace WorkStack.RegisterCompile

inductive Label (s : ℕ) where
  | get0 (q : Fin s)
  | get1 (q : Fin s) (a : Option Bool) (coin : Bool)
  | get2 (q : Fin s) (a b : Option Bool) (coin : Bool)
  | put (q : Fin s) (top : Fin 3 → Option Bool) (coin : Bool) (k : Fin 3)
  deriving DecidableEq, Fintype

noncomputable def equiv (P : Program) : Label P.states ≃ Fin (Fintype.card (Label P.states)) :=
  Fintype.equivFin _
noncomputable def enc (P : Program) (q : Label P.states) := equiv P q
@[simp] theorem decode (P : Program) (q : Label P.states) : (equiv P).symm (enc P q) = q :=
  (equiv P).symm_apply_apply q

noncomputable def program (P : Program) : RegisterBits.Program 3 where
  states := Fintype.card (Label P.states)
  start := enc P (.get0 P.start)
  read q := match (equiv P).symm q with
    | .get0 _ => 0
    | .get1 _ _ _ => 1
    | .get2 _ _ _ _ => 2
    | .put _ _ _ k => k
  transition q top coin := match (equiv P).symm q with
    | .get0 q => some ⟨enc P (.get1 q top coin), .keep, none⟩
    | .get1 q a c => some ⟨enc P (.get2 q a top c), .keep, none⟩
    | .get2 q a b c => some ⟨enc P (.put q ![a,b,top] c 0), .keep, none⟩
    | .put q ts c k => match P.transition q ts c with
      | none => none
      | some a => some ⟨enc P (if h : k.val = 2 then .get0 a.next else
          .put q ts c ⟨k.val+1, by have := k.isLt; omega⟩), a.work k, none⟩

noncomputable def lift (P : Program) (out : List Bool) (c : Config P) :
    RegisterBits.Config (program P) :=
  ⟨c.control.map (fun q => enc P (.get0 q)), c.stack, out⟩

noncomputable def state (P : Program) (q : Label P.states) (xs : Fin 3 → List Bool)
    (out : List Bool) : RegisterBits.Config (program P) := ⟨some (enc P q), xs, out⟩

@[simp] theorem read0 (P : Program) (q : Fin P.states) (xs : Fin 3 → List Bool)
    (out : List Bool) (b : Bool) :
    RegisterBits.step (program P) (state P (.get0 q) xs out) b =
      state P (.get1 q (xs 0).head? b) xs out := by
  simp [RegisterBits.step, program, state, BinaryStack.applyOp]

@[simp] theorem read1 (P : Program) (q : Fin P.states) (a : Option Bool) (c b : Bool)
    (xs : Fin 3 → List Bool) (out : List Bool) :
    RegisterBits.step (program P) (state P (.get1 q a c) xs out) b =
      state P (.get2 q a (xs 1).head? c) xs out := by
  simp [RegisterBits.step, program, state, BinaryStack.applyOp]

@[simp] theorem read2 (P : Program) (q : Fin P.states) (a d : Option Bool) (c b : Bool)
    (xs : Fin 3 → List Bool) (out : List Bool) :
    RegisterBits.step (program P) (state P (.get2 q a d c) xs out) b =
      state P (.put q ![a,d,(xs 2).head?] c 0) xs out := by
  simp [RegisterBits.step, program, state, BinaryStack.applyOp]

@[simp] theorem put_step (P : Program) (q : Fin P.states) (ts : Fin 3 → Option Bool)
    (c b : Bool) (k : Fin 3) (xs : Fin 3 → List Bool) (out : List Bool)
    (a : Act P.states) (ha : P.transition q ts c = some a) :
    RegisterBits.step (program P) (state P (.put q ts c k) xs out) b =
      state P (if h : k.val = 2 then .get0 a.next else
        .put q ts c ⟨k.val+1, by have := k.isLt; omega⟩)
        (Function.update xs k (BinaryStack.applyOp (a.work k) (xs k))) out := by
  simp [RegisterBits.step, program, state, ha]

@[simp] theorem put_stop (P : Program) (q : Fin P.states) (ts : Fin 3 → Option Bool)
    (c b : Bool) (k : Fin 3) (xs : Fin 3 → List Bool) (out : List Bool)
    (ha : P.transition q ts c = none) :
    RegisterBits.step (program P) (state P (.put q ts c k) xs out) b =
      ⟨none, xs, out⟩ := by
  simp [RegisterBits.step, program, state, ha]

theorem six_steps (P : Program) (out : List Bool) (c : Config P) (bits : ℕ → Bool) :
    RegisterBits.advance (program P) bits (lift P out c) 6 =
      lift P out (step P c (bits 0)) := by
  rcases c with ⟨q,xs⟩
  cases q with
  | none => rfl
  | some q =>
    have ht : ![(xs 0).head?, (xs 1).head?, (xs 2).head?] =
        (fun i => (xs i).head?) := by funext i; fin_cases i <;> rfl
    change RegisterBits.advance _ bits (state P (.get0 q) xs out) 6 = _
    simp only [RegisterBits.advance, read0, read1, read2, ht]
    cases ha : P.transition q (fun i => (xs i).head?) (bits 0) with
    | none =>
      rw [put_stop (ha := ha)]
      simp [RegisterBits.step, step, ha, lift]
      rfl
    | some a =>
      simp only [put_step (ha := ha), Fin.val_zero, Nat.reduceAdd, Nat.reduceEqDiff, dite_false, dite_true]
      apply BinaryData.Take.config_ext
      · simp [step, ha, lift, state]; rfl
      · funext i; fin_cases i <;> simp [step, ha, lift, state]
      · rfl

theorem advance_six (P : Program) (out : List Bool) (c : Config P) (bits : ℕ → Bool)
    (n : ℕ) :
    RegisterBits.advance (program P) bits (lift P out c) (6*n) =
      lift P out (advance P (fun i => bits (6*i)) c n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 6*(n+1) = 6*n+6 by omega, BinaryData.Take.advance_add, ih, six_steps]
    rfl

end WorkStack.RegisterCompile
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_BinaryData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.WorkStack.RegisterCompile

theorem signed_adds (a b : Bool) (xs ys out : List Bool) (bits : ℕ → Bool) :
    RegisterBits.advance (program SignedAddition.program) bits
      (lift SignedAddition.program out (SignedAddition.state .start (a::xs) (b::ys) []))
      (6*(2*max xs.length ys.length+5)) =
      lift SignedAddition.program out (SignedAddition.stopped
        ((SignedBits.add a b false xs ys).sign::(SignedBits.add a b false xs ys).digits) []) := by
  rw [advance_six, SignedAddition.program_adds]
end MeanPayoff.WorkStack.RegisterCompile
namespace MeanPayoff.BinaryData

def boolData : Bool → Data
  | false => .nil
  | true => .pair .nil .nil

def listData : List Bool → Data
  | [] => .nil
  | b :: bs => .pair (boolData b) (listData bs)

def wordData (w : SignedBits.Word) : Data := listData (w.sign :: w.digits)

def consCode : Bool → List Bool
  | false => [true, false]
  | true => [true, true, false, false]

@[simp] theorem encode_list_nil : encode (listData []) = [false] := rfl
@[simp] theorem encode_list_cons (b : Bool) (bs : List Bool) :
    encode (listData (b :: bs)) = consCode b ++ encode (listData bs) := by cases b <;> rfl

@[simp] theorem consCode_length_le (b : Bool) : (consCode b).length ≤ 4 := by cases b <;> decide

def feedCost : List Bool → ℕ
  | [] => 0
  | b :: bs => (consCode b).length + 1 + feedCost bs

@[simp] theorem feedCost_append (a b : List Bool) : feedCost (a ++ b) = feedCost a + feedCost b := by
  induction a with
  | nil => simp [feedCost]
  | cons x xs ih => simp only [List.cons_append, feedCost, ih]; omega

@[simp] theorem feedCost_reverse (a : List Bool) : feedCost a.reverse = feedCost a := by
  induction a with
  | nil => rfl
  | cons b bs ih => simp only [List.reverse_cons, feedCost_append, ih, feedCost]; omega

theorem feedCost_le (a : List Bool) : feedCost a ≤ 5*a.length := by
  induction a with
  | nil => rfl
  | cons b bs ih => have := consCode_length_le b; simp only [feedCost, List.length_cons]; omega

theorem encode_list_length_le (a : List Bool) : (encode (listData a)).length ≤ 4*a.length+1 := by
  induction a with
  | nil => simp
  | cons b bs ih =>
    simp only [encode_list_cons, List.length_append, List.length_cons]
    have := consCode_length_le b; omega

namespace Unbox
open RegisterBits
open BinaryStack (applyOp)
open Take (config_ext advance_front advance_add)

inductive Label where
  | read | bit | skip0 | skip1 | push (b : Bool) | restore | put (b : Bool)
  deriving DecidableEq, Fintype
noncomputable def equiv : Label ≃ Fin (Fintype.card Label) := Fintype.equivFin _
noncomputable def enc (q : Label) := equiv q
@[simp] theorem decode (q : Label) : equiv.symm (enc q) = q := equiv.symm_apply_apply q

noncomputable def program : Program 3 where
  states := Fintype.card Label
  start := enc .read
  read q := match equiv.symm q with
    | .read | .bit | .skip0 | .skip1 => 0
    | .push _ | .restore => 2
    | .put _ => 1
  transition q top _ := match equiv.symm q with
    | .read => top.map fun b => ⟨enc (if b then .bit else .restore), .pop, none⟩
    | .bit => top.map fun b => ⟨enc (if b then .skip0 else .push false), .pop, none⟩
    | .skip0 => some ⟨enc .skip1, .pop, none⟩
    | .skip1 => some ⟨enc (.push true), .pop, none⟩
    | .push b => some ⟨enc .read, .push b, none⟩
    | .restore => top.map fun b => ⟨enc (.put b), .pop, none⟩
    | .put b => some ⟨enc .restore, .push b, none⟩

noncomputable def cfg (q : Label) (xs ys zs out : List Bool) : Config program :=
  ⟨some (enc q), ![xs,ys,zs], out⟩
def stopped (xs ys out : List Bool) : Config program := ⟨none, ![xs,ys,[]], out⟩

@[simp] theorem read_nil (xs ys zs out : List Bool) (b : Bool) :
    RegisterBits.step program (cfg .read (false::xs) ys zs out) b = cfg .restore xs ys zs out := by
  apply config_ext <;> simp [RegisterBits.step, cfg, program, applyOp]
  funext i; fin_cases i <;> rfl

theorem feed_one (b : Bool) (xs ys zs out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .read (consCode b ++ xs) ys zs out)
      ((consCode b).length + 1) = cfg .read xs ys (b::zs) out := by
  cases b <;>
    apply config_ext <;>
    simp [advance, RegisterBits.step, cfg, program, consCode, applyOp]
  all_goals funext i; fin_cases i <;> rfl

theorem feeds (bs xs ys zs out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .read (encode (listData bs) ++ xs) ys zs out)
      (feedCost bs) = cfg .read (false::xs) ys (bs.reverse ++ zs) out := by
  induction bs generalizing zs bits with
  | nil => rfl
  | cons b bs ih =>
    simp only [encode_list_cons, List.append_assoc, feedCost]
    rw [advance_add, feed_one, ih]
    simp [List.reverse_cons, List.append_assoc]

@[simp] theorem restore_read (b : Bool) (xs ys zs out : List Bool) (coin : Bool) :
    RegisterBits.step program (cfg .restore xs ys (b::zs) out) coin = cfg (.put b) xs ys zs out := by
  apply config_ext <;> simp [RegisterBits.step, cfg, program, applyOp]
  funext i; fin_cases i <;> rfl
@[simp] theorem restore_put (b : Bool) (xs ys zs out : List Bool) (coin : Bool) :
    RegisterBits.step program (cfg (.put b) xs ys zs out) coin = cfg .restore xs (b::ys) zs out := by
  apply config_ext <;> simp [RegisterBits.step, cfg, program, applyOp]
  funext i; fin_cases i <;> rfl
@[simp] theorem restore_done (xs ys out : List Bool) (coin : Bool) :
    RegisterBits.step program (cfg .restore xs ys [] out) coin = stopped xs ys out := by
  simp [RegisterBits.step, cfg, program, stopped]

theorem restores (zs xs ys out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .restore xs ys zs out) (2*zs.length+1) =
      stopped xs (zs.reverse ++ ys) out := by
  induction zs generalizing ys bits with
  | nil => simp [advance]
  | cons b zs ih =>
    rw [show 2*(b::zs).length+1 = (2*zs.length+1+1)+1 by simp; omega,
      Take.advance_front, restore_read, Take.advance_front, restore_put, ih]
    simp [List.reverse_cons, List.append_assoc]

theorem read_nil_advance (xs ys zs out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .read (false::xs) ys zs out) 1 = cfg .restore xs ys zs out := by
  simp only [advance, read_nil]

theorem unboxes (bs xs ys out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .read (encode (listData bs) ++ xs) ys [] out)
      (feedCost bs+1+(2*bs.length+1)) = stopped xs (bs++ys) out := by
  rw [advance_add _ _ _ (feedCost bs+1) (2*bs.length+1),
    advance_add _ _ _ (feedCost bs) 1, feeds]
  simp only [List.append_nil, read_nil_advance]
  rw [show bs.length = bs.reverse.length by simp, restores]
  simp

theorem unboxes_bound (bs : List Bool) : feedCost bs+1+(2*bs.length+1) ≤ 7*bs.length+2 := by
  have := feedCost_le bs; omega

end Unbox
end MeanPayoff.BinaryData
namespace MeanPayoff.BinaryData.Box
open RegisterBits
open BinaryStack (applyOp)
open Take (config_ext advance_add)

inductive Label where
  | reverse | revPut (b : Bool) | init | feed | zero | one0 | one1 | one2 | last
  deriving DecidableEq, Fintype
noncomputable def equiv : Label ≃ Fin (Fintype.card Label) := Fintype.equivFin _
noncomputable def enc (q : Label) := equiv q
@[simp] theorem decode (q : Label) : equiv.symm (enc q) = q := equiv.symm_apply_apply q

noncomputable def program : Program 3 where
  states := Fintype.card Label
  start := enc .reverse
  read q := match equiv.symm q with
    | .reverse => 0
    | .revPut _ | .feed => 2
    | _ => 1
  transition q top _ := match equiv.symm q with
    | .reverse => some (match top with
        | none => ⟨enc .init, .keep, none⟩
        | some b => ⟨enc (.revPut b), .pop, none⟩)
    | .revPut b => some ⟨enc .reverse, .push b, none⟩
    | .init => some ⟨enc .feed, .push false, none⟩
    | .feed => top.map fun b => ⟨enc (if b then .one0 else .zero), .pop, none⟩
    | .zero => some ⟨enc .last, .push false, none⟩
    | .one0 => some ⟨enc .one1, .push false, none⟩
    | .one1 => some ⟨enc .one2, .push false, none⟩
    | .one2 => some ⟨enc .last, .push true, none⟩
    | .last => some ⟨enc .feed, .push true, none⟩

noncomputable def cfg (q : Label) (xs ys zs out : List Bool) : Config program :=
  ⟨some (enc q), ![xs,ys,zs], out⟩
def stopped (ys out : List Bool) : Config program := ⟨none, ![[],ys,[]], out⟩

@[simp] theorem reverse_read (b : Bool) (xs ys zs out : List Bool) (coin : Bool) :
    RegisterBits.step program (cfg .reverse (b::xs) ys zs out) coin = cfg (.revPut b) xs ys zs out := by
  apply config_ext <;> simp [RegisterBits.step, cfg, program, applyOp]
  funext i; fin_cases i <;> rfl
@[simp] theorem reverse_put (b : Bool) (xs ys zs out : List Bool) (coin : Bool) :
    RegisterBits.step program (cfg (.revPut b) xs ys zs out) coin = cfg .reverse xs ys (b::zs) out := by
  apply config_ext <;> simp [RegisterBits.step, cfg, program, applyOp]
  funext i; fin_cases i <;> rfl

theorem reverses (bs ys zs out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .reverse bs ys zs out) (2*bs.length) =
      cfg .reverse [] ys (bs.reverse++zs) out := by
  induction bs generalizing zs bits with
  | nil => rfl
  | cons b bs ih =>
    rw [show 2*(b::bs).length = (2*bs.length+1)+1 by simp; omega,
      Take.advance_front, reverse_read, Take.advance_front, reverse_put, ih]
    simp [List.reverse_cons, List.append_assoc]

theorem initializes (ys zs out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .reverse [] ys zs out) 2 = cfg .feed [] (false::ys) zs out := by
  apply config_ext <;> simp [advance, RegisterBits.step, cfg, program, applyOp]
  funext i; fin_cases i <;> rfl

theorem feed_one (b : Bool) (xs ys zs out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .feed xs ys (b::zs) out) ((consCode b).length+1) =
      cfg .feed xs (consCode b++ys) zs out := by
  cases b <;>
    apply config_ext <;>
    simp [advance, RegisterBits.step, cfg, program, consCode, applyOp]
  all_goals funext i; fin_cases i <;> rfl

theorem feeds (bs acc xs ys out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .feed xs (encode (listData acc)++ys) bs out) (feedCost bs) =
      cfg .feed xs (encode (listData (bs.reverse++acc))++ys) [] out := by
  induction bs generalizing acc bits with
  | nil => rfl
  | cons b bs ih =>
    rw [feedCost, advance_add, feed_one]
    rw [← List.append_assoc, ← encode_list_cons, ih]
    simp [List.reverse_cons, List.append_assoc]

@[simp] theorem feed_done (ys out : List Bool) (coin : Bool) :
    RegisterBits.step program (cfg .feed [] ys [] out) coin = stopped ys out := by
  simp [RegisterBits.step, cfg, program, stopped]

theorem boxes (bs ys out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .reverse bs ys [] out)
      (2*bs.length+2+feedCost bs+1) = stopped (encode (listData bs)++ys) out := by
  rw [advance_add _ _ _ (2*bs.length+2+feedCost bs) 1,
    advance_add _ _ _ (2*bs.length+2) (feedCost bs),
    advance_add _ _ _ (2*bs.length) 2, reverses]
  simp only [List.append_nil]
  rw [initializes]
  change advance _ _ (advance _ _ (cfg .feed [] (encode (listData [])++ys) bs.reverse out) _) 1 = _
  rw [← feedCost_reverse bs, feeds]
  simp [advance]

theorem boxes_bound (bs : List Bool) : 2*bs.length+2+feedCost bs+1 ≤ 7*bs.length+3 := by
  have := feedCost_le bs; omega

end MeanPayoff.BinaryData.Box
namespace MeanPayoff.RegisterBits.Flow
open BinaryData.Take (advance_add)

theorem hop {K : ℕ} (P : Program K) (p q : Fin P.nodes) (s t : Fin K → List Bool)
    (out : List Bool) (bits : ℕ → Bool) (N : ℕ)
    (hm : advance (P.block p) bits ⟨some (P.block p).start, s, out⟩ N = ⟨none,t,out⟩)
    (hn : ∀ top bit, P.next p top bit = some ⟨q, .keep, none⟩) :
    ∃ d ≤ N+1, advance (compile P) bits (state P p s out) d = state P q t out := by
  obtain ⟨d, hd, he⟩ := macro_runs P p s out bits N (by rw [hm])
  rw [hm] at he
  refine ⟨d+1, by omega, ?_⟩
  simp only [advance, he, step_boundary, hn]
  simp [BinaryStack.applyOp]

theorem finish {K : ℕ} (P : Program K) (p : Fin P.nodes) (s t : Fin K → List Bool)
    (out : List Bool) (bits : ℕ → Bool) (N : ℕ)
    (hm : advance (P.block p) bits ⟨some (P.block p).start, s, out⟩ N = ⟨none,t,out⟩)
    (hn : ∀ top bit, P.next p top bit = none) :
    ∃ d ≤ N+1, advance (compile P) bits (state P p s out) d = ⟨none,t,out⟩ := by
  obtain ⟨d, hd, he⟩ := macro_runs P p s out bits N (by rw [hm])
  rw [hm] at he
  refine ⟨d+1, by omega, ?_⟩
  simp only [advance, he, step_boundary, hn]
end MeanPayoff.RegisterBits.Flow
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Comparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.ArithmeticForest
open RegisterBits
open BinaryData
open WorkStack

def placeA : Fin 3 → Fin 5 := ![0,2,4]
def placeB : Fin 3 → Fin 5 := ![0,3,4]
def placeAdd : Fin 3 → Fin 5 := ![2,3,4]
def placeBox : Fin 3 → Fin 5 := ![2,1,4]

theorem injectA : Function.Injective placeA := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [placeA]
theorem injectB : Function.Injective placeB := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [placeB]
theorem injectAdd : Function.Injective placeAdd := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [placeAdd]
theorem injectBox : Function.Injective placeBox := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [placeBox]

theorem installA (s : Fin 5 → List Bool) (a b c : List Bool) :
    install placeA s ![a,b,c] = ![a,s 1,b,s 3,c] := by
  funext i; fin_cases i
  · exact install_at placeA injectA s _ 0
  · exact install_off placeA s _ _ (by intro j; fin_cases j <;> decide)
  · exact install_at placeA injectA s _ 1
  · exact install_off placeA s _ _ (by intro j; fin_cases j <;> decide)
  · exact install_at placeA injectA s _ 2

theorem installB (s : Fin 5 → List Bool) (a b c : List Bool) :
    install placeB s ![a,b,c] = ![a,s 1,s 2,b,c] := by
  funext i; fin_cases i
  · exact install_at placeB injectB s _ 0
  · exact install_off placeB s _ _ (by intro j; fin_cases j <;> decide)
  · exact install_off placeB s _ _ (by intro j; fin_cases j <;> decide)
  · exact install_at placeB injectB s _ 1
  · exact install_at placeB injectB s _ 2

theorem installAdd (s : Fin 5 → List Bool) (a b c : List Bool) :
    install placeAdd s ![a,b,c] = ![s 0,s 1,a,b,c] := by
  funext i; fin_cases i
  · exact install_off placeAdd s _ _ (by intro j; fin_cases j <;> decide)
  · exact install_off placeAdd s _ _ (by intro j; fin_cases j <;> decide)
  · exact install_at placeAdd injectAdd s _ 0
  · exact install_at placeAdd injectAdd s _ 1
  · exact install_at placeAdd injectAdd s _ 2

theorem installBox (s : Fin 5 → List Bool) (a b c : List Bool) :
    install placeBox s ![a,b,c] = ![s 0,b,a,s 3,c] := by
  funext i; fin_cases i
  · exact install_off placeBox s _ _ (by intro j; fin_cases j <;> decide)
  · exact install_at placeBox injectBox s _ 1
  · exact install_at placeBox injectBox s _ 0
  · exact install_off placeBox s _ _ (by intro j; fin_cases j <;> decide)
  · exact install_at placeBox injectBox s _ 2

noncomputable abbrev flow : Flow.Program 5 where
  nodes := 4
  start := 0
  block q := match q with
    | 0 => rename Unbox.program placeA
    | 1 => rename Unbox.program placeB
    | 2 => rename (RegisterCompile.program WorkStack.SignedAddition.program) placeAdd
    | 3 => rename Box.program placeBox
  read _ := 4
  next q _ _ := match q with
    | 0 => some ⟨1,.keep,none⟩
    | 1 => some ⟨2,.keep,none⟩
    | 2 => some ⟨3,.keep,none⟩
    | 3 => none

noncomputable def program := Flow.compile flow

def unboxTime (xs : List Bool) := feedCost xs+1+(2*xs.length+1)
def addTime (a b : SignedBits.Word) := 6*(2*max a.digits.length b.digits.length+5)
def boxTime (xs : List Bool) := 2*xs.length+2+feedCost xs+1

def addWord (a b : SignedBits.Word) := SignedBits.add a.sign b.sign false a.digits b.digits

def store0 (a b : SignedBits.Word) (xs ys : List Bool) : Fin 5 → List Bool :=
  ![encode (wordData a) ++ encode (wordData b) ++ xs, ys, [],[],[]]
def store1 (a b : SignedBits.Word) (xs ys : List Bool) : Fin 5 → List Bool :=
  ![encode (wordData b) ++ xs, ys, a.sign::a.digits,[],[]]
def store2 (a b : SignedBits.Word) (xs ys : List Bool) : Fin 5 → List Bool :=
  ![xs, ys, a.sign::a.digits,b.sign::b.digits,[]]
def store3 (a b : SignedBits.Word) (xs ys : List Bool) : Fin 5 → List Bool :=
  ![xs, ys, (addWord a b).sign::(addWord a b).digits,[],[]]
def store4 (a b : SignedBits.Word) (xs ys : List Bool) : Fin 5 → List Bool :=
  ![xs, encode (wordData (addWord a b))++ys, [],[],[]]

theorem stage0 (a b : SignedBits.Word) (xs ys out : List Bool) (bits : ℕ → Bool) :
    advance (flow.block 0) bits ⟨some (flow.block 0).start, store0 a b xs ys, out⟩
      (unboxTime (a.sign::a.digits)) = ⟨none,store1 a b xs ys,out⟩ := by
  have h := rename_advance Unbox.program placeA injectA (store0 a b xs ys)
    (Unbox.cfg .read (encode (wordData a)++(encode (wordData b)++xs)) [] [] out)
    bits (unboxTime (a.sign::a.digits))
  rw [show unboxTime (a.sign::a.digits) = feedCost (a.sign::a.digits)+1+(2*(a.sign::a.digits).length+1) by rfl,
    show wordData a = listData (a.sign::a.digits) by rfl, Unbox.unboxes] at h
  simp only [renamed, Unbox.cfg, Unbox.stopped, installA, store0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_three,
    List.append_nil, List.append_assoc] at h
  simp only [store0, List.append_assoc]
  convert h using 1 <;> rfl

theorem stage1 (a b : SignedBits.Word) (xs ys out : List Bool) (bits : ℕ → Bool) :
    advance (flow.block 1) bits ⟨some (flow.block 1).start, store1 a b xs ys, out⟩
      (unboxTime (b.sign::b.digits)) = ⟨none,store2 a b xs ys,out⟩ := by
  have h := rename_advance Unbox.program placeB injectB (store1 a b xs ys)
    (Unbox.cfg .read (encode (wordData b)++xs) [] [] out)
    bits (unboxTime (b.sign::b.digits))
  rw [show unboxTime (b.sign::b.digits) = feedCost (b.sign::b.digits)+1+(2*(b.sign::b.digits).length+1) by rfl,
    show wordData b = listData (b.sign::b.digits) by rfl, Unbox.unboxes] at h
  simp only [renamed, Unbox.cfg, Unbox.stopped, installB, store1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, List.append_nil] at h
  convert h using 1 <;> rfl

theorem stage2 (a b : SignedBits.Word) (xs ys out : List Bool) (bits : ℕ → Bool) :
    advance (flow.block 2) bits ⟨some (flow.block 2).start, store2 a b xs ys, out⟩
      (addTime a b) = ⟨none,store3 a b xs ys,out⟩ := by
  have h := rename_advance (RegisterCompile.program WorkStack.SignedAddition.program) placeAdd injectAdd
    (store2 a b xs ys) (RegisterCompile.lift WorkStack.SignedAddition.program out
      (WorkStack.SignedAddition.state .start (a.sign::a.digits) (b.sign::b.digits) []))
    bits (addTime a b)
  rw [show addTime a b = 6*(2*max a.digits.length b.digits.length+5) by rfl,
    RegisterCompile.signed_adds] at h
  simp only [renamed, RegisterCompile.lift, WorkStack.SignedAddition.state,
    WorkStack.SignedAddition.stopped, installAdd, store2, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  convert h using 1 <;> rfl

theorem stage3 (a b : SignedBits.Word) (xs ys out : List Bool) (bits : ℕ → Bool) :
    advance (flow.block 3) bits ⟨some (flow.block 3).start, store3 a b xs ys, out⟩
      (boxTime ((addWord a b).sign::(addWord a b).digits)) = ⟨none,store4 a b xs ys,out⟩ := by
  have h := rename_advance Box.program placeBox injectBox (store3 a b xs ys)
    (Box.cfg .reverse ((addWord a b).sign::(addWord a b).digits) ys [] out)
    bits (boxTime ((addWord a b).sign::(addWord a b).digits))
  rw [show boxTime ((addWord a b).sign::(addWord a b).digits) =
    2*((addWord a b).sign::(addWord a b).digits).length+2+
      feedCost ((addWord a b).sign::(addWord a b).digits)+1 by rfl, Box.boxes] at h
  simp only [renamed, Box.cfg, Box.stopped, installBox, store3, Matrix.cons_val_zero, Matrix.cons_val_three] at h
  convert h using 1 <;> rfl

end MeanPayoff.ArithmeticForest

namespace MeanPayoff.ArithmeticForest
open RegisterBits
open BinaryData
open BinaryData.Take (advance_add)

theorem total_bound (a b : SignedBits.Word) :
    (unboxTime (a.sign::a.digits)+1) + (unboxTime (b.sign::b.digits)+1) +
      (addTime a b+1) + (boxTime ((addWord a b).sign::(addWord a b).digits)+1) ≤
      30*(a.digits.length+b.digits.length+3) := by
  have ha := Unbox.unboxes_bound (a.sign::a.digits)
  have hb := Unbox.unboxes_bound (b.sign::b.digits)
  have hc := Box.boxes_bound ((addWord a b).sign::(addWord a b).digits)
  have hl := SignedBits.add_length a.sign b.sign false a.digits b.digits
  change (addWord a b).digits.length = _ at hl
  simp only [List.length_cons] at ha hb hc
  unfold unboxTime addTime boxTime
  simp only [List.length_cons]
  omega

theorem program_adds (a b : SignedBits.Word) (xs ys out : List Bool) (bits : ℕ → Bool) :
    ∃ t ≤ 30*(a.digits.length+b.digits.length+3),
      advance program bits ⟨some program.start,store0 a b xs ys,out⟩ t =
        ⟨none,store4 a b xs ys,out⟩ := by
  obtain ⟨t₀,h₀,e₀⟩ := Flow.hop flow 0 1 (store0 a b xs ys) (store1 a b xs ys) out bits
    (unboxTime (a.sign::a.digits)) (stage0 a b xs ys out bits) (by intros; rfl)
  obtain ⟨t₁,h₁,e₁⟩ := Flow.hop flow 1 2 (store1 a b xs ys) (store2 a b xs ys) out
    (fun j => bits (t₀+j)) (unboxTime (b.sign::b.digits))
    (stage1 a b xs ys out _) (by intros; rfl)
  obtain ⟨t₂,h₂,e₂⟩ := Flow.hop flow 2 3 (store2 a b xs ys) (store3 a b xs ys) out
    (fun j => bits (t₀+t₁+j)) (addTime a b) (stage2 a b xs ys out _) (by intros; rfl)
  obtain ⟨t₃,h₃,e₃⟩ := Flow.finish flow 3 (store3 a b xs ys) (store4 a b xs ys) out
    (fun j => bits (t₀+t₁+t₂+j)) (boxTime ((addWord a b).sign::(addWord a b).digits))
    (stage3 a b xs ys out _) (by intros; rfl)
  refine ⟨t₀+t₁+t₂+t₃, le_trans (by omega) (total_bound a b), ?_⟩
  change advance (Flow.compile flow) bits (Flow.state flow 0 (store0 a b xs ys) out) _ = _
  rw [advance_add _ _ _ (t₀+t₁+t₂) t₃, advance_add _ _ _ (t₀+t₁) t₂,
    advance_add _ _ _ t₀ t₁, e₀, e₁, e₂, e₃]
  rfl

end MeanPayoff.ArithmeticForest

namespace MeanPayoff.SignedBits

def compareBit (x y c : Bool) : Bool := if x = y then c else !x && y

def compare (a b c : Bool) : List Bool → List Bool → Bool
  | [], [] => if a = b then c else a
  | x::xs, [] => compare a b (compareBit x b c) xs []
  | [], y::ys => compare a b (compareBit a y c) [] ys
  | x::xs, y::ys => compare a b (compareBit x y c) xs ys
termination_by xs ys => xs.length+ys.length

theorem compare_bit_correct (x y c : Bool) (A B : ℤ) :
    (A < B ∨ A = B ∧ compareBit x y c = true) ↔
      ((x.toNat : ℤ)+2*A < (y.toNat : ℤ)+2*B ∨
       (x.toNat : ℤ)+2*A = (y.toNat : ℤ)+2*B ∧ c = true) := by
  cases x <;> cases y <;> cases c <;> simp [compareBit] <;> omega

theorem compare_correct (a b c : Bool) (xs ys : List Bool) :
    compare a b c xs ys = true ↔
      (Word.mk a xs).val < (Word.mk b ys).val ∨
      (Word.mk a xs).val = (Word.mk b ys).val ∧ c = true := by
  cases xs with
  | nil =>
    cases ys with
    | nil => cases a <;> cases b <;> cases c <;> norm_num [compare, Word.val, BinaryStack.Addition.value]
    | cons y ys =>
      rw [compare, compare_correct, compare_bit_correct]
      have hx := val_uncons a []
      have hy := val_uncons b (y::ys)
      simp only [head, List.head?_nil, List.head?_cons, Option.getD_none, Option.getD_some,
        List.tail_nil, List.tail_cons] at hx hy
      rw [← hx, ← hy]
  | cons x xs =>
    cases ys with
    | nil =>
      rw [compare, compare_correct, compare_bit_correct]
      have hx := val_uncons a (x::xs)
      have hy := val_uncons b []
      simp only [head, List.head?_nil, List.head?_cons, Option.getD_none, Option.getD_some,
        List.tail_nil, List.tail_cons] at hx hy
      rw [← hx, ← hy]
    | cons y ys =>
      rw [compare, compare_correct, compare_bit_correct]
      have hx := val_uncons a (x::xs)
      have hy := val_uncons b (y::ys)
      simp only [head, List.head?_cons, Option.getD_some, List.tail_cons] at hx hy
      rw [← hx, ← hy]
termination_by xs.length+ys.length

theorem compare_lt (a b : Word) : compare a.sign b.sign false a.digits b.digits = true ↔ a.val < b.val := by
  cases a; cases b; simp [compare_correct]

end MeanPayoff.SignedBits

namespace MeanPayoff.WorkStack.SignedCompare
open SignedBits (compare compareBit)
inductive Label where
  | start
  | feed (a b c : Bool)
  | halt
  deriving DecidableEq, Fintype
noncomputable def equiv : Label ≃ Fin (Fintype.card Label) := Fintype.equivFin _
noncomputable def enc (q : Label) := equiv q
@[simp] theorem decode (q : Label) : equiv.symm (enc q) = q := equiv.symm_apply_apply _

noncomputable def program : Program where
  states := Fintype.card Label
  start := enc .start
  transition q top _ := match equiv.symm q with
    | .start => some ⟨enc (.feed ((top 0).getD false) ((top 1).getD false) false), ![.pop,.pop,.keep]⟩
    | .feed a b c =>
      if top 0 = none ∧ top 1 = none then
        some ⟨enc .halt, ![.push (if a=b then c else a),.keep,.keep]⟩
      else some ⟨enc (.feed a b (compareBit ((top 0).getD a) ((top 1).getD b) c)), ![.pop,.pop,.keep]⟩
    | .halt => none
noncomputable def state (q : Label) (xs ys zs : List Bool) : Config program :=
  ⟨some (enc q), ![xs,ys,zs]⟩
def stopped (r : Bool) (zs : List Bool) : Config program := ⟨none, ![[r],[],zs]⟩

@[simp] theorem step_start (a b : Bool) (xs ys zs : List Bool) (bit : Bool) :
    step program (state .start (a::xs) (b::ys) zs) bit = state (.feed a b false) xs ys zs := by
  simp only [step,state,program,decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl
@[simp] theorem step_nil (a b c : Bool) (zs : List Bool) (bit : Bool) :
    step program (state (.feed a b c) [] [] zs) bit = state .halt [if a=b then c else a] [] zs := by
  simp only [step,state,program,decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl
@[simp] theorem step_left (a b c x : Bool) (xs zs : List Bool) (bit : Bool) :
    step program (state (.feed a b c) (x::xs) [] zs) bit = state (.feed a b (compareBit x b c)) xs [] zs := by
  simp only [step,state,program,decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl
@[simp] theorem step_right (a b c y : Bool) (ys zs : List Bool) (bit : Bool) :
    step program (state (.feed a b c) [] (y::ys) zs) bit = state (.feed a b (compareBit a y c)) [] ys zs := by
  simp only [step,state,program,decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl
@[simp] theorem step_both (a b c x y : Bool) (xs ys zs : List Bool) (bit : Bool) :
    step program (state (.feed a b c) (x::xs) (y::ys) zs) bit = state (.feed a b (compareBit x y c)) xs ys zs := by
  simp only [step,state,program,decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl
@[simp] theorem step_halt (r : Bool) (zs : List Bool) (bit : Bool) :
    step program (state .halt [r] [] zs) bit = stopped r zs := by
  simp only [step,state,program,decode]; rfl

theorem feed_runs (a b c : Bool) (xs ys zs : List Bool) (bits : ℕ → Bool) :
    advance program bits (state (.feed a b c) xs ys zs) (max xs.length ys.length+1) =
      state .halt [compare a b c xs ys] [] zs := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp [advance,SignedBits.compare]
    | cons y ys =>
      rw [show max [].length (y::ys).length+1 = max [].length ys.length+1+1 by simp,
        advance_front, step_right, feed_runs]
      simp only [SignedBits.compare]
  | cons x xs =>
    cases ys with
    | nil =>
      rw [show max (x::xs).length [].length+1 = max xs.length [].length+1+1 by simp,
        advance_front, step_left, feed_runs]
      simp only [SignedBits.compare]
    | cons y ys =>
      rw [show max (x::xs).length (y::ys).length+1 = max xs.length ys.length+1+1 by simp,
        advance_front, step_both, feed_runs]
      simp only [SignedBits.compare]
termination_by xs.length+ys.length

theorem program_compares (a b : SignedBits.Word) (zs : List Bool) (bits : ℕ → Bool) :
    advance program bits (state .start (a.sign::a.digits) (b.sign::b.digits) zs)
      (max a.digits.length b.digits.length+3) =
      stopped (compare a.sign b.sign false a.digits b.digits) zs := by
  rw [show max a.digits.length b.digits.length+3 = (max a.digits.length b.digits.length+1+1)+1 by omega,
    advance_front, step_start, advance, feed_runs, step_halt]

end MeanPayoff.WorkStack.SignedCompare
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_TreeDevices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.RegisterBits
open BinaryData.Take (advance_add)

def CoinFree {K : ℕ} (P : Program K) : Prop :=
  ∀ q top bit, P.transition q top bit = P.transition q top false

theorem advance_pad {K : ℕ} (P : Program K) (c d : Config P) (bits : ℕ → Bool)
    {n N : ℕ} (hn : n ≤ N) (he : advance P bits c n = d) (hd : d.control = none) :
    advance P bits c N = d := by
  rw [show N = n+(N-n) by omega, advance_add, he, advance_halted P d hd]

theorem Flow.compile_coinFree {K : ℕ} (F : Flow.Program K)
    (hb : ∀ p, CoinFree (F.block p))
    (hn : ∀ p top bit, F.next p top bit = F.next p top false) : CoinFree (Flow.compile F) := by
  intro q top bit
  simp only [Flow.compile]
  cases (Flow.equiv F).symm q with
  | inl z => rcases z with ⟨p,q⟩; dsimp only; rw [hb p q top bit]
  | inr p => dsimp only; rw [hn p top bit]
end MeanPayoff.RegisterBits

namespace MeanPayoff.TreeDevice
open BinaryData RegisterBits
open BinaryData.Take (advance_add)

def store (x : Data) (suffix : List Bool) : Fin 5 → List Bool :=
  ![encode x ++ suffix, [], [], [], []]

def treeSize (x : Data) := (encode x).length

structure Device {α β : Type} (ea : α → Data) (eb : β → Data) (f : α → β) where
  program : RegisterBits.Program 5
  limit : α → ℕ
  quiet : CoinFree program
  correct : ∀ (x : α) (suffix out : List Bool) (bits : ℕ → Bool),
    advance program bits ⟨some program.start,store (ea x) suffix,out⟩ (limit x) =
      ⟨none,store (eb (f x)) suffix,out⟩

def skip : RegisterBits.Program 5 where
  states := 1
  start := 0
  read _ := 0
  transition _ _ _ := none

def identity {α : Type} (ea : α → Data) : Device ea ea id where
  program := skip
  limit _ := 1
  quiet := by intro q top bit; rfl
  correct := by intros; rfl

noncomputable abbrev compFlow {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α → β} {g : β → γ} (F : Device ea eb f) (G : Device eb ec g) : Flow.Program 5 where
  nodes := 2
  start := 0
  block := ![F.program,G.program]
  read _ := 0
  next p _ _ := if p = 0 then some ⟨1,.keep,none⟩ else none

noncomputable def compose {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α → β} {g : β → γ} (F : Device ea eb f) (G : Device eb ec g) : Device ea ec (g ∘ f) where
  program := Flow.compile (compFlow F G)
  limit x := F.limit x + G.limit (f x) + 2
  quiet := Flow.compile_coinFree _ (by intro p; fin_cases p; exact F.quiet; exact G.quiet)
    (by intros; rfl)
  correct x suffix out bits := by
    obtain ⟨s,hs,es⟩ := Flow.hop (compFlow F G) 0 1 (store (ea x) suffix) (store (eb (f x)) suffix) out bits
      (F.limit x) (F.correct x suffix out bits) (by intros; rfl)
    obtain ⟨t,ht,et⟩ := Flow.finish (compFlow F G) 1 (store (eb (f x)) suffix) (store (ec (g (f x))) suffix) out
      (fun j => bits (s+j)) (G.limit (f x)) (G.correct (f x) suffix out _) (by intros; rfl)
    apply advance_pad _ _ _ bits (n := s+t) (by omega) ?_ rfl
    change advance _ bits (Flow.state (compFlow F G) 0 (store (ea x) suffix) out) (s+t) = _
    rw [advance_add,es,et]
    rfl

theorem store_size (x : Data) (suffix : List Bool) :
    storeSize (store x suffix) = treeSize x + suffix.length := by
  simp [storeSize,store,treeSize,Fin.sum_univ_succ]

theorem output_size {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (x : α) :
    treeSize (eb (f x)) ≤ treeSize (ea x) + F.limit x := by
  have h := advance_size F.program ⟨some F.program.start,store (ea x) [],[]⟩ (fun _ => false) (F.limit x)
  rw [F.correct] at h
  simpa only [store_size,List.length_nil,Nat.add_zero] using h

end MeanPayoff.TreeDevice

namespace MeanPayoff.RegisterBits.Flow
open BinaryData.Take (advance_add)

theorem hop_update {K : ℕ} (P : Program K) (p q : Fin P.nodes)
    (s t u : Fin K → List Bool) (out : List Bool) (bits : ℕ → Bool) (N : ℕ) (op : BinaryStack.Op)
    (hm : advance (P.block p) bits ⟨some (P.block p).start,s,out⟩ N = ⟨none,t,out⟩)
    (hn : ∀ bit, P.next p (t (P.read p)).head? bit = some ⟨q,op,none⟩)
    (hu : Function.update t (P.read p) (BinaryStack.applyOp op (t (P.read p))) = u) :
    ∃ d ≤ N+1, advance (compile P) bits (state P p s out) d = state P q u out := by
  obtain ⟨d,hd,he⟩ := macro_runs P p s out bits N (by rw [hm])
  rw [hm] at he
  refine ⟨d+1, by omega, ?_⟩
  simp only [advance,he,step_boundary,hn,hu,Option.toList_none,List.append_nil]

end MeanPayoff.RegisterBits.Flow

namespace MeanPayoff.TreeDevice
open RegisterBits BinaryData
open BinaryData.Take (advance_add)

def core (a b c : List Bool) : Fin 5 → List Bool := ![a,b,c,[],[]]
@[simp] theorem core_zero (a b c : List Bool) : core a b c 0 = a := rfl
noncomputable def moveCode (i j : Fin 3) : RegisterBits.Program 5 := rename Take.program (slots i j)

theorem move01 (x : Data) (xs ys zs out : List Bool) (bits : ℕ → Bool) :
    advance (moveCode 0 1) bits ⟨some (moveCode 0 1).start,core (encode x++xs) ys zs,out⟩
      (6*treeSize x+3) = ⟨none,core xs (encode x++ys) zs,out⟩ := by
  have h := move_tree (0:Fin 3) 1 (by decide) (core (encode x++xs) ys zs) out x xs ys
    rfl rfl rfl rfl bits
  refine h.trans ?_
  apply Take.config_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem move02 (x : Data) (xs ys zs out : List Bool) (bits : ℕ → Bool) :
    advance (moveCode 0 2) bits ⟨some (moveCode 0 2).start,core (encode x++xs) ys zs,out⟩
      (6*treeSize x+3) = ⟨none,core xs ys (encode x++zs),out⟩ := by
  have h := move_tree (0:Fin 3) 2 (by decide) (core (encode x++xs) ys zs) out x xs zs
    rfl rfl rfl rfl bits
  refine h.trans ?_
  apply Take.config_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem move10 (x : Data) (xs ys zs out : List Bool) (bits : ℕ → Bool) :
    advance (moveCode 1 0) bits ⟨some (moveCode 1 0).start,core ys (encode x++xs) zs,out⟩
      (6*treeSize x+3) = ⟨none,core (encode x++ys) xs zs,out⟩ := by
  have h := move_tree (1:Fin 3) 0 (by decide) (core ys (encode x++xs) zs) out x xs ys
    rfl rfl rfl rfl bits
  refine h.trans ?_
  apply Take.config_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem move20 (x : Data) (xs ys zs out : List Bool) (bits : ℕ → Bool) :
    advance (moveCode 2 0) bits ⟨some (moveCode 2 0).start,core ys zs (encode x++xs),out⟩
      (6*treeSize x+3) = ⟨none,core (encode x++ys) zs xs,out⟩ := by
  have h := move_tree (2:Fin 3) 0 (by decide) (core ys zs (encode x++xs)) out x xs ys
    rfl rfl rfl rfl bits
  refine h.trans ?_
  apply Take.config_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

@[simp] theorem core_update (xs ys zs : List Bool) (op : BinaryStack.Op) :
    Function.update (core xs ys zs) 0 (BinaryStack.applyOp op xs) =
      core (BinaryStack.applyOp op xs) ys zs := by
  funext i; fin_cases i <;> rfl

def listTree {α : Type} (e : α → Data) : List α → Data
  | [] => .nil
  | x::xs => .pair (e x) (listTree e xs)

@[simp] theorem listTree_nil {α : Type} (e : α → Data) : listTree e [] = .nil := rfl
@[simp] theorem listTree_cons {α : Type} (e : α → Data) (x : α) (xs : List α) :
    listTree e (x::xs) = .pair (e x) (listTree e xs) := rfl

@[simp] theorem encode_listTree_cons {α : Type} (e : α → Data) (x : α) (xs : List α) :
    encode (listTree e (x::xs)) = true :: (encode (e x) ++ encode (listTree e xs)) := rfl

@[simp] theorem treeSize_nil : treeSize Data.nil = 1 := rfl
@[simp] theorem treeSize_pair (x y : Data) : treeSize (.pair x y) = treeSize x+treeSize y+1 := by
  simp [treeSize,BinaryData.encode]

theorem listTree_size {α : Type} (e : α → Data) (xs : List α) :
    treeSize (listTree e xs) = 1 + xs.length + (xs.map (treeSize ∘ e)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Function.comp_def]; omega

end MeanPayoff.TreeDevice

namespace MeanPayoff.RegisterBits
open BinaryData.Take (advance_add)

def Reaches {K : ℕ} (P : Program K) (c d : Config P) (B : ℕ) : Prop :=
  ∀ bits : ℕ → Bool, ∃ t ≤ B, advance P bits c t = d

theorem Reaches.trans {K : ℕ} {P : Program K} {a b c : Config P} {M N : ℕ}
    (h : Reaches P a b M) (g : Reaches P b c N) : Reaches P a c (M+N) := by
  intro bits
  obtain ⟨s,hs,es⟩ := h bits
  obtain ⟨t,ht,et⟩ := g (fun j => bits (s+j))
  refine ⟨s+t, by omega, ?_⟩
  rw [advance_add,es,et]

theorem Reaches.mono {K : ℕ} {P : Program K} {a b : Config P} {M N : ℕ}
    (h : Reaches P a b M) (hm : M ≤ N) : Reaches P a b N := by
  intro bits
  obtain ⟨t,ht,he⟩ := h bits
  exact ⟨t,ht.trans hm,he⟩

theorem Reaches.pad {K : ℕ} {P : Program K} {a b : Config P} {N : ℕ}
    (h : Reaches P a b N) (hb : b.control = none) (bits : ℕ → Bool) : advance P bits a N = b := by
  obtain ⟨t,ht,he⟩ := h bits
  exact advance_pad P a b bits ht he hb
end MeanPayoff.RegisterBits

namespace MeanPayoff.TreeDevice.Map
open RegisterBits BinaryData TreeDevice

noncomputable abbrev flow {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) : Flow.Program 5 where
  nodes := 12
  start := 0
  block := ![moveCode 0 2, F.program, moveCode 0 1, moveCode 0 2, moveCode 1 0,
    moveCode 2 0, moveCode 0 2, moveCode 0 1, moveCode 0 2, moveCode 1 0, moveCode 2 0, skip]
  read _ := 0
  next p top _ := match p.val with
    | 0 => some ⟨5,.push false,none⟩
    | 1 => some ⟨2,.keep,none⟩
    | 2 => some ⟨3,.keep,none⟩
    | 3 => some ⟨4,.keep,none⟩
    | 4 => some ⟨5,.push true,none⟩
    | 5 => some ⟨if top = some true then 1 else 6,.pop,none⟩
    | 6 => some ⟨10,.push false,none⟩
    | 7 => some ⟨8,.keep,none⟩
    | 8 => some ⟨9,.keep,none⟩
    | 9 => some ⟨10,.push true,none⟩
    | 10 => some ⟨if top = some true then 7 else 11,.pop,none⟩
    | _ => none

noncomputable abbrev program {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) := Flow.compile (flow F)

noncomputable abbrev cfg {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (q : Fin 12) (a b c out : List Bool) : Config (program F) :=
  Flow.state (flow F) q (core a b c) out

def revTime {β : Type} (e : β → Data) : List β → ℕ
  | [] => 12
  | x::xs => 6*treeSize (listTree e (x::xs)) + 12*treeSize (e x) +
      6*treeSize (listTree e xs) + 16 + revTime e xs

theorem reverse_runs {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (xs acc : List β) (suffix out : List Bool) :
    Reaches (program F) (cfg F 10 (encode (listTree eb acc)++suffix) [] (encode (listTree eb xs)) out)
      ⟨none,core (encode (listTree eb (xs.reverse++acc))++suffix) [] [],out⟩ (revTime eb xs) := by
  induction xs generalizing acc with
  | nil =>
    have hl : Reaches (program F)
        (cfg F 10 (encode (listTree eb acc)++suffix) [] (encode Data.nil) out)
        (cfg F 11 (encode (listTree eb acc)++suffix) [] [] out) 10 := by
      intro bits
      apply Flow.hop_update (flow F) 10 11 _ _ _ out bits 9 .pop
        (move20 .nil [] (encode (listTree eb acc)++suffix) [] out bits)
        (by intro bit; rfl)
      change Function.update (core _ _ _) 0 (BinaryStack.applyOp .pop _) = _
      simp only [core_zero,core_update]; rfl
    have hf : Reaches (program F) (cfg F 11 (encode (listTree eb acc)++suffix) [] [] out)
        ⟨none,core (encode (listTree eb acc)++suffix) [] [],out⟩ 2 := by
      intro bits
      exact Flow.finish (flow F) 11 _ _ out bits 1 rfl (by intros; rfl)
    exact hl.trans hf
  | cons x xs ih =>
    have h₀ : Reaches (program F)
        (cfg F 10 (encode (listTree eb acc)++suffix) [] (encode (listTree eb (x::xs))) out)
        (cfg F 7 (encode (eb x)++encode (listTree eb xs)++encode (listTree eb acc)++suffix) [] [] out)
        (6*treeSize (listTree eb (x::xs))+4) := by
      intro bits
      have h := Flow.hop_update (flow F) 10 7 _ _
        (core (encode (eb x)++encode (listTree eb xs)++encode (listTree eb acc)++suffix) [] []) out bits _ .pop
        (move20 (listTree eb (x::xs)) [] (encode (listTree eb acc)++suffix) [] out bits)
        (by intro bit; rfl)
        (by
          change Function.update (core _ _ _) 0 (BinaryStack.applyOp _ _) = _
          simp only [core_zero,core_update]
          simp only [listTree_cons,BinaryData.encode,List.cons_append,BinaryStack.applyOp,List.tail_cons,List.append_assoc])
      simpa only [List.append_nil,List.append_assoc,Nat.add_assoc] using h
    have h₁ : Reaches (program F)
        (cfg F 7 (encode (eb x)++encode (listTree eb xs)++encode (listTree eb acc)++suffix) [] [] out)
        (cfg F 8 (encode (listTree eb xs)++encode (listTree eb acc)++suffix) (encode (eb x)) [] out)
        (6*treeSize (eb x)+4) := by
      intro bits
      have h := Flow.hop (flow F) 7 8 _ _ out bits _
        (move01 (eb x) (encode (listTree eb xs)++encode (listTree eb acc)++suffix) [] [] out bits)
        (by intros; rfl)
      simpa only [List.append_nil,List.append_assoc,Nat.add_assoc] using h
    have h₂ : Reaches (program F)
        (cfg F 8 (encode (listTree eb xs)++encode (listTree eb acc)++suffix) (encode (eb x)) [] out)
        (cfg F 9 (encode (listTree eb acc)++suffix) (encode (eb x)) (encode (listTree eb xs)) out)
        (6*treeSize (listTree eb xs)+4) := by
      intro bits
      have h := Flow.hop (flow F) 8 9 _ _ out bits _
        (move02 (listTree eb xs) (encode (listTree eb acc)++suffix) (encode (eb x)) [] out bits)
        (by intros; rfl)
      simpa only [List.append_nil,List.append_assoc,Nat.add_assoc] using h
    have h₃ : Reaches (program F)
        (cfg F 9 (encode (listTree eb acc)++suffix) (encode (eb x)) (encode (listTree eb xs)) out)
        (cfg F 10 (encode (listTree eb (x::acc))++suffix) [] (encode (listTree eb xs)) out)
        (6*treeSize (eb x)+4) := by
      intro bits
      have h := Flow.hop_update (flow F) 9 10 _ _
        (core (encode (listTree eb (x::acc))++suffix) [] (encode (listTree eb xs))) out bits _ (.push true)
        (move10 (eb x) [] (encode (listTree eb acc)++suffix) (encode (listTree eb xs)) out bits)
        (by intro bit; rfl)
        (by
          change Function.update (core _ _ _) 0 (BinaryStack.applyOp _ _) = _
          simp only [core_zero,core_update]
          simp only [listTree_cons,BinaryData.encode,List.cons_append,BinaryStack.applyOp,List.append_assoc])
      simpa only [List.append_nil,List.append_assoc,Nat.add_assoc] using h
    have h := h₀.trans (h₁.trans (h₂.trans (h₃.trans (ih (x::acc)))))
    have h' := h.mono (show _ ≤ revTime eb (x::xs) by simp only [revTime]; omega)
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using h'

def frontTime {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) : List α → ℕ
  | [] => 10
  | x::xs => 6*treeSize (listTree ea (x::xs)) + 12*treeSize (eb (f x)) +
      6*treeSize (listTree ea xs) + F.limit x + 17 + frontTime F xs

theorem forward_runs {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (xs : List α) (acc : List β) (suffix out : List Bool) :
    Reaches (program F) (cfg F 5 (encode (listTree eb acc)++suffix) [] (encode (listTree ea xs)) out)
      (cfg F 6 (encode (listTree eb ((xs.map f).reverse++acc))++suffix) [] [] out)
       (frontTime F xs) := by
  induction xs generalizing acc with
  | nil =>
    intro bits
    apply Flow.hop_update (flow F) 5 6 _ _ _ out bits 9 .pop
      (move20 .nil [] (encode (listTree eb acc)++suffix) [] out bits)
      (by intro bit; rfl)
    change Function.update (core _ _ _) 0 (BinaryStack.applyOp .pop _) = _
    simp only [core_zero,core_update]; rfl
  | cons x xs ih =>
    have h₀ : Reaches (program F)
        (cfg F 5 (encode (listTree eb acc)++suffix) [] (encode (listTree ea (x::xs))) out)
        (cfg F 1 (encode (ea x)++encode (listTree ea xs)++encode (listTree eb acc)++suffix) [] [] out)
        (6*treeSize (listTree ea (x::xs))+4) := by
      intro bits
      have h := Flow.hop_update (flow F) 5 1 _ _
        (core (encode (ea x)++encode (listTree ea xs)++encode (listTree eb acc)++suffix) [] []) out bits _ .pop
        (move20 (listTree ea (x::xs)) [] (encode (listTree eb acc)++suffix) [] out bits)
        (by intro bit; rfl)
        (by
          change Function.update (core _ _ _) 0 (BinaryStack.applyOp _ _) = _
          simp only [core_zero,core_update]
          simp only [listTree_cons,BinaryData.encode,List.cons_append,BinaryStack.applyOp,List.tail_cons,List.append_assoc])
      simpa only [List.append_nil,List.append_assoc,Nat.add_assoc] using h
    have hF : Reaches (program F)
        (cfg F 1 (encode (ea x)++encode (listTree ea xs)++encode (listTree eb acc)++suffix) [] [] out)
        (cfg F 2 (encode (eb (f x))++encode (listTree ea xs)++encode (listTree eb acc)++suffix) [] [] out)
        (F.limit x+1) := by
      intro bits
      have h := Flow.hop (flow F) 1 2 _ _ out bits _
        (F.correct x (encode (listTree ea xs)++encode (listTree eb acc)++suffix) out bits)
        (by intros; rfl)
      simpa only [store,core,cfg,List.append_assoc] using h
    have h₁ : Reaches (program F)
        (cfg F 2 (encode (eb (f x))++encode (listTree ea xs)++encode (listTree eb acc)++suffix) [] [] out)
        (cfg F 3 (encode (listTree ea xs)++encode (listTree eb acc)++suffix) (encode (eb (f x))) [] out)
        (6*treeSize (eb (f x))+4) := by
      intro bits
      have h := Flow.hop (flow F) 2 3 _ _ out bits _
        (move01 (eb (f x)) (encode (listTree ea xs)++encode (listTree eb acc)++suffix) [] [] out bits)
        (by intros; rfl)
      simpa only [List.append_nil,List.append_assoc,Nat.add_assoc] using h
    have h₂ : Reaches (program F)
        (cfg F 3 (encode (listTree ea xs)++encode (listTree eb acc)++suffix) (encode (eb (f x))) [] out)
        (cfg F 4 (encode (listTree eb acc)++suffix) (encode (eb (f x))) (encode (listTree ea xs)) out)
        (6*treeSize (listTree ea xs)+4) := by
      intro bits
      have h := Flow.hop (flow F) 3 4 _ _ out bits _
        (move02 (listTree ea xs) (encode (listTree eb acc)++suffix) (encode (eb (f x))) [] out bits)
        (by intros; rfl)
      simpa only [List.append_nil,List.append_assoc,Nat.add_assoc] using h
    have h₃ : Reaches (program F)
        (cfg F 4 (encode (listTree eb acc)++suffix) (encode (eb (f x))) (encode (listTree ea xs)) out)
        (cfg F 5 (encode (listTree eb (f x::acc))++suffix) [] (encode (listTree ea xs)) out)
        (6*treeSize (eb (f x))+4) := by
      intro bits
      have h := Flow.hop_update (flow F) 4 5 _ _
        (core (encode (listTree eb (f x::acc))++suffix) [] (encode (listTree ea xs))) out bits _ (.push true)
        (move10 (eb (f x)) [] (encode (listTree eb acc)++suffix) (encode (listTree ea xs)) out bits)
        (by intro bit; rfl)
        (by
          change Function.update (core _ _ _) 0 (BinaryStack.applyOp _ _) = _
          simp only [core_zero,core_update]
          simp only [listTree_cons,BinaryData.encode,List.cons_append,BinaryStack.applyOp,List.append_assoc])
      simpa only [List.append_nil,List.append_assoc,Nat.add_assoc] using h
    have h := h₀.trans (hF.trans (h₁.trans (h₂.trans (h₃.trans (ih (f x::acc))))))
    have h' := h.mono (show _ ≤ frontTime F (x::xs) by simp only [frontTime]; omega)
    simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using h'

def limit {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (xs : List α) :=
  6*treeSize (listTree ea xs)+4+frontTime F xs+
    (6*treeSize (listTree eb (xs.map f).reverse)+4)+revTime eb (xs.map f).reverse

theorem runs {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (xs : List α) (suffix out : List Bool) :
    Reaches (program F) ⟨some (program F).start,store (listTree ea xs) suffix,out⟩
      ⟨none,store (listTree eb (xs.map f)) suffix,out⟩ (limit F xs) := by
  have h₀ : Reaches (program F) (cfg F 0 (encode (listTree ea xs)++suffix) [] [] out)
      (cfg F 5 (encode Data.nil++suffix) [] (encode (listTree ea xs)) out)
      (6*treeSize (listTree ea xs)+4) := by
    intro bits
    have h := Flow.hop_update (flow F) 0 5 _ _
      (core (encode Data.nil++suffix) [] (encode (listTree ea xs))) out bits _ (.push false)
      (move02 (listTree ea xs) suffix [] [] out bits) (by intros; rfl)
      (by change Function.update (core _ _ _) 0 (BinaryStack.applyOp _ _) = _
          simp only [core_zero,core_update,List.append_nil]; rfl)
    simpa only [List.append_nil,Nat.add_assoc] using h
  have h₁ := forward_runs F xs [] suffix out
  simp only [List.append_nil,listTree_nil] at h₁
  have h₂ : Reaches (program F)
      (cfg F 6 (encode (listTree eb (xs.map f).reverse)++suffix) [] [] out)
      (cfg F 10 (encode Data.nil++suffix) [] (encode (listTree eb (xs.map f).reverse)) out)
      (6*treeSize (listTree eb (xs.map f).reverse)+4) := by
    intro bits
    have h := Flow.hop_update (flow F) 6 10 _ _
      (core (encode Data.nil++suffix) [] (encode (listTree eb (xs.map f).reverse))) out bits _ (.push false)
      (move02 (listTree eb (xs.map f).reverse) suffix [] [] out bits) (by intros; rfl)
      (by change Function.update (core _ _ _) 0 (BinaryStack.applyOp _ _) = _
          simp only [core_zero,core_update,List.append_nil]; rfl)
    simpa only [List.append_nil,Nat.add_assoc] using h
  have h₃ := reverse_runs F (xs.map f).reverse [] suffix out
  simp only [List.reverse_reverse,List.append_nil,listTree_nil] at h₃
  have h := h₀.trans (h₁.trans (h₂.trans h₃))
  exact h.mono (by simp only [limit]; omega)

noncomputable def device {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) : Device (listTree ea) (listTree eb) (List.map f) where
  program := program F
  limit := limit F
  quiet := by
    apply Flow.compile_coinFree
    · intro p
      fin_cases p <;> first | exact F.quiet | (intro q top bit; rfl)
    · intros; rfl
  correct xs suffix out bits := (runs F xs suffix out).pad rfl bits

end MeanPayoff.TreeDevice.Map
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_VectorDevices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.TreeDevice
open BinaryData RegisterBits

theorem treeSize_pos (x : Data) : 0 < treeSize x := by
  cases x <;> simp

@[simp] theorem listTree_reverse_size {α : Type} (e : α → Data) (xs : List α) :
    treeSize (listTree e xs.reverse) = treeSize (listTree e xs) := by
  simp only [listTree_size,List.length_reverse,List.map_reverse,List.sum_reverse]

namespace Map

def resource {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (xs : List α) := treeSize (listTree ea xs)+(xs.map F.limit).sum

@[simp] theorem resource_nil {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) : resource F [] = 1 := rfl

@[simp] theorem resource_cons {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (x : α) (xs : List α) :
    resource F (x::xs) = resource F xs+treeSize (ea x)+F.limit x+1 := by
  simp only [resource,listTree_cons,treeSize_pair,List.map_cons,List.sum_cons]; omega

theorem input_size_le {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (xs : List α) : treeSize (listTree ea xs) ≤ resource F xs := Nat.le_add_right _ _

theorem output_size_le {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (xs : List α) : treeSize (listTree eb (xs.map f)) ≤ resource F xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have h := TreeDevice.output_size F x
    simp only [List.map_cons,listTree_cons,treeSize_pair,resource_cons]
    omega

theorem reverse_cost {β : Type} (e : β → Data) (xs : List β) :
    revTime e xs ≤ 52*treeSize (listTree e xs)^2 := by
  induction xs with
  | nil => norm_num [revTime]
  | cons x xs ih =>
    simp only [revTime,listTree_cons,treeSize_pair]
    have h := treeSize_pos (e x)
    nlinarith

theorem forward_cost {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (xs : List α) : frontTime F xs ≤ 64*(resource F xs)^2 := by
  induction xs with
  | nil => norm_num [frontTime]
  | cons x xs ih =>
    have h := TreeDevice.output_size F x
    have hY := input_size_le F xs
    simp only [frontTime,resource_cons,listTree_cons,treeSize_pair]
    nlinarith

theorem limit_le {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (xs : List α) : limit F xs ≤ 128*(resource F xs+1)^2 := by
  have hi := input_size_le F xs
  have ho := output_size_le F xs
  have hf := forward_cost F xs
  have hr := reverse_cost eb (xs.map f).reverse
  simp only [listTree_reverse_size] at hr
  have hs : treeSize (listTree eb (xs.map f))^2 ≤ (resource F xs)^2 := Nat.pow_le_pow_left ho 2
  simp only [limit,listTree_reverse_size]
  nlinarith

end Map
end MeanPayoff.TreeDevice

namespace MeanPayoff.RegisterBits

def quieten {K : ℕ} (P : Program K) : Program K where
  states := P.states
  start := P.start
  read := P.read
  transition q top _ := P.transition q top false

def quietConfig {K : ℕ} (P : Program K) (c : Config P) : Config (quieten P) :=
  ⟨c.control,c.stack,c.output⟩

theorem quieten_coinFree {K : ℕ} (P : Program K) : CoinFree (quieten P) := by intro q top bit; rfl

theorem quieten_step {K : ℕ} (P : Program K) (c : Config P) (bit : Bool) :
    step (quieten P) (quietConfig P c) bit = quietConfig P (step P c false) := by
  cases c with
  | mk control s out =>
    cases control with
    | none => rfl
    | some q =>
      simp only [step,quietConfig,quieten]
      cases P.transition q (s (P.read q)).head? false <;> rfl

theorem quieten_advance {K : ℕ} (P : Program K) (c : Config P) (bits : ℕ → Bool) (N : ℕ) :
    advance (quieten P) bits (quietConfig P c) N =
      quietConfig P (advance P (fun _ => false) c N) := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [advance,ih,quieten_step]

end MeanPayoff.RegisterBits

namespace MeanPayoff.TreeDevice
open BinaryData RegisterBits

def ofProgram {α β : Type} (ea : α → Data) (eb : β → Data) (f : α → β)
    (P : Program 5) (N : α → ℕ)
    (h : ∀ x suffix out bits,
      advance P bits ⟨some P.start,store (ea x) suffix,out⟩ (N x) =
        ⟨none,store (eb (f x)) suffix,out⟩) : Device ea eb f where
  program := quieten P
  limit := N
  quiet := quieten_coinFree P
  correct x suffix out bits := by
    change advance (quieten P) bits (quietConfig P ⟨some P.start,store (ea x) suffix,out⟩) (N x) = _
    rw [quieten_advance,h]; rfl

end MeanPayoff.TreeDevice

namespace MeanPayoff.WorkStack.RegisterCompile

theorem signed_compares (a b : SignedBits.Word) (out : List Bool) (bits : ℕ → Bool) :
    RegisterBits.advance (program SignedCompare.program) bits
      (lift SignedCompare.program out (SignedCompare.state .start (a.sign::a.digits) (b.sign::b.digits) []))
      (6*(max a.digits.length b.digits.length+3)) =
        lift SignedCompare.program out
          (SignedCompare.stopped (SignedBits.compare a.sign b.sign false a.digits b.digits) []) := by
  rw [advance_six,SignedCompare.program_compares]
end MeanPayoff.WorkStack.RegisterCompile

namespace MeanPayoff.ComparisonForest
open RegisterBits BinaryData WorkStack
open ArithmeticForest (placeA placeB placeAdd placeBox injectA injectB injectAdd injectBox
  installA installB installAdd installBox store0 store1 store2 unboxTime boxTime)
open BinaryData.Take (advance_add)

def test (a b : SignedBits.Word) := SignedBits.compare a.sign b.sign false a.digits b.digits

theorem test_eq (a b : SignedBits.Word) : test a b = decide (a.val < b.val) := by
  apply Bool.eq_iff_iff.mpr
  simp only [test,decide_eq_true_eq,SignedBits.compare_lt]

noncomputable abbrev flow : Flow.Program 5 where
  nodes := 4
  start := 0
  block q := match q with
    | 0 => rename Unbox.program placeA
    | 1 => rename Unbox.program placeB
    | 2 => rename (RegisterCompile.program SignedCompare.program) placeAdd
    | 3 => rename Box.program placeBox
  read _ := 4
  next q _ _ := match q with
    | 0 => some ⟨1,.keep,none⟩
    | 1 => some ⟨2,.keep,none⟩
    | 2 => some ⟨3,.keep,none⟩
    | 3 => none

noncomputable def program := Flow.compile flow

def store3 (a b : SignedBits.Word) (xs ys : List Bool) : Fin 5 → List Bool :=
  ![xs,ys,[test a b],[],[]]
def store4 (a b : SignedBits.Word) (xs ys : List Bool) : Fin 5 → List Bool :=
  ![xs,encode (listData [test a b])++ys,[],[],[]]

theorem stage2 (a b : SignedBits.Word) (xs ys out : List Bool) (bits : ℕ → Bool) :
    advance (flow.block 2) bits ⟨some (flow.block 2).start,store2 a b xs ys,out⟩
      (6*(max a.digits.length b.digits.length+3)) = ⟨none,store3 a b xs ys,out⟩ := by
  have h := rename_advance (RegisterCompile.program SignedCompare.program) placeAdd injectAdd
    (store2 a b xs ys) (RegisterCompile.lift SignedCompare.program out
      (SignedCompare.state .start (a.sign::a.digits) (b.sign::b.digits) []))
    bits (6*(max a.digits.length b.digits.length+3))
  rw [RegisterCompile.signed_compares] at h
  simp only [renamed,RegisterCompile.lift,SignedCompare.state,SignedCompare.stopped,
    installAdd,store2,Matrix.cons_val_zero,Matrix.cons_val_one] at h
  convert h using 1 <;> rfl

theorem stage3 (a b : SignedBits.Word) (xs ys out : List Bool) (bits : ℕ → Bool) :
    advance (flow.block 3) bits ⟨some (flow.block 3).start,store3 a b xs ys,out⟩
      (boxTime [test a b]) = ⟨none,store4 a b xs ys,out⟩ := by
  have h := rename_advance Box.program placeBox injectBox (store3 a b xs ys)
    (Box.cfg .reverse [test a b] ys [] out) bits (boxTime [test a b])
  rw [show boxTime [test a b] = 2*[test a b].length+2+feedCost [test a b]+1 by rfl,
    Box.boxes] at h
  simp only [renamed,Box.cfg,Box.stopped,installBox,store3,Matrix.cons_val_zero,Matrix.cons_val_three] at h
  convert h using 1 <;> rfl

theorem total_bound (a b : SignedBits.Word) :
    (unboxTime (a.sign::a.digits)+1)+(unboxTime (b.sign::b.digits)+1)+
      (6*(max a.digits.length b.digits.length+3)+1)+(boxTime [test a b]+1) ≤
        30*(a.digits.length+b.digits.length+3) := by
  have ha := Unbox.unboxes_bound (a.sign::a.digits)
  have hb := Unbox.unboxes_bound (b.sign::b.digits)
  have hc := Box.boxes_bound [test a b]
  simp only [List.length_cons,List.length_nil] at ha hb hc
  unfold unboxTime boxTime
  simp only [List.length_cons,List.length_nil]
  omega

theorem program_compares (a b : SignedBits.Word) (xs ys out : List Bool) (bits : ℕ → Bool) :
    ∃ t ≤ 30*(a.digits.length+b.digits.length+3),
      advance program bits ⟨some program.start,store0 a b xs ys,out⟩ t =
        ⟨none,store4 a b xs ys,out⟩ := by
  obtain ⟨t₀,h₀,e₀⟩ := Flow.hop flow 0 1 (store0 a b xs ys) (store1 a b xs ys) out bits
    (unboxTime (a.sign::a.digits)) (ArithmeticForest.stage0 a b xs ys out bits) (by intros; rfl)
  obtain ⟨t₁,h₁,e₁⟩ := Flow.hop flow 1 2 (store1 a b xs ys) (store2 a b xs ys) out
    (fun j => bits (t₀+j)) (unboxTime (b.sign::b.digits))
    (ArithmeticForest.stage1 a b xs ys out _) (by intros; rfl)
  obtain ⟨t₂,h₂,e₂⟩ := Flow.hop flow 2 3 (store2 a b xs ys) (store3 a b xs ys) out
    (fun j => bits (t₀+t₁+j)) (6*(max a.digits.length b.digits.length+3)) (stage2 a b xs ys out _)
    (by intros; rfl)
  obtain ⟨t₃,h₃,e₃⟩ := Flow.finish flow 3 (store3 a b xs ys) (store4 a b xs ys) out
    (fun j => bits (t₀+t₁+t₂+j)) (boxTime [test a b]) (stage3 a b xs ys out _) (by intros; rfl)
  refine ⟨t₀+t₁+t₂+t₃,le_trans (by omega) (total_bound a b),?_⟩
  change advance (Flow.compile flow) bits (Flow.state flow 0 (store0 a b xs ys) out) _ = _
  rw [BinaryData.Take.advance_add _ _ _ (t₀+t₁+t₂) t₃,BinaryData.Take.advance_add _ _ _ (t₀+t₁) t₂,
    BinaryData.Take.advance_add _ _ _ t₀ t₁,e₀,e₁,e₂,e₃]
  rfl

end MeanPayoff.ComparisonForest

namespace MeanPayoff.TreeDevice.Compare
open RegisterBits BinaryData
open BinaryData.Take (advance_add)

def pairWord (ab : SignedBits.Word × SignedBits.Word) : Data := .pair (wordData ab.1) (wordData ab.2)
def bitTree (b : Bool) : Data := listData [b]
def testPair (ab : SignedBits.Word × SignedBits.Word) : Bool := ComparisonForest.test ab.1 ab.2

noncomputable abbrev flow : Flow.Program 5 where
  nodes := 3
  start := 0
  block := ![skip, ComparisonForest.program, moveCode 1 0]
  read _ := 0
  next p _ _ := match p.val with
    | 0 => some ⟨1,.pop,none⟩
    | 1 => some ⟨2,.keep,none⟩
    | _ => none

noncomputable abbrev program := Flow.compile flow

def limit (ab : SignedBits.Word × SignedBits.Word) :=
  30*(ab.1.digits.length+ab.2.digits.length+3)+6*treeSize (bitTree (testPair ab))+7

theorem runs (ab : SignedBits.Word × SignedBits.Word) (suffix out : List Bool) :
    Reaches program ⟨some program.start,store (pairWord ab) suffix,out⟩
      ⟨none,store (bitTree (testPair ab)) suffix,out⟩ (limit ab) := by
  let s₀ := store (pairWord ab) suffix
  let s₁ := ArithmeticForest.store0 ab.1 ab.2 suffix []
  let s₂ := ComparisonForest.store4 ab.1 ab.2 suffix []
  have h₀ : Reaches program (Flow.state flow 0 s₀ out) (Flow.state flow 1 s₁ out) 2 := by
    intro bits
    exact Flow.hop_update flow 0 1 s₀ s₀ s₁ out bits 1 .pop rfl (by intros; rfl) (by
      change Function.update (core (encode (pairWord ab)++suffix) [] []) 0
        (BinaryStack.applyOp .pop (encode (pairWord ab)++suffix)) = _
      rw [core_update]
      simp only [pairWord,BinaryData.encode,List.cons_append,BinaryStack.applyOp,List.tail_cons]
      rfl)
  have h₁ : Reaches program (Flow.state flow 1 s₁ out) (Flow.state flow 2 s₂ out)
      (30*(ab.1.digits.length+ab.2.digits.length+3)+1) := by
    intro bits
    obtain ⟨t,ht,he⟩ := ComparisonForest.program_compares ab.1 ab.2 suffix [] out bits
    obtain ⟨d,hd,hdone⟩ := Flow.hop flow 1 2 s₁ s₂ out bits t he (by intros; rfl)
    exact ⟨d,by omega,hdone⟩
  have h₂ : Reaches program (Flow.state flow 2 s₂ out)
      ⟨none,store (bitTree (testPair ab)) suffix,out⟩ (6*treeSize (bitTree (testPair ab))+4) := by
    intro bits
    have h := Flow.finish flow 2 _ _ out bits _
      (move10 (bitTree (testPair ab)) [] suffix [] out bits) (by intros; rfl)
    simpa only [s₂,ComparisonForest.store4,bitTree,testPair,List.append_nil,Nat.add_assoc,core,store] using h
  exact (h₀.trans (h₁.trans h₂)).mono (by simp only [limit]; omega)

noncomputable def device : Device pairWord bitTree testPair :=
  ofProgram pairWord bitTree testPair program limit (fun ab suffix out bits => (runs ab suffix out).pad rfl bits)

theorem limit_le (ab : SignedBits.Word × SignedBits.Word) :
    limit ab ≤ 40*(ab.1.digits.length+ab.2.digits.length+4) := by
  have h := encode_list_length_le [testPair ab]
  simp only [List.length_cons,List.length_nil] at h
  unfold limit treeSize bitTree
  omega

theorem testPair_eq (ab : SignedBits.Word × SignedBits.Word) :
    testPair ab = decide (ab.1.val < ab.2.val) := ComparisonForest.test_eq ab.1 ab.2

end MeanPayoff.TreeDevice.Compare
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_LoopDevices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Forest
open RegisterBits BinaryData
open BinaryData.Take (advance_add)

def encode (xs : List Data) : List Bool := xs.flatMap BinaryData.encode
@[simp] theorem encode_nil : encode [] = [] := rfl
@[simp] theorem encode_cons (x : Data) (xs : List Data) :
    encode (x::xs) = BinaryData.encode x++encode xs := rfl
@[simp] theorem encode_append (a b : List Data) : encode (a++b) = encode a++encode b := List.flatMap_append

structure Layout where
  a : List Data
  b : List Data
  c : List Data

def stack (x : Layout) (suffix : List Bool) := core (encode x.a++suffix) (encode x.b) (encode x.c)

structure Segment {α : Type} (s t : α → Layout) where
  program : RegisterBits.Program 5
  limit : α → ℕ
  correct : ∀ x suffix out bits,
    advance program bits ⟨some program.start,stack (s x) suffix,out⟩ (limit x) =
      ⟨none,stack (t x) suffix,out⟩

noncomputable abbrev seqFlow {α : Type} {s t u : α → Layout} (P : Segment s t) (Q : Segment t u) :
    Flow.Program 5 where
  nodes := 2
  start := 0
  block := ![P.program,Q.program]
  read _ := 0
  next p _ _ := if p=0 then some ⟨1,.keep,none⟩ else none

noncomputable def Segment.seq {α : Type} {s t u : α → Layout} (P : Segment s t) (Q : Segment t u) :
    Segment s u where
  program := Flow.compile (seqFlow P Q)
  limit x := P.limit x+Q.limit x+2
  correct x suffix out bits := by
    obtain ⟨m,hm,he⟩ := Flow.hop (seqFlow P Q) 0 1 _ _ out bits _
      (P.correct x suffix out bits) (by intros; rfl)
    obtain ⟨n,hn,he'⟩ := Flow.finish (seqFlow P Q) 1 _ _ out (fun j => bits (m+j)) _
      (Q.correct x suffix out _) (by intros; rfl)
    apply advance_pad _ _ _ bits (n := m+n) (by omega) ?_ rfl
    change advance _ bits (Flow.state (seqFlow P Q) 0 _ out) _ = _
    rw [advance_add,he,he']

noncomputable def move01 {α : Type} (x : α → Data) (a b c : α → List Data) :
    Segment (fun z => ⟨x z::a z,b z,c z⟩) (fun z => ⟨a z,x z::b z,c z⟩) where
  program := moveCode 0 1
  limit z := 6*treeSize (x z)+3
  correct z suffix out bits := by
    simpa only [stack,encode_cons,List.append_assoc] using
      TreeDevice.move01 (x z) (encode (a z)++suffix) (encode (b z)) (encode (c z)) out bits

noncomputable def move02 {α : Type} (x : α → Data) (a b c : α → List Data) :
    Segment (fun z => ⟨x z::a z,b z,c z⟩) (fun z => ⟨a z,b z,x z::c z⟩) where
  program := moveCode 0 2
  limit z := 6*treeSize (x z)+3
  correct z suffix out bits := by
    simpa only [stack,encode_cons,List.append_assoc] using
      TreeDevice.move02 (x z) (encode (a z)++suffix) (encode (b z)) (encode (c z)) out bits

noncomputable def move10 {α : Type} (x : α → Data) (a b c : α → List Data) :
    Segment (fun z => ⟨a z,x z::b z,c z⟩) (fun z => ⟨x z::a z,b z,c z⟩) where
  program := moveCode 1 0
  limit z := 6*treeSize (x z)+3
  correct z suffix out bits := by
    simpa only [stack,encode_cons,List.append_assoc] using
      TreeDevice.move10 (x z) (encode (b z)) (encode (a z)++suffix) (encode (c z)) out bits

noncomputable def move20 {α : Type} (x : α → Data) (a b c : α → List Data) :
    Segment (fun z => ⟨a z,b z,x z::c z⟩) (fun z => ⟨x z::a z,b z,c z⟩) where
  program := moveCode 2 0
  limit z := 6*treeSize (x z)+3
  correct z suffix out bits := by
    simpa only [stack,encode_cons,List.append_assoc] using
      TreeDevice.move20 (x z) (encode (c z)) (encode (a z)++suffix) (encode (b z)) out bits

noncomputable def swap {α : Type} (x y : α → Data) (a : α → List Data) :
    Segment (fun z => ⟨x z::y z::a z,[],[]⟩) (fun z => ⟨y z::x z::a z,[],[]⟩) :=
  (move01 x (fun z => y z::a z) (fun _ => []) (fun _ => [])).seq
    ((move02 y a (fun z => [x z]) (fun _ => [])).seq
      ((move10 x a (fun _ => []) (fun z => [y z])).seq
        (move20 y (fun z => x z::a z) (fun _ => []) (fun _ => []))))

def bitOp (i : Fin 5) (op : BinaryStack.Op) : RegisterBits.Program 5 where
  states := 2
  start := 0
  read _ := i
  transition q _ _ := if q=0 then some ⟨1,op,none⟩ else none

theorem bitOp_runs (i : Fin 5) (op : BinaryStack.Op) (s : Fin 5 → List Bool)
    (out : List Bool) (bits : ℕ → Bool) :
    advance (bitOp i op) bits ⟨some (bitOp i op).start,s,out⟩ 2 =
      ⟨none,Function.update s i (BinaryStack.applyOp op (s i)),out⟩ := by
  simp [advance,RegisterBits.step,bitOp]

def unpair {α : Type} (x y : α → Data) (a b c : α → List Data) :
    Segment (fun z => ⟨Data.pair (x z) (y z)::a z,b z,c z⟩)
      (fun z => ⟨x z::y z::a z,b z,c z⟩) where
  program := bitOp 0 .pop
  limit _ := 2
  correct z suffix out bits := by
    rw [bitOp_runs]
    simp only [stack,encode_cons,BinaryData.encode,List.cons_append,List.append_assoc,core_zero,
      BinaryStack.applyOp,List.tail_cons]
    congr 1
    funext i; fin_cases i <;> rfl

def pair {α : Type} (x y : α → Data) (a b c : α → List Data) :
    Segment (fun z => ⟨x z::y z::a z,b z,c z⟩)
      (fun z => ⟨Data.pair (x z) (y z)::a z,b z,c z⟩) where
  program := bitOp 0 (.push true)
  limit _ := 2
  correct z suffix out bits := by
    rw [bitOp_runs]
    simp only [stack,encode_cons,BinaryData.encode,List.cons_append,List.append_assoc,core_zero,
      BinaryStack.applyOp]
    congr 1
    funext i; fin_cases i <;> rfl

noncomputable def applyDevice {α β γ : Type} {ea : β → Data} {eb : γ → Data} {f : β → γ}
    (F : Device ea eb f) (x : α → β) (a : α → List Data) :
    Segment (fun z => ⟨ea (x z)::a z,[],[]⟩) (fun z => ⟨eb (f (x z))::a z,[],[]⟩) where
  program := F.program
  limit z := F.limit (x z)
  correct z suffix out bits := by
    simpa only [store,stack,encode_cons,encode_nil,core,List.append_assoc] using
      F.correct (x z) (encode (a z)++suffix) out bits

noncomputable def toDevice {α β : Type} (ea : α → Data) (eb : β → Data) (f : α → β)
    (P : Segment (fun z => ⟨[ea z],[],[]⟩) (fun z => ⟨[eb (f z)],[],[]⟩)) : Device ea eb f :=
  ofProgram ea eb f P.program P.limit (by
    intros x suffix out bits
    simpa only [stack,encode_cons,encode_nil,List.append_nil,core,store] using P.correct x suffix out bits)

end MeanPayoff.TreeDevice.Forest
namespace MeanPayoff.TreeDevice.Forest
open RegisterBits BinaryData

noncomputable def copy01 {α : Type} (x : α → Data) (a b c : α → List Data) :
    Segment (fun z => ⟨x z::a z,b z,c z⟩) (fun z => ⟨x z::a z,x z::b z,c z⟩) where
  program := rename Copy.program (slots (0:Fin 3) 1)
  limit z := 7*treeSize (x z)+3
  correct z suffix out bits := by
    have h := copy_tree (0:Fin 3) 1 (by decide)
      (core (BinaryData.encode (x z)++(encode (a z)++suffix)) (encode (b z)) (encode (c z)))
      out (x z) (encode (a z)++suffix) (encode (b z)) rfl rfl rfl rfl bits
    simp only [stack,encode_cons,List.append_assoc]
    refine h.trans ?_
    apply Take.config_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl

noncomputable def duplicate {α : Type} (x : α → Data) (a : α → List Data) :
    Segment (fun z => ⟨x z::a z,[],[]⟩) (fun z => ⟨x z::x z::a z,[],[]⟩) :=
  (copy01 x a (fun _ => []) (fun _ => [])).seq
    (move10 x (fun z => x z::a z) (fun _ => []) (fun _ => []))

def erase (i : Fin 5) : RegisterBits.Program 5 where
  states := 1
  start := 0
  read _ := i
  transition _ top _ := match top with
    | none => none
    | some _ => some ⟨0,.pop,none⟩

theorem erase_runs (i : Fin 5) (s : Fin 5 → List Bool) (out : List Bool) (bits : ℕ → Bool) :
    advance (erase i) bits ⟨some (erase i).start,s,out⟩ ((s i).length+1) =
      ⟨none,Function.update s i [],out⟩ := by
  generalize hx : s i = xs
  induction xs generalizing s bits with
  | nil => simp [hx,advance,RegisterBits.step,erase]
  | cons b xs ih =>
    rw [show (b::xs).length+1 = 1+(xs.length+1) by simp; omega,Take.advance_add]
    have hs : advance (erase i) bits ⟨some (erase i).start,s,out⟩ 1 =
        ⟨some (erase i).start,Function.update s i xs,out⟩ := by
      simp [advance,RegisterBits.step,erase,hx,BinaryStack.applyOp]
    rw [hs,ih _ _ (by simp)]
    simp

noncomputable def drop {α : Type} (x : α → Data) (a : α → List Data) :
    Segment (fun z => ⟨x z::a z,[],[]⟩) (fun z => ⟨a z,[],[]⟩) :=
  (move01 x a (fun _ => []) (fun _ => [])).seq {
    program := erase 1
    limit z := treeSize (x z)+1
    correct := by
      intro z suffix out bits
      have h := erase_runs (1:Fin 5) (stack ⟨a z,[x z],[]⟩ suffix) out bits
      simp only [stack,encode_cons,encode_nil,List.append_nil] at h ⊢
      refine h.trans ?_
      apply Take.config_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · rfl }

end MeanPayoff.TreeDevice.Forest

namespace MeanPayoff.TreeDevice
open BinaryData Forest

def product {α β : Type} (ea : α → Data) (eb : β → Data) (x : α × β) : Data := .pair (ea x.1) (eb x.2)

noncomputable def pairMap {α β γ δ : Type} {ea : α → Data} {eb : β → Data}
    {ec : γ → Data} {ed : δ → Data} {f : α → β} {g : γ → δ}
    (F : Device ea eb f) (G : Device ec ed g) :
    Device (product ea ec) (product eb ed) (fun z : α × γ => (f z.1,g z.2)) :=
  toDevice _ _ _ <|
    (unpair (fun z : α × γ => ea z.1) (fun z : α × γ => ec z.2) (fun _ => []) (fun _ => []) (fun _ => [])).seq
      ((applyDevice F Prod.fst (fun z : α × γ => [ec z.2])).seq
        ((swap (fun z : α × γ => eb (f z.1)) (fun z : α × γ => ec z.2) (fun _ => [])).seq
          ((applyDevice G Prod.snd (fun z : α × γ => [eb (f z.1)])).seq
            ((swap (fun z : α × γ => ed (g z.2)) (fun z : α × γ => eb (f z.1)) (fun _ => [])).seq
              (pair (fun z : α × γ => eb (f z.1)) (fun z : α × γ => ed (g z.2)) (fun _ => []) (fun _ => []) (fun _ => []))))))

noncomputable def dup {α : Type} (ea : α → Data) : Device ea (product ea ea) (fun x => (x,x)) :=
  toDevice _ _ _ <| (duplicate ea (fun _ => [])).seq
    (pair ea ea (fun _ => []) (fun _ => []) (fun _ => []))

noncomputable def fanout {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α → β} {g : α → γ} (F : Device ea eb f) (G : Device ea ec g) :
    Device ea (product eb ec) (fun x => (f x,g x)) :=
  compose (dup ea) (pairMap F G)

noncomputable def first {α β : Type} (ea : α → Data) (eb : β → Data) :
    Device (product ea eb) ea Prod.fst :=
  toDevice _ _ _ <|
    (unpair (fun z : α × β => ea z.1) (fun z : α × β => eb z.2) (fun _ => []) (fun _ => []) (fun _ => [])).seq
      ((swap (fun z : α × β => ea z.1) (fun z : α × β => eb z.2) (fun _ => [])).seq
        (drop (fun z : α × β => eb z.2) (fun z : α × β => [ea z.1])))

noncomputable def second {α β : Type} (ea : α → Data) (eb : β → Data) :
    Device (product ea eb) eb Prod.snd :=
  toDevice _ _ _ <|
    (unpair (fun z : α × β => ea z.1) (fun z : α × β => eb z.2) (fun _ => []) (fun _ => []) (fun _ => [])).seq
      (drop (fun z : α × β => ea z.1) (fun z : α × β => [eb z.2]))

end MeanPayoff.TreeDevice
namespace MeanPayoff.TreeDevice.Fold
open RegisterBits BinaryData

noncomputable abbrev flow {α β : Type} {ea : α → Data} {eb : β → Data} {f : α × β → α}
    (F : Device (product ea eb) ea f) : Flow.Program 5 where
  nodes := 6
  start := 0
  block := ![skip,moveCode 0 1,skip,moveCode 1 0,F.program,moveCode 1 0]
  read _ := 0
  next p top _ := match p.val with
    | 0 => some ⟨1,.pop,none⟩
    | 1 => some ⟨2,.keep,none⟩
    | 2 => some ⟨if top=some true then 3 else 5,.pop,none⟩
    | 3 => some ⟨4,.push true,none⟩
    | 4 => some ⟨1,.keep,none⟩
    | _ => none

noncomputable abbrev program {α β : Type} {ea : α → Data} {eb : β → Data} {f : α × β → α}
    (F : Device (product ea eb) ea f) := Flow.compile (flow F)

noncomputable abbrev cfg {α β : Type} {ea : α → Data} {eb : β → Data} {f : α × β → α}
    (F : Device (product ea eb) ea f) (q : Fin 6) (a b out : List Bool) : Config (program F) :=
  Flow.state (flow F) q (core a b []) out

def fold {α β : Type} (f : α × β → α) (a : α) (xs : List β) := xs.foldl (fun a x => f (a,x)) a

def time {α β : Type} {ea : α → Data} {eb : β → Data} {f : α × β → α}
    (F : Device (product ea eb) ea f) (a : α) : List β → ℕ
  | [] => 12*treeSize (ea a)+10
  | b::bs => 12*treeSize (ea a)+F.limit (a,b)+11+time F (f (a,b)) bs

theorem loop {α β : Type} {ea : α → Data} {eb : β → Data} {f : α × β → α}
    (F : Device (product ea eb) ea f) (a : α) (xs : List β) (suffix out : List Bool) :
    Reaches (program F)
      (cfg F 1 (encode (ea a)++encode (listTree eb xs)++suffix) [] out)
      ⟨none,core (encode (ea (fold f a xs))++suffix) [] [],out⟩ (time F a xs) := by
  induction xs generalizing a with
  | nil =>
    have h₁ : Reaches (program F) (cfg F 1 (encode (ea a)++encode Data.nil++suffix) [] out)
        (cfg F 2 (encode Data.nil++suffix) (encode (ea a)) out) (6*treeSize (ea a)+4) := by
      intro bits
      simpa only [List.append_nil,List.append_assoc] using Flow.hop (flow F) 1 2 _ _ out bits _
        (move01 (ea a) (encode Data.nil++suffix) [] [] out bits) (by intros; rfl)
    have h₂ : Reaches (program F) (cfg F 2 (encode Data.nil++suffix) (encode (ea a)) out)
        (cfg F 5 suffix (encode (ea a)) out) 2 := by
      intro bits
      apply Flow.hop_update (flow F) 2 5 _ _ _ out bits 1 .pop rfl (by intros; rfl)
      change Function.update (core _ _ _) 0 (BinaryStack.applyOp .pop _) = _
      simp only [flow,advance,core_zero,core_update]; rfl
    have h₃ : Reaches (program F) (cfg F 5 suffix (encode (ea a)) out)
        ⟨none,core (encode (ea a)++suffix) [] [],out⟩ (6*treeSize (ea a)+4) := by
      intro bits
      simpa only [List.append_nil] using Flow.finish (flow F) 5 _ _ out bits _
        (move10 (ea a) [] suffix [] out bits) (by intros; rfl)
    exact (h₁.trans (h₂.trans h₃)).mono (by simp [time]; omega)
  | cons b bs ih =>
    let tail := encode (listTree eb bs)++suffix
    have h₁ : Reaches (program F)
        (cfg F 1 (encode (ea a)++encode (listTree eb (b::bs))++suffix) [] out)
        (cfg F 2 (encode (listTree eb (b::bs))++suffix) (encode (ea a)) out)
        (6*treeSize (ea a)+4) := by
      intro bits
      simpa only [List.append_nil,List.append_assoc] using Flow.hop (flow F) 1 2 _ _ out bits _
        (move01 (ea a) (encode (listTree eb (b::bs))++suffix) [] [] out bits) (by intros; rfl)
    have h₂ : Reaches (program F)
        (cfg F 2 (encode (listTree eb (b::bs))++suffix) (encode (ea a)) out)
        (cfg F 3 (encode (eb b)++tail) (encode (ea a)) out) 2 := by
      intro bits
      apply Flow.hop_update (flow F) 2 3 _ _ _ out bits 1 .pop rfl (by intros; rfl)
      change Function.update (core _ _ _) 0 (BinaryStack.applyOp .pop _) = _
      simp only [flow,advance,core_zero,core_update]
      simp only [listTree,BinaryData.encode,List.cons_append,BinaryStack.applyOp,List.tail_cons,
        List.append_assoc,tail]
    have h₃ : Reaches (program F) (cfg F 3 (encode (eb b)++tail) (encode (ea a)) out)
        (cfg F 4 (encode (product ea eb (a,b))++tail) [] out) (6*treeSize (ea a)+4) := by
      intro bits
      apply Flow.hop_update (flow F) 3 4 (core (encode (eb b)++tail) (encode (ea a)) [])
        (core (encode (ea a)++(encode (eb b)++tail)) [] [])
        (core (encode (product ea eb (a,b))++tail) [] []) out bits (6*treeSize (ea a)+3) (.push true)
        (by convert move10 (ea a) [] (encode (eb b)++tail) [] out bits using 1 <;> simp [flow])
        (by intros; rfl)
      change Function.update (core _ _ _) 0 (BinaryStack.applyOp (.push true) _) = _
      simp only [core_zero,core_update]
      simp only [product,BinaryData.encode,BinaryStack.applyOp,List.cons_append,List.append_assoc]
    have h₄ : Reaches (program F) (cfg F 4 (encode (product ea eb (a,b))++tail) [] out)
        (cfg F 1 (encode (ea (f (a,b)))++encode (listTree eb bs)++suffix) [] out)
        (F.limit (a,b)+1) := by
      intro bits
      simpa only [store,core,tail,List.append_assoc,cfg] using Flow.hop (flow F) 4 1 _ _ out bits _
        (F.correct (a,b) tail out bits) (by intros; rfl)
    exact (h₁.trans (h₂.trans (h₃.trans (h₄.trans (ih (f (a,b))))))).mono (by simp [time]; omega)

noncomputable def device {α β : Type} {ea : α → Data} {eb : β → Data} {f : α × β → α}
    (F : Device (product ea eb) ea f) :
    Device (product ea (listTree eb)) ea (fun z => fold f z.1 z.2) :=
  ofProgram _ _ _ (program F) (fun z => time F z.1 z.2+2) (by
    intro z suffix out bits
    have h₀ : Reaches (program F)
        ⟨some (program F).start,store (product ea (listTree eb) z) suffix,out⟩
        (cfg F 1 (encode (ea z.1)++encode (listTree eb z.2)++suffix) [] out) 2 := by
      intro bits
      apply Flow.hop_update (flow F) 0 1 _ _ _ out bits 1 .pop rfl (by intros; rfl)
      change Function.update (core _ _ _) 0 (BinaryStack.applyOp .pop _) = _
      simp only [flow,advance]
      simp only [product,BinaryData.encode,BinaryStack.applyOp,List.cons_append,List.append_assoc]
      funext i; fin_cases i <;> simp [store,core,BinaryData.encode,List.append_assoc]
    exact ((h₀.trans (loop F z.1 z.2 suffix out)).mono (by omega)).pad rfl bits)

end MeanPayoff.TreeDevice.Fold
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_OperatorDevices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Select
open RegisterBits BinaryData

def choose {α : Type} (z : Bool × (α × α)) : α := if z.1 then z.2.1 else z.2.2

noncomputable abbrev flow {α : Type} (ea : α → Data) : Flow.Program 5 where
  nodes := 9
  start := 0
  block := ![skip,skip,skip,skip,skip,skip,skip,(first ea ea).program,(second ea ea).program]
  read _ := 0
  next p top _ := match p.val with
    | 0 => some ⟨1,.pop,none⟩
    | 1 => some ⟨2,.pop,none⟩
    | 2 => some ⟨if top=some true then 3 else 6,.pop,none⟩
    | 3 => some ⟨4,.pop,none⟩
    | 4 => some ⟨5,.pop,none⟩
    | 5 => some ⟨7,.pop,none⟩
    | 6 => some ⟨8,.pop,none⟩
    | _ => none

noncomputable abbrev program {α : Type} (ea : α → Data) := Flow.compile (flow ea)
noncomputable abbrev cfg {α : Type} (ea : α → Data) (q : Fin 9) (s out : List Bool) :=
  Flow.state (flow ea) q (core s [] []) out

theorem popHop {α : Type} (ea : α → Data) (p q : Fin 9) (b : Bool) (xs out : List Bool)
    (hblock : (flow ea).block p = skip)
    (hnext : ∀ bit, (flow ea).next p (some b) bit = some ⟨q,.pop,none⟩) :
    Reaches (program ea) (cfg ea p (b::xs) out) (cfg ea q xs out) 2 := by
  intro bits
  apply Flow.hop_update (flow ea) p q (core (b::xs) [] []) (core (b::xs) [] [])
    (core xs [] []) out bits 1 .pop (by rw [hblock]; rfl) hnext
  change Function.update (core _ _ _) 0 (BinaryStack.applyOp .pop _) = _
  simp only [core_zero,core_update]; rfl

noncomputable def limit {α : Type} (ea : α → Data) (z : Bool × (α × α)) :=
  13 + max ((first ea ea).limit z.2) ((second ea ea).limit z.2)

theorem runs {α : Type} (ea : α → Data) (z : Bool × (α × α)) (suffix out : List Bool) :
    Reaches (program ea)
      ⟨some (program ea).start,store (product Compare.bitTree (product ea ea) z) suffix,out⟩
      ⟨none,store (ea (choose z)) suffix,out⟩ (limit ea z) := by
  rcases z with ⟨b,x,y⟩
  let tail := encode (product ea ea (x,y))++suffix
  have ht : Reaches (program ea) (cfg ea 7 tail out)
      ⟨none,store (ea x) suffix,out⟩ ((first ea ea).limit (x,y)+1) := by
    intro bits
    exact Flow.finish (flow ea) 7 _ _ out bits _ ((first ea ea).correct (x,y) suffix out bits)
      (by intros; rfl)
  have hf : Reaches (program ea) (cfg ea 8 tail out)
      ⟨none,store (ea y) suffix,out⟩ ((second ea ea).limit (x,y)+1) := by
    intro bits
    exact Flow.finish (flow ea) 8 _ _ out bits _ ((second ea ea).correct (x,y) suffix out bits)
      (by intros; rfl)
  cases b
  · have h₀ := popHop ea 0 1 true (true::false::false::tail) out rfl (by intros; rfl)
    have h₁ := popHop ea 1 2 true (false::false::tail) out rfl (by intros; rfl)
    have h₂ := popHop ea 2 6 false (false::tail) out rfl (by intros; rfl)
    have h₃ := popHop ea 6 8 false tail out rfl (by intros; rfl)
    exact (h₀.trans (h₁.trans (h₂.trans (h₃.trans hf)))).mono (by
      dsimp only [limit]; have := le_max_right ((first ea ea).limit (x,y)) ((second ea ea).limit (x,y)); omega)
  · have h₀ := popHop ea 0 1 true (true::true::false::false::false::tail) out rfl (by intros; rfl)
    have h₁ := popHop ea 1 2 true (true::false::false::false::tail) out rfl (by intros; rfl)
    have h₂ := popHop ea 2 3 true (false::false::false::tail) out rfl (by intros; rfl)
    have h₃ := popHop ea 3 4 false (false::false::tail) out rfl (by intros; rfl)
    have h₄ := popHop ea 4 5 false (false::tail) out rfl (by intros; rfl)
    have h₅ := popHop ea 5 7 false tail out rfl (by intros; rfl)
    exact (h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans ht)))))).mono (by
      dsimp only [limit]; have := le_max_left ((first ea ea).limit (x,y)) ((second ea ea).limit (x,y)); omega)

noncomputable def device {α : Type} (ea : α → Data) :
    Device (product Compare.bitTree (product ea ea)) ea choose :=
  ofProgram _ _ _ (program ea) (limit ea) (fun z suffix out bits => (runs ea z suffix out).pad rfl bits)

end MeanPayoff.TreeDevice.Select
namespace MeanPayoff.TreeDevice
open BinaryData

def Device.extFun {α β : Type} {ea : α → Data} {eb : β → Data} {f g : α → β}
    (F : Device ea eb f) (h : ∀ x, f x = g x) : Device ea eb g where
  program := F.program
  limit := F.limit
  quiet := F.quiet
  correct x suffix out bits := by rw [← h x]; exact F.correct x suffix out bits

namespace Order

def low (ab : SignedBits.Word × SignedBits.Word) : SignedBits.Word :=
  if Compare.testPair ab then ab.1 else ab.2

def high (ab : SignedBits.Word × SignedBits.Word) : SignedBits.Word :=
  if Compare.testPair ab then ab.2 else ab.1

noncomputable def minDevice : Device (product wordData wordData) wordData low :=
  compose (fanout Compare.device (identity (product wordData wordData))) (Select.device wordData)

noncomputable def swapDevice : Device (product wordData wordData) (product wordData wordData)
    (fun z => (z.2,z.1)) := fanout (second wordData wordData) (first wordData wordData)

noncomputable def maxDevice : Device (product wordData wordData) wordData high :=
  compose (fanout Compare.device swapDevice) (Select.device wordData)

end Order
end MeanPayoff.TreeDevice
namespace MeanPayoff.TreeDevice.Add
open RegisterBits BinaryData
open BinaryData.Take (advance_add)

def pairWord (ab : SignedBits.Word × SignedBits.Word) : Data := .pair (wordData ab.1) (wordData ab.2)
def sumPair (ab : SignedBits.Word × SignedBits.Word) : SignedBits.Word := ArithmeticForest.addWord ab.1 ab.2

noncomputable abbrev flow : Flow.Program 5 where
  nodes := 3
  start := 0
  block := ![skip, ArithmeticForest.program, moveCode 1 0]
  read _ := 0
  next p _ _ := match p.val with
    | 0 => some ⟨1,.pop,none⟩
    | 1 => some ⟨2,.keep,none⟩
    | _ => none

noncomputable abbrev program := Flow.compile flow

def limit (ab : SignedBits.Word × SignedBits.Word) :=
  30*(ab.1.digits.length+ab.2.digits.length+3)+6*treeSize (wordData (sumPair ab))+7

theorem runs (ab : SignedBits.Word × SignedBits.Word) (suffix out : List Bool) :
    Reaches program ⟨some program.start,store (pairWord ab) suffix,out⟩
      ⟨none,store (wordData (sumPair ab)) suffix,out⟩ (limit ab) := by
  let s₀ := store (pairWord ab) suffix
  let s₁ := ArithmeticForest.store0 ab.1 ab.2 suffix []
  let s₂ := ArithmeticForest.store4 ab.1 ab.2 suffix []
  have h₀ : Reaches program (Flow.state flow 0 s₀ out) (Flow.state flow 1 s₁ out) 2 := by
    intro bits
    exact Flow.hop_update flow 0 1 s₀ s₀ s₁ out bits 1 .pop rfl (by intros; rfl) (by
      change Function.update (core (encode (pairWord ab)++suffix) [] []) 0
        (BinaryStack.applyOp .pop (encode (pairWord ab)++suffix)) = _
      rw [core_update]
      simp only [pairWord,BinaryData.encode,List.cons_append,BinaryStack.applyOp,List.tail_cons]
      rfl)
  have h₁ : Reaches program (Flow.state flow 1 s₁ out) (Flow.state flow 2 s₂ out)
      (30*(ab.1.digits.length+ab.2.digits.length+3)+1) := by
    intro bits
    obtain ⟨t,ht,he⟩ := ArithmeticForest.program_adds ab.1 ab.2 suffix [] out bits
    obtain ⟨d,hd,hdone⟩ := Flow.hop flow 1 2 s₁ s₂ out bits t he (by intros; rfl)
    exact ⟨d,by omega,hdone⟩
  have h₂ : Reaches program (Flow.state flow 2 s₂ out)
      ⟨none,store (wordData (sumPair ab)) suffix,out⟩ (6*treeSize (wordData (sumPair ab))+4) := by
    intro bits
    have h := Flow.finish flow 2 _ _ out bits _
      (move10 (wordData (sumPair ab)) [] suffix [] out bits) (by intros; rfl)
    simpa only [s₂,ArithmeticForest.store4,wordData,sumPair,List.append_nil,Nat.add_assoc,core,store] using h
  exact (h₀.trans (h₁.trans h₂)).mono (by simp only [limit]; omega)

noncomputable def device : Device pairWord wordData sumPair :=
  ofProgram pairWord wordData sumPair program limit (fun ab suffix out bits => (runs ab suffix out).pad rfl bits)

theorem sumPair_val (ab : SignedBits.Word × SignedBits.Word) :
    (sumPair ab).val = ab.1.val + ab.2.val := by
  simpa only [sumPair,ArithmeticForest.addWord,Bool.toNat_false,Nat.cast_zero,add_zero] using
    SignedBits.add_val ab.1.sign ab.2.sign false ab.1.digits ab.2.digits

end MeanPayoff.TreeDevice.Add

namespace MeanPayoff.TreeDevice
open BinaryData

theorem compose_limit {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α → β} {g : β → γ} (F : Device ea eb f) (G : Device eb ec g) (x : α) :
    (compose F G).limit x = F.limit x+G.limit (f x)+2 := rfl

theorem dup_limit {α : Type} (ea : α → Data) (x : α) :
    (dup ea).limit x = 13*treeSize (ea x)+12 := by
  dsimp [dup,Forest.toDevice,ofProgram,Forest.Segment.seq,Forest.duplicate,Forest.copy01,
    Forest.move10,Forest.pair]
  omega

theorem pairMap_limit {α β γ δ : Type} {ea : α → Data} {eb : β → Data}
    {ec : γ → Data} {ed : δ → Data} {f : α → β} {g : γ → δ}
    (F : Device ea eb f) (G : Device ec ed g) (x : α) (y : γ) :
    (pairMap F G).limit (x,y) = F.limit x+G.limit y+24*treeSize (eb (f x))+
      12*treeSize (ec y)+12*treeSize (ed (g y))+50 := by
  dsimp [pairMap,Forest.toDevice,ofProgram,Forest.Segment.seq,Forest.unpair,Forest.swap,
    Forest.move01,Forest.move02,Forest.move10,Forest.move20,Forest.applyDevice,Forest.pair]
  omega

theorem fanout_limit {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α → β} {g : α → γ} (F : Device ea eb f) (G : Device ea ec g) (x : α) :
    (fanout F G).limit x = F.limit x+G.limit x+25*treeSize (ea x)+24*treeSize (eb (f x))+
      12*treeSize (ec (g x))+64 := by
  rw [fanout,compose_limit,dup_limit,pairMap_limit]
  omega

theorem first_limit {α β : Type} (ea : α → Data) (eb : β → Data) (x : α) (y : β) :
    (first ea eb).limit (x,y) = 12*treeSize (ea x)+19*treeSize (eb y)+30 := by
  dsimp [first,Forest.toDevice,ofProgram,Forest.Segment.seq,Forest.unpair,Forest.swap,
    Forest.move01,Forest.move02,Forest.move10,Forest.move20,Forest.drop]
  omega

theorem second_limit {α β : Type} (ea : α → Data) (eb : β → Data) (x : α) (y : β) :
    (second ea eb).limit (x,y) = 7*treeSize (ea x)+10 := by
  dsimp [second,Forest.toDevice,ofProgram,Forest.Segment.seq,Forest.unpair,Forest.drop,Forest.move01]
  omega

theorem Select.limit_le {α : Type} (ea : α → Data) (z : Bool × (α × α)) :
    Select.limit ea z ≤ 19*(treeSize (ea z.2.1)+treeSize (ea z.2.2))+43 := by
  rcases z with ⟨b,x,y⟩
  dsimp only [Select.limit]
  rw [first_limit,second_limit]
  omega

theorem wordSize_bound (w : SignedBits.Word) : treeSize (wordData w) ≤ 4*w.digits.length+5 := by
  have h := encode_list_length_le (w.sign::w.digits)
  simpa [treeSize,wordData,Nat.mul_add,Nat.add_assoc] using h

theorem digits_le_wordSize (w : SignedBits.Word) : w.digits.length ≤ treeSize (wordData w) := by
  have h (xs : List Bool) : xs.length ≤ treeSize (listData xs) := by
    induction xs with
    | nil => simp
    | cons b bs ih =>
      cases b <;> simp only [listData,treeSize_pair,boolData,List.length_cons] <;> omega
  have := h (w.sign::w.digits)
  simpa only [List.length_cons,wordData] using le_trans (Nat.le_succ w.digits.length) this

end MeanPayoff.TreeDevice

namespace MeanPayoff.TreeDevice.EdgeScan
open BinaryData

abbrev Pair := SignedBits.Word × SignedBits.Word

def maxScan (z : Pair × List Pair) : SignedBits.Word :=
  Fold.fold Order.high (Add.sumPair z.1) (z.2.map Add.sumPair)

def minScan (z : Pair × List Pair) : SignedBits.Word :=
  Fold.fold Order.low (Add.sumPair z.1) (z.2.map Add.sumPair)

noncomputable def maxDevice :
    Device (product (product wordData wordData) (listTree (product wordData wordData))) wordData maxScan :=
  compose (pairMap Add.device (Map.device Add.device)) (Fold.device Order.maxDevice)

noncomputable def minDevice :
    Device (product (product wordData wordData) (listTree (product wordData wordData))) wordData minScan :=
  compose (pairMap Add.device (Map.device Add.device)) (Fold.device Order.minDevice)

theorem high_mem (z : SignedBits.Word × SignedBits.Word) : Order.high z = z.1 ∨ Order.high z = z.2 := by
  unfold Order.high
  split <;> simp

theorem low_mem (z : SignedBits.Word × SignedBits.Word) : Order.low z = z.1 ∨ Order.low z = z.2 := by
  unfold Order.low
  split <;> simp

theorem fold_mem (f : SignedBits.Word × SignedBits.Word → SignedBits.Word)
    (hf : ∀ z, f z=z.1 ∨ f z=z.2) (a : SignedBits.Word) (xs : List SignedBits.Word) :
    Fold.fold f a xs ∈ a::xs := by
  induction xs generalizing a with
  | nil => simp [Fold.fold]
  | cons b bs ih =>
    change Fold.fold f (f (a,b)) bs ∈ a::b::bs
    rcases List.mem_cons.mp (ih (f (a,b))) with h | h
    · rw [h]
      rcases hf (a,b) with h | h <;> simp [h]
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

end MeanPayoff.TreeDevice.EdgeScan
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Sorting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.RegisterBits.Flow

theorem finish_at {K : ℕ} (P : Program K) (p : Fin P.nodes) (s t : Fin K → List Bool)
    (out : List Bool) (bits : ℕ → Bool) (N : ℕ)
    (hm : advance (P.block p) bits ⟨some (P.block p).start,s,out⟩ N = ⟨none,t,out⟩)
    (hn : ∀ bit, P.next p (t (P.read p)).head? bit = none) :
    ∃ d ≤ N+1, advance (compile P) bits (state P p s out) d = ⟨none,t,out⟩ := by
  obtain ⟨d,hd,he⟩ := macro_runs P p s out bits N (by rw [hm])
  rw [hm] at he
  refine ⟨d+1,by omega,?_⟩
  simp only [advance,he,step_boundary,hn]

end MeanPayoff.RegisterBits.Flow

namespace MeanPayoff.TreeDevice.Tail
open RegisterBits BinaryData

noncomputable abbrev discard {α : Type} (ea : α → Data) := Forest.drop ea (fun _ => [])

noncomputable abbrev flow {α : Type} (ea : α → Data) : Flow.Program 5 where
  nodes := 2
  start := 0
  block := ![skip,(discard ea).program]
  read _ := 0
  next p top _ := if p=0 ∧ top=some true then some ⟨1,.pop,none⟩ else none

noncomputable abbrev program {α : Type} (ea : α → Data) := Flow.compile (flow ea)

noncomputable def limit {α : Type} (ea : α → Data) : List α → ℕ
  | [] => 2
  | x::_ => (discard ea).limit x+3

theorem runs {α : Type} (ea : α → Data) (xs : List α) (suffix out : List Bool) :
    Reaches (program ea) ⟨some (program ea).start,store (listTree ea xs) suffix,out⟩
      ⟨none,store (listTree ea xs.tail) suffix,out⟩ (limit ea xs) := by
  cases xs with
  | nil =>
    intro bits
    exact Flow.finish_at (flow ea) 0 _ _ out bits 1 rfl (by intros; rfl)
  | cons x xs =>
    let s₀ := store (listTree ea (x::xs)) suffix
    let s₁ := core (encode (ea x)++(encode (listTree ea xs)++suffix)) [] []
    have h₀ : Reaches (program ea) (Flow.state (flow ea) 0 s₀ out)
        (Flow.state (flow ea) 1 s₁ out) 2 := by
      intro bits
      apply Flow.hop_update (flow ea) 0 1 s₀ s₀ s₁ out bits 1 .pop rfl (by intros; rfl)
      change Function.update (core (encode (listTree ea (x::xs))++suffix) [] []) 0
        (BinaryStack.applyOp .pop (encode (listTree ea (x::xs))++suffix)) = s₁
      rw [core_update]
      simp only [encode_listTree_cons,List.cons_append,BinaryStack.applyOp,List.tail_cons]
      simp only [List.append_assoc]
      rfl
    have h₁ : Reaches (program ea) (Flow.state (flow ea) 1 s₁ out)
        ⟨none,store (listTree ea xs) suffix,out⟩ ((discard ea).limit x+1) := by
      intro bits
      have h := (discard ea).correct x (encode (listTree ea xs)++suffix) out bits
      simp only [Forest.stack,Forest.encode_cons,Forest.encode_nil,List.append_nil] at h
      exact Flow.finish (flow ea) 1 _ _ out bits _ h (by intros; rfl)
    exact (h₀.trans h₁).mono (by dsimp only [limit]; omega)

noncomputable def device {α : Type} (ea : α → Data) :
    Device (listTree ea) (listTree ea) List.tail :=
  ofProgram _ _ _ (program ea) (limit ea) (fun xs suffix out bits => (runs ea xs suffix out).pad rfl bits)

end MeanPayoff.TreeDevice.Tail

namespace MeanPayoff.TreeDevice.Halve
open BinaryData

def halve (w : SignedBits.Word) : SignedBits.Word := ⟨w.sign,w.digits.tail⟩

theorem listTree_boolData (bs : List Bool) : listTree boolData bs = listData bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [listTree_cons,listData,ih]

end MeanPayoff.TreeDevice.Halve
namespace MeanPayoff.TreeDevice
open RegisterBits BinaryData

def Device.recode {α β γ δ : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (ec : γ → Data) (ed : δ → Data) (i : γ → α) (h : γ → δ)
    (hin : ∀ x, ea (i x) = ec x) (hout : ∀ x, eb (f (i x)) = ed (h x)) : Device ec ed h where
  program := F.program
  limit x := F.limit (i x)
  quiet := F.quiet
  correct x suffix out bits := by
    rw [← hin x,← hout x]
    exact F.correct (i x) suffix out bits

noncomputable def pairSwap {α β : Type} (ea : α → Data) (eb : β → Data) :
    Device (product ea eb) (product eb ea) (fun z => (z.2,z.1)) :=
  fanout (second ea eb) (first ea eb)

namespace Forest

def pushNil {α : Type} (x : α → Data) :
    Segment (fun z => ⟨[x z],[],[]⟩) (fun z => ⟨[Data.nil,x z],[],[]⟩) where
  program := bitOp 0 (.push false)
  limit _ := 2
  correct z suffix out bits := by
    rw [bitOp_runs]
    simp only [stack,encode_cons,encode_nil,List.append_nil,BinaryData.encode,List.cons_append,
      core_zero,BinaryStack.applyOp]
    apply Take.config_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl

end Forest
namespace Lists

noncomputable def nilPrefix {α β : Type} (ea : α → Data) (eb : β → Data) :
    Device ea (product (listTree eb) ea) (fun x => ([],x)) :=
  Forest.toDevice _ _ _ <| (Forest.pushNil ea).seq
    (Forest.pair (fun _ => Data.nil) ea (fun _ => []) (fun _ => []) (fun _ => []))

noncomputable def nilSuffix {α β : Type} (ea : α → Data) (eb : β → Data) :
    Device ea (product ea (listTree eb)) (fun x => (x,[])) :=
  compose (nilPrefix ea eb) (pairSwap (listTree eb) ea)

def consDevice {α : Type} (ea : α → Data) :
    Device (product ea (listTree ea)) (listTree ea) (fun z => z.1::z.2) :=
  (identity (product ea (listTree ea))).recode _ _ id (fun z => z.1::z.2)
    (by intros; rfl) (by intros; rfl)

noncomputable def consAcc {α : Type} (ea : α → Data) :
    Device (product (listTree ea) ea) (listTree ea) (fun z => z.2::z.1) :=
  compose (pairSwap (listTree ea) ea) (consDevice ea)

noncomputable def reverseDevice {α : Type} (ea : α → Data) :
    Device (listTree ea) (listTree ea) List.reverse :=
  (compose (nilPrefix (listTree ea) ea) (Fold.device (consAcc ea))).extFun (by
    intro xs
    exact List.foldl_cons_nil)

end Lists
end MeanPayoff.TreeDevice

namespace MeanPayoff.TreeDevice.Sort
open BinaryData

abbrev W := SignedBits.Word
abbrev Acc := W × List W
abbrev InStep := Acc × W

def carryStep (z : InStep) : Acc :=
  (Order.high (z.1.1,z.2),Order.low (z.1.1,z.2)::z.1.2)

noncomputable def pairDevice : Device (product (product wordData (listTree wordData)) wordData)
    (product wordData wordData) (fun z : InStep => (z.1.1,z.2)) :=
  fanout (compose (first (product wordData (listTree wordData)) wordData)
    (first wordData (listTree wordData))) (second (product wordData (listTree wordData)) wordData)

noncomputable def tailDevice : Device (product (product wordData (listTree wordData)) wordData)
    (listTree wordData) (fun z : InStep => z.1.2) :=
  compose (first (product wordData (listTree wordData)) wordData) (second wordData (listTree wordData))

noncomputable def carryDevice : Device (product (product wordData (listTree wordData)) wordData)
    (product wordData (listTree wordData)) carryStep :=
  fanout (compose pairDevice Order.maxDevice)
    (compose (fanout (compose pairDevice Order.minDevice) tailDevice) (Lists.consDevice wordData))

def insert (z : W × List W) : List W :=
  let a := Fold.fold carryStep (z.1,[]) z.2
  (a.1::a.2).reverse

noncomputable def initialDevice : Device (product wordData (listTree wordData))
    (product (product wordData (listTree wordData)) (listTree wordData))
    (fun z : W × List W => ((z.1,[]),z.2)) :=
  fanout (compose (first wordData (listTree wordData)) (Lists.nilSuffix wordData wordData))
    (second wordData (listTree wordData))

noncomputable def insertDevice : Device (product wordData (listTree wordData)) (listTree wordData) insert :=
  compose initialDevice (compose (Fold.device carryDevice)
    (compose (Lists.consDevice wordData) (Lists.reverseDevice wordData)))

def sort (xs : List W) : List W := xs.foldl (fun a w => insert (w,a)) []

noncomputable def sortDevice : Device (listTree wordData) (listTree wordData) sort := by
  let P := compose (Lists.nilPrefix (listTree wordData) wordData)
    (Fold.device (compose (pairSwap (listTree wordData) wordData) insertDevice))
  exact P.extFun (by intro xs; rfl)

def bubble (w : W) : List W → List W
  | [] => [w]
  | x::xs => Order.low (w,x)::bubble (Order.high (w,x)) xs

theorem fold_carry (w : W) (xs acc : List W) :
    let a := Fold.fold carryStep (w,acc) xs
    (a.1::a.2).reverse = acc.reverse++bubble w xs := by
  induction xs generalizing acc w with
  | nil => simp [Fold.fold,bubble]
  | cons x xs ih =>
    simpa only [Fold.fold,List.foldl_cons,carryStep,List.reverse_cons,List.append_assoc,
      List.singleton_append,bubble] using ih (Order.high (w,x)) (Order.low (w,x)::acc)

theorem insert_eq (z : W × List W) : insert z = bubble z.1 z.2 := by
  simpa only [insert,List.reverse_nil,List.nil_append] using fold_carry z.1 z.2 []

end MeanPayoff.TreeDevice.Sort
namespace MeanPayoff.TreeDevice.Sort
open BinaryData

theorem bubble_perm (w : W) (xs : List W) : (bubble w xs).Perm (w::xs) := by
  induction xs generalizing w with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    by_cases h : Compare.testPair (w,x)=true
    · simpa only [bubble,Order.low,Order.high,h,ite_true, if_true] using (ih x).cons w
    · have hf : Compare.testPair (w,x)=false := Bool.eq_false_iff.mpr h
      simpa only [bubble,Order.low,Order.high,hf,Bool.false_eq_true,ite_false, if_false] using
        ((ih w).cons x).trans (List.Perm.swap _ _ _)

theorem insert_perm (w : W) (xs : List W) : (insert (w,xs)).Perm (w::xs) := by
  rw [insert_eq]
  exact bubble_perm w xs

theorem insert_size (w : W) (xs : List W) :
    treeSize (listTree wordData (insert (w,xs))) = treeSize (wordData w)+treeSize (listTree wordData xs)+1 := by
  have hp := insert_perm w xs
  have hlen := hp.length_eq
  have hsum := (hp.map (treeSize ∘ wordData)).sum_eq
  rw [listTree_size,listTree_size]
  simp only [List.length_cons,List.map_cons,List.sum_cons,Function.comp_def] at hlen hsum ⊢
  omega

end MeanPayoff.TreeDevice.Sort
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_ArithmeticDevices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Forest
open RegisterBits BinaryData

def atom {α : Type} (a : α → List Data) :
    Segment (fun z => ⟨a z,[],[]⟩) (fun z => ⟨Data.nil::a z,[],[]⟩) where
  program := bitOp 0 (.push false)
  limit _ := 2
  correct z suffix out bits := by
    rw [bitOp_runs]
    simp only [stack,encode_cons,encode_nil,BinaryData.encode,List.cons_append,core_zero,BinaryStack.applyOp]
    apply Take.config_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl

noncomputable def literal {α : Type} (t : Data) (a : α → List Data) :
    Segment (fun z => ⟨a z,[],[]⟩) (fun z => ⟨t::a z,[],[]⟩) :=
  match t with
  | .nil => atom a
  | .pair u v => (literal v a).seq ((literal u (fun z => v::a z)).seq
      (pair (fun _ => u) (fun _ => v) a (fun _ => []) (fun _ => [])))

end MeanPayoff.TreeDevice.Forest
namespace MeanPayoff.TreeDevice
open BinaryData

noncomputable def constant {α β : Type} (ea : α → Data) (eb : β → Data) (b : β) :
    Device ea eb (fun _ => b) :=
  Forest.toDevice _ _ _ ((Forest.drop ea (fun _ => [])).seq (Forest.literal (eb b) (fun _ => [])))

noncomputable def branch {α β : Type} {ea : α → Data} {eb : β → Data}
    {test : α → Bool} {f g : α → β} (T : Device ea Compare.bitTree test)
    (F : Device ea eb f) (G : Device ea eb g) : Device ea eb (fun a => if test a then f a else g a) :=
  compose (fanout T (fanout F G)) (Select.device eb)

namespace Bits

noncomputable def notDevice : Device Compare.bitTree Compare.bitTree Bool.not :=
  (branch (identity Compare.bitTree) (constant Compare.bitTree Compare.bitTree false)
    (constant Compare.bitTree Compare.bitTree true)).extFun (by intro b; cases b <;> rfl)

end Bits
namespace Head
open RegisterBits

noncomputable abbrev flow {α : Type} (ea : α → Data) (a : α) : Flow.Program 5 where
  nodes := 3
  start := 0
  block := ![skip,(first ea (listTree ea)).program,(constant (listTree ea) ea a).program]
  read _ := 0
  next p top _ := if p=0 then some ⟨if top=some true then 1 else 2,.keep,none⟩ else none

noncomputable abbrev program {α : Type} (ea : α → Data) (a : α) := Flow.compile (flow ea a)

noncomputable def limit {α : Type} (ea : α → Data) (a : α) : List α → ℕ
  | [] => (constant (listTree ea) ea a).limit []+3
  | x::xs => (first ea (listTree ea)).limit (x,xs)+3

theorem runs {α : Type} (ea : α → Data) (a : α) (xs : List α) (suffix out : List Bool) :
    Reaches (program ea a) ⟨some (program ea a).start,store (listTree ea xs) suffix,out⟩
      ⟨none,store (ea (xs.headD a)) suffix,out⟩ (limit ea a xs) := by
  cases xs with
  | nil =>
    have h₀ : Reaches (program ea a)
        (Flow.state (flow ea a) 0 (store (listTree ea []) suffix) out)
        (Flow.state (flow ea a) 2 (store (listTree ea []) suffix) out) 2 := by
      intro bits
      apply Flow.hop_update (flow ea a) 0 2 _ _ _ out bits 1 .keep rfl (by intros; rfl)
      simp only [BinaryStack.applyOp,Function.update_eq_self,advance]
    have h₁ : Reaches (program ea a)
        (Flow.state (flow ea a) 2 (store (listTree ea []) suffix) out)
        ⟨none,store (ea a) suffix,out⟩ ((constant (listTree ea) ea a).limit []+1) := by
      intro bits
      exact Flow.finish (flow ea a) 2 _ _ out bits _
        ((constant (listTree ea) ea a).correct [] suffix out bits) (by intros; rfl)
    exact (h₀.trans h₁).mono (by dsimp only [limit]; omega)
  | cons x xs =>
    have h₀ : Reaches (program ea a)
        (Flow.state (flow ea a) 0 (store (listTree ea (x::xs)) suffix) out)
        (Flow.state (flow ea a) 1 (store (listTree ea (x::xs)) suffix) out) 2 := by
      intro bits
      apply Flow.hop_update (flow ea a) 0 1 _ _ _ out bits 1 .keep rfl (by intros; rfl)
      simp only [BinaryStack.applyOp,Function.update_eq_self,advance]
    have h₁ : Reaches (program ea a)
        (Flow.state (flow ea a) 1 (store (listTree ea (x::xs)) suffix) out)
        ⟨none,store (ea x) suffix,out⟩ ((first ea (listTree ea)).limit (x,xs)+1) := by
      intro bits
      exact Flow.finish (flow ea a) 1 _ _ out bits _
        ((first ea (listTree ea)).correct (x,xs) suffix out bits) (by intros; rfl)
    exact (h₀.trans h₁).mono (by dsimp only [limit]; omega)

noncomputable def device {α : Type} (ea : α → Data) (a : α) :
    Device (listTree ea) ea (fun xs => xs.headD a) :=
  ofProgram _ _ _ (program ea a) (limit ea a)
    (fun xs suffix out bits => (runs ea a xs suffix out).pad rfl bits)

end Head
end MeanPayoff.TreeDevice
namespace MeanPayoff.TreeDevice.Median
open BinaryData

abbrev Count := List Unit
abbrev State := Bool × Count

def unitData (_ : Unit) : Data := .nil
def stateData := product Compare.bitTree (listTree unitData)

def halfStep (s : State) : State := (!s.1, if s.1 then ()::s.2 else s.2)

noncomputable def incrementDevice : Device (listTree unitData) (listTree unitData) (fun xs => ()::xs) := by
  let P := compose (fanout (constant (listTree unitData) unitData ()) (identity (listTree unitData)))
    (Lists.consDevice unitData)
  exact P.extFun (by intro xs; rfl)

noncomputable def halfStepDevice : Device stateData stateData halfStep :=
  fanout (compose (first Compare.bitTree (listTree unitData)) Bits.notDevice)
    (branch (first Compare.bitTree (listTree unitData))
      (compose (second Compare.bitTree (listTree unitData)) incrementDevice)
      (second Compare.bitTree (listTree unitData)))

def count {α : Type} (xs : List α) : Count :=
  (xs.foldl (fun s _ => halfStep s) (false,[])).2

noncomputable def countDevice {α : Type} (ea : α → Data) : Device (listTree ea) (listTree unitData) count := by
  let F := compose (first stateData ea) halfStepDevice
  let P := compose (fanout (constant (listTree ea) stateData (false,[])) (identity (listTree ea)))
    (compose (Fold.device F) (second Compare.bitTree (listTree unitData)))
  exact P.extFun (by intro xs; rfl)

theorem repeatTail {α : Type} (xs : List α) (ns : Count) :
    Fold.fold (fun z : List α × Unit => z.1.tail) xs ns = xs.drop ns.length := by
  induction ns generalizing xs with
  | nil => simp [Fold.fold]
  | cons u ns ih =>
    change Fold.fold (fun z : List α × Unit => z.1.tail) xs.tail ns = _
    rw [ih]
    simpa only [List.length_cons] using (List.drop_tail (l := xs) (i := ns.length))

noncomputable def dropDevice {α : Type} (ea : α → Data) :
    Device (product (listTree ea) (listTree unitData)) (listTree ea)
      (fun z : List α × Count => z.1.drop z.2.length) :=
  (Fold.device (compose (first (listTree ea) unitData) (Tail.device ea))).extFun (by
    intro z
    exact repeatTail _ _)

def zeroWord : SignedBits.Word := ⟨false,[]⟩

def median (xs : List SignedBits.Word) : SignedBits.Word :=
  ((Sort.sort xs).drop (count xs).length).headD zeroWord

noncomputable def device : Device (listTree wordData) wordData median :=
  compose (fanout Sort.sortDevice (countDevice wordData))
    (compose (dropDevice wordData) (Head.device wordData zeroWord))

end MeanPayoff.TreeDevice.Median
namespace MeanPayoff.TreeDevice.Median
open BinaryData

@[simp] theorem zeroWord_val : zeroWord.val = 0 := rfl

end MeanPayoff.TreeDevice.Median
namespace MeanPayoff.TreeDevice
open BinaryData

def LinearCost {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) : Prop := ∃ K : ℕ, ∀ x, F.limit x ≤ K*(treeSize (ea x)+1)

namespace LinearCost

theorem identity {α : Type} (ea : α → Data) : LinearCost (TreeDevice.identity ea) := by
  refine ⟨1,?_⟩
  intro x
  simp only [TreeDevice.identity,Nat.one_mul]
  omega

theorem compose {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α → β} {g : β → γ} {F : Device ea eb f} {G : Device eb ec g}
    (hF : LinearCost F) (hG : LinearCost G) : LinearCost (TreeDevice.compose F G) := by
  obtain ⟨K,hK⟩ := hF
  obtain ⟨M,hM⟩ := hG
  refine ⟨K+M*(K+2)+2,?_⟩
  intro x
  have h₁ := hK x
  have h₂ := hM (f x)
  have hi := TreeDevice.output_size F x
  have hb : treeSize (eb (f x))+1 ≤ (K+2)*(treeSize (ea x)+1) := by nlinarith
  have hm := Nat.mul_le_mul_left M hb
  rw [compose_limit]
  nlinarith

theorem dup {α : Type} (ea : α → Data) : LinearCost (TreeDevice.dup ea) := by
  refine ⟨13,?_⟩
  intro x
  rw [dup_limit]
  omega

theorem pairMap {α β γ δ : Type} {ea : α → Data} {eb : β → Data}
    {ec : γ → Data} {ed : δ → Data} {f : α → β} {g : γ → δ}
    {F : Device ea eb f} {G : Device ec ed g} (hF : LinearCost F) (hG : LinearCost G) :
    LinearCost (TreeDevice.pairMap F G) := by
  obtain ⟨K,hK⟩ := hF
  obtain ⟨M,hM⟩ := hG
  refine ⟨25*K+13*M+100,?_⟩
  rintro ⟨x,y⟩
  have h₁ : F.limit x ≤ K*(treeSize (ea x)+treeSize (ec y)+2) :=
    (hK x).trans (Nat.mul_le_mul_left K (by omega))
  have h₂ : G.limit y ≤ M*(treeSize (ea x)+treeSize (ec y)+2) :=
    (hM y).trans (Nat.mul_le_mul_left M (by omega))
  have hi := TreeDevice.output_size F x
  have hj := TreeDevice.output_size G y
  rw [pairMap_limit]
  simp only [product,treeSize_pair]
  nlinarith

theorem fanout {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α → β} {g : α → γ} {F : Device ea eb f} {G : Device ea ec g}
    (hF : LinearCost F) (hG : LinearCost G) : LinearCost (TreeDevice.fanout F G) :=
  compose (dup ea) (pairMap hF hG)

theorem first {α β : Type} (ea : α → Data) (eb : β → Data) : LinearCost (TreeDevice.first ea eb) := by
  refine ⟨30,?_⟩
  rintro ⟨x,y⟩
  rw [first_limit]
  simp only [product,treeSize_pair]
  omega

theorem second {α β : Type} (ea : α → Data) (eb : β → Data) : LinearCost (TreeDevice.second ea eb) := by
  refine ⟨10,?_⟩
  rintro ⟨x,y⟩
  rw [second_limit]
  simp only [product,treeSize_pair]
  omega

theorem select {α : Type} (ea : α → Data) : LinearCost (Select.device ea) := by
  refine ⟨43,?_⟩
  rintro ⟨b,x,y⟩
  have h := Select.limit_le ea (b,x,y)
  dsimp only at h
  change Select.limit ea (b,x,y) ≤ _
  simp only [product,treeSize_pair]
  omega

theorem compare : LinearCost Compare.device := by
  refine ⟨100,?_⟩
  intro z
  have h := Compare.limit_le z
  have h₁ := digits_le_wordSize z.1
  have h₂ := digits_le_wordSize z.2
  change Compare.limit z ≤ _
  simp only [Compare.pairWord,treeSize_pair]
  omega

theorem add : LinearCost Add.device := by
  refine ⟨100,?_⟩
  intro z
  have h₁ := digits_le_wordSize z.1
  have h₂ := digits_le_wordSize z.2
  have ho := wordSize_bound (Add.sumPair z)
  have hl := SignedBits.add_length z.1.sign z.2.sign false z.1.digits z.2.digits
  change (Add.sumPair z).digits.length = _ at hl
  change Add.limit z ≤ _
  simp only [Add.limit,Add.pairWord,treeSize_pair]
  rw [hl] at ho
  omega

theorem min : LinearCost Order.minDevice :=
  compose (fanout compare (identity _)) (select _)

theorem max : LinearCost Order.maxDevice :=
  compose (fanout compare (fanout (second _ _) (first _ _))) (select _)

end LinearCost
end MeanPayoff.TreeDevice
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_PolynomialCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.TreeDevice
open BinaryData

def PolynomialCost {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) : Prop := ∃ K d : ℕ, ∀ x, F.limit x ≤ K*(treeSize (ea x)+1)^d

theorem LinearCost.polynomial {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    {F : Device ea eb f} (h : LinearCost F) : PolynomialCost F := by
  obtain ⟨K,hK⟩ := h
  exact ⟨K,1,by simpa using hK⟩

namespace PolynomialCost

theorem compose {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α → β} {g : β → γ} {F : Device ea eb f} {G : Device eb ec g}
    (hF : PolynomialCost F) (hG : PolynomialCost G) : PolynomialCost (TreeDevice.compose F G) := by
  obtain ⟨K,d,hK⟩ := hF
  obtain ⟨M,e,hM⟩ := hG
  let D := d+1+(d+1)*e
  refine ⟨K+M*(K+2)^e+2,D,?_⟩
  intro x
  let N := treeSize (ea x)+1
  have hn : 1 ≤ N := by dsimp [N]; omega
  have hd : N^d ≤ N^(d+1) := pow_le_pow_right' hn (by omega)
  have hn' : N ≤ N^(d+1) := by simpa using pow_le_pow_right' hn (show 1 ≤ d+1 by omega)
  have h₁ := hK x
  have ho := output_size F x
  have hb : treeSize (eb (f x))+1 ≤ (K+2)*N^(d+1) := by dsimp [N] at *; nlinarith
  have h₂ := (hM (f x)).trans (Nat.mul_le_mul_left M (Nat.pow_le_pow_left hb e))
  rw [mul_pow,←pow_mul] at h₂
  have hD : N^d ≤ N^D := pow_le_pow_right' hn (by dsimp [D]; omega)
  have he : N^((d+1)*e) ≤ N^D := pow_le_pow_right' hn (by dsimp [D]; omega)
  have hpos : 1 ≤ N^D := one_le_pow₀ hn
  have hk := Nat.mul_le_mul_left K hD
  have hm := Nat.mul_le_mul_left (M*(K+2)^e) he
  rw [compose_limit]
  dsimp [N] at *
  nlinarith

theorem pairMap {α β γ δ : Type} {ea : α → Data} {eb : β → Data}
    {ec : γ → Data} {ed : δ → Data} {f : α → β} {g : γ → δ}
    {F : Device ea eb f} {G : Device ec ed g} (hF : PolynomialCost F) (hG : PolynomialCost G) :
    PolynomialCost (TreeDevice.pairMap F G) := by
  obtain ⟨K,d,hK⟩ := hF
  obtain ⟨M,e,hM⟩ := hG
  let D := d+e+1
  refine ⟨25*K+13*M+100,D,?_⟩
  rintro ⟨x,y⟩
  let N := treeSize (ea x)+treeSize (ec y)+2
  have hn : 1 ≤ N := by dsimp [N]; omega
  have hnx : treeSize (ea x)+1 ≤ N := by dsimp [N]; omega
  have hny : treeSize (ec y)+1 ≤ N := by dsimp [N]; omega
  have hd : N^d ≤ N^D := pow_le_pow_right' hn (by dsimp [D]; omega)
  have he : N^e ≤ N^D := pow_le_pow_right' hn (by dsimp [D]; omega)
  have hn' : N ≤ N^D := by simpa using pow_le_pow_right' hn (show 1 ≤ D by dsimp [D]; omega)
  have h₁ := (hK x).trans (Nat.mul_le_mul_left K ((Nat.pow_le_pow_left hnx d).trans hd))
  have h₂ := (hM y).trans (Nat.mul_le_mul_left M ((Nat.pow_le_pow_left hny e).trans he))
  have ho₁ := output_size F x
  have ho₂ := output_size G y
  rw [pairMap_limit]
  simp only [product,treeSize_pair]
  change _ ≤ (25*K+13*M+100)*N^D
  change treeSize (ea x)+treeSize (ec y)+2 ≤ N^D at hn'
  nlinarith

theorem fanout {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α → β} {g : α → γ} {F : Device ea eb f} {G : Device ea ec g}
    (hF : PolynomialCost F) (hG : PolynomialCost G) : PolynomialCost (TreeDevice.fanout F G) :=
  compose (LinearCost.dup ea).polynomial (pairMap hF hG)

end PolynomialCost

namespace Fold

theorem time_le {α β : Type} {ea : α → Data} {eb : β → Data} {f : α × β → α}
    (F : Device (product ea eb) ea f) (K d : ℕ)
    (hF : ∀ z, F.limit z ≤ K*(treeSize (product ea eb z)+1)^d)
    (hg : ∀ a b, treeSize (ea (f (a,b))) ≤ treeSize (ea a)+treeSize (eb b)+1)
    (a : α) (xs : List β) (M : ℕ) (hM : treeSize (ea a)+treeSize (listTree eb xs)+1 ≤ M) :
    time F a xs ≤ (xs.length+1)*(12*M+K*M^d+11) := by
  induction xs generalizing a with
  | nil =>
    have ha : treeSize (ea a) ≤ M := by omega
    simp only [time,List.length_nil]
    omega
  | cons b bs ih =>
    have hg' := hg a b
    have hc : treeSize (ea (f (a,b)))+treeSize (listTree eb bs)+1 ≤ M := by
      simp only [listTree,treeSize_pair] at hM
      omega
    have hs : treeSize (product ea eb (a,b))+1 ≤ M := by
      have hp : 1 ≤ treeSize (listTree eb bs) := treeSize_pos _
      simp only [product,treeSize_pair,listTree] at *
      omega
    have hlim := (hF (a,b)).trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_left hs d))
    have hrec := ih (f (a,b)) hc
    simp only [time,List.length_cons]
    nlinarith

theorem polynomial {α β : Type} {ea : α → Data} {eb : β → Data} {f : α × β → α}
    {F : Device (product ea eb) ea f} (hF : PolynomialCost F)
    (hg : ∀ a b, treeSize (ea (f (a,b))) ≤ treeSize (ea a)+treeSize (eb b)+1) :
    PolynomialCost (device F) := by
  obtain ⟨K,d,hK⟩ := hF
  refine ⟨K+30,d+2,?_⟩
  rintro ⟨a,xs⟩
  let N := treeSize (product ea (listTree eb) (a,xs))+1
  have hn : 1 ≤ N := by dsimp [N]; omega
  have he : xs.length+1 ≤ N := by
    dsimp [N,product]
    rw [treeSize_pair,listTree_size]
    omega
  have ht := time_le F K d hK hg a xs N (by dsimp [N,product]; rw [treeSize_pair]; omega)
  have hh := ht.trans (Nat.mul_le_mul_right _ he)
  have hd : N^d ≤ N^(d+1) := pow_le_pow_right' hn (by omega)
  have hn' : N ≤ N^(d+1) := by simpa using pow_le_pow_right' hn (show 1 ≤ d+1 by omega)
  have hpos : 1 ≤ N^(d+2) := one_le_pow₀ hn
  change time F a xs+2 ≤ (K+30)*N^(d+2)
  have hmul := Nat.mul_le_mul_left N hd
  have hmul' := Nat.mul_le_mul_left N hn'
  have hmono : N ≤ N^(d+2) := by simpa using pow_le_pow_right' hn (show 1 ≤ d+2 by omega)
  rw [show d+2=(d+1)+1 by omega,pow_succ] at hpos hmono ⊢
  nlinarith

end Fold
end MeanPayoff.TreeDevice

namespace MeanPayoff.TreeDevice
open BinaryData
namespace LinearCost

theorem recode {α β γ δ : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    {F : Device ea eb f} (hF : LinearCost F) (ec : γ → Data) (ed : δ → Data)
    (i : γ → α) (h : γ → δ) (hi : ∀ x, ea (i x)=ec x) (ho : ∀ x, eb (f (i x))=ed (h x)) :
    LinearCost (F.recode ec ed i h hi ho) := by
  obtain ⟨K,hK⟩ := hF
  refine ⟨K,?_⟩
  intro x
  simpa only [Device.recode,hi] using hK (i x)

theorem pairSwap {α β : Type} (ea : α → Data) (eb : β → Data) : LinearCost (TreeDevice.pairSwap ea eb) :=
  fanout (second ea eb) (first ea eb)

theorem nilPrefix {α β : Type} (ea : α → Data) (eb : β → Data) : LinearCost (Lists.nilPrefix ea eb) := by
  refine ⟨6,?_⟩
  intro x
  change 6 ≤ 6*(treeSize (ea x)+1)
  omega

theorem nilSuffix {α β : Type} (ea : α → Data) (eb : β → Data) : LinearCost (Lists.nilSuffix ea eb) :=
  compose (nilPrefix ea eb) (pairSwap _ _)

theorem cons {α : Type} (ea : α → Data) : LinearCost (Lists.consDevice ea) :=
  recode (identity _) _ _ _ _ _ _

theorem consAcc {α : Type} (ea : α → Data) : LinearCost (Lists.consAcc ea) :=
  compose (pairSwap _ _) (cons _)
end LinearCost
namespace Forest

theorem literal_limit {α : Type} (t : Data) (a : α → List Data) (x : α) :
    (literal t a).limit x ≤ 6*treeSize t := by
  induction t generalizing a with
  | nil => simp [literal,atom]
  | pair u v ihu ihv =>
    have h₁ := ihu (fun z => v::a z)
    have h₂ := ihv a
    change (literal v a).limit x+((literal u (fun z => v::a z)).limit x+2+2)+2 ≤ _
    rw [treeSize_pair]
    omega
end Forest
namespace LinearCost

theorem constant {α β : Type} (ea : α → Data) (eb : β → Data) (b : β) :
    LinearCost (TreeDevice.constant ea eb b) := by
  refine ⟨6*treeSize (eb b)+12,?_⟩
  intro x
  have h := Forest.literal_limit (eb b) (fun _ : α => []) x
  change (Forest.drop ea (fun _ => [])).limit x + (Forest.literal (eb b) (fun _ : α => [])).limit x+2 ≤ _
  dsimp [Forest.drop,Forest.Segment.seq,Forest.move01] at *
  nlinarith

theorem branch {α β : Type} {ea : α → Data} {eb : β → Data}
    {test : α → Bool} {f g : α → β} {T : Device ea Compare.bitTree test}
    {F : Device ea eb f} {G : Device ea eb g} (hT : LinearCost T) (hF : LinearCost F) (hG : LinearCost G) :
    LinearCost (TreeDevice.branch T F G) := compose (fanout hT (fanout hF hG)) (select _)

theorem not : LinearCost Bits.notDevice :=
  branch (identity _) (constant _ _ _) (constant _ _ _)

theorem tail {α : Type} (ea : α → Data) : LinearCost (Tail.device ea) := by
  refine ⟨10,?_⟩
  intro xs
  cases xs with
  | nil => change 2 ≤ 10*(treeSize (listTree ea [])+1); omega
  | cons x xs =>
    change (Forest.drop ea (fun _ => [])).limit x+3 ≤ _
    dsimp [Forest.drop,Forest.Segment.seq,Forest.move01,listTree]
    rw [treeSize_pair]
    omega

theorem head {α : Type} (ea : α → Data) (a : α) : LinearCost (Head.device ea a) := by
  obtain ⟨K,hK⟩ := constant (listTree ea) ea a
  refine ⟨K+50,?_⟩
  intro xs
  cases xs with
  | nil =>
    have h := hK []
    change (TreeDevice.constant (listTree ea) ea a).limit []+3 ≤ _
    simp only [listTree,treeSize_nil] at *
    omega
  | cons x xs =>
    change (TreeDevice.first ea (listTree ea)).limit (x,xs)+3 ≤ _
    rw [first_limit]
    simp only [listTree,treeSize_pair]
    nlinarith
end LinearCost
namespace PolynomialCost

theorem reverse {α : Type} (ea : α → Data) : PolynomialCost (Lists.reverseDevice ea) := by
  apply compose (LinearCost.nilPrefix _ _).polynomial
  apply Fold.polynomial (LinearCost.consAcc _).polynomial
  intro a b
  simp only [listTree,treeSize_pair]
  omega
end PolynomialCost
namespace «Sort»

theorem carry_linear : LinearCost carryDevice := by
  have hp : LinearCost pairDevice := LinearCost.fanout
    (LinearCost.compose (LinearCost.first _ _) (LinearCost.first _ _)) (LinearCost.second _ _)
  have ht : LinearCost tailDevice := LinearCost.compose (LinearCost.first _ _) (LinearCost.second _ _)
  exact LinearCost.fanout (LinearCost.compose hp LinearCost.max)
    (LinearCost.compose (LinearCost.fanout (LinearCost.compose hp LinearCost.min) ht) (LinearCost.cons _))

theorem carry_size (a : Acc) (b : W) :
    treeSize (product wordData (listTree wordData) (carryStep (a,b))) ≤
      treeSize (product wordData (listTree wordData) a)+treeSize (wordData b)+1 := by
  rcases a with ⟨w,xs⟩
  unfold carryStep Order.high Order.low
  split_ifs <;> simp only [product,treeSize_pair,listTree] <;> omega

theorem initial_linear : LinearCost initialDevice :=
  LinearCost.fanout (LinearCost.compose (LinearCost.first _ _) (LinearCost.nilSuffix _ _)) (LinearCost.second _ _)

theorem insert_polynomial : PolynomialCost insertDevice :=
  PolynomialCost.compose initial_linear.polynomial
    (PolynomialCost.compose (Fold.polynomial carry_linear.polynomial carry_size)
      (PolynomialCost.compose (LinearCost.cons _).polynomial (PolynomialCost.reverse _)))

theorem sort_polynomial : PolynomialCost sortDevice := by
  apply PolynomialCost.compose (LinearCost.nilPrefix _ _).polynomial
  apply Fold.polynomial (PolynomialCost.compose (LinearCost.pairSwap _ _).polynomial insert_polynomial)
  intro a b
  dsimp only [Function.comp_def]
  rw [insert_size]
  omega
end «Sort»
end MeanPayoff.TreeDevice

namespace MeanPayoff.TreeDevice
open BinaryData

theorem element_size_le {α : Type} (ea : α → Data) {x : α} {xs : List α} (hx : x∈xs) :
    treeSize (ea x)+1 ≤ treeSize (listTree ea xs) := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · simp only [listTree,treeSize_pair]; omega
    · have h := ih hx
      simp only [listTree,treeSize_pair]; omega

theorem list_length_le_size {α : Type} (ea : α → Data) (xs : List α) :
    xs.length+1 ≤ treeSize (listTree ea xs) := by rw [listTree_size]; omega

namespace PolynomialCost

theorem map {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    {F : Device ea eb f} (hF : PolynomialCost F) : PolynomialCost (Map.device F) := by
  obtain ⟨K,d,hK⟩ := hF
  refine ⟨128*(K+2)^2,(d+1)*2,?_⟩
  intro xs
  let N := treeSize (listTree ea xs)+1
  have hn : 1 ≤ N := by dsimp [N]; omega
  have hlen : xs.length ≤ N := (list_length_le_size ea xs).trans (by dsimp [N]; omega) |>.trans' (by omega)
  have he : ∀ x∈xs, F.limit x ≤ K*N^d := by
    intro x hx
    exact (hK x).trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_left ((element_size_le ea hx).trans (by dsimp [N]; omega)) d))
  have sum_bound (ys : List α) (C : ℕ) (hc : ∀ y∈ys, F.limit y ≤ C) :
      (ys.map F.limit).sum ≤ ys.length*C := by
    induction ys with
    | nil => simp
    | cons y ys ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      have hh := hc y (List.mem_cons_self ..)
      have ht := ih (fun z hz => hc z (List.mem_cons_of_mem _ hz))
      nlinarith
  have hsum := sum_bound xs (K*N^d) he
  have hs := hsum.trans (Nat.mul_le_mul_right (K*N^d) hlen)
  have hpow : N ≤ N^(d+1) := by simpa using pow_le_pow_right' hn (show 1 ≤ d+1 by omega)
  have hr : Map.resource F xs+1 ≤ (K+2)*N^(d+1) := by
    change treeSize (listTree ea xs)+(xs.map F.limit).sum+1 ≤ _
    have hnEq : treeSize (listTree ea xs)+1=N := rfl
    rw [pow_succ] at hpow ⊢
    nlinarith
  have hm := (Map.limit_le F xs).trans (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left hr 2))
  change Map.limit F xs ≤ _
  simpa only [mul_pow,←pow_mul,Nat.mul_assoc] using hm

end PolynomialCost
namespace Median

theorem halfStep_linear : LinearCost halfStepDevice := by
  have hi : LinearCost incrementDevice := LinearCost.compose
    (LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.identity _)) (LinearCost.cons _)
  exact LinearCost.fanout (LinearCost.compose (LinearCost.first _ _) LinearCost.not)
    (LinearCost.branch (LinearCost.first _ _) (LinearCost.compose (LinearCost.second _ _) hi) (LinearCost.second _ _))

theorem halfStep_size {α : Type} (ea : α → Data) (s : State) (x : α) :
    treeSize (stateData (halfStep s)) ≤ treeSize (stateData s)+treeSize (ea x)+1 := by
  have h := treeSize_pos (ea x)
  rcases s with ⟨b,c⟩
  cases b <;> simp only [halfStep,Bool.not_true,Bool.not_false,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,
    stateData,product,Compare.bitTree,listData,boolData,listTree,treeSize_pair,treeSize_nil,unitData] <;> omega

theorem count_polynomial {α : Type} (ea : α → Data) : PolynomialCost (countDevice ea) := by
  apply PolynomialCost.compose
    (LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.identity _)).polynomial
  apply PolynomialCost.compose ?_ (LinearCost.second _ _).polynomial
  apply Fold.polynomial (LinearCost.compose (LinearCost.first _ _) halfStep_linear).polynomial
  intro a b
  exact halfStep_size ea a b

theorem drop_polynomial {α : Type} (ea : α → Data) : PolynomialCost (dropDevice ea) := by
  apply Fold.polynomial (LinearCost.compose (LinearCost.first _ _) (LinearCost.tail _)).polynomial
  intro a b
  change treeSize (listTree ea a.tail) ≤ treeSize (listTree ea a)+treeSize (unitData b)+1
  cases a <;> simp [listTree] ; omega

theorem polynomial : PolynomialCost device :=
  PolynomialCost.compose (PolynomialCost.fanout Sort.sort_polynomial (count_polynomial _))
    (PolynomialCost.compose (drop_polynomial _) (LinearCost.head _ _).polynomial)
end Median
end MeanPayoff.TreeDevice
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_BatchDevices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.TreeDevice.EnvMap
open BinaryData

abbrev Acc (α γ : Type) := α × List γ

def step {α β γ : Type} (f : α × β → γ) (z : Acc α γ × β) : Acc α γ :=
  (z.1.1,f (z.1.1,z.2)::z.1.2)

noncomputable def argument {α β γ : Type} (ea : α → Data) (eb : β → Data) (ec : γ → Data) :
    Device (product (product ea (listTree ec)) eb) (product ea eb)
      (fun z : Acc α γ × β => (z.1.1,z.2)) :=
  fanout (compose (first (product ea (listTree ec)) eb) (first ea (listTree ec)))
    (second (product ea (listTree ec)) eb)

noncomputable def stepDevice {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α × β → γ} (F : Device (product ea eb) ec f) :
    Device (product (product ea (listTree ec)) eb) (product ea (listTree ec)) (step f) :=
  fanout (compose (first (product ea (listTree ec)) eb) (first ea (listTree ec)))
    (compose (fanout (compose (argument ea eb ec) F)
      (compose (first (product ea (listTree ec)) eb) (second ea (listTree ec)))) (Lists.consDevice ec))

theorem fold_eq {α β γ : Type} (f : α × β → γ) (p : α) (xs : List β) (acc : List γ) :
    Fold.fold (step f) (p,acc) xs = (p,(xs.map (fun x => f (p,x))).reverse++acc) := by
  induction xs generalizing acc with
  | nil => simp [Fold.fold]
  | cons x xs ih =>
    change Fold.fold (step f) (p,f (p,x)::acc) xs = _
    rw [ih]
    simp [List.reverse_cons,List.append_assoc]

noncomputable def device {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α × β → γ} (F : Device (product ea eb) ec f) :
    Device (product ea (listTree eb)) (listTree ec)
      (fun z : α × List β => z.2.map (fun x => f (z.1,x))) := by
  let initial := fanout (compose (first ea (listTree eb)) (Lists.nilSuffix ea ec))
    (second ea (listTree eb))
  let P := compose initial (compose (Fold.device (stepDevice F))
    (compose (second ea (listTree ec)) (Lists.reverseDevice ec)))
  exact P.extFun (by
    rintro ⟨p,xs⟩
    change (Fold.fold (step f) (p,[]) xs).2.reverse = _
    rw [fold_eq]
    simp)

end MeanPayoff.TreeDevice.EnvMap

namespace MeanPayoff.TreeDevice.Graph
open BinaryData

abbrev W := SignedBits.Word
abbrev Count := Median.Count
abbrev Pot := List W
abbrev Edge := Count × W
abbrev Edges := Edge × List Edge
abbrev Vertex := Bool × Edges
abbrev Batch := EdgeScan.Pair × List EdgeScan.Pair

def countData := listTree Median.unitData
def potData := listTree wordData
def edgeData := product countData wordData
def edgesData := product edgeData (listTree edgeData)
def vertexData := product Compare.bitTree edgesData
def valuePairData := product wordData wordData
def batchData := product valuePairData (listTree valuePairData)

def lookup (z : Pot × Count) : W := (z.1.drop z.2.length).headD Median.zeroWord

noncomputable def lookupDevice : Device (product potData countData) wordData lookup :=
  compose (Median.dropDevice wordData) (Head.device wordData Median.zeroWord)

def edgePair (z : Pot × Edge) : EdgeScan.Pair := (z.2.2,lookup (z.1,z.2.1))

noncomputable def edgeDevice : Device (product potData edgeData) valuePairData edgePair :=
  fanout (compose (second potData edgeData) (second countData wordData))
    (compose (fanout (first potData edgeData)
      (compose (second potData edgeData) (first countData wordData))) lookupDevice)

def batch (z : Pot × Edges) : Batch :=
  (edgePair (z.1,z.2.1),z.2.2.map (fun e => edgePair (z.1,e)))

noncomputable def batchDevice : Device (product potData edgesData) batchData batch :=
  fanout (compose (fanout (first potData edgesData)
      (compose (second potData edgesData) (first edgeData (listTree edgeData)))) edgeDevice)
    (compose (fanout (first potData edgesData)
      (compose (second potData edgesData) (second edgeData (listTree edgeData)))) (EnvMap.device edgeDevice))

def vertex (z : Pot × Vertex) : W :=
  if z.2.1 then EdgeScan.maxScan (batch (z.1,z.2.2)) else EdgeScan.minScan (batch (z.1,z.2.2))

noncomputable def vertexDevice : Device (product potData vertexData) wordData vertex := by
  let B := compose (fanout (first potData vertexData)
    (compose (second potData vertexData) (second Compare.bitTree edgesData))) batchDevice
  exact branch (compose (second potData vertexData) (first Compare.bitTree edgesData))
    (compose B EdgeScan.maxDevice) (compose B EdgeScan.minDevice)

noncomputable def device : Device (product potData (listTree vertexData)) potData
    (fun z : Pot × List Vertex => z.2.map (fun v => vertex (z.1,v))) := EnvMap.device vertexDevice

end MeanPayoff.TreeDevice.Graph

namespace MeanPayoff.TreeDevice.EnvMap
open BinaryData

theorem step_limit {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α × β → γ} (F : Device (product ea eb) ec f) (p : α) (acc : List γ) (b : β) :
    (stepDevice F).limit ((p,acc),b) ≤
      1000*(treeSize (ea p)+treeSize (listTree ec acc)+treeSize (eb b)+F.limit (p,b)+1) := by
  have ho := output_size F (p,b)
  simp only [product,treeSize_pair] at ho
  simp only [stepDevice,argument,fanout_limit,compose_limit,first_limit,second_limit,
    Function.comp_def,product,treeSize_pair,listTree_cons,Lists.consDevice,Device.recode,identity]
  nlinarith

def resource {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α × β → γ} (F : Device (product ea eb) ec f) (p : α) (acc : List γ) (xs : List β) : ℕ :=
  treeSize (ea p)+treeSize (listTree ec acc)+treeSize (listTree eb xs)+
    xs.length*(treeSize (ea p)+1)+(xs.map (fun b => F.limit (p,b))).sum+1

theorem resource_decrease {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α × β → γ} (F : Device (product ea eb) ec f) (p : α) (acc : List γ) (b : β) (bs : List β) :
    resource F p (f (p,b)::acc) bs ≤ resource F p acc (b::bs) := by
  have ho := output_size F (p,b)
  simp only [product,treeSize_pair] at ho
  simp only [resource,listTree,treeSize_pair,List.length_cons,List.map_cons,List.sum_cons]
  nlinarith

theorem fold_time {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α × β → γ} (F : Device (product ea eb) ec f) (p : α) (acc : List γ) (xs : List β) :
    Fold.time (stepDevice F) (p,acc) xs ≤ 1200*(xs.length+1)*resource F p acc xs := by
  induction xs generalizing acc with
  | nil =>
    simp only [Fold.time,resource,product,treeSize_pair,listTree,treeSize_nil,List.length_nil,List.map_nil,List.sum_nil]
    nlinarith
  | cons b bs ih =>
    have hs := step_limit F p acc b
    have hd := resource_decrease F p acc b bs
    have hr := ih (f (p,b)::acc)
    have hm := Nat.mul_le_mul_left (1200*(bs.length+1)) hd
    have hlocal : treeSize (ea p)+treeSize (listTree ec acc)+treeSize (eb b)+F.limit (p,b)+1 ≤ resource F p acc (b::bs) := by
      simp only [resource,listTree,treeSize_pair,List.length_cons,List.map_cons,List.sum_cons]
      omega
    change 12*treeSize (product ea (listTree ec) (p,acc))+(stepDevice F).limit ((p,acc),b)+11+
      Fold.time (stepDevice F) (step f ((p,acc),b)) bs ≤ _
    dsimp only [step]
    simp only [product,treeSize_pair,List.length_cons]
    have hp : 1 ≤ resource F p acc (b::bs) := by unfold resource; omega
    nlinarith

theorem fold_polynomial {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α × β → γ} {F : Device (product ea eb) ec f} (hF : PolynomialCost F) :
    PolynomialCost (Fold.device (stepDevice F)) := by
  obtain ⟨K,d,hK⟩ := hF
  refine ⟨1200*(K+3)+2,d+3,?_⟩
  rintro ⟨⟨p,acc⟩,xs⟩
  let N := treeSize (product (product ea (listTree ec)) (listTree eb) ((p,acc),xs))+1
  have hN : N = treeSize (ea p)+treeSize (listTree ec acc)+treeSize (listTree eb xs)+3 := by
    simp [N,product,treeSize_pair]; omega
  have hn : 1 ≤ N := by omega
  have hlen : xs.length+1 ≤ N := (list_length_le_size eb xs).trans (by omega)
  have he : ∀ x∈xs, F.limit (p,x) ≤ K*N^d := by
    intro x hx
    have hh := element_size_le eb hx
    have hi : treeSize (product ea eb (p,x))+1 ≤ N := by
      simp only [product,treeSize_pair]; omega
    exact (hK (p,x)).trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_left hi d))
  have hsum : (xs.map (fun b => F.limit (p,b))).sum ≤ xs.length*(K*N^d) := by
    have hh := List.sum_le_card_nsmul (xs.map (fun b => F.limit (p,b))) (K*N^d) (by
      intro y hy
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
      exact he b hb)
    simpa using hh
  have hs := hsum.trans (Nat.mul_le_mul_right (K*N^d) (show xs.length ≤ N by omega))
  have hd : N^(d+1) ≤ N^(d+2) := pow_le_pow_right' hn (by omega)
  have htwo : N^2 ≤ N^(d+2) := pow_le_pow_right' hn (by omega)
  have hlin : N ≤ N^(d+2) := by simpa using pow_le_pow_right' hn (show 1 ≤ d+2 by omega)
  have hpm := Nat.mul_le_mul (show xs.length ≤ N by omega) (show treeSize (ea p)+1 ≤ N by omega)
  have hcost : resource F p acc xs ≤ (K+3)*N^(d+2) := by
    unfold resource
    rw [pow_succ] at hd
    rw [pow_two] at htwo
    have hh := Nat.mul_le_mul_left K hd
    nlinarith
  have ht := fold_time F p acc xs
  have hl := Nat.mul_le_mul (show 1200*(xs.length+1) ≤ 1200*N from Nat.mul_le_mul_left _ hlen) hcost
  have hpos : 1 ≤ N^(d+3) := one_le_pow₀ hn
  change Fold.time (stepDevice F) (p,acc) xs+2 ≤ (1200*(K+3)+2)*N^(d+3)
  rw [show d+3=(d+2)+1 by omega,pow_succ] at hpos ⊢
  nlinarith

theorem polynomial {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α × β → γ} {F : Device (product ea eb) ec f} (hF : PolynomialCost F) :
    PolynomialCost (device F) := by
  apply PolynomialCost.compose
    (LinearCost.fanout (LinearCost.compose (LinearCost.first _ _) (LinearCost.nilSuffix _ _))
      (LinearCost.second _ _)).polynomial
  apply PolynomialCost.compose (fold_polynomial hF)
  exact PolynomialCost.compose (LinearCost.second _ _).polynomial (PolynomialCost.reverse _)

end MeanPayoff.TreeDevice.EnvMap

namespace MeanPayoff.TreeDevice
open BinaryData
namespace PolynomialCost

theorem branch {α β : Type} {ea : α → Data} {eb : β → Data}
    {test : α → Bool} {f g : α → β} {T : Device ea Compare.bitTree test}
    {F : Device ea eb f} {G : Device ea eb g}
    (hT : PolynomialCost T) (hF : PolynomialCost F) (hG : PolynomialCost G) :
    PolynomialCost (TreeDevice.branch T F G) :=
  compose (fanout hT (fanout hF hG)) (LinearCost.select _).polynomial

end PolynomialCost
namespace EdgeScan

theorem max_polynomial : PolynomialCost maxDevice := by
  apply PolynomialCost.compose
    (PolynomialCost.pairMap LinearCost.add.polynomial (PolynomialCost.map LinearCost.add.polynomial))
  apply Fold.polynomial LinearCost.max.polynomial
  intro a b
  rcases high_mem (a,b) with h | h <;> rw [h] <;> dsimp only <;> omega

theorem min_polynomial : PolynomialCost minDevice := by
  apply PolynomialCost.compose
    (PolynomialCost.pairMap LinearCost.add.polynomial (PolynomialCost.map LinearCost.add.polynomial))
  apply Fold.polynomial LinearCost.min.polynomial
  intro a b
  rcases low_mem (a,b) with h | h <;> rw [h] <;> dsimp only <;> omega

end EdgeScan
namespace Graph

theorem lookup_polynomial : PolynomialCost lookupDevice :=
  PolynomialCost.compose (Median.drop_polynomial _) (LinearCost.head _ _).polynomial

theorem edge_polynomial : PolynomialCost edgeDevice := by
  refine PolynomialCost.fanout ?_ ?_
  · exact (LinearCost.compose (LinearCost.second _ _) (LinearCost.second _ _)).polynomial
  · exact PolynomialCost.compose
      (LinearCost.fanout (LinearCost.first _ _)
        (LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _))).polynomial lookup_polynomial

theorem batch_polynomial : PolynomialCost batchDevice := by
  refine PolynomialCost.fanout ?_ ?_
  · exact PolynomialCost.compose
      (LinearCost.fanout (LinearCost.first _ _)
        (LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _))).polynomial edge_polynomial
  · exact PolynomialCost.compose
      (LinearCost.fanout (LinearCost.first _ _)
        (LinearCost.compose (LinearCost.second _ _) (LinearCost.second _ _))).polynomial
      (EnvMap.polynomial edge_polynomial)

theorem vertex_polynomial : PolynomialCost vertexDevice := by
  have hB := PolynomialCost.compose
    (LinearCost.fanout (LinearCost.first potData vertexData)
      (LinearCost.compose (LinearCost.second potData vertexData)
        (LinearCost.second Compare.bitTree edgesData))).polynomial batch_polynomial
  exact PolynomialCost.branch
    (LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _)).polynomial
    (PolynomialCost.compose hB EdgeScan.max_polynomial)
    (PolynomialCost.compose hB EdgeScan.min_polynomial)

theorem polynomial : PolynomialCost device := EnvMap.polynomial vertex_polynomial

end Graph
end MeanPayoff.TreeDevice
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_OperatorCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.TreeDevice.Graph
open BinaryData

def outList (G : Game) (v : Fin G.n) : List (Fin G.m) := (List.finRange G.m).filter (fun e => G.tail e = v)

@[simp] theorem mem_outList (G : Game) (v : Fin G.n) (e : Fin G.m) :
    e ∈ outList G v ↔ e ∈ outgoing G v := by
  simp [outList,outgoing]

end MeanPayoff.TreeDevice.Graph

namespace MeanPayoff.SignedBits
open BinaryStack.Addition (value)

 theorem value_complement (xs : List Bool) :
    (value (xs.map Bool.not) : ℤ) + value xs = 2^xs.length-1 := by
  induction xs with
  | nil => simp [value]
  | cons b bs ih =>
    cases b <;> simp only [List.map_cons,value,Bool.not_false,Bool.not_true,
      Bool.toNat_true,Bool.toNat_false,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
      Nat.cast_zero, List.length_cons,pow_succ] <;> omega

def Word.complement (w : Word) : Word := ⟨!w.sign,w.digits.map Bool.not⟩

theorem Word.complement_val (w : Word) : w.complement.val = -w.val-1 := by
  have h := value_complement w.digits
  cases w with
  | mk s ds => cases s <;> simp [Word.complement,Word.val] at * <;> omega

end MeanPayoff.SignedBits
namespace MeanPayoff.TreeDevice.Negate
open BinaryData

def one : SignedBits.Word := ⟨false,[true]⟩
@[simp] theorem one_val : one.val = 1 := by rfl

noncomputable def rawNot : Device boolData boolData Bool.not := by
  let test : Device boolData Compare.bitTree id :=
    (Lists.nilSuffix boolData boolData).recode boolData Compare.bitTree id id (by intro b; rfl)
      (by intro b; cases b <;> rfl)
  exact (branch test (constant boolData boolData false) (constant boolData boolData true)).extFun
    (by intro b; cases b <;> rfl)

noncomputable def complement : Device wordData wordData SignedBits.Word.complement :=
  (Map.device rawNot).recode wordData wordData (fun w => w.sign::w.digits)
    SignedBits.Word.complement (by intro w; exact Halve.listTree_boolData _)
    (by intro w; simpa only [wordData,SignedBits.Word.complement,List.map_cons] using Halve.listTree_boolData ((w.sign::w.digits).map Bool.not))

def negate (w : SignedBits.Word) : SignedBits.Word := Add.sumPair (w.complement,one)

noncomputable def device : Device wordData wordData negate :=
  compose (fanout complement (constant wordData wordData one)) Add.device

theorem exact (w : SignedBits.Word) : (negate w).val = -w.val := by
  simp [negate,Add.sumPair_val,SignedBits.Word.complement_val]

theorem rawNot_linear : LinearCost rawNot :=
  LinearCost.branch
    (LinearCost.recode (LinearCost.nilSuffix _ _) _ _ _ _ _ _)
    (LinearCost.constant _ _ _) (LinearCost.constant _ _ _)

theorem complement_polynomial : PolynomialCost complement := by
  obtain ⟨K,d,h⟩ := PolynomialCost.map rawNot_linear.polynomial
  refine ⟨K,d,?_⟩
  intro w
  simpa only [complement,Device.recode,Halve.listTree_boolData,wordData] using h (w.sign::w.digits)

theorem polynomial : PolynomialCost device :=
  PolynomialCost.compose (PolynomialCost.fanout complement_polynomial
    (LinearCost.constant _ _ _).polynomial) LinearCost.add.polynomial

end MeanPayoff.TreeDevice.Negate

namespace MeanPayoff.TreeDevice.Fold
open BinaryData

theorem time_of_prefix_bound {α β : Type} {ea : α → Data} {eb : β → Data}
    {f : α × β → α} (F : Device (product ea eb) ea f) (K d M S : ℕ)
    (hF : ∀ z, F.limit z ≤ K*(treeSize (product ea eb z)+1)^d)
    (a : α) (xs : List β) (hs : treeSize (listTree eb xs) ≤ S)
    (ha : ∀ k ≤ xs.length, treeSize (ea (fold f a (xs.take k))) ≤ M) :
    time F a xs ≤ (xs.length+1)*(12*M+K*(M+S+2)^d+11) := by
  induction xs generalizing a with
  | nil =>
    have hh := ha 0 (by simp)
    simp only [List.take_zero,fold,List.foldl_nil] at hh
    simp only [time,List.length_nil,Nat.zero_add,Nat.one_mul]
    omega
  | cons b bs ih =>
    have ha₀ := ha 0 (by omega)
    simp only [List.take_zero,fold,List.foldl_nil] at ha₀
    have hb : treeSize (eb b) ≤ S := by
      simp only [listTree,treeSize_pair] at hs
      omega
    have hbs : treeSize (listTree eb bs) ≤ S := by
      simp only [listTree,treeSize_pair] at hs
      omega
    have hnext : ∀ k ≤ bs.length, treeSize (ea (fold f (f (a,b)) (bs.take k))) ≤ M := by
      intro k hk
      have hh := ha (k+1) (by simpa using Nat.add_le_add_right hk 1)
      simpa only [List.take_succ_cons,fold,List.foldl_cons] using hh
    have hlim := (hF (a,b)).trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_left
      (show treeSize (product ea eb (a,b))+1 ≤ M+S+2 by simp only [product,treeSize_pair]; omega) d))
    have hrec := ih (f (a,b)) hbs hnext
    simp only [time,List.length_cons]
    nlinarith

end MeanPayoff.TreeDevice.Fold

namespace MeanPayoff.BinaryStack.Addition

theorem value_bits (n : ℕ) : value n.bits = n := by
  have h (xs : List Bool) : value xs = BinaryInput.bitsValue xs := by
    induction xs with
    | nil => rfl
    | cons b bs ih => cases b <;> simp [value,BinaryInput.bitsValue,Nat.bit,ih] ; omega
  rw [h,BinaryInput.bitsValue_bits]

end MeanPayoff.BinaryStack.Addition
namespace MeanPayoff.TreeDevice.Multiply
open BinaryData
abbrev W := SignedBits.Word
abbrev State := W × W

def stateData := product wordData wordData

def double (w : W) := SignedBits.cons false w
@[simp] theorem double_val (w : W) : (double w).val = 2*w.val := by simp [double,SignedBits.val_cons]
@[simp] theorem double_length (w : W) : (double w).digits.length = w.digits.length+1 := rfl

noncomputable def doubleDevice : Device wordData wordData double := by
  let F := compose (fanout (constant (listTree boolData) boolData false) (identity (listTree boolData)))
    (Lists.consDevice boolData)
  exact (pairMap (identity boolData) F).recode wordData wordData
    (fun w => (w.sign,w.digits)) double
    (by intro w; simp only [product,Halve.listTree_boolData,wordData,listData])
    (by intro w; simp only [product,Halve.listTree_boolData,wordData,listData,double,SignedBits.cons,Function.comp_def,id_eq])

noncomputable def rawTest : Device boolData Compare.bitTree id :=
  (Lists.nilSuffix boolData boolData).recode boolData Compare.bitTree id id
    (by intro b; rfl) (by intro b; cases b <;> rfl)

def step (z : State × Bool) : State :=
  (z.1.1,if z.2 then Add.sumPair (double z.1.2,z.1.1) else double z.1.2)

noncomputable def baseDevice : Device (product stateData boolData) wordData (fun z : State × Bool => z.1.1) :=
  compose (first stateData boolData) (first wordData wordData)

noncomputable def accDevice : Device (product stateData boolData) wordData (fun z : State × Bool => double z.1.2) :=
  compose (compose (first stateData boolData) (second wordData wordData)) doubleDevice

noncomputable def testDevice : Device (product stateData boolData) Compare.bitTree (fun z : State × Bool => z.2) :=
  (compose (second stateData boolData) rawTest).extFun (by intro z; rfl)

noncomputable def sumDevice : Device (product stateData boolData) wordData (fun z : State × Bool => Add.sumPair (double z.1.2,z.1.1)) :=
  compose (fanout accDevice baseDevice) Add.device

noncomputable def choiceDevice : Device (product stateData boolData) wordData
    (fun z : State × Bool => if z.2 then Add.sumPair (double z.1.2,z.1.1) else double z.1.2) :=
  branch testDevice sumDevice accDevice

noncomputable def stepDevice : Device (product stateData boolData) stateData step :=
  fanout baseDevice choiceDevice

def multiply (z : W × List Bool) : W := (Fold.fold step (z.1,Median.zeroWord) z.2.reverse).2

noncomputable def initDevice : Device (product wordData (listTree boolData))
    (product stateData (listTree boolData)) (fun z : W × List Bool => ((z.1,Median.zeroWord),z.2.reverse)) :=
  fanout (fanout (first wordData (listTree boolData)) (constant (product wordData (listTree boolData)) wordData Median.zeroWord))
    (compose (second wordData (listTree boolData)) (Lists.reverseDevice boolData))

noncomputable def device : Device (product wordData (listTree boolData)) wordData multiply := by
  let P := compose initDevice (compose (Fold.device stepDevice) (second wordData wordData))
  exact P.extFun (by intro z; rfl)

@[simp] theorem step_first (s : State) (b : Bool) : (step (s,b)).1 = s.1 := rfl

theorem fold_first (s : State) (bs : List Bool) : (Fold.fold step s bs).1 = s.1 := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih => exact (ih (step (s,b))).trans rfl

theorem double_linear : LinearCost doubleDevice := by
  unfold doubleDevice
  apply LinearCost.recode
  exact LinearCost.pairMap (LinearCost.identity _)
    (LinearCost.compose (LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.identity _))
      (LinearCost.cons _))

theorem rawTest_linear : LinearCost rawTest := LinearCost.recode (LinearCost.nilSuffix _ _) _ _ _ _ _ _

theorem base_linear : LinearCost baseDevice :=
  LinearCost.compose (LinearCost.first stateData boolData) (LinearCost.first wordData wordData)

theorem acc_linear : LinearCost accDevice :=
  LinearCost.compose (LinearCost.compose (LinearCost.first stateData boolData)
    (LinearCost.second wordData wordData)) double_linear

theorem test_linear : LinearCost testDevice := LinearCost.compose (LinearCost.second _ _) rawTest_linear

theorem sum_linear : LinearCost sumDevice :=
  LinearCost.compose (LinearCost.fanout acc_linear base_linear) LinearCost.add

theorem choice_linear : LinearCost choiceDevice := LinearCost.branch test_linear sum_linear acc_linear

theorem step_linear : LinearCost stepDevice := LinearCost.fanout base_linear choice_linear

end MeanPayoff.TreeDevice.Multiply
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_WordDecoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.TreeDevice.Multiply
open BinaryData

theorem step_length (s : State) (b : Bool) :
    (step (s,b)).2.digits.length ≤ max s.2.digits.length s.1.digits.length+2 := by
  cases b with
  | false => simp only [step,Bool.false_eq_true,↓reduceIte,double_length]; omega
  | true =>
    change (SignedBits.add (double s.2).sign s.1.sign false (double s.2).digits s.1.digits).digits.length ≤ _
    rw [SignedBits.add_length,double_length]
    omega

theorem fold_length (s : State) (bs : List Bool) :
    (Fold.fold step s bs).2.digits.length ≤ max s.2.digits.length s.1.digits.length+2*bs.length := by
  induction bs generalizing s with
  | nil => simp only [Fold.fold,List.foldl_nil,List.length_nil,Nat.mul_zero,Nat.add_zero]; omega
  | cons b bs ih =>
    have hh := ih (step (s,b))
    have hs := step_length s b
    rw [step_first] at hh
    change (Fold.fold step (step (s,b)) bs).2.digits.length ≤ _
    simp only [List.length_cons]
    omega

theorem fold_polynomial : PolynomialCost (Fold.device stepDevice) := by
  obtain ⟨K,hK⟩ := step_linear
  refine ⟨402+40*K,2,?_⟩
  rintro ⟨s,xs⟩
  let N := treeSize (product stateData (listTree boolData) (s,xs))+1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hs₀ : treeSize (wordData s.1)+treeSize (wordData s.2)+treeSize (listTree boolData xs)+3 = N := by
    simp only [N,product,stateData,treeSize_pair]; omega
  have hw : s.1.digits.length ≤ N := by have := digits_le_wordSize s.1; omega
  have ha : s.2.digits.length ≤ N := by have := digits_le_wordSize s.2; omega
  have hl : xs.length+1 ≤ N := by have := list_length_le_size boolData xs; omega
  have he : treeSize (listTree boolData xs) ≤ N := by omega
  have hp : ∀ k ≤ xs.length, treeSize (stateData (Fold.fold step s (xs.take k))) ≤ 32*N := by
    intro k hk
    have hw' := wordSize_bound (Fold.fold step s (xs.take k)).1
    have ha' := wordSize_bound (Fold.fold step s (xs.take k)).2
    rw [fold_first] at hw'
    have hd := fold_length s (xs.take k)
    have hx : (xs.take k).length ≤ k := List.length_take_le _ _
    have hm : max s.2.digits.length s.1.digits.length ≤ N := max_le ha hw
    have hlen : (Fold.fold step s (xs.take k)).2.digits.length ≤ 3*N := by omega
    simp only [stateData,product,treeSize_pair,fold_first]
    omega
  have ht := Fold.time_of_prefix_bound stepDevice K 1 (32*N) N
    (by intro z; simpa only [pow_one] using hK z) s xs he hp
  have hc : 12*(32*N)+K*(32*N+N+2)^1+11 ≤ (400+40*K)*N := by
    simp only [pow_one]
    nlinarith
  have hbig := (Nat.mul_le_mul hl hc)
  have htime := ht.trans hbig
  have hpos : 1 ≤ N^2 := one_le_pow₀ hN
  change Fold.time stepDevice s xs+2 ≤ (402+40*K)*N^2
  rw [pow_two] at hpos ⊢
  nlinarith

theorem init_polynomial : PolynomialCost initDevice :=
  PolynomialCost.fanout
    (LinearCost.fanout (LinearCost.first _ _) (LinearCost.constant _ _ _)).polynomial
    (PolynomialCost.compose (LinearCost.second _ _).polynomial (PolynomialCost.reverse _))

theorem polynomial : PolynomialCost device :=
  PolynomialCost.compose init_polynomial
    (PolynomialCost.compose fold_polynomial (LinearCost.second _ _).polynomial)

end MeanPayoff.TreeDevice.Multiply

namespace MeanPayoff.TreeDevice.IntegerRead
open BinaryData
abbrev W := SignedBits.Word
def positive (xs : List Bool) : W := ⟨false,xs⟩
def minusOne : W := ⟨true,[]⟩
def decrement (xs : List Bool) : W := Add.sumPair (positive xs,minusOne)

theorem decrement_val (xs : List Bool) : (decrement xs).val = (BinaryStack.Addition.value xs : ℤ)-1 := by
  rw [decrement,Add.sumPair_val]
  simp [positive,minusOne,SignedBits.Word.val,BinaryStack.Addition.value,sub_eq_add_neg]

end MeanPayoff.TreeDevice.IntegerRead
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Counters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.EdgeRead
open BinaryData
abbrev W := SignedBits.Word
abbrev Count := Median.Count
abbrev Edge := Count × (Count × W)
def countData := listTree Median.unitData
def edgeData := product countData (product countData wordData)

def encodedWord (z : ℤ) : W :=
  let w := IntegerRead.decrement (z.natAbs+1).bits
  if z<0 then Negate.negate w else w

theorem encodedWord_val (z : ℤ) : (encodedWord z).val = z := by
  unfold encodedWord
  split
  · rename_i hz
    rw [Negate.exact,IntegerRead.decrement_val,BinaryStack.Addition.value_bits]
    simp [abs_of_neg hz]
  · rename_i hz
    rw [IntegerRead.decrement_val,BinaryStack.Addition.value_bits]
    simp [abs_of_nonneg (by omega : 0≤z)]

end MeanPayoff.TreeDevice.EdgeRead
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_ParserCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.StreamFold
open BinaryData
abbrev State (α β ρ : Type) := α × (List β × ρ)
def stateData {α β ρ : Type} (ea : α → Data) (eb : β → Data) (er : ρ → Data) := product ea (product (listTree eb) er)
def inputData {α β ρ : Type} (ea : α → Data) (eb : β → Data) (er : ρ → Data) := product (stateData ea eb er) Median.unitData

def step {α β ρ : Type} (f : α × ρ → β × ρ) (z : State α β ρ × Unit) : State α β ρ :=
  let p := f (z.1.1,z.1.2.2)
  (z.1.1,(p.1::z.1.2.1,p.2))

variable {α β ρ : Type} (ea : α → Data) (eb : β → Data) (er : ρ → Data)
noncomputable def envDevice : Device (inputData ea eb er) ea (fun z : State α β ρ × Unit => z.1.1) :=
  compose (first (stateData ea eb er) Median.unitData) (first ea (product (listTree eb) er))
noncomputable def localDevice : Device (inputData ea eb er) (product (listTree eb) er) (fun z : State α β ρ × Unit => z.1.2) :=
  compose (first (stateData ea eb er) Median.unitData) (second ea (product (listTree eb) er))
noncomputable def accDevice : Device (inputData ea eb er) (listTree eb) (fun z : State α β ρ × Unit => z.1.2.1) :=
  compose (localDevice ea eb er) (first (listTree eb) er)
noncomputable def streamDevice : Device (inputData ea eb er) er (fun z : State α β ρ × Unit => z.1.2.2) :=
  compose (localDevice ea eb er) (second (listTree eb) er)

variable {ea eb er} {f : α × ρ → β × ρ} (F : Device (product ea er) (product eb er) f)
noncomputable def parseDevice : Device (inputData ea eb er) (product eb er)
    (fun z : State α β ρ × Unit => f (z.1.1,z.1.2.2)) :=
  compose (fanout (envDevice ea eb er) (streamDevice ea eb er)) F
noncomputable def itemDevice : Device (inputData ea eb er) eb
    (fun z : State α β ρ × Unit => (f (z.1.1,z.1.2.2)).1) :=
  compose (parseDevice F) (first eb er)
noncomputable def restDevice : Device (inputData ea eb er) er
    (fun z : State α β ρ × Unit => (f (z.1.1,z.1.2.2)).2) :=
  compose (parseDevice F) (second eb er)
noncomputable def newAccDevice : Device (inputData ea eb er) (listTree eb)
    (fun z : State α β ρ × Unit => (f (z.1.1,z.1.2.2)).1::z.1.2.1) :=
  compose (fanout (itemDevice F) (accDevice ea eb er)) (Lists.consDevice eb)
noncomputable def stepDevice : Device (inputData ea eb er) (stateData ea eb er) (step f) :=
  fanout (envDevice ea eb er) (fanout (newAccDevice F) (restDevice F))

variable (ea eb er)
theorem env_linear : LinearCost (envDevice ea eb er) := LinearCost.compose (LinearCost.first _ _) (LinearCost.first _ _)
theorem local_linear : LinearCost (localDevice ea eb er) := LinearCost.compose (LinearCost.first _ _) (LinearCost.second _ _)
theorem acc_linear : LinearCost (accDevice ea eb er) := LinearCost.compose (local_linear _ _ _) (LinearCost.first _ _)
theorem stream_linear : LinearCost (streamDevice ea eb er) := LinearCost.compose (local_linear _ _ _) (LinearCost.second _ _)
variable {ea eb er}
theorem parse_polynomial (hF : PolynomialCost F) : PolynomialCost (parseDevice F) :=
  PolynomialCost.compose (LinearCost.fanout (env_linear _ _ _) (stream_linear _ _ _)).polynomial hF
theorem item_polynomial (hF : PolynomialCost F) : PolynomialCost (itemDevice F) :=
  PolynomialCost.compose (parse_polynomial F hF) (LinearCost.first _ _).polynomial
theorem rest_polynomial (hF : PolynomialCost F) : PolynomialCost (restDevice F) :=
  PolynomialCost.compose (parse_polynomial F hF) (LinearCost.second _ _).polynomial
theorem newAcc_polynomial (hF : PolynomialCost F) : PolynomialCost (newAccDevice F) :=
  PolynomialCost.compose (PolynomialCost.fanout (item_polynomial F hF) (acc_linear _ _ _).polynomial) (LinearCost.cons _).polynomial
theorem step_polynomial (hF : PolynomialCost F) : PolynomialCost (stepDevice F) :=
  PolynomialCost.fanout (env_linear _ _ _).polynomial
    (PolynomialCost.fanout (newAcc_polynomial F hF) (rest_polynomial F hF))

include F in
theorem fold_bound (K d : ℕ) (hF : ∀ z, F.limit z≤K*(treeSize (product ea er z)+1)^d)
    (hr : ∀ p r, treeSize (er (f (p,r)).2)≤treeSize (er r))
    (s : State α β ρ) (xs : List Unit) (N : ℕ)
    (hN : treeSize (ea s.1)+treeSize (er s.2.2)+2 ≤ N) :
    (Fold.fold (step f) s xs).1=s.1 ∧
    treeSize (er (Fold.fold (step f) s xs).2.2)≤treeSize (er s.2.2) ∧
    treeSize (listTree eb (Fold.fold (step f) s xs).2.1)≤
      treeSize (listTree eb s.2.1)+xs.length*(N+K*N^d+1) := by
  induction xs generalizing s with
  | nil => simp [Fold.fold]
  | cons u xs ih =>
    let s' := step f (s,u)
    have hre := hr s.1 s.2.2
    have hh := ih s' (by change treeSize (ea s.1)+treeSize (er (f (s.1,s.2.2)).2)+2≤N; omega)
    have ho := output_size F (s.1,s.2.2)
    have hx : treeSize (product ea er (s.1,s.2.2))+1 ≤ N := by simp only [product,treeSize_pair]; omega
    have ht := (hF (s.1,s.2.2)).trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_left hx d))
    change (Fold.fold (step f) s' xs).1=s.1 ∧ _
    refine ⟨hh.1,hh.2.1.trans hre,?_⟩
    have hs : treeSize (listTree eb s'.2.1)≤treeSize (listTree eb s.2.1)+N+K*N^d+1 := by
      simp only [s',step,listTree,treeSize_pair,product] at *
      omega
    have hh' := hh.2.2
    change treeSize (listTree eb (Fold.fold (step f) s' xs).2.1)≤_
    simp only [List.length_cons]
    nlinarith
end MeanPayoff.TreeDevice.StreamFold
namespace MeanPayoff.TreeDevice.Fold
open BinaryData

theorem polynomial_of_prefix {α β : Type} {ea : α → Data} {eb : β → Data}
    {f : α × β → α} {F : Device (product ea eb) ea f} (hF : PolynomialCost F)
    (B e : ℕ) (ha : ∀ a xs k, k≤xs.length →
      treeSize (ea (fold f a (xs.take k)))≤B*(treeSize (product ea (listTree eb) (a,xs))+1)^e) :
    PolynomialCost (device F) := by
  obtain ⟨K,d,hK⟩ := hF
  refine ⟨12*B+K*(B+3)^d+13,(e+1)*(d+1)+1,?_⟩
  rintro ⟨a,xs⟩
  let N := treeSize (product ea (listTree eb) (a,xs))+1
  have hN : 1≤N := by dsimp [N]; omega
  have hn : N≤N^(e+1) := by simpa only [pow_one] using pow_le_pow_right' hN (show 1≤e+1 by omega)
  have hp : 1≤N^(e+1) := one_le_pow₀ hN
  have he : N^e≤N^(e+1) := pow_le_pow_right' hN (by omega)
  have hs : treeSize (listTree eb xs)≤N := by simp only [N,product,treeSize_pair]; omega
  have hl : xs.length+1≤N := by have := list_length_le_size eb xs; simp only [N,product,treeSize_pair]; omega
  have ht := time_of_prefix_bound F K d (B*N^(e+1)) N hK a xs hs
    (by intro k hk; exact (ha a xs k hk).trans (Nat.mul_le_mul_left B he))
  have hb : B*N^(e+1)+N+2≤(B+3)*N^(e+1) := by nlinarith
  have hbpow := Nat.pow_le_pow_left hb d
  rw [mul_pow,← pow_mul] at hbpow
  have hd : N^((e+1)*d)≤N^((e+1)*(d+1)) := pow_le_pow_right' hN (by nlinarith)
  have hg : N^(e+1)≤N^((e+1)*(d+1)) := pow_le_pow_right' hN (by nlinarith)
  have hr : 1≤N^((e+1)*(d+1)) := one_le_pow₀ hN
  have hbp := hbpow.trans (Nat.mul_le_mul_left ((B+3)^d) hd)
  have hlocal : 12*(B*N^(e+1))+K*(B*N^(e+1)+N+2)^d+11 ≤
      (12*B+K*(B+3)^d+11)*N^((e+1)*(d+1)) := by
    nlinarith
  have hall := ht.trans (Nat.mul_le_mul hl hlocal)
  have hpos : 1≤N^((e+1)*(d+1)+1) := one_le_pow₀ hN
  change time F a xs+2≤(12*B+K*(B+3)^d+13)*N^((e+1)*(d+1)+1)
  rw [pow_succ] at hpos ⊢
  nlinarith
end MeanPayoff.TreeDevice.Fold

namespace MeanPayoff.TreeDevice.StreamFold
open BinaryData

theorem polynomial {α β ρ : Type} {ea : α → Data} {eb : β → Data} {er : ρ → Data}
    {f : α × ρ → β × ρ} (F : Device (product ea er) (product eb er) f)
    (hF : PolynomialCost F) (hr : ∀ p r, treeSize (er (f (p,r)).2)≤treeSize (er r)) :
    PolynomialCost (Fold.device (stepDevice F)) := by
  obtain ⟨K,d,hK⟩ := hF
  apply Fold.polynomial_of_prefix (step_polynomial F ⟨K,d,hK⟩) (K+4) (d+2)
  intro s xs k hk
  let N := treeSize (product (stateData ea eb er) (listTree Median.unitData) (s,xs))+1
  have hN : 1≤N := by dsimp [N]; omega
  have hs : treeSize (ea s.1)+treeSize (listTree eb s.2.1)+treeSize (er s.2.2)+treeSize (listTree Median.unitData xs)+4=N := by
    simp only [N,product,stateData,treeSize_pair]; omega
  have hi : treeSize (ea s.1)+treeSize (er s.2.2)+2≤N := by have := treeSize_pos (listTree eb s.2.1); omega
  have hl : (xs.take k).length≤N := by have := list_length_le_size Median.unitData xs; have := List.length_take_le k xs; omega
  have hb := fold_bound F K d hK hr s (xs.take k) N hi
  have henv := hb.1
  have hrest := hb.2.1
  have hacc := hb.2.2
  have hlast := Nat.mul_le_mul_right (N+K*N^d+1) hl
  have hp : N≤N^(d+1) := by simpa only [pow_one] using pow_le_pow_right' hN (show 1≤d+1 by omega)
  have hd : N^d≤N^(d+1) := pow_le_pow_right' hN (by omega)
  have hone : 1≤N^(d+1) := one_le_pow₀ hN
  have hfactor : N+K*N^d+1≤(K+2)*N^(d+1) := by nlinarith
  have hmul := Nat.mul_le_mul_left N hfactor
  change treeSize (stateData ea eb er (Fold.fold (step f) s (xs.take k)))≤(K+4)*N^(d+2)
  simp only [stateData,product,treeSize_pair,henv]
  rw [show d+2=(d+1)+1 by omega,pow_succ]
  nlinarith
end MeanPayoff.TreeDevice.StreamFold
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_ArenaParsing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.ArenaRead
open BinaryData
abbrev Count := Median.Count
abbrev Arena := Count × (List Bool × List EdgeRead.Edge)
def restData := listTree boolData
def countData := listTree Median.unitData
def edgesData := listTree EdgeRead.edgeData
def arenaData := product countData (product restData edgesData)

end MeanPayoff.TreeDevice.ArenaRead
namespace MeanPayoff.TreeDevice.Scale
open BinaryData
abbrev W := SignedBits.Word
abbrev Count := Median.Count
abbrev State := W × W

def step (z : State × Unit) : State := (z.1.1,Add.sumPair (z.1.2,z.1.1))

def scale (z : W × Count) : W := (Fold.fold step (z.1,z.1) z.2).2

@[simp] theorem step_first (s : State) (b : Unit) : (step (s,b)).1=s.1 := rfl
@[simp] theorem step_val (s : State) (b : Unit) : (step (s,b)).2.val=s.2.val+s.1.val := Add.sumPair_val _

def oneWord : W := ⟨false,[true]⟩

def transform (z : W × Count) : W := Add.sumPair (scale z,oneWord)
end MeanPayoff.TreeDevice.Scale
namespace MeanPayoff.TreeDevice.CountTest
open BinaryData
abbrev Count := Median.Count
def countData := listTree Median.unitData

def emptyStep (_ : Bool × Unit) : Bool := false
noncomputable def emptyStepDevice : Device (product Compare.bitTree Median.unitData) Compare.bitTree emptyStep :=
  constant _ _ false

theorem fold_false (xs : Count) : Fold.fold emptyStep false xs=false := by
  induction xs with
  | nil => rfl
  | cons b bs ih => exact ih

theorem fold_empty (xs : Count) : Fold.fold emptyStep true xs=xs.isEmpty := by
  cases xs with
  | nil => rfl
  | cons b bs => exact fold_false bs

noncomputable def emptyDevice : Device countData Compare.bitTree (fun xs : Count => xs.isEmpty) :=
  (compose (fanout (constant countData Compare.bitTree true) (identity countData))
    (Fold.device emptyStepDevice)).extFun fold_empty

theorem emptyStep_polynomial : PolynomialCost emptyStepDevice := (LinearCost.constant _ _ _).polynomial

theorem empty_polynomial : PolynomialCost emptyDevice := by
  apply PolynomialCost.compose
    (LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.identity _)).polynomial
  apply Fold.polynomial emptyStep_polynomial
  intro b u
  cases b <;> simp [emptyStep,Compare.bitTree,listData,boolData,treeSize,Median.unitData,encode]

end MeanPayoff.TreeDevice.CountTest

namespace MeanPayoff.TreeDevice.EnvFilter
open BinaryData
variable {α β : Type} {ea : α → Data} {eb : β → Data} {p : α × β → Bool}

def stateData (ea : α → Data) (eb : β → Data) := product ea (listTree eb)
def step (p : α × β → Bool) (z : (α × List β) × β) : α × List β :=
  (z.1.1,if p (z.1.1,z.2) then z.2::z.1.2 else z.1.2)

noncomputable def envDevice : Device (product (stateData ea eb) eb) ea (fun z : (α × List β) × β => z.1.1) :=
  compose (first (stateData ea eb) eb) (first ea (listTree eb))
noncomputable def accDevice : Device (product (stateData ea eb) eb) (listTree eb) (fun z : (α × List β) × β => z.1.2) :=
  compose (first (stateData ea eb) eb) (second ea (listTree eb))
noncomputable def testDevice (P : Device (product ea eb) Compare.bitTree p) :
    Device (product (stateData ea eb) eb) Compare.bitTree (fun z : (α × List β) × β => p (z.1.1,z.2)) :=
  compose (fanout envDevice (second (stateData ea eb) eb)) P
noncomputable def consDevice : Device (product (stateData ea eb) eb) (listTree eb)
    (fun z : (α × List β) × β => z.2::z.1.2) :=
  compose (fanout (second (stateData ea eb) eb) accDevice) (Lists.consDevice eb)
noncomputable def stepDevice (P : Device (product ea eb) Compare.bitTree p) :
    Device (product (stateData ea eb) eb) (stateData ea eb) (step p) :=
  fanout envDevice (branch (testDevice P) consDevice accDevice)

noncomputable def initDevice : Device (product ea (listTree eb)) (product (stateData ea eb) (listTree eb))
    (fun z : α × List β => ((z.1,[]),z.2)) :=
  fanout (fanout (first ea (listTree eb)) (constant _ (listTree eb) [])) (second ea (listTree eb))
noncomputable def rawDevice (P : Device (product ea eb) Compare.bitTree p) :
    Device (product ea (listTree eb)) (listTree eb)
      (fun z : α × List β => (Fold.fold (step p) (z.1,[]) z.2).2) :=
  @compose (α × List β) (α × List β) (List β) (product ea (listTree eb)) (stateData ea eb) (listTree eb)
    (fun z => Fold.fold (step p) (z.1,[]) z.2) (fun z => z.2)
    (compose initDevice (Fold.device (stepDevice P))) (second ea (listTree eb))

theorem fold_exact (a : α) (acc xs : List β) :
    Fold.fold (step p) (a,acc) xs = (a,((xs.filter (fun b => p (a,b))).reverse++acc)) := by
  induction xs generalizing acc with
  | nil => simp [Fold.fold]
  | cons b bs ih =>
    change Fold.fold (step p) (step p ((a,acc),b)) bs=_
    simp only [step]
    split <;> rename_i h
    · rw [ih]
      simp [h,List.reverse_cons,List.append_assoc]
    · rw [ih]
      simp [h]

noncomputable def device (P : Device (product ea eb) Compare.bitTree p) :
    Device (product ea (listTree eb)) (listTree eb) (fun z : α × List β => z.2.filter (fun b => p (z.1,b))) :=
  (compose (rawDevice P) (Lists.reverseDevice eb)).extFun (by intro z; simp [fold_exact])

theorem env_linear : LinearCost (envDevice (ea:=ea) (eb:=eb)) := LinearCost.compose (LinearCost.first _ _) (LinearCost.first _ _)
theorem acc_linear : LinearCost (accDevice (ea:=ea) (eb:=eb)) := LinearCost.compose (LinearCost.first _ _) (LinearCost.second _ _)
theorem cons_linear : LinearCost (consDevice (ea:=ea) (eb:=eb)) :=
  LinearCost.compose (LinearCost.fanout (LinearCost.second _ _) acc_linear) (LinearCost.cons _)
theorem test_polynomial {P : Device (product ea eb) Compare.bitTree p} (hP : PolynomialCost P) : PolynomialCost (testDevice P) :=
  PolynomialCost.compose (LinearCost.fanout env_linear (LinearCost.second _ _)).polynomial hP

theorem step_polynomial {P : Device (product ea eb) Compare.bitTree p} (hP : PolynomialCost P) : PolynomialCost (stepDevice P) :=
  PolynomialCost.fanout env_linear.polynomial (PolynomialCost.branch (test_polynomial hP) cons_linear.polynomial acc_linear.polynomial)
theorem fold_polynomial {P : Device (product ea eb) Compare.bitTree p} (hP : PolynomialCost P) : PolynomialCost (Fold.device (stepDevice P)) := by
  apply Fold.polynomial (step_polynomial hP)
  intro a b
  simp only [step]
  split <;> simp only [stateData,product,listTree,treeSize_pair] <;> omega

theorem init_linear : LinearCost (initDevice (ea:=ea) (eb:=eb)) :=
  LinearCost.fanout (LinearCost.fanout (LinearCost.first _ _) (LinearCost.constant _ _ _)) (LinearCost.second _ _)
theorem raw_polynomial {P : Device (product ea eb) Compare.bitTree p} (hP : PolynomialCost P) : PolynomialCost (rawDevice P) := by
  exact PolynomialCost.compose (PolynomialCost.compose init_linear.polynomial (fold_polynomial hP)) (LinearCost.second _ _).polynomial
theorem polynomial {P : Device (product ea eb) Compare.bitTree p} (hP : PolynomialCost P) : PolynomialCost (device P) :=
  PolynomialCost.compose (raw_polynomial hP) (PolynomialCost.reverse _)
end MeanPayoff.TreeDevice.EnvFilter
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Normalize
open BinaryData
abbrev Count := Median.Count
abbrev Edge := EdgeRead.Edge
abbrev Arena := ArenaRead.Arena

def countData := listTree Median.unitData
def edgeData := EdgeRead.edgeData
def edgesData := listTree edgeData
def ownersData := listTree boolData
def arenaData := ArenaRead.arenaData

noncomputable def nDevice : Device arenaData countData (fun z : Arena => z.1) := first countData (product ownersData edgesData)

def word (G : Game) (e : Fin G.m) := Scale.transform (EdgeRead.encodedWord (G.weight e),List.replicate G.n ())
def encodedEdge (G : Game) (e : Fin G.m) : Edge :=
  (List.replicate (G.tail e).val (),(List.replicate (G.head e).val (),word G e))

end MeanPayoff.TreeDevice.Normalize
namespace MeanPayoff.TreeDevice.Rows
open BinaryData
abbrev Edge := EdgeRead.Edge
end MeanPayoff.TreeDevice.Rows
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_EncodedPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Zip
open BinaryData
variable {α β γ : Type} (ea : α → Data) (eb : β → Data) (ec : γ → Data) (a : α) (b : β)

def restData := product (listTree ea) (listTree eb)
def stateData := StreamFold.stateData Median.unitData ec (restData ea eb)
def countData := listTree Median.unitData

variable {ea eb ec} {f : α × β → γ}
def zip (f : α × β → γ) (b : β) : List α → List β → List γ
  | [],_ => []
  | x::xs,ys => f (x,ys.headD b)::zip f b xs ys.tail

def row (f : α × β → γ) (a : α) (b : β) (p : Unit × (List α × List β)) : γ × (List α × List β) :=
  (f (p.2.1.headD a,p.2.2.headD b),(p.2.1.tail,p.2.2.tail))

noncomputable def localDevice : Device (product Median.unitData (restData ea eb)) (restData ea eb)
    (fun p : Unit × (List α × List β) => p.2) := second Median.unitData (restData ea eb)
noncomputable def leftDevice : Device (product Median.unitData (restData ea eb)) (listTree ea)
    (fun p : Unit × (List α × List β) => p.2.1) := compose localDevice (first (listTree ea) (listTree eb))
noncomputable def rightDevice : Device (product Median.unitData (restData ea eb)) (listTree eb)
    (fun p : Unit × (List α × List β) => p.2.2) := compose localDevice (second (listTree ea) (listTree eb))
noncomputable def headArgsDevice : Device (product Median.unitData (restData ea eb)) (product ea eb)
    (fun p : Unit × (List α × List β) => (p.2.1.headD a,p.2.2.headD b)) :=
  fanout (compose leftDevice (Head.device ea a)) (compose rightDevice (Head.device eb b))
noncomputable def tailsDevice : Device (product Median.unitData (restData ea eb)) (restData ea eb)
    (fun p : Unit × (List α × List β) => (p.2.1.tail,p.2.2.tail)) :=
  fanout (compose leftDevice (Tail.device ea)) (compose rightDevice (Tail.device eb))

variable (F : Device (product ea eb) ec f)
noncomputable def headDevice : Device (product Median.unitData (restData ea eb)) ec
    (fun p : Unit × (List α × List β) => f (p.2.1.headD a,p.2.2.headD b)) :=
  compose (headArgsDevice a b) F
noncomputable def rowDevice : Device (product Median.unitData (restData ea eb)) (product ec (restData ea eb)) (row f a b) :=
  fanout (headDevice a b F) tailsDevice

noncomputable def stateDevice : Device (restData ea eb) (stateData ea eb ec)
    (fun p : List α × List β => ((),([],p))) :=
  fanout (constant (restData ea eb) Median.unitData ()) (Lists.nilPrefix (restData ea eb) ec)
noncomputable def countDevice : Device (restData ea eb) countData
    (fun p : List α × List β => p.1.map (fun _ => ())) :=
  compose (first (listTree ea) (listTree eb)) (Map.device (constant ea Median.unitData ()))
noncomputable def initDevice : Device (restData ea eb) (product (stateData ea eb ec) countData)
    (fun p : List α × List β => (((),([],p)),p.1.map (fun _ => ()))) :=
  fanout stateDevice countDevice
noncomputable def resultDevice : Device (stateData ea eb ec) (listTree ec)
    (fun s : StreamFold.State Unit γ (List α × List β) => s.2.1.reverse) :=
  compose (compose (second Median.unitData (product (listTree ec) (restData ea eb)))
    (first (listTree ec) (restData ea eb))) (Lists.reverseDevice ec)
noncomputable def foldedDevice : Device (product (stateData ea eb ec) countData) (listTree ec)
    (fun z : StreamFold.State Unit γ (List α × List β) × Median.Count =>
      (Fold.fold (StreamFold.step (row f a b)) z.1 z.2).2.1.reverse) :=
  @compose (StreamFold.State Unit γ (List α × List β) × Median.Count)
    (StreamFold.State Unit γ (List α × List β)) (List γ)
    (product (stateData ea eb ec) countData) (stateData ea eb ec) (listTree ec)
    (fun z => Fold.fold (StreamFold.step (row f a b)) z.1 z.2) (fun s => s.2.1.reverse)
    (Fold.device (StreamFold.stepDevice (rowDevice a b F))) resultDevice
noncomputable def rawDevice : Device (restData ea eb) (listTree ec)
    (fun p : List α × List β =>
      (Fold.fold (StreamFold.step (row f a b)) ((),([],p)) (p.1.map (fun _ => ()))).2.1.reverse) :=
  compose initDevice (foldedDevice a b F)

theorem fold_exact (xs : List α) (ys : List β) (acc : List γ) :
    Fold.fold (StreamFold.step (row f a b)) ((),(acc,(xs,ys))) (List.replicate xs.length ()) =
      ((),((zip f b xs ys).reverse++acc,([],ys.drop xs.length))) := by
  induction xs generalizing ys acc with
  | nil => simp [Fold.fold,zip]
  | cons x xs ih =>
    simp only [List.length_cons,List.replicate_succ,Fold.fold,List.foldl_cons]
    change Fold.fold (StreamFold.step (row f a b))
      (StreamFold.step (row f a b) (((),(acc,(x::xs,ys))),())) (List.replicate xs.length ())=_
    simp only [StreamFold.step,row,List.headD_cons,List.tail_cons]
    rw [ih]
    simp [zip,List.reverse_cons,List.append_assoc,List.drop_tail]

noncomputable def device : Device (restData ea eb) (listTree ec) (fun p : List α × List β => zip f b p.1 p.2) :=
  (rawDevice a b F).extFun (by
    rintro ⟨xs,ys⟩
    change (Fold.fold (StreamFold.step (row f a b)) ((),([], (xs,ys)))
      (xs.map (fun _ => ()))).2.1.reverse = _
    rw [List.map_const, fold_exact]
    simp)

theorem local_linear : LinearCost (localDevice (ea:=ea) (eb:=eb)) := LinearCost.second _ _
theorem left_linear : LinearCost (leftDevice (ea:=ea) (eb:=eb)) := LinearCost.compose local_linear (LinearCost.first _ _)
theorem right_linear : LinearCost (rightDevice (ea:=ea) (eb:=eb)) := LinearCost.compose local_linear (LinearCost.second _ _)
theorem headArgs_linear : LinearCost (headArgsDevice (ea:=ea) (eb:=eb) a b) :=
  LinearCost.fanout (LinearCost.compose left_linear (LinearCost.head _ _)) (LinearCost.compose right_linear (LinearCost.head _ _))
theorem tails_linear : LinearCost (tailsDevice (ea:=ea) (eb:=eb)) :=
  LinearCost.fanout (LinearCost.compose left_linear (LinearCost.tail _)) (LinearCost.compose right_linear (LinearCost.tail _))
theorem head_polynomial (hF : PolynomialCost F) : PolynomialCost (headDevice a b F) := PolynomialCost.compose (headArgs_linear a b).polynomial hF
theorem row_polynomial (hF : PolynomialCost F) : PolynomialCost (rowDevice a b F) := PolynomialCost.fanout (head_polynomial a b F hF) tails_linear.polynomial

theorem fold_polynomial (hF : PolynomialCost F) : PolynomialCost (Fold.device (StreamFold.stepDevice (rowDevice a b F))) := by
  apply StreamFold.polynomial _ (row_polynomial a b F hF)
  intro u r
  have hl : treeSize (listTree ea r.1.tail)≤treeSize (listTree ea r.1) := by
    rcases r with ⟨xs,ys⟩; cases xs <;> simp only [List.tail_nil,List.tail_cons,listTree,treeSize_pair] <;> omega
  have hr : treeSize (listTree eb r.2.tail)≤treeSize (listTree eb r.2) := by
    rcases r with ⟨xs,ys⟩; cases ys <;> simp only [List.tail_nil,List.tail_cons,listTree,treeSize_pair] <;> omega
  simp only [row,restData,product,treeSize_pair]
  omega

theorem state_linear : LinearCost (stateDevice (ea:=ea) (eb:=eb) (ec:=ec)) := LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.nilPrefix _ _)
theorem count_polynomial : PolynomialCost (countDevice (ea:=ea) (eb:=eb)) :=
  PolynomialCost.compose (LinearCost.first _ _).polynomial (PolynomialCost.map (LinearCost.constant _ _ _).polynomial)
theorem init_polynomial : PolynomialCost (initDevice (ea:=ea) (eb:=eb) (ec:=ec)) := PolynomialCost.fanout state_linear.polynomial count_polynomial
theorem result_polynomial : PolynomialCost (resultDevice (ea:=ea) (eb:=eb) (ec:=ec)) :=
  PolynomialCost.compose (LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _)).polynomial (PolynomialCost.reverse _)
theorem folded_polynomial (hF : PolynomialCost F) : PolynomialCost (foldedDevice a b F) := PolynomialCost.compose (fold_polynomial a b F hF) result_polynomial
theorem raw_polynomial (hF : PolynomialCost F) : PolynomialCost (rawDevice a b F) := PolynomialCost.compose init_polynomial (folded_polynomial a b F hF)
theorem polynomial (hF : PolynomialCost F) : PolynomialCost (device a b F) := raw_polynomial a b F hF
end MeanPayoff.TreeDevice.Zip
namespace MeanPayoff.TreeDevice.Certified
open BinaryData

class Encoding (α : Type) where
  encode : α → Data
export Encoding (encode)

instance instEncodingUnit : Encoding Unit := ⟨Median.unitData⟩
instance instEncodingBool : Encoding Bool := ⟨Compare.bitTree⟩
instance instEncodingWord : Encoding SignedBits.Word := ⟨wordData⟩
instance instEncodingProd {α β : Type} [Encoding α] [Encoding β] : Encoding (α × β) :=
  ⟨product encode encode⟩
instance instEncodingList {α : Type} [Encoding α] : Encoding (List α) := ⟨listTree encode⟩

structure Code (α β : Type) [Encoding α] [Encoding β] where
  eval : α → β
  device : Device encode encode eval
  polynomial : PolynomialCost device

namespace Code
variable {α β γ δ : Type} [Encoding α] [Encoding β] [Encoding γ] [Encoding δ]
instance instCoeFunForall : CoeFun (Code α β) (fun _ => α → β) := ⟨Code.eval⟩

noncomputable def id : Code α α := ⟨_root_.id, identity encode, (LinearCost.identity _).polynomial⟩
noncomputable def const (b : β) : Code α β :=
  ⟨fun _ => b, constant encode encode b, (LinearCost.constant _ _ _).polynomial⟩
noncomputable def comp (f : Code α β) (g : Code β γ) : Code α γ :=
  ⟨g.eval ∘ f.eval, compose f.device g.device, PolynomialCost.compose f.polynomial g.polynomial⟩
noncomputable def pair (f : Code α β) (g : Code α γ) : Code α (β × γ) :=
  ⟨fun x => (f x,g x), fanout f.device g.device, PolynomialCost.fanout f.polynomial g.polynomial⟩
noncomputable def fst : Code (α × β) α :=
  ⟨Prod.fst, first encode encode, (LinearCost.first _ _).polynomial⟩
noncomputable def snd : Code (α × β) β :=
  ⟨Prod.snd, second encode encode, (LinearCost.second _ _).polynomial⟩
noncomputable def branch (p : Code α Bool) (f g : Code α β) : Code α β :=
  ⟨fun x => if p x then f x else g x, TreeDevice.branch p.device f.device g.device,
    PolynomialCost.branch p.polynomial f.polynomial g.polynomial⟩
noncomputable def map (f : Code α β) : Code (List α) (List β) :=
  ⟨List.map f.eval, Map.device f.device, PolynomialCost.map f.polynomial⟩
noncomputable def envMap (f : Code (α × β) γ) : Code (α × List β) (List γ) :=
  ⟨fun z => z.2.map (fun x => f (z.1,x)), EnvMap.device f.device, EnvMap.polynomial f.polynomial⟩
noncomputable def head (a : α) : Code (List α) α :=
  ⟨fun xs => xs.headD a, Head.device encode a, (LinearCost.head _ _).polynomial⟩
noncomputable def tail : Code (List α) (List α) :=
  ⟨List.tail, Tail.device encode, (LinearCost.tail _).polynomial⟩
noncomputable def cons : Code (α × List α) (List α) :=
  ⟨fun z => z.1::z.2, Lists.consDevice encode, (LinearCost.cons _).polynomial⟩
noncomputable def reverse : Code (List α) (List α) :=
  ⟨List.reverse, Lists.reverseDevice encode, PolynomialCost.reverse _⟩
noncomputable def zip (a : α) (b : β) (f : Code (α × β) γ) : Code (List α × List β) (List γ) :=
  ⟨fun z => Zip.zip f.eval b z.1 z.2, Zip.device a b f.device, Zip.polynomial a b f.device f.polynomial⟩
noncomputable def fold (f : Code (α × β) α)
    (hg : ∀ a b, treeSize (encode (f (a,b))) ≤ treeSize (encode a)+treeSize (encode b)+1) :
    Code (α × List β) α :=
  ⟨fun z => Fold.fold f.eval z.1 z.2, Fold.device f.device, Fold.polynomial f.polynomial hg⟩

noncomputable def recode (f : Code α β) (i : γ → α) (g : γ → δ)
    (hi : ∀ x, encode (i x)=encode x) (ho : ∀ x, encode (f (i x))=encode (g x)) : Code γ δ := by
  refine ⟨g,f.device.recode encode encode i g hi ho,?_⟩
  obtain ⟨K,d,h⟩ := f.polynomial
  refine ⟨K,d,fun x => ?_⟩
  change f.device.limit (i x) ≤ _
  simpa only [hi x] using h (i x)
noncomputable def foldPrefix (f : Code (α × β) α) (B e : ℕ)
    (hb : ∀ (a : α) (xs : List β) (k : ℕ), k≤xs.length → treeSize (encode (Fold.fold f.eval a (xs.take k))) ≤
      B*(treeSize (encode (a,xs))+1)^e) : Code (α × List β) α :=
  ⟨fun z => Fold.fold f.eval z.1 z.2,Fold.device f.device,Fold.polynomial_of_prefix f.polynomial B e hb⟩

def ext (f : Code α β) (g : α → β) (h : ∀ x, f x = g x) : Code α β :=
  ⟨g,f.device.extFun h,f.polynomial⟩

@[simp] theorem id_eval (x : α) : (id : Code α α) x=x := rfl
@[simp] theorem const_eval (b : β) (x : α) : (const b : Code α β) x=b := rfl
@[simp] theorem comp_eval (f : Code α β) (g : Code β γ) (x : α) : comp f g x=g (f x) := rfl
@[simp] theorem pair_eval (f : Code α β) (g : Code α γ) (x : α) : pair f g x=(f x,g x) := rfl
@[simp] theorem fst_eval (x : α × β) : (fst : Code (α × β) α) x=x.1 := rfl
@[simp] theorem snd_eval (x : α × β) : (snd : Code (α × β) β) x=x.2 := rfl
@[simp] theorem branch_eval (p : Code α Bool) (f g : Code α β) (x : α) : branch p f g x=(if p x then f x else g x) := rfl
@[simp] theorem map_eval (f : Code α β) (xs : List α) : map f xs=xs.map f.eval := rfl
@[simp] theorem envMap_eval (f : Code (α × β) γ) (z : α × List β) : envMap f z=z.2.map (fun x => f (z.1,x)) := rfl
@[simp] theorem head_eval (a : α) (xs : List α) : head a xs=xs.headD a := rfl
@[simp] theorem tail_eval (xs : List α) : tail xs=xs.tail := rfl
@[simp] theorem cons_eval (z : α × List α) : cons z=z.1::z.2 := rfl
@[simp] theorem reverse_eval (xs : List α) : reverse xs=xs.reverse := rfl
@[simp] theorem zip_eval (a : α) (b : β) (f : Code (α × β) γ) (z : List α × List β) : zip a b f z=Zip.zip f.eval b z.1 z.2 := rfl
@[simp] theorem ext_eval (f : Code α β) (g : α → β) (h : ∀ x, f x=g x) (x : α) : ext f g h x=g x := rfl
end Code
end MeanPayoff.TreeDevice.Certified
namespace MeanPayoff.TreeDevice.Certified
open BinaryData
open Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
abbrev W := SignedBits.Word
abbrev Count := List Unit

namespace Code
variable {α β : Type} [Encoding α] [Encoding β]
noncomputable def swap : Code (α × β) (β × α) := snd ⋏ₚ fst
noncomputable def count : Code (List α) Count := map (const ())
noncomputable def not : Code Bool Bool := ⟨Bool.not,Bits.notDevice,LinearCost.not.polynomial⟩
noncomputable def empty : Code (List α) Bool :=
  count ≫ₚ (⟨List.isEmpty,CountTest.emptyDevice,CountTest.empty_polynomial⟩ : Code Count Bool)
noncomputable def drop : Code (List α × Count) (List α) :=
  ⟨fun z => z.1.drop z.2.length,Median.dropDevice encode,Median.drop_polynomial _⟩
noncomputable def nth (a : α) : Code (List α × Count) α := drop ≫ₚ head a

theorem list_size_append (xs ys : List α) :
    treeSize (encode (xs++ys))+1=treeSize (encode xs)+treeSize (encode ys) := by
  change treeSize (listTree encode (xs++ys))+1=treeSize (listTree encode xs)+treeSize (listTree encode ys)
  simp only [listTree_size,List.length_append,List.map_append,List.sum_append]
  omega

noncomputable def consAcc : Code (List α × α) (List α) := swap ≫ₚ cons
noncomputable def revAppend : Code (List α × List α) (List α) :=
  fold consAcc (by
    intro xs x
    change treeSize (listTree encode (x::xs)) ≤ treeSize (listTree encode xs)+treeSize (encode x)+1
    rw [listTree,treeSize_pair]
    omega)
noncomputable def append : Code (List α × List α) (List α) :=
  (snd ⋏ₚ (fst ≫ₚ reverse)) ≫ₚ revAppend

theorem revAppend_eval (z : List α × List α) : revAppend z=z.2.reverse++z.1 := by
  change z.2.foldl (fun xs x => x::xs) z.1 = _
  exact List.foldl_flip_cons_eq_append'
@[simp] theorem append_eval (z : List α × List α) : append z=z.1++z.2 := by
  simp only [append,comp_eval,pair_eval,snd_eval,fst_eval,reverse_eval,revAppend_eval,List.reverse_reverse]

noncomputable def flatten : Code (List (List α)) (List α) :=
  (const [] ⋏ₚ Code.id) ≫ₚ fold append (by
    intro xs ys
    have h := list_size_append xs ys
    rw [append_eval]
    dsimp only at *
    omega)
@[simp] theorem flatten_eval (xss : List (List α)) : flatten xss=xss.flatten := by
  change xss.foldl (fun xs ys => append (xs,ys)) [] = _
  simp only [append_eval]
  simpa using (List.foldl_append_eq_append (l:=xss) (f:=_root_.id) (l':=[]))

noncomputable def filter (p : Code α Bool) : Code (List α) (List α) := by
  let q : Code (Unit × α) Bool := snd ≫ₚ p
  let f : Code (Unit × List α) (List α) :=
    ⟨fun z => z.2.filter (fun x => q (z.1,x)),EnvFilter.device q.device,EnvFilter.polynomial q.polynomial⟩
  exact (const () ⋏ₚ Code.id) ≫ₚ f
@[simp] theorem filter_eval (p : Code α Bool) (xs : List α) : filter p xs=xs.filter p.eval := rfl

noncomputable def any (p : Code α Bool) : Code (List α) Bool :=
  filter p ≫ₚ empty ≫ₚ not
@[simp] theorem empty_eval (xs : List α) : empty xs=xs.isEmpty := by
  cases xs <;> rfl
@[simp] theorem count_eval (xs : List α) : count xs=xs.map (fun _ => ()) := rfl
@[simp] theorem not_eval (b : Bool) : not b= !b := rfl
@[simp] theorem nth_eval (a : α) (z : List α × Count) : nth a z=z.1.getD z.2.length a := by
  change (z.1.drop z.2.length).headD a=z.1.getD z.2.length a
  rw [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]
end Code

structure Digits where
  bits : List Bool
instance instEncodingDigits : Encoding Digits := ⟨fun d => listTree boolData d.bits⟩

namespace Word
noncomputable def add : Code (W × W) W :=
  ⟨Add.sumPair,Add.device,LinearCost.add.polynomial⟩
noncomputable def neg : Code W W := ⟨Negate.negate,Negate.device,Negate.polynomial⟩
noncomputable def sub : Code (W × W) W := (fst ⋏ₚ (snd ≫ₚ neg)) ≫ₚ add
noncomputable def lt : Code (W × W) Bool :=
  ⟨Compare.testPair,Compare.device,LinearCost.compare.polynomial⟩
noncomputable def le : Code (W × W) Bool := Code.swap ≫ₚ lt ≫ₚ Code.not
noncomputable def min : Code (W × W) W := ⟨Order.low,Order.minDevice,LinearCost.min.polynomial⟩
noncomputable def max : Code (W × W) W := ⟨Order.high,Order.maxDevice,LinearCost.max.polynomial⟩
noncomputable def half : Code W W := by
  let P := pairMap (identity boolData) (Tail.device boolData)
  let hP := LinearCost.pairMap (LinearCost.identity boolData) (LinearCost.tail boolData)
  let hin : ∀ w : W, product boolData (listTree boolData) (w.sign,w.digits)=wordData w := by
    intro w
    simp only [product,wordData,listData,Halve.listTree_boolData]
  let F := P.recode wordData wordData (fun w : W => (w.sign,w.digits)) Halve.halve hin (by
    intro w
    simp only [product,wordData,listData,Halve.halve,Halve.listTree_boolData]
    rfl)
  exact ⟨Halve.halve,F,(LinearCost.recode hP _ _ _ _ _ _).polynomial⟩
noncomputable def double : Code W W := ⟨Multiply.double,Multiply.doubleDevice,Multiply.double_linear.polynomial⟩
noncomputable def average : Code (W × W) W := add ≫ₚ half
noncomputable def signDevice : Device wordData Compare.bitTree SignedBits.Word.sign :=
  (compose (Head.device boolData false) Multiply.rawTest).recode wordData Compare.bitTree
    (fun w => w.sign::w.digits) SignedBits.Word.sign
    (by intro w; exact Halve.listTree_boolData _) (by intro w; rfl)
noncomputable def sign : Code W Bool :=
  ⟨SignedBits.Word.sign, signDevice,
    (LinearCost.recode (LinearCost.compose (LinearCost.head _ _) Multiply.rawTest_linear) _ _ _ _ _ _).polynomial⟩
noncomputable def digitsDevice : Device wordData encode (fun w : W => Digits.mk w.digits) :=
  (Tail.device boolData).recode wordData encode (fun w => w.sign::w.digits)
    (fun w => Digits.mk w.digits) (by intro w; exact Halve.listTree_boolData _) (by intro w; rfl)
noncomputable def digits : Code W Digits :=
  ⟨fun w => ⟨w.digits⟩,digitsDevice,(LinearCost.recode (LinearCost.tail _) _ _ _ _ _ _).polynomial⟩
noncomputable def mulDigitsDevice : Device encode wordData (fun z : W × Digits => Multiply.multiply (z.1,z.2.bits)) :=
  Multiply.device.recode encode wordData (fun z : W × Digits => (z.1,z.2.bits))
    (fun z : W × Digits => Multiply.multiply (z.1,z.2.bits)) (by intro z; rfl) (by intro z; rfl)
noncomputable def mulDigits : Code (W × Digits) W := by
  refine ⟨fun z => Multiply.multiply (z.1,z.2.bits),mulDigitsDevice,?_⟩
  obtain ⟨K,d,h⟩ := Multiply.polynomial
  exact ⟨K,d,fun z => h (z.1,z.2.bits)⟩
noncomputable def unsignedMul : Code (W × W) W := (fst ⋏ₚ (snd ≫ₚ digits)) ≫ₚ mulDigits
noncomputable def mul : Code (W × W) W :=
  Code.branch (snd ≫ₚ sign) (((fst ⋏ₚ (snd ≫ₚ neg)) ≫ₚ unsignedMul) ≫ₚ neg) unsignedMul

@[simp] theorem add_val (x y : W) : (add (x,y)).val=x.val+y.val := Add.sumPair_val _
@[simp] theorem neg_val (x : W) : (neg x).val= -x.val := Negate.exact x
@[simp] theorem sub_val (x y : W) : (sub (x,y)).val=x.val-y.val := by simp [sub,sub_eq_add_neg]
@[simp] theorem lt_eval (x y : W) : lt (x,y)=decide (x.val<y.val) := Compare.testPair_eq _
@[simp] theorem le_eval (x y : W) : le (x,y)=decide (x.val≤y.val) := by
  simp only [le,Code.swap,comp_eval,pair_eval,snd_eval,fst_eval,lt_eval,not_eval]
  rw [← decide_not]
  exact decide_eq_decide.mpr not_lt
@[simp] theorem double_val (x : W) : (double x).val=2*x.val := Multiply.double_val _
@[simp] theorem sign_eval (x : W) : sign x=x.sign := rfl
end Word
end MeanPayoff.TreeDevice.Certified
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_EncodedArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

theorem take_size {α : Type} [Encoding α] (xs : List α) (k : ℕ) :
    treeSize (encode (xs.take k)) ≤ treeSize (encode xs) := by
  induction xs generalizing k with
  | nil => simp
  | cons x xs ih =>
    cases k with
    | zero => exact treeSize_pos _
    | succ k =>
      change treeSize (listTree encode ((x::xs).take (k+1))) ≤ treeSize (listTree encode (x::xs))
      simp only [List.take_succ_cons,listTree,treeSize_pair]
      have h := ih k
      change treeSize (listTree encode (xs.take k)) ≤ treeSize (listTree encode xs) at h
      omega

namespace Word
@[simp] theorem add_length (x y : W) : (add (x,y)).digits.length=Max.max x.digits.length y.digits.length+1 :=
  SignedBits.add_length _ _ _ _ _
@[simp] theorem neg_length (x : W) : (neg x).digits.length=Max.max x.digits.length 1+1 := by
  change (SignedBits.add _ _ _ _ _).digits.length=_
  rw [SignedBits.add_length]
  simp [SignedBits.Word.complement,Negate.one]
@[simp] theorem half_length (x : W) : (half x).digits.length=x.digits.length-1 := List.length_tail
@[simp] theorem double_length (x : W) : (double x).digits.length=x.digits.length+1 := Multiply.double_length _

theorem addFold_length (a : W) (xs : List W) :
    (Fold.fold add.eval a xs).digits.length ≤ a.digits.length+(xs.map (fun x => x.digits.length+1)).sum := by
  induction xs generalizing a with
  | nil => simp [Fold.fold]
  | cons x xs ih =>
    have h := ih (add (a,x))
    change (Fold.fold add.eval (add (a,x)) xs).digits.length ≤ _
    simp only [List.map_cons,List.sum_cons]
    rw [add_length] at h
    omega

theorem digitSum_le_size (xs : List W) :
    (xs.map (fun x => x.digits.length+1)).sum ≤ treeSize (encode xs) := by
  induction xs with
  | nil => simp []
  | cons x xs ih =>
    have h := digits_le_wordSize x
    change _ ≤ treeSize (listTree wordData (x::xs))
    rw [listTree,treeSize_pair]
    simp only [List.map_cons,List.sum_cons]
    change _ ≤ treeSize (listTree wordData xs) at ih
    omega

noncomputable def addFold : Code (W × List W) W := foldPrefix add 10 1 (by
  intro a xs k hk
  have hl := addFold_length a (xs.take k)
  have hs := digitSum_le_size (xs.take k)
  have ht : treeSize (encode (xs.take k)) ≤ treeSize (encode xs) := by
    exact take_size xs k
  have ha := digits_le_wordSize a
  have hh := wordSize_bound (Fold.fold add.eval a (xs.take k))
  simp only [pow_one]
  change treeSize (wordData (Fold.fold add.eval a (xs.take k))) ≤ 10*(treeSize (product wordData (listTree wordData) (a,xs))+1)
  rw [product,treeSize_pair]
  change (List.map (fun x => x.digits.length+1) (xs.take k)).sum ≤ treeSize (listTree wordData (xs.take k)) at hs
  change treeSize (listTree wordData (xs.take k)) ≤ treeSize (listTree wordData xs) at ht
  dsimp only [Prod.fst,Prod.snd]
  nlinarith)

noncomputable def sum : Code (List W) W := (const Median.zeroWord ⋏ₚ Code.id) ≫ₚ addFold

noncomputable def shiftStep : Code (W × Unit) W := fst ≫ₚ half
noncomputable def shiftRight : Code (W × Count) W := fold shiftStep (by
  intro w u
  change treeSize (wordData (Halve.halve w)) ≤ treeSize (wordData w)+treeSize (Median.unitData u)+1
  cases w with
  | mk s ds =>
    cases ds with
    | nil =>
      simp only [Halve.halve,wordData,listData,treeSize_pair,List.tail_nil]
      omega
    | cons b bs =>
      simp only [Halve.halve,wordData,listData,List.tail_cons,treeSize_pair]
      omega)

end Word

namespace Counter
noncomputable def inc : Code Count Count := (const () ⋏ₚ Code.id) ≫ₚ cons
noncomputable def word : Code Count W := map (const Negate.one) ≫ₚ Word.sum
noncomputable def add : Code (Count × Count) Count := append
noncomputable def mul : Code (Count × Count) Count := envMap (fst : Code (Count × Unit) Count) ≫ₚ flatten
@[simp] theorem add_length (a b : Count) : (add (a,b)).length=a.length+b.length := by simp [add]
@[simp] theorem mul_length (a b : Count) : (mul (a,b)).length=a.length*b.length := by
  simp [mul,List.length_flatten,List.sum_replicate,Nat.mul_comm]
end Counter
end MeanPayoff.TreeDevice.Certified
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

namespace Word
noncomputable def constant {α : Type} [Encoding α] (z : ℤ) : Code α W := const (EdgeRead.encodedWord z)
@[simp] theorem constant_val {α : Type} [Encoding α] (z : ℤ) (x : α) :
    (constant z x).val=z := EdgeRead.encodedWord_val z
end Word

namespace Array
def zero : W := Median.zeroWord
noncomputable def sub : Code (List W × List W) (List W) := zip zero zero Word.sub
noncomputable def min : Code (List W × List W) (List W) := zip zero zero Word.min
noncomputable def max : Code (List W × List W) (List W) := zip zero zero Word.max
noncomputable def average : Code (List W × List W) (List W) := zip zero zero Word.average
noncomputable def mul : Code (List W × List W) (List W) := zip zero zero Word.mul
noncomputable def lt : Code (List W × List W) (List Bool) := zip zero zero Word.lt
noncomputable def scale : Code (W × List W) (List W) := envMap Word.mul
noncomputable def translate : Code (W × List W) (List W) := envMap Word.add
noncomputable def complement : Code (List Bool) (List Bool) := map Code.not
noncomputable def mask : Code (List W × List Bool) (List W) :=
  zip zero false (Code.branch snd fst (Word.constant 0))
noncomputable def doubleOn : Code (List W × List Bool) (List W) :=
  zip zero false (Code.branch snd (fst ≫ₚ Word.double) fst)

end Array

namespace RawBudget

abbrev Data := (W × W) × (W × W) × List W × List W
noncomputable def k : Code Data (W × W) := fst
noncomputable def m : Code Data (W × W) := snd ≫ₚ fst
noncomputable def alpha : Code Data (List W) := snd ≫ₚ snd ≫ₚ fst
noncomputable def beta : Code Data (List W) := snd ≫ₚ snd ≫ₚ snd
noncomputable def kn : Code Data W := k ≫ₚ fst
noncomputable def kd : Code Data W := k ≫ₚ snd
noncomputable def mn : Code Data W := m ≫ₚ fst
noncomputable def md : Code Data W := m ≫ₚ snd
noncomputable def times (r : ℤ) : Code W W := (Code.id ⋏ₚ Word.constant r) ≫ₚ Word.mul
noncomputable def shrink (r : ℤ) : Code (W × W) (W × W) :=
  (fst ≫ₚ times r) ⋏ₚ (snd ≫ₚ times 5)
noncomputable def reduceK : Code Data Data := (k ≫ₚ shrink 4) ⋏ₚ m ⋏ₚ alpha ⋏ₚ beta
noncomputable def reduceM : Code Data Data := k ⋏ₚ (m ≫ₚ shrink 4) ⋏ₚ alpha ⋏ₚ beta
noncomputable def reweightK : Code (Data × List Bool) Data :=
  (fst ≫ₚ k ≫ₚ shrink 3) ⋏ₚ (fst ≫ₚ m) ⋏ₚ
    (((fst ≫ₚ alpha) ⋏ₚ snd) ≫ₚ Array.doubleOn) ⋏ₚ (fst ≫ₚ beta)
noncomputable def reweightM : Code (Data × List Bool) Data :=
  (fst ≫ₚ k) ⋏ₚ (fst ≫ₚ m ≫ₚ shrink 3) ⋏ₚ (fst ≫ₚ alpha) ⋏ₚ
    (((fst ≫ₚ beta) ⋏ₚ snd) ≫ₚ Array.doubleOn)
noncomputable def density : Code Data (List W) := (alpha ⋏ₚ beta) ≫ₚ Array.mul
noncomputable def total : Code Data W := density ≫ₚ Word.sum
noncomputable def parameterNumerator : Code Data W := (((kn ⋏ₚ mn) ≫ₚ Word.mul) ⋏ₚ total) ≫ₚ Word.mul
noncomputable def parameterDenominator : Code Data W := (kd ⋏ₚ md) ≫ₚ Word.mul
noncomputable def small : Code Data Bool := (parameterNumerator ⋏ₚ parameterDenominator) ≫ₚ Word.lt
noncomputable def measureLarge : Code (Data × List Bool) Bool :=
  ((fst ≫ₚ total) ⋏ₚ ((((fst ≫ₚ density) ⋏ₚ snd) ≫ₚ Array.mask ≫ₚ Word.sum) ≫ₚ Word.double)) ≫ₚ Word.lt
noncomputable def smallMask : Code Data (List Bool) :=
  (((mn ⋏ₚ beta) ≫ₚ Array.scale) ⋏ₚ ((md ⋏ₚ beta) ≫ₚ envMap (fst : Code (W × W) W))) ≫ₚ Array.lt

end RawBudget
end MeanPayoff.TreeDevice.Certified
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_FiniteIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace Array
noncomputable def choose : Code (List Bool × List W × List W) (List W) :=
  (fst ⋏ₚ ((snd ≫ₚ fst ⋏ₚ snd ≫ₚ snd) ≫ₚ zip zero zero (fst ⋏ₚ snd))) ≫ₚ
    zip false (zero,zero) (Code.branch fst (snd ≫ₚ fst) (snd ≫ₚ snd))
noncomputable def anyLE : Code (W × List W) Bool := envMap Word.le ≫ₚ any Code.id
end Array

end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

namespace RawBox
abbrev Data := W × List W × List W
noncomputable def width : Code Data W := fst
noncomputable def lower : Code Data (List W) := snd ≫ₚ fst
noncomputable def upper : Code Data (List W) := snd ≫ₚ snd
noncomputable def withFloor : Code (Data × List W) Data :=
  (fst ≫ₚ width) ⋏ₚ snd ⋏ₚ (fst ≫ₚ upper)
noncomputable def withCeiling : Code (Data × List W) Data :=
  (fst ≫ₚ width) ⋏ₚ (fst ≫ₚ lower) ⋏ₚ snd
noncomputable def clip : Code (Data × List W) (List W) :=
  ((fst ≫ₚ upper) ⋏ₚ (((fst ≫ₚ lower) ⋏ₚ snd) ≫ₚ Array.max)) ≫ₚ Array.min
noncomputable def midpoint : Code Data (List W) := (lower ⋏ₚ upper) ≫ₚ Array.average
noncomputable def averageClipped : Code (Data × List W × List W) (List W) :=
  (fst ⋏ₚ (snd ≫ₚ Array.average)) ≫ₚ clip
noncomputable def centered : Code (W × List W) Data :=
  (fst ≫ₚ Word.double) ⋏ₚ
    (((fst ≫ₚ Word.neg) ⋏ₚ snd) ≫ₚ Array.translate) ⋏ₚ (Code.id ≫ₚ Array.translate)
noncomputable def capLow : Code (Data × W) Data :=
  snd ⋏ₚ (fst ≫ₚ lower) ⋏ₚ
    (((fst ≫ₚ upper) ⋏ₚ ((snd ⋏ₚ (fst ≫ₚ lower)) ≫ₚ Array.translate)) ≫ₚ Array.min)
noncomputable def capHigh : Code (Data × W) Data :=
  snd ⋏ₚ (((fst ≫ₚ lower) ⋏ₚ (((snd ≫ₚ Word.neg) ⋏ₚ (fst ≫ₚ upper)) ≫ₚ Array.translate)) ≫ₚ Array.max) ⋏ₚ
    (fst ≫ₚ upper)
noncomputable def smallVector : Code (RawBudget.Data × Data) (List W) :=
  ((fst ≫ₚ RawBudget.smallMask) ⋏ₚ (snd ≫ₚ upper) ⋏ₚ (snd ≫ₚ lower)) ≫ₚ Array.choose
noncomputable def dividedWidth : Code (Data × Count) W := ((fst ≫ₚ width) ⋏ₚ snd) ≫ₚ Word.shiftRight
noncomputable def movedFloor : Code (Data × List W × W) Bool :=
  ((snd ≫ₚ snd) ⋏ₚ (((snd ≫ₚ fst) ⋏ₚ (fst ≫ₚ lower)) ≫ₚ Array.sub)) ≫ₚ Array.anyLE
noncomputable def movedCeiling : Code (Data × List W × W) Bool :=
  ((snd ≫ₚ snd) ⋏ₚ (((fst ≫ₚ upper) ⋏ₚ (snd ≫ₚ fst)) ≫ₚ Array.sub)) ≫ₚ Array.anyLE

end RawBox
end MeanPayoff.TreeDevice.Certified

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_RawSolutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

namespace Size
variable {α β : Type} [Encoding α] [Encoding β]
theorem fst (x : α×β) : treeSize (encode x.1)≤treeSize (encode x) := by
  change _≤treeSize (product encode encode x)
  simp only [product,treeSize_pair]
  omega
theorem snd (x : α×β) : treeSize (encode x.2)≤treeSize (encode x) := by
  change _≤treeSize (product encode encode x)
  simp only [product,treeSize_pair]
  omega
theorem mem {xs : List α} {x : α} (hx : x∈xs) : treeSize (encode x)≤treeSize (encode xs) := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    change _≤treeSize (listTree encode (a::xs))
    rw [listTree,treeSize_pair]
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have := ih hx; change _≤treeSize (listTree encode xs) at this; omega
theorem length (xs : List α) : xs.length≤treeSize (encode xs) := by
  change _≤treeSize (listTree encode xs)
  rw [listTree_size]
  omega
end Size

namespace Array

def Bounded (xs : List W) (N : ℕ) : Prop := ∀ w∈xs, w.digits.length≤N

theorem bounded_size (xs : List W) : Bounded xs (treeSize (encode xs)) := by
  intro w hw
  exact (digits_le_wordSize w).trans (Size.mem hw)

theorem size_bound {xs : List W} {N : ℕ} (h : Bounded xs N) :
    treeSize (encode xs)≤xs.length*(4*N+6)+1 := by
  induction xs with
  | nil => change 1≤0*(4*N+6)+1; omega
  | cons w ws ih =>
    have hw := wordSize_bound w
    have hn := h w (by simp)
    have ht := ih (fun v hv => h v (by simp [hv]))
    change treeSize (listTree wordData (w::ws))≤_
    rw [listTree,treeSize_pair,List.length_cons]
    change treeSize (listTree wordData ws)≤_ at ht
    nlinarith

theorem bounded_zip {xs ys : List W} {N : ℕ} (hx : Bounded xs N) (hy : Bounded ys N)
    (f : Code (W×W) W) (hf : ∀ z, f z=z.1 ∨ f z=z.2) :
    Bounded (zip zero zero f (xs,ys)) N := by
  change Bounded (Zip.zip f.eval zero xs ys) N
  induction xs generalizing ys with
  | nil => simp [Zip.zip,Bounded]
  | cons a as ih =>
    cases ys with
    | nil =>
      simp only [Zip.zip,List.headD_nil,List.tail_nil]
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · rcases hf (a,zero) with he | he
        · rw [he]; exact hx a (by simp)
        · rw [he]; exact Nat.zero_le _
      · exact ih (fun w hw => hx w (by simp [hw])) (ys:=[]) (by simp [Bounded]) w hw
    | cons b bs =>
      simp only [Zip.zip,List.headD_cons,List.tail_cons]
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · rcases hf (a,b) with he | he
        · rw [he]; exact hx a (by simp)
        · rw [he]; exact hy b (by simp)
      · exact ih (fun w hw => hx w (by simp [hw])) (ys:=bs)
          (fun w hw => hy w (by simp [hw])) w hw

theorem zip_length {α β γ : Type} (f : α×β→γ) (b : β) (xs : List α) (ys : List β) :
    (Zip.zip f b xs ys).length=xs.length := by
  induction xs generalizing ys with
  | nil => rfl
  | cons a as ih => cases ys <;> simp [Zip.zip,ih]
end Array

namespace RawBasic
abbrev Arena := List Graph.Vertex
abbrev Env := Arena × RawBox.Data
abbrev Acc := Env × List W

noncomputable def graph : Code (List W × Arena) (List W) :=
  ⟨fun z => z.2.map (fun v => Graph.vertex (z.1,v)),Graph.device,Graph.polynomial⟩
noncomputable def next : Code Acc (List W) :=
  ((fst ≫ₚ snd) ⋏ₚ ((snd ⋏ₚ (fst ≫ₚ fst)) ≫ₚ graph)) ≫ₚ RawBox.clip
noncomputable def advance : Code (Acc × Unit) Acc :=
  (fst ≫ₚ fst) ⋏ₚ (fst ≫ₚ next)

def ArenaBounded (g : Arena) (N : ℕ) : Prop :=
  ∀ v∈g, ∀ e∈v.2.1::v.2.2, e.2.digits.length≤N

theorem arenaBounded_size (g : Arena) : ArenaBounded g (treeSize (encode g)) := by
  intro v hv e he
  have hg := Size.mem hv
  have hv' := Size.snd v
  have he' : treeSize (encode e)≤treeSize (encode v.2) := by
    rcases List.mem_cons.mp he with rfl | he
    · exact Size.fst _
    · exact (Size.mem he).trans (Size.snd _)
  exact (digits_le_wordSize e.2).trans ((Size.snd e).trans (he'.trans (hv'.trans hg)))

theorem lookup_bound {xs : List W} {N : ℕ} (h : Array.Bounded xs N) (c : Count) :
    (Graph.lookup (xs,c)).digits.length≤N := by
  unfold Graph.lookup
  generalize hd : xs.drop c.length=ys
  cases ys with
  | nil => exact Nat.zero_le _
  | cons w ws =>
    apply h
    have hh : w∈xs.drop c.length := by rw [hd]; simp
    exact List.mem_of_mem_drop hh

theorem vertex_bound {xs : List W} {P Q : ℕ} (h : Array.Bounded xs P) (v : Graph.Vertex)
    (hv : ∀ e∈v.2.1::v.2.2, e.2.digits.length≤Q) :
    (Graph.vertex (xs,v)).digits.length≤P+Q+1 := by
  have he (e : Graph.Edge) (he : e∈v.2.1::v.2.2) :
      (Add.sumPair (Graph.edgePair (xs,e))).digits.length≤P+Q+1 := by
    have hp := lookup_bound h e.1
    have hq := hv e he
    change (Word.add (e.2,Graph.lookup (xs,e.1))).digits.length≤_
    rw [Word.add_length]
    omega
  have hm (f : W×W→W) (hf : ∀ z, f z=z.1 ∨ f z=z.2) :
      (Fold.fold f (Add.sumPair (Graph.batch (xs,v.2)).1)
        ((Graph.batch (xs,v.2)).2.map Add.sumPair)).digits.length≤P+Q+1 := by
    have H := EdgeScan.fold_mem f hf (Add.sumPair (Graph.batch (xs,v.2)).1)
      ((Graph.batch (xs,v.2)).2.map Add.sumPair)
    rcases List.mem_cons.mp H with hh | hh
    · rw [hh]; exact he v.2.1 (by simp)
    · obtain ⟨e,he',hh⟩ := List.mem_map.mp hh
      obtain ⟨e,hem,rfl⟩ := List.mem_map.mp he'
      rw [←hh]
      exact he e (List.mem_cons_of_mem _ hem)
  unfold Graph.vertex
  split
  · exact hm Order.high EdgeScan.high_mem
  · exact hm Order.low EdgeScan.low_mem

theorem graph_bound {xs : List W} {g : Arena} {P Q : ℕ}
    (h : Array.Bounded xs P) (hg : ArenaBounded g Q) :
    Array.Bounded (graph (xs,g)) (P+Q+1) := by
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  exact vertex_bound h v (hg v hv)

theorem clip_bound {b : RawBox.Data} {xs : List W} {N : ℕ}
    (ha : Array.Bounded b.2.1 N) (hb : Array.Bounded b.2.2 N) (hx : Array.Bounded xs N) :
    Array.Bounded (RawBox.clip (b,xs)) N := by
  exact Array.bounded_zip hb (Array.bounded_zip ha hx Word.max EdgeScan.high_mem)
    Word.min EdgeScan.low_mem

theorem next_bound {e : Env} {xs : List W} {N k : ℕ}
    (hg : ArenaBounded e.1 N) (ha : Array.Bounded e.2.2.1 N) (hb : Array.Bounded e.2.2.2 N)
    (hx : Array.Bounded xs (N+k*(N+1))) :
    Array.Bounded (next (e,xs)) (N+(k+1)*(N+1)) := by
  apply clip_bound
  · intro w hw; have := ha w hw; omega
  · intro w hw; have := hb w hw; omega
  · have hh := graph_bound hx hg
    intro w hw
    have := hh w hw
    simp only [Nat.add_mul,Nat.one_mul]
    omega

theorem next_length (e : Env) (xs : List W) : (next (e,xs)).length=e.2.2.2.length :=
  Array.zip_length _ _ _ _

theorem fold_layout (e : Env) (xs : List W) (cs : Count) :
    (Fold.fold advance.eval (e,xs) cs).1=e ∧
    (Fold.fold advance.eval (e,xs) cs).2.length=if cs=[] then xs.length else e.2.2.2.length := by
  induction cs generalizing xs with
  | nil => simp [Fold.fold]
  | cons u cs ih =>
    change (Fold.fold advance.eval (e,next (e,xs)) cs).1=e ∧ _
    have hh := ih (next (e,xs))
    refine ⟨hh.1,?_⟩
    change (Fold.fold advance.eval (e,next (e,xs)) cs).2.length=_
    rw [hh.2,next_length]
    simp

theorem fold_bound (s : Acc) (cs : Count) (N : ℕ)
    (hg : ArenaBounded s.1.1 N) (ha : Array.Bounded s.1.2.2.1 N)
    (hb : Array.Bounded s.1.2.2.2 N) (hx : Array.Bounded s.2 N) :
    (Fold.fold advance.eval s cs).1=s.1 ∧
    (Fold.fold advance.eval s cs).2.length ≤ s.2.length+s.1.2.2.2.length ∧
    Array.Bounded (Fold.fold advance.eval s cs).2 (N+cs.length*(N+1)) := by
  have main (e : Env) (xs : List W) (cs : Count) (k : ℕ)
      (hg : ArenaBounded e.1 N) (ha : Array.Bounded e.2.2.1 N) (hb : Array.Bounded e.2.2.2 N)
      (hx : Array.Bounded xs (N+k*(N+1))) :
      Array.Bounded (Fold.fold advance.eval (e,xs) cs).2 (N+(k+cs.length)*(N+1)) := by
    induction cs generalizing xs k with
    | nil => simpa [Fold.fold] using hx
    | cons u cs ih =>
      change Array.Bounded (Fold.fold advance.eval (e,next (e,xs)) cs).2 _
      have hh := ih (next (e,xs)) (k+1) (next_bound hg ha hb hx)
      simpa only [List.length_cons,show k+1+cs.length=k+(cs.length+1) by omega] using hh
  have hl := fold_layout s.1 s.2 cs
  refine ⟨hl.1,?_,?_⟩
  · rw [hl.2]; split <;> omega
  · simpa using main s.1 s.2 cs 0 hg ha hb (by simpa using hx)

theorem prefix_size (s : Acc) (cs : Count) (k : ℕ) (hk : k ≤ cs.length) :
    treeSize (encode (Fold.fold advance.eval s (cs.take k))) ≤
      50*(treeSize (encode (s,cs))+1)^3 := by
  let N := treeSize (encode (s,cs))+1
  have hs : treeSize (encode s)≤N := (Size.fst (s,cs)).trans (Nat.le_succ _)
  have he : treeSize (encode s.1)≤N := (Size.fst s).trans hs
  have hx : treeSize (encode s.2)≤N := (Size.snd s).trans hs
  have hg : treeSize (encode s.1.1)≤N := (Size.fst s.1).trans he
  have hb : treeSize (encode s.1.2)≤N := (Size.snd s.1).trans he
  have hab : treeSize (encode s.1.2.2)≤N := (Size.snd s.1.2).trans hb
  have ha : treeSize (encode s.1.2.2.1)≤N := (Size.fst s.1.2.2).trans hab
  have hb' : treeSize (encode s.1.2.2.2)≤N := (Size.snd s.1.2.2).trans hab
  have hl : (cs.take k).length≤N :=
    (List.length_take_le _ _).trans (hk.trans ((Size.length cs).trans ((Size.snd (s,cs)).trans (Nat.le_succ _))))
  have hh := fold_bound s (cs.take k) N
    (fun v hv e he => (arenaBounded_size _ v hv e he).trans hg)
    (fun w hw => (Array.bounded_size _ w hw).trans ha)
    (fun w hw => (Array.bounded_size _ w hw).trans hb')
    (fun w hw => (Array.bounded_size _ w hw).trans hx)
  have ho := Array.size_bound hh.2.2
  have hn : (Fold.fold advance.eval s (cs.take k)).2.length≤2*N := by
    have hx' := (Size.length s.2).trans hx
    have hb'' := (Size.length s.1.2.2.2).trans hb'
    omega
  have hm : N+(cs.take k).length*(N+1)≤N+N*(N+1) := by gcongr
  have ho' : treeSize (encode (Fold.fold advance.eval s (cs.take k)).2) ≤
      2*N*(4*(N+N*(N+1))+6)+1 := by
    apply ho.trans
    gcongr
  change treeSize (product encode encode (Fold.fold advance.eval s (cs.take k)))≤50*N^3
  rw [product,treeSize_pair,hh.1]
  have hpos : 1≤N := Nat.le_add_left _ _
  have h2 : N≤N*N := Nat.le_mul_self N
  have h3 : N*N≤N*N*N := Nat.mul_le_mul_right N h2
  nlinarith

noncomputable def loop : Code (Acc × Count) Acc := foldPrefix advance 50 3 prefix_size
noncomputable def solve : Code (Env × Count) (List W) :=
  (((fst ⋏ₚ (fst ≫ₚ snd ≫ₚ RawBox.lower)) ⋏ₚ snd) ≫ₚ loop) ≫ₚ snd

end RawBasic
end MeanPayoff.TreeDevice.Certified
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_RawLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

namespace Code
@[simp] theorem any_ofFn {α : Type} [Encoding α] {n : ℕ} (f : Code α Bool) (xs : Fin n → α) :
    any f (List.ofFn xs) = decide (∃ i, f (xs i)=true) := by
  simp only [any,comp_eval,filter_eval,empty_eval,not_eval]
  apply Bool.eq_iff_iff.mpr
  simp [List.filter_eq_nil_iff]
end Code

end MeanPayoff.TreeDevice.Certified

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_SizeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

namespace Word
@[simp] theorem sub_length (x y : W) : (sub (x,y)).digits.length = Max.max x.digits.length (Max.max y.digits.length 1+1)+1 := by
  change (add (x,neg y)).digits.length = _
  rw [add_length,neg_length]
@[simp] theorem average_length (x y : W) : (average (x,y)).digits.length=Max.max x.digits.length y.digits.length := by
  change (half (add (x,y))).digits.length = _
  simp only [half_length,add_length,Nat.add_sub_cancel]
end Word
end MeanPayoff.TreeDevice.Certified

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Driver
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp

namespace Code
variable {α β : Type} [Encoding α] [Encoding β]
noncomputable def select (tag : Code α Count) (cases : List (Code α β)) (fallback : Code α β) : Code α β :=
  match cases with
  | [] => fallback
  | c::cs => Code.branch (tag ≫ₚ empty) c (select (tag ≫ₚ tail) cs fallback)
end Code

end MeanPayoff.TreeDevice.Certified

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_DriverExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

namespace Size
@[simp] theorem pair {α β : Type} [Encoding α] [Encoding β] (x : α) (y : β) :
    treeSize (encode (x,y))=treeSize (encode x)+treeSize (encode y)+1 := by
  change treeSize (product encode encode (x,y))=_
  simp only [product,treeSize_pair]
end Size

end MeanPayoff.TreeDevice.Certified

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_InputCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace Word
noncomputable def digitCount : Code W Count := by
  let F := Map.device (TreeDevice.constant boolData Median.unitData ())
  let D : Code Digits Count := by
    refine ⟨fun d => d.bits.map (fun _ => ()), F.recode encode encode Digits.bits
      (fun d => d.bits.map (fun _ => ())) (fun _ => rfl) (fun _ => rfl), ?_⟩
    obtain ⟨K,d,h⟩ := PolynomialCost.map (LinearCost.constant boolData Median.unitData ()).polynomial
    exact ⟨K,d,fun z => h z.bits⟩
  exact digits ≫ₚ D
@[simp] theorem digitCount_length (w : W) : (digitCount w).length=w.digits.length := by
  change (w.digits.map (fun _ => ())).length=w.digits.length
  simp only [List.length_map]

end Word
namespace NaturalLog
abbrev State := W×Count
noncomputable def positive : Code State Bool := (Word.constant 0 ⋏ₚ fst) ≫ₚ Word.lt
noncomputable def step : Code (State×Unit) State :=
  Code.branch (fst ≫ₚ positive) (((fst ≫ₚ fst ≫ₚ Word.half) ⋏ₚ (fst ≫ₚ snd ≫ₚ Counter.inc))) fst
@[simp] theorem step_eval (s : State) (u : Unit) : step (s,u)=
    if 0 < s.1.val then (Word.half s.1,()::s.2) else s := by
  simp [step,positive,Counter.inc]
end NaturalLog
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

structure Parsed where
  raw : Normalize.Arena
instance instEncodingParsed : Encoding Parsed := ⟨fun p => Normalize.arenaData p.raw⟩
namespace InputCode
noncomputable def n : Code Parsed Count := by
  refine ⟨fun p => p.raw.1, Normalize.nDevice.recode encode encode Parsed.raw (fun p => p.raw.1)
    (fun _ => rfl) (fun _ => rfl), ?_⟩
  obtain ⟨K,d,h⟩ := (LinearCost.first Normalize.countData (product Normalize.ownersData Normalize.edgesData)).polynomial
  exact ⟨K,d,fun p => h p.raw⟩

def game (G : Game) : Parsed := ⟨(List.replicate G.n (),(List.ofFn G.maxOwner,List.ofFn (Normalize.encodedEdge G)))⟩
@[simp] theorem n_game (G : Game) : n (game G)=List.replicate G.n () := rfl
end InputCode
end MeanPayoff.TreeDevice.Certified
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Preparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Counter
@[simp] theorem inc_length (cs : Count) : (inc cs).length=cs.length+1 := rfl
end Counter
end MeanPayoff.TreeDevice.Certified

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Realizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.Box5
open RegisterBits BinaryData TreeDevice
open BinaryData.Take (config_ext)
def place (i : Fin 3) : Fin 5 := ⟨i.val,by omega⟩
noncomputable def program : Program 5 := rename Box.program place
end MeanPayoff.Box5

end

section
namespace MeanPayoff.Emit
open RegisterBits BinaryData TreeDevice
open BinaryData.Take (advance_add config_ext)
def program : RegisterBits.Program 5 where
  states := 5
  start := 0
  read _ := 0
  transition q top _ := match q.val with
    | 0 => top.map (fun b => ⟨if b then 1 else 4,.pop,none⟩)
    | 1 => top.map (fun b => if b then ⟨2,.pop,none⟩ else ⟨0,.pop,some false⟩)
    | 2 => some ⟨3,.pop,none⟩
    | 3 => some ⟨0,.pop,some true⟩
    | _ => none
def cfg (q : Fin 5) (xs out : List Bool) : Config program := ⟨some q,core xs [] [],out⟩
def cost (bs : List Bool) : ℕ := (bs.map (fun b => if b then 4 else 2)).sum+2
end MeanPayoff.Emit

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Orientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

namespace Code
variable {α β ρ : Type} [Encoding α] [Encoding β] [Encoding ρ]
noncomputable def stream (f : Code (α×ρ) (β×ρ))
    (hr : ∀ p r, treeSize (encode (f (p,r)).2)≤treeSize (encode r)) :
    Code ((α×List β×ρ)×Count) (α×List β×ρ) :=
  ⟨fun z => Fold.fold (StreamFold.step f.eval) z.1 z.2,
    Fold.device (StreamFold.stepDevice f.device),StreamFold.polynomial f.device f.polynomial hr⟩
end Code

namespace Counter
noncomputable def enumRow : Code (Unit×Count) (Count×Count) := (snd ≫ₚ tail) ⋏ₚ (snd ≫ₚ tail)
noncomputable def enumLoop : Code ((Unit×List Count×Count)×Count) (Unit×List Count×Count) :=
  stream enumRow (by
    intro u r
    cases r with
    | nil => exact le_rfl
    | cons a r =>
      change treeSize (listTree Median.unitData r)≤treeSize (listTree Median.unitData (a::r))
      rw [listTree,treeSize_pair]
      omega)
noncomputable def enum : Code Count (List Count) :=
  (((const () ⋏ₚ const [] ⋏ₚ Code.id) ⋏ₚ Code.id) ≫ₚ enumLoop) ≫ₚ snd ≫ₚ fst

end Counter

namespace RawMedian
noncomputable def scalar : Code (List W) W := ⟨Median.median,Median.device,Median.polynomial⟩
noncomputable def entry : Code (Count×List W) W := swap ≫ₚ nth Array.zero
noncomputable def column : Code (List (List W)×Count) W := swap ≫ₚ envMap entry ≫ₚ scalar
noncomputable def coordinates : Code (Count×List (List W)) (List W) :=
  (snd ⋏ₚ (fst ≫ₚ Counter.enum)) ≫ₚ envMap column
noncomputable def boxed : Code (RawBox.Data×List (List W)) (List W) :=
  Code.branch (snd ≫ₚ empty) (fst ≫ₚ RawBox.lower)
    (((fst ≫ₚ RawBox.lower ≫ₚ count) ⋏ₚ snd) ≫ₚ coordinates)

end RawMedian
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

namespace Code
variable {α : Type} [Encoding α]
noncomputable def getD (a : α) : Code ((List α×Count)×α) α :=
  Code.branch (fst ≫ₚ drop ≫ₚ empty) snd (fst ≫ₚ drop ≫ₚ head a)
@[simp] theorem getD_eval (a : α) (z : (List α×Count)×α) :
    getD a z=z.1.1.getD z.1.2.length z.2 := by
  simp only [getD,branch_eval,comp_eval,fst_eval,snd_eval,empty_eval,head_eval]
  change (if (z.1.1.drop z.1.2.length).isEmpty then z.2 else
    (z.1.1.drop z.1.2.length).headD a)=_
  rw [List.getD_eq_getElem?_getD,←List.head?_drop]
  generalize z.1.1.drop z.1.2.length=xs
  cases xs <;> rfl
end Code

namespace Array
noncomputable def scalarLT : Code (W×List W) (List Bool) := envMap Word.lt
noncomputable def scalarLE : Code (W×List W) (List Bool) := envMap Word.le
noncomputable def belowScalar : Code (W×List W) (List Bool) := envMap (swap ≫ₚ Word.lt)

end Array

namespace RawOrientation
abbrev Data := Bool×List (List Bool)

noncomputable def positives : Code (RawBox.Data×W×List W) (List Bool) :=
  ((fst ≫ₚ RawBox.width ≫ₚ Word.double) ⋏ₚ
    (((snd ≫ₚ fst) ⋏ₚ (((snd ≫ₚ snd) ⋏ₚ (fst ≫ₚ RawBox.midpoint)) ≫ₚ Array.sub)) ≫ₚ Array.scale)) ≫ₚ Array.scalarLT
noncomputable def negatives : Code (RawBox.Data×W×List W) (List Bool) :=
  ((fst ≫ₚ RawBox.width ≫ₚ Word.double ≫ₚ Word.neg) ⋏ₚ
    (((snd ≫ₚ fst) ⋏ₚ (((snd ≫ₚ snd) ⋏ₚ (fst ≫ₚ RawBox.midpoint)) ≫ₚ Array.sub)) ≫ₚ Array.scale)) ≫ₚ Array.belowScalar
noncomputable def baseMask : Code (RawBox.Data×List W) (List Bool) :=
  ((fst ≫ₚ RawBox.width) ⋏ₚ (((snd ⋏ₚ (fst ≫ₚ RawBox.lower)) ≫ₚ Array.sub) ≫ₚ map Word.double)) ≫ₚ Array.scalarLE
noncomputable def singleton : Code (Bool×List Bool) Data := fst ⋏ₚ ((snd ⋏ₚ const []) ≫ₚ cons)
noncomputable def trueComplement : Code (List Bool) Data :=
  (const true ⋏ₚ Array.complement) ≫ₚ singleton
noncomputable def falseComplement : Code (List Bool) Data :=
  (const false ⋏ₚ Array.complement) ≫ₚ singleton
noncomputable def baseOnMask : Code (RawBudget.Data×List Bool) Data :=
  Code.branch RawBudget.measureLarge (snd ≫ₚ trueComplement) ((const false ⋏ₚ snd) ≫ₚ singleton)
noncomputable def base : Code (RawBudget.Data×RawBox.Data×List W) Data :=
  (fst ⋏ₚ (snd ≫ₚ baseMask)) ≫ₚ baseOnMask
noncomputable def extend : Code (Data×List Bool×List Bool) Data :=
  (fst ≫ₚ fst) ⋏ₚ (((fst ≫ₚ snd) ⋏ₚ (((snd ≫ₚ fst) ⋏ₚ (((snd ≫ₚ snd) ⋏ₚ const []) ≫ₚ cons)) ≫ₚ cons)) ≫ₚ append)
noncomputable def combine : Code (List Data) Data :=
  (((count ≫ₚ Counter.word) ⋏ₚ (filter fst ≫ₚ count ≫ₚ Counter.word ≫ₚ Word.double)) ≫ₚ Word.lt) ⋏ₚ
    (map snd ≫ₚ flatten)

end RawOrientation
end MeanPayoff.TreeDevice.Certified

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Control
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

namespace RawControl
abbrev Orient := RawOrientation.Data
abbrev Tuple := RawBudget.Data×RawBox.Data×Count×List W×List W×List (List W)×Orient×List Orient
structure Pack where
  p : RawBudget.Data
  b : RawBox.Data
  t : Count
  q : List W
  r : List W
  vs : List (List W)
  o : Orient
  os : List Orient

def Pack.tuple (z : Pack) : Tuple := (z.p,z.b,z.t,z.q,z.r,z.vs,z.o,z.os)
instance instEncodingPack : Encoding Pack := ⟨fun z => encode z.tuple⟩

def zeroBudget : RawBudget.Data := ((Array.zero,Array.zero),(Array.zero,Array.zero),[],[])
def zeroBox : RawBox.Data := (Array.zero,[],[])
def Pack.zero : Pack := ⟨zeroBudget,zeroBox,[],[],[],[],(false,[]),[]⟩

noncomputable def proj {α : Type} [Encoding α] (f : Code Tuple α) : Code Pack α :=
  f.recode Pack.tuple (fun z => f z.tuple) (fun _ => rfl) (fun _ => rfl)
noncomputable def p : Code Pack RawBudget.Data := proj fst
noncomputable def b : Code Pack RawBox.Data := proj (snd ≫ₚ fst)
noncomputable def t : Code Pack Count := proj (snd ≫ₚ snd ≫ₚ fst)
noncomputable def q : Code Pack (List W) := proj (snd ≫ₚ snd ≫ₚ snd ≫ₚ fst)
noncomputable def r : Code Pack (List W) := proj (snd ≫ₚ snd ≫ₚ snd ≫ₚ snd ≫ₚ fst)
noncomputable def vs : Code Pack (List (List W)) := proj (snd ≫ₚ snd ≫ₚ snd ≫ₚ snd ≫ₚ snd ≫ₚ fst)
noncomputable def o : Code Pack Orient := proj (snd ≫ₚ snd ≫ₚ snd ≫ₚ snd ≫ₚ snd ≫ₚ snd ≫ₚ fst)
noncomputable def os : Code Pack (List Orient) := proj (snd ≫ₚ snd ≫ₚ snd ≫ₚ snd ≫ₚ snd ≫ₚ snd ≫ₚ snd)

@[simp] theorem p_eval (z : Pack) : p z=z.p := rfl
@[simp] theorem b_eval (z : Pack) : b z=z.b := rfl
@[simp] theorem t_eval (z : Pack) : t z=z.t := rfl
@[simp] theorem q_eval (z : Pack) : q z=z.q := rfl
@[simp] theorem r_eval (z : Pack) : r z=z.r := rfl
@[simp] theorem vs_eval (z : Pack) : vs z=z.vs := rfl
@[simp] theorem o_eval (z : Pack) : o z=z.o := rfl
@[simp] theorem os_eval (z : Pack) : os z=z.os := rfl

noncomputable def pack {α : Type} [Encoding α]
    (p : Code α RawBudget.Data := const zeroBudget)
    (b : Code α RawBox.Data := const zeroBox)
    (t : Code α Count := const [])
    (q r : Code α (List W) := const [])
    (vs : Code α (List (List W)) := const [])
    (o : Code α Orient := const (false,[]))
    (os : Code α (List Orient) := const []) : Code α Pack :=
  (p ⋏ₚ b ⋏ₚ t ⋏ₚ q ⋏ₚ r ⋏ₚ vs ⋏ₚ o ⋏ₚ os).recode _root_.id
    (fun x => ⟨p x,b x,t x,q x,r x,vs x,o x,os x⟩) (fun _ => rfl) (fun _ => rfl)
@[simp] theorem pack_eval {α : Type} [Encoding α]
    (p : Code α RawBudget.Data) (b : Code α RawBox.Data) (t : Code α Count)
    (q r : Code α (List W)) (vs : Code α (List (List W))) (o : Code α Orient) (os : Code α (List Orient)) (x : α) :
    pack p b t q r vs o os x=⟨p x,b x,t x,q x,r x,vs x,o x,os x⟩ := rfl

abbrev Cell := Count×Pack
abbrev State := Cell×List Cell
abbrev Env := RawBasic.Arena×Count×Count×Count×Count

noncomputable def arena : Code Env RawBasic.Arena := fst
noncomputable def exponent : Code Env Count := snd ≫ₚ fst
noncomputable def samples : Code Env Count := snd ≫ₚ snd ≫ₚ fst
noncomputable def trials : Code Env Count := snd ≫ₚ snd ≫ₚ snd ≫ₚ fst
noncomputable def basicSteps : Code Env Count := snd ≫ₚ snd ≫ₚ snd ≫ₚ snd

abbrev Input := Env×Count×State
noncomputable def env : Code Input Env := fst
noncomputable def random : Code Input Count := snd ≫ₚ fst
noncomputable def state : Code Input State := snd ≫ₚ snd
noncomputable def current : Code Input Pack := state ≫ₚ fst ≫ₚ snd
noncomputable def stack : Code Input (List Cell) := state ≫ₚ snd
noncomputable def caller : Code Input Pack := stack ≫ₚ head ([],Pack.zero) ≫ₚ snd
noncomputable def rest : Code Input (List Cell) := stack ≫ₚ tail
noncomputable def makeCell {α : Type} [Encoding α] (tag : ℕ) (c : Code α Pack) : Code α Cell :=
  const (List.replicate tag ()) ⋏ₚ c
noncomputable def call {α : Type} [Encoding α] (tag : ℕ) (c : Code α Pack) (k : Code α (List Cell)) : Code α State :=
  makeCell tag c ⋏ₚ k
noncomputable def ret {α : Type} [Encoding α] (c : Code α Pack) (k : Code α (List Cell)) : Code α State := call 10 c k
noncomputable def push {α : Type} [Encoding α] (tag : ℕ) (c : Code α Pack) (k : Code α (List Cell)) : Code α (List Cell) :=
  (makeCell tag c ⋏ₚ k) ≫ₚ cons
noncomputable def save (tag : ℕ) : Code Input (List Cell) := push tag current stack
noncomputable def smallWidth (x : Code Input RawBox.Data) : Code Input Bool :=
  ((x ≫ₚ RawBox.width) ⋏ₚ (env ≫ₚ samples ≫ₚ Counter.word ≫ₚ RawBudget.times 128)) ≫ₚ Word.le
noncomputable def basic (x : Code Input RawBox.Data) : Code Input (List W) :=
  (((env ≫ₚ arena) ⋏ₚ x) ⋏ₚ (env ≫ₚ basicSteps)) ≫ₚ RawBasic.solve
noncomputable def narrow (x : Code Input RawBox.Data) (v : Code Input (List W)) : Code Input RawBox.Data :=
  (((x ⋏ₚ (((env ≫ₚ exponent) ⋏ₚ const (List.replicate 5 ())) ≫ₚ Counter.add)) ≫ₚ RawBox.dividedWidth) ⋏ₚ v) ≫ₚ RawBox.centered
noncomputable def wide (x : Code Input RawBox.Data) (v : Code Input (List W)) : Code Input RawBox.Data :=
  (((x ⋏ₚ const (List.replicate 3 ())) ≫ₚ RawBox.dividedWidth) ⋏ₚ v) ≫ₚ RawBox.centered
noncomputable def delta (x : Code Input RawBox.Data) : Code Input W :=
  (x ⋏ₚ (((env ≫ₚ exponent) ⋏ₚ const (List.replicate 2 ())) ≫ₚ Counter.add)) ≫ₚ RawBox.dividedWidth
noncomputable def capWidth (x : Code Input RawBox.Data) : Code Input W :=
  ((x ≫ₚ RawBox.width) ⋏ₚ delta x) ≫ₚ Word.sub

noncomputable def solveCase : Code Input State :=
  Code.branch (current ≫ₚ p ≫ₚ RawBudget.small)
    (ret (pack (q:=((current ≫ₚ p) ⋏ₚ (current ≫ₚ b)) ≫ₚ RawBox.smallVector)) stack)
    (Code.branch (smallWidth (current ≫ₚ b))
      (ret (pack (q:=basic (current ≫ₚ b))) stack)
      (call 8 (pack (current ≫ₚ p) (current ≫ₚ b)) (save 15)))
noncomputable def askCase : Code Input State :=
  call 2 (pack (current ≫ₚ p) (current ≫ₚ b) (env ≫ₚ trials)) (save 2)
noncomputable def trialsCase : Code Input State :=
  Code.branch (current ≫ₚ t ≫ₚ empty)
    (ret (pack (vs:=const [])) stack)
    (call 0 current (push 0 (pack (current ≫ₚ p) (current ≫ₚ b) (current ≫ₚ t ≫ₚ tail)) stack))
noncomputable def updateCase : Code Input State :=
  call 1 (pack (current ≫ₚ p ≫ₚ RawBudget.reduceK) (narrow (current ≫ₚ b) (current ≫ₚ q))) (save 3)
noncomputable def centersCase : Code Input State :=
  Code.branch (current ≫ₚ t ≫ₚ empty)
    (ret (pack (vs:=((current ≫ₚ q) ⋏ₚ const []) ≫ₚ cons)) stack)
    (call 3 current (push 5 (pack (current ≫ₚ p) (current ≫ₚ b) (current ≫ₚ t ≫ₚ tail) (current ≫ₚ q)) stack))
noncomputable def orientCase : Code Input State :=
  Code.branch (smallWidth (current ≫ₚ b))
    (ret (pack (o:=((current ≫ₚ p) ⋏ₚ (current ≫ₚ b) ⋏ₚ basic (current ≫ₚ b)) ≫ₚ RawOrientation.base)) stack)
    (call 4 (pack (current ≫ₚ p) (current ≫ₚ b) (env ≫ₚ samples) (current ≫ₚ b ≫ₚ RawBox.midpoint)) (save 6))
noncomputable def orientTrialsCase : Code Input State :=
  Code.branch (current ≫ₚ t ≫ₚ empty) (ret (pack (os:=const [])) stack)
    (call 5 current (push 8 (pack (current ≫ₚ p) (current ≫ₚ b) (current ≫ₚ t ≫ₚ tail)) stack))
noncomputable def orientPlusCase : Code Input State :=
  call 6 (pack (current ≫ₚ p) (current ≫ₚ b) (env ≫ₚ trials)) (save 10)
noncomputable def tightenCase : Code Input State :=
  call 1 (pack (current ≫ₚ p ≫ₚ RawBudget.reduceK) (current ≫ₚ b)) (save 11)
noncomputable def reweightCase : Code Input State :=
  Code.branch (current ≫ₚ o ≫ₚ snd ≫ₚ empty) (ret (pack (vs:=const [])) stack)
    (call 1 (pack
      (Code.branch (current ≫ₚ o ≫ₚ fst)
        (((current ≫ₚ p) ⋏ₚ (current ≫ₚ o ≫ₚ snd ≫ₚ head [])) ≫ₚ RawBudget.reweightM)
        (((current ≫ₚ p) ⋏ₚ (current ≫ₚ o ≫ₚ snd ≫ₚ head [])) ≫ₚ RawBudget.reweightK))
      (current ≫ₚ b))
      (push 17 (pack (current ≫ₚ p) (current ≫ₚ b)
        (o:=(current ≫ₚ o ≫ₚ fst) ⋏ₚ (current ≫ₚ o ≫ₚ snd ≫ₚ tail))) stack))
end RawControl
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Array

theorem fold_select_bound (f : Code (W×W) W) (hf : ∀ z, f z=z.1 ∨ f z=z.2)
    {N : ℕ} {xs : List W} {xss : List (List W)} (h : Bounded xs N)
    (hs : ∀ ys∈xss, Bounded ys N) :
    Bounded (Fold.fold (zip zero zero f).eval xs xss) N ∧
      (Fold.fold (zip zero zero f).eval xs xss).length=xs.length := by
  induction xss generalizing xs with
  | nil => exact ⟨h,rfl⟩
  | cons ys yss ih =>
    change Bounded (Fold.fold _ (zip zero zero f (xs,ys)) yss) N ∧ _
    have hh := ih (bounded_zip h (hs ys (by simp)) f hf) (fun zs hz => hs zs (by simp [hz]))
    exact ⟨hh.1,hh.2.trans (zip_length f.eval zero xs ys)⟩

noncomputable def foldSelect (f : Code (W×W) W) (hf : ∀ z, f z=z.1 ∨ f z=z.2) :
    Code (List W×List (List W)) (List W) :=
  foldPrefix (zip zero zero f) 20 2 (by
    intro xs xss k _hk
    let S := treeSize (encode (xs,xss))
    have hx : Bounded xs S := fun w hw => (digits_le_wordSize w).trans ((Size.mem hw).trans (Size.fst (xs,xss)))
    have hxs : ∀ ys∈xss.take k, Bounded ys S := by
      intro ys hy w hw
      exact (digits_le_wordSize w).trans ((Size.mem hw).trans
        ((Size.mem (List.mem_of_mem_take hy)).trans (Size.snd (xs,xss))))
    have hb := fold_select_bound f hf hx hxs
    have ht := size_bound hb.1
    rw [hb.2] at ht
    have hl := (Size.length xs).trans (Size.fst (xs,xss))
    change xs.length≤S at hl
    have hm := Nat.mul_le_mul_right (4*S+6) hl
    calc
      treeSize (encode (Fold.fold (zip zero zero f).eval xs (xss.take k))) ≤ xs.length*(4*S+6)+1 := ht
      _ ≤ 20*(S+1)^2 := by nlinarith)
noncomputable def foldMin : Code (List W×List (List W)) (List W) := foldSelect Word.min EdgeScan.low_mem
noncomputable def foldMax : Code (List W×List (List W)) (List W) := foldSelect Word.max EdgeScan.high_mem

end Array
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

noncomputable def trialsHeadCase : Code Input State :=
  call 2 (pack (caller ≫ₚ p) (caller ≫ₚ b) (caller ≫ₚ t))
    (push 1 (pack (q:=current ≫ₚ q)) rest)
noncomputable def vectorConsCase : Code Input State :=
  ret (pack (vs:=((caller ≫ₚ q) ⋏ₚ (current ≫ₚ vs)) ≫ₚ cons)) rest
noncomputable def medianCase : Code Input State :=
  ret (pack (q:=((caller ≫ₚ b) ⋏ₚ (current ≫ₚ vs)) ≫ₚ RawMedian.boxed)) rest
noncomputable def centerFirstCase : Code Input State :=
  call 1 (pack (caller ≫ₚ p ≫ₚ RawBudget.reduceM) (narrow (caller ≫ₚ b) (caller ≫ₚ q)))
    (push 4 (pack (b:=caller ≫ₚ b) (r:=current ≫ₚ q)) rest)
noncomputable def centerSecondCase : Code Input State :=
  ret (pack (q:=((caller ≫ₚ b) ⋏ₚ (caller ≫ₚ r) ⋏ₚ (current ≫ₚ q)) ≫ₚ RawBox.averageClipped)) rest
noncomputable def centersHeadCase : Code Input State :=
  call 4 (pack (caller ≫ₚ p) (caller ≫ₚ b) (caller ≫ₚ t) (current ≫ₚ q))
    (push 1 (pack (q:=caller ≫ₚ q)) rest)
noncomputable def centerAt (index : Code Input Count) : Code Input (List W) :=
  (((current ≫ₚ vs) ⋏ₚ index) ⋏ₚ (caller ≫ₚ b ≫ₚ RawBox.midpoint)) ≫ₚ getD []
noncomputable def lastPositive : Code Input (List Bool) :=
  ((caller ≫ₚ b) ⋏ₚ (env ≫ₚ samples ≫ₚ Counter.word) ⋏ₚ centerAt (env ≫ₚ samples)) ≫ₚ RawOrientation.positives
noncomputable def lastNegative : Code Input (List Bool) :=
  ((caller ≫ₚ b) ⋏ₚ (env ≫ₚ samples ≫ₚ Counter.word) ⋏ₚ centerAt (env ≫ₚ samples)) ≫ₚ RawOrientation.negatives
noncomputable def orientLoopCase : Code Input State :=
  Code.branch (((caller ≫ₚ p) ⋏ₚ lastPositive) ≫ₚ RawBudget.measureLarge)
    (ret (pack (o:=lastPositive ≫ₚ RawOrientation.trueComplement)) rest)
    (Code.branch (((caller ≫ₚ p) ⋏ₚ lastNegative) ≫ₚ RawBudget.measureLarge)
      (ret (pack (o:=lastNegative ≫ₚ RawOrientation.falseComplement)) rest)
      (call 5 (pack (caller ≫ₚ p) (wide (caller ≫ₚ b) (centerAt random)))
        (push 7 (pack (o:=const false ⋏ₚ ((lastPositive ⋏ₚ ((lastNegative ⋏ₚ const []) ≫ₚ cons)) ≫ₚ cons))) rest)))
noncomputable def orientTailCase : Code Input State :=
  ret (pack (o:=((current ≫ₚ o) ⋏ₚ (caller ≫ₚ o ≫ₚ snd ≫ₚ head []) ⋏ₚ
    (caller ≫ₚ o ≫ₚ snd ≫ₚ tail ≫ₚ head [])) ≫ₚ RawOrientation.extend)) rest
noncomputable def orientHeadCase : Code Input State :=
  call 6 (pack (caller ≫ₚ p) (caller ≫ₚ b) (caller ≫ₚ t))
    (push 9 (pack (o:=current ≫ₚ o)) rest)
noncomputable def orientConsCase : Code Input State :=
  ret (pack (os:=((caller ≫ₚ o) ⋏ₚ (current ≫ₚ os)) ≫ₚ cons)) rest
noncomputable def combineCase : Code Input State :=
  ret (pack (o:=current ≫ₚ os ≫ₚ RawOrientation.combine)) rest
noncomputable def tightenFirstCase : Code Input State :=
  Code.branch (((caller ≫ₚ b) ⋏ₚ (current ≫ₚ q) ⋏ₚ delta (caller ≫ₚ b)) ≫ₚ RawBox.movedFloor)
    (call 8 (pack (caller ≫ₚ p) (((caller ≫ₚ b) ⋏ₚ (current ≫ₚ q)) ≫ₚ RawBox.withFloor))
      (push 13 (pack (b:=caller ≫ₚ b) (q:=current ≫ₚ q)) rest))
    (call 1 (pack (caller ≫ₚ p ≫ₚ RawBudget.reduceM) (caller ≫ₚ b)) (push 12 caller rest))
noncomputable def tightenSecondCase : Code Input State :=
  Code.branch (((caller ≫ₚ b) ⋏ₚ (current ≫ₚ q) ⋏ₚ delta (caller ≫ₚ b)) ≫ₚ RawBox.movedCeiling)
    (call 8 (pack (caller ≫ₚ p) (((caller ≫ₚ b) ⋏ₚ (current ≫ₚ q)) ≫ₚ RawBox.withCeiling))
      (push 14 (pack (b:=caller ≫ₚ b) (q:=current ≫ₚ q)) rest))
    (ret (pack (b:=caller ≫ₚ b)) rest)
noncomputable def boxPassCase : Code Input State := ret (pack (b:=current ≫ₚ b)) rest
noncomputable def solveTightCase : Code Input State :=
  call 7 (pack (caller ≫ₚ p) (current ≫ₚ b))
    (push 16 (pack (caller ≫ₚ p) (current ≫ₚ b)) (push 21 (const Pack.zero) rest))
noncomputable def solveOrientedCase : Code Input State :=
  call 9 (pack (caller ≫ₚ p) (caller ≫ₚ b) (o:=current ≫ₚ o))
    (push 18 (pack (caller ≫ₚ p) (caller ≫ₚ b) (o:=(current ≫ₚ o ≫ₚ fst) ⋏ₚ const [])) rest)
noncomputable def reweightHeadCase : Code Input State :=
  call 9 (pack (caller ≫ₚ p) (caller ≫ₚ b) (o:=caller ≫ₚ o))
    (push 1 (pack (q:=current ≫ₚ q)) rest)
noncomputable def solveReweightedCase : Code Input State :=
  Code.branch (caller ≫ₚ o ≫ₚ fst)
    (call 0 (pack (caller ≫ₚ p) (((caller ≫ₚ b) ⋏ₚ capWidth (caller ≫ₚ b)) ≫ₚ RawBox.capHigh))
      (push 19 (pack (b:=caller ≫ₚ b) (vs:=current ≫ₚ vs)) rest))
    (call 0 (pack (caller ≫ₚ p) (((caller ≫ₚ b) ⋏ₚ capWidth (caller ≫ₚ b)) ≫ₚ RawBox.capLow))
      (push 20 (pack (b:=caller ≫ₚ b) (vs:=current ≫ₚ vs)) rest))
noncomputable def capHighCase : Code Input State :=
  ret (pack (q:=((current ≫ₚ q) ⋏ₚ (caller ≫ₚ vs)) ≫ₚ Array.foldMin)) rest
noncomputable def capLowCase : Code Input State :=
  ret (pack (q:=((current ≫ₚ q) ⋏ₚ (caller ≫ₚ vs)) ≫ₚ Array.foldMax)) rest
noncomputable def includeInnerCase : Code Input State := ret (pack (q:=current ≫ₚ q)) rest

noncomputable def resume : Code Input State :=
  Code.branch (stack ≫ₚ empty) state
    (select (stack ≫ₚ head ([],Pack.zero) ≫ₚ fst)
      [trialsHeadCase,vectorConsCase,medianCase,centerFirstCase,centerSecondCase,centersHeadCase,
       orientLoopCase,orientTailCase,orientHeadCase,orientConsCase,combineCase,tightenFirstCase,
       tightenSecondCase,boxPassCase,boxPassCase,solveTightCase,solveOrientedCase,reweightHeadCase,
       solveReweightedCase,capHighCase,capLowCase,includeInnerCase] state)

noncomputable def dispatch : Code Input State :=
  select (state ≫ₚ fst ≫ₚ fst)
    [solveCase,askCase,trialsCase,updateCase,centersCase,orientCase,orientTrialsCase,orientPlusCase,
      tightenCase,reweightCase] resume
end MeanPayoff.TreeDevice.Certified.RawControl

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_StateGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace RawOrientation
 def listMass (os : List Data) : ℕ := (os.map (fun o => o.2.length)).sum
 @[simp] theorem listMass_nil : listMass []=0 := rfl
 @[simp] theorem listMass_cons (o : Data) (os : List Data) : listMass (o::os)=o.2.length+listMass os := rfl
end RawOrientation
namespace RawControl
 def Pack.mass (z : Pack) : ℕ := z.vs.length+z.o.2.length+z.os.length+RawOrientation.listMass z.os
 def stackMass (ks : List Cell) : ℕ := (ks.map (fun c => c.2.mass)).sum
 @[simp] theorem stackMass_nil : stackMass []=0 := rfl
 @[simp] theorem stackMass_cons (c : Cell) (ks : List Cell) : stackMass (c::ks)=c.2.mass+stackMass ks := rfl
end RawControl
end MeanPayoff.TreeDevice.Certified

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_SizeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
 def StackTags (H : ℕ) (ks : List Cell) : Prop := ∀ c∈ks, c.1.length≤H
 @[simp] theorem stackTags_nil (H : ℕ) : StackTags H [] := by intro c hc; cases hc
end MeanPayoff.TreeDevice.Certified.RawControl

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Loop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
abbrev Acc := Env×State
end MeanPayoff.TreeDevice.Certified.RawControl

end

end OAI
end


