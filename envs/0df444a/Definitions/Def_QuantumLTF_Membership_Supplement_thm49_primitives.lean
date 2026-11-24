-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
-- name    : QuantumLTF_Membership_Supplement_thm49_primitives
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-24T05:57:34.041479+00:00
-- url     : https://prove2.me/theorems/28af482e-752e-4ea8-9afc-e892e8959cd4
-- title:
--   Coherent quantum circuit primitives (`ctrlHadamardN`, `multiEqCtrl1`, `hammingCounter`) in `gates12`
-- statement:
--   This module provides foundational circuit combinators and arithmetic/control primitives in the $1$- and $2$-qubit unitary gate model (`gates12`) with clean ancillas (`nonOracleDepth`).
--
--   Let $n, L \in \mathbb{N}$ be register sizes, let $p \in \{0,1\}^L$ be a bit-pattern, and let $U \in U(2)$ be a single-qubit unitary gate. The module formalizes LSB binary encodings `natToBitsLSB` and `bitsToNatLSB`, depth-additive `LayeredCircuit` composition (`seq`, `parMerge`, `mapWires`, `adj`) with clean-ancilla correctness `ImplementsOnClean`, a logarithmic-depth parallel fanout and controlled-Hadamard layer `ctrlHadamardN` ($O(n)$ gates, $O(\log n)$ depth), a multi-qubit equality-controlled gate `multiEqCtrl1` ($O(L)$ gates, $O(\log(L+1))$ depth), and a parallel carry-save/ripple-carry Hamming-weight adder `hammingCounter`:
--
--   $$|x\rangle |0\rangle^{\otimes \lceil \log_2(n+1)\rceil} |0\rangle^{\otimes a} \longmapsto |x\rangle |w(x)\rangle |0\rangle^{\otimes a},$$
--
--   where $w(x) = \sum_{i=0}^{n-1} x_i$, implemented with $O(n)$ gates and $O(\log(n+1))$ non-oracle depth.
--
--   These primitives serve as shared verified building blocks for clocked quantum walk and coherent routing circuits.
--
--   **Formalization Note.** All declarations live in namespace `Thm49Primitives`, compiled under `autoImplicit false`, over `QAlgorithms.LayeredCircuit` / `gates12` / `nonOracleDepth`.
-- source:
--   Krivcenko, Nguyen, de Wolf (2026), Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Appendix C.5, pp. 95-99

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Supplement_nonOracleDepth

set_option autoImplicit false

namespace Thm49Primitives

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

/-! ### 1. LSB Binary Encoding Helpers -/

def natToBitsLSB (ℓ val : ℕ) : Qubits ℓ := fun j => val.testBit j.val

def bitsToNatLSB {ℓ : ℕ} (v : Qubits ℓ) : ℕ :=
  ∑ j : Fin ℓ, if v j then 2 ^ j.val else 0

lemma bitsToNatLSB_lt (ℓ : ℕ) (v : Qubits ℓ) : bitsToNatLSB v < 2 ^ ℓ := by
  induction ℓ with
  | zero => simp [bitsToNatLSB]
  | succ ℓ ih =>
    simp only [bitsToNatLSB, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    have hinit : (∑ i : Fin ℓ, if v i.castSucc then 2 ^ i.val else 0) < 2 ^ ℓ :=
      ih (fun i => v i.castSucc)
    have hlast : (if v (Fin.last ℓ) then 2 ^ ℓ else 0) ≤ 2 ^ ℓ := by split_ifs <;> omega
    rw [pow_succ']
    omega

lemma natToBitsLSB_zero (ℓ : ℕ) : natToBitsLSB ℓ 0 = fun _ => false := by
  funext j
  simp [natToBitsLSB]

lemma natToBitsLSB_testBit1 {ℓ t : ℕ} (h1 : 1 < ℓ) :
    natToBitsLSB ℓ t ⟨1, h1⟩ = decide (t % 4 = 2 ∨ t % 4 = 3) := by
  simp only [natToBitsLSB]
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h4 : t = 4 * (t / 4) + t % 4 := (Nat.div_add_mod t 4).symm
  have ht2 : t / 2 = 2 * (t / 4) + (t % 4) / 2 := by omega
  have hlt : t % 4 < 4 := Nat.mod_lt t (by norm_num)
  have hpow : (2 : ℕ) ^ 1 = 2 := by norm_num
  rw [hpow, ht2]
  rcases (by omega : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3) with hr | hr | hr | hr <;>
  · rw [hr]; simp

lemma natToBitsLSB_bitsToNatLSB {ℓ : ℕ} (v : Qubits ℓ) :
    natToBitsLSB ℓ (bitsToNatLSB v) = v := by
  induction ℓ with
  | zero =>
    funext j
    exact Fin.elim0 j
  | succ ℓ ih =>
    funext j
    simp only [natToBitsLSB, bitsToNatLSB, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    set a := ∑ i : Fin ℓ, if v i.castSucc then 2 ^ i.val else 0
    have ha : a < 2 ^ ℓ := bitsToNatLSB_lt ℓ (fun i => v i.castSucc)
    refine Fin.lastCases ?_ ?_ j
    · simp only [Fin.val_last]
      rw [Nat.testBit_eq_decide_div_mod_eq]
      cases hv : v (Fin.last ℓ)
      · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
        have hdiv : a / 2 ^ ℓ = 0 := Nat.div_eq_of_lt ha
        simp [hdiv]
      · simp only [↓reduceIte]
        have hdiv : (a + 2 ^ ℓ) / 2 ^ ℓ = 1 := by
          rw [Nat.add_div_right _ (Nat.two_pow_pos ℓ), Nat.div_eq_of_lt ha]
        simp [hdiv]
    · intro i
      simp only [Fin.val_castSucc]
      have hi : i.val < ℓ := i.isLt
      have hmod_add : (a + (if v (Fin.last ℓ) then 2 ^ ℓ else 0)) % 2 ^ ℓ = a := by
        split_ifs
        · rw [Nat.add_mod_right, Nat.mod_eq_of_lt ha]
        · rw [add_zero, Nat.mod_eq_of_lt ha]
      have htb_mod : ∀ x : ℕ, (x % 2 ^ ℓ).testBit i.val = x.testBit i.val := by
        intro x
        rw [Nat.testBit_mod_two_pow]
        simp [hi]
      rw [← htb_mod (a + (if v (Fin.last ℓ) then 2 ^ ℓ else 0)), hmod_add]
      exact congrFun (ih (fun k => v k.castSucc)) i

lemma bitsToNatLSB_natToBitsLSB {ℓ val : ℕ} (h : val < 2 ^ ℓ) :
    bitsToNatLSB (natToBitsLSB ℓ val) = val := by
  induction ℓ generalizing val with
  | zero =>
    simp only [pow_zero] at h
    have : val = 0 := by omega
    subst this
    simp [bitsToNatLSB]
  | succ ℓ ih =>
    simp only [bitsToNatLSB, natToBitsLSB, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    have hmod_lt : val % 2 ^ ℓ < 2 ^ ℓ := Nat.mod_lt val (Nat.two_pow_pos ℓ)
    have hih := ih hmod_lt
    have hleft : (∑ i : Fin ℓ, if natToBitsLSB (ℓ + 1) val i.castSucc then 2 ^ i.val else 0) = val % 2 ^ ℓ := by
      rw [← hih]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : i.val < ℓ := i.isLt
      have htb : val.testBit i.val = (val % 2 ^ ℓ).testBit i.val := by
        rw [Nat.testBit_mod_two_pow]
        simp [hi]
      simp only [natToBitsLSB, Fin.val_castSucc]
      by_cases hc : val.testBit i.val <;> simp [hc, htb.symm]
    change (∑ i : Fin ℓ, if natToBitsLSB (ℓ + 1) val i.castSucc then 2 ^ i.val else 0) +
      (if val.testBit ℓ then 2 ^ ℓ else 0) = val
    rw [hleft]
    have hdiv_lt : val / 2 ^ ℓ < 2 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos ℓ)]
      simpa [pow_succ'] using h
    have hbit : val.testBit ℓ = decide (val / 2 ^ ℓ = 1) := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have : (val / 2 ^ ℓ) % 2 = val / 2 ^ ℓ := Nat.mod_eq_of_lt hdiv_lt
      rw [this]
    rw [hbit]
    have hdecomp := (Nat.div_add_mod val (2 ^ ℓ)).symm
    by_cases h0 : val / 2 ^ ℓ = 0
    · simp only [h0, zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte, add_zero]
      rw [h0, mul_zero, zero_add] at hdecomp
      exact hdecomp.symm
    · have h1 : val / 2 ^ ℓ = 1 :=
        Nat.le_antisymm (Nat.lt_succ_iff.mp hdiv_lt) (Nat.pos_of_ne_zero h0)
      simp only [h1, decide_true, ↓reduceIte]
      rw [h1, mul_one] at hdecomp
      linarith [hdecomp]

lemma natToBitsLSB_inj {ℓ a b : ℕ} (ha : a < 2 ^ ℓ) (hb : b < 2 ^ ℓ)
    (h : natToBitsLSB ℓ a = natToBitsLSB ℓ b) : a = b := by
  have := congrArg bitsToNatLSB h
  rwa [bitsToNatLSB_natToBitsLSB ha, bitsToNatLSB_natToBitsLSB hb] at this

/-! ### 2. `OracleCircuit` & `nonOracleDepth` Composition Lemmas -/

def stepWires {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ} :
    OracleStep S a m → Finset (Fin m)
  | .gate g => Finset.univ.image g.wires
  | .query _ _ ctl wires _ =>
      Finset.univ.image wires ∪ (match ctl with | none => ∅ | some c => {c})

def stepCost {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ} : OracleStep S a m → ℕ
  | .gate _ => 1
  | .query _ _ _ _ _ => 0

def stepTime {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (st : OracleStep S a m) (τ : Fin m → ℕ) : Fin m → ℕ :=
  let t := (stepWires st).sup τ + stepCost st
  fun j => if j ∈ stepWires st then t else τ j

def foldTimes {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c : OracleCircuit S a m) (τ₀ : Fin m → ℕ) : Fin m → ℕ :=
  c.foldl (fun τ st => stepTime st τ) τ₀

lemma nonOracleDepth_eq_sup_foldTimes {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c : OracleCircuit S a m) :
    nonOracleDepth c = Finset.univ.sup (foldTimes c (fun _ => 0)) := rfl

lemma foldTimes_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c1 c2 : OracleCircuit S a m) (τ₀ : Fin m → ℕ) :
    foldTimes (c1 ++ c2) τ₀ = foldTimes c2 (foldTimes c1 τ₀) := by
  simp [foldTimes, List.foldl_append]

lemma stepTime_mono {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (st : OracleStep S a m) {τ₁ τ₂ : Fin m → ℕ} (h : ∀ j, τ₁ j ≤ τ₂ j) :
    ∀ j, stepTime st τ₁ j ≤ stepTime st τ₂ j := by
  intro j
  simp only [stepTime]
  split_ifs
  · exact Nat.add_le_add_right (Finset.sup_mono_fun fun i _ => h i) _
  · exact h j

lemma stepTime_add_const {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (st : OracleStep S a m) (τ : Fin m → ℕ) (B : ℕ) :
    ∀ j, stepTime st (fun i => τ i + B) j ≤ stepTime st τ j + B := by
  intro j
  simp only [stepTime]
  split_ifs
  · have hsup : (stepWires st).sup (fun i => τ i + B) ≤ (stepWires st).sup τ + B := by
      apply Finset.sup_le
      intro i hi
      exact Nat.add_le_add_right (Finset.le_sup hi) B
    omega
  · exact le_rfl

lemma foldTimes_le_add {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c : OracleCircuit S a m) {τ₀ τ₁ : Fin m → ℕ} {B : ℕ}
    (h : ∀ j, τ₀ j ≤ τ₁ j + B) :
    ∀ j, foldTimes c τ₀ j ≤ foldTimes c τ₁ j + B := by
  induction c generalizing τ₀ τ₁ with
  | nil => exact h
  | cons st rest ih =>
    intro j
    simp only [foldTimes, List.foldl_cons]
    apply ih
    intro k
    calc stepTime st τ₀ k
        ≤ stepTime st (fun i => τ₁ i + B) k := stepTime_mono st h k
      _ ≤ stepTime st τ₁ k + B := stepTime_add_const st τ₁ B k

theorem nonOracleDepth_nil {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ} :
    nonOracleDepth ([] : OracleCircuit S a m) = 0 := by
  simp [nonOracleDepth]

theorem nonOracleDepth_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c1 c2 : OracleCircuit S a m) :
    nonOracleDepth (c1 ++ c2) ≤ nonOracleDepth c1 + nonOracleDepth c2 := by
  rw [nonOracleDepth_eq_sup_foldTimes, foldTimes_append]
  apply Finset.sup_le
  intro j _
  have hstart : ∀ i : Fin m, foldTimes c1 (fun _ => 0) i ≤ (fun _ => 0) i + nonOracleDepth c1 := by
    intro i
    rw [zero_add, nonOracleDepth_eq_sup_foldTimes]
    exact Finset.le_sup (Finset.mem_univ i)
  have hle := foldTimes_le_add c2 hstart j
  have hc2 : foldTimes c2 (fun _ => 0) j ≤ nonOracleDepth c2 := by
    rw [nonOracleDepth_eq_sup_foldTimes]
    exact Finset.le_sup (Finset.mem_univ j)
  omega

theorem nonOracleDepth_query_single {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (k : Fin r) (adj : Bool) (ctl : Option (Fin m)) (wires : Fin (a k) ↪ Fin m)
    (hc : ∀ c, ctl = some c → c ∉ Set.range wires) :
    nonOracleDepth ([OracleStep.query k adj ctl wires hc] : OracleCircuit S a m) = 0 := by
  simp [nonOracleDepth]

theorem nonOracleDepth_append_query {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c : OracleCircuit S a m) (k : Fin r) (adj : Bool) (ctl : Option (Fin m))
    (wires : Fin (a k) ↪ Fin m) (hc : ∀ c, ctl = some c → c ∉ Set.range wires) :
    nonOracleDepth (c ++ [OracleStep.query k adj ctl wires hc]) ≤ nonOracleDepth c := by
  calc nonOracleDepth (c ++ [OracleStep.query k adj ctl wires hc])
      ≤ nonOracleDepth c + nonOracleDepth [OracleStep.query k adj ctl wires hc] :=
        nonOracleDepth_append _ _
    _ = nonOracleDepth c := by rw [nonOracleDepth_query_single, add_zero]

def LayerDisjoint {S : Set Gate} {m : ℕ} (L : List (GateApp S m)) : Prop :=
  L.Pairwise fun g h => Disjoint (Set.range g.wires) (Set.range h.wires)

private lemma foldTimes_parallelLayer_le {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (L : List (GateApp S m)) (hL : LayerDisjoint L) (τ : Fin m → ℕ) (B : ℕ)
    (hτ : ∀ j, τ j ≤ B + 1)
    (hLτ : ∀ g ∈ L, ∀ j ∈ Finset.univ.image g.wires, τ j ≤ B) :
    ∀ j, foldTimes (L.map (OracleStep.gate (r := r) (a := a))) τ j ≤ B + 1 := by
  induction L generalizing τ with
  | nil => exact hτ
  | cons g rest ih =>
    rw [List.map_cons]
    simp only [foldTimes, List.foldl_cons]
    rw [LayerDisjoint, List.pairwise_cons] at hL
    apply ih hL.2
    · intro j
      by_cases hj : j ∈ Finset.univ.image g.wires
      · have hsup : (Finset.univ.image g.wires).sup τ ≤ B :=
          Finset.sup_le fun i hi => hLτ g List.mem_cons_self i hi
        simp only [stepTime, stepWires, stepCost, hj, ↓reduceIte]
        omega
      · simp only [stepTime, stepWires, hj, ↓reduceIte]
        exact hτ j
    · intro h hmem j hj
      have hdisj := hL.1 h hmem
      have hj_not : j ∉ Finset.univ.image g.wires := by
        intro hjg
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hj hjg
        rcases hj with ⟨a1, rfl⟩
        rcases hjg with ⟨a2, ha2⟩
        exact Set.disjoint_left.mp hdisj ⟨a2, ha2⟩ ⟨a1, rfl⟩
      simp only [stepTime, stepWires, hj_not, ↓reduceIte]
      exact hLτ h (List.mem_cons_of_mem g hmem) j hj

theorem nonOracleDepth_parallelLayer {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (L : List (GateApp S m)) (hL : LayerDisjoint L) :
    nonOracleDepth (L.map (OracleStep.gate (r := r) (a := a))) ≤ 1 := by
  rw [nonOracleDepth_eq_sup_foldTimes]
  apply Finset.sup_le
  intro j _
  exact foldTimes_parallelLayer_le L hL (fun _ => 0) 0 (fun _ => Nat.le_add_left _ _)
    (fun _ _ _ _ => Nat.zero_le _) j

/-! ### 3. Circuit & OracleCircuit Algebraic Helpers -/

lemma circuit_unitary_nil {S : Set Gate} {n : ℕ} :
    Circuit.unitary ([] : Circuit S n) = 1 := by
  simp [Circuit.unitary]

lemma circuit_unitary_cons {S : Set Gate} {n : ℕ} (g : GateApp S n) (c : Circuit S n) :
    Circuit.unitary (g :: c) = Circuit.unitary c * embedOp g.gate.mat g.wires := by
  simp [Circuit.unitary]

lemma circuit_unitary_append {S : Set Gate} {n : ℕ} (c1 c2 : Circuit S n) :
    Circuit.unitary (c1 ++ c2) = Circuit.unitary c2 * Circuit.unitary c1 := by
  simp [Circuit.unitary]

lemma oracleCircuit_unitary_nil {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    OracleCircuit.unitary ([] : OracleCircuit S a n) orc = 1 := by
  simp [OracleCircuit.unitary]

lemma oracleCircuit_unitary_cons {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (st : OracleStep S a n) (c : OracleCircuit S a n)
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    OracleCircuit.unitary (st :: c) orc = OracleCircuit.unitary c orc * OracleStep.mat orc st := by
  simp [OracleCircuit.unitary]

lemma oracleCircuit_unitary_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c1 c2 : OracleCircuit S a n) (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    OracleCircuit.unitary (c1 ++ c2) orc =
      OracleCircuit.unitary c2 orc * OracleCircuit.unitary c1 orc := by
  simp [OracleCircuit.unitary]

lemma oracleCircuit_queryCount_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c1 c2 : OracleCircuit S a n) (k : Fin r) :
    (c1 ++ c2).queryCount k = c1.queryCount k + c2.queryCount k := by
  simp [OracleCircuit.queryCount, List.countP_append]

lemma oracleCircuit_gateCount_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c1 c2 : OracleCircuit S a n) :
    (c1 ++ c2).gateCount = c1.gateCount + c2.gateCount := by
  simp [OracleCircuit.gateCount, List.countP_append]

lemma oracleCircuit_map_gate_unitary {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c : Circuit S n) (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    OracleCircuit.unitary (c.map (OracleStep.gate (r := r) (a := a))) orc = c.unitary := by
  simp only [OracleCircuit.unitary, Circuit.unitary, List.map_map]
  rfl

lemma oracleCircuit_map_gate_queryCount {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c : Circuit S n) (k : Fin r) :
    OracleCircuit.queryCount (c.map (OracleStep.gate (r := r) (a := a))) k = 0 := by
  induction c with
  | nil => simp [OracleCircuit.queryCount]
  | cons g rest ih =>
    simp only [List.map_cons, OracleCircuit.queryCount, List.countP_cons, OracleStep.IsQueryTo,
      Bool.false_eq_true, ↓reduceIte, add_zero] at ih ⊢
    exact ih

lemma oracleCircuit_map_gate_gateCount {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c : Circuit S n) :
    OracleCircuit.gateCount (c.map (OracleStep.gate (r := r) (a := a))) = c.length := by
  induction c with
  | nil => simp [OracleCircuit.gateCount]
  | cons g rest ih =>
    simp only [List.map_cons, OracleCircuit.gateCount, List.countP_cons, List.length_cons] at ih ⊢
    exact congrArg (· + 1) ih

/-! ### 4. `embedOp` Algebra, Commutation & Action Helpers -/

lemma act_add {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (ψ φ : EuclideanSpace ℂ ι) :
    act U (ψ + φ) = act U ψ + act U φ := by
  ext y; simp [act, Matrix.mulVec_add]

lemma act_sub {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (ψ φ : EuclideanSpace ℂ ι) :
    act U (ψ - φ) = act U ψ - act U φ := by
  ext y; simp [act, Matrix.mulVec_sub]

lemma act_smul {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (c : ℂ) (ψ : EuclideanSpace ℂ ι) :
    act U (c • ψ) = c • act U ψ := by
  ext y; simp [act, Matrix.mulVec_smul]

lemma act_sum {ι κ : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (s : Finset κ)
    (f : κ → EuclideanSpace ℂ ι) :
    act U (∑ x ∈ s, f x) = ∑ x ∈ s, act U (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext y; simp [act]
  | insert a s ha ih => rw [Finset.sum_insert ha, act_add, ih, Finset.sum_insert ha]

lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    act (A * B) ψ = act A (act B ψ) := by
  ext y; simp [act, Matrix.mulVec_mulVec]

lemma act_one {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    act (1 : Matrix ι ι ℂ) ψ = ψ := by
  simp [act]

lemma act_ket_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (z : ι) :
    act M (ket z) = ∑ y : ι, M y z • ket y := by
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, ket, PiLp.single_apply,
    WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single z, Finset.sum_eq_single y]
  · simp
  · intro x _ hx; simp [hx.symm]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (Finset.mem_univ _) h

def permMat {ι : Type*} [DecidableEq ι] (f : ι → ι) : Matrix ι ι ℂ :=
  Matrix.of fun y z => if y = f z then 1 else 0

lemma act_permMat_ket {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ι) (z : ι) :
    act (permMat f) (ket z) = ket (f z) := by
  rw [act_ket_eq, Finset.sum_eq_single (f z)]
  · simp [permMat]
  · intro y _ hy; simp [permMat, hy]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma permMat_mem_unitaryGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → ι} (hf : Function.Bijective f) :
    permMat f ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext x y
  simp only [Matrix.mul_apply, Matrix.star_apply, permMat, Matrix.of_apply, Matrix.one_apply]
  obtain ⟨u, hu⟩ := hf.surjective x
  rw [Finset.sum_eq_single u]
  · by_cases hxy : x = y
    · subst hxy; simp [hu]
    · have hne : y ≠ f u := fun h => hxy (hu.symm.trans h.symm)
      simp [hu, hxy, ne_comm.mp hxy]
  · intro z _ hz
    have hzx : x ≠ f z := fun h => hz (hf.injective (h.symm.trans hu.symm))
    simp [hzx]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma embedOp_star {k n : ℕ} (A : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp (star A) w = star (embedOp A w) := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.star_apply]
  by_cases h : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · have h' : ∀ a : Fin n, a ∉ Set.range w → z a = y a := fun a ha => (h a ha).symm
    rw [if_pos h, if_pos h']
  · have h' : ¬ ∀ a : Fin n, a ∉ Set.range w → z a = y a := fun hzy =>
      h (fun a ha => (hzy a ha).symm)
    rw [if_neg h, if_neg h', star_zero]

private noncomputable def splitQubits {k n : ℕ} (w : Fin k ↪ Fin n) (y₀ : Qubits n) :
    Qubits k ↪ Qubits n where
  toFun v a :=
    open Classical in
    if h : ∃ i, w i = a then v (Classical.choose h) else y₀ a
  inj' v1 v2 hv := by
    classical
    funext i
    have hi := congrFun hv (w i)
    have hmem : ∃ j, w j = w i := ⟨i, rfl⟩
    change (if h : ∃ j, w j = w i then v1 (Classical.choose h) else y₀ (w i)) =
      (if h : ∃ j, w j = w i then v2 (Classical.choose h) else y₀ (w i)) at hi
    rw [dif_pos hmem, dif_pos hmem, w.injective (Classical.choose_spec hmem)] at hi
    exact hi

private lemma splitQubits_comp {k n : ℕ} (w : Fin k ↪ Fin n) (y₀ : Qubits n) (v : Qubits k) :
    splitQubits w y₀ v ∘ w = v := by
  classical
  funext i
  have hmem : ∃ j, w j = w i := ⟨i, rfl⟩
  change (if h : ∃ j, w j = w i then v (Classical.choose h) else y₀ (w i)) = v i
  rw [dif_pos hmem, w.injective (Classical.choose_spec hmem)]

private lemma splitQubits_off {k n : ℕ} (w : Fin k ↪ Fin n) (y₀ : Qubits n) (v : Qubits k)
    {a : Fin n} (ha : a ∉ Set.range w) :
    splitQubits w y₀ v a = y₀ a := by
  classical
  have hnot : ¬ ∃ i, w i = a := ha
  change (if h : ∃ i, w i = a then v (Classical.choose h) else y₀ a) = y₀ a
  rw [dif_neg hnot]

private lemma eq_splitQubits_of_agree {k n : ℕ} (w : Fin k ↪ Fin n) {y₀ x : Qubits n}
    (hx : ∀ a : Fin n, a ∉ Set.range w → y₀ a = x a) :
    x = splitQubits w y₀ (x ∘ w) := by
  classical
  funext a
  by_cases ha : a ∈ Set.range w
  · have hmem : ∃ i, w i = a := ha
    change x a = if h : ∃ i, w i = a then (x ∘ w) (Classical.choose h) else y₀ a
    rw [dif_pos hmem, Function.comp_apply, Classical.choose_spec hmem]
  · rw [splitQubits_off w y₀ _ ha, hx a ha]

lemma embedOp_mul {k n : ℕ} (A B : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp (A * B) w = embedOp A w * embedOp B w := by
  classical
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.mul_apply]
  by_cases hyz : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos hyz]
    have hsum : (∑ x : Qubits n,
        (if ∀ a, a ∉ Set.range w → y a = x a then A (y ∘ w) (x ∘ w) else 0) *
        (if ∀ a, a ∉ Set.range w → x a = z a then B (x ∘ w) (z ∘ w) else 0)) =
        ∑ x ∈ Finset.univ.image (splitQubits w y),
        (if ∀ a, a ∉ Set.range w → y a = x a then A (y ∘ w) (x ∘ w) else 0) *
        (if ∀ a, a ∉ Set.range w → x a = z a then B (x ∘ w) (z ∘ w) else 0) := by
      rw [← Finset.sum_subset (Finset.subset_univ _)]
      intro x _ hx
      by_cases hyx : ∀ a, a ∉ Set.range w → y a = x a
      · exfalso; apply hx
        rw [Finset.mem_image]
        exact ⟨x ∘ w, Finset.mem_univ _, (eq_splitQubits_of_agree w hyx).symm⟩
      · rw [if_neg hyx, zero_mul]
    rw [hsum, Finset.sum_image (fun v1 _ v2 _ h => (splitQubits w y).injective h)]
    refine Finset.sum_congr rfl fun v _ => ?_
    have h1 : ∀ a, a ∉ Set.range w → y a = splitQubits w y v a := fun a ha =>
      (splitQubits_off w y v ha).symm
    have h2 : ∀ a, a ∉ Set.range w → splitQubits w y v a = z a := fun a ha => by
      rw [splitQubits_off w y v ha, hyz a ha]
    rw [if_pos h1, if_pos h2, splitQubits_comp]
  · rw [if_neg hyz]
    symm
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases h1 : ∀ a, a ∉ Set.range w → y a = x a
    · have h2 : ¬ ∀ a, a ∉ Set.range w → x a = z a := fun hxz =>
        hyz fun a ha => (h1 a ha).trans (hxz a ha)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

lemma embedOp_mem_unitaryGroup {k n : ℕ} {A : Matrix (Qubits k) (Qubits k) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp A w ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, ← embedOp_star, ← embedOp_mul,
    Matrix.mem_unitaryGroup_iff.mp hA, embedOp_one]

lemma embedOp_embedOp {k m n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (w₁ : Fin k ↪ Fin m) (w₂ : Fin m ↪ Fin n) :
    embedOp (embedOp M w₁) w₂ = embedOp M (w₁.trans w₂) := by
  ext y z
  simp only [embedOp, Matrix.of_apply]
  have hiff : (∀ a : Fin n, a ∉ Set.range (w₁.trans w₂) → y a = z a) ↔
      (∀ a : Fin n, a ∉ Set.range w₂ → y a = z a) ∧
      (∀ b : Fin m, b ∉ Set.range w₁ → (y ∘ w₂) b = (z ∘ w₂) b) := by
    constructor
    · intro h
      refine ⟨fun a ha => h a ?_, fun b hb => h (w₂ b) ?_⟩
      · rintro ⟨i, rfl⟩; exact ha ⟨w₁ i, rfl⟩
      · rintro ⟨i, hi⟩; exact hb ⟨i, w₂.injective hi⟩
    · rintro ⟨h2, h1⟩ a ha
      by_cases ha2 : a ∈ Set.range w₂
      · rcases ha2 with ⟨b, rfl⟩
        apply h1 b
        rintro ⟨i, rfl⟩
        exact ha ⟨i, rfl⟩
      · exact h2 a ha2
  by_cases hall : ∀ a : Fin n, a ∉ Set.range (w₁.trans w₂) → y a = z a
  · rw [if_pos hall]
    obtain ⟨h2, h1⟩ := hiff.mp hall
    rw [if_pos h2, if_pos h1]
    rfl
  · rw [if_neg hall]
    by_cases h2 : ∀ a : Fin n, a ∉ Set.range w₂ → y a = z a
    · rw [if_pos h2]
      have h1 : ¬ ∀ b : Fin m, b ∉ Set.range w₁ → (y ∘ w₂) b = (z ∘ w₂) b := fun h1 =>
        hall (hiff.mpr ⟨h2, h1⟩)
      rw [if_neg h1]
    · rw [if_neg h2]

lemma embedOp_comm_of_disjoint {k₁ k₂ n : ℕ}
    (A : Matrix (Qubits k₁) (Qubits k₁) ℂ) (B : Matrix (Qubits k₂) (Qubits k₂) ℂ)
    (w₁ : Fin k₁ ↪ Fin n) (w₂ : Fin k₂ ↪ Fin n)
    (hdisj : Disjoint (Set.range w₁) (Set.range w₂)) :
    embedOp A w₁ * embedOp B w₂ = embedOp B w₂ * embedOp A w₁ := by
  classical
  ext y z
  simp only [Matrix.mul_apply, embedOp, Matrix.of_apply]
  by_cases hout : ∀ a : Fin n, a ∉ Set.range w₁ → a ∉ Set.range w₂ → y a = z a
  · let x₁ : Qubits n := fun a => if a ∈ Set.range w₁ then z a else y a
    let x₂ : Qubits n := fun a => if a ∈ Set.range w₂ then z a else y a
    have hx₁_w1 : x₁ ∘ w₁ = z ∘ w₁ := by
      funext i
      change (if w₁ i ∈ Set.range w₁ then z (w₁ i) else y (w₁ i)) = z (w₁ i)
      rw [if_pos ⟨i, rfl⟩]
    have hx₁_w2 : x₁ ∘ w₂ = y ∘ w₂ := by
      funext i
      have hnot : w₂ i ∉ Set.range w₁ := Set.disjoint_right.mp hdisj ⟨i, rfl⟩
      change (if w₂ i ∈ Set.range w₁ then z (w₂ i) else y (w₂ i)) = y (w₂ i)
      rw [if_neg hnot]
    have hx₂_w2 : x₂ ∘ w₂ = z ∘ w₂ := by
      funext i
      change (if w₂ i ∈ Set.range w₂ then z (w₂ i) else y (w₂ i)) = z (w₂ i)
      rw [if_pos ⟨i, rfl⟩]
    have hx₂_w1 : x₂ ∘ w₁ = y ∘ w₁ := by
      funext i
      have hnot : w₁ i ∉ Set.range w₂ := Set.disjoint_left.mp hdisj ⟨i, rfl⟩
      change (if w₁ i ∈ Set.range w₂ then z (w₁ i) else y (w₁ i)) = y (w₁ i)
      rw [if_neg hnot]
    have hL : (∑ x : Qubits n,
        (if ∀ a, a ∉ Set.range w₁ → y a = x a then A (y ∘ w₁) (x ∘ w₁) else 0) *
        (if ∀ a, a ∉ Set.range w₂ → x a = z a then B (x ∘ w₂) (z ∘ w₂) else 0)) =
        A (y ∘ w₁) (z ∘ w₁) * B (y ∘ w₂) (z ∘ w₂) := by
      rw [Finset.sum_eq_single x₁]
      · have h1 : ∀ a, a ∉ Set.range w₁ → y a = x₁ a := fun a ha => by
          change y a = if a ∈ Set.range w₁ then z a else y a
          rw [if_neg ha]
        have h2 : ∀ a, a ∉ Set.range w₂ → x₁ a = z a := fun a ha => by
          by_cases ha1 : a ∈ Set.range w₁
          · change (if a ∈ Set.range w₁ then z a else y a) = z a
            rw [if_pos ha1]
          · change (if a ∈ Set.range w₁ then z a else y a) = z a
            rw [if_neg ha1, hout a ha1 ha]
        rw [if_pos h1, if_pos h2, hx₁_w1, hx₁_w2]
      · intro x _ hx
        by_cases h1 : ∀ a, a ∉ Set.range w₁ → y a = x a
        · by_cases h2 : ∀ a, a ∉ Set.range w₂ → x a = z a
          · exfalso; apply hx
            funext a
            by_cases ha1 : a ∈ Set.range w₁
            · have ha2 : a ∉ Set.range w₂ := Set.disjoint_left.mp hdisj ha1
              change x a = if a ∈ Set.range w₁ then z a else y a
              rw [if_pos ha1, h2 a ha2]
            · change x a = if a ∈ Set.range w₁ then z a else y a
              rw [if_neg ha1, (h1 a ha1).symm]
          · rw [if_neg h2, mul_zero]
        · rw [if_neg h1, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR : (∑ x : Qubits n,
        (if ∀ a, a ∉ Set.range w₂ → y a = x a then B (y ∘ w₂) (x ∘ w₂) else 0) *
        (if ∀ a, a ∉ Set.range w₁ → x a = z a then A (x ∘ w₁) (z ∘ w₁) else 0)) =
        B (y ∘ w₂) (z ∘ w₂) * A (y ∘ w₁) (z ∘ w₁) := by
      rw [Finset.sum_eq_single x₂]
      · have h1 : ∀ a, a ∉ Set.range w₂ → y a = x₂ a := fun a ha => by
          change y a = if a ∈ Set.range w₂ then z a else y a
          rw [if_neg ha]
        have h2 : ∀ a, a ∉ Set.range w₁ → x₂ a = z a := fun a ha => by
          by_cases ha2 : a ∈ Set.range w₂
          · change (if a ∈ Set.range w₂ then z a else y a) = z a
            rw [if_pos ha2]
          · change (if a ∈ Set.range w₂ then z a else y a) = z a
            rw [if_neg ha2, hout a ha ha2]
        rw [if_pos h1, if_pos h2, hx₂_w2, hx₂_w1]
      · intro x _ hx
        by_cases h1 : ∀ a, a ∉ Set.range w₂ → y a = x a
        · by_cases h2 : ∀ a, a ∉ Set.range w₁ → x a = z a
          · exfalso; apply hx
            funext a
            by_cases ha2 : a ∈ Set.range w₂
            · have ha1 : a ∉ Set.range w₁ := Set.disjoint_right.mp hdisj ha2
              change x a = if a ∈ Set.range w₂ then z a else y a
              rw [if_pos ha2, h2 a ha1]
            · change x a = if a ∈ Set.range w₂ then z a else y a
              rw [if_neg ha2, (h1 a ha2).symm]
          · rw [if_neg h2, mul_zero]
        · rw [if_neg h1, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hL, hR, mul_comm]
  · push Not at hout
    rcases hout with ⟨a₀, ha1, ha2, hne⟩
    have hzero1 : (∑ x : Qubits n,
        (if ∀ a, a ∉ Set.range w₁ → y a = x a then A (y ∘ w₁) (x ∘ w₁) else 0) *
        (if ∀ a, a ∉ Set.range w₂ → x a = z a then B (x ∘ w₂) (z ∘ w₂) else 0)) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases h1 : ∀ a, a ∉ Set.range w₁ → y a = x a
      · have h2 : ¬ ∀ a, a ∉ Set.range w₂ → x a = z a := fun hxz =>
          hne ((h1 a₀ ha1).trans (hxz a₀ ha2))
        rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    have hzero2 : (∑ x : Qubits n,
        (if ∀ a, a ∉ Set.range w₂ → y a = x a then B (y ∘ w₂) (x ∘ w₂) else 0) *
        (if ∀ a, a ∉ Set.range w₁ → x a = z a then A (x ∘ w₁) (z ∘ w₁) else 0)) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases h1 : ∀ a, a ∉ Set.range w₂ → y a = x a
      · have h2 : ¬ ∀ a, a ∉ Set.range w₁ → x a = z a := fun hxz =>
          hne ((h1 a₀ ha2).trans (hxz a₀ ha1))
        rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    rw [hzero1, hzero2]

/-! ### 5. `LayeredCircuit` & `ImplementsOnClean` -/

def GateApp.adj {m : ℕ} (g : GateApp gates12 m) : GateApp gates12 m where
  gate := ⟨g.gate.arity, star g.gate.mat⟩
  mem := by
    rcases g.mem with ⟨hu, h1, h2⟩
    refine ⟨?_, h1, h2⟩
    exact Unitary.star_mem hu
  wires := g.wires

def GateApp.mapWires {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (g : GateApp gates12 m₀) :
    GateApp gates12 m where
  gate := g.gate
  mem := g.mem
  wires := g.wires.trans emb

lemma GateApp.unitary_mem_unitaryGroup {m : ℕ} (g : GateApp gates12 m) :
    embedOp g.gate.mat g.wires ∈ Matrix.unitaryGroup (Qubits m) ℂ :=
  embedOp_mem_unitaryGroup g.mem.1 g.wires

lemma circuit_unitary_mem_unitaryGroup {m : ℕ} (c : Circuit gates12 m) :
    c.unitary ∈ Matrix.unitaryGroup (Qubits m) ℂ := by
  induction c with
  | nil =>
    rw [circuit_unitary_nil]
    exact one_mem _
  | cons g rest ih =>
    rw [circuit_unitary_cons]
    exact mul_mem ih (GateApp.unitary_mem_unitaryGroup g)

structure LayeredCircuit (m : ℕ) where
  layers : List (List (GateApp gates12 m))
  disjoint : ∀ L ∈ layers, LayerDisjoint L

namespace LayeredCircuit

def toCircuit {m : ℕ} (lc : LayeredCircuit m) : Circuit gates12 m :=
  lc.layers.flatten

def size {m : ℕ} (lc : LayeredCircuit m) : ℕ :=
  lc.toCircuit.length

def depth {m : ℕ} (lc : LayeredCircuit m) : ℕ :=
  lc.layers.length

noncomputable def unitary {m : ℕ} (lc : LayeredCircuit m) : Matrix (Qubits m) (Qubits m) ℂ :=
  lc.toCircuit.unitary

def UsesOnly {m : ℕ} (lc : LayeredCircuit m) (S : Finset (Fin m)) : Prop :=
  ∀ L ∈ lc.layers, ∀ g ∈ L, ∀ i : Fin g.gate.arity, g.wires i ∈ S

lemma UsesOnly.mono {m : ℕ} {lc : LayeredCircuit m} {S₁ S₂ : Finset (Fin m)}
    (h : lc.UsesOnly S₁) (hsub : S₁ ⊆ S₂) : lc.UsesOnly S₂ :=
  fun L hL g hg i => hsub (h L hL g hg i)

lemma unitary_mem_unitaryGroup {m : ℕ} (lc : LayeredCircuit m) :
    lc.unitary ∈ Matrix.unitaryGroup (Qubits m) ℂ :=
  circuit_unitary_mem_unitaryGroup lc.toCircuit

lemma nonOracleDepth_le {r : ℕ} {a : Fin r → ℕ} {m : ℕ} (lc : LayeredCircuit m) :
    nonOracleDepth (lc.toCircuit.map (OracleStep.gate (r := r) (a := a))) ≤ lc.depth := by
  rcases lc with ⟨layers, hdisj⟩
  dsimp only [toCircuit, depth]
  induction layers with
  | nil => simp [nonOracleDepth_nil]
  | cons L rest ih =>
    simp only [List.flatten_cons, List.map_append, List.length_cons]
    have hL : nonOracleDepth (L.map (OracleStep.gate (r := r) (a := a))) ≤ 1 :=
      nonOracleDepth_parallelLayer L (hdisj L List.mem_cons_self)
    have hrest : nonOracleDepth (rest.flatten.map (OracleStep.gate (r := r) (a := a))) ≤ rest.length :=
      ih fun L' hL' => hdisj L' (List.mem_cons_of_mem L hL')
    calc nonOracleDepth (L.map OracleStep.gate ++ rest.flatten.map OracleStep.gate)
        ≤ nonOracleDepth (L.map OracleStep.gate) + nonOracleDepth (rest.flatten.map OracleStep.gate) :=
          nonOracleDepth_append _ _
      _ ≤ 1 + rest.length := Nat.add_le_add hL hrest
      _ = rest.length + 1 := Nat.add_comm _ _

def id (m : ℕ) : LayeredCircuit m where
  layers := []
  disjoint _ h := by contradiction

@[simp] lemma id_size {m : ℕ} : (id m).size = 0 := rfl
@[simp] lemma id_depth {m : ℕ} : (id m).depth = 0 := rfl
@[simp] lemma id_unitary {m : ℕ} : (id m).unitary = 1 := by
  simp [unitary, toCircuit, id, Circuit.unitary]
lemma id_usesOnly {m : ℕ} (S : Finset (Fin m)) : (id m).UsesOnly S := by
  intro L h; cases h

def single {m : ℕ} (g : GateApp gates12 m) : LayeredCircuit m where
  layers := [[g]]
  disjoint L h := by
    simp only [List.mem_singleton] at h
    subst h
    simp [LayerDisjoint]

@[simp] lemma single_size {m : ℕ} (g : GateApp gates12 m) : (single g).size = 1 := rfl
@[simp] lemma single_depth {m : ℕ} (g : GateApp gates12 m) : (single g).depth = 1 := rfl
@[simp] lemma single_unitary {m : ℕ} (g : GateApp gates12 m) :
    (single g).unitary = embedOp g.gate.mat g.wires := by
  simp [unitary, toCircuit, single, Circuit.unitary]
lemma single_usesOnly {m : ℕ} (g : GateApp gates12 m) {S : Finset (Fin m)}
    (h : ∀ i, g.wires i ∈ S) : (single g).UsesOnly S := by
  intro L hL g' hg'
  simp only [single, List.mem_singleton] at hL hg'
  subst hL
  rw [List.mem_singleton] at hg'
  subst hg'
  exact h

def ofLayer {m : ℕ} (L : List (GateApp gates12 m)) (hL : LayerDisjoint L) : LayeredCircuit m where
  layers := if L.isEmpty then [] else [L]
  disjoint L' hL' := by
    split_ifs at hL'
    · cases hL'
    · simp only [List.mem_singleton] at hL'
      subst hL'
      exact hL

lemma ofLayer_size {m : ℕ} (L : List (GateApp gates12 m)) (hL : LayerDisjoint L) :
    (ofLayer L hL).size = L.length := by
  dsimp [ofLayer, size, toCircuit]
  split_ifs with h
  · rw [List.isEmpty_iff] at h; subst h; rfl
  · simp

lemma ofLayer_depth {m : ℕ} (L : List (GateApp gates12 m)) (hL : LayerDisjoint L) :
    (ofLayer L hL).depth ≤ 1 := by
  dsimp [ofLayer, depth]
  split_ifs <;> simp

lemma ofLayer_unitary {m : ℕ} (L : List (GateApp gates12 m)) (hL : LayerDisjoint L) :
    (ofLayer L hL).unitary = Circuit.unitary L := by
  dsimp [ofLayer, unitary, toCircuit]
  split_ifs with h
  · rw [List.isEmpty_iff] at h; subst h; simp [Circuit.unitary]
  · simp [Circuit.unitary]

lemma ofLayer_usesOnly {m : ℕ} (L : List (GateApp gates12 m)) (hL : LayerDisjoint L)
    {S : Finset (Fin m)} (h : ∀ g ∈ L, ∀ i, g.wires i ∈ S) : (ofLayer L hL).UsesOnly S := by
  intro L' hL'
  dsimp [ofLayer] at hL'
  split_ifs at hL'
  · cases hL'
  · simp only [List.mem_singleton] at hL'
    subst hL'
    exact h

def seq {m : ℕ} (lc1 lc2 : LayeredCircuit m) : LayeredCircuit m where
  layers := lc1.layers ++ lc2.layers
  disjoint L hL := by
    rcases List.mem_append.mp hL with h1 | h2
    · exact lc1.disjoint L h1
    · exact lc2.disjoint L h2

@[simp] lemma seq_size {m : ℕ} (lc1 lc2 : LayeredCircuit m) :
    (lc1.seq lc2).size = lc1.size + lc2.size := by
  simp [seq, size, toCircuit]

@[simp] lemma seq_depth {m : ℕ} (lc1 lc2 : LayeredCircuit m) :
    (lc1.seq lc2).depth = lc1.depth + lc2.depth := by
  simp [seq, depth]

@[simp] lemma seq_unitary {m : ℕ} (lc1 lc2 : LayeredCircuit m) :
    (lc1.seq lc2).unitary = lc2.unitary * lc1.unitary := by
  simp [seq, unitary, toCircuit, circuit_unitary_append]

lemma seq_usesOnly {m : ℕ} {lc1 lc2 : LayeredCircuit m} {S : Finset (Fin m)}
    (h1 : lc1.UsesOnly S) (h2 : lc2.UsesOnly S) : (lc1.seq lc2).UsesOnly S := by
  intro L hL
  rcases List.mem_append.mp hL with hL1 | hL2
  · exact h1 L hL1
  · exact h2 L hL2

def seqList {m : ℕ} : List (LayeredCircuit m) → LayeredCircuit m
  | [] => id m
  | lc :: rest => lc.seq (seqList rest)

lemma seqList_size {m : ℕ} (lcs : List (LayeredCircuit m)) :
    (seqList lcs).size = (lcs.map size).sum := by
  induction lcs with
  | nil => simp [seqList]
  | cons lc rest ih => simp [seqList, ih]

lemma seqList_depth {m : ℕ} (lcs : List (LayeredCircuit m)) :
    (seqList lcs).depth = (lcs.map depth).sum := by
  induction lcs with
  | nil => simp [seqList]
  | cons lc rest ih => simp [seqList, ih]

lemma seqList_unitary {m : ℕ} (lcs : List (LayeredCircuit m)) :
    (seqList lcs).unitary = (lcs.map unitary).reverse.prod := by
  induction lcs with
  | nil => simp [seqList]
  | cons lc rest ih => simp [seqList, ih]

lemma seqList_usesOnly {m : ℕ} {lcs : List (LayeredCircuit m)} {S : Finset (Fin m)}
    (h : ∀ lc ∈ lcs, lc.UsesOnly S) : (seqList lcs).UsesOnly S := by
  induction lcs with
  | nil => exact id_usesOnly S
  | cons lc rest ih =>
    exact seq_usesOnly (h lc List.mem_cons_self) (ih fun lc' hlc' => h lc' (List.mem_cons_of_mem _ hlc'))

def mapWires {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (lc : LayeredCircuit m₀) : LayeredCircuit m where
  layers := lc.layers.map (List.map (GateApp.mapWires emb))
  disjoint L hL := by
    simp only [List.mem_map] at hL
    rcases hL with ⟨L₀, hL₀, rfl⟩
    have hdisj := lc.disjoint L₀ hL₀
    dsimp only [LayerDisjoint] at hdisj ⊢
    rw [List.pairwise_map]
    refine hdisj.imp fun {g1 g2} h => ?_
    rw [Set.disjoint_left]
    rintro x ⟨i1, hi1⟩ ⟨i2, hi2⟩
    change emb (g1.wires i1) = x at hi1
    change emb (g2.wires i2) = x at hi2
    have hweq : g1.wires i1 = g2.wires i2 := emb.injective (hi1.trans hi2.symm)
    exact Set.disjoint_left.mp h ⟨i1, rfl⟩ ⟨i2, hweq.symm⟩

@[simp] lemma mapWires_size {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (lc : LayeredCircuit m₀) :
    (lc.mapWires emb).size = lc.size := by
  simp only [mapWires, size, toCircuit, List.length_flatten, List.map_map, Function.comp_def,
    List.length_map]

@[simp] lemma mapWires_depth {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (lc : LayeredCircuit m₀) :
    (lc.mapWires emb).depth = lc.depth := by
  simp [mapWires, depth]

lemma mapWires_unitary {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (lc : LayeredCircuit m₀) :
    (lc.mapWires emb).unitary = embedOp lc.unitary emb := by
  rcases lc with ⟨layers, hdisj⟩
  dsimp only [mapWires, unitary, toCircuit]
  have hflat : (layers.map (List.map (GateApp.mapWires emb))).flatten =
      layers.flatten.map (GateApp.mapWires emb) := by
    induction layers with
    | nil => rfl
    | cons L rest ih => simp
  rw [hflat]
  generalize layers.flatten = c
  induction c with
  | nil => simp [Circuit.unitary, embedOp_one]
  | cons g rest ih =>
    simp only [List.map_cons, circuit_unitary_cons, ih]
    have hg : embedOp (GateApp.mapWires emb g).gate.mat (GateApp.mapWires emb g).wires =
        embedOp (embedOp g.gate.mat g.wires) emb :=
      (embedOp_embedOp g.gate.mat g.wires emb).symm
    rw [hg, ← embedOp_mul]

lemma mapWires_usesOnly {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (lc : LayeredCircuit m₀)
    {S₀ : Finset (Fin m₀)} (h : lc.UsesOnly S₀) :
    (lc.mapWires emb).UsesOnly (S₀.image emb) := by
  intro L hL g hg i
  simp only [mapWires, List.mem_map] at hL
  rcases hL with ⟨L₀, hL₀, rfl⟩
  simp only [List.mem_map] at hg
  rcases hg with ⟨g₀, hg₀, rfl⟩
  exact Finset.mem_image_of_mem emb (h L₀ hL₀ g₀ hg₀ i)

private lemma list_reverse_map_star_prod {α : Type*} [Monoid α] [StarMul α] (xs : List α) :
    star xs.reverse.prod = (xs.map star).prod := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
      star_mul, List.map_cons, ih]

def adj {m : ℕ} (lc : LayeredCircuit m) : LayeredCircuit m where
  layers := (lc.layers.reverse).map (fun L => (L.map GateApp.adj).reverse)
  disjoint L hL := by
    simp only [List.mem_map, List.mem_reverse] at hL
    rcases hL with ⟨L₀, hL₀, rfl⟩
    have hdisj := lc.disjoint L₀ hL₀
    dsimp only [LayerDisjoint] at hdisj ⊢
    rw [List.pairwise_reverse, List.pairwise_map]
    exact hdisj.imp fun h => h.symm

@[simp] lemma adj_size {m : ℕ} (lc : LayeredCircuit m) : lc.adj.size = lc.size := by
  simp only [adj, size, toCircuit]
  generalize lc.layers = layers
  induction layers with
  | nil => rfl
  | cons L rest ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.length_append, List.length_reverse, List.length_map] at ih ⊢
    omega

@[simp] lemma adj_depth {m : ℕ} (lc : LayeredCircuit m) : lc.adj.depth = lc.depth := by
  simp [adj, depth]

lemma adj_unitary {m : ℕ} (lc : LayeredCircuit m) : lc.adj.unitary = star lc.unitary := by
  dsimp only [adj, unitary, toCircuit]
  generalize lc.layers = layers
  have hflat : ((layers.reverse).map (fun L => (L.map GateApp.adj).reverse)).flatten =
      (layers.flatten.map GateApp.adj).reverse := by
    induction layers with
    | nil => rfl
    | cons L rest ih =>
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.map_append]
      rw [ih, List.reverse_append]
  rw [hflat]
  generalize layers.flatten = c
  simp only [Circuit.unitary, List.map_reverse, List.reverse_reverse, list_reverse_map_star_prod]
  congr 1
  induction c with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.map_cons]
    rw [ih, GateApp.adj, embedOp_star]

lemma adj_usesOnly {m : ℕ} {lc : LayeredCircuit m} {S : Finset (Fin m)}
    (h : lc.UsesOnly S) : lc.adj.UsesOnly S := by
  intro L hL g hg i
  simp only [adj, List.mem_map, List.mem_reverse] at hL
  rcases hL with ⟨L₀, hL₀, rfl⟩
  simp only [List.mem_reverse, List.mem_map] at hg
  rcases hg with ⟨g₀, hg₀, rfl⟩
  exact h L₀ hL₀ g₀ hg₀ i

/-! ### 6. Parallel Merge of Disjoint `LayeredCircuit`s -/

private lemma layerDisjoint_append {m : ℕ} {L1 L2 : List (GateApp gates12 m)}
    (h1 : LayerDisjoint L1) (h2 : LayerDisjoint L2)
    (h12 : ∀ g1 ∈ L1, ∀ g2 ∈ L2, Disjoint (Set.range g1.wires) (Set.range g2.wires)) :
    LayerDisjoint (L1 ++ L2) := by
  exact List.pairwise_append.mpr ⟨h1, h2, h12⟩

lemma circuit_comm_of_disjoint {m : ℕ} (c1 c2 : Circuit gates12 m)
    (h : ∀ g1 ∈ c1, ∀ g2 ∈ c2, Disjoint (Set.range g1.wires) (Set.range g2.wires)) :
    Circuit.unitary c1 * Circuit.unitary c2 = Circuit.unitary c2 * Circuit.unitary c1 := by
  induction c1 with
  | nil => simp [circuit_unitary_nil]
  | cons g1 rest1 ih =>
    rw [circuit_unitary_cons]
    have hrest : Circuit.unitary rest1 * Circuit.unitary c2 =
        Circuit.unitary c2 * Circuit.unitary rest1 :=
      ih fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b hb
    have hg1 : embedOp g1.gate.mat g1.wires * Circuit.unitary c2 =
        Circuit.unitary c2 * embedOp g1.gate.mat g1.wires := by
      have h1_c2 : ∀ g2 ∈ c2, Disjoint (Set.range g1.wires) (Set.range g2.wires) :=
        fun g2 hg2 => h g1 List.mem_cons_self g2 hg2
      clear ih hrest h
      induction c2 with
      | nil => simp [circuit_unitary_nil]
      | cons g2 rest2 ih2 =>
        rw [circuit_unitary_cons]
        have h12 := embedOp_comm_of_disjoint g1.gate.mat g2.gate.mat g1.wires g2.wires
          (h1_c2 g2 List.mem_cons_self)
        have h1r := ih2 fun b hb => h1_c2 b (List.mem_cons_of_mem g2 hb)
        calc embedOp g1.gate.mat g1.wires * (Circuit.unitary rest2 * embedOp g2.gate.mat g2.wires)
            = (embedOp g1.gate.mat g1.wires * Circuit.unitary rest2) *
                embedOp g2.gate.mat g2.wires := by rw [Matrix.mul_assoc]
          _ = (Circuit.unitary rest2 * embedOp g1.gate.mat g1.wires) *
                embedOp g2.gate.mat g2.wires := by rw [h1r]
          _ = Circuit.unitary rest2 *
                (embedOp g1.gate.mat g1.wires * embedOp g2.gate.mat g2.wires) := by
              rw [Matrix.mul_assoc]
          _ = Circuit.unitary rest2 *
                (embedOp g2.gate.mat g2.wires * embedOp g1.gate.mat g1.wires) := by rw [h12]
          _ = (Circuit.unitary rest2 * embedOp g2.gate.mat g2.wires) *
                embedOp g1.gate.mat g1.wires := by rw [Matrix.mul_assoc]
    calc (Circuit.unitary rest1 * embedOp g1.gate.mat g1.wires) * Circuit.unitary c2
        = Circuit.unitary rest1 * (embedOp g1.gate.mat g1.wires * Circuit.unitary c2) :=
          Matrix.mul_assoc _ _ _
      _ = Circuit.unitary rest1 * (Circuit.unitary c2 * embedOp g1.gate.mat g1.wires) := by
          rw [hg1]
      _ = (Circuit.unitary rest1 * Circuit.unitary c2) * embedOp g1.gate.mat g1.wires :=
          (Matrix.mul_assoc _ _ _).symm
      _ = (Circuit.unitary c2 * Circuit.unitary rest1) * embedOp g1.gate.mat g1.wires := by
          rw [hrest]
      _ = Circuit.unitary c2 * (Circuit.unitary rest1 * embedOp g1.gate.mat g1.wires) :=
          Matrix.mul_assoc _ _ _

private def zipLayers {m : ℕ} :
    List (List (GateApp gates12 m)) → List (List (GateApp gates12 m)) →
      List (List (GateApp gates12 m))
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x ++ y) :: zipLayers xs ys

private lemma zipLayers_length {m : ℕ}
    (xs ys : List (List (GateApp gates12 m))) :
    (zipLayers xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [zipLayers]
  | cons x xs ih =>
    cases ys with
    | nil => simp [zipLayers]
    | cons y ys => simp [zipLayers, ih, Nat.succ_max_succ]

private lemma zipLayers_flatten_length {m : ℕ}
    (xs ys : List (List (GateApp gates12 m))) :
    (zipLayers xs ys).flatten.length = xs.flatten.length + ys.flatten.length := by
  induction xs generalizing ys with
  | nil => simp [zipLayers]
  | cons x xs ih =>
    cases ys with
    | nil => simp [zipLayers]
    | cons y ys =>
      simp only [zipLayers, List.flatten_cons, List.length_append, ih]
      omega

private lemma zipLayers_mem {m : ℕ}
    {xs ys : List (List (GateApp gates12 m))} {L : List (GateApp gates12 m)}
    (hL : L ∈ zipLayers xs ys) :
    L ∈ xs ∨ L ∈ ys ∨ ∃ x ∈ xs, ∃ y ∈ ys, L = x ++ y := by
  induction xs generalizing ys with
  | nil => exact Or.inr (Or.inl hL)
  | cons x xs ih =>
    cases ys with
    | nil => exact Or.inl hL
    | cons y ys =>
      simp only [zipLayers, List.mem_cons] at hL
      rcases hL with rfl | hrest
      · exact Or.inr (Or.inr ⟨x, List.mem_cons_self, y, List.mem_cons_self, rfl⟩)
      · rcases ih hrest with h1 | h2 | ⟨x', hx', y', hy', rfl⟩
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h2))
        · exact Or.inr (Or.inr ⟨x', List.mem_cons_of_mem _ hx', y', List.mem_cons_of_mem _ hy', rfl⟩)

private lemma zipLayers_unitary {m : ℕ}
    (xs ys : List (List (GateApp gates12 m)))
    (hdisj : ∀ L1 ∈ xs, ∀ g1 ∈ L1, ∀ L2 ∈ ys, ∀ g2 ∈ L2,
      Disjoint (Set.range g1.wires) (Set.range g2.wires)) :
    Circuit.unitary (zipLayers xs ys).flatten =
      Circuit.unitary ys.flatten * Circuit.unitary xs.flatten := by
  induction xs generalizing ys with
  | nil => simp [zipLayers, circuit_unitary_nil]
  | cons x xs ih =>
    cases ys with
    | nil => simp [zipLayers, circuit_unitary_nil]
    | cons y ys =>
      simp only [zipLayers, List.flatten_cons, circuit_unitary_append]
      have hih : Circuit.unitary (zipLayers xs ys).flatten =
          Circuit.unitary ys.flatten * Circuit.unitary xs.flatten :=
        ih ys fun L1 hL1 g1 hg1 L2 hL2 g2 hg2 =>
          hdisj L1 (List.mem_cons_of_mem _ hL1) g1 hg1 L2 (List.mem_cons_of_mem _ hL2) g2 hg2
      rw [hih]
      have h_xs_y : Circuit.unitary xs.flatten * Circuit.unitary y =
          Circuit.unitary y * Circuit.unitary xs.flatten :=
        circuit_comm_of_disjoint xs.flatten y fun g1 hg1 g2 hg2 => by
          rw [List.mem_flatten] at hg1
          rcases hg1 with ⟨L1, hL1, hg1⟩
          exact hdisj L1 (List.mem_cons_of_mem _ hL1) g1 hg1 y List.mem_cons_self g2 hg2
      calc (Circuit.unitary ys.flatten * Circuit.unitary xs.flatten) *
            (Circuit.unitary y * Circuit.unitary x)
          = Circuit.unitary ys.flatten * (Circuit.unitary xs.flatten * Circuit.unitary y) *
              Circuit.unitary x := by simp only [Matrix.mul_assoc]
        _ = Circuit.unitary ys.flatten * (Circuit.unitary y * Circuit.unitary xs.flatten) *
              Circuit.unitary x := by rw [h_xs_y]
        _ = (Circuit.unitary ys.flatten * Circuit.unitary y) *
              (Circuit.unitary xs.flatten * Circuit.unitary x) := by simp only [Matrix.mul_assoc]

def parMerge {m : ℕ} (lc1 lc2 : LayeredCircuit m) {S1 S2 : Finset (Fin m)}
    (h1 : lc1.UsesOnly S1) (h2 : lc2.UsesOnly S2) (hdisj : Disjoint S1 S2) :
    LayeredCircuit m where
  layers := zipLayers lc1.layers lc2.layers
  disjoint L hL := by
    rcases zipLayers_mem hL with hL1 | hL2 | ⟨x, hx, y, hy, rfl⟩
    · exact lc1.disjoint L hL1
    · exact lc2.disjoint L hL2
    · refine layerDisjoint_append (lc1.disjoint x hx) (lc2.disjoint y hy) ?_
      intro g1 hg1 g2 hg2
      rw [Set.disjoint_left]
      rintro w ⟨i1, rfl⟩ ⟨i2, hi2⟩
      have hw1 : g1.wires i1 ∈ S1 := h1 x hx g1 hg1 i1
      have hw2 : g2.wires i2 ∈ S2 := h2 y hy g2 hg2 i2
      rw [← hi2] at hw1
      exact Finset.disjoint_left.mp hdisj hw1 hw2

lemma parMerge_size {m : ℕ} (lc1 lc2 : LayeredCircuit m) {S1 S2 : Finset (Fin m)}
    (h1 : lc1.UsesOnly S1) (h2 : lc2.UsesOnly S2) (hdisj : Disjoint S1 S2) :
    (parMerge lc1 lc2 h1 h2 hdisj).size = lc1.size + lc2.size :=
  zipLayers_flatten_length lc1.layers lc2.layers

lemma parMerge_depth {m : ℕ} (lc1 lc2 : LayeredCircuit m) {S1 S2 : Finset (Fin m)}
    (h1 : lc1.UsesOnly S1) (h2 : lc2.UsesOnly S2) (hdisj : Disjoint S1 S2) :
    (parMerge lc1 lc2 h1 h2 hdisj).depth = max lc1.depth lc2.depth :=
  zipLayers_length lc1.layers lc2.layers

lemma parMerge_unitary {m : ℕ} (lc1 lc2 : LayeredCircuit m) {S1 S2 : Finset (Fin m)}
    (h1 : lc1.UsesOnly S1) (h2 : lc2.UsesOnly S2) (hdisj : Disjoint S1 S2) :
    (parMerge lc1 lc2 h1 h2 hdisj).unitary = lc2.unitary * lc1.unitary := by
  apply zipLayers_unitary
  intro L1 hL1 g1 hg1 L2 hL2 g2 hg2
  rw [Set.disjoint_left]
  rintro w ⟨i1, rfl⟩ ⟨i2, hi2⟩
  have hw1 : g1.wires i1 ∈ S1 := h1 L1 hL1 g1 hg1 i1
  have hw2 : g2.wires i2 ∈ S2 := h2 L2 hL2 g2 hg2 i2
  rw [← hi2] at hw1
  exact Finset.disjoint_left.mp hdisj hw1 hw2

lemma parMerge_usesOnly {m : ℕ} (lc1 lc2 : LayeredCircuit m) {S1 S2 : Finset (Fin m)}
    (h1 : lc1.UsesOnly S1) (h2 : lc2.UsesOnly S2) (hdisj : Disjoint S1 S2) :
    (parMerge lc1 lc2 h1 h2 hdisj).UsesOnly (S1 ∪ S2) := by
  intro L hL g hg i
  rcases zipLayers_mem hL with hL1 | hL2 | ⟨x, hx, y, hy, rfl⟩
  · exact Finset.mem_union_left S2 (h1 L hL1 g hg i)
  · exact Finset.mem_union_right S1 (h2 L hL2 g hg i)
  · rcases List.mem_append.mp hg with hgx | hgy
    · exact Finset.mem_union_left S2 (h1 x hx g hgx i)
    · exact Finset.mem_union_right S1 (h2 y hy g hgy i)

/-! ### 7. `ImplementsOnClean` Specification & Composition -/

def ImplementsOnClean {main anc : ℕ} (lc : LayeredCircuit (main + anc))
    (U : Matrix (Qubits main) (Qubits main) ℂ) : Prop :=
  ∀ y z : Qubits (main + anc),
    (∀ j : Fin anc, z (Fin.natAdd main j) = false) →
    lc.unitary y z =
      if ∀ j : Fin anc, y (Fin.natAdd main j) = false then
        U (fun i => y (Fin.castAdd anc i)) (fun i => z (Fin.castAdd anc i))
      else 0

end LayeredCircuit

/-! ### 8. Elementary 1- and 2-Qubit Gates in `gates12` -/

private def qubits1EquivBool : Qubits 1 ≃ Bool where
  toFun b := b 0
  invFun x _ := x
  left_inv b := funext fun i => by fin_cases i; rfl
  right_inv _ := rfl

private def qubits2EquivProd : Qubits 2 ≃ Bool × Bool where
  toFun b := (b 0, b 1)
  invFun p := ![p.1, p.2]
  left_inv b := funext fun i => by fin_cases i <;> rfl
  right_inv p := by ext <;> rfl

lemma ofMatrix1_mem_gates12 {U : Matrix Bool Bool ℂ}
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    Gate.ofMatrix1 U ∈ gates12 := by
  refine ⟨?_, by simp [Gate.ofMatrix1], by simp [Gate.ofMatrix1]⟩
  let M : Matrix (Qubits 1) (Qubits 1) ℂ := U.submatrix (fun b => b 0) (fun b => b 0)
  have hM : M ∈ Matrix.unitaryGroup (Qubits 1) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have hU' := Matrix.mem_unitaryGroup_iff.mp hU
    ext y z
    simp only [M, Matrix.mul_apply, Matrix.star_apply, Matrix.submatrix_apply, Matrix.one_apply]
    have hsum : (∑ x : Qubits 1, U (y 0) (x 0) * star (U (z 0) (x 0))) =
        ∑ x : Bool, U (y 0) x * star (U (z 0) x) :=
      Fintype.sum_equiv qubits1EquivBool _ (fun x : Bool => U (y 0) x * star (U (z 0) x))
        (fun _ => rfl)
    rw [hsum]
    have hent := congrFun (congrFun hU' (y 0)) (z 0)
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at hent
    rw [hent]
    by_cases h : y 0 = z 0
    · have hyz : y = z := funext fun i => by fin_cases i; exact h
      subst hyz; simp
    · have hyz : y ≠ z := fun heq => h (congrFun heq 0)
      simp [h, hyz]
  exact hM

lemma ofMatrix2_mem_gates12 {U : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) :
    Gate.ofMatrix2 U ∈ gates12 := by
  refine ⟨?_, by simp [Gate.ofMatrix2], by simp [Gate.ofMatrix2]⟩
  let M : Matrix (Qubits 2) (Qubits 2) ℂ :=
    U.submatrix (fun b => (b 0, b 1)) (fun b => (b 0, b 1))
  have hM : M ∈ Matrix.unitaryGroup (Qubits 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have hU' := Matrix.mem_unitaryGroup_iff.mp hU
    ext y z
    simp only [M, Matrix.mul_apply, Matrix.star_apply, Matrix.submatrix_apply, Matrix.one_apply]
    have hsum : (∑ x : Qubits 2, U (y 0, y 1) (x 0, x 1) * star (U (z 0, z 1) (x 0, x 1))) =
        ∑ x : Bool × Bool, U (y 0, y 1) x * star (U (z 0, z 1) x) :=
      Fintype.sum_equiv qubits2EquivProd _
        (fun x : Bool × Bool => U (y 0, y 1) x * star (U (z 0, z 1) x)) (fun _ => rfl)
    rw [hsum]
    have hent := congrFun (congrFun hU' (y 0, y 1)) (z 0, z 1)
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at hent
    rw [hent]
    by_cases h : (y 0, y 1) = (z 0, z 1)
    · have hyz : y = z := funext fun i => by
        fin_cases i
        · exact congrArg Prod.fst h
        · exact congrArg Prod.snd h
      subst hyz; simp
    · have hyz : y ≠ z := fun heq => h (by subst heq; rfl)
      simp [h, hyz]
  exact hM

lemma controlled_mem_unitaryGroup {κ : Type*} [Fintype κ] [DecidableEq κ]
    {U : Matrix κ κ ℂ} (hU : U ∈ Matrix.unitaryGroup κ ℂ) :
    controlled U ∈ Matrix.unitaryGroup (Bool × κ) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hU' := Matrix.mem_unitaryGroup_iff.mp hU
  ext ⟨y0, y1⟩ ⟨z0, z1⟩
  simp only [Matrix.mul_apply, Matrix.star_apply, controlled, Matrix.of_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  by_cases hyz : y0 = z0
  · subst hyz
    rw [Finset.sum_eq_single y0]
    · cases y0
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [Finset.sum_eq_single z1]
        · by_cases h1 : y1 = z1 <;> simp [h1]
        · intro x _ hx; simp [hx.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      · simp only [↓reduceIte]
        have hent := congrFun (congrFun hU' y1) z1
        simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using hent
    · intro b _ hb
      refine Finset.sum_eq_zero fun x _ => ?_
      simp [hb.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hpne : (y0, y1) ≠ (z0, z1) := fun h => hyz (congrArg Prod.fst h)
    rw [if_neg hpne]
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun x _ => ?_
    by_cases hb : y0 = b
    · subst hb; simp [ne_comm.mp hyz]
    · simp [hb]

lemma pauliX_mem_unitaryGroup : pauliX ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Fintype.sum_bool, pauliX,
    Matrix.of_apply]
  cases a <;> cases b <;> norm_num

lemma pauliZ_mem_unitaryGroup : pauliZ ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Fintype.sum_bool, pauliZ,
    Matrix.diagonal_apply]
  cases a <;> cases b <;> norm_num

lemma hadamard_mem_unitaryGroup : hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
  have hstar : star hadamard = hadamard := by
    ext a b
    cases a <;> cases b <;> simp [hadamard, Matrix.star_apply]
  rw [Matrix.mem_unitaryGroup_iff, hstar, hadamard_mul_self]

lemma cnot_mem_unitaryGroup : cnot ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Fintype.sum_bool, cnot, Matrix.of_apply]
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> simp

lemma swapGate_mem_unitaryGroup : swapGate ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Fintype.sum_bool, swapGate, Matrix.of_apply]
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> simp

def wire1Emb {m : ℕ} (w : Fin m) : Fin 1 ↪ Fin m where
  toFun _ := w
  inj' i j _ := Subsingleton.elim i j

def wire2Emb {m : ℕ} (w0 w1 : Fin m) (hne : w0 ≠ w1) : Fin 2 ↪ Fin m where
  toFun := ![w0, w1]
  inj' i j h := by
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd h hne
    · exact absurd h.symm hne
    · rfl

lemma wire1Emb_mem {m : ℕ} (w : Fin m) (i : Fin 1) : wire1Emb w i = w := rfl

lemma wire2Emb_zero {m : ℕ} (w0 w1 : Fin m) (hne : w0 ≠ w1) : wire2Emb w0 w1 hne 0 = w0 := rfl

lemma wire2Emb_one {m : ℕ} (w0 w1 : Fin m) (hne : w0 ≠ w1) : wire2Emb w0 w1 hne 1 = w1 := rfl

def gate1App {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (w : Fin m) : GateApp gates12 m where
  gate := Gate.ofMatrix1 U
  mem := ofMatrix1_mem_gates12 hU
  wires := wire1Emb w

def gate2App {m : ℕ} (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) (w0 w1 : Fin m) (hne : w0 ≠ w1) :
    GateApp gates12 m where
  gate := Gate.ofMatrix2 U
  mem := ofMatrix2_mem_gates12 hU
  wires := wire2Emb w0 w1 hne

def ctrlGate1App {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (c t : Fin m) (hne : c ≠ t) : GateApp gates12 m :=
  gate2App (controlled U) (controlled_mem_unitaryGroup hU) c t hne

def pauliXApp {m : ℕ} (w : Fin m) : GateApp gates12 m :=
  gate1App pauliX pauliX_mem_unitaryGroup w

def pauliZApp {m : ℕ} (w : Fin m) : GateApp gates12 m :=
  gate1App pauliZ pauliZ_mem_unitaryGroup w

noncomputable def hadamardApp {m : ℕ} (w : Fin m) : GateApp gates12 m :=
  gate1App hadamard hadamard_mem_unitaryGroup w

def cnotApp {m : ℕ} (c t : Fin m) (hne : c ≠ t) : GateApp gates12 m :=
  gate2App cnot cnot_mem_unitaryGroup c t hne

def swapApp {m : ℕ} (a b : Fin m) (hne : a ≠ b) : GateApp gates12 m :=
  gate2App swapGate swapGate_mem_unitaryGroup a b hne

def gate1 {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (w : Fin m) : LayeredCircuit m :=
  LayeredCircuit.single (gate1App U hU w)

def ctrlGate1 {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (c t : Fin m) (hne : c ≠ t) : LayeredCircuit m :=
  LayeredCircuit.single (ctrlGate1App U hU c t hne)

def pauliXGate {m : ℕ} (w : Fin m) : LayeredCircuit m :=
  LayeredCircuit.single (pauliXApp w)

def pauliZGate {m : ℕ} (w : Fin m) : LayeredCircuit m :=
  LayeredCircuit.single (pauliZApp w)

noncomputable def hadamardGate {m : ℕ} (w : Fin m) : LayeredCircuit m :=
  LayeredCircuit.single (hadamardApp w)

def cnotGate {m : ℕ} (c t : Fin m) (hne : c ≠ t) : LayeredCircuit m :=
  LayeredCircuit.single (cnotApp c t hne)

@[simp] lemma gate1_size {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (w : Fin m) : (gate1 U hU w).size = 1 := rfl

@[simp] lemma gate1_depth {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (w : Fin m) : (gate1 U hU w).depth = 1 := rfl

lemma gate1_usesOnly {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (w : Fin m) : (gate1 U hU w).UsesOnly {w} :=
  LayeredCircuit.single_usesOnly _ fun _ => Finset.mem_singleton_self w

@[simp] lemma ctrlGate1_size {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (c t : Fin m) (hne : c ≠ t) : (ctrlGate1 U hU c t hne).size = 1 := rfl

@[simp] lemma ctrlGate1_depth {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (c t : Fin m) (hne : c ≠ t) : (ctrlGate1 U hU c t hne).depth = 1 := rfl

lemma ctrlGate1_usesOnly {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (c t : Fin m) (hne : c ≠ t) : (ctrlGate1 U hU c t hne).UsesOnly {c, t} := by
  refine LayeredCircuit.single_usesOnly _ fun i => ?_
  dsimp only [ctrlGate1App, gate2App, Gate.ofMatrix2] at i ⊢
  rw [Finset.mem_insert, Finset.mem_singleton]
  rcases (by fin_cases i <;> decide : i = 0 ∨ i = 1) with rfl | rfl
  · left; rfl
  · right; rfl

@[simp] lemma pauliXGate_size {m : ℕ} (w : Fin m) : (pauliXGate w).size = 1 := rfl
@[simp] lemma pauliXGate_depth {m : ℕ} (w : Fin m) : (pauliXGate w).depth = 1 := rfl

lemma pauliXGate_usesOnly {m : ℕ} (w : Fin m) : (pauliXGate w).UsesOnly {w} :=
  gate1_usesOnly pauliX pauliX_mem_unitaryGroup w

@[simp] lemma pauliZGate_size {m : ℕ} (w : Fin m) : (pauliZGate w).size = 1 := rfl
@[simp] lemma pauliZGate_depth {m : ℕ} (w : Fin m) : (pauliZGate w).depth = 1 := rfl

@[simp] lemma hadamardGate_size {m : ℕ} (w : Fin m) : (hadamardGate w).size = 1 := rfl
@[simp] lemma hadamardGate_depth {m : ℕ} (w : Fin m) : (hadamardGate w).depth = 1 := rfl

@[simp] lemma cnotGate_size {m : ℕ} (c t : Fin m) (hne : c ≠ t) :
    (cnotGate c t hne).size = 1 := rfl

@[simp] lemma cnotGate_depth {m : ℕ} (c t : Fin m) (hne : c ≠ t) :
    (cnotGate c t hne).depth = 1 := rfl

lemma cnotGate_usesOnly {m : ℕ} (c t : Fin m) (hne : c ≠ t) :
    (cnotGate c t hne).UsesOnly {c, t} := by
  refine LayeredCircuit.single_usesOnly _ fun i => ?_
  dsimp only [cnotApp, gate2App, Gate.ofMatrix2] at i ⊢
  rw [Finset.mem_insert, Finset.mem_singleton]
  rcases (by fin_cases i <;> decide : i = 0 ∨ i = 1) with rfl | rfl
  · left; rfl
  · right; rfl

private lemma embedOp_ofMatrix1_entry {m : ℕ} (U : Matrix Bool Bool ℂ) (w : Fin m)
    (y z : Qubits m) :
    embedOp (U.submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0)) (wire1Emb w) y z =
      if (∀ a : Fin m, a ≠ w → y a = z a) then U (y w) (z w) else 0 := by
  simp only [embedOp, Matrix.of_apply, Matrix.submatrix_apply]
  have hiff : (∀ a : Fin m, a ∉ Set.range (wire1Emb w) → y a = z a) ↔
      (∀ a : Fin m, a ≠ w → y a = z a) := by
    constructor
    · intro h a ha
      apply h a
      rintro ⟨i, hi⟩
      exact ha hi.symm
    · intro h a ha
      apply h a
      intro heq
      subst heq
      exact ha ⟨0, rfl⟩
  by_cases h : ∀ a : Fin m, a ≠ w → y a = z a
  · rw [if_pos (hiff.mpr h), if_pos h]; rfl
  · rw [if_neg (mt hiff.mp h), if_neg h]

lemma embedOp_gate1App_entry {m : ℕ} (U : Matrix Bool Bool ℂ) (w : Fin m)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) (y z : Qubits m) :
    embedOp (gate1App U hU w).gate.mat (gate1App U hU w).wires y z =
      if (∀ a : Fin m, a ≠ w → y a = z a) then U (y w) (z w) else 0 :=
  embedOp_ofMatrix1_entry U w y z

private lemma embedOp_ofMatrix2_entry {m : ℕ} (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (w0 w1 : Fin m) (hne : w0 ≠ w1) (y z : Qubits m) :
    embedOp (U.submatrix (fun b : Qubits 2 => (b 0, b 1)) (fun b : Qubits 2 => (b 0, b 1)))
        (wire2Emb w0 w1 hne) y z =
      if (∀ a : Fin m, a ≠ w0 → a ≠ w1 → y a = z a) then U (y w0, y w1) (z w0, z w1) else 0 := by
  simp only [embedOp, Matrix.of_apply, Matrix.submatrix_apply]
  have hiff : (∀ a : Fin m, a ∉ Set.range (wire2Emb w0 w1 hne) → y a = z a) ↔
      (∀ a : Fin m, a ≠ w0 → a ≠ w1 → y a = z a) := by
    constructor
    · intro h a ha0 ha1
      apply h a
      rintro ⟨i, rfl⟩
      fin_cases i
      · exact ha0 rfl
      · exact ha1 rfl
    · intro h a ha
      apply h a
      · intro h0; subst h0; exact ha ⟨0, rfl⟩
      · intro h1; subst h1; exact ha ⟨1, rfl⟩
  by_cases h : ∀ a : Fin m, a ≠ w0 → a ≠ w1 → y a = z a
  · rw [if_pos (hiff.mpr h), if_pos h]; rfl
  · rw [if_neg (mt hiff.mp h), if_neg h]

lemma embedOp_gate2App_entry {m : ℕ} (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) (w0 w1 : Fin m) (hne : w0 ≠ w1)
    (y z : Qubits m) :
    embedOp (gate2App U hU w0 w1 hne).gate.mat (gate2App U hU w0 w1 hne).wires y z =
      if (∀ a : Fin m, a ≠ w0 → a ≠ w1 → y a = z a) then U (y w0, y w1) (z w0, z w1) else 0 :=
  embedOp_ofMatrix2_entry U w0 w1 hne y z

lemma act_pauliXGate_ket {m : ℕ} (w : Fin m) (x : Qubits m) :
    act (pauliXGate w).unitary (ket x) = ket (Function.update x w (!x w)) := by
  rw [pauliXGate, LayeredCircuit.single_unitary, act_ket_eq]
  rw [Finset.sum_eq_single (Function.update x w (!x w))]
  · rw [pauliXApp, embedOp_gate1App_entry]
    have hoff : ∀ a : Fin m, a ≠ w → Function.update x w (!x w) a = x a :=
      fun a ha => Function.update_of_ne ha _ _
    rw [if_pos hoff, Function.update_self]
    cases hx : x w <;> simp [pauliX]
  · intro y _ hy
    rw [pauliXApp, embedOp_gate1App_entry]
    by_cases hoff : ∀ a : Fin m, a ≠ w → y a = x a
    · rw [if_pos hoff]
      have hyw : y w = x w := by
        by_contra hne
        apply hy
        funext a
        by_cases haw : a = w
        · subst haw
          cases hxw : x a <;> cases hyw' : y a <;> simp_all
        · rw [hoff a haw, Function.update_of_ne haw]
      simp [pauliX, hyw]
    · rw [if_neg hoff, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma act_cnotGate_ket {m : ℕ} (c t : Fin m) (hne : c ≠ t) (x : Qubits m) :
    act (cnotGate c t hne).unitary (ket x) =
      ket (Function.update x t (xor (x t) (x c))) := by
  rw [cnotGate, LayeredCircuit.single_unitary, act_ket_eq]
  rw [Finset.sum_eq_single (Function.update x t (xor (x t) (x c)))]
  · rw [cnotApp, embedOp_gate2App_entry]
    have hoff : ∀ a : Fin m, a ≠ c → a ≠ t → Function.update x t (xor (x t) (x c)) a = x a :=
      fun a _ hat => Function.update_of_ne hat _ _
    rw [if_pos hoff, Function.update_of_ne hne, Function.update_self]
    simp [cnot]
  · intro y _ hy
    rw [cnotApp, embedOp_gate2App_entry]
    by_cases hoff : ∀ a : Fin m, a ≠ c → a ≠ t → y a = x a
    · rw [if_pos hoff]
      have hne_cnot : ¬ (y c = x c ∧ y t = xor (x t) (x c)) := by
        rintro ⟨hyc, hyt⟩
        apply hy
        funext a
        by_cases hac : a = c
        · subst hac; rw [hyc, Function.update_of_ne hne]
        · by_cases hat : a = t
          · subst hat; rw [hyt, Function.update_self]
          · rw [hoff a hac hat, Function.update_of_ne hat]
      simp [cnot, hne_cnot]
    · rw [if_neg hoff, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma act_ctrlGate1_ket {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (c t : Fin m) (hne : c ≠ t) (x : Qubits m) :
    act (ctrlGate1 U hU c t hne).unitary (ket x) =
      ∑ b : Bool, (if x c then U b (x t) else if b = x t then 1 else 0) •
        ket (Function.update x t b) := by
  rw [ctrlGate1, LayeredCircuit.single_unitary, act_ket_eq]
  have hsum : (∑ y : Qubits m,
      embedOp (ctrlGate1App U hU c t hne).gate.mat (ctrlGate1App U hU c t hne).wires y x •
        ket y) =
      ∑ y ∈ Finset.univ.image (fun b : Bool => Function.update x t b),
      embedOp (ctrlGate1App U hU c t hne).gate.mat (ctrlGate1App U hU c t hne).wires y x •
        ket y := by
    rw [← Finset.sum_subset (Finset.subset_univ _)]
    intro y _ hy
    dsimp only [ctrlGate1App]
    rw [embedOp_gate2App_entry]
    by_cases hoff : ∀ a : Fin m, a ≠ c → a ≠ t → y a = x a
    · rw [if_pos hoff]
      by_cases hyc : y c = x c
      · exfalso; apply hy
        rw [Finset.mem_image]
        refine ⟨y t, Finset.mem_univ _, ?_⟩
        funext a
        by_cases hat : a = t
        · subst hat; simp
        · rw [Function.update_of_ne hat]
          by_cases hac : a = c
          · subst hac; exact hyc.symm
          · exact (hoff a hac hat).symm
      · simp [controlled, hyc]
    · rw [if_neg hoff, zero_smul]
  rw [hsum, Finset.sum_image]
  · refine Finset.sum_congr rfl fun b _ => ?_
    dsimp only [ctrlGate1App]
    rw [embedOp_gate2App_entry]
    have hoff : ∀ a : Fin m, a ≠ c → a ≠ t → Function.update x t b a = x a :=
      fun a _ hat => Function.update_of_ne hat _ _
    rw [if_pos hoff, Function.update_of_ne hne, Function.update_self]
    simp [controlled, Matrix.one_apply]
  · intro b1 _ b2 _ hb
    have := congrFun hb t
    simpa using this

/-! ### 9. Barenco 5-Gate Toffoli (`toffoli3`, `toffoliOn`) -/

noncomputable def sqrtX : Matrix Bool Bool ℂ :=
  ((1 - Complex.I) / 2) • (1 : Matrix Bool Bool ℂ) + ((1 + Complex.I) / 2) • pauliX

lemma sqrtX_mem_unitaryGroup : sqrtX ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Fintype.sum_bool, sqrtX,
    pauliX, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  cases a <;> cases b <;> simp <;> ring_nf <;> norm_num

lemma sqrtX_mul_self : sqrtX * sqrtX = pauliX := by
  ext a b
  simp only [Matrix.mul_apply, Fintype.sum_bool, sqrtX, pauliX, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul]
  cases a <;> cases b <;> simp <;> ring_nf <;> norm_num

def toffoliMat : Matrix (Qubits 3) (Qubits 3) ℂ :=
  permMat fun z => ![z 0, z 1, xor (z 2) (z 0 && z 1)]

lemma toffoliMat_mem_unitaryGroup : toffoliMat ∈ Matrix.unitaryGroup (Qubits 3) ℂ := by
  apply permMat_mem_unitaryGroup
  refine ⟨fun a b h => ?_, fun b => ⟨![b 0, b 1, xor (b 2) (b 0 && b 1)], ?_⟩⟩
  · have h0 : a 0 = b 0 := congrFun h 0
    have h1 : a 1 = b 1 := congrFun h 1
    have h2 : xor (a 2) (a 0 && a 1) = xor (b 2) (b 0 && b 1) := congrFun h 2
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · rw [h0, h1] at h2
      simpa using congrArg (fun x => xor x (b 0 && b 1)) h2
  · funext i
    fin_cases i <;> simp

noncomputable def toffoli3 : LayeredCircuit 3 :=
  (ctrlGate1 sqrtX sqrtX_mem_unitaryGroup 1 2 (by decide)).seq
    ((cnotGate 0 1 (by decide)).seq
      ((ctrlGate1 (star sqrtX) (Unitary.star_mem sqrtX_mem_unitaryGroup) 1 2 (by decide)).seq
        ((cnotGate 0 1 (by decide)).seq
          (ctrlGate1 sqrtX sqrtX_mem_unitaryGroup 0 2 (by decide)))))

@[simp] lemma toffoli3_size : toffoli3.size = 5 := rfl
@[simp] lemma toffoli3_depth : toffoli3.depth = 5 := rfl

private lemma block3_mul (M N : Bool → Bool → Matrix Bool Bool ℂ) :
    (Matrix.of fun y z : Qubits 3 =>
      if y 0 = z 0 ∧ y 1 = z 1 then M (y 0) (y 1) (y 2) (z 2) else 0) *
    (Matrix.of fun y z : Qubits 3 =>
      if y 0 = z 0 ∧ y 1 = z 1 then N (y 0) (y 1) (y 2) (z 2) else 0) =
    Matrix.of fun y z : Qubits 3 =>
      if y 0 = z 0 ∧ y 1 = z 1 then (M (y 0) (y 1) * N (y 0) (y 1)) (y 2) (z 2) else 0 := by
  classical
  ext y z
  simp only [Matrix.mul_apply, Matrix.of_apply]
  by_cases hyz : y 0 = z 0 ∧ y 1 = z 1
  · rw [if_pos hyz]
    have hsum : (∑ x : Qubits 3,
        (if y 0 = x 0 ∧ y 1 = x 1 then M (y 0) (y 1) (y 2) (x 2) else 0) *
        (if x 0 = z 0 ∧ x 1 = z 1 then N (x 0) (x 1) (x 2) (z 2) else 0)) =
        ∑ x ∈ Finset.univ.image (fun b : Bool => ![y 0, y 1, b]),
        (if y 0 = x 0 ∧ y 1 = x 1 then M (y 0) (y 1) (y 2) (x 2) else 0) *
        (if x 0 = z 0 ∧ x 1 = z 1 then N (x 0) (x 1) (x 2) (z 2) else 0) := by
      rw [← Finset.sum_subset (Finset.subset_univ _)]
      intro x _ hx
      by_cases hyx : y 0 = x 0 ∧ y 1 = x 1
      · exfalso; apply hx
        rw [Finset.mem_image]
        refine ⟨x 2, Finset.mem_univ _, ?_⟩
        funext i; fin_cases i
        · exact hyx.1
        · exact hyx.2
        · rfl
      · rw [if_neg hyx, zero_mul]
    rw [hsum, Finset.sum_image]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [hyz.1, hyz.2]
      have he0 : (![z 0, z 1, b] : Qubits 3) 0 = z 0 := rfl
      have he1 : (![z 0, z 1, b] : Qubits 3) 1 = z 1 := rfl
      have he2 : (![z 0, z 1, b] : Qubits 3) 2 = b := rfl
      simp only [he0, he1, he2, ↓reduceIte, true_and]
    · intro b1 _ b2 _ hb
      have := congrFun hb 2
      simpa using this
  · rw [if_neg hyz]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hyx : y 0 = x 0 ∧ y 1 = x 1
    · have hxz : ¬ (x 0 = z 0 ∧ x 1 = z 1) := fun h =>
        hyz ⟨hyx.1.trans h.1, hyx.2.trans h.2⟩
      rw [if_neg hxz, mul_zero]
    · rw [if_neg hyx, zero_mul]

lemma toffoli3_unitary : toffoli3.unitary = toffoliMat := by
  have h54321 : toffoli3.unitary =
      (ctrlGate1 sqrtX sqrtX_mem_unitaryGroup 0 2 (by decide)).unitary *
      (((cnotGate 0 1 (by decide)).unitary *
        ((ctrlGate1 (star sqrtX) (Unitary.star_mem sqrtX_mem_unitaryGroup) 1 2 (by decide)).unitary *
          (cnotGate 0 1 (by decide)).unitary)) *
      (ctrlGate1 sqrtX sqrtX_mem_unitaryGroup 1 2 (by decide)).unitary) := by
    simp only [toffoli3, LayeredCircuit.seq_unitary, Matrix.mul_assoc]
  rw [h54321]
  let flip1 : Qubits 3 → Qubits 3 := fun z => ![z 0, xor (z 1) (z 0), z 2]
  have hflip1_invol : ∀ z : Qubits 3, flip1 (flip1 z) = z := by
    intro z; funext i; fin_cases i <;> simp [flip1]
  have hcnot_entry : ∀ y z : Qubits 3,
      (cnotGate 0 1 (by decide)).unitary y z = if y = flip1 z then 1 else 0 := by
    intro y z
    rw [cnotGate, LayeredCircuit.single_unitary, cnotApp, embedOp_gate2App_entry]
    by_cases hoff : ∀ a : Fin 3, a ≠ 0 → a ≠ 1 → y a = z a
    · rw [if_pos hoff]
      by_cases hy : y = flip1 z
      · rw [if_pos hy, hy]; simp [flip1, cnot]
      · rw [if_neg hy]
        have hnot : ¬ (y 0 = z 0 ∧ y 1 = xor (z 1) (z 0)) := by
          rintro ⟨h0, h1⟩
          apply hy
          funext i; fin_cases i
          · exact h0
          · exact h1
          · exact hoff 2 (by decide) (by decide)
        simp [cnot, hnot]
    · rw [if_neg hoff]
      have hy : y ≠ flip1 z := by
        intro h
        apply hoff
        intro a ha0 ha1
        fin_cases a
        · exact absurd rfl ha0
        · exact absurd rfl ha1
        · rw [h]; rfl
      rw [if_neg hy]
  have hctrl_entry : ∀ (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
      (c : Fin 3) (hc2 : c ≠ 2) (y z : Qubits 3),
      (ctrlGate1 U hU c 2 hc2).unitary y z =
        if y 0 = z 0 ∧ y 1 = z 1 then (if y c then U (y 2) (z 2) else if y 2 = z 2 then 1 else 0)
        else 0 := by
    intro U hU c hc2 y z
    rw [ctrlGate1, LayeredCircuit.single_unitary]
    dsimp only [ctrlGate1App]
    rw [embedOp_gate2App_entry]
    rcases (by fin_cases c <;> decide : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
    · by_cases h1 : y 1 = z 1
      · have hoff : ∀ a : Fin 3, a ≠ 0 → a ≠ 2 → y a = z a := by
          intro a ha0 ha2; fin_cases a
          · exact absurd rfl ha0
          · exact h1
          · exact absurd rfl ha2
        rw [if_pos hoff]
        by_cases h0 : y 0 = z 0
        · rw [if_pos ⟨h0, h1⟩, controlled, Matrix.of_apply, if_pos h0]
          simp [Matrix.one_apply]
        · rw [if_neg (fun ⟨h0', _⟩ => h0 h0'), controlled, Matrix.of_apply, if_neg h0]
      · have hoff : ¬ ∀ a : Fin 3, a ≠ 0 → a ≠ 2 → y a = z a := fun h =>
          h1 (h 1 (by decide) (by decide))
        rw [if_neg hoff, if_neg (fun ⟨_, h1'⟩ => h1 h1')]
    · by_cases h0 : y 0 = z 0
      · have hoff : ∀ a : Fin 3, a ≠ 1 → a ≠ 2 → y a = z a := by
          intro a ha1 ha2; fin_cases a
          · exact h0
          · exact absurd rfl ha1
          · exact absurd rfl ha2
        rw [if_pos hoff]
        by_cases h1 : y 1 = z 1
        · rw [if_pos ⟨h0, h1⟩, controlled, Matrix.of_apply, if_pos h1]
          simp [Matrix.one_apply]
        · rw [if_neg (fun ⟨_, h1'⟩ => h1 h1'), controlled, Matrix.of_apply, if_neg h1]
      · have hoff : ¬ ∀ a : Fin 3, a ≠ 1 → a ≠ 2 → y a = z a := fun h =>
          h0 (h 0 (by decide) (by decide))
        rw [if_neg hoff, if_neg (fun ⟨h0', _⟩ => h0 h0')]
    · exact absurd rfl hc2
  let M1 : Bool → Bool → Matrix Bool Bool ℂ := fun _ b1 => if b1 then sqrtX else 1
  let M3 : Bool → Bool → Matrix Bool Bool ℂ := fun b0 b1 => if xor b1 b0 then star sqrtX else 1
  let M5 : Bool → Bool → Matrix Bool Bool ℂ := fun b0 _ => if b0 then sqrtX else 1
  have hG1 : (ctrlGate1 sqrtX sqrtX_mem_unitaryGroup 1 2 (by decide)).unitary =
      Matrix.of fun y z : Qubits 3 =>
        if y 0 = z 0 ∧ y 1 = z 1 then M1 (y 0) (y 1) (y 2) (z 2) else 0 := by
    ext y z
    rw [hctrl_entry _ _ 1 (by decide) y z, Matrix.of_apply]
    dsimp [M1]
    split_ifs with h1 h2 <;> simp [Matrix.one_apply, *]
  have hG5 : (ctrlGate1 sqrtX sqrtX_mem_unitaryGroup 0 2 (by decide)).unitary =
      Matrix.of fun y z : Qubits 3 =>
        if y 0 = z 0 ∧ y 1 = z 1 then M5 (y 0) (y 1) (y 2) (z 2) else 0 := by
    ext y z
    rw [hctrl_entry _ _ 0 (by decide) y z, Matrix.of_apply]
    dsimp [M5]
    split_ifs with h1 h2 <;> simp [Matrix.one_apply, *]
  have hG3 : ((cnotGate 0 1 (by decide)).unitary *
      ((ctrlGate1 (star sqrtX) (Unitary.star_mem sqrtX_mem_unitaryGroup) 1 2 (by decide)).unitary *
        (cnotGate 0 1 (by decide)).unitary)) =
      Matrix.of fun y z : Qubits 3 =>
        if y 0 = z 0 ∧ y 1 = z 1 then M3 (y 0) (y 1) (y 2) (z 2) else 0 := by
    ext y z
    simp only [Matrix.mul_apply, Matrix.of_apply]
    have hR : ∀ x : Qubits 3,
        (∑ w : Qubits 3,
          (ctrlGate1 (star sqrtX) (Unitary.star_mem sqrtX_mem_unitaryGroup) 1 2 (by decide)).unitary x w *
            (cnotGate 0 1 (by decide)).unitary w z) =
        (ctrlGate1 (star sqrtX) (Unitary.star_mem sqrtX_mem_unitaryGroup) 1 2 (by decide)).unitary
          x (flip1 z) := by
      intro x
      rw [Finset.sum_eq_single (flip1 z)]
      · rw [hcnot_entry, if_pos rfl, mul_one]
      · intro w _ hw; rw [hcnot_entry, if_neg hw, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [hR]
    rw [Finset.sum_eq_single (flip1 y)]
    · rw [hcnot_entry, if_pos (hflip1_invol y).symm, one_mul, hctrl_entry _ _ 1 (by decide)]
      have hiff : flip1 y 0 = flip1 z 0 ∧ flip1 y 1 = flip1 z 1 ↔ y 0 = z 0 ∧ y 1 = z 1 := by
        simp only [flip1, Matrix.cons_val_zero, Matrix.cons_val_one]
        cases y 0 <;> cases z 0 <;> cases y 1 <;> cases z 1 <;> simp
      by_cases hyz : y 0 = z 0 ∧ y 1 = z 1
      · rw [if_pos (hiff.mpr hyz), if_pos hyz]
        have h1L : flip1 y 1 = xor (y 1) (y 0) := rfl
        have h2L : flip1 y 2 = y 2 := rfl
        have h2R : flip1 z 2 = z 2 := rfl
        rw [h1L, h2L, h2R]
        dsimp only [M3]
        cases h0 : y 0 <;> cases h1 : y 1 <;> simp [Matrix.one_apply]
      · rw [if_neg (mt hiff.mp hyz), if_neg hyz]
    · intro x _ hx
      have hne : y ≠ flip1 x := fun h => hx (by rw [h, hflip1_invol])
      rw [hcnot_entry, if_neg hne, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hG1, hG3, hG5, block3_mul M3 M1, block3_mul M5 (fun b0 b1 => M3 b0 b1 * M1 b0 b1)]
  ext y z
  simp only [Matrix.of_apply, toffoliMat, permMat]
  have hprod : ∀ b0 b1 : Bool, M5 b0 b1 * (M3 b0 b1 * M1 b0 b1) =
      if b0 && b1 then pauliX else 1 := by
    intro b0 b1
    have hstar : star sqrtX * sqrtX = 1 := by
      simpa using Matrix.mem_unitaryGroup_iff'.mp sqrtX_mem_unitaryGroup
    have hmul_star : sqrtX * star sqrtX = 1 := by
      simpa using Matrix.mem_unitaryGroup_iff.mp sqrtX_mem_unitaryGroup
    cases b0 <;> cases b1 <;> simp [M1, M3, M5, hstar, hmul_star, sqrtX_mul_self]
  have hboolX : ∀ (b y2 z2 : Bool),
      (if b then pauliX else (1 : Matrix Bool Bool ℂ)) y2 z2 =
        if y2 = xor z2 b then 1 else 0 := by
    intro b y2 z2
    cases b <;> cases y2 <;> cases z2 <;> simp [pauliX]
  by_cases hyz : y 0 = z 0 ∧ y 1 = z 1
  · rw [if_pos hyz, hprod (y 0) (y 1), hboolX (y 0 && y 1) (y 2) (z 2)]
    by_cases hy_eq : y = ![z 0, z 1, xor (z 2) (z 0 && z 1)]
    · rw [if_pos hy_eq]
      have hy2 : y 2 = xor (z 2) (y 0 && y 1) := by
        have := congrFun hy_eq 2
        simpa [hyz.1, hyz.2] using this
      rw [if_pos hy2]
    · rw [if_neg hy_eq]
      have hy2 : y 2 ≠ xor (z 2) (y 0 && y 1) := by
        intro h2
        apply hy_eq
        funext i; fin_cases i
        · exact hyz.1
        · exact hyz.2
        · simpa [hyz.1, hyz.2] using h2
      rw [if_neg hy2]
  · rw [if_neg hyz]
    have hy_ne : y ≠ ![z 0, z 1, xor (z 2) (z 0 && z 1)] := by
      intro h; apply hyz
      exact ⟨congrFun h 0, congrFun h 1⟩
    rw [if_neg hy_ne]

lemma act_toffoli3_ket (x : Qubits 3) :
    act toffoli3.unitary (ket x) = ket ![x 0, x 1, xor (x 2) (x 0 && x 1)] := by
  rw [toffoli3_unitary, toffoliMat, act_permMat_ket]

def wire3Emb {m : ℕ} (w0 w1 w2 : Fin m) (h01 : w0 ≠ w1) (h02 : w0 ≠ w2) (h12 : w1 ≠ w2) :
    Fin 3 ↪ Fin m where
  toFun := ![w0, w1, w2]
  inj' i j h := by
    fin_cases i <;> fin_cases j <;> simp_all

@[simp] lemma wire3Emb_zero {m : ℕ} (w0 w1 w2 : Fin m) (h01 : w0 ≠ w1) (h02 : w0 ≠ w2)
    (h12 : w1 ≠ w2) : wire3Emb w0 w1 w2 h01 h02 h12 0 = w0 := rfl
@[simp] lemma wire3Emb_one {m : ℕ} (w0 w1 w2 : Fin m) (h01 : w0 ≠ w1) (h02 : w0 ≠ w2)
    (h12 : w1 ≠ w2) : wire3Emb w0 w1 w2 h01 h02 h12 1 = w1 := rfl
@[simp] lemma wire3Emb_two {m : ℕ} (w0 w1 w2 : Fin m) (h01 : w0 ≠ w1) (h02 : w0 ≠ w2)
    (h12 : w1 ≠ w2) : wire3Emb w0 w1 w2 h01 h02 h12 2 = w2 := rfl

noncomputable def toffoliOn {m : ℕ} (c1 c2 tgt : Fin m)
    (h12 : c1 ≠ c2) (h1t : c1 ≠ tgt) (h2t : c2 ≠ tgt) : LayeredCircuit m :=
  toffoli3.mapWires (wire3Emb c1 c2 tgt h12 h1t h2t)

@[simp] lemma toffoliOn_size {m : ℕ} (c1 c2 tgt : Fin m)
    (h12 : c1 ≠ c2) (h1t : c1 ≠ tgt) (h2t : c2 ≠ tgt) :
    (toffoliOn c1 c2 tgt h12 h1t h2t).size = 5 := by
  simp [toffoliOn]

@[simp] lemma toffoliOn_depth {m : ℕ} (c1 c2 tgt : Fin m)
    (h12 : c1 ≠ c2) (h1t : c1 ≠ tgt) (h2t : c2 ≠ tgt) :
    (toffoliOn c1 c2 tgt h12 h1t h2t).depth = 5 := by
  simp [toffoliOn]

lemma toffoliOn_usesOnly {m : ℕ} (c1 c2 tgt : Fin m)
    (h12 : c1 ≠ c2) (h1t : c1 ≠ tgt) (h2t : c2 ≠ tgt) :
    (toffoliOn c1 c2 tgt h12 h1t h2t).UsesOnly {c1, c2, tgt} := by
  have h3 : toffoli3.UsesOnly Finset.univ := fun _ _ _ _ _ => Finset.mem_univ _
  refine (LayeredCircuit.mapWires_usesOnly (wire3Emb c1 c2 tgt h12 h1t h2t) toffoli3 h3).mono ?_
  intro x hx
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with ⟨i, rfl⟩
  rcases (by fin_cases i <;> decide : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp

lemma act_toffoliOn_ket {m : ℕ} (c1 c2 tgt : Fin m)
    (h12 : c1 ≠ c2) (h1t : c1 ≠ tgt) (h2t : c2 ≠ tgt) (x : Qubits m) :
    act (toffoliOn c1 c2 tgt h12 h1t h2t).unitary (ket x) =
      ket (Function.update x tgt (xor (x tgt) (x c1 && x c2))) := by
  rw [toffoliOn, LayeredCircuit.mapWires_unitary, act_ket_eq, toffoli3_unitary]
  let x' := Function.update x tgt (xor (x tgt) (x c1 && x c2))
  rw [Finset.sum_eq_single x']
  · simp only [embedOp, Matrix.of_apply, toffoliMat, permMat]
    have hoff : ∀ a : Fin m, a ∉ Set.range (wire3Emb c1 c2 tgt h12 h1t h2t) → x' a = x a := by
      intro a ha
      have hat : a ≠ tgt := fun h => ha ⟨2, by simp [h]⟩
      exact Function.update_of_ne hat _ _
    rw [if_pos hoff]
    have heq : (x' ∘ wire3Emb c1 c2 tgt h12 h1t h2t) =
        ![(x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 0, (x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 1,
          xor ((x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 2)
            ((x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 0 && (x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 1)] := by
      funext i
      rcases (by fin_cases i <;> decide : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · change x' c1 = x c1; exact Function.update_of_ne h1t _ _
      · change x' c2 = x c2; exact Function.update_of_ne h2t _ _
      · change x' tgt = xor (x tgt) (x c1 && x c2); exact Function.update_self _ _ _
    rw [if_pos heq, one_smul]
  · intro y _ hy
    simp only [embedOp, Matrix.of_apply, toffoliMat, permMat]
    by_cases hoff : ∀ a : Fin m, a ∉ Set.range (wire3Emb c1 c2 tgt h12 h1t h2t) → y a = x a
    · rw [if_pos hoff]
      have hne : (y ∘ wire3Emb c1 c2 tgt h12 h1t h2t) ≠
          ![(x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 0, (x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 1,
            xor ((x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 2)
              ((x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 0 && (x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 1)] := by
        intro h
        apply hy
        funext a
        dsimp only [x']
        by_cases ha0 : a = c1
        · subst ha0; rw [Function.update_of_ne h1t]; simpa using congrFun h 0
        · by_cases ha1 : a = c2
          · subst ha1; rw [Function.update_of_ne h2t]; simpa using congrFun h 1
          · by_cases ha2 : a = tgt
            · subst ha2; rw [Function.update_self]; simpa using congrFun h 2
            · rw [Function.update_of_ne ha2]
              apply hoff a
              rintro ⟨i, rfl⟩
              rcases (by fin_cases i <;> decide : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
                simp at ha0 ha1 ha2
      rw [if_neg hne, zero_smul]
    · rw [if_neg hoff, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### 10. `Nat.clog 2` Helper Lemmas -/

lemma clog2_le_iff_le_pow {n k : ℕ} : Nat.clog 2 n ≤ k ↔ n ≤ 2 ^ k :=
  Nat.clog_le_iff_le_pow (by norm_num)

lemma clog2_rec {len : ℕ} (h : 2 ≤ len) :
    Nat.clog 2 ((len + 1) / 2) + 1 = Nat.clog 2 len := by
  apply le_antisymm
  · rw [← Nat.add_le_add_iff_right (n := 0), add_zero]
    have hlt : 0 < Nat.clog 2 len := by
      by_contra hz
      have h0 : Nat.clog 2 len = 0 := by omega
      have hle : len ≤ 2 ^ 0 := clog2_le_iff_le_pow.mp (le_of_eq h0)
      omega
    have hprev : len ≤ 2 ^ Nat.clog 2 len := Nat.le_pow_clog (by norm_num) len
    have hpow_eq : 2 ^ Nat.clog 2 len = 2 * 2 ^ (Nat.clog 2 len - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hlt, pow_succ']
    have hdiv_le : (len + 1) / 2 ≤ 2 ^ (Nat.clog 2 len - 1) := by omega
    have hclog_le : Nat.clog 2 ((len + 1) / 2) ≤ Nat.clog 2 len - 1 :=
      clog2_le_iff_le_pow.mpr hdiv_le
    omega
  · rw [clog2_le_iff_le_pow, pow_succ']
    have hdiv : (len + 1) / 2 ≤ 2 ^ Nat.clog 2 ((len + 1) / 2) :=
      Nat.le_pow_clog (by norm_num) _
    omega

lemma clog2_half_le {len : ℕ} : Nat.clog 2 (len / 2) ≤ Nat.clog 2 ((len + 1) / 2) :=
  Nat.clog_mono_right 2 (by omega)

lemma clog2_succ_le_real_log {n : ℕ} (hn : 1 ≤ n) :
    (Nat.clog 2 (n + 1) : ℝ) ≤ Real.log n / Real.log 2 + 1 := by
  set k := Nat.clog 2 (n + 1)
  have hk_pos : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have hle : n + 1 ≤ 2 ^ 0 := clog2_le_iff_le_pow.mp (le_of_eq hk0)
    omega
  have hlt : 2 ^ (k - 1) < n + 1 := by
    by_contra hge
    have hle : n + 1 ≤ 2 ^ (k - 1) := by omega
    have hck : k ≤ k - 1 := clog2_le_iff_le_pow.mpr hle
    omega
  have hpow_le : (2 : ℝ) ^ (k - 1) ≤ n := by exact_mod_cast (by omega : 2 ^ (k - 1) ≤ n)
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_le : Real.log ((2 : ℝ) ^ (k - 1)) ≤ Real.log n :=
    Real.log_le_log (by positivity) hpow_le
  rw [Real.log_pow] at hlog_le
  have hk_cast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk_pos, Nat.cast_one]
  rw [hk_cast] at hlog_le
  have hdiv : (k : ℝ) - 1 ≤ Real.log n / Real.log 2 := (le_div_iff₀ hlog2_pos).mpr hlog_le
  linarith

/-! ### 11. Parallel Hadamard Layer (`hadamardLayer`) & `ctrlHadamardN` -/

lemma hadamard_prod_eq_hadamardN {n : ℕ} (y z : Qubits n) :
    (∏ i : Fin n, hadamard (y i) (z i)) = hadamardN n y z := by
  have h00 : (false + false : Bool) = false := by decide
  have h01 : (false + true : Bool) = true := by decide
  have h10 : (true + false : Bool) = true := by decide
  have h11 : (true + true : Bool) = false := by decide
  have hprod_sign : ∀ s : Finset (Fin n),
      (∏ i ∈ s, (if y i && z i then (-1 : ℂ) else 1)) =
        if (∑ i ∈ s, (z i && y i)) then (-1 : ℂ) else 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
      have hcomm : (y a && z a) = (z a && y a) := Bool.and_comm _ _
      rw [hcomm]
      cases (z a && y a) <;> cases (∑ i ∈ s, (z i && y i)) <;> simp [h00, h01, h10, h11]
  have hsplit : ∀ i : Fin n,
      hadamard (y i) (z i) = ((Real.sqrt 2)⁻¹ : ℂ) * (if y i && z i then (-1 : ℂ) else 1) := by
    intro i
    simp only [hadamard, Matrix.of_apply]
    split_ifs <;> ring
  simp_rw [hsplit, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    hprod_sign Finset.univ]
  simp only [hadamardN, Matrix.of_apply]
  change (((Real.sqrt 2)⁻¹ : ℂ) ^ n) * (if dotBits z y then (-1 : ℂ) else 1) = _
  have hpow : (((Real.sqrt 2)⁻¹ : ℂ) ^ n) = (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hpow]
  cases dotBits z y <;> simp

private lemma circuit_prod_gate1_of_nodup {m : ℕ}
    (L : List (Fin m)) (hL : L.Nodup) (U : Fin m → Matrix Bool Bool ℂ)
    (hU : ∀ w, U w ∈ Matrix.unitaryGroup Bool ℂ) (y z : Qubits m) :
    Circuit.unitary (L.map fun w => gate1App (U w) (hU w) w) y z =
      if (∀ q : Fin m, q ∉ L → y q = z q) then ∏ w ∈ L.toFinset, U w (y w) (z w) else 0 := by
  classical
  induction L generalizing y z with
  | nil =>
    simp only [List.map_nil, circuit_unitary_nil, Matrix.one_apply, List.not_mem_nil,
      not_false_eq_true, forall_true_left, List.toFinset_nil, Finset.prod_empty]
    by_cases h : y = z
    · subst h; rw [if_pos rfl, if_pos (fun _ => rfl)]
    · rw [if_neg h]
      have hne : ¬ ∀ q : Fin m, y q = z q := fun hq => h (funext hq)
      rw [if_neg hne]
  | cons a rest ih =>
    rw [List.nodup_cons] at hL
    simp only [List.map_cons, circuit_unitary_cons, Matrix.mul_apply]
    have hih := ih hL.2
    let x₀ : Qubits m := Function.update z a (y a)
    have hx₀_single : (∑ x : Qubits m,
        Circuit.unitary (rest.map fun w => gate1App (U w) (hU w) w) y x *
          embedOp (gate1App (U a) (hU a) a).gate.mat (gate1App (U a) (hU a) a).wires x z) =
        Circuit.unitary (rest.map fun w => gate1App (U w) (hU w) w) y x₀ *
          embedOp (gate1App (U a) (hU a) a).gate.mat (gate1App (U a) (hU a) a).wires x₀ z := by
      rw [Finset.sum_eq_single x₀]
      · intro x _ hx
        rw [embedOp_gate1App_entry]
        by_cases hoff : ∀ q : Fin m, q ≠ a → x q = z q
        · rw [if_pos hoff]
          by_cases hxa : x a = y a
          · exfalso; apply hx
            funext q
            by_cases hqa : q = a
            · subst hqa; simp [x₀, hxa]
            · simp [x₀, Function.update_of_ne hqa, hoff q hqa]
          · rw [hih y x]
            have hnot : ¬ ∀ q : Fin m, q ∉ rest → y q = x q := fun h => hxa (h a hL.1).symm
            rw [if_neg hnot, zero_mul]
        · rw [if_neg hoff, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hx₀_single, hih y x₀, embedOp_gate1App_entry]
    have hx₀_off : ∀ q : Fin m, q ≠ a → x₀ q = z q := fun q hq => Function.update_of_ne hq _ _
    rw [if_pos hx₀_off, show x₀ a = y a from Function.update_self _ _ _]
    have hiff : (∀ q : Fin m, q ∉ rest → y q = x₀ q) ↔ (∀ q : Fin m, q ∉ a :: rest → y q = z q) := by
      constructor
      · intro h q hq
        have hqa : q ≠ a := fun heq => hq (by simp [heq])
        have hqr : q ∉ rest := fun hr => hq (by simp [hr])
        rw [h q hqr, hx₀_off q hqa]
      · intro h q hqr
        by_cases hqa : q = a
        · subst hqa; simp [x₀]
        · have hq : q ∉ a :: rest := by simp [hqa, hqr]
          rw [h q hq, hx₀_off q hqa]
    by_cases hcond : ∀ q : Fin m, q ∉ a :: rest → y q = z q
    · rw [if_pos (hiff.mpr hcond), if_pos hcond, List.toFinset_cons]
      have ha_mem : a ∉ rest.toFinset := by simpa using hL.1
      rw [Finset.prod_insert ha_mem, mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun w hw => ?_
      have hwa : w ≠ a := by
        intro heq; subst heq; exact ha_mem hw
      rw [hx₀_off w hwa]
    · rw [if_neg (mt hiff.mp hcond), if_neg hcond, zero_mul]

noncomputable def hadamardLayer (n : ℕ) : LayeredCircuit n :=
  LayeredCircuit.ofLayer ((List.finRange n).map hadamardApp) (by
    dsimp only [LayerDisjoint]
    rw [List.pairwise_map]
    refine (List.nodup_iff_pairwise_ne.mp (List.nodup_finRange n)).imp fun {i j} hij => ?_
    rw [Set.disjoint_left]
    rintro w ⟨a, rfl⟩ ⟨b, hb⟩
    exact hij (hb.symm))

lemma hadamardLayer_size (n : ℕ) : (hadamardLayer n).size = n := by
  simp [hadamardLayer, LayeredCircuit.ofLayer_size]

lemma hadamardLayer_depth (n : ℕ) : (hadamardLayer n).depth ≤ 1 :=
  LayeredCircuit.ofLayer_depth _ _

lemma hadamardLayer_unitary (n : ℕ) : (hadamardLayer n).unitary = hadamardN n := by
  rw [hadamardLayer, LayeredCircuit.ofLayer_unitary]
  ext y z
  have h := circuit_prod_gate1_of_nodup (List.finRange n) (List.nodup_finRange n)
    (fun _ => hadamard) (fun _ => hadamard_mem_unitaryGroup) y z
  have heq : (List.finRange n).map hadamardApp =
      (List.finRange n).map (fun w => gate1App hadamard hadamard_mem_unitaryGroup w) := rfl
  rw [heq, h]
  have hall : ∀ q : Fin n, q ∉ List.finRange n → y q = z q := fun q hq =>
    absurd (List.mem_finRange q) hq
  rw [if_pos hall]
  have hfin : (List.finRange n).toFinset = Finset.univ := by
    ext i; simp
  rw [hfin]
  exact hadamard_prod_eq_hadamardN y z

/-! ### 12. Balanced CNOT Fanout & `ctrlHadamardN` -/

private def ancSlice {m : ℕ} (base lo len : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun w => base + lo ≤ w.1 ∧ w.1 < base + lo + len

private lemma ancSlice_disjoint {m : ℕ} (base lo mid len : ℕ) :
    Disjoint (ancSlice (m := m) base lo mid) (ancSlice (m := m) base (lo + mid) (len - mid)) := by
  rw [Finset.disjoint_left]
  intro w h1 h2
  simp only [ancSlice, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  omega

private lemma ancSlice_union_sub {m : ℕ} (base lo mid len : ℕ) (hmid : mid ≤ len) :
    ancSlice (m := m) base lo mid ∪ ancSlice (m := m) base (lo + mid) (len - mid) ⊆
      ancSlice (m := m) base lo len := by
  intro w hw
  simp only [Finset.mem_union, ancSlice, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  omega

private def fanoutRange (n lo len : ℕ) (_hlen : 1 ≤ len) (hb : lo + len ≤ n) :
    { lc : LayeredCircuit (1 + n + n) // lc.UsesOnly (ancSlice (1 + n) lo len) } :=
  if h2 : len < 2 then
    ⟨LayeredCircuit.id (1 + n + n), LayeredCircuit.id_usesOnly _⟩
  else
    let mid := len / 2
    have hmid1 : 1 ≤ mid := by omega
    have hrem1 : 1 ≤ len - mid := by omega
    have hbL : lo + mid ≤ n := by omega
    have hbR : lo + mid + (len - mid) ≤ n := by omega
    let L := fanoutRange n lo mid hmid1 hbL
    let R := fanoutRange n (lo + mid) (len - mid) hrem1 hbR
    let wL : Fin (1 + n + n) := ⟨1 + n + lo, by omega⟩
    let wR : Fin (1 + n + n) := ⟨1 + n + (lo + mid), by omega⟩
    have hne : wL ≠ wR := by
      intro h; have := congrArg Fin.val h; dsimp [wL, wR] at this; omega
    let step := cnotGate wL wR hne
    let merged := LayeredCircuit.parMerge L.1 R.1 L.2 R.2 (ancSlice_disjoint (1 + n) lo mid len)
    ⟨step.seq merged,
      LayeredCircuit.seq_usesOnly
        ((cnotGate_usesOnly wL wR hne).mono (by
          intro w hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · simp [ancSlice, wL]; omega
          · simp [ancSlice, wR]; omega))
        ((LayeredCircuit.parMerge_usesOnly L.1 R.1 L.2 R.2 _).mono
          (ancSlice_union_sub (1 + n) lo mid len (by omega)))⟩
termination_by len

private lemma fanoutRange_size (n lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ n) :
    (fanoutRange n lo len hlen hb).1.size = len - 1 := by
  induction len using Nat.strong_induction_on generalizing lo with
  | h len ih =>
    unfold fanoutRange
    split_ifs with h2
    · simp; omega
    · dsimp only
      have hsL := ih (len / 2) (by omega) lo (by omega) (by omega)
      have hsR := ih (len - len / 2) (by omega) (lo + len / 2) (by omega) (by omega)
      simp only [LayeredCircuit.seq_size, LayeredCircuit.parMerge_size, cnotGate_size]
      rw [hsL, hsR]
      omega

private lemma fanoutRange_depth (n lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ n) :
    (fanoutRange n lo len hlen hb).1.depth ≤ Nat.clog 2 len := by
  induction len using Nat.strong_induction_on generalizing lo with
  | h len ih =>
    unfold fanoutRange
    split_ifs with h2
    · simp
    · dsimp only
      have hlen2 : 2 ≤ len := by omega
      have hdL := ih (len / 2) (by omega) lo (by omega) (by omega)
      have hdR := ih (len - len / 2) (by omega) (lo + len / 2) (by omega) (by omega)
      have hL_le : (fanoutRange n lo (len / 2) (by omega) (by omega)).1.depth ≤
          Nat.clog 2 ((len + 1) / 2) :=
        le_trans hdL clog2_half_le
      have hclog_sub : Nat.clog 2 (len - len / 2) = Nat.clog 2 ((len + 1) / 2) := by
        congr 1; omega
      have hR_le : (fanoutRange n (lo + len / 2) (len - len / 2) (by omega) (by omega)).1.depth ≤
          Nat.clog 2 ((len + 1) / 2) := hclog_sub ▸ hdR
      simp only [LayeredCircuit.seq_depth, LayeredCircuit.parMerge_depth, cnotGate_depth]
      rw [← clog2_rec hlen2, Nat.add_comm 1]
      exact Nat.add_le_add_right (max_le hL_le hR_le) 1

private lemma act_fanoutRange_ket (n lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ n)
    (c : Bool) (x : Qubits (1 + n + n))
    (hroot : x ⟨1 + n + lo, by omega⟩ = c)
    (hclean : ∀ k : ℕ, lo < k → ∀ (_hk2 : k < lo + len), x ⟨1 + n + k, by omega⟩ = false) :
    act (fanoutRange n lo len hlen hb).1.unitary (ket x) =
      ket (fun w => if 1 + n + lo ≤ w.1 ∧ w.1 < 1 + n + lo + len then c else x w) := by
  induction len using Nat.strong_induction_on generalizing lo x with
  | h len ih =>
    unfold fanoutRange
    split_ifs with h2
    · have hlen1 : len = 1 := by omega
      subst hlen1
      simp only [LayeredCircuit.id_unitary, act_one]
      congr 1
      funext w
      split_ifs with hw
      · have hw_eq : w = ⟨1 + n + lo, by omega⟩ := Fin.ext (by simp; omega)
        rw [hw_eq, hroot]
      · rfl
    · dsimp only
      set mid := len / 2
      have hmid1 : 1 ≤ mid := by omega
      have hrem1 : 1 ≤ len - mid := by omega
      have hmid_lt : mid < len := by omega
      have hrem_lt : len - mid < len := by omega
      have hbL : lo + mid ≤ n := by omega
      have hbR : lo + mid + (len - mid) ≤ n := by omega
      let wL : Fin (1 + n + n) := ⟨1 + n + lo, by omega⟩
      let wR : Fin (1 + n + n) := ⟨1 + n + (lo + mid), by omega⟩
      have hne : wL ≠ wR := by
        intro h; have := congrArg Fin.val h; dsimp [wL, wR] at this; omega
      simp only [LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket,
        LayeredCircuit.parMerge_unitary]
      let x1 : Qubits (1 + n + n) := Function.update x wR (xor (x wR) (x wL))
      have hx1_wL : x1 wL = c := by
        dsimp only [x1]
        rw [Function.update_of_ne hne, hroot]
      have hx1_wR : x1 wR = c := by
        have hzero : x wR = false := hclean (lo + mid) (by omega) (by omega)
        dsimp only [x1]
        rw [Function.update_self, hzero]
        change xor false (x ⟨1 + n + lo, by omega⟩) = c
        rw [hroot, Bool.false_xor]
      have hx1_cleanL : ∀ k : ℕ, lo < k → ∀ (_hk2 : k < lo + mid), x1 ⟨1 + n + k, by omega⟩ = false := by
        intro k hk1 hk2
        have hneR : (⟨1 + n + k, by omega⟩ : Fin (1 + n + n)) ≠ wR := by
          intro h; have := congrArg Fin.val h; dsimp [wR] at this; omega
        dsimp only [x1]
        rw [Function.update_of_ne hneR]
        exact hclean k hk1 (by omega)
      have hx1_cleanR : ∀ k : ℕ, lo + mid < k → ∀ (_hk2 : k < lo + mid + (len - mid)),
          x1 ⟨1 + n + k, by omega⟩ = false := by
        intro k hk1 hk2
        have hneR : (⟨1 + n + k, by omega⟩ : Fin (1 + n + n)) ≠ wR := by
          intro h; have := congrArg Fin.val h; dsimp [wR] at this; omega
        dsimp only [x1]
        rw [Function.update_of_ne hneR]
        exact hclean k (by omega) (by omega)
      have hL_act := ih mid hmid_lt lo hmid1 hbL x1 hx1_wL hx1_cleanL
      let x2 : Qubits (1 + n + n) := fun w =>
        if 1 + n + lo ≤ w.1 ∧ w.1 < 1 + n + lo + mid then c else x1 w
      have hL_act' : act (fanoutRange n lo mid hmid1 hbL).1.unitary (ket x1) = ket x2 := hL_act
      rw [hL_act']
      have hx2_wR : x2 wR = c := by
        have hnot : ¬ (1 + n + lo ≤ wR.1 ∧ wR.1 < 1 + n + lo + mid) := by
          dsimp [wR]; omega
        dsimp only [x2]
        rw [if_neg hnot, hx1_wR]
      have hx2_cleanR : ∀ k : ℕ, lo + mid < k → ∀ (_hk2 : k < lo + mid + (len - mid)),
          x2 ⟨1 + n + k, by omega⟩ = false := by
        intro k hk1 hk2
        have hnot : ¬ (1 + n + lo ≤ 1 + n + k ∧ 1 + n + k < 1 + n + lo + mid) := by omega
        dsimp only [x2]
        rw [if_neg hnot]
        exact hx1_cleanR k hk1 hk2
      have hR_act := ih (len - mid) hrem_lt (lo + mid) hrem1 hbR x2 hx2_wR hx2_cleanR
      rw [hR_act]
      congr 1
      funext w
      dsimp only [x2, x1]
      by_cases hwR : 1 + n + (lo + mid) ≤ w.1 ∧ w.1 < 1 + n + (lo + mid) + (len - mid)
      · rw [if_pos hwR, if_pos (by omega)]
      · rw [if_neg hwR]
        by_cases hwL : 1 + n + lo ≤ w.1 ∧ w.1 < 1 + n + lo + mid
        · rw [if_pos hwL, if_pos (by omega)]
        · rw [if_neg hwL, if_neg (by omega)]
          have hneR : w ≠ wR := by
            intro h; apply hwR; rw [h]; dsimp [wR]; omega
          rw [Function.update_of_ne hneR]

private def fanoutTree (n : ℕ) (hn : 1 ≤ n) :
    { lc : LayeredCircuit (1 + n + n) //
      lc.UsesOnly ({0} ∪ ancSlice (1 + n) 0 n) ∧ lc.size = n ∧ lc.depth ≤ Nat.clog 2 n + 1 } :=
  let w0 : Fin (1 + n + n) := ⟨0, by omega⟩
  let a0 : Fin (1 + n + n) := ⟨1 + n, by omega⟩
  have hne : w0 ≠ a0 := by intro h; have := congrArg Fin.val h; dsimp [w0, a0] at this; omega
  let step0 := cnotGate w0 a0 hne
  let tree := fanoutRange n 0 n hn (by omega)
  ⟨step0.seq tree.1,
    LayeredCircuit.seq_usesOnly
      ((cnotGate_usesOnly w0 a0 hne).mono (by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
          ancSlice, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        rcases hw with rfl | rfl
        · left; exact Fin.ext rfl
        · right; dsimp [a0]; omega))
      (tree.2.mono Finset.subset_union_right),
    by simp only [step0, tree, LayeredCircuit.seq_size, cnotGate_size,
         fanoutRange_size n 0 n hn (by omega)]
       omega,
    by simp only [step0, tree, LayeredCircuit.seq_depth, cnotGate_depth]
       have hd := fanoutRange_depth n 0 n hn (by omega)
       omega⟩

private lemma act_fanoutTree_ket (n : ℕ) (hn : 1 ≤ n) (x : Qubits (1 + n + n))
    (hclean : ∀ j : Fin n, x ⟨1 + n + j.1, by have := j.isLt; omega⟩ = false) :
    act (fanoutTree n hn).1.unitary (ket x) =
      ket (fun w => if 1 + n ≤ w.1 then x 0 else x w) := by
  dsimp only [fanoutTree]
  simp only [LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket]
  let a0 : Fin (1 + n + n) := ⟨1 + n, by omega⟩
  let x1 : Qubits (1 + n + n) := Function.update x a0 (xor (x a0) (x ⟨0, by omega⟩))
  have hx1_a0 : x1 a0 = x 0 := by
    have h0 := hclean ⟨0, hn⟩
    dsimp only [x1]
    rw [Function.update_self]
    change xor (x ⟨1 + n, by omega⟩) (x 0) = x 0
    have h0' : x ⟨1 + n, by omega⟩ = false := h0
    rw [h0', Bool.false_xor]
  have hx1_clean : ∀ k : ℕ, 0 < k → ∀ (_hk2 : k < 0 + n), x1 ⟨1 + n + k, by omega⟩ = false := by
    intro k hk1 hk2
    have hne : (⟨1 + n + k, by omega⟩ : Fin (1 + n + n)) ≠ a0 := by
      intro h; have := congrArg Fin.val h; dsimp [a0] at this; omega
    dsimp only [x1]
    rw [Function.update_of_ne hne]
    exact hclean ⟨k, by omega⟩
  rw [act_fanoutRange_ket n 0 n hn (by omega) (x 0) x1 hx1_a0 hx1_clean]
  congr 1
  funext w
  have hw_iff : (1 + n + 0 ≤ w.1 ∧ w.1 < 1 + n + 0 + n) ↔ 1 + n ≤ w.1 := by
    have := w.isLt; constructor <;> intro <;> omega
  by_cases hw : 1 + n ≤ w.1
  · rw [if_pos (hw_iff.mpr hw), if_pos hw]
  · have hne : w ≠ a0 := fun h => hw (by rw [h])
    rw [if_neg (mt hw_iff.mp hw), if_neg hw]
    dsimp only [x1]
    rw [Function.update_of_ne hne]

private def ctrlHTgtWire (n : ℕ) (i : Fin n) : Fin (1 + n + n) :=
  ⟨1 + i.1, by have := i.isLt; omega⟩

private def ctrlHAncWire (n : ℕ) (i : Fin n) : Fin (1 + n + n) :=
  ⟨1 + n + i.1, by have := i.isLt; omega⟩

private lemma ctrlHAncWire_ne_tgtWire (n : ℕ) (i : Fin n) :
    ctrlHAncWire n i ≠ ctrlHTgtWire n i := by
  intro h; have := congrArg Fin.val h; dsimp [ctrlHAncWire, ctrlHTgtWire] at this; omega

private noncomputable def ctrlHApp (n : ℕ) (i : Fin n) : GateApp gates12 (1 + n + n) :=
  ctrlGate1App hadamard hadamard_mem_unitaryGroup
    (ctrlHAncWire n i) (ctrlHTgtWire n i) (ctrlHAncWire_ne_tgtWire n i)

private lemma ctrlHLayer_entry (n : ℕ) (L : List (Fin n)) (hL : L.Nodup)
    (y z : Qubits (1 + n + n)) :
    Circuit.unitary (L.map (ctrlHApp n)) y z =
      if (∀ w : Fin (1 + n + n), (∀ i ∈ L, w ≠ ctrlHTgtWire n i) → y w = z w) then
        ∏ i ∈ L.toFinset,
          (if z (ctrlHAncWire n i) then hadamard (y (ctrlHTgtWire n i)) (z (ctrlHTgtWire n i))
          else if y (ctrlHTgtWire n i) = z (ctrlHTgtWire n i) then 1 else 0)
      else 0 := by
  classical
  induction L generalizing y z with
  | nil =>
    simp only [List.map_nil, circuit_unitary_nil, Matrix.one_apply, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, true_implies, List.toFinset_nil, Finset.prod_empty]
    by_cases h : y = z
    · subst h; rw [if_pos rfl, if_pos (fun _ => rfl)]
    · rw [if_neg h]
      have hne : ¬ ∀ w : Fin (1 + n + n), y w = z w := fun hw => h (funext hw)
      rw [if_neg hne]
  | cons a rest ih =>
    rw [List.nodup_cons] at hL
    simp only [List.map_cons, circuit_unitary_cons, Matrix.mul_apply]
    have hih := ih hL.2
    let ancA := ctrlHAncWire n a
    let tgtA := ctrlHTgtWire n a
    have hneA := ctrlHAncWire_ne_tgtWire n a
    let x₀ : Qubits (1 + n + n) := Function.update z tgtA (y tgtA)
    have hx₀_single : (∑ x : Qubits (1 + n + n),
        Circuit.unitary (rest.map (ctrlHApp n)) y x *
          embedOp (ctrlHApp n a).gate.mat (ctrlHApp n a).wires x z) =
        Circuit.unitary (rest.map (ctrlHApp n)) y x₀ *
          embedOp (ctrlHApp n a).gate.mat (ctrlHApp n a).wires x₀ z := by
      rw [Finset.sum_eq_single x₀]
      · intro x _ hx
        dsimp only [ctrlHApp, ctrlGate1App]
        rw [embedOp_gate2App_entry]
        by_cases hoff : ∀ q : Fin (1 + n + n), q ≠ ancA → q ≠ tgtA → x q = z q
        · rw [if_pos hoff]
          by_cases hxa : x ancA = z ancA
          · by_cases hxta : x tgtA = y tgtA
            · exfalso; apply hx
              funext q
              by_cases hqt : q = tgtA
              · subst hqt; simp [x₀, hxta]
              · by_cases hqa : q = ancA
                · subst hqa; dsimp [x₀]; rw [Function.update_of_ne hneA, hxa]
                · simp [x₀, Function.update_of_ne hqt, hoff q hqa hqt]
            · rw [hih y x]
              have hnot : ¬ ∀ w : Fin (1 + n + n),
                  (∀ i ∈ rest, w ≠ ctrlHTgtWire n i) → y w = x w := by
                intro h
                apply hxta
                refine (h tgtA ?_).symm
                intro i hi heq
                have hv := congrArg Fin.val heq
                dsimp [tgtA, ctrlHTgtWire] at hv
                exact hL.1 (by convert hi using 2; exact Fin.ext (by omega))
              rw [if_neg hnot, zero_mul]
          · dsimp only [controlled, Matrix.of_apply]
            rw [if_neg hxa, mul_zero]
        · rw [if_neg hoff, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hx₀_single, hih y x₀]
    dsimp only [ctrlHApp, ctrlGate1App]
    rw [embedOp_gate2App_entry]
    have hx₀_off : ∀ q : Fin (1 + n + n), q ≠ ancA → q ≠ tgtA → x₀ q = z q :=
      fun q _ hqt => Function.update_of_ne hqt _ _
    rw [if_pos hx₀_off]
    have hx₀_anc : x₀ ancA = z ancA := Function.update_of_ne hneA _ _
    have hx₀_tgt : x₀ tgtA = y tgtA := Function.update_self _ _ _
    dsimp only [controlled, Matrix.of_apply]
    rw [if_pos hx₀_anc, hx₀_anc, hx₀_tgt]
    simp only [Matrix.one_apply]
    have hiff : (∀ w : Fin (1 + n + n), (∀ i ∈ rest, w ≠ ctrlHTgtWire n i) → y w = x₀ w) ↔
        (∀ w : Fin (1 + n + n), (∀ i ∈ a :: rest, w ≠ ctrlHTgtWire n i) → y w = z w) := by
      constructor
      · intro h w hw
        have hwt : w ≠ tgtA := fun heq => hw a List.mem_cons_self heq
        have hwr : ∀ i ∈ rest, w ≠ ctrlHTgtWire n i := fun i hi =>
          hw i (List.mem_cons_of_mem _ hi)
        rw [h w hwr]
        dsimp only [x₀]
        exact Function.update_of_ne hwt _ _
      · intro h w hwr
        by_cases hwt : w = tgtA
        · subst hwt; simp [x₀]
        · have hw : ∀ i ∈ a :: rest, w ≠ ctrlHTgtWire n i := by
            intro i hi
            rcases List.mem_cons.mp hi with rfl | hr
            · exact hwt
            · exact hwr i hr
          rw [h w hw]
          dsimp only [x₀]
          exact (Function.update_of_ne hwt _ _).symm
    by_cases hcond : ∀ w : Fin (1 + n + n), (∀ i ∈ a :: rest, w ≠ ctrlHTgtWire n i) → y w = z w
    · rw [if_pos (hiff.mpr hcond), if_pos hcond, List.toFinset_cons]
      have ha_mem : a ∉ rest.toFinset := by simpa using hL.1
      rw [Finset.prod_insert ha_mem, mul_comm]
      have hprod_rest : (∏ i ∈ rest.toFinset,
            (if x₀ (ctrlHAncWire n i) then hadamard (y (ctrlHTgtWire n i)) (x₀ (ctrlHTgtWire n i))
             else if y (ctrlHTgtWire n i) = x₀ (ctrlHTgtWire n i) then 1 else 0)) =
          (∏ i ∈ rest.toFinset,
            (if z (ctrlHAncWire n i) then hadamard (y (ctrlHTgtWire n i)) (z (ctrlHTgtWire n i))
             else if y (ctrlHTgtWire n i) = z (ctrlHTgtWire n i) then 1 else 0)) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hia : i ≠ a := by intro heq; subst heq; exact ha_mem hi
        have hanc_ne : ctrlHAncWire n i ≠ tgtA := by
          intro h; have := congrArg Fin.val h
          dsimp [ctrlHAncWire, tgtA, ctrlHTgtWire] at this
          have := i.isLt; have := a.isLt; omega
        have htgt_ne : ctrlHTgtWire n i ≠ tgtA := by
          intro h; have := congrArg Fin.val h
          dsimp [ctrlHTgtWire, tgtA] at this
          exact hia (Fin.ext (by omega))
        dsimp only [x₀]
        simp_rw [Function.update_of_ne hanc_ne, Function.update_of_ne htgt_ne]
      rw [hprod_rest]
    · rw [if_neg (mt hiff.mp hcond), if_neg hcond, zero_mul]

private lemma ctrlHLayer_disjoint (n : ℕ) :
    LayerDisjoint ((List.finRange n).map (ctrlHApp n)) := by
  dsimp only [LayerDisjoint]
  rw [List.pairwise_map]
  refine (List.nodup_iff_pairwise_ne.mp (List.nodup_finRange n)).imp fun {i j} hij => ?_
  rw [Set.disjoint_left]
  rintro w ⟨a, rfl⟩ ⟨b, hb⟩
  dsimp only [ctrlHApp, ctrlGate1App, gate2App, Gate.ofMatrix2] at a b hb ⊢
  have hi := i.isLt
  have hj := j.isLt
  have hval := congrArg Fin.val hb.symm
  rcases (by fin_cases a <;> decide : a = 0 ∨ a = 1) with rfl | rfl <;>
    rcases (by fin_cases b <;> decide : b = 0 ∨ b = 1) with rfl | rfl
  · change 1 + n + i.1 = 1 + n + j.1 at hval; exact hij (Fin.ext (by omega))
  · change 1 + n + i.1 = 1 + j.1 at hval; omega
  · change 1 + i.1 = 1 + n + j.1 at hval; omega
  · change 1 + i.1 = 1 + j.1 at hval; exact hij (Fin.ext (by omega))

noncomputable def ctrlHadamardMat (n : ℕ) : Matrix (Qubits (1 + n)) (Qubits (1 + n)) ℂ :=
  Matrix.of fun y z =>
    controlledQubits (hadamardN n)
      (fun i : Fin (n + 1) => y (i.cast (Nat.add_comm n 1)))
      (fun i : Fin (n + 1) => z (i.cast (Nat.add_comm n 1)))

noncomputable def ctrlHadamardN (n : ℕ) : LayeredCircuit (1 + n + n) :=
  if hn : 1 ≤ n then
    let fan := fanoutTree n hn
    let hLayer := LayeredCircuit.ofLayer ((List.finRange n).map (ctrlHApp n)) (ctrlHLayer_disjoint n)
    fan.1.seq (hLayer.seq fan.1.adj)
  else
    LayeredCircuit.id (1 + n + n)

lemma ctrlHadamardN_size (n : ℕ) : (ctrlHadamardN n).size ≤ 3 * n := by
  unfold ctrlHadamardN
  split_ifs with hn
  · simp only [LayeredCircuit.seq_size, LayeredCircuit.adj_size, LayeredCircuit.ofLayer_size,
      List.length_map, List.length_finRange]
    have hfan := (fanoutTree n hn).2.2.1
    omega
  · simp

lemma ctrlHadamardN_depth (n : ℕ) : (ctrlHadamardN n).depth ≤ 2 * Nat.clog 2 (n + 1) + 3 := by
  unfold ctrlHadamardN
  split_ifs with hn
  · simp only [LayeredCircuit.seq_depth, LayeredCircuit.adj_depth]
    have hfan : (fanoutTree n hn).1.depth ≤ Nat.clog 2 n + 1 := (fanoutTree n hn).2.2.2
    have hclog : Nat.clog 2 n ≤ Nat.clog 2 (n + 1) := Nat.clog_mono_right 2 (by omega)
    have hlay := LayeredCircuit.ofLayer_depth ((List.finRange n).map (ctrlHApp n))
      (ctrlHLayer_disjoint n)
    omega
  · simp

lemma ctrlHadamardN_depth_real (n : ℕ) (hn : 2 ≤ n) :
    ((ctrlHadamardN n).depth : ℝ) ≤ (7 / Real.log 2) * Real.log n := by
  have h1 : 1 ≤ n := by omega
  have hd : ((ctrlHadamardN n).depth : ℝ) ≤ 2 * (Nat.clog 2 (n + 1) : ℝ) + 3 := by
    exact_mod_cast ctrlHadamardN_depth n
  have hclog := clog2_succ_le_real_log h1
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_ge : 1 ≤ Real.log n / Real.log 2 := by
    rw [one_le_div hlog2_pos]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  calc ((ctrlHadamardN n).depth : ℝ)
      ≤ 2 * (Real.log n / Real.log 2 + 1) + 3 := by linarith
    _ = 2 * (Real.log n / Real.log 2) + 5 := by ring
    _ ≤ 2 * (Real.log n / Real.log 2) + 5 * (Real.log n / Real.log 2) := by linarith
    _ = (7 / Real.log 2) * Real.log n := by ring

theorem ctrlHadamardN_implements (n : ℕ) :
    (ctrlHadamardN n).ImplementsOnClean (ctrlHadamardMat n) := by
  intro y z hz
  by_cases hn : 1 ≤ n
  · simp only [ctrlHadamardN, dif_pos hn]
    let fan := fanoutTree n hn
    let hLayer := LayeredCircuit.ofLayer ((List.finRange n).map (ctrlHApp n)) (ctrlHLayer_disjoint n)
    let withTgt : Qubits (1 + n + n) → Qubits n → Qubits (1 + n + n) := fun x t w =>
      if h : 1 ≤ w.1 ∧ w.1 < 1 + n then t ⟨w.1 - 1, by omega⟩ else x w
    let fanZ : Qubits (1 + n + n) → Qubits (1 + n + n) := fun x w =>
      if 1 + n ≤ w.1 then x 0 else x w
    let tgtPart : Qubits (1 + n + n) → Qubits n := fun x i => x (ctrlHTgtWire n i)
    have hfan_z : act fan.1.unitary (ket z) = ket (fanZ z) :=
      act_fanoutTree_ket n hn z fun j => hz j
    have hmid : act hLayer.unitary (ket (fanZ z)) =
        ∑ t : Qubits n,
          (if z 0 then hadamardN n t (tgtPart z) else if t = tgtPart z then 1 else 0) •
            ket (withTgt (fanZ z) t) := by
      rw [act_ket_eq]
      have hsum : (∑ w : Qubits (1 + n + n), hLayer.unitary w (fanZ z) • ket w) =
          ∑ w ∈ Finset.univ.image (withTgt (fanZ z)), hLayer.unitary w (fanZ z) • ket w := by
        rw [← Finset.sum_subset (Finset.subset_univ _)]
        intro w _ hw
        rw [LayeredCircuit.ofLayer_unitary, ctrlHLayer_entry n (List.finRange n) (List.nodup_finRange n)]
        by_cases hoff : ∀ q : Fin (1 + n + n), (∀ i ∈ List.finRange n, q ≠ ctrlHTgtWire n i) →
            w q = fanZ z q
        · exfalso; apply hw
          rw [Finset.mem_image]
          refine ⟨tgtPart w, Finset.mem_univ _, ?_⟩
          funext q
          dsimp only [withTgt, tgtPart, ctrlHTgtWire]
          split_ifs with hq
          · congr 1; apply Fin.ext; simp; omega
          · refine (hoff q ?_).symm
            intro i _ heq
            have hv := congrArg Fin.val heq
            dsimp [ctrlHTgtWire] at hv
            omega
        · rw [if_neg hoff, zero_smul]
      rw [hsum, Finset.sum_image]
      · refine Finset.sum_congr rfl fun t _ => ?_
        rw [LayeredCircuit.ofLayer_unitary, ctrlHLayer_entry n (List.finRange n) (List.nodup_finRange n)]
        have hoff : ∀ q : Fin (1 + n + n), (∀ i ∈ List.finRange n, q ≠ ctrlHTgtWire n i) →
            withTgt (fanZ z) t q = fanZ z q := by
          intro q hq
          dsimp only [withTgt]
          split_ifs with hq'
          · exfalso
            exact hq ⟨q.1 - 1, by omega⟩ (List.mem_finRange _)
              (Fin.ext (by dsimp [ctrlHTgtWire]; omega))
          · rfl
        rw [if_pos hoff]
        have hfin : (List.finRange n).toFinset = Finset.univ := by ext i; simp
        rw [hfin]
        have hfan_anc : ∀ i : Fin n, fanZ z (ctrlHAncWire n i) = z 0 := fun i => by
          dsimp only [fanZ, ctrlHAncWire]; rw [if_pos (by omega)]
        have hwt_tgt : ∀ i : Fin n, withTgt (fanZ z) t (ctrlHTgtWire n i) = t i := fun i => by
          dsimp only [withTgt, ctrlHTgtWire]
          have hi := i.isLt
          rw [dif_pos (by omega)]
          congr 1; exact Fin.ext (by simp)
        have hfz_tgt : ∀ i : Fin n, fanZ z (ctrlHTgtWire n i) = tgtPart z i := fun i => by
          dsimp only [fanZ, tgtPart, ctrlHTgtWire]
          have hi := i.isLt
          rw [if_neg (by omega)]
        simp_rw [hfan_anc, hwt_tgt, hfz_tgt]
        congr 1
        cases hz0 : z 0
        · simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases ht : t = tgtPart z
          · subst ht; simp
          · simp only [ht, ↓reduceIte]
            have hex : ∃ i : Fin n, t i ≠ tgtPart z i := by
              by_contra h; apply ht; funext i; by_contra hi; exact h ⟨i, hi⟩
            rcases hex with ⟨i₀, hi₀⟩
            exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀])
        · simp only [↓reduceIte, hadamard_prod_eq_hadamardN]
      · intro t1 _ t2 _ ht
        funext i
        have hi := congrFun ht (ctrlHTgtWire n i)
        dsimp only [withTgt, ctrlHTgtWire] at hi
        have his := i.isLt
        rw [dif_pos (by omega), dif_pos (by omega)] at hi
        simpa using hi
    have hfan_adj : ∀ t : Qubits n,
        act fan.1.adj.unitary (ket (withTgt (fanZ z) t)) = ket (withTgt z t) := by
      intro t
      have hwith_clean : ∀ j : Fin n,
          withTgt z t ⟨1 + n + j.1, by have := j.isLt; omega⟩ = false := fun j => by
        dsimp only [withTgt]
        rw [dif_neg (by omega)]
        exact hz j
      have hfan_wt := act_fanoutTree_ket n hn (withTgt z t) hwith_clean
      have hfan_eq : (fun w => if 1 + n ≤ w.1 then withTgt z t 0 else withTgt z t w) =
          withTgt (fanZ z) t := by
        funext w
        by_cases h1 : 1 ≤ w.1 ∧ w.1 < 1 + n
        · dsimp only [withTgt]
          rw [if_neg (by omega), dif_pos h1, dif_pos h1]
        · dsimp only [withTgt, fanZ]
          rw [dif_neg h1]
          by_cases h2 : 1 + n ≤ w.1
          · rw [if_pos h2, if_pos h2, dif_neg (by simp), dif_neg h1]
          · rw [if_neg h2, if_neg h2, dif_neg h1]
      rw [hfan_eq] at hfan_wt
      rw [← hfan_wt, ← act_mul, LayeredCircuit.adj_unitary,
        Matrix.mem_unitaryGroup_iff'.mp fan.1.unitary_mem_unitaryGroup, act_one]
    have htot : act (fan.1.seq (hLayer.seq fan.1.adj)).unitary (ket z) =
        ∑ t : Qubits n,
          (if z 0 then hadamardN n t (tgtPart z) else if t = tgtPart z then 1 else 0) •
            ket (withTgt z t) := by
      simp only [LayeredCircuit.seq_unitary, act_mul, hfan_z, hmid, act_sum, act_smul, hfan_adj]
    have hentry : (fan.1.seq (hLayer.seq fan.1.adj)).unitary y z =
        inner ℂ (ket y) (act (fan.1.seq (hLayer.seq fan.1.adj)).unitary (ket z)) := by
      rw [act_ket_eq, inner_sum]
      simp [inner_smul_right, ket, EuclideanSpace.inner_single_left]
    rw [hentry, htot, inner_sum]
    simp only [inner_smul_right, ket, EuclideanSpace.inner_single_left, PiLp.single_apply,
      map_one, mul_ite, mul_one, mul_zero]
    by_cases hy : ∀ j : Fin n, y (Fin.natAdd (1 + n) j) = false
    · rw [if_pos hy]
      have h_off : ∀ (t : Qubits n), withTgt z t = y ↔ (y 0 = z 0 ∧ t = tgtPart y) := by
        intro t
        constructor
        · intro heq
          refine ⟨by rw [← heq]; simp [withTgt], ?_⟩
          funext i
          have his := i.isLt
          have := congrFun heq (ctrlHTgtWire n i)
          dsimp [withTgt, tgtPart, ctrlHTgtWire] at this ⊢
          rw [dif_pos (by omega)] at this
          simpa using this
        · rintro ⟨h0, rfl⟩
          funext w
          dsimp only [withTgt, tgtPart, ctrlHTgtWire]
          by_cases hw : 1 ≤ w.1 ∧ w.1 < 1 + n
          · rw [dif_pos hw]; congr 1; apply Fin.ext; simp; omega
          · rw [dif_neg hw]
            by_cases hw0 : w.1 = 0
            · have : w = ⟨0, by omega⟩ := Fin.ext hw0
              rw [this]; exact h0.symm
            · have hwlt := w.isLt
              have hj : ∃ j : Fin n, w = Fin.natAdd (1 + n) j :=
                ⟨⟨w.1 - (1 + n), by omega⟩, Fin.ext (by simp; omega)⟩
              rcases hj with ⟨j, rfl⟩
              rw [hz j, hy j]
      have hcast0_y : y (Fin.castAdd n ((0 : Fin (n + 1)).cast (Nat.add_comm n 1))) = y 0 := rfl
      have hcast0_z : z (Fin.castAdd n ((0 : Fin (n + 1)).cast (Nat.add_comm n 1))) = z 0 := rfl
      have htail_y : Fin.tail (fun i : Fin (n + 1) =>
          y (Fin.castAdd n (i.cast (Nat.add_comm n 1)))) = tgtPart y := by
        funext i; dsimp [Fin.tail, tgtPart, ctrlHTgtWire]; congr 1; exact Fin.ext (by simp; omega)
      have htail_z : Fin.tail (fun i : Fin (n + 1) =>
          z (Fin.castAdd n (i.cast (Nat.add_comm n 1)))) = tgtPart z := by
        funext i; dsimp [Fin.tail, tgtPart, ctrlHTgtWire]; congr 1; exact Fin.ext (by simp; omega)
      by_cases hy0 : y 0 = z 0
      · rw [Finset.sum_eq_single (tgtPart y)]
        · have heq : withTgt z (tgtPart y) = y := (h_off (tgtPart y)).mpr ⟨hy0, rfl⟩
          rw [if_pos heq.symm]
          simp only [ctrlHadamardMat, Matrix.of_apply, controlledQubits, controlled,
            Matrix.submatrix_apply, hcast0_y, hcast0_z, htail_y, htail_z, if_pos hy0]
          cases hz0 : z 0
          · have hyf : y 0 = false := hy0.trans hz0
            simp only [hyf, Bool.false_eq_true, ↓reduceIte, Matrix.one_apply, htail_y, htail_z]
          · have hyt : y 0 = true := hy0.trans hz0
            simp only [hyt, ↓reduceIte]
        · intro t _ ht
          have hne : withTgt z t ≠ y := fun h => ht ((h_off t).mp h).2
          rw [if_neg hne.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      · have hzero_sum : (∑ t : Qubits n,
            (if y = withTgt z t then
              if z 0 then hadamardN n t (tgtPart z) else if t = tgtPart z then 1 else 0
            else 0)) = 0 := by
          refine Finset.sum_eq_zero fun t _ => ?_
          have hne : withTgt z t ≠ y := fun h => hy0 ((h_off t).mp h).1
          rw [if_neg hne.symm]
        rw [hzero_sum]
        simp only [ctrlHadamardMat, Matrix.of_apply, controlledQubits, controlled,
          Matrix.submatrix_apply, hcast0_y, hcast0_z, if_neg hy0]
    · rw [if_neg hy]
      refine Finset.sum_eq_zero fun t _ => ?_
      have hne : withTgt z t ≠ y := by
        intro h
        apply hy
        intro j
        rw [← h]
        dsimp only [withTgt]
        rw [dif_neg (by simp)]
        exact hz j
      rw [if_neg hne.symm]
  · simp only [ctrlHadamardN, dif_neg hn]
    have hn0 : n = 0 := by omega
    subst hn0
    have htru : ∀ j : Fin 0, y (Fin.natAdd (1 + 0) j) = false := fun j => Fin.elim0 j
    rw [if_pos htru]
    simp only [LayeredCircuit.id_unitary, Matrix.one_apply, ctrlHadamardMat, Matrix.of_apply,
      controlledQubits, controlled, Matrix.submatrix_apply]
    have hcast0 : ∀ x : Qubits 1, x (Fin.castAdd 0 ((0 : Fin 1).cast (Nat.add_comm 0 1))) = x 0 :=
      fun _ => rfl
    rw [hcast0 y, hcast0 z]
    by_cases h : y = z
    · subst h; rw [if_pos rfl, if_pos rfl]
      cases h0 : y 0
      · simp
      · simp [hadamardN, dotBits]
    · have h0_ne : y 0 ≠ z 0 := fun h0 => h (funext fun i => by fin_cases i; exact h0)
      rw [if_neg h, if_neg h0_ne]


/-! ### 13. Multi-Controlled Single-Qubit Unitary (`multiEqCtrl1`) -/

lemma circuit_preserves_wire {m : ℕ} (c : Circuit gates12 m) (t : Fin m)
    (ht : ∀ g ∈ c, t ∉ Set.range g.wires) (y z : Qubits m) (hne : y t ≠ z t) :
    Circuit.unitary c y z = 0 := by
  induction c generalizing y z with
  | nil =>
    rw [circuit_unitary_nil, Matrix.one_apply]
    have hyz : y ≠ z := fun h => hne (congrFun h t)
    rw [if_neg hyz]
  | cons g rest ih =>
    rw [circuit_unitary_cons, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hgt : t ∉ Set.range g.wires := ht g List.mem_cons_self
    have hrest : ∀ g' ∈ rest, t ∉ Set.range g'.wires := fun g' hg' =>
      ht g' (List.mem_cons_of_mem _ hg')
    by_cases hxt : x t = z t
    · have hyx : y t ≠ x t := fun h => hne (h.trans hxt)
      rw [ih hrest y x hyx, zero_mul]
    · have h0 : embedOp g.gate.mat g.wires x z = 0 := by
        simp only [embedOp, Matrix.of_apply]
        rw [if_neg (fun h => hxt (h t hgt))]
      rw [h0, mul_zero]

lemma act_ket_update_of_not_mem {m : ℕ} (lc : LayeredCircuit m) {S : Finset (Fin m)}
    (hS : lc.UsesOnly S) (t : Fin m) (ht : t ∉ S)
    {x x' : Qubits m} (hact : act lc.unitary (ket x) = ket x') (b : Bool) :
    act lc.unitary (ket (Function.update x t b)) = ket (Function.update x' t b) := by
  have hnot_wires : ∀ g ∈ lc.toCircuit, t ∉ Set.range g.wires := by
    intro g hg ⟨i, hi⟩
    rw [LayeredCircuit.toCircuit, List.mem_flatten] at hg
    rcases hg with ⟨L, hL, hgL⟩
    exact ht (hi ▸ hS L hL g hgL i)
  have hxt : x' t = x t := by
    by_contra hne
    have hzero := circuit_preserves_wire lc.toCircuit t hnot_wires x' x hne
    have hket : (act lc.unitary (ket x)) x' = 1 := by rw [hact]; simp [ket]
    have hket' : (act lc.unitary (ket x)) x' = lc.unitary x' x := by
      have hinner : (act lc.unitary (ket x)) x' = inner ℂ (ket x') (act lc.unitary (ket x)) := by
        simp [ket, EuclideanSpace.inner_single_left]
      rw [hinner, act_ket_eq, inner_sum]
      simp [inner_smul_right, ket, EuclideanSpace.inner_single_left]
    have h0' : lc.unitary x' x = 0 := hzero
    rw [hket', h0'] at hket
    exact one_ne_zero hket.symm
  have hcomm : lc.unitary * (pauliXGate t).unitary = (pauliXGate t).unitary * lc.unitary := by
    apply LayeredCircuit.circuit_comm_of_disjoint
    intro g1 hg1 g2 hg2
    simp only [pauliXGate, LayeredCircuit.single, LayeredCircuit.toCircuit, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.mem_singleton] at hg2
    subst hg2
    rw [Set.disjoint_left]
    rintro w hw1 ⟨i, hi⟩
    have hwt : w = t := by
      have : (pauliXApp t).wires i = t := rfl
      rw [← hi, this]
    subst hwt
    exact hnot_wires g1 hg1 hw1
  by_cases hb : b = x t
  · have hx_eq : Function.update x t b = x := by
      funext w
      by_cases hw : w = t
      · subst hw; simp [hb]
      · exact Function.update_of_ne hw _ _
    have hx'_eq : Function.update x' t b = x' := by
      funext w
      by_cases hw : w = t
      · subst hw; simp [hb, hxt]
      · exact Function.update_of_ne hw _ _
    rw [hx_eq, hx'_eq, hact]
  · have hbx : b = !x t := by
      revert hb; cases x t <;> cases b <;> decide
    have hbx' : b = !x' t := by rw [hbx, hxt]
    have hkx : ket (Function.update x t b) = act (pauliXGate t).unitary (ket x) := by
      rw [act_pauliXGate_ket, hbx]
    have hkx' : ket (Function.update x' t b) = act (pauliXGate t).unitary (ket x') := by
      rw [act_pauliXGate_ket, hbx']
    rw [hkx, ← act_mul, hcomm, act_mul, hact, ← hkx']

private lemma foldl_update_apply {m : ℕ} (L : List (Fin m)) (val f : Fin m → Bool) (w : Fin m) :
    L.foldl (fun g t => Function.update g t (val t)) f w = if w ∈ L then val w else f w := by
  induction L generalizing f with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    by_cases hr : w ∈ rest
    · simp [hr]
    · by_cases hwa : w = a
      · subst hwa; simp [hr]
      · simp [hr, hwa]

private lemma act_ket_updateList_of_not_mem {m : ℕ} (lc : LayeredCircuit m) {S : Finset (Fin m)}
    (hS : lc.UsesOnly S) {x x' : Qubits m} (hact : act lc.unitary (ket x) = ket x')
    (L : List (Fin m)) (hL : ∀ t ∈ L, t ∉ S) (val : Fin m → Bool) :
    act lc.unitary (ket (L.foldl (fun g t => Function.update g t (val t)) x)) =
      ket (L.foldl (fun g t => Function.update g t (val t)) x') := by
  induction L generalizing x x' with
  | nil => exact hact
  | cons a rest ih =>
    simp only [List.foldl_cons]
    exact ih
      (act_ket_update_of_not_mem lc hS a (hL a List.mem_cons_self) hact (val a))
      (fun t ht => hL t (List.mem_cons_of_mem _ ht))

lemma act_ket_agree_on_usesOnly {m : ℕ} (lc : LayeredCircuit m) {S : Finset (Fin m)}
    (hS : lc.UsesOnly S) {x₁ x₁' x₂ : Qubits m}
    (hact : act lc.unitary (ket x₁) = ket x₁')
    (hagree : ∀ w ∈ S, x₂ w = x₁ w) :
    act lc.unitary (ket x₂) = ket (fun w => if w ∈ S then x₁' w else x₂ w) := by
  classical
  let L : List (Fin m) := (Finset.univ.filter (fun w : Fin m => w ∉ S)).toList
  have hL : ∀ t ∈ L, t ∉ S := by
    intro t ht
    simpa [L] using ht
  have hx1 : L.foldl (fun g t => Function.update g t (x₂ t)) x₁ = x₂ := by
    funext w
    rw [foldl_update_apply]
    by_cases hw : w ∈ S
    · have hwL : w ∉ L := fun h => hL w h hw
      rw [if_neg hwL, hagree w hw]
    · have hwL : w ∈ L := by simp [L, hw]
      rw [if_pos hwL]
  have hx1' : L.foldl (fun g t => Function.update g t (x₂ t)) x₁' =
      (fun w => if w ∈ S then x₁' w else x₂ w) := by
    funext w
    rw [foldl_update_apply]
    by_cases hw : w ∈ S
    · have hwL : w ∉ L := fun h => hL w h hw
      rw [if_neg hwL, if_pos hw]
    · have hwL : w ∈ L := by simp [L, hw]
      rw [if_pos hwL, if_neg hw]
  have h := act_ket_updateList_of_not_mem lc hS hact L hL x₂
  rwa [hx1, hx1'] at h

def eqCtrlMat (L : ℕ) (pat : Qubits L) (U : Matrix Bool Bool ℂ) :
    Matrix (Qubits (L + 1)) (Qubits (L + 1)) ℂ :=
  Matrix.of fun y z =>
    if ∀ i : Fin L, y ⟨i.1, by omega⟩ = z ⟨i.1, by omega⟩ then
      if ∀ i : Fin L, z ⟨i.1, by omega⟩ = pat i then U (y ⟨L, by omega⟩) (z ⟨L, by omega⟩)
      else if y ⟨L, by omega⟩ = z ⟨L, by omega⟩ then 1 else 0
    else 0

private def treeOut (L lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ L) : Fin (L + 1 + L) :=
  if len = 1 then ⟨lo, by omega⟩ else ⟨L + 1 + (lo + len / 2 - 1), by omega⟩

private def treeSupport (L lo len : ℕ) : Finset (Fin (L + 1 + L)) :=
  Finset.univ.filter fun w =>
    (lo ≤ w.1 ∧ w.1 < lo + len) ∨ (L + 1 + lo ≤ w.1 ∧ w.1 + 1 < L + 1 + lo + len)

private lemma mem_treeSupport_iff {L lo len : ℕ} {w : Fin (L + 1 + L)} :
    w ∈ treeSupport L lo len ↔
      (lo ≤ w.1 ∧ w.1 < lo + len) ∨ (L + 1 + lo ≤ w.1 ∧ w.1 + 1 < L + 1 + lo + len) := by
  simp [treeSupport]

private lemma treeOut_mem_treeSupport (L lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ L) :
    treeOut L lo len hlen hb ∈ treeSupport L lo len := by
  rw [mem_treeSupport_iff]
  unfold treeOut
  split_ifs with h1
  · left; simp; omega
  · right; simp; omega

private lemma treeSupport_disjoint (L lo len : ℕ) (hb : lo + len ≤ L) :
    Disjoint (treeSupport L lo (len / 2)) (treeSupport L (lo + len / 2) (len - len / 2)) := by
  rw [Finset.disjoint_left]
  intro w hwL hwR
  rw [mem_treeSupport_iff] at hwL hwR
  omega

private lemma treeSupport_left_subset (L lo len : ℕ) :
    treeSupport L lo (len / 2) ⊆ treeSupport L lo len := by
  intro w hw
  rw [mem_treeSupport_iff] at hw ⊢
  omega

private lemma treeSupport_right_subset (L lo len : ℕ) :
    treeSupport L (lo + len / 2) (len - len / 2) ⊆ treeSupport L lo len := by
  intro w hw
  rw [mem_treeSupport_iff] at hw ⊢
  omega

private lemma treeOut_not_mem_left (L lo len : ℕ) (hlen2 : 2 ≤ len) (hb : lo + len ≤ L) :
    treeOut L lo len (by omega) hb ∉ treeSupport L lo (len / 2) := by
  intro h
  rw [mem_treeSupport_iff] at h
  simp only [treeOut, show len ≠ 1 by omega, ↓reduceIte] at h
  omega

private lemma treeOut_not_mem_right (L lo len : ℕ) (hlen2 : 2 ≤ len) (hb : lo + len ≤ L) :
    treeOut L lo len (by omega) hb ∉ treeSupport L (lo + len / 2) (len - len / 2) := by
  intro h
  rw [mem_treeSupport_iff] at h
  simp only [treeOut, show len ≠ 1 by omega, ↓reduceIte] at h
  omega

private noncomputable def andTree (L lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ L) :
    { lc : LayeredCircuit (L + 1 + L) // lc.UsesOnly (treeSupport L lo len) } :=
  if h2 : len < 2 then
    ⟨LayeredCircuit.id (L + 1 + L), LayeredCircuit.id_usesOnly _⟩
  else
    let mid := len / 2
    have hlen2 : 2 ≤ len := by omega
    have hmid1 : 1 ≤ mid := by omega
    have hrem1 : 1 ≤ len - mid := by omega
    have hbL : lo + mid ≤ L := by omega
    have hbR : lo + mid + (len - mid) ≤ L := by omega
    let lcL := andTree L lo mid hmid1 hbL
    let lcR := andTree L (lo + mid) (len - mid) hrem1 hbR
    let merged := LayeredCircuit.parMerge lcL.1 lcR.1 lcL.2 lcR.2
      (treeSupport_disjoint L lo len hb)
    let outL := treeOut L lo mid hmid1 hbL
    let outR := treeOut L (lo + mid) (len - mid) hrem1 hbR
    let out := treeOut L lo len hlen hb
    have hLR : outL ≠ outR := by
      intro heq
      have h1 := treeOut_mem_treeSupport L lo mid hmid1 hbL
      have h2' := treeOut_mem_treeSupport L (lo + mid) (len - mid) hrem1 hbR
      change outL ∈ treeSupport L lo mid at h1
      rw [heq] at h1
      exact Finset.disjoint_left.mp (treeSupport_disjoint L lo len hb) h1 h2'
    have hLo : outL ≠ out := by
      intro heq
      have h1 := treeOut_mem_treeSupport L lo mid hmid1 hbL
      change outL ∈ treeSupport L lo mid at h1
      rw [heq] at h1
      exact treeOut_not_mem_left L lo len hlen2 hb h1
    have hRo : outR ≠ out := by
      intro heq
      have h2' := treeOut_mem_treeSupport L (lo + mid) (len - mid) hrem1 hbR
      change outR ∈ treeSupport L (lo + mid) (len - mid) at h2'
      rw [heq] at h2'
      exact treeOut_not_mem_right L lo len hlen2 hb h2'
    let tof := toffoliOn outL outR out hLR hLo hRo
    have hmerged_uses : merged.UsesOnly (treeSupport L lo len) :=
      (LayeredCircuit.parMerge_usesOnly lcL.1 lcR.1 lcL.2 lcR.2 _).mono
        (Finset.union_subset (treeSupport_left_subset L lo len) (treeSupport_right_subset L lo len))
    have htof_uses : tof.UsesOnly (treeSupport L lo len) := by
      refine (toffoliOn_usesOnly outL outR out hLR hLo hRo).mono ?_
      rw [Finset.insert_subset_iff, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨treeSupport_left_subset L lo len (treeOut_mem_treeSupport L lo mid hmid1 hbL),
        treeSupport_right_subset L lo len (treeOut_mem_treeSupport L (lo + mid) (len - mid) hrem1 hbR),
        treeOut_mem_treeSupport L lo len hlen hb⟩
    ⟨merged.seq tof, LayeredCircuit.seq_usesOnly hmerged_uses htof_uses⟩
termination_by len
decreasing_by all_goals omega

private lemma andTree_size (L lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ L) :
    (andTree L lo len hlen hb).1.size = 5 * (len - 1) := by
  induction len using Nat.strong_induction_on generalizing lo with
  | h len ih =>
    unfold andTree
    split_ifs with h2
    · simp; omega
    · dsimp only
      have hsL := ih (len / 2) (by omega) lo (by omega) (by omega)
      have hsR := ih (len - len / 2) (by omega) (lo + len / 2) (by omega) (by omega)
      simp only [LayeredCircuit.seq_size, LayeredCircuit.parMerge_size, toffoliOn_size]
      rw [hsL, hsR]
      omega

private lemma andTree_depth (L lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ L) :
    (andTree L lo len hlen hb).1.depth ≤ 5 * Nat.clog 2 len := by
  induction len using Nat.strong_induction_on generalizing lo with
  | h len ih =>
    unfold andTree
    split_ifs with h2
    · simp
    · dsimp only
      have hlen2 : 2 ≤ len := by omega
      have hdL := ih (len / 2) (by omega) lo (by omega) (by omega)
      have hdR := ih (len - len / 2) (by omega) (lo + len / 2) (by omega) (by omega)
      have hL_le : (andTree L lo (len / 2) (by omega) (by omega)).1.depth ≤
          5 * Nat.clog 2 ((len + 1) / 2) :=
        le_trans hdL (Nat.mul_le_mul_left 5 clog2_half_le)
      have hclog_sub : Nat.clog 2 (len - len / 2) = Nat.clog 2 ((len + 1) / 2) := by
        congr 1; omega
      have hR_le : (andTree L (lo + len / 2) (len - len / 2) (by omega) (by omega)).1.depth ≤
          5 * Nat.clog 2 ((len + 1) / 2) := by
        have := hdR; rw [hclog_sub] at this; exact this
      have hrec := clog2_rec hlen2
      simp only [LayeredCircuit.seq_depth, LayeredCircuit.parMerge_depth, toffoliOn_depth]
      have hmax := max_le hL_le hR_le
      omega

private lemma andTree_ket (L lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ L)
    (z : Qubits (L + 1 + L))
    (hclean : ∀ w ∈ treeSupport L lo len, L + 1 ≤ w.1 → z w = false) :
    ∃ z' : Qubits (L + 1 + L),
      act (andTree L lo len hlen hb).1.unitary (ket z) = ket z' ∧
      (∀ w, w ∉ treeSupport L lo len → z' w = z w) ∧
      (∀ (k : ℕ), lo ≤ k → ∀ (_hk2 : k < lo + len), z' ⟨k, by omega⟩ = z ⟨k, by omega⟩) ∧
      z' (treeOut L lo len hlen hb) =
        decide (∀ i : Fin L, lo ≤ i.1 → i.1 < lo + len →
          z ⟨i.1, by have := i.isLt; omega⟩ = true) := by
  induction len using Nat.strong_induction_on generalizing lo z with
  | h len ih =>
    unfold andTree
    split_ifs with h2
    · have hlen1 : len = 1 := by omega
      subst hlen1
      refine ⟨z, by simp only [LayeredCircuit.id_unitary, act_one], fun _ _ => rfl,
        fun _ _ _ => rfl, ?_⟩
      simp only [treeOut, ↓reduceIte]
      rw [Bool.eq_iff_iff, decide_eq_true_eq]
      cases hz : z ⟨lo, by omega⟩
      · simp only [Bool.false_eq_true, false_iff, not_forall]
        exact ⟨⟨lo, by omega⟩, le_rfl, Nat.lt_succ_self lo, by simp [hz]⟩
      · simp only [true_iff]
        intro i hi1 hi2
        have hk : i.1 = lo := by omega
        have heq : (⟨i.1, by have := i.isLt; omega⟩ : Fin (L + 1 + L)) = ⟨lo, by omega⟩ :=
          Fin.ext hk
        rw [heq, hz]
    · dsimp only
      set mid := len / 2
      have hlen2 : 2 ≤ len := by omega
      have hmid1 : 1 ≤ mid := by omega
      have hrem1 : 1 ≤ len - mid := by omega
      have hmid_lt : mid < len := by omega
      have hrem_lt : len - mid < len := by omega
      have hbL : lo + mid ≤ L := by omega
      have hbR : lo + mid + (len - mid) ≤ L := by omega
      let lcL := andTree L lo mid hmid1 hbL
      let lcR := andTree L (lo + mid) (len - mid) hrem1 hbR
      let outL := treeOut L lo mid hmid1 hbL
      let outR := treeOut L (lo + mid) (len - mid) hrem1 hbR
      let out := treeOut L lo len hlen hb
      have hcleanL : ∀ w ∈ treeSupport L lo mid, L + 1 ≤ w.1 → z w = false := fun w hw =>
        hclean w (treeSupport_left_subset L lo len hw)
      rcases ih mid hmid_lt lo hmid1 hbL z hcleanL with
        ⟨zL, hactL, houtL, haddrL, hresL⟩
      have hcleanR_z : ∀ w ∈ treeSupport L (lo + mid) (len - mid), L + 1 ≤ w.1 → z w = false :=
        fun w hw => hclean w (treeSupport_right_subset L lo len hw)
      rcases ih (len - mid) hrem_lt (lo + mid) hrem1 hbR z hcleanR_z with
        ⟨zR0, hactR0, houtR0, haddrR0, hresR0⟩
      let z2 : Qubits (L + 1 + L) := fun w =>
        if w ∈ treeSupport L (lo + mid) (len - mid) then zR0 w else zL w
      have hagreeR : ∀ w ∈ treeSupport L (lo + mid) (len - mid), zL w = z w := fun w hw =>
        houtL w (Finset.disjoint_right.mp (treeSupport_disjoint L lo len hb) hw)
      have hactR : act lcR.1.unitary (ket zL) = ket z2 :=
        act_ket_agree_on_usesOnly lcR.1 lcR.2 hactR0 hagreeR
      have hmerged_act : act (LayeredCircuit.parMerge lcL.1 lcR.1 lcL.2 lcR.2
          (treeSupport_disjoint L lo len hb)).unitary (ket z) = ket z2 := by
        rw [LayeredCircuit.parMerge_unitary, act_mul, hactL, hactR]
      have hLR : outL ≠ outR := by
        intro heq
        have h1 := treeOut_mem_treeSupport L lo mid hmid1 hbL
        have h2' := treeOut_mem_treeSupport L (lo + mid) (len - mid) hrem1 hbR
        change outL ∈ treeSupport L lo mid at h1
        rw [heq] at h1
        exact Finset.disjoint_left.mp (treeSupport_disjoint L lo len hb) h1 h2'
      have hLo : outL ≠ out := by
        intro heq
        have h1 := treeOut_mem_treeSupport L lo mid hmid1 hbL
        change outL ∈ treeSupport L lo mid at h1
        rw [heq] at h1
        exact treeOut_not_mem_left L lo len hlen2 hb h1
      have hRo : outR ≠ out := by
        intro heq
        have h2' := treeOut_mem_treeSupport L (lo + mid) (len - mid) hrem1 hbR
        change outR ∈ treeSupport L (lo + mid) (len - mid) at h2'
        rw [heq] at h2'
        exact treeOut_not_mem_right L lo len hlen2 hb h2'
      let tof := toffoliOn outL outR out hLR hLo hRo
      let z' : Qubits (L + 1 + L) :=
        Function.update z2 out (xor (z2 out) (z2 outL && z2 outR))
      have htot_act : act ((LayeredCircuit.parMerge lcL.1 lcR.1 lcL.2 lcR.2
          (treeSupport_disjoint L lo len hb)).seq tof).unitary (ket z) = ket z' := by
        rw [LayeredCircuit.seq_unitary, act_mul, hmerged_act]
        exact act_toffoliOn_ket outL outR out hLR hLo hRo z2
      refine ⟨z', htot_act, ?_, ?_, ?_⟩
      · intro w hw
        have hwL : w ∉ treeSupport L lo mid := fun h => hw (treeSupport_left_subset L lo len h)
        have hwR : w ∉ treeSupport L (lo + mid) (len - mid) :=
          fun h => hw (treeSupport_right_subset L lo len h)
        have hw_out : w ≠ out := fun h => hw (h ▸ treeOut_mem_treeSupport L lo len hlen hb)
        dsimp only [z', z2]
        rw [Function.update_of_ne hw_out, if_neg hwR, houtL w hwL]
      · intro k hk1 hk2
        have hk_out : (⟨k, by omega⟩ : Fin (L + 1 + L)) ≠ out := by
          intro h
          have := congrArg Fin.val h
          simp only [out, treeOut, show len ≠ 1 by omega, ↓reduceIte] at this
          omega
        dsimp only [z', z2]
        rw [Function.update_of_ne hk_out]
        by_cases hkL : k < lo + mid
        · have hkR : (⟨k, by omega⟩ : Fin (L + 1 + L)) ∉ treeSupport L (lo + mid) (len - mid) := by
            rw [mem_treeSupport_iff]; simp; omega
          rw [if_neg hkR]
          exact haddrL k hk1 hkL
        · have hkR : (⟨k, by omega⟩ : Fin (L + 1 + L)) ∈ treeSupport L (lo + mid) (len - mid) := by
            rw [mem_treeSupport_iff]; left; simp; omega
          rw [if_pos hkR]
          exact haddrR0 k (by omega) (by omega)
      · dsimp only [z']
        rw [Function.update_self]
        have hout_clean : z2 out = false := by
          have hout_notL := treeOut_not_mem_left L lo len hlen2 hb
          have hout_notR := treeOut_not_mem_right L lo len hlen2 hb
          dsimp only [z2]
          rw [if_neg hout_notR, houtL out hout_notL]
          exact hclean out (treeOut_mem_treeSupport L lo len hlen hb) (by
            simp [out, treeOut, show len ≠ 1 by omega])
        have hz2_outL : z2 outL = zL outL := by
          have hnotR : outL ∉ treeSupport L (lo + mid) (len - mid) :=
            Finset.disjoint_left.mp (treeSupport_disjoint L lo len hb)
              (treeOut_mem_treeSupport L lo mid hmid1 hbL)
          dsimp only [z2]; rw [if_neg hnotR]
        have hz2_outR : z2 outR = zR0 outR := by
          have hinR := treeOut_mem_treeSupport L (lo + mid) (len - mid) hrem1 hbR
          dsimp only [z2]; rw [if_pos hinR]
        rw [hout_clean, hz2_outL, hz2_outR, hresL, hresR0, Bool.false_xor]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨hL_all, hR_all⟩ i hi1 hi2
          by_cases hk : i.1 < lo + mid
          · exact hL_all i hi1 hk
          · exact hR_all i (by omega) (by omega)
        · intro h_all
          exact ⟨fun i hi1 hi2 => h_all i hi1 (by omega),
            fun i hi1 hi2 => h_all i (by omega) (by omega)⟩

private def flipPatLayer (L : ℕ) (pat : Qubits L) :
    { lc : LayeredCircuit (L + 1 + L) //
      lc.UsesOnly (Finset.univ.filter fun w : Fin (L + 1 + L) => w.1 < L) ∧
      lc.size ≤ L ∧
      lc.depth ≤ 1 } :=
  let idxs : List (Fin L) := (List.finRange L).filter fun i => !pat i
  let apps : List (GateApp gates12 (L + 1 + L)) :=
    idxs.map fun i => pauliXApp ⟨i.1, by have := i.isLt; omega⟩
  have hnodup : idxs.Nodup := (List.nodup_finRange L).filter _
  have hdisj : LayerDisjoint apps := by
    dsimp only [LayerDisjoint, apps]
    rw [List.pairwise_map]
    refine (List.nodup_iff_pairwise_ne.mp hnodup).imp fun {i j} hij => ?_
    rw [Set.disjoint_left]
    rintro w ⟨a, rfl⟩ ⟨b, hb⟩
    have hi := i.isLt
    have hj := j.isLt
    have hval : (wire1Emb (⟨i.1, by omega⟩ : Fin (L + 1 + L)) a).1 =
        (wire1Emb (⟨j.1, by omega⟩ : Fin (L + 1 + L)) b).1 := congrArg Fin.val hb.symm
    simp [wire1Emb] at hval
    exact hij (Fin.ext hval)
  let lc := LayeredCircuit.ofLayer apps hdisj
  have huses : lc.UsesOnly (Finset.univ.filter fun w : Fin (L + 1 + L) => w.1 < L) := by
    apply LayeredCircuit.ofLayer_usesOnly
    intro g hg a
    simp only [apps, List.mem_map] at hg
    rcases hg with ⟨i, _, rfl⟩
    simp [pauliXApp, gate1App, wire1Emb]
    exact i.isLt
  have hsize : lc.size ≤ L := by
    simp only [lc, LayeredCircuit.ofLayer_size, apps, List.length_map, idxs]
    calc ((List.finRange L).filter fun i => !pat i).length
        ≤ (List.finRange L).length := List.length_filter_le _ _
      _ = L := List.length_finRange
  have hdepth : lc.depth ≤ 1 := by
    simpa only [lc] using LayeredCircuit.ofLayer_depth apps hdisj
  ⟨lc, huses, hsize, hdepth⟩

private lemma act_flipPatLayer_ket (L : ℕ) (pat : Qubits L) (x : Qubits (L + 1 + L)) :
    act (flipPatLayer L pat).1.unitary (ket x) =
      ket (fun w => if hw : w.1 < L then (if pat ⟨w.1, hw⟩ then x w else !x w) else x w) := by
  classical
  dsimp only [flipPatLayer]
  rw [LayeredCircuit.ofLayer_unitary, act_ket_eq]
  let idxs : List (Fin L) := (List.finRange L).filter fun i => !pat i
  let ws : List (Fin (L + 1 + L)) := idxs.map fun i => ⟨i.1, by have := i.isLt; omega⟩
  have hws_nodup : ws.Nodup :=
    ((List.nodup_finRange L).filter _).map fun a b hab => Fin.ext (by
      have := congrArg Fin.val hab; simpa using this)
  have happs_eq : (idxs.map fun i : Fin L => pauliXApp (⟨i.1, by have := i.isLt; omega⟩ : Fin (L + 1 + L))) =
      ws.map fun w => gate1App pauliX pauliX_mem_unitaryGroup w := by
    simp [ws, pauliXApp]
  rw [happs_eq]
  let x' : Qubits (L + 1 + L) :=
    fun w => if hw : w.1 < L then (if pat ⟨w.1, hw⟩ then x w else !x w) else x w
  have hx'_mem : ∀ w : Fin (L + 1 + L), w ∈ ws ↔ (∃ hw : w.1 < L, pat ⟨w.1, hw⟩ = false) := by
    intro w
    simp only [ws, idxs, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨i.isLt, ?_⟩
      cases hpi : pat i <;> simp_all
    · rintro ⟨hw, hpat⟩
      exact ⟨⟨w.1, hw⟩, by simp [hpat], Fin.ext rfl⟩
  rw [Finset.sum_eq_single x']
  · rw [circuit_prod_gate1_of_nodup ws hws_nodup _ _ x' x]
    have hoff : ∀ q : Fin (L + 1 + L), q ∉ ws → x' q = x q := by
      intro q hq
      dsimp only [x']
      split_ifs with hql hpat
      · rfl
      · exfalso; exact hq ((hx'_mem q).mpr ⟨hql, by cases hpat_q : pat ⟨q.1, hql⟩ <;> simp_all⟩)
      · rfl
    rw [if_pos hoff]
    have hprod : (∏ w ∈ ws.toFinset, pauliX (x' w) (x w)) = 1 := by
      refine Finset.prod_eq_one fun w hw => ?_
      have hw_ws : w ∈ ws := List.mem_toFinset.mp hw
      rcases (hx'_mem w).mp hw_ws with ⟨hw_lt, hpat⟩
      have hxw : x' w = !x w := by simp [x', hw_lt, hpat]
      rw [hxw]
      cases x w <;> simp [pauliX]
    rw [hprod, one_smul]
  · intro y _ hy
    rw [circuit_prod_gate1_of_nodup ws hws_nodup _ _ y x]
    by_cases hoff : ∀ q : Fin (L + 1 + L), q ∉ ws → y q = x q
    · rw [if_pos hoff]
      by_cases hprod0 : ∃ w ∈ ws.toFinset, pauliX (y w) (x w) = 0
      · rcases hprod0 with ⟨w, hw, h0⟩
        rw [Finset.prod_eq_zero hw h0, zero_smul]
      · push Not at hprod0
        exfalso; apply hy
        funext w
        by_cases hw : w ∈ ws
        · have hne0 := hprod0 w (List.mem_toFinset.mpr hw)
          rcases (hx'_mem w).mp hw with ⟨hw_lt, hpat⟩
          have hyw : y w = !x w := by
            revert hne0; cases y w <;> cases x w <;> simp [pauliX]
          simp [x', hw_lt, hpat, hyw]
        · rw [hoff w hw]
          dsimp only [x']
          split_ifs with hw_lt hpat
          · rfl
          · exfalso; exact hw ((hx'_mem w).mpr ⟨hw_lt, by cases hpat_w : pat ⟨w.1, hw_lt⟩ <;> simp_all⟩)
          · rfl
    · rw [if_neg hoff, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

noncomputable def multiEqCtrl1 (L : ℕ) (pat : Qubits L) (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) : LayeredCircuit (L + 1 + L) :=
  if hL : 1 ≤ L then
    let flip := flipPatLayer L pat
    let tree := andTree L 0 L hL (by omega)
    let out := treeOut L 0 L hL (by omega)
    let tgt : Fin (L + 1 + L) := ⟨L, by omega⟩
    have hne : out ≠ tgt := by
      intro h
      have hv := congrArg Fin.val h
      dsimp only [out, treeOut, tgt] at hv
      split_ifs at hv <;> simp at hv <;> omega
    let ctrl := ctrlGate1 U hU out tgt hne
    flip.1.seq (tree.1.seq (ctrl.seq (tree.1.adj.seq flip.1)))
  else
    gate1 U hU ⟨L, by omega⟩

lemma multiEqCtrl1_size (L : ℕ) (pat : Qubits L) (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    (multiEqCtrl1 L pat U hU).size ≤ 12 * (L + 1) := by
  unfold multiEqCtrl1
  split_ifs with hL
  · simp only [LayeredCircuit.seq_size, LayeredCircuit.adj_size, ctrlGate1_size]
    have h1 := (flipPatLayer L pat).2.2.1
    have h2 := andTree_size L 0 L hL (by omega)
    omega
  · simp; omega

lemma multiEqCtrl1_depth (L : ℕ) (pat : Qubits L) (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    (multiEqCtrl1 L pat U hU).depth ≤ 10 * Nat.clog 2 (L + 1) + 3 := by
  unfold multiEqCtrl1
  split_ifs with hL
  · simp only [LayeredCircuit.seq_depth, LayeredCircuit.adj_depth, ctrlGate1_depth]
    have h1 := (flipPatLayer L pat).2.2.2
    have h2 := andTree_depth L 0 L hL (by omega)
    have hclog : Nat.clog 2 L ≤ Nat.clog 2 (L + 1) := Nat.clog_mono_right 2 (by omega)
    omega
  · simp

theorem multiEqCtrl1_implements (L : ℕ) (pat : Qubits L) (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    (multiEqCtrl1 L pat U hU).ImplementsOnClean (eqCtrlMat L pat U) := by
  intro y z hz
  by_cases hL : 1 ≤ L
  · simp only [multiEqCtrl1, dif_pos hL]
    let flip := flipPatLayer L pat
    let tree := andTree L 0 L hL (by omega)
    let out := treeOut L 0 L hL (by omega)
    let tgt : Fin (L + 1 + L) := ⟨L, by omega⟩
    have hne : out ≠ tgt := by
      intro h
      have hv := congrArg Fin.val h
      dsimp only [out, treeOut, tgt] at hv
      split_ifs at hv <;> simp at hv <;> omega
    let ctrl := ctrlGate1 U hU out tgt hne
    let z1 : Qubits (L + 1 + L) :=
      fun w => if hw : w.1 < L then (if pat ⟨w.1, hw⟩ then z w else !z w) else z w
    have hflip_z : act flip.1.unitary (ket z) = ket z1 := act_flipPatLayer_ket L pat z
    have hclean_z1 : ∀ w ∈ treeSupport L 0 L, L + 1 ≤ w.1 → z1 w = false := by
      intro w _ hw_ge
      have hnot_lt : ¬ w.1 < L := by omega
      dsimp only [z1]
      rw [dif_neg hnot_lt]
      have hw_lt := w.isLt
      have hj : ∃ j : Fin L, w = ⟨L + 1 + j.1, by omega⟩ :=
        ⟨⟨w.1 - (L + 1), by omega⟩, Fin.ext (by simp; omega)⟩
      rcases hj with ⟨j, hw_eq⟩
      rw [hw_eq]
      exact hz j
    rcases andTree_ket L 0 L hL (by omega) z1 hclean_z1 with
      ⟨z', htree_fwd, hout_tree, _, hres_tree⟩
    have htgt_not_tree : tgt ∉ treeSupport L 0 L := by
      rw [mem_treeSupport_iff]; simp [tgt]
    have hz'_tgt : z' tgt = z tgt := by
      rw [hout_tree tgt htgt_not_tree]
      dsimp only [z1, tgt]
      rw [dif_neg (by omega)]
    have hz'_out : z' out = decide (∀ i : Fin L, z ⟨i.1, by omega⟩ = pat i) := by
      rw [hres_tree]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · intro h i
        have hi := h i (Nat.zero_le _) (by have := i.isLt; omega)
        dsimp only [z1] at hi
        rw [dif_pos i.isLt] at hi
        cases hzi : z ⟨i.1, by omega⟩ <;> cases hpi : pat i <;>
          simp [hzi, hpi] at hi ⊢
      · intro h i _ _
        dsimp only [z1]
        rw [dif_pos i.isLt]
        have hi := h i
        cases hzi : z ⟨i.1, by omega⟩ <;> cases hpi : pat i <;>
          simp [hzi, hpi] at hi ⊢
    have htree_adj : ∀ b : Bool,
        act tree.1.adj.unitary (ket (Function.update z' tgt b)) =
          ket (Function.update z1 tgt b) := by
      intro b
      have hfwd_b := act_ket_update_of_not_mem tree.1 tree.2 tgt htgt_not_tree htree_fwd b
      rw [← hfwd_b, ← act_mul, LayeredCircuit.adj_unitary,
        Matrix.mem_unitaryGroup_iff'.mp tree.1.unitary_mem_unitaryGroup, act_one]
    have hflip_inv : ∀ b : Bool,
        act flip.1.unitary (ket (Function.update z1 tgt b)) =
          ket (Function.update z tgt b) := by
      intro b
      rw [act_flipPatLayer_ket]
      congr 1
      funext w
      by_cases hw : w.1 < L
      · have hw_ne : w ≠ tgt := by intro h; have := congrArg Fin.val h; simp [tgt] at this; omega
        rw [dif_pos hw, Function.update_of_ne hw_ne, Function.update_of_ne hw_ne]
        dsimp only [z1]
        rw [dif_pos hw]
        cases pat ⟨w.1, hw⟩ <;> simp
      · rw [dif_neg hw]
        by_cases hwt : w = tgt
        · subst hwt; simp
        · rw [Function.update_of_ne hwt, Function.update_of_ne hwt]
          dsimp only [z1]; rw [dif_neg hw]
    have htot : act (flip.1.seq (tree.1.seq (ctrl.seq (tree.1.adj.seq flip.1)))).unitary (ket z) =
        ∑ b : Bool,
          (if (∀ i : Fin L, z ⟨i.1, by omega⟩ = pat i) then U b (z tgt)
           else if b = z tgt then 1 else 0) •
            ket (Function.update z tgt b) := by
      simp only [LayeredCircuit.seq_unitary, act_mul, hflip_z]
      rw [htree_fwd]
      dsimp only [ctrl]
      rw [act_ctrlGate1_ket, act_sum, act_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [act_smul, htree_adj, hflip_inv, hz'_tgt, hz'_out]
      by_cases hpat : ∀ i : Fin L, z ⟨i.1, by omega⟩ = pat i
      · simp [hpat]
      · simp [hpat]
    have hentry : (flip.1.seq (tree.1.seq (ctrl.seq (tree.1.adj.seq flip.1)))).unitary y z =
        inner ℂ (ket y)
          (act (flip.1.seq (tree.1.seq (ctrl.seq (tree.1.adj.seq flip.1)))).unitary (ket z)) := by
      rw [act_ket_eq, inner_sum]
      simp [inner_smul_right, ket, EuclideanSpace.inner_single_left]
    rw [hentry, htot, inner_sum]
    simp only [inner_smul_right, ket, EuclideanSpace.inner_single_left, PiLp.single_apply,
      map_one, mul_ite, mul_one, mul_zero]
    by_cases hy : ∀ j : Fin L, y (Fin.natAdd (L + 1) j) = false
    · rw [if_pos hy]
      have hoff : ∀ b : Bool, Function.update z tgt b = y ↔
          ((∀ i : Fin L, y ⟨i.1, by omega⟩ = z ⟨i.1, by omega⟩) ∧ y tgt = b) := by
        intro b
        constructor
        · intro heq
          refine ⟨fun i => ?_, by rw [← heq, Function.update_self]⟩
          rw [← heq, Function.update_of_ne]
          intro h; have := congrArg Fin.val h; dsimp [tgt] at this; omega
        · rintro ⟨haddr, rfl⟩
          funext w
          by_cases hwt : w = tgt
          · subst hwt; simp
          · rw [Function.update_of_ne hwt]
            by_cases hw_lt : w.1 < L
            · exact (haddr ⟨w.1, hw_lt⟩).symm
            · have hw_isLt := w.isLt
              have hw_ne_L : w.1 ≠ L := fun h => hwt (Fin.ext h)
              have hj : ∃ j : Fin L, w = Fin.natAdd (L + 1) j :=
                ⟨⟨w.1 - (L + 1), by omega⟩, Fin.ext (by simp; omega)⟩
              rcases hj with ⟨j, rfl⟩
              rw [hz j, hy j]
      by_cases haddr : ∀ i : Fin L, y ⟨i.1, by omega⟩ = z ⟨i.1, by omega⟩
      · rw [Finset.sum_eq_single (y tgt)]
        · have heq : Function.update z tgt (y tgt) = y := (hoff (y tgt)).mpr ⟨haddr, rfl⟩
          rw [if_pos heq.symm]
          simp only [eqCtrlMat, Matrix.of_apply]
          have haddr_cast : ∀ i : Fin L, y (Fin.castAdd L ⟨i.1, by omega⟩) =
              z (Fin.castAdd L ⟨i.1, by omega⟩) := haddr
          rw [if_pos haddr_cast]
          rfl
        · intro b _ hb
          have hne_upd : Function.update z tgt b ≠ y := fun h => hb ((hoff b).mp h).2.symm
          rw [if_neg hne_upd.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      · have hzero : (∑ b : Bool,
            (if y = Function.update z tgt b then
              if (∀ i : Fin L, z ⟨i.1, by omega⟩ = pat i) then U b (z tgt)
              else if b = z tgt then 1 else 0
            else 0)) = 0 := by
          refine Finset.sum_eq_zero fun b _ => ?_
          have hne_upd : Function.update z tgt b ≠ y := fun h => haddr ((hoff b).mp h).1
          rw [if_neg hne_upd.symm]
        rw [hzero]
        simp only [eqCtrlMat, Matrix.of_apply]
        have hnot : ¬ ∀ i : Fin L, y (Fin.castAdd L ⟨i.1, by omega⟩) =
            z (Fin.castAdd L ⟨i.1, by omega⟩) := haddr
        rw [if_neg hnot]
    · rw [if_neg hy]
      refine Finset.sum_eq_zero fun b _ => ?_
      have hne_upd : Function.update z tgt b ≠ y := by
        intro h
        apply hy
        intro j
        have hj_lt := j.isLt
        have hjn : Fin.natAdd (L + 1) j ≠ tgt := by
          intro heq; have := congrArg Fin.val heq; simp [tgt] at this; omega
        rw [← h, Function.update_of_ne hjn]
        exact hz j
      rw [if_neg hne_upd.symm]
  · simp only [multiEqCtrl1, dif_neg hL]
    have hL0 : L = 0 := by omega
    subst hL0
    have hy0 : ∀ j : Fin 0, y (Fin.natAdd (0 + 1) j) = false := fun j => Fin.elim0 j
    rw [if_pos hy0]
    simp only [gate1, LayeredCircuit.single_unitary, embedOp_gate1App_entry, eqCtrlMat,
      Matrix.of_apply]
    have hoff : ∀ a : Fin 1, a ≠ ⟨0, by omega⟩ → y a = z a := by
      intro a ha; fin_cases a; exact absurd rfl ha
    rw [if_pos hoff, if_pos (fun i => Fin.elim0 i), if_pos (fun i => Fin.elim0 i)]
    rfl

/-! ### 14. Parallel Carry-Save Hamming Weight Counter (`hammingCounter`) -/

lemma act_ket_usesOnly_outside {m : ℕ} {lc : LayeredCircuit m} {S : Finset (Fin m)}
    (hS : lc.UsesOnly S) {z z' : Qubits m} (hact : act lc.unitary (ket z) = ket z')
    {w : Fin m} (hw : w ∉ S) : z' w = z w := by
  by_contra hne
  have hnot_wires : ∀ g ∈ lc.toCircuit, w ∉ Set.range g.wires := by
    intro g hg ⟨i, hi⟩
    rw [LayeredCircuit.toCircuit, List.mem_flatten] at hg
    rcases hg with ⟨L, hL, hgL⟩
    exact hw (hi ▸ hS L hL g hgL i)
  have hzero := circuit_preserves_wire lc.toCircuit w hnot_wires z' z hne
  have h1 : (act lc.unitary (ket z)) z' = 1 := by rw [hact]; simp [ket]
  have h2 : (act lc.unitary (ket z)) z' = lc.unitary z' z := by
    have hinner : (act lc.unitary (ket z)) z' = inner ℂ (ket z') (act lc.unitary (ket z)) := by
      simp [ket, EuclideanSpace.inner_single_left]
    rw [hinner, act_ket_eq, inner_sum]
    simp [inner_smul_right, ket, EuclideanSpace.inner_single_left]
  rw [h2, (show lc.unitary z' z = 0 from hzero)] at h1
  exact one_ne_zero h1.symm

private lemma foldr_disjoint_of_pairwise {m : ℕ} {S : Finset (Fin m)}
    {rest : List (LayeredCircuit m × Finset (Fin m))}
    (hhd : ∀ q ∈ rest, Disjoint S q.2) :
    Disjoint S (rest.foldr (fun p acc => p.2 ∪ acc) ∅) := by
  induction rest with
  | nil => simp
  | cons p rp ihr =>
    simp only [List.foldr_cons, Finset.disjoint_union_right]
    exact ⟨hhd p List.mem_cons_self, ihr fun q hq => hhd q (List.mem_cons_of_mem _ hq)⟩

private def parMergeAux {m : ℕ} :
    (xs : List (LayeredCircuit m × Finset (Fin m))) →
    (∀ p ∈ xs, p.1.UsesOnly p.2) →
    xs.Pairwise (fun p q => Disjoint p.2 q.2) →
    { lc : LayeredCircuit m //
      lc.UsesOnly (xs.foldr (fun p acc => p.2 ∪ acc) ∅) ∧
      lc.size = (xs.map (fun p => p.1.size)).sum ∧
      lc.depth ≤ xs.foldr (fun p acc => max p.1.depth acc) 0 }
  | [], _, _ => ⟨LayeredCircuit.id m, LayeredCircuit.id_usesOnly _, rfl, le_rfl⟩
  | (lc, S) :: rest, huses, hpw =>
    have huses_rest : ∀ p ∈ rest, p.1.UsesOnly p.2 := fun p hp =>
      huses p (List.mem_cons_of_mem _ hp)
    have hpw_rest : rest.Pairwise (fun p q => Disjoint p.2 q.2) :=
      (List.pairwise_cons.mp hpw).2
    let ih := parMergeAux rest huses_rest hpw_rest
    have hdisj : Disjoint S (rest.foldr (fun p acc => p.2 ∪ acc) ∅) :=
      foldr_disjoint_of_pairwise (List.pairwise_cons.mp hpw).1
    let merged := LayeredCircuit.parMerge lc ih.1 (huses _ List.mem_cons_self) ih.2.1 hdisj
    ⟨merged,
      LayeredCircuit.parMerge_usesOnly lc ih.1 (huses _ List.mem_cons_self) ih.2.1 hdisj,
      by simp [merged, LayeredCircuit.parMerge_size, ih.2.2.1],
      by
        simp only [merged, LayeredCircuit.parMerge_depth, List.foldr_cons]
        exact max_le_max_left _ ih.2.2.2⟩

private lemma foldr_max_le {m : ℕ} (xs : List (LayeredCircuit m × Finset (Fin m)))
    (B : ℕ) (hB : ∀ p ∈ xs, p.1.depth ≤ B) :
    xs.foldr (fun p acc => max p.1.depth acc) 0 ≤ B := by
  induction xs with
  | nil => simp
  | cons p rest ih =>
    simp only [List.foldr_cons]
    exact max_le (hB p List.mem_cons_self) (ih fun q hq => hB q (List.mem_cons_of_mem _ hq))

private lemma act_parMergeAux_ket {m : ℕ}
    (xs : List (LayeredCircuit m × Finset (Fin m)))
    (huses : ∀ p ∈ xs, p.1.UsesOnly p.2)
    (hpw : xs.Pairwise (fun p q => Disjoint p.2 q.2))
    (z z_next : Qubits m)
    (hact : ∀ p ∈ xs, ∃ x' : Qubits m,
      act p.1.unitary (ket z) = ket x' ∧ ∀ w ∈ p.2, x' w = z_next w) :
    act (parMergeAux xs huses hpw).1.unitary (ket z) =
      ket (fun w => if w ∈ xs.foldr (fun p acc => p.2 ∪ acc) ∅ then z_next w else z w) := by
  induction xs with
  | nil => simp [parMergeAux, LayeredCircuit.id_unitary, act_one]
  | cons p rest ih =>
    rcases p with ⟨lc, S⟩
    dsimp only [parMergeAux]
    rw [LayeredCircuit.parMerge_unitary, act_mul]
    have huses_lc : lc.UsesOnly S := huses (lc, S) List.mem_cons_self
    rcases hact (lc, S) List.mem_cons_self with ⟨x', hx'_act, hx'_in⟩
    rw [hx'_act]
    have hih := ih (fun q hq => huses q (List.mem_cons_of_mem _ hq))
      (List.pairwise_cons.mp hpw).2 (fun q hq => hact q (List.mem_cons_of_mem _ hq))
    have huses_rest : ∀ q ∈ rest, q.1.UsesOnly q.2 := fun q hq =>
      huses q (List.mem_cons_of_mem _ hq)
    let ihRes := parMergeAux rest huses_rest (List.pairwise_cons.mp hpw).2
    let S_rest : Finset (Fin m) := rest.foldr (fun q acc => q.2 ∪ acc) ∅
    have hdisj : Disjoint S S_rest :=
      foldr_disjoint_of_pairwise (List.pairwise_cons.mp hpw).1
    have hx'_out : ∀ w, w ∉ S → x' w = z w := fun w hw =>
      act_ket_usesOnly_outside huses_lc hx'_act hw
    have hagree : ∀ w ∈ S_rest, x' w = z w := fun w hw =>
      hx'_out w (Finset.disjoint_right.mp hdisj hw)
    have hstep := act_ket_agree_on_usesOnly ihRes.1 ihRes.2.1 hih hagree
    rw [hstep]
    congr 1
    funext w
    simp only [List.foldr_cons, Finset.mem_union]
    by_cases hwR : w ∈ S_rest
    · rw [if_pos hwR, if_pos hwR, if_pos (Or.inr hwR)]
    · by_cases hwS : w ∈ S
      · rw [if_neg hwR, hx'_in w hwS, if_pos (Or.inl hwS)]
      · rw [if_neg hwR, hx'_out w hwS, if_neg (not_or.mpr ⟨hwS, hwR⟩)]

noncomputable def halfAdder4 {m : ℕ} (a b s c : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (hac : a ≠ c) (hbs : b ≠ s) (hbc : b ≠ c) :
    LayeredCircuit m :=
  (cnotGate a s has).seq ((cnotGate b s hbs).seq (toffoliOn a b c hab hac hbc))

@[simp] lemma halfAdder4_size {m : ℕ} (a b s c : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (hac : a ≠ c) (hbs : b ≠ s) (hbc : b ≠ c) :
    (halfAdder4 a b s c hab has hac hbs hbc).size = 7 := by
  simp [halfAdder4]

@[simp] lemma halfAdder4_depth {m : ℕ} (a b s c : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (hac : a ≠ c) (hbs : b ≠ s) (hbc : b ≠ c) :
    (halfAdder4 a b s c hab has hac hbs hbc).depth = 7 := by
  simp [halfAdder4]

lemma halfAdder4_usesOnly {m : ℕ} (a b s c : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (hac : a ≠ c) (hbs : b ≠ s) (hbc : b ≠ c) :
    (halfAdder4 a b s c hab has hac hbs hbc).UsesOnly {a, b, s, c} := by
  refine LayeredCircuit.seq_usesOnly ?_ (LayeredCircuit.seq_usesOnly ?_ ?_)
  · exact (cnotGate_usesOnly a s has).mono (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> simp)
  · exact (cnotGate_usesOnly b s hbs).mono (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> simp)
  · exact (toffoliOn_usesOnly a b c hab hac hbc).mono
      (by intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> simp)

lemma act_halfAdder4_ket {m : ℕ} (a b s c : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (hac : a ≠ c) (hbs : b ≠ s) (hbc : b ≠ c) (hsc : s ≠ c)
    (x : Qubits m) (hxs : x s = false) (hxc : x c = false) :
    act (halfAdder4 a b s c hab has hac hbs hbc).unitary (ket x) =
      ket (fun w => if w = s then xor (x a) (x b) else if w = c then x a && x b else x w) := by
  simp only [halfAdder4, LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket, act_toffoliOn_ket]
  congr 1
  funext w
  by_cases hws : w = s
  · subst hws
    simp only [Function.update_self, Function.update_of_ne hsc, Function.update_of_ne has,
      Function.update_of_ne hbs, hxs, Bool.false_xor, ite_true]
  · by_cases hwc : w = c
    · subst hwc
      simp only [Function.update_self, Function.update_of_ne hsc.symm, Function.update_of_ne has,
        Function.update_of_ne hbs, hxc, Bool.false_xor, if_neg hws, ite_true]
    · simp only [Function.update_of_ne hwc, Function.update_of_ne hws, if_neg hws, if_neg hwc]

lemma bool_halfAdder_arith (va vb : Bool) :
    (if xor va vb then 1 else 0) + 2 * (if va && vb then 1 else 0) =
      (if va then 1 else 0) + (if vb then 1 else 0) := by
  cases va <;> cases vb <;> decide

noncomputable def fullAdder5 {m : ℕ} (a b c s cout : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (haco : a ≠ cout)
    (hbs : b ≠ s) (hbco : b ≠ cout)
    (hcs : c ≠ s) (hcco : c ≠ cout) (hsco : s ≠ cout) : LayeredCircuit m :=
  (cnotGate a s has).seq
    ((cnotGate b s hbs).seq
      ((toffoliOn a b cout hab haco hbco).seq
        ((toffoliOn s c cout hcs.symm hsco hcco).seq
          (cnotGate c s hcs))))

@[simp] lemma fullAdder5_size {m : ℕ} (a b c s cout : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (haco : a ≠ cout)
    (hbs : b ≠ s) (hbco : b ≠ cout)
    (hcs : c ≠ s) (hcco : c ≠ cout) (hsco : s ≠ cout) :
    (fullAdder5 a b c s cout hab has haco hbs hbco hcs hcco hsco).size = 13 := by
  simp [fullAdder5]

@[simp] lemma fullAdder5_depth {m : ℕ} (a b c s cout : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (haco : a ≠ cout)
    (hbs : b ≠ s) (hbco : b ≠ cout)
    (hcs : c ≠ s) (hcco : c ≠ cout) (hsco : s ≠ cout) :
    (fullAdder5 a b c s cout hab has haco hbs hbco hcs hcco hsco).depth = 13 := by
  simp [fullAdder5]

lemma fullAdder5_usesOnly {m : ℕ} (a b c s cout : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (haco : a ≠ cout)
    (hbs : b ≠ s) (hbco : b ≠ cout)
    (hcs : c ≠ s) (hcco : c ≠ cout) (hsco : s ≠ cout) :
    (fullAdder5 a b c s cout hab has haco hbs hbco hcs hcco hsco).UsesOnly
      {a, b, c, s, cout} := by
  refine LayeredCircuit.seq_usesOnly ?_
    (LayeredCircuit.seq_usesOnly ?_
      (LayeredCircuit.seq_usesOnly ?_
        (LayeredCircuit.seq_usesOnly ?_ ?_)))
  · exact (cnotGate_usesOnly a s has).mono (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> simp)
  · exact (cnotGate_usesOnly b s hbs).mono (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> simp)
  · exact (toffoliOn_usesOnly a b cout hab haco hbco).mono
      (by intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> simp)
  · exact (toffoliOn_usesOnly s c cout hcs.symm hsco hcco).mono
      (by intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> simp)
  · exact (cnotGate_usesOnly c s hcs).mono (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> simp)

lemma act_fullAdder5_ket {m : ℕ} (a b c s cout : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (haco : a ≠ cout)
    (hbs : b ≠ s) (hbco : b ≠ cout)
    (hcs : c ≠ s) (hcco : c ≠ cout) (hsco : s ≠ cout)
    (x : Qubits m) (hxs : x s = false) (hxco : x cout = false) :
    act (fullAdder5 a b c s cout hab has haco hbs hbco hcs hcco hsco).unitary (ket x) =
      ket (fun w =>
        if w = s then xor (xor (x a) (x b)) (x c)
        else if w = cout then xor (x a && x b) (xor (x a) (x b) && x c)
        else x w) := by
  simp only [fullAdder5, LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket, act_toffoliOn_ket]
  congr 1
  funext w
  by_cases hws : w = s
  · subst hws
    simp only [Function.update_self, Function.update_of_ne hsco, Function.update_of_ne hcs,
      Function.update_of_ne hcco, Function.update_of_ne has, Function.update_of_ne hbs,
      hxs, Bool.false_xor, ite_true]
  · by_cases hwco : w = cout
    · subst hwco
      simp only [Function.update_self, Function.update_of_ne hsco.symm, Function.update_of_ne hsco,
        Function.update_of_ne hcco, Function.update_of_ne hcs, Function.update_of_ne has,
        Function.update_of_ne hbs, hxs, hxco, Bool.false_xor, if_neg hws, ite_true]
    · simp only [Function.update_of_ne hws, Function.update_of_ne hwco, if_neg hws, if_neg hwco]

lemma bool_fullAdder_arith (va vb vc : Bool) :
    (if xor (xor va vb) vc then 1 else 0) +
      2 * (if xor (va && vb) (xor va vb && vc) then 1 else 0) =
      (if va then 1 else 0) + (if vb then 1 else 0) + (if vc then 1 else 0) := by
  cases va <;> cases vb <;> cases vc <;> decide

private def takeTriples {α : Type*} : List α → List (α × α × α) × List α
  | a :: b :: c :: rest =>
    let res := takeTriples rest
    ((a, b, c) :: res.1, res.2)
  | rem => ([], rem)

private lemma takeTriples_ind {α : Type*} (P : List α → Prop)
    (h0 : P []) (h1 : ∀ a, P [a]) (h2 : ∀ a b, P [a, b])
    (h3 : ∀ a b c rest, P rest → P (a :: b :: c :: rest)) (L : List α) : P L := by
  match L with
  | [] => exact h0
  | [a] => exact h1 a
  | [a, b] => exact h2 a b
  | a :: b :: c :: rest => exact h3 a b c rest (takeTriples_ind P h0 h1 h2 h3 rest)
termination_by L.length

private lemma takeTriples_fst_length {α : Type*} (L : List α) :
    (takeTriples L).1.length = L.length / 3 := by
  refine takeTriples_ind (fun L => (takeTriples L).1.length = L.length / 3)
    (by simp [takeTriples]) (fun a => by simp [takeTriples])
    (fun a b => by simp [takeTriples]) (fun a b c rest ih => ?_) L
  change ((a, b, c) :: (takeTriples rest).1).length = (rest.length + 3) / 3
  simp only [List.length_cons, ih]
  omega

private lemma takeTriples_snd_length {α : Type*} (L : List α) :
    (takeTriples L).2.length = L.length % 3 := by
  refine takeTriples_ind (fun L => (takeTriples L).2.length = L.length % 3)
    (by simp [takeTriples]) (fun a => by simp [takeTriples]) (fun a b => by simp [takeTriples])
    (fun a b c rest ih => ?_) L
  change (takeTriples rest).2.length = (rest.length + 3) % 3
  simp only [ih]
  omega

private lemma takeTriples_mem_snd {α : Type*} {L : List α} {x : α} (hx : x ∈ (takeTriples L).2) :
    x ∈ L := by
  revert hx
  refine takeTriples_ind (fun L => x ∈ (takeTriples L).2 → x ∈ L)
    (by simp [takeTriples]) (fun a => by simp [takeTriples]) (fun a b => by simp [takeTriples])
    (fun a b c rest ih h => by
      change x ∈ (takeTriples rest).2 at h
      simp [ih h]) L

private lemma takeTriples_mem_fst {α : Type*} {L : List α} {t : α × α × α}
    (ht : t ∈ (takeTriples L).1) : t.1 ∈ L ∧ t.2.1 ∈ L ∧ t.2.2 ∈ L := by
  revert ht
  refine takeTriples_ind (fun L => t ∈ (takeTriples L).1 → t.1 ∈ L ∧ t.2.1 ∈ L ∧ t.2.2 ∈ L)
    (by simp [takeTriples]) (fun a => by simp [takeTriples]) (fun a b => by simp [takeTriples])
    (fun a b c rest ih h => by
      change t ∈ (a, b, c) :: (takeTriples rest).1 at h
      rw [List.mem_cons] at h
      rcases h with rfl | hrest
      · simp
      · have h' := ih hrest
        simp [h'.1, h'.2.1, h'.2.2]) L

private lemma takeTriples_nodup_snd {α : Type*} {L : List α} (hL : L.Nodup) :
    (takeTriples L).2.Nodup := by
  revert hL
  refine takeTriples_ind (fun L => L.Nodup → (takeTriples L).2.Nodup)
    (by simp [takeTriples]) (fun a => by simp [takeTriples]) (fun a b => by simp [takeTriples])
    (fun a b c rest ih h => by
      change (takeTriples rest).2.Nodup
      rw [List.nodup_cons, List.nodup_cons, List.nodup_cons] at h
      exact ih h.2.2.2) L

private lemma takeTriples_triples_disjoint {α : Type*} [DecidableEq α] {L : List α}
    (hL : L.Nodup) :
    (takeTriples L).1.Pairwise (fun t1 t2 =>
      Disjoint ({t1.1, t1.2.1, t1.2.2} : Finset α) ({t2.1, t2.2.1, t2.2.2} : Finset α)) ∧
    ∀ t ∈ (takeTriples L).1, t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 := by
  revert hL
  refine takeTriples_ind (fun L => L.Nodup →
      ((takeTriples L).1.Pairwise fun t1 t2 =>
        Disjoint ({t1.1, t1.2.1, t1.2.2} : Finset α) ({t2.1, t2.2.1, t2.2.2} : Finset α)) ∧
      ∀ t ∈ (takeTriples L).1, t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2)
    (by simp [takeTriples]) (fun a => by simp [takeTriples]) (fun a b => by simp [takeTriples])
    (fun a b c rest ih h => by
      have ha : a ≠ b ∧ a ≠ c ∧ a ∉ rest := by
        rw [List.nodup_cons] at h; simp at h; exact ⟨h.1.1, h.1.2.1, h.1.2.2⟩
      have hb : b ≠ c ∧ b ∉ rest := by
        rw [List.nodup_cons, List.nodup_cons] at h; simp at h; exact ⟨h.2.1.1, h.2.1.2⟩
      have hc : c ∉ rest := by
        rw [List.nodup_cons, List.nodup_cons, List.nodup_cons] at h; exact h.2.2.1
      have hrest_nd : rest.Nodup := by
        rw [List.nodup_cons, List.nodup_cons, List.nodup_cons] at h; exact h.2.2.2
      rcases ih hrest_nd with ⟨hpw_rest, hdistinct_rest⟩
      change ((a, b, c) :: (takeTriples rest).1).Pairwise _ ∧
        ∀ t ∈ (a, b, c) :: (takeTriples rest).1, _
      refine ⟨List.pairwise_cons.mpr ⟨?_, hpw_rest⟩, ?_⟩
      · intro t ht
        have hm := takeTriples_mem_fst ht
        rw [Finset.disjoint_left]
        intro w hw1 hw2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw1 hw2
        have hw_rest : w ∈ rest := by rcases hw2 with rfl | rfl | rfl <;> tauto
        rcases hw1 with rfl | rfl | rfl
        · exact ha.2.2 hw_rest
        · exact hb.2 hw_rest
        · exact hc hw_rest
      · intro t ht
        rw [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact ⟨ha.1, ha.2.1, hb.1⟩
        · exact hdistinct_rest t ht) L

private lemma takeTriples_countP {α : Type*} (L : List α) (p : α → Bool) :
    L.countP p =
      ((takeTriples L).1.map (fun t =>
        (if p t.1 then 1 else 0) + (if p t.2.1 then 1 else 0) +
          (if p t.2.2 then 1 else 0))).sum +
      (takeTriples L).2.countP p := by
  refine takeTriples_ind (fun L => L.countP p =
      ((takeTriples L).1.map (fun t =>
        (if p t.1 then 1 else 0) + (if p t.2.1 then 1 else 0) +
          (if p t.2.2 then 1 else 0))).sum +
      (takeTriples L).2.countP p)
    (by simp [takeTriples]) (fun a => by simp [takeTriples]) (fun a b => by simp [takeTriples])
    (fun a b c rest ih => by
      change (a :: b :: c :: rest).countP p =
        ((if p a then 1 else 0) + (if p b then 1 else 0) + (if p c then 1 else 0) +
          ((takeTriples rest).1.map _).sum) + (takeTriples rest).2.countP p
      simp only [List.countP_cons, ih]
      split_ifs <;> omega) L

private def numberItems {α : Type*} (start : ℕ) : List α → List (α × ℕ)
  | [] => []
  | x :: xs => (x, start) :: numberItems (start + 1) xs

private lemma numberItems_map_fst {α : Type*} (start : ℕ) (xs : List α) :
    (numberItems start xs).map Prod.fst = xs := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih => simp [numberItems, ih]

private lemma mem_numberItems_bounds {α : Type*} {start : ℕ} {xs : List α} {p : α × ℕ}
    (hp : p ∈ numberItems start xs) :
    start ≤ p.2 ∧ p.2 < start + xs.length ∧ p.1 ∈ xs := by
  induction xs generalizing start with
  | nil => cases hp
  | cons x xs ih =>
    simp only [numberItems, List.mem_cons] at hp
    rcases hp with rfl | hrest
    · simp
    · rcases ih hrest with ⟨h1, h2, h3⟩
      simp only [List.length_cons, List.mem_cons]
      exact ⟨by omega, by omega, Or.inr h3⟩

private lemma numberItems_pairwise_ne {α : Type*} (start : ℕ) (xs : List α) :
    (numberItems start xs).Pairwise (fun p q => p.2 ≠ q.2) := by
  induction xs generalizing start with
  | nil => simp [numberItems]
  | cons x xs ih =>
    simp only [numberItems, List.pairwise_cons]
    refine ⟨fun q hq heq => ?_, ih (start + 1)⟩
    have hlt := (mem_numberItems_bounds hq).1
    omega

private lemma numberItems_length {α : Type*} (start : ℕ) (xs : List α) :
    (numberItems start xs).length = xs.length := by
  induction xs generalizing start with
  | nil => simp [numberItems]
  | cons x xs ih => simp [numberItems, ih]

private lemma numberItems_filter_length {α : Type*} (start : ℕ) (xs : List α) (P : α → Bool) :
    ((numberItems start xs).filter fun p => P p.1).length = (xs.filter P).length := by
  induction xs generalizing start with
  | nil => simp [numberItems]
  | cons x xs ih =>
    simp only [numberItems, List.filter_cons]
    cases P x <;> simp [ih]

private lemma nodup_map_of_pairwise {α β : Type*} {xs : List α} {f : α → β}
    (hpw : xs.Pairwise (fun a b => f a ≠ f b)) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    rw [List.pairwise_cons] at hpw
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun h => ?_, ih hpw.2⟩
    rw [List.mem_map] at h
    rcases h with ⟨b, hb, heq⟩
    exact hpw.1 b hb heq.symm

private lemma pairwise_eq_of_snd {α β : Type*} {xs : List (α × β)}
    (hpw : xs.Pairwise (fun p q => p.2 ≠ q.2))
    {p q : α × β} (hp : p ∈ xs) (hq : q ∈ xs) (hsnd : p.2 = q.2) : p = q := by
  induction xs with
  | nil => cases hp
  | cons a rest ih =>
    rw [List.pairwise_cons] at hpw
    rw [List.mem_cons] at hp hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · rfl
    · exact absurd hsnd (hpw.1 q hq)
    · exact absurd hsnd.symm (hpw.1 p hp)
    · exact ih hpw.2 hp hq

private lemma sum_map_finRange {k : ℕ} (f : Fin k → ℕ) :
    ((List.finRange k).map f).sum = ∑ b : Fin k, f b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map, Fin.sum_univ_succ]
    exact congrArg (f 0 + ·) (ih (f ∘ Fin.succ))

private lemma nodup_flatMap_of {α β : Type*} {xs : List α} {f : α → List β}
    (hxs : xs.Nodup) (hnd : ∀ a ∈ xs, (f a).Nodup)
    (hdisj : ∀ a ∈ xs, ∀ b ∈ xs, a ≠ b → ∀ w, w ∈ f a → w ∉ f b) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    rw [List.nodup_cons] at hxs
    simp only [List.flatMap_cons, List.nodup_append]
    refine ⟨hnd a List.mem_cons_self, ih hxs.2 (fun b hb => hnd b (List.mem_cons_of_mem _ hb))
      (fun b hb c hc hne w hwb => hdisj b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc) hne w hwb), ?_⟩
    intro w hwa w' hwr heq
    subst heq
    rw [List.mem_flatMap] at hwr
    rcases hwr with ⟨b, hb, hwb⟩
    have hab : a ≠ b := fun h => hxs.1 (h ▸ hb)
    exact hdisj a List.mem_cons_self b (List.mem_cons_of_mem _ hb) hab w hwa hwb

private lemma countP_flatMap {α β : Type*} (xs : List α) (f : α → List β) (p : β → Bool) :
    (xs.flatMap f).countP p = (xs.map fun a => (f a).countP p).sum := by
  induction xs with
  | nil => simp
  | cons a rest ih => simp [List.flatMap_cons, List.countP_append, ih]

abbrev hcEll (n : ℕ) : ℕ := Nat.clog 2 (n + 1)

abbrev hammingAnc (n : ℕ) : ℕ := 2 * n + 2 * hcEll n + 1

abbrev hcWires (n : ℕ) : ℕ := (n + hcEll n) + hammingAnc n

lemma hcEll_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ hcEll n := by
  by_contra h
  have h0 : hcEll n = 0 := by omega
  have hle : n + 1 ≤ 2 ^ 0 := clog2_le_iff_le_pow.mp (le_of_eq h0)
  omega

lemma hcEll_le_self (n : ℕ) : hcEll n ≤ n := by
  rw [hcEll, clog2_le_iff_le_pow]
  induction n with
  | zero => decide
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · decide
    · rw [pow_succ']; omega

lemma lt_two_pow_hcEll (n : ℕ) : n < 2 ^ hcEll n := by
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) (n + 1)
  change n + 1 ≤ 2 ^ hcEll n at h
  omega

def hcQWire (n : ℕ) (i : Fin n) : Fin (hcWires n) :=
  ⟨i.1, by dsimp only [hcWires, hammingAnc]; have := i.isLt; omega⟩

def hcOutWire (n : ℕ) (b : Fin (hcEll n)) : Fin (hcWires n) :=
  ⟨n + b.1, by dsimp only [hcWires, hammingAnc]; have := b.isLt; omega⟩

def hcPoolWire (n : ℕ) (k : ℕ) (hk : k < 2 * n) : Fin (hcWires n) :=
  ⟨n + hcEll n + k, by dsimp only [hcWires, hammingAnc]; omega⟩

def hcSumWire (n : ℕ) (b : Fin (hcEll n)) : Fin (hcWires n) :=
  ⟨n + hcEll n + 2 * n + b.1, by dsimp only [hcWires, hammingAnc]; have := b.isLt; omega⟩

def hcCarryWire (n : ℕ) (b : ℕ) (hb : b ≤ hcEll n) : Fin (hcWires n) :=
  ⟨n + hcEll n + 2 * n + hcEll n + b, by dsimp only [hcWires, hammingAnc]; omega⟩

private def fwdSupport (n : ℕ) : Finset (Fin (hcWires n)) :=
  Finset.univ.filter fun w => w.1 < n ∨ n + hcEll n ≤ w.1

private lemma mem_fwdSupport_iff {n : ℕ} {w : Fin (hcWires n)} :
    w ∈ fwdSupport n ↔ w.1 < n ∨ n + hcEll n ≤ w.1 := by
  simp [fwdSupport]

private def csRawSum (n : ℕ) (idx : ℕ) : Fin (hcWires n) :=
  ⟨(n + hcEll n + 2 * idx) % hcWires n,
    Nat.mod_lt _ (by dsimp only [hcWires, hammingAnc]; omega)⟩

private def csRawCarry (n : ℕ) (idx : ℕ) : Fin (hcWires n) :=
  ⟨(n + hcEll n + 2 * idx + 1) % hcWires n,
    Nat.mod_lt _ (by dsimp only [hcWires, hammingAnc]; omega)⟩

private lemma csRawSum_val {n : ℕ} {idx : ℕ} (hidx : idx < n) :
    (csRawSum n idx).1 = n + hcEll n + 2 * idx := by
  dsimp [csRawSum]
  exact Nat.mod_eq_of_lt (by dsimp only [hcWires, hammingAnc]; omega)

private lemma csRawCarry_val {n : ℕ} {idx : ℕ} (hidx : idx < n) :
    (csRawCarry n idx).1 = n + hcEll n + 2 * idx + 1 := by
  dsimp [csRawCarry]
  exact Nat.mod_eq_of_lt (by dsimp only [hcWires, hammingAnc]; omega)

private structure CSState (n : ℕ) where
  cols : Fin (hcEll n) → List (Fin (hcWires n))
  nextPair : ℕ

private def csInit (n : ℕ) : CSState n where
  cols b := if b.1 = 0 then (List.finRange n).map (hcQWire n) else []
  nextPair := 0

private def csAllTriples (n : ℕ) (st : CSState n) :
    List (Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) :=
  (List.finRange (hcEll n)).flatMap fun b =>
    (takeTriples (st.cols b)).1.map fun t => (b, t)

private lemma csAllTriples_length (n : ℕ) (st : CSState n) :
    (csAllTriples n st).length = ∑ b : Fin (hcEll n), (st.cols b).length / 3 := by
  simp only [csAllTriples, List.length_flatMap, List.length_map, takeTriples_fst_length]
  exact sum_map_finRange (fun b => (st.cols b).length / 3)

private lemma csAllTriples_filter_fst_length (n : ℕ) (st : CSState n) (b : Fin (hcEll n)) :
    ((csAllTriples n st).filter fun p => decide (p.1 = b)).length = (st.cols b).length / 3 := by
  rw [← takeTriples_fst_length (st.cols b)]
  dsimp only [csAllTriples]
  have hf : ∀ bs : List (Fin (hcEll n)), bs.Nodup →
      ((bs.flatMap fun b' => (takeTriples (st.cols b')).1.map fun t => (b', t)).filter
        fun p => decide (p.1 = b)).length =
      if b ∈ bs then (takeTriples (st.cols b)).1.length else 0 := by
    intro bs hbs
    induction bs with
    | nil => simp
    | cons a rest ih =>
      rw [List.nodup_cons] at hbs
      simp only [List.flatMap_cons, List.filter_append, List.length_append, ih hbs.2, List.mem_cons]
      have hcur : (((takeTriples (st.cols a)).1.map fun t => (a, t)).filter
          fun p => decide (p.1 = b)).length =
          if a = b then (takeTriples (st.cols a)).1.length else 0 := by
        by_cases hab : a = b
        · subst hab
          have hself : ((takeTriples (st.cols a)).1.map fun t => (a, t)).filter
              (fun p => decide (p.1 = a)) = (takeTriples (st.cols a)).1.map fun t => (a, t) := by
            rw [List.filter_eq_self]
            intro p hp
            simp only [List.mem_map] at hp
            rcases hp with ⟨t, _, rfl⟩
            simp
          rw [hself, List.length_map, if_pos rfl]
        · have hnil : ((takeTriples (st.cols a)).1.map fun t => (a, t)).filter
              (fun p => decide (p.1 = b)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro p hp
            simp only [List.mem_map] at hp
            rcases hp with ⟨t, _, rfl⟩
            simp [hab]
          rw [hnil, List.length_nil, if_neg hab]
      rw [hcur]
      by_cases hab : a = b
      · subst hab; simp [hbs.1]
      · simp [hab, ne_comm.mp hab]
  rw [hf (List.finRange (hcEll n)) (List.nodup_finRange _)]
  simp

private lemma csAllTriples_filter_pred_length (n : ℕ) (st : CSState n) (b : Fin (hcEll n)) :
    ((csAllTriples n st).filter fun p => decide (p.1.1 + 1 = b.1)).length =
      if h : 0 < b.1 then (st.cols ⟨b.1 - 1, by have := b.isLt; omega⟩).length / 3 else 0 := by
  by_cases hb : 0 < b.1
  · rw [dif_pos hb]
    let prev : Fin (hcEll n) := ⟨b.1 - 1, by have := b.isLt; omega⟩
    have hpred : (fun p : Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n)) =>
        decide (p.1.1 + 1 = b.1)) =
        (fun p => decide (p.1 = prev)) := by
      funext p
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Fin.ext_iff, prev]
      omega
    rw [hpred, csAllTriples_filter_fst_length]
  · rw [dif_neg hb]
    have hnil : ((csAllTriples n st).filter fun p => decide (p.1.1 + 1 = b.1)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro p _ h
      simp only [decide_eq_true_eq] at h
      omega
    rw [hnil, List.length_nil]

private def csStep (n : ℕ) (st : CSState n) : CSState n :=
  let ann := numberItems st.nextPair (csAllTriples n st)
  { cols := fun b =>
      (takeTriples (st.cols b)).2 ++
      ((ann.filter fun p => decide (p.1.1 = b)).map fun p => csRawSum n p.2) ++
      ((ann.filter fun p => decide (p.1.1.1 + 1 = b.1)).map fun p => csRawCarry n p.2)
    nextPair := st.nextPair + (csAllTriples n st).length }

private def csStateAt (n : ℕ) : ℕ → CSState n
  | 0 => csInit n
  | r + 1 => csStep n (csStateAt n r)

private lemma csStep_col_length (n : ℕ) (st : CSState n) (b : Fin (hcEll n)) :
    ((csStep n st).cols b).length =
      (st.cols b).length % 3 + (st.cols b).length / 3 +
        if h : 0 < b.1 then (st.cols ⟨b.1 - 1, by have := b.isLt; omega⟩).length / 3 else 0 := by
  dsimp only [csStep]
  rw [List.length_append, List.length_append, List.length_map, List.length_map,
    takeTriples_snd_length,
    numberItems_filter_length st.nextPair (csAllTriples n st) (fun q => decide (q.1 = b)),
    numberItems_filter_length st.nextPair (csAllTriples n st) (fun q => decide (q.1.1 + 1 = b.1)),
    csAllTriples_filter_fst_length, csAllTriples_filter_pred_length]

private lemma cs_step_num_bound (x y M : ℕ) (hx : x ≤ M) (hy : y ≤ M) :
    3 * (x % 3 + x / 3 + y / 3) ≤ 2 * M + 3 := by
  omega

private lemma nat_mul_sup_le {ι : Type*} (s : Finset ι) (c : ℕ) (f : ι → ℕ) (B : ℕ) :
    c * s.sup f ≤ B ↔ ∀ x ∈ s, c * f x ≤ B := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  · constructor
    · intro h x hx
      exact le_trans (Nat.mul_le_mul_left c (Finset.le_sup hx)) h
    · intro h
      have hdiv : ∀ x ∈ s, f x ≤ B / c := fun x hx =>
        (Nat.le_div_iff_mul_le hc).mpr (by rw [mul_comm]; exact h x hx)
      exact (Nat.mul_le_mul_left c (Finset.sup_le hdiv)).trans (Nat.mul_div_le B c)

private def maxColLen (n : ℕ) (st : CSState n) : ℕ :=
  Finset.univ.sup fun b : Fin (hcEll n) => (st.cols b).length

private lemma maxColLen_step_le (n : ℕ) (st : CSState n) :
    3 * (maxColLen n (csStep n st) - 3) ≤ 2 * (maxColLen n st - 3) := by
  have h1 : 3 * maxColLen n (csStep n st) ≤ 2 * maxColLen n st + 3 := by
    dsimp only [maxColLen]
    rw [nat_mul_sup_le]
    intro b _
    rw [csStep_col_length]
    have hx : (st.cols b).length ≤ Finset.univ.sup (fun b => (st.cols b).length) :=
      Finset.le_sup (f := fun b : Fin (hcEll n) => (st.cols b).length) (Finset.mem_univ b)
    by_cases hb : 0 < b.1
    · rw [dif_pos hb]
      have hy : (st.cols ⟨b.1 - 1, by have := b.isLt; omega⟩).length ≤
          Finset.univ.sup (fun b => (st.cols b).length) :=
        Finset.le_sup (f := fun b : Fin (hcEll n) => (st.cols b).length) (Finset.mem_univ _)
      exact cs_step_num_bound _ _ _ hx hy
    · rw [dif_neg hb]
      omega
  omega

private lemma maxColLen_two_steps (n : ℕ) (st : CSState n) :
    2 * (maxColLen n (csStep n (csStep n st)) - 3) ≤ maxColLen n st - 3 := by
  have h1 := maxColLen_step_le n st
  have h2 := maxColLen_step_le n (csStep n st)
  omega

private lemma csStateAt_init_max (n : ℕ) :
    maxColLen n (csStateAt n 0) ≤ n := by
  dsimp only [maxColLen, csStateAt, csInit]
  refine Finset.sup_le fun b _ => ?_
  split_ifs <;> simp

private lemma csStateAt_two_mul_clog (n : ℕ) :
    ∀ b : Fin (hcEll n), ((csStateAt n (2 * hcEll n)).cols b).length ≤ 3 := by
  have hpow : ∀ k : ℕ, 2 ^ k * (maxColLen n (csStateAt n (2 * k)) - 3) ≤
      maxColLen n (csStateAt n 0) - 3 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, csStateAt, csStateAt, pow_succ']
      have h2 := maxColLen_two_steps n (csStateAt n (2 * k))
      calc 2 * 2 ^ k * (maxColLen n (csStep n (csStep n (csStateAt n (2 * k)))) - 3)
          = 2 ^ k * (2 * (maxColLen n (csStep n (csStep n (csStateAt n (2 * k)))) - 3)) := by
            ring
        _ ≤ 2 ^ k * (maxColLen n (csStateAt n (2 * k)) - 3) := Nat.mul_le_mul_left _ h2
        _ ≤ maxColLen n (csStateAt n 0) - 3 := ih
  have hk := hpow (hcEll n)
  have h0 := csStateAt_init_max n
  have hlt := lt_two_pow_hcEll n
  have hsub0 : maxColLen n (csStateAt n (2 * hcEll n)) - 3 = 0 := by
    by_contra hne
    have hge1 : 1 ≤ maxColLen n (csStateAt n (2 * hcEll n)) - 3 := by omega
    have hmul : 2 ^ hcEll n ≤ 2 ^ hcEll n * (maxColLen n (csStateAt n (2 * hcEll n)) - 3) :=
      Nat.le_mul_of_pos_right _ hge1
    omega
  intro b
  have hb : ((csStateAt n (2 * hcEll n)).cols b).length ≤
      maxColLen n (csStateAt n (2 * hcEll n)) := by
    dsimp only [maxColLen]
    exact Finset.le_sup (f := fun b : Fin (hcEll n) => ((csStateAt n (2 * hcEll n)).cols b).length)
      (Finset.mem_univ b)
  omega

private lemma csStateAt_three_mul_clog (n : ℕ) :
    ∀ b : Fin (hcEll n), ((csStateAt n (3 * hcEll n)).cols b).length ≤ 2 := by
  have hpref : ∀ t : ℕ,
      (∀ b : Fin (hcEll n), ((csStateAt n (2 * hcEll n + t)).cols b).length ≤ 3) ∧
      (∀ b : Fin (hcEll n), b.1 < t →
        ((csStateAt n (2 * hcEll n + t)).cols b).length ≤ 2) := by
    intro t
    induction t with
    | zero => exact ⟨csStateAt_two_mul_clog n, fun b hb => by omega⟩
    | succ t ih =>
      rcases ih with ⟨ih3, ih2⟩
      rw [← Nat.add_assoc]
      dsimp only [csStateAt]
      refine ⟨fun b => ?_, fun b hb => ?_⟩
      · rw [csStep_col_length]
        have hx := ih3 b
        by_cases h0 : 0 < b.1
        · rw [dif_pos h0]
          have hy := ih3 ⟨b.1 - 1, by have := b.isLt; omega⟩
          omega
        · rw [dif_neg h0]; omega
      · rw [csStep_col_length]
        have hx := ih3 b
        by_cases h0 : 0 < b.1
        · rw [dif_pos h0]
          have hy := ih2 ⟨b.1 - 1, by have := b.isLt; omega⟩ (by simp; omega)
          omega
        · rw [dif_neg h0]; omega
  intro b
  have h3 : 3 * hcEll n = 2 * hcEll n + hcEll n := by omega
  rw [h3]
  exact (hpref (hcEll n)).2 b b.isLt

private structure CSValid (n : ℕ) (st : CSState n) : Prop where
  pair_le : st.nextPair ≤ n
  nodup : ((List.finRange (hcEll n)).flatMap st.cols).Nodup
  wire_bound : ∀ b : Fin (hcEll n), ∀ w ∈ st.cols b,
    w.1 < n ∨ (n + hcEll n ≤ w.1 ∧ w.1 < n + hcEll n + 2 * st.nextPair)
  work_le : (∑ b : Fin (hcEll n), (st.cols b).length) + st.nextPair ≤ n

private lemma csValid_nextPair_add_triples {n : ℕ} {st : CSState n} (hv : CSValid n st) :
    st.nextPair + (csAllTriples n st).length ≤ n := by
  have hT_le_sum : 3 * (csAllTriples n st).length ≤ ∑ b : Fin (hcEll n), (st.cols b).length := by
    rw [csAllTriples_length, Finset.mul_sum]
    exact Finset.sum_le_sum fun _ _ => by omega
  have := hv.work_le
  omega

private lemma csValid_cols_nodup {n : ℕ} {st : CSState n} (hv : CSValid n st) :
    ∀ b : Fin (hcEll n), (st.cols b).Nodup ∧
      ∀ b' : Fin (hcEll n), b ≠ b' → ∀ w, w ∈ st.cols b → w ∉ st.cols b' := by
  have hfm := hv.nodup
  have hmem : ∀ b : Fin (hcEll n), (st.cols b).Nodup := by
    intro b
    have hb : b ∈ List.finRange (hcEll n) := List.mem_finRange b
    generalize List.finRange (hcEll n) = bs at hfm hb
    induction bs with
    | nil => cases hb
    | cons a rest ih =>
      simp only [List.flatMap_cons, List.nodup_append] at hfm
      rw [List.mem_cons] at hb
      rcases hb with rfl | hrest
      · exact hfm.1
      · exact ih hfm.2.1 hrest
  refine fun b => ⟨hmem b, fun b' hne w hwb hwb' => ?_⟩
  have ha : b ∈ List.finRange (hcEll n) := List.mem_finRange b
  have hb' : b' ∈ List.finRange (hcEll n) := List.mem_finRange b'
  have hnd := List.nodup_finRange (hcEll n)
  generalize List.finRange (hcEll n) = bs at hfm ha hb' hnd
  induction bs with
  | nil => cases ha
  | cons a rest ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.flatMap_cons, List.nodup_append] at hfm
    rw [List.mem_cons] at ha hb'
    rcases ha with rfl | ha <;> rcases hb' with rfl | hb'
    · exact hne rfl
    · exact hfm.2.2 w hwb w (List.mem_flatMap.mpr ⟨b', hb', hwb'⟩) rfl
    · exact hfm.2.2 w hwb' w (List.mem_flatMap.mpr ⟨b, ha, hwb⟩) rfl
    · exact ih hfm.2.1 ha hb' hnd.2

private lemma csValid_init (n : ℕ) (hn : 1 ≤ n) : CSValid n (csInit n) := by
  have hell := hcEll_pos hn
  refine ⟨by simp [csInit], ?_, ?_, ?_⟩
  · dsimp only [csInit]
    apply nodup_flatMap_of (List.nodup_finRange _)
    · intro b _
      split_ifs
      · refine List.Nodup.map (fun i j h => ?_) (List.nodup_finRange n)
        exact Fin.ext (by simpa [hcQWire] using congrArg Fin.val h)
      · simp
    · intro a _ b _ hab w hwa hwb
      split_ifs at hwa hwb with ha hb
      · exact hab (Fin.ext (by omega))
      · simp at hwb
      · simp at hwa
      · simp at hwa
  · intro b w hw
    dsimp only [csInit] at hw
    split_ifs at hw
    · simp only [List.mem_map, List.mem_finRange, true_and] at hw
      rcases hw with ⟨i, rfl⟩
      left; exact i.isLt
    · cases hw
  · dsimp only [csInit]
    let z0 : Fin (hcEll n) := ⟨0, hell⟩
    have hlen : ∀ b : Fin (hcEll n),
        (if b.1 = 0 then (List.finRange n).map (hcQWire n) else []).length =
        if b = z0 then n else 0 := by
      intro b
      by_cases hb : b = z0
      · subst hb; simp [z0]
      · have hne : b.1 ≠ 0 := fun h => hb (Fin.ext h)
        rw [if_neg hne, if_neg hb, List.length_nil]
    simp_rw [hlen]
    simp

private lemma sum_shift_pred_le {m : ℕ} (hm : 1 ≤ m) (f : Fin m → ℕ) :
    (∑ b : Fin m, if h : 0 < b.1 then f ⟨b.1 - 1, by have := b.isLt; omega⟩ else 0) ≤
      ∑ b : Fin m, f b := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m = k + 1 := ⟨m - 1, by omega⟩
  have hsub : ∀ g : Fin (k + 1) → ℕ,
      (∑ b : Fin (k + 1), if h : 0 < b.1 then g ⟨b.1 - 1, by have := b.isLt; omega⟩ else 0) ≤
        ∑ b : Fin (k + 1), g b := by
    intro g
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp only [Fin.val_zero, lt_self_iff_false, ↓reduceDIte, zero_add, Fin.val_succ,
      Nat.zero_lt_succ, Nat.add_sub_cancel]
    exact Nat.le_add_right _ _
  subst hk
  exact hsub f

private lemma csValid_step {n : ℕ} (hn : 1 ≤ n) {st : CSState n} (hv : CSValid n st) :
    CSValid n (csStep n st) := by
  have hell := hcEll_pos hn
  have hnext_le : st.nextPair + (csAllTriples n st).length ≤ n :=
    csValid_nextPair_add_triples hv
  have hmem_lt : ∀ {p}, p ∈ numberItems st.nextPair (csAllTriples n st) → p.2 < n := by
    intro p hp
    have hb := mem_numberItems_bounds hp
    omega
  have hpair' : (csStep n st).nextPair ≤ n := hnext_le
  have hnodup_cols := csValid_cols_nodup hv
  have hwire' : ∀ b : Fin (hcEll n), ∀ w ∈ (csStep n st).cols b,
      w.1 < n ∨ (n + hcEll n ≤ w.1 ∧ w.1 < n + hcEll n + 2 * (csStep n st).nextPair) := by
    intro b w hw
    dsimp only [csStep] at hw ⊢
    simp only [List.mem_append, List.mem_map, List.mem_filter] at hw
    rcases hw with (hw | ⟨p, ⟨hp, _⟩, rfl⟩) | ⟨p, ⟨hp, _⟩, rfl⟩
    · rcases hv.wire_bound b w (takeTriples_mem_snd hw) with hq | hp
      · left; exact hq
      · right; omega
    · have hb := mem_numberItems_bounds hp
      right; rw [csRawSum_val (hmem_lt hp)]; omega
    · have hb := mem_numberItems_bounds hp
      right; rw [csRawCarry_val (hmem_lt hp)]; omega
  have hwork' : (∑ b : Fin (hcEll n), ((csStep n st).cols b).length) +
      (csStep n st).nextPair ≤ n := by
    have hcol_sum : (∑ b : Fin (hcEll n), ((csStep n st).cols b).length) =
        (∑ b : Fin (hcEll n), ((st.cols b).length % 3 + (st.cols b).length / 3)) +
        ∑ b : Fin (hcEll n),
          (if h : 0 < b.1 then (st.cols ⟨b.1 - 1, by have := b.isLt; omega⟩).length / 3 else 0) := by
      simp_rw [csStep_col_length, Finset.sum_add_distrib]
    have hcarry_le : (∑ b : Fin (hcEll n),
        (if h : 0 < b.1 then (st.cols ⟨b.1 - 1, by have := b.isLt; omega⟩).length / 3 else 0)) ≤
        ∑ b : Fin (hcEll n), (st.cols b).length / 3 :=
      sum_shift_pred_le hell (fun b => (st.cols b).length / 3)
    have hrem_add : (∑ b : Fin (hcEll n), ((st.cols b).length % 3 + (st.cols b).length / 3)) +
        (∑ b : Fin (hcEll n), (st.cols b).length / 3) + (csAllTriples n st).length =
        ∑ b : Fin (hcEll n), (st.cols b).length := by
      rw [csAllTriples_length, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      omega
    have hnext_val : (csStep n st).nextPair = st.nextPair + (csAllTriples n st).length := rfl
    have hwl := hv.work_le
    rw [hcol_sum, hnext_val]
    omega
  have hnodup' : ((List.finRange (hcEll n)).flatMap (csStep n st).cols).Nodup := by
    apply nodup_flatMap_of (List.nodup_finRange _)
    · intro b _
      dsimp only [csStep]
      rw [List.nodup_append, List.nodup_append]
      refine ⟨⟨takeTriples_nodup_snd (hnodup_cols b).1, ?_, ?_⟩, ?_, ?_⟩
      · refine nodup_map_of_pairwise ?_
        refine ((numberItems_pairwise_ne st.nextPair (csAllTriples n st)).filter _).imp_of_mem ?_
        intro p q hp hq hpq heq
        simp only [List.mem_filter] at hp hq
        have hval := congrArg Fin.val heq
        rw [csRawSum_val (hmem_lt hp.1), csRawSum_val (hmem_lt hq.1)] at hval
        exact hpq (by omega)
      · intro w hwr w' hws heq
        subst heq
        simp only [List.mem_map, List.mem_filter] at hws
        rcases hws with ⟨p, ⟨hp, _⟩, rfl⟩
        rcases hv.wire_bound b _ (takeTriples_mem_snd hwr) with hwq | hwp
        · have := csRawSum_val (hmem_lt hp); omega
        · have := (mem_numberItems_bounds hp).1; have := csRawSum_val (hmem_lt hp); omega
      · refine nodup_map_of_pairwise ?_
        refine ((numberItems_pairwise_ne st.nextPair (csAllTriples n st)).filter _).imp_of_mem ?_
        intro p q hp hq hpq heq
        simp only [List.mem_filter] at hp hq
        have hval := congrArg Fin.val heq
        rw [csRawCarry_val (hmem_lt hp.1), csRawCarry_val (hmem_lt hq.1)] at hval
        exact hpq (by omega)
      · intro w hwa w' hwc heq
        subst heq
        simp only [List.mem_append, List.mem_map, List.mem_filter] at hwa hwc
        rcases hwc with ⟨q, ⟨hq, _⟩, rfl⟩
        rcases hwa with hwr | ⟨p, ⟨hp, _⟩, heq⟩
        · rcases hv.wire_bound b _ (takeTriples_mem_snd hwr) with hwq | hwp
          · have := csRawCarry_val (hmem_lt hq); omega
          · have := (mem_numberItems_bounds hq).1; have := csRawCarry_val (hmem_lt hq); omega
        · have hval := congrArg Fin.val heq
          rw [csRawSum_val (hmem_lt hp), csRawCarry_val (hmem_lt hq)] at hval
          omega
    · intro a _ b _ hab w hwa hwb
      dsimp only [csStep] at hwa hwb
      simp only [List.mem_append, List.mem_map, List.mem_filter] at hwa hwb
      rcases hwa with (hwa | ⟨p, ⟨hp, hpa⟩, rfl⟩) | ⟨p, ⟨hp, hpa⟩, rfl⟩ <;>
        rcases hwb with (hwb | ⟨q, ⟨hq, hqb⟩, heq⟩) | ⟨q, ⟨hq, hqb⟩, heq⟩
      · exact (hnodup_cols a).2 b hab w (takeTriples_mem_snd hwa) (takeTriples_mem_snd hwb)
      · have hq1 := (mem_numberItems_bounds hq).1
        rcases hv.wire_bound a w (takeTriples_mem_snd hwa) with hwq | hwp
        · have := congrArg Fin.val heq; rw [csRawSum_val (hmem_lt hq)] at this; omega
        · have := congrArg Fin.val heq; rw [csRawSum_val (hmem_lt hq)] at this; omega
      · have hq1 := (mem_numberItems_bounds hq).1
        rcases hv.wire_bound a w (takeTriples_mem_snd hwa) with hwq | hwp
        · have := congrArg Fin.val heq; rw [csRawCarry_val (hmem_lt hq)] at this; omega
        · have := congrArg Fin.val heq; rw [csRawCarry_val (hmem_lt hq)] at this; omega
      · have hp1 := (mem_numberItems_bounds hp).1
        rcases hv.wire_bound b _ (takeTriples_mem_snd hwb) with hwq | hwp
        · have := csRawSum_val (hmem_lt hp); omega
        · have := csRawSum_val (hmem_lt hp); omega
      · have hval := congrArg Fin.val heq
        rw [csRawSum_val (hmem_lt hp), csRawSum_val (hmem_lt hq)] at hval
        have heq_p : p = q :=
          pairwise_eq_of_snd (numberItems_pairwise_ne st.nextPair (csAllTriples n st)) hp hq (by omega)
        subst heq_p
        simp only [decide_eq_true_eq] at hpa hqb
        exact hab (hpa.symm.trans hqb)
      · have hval := congrArg Fin.val heq
        rw [csRawSum_val (hmem_lt hp), csRawCarry_val (hmem_lt hq)] at hval
        omega
      · have hp1 := (mem_numberItems_bounds hp).1
        rcases hv.wire_bound b _ (takeTriples_mem_snd hwb) with hwq | hwp
        · have := csRawCarry_val (hmem_lt hp); omega
        · have := csRawCarry_val (hmem_lt hp); omega
      · have hval := congrArg Fin.val heq
        rw [csRawCarry_val (hmem_lt hp), csRawSum_val (hmem_lt hq)] at hval
        omega
      · have hval := congrArg Fin.val heq
        rw [csRawCarry_val (hmem_lt hp), csRawCarry_val (hmem_lt hq)] at hval
        have heq_p : p = q :=
          pairwise_eq_of_snd (numberItems_pairwise_ne st.nextPair (csAllTriples n st)) hp hq (by omega)
        subst heq_p
        simp only [decide_eq_true_eq] at hpa hqb
        exact hab (Fin.ext (by omega))
  exact ⟨hpair', hnodup', hwire', hwork'⟩

private lemma csValid_at (n : ℕ) (hn : 1 ≤ n) (r : ℕ) : CSValid n (csStateAt n r) := by
  induction r with
  | zero => exact csValid_init n hn
  | succ r ih => exact csValid_step hn ih

private def csTripleWireSet {n : ℕ}
    (item : (Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ) :
    Finset (Fin (hcWires n)) :=
  {item.1.2.1, item.1.2.2.1, item.1.2.2.2, csRawSum n item.2, csRawCarry n item.2}

private noncomputable def csTripleGate {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (item : (Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ)
    (hitem : item ∈ numberItems st.nextPair (csAllTriples n st)) :
    { lc : LayeredCircuit (hcWires n) //
      lc.UsesOnly (csTripleWireSet item) ∧ lc.size = 13 ∧ lc.depth = 13 } :=
  let b := item.1.1
  let w1 := item.1.2.1
  let w2 := item.1.2.2.1
  let w3 := item.1.2.2.2
  let ws := csRawSum n item.2
  let wc := csRawCarry n item.2
  have hmem := mem_numberItems_bounds hitem
  have hT_le := csValid_nextPair_add_triples hv
  have hidx_lt : item.2 < n := by omega
  have htri : (w1, w2, w3) ∈ (takeTriples (st.cols b)).1 := by
    have hm := hmem.2.2
    simp only [csAllTriples, List.mem_flatMap, List.mem_map] at hm
    rcases hm with ⟨b', _, t', ht', heq⟩
    have hb : b' = b := congrArg Prod.fst heq
    have ht : t' = (w1, w2, w3) := congrArg Prod.snd heq
    subst hb; subst ht; exact ht'
  have hcol_nd : (st.cols b).Nodup := (csValid_cols_nodup hv b).1
  have h123 := (takeTriples_triples_disjoint hcol_nd).2 (w1, w2, w3) htri
  have hw_bnd : ∀ w ∈ (st.cols b), w.1 < n ∨
      (n + hcEll n ≤ w.1 ∧ w.1 < n + hcEll n + 2 * st.nextPair) := hv.wire_bound b
  have hmem_col := takeTriples_mem_fst htri
  have hw1_b := hw_bnd w1 hmem_col.1
  have hw2_b := hw_bnd w2 hmem_col.2.1
  have hw3_b := hw_bnd w3 hmem_col.2.2
  have hws_v := csRawSum_val hidx_lt
  have hwc_v := csRawCarry_val hidx_lt
  have h1s : w1 ≠ ws := fun h => by have := congrArg Fin.val h; omega
  have h1c : w1 ≠ wc := fun h => by have := congrArg Fin.val h; omega
  have h2s : w2 ≠ ws := fun h => by have := congrArg Fin.val h; omega
  have h2c : w2 ≠ wc := fun h => by have := congrArg Fin.val h; omega
  have h3s : w3 ≠ ws := fun h => by have := congrArg Fin.val h; omega
  have h3c : w3 ≠ wc := fun h => by have := congrArg Fin.val h; omega
  have hsc : ws ≠ wc := fun h => by have := congrArg Fin.val h; omega
  ⟨fullAdder5 w1 w2 w3 ws wc h123.1 h1s h1c h2s h2c h3s h3c hsc,
    fullAdder5_usesOnly w1 w2 w3 ws wc h123.1 h1s h1c h2s h2c h3s h3c hsc,
    fullAdder5_size _ _ _ _ _ _ _ _ _ _ _ _ _,
    fullAdder5_depth _ _ _ _ _ _ _ _ _ _ _ _ _⟩

private lemma csAllTriples_pairwise_disjoint {n : ℕ} (st : CSState n)
    (hv : CSValid n st) :
    (numberItems st.nextPair (csAllTriples n st)).Pairwise fun p q =>
      Disjoint (csTripleWireSet p) (csTripleWireSet q) := by
  have htri_pw : (csAllTriples n st).Pairwise fun a b =>
      Disjoint ({a.2.1, a.2.2.1, a.2.2.2} : Finset (Fin (hcWires n)))
        ({b.2.1, b.2.2.1, b.2.2.2} : Finset (Fin (hcWires n))) := by
    have hnodup_cols := csValid_cols_nodup hv
    dsimp only [csAllTriples]
    have hgen : ∀ bs : List (Fin (hcEll n)), bs.Nodup →
        (bs.flatMap fun b => (takeTriples (st.cols b)).1.map fun t => (b, t)).Pairwise fun a b =>
          Disjoint ({a.2.1, a.2.2.1, a.2.2.2} : Finset (Fin (hcWires n)))
            ({b.2.1, b.2.2.1, b.2.2.2} : Finset (Fin (hcWires n))) := by
      intro bs hbs
      induction bs with
      | nil => simp
      | cons b rest ih =>
        rw [List.nodup_cons] at hbs
        simp only [List.flatMap_cons, List.pairwise_append]
        refine ⟨?_, ih hbs.2, ?_⟩
        · rw [List.pairwise_map]
          exact (takeTriples_triples_disjoint (hnodup_cols b).1).1
        · intro x hx y hy
          simp only [List.mem_map] at hx
          simp only [List.mem_flatMap, List.mem_map] at hy
          rcases hx with ⟨tx, htx, rfl⟩
          rcases hy with ⟨b', hb', ty, hty, rfl⟩
          have hbb' : b ≠ b' := fun h => hbs.1 (h ▸ hb')
          have hmx := takeTriples_mem_fst htx
          have hmy := takeTriples_mem_fst hty
          rw [Finset.disjoint_left]
          intro w hwx hwy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hwx hwy
          have hwx' : w ∈ st.cols b := by
            rcases hwx with rfl | rfl | rfl
            · exact hmx.1
            · exact hmx.2.1
            · exact hmx.2.2
          have hwy' : w ∈ st.cols b' := by
            rcases hwy with rfl | rfl | rfl
            · exact hmy.1
            · exact hmy.2.1
            · exact hmy.2.2
          exact (hnodup_cols b).2 b' hbb' w hwx' hwy'
    exact hgen (List.finRange (hcEll n)) (List.nodup_finRange _)
  have hnumber : ∀ (start : ℕ) (xs : List (Fin (hcEll n) ×
        (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n)))),
      xs.Pairwise (fun a b =>
        Disjoint ({a.2.1, a.2.2.1, a.2.2.2} : Finset (Fin (hcWires n)))
          ({b.2.1, b.2.2.1, b.2.2.2} : Finset (Fin (hcWires n)))) →
      start + xs.length ≤ n →
      (∀ x ∈ xs, x.2.1.1 < n ∨ (n + hcEll n ≤ x.2.1.1 ∧ x.2.1.1 < n + hcEll n + 2 * start)) →
      (∀ x ∈ xs, x.2.2.1.1 < n ∨ (n + hcEll n ≤ x.2.2.1.1 ∧ x.2.2.1.1 < n + hcEll n + 2 * start)) →
      (∀ x ∈ xs, x.2.2.2.1 < n ∨ (n + hcEll n ≤ x.2.2.2.1 ∧ x.2.2.2.1 < n + hcEll n + 2 * start)) →
      (numberItems start xs).Pairwise fun p q =>
        Disjoint (csTripleWireSet p) (csTripleWireSet q) := by
    intro start xs hpwx hlen h1 h2 h3
    induction xs generalizing start with
    | nil => simp [numberItems]
    | cons x rest ih =>
      rw [List.pairwise_cons] at hpwx
      simp only [numberItems, List.pairwise_cons]
      refine ⟨fun q hq => ?_, ih (start + 1) hpwx.2 (by simp at hlen; omega)
        (fun y hy => by rcases h1 y (List.mem_cons_of_mem _ hy) with h | h <;> [left; right] <;> omega)
        (fun y hy => by rcases h2 y (List.mem_cons_of_mem _ hy) with h | h <;> [left; right] <;> omega)
        (fun y hy => by rcases h3 y (List.mem_cons_of_mem _ hy) with h | h <;> [left; right] <;> omega)⟩
      have hqb := mem_numberItems_bounds hq
      have hstart_lt : start < n := by simp at hlen; omega
      have hq_lt : q.2 < n := by simp at hlen; omega
      have hdisj_in := hpwx.1 q.1 hqb.2.2
      have hx1 := h1 x List.mem_cons_self
      have hx2 := h2 x List.mem_cons_self
      have hx3 := h3 x List.mem_cons_self
      have hq1 := h1 q.1 (List.mem_cons_of_mem _ hqb.2.2)
      have hq2 := h2 q.1 (List.mem_cons_of_mem _ hqb.2.2)
      have hq3 := h3 q.1 (List.mem_cons_of_mem _ hqb.2.2)
      have hws1 := csRawSum_val hstart_lt
      have hwc1 := csRawCarry_val hstart_lt
      have hws2 := csRawSum_val hq_lt
      have hwc2 := csRawCarry_val hq_lt
      have hx_eq : csTripleWireSet (x, start) =
          ({x.2.1, x.2.2.1, x.2.2.2} : Finset (Fin (hcWires n))) ∪
            ({csRawSum n start, csRawCarry n start} : Finset (Fin (hcWires n))) := by
        ext w; simp only [csTripleWireSet, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl | rfl | rfl | rfl) <;> simp
        · rintro ((rfl | rfl | rfl) | (rfl | rfl)) <;> simp
      have hq_eq : csTripleWireSet q =
          ({q.1.2.1, q.1.2.2.1, q.1.2.2.2} : Finset (Fin (hcWires n))) ∪
            ({csRawSum n q.2, csRawCarry n q.2} : Finset (Fin (hcWires n))) := by
        ext w; simp only [csTripleWireSet, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl | rfl | rfl | rfl) <;> simp
        · rintro ((rfl | rfl | rfl) | (rfl | rfl)) <;> simp
      have hxin_lt : ∀ w ∈ ({x.2.1, x.2.2.1, x.2.2.2} : Finset (Fin (hcWires n))),
          w.1 < n + hcEll n + 2 * start := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · rcases hx1 with h | h <;> omega
        · rcases hx2 with h | h <;> omega
        · rcases hx3 with h | h <;> omega
      have hqin_lt : ∀ w ∈ ({q.1.2.1, q.1.2.2.1, q.1.2.2.2} : Finset (Fin (hcWires n))),
          w.1 < n + hcEll n + 2 * start := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · rcases hq1 with h | h <;> omega
        · rcases hq2 with h | h <;> omega
        · rcases hq3 with h | h <;> omega
      have hxout_ge : ∀ w ∈ ({csRawSum n start, csRawCarry n start} : Finset (Fin (hcWires n))),
          n + hcEll n + 2 * start ≤ w.1 ∧ w.1 < n + hcEll n + 2 * (start + 1) := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl <;> omega
      have hqout_ge : ∀ w ∈ ({csRawSum n q.2, csRawCarry n q.2} : Finset (Fin (hcWires n))),
          n + hcEll n + 2 * (start + 1) ≤ w.1 := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        have hsq : start + 1 ≤ q.2 := hqb.1
        rcases hw with rfl | rfl <;> omega
      rw [hx_eq, hq_eq, Finset.disjoint_union_left, Finset.disjoint_union_right,
        Finset.disjoint_union_right]
      refine ⟨⟨hdisj_in, ?_⟩, ⟨?_, ?_⟩⟩
      · rw [Finset.disjoint_left]
        intro w hwx hwq
        have := hxin_lt w hwx
        have := hqout_ge w hwq
        omega
      · rw [Finset.disjoint_left]
        intro w hwx hwq
        have := hxout_ge w hwx
        have := hqin_lt w hwq
        omega
      · rw [Finset.disjoint_left]
        intro w hwx hwq
        have := hxout_ge w hwx
        have := hqout_ge w hwq
        omega
  have hT_le := csValid_nextPair_add_triples hv
  have hmem_tri : ∀ x ∈ csAllTriples n st,
      (x.2.1.1 < n ∨ (n + hcEll n ≤ x.2.1.1 ∧ x.2.1.1 < n + hcEll n + 2 * st.nextPair)) ∧
      (x.2.2.1.1 < n ∨ (n + hcEll n ≤ x.2.2.1.1 ∧ x.2.2.1.1 < n + hcEll n + 2 * st.nextPair)) ∧
      (x.2.2.2.1 < n ∨ (n + hcEll n ≤ x.2.2.2.1 ∧ x.2.2.2.1 < n + hcEll n + 2 * st.nextPair)) := by
    intro ⟨b, t⟩ hx
    simp only [csAllTriples, List.mem_flatMap, List.mem_map] at hx
    rcases hx with ⟨b', _, t', ht', heq⟩
    have hm := takeTriples_mem_fst ht'
    have h1 := hv.wire_bound b' t'.1 hm.1
    have h2 := hv.wire_bound b' t'.2.1 hm.2.1
    have h3 := hv.wire_bound b' t'.2.2 hm.2.2
    have ht_eq : (b', t') = (b, t) := heq
    cases ht_eq
    exact ⟨h1, h2, h3⟩
  exact hnumber st.nextPair (csAllTriples n st) htri_pw hT_le
    (fun x hx => (hmem_tri x hx).1)
    (fun x hx => (hmem_tri x hx).2.1)
    (fun x hx => (hmem_tri x hx).2.2)

private def csApplyList (n : ℕ) (z : Qubits (hcWires n)) :
    List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ) →
    Qubits (hcWires n)
  | [] => z
  | item :: rest =>
    let restQ := csApplyList n z rest
    let w1 := item.1.2.1
    let w2 := item.1.2.2.1
    let w3 := item.1.2.2.2
    fun w =>
      if w = csRawSum n item.2 then xor (xor (z w1) (z w2)) (z w3)
      else if w = csRawCarry n item.2 then xor (z w1 && z w2) (xor (z w1) (z w2) && z w3)
      else restQ w

private lemma csApplyList_sum {n : ℕ} (z : Qubits (hcWires n))
    {L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ)}
    (hpw : L.Pairwise fun p q => p.2 ≠ q.2)
    (hlt : ∀ p ∈ L, p.2 < n)
    {item : (Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ}
    (hitem : item ∈ L) :
    csApplyList n z L (csRawSum n item.2) =
      xor (xor (z item.1.2.1) (z item.1.2.2.1)) (z item.1.2.2.2) := by
  induction L with
  | nil => cases hitem
  | cons h rest ih =>
    rw [List.pairwise_cons] at hpw
    rw [List.mem_cons] at hitem
    dsimp only [csApplyList]
    rcases hitem with rfl | hrest
    · rw [if_pos rfl]
    · have hne_idx : h.2 ≠ item.2 := hpw.1 item hrest
      have hh_lt : h.2 < n := hlt h List.mem_cons_self
      have hi_lt : item.2 < n := hlt item (List.mem_cons_of_mem _ hrest)
      have hs := csRawSum_val hh_lt
      have hc := csRawCarry_val hh_lt
      have his := csRawSum_val hi_lt
      have hns : csRawSum n item.2 ≠ csRawSum n h.2 := fun e => by
        have := congrArg Fin.val e; omega
      have hnc : csRawSum n item.2 ≠ csRawCarry n h.2 := fun e => by
        have := congrArg Fin.val e; omega
      rw [if_neg hns, if_neg hnc]
      exact ih hpw.2 (fun p hp => hlt p (List.mem_cons_of_mem _ hp)) hrest

private lemma csApplyList_carry {n : ℕ} (z : Qubits (hcWires n))
    {L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ)}
    (hpw : L.Pairwise fun p q => p.2 ≠ q.2)
    (hlt : ∀ p ∈ L, p.2 < n)
    {item : (Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ}
    (hitem : item ∈ L) :
    csApplyList n z L (csRawCarry n item.2) =
      xor (z item.1.2.1 && z item.1.2.2.1)
        (xor (z item.1.2.1) (z item.1.2.2.1) && z item.1.2.2.2) := by
  induction L with
  | nil => cases hitem
  | cons h rest ih =>
    rw [List.pairwise_cons] at hpw
    rw [List.mem_cons] at hitem
    dsimp only [csApplyList]
    rcases hitem with rfl | hrest
    · have hh_lt : item.2 < n := hlt item List.mem_cons_self
      have hs := csRawSum_val hh_lt
      have hc := csRawCarry_val hh_lt
      have hne : csRawCarry n item.2 ≠ csRawSum n item.2 := fun e => by
        have := congrArg Fin.val e; omega
      rw [if_neg hne, if_pos rfl]
    · have hne_idx : h.2 ≠ item.2 := hpw.1 item hrest
      have hh_lt : h.2 < n := hlt h List.mem_cons_self
      have hi_lt : item.2 < n := hlt item (List.mem_cons_of_mem _ hrest)
      have hs := csRawSum_val hh_lt
      have hc := csRawCarry_val hh_lt
      have hic := csRawCarry_val hi_lt
      have hns : csRawCarry n item.2 ≠ csRawSum n h.2 := fun e => by
        have := congrArg Fin.val e; omega
      have hnc : csRawCarry n item.2 ≠ csRawCarry n h.2 := fun e => by
        have := congrArg Fin.val e; omega
      rw [if_neg hns, if_neg hnc]
      exact ih hpw.2 (fun p hp => hlt p (List.mem_cons_of_mem _ hp)) hrest

private lemma csApplyList_other {n : ℕ} (z : Qubits (hcWires n))
    {L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ)}
    {w : Fin (hcWires n)} (hw : ∀ item ∈ L, w ≠ csRawSum n item.2 ∧ w ≠ csRawCarry n item.2) :
    csApplyList n z L w = z w := by
  induction L with
  | nil => rfl
  | cons h rest ih =>
    dsimp only [csApplyList]
    have hh := hw h List.mem_cons_self
    rw [if_neg hh.1, if_neg hh.2]
    exact ih (fun p hp => hw p (List.mem_cons_of_mem _ hp))

private lemma mem_foldr_union_of_mem {α β : Type*} [DecidableEq β]
    {xs : List (α × Finset β)} {p : α × Finset β} {w : β}
    (hp : p ∈ xs) (hw : w ∈ p.2) :
    w ∈ xs.foldr (fun q acc => q.2 ∪ acc) ∅ := by
  induction xs with
  | nil => cases hp
  | cons q rest ih =>
    rw [List.mem_cons] at hp
    simp only [List.foldr_cons, Finset.mem_union]
    rcases hp with rfl | hrest
    · left; exact hw
    · right; exact ih hrest

private noncomputable def csRoundList {n : ℕ} (st : CSState n) (hv : CSValid n st) :
    (L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ)) →
    (∀ p ∈ L, p ∈ numberItems st.nextPair (csAllTriples n st)) →
    List (LayeredCircuit (hcWires n) × Finset (Fin (hcWires n)))
  | [], _ => []
  | item :: rest, h =>
    ((csTripleGate st hv item (h item List.mem_cons_self)).1, csTripleWireSet item) ::
      csRoundList st hv rest (fun p hp => h p (List.mem_cons_of_mem _ hp))

private lemma csRoundList_usesOnly {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ))
    (h : ∀ p ∈ L, p ∈ numberItems st.nextPair (csAllTriples n st)) :
    ∀ p ∈ csRoundList st hv L h, p.1.UsesOnly p.2 := by
  induction L with
  | nil => intro p hp; cases hp
  | cons item rest ih =>
    intro p hp
    dsimp only [csRoundList] at hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact (csTripleGate st hv item (h item List.mem_cons_self)).2.1
    · exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) p hp

private lemma csRoundList_map_snd {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ))
    (h : ∀ p ∈ L, p ∈ numberItems st.nextPair (csAllTriples n st)) :
    (csRoundList st hv L h).map Prod.snd = L.map csTripleWireSet := by
  induction L with
  | nil => rfl
  | cons item rest ih =>
    simp only [csRoundList, List.map_cons]
    congr 1
    exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq))

private lemma csRoundList_pairwise {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ))
    (h : ∀ p ∈ L, p ∈ numberItems st.nextPair (csAllTriples n st))
    (hpw : L.Pairwise fun p q => Disjoint (csTripleWireSet p) (csTripleWireSet q)) :
    (csRoundList st hv L h).Pairwise fun p q => Disjoint p.2 q.2 := by
  induction L with
  | nil => simp [csRoundList]
  | cons item rest ih =>
    rw [List.pairwise_cons] at hpw
    simp only [csRoundList, List.pairwise_cons]
    refine ⟨fun q hq => ?_, ih (fun r hr => h r (List.mem_cons_of_mem _ hr)) hpw.2⟩
    have hq2 : q.2 ∈ (csRoundList st hv rest _).map Prod.snd := List.mem_map_of_mem hq
    rw [csRoundList_map_snd, List.mem_map] at hq2
    rcases hq2 with ⟨item', hitem', heq⟩
    rw [← heq]
    exact hpw.1 item' hitem'

private lemma csRoundList_size {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ))
    (h : ∀ p ∈ L, p ∈ numberItems st.nextPair (csAllTriples n st)) :
    ((csRoundList st hv L h).map fun p => p.1.size).sum = 13 * L.length := by
  induction L with
  | nil => simp [csRoundList]
  | cons item rest ih =>
    simp only [csRoundList, List.map_cons, List.sum_cons, List.length_cons,
      (csTripleGate st hv item (h item List.mem_cons_self)).2.2.1,
      ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    ring

private lemma csRoundList_depth {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ))
    (h : ∀ p ∈ L, p ∈ numberItems st.nextPair (csAllTriples n st)) :
    ∀ p ∈ csRoundList st hv L h, p.1.depth ≤ 13 := by
  induction L with
  | nil => intro p hp; cases hp
  | cons item rest ih =>
    intro p hp
    dsimp only [csRoundList] at hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | hp
    · dsimp only
      have := (csTripleGate st hv item (h item List.mem_cons_self)).2.2.2
      omega
    · exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) p hp

private lemma csRoundList_fwd {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ))
    (h : ∀ p ∈ L, p ∈ numberItems st.nextPair (csAllTriples n st)) :
    ∀ p ∈ csRoundList st hv L h, p.2 ⊆ fwdSupport n := by
  have hT_le := csValid_nextPair_add_triples hv
  induction L with
  | nil => intro p hp; cases hp
  | cons item rest ih =>
    intro p hp
    dsimp only [csRoundList] at hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | hp
    · intro w hw
      have hb := mem_numberItems_bounds (h item List.mem_cons_self)
      have hidx_lt : item.2 < n := by omega
      have hmem_tri := hb.2.2
      simp only [csAllTriples, List.mem_flatMap, List.mem_map] at hmem_tri
      rcases hmem_tri with ⟨b', _, t', ht', heq⟩
      have hmem_col := takeTriples_mem_fst ht'
      have h1 := hv.wire_bound b' t'.1 hmem_col.1
      have h2 := hv.wire_bound b' t'.2.1 hmem_col.2.1
      have h3 := hv.wire_bound b' t'.2.2 hmem_col.2.2
      have ht1 : t'.1 = item.1.2.1 := congrArg (fun q => q.2.1) heq
      have ht2 : t'.2.1 = item.1.2.2.1 := congrArg (fun q => q.2.2.1) heq
      have ht3 : t'.2.2 = item.1.2.2.2 := congrArg (fun q => q.2.2.2) heq
      rw [mem_fwdSupport_iff]
      simp only [csTripleWireSet, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl
      · rw [← ht1]; rcases h1 with hlt | hlt <;> [left; right] <;> omega
      · rw [← ht2]; rcases h2 with hlt | hlt <;> [left; right] <;> omega
      · rw [← ht3]; rcases h3 with hlt | hlt <;> [left; right] <;> omega
      · right; rw [csRawSum_val hidx_lt]; omega
      · right; rw [csRawCarry_val hidx_lt]; omega
    · exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) p hp

private lemma act_csTripleGate_ket {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (item : (Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ)
    (hitem : item ∈ numberItems st.nextPair (csAllTriples n st))
    (z : Qubits (hcWires n))
    (hclean : ∀ w : Fin (hcWires n), n + hcEll n + 2 * st.nextPair ≤ w.1 → z w = false) :
    ∃ x' : Qubits (hcWires n),
      act (csTripleGate st hv item hitem).1.unitary (ket z) = ket x' ∧
      ∀ w ∈ csTripleWireSet item,
        x' w = csApplyList n z (numberItems st.nextPair (csAllTriples n st)) w := by
  let ann := numberItems st.nextPair (csAllTriples n st)
  have hT_le := csValid_nextPair_add_triples hv
  have hann_pw : ann.Pairwise fun p q => p.2 ≠ q.2 :=
    numberItems_pairwise_ne st.nextPair (csAllTriples n st)
  have hann_lt : ∀ p ∈ ann, p.2 < n := by
    intro p hp; have := mem_numberItems_bounds hp; omega
  have hb := mem_numberItems_bounds hitem
  have hidx_lt : item.2 < n := by omega
  have hws_v := csRawSum_val hidx_lt
  have hwc_v := csRawCarry_val hidx_lt
  have hzs : z (csRawSum n item.2) = false := hclean _ (by omega)
  have hzc : z (csRawCarry n item.2) = false := hclean _ (by omega)
  have hmem_tri := hb.2.2
  simp only [csAllTriples, List.mem_flatMap, List.mem_map] at hmem_tri
  rcases hmem_tri with ⟨b', _, t', ht', heq⟩
  have hmem_col := takeTriples_mem_fst ht'
  have h1 := hv.wire_bound b' t'.1 hmem_col.1
  have h2 := hv.wire_bound b' t'.2.1 hmem_col.2.1
  have h3 := hv.wire_bound b' t'.2.2 hmem_col.2.2
  have ht1 : t'.1 = item.1.2.1 := congrArg (fun q => q.2.1) heq
  have ht2 : t'.2.1 = item.1.2.2.1 := congrArg (fun q => q.2.2.1) heq
  have ht3 : t'.2.2 = item.1.2.2.2 := congrArg (fun q => q.2.2.2) heq
  refine ⟨fun w =>
    if w = csRawSum n item.2 then xor (xor (z item.1.2.1) (z item.1.2.2.1)) (z item.1.2.2.2)
    else if w = csRawCarry n item.2 then
      xor (z item.1.2.1 && z item.1.2.2.1) (xor (z item.1.2.1) (z item.1.2.2.1) && z item.1.2.2.2)
    else z w, ?_, ?_⟩
  · dsimp only [csTripleGate]
    exact act_fullAdder5_ket _ _ _ _ _ _ _ _ _ _ _ _ _ z hzs hzc
  · intro w hw
    have houtside : ∀ u : Fin (hcWires n),
        (u.1 < n ∨ (n + hcEll n ≤ u.1 ∧ u.1 < n + hcEll n + 2 * st.nextPair)) →
        csApplyList n z ann u = z u := by
      intro u hu
      apply csApplyList_other
      intro q hq
      have hqb := mem_numberItems_bounds hq
      have hq_lt : q.2 < n := by omega
      have hqs := csRawSum_val hq_lt
      have hqc := csRawCarry_val hq_lt
      constructor <;> intro e <;> [have := congrArg Fin.val e; have := congrArg Fin.val e] <;> omega
    simp only [csTripleWireSet, Finset.mem_insert, Finset.mem_singleton] at hw
    dsimp only
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · have h1b : item.1.2.1.1 < n ∨
          (n + hcEll n ≤ item.1.2.1.1 ∧ item.1.2.1.1 < n + hcEll n + 2 * st.nextPair) := by
        rw [← ht1]; exact h1
      have h1s : item.1.2.1 ≠ csRawSum n item.2 := fun e => by have := congrArg Fin.val e; omega
      have h1c : item.1.2.1 ≠ csRawCarry n item.2 := fun e => by have := congrArg Fin.val e; omega
      rw [if_neg h1s, if_neg h1c, houtside _ h1b]
    · have h2b : item.1.2.2.1.1 < n ∨
          (n + hcEll n ≤ item.1.2.2.1.1 ∧ item.1.2.2.1.1 < n + hcEll n + 2 * st.nextPair) := by
        rw [← ht2]; exact h2
      have h2s : item.1.2.2.1 ≠ csRawSum n item.2 := fun e => by have := congrArg Fin.val e; omega
      have h2c : item.1.2.2.1 ≠ csRawCarry n item.2 := fun e => by have := congrArg Fin.val e; omega
      rw [if_neg h2s, if_neg h2c, houtside _ h2b]
    · have h3b : item.1.2.2.2.1 < n ∨
          (n + hcEll n ≤ item.1.2.2.2.1 ∧ item.1.2.2.2.1 < n + hcEll n + 2 * st.nextPair) := by
        rw [← ht3]; exact h3
      have h3s : item.1.2.2.2 ≠ csRawSum n item.2 := fun e => by have := congrArg Fin.val e; omega
      have h3c : item.1.2.2.2 ≠ csRawCarry n item.2 := fun e => by have := congrArg Fin.val e; omega
      rw [if_neg h3s, if_neg h3c, houtside _ h3b]
    · rw [if_pos rfl, csApplyList_sum z hann_pw hann_lt hitem]
    · have hcs : csRawCarry n item.2 ≠ csRawSum n item.2 := fun e => by
        have := congrArg Fin.val e; omega
      rw [if_neg hcs, if_pos rfl, csApplyList_carry z hann_pw hann_lt hitem]

private lemma csRoundList_act {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ))
    (h : ∀ p ∈ L, p ∈ numberItems st.nextPair (csAllTriples n st)) :
    ∀ p ∈ csRoundList st hv L h, ∀ z : Qubits (hcWires n),
      (∀ w : Fin (hcWires n), n + hcEll n + 2 * st.nextPair ≤ w.1 → z w = false) →
      ∃ x' : Qubits (hcWires n), act p.1.unitary (ket z) = ket x' ∧
        ∀ w ∈ p.2, x' w = csApplyList n z (numberItems st.nextPair (csAllTriples n st)) w := by
  induction L with
  | nil => intro p hp; cases hp
  | cons item rest ih =>
    intro p hp z hclean
    dsimp only [csRoundList] at hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact act_csTripleGate_ket st hv item (h item List.mem_cons_self) z hclean
    · exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) p hp z hclean

private noncomputable def csRoundItems {n : ℕ} (st : CSState n) (hv : CSValid n st) :
    { xs : List (LayeredCircuit (hcWires n) × Finset (Fin (hcWires n))) //
      (∀ p ∈ xs, p.1.UsesOnly p.2) ∧
      xs.Pairwise (fun p q => Disjoint p.2 q.2) ∧
      (xs.map fun p => p.1.size).sum = 13 * (csAllTriples n st).length ∧
      (∀ p ∈ xs, p.1.depth ≤ 13) ∧
      (∀ p ∈ xs, p.2 ⊆ fwdSupport n) ∧
      (∀ p ∈ xs, ∀ z : Qubits (hcWires n),
        (∀ w : Fin (hcWires n), n + hcEll n + 2 * st.nextPair ≤ w.1 → z w = false) →
        ∃ x' : Qubits (hcWires n), act p.1.unitary (ket z) = ket x' ∧
          ∀ w ∈ p.2, x' w = csApplyList n z (numberItems st.nextPair (csAllTriples n st)) w) ∧
      xs.map Prod.snd = (numberItems st.nextPair (csAllTriples n st)).map csTripleWireSet } :=
  let ann := numberItems st.nextPair (csAllTriples n st)
  ⟨csRoundList st hv ann (fun _ h => h),
    csRoundList_usesOnly st hv ann _,
    csRoundList_pairwise st hv ann _ (csAllTriples_pairwise_disjoint st hv),
    by rw [csRoundList_size st hv ann _, numberItems_length],
    csRoundList_depth st hv ann _,
    csRoundList_fwd st hv ann _,
    csRoundList_act st hv ann _,
    csRoundList_map_snd st hv ann _⟩

private noncomputable def csRoundCircuit {n : ℕ} (st : CSState n) (hv : CSValid n st) :
    { lc : LayeredCircuit (hcWires n) //
      lc.UsesOnly (fwdSupport n) ∧
      lc.size = 13 * (csAllTriples n st).length ∧
      lc.depth ≤ 13 } :=
  let items := csRoundItems st hv
  let merged := parMergeAux items.1 items.2.1 items.2.2.1
  have huses : merged.1.UsesOnly (fwdSupport n) := by
    refine merged.2.1.mono ?_
    have hfold : ∀ (L : List (LayeredCircuit (hcWires n) × Finset (Fin (hcWires n)))),
        (∀ p ∈ L, p.2 ⊆ fwdSupport n) → L.foldr (fun p acc => p.2 ∪ acc) ∅ ⊆ fwdSupport n := by
      intro L hL
      induction L with
      | nil => simp
      | cons p rest ih =>
        simp only [List.foldr_cons, Finset.union_subset_iff]
        exact ⟨hL p List.mem_cons_self, ih fun q hq => hL q (List.mem_cons_of_mem _ hq)⟩
    exact hfold items.1 items.2.2.2.2.2.1
  ⟨merged.1, huses, merged.2.2.1.trans items.2.2.2.1,
    le_trans merged.2.2.2 (foldr_max_le items.1 13 items.2.2.2.2.1)⟩

private noncomputable def csCircuitAt (n : ℕ) (hn : 1 ≤ n) : ℕ → LayeredCircuit (hcWires n)
  | 0 => LayeredCircuit.id (hcWires n)
  | r + 1 => (csCircuitAt n hn r).seq (csRoundCircuit (csStateAt n r) (csValid_at n hn r)).1

private lemma csCircuitAt_usesOnly (n : ℕ) (hn : 1 ≤ n) (r : ℕ) :
    (csCircuitAt n hn r).UsesOnly (fwdSupport n) := by
  induction r with
  | zero => exact LayeredCircuit.id_usesOnly _
  | succ r ih =>
    exact LayeredCircuit.seq_usesOnly ih (csRoundCircuit (csStateAt n r) (csValid_at n hn r)).2.1

private lemma csCircuitAt_size (n : ℕ) (hn : 1 ≤ n) (r : ℕ) :
    (csCircuitAt n hn r).size = 13 * (csStateAt n r).nextPair := by
  induction r with
  | zero => simp [csCircuitAt, csStateAt, csInit]
  | succ r ih =>
    simp only [csCircuitAt, csStateAt, csStep, LayeredCircuit.seq_size, ih,
      (csRoundCircuit (csStateAt n r) (csValid_at n hn r)).2.2.1]
    ring

private lemma csCircuitAt_size_le (n : ℕ) (hn : 1 ≤ n) (r : ℕ) :
    (csCircuitAt n hn r).size ≤ 13 * n := by
  rw [csCircuitAt_size]
  exact Nat.mul_le_mul_left 13 (csValid_at n hn r).pair_le

private lemma csCircuitAt_depth (n : ℕ) (hn : 1 ≤ n) (r : ℕ) :
    (csCircuitAt n hn r).depth ≤ 13 * r := by
  induction r with
  | zero => simp [csCircuitAt]
  | succ r ih =>
    simp only [csCircuitAt, LayeredCircuit.seq_depth]
    have hround := (csRoundCircuit (csStateAt n r) (csValid_at n hn r)).2.2.2
    omega

private lemma countP_eq_sum_map {α : Type*} (xs : List α) (p : α → Bool) :
    xs.countP p = (xs.map fun a => if p a then 1 else 0).sum := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.countP_cons, List.map_cons, List.sum_cons, ih]
    cases p a <;> simp [Nat.add_comm]

private lemma list_finRange_countP {n : ℕ} (p : Fin n → Bool) :
    (List.finRange n).countP p = (Finset.univ.filter fun i : Fin n => p i = true).card := by
  rw [countP_eq_sum_map, List.map_congr_left (fun _ _ => rfl), sum_map_finRange, Finset.card_filter]

private lemma sum_map_flatMap {α β : Type*} (xs : List α) (f : α → List β) (g : β → ℕ) :
    ((xs.flatMap f).map g).sum = (xs.map fun a => ((f a).map g).sum).sum := by
  induction xs with
  | nil => simp
  | cons a rest ih => simp [List.flatMap_cons, ih]

private lemma sum_filter_eq_map {α : Type*} {k : ℕ} (L : List α) (col : α → Fin k) (g : α → ℕ) :
    (∑ b : Fin k, 2 ^ b.1 * ((L.filter fun a => decide (col a = b)).map g).sum) =
      (L.map fun a => 2 ^ (col a).1 * g a).sum := by
  induction L with
  | nil => simp
  | cons a rest ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    have hterm : ∀ b : Fin k,
        2 ^ b.1 * (List.map g (if decide (col a = b) = true then a :: rest.filter (fun x => decide (col x = b))
          else rest.filter (fun x => decide (col x = b)))).sum =
        (if col a = b then 2 ^ b.1 * g a else 0) +
          2 ^ b.1 * ((rest.filter fun x => decide (col x = b)).map g).sum := by
      intro b
      by_cases h : col a = b
      · simp [h, mul_add]
      · simp [h]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ih, Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

private lemma sum_filter_succ_eq_map {α : Type*} {k : ℕ} (L : List α) (col : α → Fin k) (g : α → ℕ) :
    (∑ b : Fin k, 2 ^ b.1 * ((L.filter fun a => decide ((col a).1 + 1 = b.1)).map g).sum) +
      2 ^ k * ((L.filter fun a => decide ((col a).1 + 1 = k)).map g).sum =
      (L.map fun a => 2 ^ (col a).1 * 2 * g a).sum := by
  induction L with
  | nil => simp
  | cons a rest ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    by_cases hlt : (col a).1 + 1 < k
    · let b0 : Fin k := ⟨(col a).1 + 1, hlt⟩
      have hne_k : (col a).1 + 1 ≠ k := by omega
      have hterm : ∀ b : Fin k,
          2 ^ b.1 * (List.map g (if decide ((col a).1 + 1 = b.1) = true then
              a :: rest.filter (fun x => decide ((col x).1 + 1 = b.1))
            else rest.filter (fun x => decide ((col x).1 + 1 = b.1)))).sum =
          (if b0 = b then 2 ^ b.1 * g a else 0) +
            2 ^ b.1 * ((rest.filter fun x => decide ((col x).1 + 1 = b.1)).map g).sum := by
        intro b
        by_cases h : b0 = b
        · have heq : (col a).1 + 1 = b.1 := by rw [← h]
          simp [h, heq, mul_add]
        · have hneq : (col a).1 + 1 ≠ b.1 := fun heq => h (Fin.ext heq)
          simp [h, hneq]
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ _),
        if_neg (by simp [hne_k])]
      have hpow : 2 ^ b0.1 = 2 ^ (col a).1 * 2 := by
        change 2 ^ ((col a).1 + 1) = 2 ^ (col a).1 * 2
        rw [pow_succ]
      rw [hpow, ← ih]
      ring
    · have hcol_eq : (col a).1 + 1 = k := by have := (col a).isLt; omega
      have hterm : ∀ b : Fin k,
          2 ^ b.1 * (List.map g (if decide ((col a).1 + 1 = b.1) = true then
              a :: rest.filter (fun x => decide ((col x).1 + 1 = b.1))
            else rest.filter (fun x => decide ((col x).1 + 1 = b.1)))).sum =
          2 ^ b.1 * ((rest.filter fun x => decide ((col x).1 + 1 = b.1)).map g).sum := by
        intro b
        have hneq : (col a).1 + 1 ≠ b.1 := by have := b.isLt; omega
        simp [hneq]
      simp_rw [hterm]
      rw [if_pos (by simp [hcol_eq]), List.map_cons, List.sum_cons]
      have h_assoc :
          (∑ x : Fin k, 2 ^ x.1 * ((rest.filter fun x_1 => decide ((col x_1).1 + 1 = x.1)).map g).sum) +
            2 ^ k * (g a + ((rest.filter fun x => decide ((col x).1 + 1 = k)).map g).sum) =
          2 ^ k * g a +
            ((∑ x : Fin k, 2 ^ x.1 * ((rest.filter fun x_1 => decide ((col x_1).1 + 1 = x.1)).map g).sum) +
              2 ^ k * ((rest.filter fun x => decide ((col x).1 + 1 = k)).map g).sum) := by ring
      have hpow : 2 ^ k = 2 ^ (col a).1 * 2 := by
        conv_lhs => rw [← hcol_eq, pow_succ]
      rw [h_assoc, ih, hpow]

private lemma act_csRoundCircuit_ket {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (z : Qubits (hcWires n))
    (hclean : ∀ w : Fin (hcWires n), n + hcEll n + 2 * st.nextPair ≤ w.1 → z w = false) :
    act (csRoundCircuit st hv).1.unitary (ket z) =
      ket (csApplyList n z (numberItems st.nextPair (csAllTriples n st))) := by
  dsimp only [csRoundCircuit]
  let ann := numberItems st.nextPair (csAllTriples n st)
  let z_next := csApplyList n z ann
  let items := csRoundItems st hv
  have hact_items : ∀ p ∈ items.1, ∃ x' : Qubits (hcWires n),
      act p.1.unitary (ket z) = ket x' ∧ ∀ w ∈ p.2, x' w = z_next w :=
    fun p hp => items.2.2.2.2.2.2.1 p hp z hclean
  rw [act_parMergeAux_ket items.1 items.2.1 items.2.2.1 z z_next hact_items]
  congr 1
  funext w
  split_ifs with hw
  · rfl
  · have hout : ∀ item ∈ ann, w ≠ csRawSum n item.2 ∧ w ≠ csRawCarry n item.2 := by
      intro item hitem
      have hset_mem : csTripleWireSet item ∈ items.1.map Prod.snd := by
        rw [items.2.2.2.2.2.2.2]
        exact List.mem_map_of_mem hitem
      rw [List.mem_map] at hset_mem
      rcases hset_mem with ⟨p, hp, hp_eq⟩
      constructor <;> intro heq <;> apply hw <;> rw [heq] <;>
        exact mem_foldr_union_of_mem hp (hp_eq ▸ by simp [csTripleWireSet])
    exact (csApplyList_other z hout).symm

private lemma csApplyList_preserve_low {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (z : Qubits (hcWires n)) {w : Fin (hcWires n)} (hw : w.1 < n + hcEll n) :
    csApplyList n z (numberItems st.nextPair (csAllTriples n st)) w = z w := by
  have hT_le := csValid_nextPair_add_triples hv
  apply csApplyList_other
  intro item hitem
  have hb := mem_numberItems_bounds hitem
  have hlt : item.2 < n := by omega
  have hs := csRawSum_val hlt
  have hc := csRawCarry_val hlt
  constructor <;> intro e <;> [have := congrArg Fin.val e; have := congrArg Fin.val e] <;> omega

private lemma csApplyList_preserve_high {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (z : Qubits (hcWires n)) {w : Fin (hcWires n)}
    (hw : n + hcEll n + 2 * (csStep n st).nextPair ≤ w.1) :
    csApplyList n z (numberItems st.nextPair (csAllTriples n st)) w = z w := by
  have hT_le := csValid_nextPair_add_triples hv
  apply csApplyList_other
  intro item hitem
  have hb := mem_numberItems_bounds hitem
  have hlt : item.2 < n := by omega
  have hs := csRawSum_val hlt
  have hc := csRawCarry_val hlt
  dsimp only [csStep] at hw
  constructor <;> intro e <;> [have := congrArg Fin.val e; have := congrArg Fin.val e] <;> omega

private lemma csApplyList_weighted_sum {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (z : Qubits (hcWires n)) :
    let z' := csApplyList n z (numberItems st.nextPair (csAllTriples n st))
    (∑ b : Fin (hcEll n), 2 ^ b.1 * ((csStep n st).cols b).countP z') +
      2 ^ hcEll n * (((numberItems st.nextPair (csAllTriples n st)).filter
        fun p => decide (p.1.1.1 + 1 = hcEll n)).map fun p => if z' (csRawCarry n p.2) then 1 else 0).sum =
      ∑ b : Fin (hcEll n), 2 ^ b.1 * (st.cols b).countP z := by
  let ann := numberItems st.nextPair (csAllTriples n st)
  let z' := csApplyList n z ann
  have hT_le := csValid_nextPair_add_triples hv
  have hann_pw : ann.Pairwise fun p q => p.2 ≠ q.2 :=
    numberItems_pairwise_ne st.nextPair (csAllTriples n st)
  have hann_lt : ∀ p ∈ ann, p.2 < n := by
    intro p hp; have := mem_numberItems_bounds hp; omega
  have hrem_count : ∀ b : Fin (hcEll n),
      (takeTriples (st.cols b)).2.countP z' = (takeTriples (st.cols b)).2.countP z := by
    intro b
    refine List.countP_congr fun w hw => ?_
    have hwb := hv.wire_bound b w (takeTriples_mem_snd hw)
    have hout : ∀ item ∈ ann, w ≠ csRawSum n item.2 ∧ w ≠ csRawCarry n item.2 := by
      intro item hitem
      have hb := mem_numberItems_bounds hitem
      have hlt : item.2 < n := by omega
      have hs := csRawSum_val hlt
      have hc := csRawCarry_val hlt
      constructor <;> intro e <;> [have := congrArg Fin.val e; have := congrArg Fin.val e] <;> omega
    rw [show z' w = z w from csApplyList_other z hout]
  have hstep_col : ∀ b : Fin (hcEll n),
      ((csStep n st).cols b).countP z' =
        (takeTriples (st.cols b)).2.countP z +
        ((ann.filter fun p => decide (p.1.1 = b)).map fun p => if z' (csRawSum n p.2) then 1 else 0).sum +
        ((ann.filter fun p => decide (p.1.1.1 + 1 = b.1)).map fun p =>
          if z' (csRawCarry n p.2) then 1 else 0).sum := by
    intro b
    dsimp only [csStep]
    rw [List.countP_append, List.countP_append, hrem_count b]
    simp_rw [countP_eq_sum_map, List.map_map]
    rfl
  have hsum_cols : (∑ b : Fin (hcEll n), 2 ^ b.1 * ((csStep n st).cols b).countP z') =
      (∑ b : Fin (hcEll n), 2 ^ b.1 * (takeTriples (st.cols b)).2.countP z) +
      (∑ b : Fin (hcEll n), 2 ^ b.1 * ((ann.filter fun p => decide (p.1.1 = b)).map fun p =>
        if z' (csRawSum n p.2) then 1 else 0).sum) +
      (∑ b : Fin (hcEll n), 2 ^ b.1 * ((ann.filter fun p => decide (p.1.1.1 + 1 = b.1)).map fun p =>
        if z' (csRawCarry n p.2) then 1 else 0).sum) := by
    simp_rw [hstep_col, mul_add, Finset.sum_add_distrib]
  have hpart1 : (∑ b : Fin (hcEll n), 2 ^ b.1 * ((ann.filter fun p => decide (p.1.1 = b)).map fun p =>
      if z' (csRawSum n p.2) then 1 else 0).sum) =
      (ann.map fun p => 2 ^ p.1.1.1 * (if z' (csRawSum n p.2) then 1 else 0)).sum :=
    sum_filter_eq_map ann (fun p => p.1.1) (fun p => if z' (csRawSum n p.2) then 1 else 0)
  have hpart2 : (∑ b : Fin (hcEll n), 2 ^ b.1 * ((ann.filter fun p => decide (p.1.1.1 + 1 = b.1)).map fun p =>
      if z' (csRawCarry n p.2) then 1 else 0).sum) +
      2 ^ hcEll n * ((ann.filter fun p => decide (p.1.1.1 + 1 = hcEll n)).map fun p =>
        if z' (csRawCarry n p.2) then 1 else 0).sum =
      (ann.map fun p => 2 ^ p.1.1.1 * 2 * (if z' (csRawCarry n p.2) then 1 else 0)).sum :=
    sum_filter_succ_eq_map ann (fun p => p.1.1) (fun p => if z' (csRawCarry n p.2) then 1 else 0)
  have hadd_ann : (ann.map fun p => 2 ^ p.1.1.1 * (if z' (csRawSum n p.2) then 1 else 0)).sum +
      (ann.map fun p => 2 ^ p.1.1.1 * 2 * (if z' (csRawCarry n p.2) then 1 else 0)).sum =
      ((csAllTriples n st).map fun q => 2 ^ q.1.1 * ((if z q.2.1 then 1 else 0) +
        (if z q.2.2.1 then 1 else 0) + (if z q.2.2.2 then 1 else 0))).sum := by
    have hmap_sum : ∀ (L : List _), (∀ p ∈ L, p ∈ ann) →
        (L.map fun p => 2 ^ p.1.1.1 * (if z' (csRawSum n p.2) then 1 else 0)).sum +
        (L.map fun p => 2 ^ p.1.1.1 * 2 * (if z' (csRawCarry n p.2) then 1 else 0)).sum =
        (L.map fun p => 2 ^ p.1.1.1 * ((if z p.1.2.1 then 1 else 0) +
          (if z p.1.2.2.1 then 1 else 0) + (if z p.1.2.2.2 then 1 else 0))).sum := by
      intro L hL
      induction L with
      | nil => simp
      | cons p rest ih =>
        have hp := hL p List.mem_cons_self
        have hs : z' (csRawSum n p.2) = xor (xor (z p.1.2.1) (z p.1.2.2.1)) (z p.1.2.2.2) :=
          csApplyList_sum z hann_pw hann_lt hp
        have hc : z' (csRawCarry n p.2) =
            xor (z p.1.2.1 && z p.1.2.2.1) (xor (z p.1.2.1) (z p.1.2.2.1) && z p.1.2.2.2) :=
          csApplyList_carry z hann_pw hann_lt hp
        have harith := bool_fullAdder_arith (z p.1.2.1) (z p.1.2.2.1) (z p.1.2.2.2)
        simp only [List.map_cons, List.sum_cons]
        have h_ih := ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
        rw [add_add_add_comm, h_ih, hs, hc]
        rw [mul_assoc (2 ^ p.1.1.1) 2, ← mul_add, harith]
    rw [hmap_sum ann (fun _ h => h), ← numberItems_map_fst st.nextPair (csAllTriples n st),
      List.map_map]
    rfl
  have htri_sum : ((csAllTriples n st).map fun q => 2 ^ q.1.1 * ((if z q.2.1 then 1 else 0) +
      (if z q.2.2.1 then 1 else 0) + (if z q.2.2.2 then 1 else 0))).sum =
      ∑ b : Fin (hcEll n), 2 ^ b.1 * ((takeTriples (st.cols b)).1.map fun t =>
        (if z t.1 then 1 else 0) + (if z t.2.1 then 1 else 0) + (if z t.2.2 then 1 else 0)).sum := by
    dsimp only [csAllTriples]
    rw [sum_map_flatMap]
    have hinner : ∀ b : Fin (hcEll n),
        (((takeTriples (st.cols b)).1.map fun t => (b, t)).map fun q =>
          2 ^ q.1.1 * ((if z q.2.1 then 1 else 0) + (if z q.2.2.1 then 1 else 0) +
            (if z q.2.2.2 then 1 else 0))).sum =
        2 ^ b.1 * ((takeTriples (st.cols b)).1.map fun t =>
          (if z t.1 then 1 else 0) + (if z t.2.1 then 1 else 0) + (if z t.2.2 then 1 else 0)).sum := by
      intro b
      rw [List.map_map]
      induction (takeTriples (st.cols b)).1 with
      | nil => simp
      | cons t rest ih =>
        simp only [List.map_cons, List.sum_cons, Function.comp_def] at ih ⊢
        rw [ih]; ring
    have hfun : (List.finRange (hcEll n)).map (fun b => (((takeTriples (st.cols b)).1.map fun t => (b, t)).map fun q =>
          2 ^ q.1.1 * ((if z q.2.1 then 1 else 0) + (if z q.2.2.1 then 1 else 0) +
            (if z q.2.2.2 then 1 else 0))).sum) =
        (List.finRange (hcEll n)).map fun b => 2 ^ b.1 * ((takeTriples (st.cols b)).1.map fun t =>
          (if z t.1 then 1 else 0) + (if z t.2.1 then 1 else 0) + (if z t.2.2 then 1 else 0)).sum := by
      exact List.map_congr_left fun b _ => hinner b
    change ((List.finRange (hcEll n)).map (fun x => (List.map _ _).sum)).sum = _
    rw [hfun, sum_map_finRange]
  have hcombine : (∑ b : Fin (hcEll n), 2 ^ b.1 * (takeTriples (st.cols b)).2.countP z) +
      (∑ b : Fin (hcEll n), 2 ^ b.1 * ((takeTriples (st.cols b)).1.map fun t =>
        (if z t.1 then 1 else 0) + (if z t.2.1 then 1 else 0) + (if z t.2.2 then 1 else 0)).sum) =
      ∑ b : Fin (hcEll n), 2 ^ b.1 * (st.cols b).countP z := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_add, add_comm ((takeTriples (st.cols b)).2.countP z), ← takeTriples_countP]
  dsimp only [z', ann] at hsum_cols hpart1 hpart2 hadd_ann ⊢
  calc (∑ b : Fin (hcEll n), 2 ^ b.1 * ((csStep n st).cols b).countP z') +
        2 ^ hcEll n * (((numberItems st.nextPair (csAllTriples n st)).filter
          fun p => decide (p.1.1.1 + 1 = hcEll n)).map fun p => if z' (csRawCarry n p.2) then 1 else 0).sum
      = (∑ b : Fin (hcEll n), 2 ^ b.1 * (takeTriples (st.cols b)).2.countP z) +
          ((∑ b : Fin (hcEll n), 2 ^ b.1 * ((ann.filter fun p => decide (p.1.1 = b)).map fun p =>
            if z' (csRawSum n p.2) then 1 else 0).sum) +
          ((∑ b : Fin (hcEll n), 2 ^ b.1 * ((ann.filter fun p => decide (p.1.1.1 + 1 = b.1)).map fun p =>
            if z' (csRawCarry n p.2) then 1 else 0).sum) +
          2 ^ hcEll n * ((ann.filter fun p => decide (p.1.1.1 + 1 = hcEll n)).map fun p =>
            if z' (csRawCarry n p.2) then 1 else 0).sum)) := by
        rw [hsum_cols]; abel
    _ = (∑ b : Fin (hcEll n), 2 ^ b.1 * (takeTriples (st.cols b)).2.countP z) +
          ((ann.map fun p => 2 ^ p.1.1.1 * (if z' (csRawSum n p.2) then 1 else 0)).sum +
           (ann.map fun p => 2 ^ p.1.1.1 * 2 * (if z' (csRawCarry n p.2) then 1 else 0)).sum) := by
        rw [hpart1, hpart2]
    _ = (∑ b : Fin (hcEll n), 2 ^ b.1 * (takeTriples (st.cols b)).2.countP z) +
          (∑ b : Fin (hcEll n), 2 ^ b.1 * ((takeTriples (st.cols b)).1.map fun t =>
            (if z t.1 then 1 else 0) + (if z t.2.1 then 1 else 0) + (if z t.2.2 then 1 else 0)).sum) := by
        rw [hadd_ann, htri_sum]
    _ = ∑ b : Fin (hcEll n), 2 ^ b.1 * (st.cols b).countP z := hcombine

private lemma act_csCircuitAt_ket (n : ℕ) (hn : 1 ≤ n) (z₀ : Qubits (hcWires n))
    (hclean : ∀ w : Fin (hcWires n), n + hcEll n ≤ w.1 → z₀ w = false) (r : ℕ) :
    ∃ x : Qubits (hcWires n),
      act (csCircuitAt n hn r).unitary (ket z₀) = ket x ∧
      (∀ w : Fin (hcWires n), w.1 < n + hcEll n → x w = z₀ w) ∧
      (∀ w : Fin (hcWires n), n + hcEll n + 2 * (csStateAt n r).nextPair ≤ w.1 → x w = false) ∧
      ∑ b : Fin (hcEll n), 2 ^ b.1 * ((csStateAt n r).cols b).countP x =
        (Finset.univ.filter fun i : Fin n => z₀ (hcQWire n i) = true).card := by
  have hell := hcEll_pos hn
  induction r with
  | zero =>
    refine ⟨z₀, by simp [csCircuitAt, LayeredCircuit.id_unitary, act_one], fun _ _ => rfl,
      fun w hw => hclean w (by simp [csStateAt, csInit] at hw; omega), ?_⟩
    dsimp only [csStateAt, csInit]
    let z0 : Fin (hcEll n) := ⟨0, hell⟩
    rw [Finset.sum_eq_single z0]
    · simp only [z0, pow_zero, one_mul, ↓reduceIte, List.countP_map]
      exact list_finRange_countP (fun i => z₀ (hcQWire n i))
    · intro b _ hb
      have hne : b.1 ≠ 0 := fun h => hb (Fin.ext h)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  | succ r ih =>
    rcases ih with ⟨x, hx_act, hx_low, hx_high, hx_sum⟩
    have hv := csValid_at n hn r
    have hround := act_csRoundCircuit_ket (csStateAt n r) hv x hx_high
    let x' := csApplyList n x (numberItems (csStateAt n r).nextPair (csAllTriples n (csStateAt n r)))
    refine ⟨x', ?_, ?_, ?_, ?_⟩
    · simp only [csCircuitAt, LayeredCircuit.seq_unitary, act_mul, hx_act, hround]
      rfl
    · intro w hw
      dsimp only [x']
      rw [csApplyList_preserve_low (csStateAt n r) hv x hw, hx_low w hw]
    · intro w hw
      change csApplyList n x (numberItems (csStateAt n r).nextPair (csAllTriples n (csStateAt n r))) w = false
      rw [csApplyList_preserve_high (csStateAt n r) hv x hw]
      apply hx_high
      dsimp only [csStateAt, csStep] at hw
      omega
    · have hws := csApplyList_weighted_sum (csStateAt n r) hv x
      dsimp only at hws
      have hcard_le : (Finset.univ.filter fun i : Fin n => z₀ (hcQWire n i) = true).card ≤ n := by
        calc (Finset.univ.filter fun i : Fin n => z₀ (hcQWire n i) = true).card
            ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
          _ = n := Fintype.card_fin n
      have hlt_pow := lt_two_pow_hcEll n
      have htop0 : (((numberItems (csStateAt n r).nextPair (csAllTriples n (csStateAt n r))).filter
          fun p => decide (p.1.1.1 + 1 = hcEll n)).map fun p =>
          if x' (csRawCarry n p.2) then 1 else 0).sum = 0 := by
        by_contra hne
        have h1 : 1 ≤ (((numberItems (csStateAt n r).nextPair (csAllTriples n (csStateAt n r))).filter
            fun p => decide (p.1.1.1 + 1 = hcEll n)).map fun p =>
            if x' (csRawCarry n p.2) then 1 else 0).sum := Nat.pos_of_ne_zero hne
        have hmul := Nat.mul_le_mul_left (2 ^ hcEll n) h1
        dsimp only [x'] at hmul
        omega
      dsimp only [x'] at htop0
      rw [htop0, mul_zero, add_zero] at hws
      exact hws.trans hx_sum

private noncomputable def rippleStep (n : ℕ) (b : Fin (hcEll n)) (ws : List (Fin (hcWires n))) :
    LayeredCircuit (hcWires n) :=
  let cin := hcCarryWire n b.1 (le_of_lt b.isLt)
  let s := hcSumWire n b
  let cout := hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt)
  match ws with
  | [] =>
    have hcs : cin ≠ s := by
      intro h; have := congrArg Fin.val h; dsimp [cin, s, hcCarryWire, hcSumWire] at this; omega
    cnotGate cin s hcs
  | [w1] =>
    if h1 : w1.1 < n ∨ (n + hcEll n ≤ w1.1 ∧ w1.1 < n + hcEll n + 2 * n) then
      have h1c : w1 ≠ cin := by
        intro h; have := congrArg Fin.val h; dsimp [cin, hcCarryWire] at this; omega
      have h1s : w1 ≠ s := by
        intro h; have := congrArg Fin.val h; dsimp [s, hcSumWire] at this; omega
      have h1co : w1 ≠ cout := by
        intro h; have := congrArg Fin.val h; dsimp [cout, hcCarryWire] at this; omega
      have hcs : cin ≠ s := by
        intro h; have := congrArg Fin.val h; dsimp [cin, s, hcCarryWire, hcSumWire] at this; omega
      have hcco : cin ≠ cout := by
        intro h; have := congrArg Fin.val h; dsimp [cin, cout, hcCarryWire] at this; omega
      halfAdder4 w1 cin s cout h1c h1s h1co hcs hcco
    else LayeredCircuit.id (hcWires n)
  | [w1, w2] =>
    if h12 : w1 ≠ w2 ∧ (w1.1 < n ∨ (n + hcEll n ≤ w1.1 ∧ w1.1 < n + hcEll n + 2 * n)) ∧
        (w2.1 < n ∨ (n + hcEll n ≤ w2.1 ∧ w2.1 < n + hcEll n + 2 * n)) then
      have h1s : w1 ≠ s := by
        intro h; have := congrArg Fin.val h; dsimp [s, hcSumWire] at this; omega
      have h1co : w1 ≠ cout := by
        intro h; have := congrArg Fin.val h; dsimp [cout, hcCarryWire] at this; omega
      have h2s : w2 ≠ s := by
        intro h; have := congrArg Fin.val h; dsimp [s, hcSumWire] at this; omega
      have h2co : w2 ≠ cout := by
        intro h; have := congrArg Fin.val h; dsimp [cout, hcCarryWire] at this; omega
      have hcs : cin ≠ s := by
        intro h; have := congrArg Fin.val h; dsimp [cin, s, hcCarryWire, hcSumWire] at this; omega
      have hcco : cin ≠ cout := by
        intro h; have := congrArg Fin.val h; dsimp [cin, cout, hcCarryWire] at this; omega
      have hsco : s ≠ cout := by
        intro h; have := congrArg Fin.val h; dsimp [s, cout, hcSumWire, hcCarryWire] at this; omega
      fullAdder5 w1 w2 cin s cout h12.1 h1s h1co h2s h2co hcs hcco hsco
    else LayeredCircuit.id (hcWires n)
  | _ :: _ :: _ :: _ => LayeredCircuit.id (hcWires n)

private lemma rippleStep_usesOnly (n : ℕ) (b : Fin (hcEll n)) (ws : List (Fin (hcWires n))) :
    (rippleStep n b ws).UsesOnly (fwdSupport n) := by
  rcases ws with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, rest⟩⟩⟩ <;> dsimp only [rippleStep]
  · refine (cnotGate_usesOnly _ _ _).mono fun w hw => ?_
    rw [mem_fwdSupport_iff]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl <;> [dsimp [hcCarryWire]; dsimp [hcSumWire]] <;> right <;> omega
  · split_ifs with h1
    · refine (halfAdder4_usesOnly _ _ _ _ _ _ _ _ _).mono fun w hw => ?_
      rw [mem_fwdSupport_iff]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · rcases h1 with h | h <;> [left; right] <;> omega
      · right; dsimp [hcCarryWire]; omega
      · right; dsimp [hcSumWire]; omega
      · right; dsimp [hcCarryWire]; omega
    · exact LayeredCircuit.id_usesOnly _
  · split_ifs with h12
    · refine (fullAdder5_usesOnly _ _ _ _ _ _ _ _ _ _ _ _ _).mono fun w hw => ?_
      rw [mem_fwdSupport_iff]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl
      · rcases h12.2.1 with h | h <;> [left; right] <;> omega
      · rcases h12.2.2 with h | h <;> [left; right] <;> omega
      · right; dsimp [hcCarryWire]; omega
      · right; dsimp [hcSumWire]; omega
      · right; dsimp [hcCarryWire]; omega
    · exact LayeredCircuit.id_usesOnly _
  · exact LayeredCircuit.id_usesOnly _

private lemma rippleStep_size (n : ℕ) (b : Fin (hcEll n)) (ws : List (Fin (hcWires n))) :
    (rippleStep n b ws).size ≤ 13 := by
  rcases ws with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, rest⟩⟩⟩ <;> dsimp only [rippleStep]
  · simp
  · split_ifs <;> simp
  · split_ifs <;> simp
  · simp

private lemma rippleStep_depth (n : ℕ) (b : Fin (hcEll n)) (ws : List (Fin (hcWires n))) :
    (rippleStep n b ws).depth ≤ 13 := by
  rcases ws with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, rest⟩⟩⟩ <;> dsimp only [rippleStep]
  · simp
  · split_ifs <;> simp
  · split_ifs <;> simp
  · simp

private lemma act_rippleStep_ket (n : ℕ) (b : Fin (hcEll n)) (ws : List (Fin (hcWires n)))
    (hlen : ws.length ≤ 2) (hnd : ws.Nodup)
    (hbnd : ∀ w ∈ ws, w.1 < n ∨ (n + hcEll n ≤ w.1 ∧ w.1 < n + hcEll n + 2 * n))
    (x : Qubits (hcWires n))
    (hxs : x (hcSumWire n b) = false)
    (hxc : x (hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt)) = false) :
    ∃ sVal cVal : Bool,
      act (rippleStep n b ws).unitary (ket x) =
        ket (fun w =>
          if w = hcSumWire n b then sVal
          else if w = hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt) then cVal
          else x w) ∧
      (if sVal then 1 else 0) + 2 * (if cVal then 1 else 0) =
        (if x (hcCarryWire n b.1 (le_of_lt b.isLt)) then 1 else 0) + ws.countP x := by
  let cin := hcCarryWire n b.1 (le_of_lt b.isLt)
  let s := hcSumWire n b
  let cout := hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt)
  have hsc : s ≠ cout := by
    intro h; have := congrArg Fin.val h; dsimp [s, cout, hcSumWire, hcCarryWire] at this; omega
  rcases ws with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, rest⟩⟩⟩
  · refine ⟨x cin, false, ?_, by simp [cin]⟩
    dsimp only [rippleStep]
    rw [act_cnotGate_ket]
    congr 1
    funext w
    by_cases hws : w = s
    · subst hws; simp [s, cin, hxs]
    · by_cases hwc : w = cout
      · subst hwc; rw [Function.update_of_ne hsc.symm, if_neg hws, if_pos rfl, hxc]
      · rw [Function.update_of_ne hws, if_neg hws, if_neg hwc]
  · have h1 := hbnd w1 List.mem_cons_self
    refine ⟨xor (x w1) (x cin), x w1 && x cin, ?_, ?_⟩
    · dsimp only [rippleStep]
      rw [dif_pos h1, act_halfAdder4_ket _ _ _ _ _ _ _ _ _ hsc x hxs hxc]
    · have har := bool_halfAdder_arith (x w1) (x cin)
      have hcnt : [w1].countP x = if x w1 then 1 else 0 := by
        cases hx : x w1 <;> simp [hx]
      dsimp only [cin] at har ⊢
      rw [hcnt]
      omega
  · have h1 := hbnd w1 (by simp)
    have h2 := hbnd w2 (by simp)
    rw [List.nodup_cons] at hnd
    have h12_ne : w1 ≠ w2 := fun h => hnd.1 (by simp [h])
    have h12 : w1 ≠ w2 ∧ (w1.1 < n ∨ (n + hcEll n ≤ w1.1 ∧ w1.1 < n + hcEll n + 2 * n)) ∧
        (w2.1 < n ∨ (n + hcEll n ≤ w2.1 ∧ w2.1 < n + hcEll n + 2 * n)) := ⟨h12_ne, h1, h2⟩
    refine ⟨xor (xor (x w1) (x w2)) (x cin),
      xor (x w1 && x w2) (xor (x w1) (x w2) && x cin), ?_, ?_⟩
    · dsimp only [rippleStep]
      rw [dif_pos h12, act_fullAdder5_ket _ _ _ _ _ _ _ _ _ _ _ _ _ x hxs hxc]
    · have har := bool_fullAdder_arith (x w1) (x w2) (x cin)
      have hcnt : [w1, w2].countP x = (if x w1 then 1 else 0) + (if x w2 then 1 else 0) := by
        cases hx1 : x w1 <;> cases hx2 : x w2 <;> simp [hx1, hx2]
      dsimp only [cin] at har ⊢
      rw [hcnt]
      omega
  · simp at hlen

private noncomputable def ripplePrefix (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n))) :
    (k : ℕ) → k ≤ hcEll n → LayeredCircuit (hcWires n)
  | 0, _ => LayeredCircuit.id (hcWires n)
  | k + 1, hk => (ripplePrefix n cols k (by omega)).seq (rippleStep n ⟨k, hk⟩ (cols ⟨k, hk⟩))

private lemma ripplePrefix_usesOnly (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n)))
    (k : ℕ) (hk : k ≤ hcEll n) :
    (ripplePrefix n cols k hk).UsesOnly (fwdSupport n) := by
  induction k with
  | zero => exact LayeredCircuit.id_usesOnly _
  | succ k ih =>
    exact LayeredCircuit.seq_usesOnly (ih (by omega)) (rippleStep_usesOnly n ⟨k, hk⟩ _)

private lemma ripplePrefix_size (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n)))
    (k : ℕ) (hk : k ≤ hcEll n) :
    (ripplePrefix n cols k hk).size ≤ 13 * k := by
  induction k with
  | zero => simp [ripplePrefix]
  | succ k ih =>
    simp only [ripplePrefix, LayeredCircuit.seq_size]
    have h1 := ih (by omega)
    have h2 := rippleStep_size n ⟨k, hk⟩ (cols ⟨k, hk⟩)
    omega

private lemma ripplePrefix_depth (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n)))
    (k : ℕ) (hk : k ≤ hcEll n) :
    (ripplePrefix n cols k hk).depth ≤ 13 * k := by
  induction k with
  | zero => simp [ripplePrefix]
  | succ k ih =>
    simp only [ripplePrefix, LayeredCircuit.seq_depth]
    have h1 := ih (by omega)
    have h2 := rippleStep_depth n ⟨k, hk⟩ (cols ⟨k, hk⟩)
    omega

private lemma sum_fin_lt_succ {m : ℕ} (k : ℕ) (hk : k + 1 ≤ m) (f : Fin m → ℕ) :
    (∑ j : Fin m, if j.1 < k + 1 then f j else 0) =
      (∑ j : Fin m, if j.1 < k then f j else 0) + f ⟨k, hk⟩ := by
  have hstep : ∀ j : Fin m,
      (if j.1 < k + 1 then f j else 0) =
        (if j.1 < k then f j else 0) + (if j = ⟨k, hk⟩ then f ⟨k, hk⟩ else 0) := by
    intro j
    by_cases hj : j.1 < k
    · have hne : j ≠ ⟨k, hk⟩ := fun h => by
        have := congrArg Fin.val h; dsimp at this; omega
      rw [if_pos (by omega), if_pos hj, if_neg hne, add_zero]
    · by_cases heq : j = ⟨k, hk⟩
      · subst heq; rw [if_pos (by simp), if_neg hj, if_pos rfl, zero_add]
      · have hne : j.1 ≠ k := fun h => heq (Fin.ext h)
        rw [if_neg (by omega), if_neg hj, if_neg heq]
  simp only [hstep, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private lemma act_ripplePrefix_ket (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n)))
    (hlen : ∀ b : Fin (hcEll n), (cols b).length ≤ 2)
    (hnd : ∀ b : Fin (hcEll n), (cols b).Nodup)
    (hbnd : ∀ b : Fin (hcEll n), ∀ w ∈ cols b,
      w.1 < n ∨ (n + hcEll n ≤ w.1 ∧ w.1 < n + hcEll n + 2 * n))
    (x₀ : Qubits (hcWires n))
    (hclean_sum : ∀ b : Fin (hcEll n), x₀ (hcSumWire n b) = false)
    (hclean_carry : ∀ c (hc : c ≤ hcEll n), x₀ (hcCarryWire n c hc) = false)
    (k : ℕ) (hk : k ≤ hcEll n) :
    ∃ x : Qubits (hcWires n),
      act (ripplePrefix n cols k hk).unitary (ket x₀) = ket x ∧
      (∀ w : Fin (hcWires n), w.1 < n + hcEll n + 2 * n → x w = x₀ w) ∧
      (∀ b : Fin (hcEll n), k ≤ b.1 → x (hcSumWire n b) = false) ∧
      (∀ c (hc : c ≤ hcEll n), k < c → x (hcCarryWire n c hc) = false) ∧
      (∑ j : Fin (hcEll n), if j.1 < k then 2 ^ j.1 * (if x (hcSumWire n j) then 1 else 0) else 0) +
        2 ^ k * (if x (hcCarryWire n k hk) then 1 else 0) =
        ∑ j : Fin (hcEll n), if j.1 < k then 2 ^ j.1 * (cols j).countP x₀ else 0 := by
  induction k with
  | zero =>
    refine ⟨x₀, by simp [ripplePrefix, LayeredCircuit.id_unitary, act_one], fun _ _ => rfl,
      fun b _ => hclean_sum b, fun c hc _ => hclean_carry c hc, ?_⟩
    simp [hclean_carry 0 (Nat.zero_le _)]
  | succ k ih =>
    rcases ih (by omega) with ⟨x, hx_act, hx_low, hx_sum, hx_carry, hx_val⟩
    let b : Fin (hcEll n) := ⟨k, hk⟩
    have hxs : x (hcSumWire n b) = false := hx_sum b le_rfl
    have hxc : x (hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt)) = false :=
      hx_carry (k + 1) hk (Nat.lt_succ_self k)
    rcases act_rippleStep_ket n b (cols b) (hlen b) (hnd b) (hbnd b) x hxs hxc with
      ⟨sVal, cVal, hstep_act, hstep_arith⟩
    let x' : Qubits (hcWires n) := fun w =>
      if w = hcSumWire n b then sVal
      else if w = hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt) then cVal
      else x w
    have hcount_eq : (cols b).countP x = (cols b).countP x₀ := by
      refine List.countP_congr fun w hw => ?_
      have heq : x w = x₀ w := by
        rcases hbnd b w hw with h | h <;> exact hx_low w (by omega)
      simp [heq]
    refine ⟨x', ?_, ?_, ?_, ?_, ?_⟩
    · simp only [ripplePrefix, LayeredCircuit.seq_unitary, act_mul, hx_act]
      exact hstep_act
    · intro w hw
      have hns : w ≠ hcSumWire n b := fun e => by
        have := congrArg Fin.val e; dsimp [hcSumWire] at this; omega
      have hnc : w ≠ hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt) := fun e => by
        have := congrArg Fin.val e; dsimp [hcCarryWire] at this; omega
      dsimp only [x']
      rw [if_neg hns, if_neg hnc, hx_low w hw]
    · intro j hj
      have hne_s : hcSumWire n j ≠ hcSumWire n b := fun e => by
        have := congrArg Fin.val e; dsimp [hcSumWire, b] at this; omega
      have hne_c : hcSumWire n j ≠ hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt) := fun e => by
        have := congrArg Fin.val e; dsimp [hcSumWire, hcCarryWire] at this; omega
      dsimp only [x']
      rw [if_neg hne_s, if_neg hne_c]
      exact hx_sum j (by omega)
    · intro c hc hgt
      have hne_s : hcCarryWire n c hc ≠ hcSumWire n b := fun e => by
        have := congrArg Fin.val e; dsimp [hcCarryWire, hcSumWire] at this; omega
      have hne_c : hcCarryWire n c hc ≠ hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt) := fun e => by
        have := congrArg Fin.val e; dsimp [hcCarryWire, b] at this; omega
      dsimp only [x']
      rw [if_neg hne_s, if_neg hne_c]
      exact hx_carry c hc (by omega)
    · have hsum_x' : (∑ j : Fin (hcEll n),
          if j.1 < k + 1 then 2 ^ j.1 * (if x' (hcSumWire n j) then 1 else 0) else 0) =
          (∑ j : Fin (hcEll n),
            if j.1 < k then 2 ^ j.1 * (if x (hcSumWire n j) then 1 else 0) else 0) +
            2 ^ k * (if sVal then 1 else 0) := by
        rw [sum_fin_lt_succ k hk (fun j => 2 ^ j.1 * (if x' (hcSumWire n j) then 1 else 0))]
        have hleft : (∑ j : Fin (hcEll n),
            if j.1 < k then 2 ^ j.1 * (if x' (hcSumWire n j) then 1 else 0) else 0) =
            ∑ j : Fin (hcEll n),
              if j.1 < k then 2 ^ j.1 * (if x (hcSumWire n j) then 1 else 0) else 0 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hj : j.1 < k
          · rw [if_pos hj, if_pos hj]
            have hne_s : hcSumWire n j ≠ hcSumWire n b := fun e => by
              have := congrArg Fin.val e; dsimp [hcSumWire, b] at this; omega
            have hne_c : hcSumWire n j ≠ hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt) := fun e => by
              have := congrArg Fin.val e; dsimp [hcSumWire, hcCarryWire] at this; omega
            have heq : x' (hcSumWire n j) = x (hcSumWire n j) := by
              dsimp only [x']; rw [if_neg hne_s, if_neg hne_c]
            simp only [heq]
          · rw [if_neg hj, if_neg hj]
        have hright : x' (hcSumWire n b) = sVal := by
          dsimp only [x']; rw [if_pos rfl]
        change _ + 2 ^ b.1 * (if x' (hcSumWire n b) then 1 else 0) = _
        rw [hleft, hright]
      have hcarry_x' : x' (hcCarryWire n (k + 1) hk) = cVal := by
        have hne_s : hcCarryWire n (k + 1) hk ≠ hcSumWire n b := fun e => by
          have := congrArg Fin.val e; dsimp [hcCarryWire, hcSumWire] at this; omega
        dsimp only [x']
        rw [if_neg hne_s, if_pos rfl]
      rw [hsum_x', hcarry_x', sum_fin_lt_succ k hk (fun j => 2 ^ j.1 * (cols j).countP x₀)]
      have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      rw [hpow]
      have har' : (if sVal then 1 else 0) + 2 * (if cVal then 1 else 0) =
          (if x (hcCarryWire n k (by omega)) then 1 else 0) + (cols b).countP x₀ := by
        rw [← hcount_eq]; exact hstep_arith
      dsimp only [b] at har'
      have hmk : (⟨k, hk⟩ : Fin (hcEll n)).1 = k := rfl
      rw [hmk, add_assoc, mul_assoc (2 ^ k) 2, ← mul_add, har', mul_add, ← add_assoc, hx_val]

private noncomputable def rippleCarry (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n))) :
    LayeredCircuit (hcWires n) :=
  ripplePrefix n cols (hcEll n) le_rfl

private lemma rippleCarry_usesOnly (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n))) :
    (rippleCarry n cols).UsesOnly (fwdSupport n) :=
  ripplePrefix_usesOnly n cols (hcEll n) le_rfl

private lemma rippleCarry_size (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n))) :
    (rippleCarry n cols).size ≤ 13 * hcEll n :=
  ripplePrefix_size n cols (hcEll n) le_rfl

private lemma rippleCarry_depth (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n))) :
    (rippleCarry n cols).depth ≤ 13 * hcEll n :=
  ripplePrefix_depth n cols (hcEll n) le_rfl

private lemma act_rippleCarry_ket (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n)))
    (hlen : ∀ b : Fin (hcEll n), (cols b).length ≤ 2)
    (hnd : ∀ b : Fin (hcEll n), (cols b).Nodup)
    (hbnd : ∀ b : Fin (hcEll n), ∀ w ∈ cols b,
      w.1 < n ∨ (n + hcEll n ≤ w.1 ∧ w.1 < n + hcEll n + 2 * n))
    (x₀ : Qubits (hcWires n))
    (hclean_sum : ∀ b : Fin (hcEll n), x₀ (hcSumWire n b) = false)
    (hclean_carry : ∀ c (hc : c ≤ hcEll n), x₀ (hcCarryWire n c hc) = false)
    (hw : ℕ) (hsum : ∑ b : Fin (hcEll n), 2 ^ b.1 * (cols b).countP x₀ = hw)
    (hhw_lt : hw < 2 ^ hcEll n) :
    ∃ x : Qubits (hcWires n),
      act (rippleCarry n cols).unitary (ket x₀) = ket x ∧
      (∀ w : Fin (hcWires n), w.1 < n + hcEll n + 2 * n → x w = x₀ w) ∧
      ∀ b : Fin (hcEll n), x (hcSumWire n b) = natToBitsLSB (hcEll n) hw b := by
  rcases act_ripplePrefix_ket n cols hlen hnd hbnd x₀ hclean_sum hclean_carry (hcEll n) le_rfl with
    ⟨x, hx_act, hx_low, _, _, hx_val⟩
  have hlt1 : (∑ j : Fin (hcEll n), if j.1 < hcEll n then 2 ^ j.1 * (if x (hcSumWire n j) then 1 else 0) else 0) =
      bitsToNatLSB (fun j : Fin (hcEll n) => x (hcSumWire n j)) := by
    dsimp only [bitsToNatLSB]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_pos j.isLt]
    split_ifs <;> simp
  have hlt2 : (∑ j : Fin (hcEll n), if j.1 < hcEll n then 2 ^ j.1 * (cols j).countP x₀ else 0) = hw := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun j _ => if_pos j.isLt
  rw [hlt1, hlt2] at hx_val
  have hcarry0 : (if x (hcCarryWire n (hcEll n) le_rfl) then 1 else 0) = 0 := by
    by_contra hne
    have h1 : 1 ≤ if x (hcCarryWire n (hcEll n) le_rfl) then 1 else 0 := Nat.pos_of_ne_zero hne
    have hmul := Nat.mul_le_mul_left (2 ^ hcEll n) h1
    omega
  rw [hcarry0, mul_zero, add_zero] at hx_val
  refine ⟨x, hx_act, hx_low, fun b => ?_⟩
  have hbits := natToBitsLSB_bitsToNatLSB (fun j : Fin (hcEll n) => x (hcSumWire n j))
  rw [hx_val] at hbits
  exact (congrFun hbits b).symm

private def copyWireSet (n : ℕ) (b : Fin (hcEll n)) : Finset (Fin (hcWires n)) :=
  {hcSumWire n b, hcOutWire n b}

private noncomputable def copyItems (n : ℕ) :
    List (LayeredCircuit (hcWires n) × Finset (Fin (hcWires n))) :=
  (List.finRange (hcEll n)).map fun b =>
    (cnotGate (hcSumWire n b) (hcOutWire n b) (by
      intro h; have := congrArg Fin.val h; dsimp [hcSumWire, hcOutWire] at this; omega),
     copyWireSet n b)

private lemma copyItems_usesOnly (n : ℕ) : ∀ p ∈ copyItems n, p.1.UsesOnly p.2 := by
  intro p hp
  simp only [copyItems, List.mem_map] at hp
  rcases hp with ⟨b, _, rfl⟩
  exact cnotGate_usesOnly _ _ _

private lemma copyItems_pairwise (n : ℕ) :
    (copyItems n).Pairwise fun p q => Disjoint p.2 q.2 := by
  dsimp only [copyItems]
  rw [List.pairwise_map]
  refine (List.nodup_iff_pairwise_ne.mp (List.nodup_finRange (hcEll n))).imp fun {a b} hab => ?_
  rw [Finset.disjoint_left]
  intro w ha hb
  simp only [copyWireSet, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with h | h <;>
    [have := congrArg Fin.val h; have := congrArg Fin.val h;
     have := congrArg Fin.val h; have := congrArg Fin.val h] <;>
    dsimp [hcSumWire, hcOutWire] at * <;> omega

private noncomputable def copyLayer (n : ℕ) : LayeredCircuit (hcWires n) :=
  (parMergeAux (copyItems n) (copyItems_usesOnly n) (copyItems_pairwise n)).1

private lemma copyLayer_size (n : ℕ) : (copyLayer n).size = hcEll n := by
  dsimp only [copyLayer]
  rw [(parMergeAux (copyItems n) (copyItems_usesOnly n) (copyItems_pairwise n)).2.2.1]
  have hsum : ∀ xs : List (Fin (hcEll n)),
      ((xs.map fun b => (cnotGate (hcSumWire n b) (hcOutWire n b) (by
        intro h; have := congrArg Fin.val h; dsimp [hcSumWire, hcOutWire] at this; omega),
        copyWireSet n b)).map fun p => p.1.size).sum = xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons a rest ih =>
      simp only [List.map_cons, List.sum_cons, cnotGate_size, List.length_cons]
      rw [ih]; omega
  dsimp only [copyItems]
  rw [hsum (List.finRange (hcEll n)), List.length_finRange]

private lemma copyLayer_depth (n : ℕ) : (copyLayer n).depth ≤ 1 := by
  dsimp only [copyLayer]
  refine le_trans (parMergeAux (copyItems n) (copyItems_usesOnly n) (copyItems_pairwise n)).2.2.2 ?_
  refine foldr_max_le (copyItems n) 1 fun p hp => ?_
  simp only [copyItems, List.mem_map] at hp
  rcases hp with ⟨b, _, rfl⟩
  simp

private lemma act_copyLayer_ket (n : ℕ) (z : Qubits (hcWires n)) :
    act (copyLayer n).unitary (ket z) =
      ket (fun w =>
        if h : n ≤ w.1 ∧ w.1 < n + hcEll n then
          xor (z w) (z (hcSumWire n ⟨w.1 - n, by omega⟩))
        else z w) := by
  let z_next : Qubits (hcWires n) := fun w =>
    if h : n ≤ w.1 ∧ w.1 < n + hcEll n then
      xor (z w) (z (hcSumWire n ⟨w.1 - n, by omega⟩))
    else z w
  dsimp only [copyLayer]
  have hact : ∀ p ∈ copyItems n, ∃ x' : Qubits (hcWires n),
      act p.1.unitary (ket z) = ket x' ∧ ∀ w ∈ p.2, x' w = z_next w := by
    intro p hp
    simp only [copyItems, List.mem_map] at hp
    rcases hp with ⟨b, _, rfl⟩
    refine ⟨_, act_cnotGate_ket _ _ _ z, fun w hw => ?_⟩
    simp only [copyWireSet, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · have hne : hcSumWire n b ≠ hcOutWire n b := by
        intro h; have := congrArg Fin.val h; dsimp [hcSumWire, hcOutWire] at this; omega
      have hnot : ¬ (n ≤ (hcSumWire n b).1 ∧ (hcSumWire n b).1 < n + hcEll n) := by
        dsimp [hcSumWire]; omega
      rw [Function.update_of_ne hne]
      dsimp only [z_next]
      rw [dif_neg hnot]
    · have hin : n ≤ (hcOutWire n b).1 ∧ (hcOutWire n b).1 < n + hcEll n := by
        dsimp [hcOutWire]; have := b.isLt; omega
      have hfin : (⟨(hcOutWire n b).1 - n, by omega⟩ : Fin (hcEll n)) = b := by
        ext; dsimp [hcOutWire]; omega
      rw [Function.update_self]
      dsimp only [z_next]
      rw [dif_pos hin, hfin]
  rw [act_parMergeAux_ket (copyItems n) (copyItems_usesOnly n) (copyItems_pairwise n) z z_next hact]
  congr 1
  funext w
  by_cases hw : w ∈ (copyItems n).foldr (fun p acc => p.2 ∪ acc) ∅
  · rw [if_pos hw]
  · rw [if_neg hw]
    split_ifs with h
    · exfalso; apply hw
      let b : Fin (hcEll n) := ⟨w.1 - n, by omega⟩
      have hw_eq : w = hcOutWire n b := Fin.ext (by dsimp [hcOutWire, b]; omega)
      have hp_mem : (cnotGate (hcSumWire n b) (hcOutWire n b) (by
          intro h; have := congrArg Fin.val h; dsimp [hcSumWire, hcOutWire] at this; omega),
          copyWireSet n b) ∈ copyItems n := by
        simp only [copyItems, List.mem_map]
        exact ⟨b, List.mem_finRange b, rfl⟩
      exact mem_foldr_union_of_mem hp_mem (by simp [copyWireSet, hw_eq])
    · rfl

def hammingAddFn (n : ℕ) (z : Qubits (n + hcEll n)) : Qubits (n + hcEll n) :=
  let hw : ℕ := (Finset.univ.filter fun i : Fin n => z (Fin.castAdd (hcEll n) i) = true).card
  fun k =>
    if hk : k.1 < n then z k
    else xor (z k) (natToBitsLSB (hcEll n) hw ⟨k.1 - n, by have := k.isLt; omega⟩)

private noncomputable def hammingFwd (n : ℕ) (hn : 1 ≤ n) : LayeredCircuit (hcWires n) :=
  (csCircuitAt n hn (3 * hcEll n)).seq (rippleCarry n (csStateAt n (3 * hcEll n)).cols)

private lemma hammingFwd_usesOnly (n : ℕ) (hn : 1 ≤ n) :
    (hammingFwd n hn).UsesOnly (fwdSupport n) :=
  LayeredCircuit.seq_usesOnly (csCircuitAt_usesOnly n hn (3 * hcEll n)) (rippleCarry_usesOnly n _)

noncomputable def hammingCounter (n : ℕ) : LayeredCircuit (n + hcEll n + hammingAnc n) :=
  if hn : 1 ≤ n then
    let fwd := hammingFwd n hn
    fwd.seq ((copyLayer n).seq fwd.adj)
  else
    LayeredCircuit.id (hcWires n)

lemma hammingCounter_size_tight (n : ℕ) :
    (hammingCounter n).size ≤ 26 * n + 27 * hcEll n := by
  unfold hammingCounter
  split_ifs with hn
  · simp only [hammingFwd, LayeredCircuit.seq_size, LayeredCircuit.adj_size, copyLayer_size]
    have h1 := csCircuitAt_size_le n hn (3 * hcEll n)
    have h2 := rippleCarry_size n (csStateAt n (3 * hcEll n)).cols
    omega
  · simp

lemma hammingCounter_size (n : ℕ) : (hammingCounter n).size ≤ 53 * n := by
  have h1 := hammingCounter_size_tight n
  have h2 := hcEll_le_self n
  omega

lemma hammingCounter_depth (n : ℕ) : (hammingCounter n).depth ≤ 104 * hcEll n + 1 := by
  unfold hammingCounter
  split_ifs with hn
  · simp only [hammingFwd, LayeredCircuit.seq_depth, LayeredCircuit.adj_depth]
    have h1 := csCircuitAt_depth n hn (3 * hcEll n)
    have h2 := rippleCarry_depth n (csStateAt n (3 * hcEll n)).cols
    have h3 := copyLayer_depth n
    omega
  · simp

lemma hammingCounter_depth_real (n : ℕ) (hn : 2 ≤ n) :
    ((hammingCounter n).depth : ℝ) ≤ (209 / Real.log 2) * Real.log n := by
  have h1 : 1 ≤ n := by omega
  have hd : ((hammingCounter n).depth : ℝ) ≤ 104 * (hcEll n : ℝ) + 1 := by
    exact_mod_cast hammingCounter_depth n
  have hclog := clog2_succ_le_real_log h1
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_ge : 1 ≤ Real.log n / Real.log 2 := by
    rw [one_le_div hlog2_pos]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  calc ((hammingCounter n).depth : ℝ)
      ≤ 104 * (Real.log n / Real.log 2 + 1) + 1 := by linarith
    _ = 104 * (Real.log n / Real.log 2) + 105 := by ring
    _ ≤ 104 * (Real.log n / Real.log 2) + 105 * (Real.log n / Real.log 2) := by linarith
    _ = (209 / Real.log 2) * Real.log n := by ring

private lemma act_hammingCounter_ket_aux (n : ℕ) (z : Qubits (hcWires n))
    (hclean : ∀ j : Fin (hammingAnc n), z (Fin.natAdd (n + hcEll n) j) = false) :
    act (hammingCounter n).unitary (ket z) =
      ket (Fin.addCases
        (hammingAddFn n (fun i => z (Fin.castAdd (hammingAnc n) i)))
        (fun _ : Fin (hammingAnc n) => false)) := by
  have hclean_ge : ∀ w : Fin (hcWires n), n + hcEll n ≤ w.1 → z w = false := by
    intro w hw
    have hj : w = Fin.natAdd (n + hcEll n) ⟨w.1 - (n + hcEll n), by
        dsimp only [hcWires] at *; have := w.isLt; omega⟩ := by
      ext; simp; omega
    rw [hj]
    exact hclean _
  by_cases hn : 1 ≤ n
  · simp only [hammingCounter, dif_pos hn]
    let fwd := hammingFwd n hn
    let hw : ℕ := (Finset.univ.filter fun i : Fin n =>
      z (Fin.castAdd (hammingAnc n) (Fin.castAdd (hcEll n) i)) = true).card
    have hcs := act_csCircuitAt_ket n hn z hclean_ge (3 * hcEll n)
    rcases hcs with ⟨x_cs, hcs_act, hcs_low, hcs_high, hcs_sum⟩
    have hst_len := csStateAt_three_mul_clog n
    have hvF := csValid_at n hn (3 * hcEll n)
    have hst_nd : ∀ b : Fin (hcEll n), ((csStateAt n (3 * hcEll n)).cols b).Nodup :=
      fun b => (csValid_cols_nodup hvF b).1
    have hst_bnd : ∀ b : Fin (hcEll n), ∀ w ∈ (csStateAt n (3 * hcEll n)).cols b,
        w.1 < n ∨ (n + hcEll n ≤ w.1 ∧ w.1 < n + hcEll n + 2 * n) := by
      intro b w hw_m
      have hp := hvF.pair_le
      rcases hvF.wire_bound b w hw_m with h | h
      · left; exact h
      · right; omega
    have hclean_sum : ∀ b : Fin (hcEll n), x_cs (hcSumWire n b) = false := by
      intro b
      apply hcs_high
      have := hvF.pair_le
      dsimp [hcSumWire]; omega
    have hclean_carry : ∀ c (hc : c ≤ hcEll n), x_cs (hcCarryWire n c hc) = false := by
      intro c hc
      apply hcs_high
      have := hvF.pair_le
      dsimp [hcCarryWire]; omega
    have hhw_eq : (Finset.univ.filter fun i : Fin n => z (hcQWire n i) = true).card = hw := by
      rfl
    rw [hhw_eq] at hcs_sum
    have hrc := act_rippleCarry_ket n (csStateAt n (3 * hcEll n)).cols hst_len hst_nd hst_bnd x_cs
      hclean_sum hclean_carry hw hcs_sum (by
        have hle : hw ≤ n := by
          calc hw ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
            _ = n := Fintype.card_fin n
        exact Nat.lt_of_le_of_lt hle (lt_two_pow_hcEll n))
    rcases hrc with ⟨x_mid, hrc_act, hrc_low, hrc_sum⟩
    have hfwd_act : act fwd.unitary (ket z) = ket x_mid := by
      dsimp only [fwd, hammingFwd]
      rw [LayeredCircuit.seq_unitary, act_mul, hcs_act, hrc_act]
    have hx_mid_low : ∀ w : Fin (hcWires n), w.1 < n + hcEll n → x_mid w = z w := by
      intro w hw_lt
      rw [hrc_low w (by omega), hcs_low w hw_lt]
    have hcopy := act_copyLayer_ket n x_mid
    let x_copy : Qubits (hcWires n) := fun w =>
      if h : n ≤ w.1 ∧ w.1 < n + hcEll n then
        xor (x_mid w) (x_mid (hcSumWire n ⟨w.1 - n, by omega⟩))
      else x_mid w
    have hfwd_adj_xmid : act fwd.adj.unitary (ket x_mid) = ket z := by
      rw [← hfwd_act, ← act_mul, LayeredCircuit.adj_unitary,
        Matrix.mem_unitaryGroup_iff'.mp fwd.unitary_mem_unitaryGroup, act_one]
    have hagree : ∀ w ∈ fwdSupport n, x_copy w = x_mid w := by
      intro w hw_mem
      rw [mem_fwdSupport_iff] at hw_mem
      dsimp only [x_copy]
      rw [dif_neg (by omega)]
    have hfwd_adj_copy := act_ket_agree_on_usesOnly fwd.adj
      (LayeredCircuit.adj_usesOnly (hammingFwd_usesOnly n hn)) hfwd_adj_xmid hagree
    change act (fwd.seq ((copyLayer n).seq fwd.adj)).unitary (ket z) = _
    simp only [LayeredCircuit.seq_unitary, act_mul, hfwd_act]
    rw [hcopy, hfwd_adj_copy]
    congr 1
    funext w
    refine Fin.addCases (fun i => ?_) (fun j => ?_) w
    · simp only [Fin.addCases_left, hammingAddFn]
      by_cases hi : i.1 < n
      · have hmem : Fin.castAdd (hammingAnc n) i ∈ fwdSupport n := by
          rw [mem_fwdSupport_iff]; left; simp [hi]
        rw [if_pos hmem]
        simp [hi]
      · have hnot : Fin.castAdd (hammingAnc n) i ∉ fwdSupport n := by
          rw [mem_fwdSupport_iff]; simp only [Fin.val_castAdd]; omega
        rw [if_neg hnot]
        have hi_lt := i.isLt
        have hin : n ≤ (Fin.castAdd (hammingAnc n) i).1 ∧
            (Fin.castAdd (hammingAnc n) i).1 < n + hcEll n := by
          simp only [Fin.val_castAdd]; omega
        dsimp only [x_copy]
        rw [dif_pos hin, hx_mid_low _ (by simp)]
        have hb_eq : (⟨(Fin.castAdd (hammingAnc n) i).1 - n, by omega⟩ : Fin (hcEll n)) =
            ⟨i.1 - n, by omega⟩ := Fin.ext (by simp)
        rw [hb_eq, hrc_sum ⟨i.1 - n, by omega⟩]
        simp only [hi, ↓reduceDIte]
        rfl
    · have hmem : Fin.natAdd (n + hcEll n) j ∈ fwdSupport n := by
        rw [mem_fwdSupport_iff]; right; simp
      rw [if_pos hmem, Fin.addCases_right]
      exact hclean j
  · have hn0 : n = 0 := by omega
    subst hn0
    simp only [hammingCounter, dif_neg (by decide : ¬ 1 ≤ 0), LayeredCircuit.id_unitary, act_one]
    congr 1
    funext w
    refine Fin.addCases (fun i => ?_) (fun j => ?_) w
    · simp only [Fin.addCases_left, hammingAddFn]
      have hi_lt := i.isLt
      have h0 : hcEll 0 = 0 := by simp [hcEll]
      omega
    · rw [Fin.addCases_right]
      exact hclean j

theorem act_hammingCounter_zero_ket (n : ℕ) (x : Qubits n) :
    act (hammingCounter n).unitary
        (ket (Fin.addCases (Fin.addCases x (fun _ => false)) (fun _ : Fin (hammingAnc n) => false))) =
      ket (Fin.addCases
        (Fin.addCases x (natToBitsLSB (hcEll n) (Finset.univ.filter fun i : Fin n => x i = true).card))
        (fun _ : Fin (hammingAnc n) => false)) := by
  let z : Qubits (hcWires n) :=
    Fin.addCases (Fin.addCases x (fun _ : Fin (hcEll n) => false)) (fun _ : Fin (hammingAnc n) => false)
  have hclean : ∀ j : Fin (hammingAnc n), z (Fin.natAdd (n + hcEll n) j) = false := fun j => by
    simp only [z, Fin.addCases_right]
  rw [act_hammingCounter_ket_aux n z hclean]
  congr 1
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [Fin.addCases_left, hammingAddFn]
    have hw_eq : (Finset.univ.filter fun i' : Fin n =>
        z (Fin.castAdd (hammingAnc n) (Fin.castAdd (hcEll n) i')) = true).card =
        (Finset.univ.filter fun i' : Fin n => x i' = true).card := by
      congr 1; ext i'; simp only [z, Fin.addCases_left]
    refine Fin.addCases (fun q => ?_) (fun b => ?_) i
    · simp only [Fin.val_castAdd, q.isLt, ↓reduceDIte, z, Fin.addCases_left]
    · have hnot : ¬ (n + b.1 < n) := by omega
      simp only [Fin.val_natAdd, hnot, ↓reduceDIte, Fin.addCases_right]
      have hz_b : z (Fin.castAdd (hammingAnc n) (Fin.natAdd n b)) = false := by
        simp only [z, Fin.addCases_left, Fin.addCases_right]
      have hb_sub : (⟨n + b.1 - n, by have := (Fin.natAdd n b).isLt; omega⟩ : Fin (hcEll n)) = b :=
        Fin.ext (by dsimp; omega)
      rw [hz_b, hw_eq, hb_sub]
      simp only [Bool.false_xor]
  · simp only [Fin.addCases_right]

end Thm49Primitives


