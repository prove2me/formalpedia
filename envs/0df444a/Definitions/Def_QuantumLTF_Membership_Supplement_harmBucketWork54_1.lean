-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_1
-- name    : QuantumLTF_Membership_Supplement_harmBucketWork54_1
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-25T06:28:44.031013+00:00
-- url     : https://prove2.me/theorems/3651250a-a6bd-4383-83ca-b10d9ec2f0c7
-- title:
--   Harmonic-Bucket $2$-Sort working layout and layer module (1/11)
-- statement:
--   Working Lean definitions, register embeddings, disjointness lemmas, circuit combinators, and layer interface structures (`HarmBucketOcc54`, `HarmBucketRouteA54`, `HarmBucketRouteB54`) for `HarmBucketHL54V2` — module slice 1 of 11 (`harmBucketWork54_1`).
-- source:
--   Liu, Childs, Gottesman [LCG26], First and second quantization: reversible and quantum circuits (arXiv:2411.04019, Section IV.B–C); Krivcenko, Nguyen, de Wolf [KNW26] (arXiv:2609.40331, Theorem 5.4).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54Comb
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54Circs
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketHL54V2

set_option autoImplicit false

/-!
# Harmonic-Bucket 2-Sort Working Module (1/11)
-/

namespace HarmBucketWork54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router Cslib.BitonicSort

/-! ### Part 1: Slice Embeddings & Basic Circuit Combinators -/

def sliceEmb {m : ℕ} (off len : ℕ) (h : off + len ≤ m) : Fin len ↪ Fin m where
  toFun i := ⟨off + i.1, by omega⟩
  inj' _ _ hij := Fin.ext (by have := congrArg Fin.val hij; dsimp at this; omega)

@[simp] lemma sliceEmb_apply {m : ℕ} (off len : ℕ) (h : off + len ≤ m) (i : Fin len) :
    sliceEmb off len h i = ⟨off + i.1, by omega⟩ := rfl

lemma sliceEmb_disjoint {m o1 l1 o2 l2 : ℕ} (h1 : o1 + l1 ≤ m) (h2 : o2 + l2 ≤ m)
    (h : o1 + l1 ≤ o2 ∨ o2 + l2 ≤ o1) :
    ∀ i j, sliceEmb o1 l1 h1 i ≠ sliceEmb o2 l2 h2 j := by
  intro i j hij
  have hv := congrArg Fin.val hij
  have hi := i.isLt
  have hj := j.isLt
  simp only [sliceEmb_apply] at hv
  omega

def regEmb {m : ℕ} (off N w : ℕ) (h : off + N * w ≤ m) : Fin (N * w) ↪ Fin m :=
  sliceEmb off (N * w) h

def slotInReg (N w : ℕ) (j : Fin N) : Fin w ↪ Fin (N * w) where
  toFun b := finProdFinEquiv (j, b)
  inj' _ _ h := (Prod.ext_iff.mp (finProdFinEquiv.injective h)).2

def slotEmb {m : ℕ} (off N w : ℕ) (h : off + N * w ≤ m) (j : Fin N) : Fin w ↪ Fin m :=
  (slotInReg N w j).trans (regEmb off N w h)

lemma slotInReg_disjoint {N w : ℕ} {j1 j2 : Fin N} (hj : j1 ≠ j2) :
    ∀ b1 b2, slotInReg N w j1 b1 ≠ slotInReg N w j2 b2 := by
  intro b1 b2 h
  exact hj (Prod.ext_iff.mp (finProdFinEquiv.injective h)).1

lemma slotEmb_disjoint_slot {m off N w : ℕ} (h : off + N * w ≤ m) {j1 j2 : Fin N} (hj : j1 ≠ j2) :
    ∀ b1 b2, slotEmb off N w h j1 b1 ≠ slotEmb off N w h j2 b2 := by
  intro b1 b2 hij
  exact slotInReg_disjoint hj b1 b2 ((regEmb off N w h).injective hij)

lemma slotEmb_disjoint_slice {m off N w o2 l2 : ℕ} (h1 : off + N * w ≤ m) (h2 : o2 + l2 ≤ m)
    (hdisj : off + N * w ≤ o2 ∨ o2 + l2 ≤ off) (j : Fin N) :
    ∀ b i, slotEmb off N w h1 j b ≠ sliceEmb o2 l2 h2 i :=
  fun b i => sliceEmb_disjoint h1 h2 hdisj (slotInReg N w j b) i

lemma slice_disjoint_slotEmb {m off N w o2 l2 : ℕ} (h1 : off + N * w ≤ m) (h2 : o2 + l2 ≤ m)
    (hdisj : off + N * w ≤ o2 ∨ o2 + l2 ≤ off) (j : Fin N) :
    ∀ i b, sliceEmb o2 l2 h2 i ≠ slotEmb off N w h1 j b :=
  fun i b hij => slotEmb_disjoint_slice h1 h2 hdisj j b i hij.symm

lemma emb_disjoint_combineEmb {a b c m : ℕ} {ea : Fin a ↪ Fin m} {eb : Fin b ↪ Fin m}
    {ec : Fin c ↪ Fin m} (hab : ∀ i j, ea i ≠ eb j)
    (hac : ∀ i k, ea i ≠ ec k) (hbc : ∀ j k, eb j ≠ ec k) :
    ∀ u k, combineEmb ea eb hab u ≠ ec k := by
  intro u k
  induction u using Fin.addCases with
  | left i => simp only [combineEmb_castAdd]; exact hac i k
  | right j => simp only [combineEmb_natAdd]; exact hbc j k

lemma combineEmb_disjoint_emb {a b c m : ℕ} {ea : Fin a ↪ Fin m} {eb : Fin b ↪ Fin m}
    {ec : Fin c ↪ Fin m} (hab : ∀ i j, ea i ≠ eb j)
    (hac : ∀ i k, ea i ≠ ec k) (hbc : ∀ j k, eb j ≠ ec k) :
    ∀ k u, ec k ≠ combineEmb ea eb hab u :=
  fun k u h => emb_disjoint_combineEmb hab hac hbc u k h.symm

lemma trans_disjoint_left {a b c m : ℕ} {ea : Fin a ↪ Fin b} {eb : Fin b ↪ Fin m}
    {ec : Fin c ↪ Fin m} (hbc : ∀ j k, eb j ≠ ec k) :
    ∀ i k, (ea.trans eb) i ≠ ec k :=
  fun i k => hbc (ea i) k

lemma trans_disjoint_right {a b c m : ℕ} {ea : Fin a ↪ Fin m} {eb : Fin b ↪ Fin c}
    {ec : Fin c ↪ Fin m} (hac : ∀ i k, ea i ≠ ec k) :
    ∀ i j, ea i ≠ (eb.trans ec) j :=
  fun i j => hac i (eb j)

lemma act_adj_ket {m : ℕ} (lc : LayeredCircuit m) {ψ φ : EuclideanSpace ℂ (Qubits m)}
    (h : act lc.unitary ψ = φ) :
    act lc.adj.unitary φ = ψ := by
  rw [← h, ← act_mul, LayeredCircuit.adj_unitary,
    Matrix.mem_unitaryGroup_iff'.mp lc.unitary_mem_unitaryGroup, act_one]

lemma LayeredCircuit_seqList_size_le {m : ℕ} (lcs : List (LayeredCircuit m)) (B : ℕ)
    (hB : ∀ lc ∈ lcs, lc.size ≤ B) :
    (LayeredCircuit.seqList lcs).size ≤ lcs.length * B := by
  rw [LayeredCircuit.seqList_size]
  induction lcs with
  | nil => simp
  | cons lc rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := hB lc List.mem_cons_self
    have h2 := ih fun lc' hlc' => hB lc' (List.mem_cons_of_mem _ hlc')
    omega

lemma act_seqList_foldl {m : ℕ} {S : Type*} (enc : S → Qubits m)
    (circ : ℕ → LayeredCircuit m) (trans : S → ℕ → S)
    (xs : List ℕ) (s0 : S)
    (hstep : ∀ k ∈ xs, ∀ s : S, act (circ k).unitary (ket (enc s)) = ket (enc (trans s k))) :
    act (LayeredCircuit.seqList (xs.map circ)).unitary (ket (enc s0)) =
      ket (enc (xs.foldl trans s0)) := by
  induction xs generalizing s0 with
  | nil => simp [LayeredCircuit.seqList, act_one]
  | cons k ks ih =>
    simp only [List.map_cons, LayeredCircuit.seqList, LayeredCircuit.seq_unitary,
      act_mul, List.foldl_cons]
    rw [hstep k List.mem_cons_self s0]
    exact ih (trans s0 k) fun k' hk' => hstep k' (List.mem_cons_of_mem _ hk')

lemma act_seqList_range_vec {m : ℕ} (vec : ℕ → EuclideanSpace ℂ (Qubits m))
    (circ : ℕ → LayeredCircuit m) (n : ℕ)
    (hstep : ∀ k < n, act (circ k).unitary (vec k) = vec (k + 1)) :
    act (LayeredCircuit.seqList ((List.range n).map circ)).unitary (vec 0) = vec n := by
  induction n with
  | zero => simp [LayeredCircuit.seqList, act_one]
  | succ n ih =>
    have hunit : (LayeredCircuit.seqList ((List.range (n + 1)).map circ)).unitary =
        (circ n).unitary * (LayeredCircuit.seqList ((List.range n).map circ)).unitary := by
      simp [LayeredCircuit.seqList_unitary, List.range_succ, List.map_append,
        List.reverse_append]
    rw [hunit, act_mul, ih fun k hk => hstep k (Nat.lt_succ_of_lt hk)]
    exact hstep n (Nat.lt_succ_self n)

lemma act_seqList_range {m : ℕ} (enc : ℕ → Qubits m)
    (circ : ℕ → LayeredCircuit m) (n : ℕ)
    (hstep : ∀ k < n, act (circ k).unitary (ket (enc k)) = ket (enc (k + 1))) :
    act (LayeredCircuit.seqList ((List.range n).map circ)).unitary (ket (enc 0)) =
      ket (enc n) :=
  act_seqList_range_vec (fun k => ket (enc k)) circ n hstep

lemma updateOn_comp_disjoint {k1 k2 m : ℕ} (e1 : Fin k1 ↪ Fin m) (e2 : Fin k2 ↪ Fin m)
    (hdisj : ∀ i j, e1 i ≠ e2 j) (z : Qubits m) (val : Qubits k1) :
    updateOn e1 z val ∘ e2 = z ∘ e2 := by
  funext j
  apply updateOn_apply_not_mem
  rintro ⟨i, hi⟩
  exact hdisj i j hi

@[simp] lemma slotInReg_apply (N w : ℕ) (j : Fin N) (b : Fin w) :
    slotInReg N w j b = finProdFinEquiv (j, b) := rfl

@[simp] lemma flatReg_comp_slotInReg {N w : ℕ} (arr : Fin N → Qubits w) (j : Fin N) :
    flatReg N w arr ∘ slotInReg N w j = arr j := by
  funext b
  rw [Function.comp_apply, flatReg, slotInReg_apply, Equiv.symm_apply_apply]

lemma updateOn_slotEmb_comp_regEmb {m off N w : ℕ} (h : off + N * w ≤ m)
    (z : Qubits m) (arr : Fin N → Qubits w) (hz : z ∘ regEmb off N w h = flatReg N w arr)
    (j : Fin N) (val : Qubits w) :
    updateOn (slotEmb off N w h j) z val ∘ regEmb off N w h =
      flatReg N w (Function.update arr j val) := by
  funext idx
  rcases finProdFinEquiv.surjective idx with ⟨⟨q, b⟩, rfl⟩
  simp only [Function.comp_apply, flatReg, Equiv.symm_apply_apply]
  by_cases hq : q = j
  · subst hq
    change updateOn (slotEmb off N w h q) z val (slotEmb off N w h q b) =
      Function.update arr q val q b
    rw [updateOn_apply_emb, Function.update_self]
  · rw [Function.update_of_ne hq]
    have hnot : regEmb off N w h (finProdFinEquiv (q, b)) ∉ Set.range (slotEmb off N w h j) := by
      rintro ⟨b', hb'⟩
      have heq := (regEmb off N w h).injective hb'
      exact hq (Prod.ext_iff.mp (finProdFinEquiv.injective heq)).1.symm
    rw [updateOn_apply_not_mem _ _ _ hnot]
    have := congrFun hz (finProdFinEquiv (q, b))
    simpa [flatReg] using this

/-! ### Part 2: Width-Mismatch Low-Bit Copy Circuit (`copyLowBitsCircuit`) -/

/-- Copies (XORs) the bottom `min w₁ w₂` bits from register 1 (`w₁` bits) into the bottom
`min w₁ w₂` bits of register 2 (`w₂` bits), in MSB-first layout. -/
def copyLowBitsPrefix (w₁ w₂ : ℕ) : (k : ℕ) → k ≤ min w₁ w₂ → LayeredCircuit (w₁ + w₂)
  | 0, _ => LayeredCircuit.id (w₁ + w₂)
  | k + 1, hk =>
    let prev := copyLowBitsPrefix w₁ w₂ k (by omega)
    let m := min w₁ w₂
    let c : Fin (w₁ + w₂) := ⟨w₁ - m + k, by omega⟩
    let t : Fin (w₁ + w₂) := ⟨w₁ + (w₂ - m + k), by omega⟩
    have hct : c ≠ t := Fin.ne_of_val_ne (by dsimp [c, t]; omega)
    prev.seq (cnotGate c t hct)

lemma copyLowBitsPrefix_size (w₁ w₂ k : ℕ) (hk : k ≤ min w₁ w₂) :
    (copyLowBitsPrefix w₁ w₂ k hk).size = k := by
  induction k with
  | zero => simp [copyLowBitsPrefix]
  | succ k ih => simp [copyLowBitsPrefix, ih (by omega)]

lemma act_copyLowBitsPrefix_ket (w₁ w₂ k : ℕ) (hk : k ≤ min w₁ w₂) (z : Qubits (w₁ + w₂)) :
    act (copyLowBitsPrefix w₁ w₂ k hk).unitary (ket z) =
      ket (fun u =>
        let m := min w₁ w₂
        if h : w₁ + (w₂ - m) ≤ u.1 ∧ u.1 < w₁ + (w₂ - m) + k then
          xor (z u) (z ⟨(w₁ - m) + (u.1 - (w₁ + (w₂ - m))), by omega⟩)
        else z u) := by
  induction k with
  | zero =>
    simp only [copyLowBitsPrefix, LayeredCircuit.id_unitary, act_one]
    congr 1; funext u; rw [dif_neg (by omega)]
  | succ k ih =>
    dsimp only [copyLowBitsPrefix]
    rw [LayeredCircuit.seq_unitary, act_mul, ih (by omega), act_cnotGate_ket]
    congr 1; funext u
    set m := min w₁ w₂
    let c : Fin (w₁ + w₂) := ⟨w₁ - m + k, by omega⟩
    let t : Fin (w₁ + w₂) := ⟨w₁ + (w₂ - m + k), by omega⟩
    have hnc : ¬ (w₁ + (w₂ - m) ≤ c.1 ∧ c.1 < w₁ + (w₂ - m) + k) := by dsimp [c]; omega
    by_cases hut : u = t
    · subst hut
      have hnt : ¬ (w₁ + (w₂ - m) ≤ t.1 ∧ t.1 < w₁ + (w₂ - m) + k) := by dsimp [t]; omega
      have hnew : w₁ + (w₂ - m) ≤ t.1 ∧ t.1 < w₁ + (w₂ - m) + (k + 1) := by dsimp [t]; omega
      rw [Function.update_self, dif_neg hnc, dif_neg hnt, dif_pos hnew]
      have hidx : (⟨w₁ - m + (t.1 - (w₁ + (w₂ - m))), by omega⟩ : Fin (w₁ + w₂)) = c :=
        Fin.ext (by dsimp [c, t]; omega)
      rw [hidx]
    · rw [Function.update_of_ne hut]
      by_cases hu : w₁ + (w₂ - m) ≤ u.1 ∧ u.1 < w₁ + (w₂ - m) + k
      · have hu' : w₁ + (w₂ - m) ≤ u.1 ∧ u.1 < w₁ + (w₂ - m) + (k + 1) := by omega
        rw [dif_pos hu, dif_pos hu']
      · have hu' : ¬ (w₁ + (w₂ - m) ≤ u.1 ∧ u.1 < w₁ + (w₂ - m) + (k + 1)) := by
          intro h; apply hu; refine ⟨h.1, ?_⟩
          by_contra hge
          apply hut; apply Fin.ext; dsimp [t]; omega
        rw [dif_neg hu, dif_neg hu']

def copyLowBitsCircuit (w₁ w₂ : ℕ) : LayeredCircuit ((w₁ + w₂) + 0) :=
  copyLowBitsPrefix w₁ w₂ (min w₁ w₂) le_rfl

lemma copyLowBitsCircuit_size (w₁ w₂ : ℕ) :
    (copyLowBitsCircuit w₁ w₂).size = min w₁ w₂ :=
  copyLowBitsPrefix_size w₁ w₂ (min w₁ w₂) le_rfl

def copyLowBitsFn (w₁ w₂ : ℕ) (x : Qubits (w₁ + w₂)) : Qubits (w₁ + w₂) :=
  fun u =>
    let m := min w₁ w₂
    if _h : w₁ + (w₂ - m) ≤ u.1 then
      xor (x u) (x ⟨w₁ - m + (u.1 - (w₁ + (w₂ - m))), by have := u.isLt; omega⟩)
    else x u

lemma copyLowBitsCircuit_implements (w₁ w₂ : ℕ) :
    (copyLowBitsCircuit w₁ w₂).ImplementsOnClean (permMat (copyLowBitsFn w₁ w₂)) := by
  apply implementsOnClean_of_act_perm
  intro x
  have h0 : padZero (w₁ + w₂) 0 x = x := by funext u; simp
  have h0' : padZero (w₁ + w₂) 0 (copyLowBitsFn w₁ w₂ x) = copyLowBitsFn w₁ w₂ x := by funext u; simp
  rw [h0, h0']
  change act (copyLowBitsPrefix w₁ w₂ (min w₁ w₂) le_rfl).unitary (ket x) = _
  rw [act_copyLowBitsPrefix_ket]
  congr 1; funext u
  have hu := u.isLt
  dsimp only [copyLowBitsFn]
  by_cases h1 : w₁ + (w₂ - min w₁ w₂) ≤ u.1
  · have h2 : w₁ + (w₂ - min w₁ w₂) ≤ u.1 ∧ u.1 < w₁ + (w₂ - min w₁ w₂) + min w₁ w₂ := by omega
    rw [dif_pos h2, dif_pos h1]
  · have h2 : ¬ (w₁ + (w₂ - min w₁ w₂) ≤ u.1 ∧ u.1 < w₁ + (w₂ - min w₁ w₂) + min w₁ w₂) := by omega
    rw [dif_neg h2, dif_neg h1]

lemma natToBits_eq_of_lt_min (comb : LcgSym54Comb) (w₁ w₂ x : ℕ) (hx : x < 2 ^ (min w₁ w₂)) :
    (∀ j : Fin w₂, j.1 < w₂ - min w₁ w₂ → natToBits w₂ x j = false) ∧
    (∀ j : Fin (min w₁ w₂),
      natToBits w₂ x ⟨w₂ - min w₁ w₂ + j.1, by omega⟩ =
      natToBits w₁ x ⟨w₁ - min w₁ w₂ + j.1, by omega⟩) := by
  have hm1 : min w₁ w₂ ≤ w₁ := min_le_left _ _
  have hm2 : min w₁ w₂ ≤ w₂ := min_le_right _ _
  constructor
  · intro j hj
    have hj_rev : (Fin.rev j).1 ≥ min w₁ w₂ := by rw [Fin.val_rev]; omega
    have hbit := comb.natToBits_comp_revPerm w₂ x (Fin.rev j)
    rw [Fin.rev_rev] at hbit
    rw [hbit]
    apply Nat.testBit_eq_false_of_lt
    exact lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hj_rev)
  · intro j
    let k : ℕ := min w₁ w₂ - 1 - j.1
    have hk_lt : k < min w₁ w₂ := by omega
    have h1 : (⟨w₁ - min w₁ w₂ + j.1, by omega⟩ : Fin w₁) = (⟨k, by omega⟩ : Fin w₁).rev := by
      apply Fin.ext; rw [Fin.val_rev]; dsimp [k]; omega
    have h2 : (⟨w₂ - min w₁ w₂ + j.1, by omega⟩ : Fin w₂) = (⟨k, by omega⟩ : Fin w₂).rev := by
      apply Fin.ext; rw [Fin.val_rev]; dsimp [k]; omega
    rw [h1, h2, comb.natToBits_comp_revPerm, comb.natToBits_comp_revPerm]

lemma updateOn_combineEmb_right {a b m : ℕ} (eA : Fin a ↪ Fin m) (eB : Fin b ↪ Fin m)
    (hAB : ∀ i j, eA i ≠ eB j) (z : Qubits m)
    (f : Qubits (a + b) → Qubits (a + b))
    (hleft : ∀ (x : Qubits (a + b)) (i : Fin a), f x (Fin.castAdd b i) = x (Fin.castAdd b i))
    (g : Qubits b)
    (hright : ∀ j : Fin b, f (z ∘ combineEmb eA eB hAB) (Fin.natAdd a j) = g j) :
    updateOn (combineEmb eA eB hAB) z (f (z ∘ combineEmb eA eB hAB)) = updateOn eB z g := by
  funext u
  by_cases hu : u ∈ Set.range (combineEmb eA eB hAB)
  · rcases hu with ⟨ij, rfl⟩
    induction ij using Fin.addCases with
    | left i =>
      rw [updateOn_apply_emb, combineEmb_castAdd]
      have hnot : eA i ∉ Set.range eB := by rintro ⟨j, hj⟩; exact hAB i j hj.symm
      rw [updateOn_apply_not_mem _ _ _ hnot, hleft, Function.comp_apply, combineEmb_castAdd]
    | right j =>
      rw [updateOn_apply_emb, combineEmb_natAdd, updateOn_apply_emb, hright j]
  · have hnotB : u ∉ Set.range eB := fun ⟨j, hj⟩ => hu ⟨Fin.natAdd a j, by simpa using hj⟩
    rw [updateOn_apply_not_mem _ _ _ hu, updateOn_apply_not_mem _ _ _ hnotB]

lemma combineEmb_zero_right {a m : ℕ} (e : Fin a ↪ Fin m) (e0 : Fin 0 ↪ Fin m)
    (h : ∀ i j, e i ≠ e0 j) : combineEmb e e0 h = e := by
  ext i
  have hi : (i : Fin (a + 0)) = Fin.castAdd 0 i := Fin.ext rfl
  conv_lhs => rw [hi]
  rw [combineEmb_castAdd]

lemma act_copyLowBitsOn {w₁ w₂ m : ℕ} (arith : LcgSym54ArithV2)
    (e1 : Fin w₁ ↪ Fin m) (e2 : Fin w₂ ↪ Fin m) (hdisj : ∀ i j, e1 i ≠ e2 j)
    (z : Qubits m) :
    act ((copyLowBitsCircuit w₁ w₂).mapWires (combineEmb e1 e2 hdisj)).unitary (ket z) =
      ket (updateOn e2 z (fun j =>
        let k := min w₁ w₂
        if h : w₂ - k ≤ j.1 then
          xor (z (e2 j)) (z (e1 ⟨w₁ - k + (j.1 - (w₂ - k)), by have := j.isLt; omega⟩))
        else z (e2 j))) := by
  let embAnc : Fin 0 ↪ Fin m := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  have hA : ∀ i j, combineEmb e1 e2 hdisj i ≠ embAnc j := fun _ j => Fin.elim0 j
  have hsub := arith.act_subReg_perm (copyLowBitsCircuit w₁ w₂) (copyLowBitsFn w₁ w₂)
    (copyLowBitsCircuit_implements w₁ w₂) (combineEmb e1 e2 hdisj) embAnc hA z (fun j => Fin.elim0 j)
  rw [combineEmb_zero_right] at hsub
  rw [hsub]
  congr 1
  refine updateOn_combineEmb_right e1 e2 hdisj z (copyLowBitsFn w₁ w₂) ?_ _ ?_
  · intro x i
    dsimp only [copyLowBitsFn]
    have hlt : ¬ (w₁ + (w₂ - min w₁ w₂) ≤ (Fin.castAdd w₂ i : Fin (w₁ + w₂)).1) := by
      dsimp [Fin.castAdd]; omega
    rw [dif_neg hlt]
  · intro j
    dsimp only [copyLowBitsFn, Function.comp_apply]
    have hj := j.isLt
    by_cases h : w₂ - min w₁ w₂ ≤ j.1
    · have hge : w₁ + (w₂ - min w₁ w₂) ≤ (Fin.natAdd w₁ j : Fin (w₁ + w₂)).1 := by simp; omega
      rw [dif_pos hge, dif_pos h, combineEmb_natAdd]
      have hidx : (⟨w₁ - min w₁ w₂ + ((Fin.natAdd w₁ j : Fin (w₁ + w₂)).1 - (w₁ + (w₂ - min w₁ w₂))),
          by simp; omega⟩ : Fin (w₁ + w₂)) =
          Fin.castAdd w₂ ⟨w₁ - min w₁ w₂ + (j.1 - (w₂ - min w₁ w₂)), by omega⟩ := by
        apply Fin.ext; simp; omega
      rw [hidx, combineEmb_castAdd]
    · have hnot : ¬ (w₁ + (w₂ - min w₁ w₂) ≤ (Fin.natAdd w₁ j : Fin (w₁ + w₂)).1) := by
        simp; omega
      rw [dif_neg hnot, dif_neg h, combineEmb_natAdd]

lemma act_copyLowBitsOn_zero {w₁ w₂ m : ℕ} (comb : LcgSym54Comb) (arith : LcgSym54ArithV2)
    (e1 : Fin w₁ ↪ Fin m) (e2 : Fin w₂ ↪ Fin m) (hdisj : ∀ i j, e1 i ≠ e2 j)
    (z : Qubits m) (x : ℕ) (hx : x < 2 ^ (min w₁ w₂))
    (hz1 : z ∘ e1 = natToBits w₁ x) (hz2 : z ∘ e2 = fun _ => false) :
    act ((copyLowBitsCircuit w₁ w₂).mapWires (combineEmb e1 e2 hdisj)).unitary (ket z) =
      ket (updateOn e2 z (natToBits w₂ x)) := by
  rw [act_copyLowBitsOn arith e1 e2 hdisj z]
  congr 1; congr 1; funext j
  obtain ⟨hzero, hlow⟩ := natToBits_eq_of_lt_min comb w₁ w₂ x hx
  have h2j : z (e2 j) = false := congrFun hz2 j
  by_cases h : w₂ - min w₁ w₂ ≤ j.1
  · rw [dif_pos h, h2j, Bool.false_xor]
    have h1 : z (e1 ⟨w₁ - min w₁ w₂ + (j.1 - (w₂ - min w₁ w₂)), by have := j.isLt; omega⟩) =
        natToBits w₁ x ⟨w₁ - min w₁ w₂ + (j.1 - (w₂ - min w₁ w₂)), by have := j.isLt; omega⟩ :=
      congrFun hz1 _
    rw [h1, ← hlow ⟨j.1 - (w₂ - min w₁ w₂), by have := j.isLt; omega⟩]
    congr 1; apply Fin.ext; dsimp; omega
  · rw [dif_neg h, h2j, hzero j (Nat.lt_of_not_le h)]

lemma act_copyLowBitsOn_uncompute {w₁ w₂ m : ℕ} (comb : LcgSym54Comb) (arith : LcgSym54ArithV2)
    (e1 : Fin w₁ ↪ Fin m) (e2 : Fin w₂ ↪ Fin m) (hdisj : ∀ i j, e1 i ≠ e2 j)
    (z : Qubits m) (x : ℕ) (hx : x < 2 ^ (min w₁ w₂))
    (hz1 : z ∘ e1 = natToBits w₁ x) (hz2 : z ∘ e2 = natToBits w₂ x) :
    act ((copyLowBitsCircuit w₁ w₂).mapWires (combineEmb e1 e2 hdisj)).unitary (ket z) =
      ket (updateOn e2 z (fun _ => false)) := by
  rw [act_copyLowBitsOn arith e1 e2 hdisj z]
  congr 1; congr 1; funext j
  obtain ⟨hzero, hlow⟩ := natToBits_eq_of_lt_min comb w₁ w₂ x hx
  have h2j : z (e2 j) = natToBits w₂ x j := congrFun hz2 j
  by_cases h : w₂ - min w₁ w₂ ≤ j.1
  · rw [dif_pos h, h2j]
    have h1 : z (e1 ⟨w₁ - min w₁ w₂ + (j.1 - (w₂ - min w₁ w₂)), by have := j.isLt; omega⟩) =
        natToBits w₁ x ⟨w₁ - min w₁ w₂ + (j.1 - (w₂ - min w₁ w₂)), by have := j.isLt; omega⟩ :=
      congrFun hz1 _
    rw [h1, ← hlow ⟨j.1 - (w₂ - min w₁ w₂), by have := j.isLt; omega⟩]
    have hj_eq : (⟨w₂ - min w₁ w₂ + (j.1 - (w₂ - min w₁ w₂)), by have := j.isLt; omega⟩ : Fin w₂) = j := by
      apply Fin.ext; dsimp; omega
    rw [hj_eq, Bool.xor_self]
  · rw [dif_neg h, h2j, hzero j (Nat.lt_of_not_le h)]

section ArithWrappers

open QuantumLTF.Membership.Supplement.LcgSym54


open QuantumLTF.Membership.Supplement.LcgSym54

lemma act_setConstOn {w m : ℕ} (arith : LcgSym54ArithV2) (c : ℕ)
    (e : Fin w ↪ Fin m) (z : Qubits m) :
    act ((arith.setConstMSBCircuit w c).mapWires e).unitary (ket z) =
      ket (updateOn e z (fun i => xor (z (e i)) (natToBits w c i))) := by
  let embAnc : Fin 0 ↪ Fin m := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  have hdisj : ∀ i j, e i ≠ embAnc j := fun _ j => Fin.elim0 j
  have hsub := arith.act_subReg_perm (arith.setConstMSBCircuit w c) (setConstMSBFn w c)
    (arith.setConstMSBCircuit_implements w c) e embAnc hdisj z (fun j => Fin.elim0 j)
  rw [combineEmb_zero_right] at hsub
  exact hsub

lemma act_swapRegOn {w m : ℕ} (arith : LcgSym54ArithV2)
    (eA eB : Fin w ↪ Fin m) (hAB : ∀ i j, eA i ≠ eB j) (z : Qubits m) :
    act ((arith.swapRegCircuit w).mapWires (combineEmb eA eB hAB)).unitary (ket z) =
      ket (updateOn eB (updateOn eA z (z ∘ eB)) (z ∘ eA)) := by
  let embAnc : Fin 0 ↪ Fin m := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  have hdisj : ∀ i j, combineEmb eA eB hAB i ≠ embAnc j := fun _ j => Fin.elim0 j
  have hsub := arith.act_subReg_perm (arith.swapRegCircuit w) (swapRegFn w)
    (arith.swapRegCircuit_implements w) (combineEmb eA eB hAB) embAnc hdisj z (fun j => Fin.elim0 j)
  rw [combineEmb_zero_right] at hsub
  rw [hsub]
  congr 1; funext u
  by_cases hu : u ∈ Set.range (combineEmb eA eB hAB)
  · rcases hu with ⟨ij, rfl⟩
    induction ij using Fin.addCases with
    | left i =>
      rw [updateOn_apply_emb, combineEmb_castAdd]
      have hnotB : eA i ∉ Set.range eB := by rintro ⟨j, hj⟩; exact hAB i j hj.symm
      rw [updateOn_apply_not_mem _ _ _ hnotB, updateOn_apply_emb]
      dsimp only [swapRegFn, Function.comp_apply]
      have hlt : (Fin.castAdd w i : Fin (w + w)).1 < w := by dsimp [Fin.castAdd]; exact i.isLt
      rw [dif_pos hlt]
      have heq : (⟨w + (Fin.castAdd w i : Fin (w + w)).1, by dsimp [Fin.castAdd]; omega⟩ : Fin (w + w)) =
          Fin.natAdd w i := Fin.ext (by dsimp [Fin.castAdd, Fin.natAdd])
      rw [heq, combineEmb_natAdd]
    | right j =>
      rw [updateOn_apply_emb, combineEmb_natAdd, updateOn_apply_emb]
      dsimp only [swapRegFn, Function.comp_apply]
      have hge : ¬ ((Fin.natAdd w j : Fin (w + w)).1 < w) := by simp [Fin.natAdd]
      rw [dif_neg hge]
      have heq : (⟨(Fin.natAdd w j : Fin (w + w)).1 - w, by simp [Fin.natAdd]; omega⟩ : Fin (w + w)) =
          Fin.castAdd w j := Fin.ext (by simp [Fin.natAdd, Fin.castAdd])
      rw [heq, combineEmb_castAdd]
  · have hnotA : u ∉ Set.range eA := fun ⟨i, hi⟩ => hu ⟨Fin.castAdd w i, by rw [combineEmb_castAdd]; exact hi⟩
    have hnotB : u ∉ Set.range eB := fun ⟨j, hj⟩ => hu ⟨Fin.natAdd w j, by rw [combineEmb_natAdd]; exact hj⟩
    rw [updateOn_apply_not_mem _ _ _ hu, updateOn_apply_not_mem _ _ _ hnotB, updateOn_apply_not_mem _ _ _ hnotA]

lemma act_copyRegOn {w m : ℕ} (arith : LcgSym54ArithV2)
    (eSrc eDst : Fin w ↪ Fin m) (hSD : ∀ i j, eSrc i ≠ eDst j) (z : Qubits m) :
    act ((arith.copyRegCircuit w).mapWires (combineEmb eSrc eDst hSD)).unitary (ket z) =
      ket (updateOn eDst z (fun j => xor (z (eDst j)) (z (eSrc j)))) := by
  let embAnc : Fin 0 ↪ Fin m := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  have hdisj : ∀ i j, combineEmb eSrc eDst hSD i ≠ embAnc j := fun _ j => Fin.elim0 j
  have hsub := arith.act_subReg_perm (arith.copyRegCircuit w) (copyRegFn w)
    (arith.copyRegCircuit_implements w) (combineEmb eSrc eDst hSD) embAnc hdisj z (fun j => Fin.elim0 j)
  rw [combineEmb_zero_right] at hsub
  rw [hsub]
  congr 1
  refine updateOn_combineEmb_right eSrc eDst hSD z (copyRegFn w) ?_ _ ?_
  · intro x i
    dsimp only [copyRegFn]
    have hlt : ¬ (w ≤ (Fin.castAdd w i : Fin (w + w)).1) := by dsimp [Fin.castAdd]; omega
    rw [dif_neg hlt]
  · intro j
    dsimp only [copyRegFn, Function.comp_apply]
    have hge : w ≤ (Fin.natAdd w j : Fin (w + w)).1 := by dsimp [Fin.natAdd]; omega
    rw [dif_pos hge, combineEmb_natAdd]
    have hidx : (⟨(Fin.natAdd w j : Fin (w + w)).1 - w, by dsimp [Fin.natAdd]; omega⟩ : Fin (w + w)) =
        Fin.castAdd w j := Fin.ext (by dsimp [Fin.natAdd, Fin.castAdd]; omega)
    rw [hidx, combineEmb_castAdd]


end ArithWrappers


end HarmBucketWork54


